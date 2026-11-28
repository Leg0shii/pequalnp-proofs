import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37049.Model
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


end PEqualNP.Outside.L_meta_37049.Model

namespace PEqualNP.Outside.L_meta_37049
open PEqualNP.Outside.L_meta_37049.Model
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

def SBf (j : Nat) : Nat := [8, 7, 4, 4, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37049

namespace PEqualNP.Outside.L_meta_37049
open PEqualNP.Outside.L_meta_37049.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x2424d800000e802a0139c106022a2204180569531714902a13c0800c405948f504cd10328c3220050f8e0034587004c3000192d0804a0412c1ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461be428c3788518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930df21261bc424c3bc6498770c930bfa8a61f7514c2eea2985f14530fa28a6174514c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c2faa4186f90830de21061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20df21641bc42c83bc6590770cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea9441ef428837c85106f10a20f621441ac42883de6510778ca20ee19441ec328839865105f94620bea8c41ee21883d843105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c534837c84906f10920ef19241dc32482fea2907dd4520bba8a417c51483e8a2905d14520f790a41ed21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef420837c84106f10820f621041ac42083de6410778c820ee19041ec320839864105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10df21621bc42c43bc6588770cb10fd90621f820c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437c85086f10a10ef19421dc32842faa3087dd0610fa20c21f731843e863087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910df21221bc42443bc6488770c910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437c84086f10810ef19021dc32042fca2087dd0410fa20821f731043e862087dc8410fa108217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xc525077c84a0ef10941ef19283dc32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083be42107788420f78c841ee190837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598df54b31df21663bc42cc7bc6598f70cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718f790e31eea1c637e528c7dca518db94a31bea9463ed528c6daa518ef90a31de21463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931df21263bc424c7bc6498f70c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863de430c7ba8618df94831bea9063be420c7788418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f7a1643be42c87788590fb10b21d621643ef32c87bc6590f70cb21f619643cc32c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53887bca710d794e21bea9c43dd53886baa710df14e21bea9443be42887788510f78ca21ee194437e51887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487de8490ef90921de21243ec42487588490fbcc921ef19243dc32487d86490f30c921fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043be42087788410f78c821ee190437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40ef19681dc32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481be42903788520778ca40ee194817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c525037c84a06f10940ef19281dc32502fea2a07dd4540bba8a817c51503e8a2a05d14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52102faa4206f90840de21081de32103b864205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30df21661bc42cc3bc6598770cb30bf28
  | 2 => 0x8008038010020040080900200400017006004000020020080080001c0040000400000000002006004008000120100480000000c010000080000300400000401800012006fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa9287ef5250edea4a1df14943f6292876c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42ef29e855e53d0afaa7a17754f42aea9e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85be4390b7a87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1216fd4e42df29c85bd5390b78a7214f94a42dfa8c85be5190b7aa3216f14642dfa8485be5090b7aa1216f14242bfa9a85df5350abea6a15f14d42ee29a855c5350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216fd0c42df21885bd4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042dfa9885be5310b7aa6216f14c42df290853e5210b5ca4216fd4442df28885bd5110b78a2216fd4042df28085bd5010b78a0215fd5332bf2a665be54cca7ca9995f55332deaa6653d54ccaf8a9997bd0b32df21665bc42ccbd885996b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbbc87197750e32ee21c657e528cb7c85196f10a32ef99465ef328cafca3195f54632bf284657d508cbbea9197795232eeaa465dc548cabca51977d0a32ef214659e428cbba85197710a32ce21465df518cbbca3197754632ee28c65df508cbbca1197754232ee284657f544cb7ea8994fd5132bf2a2657d544caf8a8996f151329e2a265be424cb7884997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8195f55032be2a0657e530cbbe86197790c32eea1865dc430cafca4197bd0832df21065bc420cbd884196b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032efaa065de540cbbaa8197715032ef290655e520cb9ca41977d0832e7a1065de420cb3c84197750832ee210659c420cb9884196310832efa8865de510cbbaa2197714432efa8065de500cbbaa0197714032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf296837d52d077c85a0ef10b41ef19683dc32d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720efd0e41dea1c837e52907dca520db94a41bea9483ed52906daa520ef90a41de21483de32907b86520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837
  | 3 => 0x601960a8a00040c002fc0000000000028ab080013d27000000000000ce4e89054ee99c0d000000840f6800000d256c800416c68c791316017cb6926000749949606501d8e22970dad446680068272d1823a0002f8638005260004d26e5d4584b129a000b3c0000000066c55b6362e0002803b0003c80026a0009400000000002800000084b8c758000000000033e00000000000570000000ac1b439c0000057a7b8002071d800000000000001108002fc8f8290000000006c80000000000000000ce800245000001adb66676b1c002c00006fc003386ecde4002ec35e000518000000003f8000000012b8001ee7291400000000000268000000fd167152434a388735a00190153000001428004642b8520996ea001b70003c84bd9a0002b8000a41400002ec00344000960590475f0000001c51540dd850906107344a2a10005f072000054094802793f82701130b11e0f43287039cd89052bb6c2ba4460f544a1c80c330000ac48c000060274000954a2000000002368453e1f44aa318000000003d84f22a34e0001d0003b25280001536cbe8121b50d2d198900032e0002a18c6643512592e43a5d8ed1166aad94968292ee6184f8000900005a8000aa000001c052c301068004bc34d909544700004232d45c000000360b600084800000000e08000000014c86200056c0008523eadcce87c644000002715ea89c000001be000000005dc7a5218404c29d47e80053e03c002fe00000000000000bb4000003487a95fa7e00055c00000000889bbb7264cd6800000476000002cd0009087c8002861b0270ee278a60001f61e80f0018001cc001681b2000898a20c8654aa1539aa282145740ce4f4329230001247d4d013f0000018780000457c58aba000b48000004f6cc40032e0b866457aa04c6001268d643e02567000000205090000006205d000000938cd2d8008114000000010040000080000000000802000004000000040040100100200002002002004000020040000500300001800804006018010130000000000500600405802024018000000020300780900000800001000008030020000040000000200000800008000028060020000080100400004803008014008000020080400000400401816002010008000760080000200000401811000044010000000000000200000c010000020040601f000000008050000080500100a00802003000000000000000080380000c00400001008008018060000040000c00002c0280200a00401001000000048030020000080c0020240000200200c0000100600401801008004028030000380080000600c000030040280000300400403800000004008010020140100500000400801000010050030060240280000600802000046000000000020040280a0000200000001200800000000000030030
  | 4 => 0x910000002960000000022264c0025400000188800000cbdb8800516000683640e600000240000001a82e2000000000000000018c8530646c582800000000aa84300043c0000024800093b6b680000000cc54497c172150424b0101ab46853c6e0800b400000000000b295e0002d8970249730560003a1f305e001b82046ce3ed298b70008e52407e2e2d74e10000000f99aa8d1fe4a8000003cacf52e80033e928000003b0719939300620015b0fc4f0238000003420000000009a75cf18001c40000000000036000000000001648000009240034d00060c0015219e4ad1e80011230c0000023864800213000001a500019616552800208c74ef18439e7fc9b1eb03e2d030a9b0002216d2a626a00133000586da8000000004f8cc13b10c5a5ab9d04980013989143c6e4acb1e42ed586a858000000c391556acdcc8a860008597ea564e000020a365a6000002690005e0870001c66718b00000000000000556000840bd46eb595634f6b80005e000456480000000000000000051e034001390000000016b000da400000000000000000000014100826475800000000000fc28e0009fc220e12664a40028c0d6001818ed02ea44891ae554598002020005f40021c03a93c00313000b54000003520010c800620a55b7b6c6006ec8324730420c0a17b1e00000007a08c001643532460011480011a000000000eac10740000009bc9d11d52041cac2890002a000142000001a61e8392d380028400001cf9000016da18e0000007dc0006429a5399989317200000000568b70001d34d6128509255ccd0c000000000796daf6000000b7800000000d132b000000c526c0007ecb50005d6b9d6f81c34cbdc002336f000000028202325798000fa8c40034800077170325024000002f90000000010b000594eeb5f05a001b99b300000000019374789061df4fa6058680c4b60000000004e000f7951000000000000725c0bf8006966d17db74000c39008db2a00018f8c1068b190a0000000000000000000000309000000000ad0e24691600e3c22941a80029805800000000721b01c75e400000000000000db800000000371e0000820d405643600154800000198c2aef40c00072b1b4c004c00000000000002873009d8f88000001e4338004ca000b4342000440002b36280014a0004301dc001953fc0000015e0007f5a90de0000004104c268000b7307166d78b92de07e6c06e9141c06380011e1a26518135433c8d44ba522c61ed4e1d40000002bb3f002b2c5320e00083c5018d3e06e0f38e92b4658000000002e0ea80053a6948c81b3462fc000006309c84c000000314510a70de7b0000001fc000000002e80005b2d14c44c44500000000000000214041570000000002580000013c0033c482af80005e3168900036d04c3e008aaf1f4000000003b
  | 5 => 0x2ea20000000c80000c635ce1979000624000ea000000000000d4308b2096560d1c001e66b208d3a0000005e89412166c99079800000180001020000015923c0006b16ea5951000180800244cb0860000008fd72149000001918003780017880005800019a92000001402e540a34800000000000002f0446000000004340015195662ad1536b06502968002c528c000003585980000000037c8bc000000000000020353cc915c8000000008b80000000045a095fe000000005060016a0c40005d4000003980e1860050000003c0005e800000200136574fc8005ae1a116800548ab49b8000006f477ac40003c4000005c200000000
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xf528425d63d4a108fd91528423c6454a1097d8d528425c6354a10cbd48428432c5210a10d3d48328434c520ca10e310832842d663d0610ad99331843a442c8610f10cb218423e62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544427761551108f994544423e6215110c7d53534431c54d4d109798b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d1097988534423e64d49108f593524425e63d49109758f524432f54d4910cb153524434f53d4910d314f524432e64d4910cb593524434e63d4910d358f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524427b60549109b994524432f5414910cb150524434f5314910d314c524432f6414910cb190524434f6314910d318c524423e65909108f196424431f5390910c714e424432f5290910cb14a424423e65109108f194424431f5310910c714c424432f5210910cb148424425e658c91097196324431f548c910c7152324434f528c910d314a324425e650c91097194324431f540c910c7150324434f520c910d3148324438c420c910da14b10443345484110d514e104436452841109798f540425d63d50109b98b540426d62d50108f596540423e62950108f189540433461550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c109798a530431e5454c10c7551530425c6254c10d5185530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432f6494810cb192520434f6394810d318e520423f64548108f191520425f63548109718d520432e5454810cb551520434e5354810d354d520432f6454810cb191520434f6354810d318d52043646154810da181520423e64148108f590520425e63148109758c520426e62148108fd96420423d6590810c794e420431d5390810cb94a420432d52908108fd94420423d6510810c794c420431d5310810cb948420432d521081097d96320425d658c810c7952320431d548c810d394a320434d528c81097d94320425d650c810c7950320431d540c810d3948320434d520c810e3108320433554d0410b598f41042756510410ad993310435553cc4109d594310436552c8410e910b21043c432c84109d594210436952c8010f8c8720042796508010ea10820043c83208010f8084200427965840109dd9510042b46444010b518d10042e462440109ed9510042e86244010
  | 1 => 0x825d63152208f993538823d64d4e20c7952538831d5494e20c7951538831d5454e20d3d89538823e6414e208f59053882ce63d0a20d394f428831e5390a20c754e428831e5310a20c754c428832d5410a20d394c42882ad6510a20cb594428832e5310a20e394c428830e5310a20e354c428832c5310a20ab993328832e54cca20c7952328831d548ca20e310a328831e540ca20c7550328838e420ca20e3108328832e540ca20d354c32882cd650ca20d3594328834e540ca20e3950328830e540ca20e3550328834c540ca20cb109518834c3254620ab99221882ce63886208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551208f994544823e62151208f188544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534825e6514d20c7d50534831c5414d2097988534825c6214d208f996424831f5390920c714e424823e6510920c7d4c424831c531092097996324831f548c920c7152324825e650c920c7d50324831c540c920e3108324833754d4520cd153514835753d4520d514f514833642d4520cd10b514835632d4520d50cb51483375414520cd15051483575314520d514c51483364214520cd10851483563214520d50c8514826e65c8520cb153214834c53c8520d9147214832c5448520d314d21483645148520ba181214837051c8120cb152204834c5388120d9146204825f63550209718d540825e63150209758c540827661150209d584540823f6454c208f191530823e6414c208f59053082766114c209d58453082ce63d0820ab98a420826d6510820cb994420832d6510820cb94c420832c5310820ea98042083a96010820ab99332082ce628c820e310a320838e420c820e3108320826d650c820d3994320834d650c820d3950320834c540c820f298032083c9600c8208fd91510823c645442097d8d510825c6354420cb109510834c32544209b59621082ae6488420b398e210823e64940208f592500825e63940209758e500832c4294020d30ca50083a84288020f20ca200826f6548020ab19120082cc6348020b9185200827b6548020bc185200825e63d53109758f54c426e62d53109b58b54c425e63953109758e54c423e64d4f108f59353c426e62d4f109b58b53c423e6494f108f59253c423e64d4b108f59352c425e63d4b109758f52c423f6454b108f19152c425f6354b109718d52c432e5210b10cb54842c434e520cb10d354832c438c420cb10ea10820c43c8320831097d8d548425c63552109bd89548426c62552109798c548425d63152108fd91538423c6454e109bd89538426c6254e108f990538423d6414e108f993528423d64d4a109798
  | 2 => 0x32145408f997415029d63d0540c714f415032c52d0540cd147415031c5350540cb14941503345150540c714e405032c5290140cd146405025e6294c409bd89531026c6254c40b3189531034f6254c4097189531034c6254c4093189531023d6590c40c754e431031d5310c4097d8d521025c6354840c794e421031d5390840c794c421031d5310840cb948421025f658c84097596321025f650c84097594321038c420c8408f596411029e6390440c754e41102ae6290440c754c411031d53d00408fd95401029c6350040c754d40102ac6250040ad185401027b65500409b98b54cc26d62d53309d98754cc27561d5330c715143cc2cc6250f308fd9152cc23c6454b30cb94842cc32d5210b30d394832cc34d520cb30e310832cc23e64947308f59251cc26e62947309b58a51cc29d64cc7309b98b548c26d62d5230c7d50438c23f6454a308f191528c32e5210a30cb548428c34e528ca30e3108328c23f64546308f191518c29e648c630b398a318c23e62d51308f992544c26e62951309b58a544c27661951309d586544c25f63551309bd89544c26c62551309dd85544c27461551308f994544c31d63151308f988544c25e6590d30c7152434c25c6550d30c7151434c2cc6250d308f993524c23d64d4930cbd53524c32c54d4930cb993524c32d64d4930cbd50524c32c5414930cbd90524c32c6414930d3d8c524c34e4314930d350c524c23e65909308f196424c32f5290930cb14a424c23e65109308f194424c32f5210930cb148424c31f548c930c7152324c34c528c930c7d50324c31c540c930d3d48324c38c420c930cdd53514c33454d4530d9d4b514c36452d4530cd90b514c33442d4530d58cb514c35432d4530cdd50514c3345414530d9d48514c3645214530d590c514c3554314530cd908514c3344214530d58c8514c354321453097997314c29d64cc530c7153314c34c52cc530d5147314c31c544c530d3149314c354514c530c7152304c34c528c130d5146304c23d65950308f98a540c26f62550309b189540c2ac6255030c718d540c32f62550308f189540c32c62550308b189540c23e64150309798c540c25d65d0c30c7553430c25d6510c30c7550430c23f64548308f191520c23f65908308f596420c23f65108308f594420c31e548c830c7552320c31e540c830c7550320c34e520c830e3108320c25d658c430a7992310c31d548c430b398a310c31d540c430c7553300c25f654c030a7191300c31d544c030b3189300c2d4614c0309ed95300c25e63d53209758f54c827661d53209d58754c825e63953209758e54c823e64d4f208f59353c827661d4f209d58753c823e6494f208f59253c838c420cb208f99251c823d64947209798e51c825d6394720ba18121c825e63d52209758f548832f62552209798c548
  | 3 => 0xe21c794e428871d5390a21c794c428871d5310a21c7952328871d548ca21c7950328871d540ca21e3108328872e54c8621d394f218872d62d51218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e6515121c7d53534871c54d4d21d358b534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c7150534866e65d0921b398f424874c53d0921b9987424863e6590921c7d4e424871c5390921ab98a424863e6510921c7d4c424871c5310921cbd50424874c5310921ab994424872e6510921e3d4c424872e5310921cb14c424878c5310921c314c424866e65cc921ab993324872c54cc921b9987324865e658c921c7d52324871c548c921b398a324878c428c92197994324871f540c921c7150324878e420c921e3108324872c540c921d3d4c32486ce650c921d3994324878f540c921d3950324874c540c921e3150324870c540c921e910b21487c432c8521ab99221486ce6388521ced53504873854d4121d6d4f504875853d4121ea10b50487c832d4121ce90b504873842d4121d68cb504875832d4121cb108504874c3214121ced5050487385414121d6d4c50487585314121ea10850487c83214121dad08504873a4214121ce10850487684214121ca108504876b3214121d68c850487583214121da0c850487483214121dcc84504876a21141219798f540865d63d50219b98b540865e63950219758e540863e64d4c218f593530866e62d4c218f992530863d6494c21cb948420874e520c821e3108320863e64944218f592510865e63944219758e510866f6548421ba18121086776548421e990921087c63248421bc181210863f64540218f191500865f63540219718d50086ac6250f4097d8d52d025c6354b40cb94842d032d5210b40d394832d034d520cb40e310832d025e63947409758e51d026e62947409b58a51d029d63d074097d8d529025c6354a40cb94a429034e520ca40d3548329038c420ca4097d8d519025c6354640a798e41902ae62906409798b535025e6214d408f997435031c53d0d40c714d43502ac6250d409798f525025d63d4940d3d4f525034c53d4940d398f525034d63d4940d3d4c525034c5314940cbd90525034f6314940d318c525032f4314940cb50c525031f5390940c714e425032c5290940c7d4c425031c5310940cbd48425025e658c94097196325034f528c940d314a325025e650c94097194325034f520c940d3148325038c420c940d5d4f515035453d4540d9d4b515036452d4540cd90b515033442d4540d58cb515035432d4540d5d4c51503545314540d9d4851503645214540cdd0c51503354314540cd90851503344214540d58c85150354
  | 4 => 0x7189539071e53d0e41c794d43906ac6250e41d394e529074d5394a41cbd92529074f6394a41d318e529072f4394a41cb50e529065f6354a419718d529074e5354a41d354d529074f6354a41d318d529071e5390a41c754e429072e5290a41c794c429071d5310a41cb548429065f658ca4197596329074e528ca41d354a329065f650ca4197594329074e520ca41d3548329078c420ca41a758f419071e53d0641cb94b419063e6510d419798f525065d63d4941cb14a42506b66190941d3d48325074c520c941e3108325069e6390541ab98a415065e63141419758c505063f6550c41ab189431065f63548419718d521072e5210841cb54842106b56110841d3948321074d520c841e3108321069d63d04418fd954110677655044197d8d501065c63540419bd89501066c62540418f98a54cc66f62553319b18954cc6ac6255331c718d54cc72f62553318f18954cc72c62553318b18954cc71d54d0f31c755043cc63f6454b318f19152cc63f6590b318f59642cc63f6510b318f59442cc71e548cb31c755232cc71e540cb31c755032cc74e520cb31e310832cc66e62d52319b58b548c71d63952318f98a548c63c62552319b988548c66d6215231c7952438c71e5450e31b3189438c72e5494a31cb552528c72f6494a31cb192528c74f6394a31d390e528c74d4394a318fd91528c63c6454a31cb951528c72d5454a31cbd91528c72c6454a318fd96428c63d6590a31cb94a428c72d5290a318fd94428c63d6510a31cb948428c72d5210a31c7952328c71d548ca31d394a328c71e540ca31c7550328c74d520ca31e3108328c69d64cc631c7953318c74e52cc6319758e544c66f62551319b189544c67b60551319e181544c65e65d0d3197994434c71d5410d318f993524c63d64d4931cbd48424c72c5210931d314a324c6d6618c931e3108324c69e648c531b398a314c63e64141318f590504c65e63d50319b98b540c66d62d50318f992530c63d6494c3197596430c65f6550c31c7151430c6cc6250c318fd91520c63c6454831cb948420c72d5210831d3948320c74d520c831e3108320c6d5610c8318f992510c63d6494431a7593310c65f654c4319dd95310c63f64540318f191500c66f62540319b189500c65f63553219718d54c865e63153219758c54c863f6454f218f19153c863e6414f218f59053c86ce63d0b21cb99442c872d6510b21cb94c42c872c5310b21e998442c87a56110b21ab99332c878c428cb21e390832c878c420cb21d399432c874d650cb21d395032c874c540cb21f198432c87c5610cb218f99250c863d64943219798e50c865d6394321cb10a50c874c32943219798f548865d63d52219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414
  | 5 => 0x5090ab561d4242a798e5090a9d6394242d314f4250b1f5390942c714e4250aad62d0c42abd894310b1d5310c42a798f4210a9d63d08428fd954210a9f6350842a718d4210a6f6550842b318d4210a5e63944429758e5110a5f63540429718d5010a7761540429d1855010aae62d4c42ad9875310ab561d4c42c754c5310aae6214c42cb98a5210aae6394842ab5865210aae6094842a798f5110a9d63d4442a798e5110a9d6394442cd5445110a9f6354042a718d5010ab76154042ad1855010a9e6314042a758c5010ab66114042ad5845010b2f6255332cb55042ccaad6510b32cb59442ccb2c4254732cb10a50cca7661152329d584548cb1e5450e32c7d50438ca9e64cca32a7593328ca3f64546328f191518ca3e64942328f592508cace62d5232c7d52548cace6215232b5984548cad56115232e3988428cb575194632a7d91518ca9c6454632a7990518ca9d6414632a7993508ca9d64d4232b5987508cad561d4232a7992508ca9d64942328f992544ca5d639513297d8d544ca6f62551328f994544ca3e65909328f994424cb2c54cc932c7d52324cb1c548c9329d987540ca7561d50328f992530ca3d6494c3297596430cacd6290c32c7151430cacf6250c3297594430cb1d5410c32b358f420caae62908329b594420cb8f4310832e390c420cb8d4310832e310c420cb2e6510832cb594420cb8e6310832e358c420cb2e5310832a7993320ca9d64cc832e310b320ca5f654c832a7d91320ca9c644c832e3109320ca6f654c832ab191320ca3e64944328f592510cb2c4254432cb10a500ca3f64540328f191500ca7761540329d185500cace62d5032b5987540cad561d5032c7550540cace6215032d398a520cace6494832b3586520cace609483297597420cacd65d0832d3597420cacd61d0832b3983420cace6290832a798a420ca8e6290832c794a420cb8e529083297d95420cb8d4210832a7988420cb8e6210832c7948420cb8e5210832b3d94420cacd6510832b3990420cb8e6410832e3950420cb8d5410832b3584420cace6010832e3d94420cb8e6510832e3594420cb8c6510832e3d84420cb8e6110832e3584420cb8c6110832e3d80420cb8e6010832e3580420cb8c6010832a7993510ca9d64d4432e310b510ca9e6494432a7592510cb8c4294432e3109510cb8c4214432d5544510cb8c42d4032e310a500ca9f6454032a7191500cb8c4254032b5d85500cad46154032a7990500ca9d6414032e3108500cad66114032b5584500ca5e6294f419bd8953d066c6254f41b318953d074f6254f419718953d074c6254f419318953d071d5390f41c754c43d065f6354b419718d52d071e5390b41c754e42d071e5310b41c754c42d072e5210b4197d9632d065d658cb4197d9432d065d650cb41e310832d065e6294e419
  | 6 => 0xd1500981d2041a46a05a07a6407424a9d596f98b05d0ff8978531db95c1e502b14d08a0f80f09778439a19f90590a1a589e00cd21a8d10d086aa19a3494490c8829f69749731c49e70ad8b72938ed8168a899d12a1f0906a2918ea1b20104b9b31ea918a2380001502c0990f480011e27380000024e0ea0f40802961280a700027512212b8b188b1378d6a778cc84c87f0ef05190e28f21d0838000000889640cba089018000239e11f50039d482700820e8000000000000ab00000018180000000009803802000000028020100580000a0520080e000000000018000000000880201207c040000780000380301a00c0400203a000018150000140c00100000c0380903c0040a0000000000500c00202c1381100200009006000028008150000040500105c000000090000200180c00000c0080a002000170090060380f818000000000030000500e0250260140e01e02e020010000000100a00b0380000204100a020000010b4000008110000000500300a01800000006024000000100280400304000405800006030008340000040f01f0180040101300a00000003012004000040000180581302c0083003c01602c0100300000000000004020178000000040000c0040040080500204c0b81002a00c0080600008c0381d012028018010000100001703a0280d82300c0000580002c0000000000e000068040120000381b00800c070170000d00283a004030098060120000500a0000040000000a00005800004030020000060240000b020080010000220000200003800c02803000000000000020d40280600604c000290020040a80e00c0000501f000028008030020180380000a0000000400a014030290660001200c00200c0000008601c0b00b00c1180902100e000020050000640000101000c0180000a00002800008064000080000000001800803c11005006000018050160000f8110020040083c0040000300201404c1f8020000180280300e02c0a033000008080000060000200000000c0700e02602810029014068000020020100000b0360080001d0540000c8020000480180800c000000010220940380000a088000180020000001900601c0000c0120041f018cbd905250f4f6314943d3d0c5250f2e4314943a75924310e3f6550c43ab1894310e5f6550c43b31894310e9f6550c43c7d954310f8f6250c43a71894310f8c6250c43a31894310e9f6150c43a71814310f1d4394843c750e5110e6e62944439b58a5110f1d43540439bd895010e6c62540439dd855010e746154043d3d8953d0b1e5350e42a798f4290a9d63d0a4297d8d5190a5c63546429798e5090a5d6394242ab98b5390b1f5394e42ab9885390ab66114e42ad5845390b375194642a7d8d5190a9c6354642a798c5190a9d6314642a798f5090a9d63d4242ad987
  | 7 => 0x26d02315b1a0a2c049a2d9ec1d880d94196a8040cf1cea6b1701821d78e79948fe24b172a501ae18085624c89115300019c162a72232a911869cb06500ca40a3da398e20770000000458001d415e80013f8a788700025c2582388001d91ac20c9ef29280004621a1fa80000017e00000020a0000a480027b9daa8e9fb0600000468c90ac0730988370710e980010205a0e314698c19f0b9a869b383623113519b1f2a3796f21927e8bf24f0799c80a31d51cc8758019bc00017205387f8b096e00000000000000025f872a4104d890a78896a6e0000b28b485800023308f0da11f8f293694e9848b78260af95a05b93d88480015911e90310383682100018a00000003ca671111a58001712111ed05f1918ad10f16b05080001483294f9560f3132168a4a15180000025ea0022310e9b09219129c51fe28f9ad26893b93900000000024200023e8f90d81600188000000d300015780023d1860648ef8000660a202b80000004b0610000001d99ca0be0000002510180001e78d701783d01d86f15280028a84890d08aa2b80024321e28d9908d8a0680000029480016ca8701a8000c88000d60002968000b10a69a509f266a900ee8000f60000d289a94b8000079012820001bf0000749c59d80002152120bda5905500002f8c99af915a64a8c25099f80009c28b135a4185711a14d98b80020d8011061a38000b32890c191809b8a58a929b8cd9a127e06e0ae2630002040000000000002531ac96185693e112179a3b866a6b8000000000fa81a1349b2800052a8191f0000001842278c48779b58000f52449620000630000000000000000001be83f0000002699df030151047000000000000173a8a1328310001dea2089b25b00001fa9aa9d99300000021411780000000028529d2659071cc04e13700000021d8e61a91f10948e021285c27a0bb9e4a108a10808c4148a499f70fd88ba22a2a8061171301d01409458108938161fa1c01b7a3000300926008223503308d15084a80700a9ee114059a289c917b22e80024006b0000e422114b22800002d1dc00005789600000011d8b41f417d8e89ea20c01e92385a97710a01e0e58dfa6fa8096d92e11c91b9160c11e229900f85029b17692b2321679250281a78001989b61740001571041a290b85c8f72248000002180f21871961a329c1b7071a1592f985a429d326a91912882ca769a48ea9b509300004ea5c98509e0d5111a1c9bd8840d42708d78490322978cc29213110f94a8002368ee2462252038f3a0a80024c0000700c500000023580b8691fea8c80000009d0f58000000001c180000002080006a00000000005480000011a9cf81c0e50d22761e30130b803b9c0a2d19e8fd04791497a9420e114601b00003aa888278000001ce15a9540000000ff14100003e8921de198283290a4898
  | 8 => 0x22623720e00e0122479cf042a6d8c59318000000f7a741fd8d39b8a270358001d71f4a3a800000179221a838000000f10619049d180019c9761c30b620f2931e896b899989a91a95a2426f28626389e88c02898106b9ed92c99985419a2008db8e803b23a14000025595f1eb81d2032798000bf8a99588449308390d18001e802da8d1c41ba8000640001f7a4d8dc8001b120b07a0000002481910b39c685d82e07510c01f1c21bb9bd0088000002971a20bc80522225d2061f39d38318248008a384312da051bc82428280000026c16925793422022e26914303814c0c28ed0000000000001968918338941c79001f00000901c280020200d26791c0001922878001a68000001801670099b911383f8001a00000699a880027c8000001cb99580c19014517c86d21880000020927fa7f00029c8fb27b0971c3842289a98a4f9a726621f9098001b99ef98903d94e00027d8000218dd87d9978fe9e280013d0a094a22f9698e918f92327c0002999df8c318a87d1ff2171ae8c79a80819c61249559551ab25492d18300000009f8ec85e80028ba6210a94f04513996c10b000142a790628caa0d1580001081660af09a02a17199b975a3f25d9611f194980015c80027a80004028420f8c721f15d0898b208fa2c9bb0a2829a651af0be8eb12725701b860a9804fa0828597a0ab80019292c0c607b29a27002905b1e39ee88ca392848de08600a0e49d092794c93b13c99e11d000202885a6e82201422b0ac8a505e1fd04c1330688348158398680df0001da2541fb9ca93ea7280016697880002592017c0b5a59a1ea1b80018d8b90001f8a7d00209c8000fc9e19548002451089539be1cd1e08480b523c8559ec80013c25f27480013a2528c3a550001381ad9b19652119e9a3396e9bf80010900004a225892a3098780015d9152609b40e288d80000005886f92299904414780024b8dc0b016d23600e91301100012e886a1791b18f1fc8268f899397f86c8c69389490cb20181706224e83a1aa83c0bb07e1b81aa1290201940892801d29c71598a01261829e41708510059eb004a2f006a1697e92112426125e0e70fb8f69e68000aa8521609b690093f175213a0b89586d9268882318379a98c801c9b00951108128f1887a13165a3e00006725383e0ba8001882680000ce9e587827806780010d8eb93a81984d0aa000073a6180000000012a88e8001b200025ba56a4907ca3f8f000002e9c98db2161aba718000000119639dd8350001680ba002a1012988e0410e08a81ba24d136294000072038a09825022879105a071d619d87695fa4723c275902a268bd06c06ea45a3b04f1971c12629438ae90503417f08507e9db0000c226a0d90ca29502f02aa2a010030956a520000fa0000001481338000c00000001259b48831470c091000f1f98ce
  | 9 => 0x1d692f27317b96a251907800000000000183a5a0002560b68ec0000000fc0190e1a710001f32770b88709648000d48d58001630000da98e0a611687a8001a600b06580000017819a87623806380000024408100021c07c1f58cf80025aa29a8e0001d10f99f61209e626c8408a40e69c89a400000000007b8001f20d009d8000e395b9889e92439441951dd0002810001cda14a048dd0de9ff9520bc05fa3418c81397d28815e1f80d99199dc9fc0788
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x98d0c7255232cc686392a81966343dd4420cb31a18e4b1ca918e0e54189438c686392a819463431d1520ca31a1aea2106518c8c72593318c60ebb4a998c638359252cc631a18e4aa08698d1870550434c616392c828263831506250c31a18e8a906418e8442584320c646392c998863431cd6510b21a18e8b286590e0e6310a50c87073206528643439ce5310921a54e12988490e0e6510a32486873ac8419243439d2540c921a94e12a06490f085310b50487842a065a8243c210832d4121a54ea210a090f0b5310850487842988428243529d43214121e16a8190a090f08540c850486a539e8428243589c74214121a54e9990a090d6271cc850487842146428243c29083214121e1084190a090f2042c8450487a019642282434a9d22114121a94e7108a090c4c7258e5408616392c929843a89086048421d84643024210d0c7354842d0246392c7a0e81139cb6354640c18a631286a050e72d4c425028739ea42128183994420c940e0884196a2a05247250c51503822106428a81231c963d0540c1ac629682a0615631474150307ba0c4a9881831d06254c40a18e4a9c862050c7254c4310286392a721081431c95310840c1eca210642050c7254e4110306a9cc520881431c95310440a18e4a9e802050c7254d4010306a98c4a00818554c6150040c18a8312879850c7454832cc246392c998e61439cb5410e3085ce5b22a31850c7258c544c3062a0c4a1a61439cb540c930a1ce9a90649850e75108324c38221065a8a61511c94314530e0884190a29848c72593314c20ebb0a998a618359052cc530c2ac828e629860c63189540c307b98c4aa061831cc6255030a18e4aa6861850c72550430c286392a919061431c9540c830a1eea210641841f76552310c286392a91886183552628c430a18e4aa0621850c72553300c20e3b2a898061431c9544c030c1aa8312601861554185300c286390a819241439d4420c920c1cca2106490704420cb51483822106428a418a1506048520c90a6302429050c735944208216bb0a621041495c45310820b40e2b00841050c745943208226bb0a819041515c4540c820b80e2b00641060c63109510830632064a88418398c4294020c1cc8194a01044c7258e54c4216392c929e21431cd5210b10a18e8a90658844c7258c5484216392c829c21439cf5210a10a1ce9a90650860e6498f5244306320c629221439cb5310910a1ce7a90848850e72d5032442873a6a419221439d4420c910a18ea210648860e6510832443063288419221831906394810c18c831aa408628641815204324318c0a9021981846054810a18e4a98840850c735484204286392a819021431d1520c810a1eea210640850d751083204307b28841902183594420c810a4aea2164208545750cb2104314b288410021925943208010
  | 1 => 0x60b42815671fc4aaa49b0dc06e230652e421e938247626a65b8322609da0746d8dd62b3182696a044db0178c7028ec807735820d89f108e4149000361a2cd003581c005c0593ad437844a8a521a88c6722cb4d148150b09060057955167d001f87e24560012485132d826ab3ab114e8c54b2da4cc220d8041e0c024689e6ea901aad002c9222f5c96928571a8a12a1a63000d4000004146000000000001c0010e291f1c400da3698112000e82d9e00000800082008008aa815b55681b2f124ca0027aece08858000a0c56480000003d800b89624000460065088f40025a1174be000f17ed70023d0c333997c826100001300034a0000006f8011c8d17000004a2983c00006400058c10000000ae5b81c8ee22db7940313e3640ce153270ce790f9a0cc625e8a8a25601870b03a29190f0172e80c06158103c0100000ac011000400000b0080a300180c5a0301004ae38068000003180100804060180000000040006000680620050000c0100004080b018180205008000603000140c040380c7a000600012021252671d905250ea338ec62928783d946250c43c1eea3128621d0c7250e5210e8639287288878350e6294443a18e4a1aa021e0d431895010f0aa18c2a8087439cb5394e42918e6b0ca42148e739825210a87396a92a465835944310832a4ae3328841948c74586520ca473a4c129065315c76510832b0ce3b28841958571d94420cac338cca21065615c66510832c1aca328841950d75984420cb42b08c22106543dd56010832b0ee2b00841958471580420cac3388c021065615c4601083291aec214a21970442544510ca473b084a8065a110b6154032d088430aa01968442984500cb42212c22806583dd06254f41c18e8312a7a0d0c7254e43d0686392a621e83431c95390b41a18e4a9885a0e0f6510832d0707298c4a1c83431c95310a41a18e6a908520e0d651083290646392c7a0c838358e52d0641898e4b18a0a0d0c7354842106c2b888419083231c963d0441c18c6312a998e0f7318954cc706398c4aa663431c954d0f31a18e4aa087
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xa1a400120ad2018b384c4b000a0681dd46250c43a048250c6154043a0681dd06254f41a0681dcc625533180c8759252cc631a048258c51d0540a0681dd06254c40a048254c615004080c8759052cc530a048259051cc530a0681dcc625503080c87552628c43080c87550624c030a0482550614c030
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
  | 2 => 14
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (6+((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s0K6 (788+((h/14+packedAt s0K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s0K5 (27286+((h/296+packedAt s0K5 (24030+(h % 296)*11) 11) % 1421)*11) 11
  | 4 => packedAt s0K4 (55826+((h/446+packedAt s0K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s0K3 (11798+((h/75+packedAt s0K3 (11123+(h % 75)*9) 9) % 273)*9) 9
  | 2 => packedAt s0K2 (860+((h/4+packedAt s0K2 (840+(h % 4)*5) 5) % 17)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffff81ffffffffffffff0fffff
  | 2 => 0xfff03fff81fffffffe07fe07ff03fffff38e3f
  | 3 => 0xfffc07ffe03f80ffff83ff81ffc0f80fcf3cc
  | 4 => 0xf000007ffffc000fffffc0001ffff000ff03f0
  | 5 => 0xffffff800000000fffffffffe0000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x121105109048920200594a8a254510aa0534d5
  | 2 => 0xa4a48a290c912545960294454a22ad54728a2a
  | 3 => 0x88c2934a243a4159aaa8275113a88e06b8d34c
  | 4 => 0xce8b2c744920766ecd34c1861cf3c418df03b0
  | 5 => 0xf0c307871c3878f71c739e780c30860efec00
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0ccc0c0c0fcc0ccc0ccc0c0c0fcc0ccc0ccc0c0c0fcc0ccc0ccc0c0c0fcc0ccc0ccc0c0c0fcc0ccc0ccc0c0c0fcc0ccc0ccc0c0c0fcc0ccc0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37049
namespace PEqualNP.Outside.L_meta_37049
open PEqualNP.Outside.L_meta_37049.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1450a802b4e000005200800388d0221a14318486d289087cb91244c00b0000d00003c01e2c00000005418000040260084e80002002c0e005000000c8c1c082440100680000e103800204100ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21ee21fd21fc21ec21f421e421ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x40f80e001cc4a181909c7a331301cd8030117400110f988a219111f8525b0e990de05001b8d4611b1ec34711e1dc72683e96814132300046001b9d4e04e0011450172494cae66001d8f2002580074000419cb80026010a0060f0bc000000100a4121883048001f000846d0000076590008440000786c88651a9e8860d17000822a058d0386b000b060001f800a814001a4be013c0b4bc15390589e001c120ac00159341258239fcc6553a181004a03808100098084080283818501000504810004828204819101850000000486050001190302870280060b0a5b94b43b6a96877651d0eeaa3a1db94a43b6a9487765190eeaa321e750c43af29e855d53d0aeca3a15d54742bba8a85745150a7ca9994f55332bb28e657551ccaeea2995d14532af29e835d53d06dca5a0db54b41b7a92836c525067ca998cf55331b7296636d52cc6dea498db14931bb28c436e51886cca310f948421b728843e651087ce8210f990421f2a0843e441087ce6210f98c421f298843e431086eca410f994821f3a1043e642087ca8410f910821f399043e632087ca6410f90c821f3aa043e654087caa810f915021f3a9843e653087caa610f914c21f3a1843e643087ca8610f910c21f3a8043e650087caa010f914021f210e81e421902bea6a05714d40b7a92816c52502eea2a05d14540f210a815e53102baa6205b94840b6a90817651102eaa2207908440f210e61e4218c27ea8984f15130b7a92616c524c2eea2985d14530f210a613e540c27aa8185b94830b6a906176510c2eaa2187908430f210e417651882eaa31079086209faa2413c54482bea6905714d20bba8a417451483c842907908420f210e216e52842daa50879086109faa2213c54442bea6885714d10b7a92216c52443c842887908410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1200189b00000080161c800f801900119d000a82800d001d88159e000000000008800000000015000000000011020001800c05a08b830000000793948b002180070500040d8f0109000616800000001800001f899c038c9b80001280109a8e9f00100e211e931a170a142004868000001980000017808004043000e180010038081040800100004009918552d0e646254743991855290e646254643b198f41086c563d0421a999331086a564cc421b198f42086c563d0821a999332086a564cc821b198f54086c563d5021b198e54086c56395021c955054086a664d4c21a959353086a66494c21a959253087455314c2199997430866565d0c219999643086656590c21e150c43086a76454021a919150086c76354021b118d50086a66414021a959050086c66314021b158c500866661d49409998b515026665085409919421503475308540d114c2150264615484099189511026765084409959421103465308440d154c211026661d49309998b514c266650853099194214c3275408530c9150214c264615483099189510c267650843099594210c3265408430c9550210c3275408520c915021483475308520d114c21482646114910c9d5021443245408510d1d4c21443445308510
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (825+((h/15+packedAt s1K5 (720+(h % 15)*7) 7) % 72)*7) 7
  | 4 => packedAt s1K4 (3827+((h/43+packedAt s1K4 (3483+(h % 43)*8) 8) % 155)*9) 9
  | 3 => packedAt s1K3 (2738+((h/22+packedAt s1K3 (2584+(h % 22)*7) 7) % 118)*8) 8
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffffffffffc0fffffffffffffff0fffff
  | 2 => 0x1fc0fc0fe07e07fff0f07c1f03e0f81ff53267
  | 3 => 0x1fff000fff8007ffff007fe003ff001ff9c387
  | 4 => 0xe000000ffffff83fffff800003ffffe0fe03f8
  | 5 => 0xfffffff00000003ffffffffffc000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc04208002104000001108c21186108c10054ab
  | 2 => 0x4a9631964728aa9cb074351a29a8d15a753265
  | 3 => 0x930c5aaa8a1d352d57085b4852da429cb9c386
  | 4 => 0x1a28a34d1451a1b66aad0210831ce708de0350
  | 5 => 0x1c30c38e1861c63b8cce639ce0108410efa800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37049
namespace PEqualNP.Outside.L_meta_37049
open PEqualNP.Outside.L_meta_37049.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1fffffe07ffffc0ffffc0fffff81fffe78fe3f
  | 1 => 0xe07e07ff81f81ff0f07ff07c0ffe0f81af33cc
  | 3 => 0xff8007fffe001fff007fff800ffff001cfc3f0
  | 4 => 0x7ffffffffffff8000000ffffffff003ff
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc104202304108401108c42946188528c085615
  | 1 => 0x4b18aa451ca2acb074355258a6aa4b14ab32cc
  | 3 => 0x862d348a2874d557085a6b114b4d62294dc370
  | 4 => 0x1451c71051461a6aad0308420c718c71f001aa
  | 5 => 0x1861861c61871b8cce638c6380610841f6a800
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaeeaa0000eeaaeeaaeeaa0000eeaaeeaaeeaa0000eeaaeeaaeeaa0000eeaaeeaaeeaa0000eeaaeeaaeeaa0000eeaaeeaaeeaa0000eeaaeeaaeeaa0000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37049
namespace PEqualNP.Outside.L_meta_37049
open PEqualNP.Outside.L_meta_37049.Model
def s3K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffff03ffffc183fffe0ffffc1ffff0073f3fc
  | 1 => 0xf83ffc1f07fffc3c1ff0f03fe1e07ffaccccf
  | 2 => 0xf003fffe007ffffc01fff003ffe007ffcf0f0f
  | 4 => 0x3ffffff801ffffe000003fffff801f00ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x210011842000200442601118c022310c01515c
  | 1 => 0xa225228c84a90941d0a90a2952145254a4c4c5
  | 2 => 0x454a45106952129c2152a052a540a4a94b0b0a
  | 4 => 0x4a7388294c1b5ceab41888833999c031f00ea0
  | 5 => 0x8c630e318e639f33399ccce0311100c1fea000
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0eaeaeaeaeaeac0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37049
namespace PEqualNP.Outside.L_meta_37049
open PEqualNP.Outside.L_meta_37049.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x5e9800060000233a3800602e00345c84931000128900e56ba2000d181a6c98f000000000d5eab405c50000000320e0d43f223003c5864a003cf82aa768803700104000490b1c66554806c0059f009c0000600081001200102040838004181841408381bda8287785050edca421db54843afa9a855c5350aeea2a15d14542bda8285785050abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d06dca5a0db54b41af29c835d53906f4a120de54241b7a92636c524c6f4a018de54031afa9a435c534867ca810cf55021af298435d53086f4a010de54021afa9a815c53502bca6205754c40b7290816d52102eca2205d544409faa2613c544c2eca2185d544309f2a6413d54c82bca7905754f20af29c415d53882eca3105d546209faa2213c54442bea6885714d10b7a92216c52442bca6085754c10
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
  | 4 => packedAt s4K4 (1875+((h/21+packedAt s4K4 (1728+(h % 21)*7) 7) % 92)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ffffe03ff8307fe0ff87ffff83fe018cfe7c
  | 1 => 0xf81f83ffc1ffff83ff07f8780ffc1ffef3338f
  | 2 => 0xffe003fffffffffc0007ff800fffffff03c3ff
  | 3 => 0x3fffe003ffffff800000fffe003fc03f0
  | 5 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x30c320238411500c642980a8e3a1321884563c
  | 1 => 0x524424448ca11281a522883124a514a8b13285
  | 2 => 0xa1094a891144253410855502494a495302c15a
  | 3 => 0xc59673122875b9dad6b044248e739063dc03e0
  | 5 => 0x618421c31862e6318c66647004201836ba800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37049
namespace PEqualNP.Outside.L_meta_37049
open PEqualNP.Outside.L_meta_37049.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x296821b3b00853bf1c00f007cb4238003052b2c05ab046a8d17262560030b88370ebce007ae8ca20a800063af0a3916001802aa0fb1663c00d4a913006448002004401b00001440b0800198041c0820a6c2810010201bda8287785050edca421db54843afa9a855c5350aeea2a15d14542bda8285785050abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d06dca5a0db54b41af29c835d53906f4a120de54241b7a92636c524c6f4a018de54031afa9a435c534867ca810cf55021af298435d53086f4a010de54021afa9a815c53502bca6205754c40b7290816d52102eca2205d544409faa2613c544c2eca2185d544309f2a6413d54c82bca7905754f20af29c415d53882eca3105d546209faa2213c54442bea6885714d10b7a92216c52442bca6085754c10
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
  | 4 => packedAt s5K4 (1875+((h/21+packedAt s5K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ffffe03ff8307fe0ff87ffff83fe018cfe7c
  | 1 => 0xf81f83ffc1ffff83ff07f8780ffc1ffef3338f
  | 2 => 0xffe003fffffffffc0007ff800fffffff03c3ff
  | 3 => 0x3fffe003ffffff800000fffe003fc03f0
  | 4 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x30c320238411500c642980a8e3a1321884563c
  | 1 => 0x524424448ca11281a522883124a514a8b13285
  | 2 => 0xa1094a891144253410855502494a495302c15a
  | 3 => 0xc59673122875b9dad6b044248e739063dc03e0
  | 4 => 0x618421c31862e6318c66647004201836ba800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0eeeae0c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37049
namespace PEqualNP.Outside.L_meta_37049
open PEqualNP.Outside.L_meta_37049.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001027fd5007fe54007f55007fc54027fd4c01fe53007f54c09fc5301ffd0c01fe43007f50c07fc43027fd4801fe52007f54809fc5201ffd0801fe42007f50807fc42007fcc801fe32007f4c801fc32027fd4405fe51007f54405fc5101ffd0405fe41007f50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc2100ffd4003fe5000ff54003fc5000ffd0003fe4000ff50003fc4000ffcc003fe3000ff4c003fc3000ffc8003fe2000ff48003fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x82620bff1413105ffe809882ffe404c417fea02620bff1013105ffe609882fdf304c417ff182620bff4c13105fba609882ffc304c417ff902620bff8813105ffa409882ffc204c405ff8826202fdc4131017fc209880bfd104c417fa8826202ff04131007fecb90802ff65c8415ff32e4204bf99721007facb90802fd65c8415fe32e4204bf19721007fec990802ff64c8413ff3264203bf99321007fac990802fd64c8413fe3264203bf19321057fea990827fe54c8401feaa64209ff15321007fec790802ff63c8401ff31e4200bf98f21007fac790802fd63c8401fe31e4200bf18f21057fea790803fe53c8401fea9e420aff14f2104ffe8790803fe43c8401fea1e4209ff10f21015fcc59082bff52c8401ff2964200ff54b21057f8a590827ff42c8401ff2164200ff50b2104ff88590803ff32c8401ff1964200ff4cb21007f8659080afd61c8405ffa8e4202ff94721017faa39080bfc51c8405ffa0e4202ff90721017fa839080bfc41c8405ff98e4200fdcc721017fc639080bfd31c8405fe18e4202fd0c721017fc439080bee21c8405fb10e4202ff08721017d84390823ff60c84117fb064208ff9832100dfcc190823fd60c84117eb064208ff1832100df8c190823ff50c8411ff2864208ff54321047f8a190823ff40c8411ff2064208ff50321047f88190823ff30c8411ff1864208ff4c321047f86190823ff20c8411ff1064208ff48321047f8419080bff10c8405fb8864202ff84321017fa2190823f510c8405fe0864200ffd9521005feca9081ffe65484097f32a4200ff59521005faca9081ffc65484097e32a4200ffd9121005fec89081bfe64484077f3224200ff59121005fac89081bfc64484077e3224207ffd5121037fca890803fd544840dfe2a24200ffd8d21005fec690803df63484016fb1a4200ff98d21005fcc690803fd63484017eb1a4200ff18d21005f8c690803dc63484016e31a4207ffd4d21007fca690803fd534840ffe29a4206ffd0d21007fc8690803fd434840dfe21a4202bfd892103ffea490803fe5248401fea924207ff14921037fe8490803fe4248401fea124206ff10921007fe6490803fe3248401fe9924200ff0c921015fec29080bff5148405ff28a4202ff54521017f8a29080bff4148405ff20a4202ff50521017f8829080bff3148405ff18a4202ff4c521017f8629080bff2148401fb90a4202ff88521017dc429080bfc2148405f610a4202fd0852102ffec090816ff604840bff3024201bf9812102ffac090816fd604840bfe3024201bf1812102ffea090817fe504840bfea824205ff1412102ffe8090817fe404840bfea024205ff1012102ffe6090817fe304840bfe9824205ff0c12102ffe4090817fe204840bfe9024205ff08121017fe209080bfe1048405fe8824202ff04121
  | 1 => 0xbfe5150405fea8a8202ff14541017fe82a080ff74150405ff20a8202ef90541017f882a080bbc4150405fa20a8202ff8c541017f862a080bfe2150405fe10a8211ffd814108dfec0a0847fe60504037f3028211ff5814108dfac0a0847fc60504037e3028211ffd414108ffca0a0847fd5050423fe2828203ffd014101ffc80a080ffd4050407fe2028211ffcc14108ffc60a0847fd3050423fe1828211ffc814108ffc40a0847fd2050423fe1028202ffc4141017ee20a080bfe1050405fe8828211fd44141017f820a0803ff65cc4017fb2e6210ff99731025fccb98803fd65cc4017eb2e6210ff19731025f8cb98803ff64cc4017fb26620fff9933101dfcc998803fd64cc4017eb26620fff1933101df8c998843ff54cc41fff2a66200ff5533107ff8a99880afe63cc421ffa9e6200ff94f31007faa798843fc53cc41fffa1e6200ff90f31007fa879883ffc43cc401ffb166200ff98b31005fcc598803fd62cc4017eb166200ff18b31087fea598803fe52cc401fea966210ff14b3107ffe8598803fe42cc401fea16620fff10b31007fe6598803df32cc401ff1966200ff4cb31007ba6598803fc32cc4057eb0e6202ffd4731017fca39880bfd51cc405fe28e6202ffd0731017fc839880bfd41cc405fe20e6202ff8c731017bc639880bf631cc405fe18e6202f70c731017fc439880bfc21cc405fa10e620effd8331075fec19883bfe60cc4037f306620eff58331075fac19883bfc60cc4037e306620effd4331077fca19883bfd50cc41dfe286620effd0331077fc819883bfd40cc41dfe206620effcc331077be619883bfe30cc41dfe986620ef74c331077f8619883bff20cc41dff106620eff48331077f8419880bff10cc405ff0866202ff44331017f82198803ff654c4017fb2a620dff99531025fcca98803fd654c4017eb2a620dff19531025f8ca98803ff644c4017fb22620cff9913101dfcc898803fd644c4017eb22620cff1913101df8c898837ff544c419ff2a26200ff55131067f8a89880aff634c41bffa9a6200ff94d31007faa698837fc534c419ffa1a6200ff90d31007fa8698833fc434c401ffb126200bfd8931007dec498802ef624c401ff3126200ff58931007f8c498802fc624c401f63126200bb1893106ffea498803fe524c401fea92620dff14931067fe8498803fe424c401fea12620cff10931007fe6498803df324c401ff1926200ff4c931007ba6498803fc324c4057fb0a6202ffd4531017fca29880bfd514c405fe28a6202ffd0531017fc829880bfd414c405fe20a6202ffcc531007ee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ff10a6202ff0853105ffec09882eff604c417ff3026201bf9813105ffac09882efd604c417fe3026201bf1813105ffea09882ffe504c417fea
  | 2 => 0x320bff8a81906afe630c831ffa986400ff94c32007faa619063fc530c82fffa186400ff90c32007fa861905ffc430c8337f3106418ffd4832007fca419003fd520c831fe2906417ffd0832007fc8419003fd420c82ffe2106400ffcc832007be6419003fe320c801f71906400ff4c832007ba6419003ed320c801ffb086416ff98432015fcc219003fd610c8017eb086416ff18432015f8c219063ff510c82dff2886416ff144320bffe821905bfe410c82dfe2086416ff8c4320b7bc621905bfc310c82dee1886416ff884320b7dc421905bfc210c82df61086415ffd80320adfec019057fe600c8037f3006415ff580320adfac019057fc600c8037e3006415ffd40320affca019057fd500c82bfe2806415ffd00320affc8019057fd400c82bfe2006415ffcc0320afbe6019057fe300c82bfe9806415f74c0320aff86019057ff200c82bff1006415ff480320aff84019057ff100c82bff0806415ff440320aff8201900aff6554401ffb22a200bfd91510a7fcc8a880efe6454401feb22a214ff1915101df8c8a8813ff5454409bfaa2a204ff95151027faa8a88037d5454409fe2a2a200ffd8d51005fec6a8803fe6354401feb1aa200ff18d51005f8c6a8813ff5354409ff29aa204ff54d51027f8a6a8853ff4354401ff21aa200ff50d510a7f886a8803ff62544017fb12a200ff98951007fac4a8803fc62544017e312a204ffd4951026fea4a8813fe5254409fea92a200df54951027f8a4a8853ff4254401ff212a200ff509510a7f884a8803ff3254401ff192a200ff4c951007f864a880aff6154405ffa8aa204fdd4551017fca2a880b7e5154405fe28aa202df14551017e8a2a880bff4154405ff20aa202ff10551017fc62a880bfc3154405ff10aa202ff0855109ffec0a884eff6054427ff302a201bf9815109ffac0a884efd6054427fe302a201bf18151027fea0a8813fe5054409fea82a204ff1415109ffe80a884ffe4054427fea02a213ff1015109ffe60a884ffe3054427fe982a213ff0c15109ffe40a884ffe2054427fe902a213ff08151017fe20a880bf71054405ff082a202ff4415109fea20a880bfc1054401ffb2a8200bfd9541097fccaa0812fe6550401feb2a8200bf59541097f8caa0812fc65504057fb228203ffd514101ffca8a080fbe5450407feaa28200ef5514101ff8a8a0803ff63504017fb1a8200ff98d41007fac6a0803fc63504017e31a8212ffd4d41007fca6a0803fd5350425fe29a8203ffd0d4101ffc86a080ffd4350407fe21a8200ffd8941005fec4a0803fe6250401feb128200ff18941005f8c4a084bff5250401ff2928200ff54941097f8a4a080fff4250407dfa128203ff9094101ffa84a0803bd4250407fe2128200ffcc941007fc64a0803fd3250401fe1928202bfd8541017fea2a080
  | 3 => 0xeb06641abf583320d7f8c199006fc60cc835ffa86641aff943320d7faa19906bfc50cc835ffa06641aff903320d7fa819906bfc40cc835ff986641aff8c3320d7fa619906bfc30cc835ff906641aff883320d7fa419906bfc20cc835ff886641aff843320d7fa219906bfc10cc801ffb2c6400bfd963210ffccb19012fe658c801feb2c6400bf5963210ff8cb19012fc658c801ffb246400bfd9232107fcc91900efe648c801feb246400bf59232107f8c91900efc648c843ffaa46420ff95232007faa919083fc548c8377eb1c6421ffd4e32007fca719003fd538c843fe29c6420ffd0e32007fc8719003fd438c841fe21c6415bf98a3210ffea519003fe528c801fea946421ff14a32107fe8519003fe428c801fea146420ff10a32007fe6519003df328c801f79946400ffd86320fffcc31900afe618c801feb0c6400bf586320fff8c31900afc618c843ffa8c641fff946320fff8a319083ff418c83fff20c641fff106320fffc631907fde318c83ffe18c641ff70c6320fffc431907ffc218c833ffb046419bfd82320cffcc119006fe608c833feb046419bf582320cff8c119006fc608c833ffa846419ff942320cffaa119067fc508c833ffa046419ff902320cffa8119067fc408c833ff9846419f7cc2320cffc6119067fd308c833ee9846419ff0c2320cffe4119067fe208c833fe9046419ff082320cffe2119067fe108c833fe8846419ff04232007feca99002ff654c83dff32a6404bf99532007faca99002fd654c83dfe32a6404bf19532007fec899002ff644c83bff3226403bf99132007fac899002fd644c83bfe3226403bf191320f7fea899077fe544c801feaa2641dff151320f7fea699003fe534c801fea9a641eff14d320effe8699003fe434c801fea1a641dff10d320f7fea499003fe524c801fea92641eff149320effe8499003fe424c801fea12641dff10932007fe6499003ef324c801ff1926400f78c932007fec299002ff614c801fbb0a6400bdd85320e7fcc29900afe614c801feb0a641cff18532015f8c299003f4614c8057a30a641effd45320e7fca299073fc514c83bffa0a641cff905320e7f88299073fe314c839fe18a641cff885320e7f8429906fff604c8377fb02641bff9813200dfcc09906ffd604c8377eb02641bff1813200df8c09906fff504c837ff282641bff541320dff8a09906fff404c837ff202641bff501320dff8809906fff304c837ff182641bff4c1320dff8609906fff204c837ff102641bff481320dff8409906fff104c837ff082641bff441320dff82099003ff650c8017fb286418ff99432025fcca19003fd650c8017eb286418ff19432025f8ca19003ff640c8017fb206417ff9903201dfcc819003fd640c8017eb206417ff1903201df8c819063ff540c82fff2a06400ff550
  | 4 => 0xfbe5490807feaa48400ef5524201ff8a921003ff6390801ff31c8400bf98e42007fac721002fd6390801fe31c842affd4e42007fca721003fd5390855fe29c8403ffd0e4201ffc872100ffd4390807fe21c8403bf98a42157fea521003fe5290801fea94842aff14a4201ffe852100fbf4290807f7a148403ff10a4201fd88521003ff6190853ff30c8402bf98642007fac321002fd6190853fe30c8402bf18642157fea3210a7fe5190853fe28c8403ffd064201ffc832100ffc4190853ff18c8429ff0c64214ffc43210a7fc2190851ffb048428bfd8242147fcc121006fe6090851feb048428bf58242147f8c121006fc6090851ffa848428ff94242147faa1210a3fc5090807ffa048403ff9024201ffa812100ffc4090851ff9848428ff8c242147fa61210a3fc3090851ff9048428fbc8242147fc41210a3fd2090851f69048428ff08242147fe21210a3fe1090851fe8848428ff04242007fecaa1002ff655084fff32a8404bf99542007facaa1002fd655084ffe32a8404bf1954201dfec8a100fff5450807ff2a28403ff5514201ff8a8a1003ff63508017fb1a8400ff98d42007fac6a1003fc63508017e31a8427ffd4d42007fca6a1003fd535084ffe29a8403ffd0d4201ffc86a100ffd4350807fe21a8403bfd894213ffea4a1003fe5250801fea928427ff1494201ffe84a100fef4250807ff2128400ef9094201ff884a100fbc4250807f62128400ffd8542005fec2a109bfe61508057f30a8400ff58542137f8c2a100afc615084fffa8a8426ff94542137f8a2a100fff4150807dfa0a8403ff9054201ff882a109bfe315084dfe18a8426ff88542137f842a1097ff605084b7fb028425ff9814200dfcc0a1097fd605084b7eb028425ff1814200df8c0a1097ff505084bff2828425ff5414212ff8a0a100fff4050807ff2028403ff5014201ff880a1097ff305084bff1828425ff4c14212ff860a1097ff205084bf79028425ff8814212ffa40a1097ed205084bfe1028425ffc414212ffc20a1097fd105084bfe0828400ffd9732005fecb99093fe65cc8097f32e6400ff59732005facb99093fc65cc8097e32e6400ffd9332005fec99908ffe64cc8077f3266400ff59332005fac99908ffc64cc8077e3266424ffd533211ffca999003fd54cc847fe2a66424ffd4f32007fca799003fd53cc849fe29e6423ffd0f32007fc8799003fd43cc847fe21e6424ffd4b32007fca599003fd52cc849fe2966423ffd0b32007fc8599003fd42cc847fe2166400ffd8732117fcc39900afe61cc801feb0e6400bf58732117f8c39900afc61cc849ffa8e6422ff94732117f8a39908fff41cc845ff20e6422ff10732117fc639908bfc31cc845ff10e6422fb88732117f8439908bec21cc835ffb06641abfd83320d7fcc199006fe60cc835f
  | 5 => 0x8543197f8c2a180afc6150c67ffa8a8632ff94543197f8a2a180fff4150c07ff20a8603ff10543197fc62a18cbfc3150c65ff10a8632ff0854318ffec0a18c6ff6050c63ff3028601bf9814318ffac0a18c6fd6050c63fe3028601bf1814318ffea0a18c7fe5050c63fea828631ff1414301ffe80a180ffe4050c07fea028603ff1014318ffe60a18c7df3050c63ff1828631ff4c14318fba60a18c7fc3050c63ff9028631ff8814318ffa40a18c7fc2050c63ff8828631ff8414318ffa20a18c7fc1050c097eb2ca400ffd9252187fcc92900efe6494801feb24a400bf59252187f8c92900efc6494809ffaa4a404dfd5252027fca929013fd5494801beaa4a404ff15252007fec729003fe63948017f31ca400ff58e52005fac729003fc6394809ffa9ca404ff94e52027faa729013fc5394861ffa1ca400ff90e52007fa87290c3fc43948097f314a404ffd4a52026fea529013ef5294809b7a94a404ff14a52027d8a5290c3ff4294861fe214a400ffd865217ffcc32900afe6194801feb0ca400bf5865217ff8c32900afc6194809ffa8ca404ff94652027f8a3290c3ff419485fff20ca42fff1065217ffc63290bffc319485fff10ca42fff08652177fec1290baff609485dff304a401bf98252177fac1290bafd609485dfe304a401bf18252027fea129013fe5094809fea84a404ff14252177fe81290bbfe409485dfea04a42eff10252177fe61290bbfe309485dfe984a42eff0c252177fe41290bbef209485dff104a42eff48252177da41290bbfc209485dff884a42eff84252177fa21290bbfc10948097fb2aa400ffd9152005fec8a90b7fe64548077f322a400ff5915216ff8c8a900efc6454809ffaa2a404ff95152027faa8a9013fc5454801ffb1aa400bfd8d52007fcc6a9003fd6354801fe31aa400bf18d52027fea6a9013fe5354809fea9aa404ff14d5216ffe86a9003fe4354801fea1aa42dff10d52025fec4a9013ff5254809f7a92a404ff94952006fca4a9013fc5254809be292a404fb1495216ffe84a90b7fc4254801ffb0aa400bfd8552167fcc2a900afe6154801feb0aa42cff18552015f8c2a9013ff5154809bfa8aa404ff94552027f8a2a90b7ff4154859ff20aa42cff10552167fc62a90b3fc3154859ff10aa42cff0855215ffec0a90aeff6054857ff302a401bf9815215ffac0a90aefd6054857fe302a401bf18152027fea0a9013fe5054809fea82a404ff1415215ffe80a90affe4054857fea02a42bff1015215ffe60a90affe3054857fe982a42bff0c15215ffe40a90afef2054857ff102a42bff4815215fda40a90affc2054857ff882a42bff8415215ffa20a90affc1054801ffb2c8400bfd9642157fccb21012fe6590801feb2c8400bf59642157f8cb21012fc65908077eb248403ffd524201ffca921
  | 6 => 0x9be284a63affd02531d7fc81298ebfd4094c75fe204a63affcc2531d7be61298ebfe3094c75fe984a63af74c2531d7f861298ebff2094c75ff104a63aff482531d7f841298ebff1094c75ff084a63aff442531d7f82129812ff6554c01ffb22a600bfd91531cffcc8a980efe6454c01feb22a639ff1915301df8c8a9813ff5454c09ff2a2a604ff55153027f8a8a9812ff6354c09ffa9aa604f7d4d53027fca6a98037e5354c09fe29aa604df14d53027b8a6a98e7ff4354c73fe21aa600ffd8953005fec4a9803fe6254c01feb12a600ff18953005f8c4a9813ff5254c09fe292a639ffd09531cff884a9803ff6154c017fb0aa638ff98553015fcc2a9803fd6154c71fe30aa602bf18553027fea2a9813fe5154c09fe28aa639ffd05531c7fc82a98e3fc4154c71ff18aa638ff0c5531c7fc42a98e3fc2154c6fffb02a637bfd81531bffcc0a9806fe6054c6ffeb02a637bf581531bff8c0a9806fc6054c09ffa82a604ff94153027faa0a9813fc5054c6fffa02a637ff901531bffa80a98dffc4054c6fff982a637f7cc1531bffc60a98dffd3054c6fee982a637ff0c1531bffe40a98dffe2054c6ffe902a637ff081531bffe20a98dffe1054c6ffe882a637ff04153007fecb21802ff6590c6dff32c8604bf99643007facb21802fd6590c6dfe32c8604bf1964301dfac92180fff5490c07ff2a48603ef9524301ffaa921803bd5490c07fe2a48603bf98e431b7fea721803fe5390c01fea9c8636ff14e4301ffe872180fbf4390c07efa1c8603ff10e4301fb88721803ff6290c01ff3148600bf98a43007fac521802fd6290c01fe3148636ffd4a431b7f8a52180fff4290c07fe2148600ffd86431affcc32180afe6190c01feb0c8600bf586431aff8c32180afc6190c6dffa8c8635ff946431aff8a32180fff4190c07ff20c8603ff106431affc63218d7fc3190c6bff10c8635ff086431a7fec1218d2ff6090c69ff3048601bf982431a7fac1218d2fd6090c69fe3048601bf182431a7fea1218d3fe5090c69fea848634ff1424301ffe812180ffe4090c69df2048603ff5024301ff8812180fbc4090c69ff9848634f7cc2431a7fc61218d3fd3090c69ee9848634ff0c2431a7fe41218d3fe2090c69fe9048634ff082431a7fe21218d3fe1090c69fe8848634ff04243007fecaa1802ff6550c67ff32a8604bf99543007facaa1802fd6550c67fe32a8604bf1954301dfec8a180fff5450c07ff2a28603ff5514301ff8a8a180eff6350c67ffa9a8600ff94d43007faa6a18cffc5350c07ffa1a8603f7d0d4301ffc86a1803be4350c07fe21a8603ef10d4301fb886a1803ff6250c017fb128600ff98943007fac4a1803fc6250c017e3128633ffd494319ff8a4a180fff4250c07fe2128600ffd8543005fec2a18cbfe6150c057f30a8600ff5
  | 7 => 0x5010018008020080180300600a004000190020100080500c014008200120000001f00a0000b00c0000000100000200001801000004010030000280680705a0140900302400401005000060050010701541980b00400008800010018010220040040080000e018168010100000180301002c000050000600180d0220040000f00602c05008008018008000160000080005a00c1901400600c0c80000a0300a06002c00401801000060168040040000180202a014030030080100c0000020000180100807c080000340100600500001c01000008010000000120480280000a0480500100e004000020060000080302a03804010000004028170400100380300600800006002000000120120840000b022024048120000840b00700200c1181200400c000000080240880f02603400000010000068000000501380001a008000380000042a8030060380184200001000016000000077fb2aa803bfd915401ffea8aa013bf5455007ff2a2a803df9515401ff8a8aa00f7c5455007de2a2a803cf15154007fec6aa002ff6355001ff31aa800ff58d54007f8c6aa002fc6355009ffa9aa804ff14d54026f8a6aa00fff4355007fe21aa803ef10d54007fec4aa002ff6255001ff312a800ff58954007f8c4aa002fc6255009ffa92a804ff14954026f8a4aa00fff4255007fe212a803ef10954007fec2aa002ff615507dff30aa802bf98554007fac2aa0fbfc61550057e30aa804ffd4554026fea2aa013fe5155009fe28aa803ffd055401f7e82aa00ffe4155007fe20aa83eff8c5541f7f862aa0fbfe215507dfe10aa83dffd81541edfec0aa0f7fe60550037f302a83dff581541edfac0aa0f7fc60550037e302a804ffd4154026fea0aa013fe5055009fea82a83ddf54154027f8a0aa00fff4055007dfa02a803ff9015401ffa80aa0f7bd4055007fe202a83dffcc1541effc60aa0f7fd305507bfe182a83dffc81541effc40aa0f7fd205507bfe102a83dffc41541effc20aa0f7fd105507bfe082a804bf59653007fec9298f3fe6494c077f324a600ff59253005fac9298f3fc6494c077e324a604ffd5253026fea929813fe5494c09feaa4a600df55253027f8a929812fe6394c09ffa9ca604dfd4e53027bea7298135f5394c09fe29ca604f714e531e7fe87298f3fc4394c01ffb14a600ff98a53005fcc529803fd6294c017eb14a600ff18a53027fea529813fc5294c79ffa14a63cff10a53007fec3298effe6194c057f30ca600ff58653005fac3298effc6194c057e30ca604ffd4653027fca329813fc5194c79ffa0ca63bff906531dff883298effe3194c77fe18ca63bff886531dff843298ebff6094c757fb04a63aff9825300dfcc1298ebfd6094c757eb04a63aff1825300df8c129813ff5094c09ff284a63adf94253027faa129813fc5094c0
  | 8 => 0x5e00021eb78cd844cb74a8a0006e4af894c6f807641eab27ce7349aebac24cc5cb027fc5e048c69499c2b47e2c40d142b23168a60000000ba2f43aeb1cad8928bb48fe1aa2d24fa71643ed0605864e0fa8b672cc3278c0e2a463c0baa4de0565943a22c00ea5cccf83286ea67c8f67521b42c22f276a9e21b046a75047891c5ea0e67ea106c5e0720627c034a4f2a229fc5805c0254c781346701fe314b040640004c8ab4a729448207089e4b900887b4640c4415e0006489a0a2c5feaec7b8a287c44923c2d0877c47cd2c45e0000006ce000000000000ce4c9866293c7f65a6a4202eb5a00030408a1886bc5dcb9c3e6af281a68e00029c40a0001ca666d0e930330c7a000ba60a0bd8afc000808bc83466829ca00058c5d0be60002cad0a03c0006b48c22ba5129c67a47206e88ac842c606b0a76948aea55c7d460e732abc47ed108e4cceb7c5a4b2a37a89a94e1e2cea74005e98a74e11c1940ce4e47141f65e22846e27c63ee06aa50c36000b5c8f032cb467cc54a0008780003bc1704040000006a412a0229cc1f0240c629468443888566966c49da61a3c4a0e0920002ead2251800049400000063c0805648ce0000000003400000eeb966304361b857a7e6aa80002fe000a5a6160007da39828a5484e86b879c87e000c1e3ea000000ba00000005001c2794000000c500006d27d80d0196514b1ea30442256c7c18273aac0768a5c3fe85a9802743c68c852a3d8cdacc0504d4030e250aa01c497cc6ead00c0c52000b64560848612a10000000000af489087a10e83e1d27f800000027a0005c4b0686403600c00011000004000060040280282700c00001803000010040040000040280404000c0303a0160080000b00008c0000409c0080381900a004048020320200300302000c018020000000c80002c0002101e00e0000002900200002807030024020010020580000302004c058000280040001600e01c018030220000c00903e0000001c0040601681e0080240180100400c048000000000002e02600001010000000010040260080a0020020100c80602000800003000070010140200e00900200000c138000040100080d0300000200a02a018008090260240080000001c0003c000008000080000600d80100201c030000000040501200400c0a81000601c000070020200081500402806803000000068060180180700100203800800000078090240260080282500004405000038000000010080080280a00001c0500300401c048000000140180103000802015002014028050160440680501801818004004040010100020040780c00000005002034004000090020100004b02a0040680000000007803002004030050060100101d0b203c0000c00000007831028004000060100080280100000001002010000018040280040300
  | 9 => 0x7308ae13a204c284aa62c51eb70146576be204c2e04ea4963029c209ecc85f69ba074a161b60ec8c0c7ebae910186bf28747ee884a38826b8660c6ee32e41a55a2a08109d43d4846c949e0068d32ca285cb260000b40000fe48600066ab16424d34000000a2e000a78000798510c3cb10c585bc8fa34e8aa65e7640b81ac23aaa42f05346f07a6b52b4a16c5245903ecd00646b4c9040000860002e41043a6470cb06d0afa59a9f24c06547b2000876c4e00000000000049e8a8a240008ca96a54e88a6d4a9a6d800026400000007ad360001da00015ac3086684aa940007860000000006140006f433200083ab18000000006562538c2a00099a0000000006ec7aa33c000410818462b20a68ce05449f421cae076635e95aafe34c0000000002f80004b0c6c0009b6000000b0e000960c8024a0be8da93452ed028922700007a0bfc69cd180a448e40c97686245a26c98c0005d40003f082a686286bba00041439e118000000298b36c203ac0000001de3fab9e5403d0c968b07aca4400e000000024000b2c89e0004e028e8d0c82516af041ca7c700bbc000aae2bcc082528fc5666ac61852c042c226bebb2626970a40570592a021202cc26887cc6a50a70a91466cd1a852770468060a7ec040000c6208cf413ec4a1e49ea02815c0004da00aba211eca064aba81e60000009860000003a48b80005f087000064200086828006c1984f093a7dea6e1c86dc0aa5b020e1444ce38a08ea52bdab94d2a5280009be5a83345ec01e5da68c00087200042c37400017ac0031eb4e6b6000c706c016651cada21a0d21ec6b23203621261ce276cc49f688e796000c180002fa124c8a1ea94a00000049cca8776a704603c86faca4bc61fa8a03f22d82228820a6a564f6cbab2e48281620a1403dc7807a238c23216243400013023e5d21321f899242eaccbb03da7043aa1566c86a0000000b22000ad23de8f25308a20009324c25682a64307b6ae24be8d2a04c84000974c66348c0e9088944a863e55661c8bc09a5aa684a9217e3b45f459e4a444432a658000cfc0006081c07e46a625cb7e466000000bea48496e7ec248000180ac6d38000cbc00000000000080a0000001d06ba10840633800024e8228380c4bcc91e5c639aad465c3ce4ca000ace0000000002a407810093836c9526e667600000000072e0304a03e869a4b8d265d85e668aa486322940003787783b63be7f0a3a138202d3a50e90e8e6cca474a620009e886e4587dcae80f081ccd257c0001ba3928c40009ce0000006cc61030c6d69c80008d63f600076255e2d03602ae46e0009aa0008a40002ac994000000aa67b0000832354588a3214e0002e2052b6e07022a2da00000047a0006fc38289cc8e0f60000007540500340000980009260005ae56c2d6000a9e4ae00053c5326229d09
  | 10 => 0x8284b25b64088ea454b58c1c18a74a3904d2d129a2924ab8b6ccee50829ea8ea3c5c890237e82c448c688b2678598ba47726c69acbd02b037cb546524509985a23e4bc47bcae604080c000bfa3b0ce271e00029a000b1a03291a000114000000054000bb842a75e9b4aca5849582102966da92c76ccbe00026ab3a972cf022603899639c67e5ce1a838414a0000004d01901ee44a0000e043ac38be4172218bd2000906438000128668cdc00c75a0ca59c2dc000000c420cc65646c00019235a000bbe8ba000000036b60a58b8273ec02ce686aaf6a206804f84e29d84985caa0c67acfe4fe2e8bde93ec9e7a8258000b8e5ba16e07e99e7d03ba3863d6a005de13c690206000000b127464ecaaa0008121507fe35023c00000022c3188541c670e9784ba418000344184c906a81be26e0000000000000f40000bcb7200085eb28a6c9820002c4396a3619cce827ca5eb8849a9fea8ca9c8067d601058e4c43a80d69a48f8b34aa2000000834000634ccc6442a201a440d240009200000007aecd4896488b3c00018e000000000000000d4240210ac34ca6046000c14000814a145c2b9abf0c067129de1028e24ccab60e47d21aeb562ee0008024d8464000b8403e8b457867275853abd49bcac20003a07e86002364e6bb621670ca66084168c3a08c15899062ea2684ecb47ba336244b3e7f4bc270200092a000caa790000000000356b083f40005d64560004123d293685833a940116a964a233e1dc5f800011a72214268820cbcad161e00c2a60bd6cd60006383808ecabe2007184c6adc00079e45ccb695c5b440e00000004413600081e9642b6048cfa000a4e000bee9d697a3fc710272912d2e2e6a7a4161d63f89b0a6a9f8b5ecde48a9ee69e300aac72825e756364520a80706604000b5009407c0128d4000000000154954aba47243c23005a8dc000b4061e56a2927241760007882fc0008864a64b4be0b66624b488d884028c9e6148c46c0a5722249c430a56e8981d46288e87382ce7e0ad6c645be9fa9d29dcb6a50666ea901106ae2ec19a3ca3100d406ec86322916bf64f4096b80366a828240820a84dc85098e00045292e00000000028891800082e00000000000000037696c000582000000bc0ac8266a12000d0ccd00009c01cc71c008026cacb422384d616417816a000000526a3e5f2420c5a31c000342c7290a5b28040002123e0c886f61a6b62bce5ee0dc54600077a308d3cb0cc54c2497e000a0a1bc1a20f2278220a9800088c324432000cec6508008bec9a2f6d1ea1a77e000bdc782a1e0b00169009f083c692bfe51a558b7a60ac560000004265965b8a3412eb0a1601f4400b8a6f2cc690c0000000000a22a835c3127f236e6de78e5a065a19e0d89a6d20d3054c246d3e6a202cd0400017c25a5523e22d404ac102c88e
  | 11 => 0x9848de6740146fe29071a27e1220003b21e8aee00055400080eb8c726000000cc231a0002c6d285746367c862a01c358a4a7be3060184d46aa480c0c9ec53600018c000000b32000ae477486c066586a540da78ac2c03ac165421a00000000000aea643cc0000000000c8860c260000009505aca84d1c00000000084c5e400002a620698b68000c12a1874400050c000a08214000a8800000014c000b760000002427362287c236800076e00000000000009053e0acb984bc000000c92602b2400000000083600072a0000000000009627ca234352c4c8f41f2ac45506c264c9665fa0000b28cc9a8942260ab09b25e87842aa0f85220fcb92a86caeb30cb82be2dec740de1a4880b009b836a3b812c0000020002b88eecf638e04e1b21fc0e857e000000cb263a00076005c9880008884765fc8c6c8c0b6000c2e000a0673c1d874cbe8a1c1127426604ee2827fa4fcc48922000c3e000502a2a000c1abf49680006e0000b14bf844e17400000060695639402066410c6cab4479a3264ac490262792a4c22e446b38152becc7609c000000000422ade75ca7437258a428cf24b6370c9c748004830
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf3018d21006de3018d21006dd3018d21006dc3018d210fdde7618d21006de7618d210fcde7618d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d210b7ce2118d210b7cc2118d210b7d42118d21006df6018d21006de6018d21006dd6018d21006dc6018d21006df7518d21006de7518d21006dd7518d21006dc7518d21006df7418d21006de7418d21006dd7418d21006dc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d210b6df7218d210b6dd7218d21006df5218d21006dc5218d21006df4218d21006dc4218d210b6df7118d210b6de7118d210b6dd7118d210b6dc7118d210b6df5118d210b6de5118d210b6dd5118d210b6dc5118d210b6df4118d210b6de4118d210b6dd4118d210b6dc4118d210b6df2118d210b6de2118d210b6ce2118d210b6dd2118d210b6dc2118d210b6cc2118d210b6d42118d21006df7018d21006de7018d21006dd7018d21006dc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d21006df4018d21006de4018d21006dd4018d21006dc4018d21006df2018d21006de2018d21006dd2018d21006dc2018d210b6df1018d210b6de1018d210b6dd1018d210b6dc1018d21004ff7694d21004fe7694d21004fd7694d21004fc7694d21006df6394d21006dc6394d2103f5f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21006df6354d21006dc6354d21004ff7690d21004fe7690d21004fd7690d21004fc7690d21006df6390d21006dc6390d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d21006dc6350d2120cfe7694921006df6394921006dc639492103f6f529492117fe42194921024ff7654921014fe7654921164fd7654921014fc76549210067f65549210267c6554921006df6354921006dc6354921005f77154921015f47154921167e42154921204fe7690921006df6390921006dc639092101cff7650921014fe7650921134fd7650921014fc7650921006bf645092101ebc6450921006df6350921006dc6350921005f77150921015f47150921014fe76cc921014fc76cc921006df63cc921006dc63cc921116ef62cc921015f671cc921005f571cc921117e421cc9210b4fe768c9210fedf638c921006dc638c921114ff764c921014fe764c9210e4fd764c921014fc764c921006df634c921006dc634c921005f7714c921015f4714c9210fcfe760c921006df630c9210b6dc630c9210b6ef620c9210b7e4210c921015f676c8521016f676c852100cf676c8521007d763c8521006f663c8521006f463c8521007d463c8521006d463c8521015f672c8521017e672c8521016f762c8521017e762c85211fef760c85211fef560c8521
  | 1 => 0x9121004ff705912100cfe7059121004fd705912100cfc7059121004ff7655121004fe7655121004fd7655121004fc76551210067f65551210267c6555121006bf645512101ebc64551210373c5455121024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d21006df53d8d21006dc53d8d21006df43d8d21006dc43d8d210fcff71d8d210fcfd71d8d210fedf31d8d210fedd31d8d21004ff70d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006df30d8d21006de30d8d21006dd30d8d21006dc30d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210ffce21d8d210ffcc21d8d210ffd421d8d21006df60d8d21006de60d8d21006dd60d8d21006dc60d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d210fedf72d8d210fedd72d8d21006df52d8d21006dc52d8d21006df42d8d21006dc42d8d210fedf71d8d210fede71d8d210fedd71d8d210fedc71d8d210fedf51d8d210fede51d8d210fedd51d8d210fedc51d8d210fedf41d8d210fede41d8d210fedd41d8d210fedc41d8d210fedf21d8d210fede21d8d210fedc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d21006df20d8d21006de20d8d21006dd20d8d21006dc20d8d210fedf10d8d210fede10d8d210fedd10d8d210fedc10d8d21006df6398d210e5ed7298d21024fe7598d21004fd7598d21024fc7598d2101cfe7498d21004fd7498d2101cfc7498d210b4fe7398d210b4de7398d210e4fd7298d21006ed7298d21114fd7198d21006f57198d21116ee2198d21116ec2198d21116f42198d21004ff7098d2100cfe7098d21004fd7098d2100cfc7098d21115ef7258d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d21006df7358d21114ff7258d21006ef7258d21114ef7258d210e4ff7158d21006f77158d21004f77158d21004ff7058d2100cfe7058d21004fd7058d2100cfc7058d210fcfe7618d21006dd6318d21024fe7518d21004fd7518d21024fc7518d2101cfe7418d21004fd7418d2101cfc7418d21006de7318d21006df5318d21006dc5318d21006df4318d21006dc4318d210ccfe7218d210acfc7218d210b4ff7118d21014fe7118d210b4fd7118d21014fc7118d210b6df3118d210b6dd3118d210b6ee2118d210b6ec2118d210b6f42118d21004ff7018d2100cfe7018d21004fd7018d2100cfc7018d21006d
  | 2 => 0x4fe7654f21004fd7654f21004fc7654f21005f77154f21015f47154f21004ff7690f21004fe7690f21004fd7690f21004fc7690f21004ff7650f21004fe7650f21004fd7650f21004fc7650f21005f77150f21015f47150f21014ff7694b21024fe7694b21014fd7694b210267e6594b210067d6594b210576f5294b21015f67194b21005f57194b2117fe62194b2121cff7654b210067f6554b210267c6554b21167e62154b21014ff7690b2101cfe7690b21014fd7690b2101ebe6490b21006bd6490b21015f67190b21005f57190b21214ff7650b21006bf6450b2101ebc6450b210e4fd76ccb21006df63ccb21006dc63ccb21116ee62ccb21015f471ccb21014ff768cb21014fd768cb21006de638cb21006dd638cb21015f6718cb21005f5718cb210ffd4318cb21114ff764cb21006df634cb21006dc634cb21015f4714cb21014ff760cb21014fd760cb21006de630cb21006dd630cb210b6ee620cb21015f6710cb21005f5710cb210b7d4310cb21005f576cc721006f576cc721015f673cc721017d673cc721006f763cc721007d663cc721006f563cc721007d563cc721007e672cc721005f572cc721007e572cc721016f662cc721017e662cc721007d732cc721007d532cc72122df770cc72122df570cc721227d730cc721227d530cc721024fe76d952103e7e65d952101cfe74d9521004fd74d952101cfc74d952103e7f54d9521004fe73d9521004fd73d9521024fe72d9521014fd72d9521024fc72d952103e7f52d952117cff71d9521014fe71d952117cfd71d9521014fc71d952117e7f51d952117e7d51d9521004ff70d952100cfe70d9521004fd70d952100cfc70d95210067e50d952103e7c50d952103e7c6559521005df7359521005dc735952121def725952117cff75595210067f7559521004ff745952101cfe745952101cfc7459521004ff7359521006df7359521004df7359521004fc7359521006dc7359521004dc735952121cff7259521006ef7259521164ff7159521006f77159521004ff705952100cfe7059521004fd705952100cfc705952101cfe76d9121036be64d9121024fe75d9121004fd75d9121024fc75d9121036be54d9121004fe73d9121004fd73d912101cfe72d9121014fd72d912101cfc72d9121036bf42d912114cff71d9121014fe71d912114cfd71d9121014fc71d912114ebf41d912114ebd41d9121004ff70d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121036bc40d9121036bc6459121005df7359121005dc7359121215ef7259121004ff7559121024fe7559121024fc755912114cff7459121006bf7459121004ff7359121006df7359121004df7359121004fc7359121006dc7359121004dc7359121214ff7259121006ef7259121134ff7159121006f7715
  | 3 => 0xf54d9721004fe73d9721004fd73d972120cfe72d9721006ee72d97210567f52d9721006f571d9721004ff70d972100cfe70d9721004fd70d972100cfc70d972117ef710d9721006f510d9721024ff76597210567c65597210067f7559721004ff745972101cfe745972101cfc7459721004ff7359721004fc7359721024ff7259721024fd7259721014fc72597210567c52597211667f51597211667d5159721004ff705972100cfe7059721004fd705972100cfc7059721166f71059721006f5105972104ebe64d9321205ee72d9321024fe75d9321004fd75d9321024fc75d9321134fd74d932104ebe54d9321004fe73d9321004fd73d9321204fe72d9321006ee72d932104ebf42d9321006f571d9321004ff70d932100cfe70d9321004fd70d932100cfc70d932114ef710d9321006f510d932101cff765932104ebc6459321004ff7559321024fe7559321024fc7559321006bf7459321004ff7359321004fc735932101cff725932101cfd7259321014fc725932104ebc4259321136bf4159321136bd4159321004ff705932100cfe7059321004fd705932100cfc7059321136f71059321006f51059321004ff7655321004fe7655321004fd7655321004fc76553210067f65553210267c6555321006bf645532101ebc645532104f3c5455321005f77155321015f471553210b5ee72d8f210ffd431d8f21024fe75d8f21004fd75d8f21024fc75d8f2101cfe74d8f21004fd74d8f2101cfc74d8f210b4fe72d8f21006ee72d8f210b4ee72d8f21006f571d8f210fede31d8f210fedc31d8f210fef431d8f21004ff70d8f2100cfe70d8f21004fd70d8f2100cfc70d8f21006df30d8f21006dd30d8f210fef710d8f21006f510d8f210e4fd7698f21006df6398f21024fe7598f21004fd7598f21024fc7598f2101cfe7498f21004fd7498f2101cfc7498f21116df3198f21116dd3198f21116ee2198f21116ec2198f21004ff7098f2100cfe7098f21004fd7098f2100cfc7098f21004ff7558f21024fe7558f21024fc7558f21004ff7458f2101cfe7458f2101cfc7458f21006df7358f210d4ff7258f210dcfd7258f21006f77158f210e6df3158f210e6dd3158f210e6f43158f21004ff7058f2100cfe7058f21004fd7058f2100cfc7058f210e6f71058f21006f51058f21006dd6318f210fdee7218f210b7d43118f21024fe7518f21004fd7518f21024fc7518f2101cfe7418f21004fd7418f2101cfc7418f21114fe7318f21006de7318f210fcfe7218f21006ee7218f21006f57118f210b6de3118f210b6dc3118f210b6ee2118f210b6ec2118f21004ff7018f2100cfe7018f21004fd7018f2100cfc7018f21006df3018f21006dd3018f21004ff7694f21004fe7694f21004fd7694f21004fc7694f210575f5394f21004ff7654f21
  | 4 => 0x8931007e51018931006ef7518931006ee7518931006ed7518931006ec7518931006ef7418931006ee7418931006ed7418931006ec7418931006ef5418931006ee5418931006ed5418931006ec54189310b6ef73189310b6ed73189310b6cd7318931006ef5318931006ee5318931006ed5318931006ec5318931006ef4318931006ee4318931006ed4318931006ec43189310b6ef71189310b6ee71189310b6ed71189310b6ec71189310b6ef51189310b6ee51189310b6ed51189310b6ec51189310b6ef41189310b6ee41189310b6ed41189310b6ec41189310b6ef31189310b6ee31189310b6ce31189310b6ed31189310b6ec31189310b6cc31189310b6e43118931006ef7018931006ee7018931006ed7018931006ec7018931006ef5018931006ee5018931006ed5018931006ec5018931006ef4018931006ee4018931006ed4018931006ec4018931006ef3018931006cf3018931006ee3018931006ed3018931006cd3018931006ec30189310b6ef10189310b6e710189310b6ee10189310b6ed1018931006e510189310b6ec1018931004fe7694931004fd7694931004fc7694931005de7394931005dd7394931006ef6294931006ec629493106f6f5294931004ff7654931004fe7654931004fc7654931006ef6254931006ec6254931004fe7690931004fd7690931004fc7690931005de7390931005dd7390931006ef6290931006ec6290931004ff7650931004fe7650931004fc7650931006ef6250931006ec62509310b4fe76cc931116ef62cc931006ec62cc9310b5de76cc931006de76cc9310b4de76cc931117cf62cc931006dc62cc931007cc62cc931006cc62cc931015de71cc931015dc71cc931116df61cc931117ce21cc931117cc21cc93125ddf70cc93125ddd70cc931117d710cc931257d510cc931014fe768c9310e5dd738c9310fedf638c931006ef628c931006ec628c931015f6718c931005f5718c9310ffd4318c931014fc764c931006ef624c931006ec624c931005f7714c931015f4714c931015dc764c9310e6dc764c931014dc764c931007cf724c931007cf624c931006dc624c931007cc624c931006cc624c931007d7714c931015de714c931015dc714c9310e7d4714c931015d4714c9310e6df614c93124ddf704c93124ddd704c9310e7d7104c931247d5104c931114fe760c931115de730c9310b6df630c931006ef620c9310b6ec620c9310b7d4310c931015f676cc531016f676cc531015f673cc531017d673cc531016f763cc531017d763cc531007e762cc531006f462cc531007e462cc531006e462cc531007d732cc531007d532cc53123df770cc53123df570cc531237d730cc531237d530cc5310567e65d972120dee72d9721164fd75d972101cfe74d9721004fd74d972101cfc74d97210567
  | 5 => 0x5df7355131005dc735513126cfe7694d3106f5f5394d311dfd43194d31024ff7654d31014fe7654d311c4fd7654d31014fc7654d310067f6554d310267c6554d31005f77154d31015f47154d311c7d43154d31264fe7690d3101cff7650d31014fe7650d31194fd7650d31014fc7650d31006bf6450d3101ebc6450d31005f77150d31015f47150d31024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d8931006ef52d8931006ec52d8931006ef42d8931006ec42d8931116ef21d8931004ff70d893100cfe70d8931004fd70d893100cfc70d8931006ef20d8931006ee20d8931006ed20d8931006ec20d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d8931117cf73d8931117ce31d8931117cc31d8931117e431d8931006ef60d8931006ee60d8931006ed60d8931006ec60d8931007cf30d8931007cd30d8931117e710d8931007e510d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d8931116ef73d8931116ed73d8931006ef53d8931006ee53d8931006ed53d8931006ec53d8931006ef43d8931006ee43d8931006ed43d8931006ec43d8931116ef71d8931116ee71d8931116ed71d8931116ec71d8931116ef51d8931116ee51d8931116ed51d8931116ec51d8931116ef41d8931116ee41d8931116ed41d8931116ec41d8931116ef31d8931116ee31d8931116ec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931006ef40d8931006ee40d8931006ed40d8931006ec40d8931006ef30d8931006ee30d8931006ed30d8931006ec30d8931116ef10d8931116ee10d8931116ed10d8931116ec10d8931006ef6298931006ed6218931024fe7518931004fd7518931024fc751893101cfe7418931004fd741893101cfc74189310b6dd7318931006ef5218931006ec5218931006ef4218931006ec4218931014fe7118931014fc71189310b6de31189310b6dc31189310b6f431189310b6ed2118931004ff701893100cfe7018931004fd701893100cfc7018931006df3018931006dd3018931006ef2018931006ee2018931006ed2018931006ec20189310b6f71018931006f51018931115ee7618931006ee7618931006ef6518931006ee6518931006ed6518931006ec6518931006ef6418931006ee6418931006ed6418931006ec64189310b7cd73189310b7ce31189310b7cc31189310b7e43118931006ef6018931006ee6018931006ed6018931006ec6018931007cf3018931007cd30189310b7e7101
  | 6 => 0xe7690b31004fd7690b31005de7390b31005dd7390b31004ff7650b31004fd7650b31004fc7650b31005f77150b31015f47150b31014fd76ccb31006ee62ccb31006ed62ccb31015f671ccb31005f571ccb31117e421ccb31015dd76ccb31116dd76ccb31014dd76ccb31006de62ccb31007ce62ccb31007cd62ccb31015de71ccb31117d671ccb31007d571ccb31015dc71ccb31117ce21ccb31117cc21ccb31117d421ccb31117c421ccb3128ddf70ccb3128ddd70ccb310e4fd768cb310fede638cb31015f4718cb310fcff764cb31015f4714cb310fddf764cb31006df764cb310fcdf764cb31007cf724cb31006de624cb31007d7714cb31015de714cb31015dc714cb310e7d4714cb31015d4714cb310e7d4214cb31285df704cb31285dd704cb31014fd760cb310b6de630cb31006ee620cb31006ed620cb31015f6710cb31005f5710cb310b7e4210cb31024fe76d953106e7e65d953101cfe74d9531004fd74d953101cfc74d953106e7f54d9531024fe73d9531014fd73d9531024fc73d953106e7f53d9531004fe72d9531004fd72d95311dcff71d95311dcfd71d95311de7f51d95311de7d51d9531004ff70d953100cfe70d9531004fd70d953100cfc70d95310067e50d953106e7c50d9531006df30d9531006dd30d95311def710d9531006f510d953106e7c655953127ddf7359531005ef7259531005ec72595311dcff75595310067f7559531004ff745953101cfe745953101cfc745953127cff7359531006df7359531004ff7259531006ef7259531004ef7259531004fc7259531006ec7259531004ec72595311c4ff7159531006f77159531004ff705953100cfe7059531004fd705953100cfc7059531006df3059531006dd30595311c6f71059531006f5105953101cfe76d9131066be64d9131024fe75d9131004fd75d9131024fc75d9131066be54d913101cfe73d9131014fd73d913101cfc73d9131066bf43d9131004fe72d9131004fd72d91311acff71d91311acfd71d91311aebf41d91311aebd41d9131004ff70d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131066bc40d9131006df30d9131006dd30d91311aef710d9131006f510d9131066bc6459131275df7359131005ef7259131005ec7259131004ff7559131024fe7559131024fc75591311acff7459131006bf7459131274ff7359131006df7359131004ff7259131006ef7259131004ef7259131004fc7259131006ec7259131004ec7259131194ff7159131006f77159131004ff705913100cfe7059131004fd705913100cfc7059131006df3059131006dd3059131196f71059131006f51059131004ff7655131004fe7655131004fd7655131004fc76551310067f65551310267c6555131006bf645513101ebc64551310673c5455131
  | 7 => 0xc941004fc768c94101dbe748c941005bd748c941006df638c941006dc638c941004ff764c941004fe764c941004fc764c941005f7714c941015f4714c941004fe760c941004fd760c941004fc760c94101dbe740c941005bd740c941006df630c941006dc630c941006ef620c941006ec620c9410867e65d973126dde73d97311c4fd75d973101cfe74d9731004fd74d973101cfc74d97310867f54d973126cfe73d9731006de73d9731004fe72d9731004fd72d9731006f571d9731004ff70d973100cfe70d9731004fd70d973100cfc70d9731006df30d9731006dd30d9731024ff76597310867c65597310067f7559731004ff745973101cfe745973101cfc7459731024ff7359731024fd7359731014fc73597310867c5359731004ff7259731004fc72597311c67f51597311c67d5159731004ff705973100cfe7059731004fd705973100cfc7059731006df3059731006dd305973107ebe64d9331265de73d9331024fe75d9331004fd75d9331024fc75d9331194fd74d933107ebe54d9331264fe73d9331006de73d9331004fe72d9331004fd72d9331006f571d9331004ff70d933100cfe70d9331004fd70d933100cfc70d9331006df30d9331006dd30d933101cff765933107ebc6459331004ff7559331024fe7559331024fc7559331006bf745933101cff735933101cfd7359331014fc735933107ebc4359331004ff7259331004fc7259331196bf4159331196bd4159331004ff705933100cfe7059331004fd705933100cfc7059331006df3059331006dd3059331004ff7655331004fe7655331004fd7655331004fc76553310067f65553310267c6555331006bf645533101ebc645533107f3c5455331005df7355331005dc7355331014ff7694f31024fe7694f31014fd7694f310267e6594f310067d6594f310875f5394f31015f67194f31005f57194f311dfd63194f3127cff7654f311c7d63154f31014ff7690f3101cfe7690f31014fd7690f3101ebe6490f31006bd6490f31015f67190f31005f57190f31274ff7650f31117e421d8b31006ef6298b31024fe7598b31004fd7598b31024fc7598b3101cfe7498b31004fd7498b3101cfc7498b310fede7398b310fede3198b310fedc3198b310feed2198b31004ff7098b3100cfe7098b31004fd7098b3100cfc7098b31006df3098b31006dd3098b31004ff7558b31024fe7558b31024fc7558b31004ff7458b3101cfe7458b3101cfc7458b31006f77158b310e6ef2158b310e6f42158b31004ff7058b3100cfe7058b31004fd7058b3100cfc7058b31006ed6218b310b7e42118b31004ff7694b31004fe7694b31004fd7694b31005de7394b31005dd7394b310876f5294b31004ff7654b31004fd7654b31004fc7654b31005f77154b31015f47154b31004ff7690b31004f
  | 8 => 0x4fd705954100cfc70595411f6f71059541006f51059541015bc7655141026bc7655141014bc765514101dbf755514101f3f75551410073f6555141026be6555141026bc65551410973c65551410263c65551410973c5355141005bf72551410973c5255141007b77155141015be7155141015bc71551411f7b4715514101ebf615514101fb761551411f73f51551411f73d51551412bebf60551412bebd60551410973f50551412bf3d50551411f7b710551412bfb51055141024fe75d8d41004fd75d8d41024fc75d8d41014fd74d8d412b6de43d8d412b6dd43d8d41004fe72d8d41004fd72d8d4101cfd71d8d41276df31d8d41004ff70d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d41276f710d8d41006f510d8d41006df6398d41065f57198d41005ef7258d41005ec7258d4107df77158d41006dd6318d41024fe7518d41004fd7518d41024fc7518d41014fd7418d412aebe5418d41006bd5418d412aede4318d412aedd4318d41004fe7218d41004fd7218d4101cfd7118d41266dd3118d41004ff7018d4100cfe7018d41004fd7018d4100cfc7018d41006de3018d41006dc3018d41004fe7694d41004fd7694d41004fc7694d410073d5494d41006df6394d41006dc6394d410975f5394d41004ff7654d41004fe7654d41004fc7654d41006df6354d41006dc6354d41024fe75d8941004fd75d8941024fc75d8941014fd74d8941004fe73d8941004fd73d89412a6ee42d89412a6ed42d894101cfd71d8941216ef21d8941004ff70d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d8941006ef6298941035f57198941005df7358941005dc735894104df77158941006ed6218941024fe7518941004fd7518941024fc7518941014fd7418941206bd741894129ebe5418941006bd5418941004fe7318941004fd731894129ebf421894129eee421894129eed421894101cfd7118941206ed2118941004ff701894100cfe7018941004fd701894100cfc7018941006ee2018941006ec2018941206f71018941006f51018941004fe7694941004fd7694941004fc769494101dbe7494941005bd74949410073d5494941006ef6294941006ec62949410976f5294941004ff7654941004fe7654941004fc765494101dbe7454941006ef6254941006ec6254941015bc7650941136bc7650941014bc7650941005bf7550941005bd755094101dbf725094101faf7250941007af6250941006bc6250941007ac6250941007b77150941015be7150941015bc7150941137b4715094101ebf615094101fb76150941297af2050941297ad2050941137b71050941297b51050941004fe76cc941004fd76cc941004fc76cc941006ef62cc941006ec62cc941004fe768c941004fd768
  | 9 => 0xc7418d512fe7f5418d510067d5418d512fede5318d512fedd5318d51004fe7218d51004fd7218d51024fd7118d5126edd3118d51004ff7018d5100cfe7018d51004fd7018d5100cfc7018d51006de3018d51006dc3018d51004fe7690d51004fd7690d51004fc7690d510073d5490d51006df6390d51006dc6390d51004ff7650d51004fe7650d51004fc7650d51006df6350d51006dc6350d51014fd75d895101cfe74d8951004fd74d895101cfc74d8951004fe73d8951004fd73d89512f6ee52d89512f6ed52d8951024fd71d895121eef21d8951004ff70d895100cfe70d8951004fd70d895100cfc70d8951006ee20d8951006ec20d8951006ef629895103df57198951005df7358951005dc7358951055f77158951006ed6218951014fd751895120e7d751895101cfe7418951004fd741895101cfc74189512ee7f54189510067d5418951004fe7318951004fd73189512ee7f52189512eeee52189512eeed5218951024fd711895120eed2118951004ff701895100cfe7018951004fd701895100cfc7018951006ee2018951006ec201895120ef71018951006f510189510157c76549511667c76549510147c76549510057f74549510257f72549510276f72549510076f62549510067c62549510076c62549510077771549510157e71549510157c71549511677471549510267f61549510277761549512e76f20549512e76d20549511677710549512e7751054951004fe7690951004fd7690951004fc76909510257e75909510057d75909510073d5490951006ef6290951006ec6290951004ff7650951004fe7650951004fc76509510257e75509510057d7550951006ef6250951006ec6250951004fe76cc951004fd76cc951004fc76cc951006ef62cc951006ec62cc951004fe768c951004fd768c951004fc768c9510257e758c9510057d758c951006df638c951006dc638c951004ff764c951004fe764c951004fc764c951005f7714c951015f4714c951004fe760c951004fd760c951004fc760c9510257e750c9510057d750c951006df630c951006dc630c951006ef620c951006ec620c951024fe76d95410967e65d95411f4fd75d9541014ff74d954101cfe74d9541014fd74d954101cfc74d95412de7f54d95412de7d54d9541004fe73d9541004fd73d9541004fe72d9541004fd72d954101cff71d954101cfd71d95412ce7f51d95412ce7d51d9541004ff70d954100cfe70d9541004fd70d954100cfc70d95410067e50d95410967c50d95412cef710d9541006f510d9541024ff76595410967c65595412c5bf74595412d5f771595412ccff75595410067f75595412c4ff7459541006bf7459541004ff7359541004fc7359541004ff7259541004fc72595411f4ff7159541006f77159541004ff705954100cfe7059541
  | 10 => 0x4832005dd73948320c76f529483210cff7654832104ff769083201cfe769083201cfd76908320bcfc769083201ebe6490832006bd6490832005de7390832005dd7390832104ff76508320b5de71cc8320b5dc71cc83236fce21cc83236fcc21cc83234ddf70cc83234ddd70cc83233ddd738c832366de638c83233ded738c832366ee638c832007ce638c8320b5ee718c8320b5ec718c83235fce318c83235fcc318c832357cf308c832357cd308c832004ff764c832005f7714c8320b5f4714c832005df764c832006df764c832004df764c83234ddf724c832346de624c832007ce524c832007cd524c832007ce424c832007cd424c832007d7714c8320b5de714c8320b5dc714c832007d4714c8320b5d4714c832327ce214c832327cc214c83233ddf704c83233ddd704c832005ef764c832006ef764c832004ef764c832335ef734c832007cf734c83232eee634c832007ce634c832007ce534c832007cd534c832007ce434c832007cd434c832007e7714c8320b5ee714c8320b5ec714c832007e4714c8320b5e4714c832327ce314c832327cc314c8320b6f661d8432014ff76584320b6f461584320b7d431584320b7e42158432004ff7558432024fe7558432024fc7558432004ff745843201cfe745843201cfc7458432006df3258432006dd32584320b6de31584320b6dc31584320b6f431584320b6ee21584320b6ec21584320b6f42158432004ff705843200cfe7058432004fd705843200cfc7058432006df3058432006dd30584320b6f71058432006f5105843201cfe76d91510a6be64d9151014fd75d915101cfc75d91510a6be54d915131ebd54d9151004fe73d9151004fd73d9151004fe72d9151004fd72d9151024fd71d91512c6bf41d9151004ff70d915100cfe70d9151004fd70d915100cfc70d9151006be40d91510a6bc40d91512c6f710d9151006f510d91510a6bc6459151315f771591510157c765515101e7c76551510147c76551510257f74551510273f74551510073f645515101e7e645515101e7c64551510a73c645515101e3c64551510a73c43551510057f72551510a73c42551510077771551510157e71551510157c71551511f77471551510267f61551510277761551511f73f415515130e7f605515130e7d60551510a73f405515130f3d40551511f777105515130f751055151014fd75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d51306de53d8d51306dd53d8d51004fe72d8d51004fd72d8d51024fd71d8d5127edf31d8d51004ff70d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51006de30d8d51006dc30d8d5127ef710d8d51006f510d8d51006df6398d5106df57198d51005ef7258d51005ec7258d51085f77158d51006dd6318d51014fd7518d5101cfe7418d51004fd7418d5101cf
  | 11 => 0x6f750d8532006f650d8532006f550d8532006f450d8532006f740d8532006f640d8532006f540d8532006f440d8532006f730d8532006f630d8532006f530d8532006f430d8532006f720d8532006f620d8532006f520d8532006f420d85320e6f46158532005f676185320e6f67618532006f76518532006f66518532006f56518532006f46518532006f76418532006f66418532006f56418532006f464185320e7d573185320fef763185320fed76318532116f76218532116e76218532007e73218532007d632185320e7f270185320e7f17018532006f76018532006f66018532006f56018532006f460185320c67e65d94320bdbe74d9432005bd74d94320c4fd75d943201cfe74d9432006be74d943201cbe74d9432004fd74d9432006bd74d9432004bd74d943201cfc74d94320c67f54d9432124fe73d9432006de73d943210cfe72d9432006ee72d9432014fe71d9432004fd71d9432014fc71d9432004ff70d943200cfe70d9432004fd70d943200cfc70d9432006df30d9432006dd30d9432024ff76594320c67c65594320067f7559432004ff745943201cfe745943201cfc74594320067e54594320c67c54594320c4fc73594320c67c53594320c4fc72594320c67c5259432004ff7159432014fe7159432014fc71594320c67f5159432004ff705943200cfe7059432004fd705943200cfc70594320c67f50594320067d5059432006df3059432006dd30594320c57e75d90320057d75d90320bebe64d9032024fe75d90320067e75d90320247e75d9032004fd75d90320067d75d90320047d75d9032024fc75d90320bcfd74d90320bebe54d903211cfe73d9032006de73d9032104fe72d9032006ee72d9032014fe71d9032004fd71d9032014fc71d9032004ff70d903200cfe70d9032004fd70d903200cfc70d9032006df30d9032006dd30d903201cff76590320bebc6459032004ff7559032024fe7559032024fc7559032006bf7459032006bf54590320bebc54590320bcfc73590320bebc43590320bcfc72590320bebc4259032004ff7159032014fe7159032014fc71590320bebf4159032004ff705903200cfe7059032004fd705903200cfc70590320bebf4059032006bd4059032006df3059032006dd3059032004ff7655032004fe7655032004fd7655032004fc76550320067f65550320267c6555032006bf645503201ebc64550320bf3c5455032005df7355032005dc7355032124ff7694c32024fd7694c320267e6594c320067d6594c320c75f5394c32005ee7294c32005ed7294c32124ff7654c3211cff7690c3201cfd7690c3201ebe6490c32006bd6490c32005ee7290c32005ed7290c3211cff7650c3210cff7694832024fe7694832024fd76948320c4fc76948320267e65948320067d6594832005de739
  | 12 => 0xe71d9132004fd71d9132014fc71d9132004ff70d913200cfe70d9132004fd70d913200cfc70d9132006be40d91320eebc40d91320eebc6459132005f771591320e5f47159132004ff7559132024fe7559132024fc75591320ecff7459132006bf7459132104ff7359132006df735913211cff7259132006ef7259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f47159132004ff705913200cfe7059132004fd705913200cfc7059132004ff7655132004fe7655132004fd7655132004fc76551320067f65551320267c6555132006bf645513201ebc64551320ef3c54551321f6f4615513210cfe7694d320f75f5394d321def46194d32024fc7654d320067f6554d320267c6554d320f75c5354d32005ef7254d32005ec7254d321c6f46154d32104fe7690d321aef46190d3201cfc7650d32006bf6450d3201ebc6450d320ef9c4350d32005ef7250d32005ec7250d32196f46150d32124fe76949320f76f529493217ef46194932024ff76549320f4fd7654932024fc76549320067f65549320267c6554932005df7354932005dc73549320f76c5254932166f4615493211cfe769093214ef4619093201cff76509320ecfd765093201cfc7650932006bf645093201ebc6450932005df7350932005dc73509320efac4250932136f46150932116ee61cc932116ec61cc932007cf628c932005dd718c9320fede618c9320fedc618c932376df608c932376dd608c932014fe76d85320e6f661d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d8532006f751d85320e6f651d85320e6f451d8532006f741d85320e6f641d85320e6f441d85320e6f631d85320e6f621d8532004ff70d853200cfe70d8532004fd70d853200cfc70d85320e6f710d8532006f610d8532006f510d85320e6f410d85320e5f676d8532014f676d8532006f765d8532006f665d8532006f565d8532006f465d8532006f764d8532006f664d8532006f564d8532006f464d8532007d773d8532007e732d8532007d632d8532006f760d8532006f660d8532006f560d8532006f460d8532006f775d8532006f675d8532006f575d8532006f475d8532006f774d8532006f674d8532006f574d8532006f474d8532006f754d8532006f654d8532006f554d8532006f454d8532006f773d85320e6f673d8532006f753d8532006f653d8532006f553d8532006f453d8532006f743d8532006f643d8532006f543d8532006f443d8532006f772d85320e6f672d8532006f752d8532006f652d8532006f552d8532006f452d8532006f742d8532006f642d8532006f542d8532006f442d8532006f732d8532006f632d8532006f770d8532006f670d8532006f570d8532006f470d8532
  | 13 => 0x96320067e505963210e7c5059632006df3059632006dd3059632106be64d9232024fe75d9232004fd75d9232024fc75d9232104fd74d9232006dd73d9232006ee72d9232014fe71d9232004fd71d9232014fc71d9232004ff70d923200cfe70d9232004fd70d923200cfc70d9232006df30d9232006dd30d923201cff7659232106bc6459232004ff7559232024fe7559232024fc7559232006bf7459232106be5459232106bf4359232106bc4259232004ff7159232014fe7159232014fc7159232106bf4159232004ff705923200cfe7059232004fd705923200cfc7059232006be4059232106bc4059232006df3059232006dd3059232004ff7655232004fe7655232004fd7655232004fc76552320267e65552320067d655523201ebe6455232006bd64552321073c5455232005df7355232005dc73552320f4fd7694e3210f5f5394e32024ff7654e320267e6554e320067d6554e32005ef7254e32005ec7254e320ecfd7690e3201cff7650e3201ebe6450e32006bd6450e32005ef7250e32005ec7250e32024fe7694a32024fd7694a320267e6594a320067d6594a32005de7394a32005dd7394a3210f6f5294a320c4ff7654a3210f6c5254a3201cfe7690a3201cfd7690a3201ebe6490a32006bd6490a32005de7390a32005dd7390a320bcff7650a32107ac4250a32005dd76cca32006dd76cca32007ce52cca32007cd52cca320fdde71cca320fddc71cca32365df70cca32365dd70cca32005ed76cca32006ed76cca32007ce53cca32007cd53cca32116ee61cca32116ec61cca320fef661d86320ffd431d8632014ff76586320fef461586320ffd63158632004ff7558632024fe7558632024fc7558632004ff745863201cfe745863201cfc7458632006df32586320fede31586320fef631586320fedc31586320fef42158632004ff705863200cfe7058632004fd705863200cfc7058632006df3058632006dd3058632024fe76d95320f67e65d953201cfe74d9532004fd74d953201cfc74d95320f67f54d95320f4fd73d95320f67f53d95320f4fd72d95320f67f52d9532014fe71d9532004fd71d9532014fc71d9532004ff70d953200cfe70d9532004fd70d953200cfc70d95320067e50d95320f67c50d95320f67c6559532005f771595320e5f471595320f4ff75595320067f7559532004ff745953201cfe745953201cfc745953210cff7359532006df7359532124ff7259532006ef7259532004ff7159532006f77159532004f77159532014fe7159532014fc7159532006f47159532014f47159532004ff705953200cfe7059532004fd705953200cfc705953201cfe76d91320eebe64d9132024fe75d9132004fd75d9132024fc75d91320eebe54d91320ecfd73d91320eebf43d91320ecfd72d91320eebf42d9132014f
  | 14 => 0x14fc74d8542004fe73d8542004fd73d854201cfd72d8542006f751d8542136f451d8542136f641d8542136f431d8542136f621d8542004ff70d854200cfe70d8542004fd70d854200cfc70d8542136f710d8542006f510d8542005df7358542005dc7358542136f461585421267e65d9732124fd75d973201cfe74d9732004fd74d973201cfc74d9732006de73d9732006ed72d9732014fe71d9732004fd71d9732014fc71d9732004ff70d973200cfe70d9732004fd70d973200cfc70d9732024ff76597321267c65597320067f7559732004ff745973201cfe745973201cfc74597321267f54597321267c53597321267f5259732004ff7159732014fe7159732014fc7159732004ff705973200cfe7059732004fd705973200cfc705973211ebe64d9332024fe75d9332004fd75d9332024fc75d933211cfd74d9332006de73d9332006ed72d9332014fe71d9332004fd71d9332014fc71d9332004ff70d933200cfe70d9332004fd70d933200cfc70d933201cff765933211ebc6459332004ff7559332024fe7559332024fc7559332006bf745933211ebe545933211ebc435933211ebf4259332004ff7159332014fe7159332014fc7159332004ff705933200cfe7059332004fd705933200cfc7059332004ff7655332004fe7655332004fd7655332004fc76553320267e65553320067d655533201ebe6455332006bd645533211f3c5455332024fd7694f320267e6594f320067d6594f321275f5394f32005ee7294f32005ed7294f320c4ff7654f321275c5354f3201cfd7690f3201ebe6490f32006bd6490f32005ee7290f32005ed7290f320bcff7650f3211f9c4350f320f4fd7694b321276f5294b32024ff7654b32024fc7654b320267e6554b320067d6554b32005df7354b32005dc7354b320ecfd7690b3201cff7650b3201cfc7650b3201ebe6450b32006bd6450b32005df7350b32005dc7350b32116f661d8732117e421d8732014ff7658732116f46158732117e62158732004ff7558732024fe7558732024fc7558732004ff745873201cfe745873201cfc7458732116f43158732116ee2158732116f62158732116ec2158732004ff705873200cfe7058732004fd705873200cfc7058732116f71058732006f5105873210e7e65d963210cfd75d963201cfe74d9632004fd74d963201cfc74d9632006dd73d9632006ee72d9632014fe71d9632004fd71d9632014fc71d9632004ff70d963200cfe70d9632004fd70d963200cfc70d9632006df30d9632006dd30d9632024ff765963210e7c65596320067f7559632004ff745963201cfe745963201cfc745963210e7f545963210e7f535963210e7c5259632004ff7159632014fe7159632014fc715963210e7f5159632004ff705963200cfe7059632004fd705963200cfc705
  | 15 => 0xe6594a420067d6594a4201dbe7494a42005bd7494a420073d5494a421576f5294a42187af4294a4238cff7654a4201dbe7454a4216faf4254a4214ef661d8642014ff765864214ef46158642004ff7558642024fe7558642024fc7558642036be5458642006bd5458642004ff7358642004fc735864201cfc7258642036bf425864214ef6415864214ef42158642004ff705864200cfe7058642004fd705864200cfc7058642024fe76d954213e7e65d9542184ff74d9542184fd74d95421867f54d95421867d54d9542004fe73d9542004fd73d954201cfd72d954213e7f52d9542186bc42d9542014fe71d9542004fd71d9542014fc71d9542186bf41d9542004ff70d954200cfe70d9542004fd70d954200cfc70d9542006ef20d9542006ed20d954213e7c6559542005df7359542005dc735954238def7259542005f77159542135f47159542005fb705954212df87059542184ff75595420067f755954216cff7459542006bf7459542004ff7359542006df7359542004df7359542004fc7359542006dc7359542004dc735954238cff7259542006ef725954213e7c525954216ebc4259542004ff7159542006f77159542004f77159542014fe7159542014fc7159542006f47159542014f4715954213e7f515954216ebf4159542004ff7059542006fb7059542004fb705954200cfe7059542004fd705954200cfc7059542006f8705954200cf87059542006ef2059542006ed2059542024fe75d8d42004fd75d8d42024fc75d8d42006df53d8d42006dc53d8d42106de43d8d42106dd43d8d42014fe71d8d42004fd71d8d42014fc71d8d42006de31d8d42006dc31d8d42004ff70d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006df30d8d42006dd30d8d42006df6398d420eded7298d4211def7258d42005f77158d42135f47158d42006dd6318d42024fe7518d42004fd7518d42024fc7518d42006df5318d42006dc5318d420bede4318d420bedd4318d42014fe7118d42004fd7118d42014fc7118d42006de3118d42006dc3118d42004ff7018d4200cfe7018d42004fd7018d4200cfc7018d42006df3018d42006dd3018d42004fe7694d42004fd7694d42004fc7694d4201dbe7494d42005bd7494d4213f5f5394d42005ee7294d42005ed7294d42004ff7654d42004fe7654d42004fc7654d42384fe76949420267e65949420067d659494213f6f5294942187ac4294942024ff765494201cfe765494216cfd765494201cfc76549420067f65549420267c6554942005bf745494201dbc745494216fac4254942006bf6590942006bd659094201dbe729094201fae729094201ebf629094201faf6290942005bd719094237faf209094237fad2090942014fe76d8542136f661d8542024fe75d8542004fd75d8542024fc75d8542
  | 16 => 0x8d52004fd7118d52014fc7118d52006de3118d52006dc3118d52004ff7018d5200cfe7018d52004fd7018d5200cfc7018d52006df3018d52006dd3018d52004fe7690d52004fd7690d52004fc7690d520257e7590d520057d7590d52005ee7290d52005ed7290d52004ff7650d52004fe7650d52004fc7650d520067f64949520257e72949520276e72949520267f62949520276f62949520266f62949520057d719495239f6f209495239f6d2094952014fe76d8552166f661d8552014fc75d855201cfe74d8552004fd74d855201cfc74d8552004fe73d8552004fd73d8552024fd72d8552166f651d8552006f741d8552166f441d8552166f431d8552166f621d8552004ff70d855200cfe70d8552004fd70d855200cfc70d8552166f710d8552006f510d8552005df7358552005dc7358552166f461585521567e65d9642385ee72d964216cfd75d9642006bd74d9642004fe73d9642004fd73d9642384fe72d9642006ee72d9642014fe71d9642004fd71d9642014fc71d9642004ff70d964200cfe70d9642004fd70d964200cfc70d9642006ef20d9642006ed20d9642024ff76596421567c65596420067f755964216e7f545964216e7d5459642004ff7359642004fc73596421567f535964201cfc72596421567c5259642004ff7159642014fe7159642014fc71596421567f5159642004ff705964200cfe7059642004fd705964200cfc70596420067e50596421567c5059642006ef2059642006ed2059642155bf7655242026bf7655242024bf765524201dbf755524201f3f7555242026be65552421573e65552420263e65552420073d6555242026bc65552421573c5355242005bf7255242007af7255242007ac725524201ebe625524201fae62552421573c52552421573f5155242396bf6055242396bd60552421573f50552423973d5055242397af2055242397ad20552420bdee72d8e42006df6398e42024fe7598e42004fd7598e42024fc7598e4211ebe5498e42006bd5498e4211ede4398e4211edd4398e42014fe7198e42004fd7198e42014fc7198e42004ff7098e4200cfe7098e42004fd7098e4200cfc7098e42006de3098e42006dc3098e42004ff7558e42024fe7558e42024fc7558e420eede4358e420eedd4358e42004ff7158e42014fe7158e42014fc7158e42004ff7058e4200cfe7058e42004fd7058e4200cfc7058e42006de3058e42006dc3058e421557e7518e420057d7518e42006dd6318e42105ee7218e42004ff7694e42004fe7694e42004fd7694e420073d5494e42006de6394e42006dd6394e421575f5394e42005ee7294e42005ed7294e42004ff7654e42004fd7654e42004fc7654e420267e6554e420067d6554e42006de6354e42006dd6354e4201cff7694a42024fe7694a4201cfd7694a420267
  | 17 => 0x14fc7159252186bf4159252004ff705925200cfe7059252004fd705925200cfc7059252006be4059252186bc4059252006ef2059252006ed20592521857f765525201e7f765525201c7f76552520257f74552520273f745525201e7e64552521873e645525201e3e64552520073d645525201e7c64552521873c43552520057f72552520076f72552520056f72552520076c72552520267e62552520276e62552521873c42552521873f41552523ae7f60552523ae7d60552521873f40552523af3d40552523af6f20552523af6d20552520c5ee72d8e5210f6f52d8e52006df6398e521276f5298e5201cfe7498e52004fd7498e5201cfc7498e521267f5498e520067d5498e52126de5398e52126dd5398e52014fe7198e52004fd7198e52014fc7198e52004ff7098e5200cfe7098e52004fd7098e5200cfc7098e52006de3098e52006dc3098e520f76f5258e52004ff7458e5201cfe7458e5201cfc7458e520f6de5358e520f6dd5358e52004ff7158e52014fe7158e52014fc7158e52004ff7058e5200cfe7058e52004fd7058e5200cfc7058e52006de3058e52006dc3058e52185be7418e52005bd7418e52006dd6318e5210dee7218e520c76f5218e52004ff7690e52004fe7690e52004fd7690e520073d5490e52006de6390e52006dd6390e52005ee7290e52005ed7290e521b76f5290e52004ff7650e52004fd7650e52004fc7650e5201ebe6450e52006bd6450e52006de6350e52006dd6350e5219f6f5250e520576f52d865217ef661d8652014ff765865203f6f525865217ef46158652004ff745865201cfe745865201cfc745865203e7f54586520067d5458652004ff7358652004fc7358652024fc725865203e7f525865217ef6515865217ef42158652004ff705865200cfe7058652004fd705865200cfc705865201cfe76d915216ebe64d915216ebe54d9152156bd54d9152004fe73d9152004fd73d9152024fd72d91521567c52d915216ebf42d9152014fe71d9152004fd71d9152014fc71d91521567f51d9152004ff70d915200cfe70d9152004fd70d915200cfc70d9152006ef20d9152006ed20d915216ebc6459152005df7359152005dc73591523a5ef7259152005f77159152165f47159152005fb705915215df8705915201cfe74d8d52004fd74d8d5201cfc74d8d5210ede53d8d5210edd53d8d52006df43d8d52006dc43d8d52014fe71d8d52004fd71d8d52014fc71d8d52006de31d8d52006dc31d8d52004ff70d8d5200cfe70d8d52004fd70d8d5200cfc70d8d52006df30d8d52006dd30d8d52006df6398d520f5ed7298d52125ef7258d52005f77158d52165f47158d52006dd6318d5201cfe7418d52004fd7418d5201cfc7418d520c6de5318d520c6dd5318d52006df4318d52006dc4318d52014fe711
  | 18 => 0xf7158a43014fe7158a43014fc7158a43004ff7058a4300cfe7058a43004fd7058a4300cfc7058a431b57e7518a430057d7518a43006ed6218a431aef661d8643014ff76586431aef46158643004ff7558643024fe7558643024fc7558643066be5458643006bd545864301cfc7358643004ff7258643004fc72586431aef641586431aef43158643004ff705864300cfe7058643004fd705864300cfc7058643006df3058643006dd30586431aef71058643006f51058643024fe76d954319e7e65d95431e4ff74d95431e4fd74d95431e67f54d95431e67d54d954301cfd73d954319e7f53d95431e6bc43d9543004fe72d9543004fd72d9543014fe71d9543004fd71d9543014fc71d9543004ff70d954300cfe70d9543004fd70d954300cfc70d95430067e50d954319e7c50d9543006df30d9543006dd30d954319e7c65595433cddf7359543005fb705954318df870595431e4ff75595430067f75595431ccff7459543006bf74595433ccff7359543006df735954319e7c53595431cebc4359543004ff7259543004fc7259543004ff7159543014fe7159543014fc7159543004ff7059543006fb7059543004fb705954300cfe7059543004fd705954300cfc7059543006f8705954300cf87059543006df3059543006dd30595433c4fe7694d430267e6594d430067d6594d4319f5f5394d431e79c4394d43024ff7654d4301cfe7654d431ccfd7654d4301cfc7654d430067f6554d430267c6554d43005bf7454d4301dbc7454d431cf9c4354d43006bf6590d43006bd6590d4301dbe7390d4301f9e7390d4301ebf6390d4301f9f6390d431a6be6090d431a6bc6090d433bf9f3090d433bf9d3090d43024fe75d8943004fd75d8943024fc75d894311eee42d8943014fe71d8943004fd71d8943014fc71d8943006ee21d8943006ec21d8943004ff70d894300cfe70d8943004fd70d894300cfc70d8943006ef6298943005f77158943195f47158943006ed6218943024fe7518943004fd7518943024fc75189430beed4218943014fe7118943004fd7118943014fc7118943006ee2118943006ec2118943004ff701894300cfe7018943004fd701894300cfc7018943006df3018943006dd3018943014fe76d8543196f661d8543024fe75d8543004fd75d8543024fc75d854301cfd73d8543004fe72d8543004fd72d8543196f641d8543196f631d8543196f421d8543004ff70d854300cfe70d8543004fd70d854300cfc70d8543006df30d8543006dd30d8543005ef7258543005ec7258543196f46158543186be64d92523b5ee72d92521576f52d925201cff7659252186bc645925213f6f5259252186be545925213ebd5459252004ff7359252004fc7359252186bf4359252024fc7259252186bc4259252004ff7159252014fe7159252
  | 19 => 0x9153014fc71d9153004ff70d915300cfe70d9153004fd70d915300cfc70d9153006be40d91531cebc40d9153006df30d9153006dd30d91531cebc64591533e5df7359153005fb70591531bdf870591530067f6494d530257e7394d530275e7394d530267f6394d530275f6394d530265f6394d531d67e6094d531d67c6094d533df5f3094d533df5d3094d5301cfe74d8953004fd74d895301cfc74d8953126ee52d8953014fe71d8953004fd71d8953014fc71d8953006ee21d8953006ec21d8953004ff70d895300cfe70d8953004fd70d895300cfc70d8953006ef6298953005f771589531c5f47158953006ed621895301cfe7418953004fd741895301cfc74189530c6ed5218953014fe7118953004fd7118953014fc7118953006ee2118953006ec2118953004ff701895300cfe7018953004fd701895300cfc7018953006df3018953006dd3018953014fe76d85531c6f661d855301cfe74d8553004fd74d855301cfc74d8553024fd73d8553004fe72d8553004fd72d85531c6f651d85531c6f631d85531c6f421d8553004ff70d855300cfe70d8553004fd70d855300cfc70d8553006df30d8553006dd30d8553005ef7258553005ec72585531c6f461585531b67e65d96433c5de73d96431ccfd75d9643006bd74d96433c4fe73d9643006de73d9643004fe72d9643004fd72d9643014fe71d9643004fd71d9643014fc71d9643004ff70d964300cfe70d9643004fd70d964300cfc70d9643006df30d9643006dd30d9643024ff76596431b67c65596430067f75596431ce7f54596431ce7d545964301cfc73596431b67c5359643004ff7259643004fc72596431b67f5259643004ff7159643014fe7159643014fc7159643004ff705964300cfe7059643004fd705964300cfc7059643006df3059643006dd30596431b5bf7655243026bf7655243024bf765524301dbf755524301f3f7555243026be65552431b73e65552430263e65552430073d6555243026bc6555243005bf73552430079f73552430079c735524301ebe635524301f9e63552431b73c53552431b73c52552431b73f51552431a5be70552431a5bc70552433d6bf60552433d6bd60552431b73f50552433d73d50552433d79f30552433d79d305524301cff7694e43024fe7694e4301cfd7694e430267e6594e430067d6594e4301dbe7494e43005bd7494e430073d5494e431b75f5394e431e79f4394e433ccff7654e4301dbe7454e431cf9f4354e43006ef6298a43024fe7598a43004fd7598a43024fc7598a43106be5498a43006bd5498a43106ed4298a43014fe7198a43004fd7198a43014fc7198a43004ff7098a4300cfe7098a43004fd7098a4300cfc7098a43006df3098a43006dd3098a43004ff7558a43024fe7558a43024fc7558a430eeee4258a43004f
  | 20 => 0x3a67c52d895438eee42d895438ebc42d8954014fe71d8954004fd71d8954014fc71d89543a67f51d895438ebf41d8954004ff70d895400cfe70d8954004fd70d895400cfc70d89541873c5498954006ef629895416f3c5458954005df7358954005dc7358954005f771589541f5f47158954005fb70589541edf870589543873c5418954006ed621895401cfd7518954024fd7418954004fe7318954004fd73189543b6ed5218954386ed4218954014fe7118954004fd7118954014fc7118954004ff701895400cfe7018954004fd701895400cfc7018954014fe76d85542d73c54d85541f6f661d855401cfd75d8554024fd74d8554004fe73d8554004fd73d8554004fe72d8554004fd72d85541f6f651d85541f6f641d85541f6f421d8554004ff70d855400cfe70d8554004fd70d855400cfc70d85540a73c54585541f6f461585541e6be64d92533f5de73d92531b75f53d925301cff76592531e6bc645925319f5f53592531e6be545925319ebd5459253024fc73592531e6bc4359253004ff7259253004fc72592531e6bf4259253004ff7159253014fe7159253014fc7159253004ff705925300cfe7059253004fd705925300cfc7059253006df3059253006dd30592531e57f765525301e7f765525301c7f76552530257f74552530273f745525301e7e64552531e73e645525301e3e64552530073d645525301e7c64552530057f73552530075f73552530055f73552530075c73552530267e63552530275e63552531e73c43552531e73c42552531e73f41552531d57e70552531d57c70552533ee7f60552533ee7d60552531e73f40552533ef3d40552533ef5f30552533ef5d30552531275f53d8a5310f5f5398a53006ef6298a5301cfe7498a53004fd7498a5301cfc7498a5310e7f5498a530067d5498a5310eed5298a53014fe7198a53004fd7198a53014fc7198a53004ff7098a5300cfe7098a53004fd7098a5300cfc7098a53006df3098a53006dd3098a530f75f5358a53004ff7458a5301cfe7458a5301cfc7458a530f6ee5258a53004ff7158a53014fe7158a53014fc7158a53004ff7058a5300cfe7058a53004fd7058a5300cfc7058a531e5be7418a53005bd7418a530c75f5318a53006ed6218a530875f53d86531def661d8653014ff765865306f5f53586531def46158653004ff745865301cfe745865301cfc745865306e7f54586530067d5458653024fc7358653004ff7258653004fc72586531def651586531def43158653004ff705865300cfe7058653004fd705865300cfc7058653006df3058653006dd30586531def71058653006f5105865301cfe76d91531cebe64d91531cebe54d91531b6bd54d9153024fd73d91531b67c53d91531cebf43d9153004fe72d9153004fd72d9153014fe71d9153004fd71d
  | 21 => 0x60000008000000000000800c00a0020000000002000000000000200e000001000200500080040040060018008008003000001400a0000038000008004000800800000000800040040000000000000002000000000000d000000000000c001000000a001001000400000200180040040030000000000001000000400a004001000800a002000800000e000000000400200100c8000008002001001000000000080000020030028008000001000000400a0050008000002007000000401a000000000000e00c000800000c00100080040040070008004006000001801c00a00000180040080010008014002001000002400200100000180000000008008000000002000400000000080100000040048004006002000801c002004003000c0020000000004020000000800801a0020048000000000001800000000100000040000000000000002000000800000000000600080000090000004008006000800000600800000000000010020010000001000000c00000500000000000000008004016000000000000a002000800000201b000000001a002000000800c0000000000008003005000c000000000000000200000400000040050040008002000000002800000000600000080030028000000004000000000000f001801400a005002800000800000000000040010008004002005001800400000600200000000000018014004005000800400200f00200080000000000010000000004002400a0020010008006001000000c0080010000004000001000002401a0020008004004000002000000a001000800c00400000080080000020008004004002000800c0000000000004000000003800000000000400180060010000004002000000003000000b0008008000000001800800202900100000020000000000008003000800c00c007008000c00a00100180100000030010000002002000800c0080020050008000000003800000a003001000c00200600000000000023cf3c54d8d5401cfd75d8d543ce7d75d8d54024fd74d8d543e6bd74d8d543e6de53d8d543e67c53d8d543cede43d8d543cebc43d8d54004fe72d8d54004fd72d8d54014fe71d8d54004fd71d8d54014fc71d8d54004ff70d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54006de30d8d54006dc30d8d541e73c5498d54006df6398d541cf3c5458d54005fb7058d541edf87058d543c73c5418d54006dd6318d5401cfd7518d54024fd7418d543f6dd5318d543c6dd4318d54004fe7218d54004fd7218d54014fe7118d54004fd7118d54014fc7118d54004ff7018d5400cfe7018d54004fd7018d5400cfc7018d54006de3018d54006dc3018d5438f3c54d895401cfd75d895438e7d75d8954024fd74d89543a6bd74d8954004fe73d8954004fd73d89543a6ee52d8954
  | 22 => 0x100000020010010000004001003000800000100000000000020000000000006001000000e000007002c008001000000000e00000200000000000008008008002003000c0000070040004004000001800400e000000001c00a0000008020000001001800000600000380000000040050000000004000000000400700080000020000020004002001000002c00200100580000000000018024004000000001c00a001000000000000200100180000030000034006000000000400a001000000c004001001000400000000100000000020020000000000000800000000500000080100100000010000002000801400400100280080000000090000002000002000000c000002000c0000000008004000005000001801000100300100020000000004000000001000400000100080400000000020008000002001003000000d000800c00001900000080000020018000002000004001000c0010040004000002001000000201e0000018002000000000c00000e00380100000010010000000000001800400c000000000000600200000080060000048000000006000002000001500000040280040050028002001000000c00201b001001000600800200000000030048010008001000002000000b00600000020000018008002000002000800c00d00000000000010018000000000000800400800400000000000030018000004002000804c004000000800400000400080000040090000004008000000000c000008002001400000000000140000010010004000001000001c0000020008000008002000800c00a01200000000020010008004000002003800401001d00100040060040040000006000000800001800000080000000060008008004002000000c0180020000018002000000000800200100300080080000018000000006000001800000200100000060040000000000000000001000000000000000060000030000002001001000c004004000800c002000000800c000006000001403c00000080040040030000004000000000000001800000180000060000000014002000004000000000100000080000010008000002000001800000c0010008000004001002801400a00a0000004000000000800c006003000800c0040010008010008001000000000000000280000140030008010000003006000800e00000000000040090000008000000002000400400100280040040080000028000000000801400a002003000400200000080040060010020008002000000001400600000000100020070040000000002001000401600000400040000020010008000000000000c00200000000040040000018008000006002800000400000100000180000000004012001000802000600c000000400e0000000008004003000800400800000000000
  | 23 => 0x5c00000085988000da806c00000000004b9000324c0003391fb800012800054f9e38000a993d4aba89306310000000000a9e0003214822a4200000000000000002268d2633f30c25d800000022bb77dbd6b9d5ae91e051200060880001400cd34709600006d740e106d46891954a380d54e1135923005c5e676062b291a3ac232de1360db4000397000084aba81ac2fe93b0e2500319e400000000000001145ca0002ed8b7ec825b4b48c0000000eb1f719963b46a7a278cbc00000000014c4b8b000000199c0000000000000aa000003e519c42e00034f800000000000013d030e000051cbb63370002a449a2d6e0ab8e8c00040900036203c400069534d4302000000000000000028a0000d0861305580000000005779a40ca80000000000d6022202c344000015f23f1331ba000000028080000652792d7173433663e00011fc0004b98f1d51a7961560e58000878000000110a6c15c8b7a99b08330003010d980000d71f500000002058000000bd10000000000cbd5162a39baa0000002468000000000000024e018000000000000002a0de0f0212f4bdade4c560000000000000c8d26aa8757323dc641979121c000285204580a80000000000cc0000000000000d6c4b7215899c8ed000378c0003570000000000db30002ac8b5e0005e9ad7800071115f257c5260006e9000000000056a31c40004a233618800000000c780009145a50000000c6c0005ec8240a1a41818912580000005ce08f800073a4b78c9000087665d000148a9310dc80000000000000c612bc9ed00000000009096260e2c5300e203b3124c8ad9b00019345600004b800000006e000000000009a0000000000000000000000000003039e34a68000000000155c000000351400000039b94ecf888ff36e969c000d175a480f0610000288b258ba8acd3913854470bc5000000000000000015dc00000000000000000002a2800000000000029a40000000002bb0000de0000225d1de1ba00020681b02a20000001ae8bbb0b7b580ec061d67593d4e6475c1c38a9d2c6c5901d330c00000037e10d8000b7d12093cc2d43491ba000000078500000000000001838000ef062902580000002ad0000000000000000800c0020058008026003002001000200000000000000010068000006004001800401200000100040040010010014006000001000c000000000000000a000003000000200500180000060000000000000002004000800c000000001c0040020008010020000002800000200400080000000000010000002001001000c0000040050018006017000000000a0030028000000001001800400200000080040060020038018000009004800400c001000001800200500000240040090000034000002005001401200d000000c0040010038004000000000800400600f0
  | 24 => 0x6ef000138525e000000346c0000006d2000000025d58a221152a8084c098d0bb22dc31809c400000029d0a3834800002980013ba0000000000ca2cdf00000007660000ac0cb17d41c830897c027616800000005c40000001854cea1b8000150c000d1436d80000000000001009afa0003c80000000000316000070caf30000bdd2b4c9f1df86358de47f00000000000845d680013a62c6000000120c0000000000000000000000000000043900000000000000c08ee80005748000000000000000000000000024847e8a1727e80006e4b0a41608606560005f28bb40000000d980014c80005b2000110c00000000000000000000f24000000000195c0008130000000eaa00000033b982a00000005c45d600020d062c0000000000000cce0002c191d18f01844d7800000064270d2d402720623d380013b60004f582e914627a311b0d436800020b1ab80005df000000000000002100000000000002ce15c200000000000000000000000000000000000179c0000048e3c000c990001990000c2700021ddc2097808310a46160001f100007e20003f808944dc06d6e600014789385f180000000000000000000d8e0000e540000720000000000a860000000e40000713b1d95a214413e990d3a200054b0969998ac61381fa9bae37100014bc538ca80248d4800000064a87c983e0002eb38240009ae4fab64175c6710000000000bb24ff03a850620c08296d40009fd000119d9ce4cf0000d3c73cd2f6c897ddb6c0002ceb000c70000000201c23e3265d28000ab000000000000001ad0001ad527ab7221b8b612d4c9b65819959ee000000368c00000000000002787393b38000f240000002901a74000500a0b40007d5547b71d17c0d60940000000a1964e81f4a6c369000000000056b48baf615feaa92b40ef00009f800000000000ac00000000000cb000000121ed5630d8e30b6cba01bd0a2957e3110000000a3cb3000000019c60d5616000060200058ca93d0faa270e2828d8e42c80000d6845abe22d681f00009d400000012ce00021a80000000001ff00006fa00000033100000000002715594493000000000000057900000007890001d240007841eeaa898d694a43d04400000005371b6129e8d2533278894e4c40700b9c00000000029f40008f40000594000552000039d8fc3772768000d6e8206852f68d0e00000000003360000001b08f38000084800000000006a00016e88ea01f80000003b24d0a818000c2e000067c00000000008391660503a40db86be1f87030001ab8ac558e8ea000033d6dcac6c00020400000000b8b1f00000004aa7b470294ac0d4a5257d9d7d58e6ca3488000000ab93f880640000a722992094aebca6d637203241fd00000000000002b4800000071663000000000000ce000000000000000016b06523aa1
  | 25 => 0x32c80000008ab6d8882538e00066922a806868a10896356ead4659a80101dc000000000000000000011380000fc00000000000000000001bf247c559b53000000070684c973c0b022080000000000000000000a1b00004840000002b0000015a00000000000000365f816a9a2400018e800190002511618651a600056d850c000e1f590173c000000000123caf400000000017e270d38d862941a0000000000c800000002978000000000009c00086c0000eb40001ca50780000007b76a9092033272651883756a800000000014a012e6c108480e22a910e9a552107cd6b928e400090d00001545a474744d91dc0001f657b00001a261f59d026d4ac31c0ee33f5b82b9748600015b285b4528461330bc000033f9a3881e0001d1800041e433264011c0000c416ac00000000006a4be241c0002925598e131aa9b70000c18000000097c2f00000000000000000156400089f1f492fc00000000000000000000000000000abb60e00013c017a14a351c0006e36548000670bd75ed8b54d727ce3d000007fe0005648001658000000000000000000000000000000000001af4000000171cd321c658283dd95a60d00000000000004fe37b0dccbf700000005d23c23ad35d4ef481f3fa81fc000000000000168800000023b0b340003d5000095c000240800042acb20000ed800000000000008f41a52308a9800047b5de0000000000000291d81c0001f90000866000287a839310000000237c0004e300017c800000000028dc90e6826b200001f000048922902c4dcf43400000000000de80007880c06b580000009d00000e4400058021833fd8bc48c6cc80010e80001288001912000293000101e8d83f380000000003ec9f6c65400062329701a061c6678001c5858658100000000000000001bfa6920002e085868fd00023e0ac80001b18000000000000254000000000000000006eb0000000000c9158ba62420800023e80009ce00005a12800001a3182800169e6604d68001248be73a5800155035e000074000000000000000000000f980018501972159a8085a3a269d94840000000001dac0000000000e616ee00000000006140400a113c1888d5100000000007760002e995847e60000000b8cb904fa1aacb3c02a643a4756cc6fb00033d0000b452fd80018c200000007802f24201f4000000023c057874400000000000000006a12c3800012e0005ff952d87e00068f000000000040a087c0000000000000a2400000000000000000000000f46c0964207e8c1ccdd0ad19297da1c30000e0000000041c000000000009c23700000005b00000000b282cc319c00020700000018ba00000000003b600036284453f62d70000000000ad255e8ee40003680000c2400000003834040000000002334000
  | 26 => 0xec880000001826000432b4d9b5600067b00009289a2398961000000000006b068e3af3e7800000000041f1dcc0001b10000000000000603a57400098a120000000054c0d0000000000003180000003340000000000a9800000000006a643ab314000e0100023793229930000000000000000000000000000000000000000000914000000000000104400066080000000000001f5d376000000000000000021227c91528f52231145a124b400021047f84c60cd367c7acb3e080800000048000022450ce0000000000000e171ac80014ce3233eb0000000dfc0002db00000002f7a49c5ba9ac00035a4000000000083c000bc60069691c3a0005fe80018ac2d300000000000003ca8000000b980000000c16000000000022400000000012900000aa9098aae470000000000000000000000003d06cb80009f28c5000000000000057030c925257c0001ac823aafe2ad000000036b1002fe4c646f00000be85e200000000000000002691cc00005ac29c9e68d522c469b9c78d12ba42b30000e0445600013917e42d60001ead66c85a70b27dc0000002ca000000000050e000092000054e0001a0a71c6c58000000a4d07a304176ec8c3b6000000000000029502da13e3a0911c19c0004502f857080de3f68c542a08190872d54000b65000000000073e521800125698c00000008a0d6728d0000d4a0003a2000000000000000000000005b500000000000550000000000000000165200000000018eac33345a110000bef000371400000064717a8000b560000000204b612ae800000000067c8000a5ac5c5448000b1c8152c900000000000a980006ec346000080cd7c5353dc00000000da0000f4c09455b499966c0000005a08fe8dca0002602340000c3c0000000000000000000000000012f80000000002f0000000000009b800126a83200011c80000006aa80011920000000000000bfc00000006de000000000137818c0000ee800000000000000000002e480007ec58c5e7b2dc57aa9700000000000000002508000c9e1a2a3880580001eb97e88d0c02352280d14c7ef0000de5978ce158e113c21690a00000000006fe440a850b466636e12c78a2600071334680001df20f8114e1807e69cacf50142350000000a6600000018bc0009130000000ea657200000000000000001c4822c00000000ac2f600000004c4000922000215082ad380370b8c2149495b88000000c0a2ef000009854e39d8000adcbe84e7b6740000003fda3cc0000001dc340148c0003e58001930287172227400000000000000000002af800179800047e00000000000001274000000000270000000037e92f400000032d8001be000054400000000004a631e8b2a67b1b312b5c1cb8e000000000056d000000190200006c80000001a8162800000000000029fc6c88026e2
  | 27 => 0xb0a2f6672000000000008e000000000000004556265c24da000000000000000012ac00000038600000000000000e3a93f00014f904a2d125d18488766b36501c2416cc6d6b4000000000000036f1172c3804e80000000000000000a6224930810119ae0000000000000db84ce9cfc0001fe3fc800000035b0002c3000000000000000009c40000c5800000043c80015da0000000bbc000000000000000000002b336c0002c0000246c0004b710d8979c480000002174000d3c1f2800000007500000000000000000000eccb08000324145456c0000000000000000000000027f000330855696100027e400019329c16657aa7fa65a0c6c000037300083471c03e4a2abe40000000000000a2aa480000dfcaa60004440000a802af5718001516c140240ae912a5f853a80000000003e4800196677c0002a840000001912c2400000000008f4eca3d50ef00000007d824280000007e400000b40001b600000000006d1698000000000000000000005ff1058725b064733418e643849d56a825553ca7b52268eaca3aac809487059721ab6f8a985a1a40613c21ac000cf1197856d0e23ef5bb00008d41fb3d2800000000000000000000002e41eb0000da50002e34df2000000000035e37b4f780000000000000000000000000000000000022a800000000f0000000ca05d85519b400000006700000000a7c4cd29ed43000000016dc2fa7180000cb4dbe0a245d80000f400061280014660005d08c5c00000066b00017527b94630cb9c4402637aa08cbae1540f6856462058b61b01380007c0304abf153aa4a33d06c800087f000000171000035a000131a0000000000000069087b088000b3b0f400000002a1000016c5366f40001971868a2348f80012884170000220000000000000000080600035bc00029a597000000041312528e823600022f8a6534a3b0000000129a00000000000000003e5000150254d00000003a8bc32b2a65411a0000002fcc000b51669b098714000000236cd9a73c3240b940001894b030f458e5cc69680000001cb6dea5b0cf80003008000d8896920ca9554d40000e0223c6860000002ad000000001e8ac8af69ff000368428c98e5a32690c74a0522e28f839c33b08029dc05c28000032b8e0217e00020bc5fe00026a20a56087634138b989385ce2a10fac3aea6352080000000000000000000000000247112c7940002d6c00005e0002944000d48283357c0000006492be8000000000000000000000000900000002f28001b28af76940000000ab1534069d49c92c2fe800000084c0209930000000091000168edc03d300011120003a10001c040216380000dbc00000006f000068d05f8000000b6b000000049849a000000000048e552000105c000260b1d0d7677e00001ccefed273c8953c3cae0f0929bfdaa
  | 28 => 0x6e0000000000d0a2765b7aae00009540df8000454a4c4c0180c0000000000000c4806b22900000f25c42150f39744562110132984227c15d8000000d2100027258f6c3a00034fd582ade0e90e680005a00000000bb800061ba4d00000000000cf8c4ca2f0000000e5a0000002b3cfe40002d414c814c81000000000000000001d8496600000029680000000001284cfc37300010740000000000001c4200004a8001ab40006750000000df200000013280003052f5924a6ad000091877619124f074c170cc900000008961e33cf263c0004aa62883d566e0000000000000926000000000040c0a4800094c000456386501ce2e3c3000176a69b0001364a443886c380000000000460b3410e3f935180000000000000000932c16461a04852e00034e0000f66000000142c0001703ae800162200038829b09c40000000001b520151d2000000000054900002dc0006728000000a0b216160476235422602f57cc33c4e913400000000001a79b0c15600d80000000002a488084b80001a415bdbfcbf610c8000a3e00071180000004f145a9700cdc6e267e2e6ceea1f443080884d604700000000005ed000000155e00065f00000003840000000000524422800000000066a96a4000000000369d2fe00000005f13c60000000d59c28000217a8d800031e0002cac64e44a59a1e004661ff6d7363c000c0d4ef80000000002521f68b1200049b800000084d00019ad45a24f379005db5e0ff35c18cca2000046a36ed71483c50900005840002748000beabcd2e697b1852c205d197444e81dd0cb00000003e1114181800000000030e4000000000000006656368381640000001520000e80000294800000000000000000006211e6adfc0002373f402e40000003cc15fd264c064be1cb00008994f70ccce3ea25621032136c6aa0549d7812632509a82180002292318f9c728000000000166600000000000007b000000000009da0002d38000d630000000000000000270d62a6022d10000f4206841b8940a30000475800000078767c1fd10b06c343109100008c14508000ffc14d0000000986a3b62b8001698c0c0002670000000132000092a0001a82a10d922682ff240c00075b0f78a48000c5026d26f53360000000000f7800000029814b26c004080015060000002e5800029600009a5c0e6460001df4bb4d112dd00000000004b4224c0000000000001222da063600016be79b3b88d2c96475900016b985a0000a4117800000000013dc39e000000000142021e00000000000000c1aed04dedd153b02c96f60c400000002182db000206cae600014a8000000000000000000000000003317a41e44a90d1092ea150000001b6843f0000000000aa51708001a0c5f3000017d82ec642aa8000000cb60001f45190aa626b0001a6200000038a4000b8600
  | 29 => 0x5b185818e6c801a85ac0000000309e7472624b0000000a185790000000000000000000000000009d000000000000000016a4a9a1b60000000000000172c00000000019245c08ba00000000007500000000000000130ada000000000000000002ce44800000000f100000000000000c700009ae0000000001a940005e4924800000000000013506d60000799bb20001fc08ac0000000002eac00084900033a00000003d423dc0002f404599a40004911ef19f430e3620000000000be900027c519e0000002cc8b6809c3150001104b2700033401be00009580005f2de900024140000005b18544e08000000118000014a0000f8c00000062780012462176c20000000000000000169a00051c34990304a9204000000078c000000123c000000000089000053a1ca00ae0004d480000000004b9026044cbde63bb490deeccd00033bd7d8930382840c00024d00023591b2cb86d91984e9aa7100037e04fccb147300006d427355b80000000003dd0000000dca000306c0000003171d91100000292800000000000000007964fa0001b9c000a5d000356d6b200010b250175e000549b5ec300baa000235c00062200000000000001c18000000d931ef8000a585410000000e1c0002248000000bfb0bfa6d44267e969a2ad8000370000000000000000000000003810000d943b47990000000ce093c00000000860004cb0000000000561a09985630f00000019c45e90b4879c0008bc0002c9846239f00000000000003c537840000000003398da600000035f000000000009d4a6e00015a8000000ac011b0000000000623800145055c657800029e00000000000000004061ce02e64a82440000d585a10098000752a3f000000000036d0000000000d4e00011600000000001f480007b100000015ba10827584c1b24b1615b18fc38e120000000000000045421a85ea00062500002cc45a000000000000032b322800096d1df0a740000000000000000e3100000000008830000000fbcaf100030656020000001c3c00070324200011ca00007d9da52cc3cf4d383b0a048d525d800053e082466000000083b18014380000001a536c00000005158d38c1e000044800000000044637d00000000000000000232000100120800031c8fa80040004ad9a58000cc7000297dbc400030f37906980000000000d9600000015796946ba681a68cedcd445f00e8477acac1a980000000b10fc993800060431387d4000252000019000052700028856840005dd0000000000000039829c78f363b02d434793000296c00000000000000000d7000148000003200000000000000002310000a70000348800000000000400000000000001afe00040480000005e720814200003a03b1374d99058a5c9000000000000019a15d0d420dbb0901e000035e288000007400035b41
  | 30 => 0xd2947d80017e89aa00012c0daa0001d5000142c7e12f418b400000025b0000000000000000115e00026e8370000000000000080a41250f8000000dd86acb77922c0001d700000220000a62f7c0000004652a1442023b01810280004400fb80488700006d3000003aa09445b430000d983f10c0c000c6e4f218d463439c46d00000007295460f195b400044c000192e0000003458c761e1000000000031324fb5d800000015c25f40001074f9a2c00004ab0eab42123069807e80000009ab00037bc2c6df7590a2515f04c8236379c6ce65504fb6fd5c4b2a1d3000000000000000002e86474d300001d2d8d45b3658000bc70000000000000000000026c000000000000000000000012d600027d8c64000d530650479c16000206801c91600000036a82465232770ed4428cde241a5e88e25d563313b000000059f8e9417688e32d0000b3805156faee000000000007ad6e07f74eb25e498448900005d4000acb0001fb0000000211a50cdd0aba0f48aa00009c6327a1cd8f2000246a7a4cc4c9a2ba3600000000000000023400000000000000005a000000009ce00023800000000002308000bfe4fb1f7d70a0006179d5c4ee01604780014f40004970fb1726cab00023900c03c50000b40296000000000000000000000002c0c0f1648000282d9a46e8b29c140000000000000000000000000000000e3624000000695a81cb22a0a0000e252c424768780000006971cb87316462d914800010c83410118e34e984df312acb53d48515392d8812464163505d800000067600000002e80000000354000281b58480e0000000000000000072800000000018a0000000000000211990c00000000004840000ec2f90000000568261c00000001400018a600000035e1504000000000173e00063980013240000000b314a671a7043768000c485d835c0aea77700026180000005ee376c0002860000000000ca53e283040002fe00000016fc4b14141b48dd4a04000000188086300028980000cf62580000001bb1040390000dcb58680008c800000000000001fc0000001144d1f1db894cf9039b4858870000000302800000000000000009f070028221f82ba75100009e4000d6a00004d00009581e5310d57c69f3a50450de6ae40619f0c0004fc00019bc0008300001d488500000001db40009571f800000000000000000e100fa06d8000000000000000000000033a00000009844cba440000000000025800040f5c780004da9b10000000000000000000000000000000000003920000000518b1234a2c1c000d5d5550d0000000000017f00007d0151a02d9ea00045a0001834d20000000021a26700026cd9b22840000000000000103165c8280000000001bca5e200f800147a3c1005a73510e96500027b0000000697000000000000015d89fecf33
  | 31 => 0x69900016f81240001b858247eb0000000946a5826398200009e6470936c0004af00028780000000002b540009bf00000000002650001b91a08b0f1ce80009784a500000015a60002ab3774000000272afac00075600000000009c2000000136400000038ac00093b00000010dc1a63b50000000a302dd800013200034400009de0a116f00001e6ad6127000084e5716ff9aa08cc2052a52b700002cf6b8b0f800000000030c13740000001e7d61c00000000000002b93ee8f00000c9c00000000008ad0000cd5a16000000000153646e00016e1bccb941a8b3b595400000036700000005d62f2db0a000040272d6203423998000a0200000006f97625f642a967db8ce1b57290d000000000014f00000000000000000dad000000167200000000000009020000000888119000000000057e5c6000000000041e9deda3200070f23c98540002cb26f84d890142184a933c9d939e8a205f000000000000006fa6631b3cc969b0000000000000000000008022b300021645d430c2a3abc09360001fab50400a0000eca52d9a25b051a800000000000000ec0000005c18038000b950caa704ef27fd647a5f8000000000000000000070219999f40004570498000000000000000000000016f46fc53f63fa62d0da00062081480000004a320900000000002fb82f000000000005e6000395800096ad4025c25c55600b542e0000e4600063199fc0de99f3920000000000000000000000055a800000057d05410f06424de1458001180c7d4a3a084000b67000000000000000000000007350002e04000673000000000000068980018b6b2200000011a240e00038440001ec4ba82790061ee3a1800112400066d000044e6726aa211c0000000000000000758022000000000000000000000001c106752c80000000000000000418800000000013133c1b9c25400000000008395ad038cf445b10000000000686699aa2846026033682f800000023b2801bdc7270000000d020005328f2160c99900000009e80002c400000002bc0003134f8c9d749d0f804c60004a080000000030002c60f16000000099815c677000000000000000017b9ae6d9e0000a04000bc164a10e50900000003454f5c9fa6fb15e16a60000000050db2ca700022c91ec000165800000000000000000000000f5000000051957a00011702390000ce800047928d80013040000cc000000000001780000004545170000ca6c6262c2ef40006444ac80780007bb0000000d5e6ee5149fcd2508f01ec350c3e20000000bb183c3ac2d3045c00082a000000000084f00009c87b40000002b987f600041b214000000000006896e6000601800003400005e35340000006ac25dce280000000000000b895e100004ac43e0000000fc64cd000000000005d1a69afd8d00000002c941ec0000000000
  | 32 => 0x1a7a5be0e200000005610b200000009150000000000000000000000000001cb328b8256730b80000005b92c10884f0600000032844ae0000000000d620000002d21398c08000000057e14040eb4940004dc0692ab579026a400af10f5e0ef718000009a00000014c0c7c000000239c8640006df000000039003c00001fc0003f70c100000e100024d970056a0002cbc00000042f9c5c320000367059d02e0000000001bac788512260d6f4000000000100816c3c10615c1872a221000120000000000000008530000000a90000000000000046d00000000002df40280c49960e80000f99b92d66221a15d4442d401033519767c211f9a8939095c1122f740ee00000034380000000000000ba435d580057800000000000000009e71f708d00002aa234a3a45407e55c380000008b76c50001bd07252fc80013bcbbf0d827c06f83c312c81190bc0000001bd85e46ed1948000000ca34c284b40008350001bc5bea7060000000862a7e38c800000052a62aabd400071304d0000000a6d2e280018b43a723a8000842745000000174e27b2d9985030c2fc00026e0a3815c0001e5d4f08b10050000660dfa00017ac0700005258000000dcd00000018a8000000000032813f00021bc0006f800028457a00a53fb000109400054000000005dd6bf33eca8880d5060000000a901118000aa8000269a2f4d4e914000000000015200000014d67bd00005c88440003fe1f4d83a5d30000000000000660284d4de83400000000000000000514000a3271400016ae0004538000000a8700018680007703df000087a43a17d8168dd27bf0001c2852258f00003c800020a03d95189920000000000000aac1ed8000000361383a149056cf20648001080ad758d00005fa091446813c50a5f468136540000005fa80000004450000000f829e149011747a2d65000241c0000007168001c240000000000000000000000000000015280008b200047400000000002730b0400000033c000018c306000080597e2da00011bc0007ad0001dbc00033235e8f30000d2c575a3c47e63e40e69a31b5000065300a40000000000000f6446514f2729be60002d9000125abf842720e85620000002d0db8677200004f498ad775042b9ce2aa4443d8000cbecdc22d8fb445e6ec3db24f976600032e800000000000000000007e071512198760000000cc40007c72f19961b6e0000d082141480000000000a2e00039a14000000001c292b00005e600006d400000000024e4a0a59300014a01848cb00000000000003a780005680000000ff52545072a829cc0006c6000000117e0000003750d00c521b0317ca2c9dc3859e90000000000019c0000003350001138000000000000000000021a400000040b0000000000000000189c0eb00000000009b941f80009fc0003060000000974
  | 33 => 0x2de15fa1332c8000000072f0000f656da6370000000000dfb3fc0000474dba00021806b8ded0000000000d7943e2ef80000000cf0031c380836b10001bb80000000ab8258000000000000028d00000005dc000581890c000e2000000000000000001cd800000000013a88060005a5800129c0000001381a9231f6c6000000000000000000009b7463b1955b0c314a980000000000c100000007684718001b6ab6e05983b596a000674b288d3400000018f000030d00014b82c20006a58000000000347a9e508463d000000400084b3141ffdb02b3c567086911400000013d80000000000000000000585896c1a6c6968c170ce420000002b111dc4e80000c815dc0001170000000000000000177200000000000000006af00000000000000001c000003a7000000053d645a3e92a23d4235aaf155600000007c05048700bb8ca0aa27cc0000000d3a5e16d10dd451e2b72310000a12c4547c8f480005d05ea000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xacd82103634843f5ad02206c690802b560440d8d210fc6f43c41b1a42008dd87883634843f5ad03106c690802b560620d8d210243f42ee131a420087d85dc2634840717d09b84c6908022f6137098d210043fc2ae0b1a420487c855c1634840117f08b82c69080e2f2117058d210046fc1ae0b1a42008ef825c163484011ef02b82c69080237e1d6318d213fd67c12c631a4287acd829cc634840153d09a98c690802a76135318d2100566c10a631a4200a5e85d0c63484014bb0ba18c690802b36084318d210043fc2ae031a420487c855c0634840117f08b80c69080e2f2117018d2100c6ec3e6031a4200a5f854c063484014b90a980c690802a7e113018d210054e4226031a42008dd870c063484015ab02180c6908023761e6518d210054f424ca31a4200a9d84994634850159b05328c69080237e1d6518d2143567c12ca31a42008dd8799063484014bd0b320c690802976166418d2142d66c14c831a42008df87590634850959f04b20c6908023761e6018d2141d66c14c031a42008df8758063484014bf0ab00c690802972156018d210054fc22c031a4200a9c84580634850559f04b00c69080317dd67518d210054f424ea31a4200a9d849d4634840159d043a8c69085ab36087518d210052f42ce831a4200a5d859d0634840159d043a0c69085ab36087418d210070faa4a831a4200e1d54150634840153d09a90c690802a76135218d210b56b40ea431a4200ad581d4863484014bd0ba10c690802976174218d210b56b40e8431a4200ad581d0863484014bf0ab80c690802972157018d210054fc22e031a4200a9c845c0634842d5ad02380c690802b56047018d210046f438a031a42008dd87140634840153d08280c690802a76105018d2100567410a031a4200acd82140634842d5ad02280c690802b56045018d210046f4388031a42008dd8710063484014bd0a200c690802976144018d21005674108031a4200acd82100634842d5ad02200c690802b56044018d210b46f43c4031a42008dd87880634842d5ad03100c690802b56062018d210056bc0a4031a4216ad48148063484011bd07bb4a6908123761c6394d210252f428c729a42008df835d953484011df04bb2a6908023de057654d210246f43ec6a9a42008de83dda43484071bb0e31c869080237e0d7650d2100477c12eca1a42008f7815d943484071bd0fb1a869080393d4b639492100727a90c72924281ec42118e524842d9a8e231aa490a03b108463549210066a31ee2a924216cd47118d42484019a8c7b8a849085b359c463cc9213ff62108c79924200cd4635c7324843f9a8e3b1a649085b351c4634c92100c7b436e29924200cd463dc5324843f9acedb1e42908723d61e63c85210b56b41cc790a4216cd67618f214842d9ace431e429085bb19c863c8521
  | 1 => 0xf0e886c99080237e0d76553210046e41aecaa642008fb805d954c84031f100bb2a99080e1fa1f655532101d1f426caaa642048be87d9154c840947d0bb22a990803399c971d8f210243f42ee1b1e420087d85dc363c840717d09b86c7908022f61370d8f2100477416e1b1e428acce72cc363c84031bf0e986c790a27339c930d8f2100c7bc3a21b1e4216ce67244363c8401da260886c7909b6b3a0b6398f2132567416e6b1e420087f855c163c84090f90ab82c7908022fe117058f2101c5e422e0b1e42008df8758c63c84031bb0f980c79080e2fa107694f210045ec20ed29e42008ee829d953c84090fd0a3b487908021f6147690f2100477414eca1e4204a6f8259652c84018eacab8ca59080a1fa1f6554b210145f43ec8a16426dace82d8f32c84051bb0e31e659080a37a1f634cb2132567416c6996421fcd471d8d32c84011bd0e31a659085b351c4634cb210046fc3ac61964216ae682d8f31c8445d8cc531e639087e3de1d63cc7210fcebc3ac798e421fdc6739cb31c84451ef0cb96639088ab9e1972cc7210e56ac366598e4222ec662ccb31c843f3af0e996639088ab5e1932cc72144637baee4b2a4200ccc73dc965484019a8e7b8aca908021fe1570595210045fc22e0b2a42038bc845c165484011bf06b82ca908023720d705952100477c12e0b2a4200ccc73dc964484019a8e7b8ac8908021fe1570591210243e42ae0b2242008bf845c164484011bf06b82c8908023720d705912100477c12e0b2242008de83dd954484011bb07bb2a89080237e0d76551210046e41aecaa242008f7815d954484011f700bb2a8908063e201765512101c3f43ecaaa24203a3e84d95544840917d0fb22a8908128fa1764551210062ebaea7b1a4200a9e84d4f634840153b09a9ec69080297a1743d8d210052ec2e87b1a420487e85dc363484010fb0bb86c69080e2fa1370d8d210045ec26e1b1a42018df874c363484014bf0a986c6908029721530d8d210054fc2261b1a4200a9c844c363484015ab02186c690802a7a1265d8d210054ec24cbb1a4200a5e8599363484014bb0b326c69080297e1560d8d210052e42ac1b1a4200a9f84583634840153908b06c690803175d475d8d210054f420ebb1a4200a9d841d763484014bd0a3a6c6908029761474d8d210070faa4a9b1a4200e1d54153634840153d09a96c690802a761352d8d210052f42e85b1a4200a5d85d0b63484014bd0bb86c6908029761770d8d210054f426e1b1a4200a9d84dc3634843f5ad03386c690802b560670d8d210046f438a1b1a42008dd87143634840153d08286c690802a761050d8d2100567410a1b1a4200acd82143634843f5ad02286c690802b560450d8d210046f43881b1a42008dd8710363484014bd0a206c6908029761440d8d210056741081b1a4200
  | 2 => 0x501893100556c20a03126200ace83140624c40159b06280c49885ab9a04501893100572c08a03126200ace83900624c40159b07200c49885ab9a06401893100572c0c8031262008ee87100624c4011db0e200c4988029ba14401893100536c28803126200ace83100624c40159b06200c49885ab9a04401893100572c08803126216ae481cc0624c515d8863980c498802b361f301893100763c0e603126216ace81cc0624c42d59903980c498a2bb1207301893100765386603126200ec970cc0624c515d8e21980c49885ab9a06301893100572c0c603126200a6f854c0624c4014d90a980c498802abe11301893100556422603126200ae7814c0624c42d5c902980c498a27b10c5301893100567c3a60312628cacd874c0624c401c9f0a980c49880393215301893100747c22603126200e8c844c0624c401d8f02980c49885ab3a0530189310b56640a603126289ec4814c0624c401d9700980c498a27b1c41301893144f65082603126289ec9104c0624c42d5cd02180c498802b9604301893100763c1a203126200ae483440624c401d8906880c49885bb15cd10189310b573c02203126216ee380440624c401dc4e0880c498803b85c1101893100763982203126200ee230440624c401d8a60880c498803b84c11018931007609822031262038be841da524c40117b083b4a49880a372197394931014ea40ae729262048ed8718a524c4094dd0a314a498803339cc629493100666b98c529262048ee87d89524c4090fd0a3b484988021f61476909310146e432e721262038ed8718a424c40199ce63148498803335cc629093101c7743ec4a126216cce7618b324c42d99ce2316649885b331c462cc93100667b80c59926200ccd7018b324c4ffd8e203166498803b144062cc9310b673388c5192628bec43118a324c4459c8e3b12649885b391c4624c93100672316e29926264ace86dc9324c445998edb92649888b711c7724c931116663b6c49926222dc471d89324c42d9a8e2312649885b331d8624c9310b6e2388c49926200ace87189324c40199d0e312649885b339c4624c9310b666388c49926287ec471189324c42d988e2312649880333dc0624c93100666b80c49926287ec710189324c401d8a20312649880a75a1f714c9310e66a3b6e29926200ec462dc5324c4459ccedb16629885b399d862cc5310b762c18c598a6216ce67318b314c42dd8ce6316629880339dc062cc53100672b80c598a6200ec73018b314c401d8a603166298803b118b32cc5310fcebc3a6598a6202ad4864cb314c401d88c4996629880e2fa1370d97210045ec26e1b2e42008de83dc365c84011bb07b86cb908023ba0b70d972100c7bc3a21b2e420487e85dc364c84010fb0bb86c99080237a0f70d93210046ec1ee1b2642008ee82dc364c84031e
  | 3 => 0xbb126200a6e851d3624c4014db0a3a6c4988038bd5254d893100716aa0a9b126200aae84d4f624c40155b09a9ec49880393d4e53d89310053742e87b126200a6d85d0f624c40159d06386c49888ab360c70d893111573408e1b126200ae5811c3624c4011dd0e286c4988023b61c50d893100557420a1b126200aad84143624c40159d06286c498802b360c50d893111573408a1b126200ae581143624c4011dd0e206c4988023b61c40d89310053742881b126200a6d85103624c40159d06206c498802b360c40d89311157340881b126200ae581103624c4014df0a986c4988029b21530d893100557c2261b126200aac844c3624c4455cd02186c498802b960430d893100477c3ac4312628bacf83588624c40155d09a90c498802ab613521893100566c18a43126200a6e85d08624c4014db0ba10c498802b360c42189310146ec1ee031262008dd87cc0624c40159b05980c498802b3e09301893100c76c3e403126200acd83c80624c40159b07100c498802b9606201893100566c18403126200ae581080624c4059aae6880c4988073c9c1101893100768982203126200ee220440624c401dc240880c4988023b61e651893100557424ca3126200aad84994624c52959b07328c4988023be1d651893149d67c1aca31262008ed87990624c4014dd0b320c4988029b616641893149566c1cc831262008ef87590624c52359f06b20c4988023b61e601893146566c1cc031262008ef87580624c4014df0ab00c4988029b215601893100557c22c03126200aac84580624c52159f06b00c498a3eb3a1b30189310b566432603126200ecb604c0624c42dd8ec6880c498803b8d811018931007e0982203126200aae84dd4624c40155b09ba8c49885ab360f751893100637bacea3126200aae849d4624c40155b093a8c498802b3a0c75189310b566c18ea3126200a6e85dd0624c4014db0bba0c49885ab360f74189310053742ce83126200a6d859d0624c40159d063a0c49885ab360c741893100717aa4a83126200acf83550624c40159906aa0c4988038b550541893100557426a63126200aad84d4c624c42d5cd03a98c498802b9607531893100727a9ca6312628eec43194c624c4015cf02a98c49885ab9205531893146f6218aa63126200a6e85d0c624c4014db0ba18c49885ab9a07431893100572c0e863126200ae78150c624c42d5c902a18c498802b3a0f70189310b566c1ee03126200ace839c0624c51959b07380c49885ab9a06701893100572c0ce03126200a6e851c0624c4014db0a380c498802aba10701893100556c20e03126200ace831c0624c42d59b06380c49885ab9a04701893100572c08e03126200ace83940624c40159b07280c49885ab9a06501893100572c0ca031262008ee87140624c4011db0e280c498802aba1
  | 4 => 0x3504091bd0fb1aa6a0802b3a0e20d894100477c3ac43128200acc835886250409878eaaa0c4a080a2f61370189410056741c403128200ae581880625040596ae8880c4a08073c9c11018941007711022031282008df835da52504011b906bb4a4a080237a0c76949410046ec18ed29282028bc865d2525040727f0eaa4a4a08030f9d9549494100597c12a929282048ed8718a52504094dd0a314a4a08038b55062949410247743ec4a9282028bc865d5425041317d0e31284a08121fa14768c9410043ec28ed19282028bc865d232504051e9023b264a080e3da1b714c9410145e432e81928200c9d7418c325040195ae831064a080e2fa1370d97310045ec26e1b2e62008de83dc365cc4011dd05b86cb988023b60b70d973100c6ec3e61b2e62008df874c365cc4090fd0bb86c9988021f61770d93310046f41ee1b2662008ee82dc364cc4011db05b86c9988063761f30d93310046fc3a61b2662008fb805d954cc4031f100bb2a99880e1fa1f655533101d1f426caaa662048be87d9154cc40947d0bb22a99880a3761873553310252fc1acb29e6200c75655c653cc4d759d07b14c5988121fa177098b310043ec2ee131662038be84dc262cc40117b09b84c59880a37a0f7098b310046fc3a613166200acf824c262cc4011df0eb10c59880a3761a7394b310146ec34e7216621fcd471dd932cc445b88e3b92659887f351c6624cb31014eb43ee29966200cd776dc532cc4014bb07286ca98803b44c110d95314ae2fbaee6b2a6200ccf731c9654c4019ce20392ca98803391cb71595310043fc2ae0b2a62008bf845c1654c40717908b82ca9880237e0d705953100477c12e0b2a62008ec825c1654c4011bd0f982ca98803331cb305953100c6e43a60b2a6200ccc724c1654c4031e90e882ca98803391c910595310076898220b2a6200ed130443644c40199ee6392c89880339c40725913100672396e2b22620087f855c1644c4090f90ab82c8988022fe1170591310046fc1ae0b2262008ef825c1644c4011d904b82c89880237a1f30591310066639660b2262018dc874c1644c401998e4982c8988063d21d10591310067239220b226200ed130441644c4011dd05bb2a8988023b60b765513100477c12ecaa262008ec825d9544c4011f700bb2a8988063e201765513101c3f43ecaaa26203a3e84d95544c40917d0fb22a8988128fa1764551310146f436e6aa26200c5f65dcd544c4018daeba96c498802aba1352d893100556c26a5b126200a6e85d0b624c4014db0ba16c4988063be1d20d893100557424cbb126200aad84997624c4014dd0b326c4988029b61664d893100537c2ac1b126200a6c85583624c40155f08b06c498802ab21160d89311156643261b126200fc130443624c4018daea3aec498802aba1075d893100556c20e
  | 5 => 0x90031b5d672d90320243f42ee1b20640087d85dc3640c8011bd07b86c8190063761f30d90320062ebae61b2064008df874c3640c8018baea986c8190028fa1774590320061fbaea8b2064018bc87501640c801878a9bb2a8190021f61676550320045ec24ecaa06400c3c545d9540c8011f700bb2a8190063e201765503201c3f43ecaaa06403a3e84d95540c80917d0fb22a8190128fa1764550320046ec30e6aa064009cd821cd540c8018dacb394a6190032b5927290c320062eb2ce72906400c9d649ce420c80199eed2926419273711c6524c83200667bb2a4990649bdc471549320c935b88e32126419267711c5424c8320b4eb43ee29906400cd776dc5320c8019aeec38a64191b7711c6634c83200667bb4a6990648edc47194d320c80199eeca9a6419237711c5534c8324c6e238c869906497dc47150d320c82d3cd0fb8a641900339ddb714c83200673bb0e2990648bdc7731c5320c82d1bd0f992c21905ab5a07325843236f6210e64b0864168dc874c9610c82d5a902992c2190021fe1570584320243e42ae0b0864008bf845c1610c80717908b82c21905a3721d305843200c7a43a20b086400ed130441610c8070f90ab9ec8a880e1f21572d915101d1f436c8aa2a20287d85dc3635440717d09b86c6a88022f61370d8d510056ac0861b1aa200ed23044363544011bf0eb18c6a8802b32096318d5101e1e3a2a831aa20487c855c0635440117f08b80c6a880e2f2117018d510056ac086031aa2008ef825da43544011d904bb486a88030f9d95490d5101c6ec38c721aa200e1d5418e43544071bd0fb1a86a8802b3a0e20d895100477c3ac4312a200acc835886254407878e8aa0c4a880a1f61770189510056741c40312a200ae58188062544058eaea880c4a88073c9c110189510077110220312a20a87e8718952544011bf06bb484a88023720d76909510046f418ed212a2008dd831da42544050f90cbac84a88124fe1d54909510061f3b2a9212a2038ed8718a4254401c5aa831484a880a1f219755095101c7743ec4a12a2038be841da325440117b083b464a880a1f219758c9510062ebaec7192a2048f686dc532544050f90cba864a8803175d4630c95100636ba8c4192a2038bc845cf655040717908b96caa0a5b0fdd774595410043fc2ae0b2a82008bf845c165504011bf06b82caa08023720d705954100477c12e0b2a82008ec825c165504031e90e882caa08128fa1b65551410243f42ee1b1a820087d85dc3635040517b09b86c6a0802b560430d8d410076918221b1a82008df8758c635040159904b18c6a08130f1d55418d410043fc2ae031a820487c855c0635040717908b80c6a0802b56043018d4100477c12ed29a82008ec825da535040187cecaa4a6a08123761c6394d410252f428c729a8200e1d5418e5
  | 6 => 0xfc6f43e64b0c641fad681cc9618c83f1bd0f982c3190023760f70d95320063cb84a1b2a64028f687dc5654c8019aee638aca9900339dc871595320043fc2ae0b2a64008bf845c1654c80717908b82ca990023de0570595320147a40ae0b2a64008dd83dc3644c8051ed0fb8ac89900335dcc715913200673b90e2b22640087f855c1644c8090f90ab82c8990022fe1170591320047bc0ae0b2264028f4815c1644c8051ed03bb2a8990023d60776551320046fc1aecaa264008f7815d9544c8051e902bb2a8990023ee01765513200c7c402ecaa2640387e87d95544c80747d09b2aa8990122fa1f64551320251f42ec8aa26400c6f65dc9534c8019c8c2392a699003391847250d320062fb2ee6a926400cd4611cd524c8019a8c239a849907e37219718c9320fe6a30ae31926400c7575d47614c8031ef0e886c299002ada1265d85320055ac24cbb0a6400a7685993614c8014eb0b326c29908b399db32d85320fe6b3b465b0a6400a7785583614c8014e90ab06c299002ade1160d85320055a422c1b0a6400ab6849d7614c80156b093aec2990031d5d475d85320053b42ce9b0a6400a75859d3614c801c6ea92a6c2990038d55054d85320055b426a7b0a6400ab584d4f614c801caea729ec2990029da1743d85320053ac2e87b0a6400ab684d4b614c80156b09a96c29900399d4a52d85320053b42e85b0a6400a7585d0b614c8395ad07386c299002b560e70d85320047b438a1b0a64008f587143614c80156d08286c299002ad61050d85320056b418a1b0a6400ad583143614c8015cd04286c299002b960850d85320047b43881b0a64008f587103614c8014ed0a206c2990029d61440d85320056b41881b0a6400ad583103614c8015cd04206c299002b960840d85320053bc2a61b0a6400a74854c3614c80156f08986c299002ad21130d85320047b43861b0a641c8f5870c3614c8011ed0f106c2990023d61e20d85320056b41c41b0a6400ad583883614c8011eb0f328c299002ada1265185320055ac24ca30a6400ad583994614c8015cb05328c2990023de1d65185320056bc1aca30a6400ae782594614c8011eb0f320c2990029da1664185320053ac2cc830a6400ad583990614c8015cb05320c2990023de1d64185320056bc1ac830a6400ae782590614c8011eb0f300c299002b560e601853200572c14c030a64008f787580614c8014ef0ab00c2990029d21560185320055bc22c030a6400ab484580614c8015af06b00c299002b9e09601853201c5fc3ae9b286400c9d749cf650c80195ae9396ca1900e2fa1370d94320045ec26e1b2864008de83dc3650c8031bb0f986ca19003275d330d94320046fc3a61b286400c9d744c3650c80147d09baaca190030fdd2545943200c3e43aa0b28640487f875d7640c8018baeb39ec81
  | 7 => 0xbc845c163948015ab02182c7290034bd497418e520046fc3ac631ca400c9d7458c639480187aecaa4872900e3761e6390e520070eaa4c721ca4048ed869ca43948092dd0b39487290034b5527290e5201c6e43ac6a1ca403c3e7455161948014bb0ba1ec6a90029761631d8d520056cc0063b1aa4038be84dc3635480117b09b86c6a900637e1d30d8d520052fc2a61b1aa400a9c844c363548011bf0eb18c6a9002b52056318d520052ec2e8631aa400c9d7410c63548015b300188c6a90063761f3018d520052fc2a6031aa400a9c844c063548091d90cb9486a90063de1d10d85520066a308e6b0aa4008de83dc365908011bb07b86cb210063b61f20d96420043f43ca0b2c8404a3f86595549085b17b0db92a9210130f1d55498e420043fc2ae131c840487c855c263908015ab02184c7210021fe157058e420243e42ae0b1c8400ad5810c163908011bf0eb18c721003175d56318e420061ebb2a929c84048dd8798e53908094bd0b31ca721003875526394e4201c76c34e529c8400d2d549ca53908091b90eb1aa7210030f5957494a4201c9fc3aa92948404a3f86552529080787aecaa4a521002cbe095494a420261f3aaa8b0c84008bd84dc3655093b8deebb92caa100a3da1f71595420066bb9ee2b2a8400cd473dc565508019aee638acaa1003351cc715954200c7d43ee0b2a8400cdb73dc165508019b0e7b82caa10033cdc770595420067838ee0b2a84008df835c165508011b906b82caa10023de0570595420147a40ae0b2a84008fa871c165508019b6e6382caa1003361cc705954200679b88e0b2a8400cf0711c165508039d0e1902caa10063b21d20595420062ebaea7b1a8400a9d84d4f63508015b30018ec6a10121fa1770d8d420043ec2ee1b1a84018df874c363508014b90a986c6a100237e1d6318d420056a40ac631a8400a9d84d4c63508015b300188c6a10063761f3018d420052e42a6031a8400a9f844c063508071d90cb94a6a100e1fe1d65949423a537c12cb2928400c3f65dd1525080917f0eb2c84a10031d5d751d854200c7bc3a21b0a8400cd4611cd615080117f08b82cb9900e2f21170597320043fc2ae0b26640487c855c164cc8051ed033b2a9990023d606765533200c7d404ecaa664008f9809d954cc8070f90eb2aa99900e8f21165553320245e43ac8aa66404a3c8559154cc8018dacab94a7990063d21d105873201c5f426e1b2c64008bd84dc3658c8011bb0f986cb1900637e1d30d96320043f43ca0b2c6400a5d83941658c8090fd0bb86c9190021f61770d92320046ec3e61b2464018df874c3648c8039b4e0986c9190022fa1e405923200c7d404ecaa464008f9809d9548c8070f90eb2aa91900e8f21165552320245e43ac8aa46404a3c85591548c8018bacbb9aa919003175957394a320
  | 8 => 0x80000000c00000000004008000000240180e0060200000f004008020030000080000d01a004010000000080380301000c0081b0000100000000a000000000000040081100604c0080201a0040080200a0180080201c004000020460200000300a00000000016000068000000100380d01e0000680000606c0000400e010010000000000380200200c000020000000080000006c018010000000080001202801003004000038040120080000100c00400800010000090010020280100200c0040100000e0000100a0020000080c004000120020260140000003a000030090120000000100a00002807002000000000040000000a00004002803018068028000080000000001e00c0880a00000001001002008030010040100100000a0387d85dc3635500917b09b86c6aa0029761630d8d540056ac0861b1aa800d3854dc163550011bf0eb18c6aa002b62016318d540047bc0ae431aa8028f4815c863550015ab02180c6aa00e1f61770d89540245ec26e1b12a800d1c54dcd6255001a38a839ac4aa0034d15371589540069c2a6e0b12a8008ef87588625500747f0cb22a9298ce1f61b735525319caec36e6aa4a600c5d86dcd5494d3da3d09b9aa9299f347613735525301e1e3a2a9314a6008bf845c16294c0717908b82c52980347d4d7418a5300477c3ac4314a600cad745886294c0787ce8aa2c32980e2fa1072586530045ec20e4b0ca6018f4874416194c014ef0a882c329803b44c1105865300536c2843b12a600acd830876254c011df0eb10c4a9802b920562189530143f42ce5b0aa600ce4611c96154c011bd07b86cb218063761f30d96430046fc3a61b2c8604a3f865955490c7317b0db9aa9218030f5957494e4301c9fc3aa929c8604a3f865525390c0787aecaa4a721802c7e0d5494e430261e3aaa9314860087f855c16290c090f90ab82c5218023be1d6218a4300636baac43148604c3e755516190c090fd0a392c3218021f614725864300c7a43a20b0c8600ed1304416190c014bb07286caa18031e5c250d95434f62fbaee6b2a86018fa87dc16550c010ff0ab82caa18022fe1170595430046fc1ae0b2a86008fa871c16550c018f6ea382caa18032edd070595430066db98e0b2a86008de87cc16550c039b0e1982caa18063721d305954300e6c38260b2a860387f875965350cf94bf06b2ca6a18ea9e2016594d430061fb2ee8a9a86048bf875964350c6957100b2c86a1802ab61021d894300566c1843b1286008ef875886250c015c902b10c4a180a2fa1272d854300672308e4b0a8603a3f86591549484f0fb0db92a92909e5b61b725525200636c36e4aa4a49dd2e84dc954948e9a5b09b92a9292774bd07725525201e1e3a2a931ca4008bf845c2639480717908b84c729002b56043098e520045fc22e0b1ca4038
  | 9 => 0x1f50001e480013fa1780000000017c8e2025a520001180000820000000098001f380001d9dd89b00000000021a8002398001f880005100000000011320d18c0001118610c500015600000000000004e13500000000000020889e000228221996a080000fa0000000000d20000368000790bb80023019a80011610e9d09b10ca161000043807a151ab0b18001c380000003fa0401f2039f424d0b00bc86780b8c587701d1bc14a1e603319113c01801900000005d0000001b08da8000c78ab04680000000023b06212f82a8001140000000001eb1412012028000001a61389a080004412380019b80003600017fa3b9b58aa06f9619a411021e00014690a9bb8000001b49f986c2480b98b596297d8940810d4a308000000000b90c30001ba16e93a8001ed00018325386b0001f68001648000000d38000000000eb1208000dc8539081341b41880000640661121c718ea579800280a21348001600d719501491d85da269c0942892835a06a1103e01194598886690081000000494e21d8000001a4a5d0000000001a98002571eda3912ea198231a280000019980000011688000004f1c7a060000cf1361c60240001e72288000f489589c8000001ff2000f60000001fd1668000000000000000000850001868001620001578000000000000d30e79a50000c38000001e907082ba1488e0000a880005c8581759462310920859d71f78050000001d51228000000db9ac0000000458000e481780012d10b0000df1370001ea80007600014b22aa1181680011b99b1c894300000000000000000000019e81414419887c00003c8000c49c28000060000e58000000320000001650000d602f8c080a80004c1bd8ce0afa0f2448001ec1279700000002599591420ef8419e2848a2c11911b23205a0000000f40000d69ec80005b17a09c1ae9c69cf15580000018d80008f1bb0d7a1b87d92f0638652241cb8ba8e280701c229838a4d80024f20d80000000002da1a00000017e90780018a0001aa9c480423c03d00023715715c8e024f98397e11f973887a0ba42000001000004010080060000080100a0040180000000c0400001800c02804008000050000000000000f006010000080000000380100a00003803008008000030040000080900000400800000028008010260540a002000018008000040580000d0080000280c0080500100100a004000000080000a00100c0000000001601c000170040000100000203c018020040180000200a01802800024008000020080100180600e0000080200c00c0f8000000140200602200008000020000048100280000080a00000003001004010038010060080680001603001000000014048000000100400000400000800002000030070020400000201800401003004008008030000000000303e0040000100400
  | 10 => 0xd1a1396996d00f1ca00004b87e9011718949a70e41ba9fe8589e180017280021b0a90ed85b8010971d99ff9671a002a2248000e08c993d80682e97984f8b09d80000000d50001ef1b198ca140658c400000004615b0ec8000e60b402b0001b018d0000000000000001fc800072800003800194a070e809b8341e20521a90d92220001cd9e9a020c90000001198000001b90f10001510001e518980019d00002e1d69918a41fd83513024980007aa161db00022382c00008706e0ea0fd92c8d10091ae0d81520b495292c0001a30000450e123a8e51358c700009980014017700023e06190d21c0d017402d00000017680024712484280000000002f00005e8000000000ef0001fb91e1d186a10000c80004a9d60001ca80000025a24b9939e68001250001bf0000e18dd07b1e894c0980001b80000a18f680000000000000000005f9be8bf0f800021f8f90000a81d005f16d80003ba468001d302110485e0001e0a0aa1f000a3f07112d98f2419711cc03288a15a9878279658fc00018921200006c93f0000d99580bc0540001f580000009d10a1b28209fe0000ac9ab89680015f09900012801315a20c0001d39a815f93b21e8421170e38161a180000011c0000000808478b20f58fba492100db084218a4319e0000002190000f8a3680001e0000ea8518001820000000001448000000cc93e24a9c200022116c00014e8000001059f480000013180000000013e8001b516a1922231f90000000001e400000007d0550001bd0a98371268000151f110681b24583d8c88bb2580a50df87f0c28000001478002568f19c00faa338a00129630ed0691f600003a11504325617880010201a80c00019f8000750e99b309189f24e1c515ba251290001faa551a39af9368000ae0769d485006e9e80b2a5100024c83c153a5b8059808000000000000cb94f80008ea3500000000019414903aa540000f2a3898f83900024600000020180000a2170b38301860031cd0dea3ea319608001158001548000001818000000d400000012721c99780000000017c19c80d0000ada331692559fc0748000cb10406884e9828ab9312130c680007791d1e300021d0020121d412597216400fa3c8cd8f781e8e696380024508c06a80000000000011780000000022b00023d0000238ec10900000000e8000000480491730000000000001b88cc0080ff80006d0000000ac16b8dc0000560000000001cc8f70379ad0000000298000000f00000000000950001108d290e24b1b987814a8001d21089381550000000da1378a713225318418596f80012119c20b00000016e0ae9cf80000000023280017a9f180005292aa360001db8718d586700000000015c0000000171df8c810fa3f80008d0002529fb02211298e0001dc8000000002548f300009880010d9a1044a3597f
  | 11 => 0x201810629760ce91480007980016a92b09395d8bf8898af1b694c9d787b89a8c1a0e8001c41d881f9e39751f28001139b713d0891982519e58498591958ca800053250a258000630001f31a887a0a080005790319d9c18a31fa04099016b04d8a78000b7a4783184b22fa4414800019300018500009f81080000021800011e81588f92300024296797b83f06997b1419220910738001aa190a5908d9779961599708001be1ea00020915888a92e0000c20000e722000000000000022b8001f01da19719f00000e1c990980008600000019a0000001b38f09af1071681de94d20500b075a2c80015e0001a5901a04945026a0e0fc81383e8348701f20000248002271eb8000000000000002380188398b880000013c9b20000000818000000000000000cf8d88271260000401c10000001ac80000018a80020980000000002188b80008697d0000000002438001da8b81d107894f04a1028000fe1111f092a1ce24080d8000000000000831218ba21080008b0680a28000bd85099280020a0000c600000022d0888000000001c80000ee0001780d08b683391c80000002500022d9c92229cb2208001a20ad0198549df1e780011a8000000f38a395e98704c83101112890c9b794ba0c8b31ce93b932a2786ba5c84d237a2ea348a48961518978000bd15403b00022611f0001dd00000024a0cd2489438f500014d90f0000000002158000001398ee86085c0900000eb80000000018480022e0000000558be13a002a1681b9ef83094885700000015d1dc1bca0780000023d8000000000908000410000000002500001038c000000000000007e00000024e80000000023a18b0001ad8000000fb0b10838fe800059a1299903824c000001a030c10f20001569f80000aa9060000b500010b87f8848f98de1f71e000005692009a00005aa411ee13391896ca2a06d9308001331b608280007220581a25c23400009d9a69a786f008a009c58a117907c8931d902880015011a0881409498000000e88000228e325880000000002c8000000000000000000649298000000000e90000000001e11689c30be80025a8000dd9de00002900010c22917492ba400a600000016f0000001241ee80010501c8000000001bf9530000b700015080000020f98b89e8470000260001660b60ff0a59d2a5b1d588c9470a686007313922f0740fd0
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x3c00c880091500000000c00587802a2c18e20950821435011568cd1c0e6c2130c98b813000fa2009c0000a00e9228004a9500c11403061802064400c10050ea5854dc1635500141e96153735895400507a58541cd62550014369615371589540050ea5854dc162550012379855054d85320040f66054dd9540c80103e9815176550320b471245821cd540c801cc0724c11059531007301c930441644c40122f9855054d89310b4b124583c80624c4016c3924c11018931005b064e20440624c40122f9855054189310b4b124587cc0624c401a4431e15301893100691207854c0624c401a0c852113018931465b064e70440624c42d2e0984c110189310b5b0a6130440624c42d6c0984c1101893144eb026130440624c4016c3974c11018931465b065d30440624c401e43954c110189310079025530440624c401e83944c11018931007a025130440624c42d4c4915cc6294931007305c11018b324c42d4c491dc0624c9310b53124570189324c4014c497440624c931007305c110189324c42d8c68718b714c931007305c33018b314c401cc3704c062cc53145e31e1c624cb314c513cc2724c110d8f2100487e6154153634840121f985505418d21
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x22000324098e5530440624c401b004a9289822031262169302a570440624c931
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0xb09
  | 6 => 0xb0d
  | 7 => 0xb0e
  | 8 => 0x1549
  | 9 => 0x154d
  | 10 => 0x154e
  | 11 => 0xb49
  | 12 => 0xb4d
  | 13 => 0xb4e
  | 14 => 0x16c9
  | 15 => 0x16cd
  | 16 => 0x16ce
  | 17 => 0xb89
  | 18 => 0xb8e
  | 19 => 0xbc9
  | 20 => 0xbcd
  | 21 => 0x3c9
  | 22 => 0x3ca
  | 23 => 0x3cd
  | 24 => 0x3ce
  | 25 => 0x15c9
  | 26 => 0x1709
  | 27 => 0xcc9
  | 28 => 0xcca
  | 29 => 0xccd
  | 30 => 0xcce
  | 31 => 0x15ca
  | 32 => 0x15cd
  | 33 => 0x15ce
  | 34 => 0x170a
  | 35 => 0x170d
  | 36 => 0x170e
  | 37 => 0xd09
  | 38 => 0xd0a
  | 39 => 0xd0e
  | 40 => 0x1609
  | 41 => 0x160a
  | 42 => 0x160e
  | 43 => 0xd49
  | 44 => 0xd4a
  | 45 => 0xd4d
  | 46 => 0x1649
  | 47 => 0x164a
  | 48 => 0x164d
  | 49 => 0xe89
  | 50 => 0xe8a
  | 51 => 0xe8e
  | 52 => 0x1789
  | 53 => 0x178a
  | 54 => 0x178e
  | 55 => 0xec9
  | 56 => 0xeca
  | 57 => 0xecd
  | 58 => 0x17c9
  | 59 => 0x17ca
  | 60 => 0x17cd
  | 61 => 0x1049
  | 62 => 0x104a
  | 63 => 0x154b11
  | 64 => 0x40a
  | 65 => 0x44a
  | 66 => 0x188a
  | 67 => 0x1a0a
  | 68 => 0x16d551
  | 69 => 0x1556d1
  | 70 => 0x16cb51
  | 71 => 0xb56d1
  | 72 => 0xccb51
  | 73 => 0xb4cd1
  | 74 => 0x170b51
  | 75 => 0xb5711
  | 76 => 0x58a
  | 77 => 0x5ca
  | 78 => 0x18ca
  | 79 => 0x1a4a
  | 80 => 0x16ccd1
  | 81 => 0x16d711
  | 82 => 0xd0b91
  | 83 => 0x20d
  | 84 => 0x140d
  | 85 => 0x24d
  | 86 => 0x144d
  | 87 => 0x104b91
  | 88 => 0x1a8a
  | 89 => 0x194a
  | 90 => 0x19cd
  | 91 => 0x14cd
  | 92 => 0xd4bd1
  | 93 => 0x20e
  | 94 => 0x140e
  | 95 => 0x24e
  | 96 => 0x144e
  | 97 => 0x104bd1
  | 98 => 0x184e
  | 99 => 0x148e
  | 100 => 0xcc3d2
  | 101 => 0xcd711
  | 102 => 0x3d5d1
  | 103 => 0x3ccd1
  | 104 => 0xcd5d1
  | 105 => 0x3d711
  | 106 => 0x15c3d1
  | 107 => 0x15c3d2
  | 108 => 0x15d711
  | 109 => 0x1703d2
  | 110 => 0x15ccd1
  | 111 => 0x160d11
  | 112 => 0x44d
  | 113 => 0x1a0d
  | 114 => 0x105611
  | 115 => 0x164d51
  | 116 => 0x188e
  | 117 => 0x105651
  | 118 => 0x40e
  | 119 => 0x178e91
  | 120 => 0x5cd
  | 121 => 0x1a4d
  | 122 => 0x105791
  | 123 => 0x17ced1
  | 124 => 0x18ce
  | 125 => 0x1057d1
  | 126 => 0x58e
  | 127 => 0x3d712
  | 128 => 0x3cd52
  | 129 => 0x3d652
  | 130 => 0x3d292
  | 131 => 0x3c992
  | 132 => 0x3d892
  | 133 => 0x3cd12
  | 134 => 0x3da12
  | 135 => 0x3ccd2
  | 136 => 0x1a1652
  | 137 => 0x9c3d2
  | 138 => 0x1683d2
  | 139 => 0x3d5d2
  | 140 => 0x3c9d2
  | 141 => 0xec3d2
  | 142 => 0x17c3d2
  | 143 => 0x3c0d2
  | 144 => 0x3d2d2
  | 145 => 0x3d8d2
  | 146 => 0x3ce92
  | 147 => 0x3da52
  | 148 => 0x3ced2
  | 149 => 0x1a57d2
  | 150 => 0x1a9952
  | 151 => 0xe83d2
  | 152 => 0x1783d2
  | 153 => 0xd03d2
  | 154 => 0x1603d2
  | 155 => 0xd43d2
  | 156 => 0x1643d2
  | 157 => 0x1a1655
  | 158 => 0x1a57d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1698
  | 6 => 3634
  | 5 => 1211
  | 4 => 44
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (69052+((h/566+packedAt gbK7 (62826+(h % 566)*11) 11) % 2038)*12) 12
  | 6 => packedAt gbK6 (190175+((h/1211+packedAt gbK6 (174432+(h % 1211)*13) 13) % 6383)*13) 13
  | 5 => packedAt gbK5 (75882+((h/403+packedAt gbK5 (71449+(h % 403)*11) 11) % 1758)*12) 12
  | 4 => packedAt gbK4 (3164+((h/14+packedAt gbK4 (3080+(h % 14)*6) 6) % 58)*7) 7
  | 3 => packedAt gbK3 (245+((h/1+packedAt gbK3 (243+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfff07fe03ff03fffff81ff80009d8cfd8cfe7c
  | 1 => 0xc03f83ffc0ffc1f00ffe07ffc36af332f3338f
  | 2 => 0x3ffc0000fffe000ffffffffc7303c303c3ff
  | 3 => 0x3fffffff0000000ffff8003f83fc03fc03f0
  | 4 => 0x3ffffffffffffff00000003ffc0003fffc00
  | 5 => 0xffc0000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x43900c6105300250e3904c818000845484563c
  | 1 => 0x849281a9445441612492452a8128b130b13285
  | 2 => 0x925340410aab402496592551c5302c302c15a
  | 3 => 0x1239dad5b60210448e79e4062e83dc03dc03e0
  | 4 => 0x202e631e38cf398f0020801837fc00036ba800
  | 5 => 0x3c000018200c2108004100603bff6ba8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37049
namespace PEqualNP.Outside.L_meta_37049
open PEqualNP.Outside.L_meta_37049.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 14 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_64 : Interval s0Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_96 : Interval s0Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_128 : Interval s0Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_160 : Interval s0Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_192 : Interval s0Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_224 : Interval s0Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 227 := (concat (concat (concat bs0_3_0 bs0_3_32) (concat bs0_3_64 bs0_3_96)) (concat (concat bs0_3_128 bs0_3_160) (concat bs0_3_192 bs0_3_224)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_224 : Interval s0Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_256 : Interval s0Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_320 : Interval s0Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_352 : Interval s0Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_416 : Interval s0Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_448 : Interval s0Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_512 : Interval s0Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_544 : Interval s0Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_608 : Interval s0Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_640 : Interval s0Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_704 : Interval s0Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_736 : Interval s0Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_800 : Interval s0Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_832 : Interval s0Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_864 : Interval s0Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_896 : Interval s0Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_928 : Interval s0Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_960 : Interval s0Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_992 : Interval s0Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1024 : Interval s0Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1056 : Interval s0Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1088 : Interval s0Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1120 : Interval s0Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1152 : Interval s0Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1184 : Interval s0Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1216 : Interval s0Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1248 : Interval s0Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1280 : Interval s0Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1312 : Interval s0Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128))) (concat (concat bs0_4_160 bs0_4_192) (concat bs0_4_224 (concat bs0_4_256 bs0_4_288)))) (concat (concat (concat bs0_4_320 bs0_4_352) (concat bs0_4_384 (concat bs0_4_416 bs0_4_448))) (concat (concat bs0_4_480 (concat bs0_4_512 bs0_4_544)) (concat bs0_4_576 (concat bs0_4_608 bs0_4_640))))) (concat (concat (concat (concat bs0_4_672 bs0_4_704) (concat bs0_4_736 (concat bs0_4_768 bs0_4_800))) (concat (concat bs0_4_832 bs0_4_864) (concat bs0_4_896 (concat bs0_4_928 bs0_4_960)))) (concat (concat (concat bs0_4_992 bs0_4_1024) (concat bs0_4_1056 (concat bs0_4_1088 bs0_4_1120))) (concat (concat bs0_4_1152 (concat bs0_4_1184 bs0_4_1216)) (concat bs0_4_1248 (concat bs0_4_1280 bs0_4_1312))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_64 : Interval s0Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_128 : Interval s0Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_160 : Interval s0Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_224 : Interval s0Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_256 : Interval s0Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_320 : Interval s0Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_352 : Interval s0Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_416 : Interval s0Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_448 : Interval s0Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_512 : Interval s0Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_544 : Interval s0Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_608 : Interval s0Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_640 : Interval s0Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_704 : Interval s0Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_736 : Interval s0Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_800 : Interval s0Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_832 : Interval s0Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_864 : Interval s0Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 890 := (concat (concat (concat (concat bs0_5_0 (concat bs0_5_32 bs0_5_64)) (concat (concat bs0_5_96 bs0_5_128) (concat bs0_5_160 bs0_5_192))) (concat (concat bs0_5_224 (concat bs0_5_256 bs0_5_288)) (concat (concat bs0_5_320 bs0_5_352) (concat bs0_5_384 bs0_5_416)))) (concat (concat (concat bs0_5_448 (concat bs0_5_480 bs0_5_512)) (concat (concat bs0_5_544 bs0_5_576) (concat bs0_5_608 bs0_5_640))) (concat (concat bs0_5_672 (concat bs0_5_704 bs0_5_736)) (concat (concat bs0_5_768 bs0_5_800) (concat bs0_5_832 bs0_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_32 : Interval s0Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 44 := (concat bs0_6_0 bs0_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 68 := (concat bs1_3_0 (concat bs1_3_32 bs1_3_64))
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
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 129 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 45 := (concat bs1_5_0 bs1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
theorem alls3 : ∀ k ≤ 3, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 44 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1184 : Interval gbAtlas 5 1184 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1211 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)))) (concat (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184))))))
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
theorem bgb_6_3616 : Interval gbAtlas 6 3616 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3634 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)))))) (concat (concat (concat (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240)))) (concat (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))) (concat (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)) (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688))))) (concat (concat (concat (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)) (concat (concat bgb_6_2816 bgb_6_2848) (concat bgb_6_2880 bgb_6_2912))) (concat (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008)) (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136)))) (concat (concat (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360))) (concat (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)) (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)))))))
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
theorem bgb_7_1696 : Interval gbAtlas 7 1696 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1698 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608))) (concat (concat bgb_7_640 (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 bgb_7_832))))) (concat (concat (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024))) (concat (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)) (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248)))) (concat (concat (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344)) (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472))) (concat (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568)) (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0feeaeeeaeeeae0c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4008370368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37049.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[0,6]⟩,⟨.or,[4,5]⟩,⟨.and,[1,2]⟩,⟨.and,[2,7]⟩,⟨.and,[1,3]⟩,⟨.or,[0,11]⟩,⟨.and,[3,10]⟩,⟨.and,[8,12]⟩,⟨.or,[9,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008370368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008370368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37049

open PEqualNP.Outside.L_meta_37049 in
theorem PEqualNP.Outside.L_meta_37049 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008370368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008370368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
