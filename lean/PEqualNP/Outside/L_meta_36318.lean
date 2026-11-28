import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36318.Model
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


end PEqualNP.Outside.L_meta_36318.Model

namespace PEqualNP.Outside.L_meta_36318
open PEqualNP.Outside.L_meta_36318.Model
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

def SBf (j : Nat) : Nat := [7, 7, 6, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36318

namespace PEqualNP.Outside.L_meta_36318
open PEqualNP.Outside.L_meta_36318.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x1abc8161e302230070c1a44852275404eac00987170c008803e940035a6d4095c00a803c009294000c80261c2ab0428a081600138d2472000c004f041140ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1486ca64d0d04844723d060647b3c10cc244289a06e7e011fc066b032004c2b0a1b0f23322a08cc040a9bc46002a92c5400249f10a1c00000b8113b9500a2d041901e160007c7a6531918122c00000c400001080067370400000000800000388ec002e2c01c325a1e128002435000ae48000bc00002382c807000130005f000fc3a001a8e90674291d4da4e208c01400300e0005e3e800e6252e85c7c39188d89e76098a0a00142030b63413834ac81108781c692c80030015418149400002420580c3c6c1004140000004450a40004041c0400000014080844f0080000000400127ca5a1cf947439ea86873d5490f3ea6a1cf149439e28a873f5050e7ca821cf54e429f294853e5190a7aa1215794c42aea98859e5310a7aa6216754c428ea98853e5210b5ca4214f944429ea80853e54cca7aa9996750f32bb28e657551cca7ea9194f152329faa2653c544cb3a86994f950329eaa0653d539067ca520cf946419ea84835e53106baa620e794c419ea98839d531063aa620cf948419f28883b6511067aa020cf953319eaa6639d43cc6dca598db54b319faa4633c548c67ea898cf15131cea1a633e540c67aa818cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cfd51219e2a2433f5408678a810f948421af29e815d53d033ca7a04f54f40cea9e811d53d027ca5a04f947409eaa4813f5350278a4a04f14540dda82813e541027ca9984f553309f2a4613d548c33a87184f951309eaa2613e540c27aa8186750c30b7290616d520c2eca2185d544309faa6413c54c827ca9104f552209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x90000001c98082a000000600384bb2280022000200080c0c0005807800144a800000019000002c00001a0000400410020048758e5190a1f6354242c550d51cca3661d523287195434ca8c6250d328758e529061f6354241c350d52cc62e62d523187195434c6946150d318758c544861d63150218e580540861d63149408758c515021d63951308b189544c2346155130c350d520c31543544308758c54c821d63952208758c54c421d6395210
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (864+((h/16+packedAt s0K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s0K4 (3970+((h/44+packedAt s0K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s0K3 (1036+((h/8+packedAt s0K3 (988+(h % 8)*6) 6) % 58)*6) 6
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff0ffffffff81ffff07ff07fffffe78f1ff
  | 2 => 0xf07fff03f07e1ffe1e0ff87ff878383fa73e93
  | 3 => 0xff83fffc007fe1ffe00fff87ff803fc1c7cf1c
  | 4 => 0x3ffffff8001fffff00007ffffc001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x800010208010000044120088008a0a10085025
  | 2 => 0x2519221924a430960a854853485090aca32692
  | 3 => 0x432a44486949032aa109950595012585458b18
  | 4 => 0x6a5388924c0d55cd33a0c446e6658109f00dc0
  | 5 => 0x8c630ee38e7199f1ddcee660c4460631fef000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36318
namespace PEqualNP.Outside.L_meta_36318
open PEqualNP.Outside.L_meta_36318.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x102a08f00246d09650bd1991e34008280000a222d5974a4c380340c006301002a5a8922c029ce003a006201c7c02912b82a600280080002080340040043600ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x24800b25f1709400043401c60003b898002d000f80000268008e0000000b081000cc000000070da14000f0c21d001200031018790800151149e0000000f0670d00050632082400402192c987c00030423f2d800f46a34808ec15149b816853f0d8de0f1395422710d9942e561794c48192f1481c602e0f4885a1c918684a4107c5679009d0fa83330d4e02c100e8ea18000010057068ec00000408c0c510004cd612361380a00280004464050000000310006e0019000e4100005870423d9fc00002a000005d3980400b8000400503408007c040c040408004c000804382c000c54000c182074040808080008003c0814100042baa921d794a43af28c875d5090f3ea8a1d714943ae28a875f5050ebca621d794f42aea9e859d43d0aeca3a15d54742afa9a855c5350b3a86a15794c42aea98855f548cabaa9195794a32af28c655d508ca7ca8194f55032afaa0659e540cabaa81967550328eaa0655e520cb9ca4195794432aea80655e53d06baa7a0e750f41b7296836d52d06bea6a0d714d41cea1a835e53106baa620d7d5231aeaa4635e528c6bca318d7542319f2a0633d540c6bea818e795031aeaa0639d540c63aa818d794831af28863d6510c6baa018cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710d7d4d21ae29a435f53086b8a610f948421af29e815d53d02bca7205754e40cea1c815e53102baa6206750c40b7290816d52102eca2205d544409f2a6613d54cc2bea9986795330aeaa6619d54cc23aa9985794b30af28e615d538c2bea8985755130ae292615c514c3b6a0985794c30afa9e415c53c82bca7105754e209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d54420afa9e215c53c42bca7085754e109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x78089400001a81600810002c00a6009a4000000032330012000a9000001c00e00002e006002000a000000000050000c00c1c550d51d0a8c6250d4295987548ca1d649463287d91508ca1d6595032c350d52d06946150d419398b548c61d6494a3187d91508c61d659503187590534861d6414c2196580530870d4354840c550d511024c625513095185544c21d641493087590514c21d6494c308759053c821d6494e208759053c421d6494e10
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s1K5 (864+((h/16+packedAt s1K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s1K4 (3970+((h/44+packedAt s1K4 (3618+(h % 44)*8) 8) % 177)*9) 9
  | 3 => packedAt s1K3 (1036+((h/8+packedAt s1K3 (988+(h % 8)*6) 6) % 58)*6) 6
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1fffffc1ffffff81fffe0ffff83ffffe78f1ff
  | 2 => 0xe07e0ffe0ffe1ffe1e0ff0f07fc3f83fa74e73
  | 3 => 0xff800ffff07fe1ffe00fff007ffc3fc1c78f9c
  | 4 => 0xfffff8001fffff000007fffc001f80fe0
  | 5 => 0xfffff000000001ffffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x20800440004000022100111100449080810a5
  | 2 => 0x49149488652830960c8690a22a4290b4a34652
  | 3 => 0x85252910a351032ac10b2a044ca82685458b18
  | 4 => 0xd659ce254a1d55cd77a1888977330319f80de0
  | 5 => 0x18618c398c6199f199cdccce06220421f6e000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0faaafaaafaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36318
namespace PEqualNP.Outside.L_meta_36318
open PEqualNP.Outside.L_meta_36318.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2900580200012029c8301800100018c60bf42bd42df32dd32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1094058c000818d424ca5aa5a0d354831aca80632d521026aa2205354b30
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
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
  | 4 => packedAt s2K4 (212+((h/4+packedAt s2K4 (192+(h % 4)*5) 5) % 22)*5) 5
  | 3 => packedAt s2K3 (197+((h/2+packedAt s2K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf8ffffc1fc3e1fe1fc3f0fffc3f8387f4cf70f
  | 1 => 0xff0787fe3fffe1fe1fc3f0e0fc3fff87b349f3
  | 3 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8110044004420002404012240488812041305
  | 1 => 0x10400888101002040841104404121204114052
  | 3 => 0xa22255108aa9106ac222aa08aa812560c28c28
  | 4 => 0x86b566252a0d54b376a88812f3258132ec0f80
  | 5 => 0xc4c64439b331993d9b33cc9c22060644fbe000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36318
namespace PEqualNP.Outside.L_meta_36318
open PEqualNP.Outside.L_meta_36318.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x83a402518000106502c201b5bf42bd42df32dd32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x141810084c018d424ca5aa5a0d354831aca80632d521026aa2205354b30
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
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
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s3K3 (197+((h/2+packedAt s3K3 (189+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf8ffffc1fc3e1fe1fc3f0fffc3f8387f4cf70f
  | 1 => 0xff0787fe3fffe1fe1fc3f0e0fc3fff87b349f3
  | 2 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8110044004420002404012240488812041305
  | 1 => 0x10400888101002040841104404121204114052
  | 2 => 0xa22255108aa9106ac222aa08aa812560c28c28
  | 4 => 0x86b566252a0d54b376a88812f3258132ec0f80
  | 5 => 0xc4c64439b331993d9b33cc9c22060644fbe000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36318
namespace PEqualNP.Outside.L_meta_36318
open PEqualNP.Outside.L_meta_36318.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x6006cc21000000a243098e347ce8000007912000e000064a0000154a4000941e00580002e00001000000000986a000944800000027462c0000e10003000000844000150000001010000000061001e0000004ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2206fd0440dea08817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3bc87987750f30bf296617d52cc3be6598774cb30bf28e617d51cc37e83986f50730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3186fd0630dea0c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930ef99261dd324c2fea2985f14530dfa0a61bd414c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa2186fd0430dea08617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83dc85907b50b20f719641ed32c82fca3905f54720dfa0e41bd41c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106fd0620dea0c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42483dc64907b4c920bfa8a417c514837e82906f50520f790a41ed21483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2106fd0420dea08417e50083de40107e88020f690041f920082fea9885f95310df2a6213e54c42faa9886f553109eaa6217c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c437e83887d90710dea0e21f541c436a83887d8c710fa98e21f621c43ea43885fd5210bf2a4217d54842f8a9085fd4e10bf29c217d53842f8a7085fd4a10bf294217d52842f8a5085f54610dfa0c21bd41842fca1087e8c210fc98421fa20843f241087dc4210fd884217f54442fca8885f55110be2a2217f53442fca6885f54d10be29a217f52442fca4885f54910be29221bf41443ec82886f50510faa0a21b541443ec62887d4c510fb10a21f521443f460887e4c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821bf410437a82085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a0657d540caf8a8195f94c32bf29065df320cbdc6419774c832f699065cd320cafca2195f54432bf280657d500cafca7a0df54f41dfa1e83be43d077a87a0ef10f41bf296837d52d077e85a0ef90b41dea1683bc42d06fca1a0df54341dfa9e83be53d077aa7a0ef14f41dfa9683be52d077aa5a0ef14b41df99683be32d077a65a0ef0cb41dfa8683be50d077aa1a0ef14341beaa4833d54906fca720df54e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077c86a0ef50d41de21a837f52506f8a4a0efd0941df21283bd425077884a0fdd0541df20a837f50506f8a0a0efd4d41df29a83bd5350778a6a0efd4941df29283bd5250778a4a0efcc941df19283bd325077864a0efd4541dba8a83bf505077ca0a0ef54141de282837e541067ca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef99663dd32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31bea94637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7be6498f74c931dfa0a63bd414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a90637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc6590fb4cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21bea94437e518877e8310ef50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f719243ed324877e8290ef50521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40dfa1681bd42d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481be429037885205f94640bea8c81bf419037a83205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940dfa1281bd42502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a
  | 2 => 0xe6acd918d0003580015b148928002ae592a240015a0000000000000060cc21b34220ad5c2c342a06d219bf1ce4f00000057c0000004c53e7315d9354083a8f40aa28a00000000414680001ae3765094415004a5a9212923309b5018000001f8ea0e33ee5a44a167196439499a30000010c2373da770681793f4ae8058001602d0ef9030b6868dca6e1e0620b99a44d058c64ac11ee708e28dd3dc0000024d27200099ad70fa858331ff39a48847240190a00f89c7000970000985729c0002cd012000000000006dc9ba813f244042a200263d52d8f414c000c71b0050759521c100000000000250000001cb3342b90a2c247699c402c60c02a49b19e24e334ac86722825c050920007f06c00004c98c0000000000059a5e08aa5cfc0ac0100080000802068000200001802000100b01a0480600002000000101c0a8000000c088160580203814038000400c01002000241300201800030000200e038000c80e020020080e040220701a00000000480184c010020280002008008020a0020380000000000060280e0000602002000020382c028020200002808010000180202800018040481a0080c02008018000600002812008100880a2e00401002048100002e01802000180003000000118380080e010340080604000058040000600018010060180c018100580002000058020080000802008080201000020000060000e0a80003004010420000a0082e00002018000100600808010000200207008000060001004000000060080e0300005806008200002802800008100280e000100280c0080202000010000401400800000237e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43f7294876e5290efaa521fb54a43b6a94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16f90f42de21e857e51d0afaa3a15f94342bea86857d5490afca7217794e42af29c857d5390bbaa7215754e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16f90d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665df43ccbb887995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32bf29465ef428cbd8851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265df434cbb886997bd0932f621265e
  | 3 => 0x1d8168852d83886990d8c12941a00029834283c9e80022400000082000134000365048186d07511626914199268104959a22929e486a6500001d5610013a8416382020c2640000049ca34000022102250f0430baad41da3d3a03a0fd8583d8000000e53c0128002c4598628000002a8590480160f6b383f8961d22d4d3a5214e8a92998b4261c0000fe4102f4ed8c00423cc171c906a07d5181807430d659d1400350610ef3500007721c4602807d8030000016d83d29e000da99b0004ec700000000000000000a7a9538dc0001e80000050e000848460008b4a00574d60000010c000000110d23280700015336c27c8f10f000000351660002783705552a6a8392c8432000de27a55a5891ca750d20015b13a53c0006518120a81c8e03e456a98000000005a0a900003a648960ab000718a616e50c0000000041c230001eb000570dd0b822c8e92d1ad3c4001128002bc25517a4b0d82a011948000000c323e3ec3f4c80001e4ac4ae85400029400000000a80a68ed5521493491712242cf483f0000013c11151e3e40f1d801c5ed3f958202674c60b151c9d8578f6146624000560006f95f8000c4824002415ba898b5800000000e70004ee798c002424c654002a12824f80009b3e48fc0026120e3e089a8c060030fa800020000000db3ba0000007c2fc001682d51782d8aa8003a4000f2120000000bc08810800056800000389312362620c92c1240ee700ab80023a00031800000000c785f00093006800000000968000000011a9603aeb44720002640000028a000000002b242e0006380033e37d3e8000004c0b0831544728e18113e05195e9e34f8ac0ab27b0bc6c51c0640a64e05d84b0001d95524659e888000004cc20449a6418a510ba8045b2270000d343e9f83c2442e8a2d5b85c236049188d132e1d01ba120a2b28dc0000002195a0002863845904e00000000000000140222b30905f1488ba0ca288810fa232a0ced1873e89640004f49e91c678000003fc978004ba7f5420b73385954e02d4de001698000002f89480008e000e9887000379122c55360f12b97f05e6591e0ce24a69519a90352a68c9800000228f9a45578001392343045bc210792ecb795788f41a050b82290028b0000831f8b51242da22a018398c44040006aa5f0000005f800068001008cc000164f78004d8000002562965e8160d70de0a8388004d4000a881524651ceaa85142184d600029c884c8a9d000001690000000e524aa5000001171b440a0000c8eb000000000000008c8001e537a4fc001fe000000248000006140000000082c4692125c9cc002554c0aac0006b1cc4680001700088d3a2945ac020001af00094400000000b7000172034000b691823e000001042e2b00af8d9000000f38002d809c14800080778bb800000a58630001727640012a01
  | 4 => 0x73c78a99550830be9c80000000006d44e875282714a80cc1c1e1
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x5414823c65505209798f540825d63d50209d987540827561d50208f596540823d61950208fd85540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c530826e6214c209d98453082756114c208f992510823d6494420cd95251083355494420d594e51083555394420cd99251083356494420cd95151083355454420d594d51083555354420cd991510833564544208fd97410823d65d0420c794f410831d53d0420cd947410833551d04208fd95410823d6550420c794d410831d5350420cd94541083355150420cb553200834d53c8020d9547200837151880209bd95200832d5448020d354d200836551480209ed9520083715148020cd98654c423e64d4f108f59353c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6414b108f59052c425e6314b109758c52c43365450710add9541c43376550710ad59231c42b564887109798c548425d63152109b988548426d62152108fd91538423c6454e108f990538423d6414e109b988538426d6214e108fd91528423c6454a108f990528423d6414a109798c528425d6314a1097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108f990534423d6414d109b988534426d6214d108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d6314910ad59241442746550510bc18141443376550510cd19541443b36050510ec18141442b5648c5109d19531442b564885109d19521443b1418c1109e19530443b1414c110f44c530443b141881109e19520443b14148110f848520443b141c41109798f540425d63d50109b98b540426d62d50108f596540423f61550108f585540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520427661148109e980520423e64944108f592510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb54941043365150410cd553100435553c4010d954b10042796584010d654e100436952840109dd9510043355444010d554d100436552440109ed9510043595344010da54910043b34144010
  | 1 => 0x87395494021d694e50087595394021ced0650087394194021ce95150087395454021d694d50087595354021ced0550087394154021dac8550087722154021da485500877121540219b98a53d026d6294f409798e52d025d6394b40cd54741d02ae6290e40a798e42903365150640cd545419023e65d0d408f997425033751505408f596431031d5390c40ab98a431031d5310c40d394e521034d5394840d394d521034d5354840cb90d521032c43548408f596421029e6390840c754e421032d5290840c754c421032d5210840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cd99151103364354440cd10d51103364254440cd109511031e53d0440c754f411032e52d0440cb54b411033551d0440c794d411031d5350440cb949411032d5250440cd945411031d53d0040cb54b401033551d00408fd95401031d5350040cb549401033551500409ed95401026e62d53309b58b54cc2cd6290f308f99252cc23d6494b30a759332cc23e64947308f59251cc26e62152309b588548c27661152309d584548c23f6454a308f191528c23e64946308f592518c3365150630cd545418c23d61d51308f992544c23e6515130c758c544c23d6115130c7152434c2cd6290d3097195434c29d64cc930c7153324c31c544c930d3149324c23e64145308f590514c26e62145309b588514c23e65d05308f197414c23e65505308f195414c26e62d50309b58b540c27661d50309d587540c23d65950308f586540c23f61550308f990540c25e63150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d54548308f992510c23d6494430cd952510c3355494430d994a510c3655294430cd992510c3356494430cd951510c3355454430d9949510c3655254430cd991510c33564544308fd97410c23d65d0430cb94b410c32d52d0430cd947410c33551d04308fd95410c23d6550430cb949410c32d5250430cd945410c3355150430c7553300c34d52cc030d5547300c371518c03097d95300c31d544c030d3549300c355514c0309ed95300c371514c0309798f54c825d63d53208f99353c823d64d4f208f99253c823d6494f20b358e42c82ad648cb20d314d32c823e64947208f59251c825e63152209758c548827661152209d584548823f6454e208f191538823e6414e208f59053882766114e209d584538823e64946208f59251883365150620cd545418823d61d51208f992544823e6515120cb588544823d61151208f992534823d6494d208fd91534823c6454d209dd8553482746154d20cb15242482cd63909209b19542482ad648c920cb152324826c654c920cb151324834c534c9208f990514823d64145209798c514825d63145208f997414823c65d05208f99
  | 2 => 0x6494c328f992520ca3d6494832b358e320ca5f654c8329bd95320cacf654c832d3d95320cb4e544c832d3151320ca3e64944328f592510cb4d32544328fd91500ca3c6454032d34c9500ca6e6294f419b58a53d06ae6290f41ab58a43d071d5310f419798e52d065d6394b41a798e42d069d6390b41cb54842d06ae62d4f41ab58b53d06b561d4f41ab98a53d06ad6294f41c754c53d06b56114f41a798f52d069d63d4b41ad58752d069e6394b41a758e52d072d5214b41ad58452d063e65ccb418f59732d063e658cb418f59632d078d320cb41a798c50d069d6314341ab98850d06ad6214341ab98a43506ad6290d41c714d435069e6390941a758e425072c52509419798c505065d63141419b988505066d6214141ab98a53506ad6294d41ad58653506b76154d41c754c535069e6394941a758e52506b56194941add85525072d52149418f997325063d65cc9418f996325063d658c941add8532506b4614c941e34c832506b6610c941ad58432506b560d4541a7d8d505069c6354141abd8950506ac6254141a798c505069d6314141ab98850506ad62141418fd9541106776550441cd951411066e62d53319b58b54cc63e6494b318f59252cc63f64543318f19150cc66e62951319b58a544c63e64d49318f593524c74c524c931b5185324c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f990540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc43197d95310c74d524c431e5505310c677654c431ce952500c7395494031da94a500c7695294031ced06500c7394194031ce951500c7395454031da949500c7695254031ced05500c7394154031d6cc5500c7723154031d64c5500c77131540319798f54c865d63d53218f99353c863d64d4f218f99253c863d6494f21d314d32c863f64543218f19150c863e64d4e218f593538863e6414e218f590538867a6014e219e580538865e63951219758e544863e64d4d218f593534863e6494d218f592534866c654c921d314d32486e4614c9218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219b988530867a6014c219e580530863e64944218f592510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410874d53c84219bd95210874d5348421e950521086776548421ce952500
  | 3 => 0x900041c3b1ee000ad125a7b1b2788001724762a4001c4000000679aa0004c0000181402c4ca0193060005c16c2342600000005c0001ca02324000228004209b0671564d61d4fc833006791228b64304d4b08d01a6870c98912861591e9a62a67685c9364008cc371040d82750483720a4603494a3006cc1d000000a58ba2bc44200155a9b48e4d0ce99f29c41800000000000bd9e51803c4002bd192aa09603d0f658935216000004b28770003f02f93b5148b53200033226c7a1231c6000db0000006f4201250009d1030000008786a28b0b228c001be0fc0e08f2a0374908f4a882b8958000002362207aa580005fc2d8c350c0000001c436015611c340e1bc3c0000006084b000000001219ac23a53c1b1a939671d1f20f2a8a348a00053a9b4df95f42852c570000766c83988d000094000740947fd2d9e82c81500005c54e1c0000c42ce0000027d054578a40ac000b10eca654c4248b791f3be0a4340d54f001d50a312527747b8a438489d1017c03a87456a852568d40008611c0000008a01a0c91900002e921530974fe9c84818f24061800152156a500003c0000000000200009008030001112428010020f4030281a000000000d09c00004000002100400008050100700000000070041b0001d0a403004060080000805004000000401002000000000b00002000000fc0701804024040080c014000040401801058110000a00002014420540002807020000280b05c0100c0e01402000030100600c050000000000018020a4170000100c020000d0c80800c41000070dc13000010000b00801020050081f018070100a07c081c01204c0a0101000c0805000024240000308815000250000005c000100202c0e0600c0081a03431000000080c004000ec0208410000000000c00000020080040d00400040160700116c30004190003d000020081400409024070000300000040650300301c0f05821004050640c04800004030340100005cbd0e5290f4f4354a43ab98a4350e6e62141439b5885050e7661141439d5845050ecd6290c438fd954310e5f6550c43ab98a43d0b1e53d0e42c794d4390b1e53d0a42d354f4290aae6290d428f9944350a9e63909429798c5050a5d63141429d9845050a7561141428fd954310acd63908428fd954210a6f65508428f58654ccb1c63553328fd8554ccb1d54d0f328f99251cca3d64947328f586548cb2c62552328fd85548cb2d54d0a32c7953328caae64cca328f992518ca3d64946329d986544ca75619513297997434cace62d0d329b997424cace63d0932e310f424cb8f4310932ab993324ca9e648c9328f990514ca3d64145329e980514ca7960145328f990504ca3d64141329d984504ca7561141329798f540ca6e62d50329d984540ca7561150329e980540ca7960150328f992530ca3d
  | 4 => 0x262688ab9d60002140017621a0009e229000360000000000000200009a6105a9a839414ce41004fc000390160009cce4915000000000b00000000025535e13d23253000090e82760009f0a20ca000000bf0d12c03cc0015807ca40c888b1d26150d17922e5ccf98284bc1f15d2c0000000d08002b60000015a0005a95f1961c461c812301f4a386fa753de0007b0a73a83814b8002d000096aad0d64849326e3ceac92f8e5000000000004f2abc9f17a11e82d378ed2241888c9593608b00910e49269c1f9ed2a26b8e318e3704b91e02d0627307d813154131092831505c45d1d119a6c544a81000230fa055368950fc0c62ea050220000a29c15200000006ce780a00066d4f0650005a4ec011184140002c50008ac0a80045c2ec0002f58c1e8fb8831080008510b0006dcf816e48043122000082000002c1000000aa860444ae0f584b266000001f2274001598003c60007f908164a644092203e44c001de1dc21c001c548299cea8fe56a038878e749ea08f50dc31a8dc49942000694fda5051e6b4001c04ba679089460c23e0b18a15462dce6a69410aa42385d0cc9490caaa15e76c2f1b51b465c721010b494404843474834321a301e9713d00c3383145e8c147e62059abf2ba8e0248a2282add489dc4685c09c2251320ac750102383302b8234d03ad49000222604ff29a040084fa8c83a4378211ce20609c9e9455864c91526658e8991413f14c358a00581ae018d0204378254cc124044ac44f0670e2a952d2934c087d0184e1964a0939783ec8bce9a98090ae53bab049a5ac1307f1e4a54782610da6ac882392a06682324e3f46303c82c46c629029953c2078d21fd42e2250aa634b23b097800558000001ec06a89000201010001118f957602c52966292a7c5f8001002d0638e113418c77989418000001d73cca1c180820007c5510000008280d28c29aad92b8001b662c000003f8000f00be28e0014217722c3745e17d4947055724c0d44dc0028013ea70dc8024266ec9c87d0003993880041c3f495094320348a60520005b44e0e8068000001
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x184a6580030000b8eca802270c41ad80184e34000020e8ab00002788914a916000020070c926873a6ca99065515c4544c832a92e02a2641943571191500cb0632264a80652c5c0614c941d0a64b0864a0cd170185324c782a928298863c450531540319c2e030a6490f05535052108790a0a42a80438354e6290c40c1cc6a9484205267290d511028b39c84a8881831516290d3083aec2a6649860c5458e4248216bb0a919241345cc60505109c2e430282885917318141442d0b90c0a0a212c1d9414c110960eca0a408853175d051004388a9e8288021c854b4144010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8905819d3654c832a05811913254032
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 735
  | 4 => 712
  | 3 => 30
  | 2 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | 2 => packedAt s4K2 (i*60) 60
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (770+((h/14+packedAt s4K6 (672+(h % 14)*7) 7) % 80)*7) 7
  | 5 => packedAt s4K5 (22295+((h/245+packedAt s4K5 (19845+(h % 245)*10) 10) % 971)*11) 11
  | 4 => packedAt s4K4 (29426+((h/237+packedAt s4K4 (27056+(h % 237)*10) 10) % 855)*11) 11
  | 3 => packedAt s4K3 (1530+((h/10+packedAt s4K3 (1470+(h % 10)*6) 6) % 40)*6) 6
  | 2 => packedAt s4K2 (122+((h/1+packedAt s4K2 (120+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xcf1fe3fff0fe3f8fc38c7c7ff1f87e1f04f4cf
  | 1 => 0xfe1fc38ff1fc7f1fc0f8f8e1e3f8fe31b4b33
  | 2 => 0xf001ffc0ffe007fe3ff00ff01fc00ffce38c3c
  | 3 => 0xfffe0000fffff8003ffff0001ffff000fc0fc0
  | 5 => 0xffffffff000000003fffffffe0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x41002000100040100000101200480200001045
  | 1 => 0x2208410122080a020804848442120482094112
  | 2 => 0x80d48892444495005590092094812958628c28
  | 3 => 0x4441aa488940124a6a9200119256048b40e80
  | 5 => 0x289913300ed926493b4e4e49c0064192dfe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36318
namespace PEqualNP.Outside.L_meta_36318
open PEqualNP.Outside.L_meta_36318.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0xd12381540000593874098a0a009001b180049e00840080608aa3321149f1644b8f00608000038e80008898000186814a0000420020442d11820cbff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa81bd5350378a6a06fd4940df29281bd5250378a4a06fcc940df19281bd325037864a06fd4540df28a81bd5150378a2a06fcc540df18a81bd315037862a06fc8540df10a81bd215037842a06fd4140dda82817e541027ca8205f94c40bea98817e52102faa4205f94440bea88817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc37e81986f50330bfaa4617e548c37ca9184f95230beaa461bd548c27aa9185f15230bea9c617e528c2faa5185f94630bea8c617e508c37e81186f50230ef98461fb308c2fea8985f95130beaa2617c544c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c37e80986f50130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa2185f94030dfa0061bd400c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83dc65907b4cb20bf28e417d51c83de43907b48720dfa0641bd40c82fea9105f95220df2a4413e54882faa9106f552209eaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c417e508837e81106f50220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc64907b4c920bfa8a417c51483de42907b48520dfa0241bd40483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020dfa0041bd40083de40107e88020f690041f920082fea9885f95310beaa6217c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c43ec63887d4c710fb10e21f521c437e81886f50310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e508437e81087e90210dea0421f9408437281087e8c210fc98421fa20843f241087dc4210fd884217f54442fca8885f55110be2a2217f53442fca6885f54d10be29a217f52442fca4885f54910be29221f631443ea62887d88510fa90a21bf40443f480886f50110fca0221b940443f460887e4c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e500437e80086f50010fb88021fa10043ea20087e44010
  | 1 => 0xf324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a0657d540caf8a8195f94c32bf29065df320cbdc6419774c832f699065cd320cafca2195f54432bf280657d500cafca7a0df54f41dfa1e83bd43d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52906faa520ef90a41de214837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83bd43506fea4a0df14941dfa1283bd42507ee82a0ef90541bfa82837c50506fca820df94c41ef298835e53106faa620f754c41aea9883be43107788620df94841f7290836e52106faa420fb54841b6a9083be42107788420df94441dfa0883f6411077a8220fd50441bf28083fa50106f4a020df54041fca80837950106fea998df95331beaa6637c54cc7bc8798f750f31bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c7bc8698f750d31bfa92637c524c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c7dca418db94831bea9063ed520c6daa418df94431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc8590fb50b21f719643ed32c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea94437e51887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690df94d21bea9a437c53487dc8490fb50921f719243ed32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410df94421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40dfa1e81be43d037a87a06f10f40bf296817d52d037e85a06f90b40dea1681bc42d02fca3a05f54740dfa0e81be41d037a83a06f10740dfa9e81be53d037aa7a06f14f40dfa9681be52d037aa5a06f14b40df99681be32d037a65a06f0cb40dfa8e81be51d037aa3a06f14740df98e81be31d037a63a06f0c740df90e81be21d037a43a06f08740beaa4813d54902fca7205f54e40bf294817d52902fca3205f54640bf28481bf40903f681205fd4d40be29a81bf435037c86a06f50d40de21a817f52502f8a4a06fd0940df21281bd425037884a05fd4540be28a81bf415037c82a06f50540de20a81fb405037c80a06fd4d40df29
  | 2 => 0x45c0be06c2fa88c001c332a6c15315c48e7a80005d0005504f84407eadc0005b5a015c489050001480022b0000000000e21eb30ccab300020877a1145aad4989b90000a4001ab1dc2c553a1c000370b0269586828c4a8c000710000000000002b02422c874000005780016c0fd0000010d1fe5b679800101546030182dd0003d0cf0190000005a1f9170aa03e19c41c3080028032c9240819a11029cc98003e2a051b90d000001611181a6688c903200087c000001061dca000032281c8981a35e7148f00d0c6930b6000222381632bf2ae5613f9802c27b8fa9a94ca3a40017600014d43000000b25150001b600018800302001590112841885b8000009f00000015c6f42711a03ea6c2e1cd2e2000860000ec888000000000000000001800014008081200601000028040500001806080000581000000000220301201804000000181800000038140200a000080100a0100204000128360001000800068000200e188020980003006000180080000010000020000c0080001004018080182a018000900e010000000a0601a0100c0000000812078000500007800018200d01400004020040080c01000048100080a00000020080300200008038a20281e0001002006008ce038000000600004000000080401000010040200206810000040700a08800100040102401020020080000c01004020060080200000000060100e00802028000f82803006010080200c1c800000020a002070080c80c028000201a0180000006028000f80400002008000100208012040000100a000040100402802000060a800008020000000828010257e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43f7294876e5290efaa521fb54a43b6a94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16f90f42de21e857e51d0afaa3a15f94342bea86857d5490afca7217794e42af29c857d5390bbaa7215754e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16f90d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665df43ccbb887995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32bf29465ef428cbd8851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265df434cbb886997bd0932f621265e
  | 3 => 0xe81e0b400002433c8a05a44a7486f80045059568800000000000004688eca604b0002b023a750003605b0fe13c3e8b20f00000009281e08600127a59000a3c001323ecb3d3d8004ba32ca4800370000000000000006d1364de7756684a0002d4a9ab1000835160283360bce10000780000000000056ce086e542810000a834a000f488c59c000001a031a4ec6524011e6d0000005960500080023a6cc7907936ca20602613bc344398002de000000ba412000ae800486a1464244524b541a26c0009d80026600000038a6a000001180000006614694f3f67cc0009b000054d89eb00051c3280000072109aa40008cc000000005a87c8000008613e8fc576000a800000077c0027455a9c42a00008475c0004c22a1985698b3fe5c8002160d6b04001da00052c0b8e245257d4d1122b442c000004c0820e58084a28f86a0690000015100000071cc800504ea51229482405b8bfaa03de628dbade06e0b86202c520214408bd0b248d1398f2105040000f2f6001629fd3b669d562362f0928e704039e68484a122f46f04383a4842ec0013c0a2a455c93e000000000e33b08300004f0003dd4c8ec2ce7908327857cabd1c95e256290341882666e8001d53c272812897000218d1a6234c22d0cab40fcb68f90c730e248c2aaa0008d54b8003f07b5698ff3a64b0cb80b37e8782f88007280cb30a625e2c0d51690a03e0c18cc214314e02c74703a8f297455c8b926a2142e0006b25c1644a8002062c4ac00e15611c2a88e1521321f5548184e0275370091d658c8ba3a46441cf629e1407453f0134b60000000000000117a263e8000169fa000b00000001eca751200000000133a0550e074320001460010a13a0146b86480000025493268000730339100000007382b4bc51800000000920001dc3ce4f46e848036001080005381b4000004a8b65418005040cc002c852617928000208a2c5499d508000dd9352da9612f8362320006a8463285383a8c325c534df08d512b706900041ea9400264000400209a40009e4948070000815ea4e4784a13908907000800175000000001ac0000001d8611c20004810200000072296404788268002aa394f1ab6128058740b30081ec3fad4272948c10a10b094cd68001f650cbb8263ee528559370424881a8af17295ca88bf178000680e60002f80015900082cf829f0062687880028a0000000000040c1ead21b2764bca002700012a8004ee000938ce0f48fc96800000001358491bcb5c90a98288a39398c64363d4450004820011e9733a0000e30223d06115c06a5141c0390553ac001188450000013d22042a98c001a80002113699f2680012b2ab07c000002ba52a2586b8002d67800013f14a6c8c309848c000c61b50004c08fa0131c7501511b0de000e48005940004e023496490000932fc968870f314
  | 4 => 0x30c10003b400000000b5800000588000000000007f066860
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe544823e64d4d208f593534823e6494d208f592534826c654c920d314d32482e8604c9208f990514823d64145209798c514825d63145209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510823e64940208f592500823d65d0020c794f400831d53d0020cd947400833551d00208fd95400831e5350020c754d40083365150020cd545400834d53c8020d9547200837151880209bd95200834d5348020d954520083a940480209ed95200837151480209798c54c425d63153109b98854c426d62153108fd9153c423c6454f108f99053c423d6414f109b98853c426d6214f108fd9152c423c6454b108f99052c423d6414b109798c52c425d6314b10ce982548423e64d4e108f593538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6414a108f590528425e6314a109758c528433a5450210aed95408433b6550210ae59230842b9648821097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108f990534423d6414d109b988534426d6214d108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109d19531442746548510ae59240442786550110bc185404433b6550110ce19540443b36150110ec18540443b23150110ec4c540443b22150110ec48540442b9648c1109e19530443d1314c110ae59220442786548110f848520443b140841109798f540425d63d50109b98b540426d62d50108f596540423f60550108f581540423e64150109798c540425d63150109b988540426d62150109e980540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520427661148109e980520423e64940108f592500423d65d0010c794f400431d53d0010cb94b400432d52d00108fd95400431e5350010c754d400432e5250010cb549400433a5050010d554f100436552c40109e59610043395484010d654e100436952840109dd9510043555344010d954910043b340440109ed9510043395444010d654d10043695244010
  | 1 => 0x873a5494021ce552500875a5394021d654e500873a6494021ce592500873a5454021ce551500875a5354021d654d500873a6454021ce591500876b2154021dc88550087692154021dc485500866e6294f409b58a53d02ae6290f40ab58a43d031d5310f409798e52d025d6394b40a798e42d029d6390b40cb54842d029e6310740a758c41d02ae6210740ab58841d02ae62d4f40ab58b53d02b960d4f40ab98a53d02ad6294f40c754c53d02b96014f40a798f52d029d63d4b40ae58352d029e6394b40a758e52d032d5214b40ae58052d023e65ccb408f59732d023e658cb408f59632d038d320cb40ae58351d029e6314740a758c51d02ae6214740ab58851d02b960147408fd9531d023c654c7408f99431d023d650c740ab98831d02ad620c740ae98031d02b9600c7408fd9521d023c65487408f99421d023d6508740a798c21d029d6308740ae98021d02b96008740ab98a43502ad6290d40c714d435029e6390940a758e425032c52509409798c515025d63145409b988515026d6214540ae982415029e6310540a758c41502ae6210540ab58841502ba6010540ab98a53502ad6294d40ae58253502bb6054d40c754c535029e6394940a758e52502b96094940aed81525032d52149408f997325023d65cc9408f996325023d658c940aed8132502b8604c940e34c832502ba600c940ae58032502b96094540a7d8d515029c6354540abd8951502ac6254540aed81515029e6314540a758c51502ae6214540ab58851502ba608c540ae582315023f654c5408f195315023e650c5408f59431502ae620c540ab58831502ba600c540ae58031502ba6088540ae582215023f65485408f195215023e65085408f594215029e6308540a758c21502ba6008540ae58021502b961d41408fd95401027b6550040ce951401026e62d53309b58b54cc23e6494b308f59252cc23f64547308f19151cc26e62951309b58a544c23e64d49308f593524c34c524c930b6181324c23e64145308f590514c26e62145309b588514c26e62d50309b58b540c27661d50309d587540c23d65950308f990540c26e62150309b588540c27661150309d584540c32e5494830cb552520c32e5454830cb551520c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c23e64940308f592500c23d65d0030cb94b400c32d52d0030cd947400c33551d00308fd95400c32e5250030cb549400c3365150030cd545400c34d52cc030d5547300c371518c03097d95300c34d524c030d5545300c399404c0309ed95300c371514c0309798f54c825d63d53208f99353c823d64d4f208f99253c823d6494f20d314d32c823f64547208f19151c823e64d4e208f593538823e6414e208f59053882766114e209d584538825e63951209758
  | 2 => 0x6494c328f992520ca3d6494832b358e320ca5f654c8329bd95320cacf654c832d3d95320cb4e544c832d3151320ca3f64544328f191510cb4d32544328f992500ca3d6494032d34c9500ca6e6294f419b58a53d065e6394b419758e52d06ae6290e41a798e429063e65d0d418f997425063d6590c41c754e43106ae6290c41c754c431074e5394841d354e521074e5354841d354d521072e4354841cb10d521063d6590841a798e421071d5390841cb54a421071d5310841cb548421071d53d0441cb54b411063f6550441c754d411072d52504419dd95411075a5394041d654e501076a5294041da54a501075a5354041d654d501076a5254041da549501073a6454041ce90d50107384354041ce90950107384254041ced05501073941540419b98b54cc66d62d5331b358a43cc63e6494b318f59252cc69d64ccb318f99250cc63d64943319b988548c66d62152319e980548c67960152318fd91528c63c6454a318f992508c63d64942318f583544c63e64951318f994544c71d63151318f580544c71c5490d31b358a434c65c6550d31a7593324c71c54cc931c7151324c74c524c9318f990504c63d64141319b988504c66d62141319b98b540c66d62d50319e983540c67960d50318f596540c63d60950318fd81540c63e64150319798c540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c71d54cc431d354b310c65f654c431c7551310c74d524c4319dd95310c63e64940318f592500c73a5494031ce552500c76a5294031da54a500c73a6494031ce592500c73a5454031ce551500c76a5254031da549500c73a6454031ce591500c75b3154031dc8c5500c7593154031dc4c5500c65e63d53219758f54c863e64d4f218f59353c863e6494f218f59253c86cd6390b21ab59232c874c534cb218f99250c863d64943219798c548865d63152219e980548867960152218fd91538863c6454e218f990538863d6414e219e98053886796014e218f992508863d64942218f583544863e64951218f994544872d62151218f580544863e6494d218f592534863f6454d218f191534867b6054d219e181534872c5490921b358e424866c6550921ab592324872c548c9219b195324872c544c921d314d324863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f582540863f60550218f990540865e63150219758c540866e62150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219b988530867a6014c219e580530872d54c8421d354f210866f6548421cb551210874d53484219dd95210863e64940218f592500
  | 3 => 0x15029f30c560b4068000000688003f20014e9210f41fc7189444234c000000000013c8ea000aa0000002268e0af0000f09a4ce80013a000a480000074891a4d1362147b01d48c02c5780039e000000b929a0001c80050a00000053000000680f24ce77c000c954816c0017c11e288bb0cc58c7447f0900d89cc19005454094000002048043918a0000000006600094d028d219a880c181c0c2270c38c716e50132a71352550400894143dce99db1ca29c802864b83888902f4ea000001a125a510001d93681dcfe8000003b8d30871cc8b85096311842d1c9ec5760b9581f7294064000ae49c5e84c14f16290cd100048e8593f107000af4ae15652e00120800276738dc9c54f4000002230126093faa914c310001842dc4bc822a203c000958100001140028f4cc00000000382168000003e4740af9961d0468bd8070006512b0000000008d857000974e68000004fcd420d232630372c73da89d4993949e1cc3a9420346780a80044a95414046300000000471e6440500000000000004a41c2486580000400202c0100000000001803006000008040160000100700c000070040000200000000200000800000004000000060000100200000c0180000c0000000000000c008040080000000000e000000000000080380200400c0180b0020040100201e0200080200a000060000040040b8040140040a001008000008010000000480200600009800008004000000020000080200200401003008004098380020040101e0000000000d0000000080702e004058020020080080d00600001001002000000010000040080002c000020030000040100000001402003016000030070000001f80000a008010000040080980500200400000000000000000060000001d008004018030000b0000000060080100500802001804004000020040000040a8000000180000101000c038000020000080400800000000008000030030000000000300200000800cbd0e5290f4f4354a43ab98a4350e6e62145439b5885150e7a60145439e5805150ecd6290c438fd954310e5f6550c43ab98a43d0b1e53d0e42c794d4390b1e53d0a42d354f4290aae6290d428f9944350a9e63909429798c5150a5d63145429e9805150a7960145428fd954310acd63908428fd954210a6f65508428f58254ccb1c63553328fd8154ccb1d54d0f328f99250cca3d64943328f582548cb2c62552328fd81548cb2d54d0a32c7953328caae64cca328f992508ca3d64942329e982544ca79609513297997434cace62d0d329b997424cace63d0932e310f424cb8f4310932ab993324ca9e648c9328f990514ca3d64145329e980514ca7960145328f990504ca3d64141329d984504ca7561141329798f540ca6e62d50329d984540ca7561150329e980540ca7960150328f992530ca3d
  | 4 => 0xad8000004f600121000104328831ba09272535000000000f221b000000b99c3000000a19c80007980000026e001531d84d60014e0622d4854f780043a001568000000000026e4d013c2f00000063c8e086000768000f43ca0004198b51a130000005720000029956800000000000000000003b86e0c680000000000064000000000001d60012ca290245d0d8254000000bc80039600020000000000ee8000009c8568bf1f27a4000000360000000000047c0026d36203c0005c00000077a5a0000000000000c781419bf06e1d96280055805d550812a60e08ea5e00000000000000001590000000000012a000900001b630a000000000003080a06948a000001f54ae0913b24a00000000000000000da85119e4215780055c6ece60002b43155a8d73fc5bc0003500027c001f31108001f1c70005ac91000000990020001f80001a0002c8a40000a842497d2200000628cac800426478ef0235420015f0000009f4421ad324480000000000005219f0004c00023f320a9ca71be076000d200000085ce11e25624a0eb1970006ac2a1b344c0012600000016400191000920000000000003e1352fe51c0029140e0011a80057e000000000006c90612c0000000000d4442a8db80013c390001500005a55b8004e09b0072372f0001041c400030c00042000000000002fc00000131000554b600000018c0c000404a6c760005108d9420003ce0000022c03e424002181787c524a1e4643c0fe2b80e255c188f50143a51a22d35e000f5ac42188f9081bc22c620b815d4120015584804ca246d83a12e4b8099fb24c000000000ac00000000000228000000008693b800000000001612ee0003a0004b6000be800000000000001747c0001c00003508ba8c474000000ff1b00010e0d6000000641ac2c4000000003c2000000000003ec00000000000001c60103000006011c0006c8d5214a1c8a800000000000000000014a9812ea318cc8001cea0826a9e0524d9280004a4000001d50888ec000000005b4002c3000ae8818b30000000004e00000000001000000002602b68f4a0a580006a82582c4a2000000003fea2cfb1ae3ae6693a00000058000166164000000000228cc2f8be0000000003f000154378000004600000011a0000022b000000caabc27c64c000001340014d0950a4000f1800000a04000000003741e00033659d0887b00010435800000058000000000d8000fd000444000001be001141f400000000000060000b28000fa10d3e20319c5194c0b629622c9d0003d4acc338004f0000ce1141da304d3a8021c6249c0912a400000000000000000960001e400000000a50d18001260000007024e00105a1f408000001a51c240400000000000f7000000000000b00000005d82207a000920000b04f4000dc20a000a62610002f5378201e27a
  | 5 => 0x23000003000000000b080024b3a8680c71320002d4a28000568c5310000002a4fc0ac40ca8c3f0fa000b04e51511320000005d2668f07c0a50ca0b4002c004e00019821428a28280001bc2e0000002e298d1206d41e0000010d1c0000000000000000022f000a48de8000005209a02a000494cc000000001528000001a8878da2e4864000000004a40000051c000010ab3f4a589e000168
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x247a2580100338018e80000d80b2639a000a1cc864aed02ab040020a8140012c00400c808002873a6ca99065515c4544c832a92e02a2641943970191510cb0632264a88658354e6290c41c1cc6a948420d2a7290d501068d39c84a8083831516290d3183aec2a66498e0c5458e4248616bb0a9192432c5c4604c940d1264b0064a04d171181324c384a928098061c4545404c0309c2e23026490709535012008390a8a8090041345cc61501109c2e430a80885917318540442d0b90c2a02212c1d93150110960ec90a808853175d011004388a9e8088021c854b4044010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8909809d3654c832a09801913254432
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
  | 4 => packedAt s5K4 (29663+((h/237+packedAt s5K4 (27056+(h % 237)*11) 11) % 1137)*11) 11
  | 3 => packedAt s5K3 (1530+((h/10+packedAt s5K3 (1470+(h % 10)*6) 6) % 40)*6) 6
  | 2 => packedAt s5K2 (122+((h/1+packedAt s5K2 (120+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xcf0fe1f8f1fe3f8fc78c7c7e11f8fe3f0dc4cf
  | 1 => 0xff1fe3ffe1fc7f1f80f8f8ffe3f0fc3127b33
  | 2 => 0xf001ffc0ffe007fe3ff00ff01fc00ffce38c3c
  | 3 => 0xfffe0000fffff8003ffff0001ffff000fc0fc0
  | 4 => 0xffffffff000000003fffffffe0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x6140280110484210010414124048421204c045
  | 1 => 0x2004000200008020000808402100400001112
  | 2 => 0x80ac8492448495005a900920948229a8630c28
  | 3 => 0x42415a489140124aca920011926a088b80e80
  | 4 => 0x28c919300dd92649374e4e49c004c132dfe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36318
namespace PEqualNP.Outside.L_meta_36318
open PEqualNP.Outside.L_meta_36318.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x6c789000c62800880000098b0040a40064660e2e58018004a49f0228dc51f0a2089978e508474fcebd68383a45400b9302ac02f5acdb2700d481e76000150001c0b623400000c801a0100080014a180821228c8000040000e00a0001ffd5007fe5401ff55007fc54027fd4c09fe53027f54c09fc5301ffd0c07fe4301ff50c07fc43027fd4809fe52027f54809fc5201ffd0807fe4201ff50807fc42007fcc801fe32007f4c801fc32027fd44097f51017f94409fd51005f54405fc5101ffd0405fe4101ff50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc21027fd4003fe50027f54003fc5001ffd0007bf4000ff90007fd40006f50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a400bff99520025fcca9002ffd65480177eb2a400bff19520025f8ca9002f7c65480093e32a400affd9120055fec89002bfe64480077f322400aff59120055fac89002bfc64480077e322400affd5120057fca89002bfd5448015fe2a24000ffd8d20005fec690003fe63480117f31a4000ff58d20005fac690003fc63480117e31a400bffd4d2005ffca69002ffd5348017fe29a400affd0d20057fc869002bfd4348015fe21a4001bfd892005ffea49001ffe5248017f7292400bff5492005fdaa49001ffc5248015ffa124007ff90920057fa849001ffc4248001ff9924007ff8c920007dc6490003fd3248001f69924007ff0c920007fec290002ff6148013ff30a4002bf98520007fac290027fc61480057e30a400bffd452005efea290027fe5148017fea8a4000df5452004ff8a29002bff4148013ff20a400aff5052004ff88290003ff3148013ff18a4000ff4c52004ff8629001fff2148001f790a4009ff88520007fa4290003ed214800ffe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007bf4048003ff2024001ff5012000f7a8090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9024007fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007ff1048003ff0824001fe8412000ff8209001bff654400d7fb2a2006ff99510025fcca8801bfd654400d7eb2a2006ff19510025f8ca88017ff644400b7fb222005ff9911001dfcc888017fd644400b7eb222005ff1911001df8c888017ff544400bff2a22005ff5511002ff8a888003ff63440017fb1a2000ff98d10045fcc688003fd63440017eb1a2000ff18d10045f8c68801bff534400dff29a2006ff54d10037f8a688017ff434400bff21a2005ff50d1002ff88688003ff62440017fb122000ff9891003dfcc488003fd62440017eb122000ff1891003df8c48801bff524400dff2922006ff54910037f8a488017ff424400bff2122005ff5091002ff88488003ff3244001ff1922000ff4c910007f86488006ff6144005ffa8a2002dfd4510017fca28800bf65144005fea8a2002df54510037eaa288003755144005fe28a2002ffd0510017fc828800bfd4144005fe20a2002ffcc510017fc628800bf63144005fe98a2000fd4c510017f8628800bff2144005ff10a2002fd88510017fa4288003f52144005fe10a2001bfd811000ffea088007fe5044003fea822001ff1411000ffe8088007bf4044003ff2022001fe9011000ffa8088007bd404400bfca022000ee5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7de30cc003fd1866001ff0c33000fb86198007fe20cc003fe1066001ffc433000ffc2198007fc10cc023ffb2a6011bfd9530006feca980027f654c023ff32a6004bf9953008ffaca98046fd654c023fe32a6004bf1953008ef8ca980127c654c021ffb226010bfd9130087fcc89800efe644c021feb226010bf59130087f8c89800efc644c021ffaa26010ff95130087faa898043fc544c0037fb1a6011ffd4d30047fca698047de534c023fea9a6011f754d30047f8a698043ff434c011ff21a6010ff50d30047f88698003ff624c0017fb126000ff98930007fac498003fc624c00f7e3126011ffd493008ffca498047fd524c023fe2926010ffd0930087fc8498043fd424c021fe2126008ffcc930007be6498003fe324c001fe9926000f74c930047f86498003ff614c0017fb0a600fff98530015fcc298003fd614c01ffe30a6002bf1853008ffea2980477f514c01fff28a6011ff54530006faa29803ffc514c021ffa0a600fff90530087fa829803ffc414c011ff98a6000f7cc53007ffc6298003fd314c001ee98a6008ff0c530007fe429803ffe214c001fe90a600fff0853000dfec098007ff504c003ff2826001ff5413000ff8a098007ff404c003dfa026001ff9013000ffa8098007bd404c003fe2026001ffcc130047f66098007fe304c003ef1826001ff0c13000fb86098007f8304c003ff1026001ff0813000ffe2098007fe104c003fd0826001ff0413003ffecb9001eff65c800fff32e4004bf9972003ffacb9003afd65c800ffe32e4007bf1972003ffec99001eff64c800fff3264003bf9932003ffac990036fd64c800ffe3264007bf1932006ffea990037fe54c801bfeaa6400dff1532003ffec79001eff63c800fff31e4008bf98f2003ffac790002fd63c800ffe31e4007bf18f20077fea79003bfe53c801dfea9e400eff14f2006ffe8790037fe43c801bfea1e400dff10f2000dfcc59001fff52c800fff2964007fb94b2003ffaa59003bed52c800ffe2964007ffd0b2003ffc859001ffd42c800ffe2164007ffccb2003ffc659001fee32c800ffe9964000fb4cb2003ff8659001fff61c800fff30e4002bf9872003ffac390002fd61c800ffe30e4002bf18720077fea39003b7f51c8019ff28e400eff54720006faa390033fc51c801bffa0e400cff9072006ffa8390033fc41c8001ff98e400cff8c720007fa6390033fc31c800fff90e4007fbc872003ffc439001ffd21c8001f690e4007ff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003dfa064001ff9032000ffa8190007bd40c8003fe2064001ffcc32000ffc6190007fd30c8003fe1864001ff8832000fdc4190007fa20c8003fe1064001fb0832000ffe2190007fe10c8003fe086400bffd952005dfeca900037f65480013fb
  | 2 => 0x21005fac690803fc63484117e31a4219ffd4d210cffca690867fd5348433fe29a4218ffd0d210c7fc8690863fd4348431fe21a4202bfd89210cffea49081ffe5248433fea924207ff149210c7fe849081ffe4248431f72124218ff509210c7da849081ffc4248401ff9924207ff8c921007dc6490803fd3248401f69924207ff0c921015fec29080bff5148405bfa8a4202ff94521017faa29080b7d5148405fe28a4202ffd0521017fc829080bfd4148405fe20a4202ffcc521017fc629080bfd3148405fe18a4202ffc852103fee429080bfe2148405f710a4202ff08521017d8429080bf42148401ffb024200bfd81210bffcc090806fe6048401feb024217ff1812100df8c090867ff504842fff2824219ff541210bff8a090863ff4048431dfa024217ff901210c7fa809085ffc404842fff1824217ff0c1210bffc409081ffc2048405ff8824202fdc4121017fc209080bfc104842ddfb2a8016ef995400b77acaa005bbc6550001dfb1a8000ef98d400077ac6a0003bc635002ddfa9a8016ef94d400b77aa6a005bbc5350001dfb128000ef989400077ac4a0003bc625002ddfa928016ef949400b77aa4a005bbc5250001df9928000ef8c9400077a64a0003bc3250001dfb0a8015ef985400077ac2a0057bc615002ddfa8a8016cfd45400af7ca2a005bbd51500019ea8a8015ef145400077e62a0057be3150001de98a8015ef0c5400077e42a0057be2150001de90a8015ef0854000f7ec0a0006bf6050007ddb028001efd414000f7ca0a0007bd5050003de2828001ef8c14000f7860a0007be2050003de1028001efc414000f7c20a0007ba1050003de0828008ffd9730045fecb98023fe65cc0097f32e6008ff597300a5facb98023fc65cc0117e32e6008ffd9330045fec998023fe64cc0077f3266008ff5933009dfac998023fc64cc0117e3266013ffd533009ffca99804ffd54cc027fe2a66001bf98f30047fea798023fe53cc011ef29e6008ff54f300a7baa798023fc53cc011ffa1e6008ff90f30047fa8798023fc43cc011ffb166008ff98b3003dfcc598023fd62cc0017eb166008ff18b300a7fea598053fe52cc029fea966014ff14b3009ffe859804ffe42cc027fea166013ff10b30047fe6598023df32cc011ff1966008ff4cb30007ba6598023fc32cc011ffb0e6008ff98730015fcc398023fd61cc0017eb0e6008ff18730015f8c398053ff51cc029bfa8e6012ff947300a7faa3980037d51cc025fe28e6013ffd0730097fc839804ffd41cc025fe20e6008ffcc730047be6398023fe31cc011fe98e6000f74c730047f86398003ff21cc025ff10e6000ff48730097f84398006fd60cc003ffa866001ff9433000ffaa198007fc50cc003ffa066001efd033000ffc8198007fd40cc003dea066001ff1033000ffc619800
  | 3 => 0xf32a6204bf995310fffaca9887efd654c43ffe32a6204bf195310f7fec89887aff644c401dfb226200afd91310f7fcc89880efe644c43dfeb22621ebf591310f7f8c89880efc644c43dde3226203af191310f7fea89887bfe544c43dfeaa2621eff15131015fec69887fff534c411ff29a621fff54d31047f8a69887bff434c411ff21a621ef790d310f7fa869887bdd434c411fe21a6200ffd8931005fec498803fe624c401feb126200ff1893103df8c49887fff524c43fff292621fff549310fff8a49887bff424c43dff212621eff509310f7f88498823ff324c401ef9926200ff8c931007fa6498803dd324c411fe1926202bfd8531017fea29880b7f514c405ff28a6202ff54531016faa29880bfc514c405ffa0a6202ff90531017fa829880bfc414c405ff98a6208fdcc531017fc629880bde314c405fe18a6202f70c531017e8629880bfe214c405fe10a6200ffd8131005fec098877fe604c4037f3026200ff581310eff8c098806fc604c43fffa82621dff941310fffaa098877fc504c43dffa02621eefd01310effc809887bfd404c43bfe202621dff8c131047f86098877fe204c43bfe1026202ffc4131017ee209880bfe104c405fe0826207ffd972103dfecb9081ffe65c84097f32e4207ff597210e5facb9081ffc65c840f7e32e4207ffd932103dfec99081ffe64c84077f3264207ff593210ddfac99081ffc64c840f7e326421bffd53210dffca99086ffd54c8437fe2a64207ffd8f2103dfec79081ffe63c84117f31e4207ff58f21005fac79081ffc63c840f7e31e421cffd4f210e7fca790873fd53c8439fe29e421bffd0f210dffc879086ffd43c8437fe21e4202bf98b2103ffea59081ffe52c840ffea964207ff14b2103ffe859081ffe42c840ff72164207ff50b210dfda859081ffc42c840fff9964207ff8cb2103fdc659081ffd32c8401f69964207ff0cb21015fac39080bff51c8405bfa8e4202ff94721017faa39080b7d51c8405fe28e4202ffd0721017fc839080bfd41c8405fe20e4202ffcc721017fc639080bfd31c8405fe18e4202ff88721017dc439080bf621c8405fe10e4202fb0872103ffec19081ffe60c84037f3064207ff58321005fac19081ffc60c84037e306421cffd43210d7fca190873fd50c8435fe286421bffd03210df7e819086bfe40c8437fea06421aff103210d7fc619086bfc30c840fff1064207ff08321017fe219080bfe10c8405fe0864219ffd95210cdfeca90867fe65484097f32a4219ff595210cdfaca90867fc65484097e32a4218ffd91210c5fec890803bf64484015fb224218ff9912101dfcc890863fd64484317eb224218ff1912101df8c890863bc64484075e3224218ffd51210c7fca890863fd5448431fe2a24200ffd8d21005fec690803fe63484117f31a4200ff58d
  | 4 => 0x1ffc640c80f7e3206427ffd503213ffca81909ffd540c84ffe2a06408bf98c32047fea619023fe530c811fea986408ff14c32047fe8619023fe430c811fea186408ff10c3203dfcc41901fff520c80fff2906407ff5483203ff8a41901fff420c80fff2106407ff5083203ff8841901fff320c80fef9906407ff8c83203fdc641901ffd320c80fee9906408fb4c8320079a641901fff610c80fff3086402bf9843203ffac219002fd610c80ffe3086402bf18432147fea2190a37f510c84dff2886428ff54432137f8a21909fff410c84dff2086427ff50432137f88219023fe310c811fe1886407ff8843203ff8421901fff600c80fff3006401bf9803203ffac019002fd600c80ffe3006401bf18032147fea019097fe500c851fea806425ff1403213ffe801909fbf400c84bff2006427ff5003212ff88019023fe300c811fe1806407ff8803203ff8401909bff100c84bff0806425ff04032126fec8a88937e6454449beb22a224df19151006fec6a88037e6354401beb1aa200df18d51126fe86a88937e4354449bea1aa224df10d51006fec4a88037e6254401beb12a200df18951126fe84a88937e4254449bea12a224df10951006fe64a88037e3254401be992a200df0c951016fec2a880a7f6154409bbb0aa202dfd0551016fc82a880b7d4154405be20aa202df8c551016f862a880b7e2154405be10aa200dfd815111efcc0a88037d6054447be302a224dfd01511267e80a888f7e4054449bea02a223df1015111efc60a888f7c3054447bf102a223df08151016fe20a880b771054405bf082a202df04151047fecb98822ff65cc411ff32e6204bf99731047facb9888afd65cc411fe32e6208bf19731047fec998822ff64cc411ff3266203bf99331047fac998886fd64cc411fe3266208bf1933110ffea998887fe54cc443feaa66221ff15331015fcc798823ff53cc411ff29e6208ff54f31047f8a798823ff43cc411ff21e6208f790f31047fa8798887dd43cc411fe21e6208ffd8b31047fcc59881efe62cc411feb166200bf58b31047f8c59888bff52cc445ff2966222ff54b31117f8a598887ff42cc443ff2166221ff50b3110ff88598823ff32cc411ef9966208ff8cb31047fa6598803dd32cc411fe1966202bf58731017fea39880b7f51cc405ff28e6202ff54731016faa39880bfc51cc405ffa0e6202ff90731017fa839880bfc41cc405ff18e6202f78c731017ec639880bfc31cc405ee18e6202ff88731017f84398823ff60cc411ff3066201bf98331047fac198802fd60cc411fe3066201bf18331117fea198883fe50cc445fea866220ff1433110ffe8198887bf40cc441ff2066221ff50331107f88198823fe30cc411fe1866220ff88331107f8419880bff10cc405ff0866202ff043310fffeca9887eff654c43ff
  | 5 => 0x4732197f8a3990cfff41cc865ff20e6433ff50732197f88399023fe31cc811fe18e6432ff8873203ff84399023ff60cc811ff3066401bf98332047fac199002fd60cc811fe3066401bf183321a7fea1990c7fe50cc869fea866431ff1433219ffe81990cfbf40cc863ff2066433ff5033218ff88199023fe30cc811fe1866431ff8833203ff841990cbff10cc863ff0866431ff0433203ffecb1901eff658c80fff32c6404bf9963203efccb190127e658c80ffeb2c6430bf5963203efacb190027d658c80ffe32c6407bf1963203ffec91901eff648c80fff3246403bf9923203f7cc91900ebe648c80ffeb24642fbf5923203f7ac919002bd648c80ffe3246407bf1923217ffea9190bffe548c85ffeaa4642fff1523215dfac7190c3ff538c811ff29c6430ff54e32047f8a7190bfff438c811ff21c642fff50e32047f8871901efe628c80fffa946407ff94a3203ffaa51901ffc528c80fffa146407ff90a3203ffa851901ffc428c80fff9946407f7cca32047de651901fff618c80fff30c6402bf9863203ffac319002fd618c80ffe30c6402bf18632187fea3190c37f518c85dff28c6430ff54632177f8a3190bfff418c85dff20c642fff50632177f883190bbfe318c811fe18c6407ff8863203ff8431901fff608c80fff3046401bf9823203ffac119002fd608c80ffe3046401bf18232187fea1190b7fe508c861fea84642dff1423217ffe81190bfbf408c85bff204642fff5023216ff881190b7fe308c811fe1846407ff8823203ff841190bbff108c85bff084642dff04232167feca990b2ff654c859ff32a6404bf99532167faca990b2fd654c859fe32a6404bf1953215ffec8990aeff644c857ff3226403bf9913215ffac8990aefd644c857fe3226403bf1913215ffea8990affe544c857feaa2642bff15132167fea699023fe534c859fea9a6408ff14d3215ffe8699023fe434c857fea1a6408ff10d32167fea49901ffe524c859fea926407ff1493215ffe849901ffe424c857fea126407ff10932047fe6499023ef324c80fff1926407f78c932007fec299002ff614c855ff30a6402bf98532007fac2990abfc614c8057e30a642cffd4532166fea2990abfe514c859fea8a642aff1453215ffe82990abfe414c857fea0a642aff10532157fc6299023fc314c855ff10a6407ff08532007fec099002ff604c853ff3026401bf98132007fac0990a7fc604c8037e302642cffd413214ffca0990b3fd504c853fe282642bffd013215f7e80990a7fe404c857fea026429ff1013214ffc6099023fc304c853ff1026407ff08132157fe20990a7fe104c853fe0826407ffd943203dfeca1901ffe650c8097f3286407ff59432145faca1901ffc650c80f7e3286407ffd903203dfec81901ffe640c8077f3206407ff5903213dfac819
  | 6 => 0x1011800000000021980000014e94303e908079800158894000000219137061a1584c08d14c000191a2f08314a0002ad8000001e0a11a638fd2881100e88020b49ea0230e120a0d09aa93310600f22413d0c084ea5a8409d59dc8701a61ab0540730000000069638000000000eaa338f4a74a1380009626106407914621e15d8001388000000cd8008180580000980100200401002004084030010120040181100a018030010000000002c006000008020300000102c00c01c0f00100c02c0080c00a0300080900000000000032004098070000540c00601c00c000010040440400500c000010040020140581600600405800006004038020140040e00700005c0000400201c0300f00e00004804008004148050080000280401a02000000020000020020000140181601401c00000006000160110000440180a002034008050040100880400000c00017002010048000020380380207e004000000180080000e00800c0000202a02c0000001201800000002004000000140180f80601a0181180202404c000290000040080900c0080600300200c0200300200801006006038068040020100580600a0100000200c00400014000058000050000080500b00600000000000000058000080000000a00001c0100100e00c0180200000c0180201e0000200502e048000150080000a8030060000180000a020080050320000280e01c05004801014008020160080140000002a0040100701400400810004000008170000140000700400c018020040000200001e02c0000100003c03001000000000000020180181b0060040080200000800001006034000020020240002f004004048020040000000000006c00802000004020000060000600800c014018000000000001a01200011002020000008000140040700000a000080000080000080f0000600200a0000200000001c0100800000000002807004000008040040000a00000e00003804006000008000300200080e006010008200060200700101202c00000004004008130080140400300000c0000d008004180020000440480002e04800023ff65cc8117fb2e6408ff99732025fccb990237e65cc8093f32e6408ff597321a5facb990237d65cc8013eb2e6408ff19732045f8cb99023ff64cc8117fb266408ff9933201dfcc999023be64cc8075f3266408ff5933219dfac999023bd64cc8015eb266408ff19332045f8c9990cfff54cc867ff2a66433ff5533219ff8a999023ff53cc811ff29e6408ff54f32047f8a799023ff43cc811ff21e6408ff50f32047f887990d3ff52cc80fff2966434ff54b3203ff8a5990cfff42cc80fff2166433ff50b3203ff88599023ff61cc811ff30e6402bf98732047fac399002fd61cc811fe30e6402bf187321a7fea3990d37f51cc865ff28e6434ff5
  | 7 => 0x795b0648a989387f15280015191124b86c8001618c690b1f62598001eba9723319b0001b60582b32798f095d012a8913d8ee0600000001bb186a4580000002a01e985950a6604a0a91911040fc8cf8e580022399d080a499adaae2780000001a41758668000000fa80005005c1cba1080008c82d0000001560001481b8908a030891b59ce1b490a9c28e804b81a18b81f0ca1959848f40151f302490709a8861368751949d29f91699c429423d8001d08002708440930b5a1d97e88e80991f85eaa400005795519080000014101b84d8001c61b780025011e8001db17510ba5da4913810126a8140aa1c50b8200a270bf86e0f61808bd9900fc10fa1f9359f71692439da9f98280c624f9b19b6a231a1a858d189f97c00000010d8000001d61ee0000000db9bb94f0000000b08ae00000027600000028b84394d80009097f96a947a4216f0001442988000c78729c78000000da8000001f697d00006d26fa91a3e1b326216098d0c318802427e8880000432401fe9962b22a22ad0550f706619504916c97aa368a0a9d00724e02e26c19c220a059cc8b01151742488001bd0000c51b20000000000000000000000000000000001e802917480000000009892327daa80a598f22e00000014500001386703d8000001291e21c8a772a980028780000019f0b6800051a668001228001710c589c95380000016009007211484c9258162360f90e60000000002568002a880003326d82b800216a0e1c81109a91029671ff9b101f9f38709189929de0001d20420cc8390262a323584895f8a3a931b3854a9c035271007a5198229492402184f83018f8b10d90f00000000ee97390e8000b41ae8418cf0bf02880018627a9dc1e91161c99cd8001210ca80000000023295ca041b29d30712822769fa27300000000009103d2ab98704580029d87a8001850658a28000bb1979e780029007480011f1bf8b79271ce95997daa6000046218a0d8c003796ba3f1118d9aaa99a0000001ff00015e97f00026e0e20000f784289ea0480000005fa9faa28afa2110508e0aa8229da20b000113a3480396e8b89db9268dc000000127a75170988a0686f9e580027409d1a7a419e680000000009925ba7c8000f596f9458638d100012ea9a11b8268801578000000000f180000000021f03e18e0c800021a80012a00000000018000000000000000003200000022aa381622512862b100020c1ec1818000000002a08000001438002898e703580000009a22908d80010d0000002111c71dd000000000000000000264a2c1782811c907f895a0215723515f00024f23a00006084017ba2580019b8c48002922848000002b00000001378001008f5000000000085a269a29a0a1e8ff9a98000011310e680000022d02f19e0c90000000ed25a0d890a0812b29a81329649d38b20
  | 8 => 0x14980000000000000000000000000028d92c00000000001900010c0000000000002580001ef8c21f21989ca8058be0000000002578000000001ad0002688000000250000001f880016d28d06c15e25c0002478178000002a709f17292507580000000000020e99300c0001e00001032559d48b381b23400000000000000016e15400019aab080000024100028a00b8001df00000005e1841631cf8dd9ec8ef01c0919f58d3a4c9a3800167a5225e20727c0c18d68cd0bd00026b1f080004997180000b00022d8631d78819791130531b08cc06a8bc2968000a00b32161d900011c2af921a440d412a9cb0000000fd8571ac9a59c200f84b0ba1ee831a6183087608428c06a26f0000f88b99dd8898e913929909800009d9d42471cd27b0d709980821200003b9828000b5000000000284116a640650ad9e3a628f100c87a11c8eb87d15a02a85909c03f8f300000000021c892214193a5e8c985da789e48b726c9a68ef8c118ca54a8f800000117a01a4d8001c180017a2a699908f8e196880023b23d0e40000cb00013b8000000000a313e02e80020aa2b0000000000000d59ef00000002c0fb2220ad07c00025300020c989867a1828ca631c12a49580000000001d18f68d220d1e196a24292e0002200000000000000000000000001732480ac81d14480000005b1468000e38000b197603c8829658a21048c725920f871a3900007c8000000001249d82508089810ce8be80010000000006b1be0538000000002aa00000024a24d179a5d00024500009e13400000000000008f0000000000ea2588da1c4a051cc0000000002130000520a68000000002a90000002828000001318a883a00015698a80600003807d8000001141af8000000969c01ed92880001720113a2288001c588b8000b628b094a6800000000022ba6e9cf21020f1591771c68f829c85a8d32320ab9320e481aa4b03c00911591998b0bc81d8e795c123aac2ae802a9b1a726a08c0fe2038f29922700d61c3839a2c883800000252a1c2248b914b8002650001e10272909f51d01338bb80000e811aab18d8ab135244a9614010980011d0680001490000362608768279f80848af2831de8001078eb1a52869c0a149a100029822e83a8ce17c8f382200027580021d0978000ec27383680018785b98300004513b08b1fca178000de0002078000000001058928109409e880007ba9a80003f1201302818ac1998000001e2a8e8000cb9fe00026580000000000000080022a0001b4000269058aa192b11e1e313fa308fb8a190c86da1ba3b93c15aa30202852a228002a00180000000030000001348d51a4a801b01a880018a0f98001f2800033a5394a9e41b825b0001f18001b50000001af29380014714d04aa431fd80180029299f9b725623780027f0001e98000000879bf23117
  | 9 => 0x1ba1221fd000196a5ca2180024600004793a8448000c292d8c88210fe8000001ea9488000000000001aa0fa14200005c800000288942a728000a79d682c800078aa11bda5712f92800018c05a28f09b8e088a9b907ea8a9ed1fc19c91a20997e06e80022600023e96b01594b1ca00405080000000012d0001fb846a170198611e725516d8e01982670001628689d9a9f102183a000f22092408e5000170229a1b2280c382082f9520740a628500022f94c80018909702b2720db2ac8471610110869e515312ca7a04d01483b1419970822911209361f415013f2372b186200010e077a950dd24c1789a21ae2062790d492611a95107e1e610928381c8000d79ba8baaaf1b980000000008a176859aa5a6b8a10a48e9a4a9fb0372128b288529b9941f786b816aa79299a300027e29e8000000239399ac19da3180e004877029a67a3a84823c1668df1309bc2a50562080000000188a70200000eca7d05f27780026028721a07382da540ed87b00018ea15271a6989b08712b99ea999558de8d81171f100011b0001039f496500500013e8a41dfa3f96c08895b9ab8629bc9c320ba9583404e1fa93c80d90f0e289507806f154a39856a809d7101a5f9eb28e11280026d29e051227aa38002978699d88328000000d01069a00000d29be8410ff1680ae80a86914e04f16420880027f8a50dc92f00d0df8120389660c411d94f82583101e1121d517b013000238a251d1246a3c834a5f00011905d0000558000e327b80a0a824e9721f0
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x774485101dfb47448510005f77348510005f57348510015f77248510017e77248510007e7624851003ef6624851003ef46248510007e462485101dfe642485101dfe54248510007e63248510007e53248510007f3704851000df6704851000df470485100bff07048510016f76048510017f360485100bfb740485100bff240485100bfb540485101dff140485100bff230485100bfe720485100bff220485100bfe5204851002fbb765011001ebb76501100afb8765011001eb876501101d7bb75501101cfba75501101d7b975501101cfb875501101cfbb65501101cfba65501101cfb965501101cfb86550110007bb7350110007ba7350110007b97350110007b87350110007bb6350110007ba6350110007b96350110007b863501101cfbb53501101cfba53501101cfb953501101cfb85350110007bb7250110007ba7250110007b97250110007b87250110007bb6250110007ba6250110007b96250110007b862501101cfbb52501101cfba52501101cfb952501101cfb85250110007bb3250110007ba3250110007b93250110007b832501100afbb7150110007b371501100afba71501100afb971501100afb871501100afb0715011000fbb615011000ebb615011000fb361501100afbb51501100af3b51501100afba51501100afb251501100afb951501100af3951501101cfb151501100073151501100afb851501100afbb31501100afba31501100afb231501100afb93150110007b131501100afb831501100afbb21501100afba21501100afb221501100afb92150110007b121501100afb82150110015f8764c110046f8764c110014f8764c1100077b754c1101bf78754c1101c5fb744c1101c5f9744c11000dfb734c11000fdb734c110007db634c110046fa634c110046f8634c110007d8634c1101bfda534c1101bfd9534c110005fb724c110007db324c110007d9324c110007f3714c110015fa714c110015f8714c11007ff0714c11000efb614c11000ff3614c11007f7b514c11007ff2514c11007f79514c1101bff1514c11000771514c11007fdb314c11007ff2314c11007fd9314c110007f1314c110007d1314c11007ff2214c110007f1214c110015f8764811003ef87648110014f876481100077b75481101af7875481101b5fb74481101b5f97448110005fb7348110005f9734811000dfb724811000feb7248110007eb624811003efa624811003ef86248110007e862481101afea52481101afe95248110007ea3248110007e93248110007f37148110015fa7148110015f8714811004ff0714811000efb614811000ff3614811004f7b514811004ff2514811004f7951481101aff1514811000771514811004ff23148110007f1314811004feb214811004ff2214811004fe92148110007f12148110007e12148110
  | 1 => 0x89100bebf40589100bebd405891020cfe76189100357e75189100057d751891002dbe7418910005bd7418910005de7318910005dd731891003eee6218910006ed6218910044ff76cc910004fe76cc910004fd76cc910044fc76cc9100357e75cc9100057d75cc91002dbe74cc910005bd74cc910046de63cc910006dd63cc910006ef62cc91003eec62cc910015f671cc910005f571cc91000dfa70cc910005f970cc91003cff768c910004fe768c910004fd768c91003cfc768c9100357e758c9100057d758c91002dbe748c910005bd748c910006df638c910046dc638c91003eee628c910006ed628c910015f6718c910005f5718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c910046de634c910006dd634c91003eee624c910006ed624c910015f6714c91000dfa704c91003cff760c910004fe760c910004fd760c91003cfc760c910006df630c910046dc630c910006ef620c91003eec620c910007cd320c910015f6710c910005f5710c91000dfa700c910005f9700c91003777765451002677765451011f7476545100267476545102077774545101ff7674545102077574545101ff7474545101ff7764545101ff7664545101ff7564545101ff7464545100077773545100077673545100077573545100077473545100077763545100077663545100077563545100077463545101ff7743545101ff7643545101ff7543545101ff7443545100077772545100077672545100077572545100077472545100077762545100077662545100077562545100077462545101ff7742545101ff7642545101ff7542545101ff74425451000777325451000776325451000775325451000774325451011f77705451000773705451011f76705451011f75705451011f74705451011f70705451001777605451001677605451001773605451011f77405451011f37405451011f76405451011f72405451011f75405451011f3540545101ff71405451011f74405451011f77305451011f76305451011f72305451011f75305451011f74305451011f77205451011f76205451011f72205451011f75205451011f74205451000df4764c510046f4764c51000cf4764c5101f5f7754c5101f5f5754c510007b7744c5101efb4744c510015f7734c510017d7734c510007d7634c510046f6634c510046f4634c510007d4634c5101efd6434c5101efd5434c510005f7724c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100eff0704c510016f7604c510017f3604c5100efb7404c5100eff2404c5100efb5404c5101eff1404c5100efd7304c5100eff2304c5100efd5304c5100eff2204c51000df4764851003ef4764851000cf476485101e5f775485101e5f57548510007b
  | 2 => 0x5ef7348520005ed7348520006ef6348520006ed634852003def714852003fe77148520007e76148520016ee6148520016ec614852004fe4614852004f6f514852004f6d5148520007eb704852000dee704852000dec70485200bfe8704852003eef604852003feb60485200bfaf40485200bfad40485200bfe710485200bfea1048520044fe76d8d10004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d10004ff74d8d1001cfe74d8d10004fd74d8d1001cfc74d8d1003cfe72d8d10004fd72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d102267f51d8d102267d51d8d10226df31d8d10226dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d1021ebf40d8d1021ebd40d8d1021edf30d8d1021edd30d8d100ecfd7698d10006df6398d100edf57198d1007df97098d10044ff7658d100057f7558d100357c7558d10005bf7458d1002dbc7458d10005ef7258d10005ec7258d10105f77158d10095fb7058d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d10004fd7458d1001cfc7458d10006bc7458d1001cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d10104ff7158d10006f77158d1007e7f5158d1007e7d5158d100ecff7058d10006fb7058d100eebf4058d100eebd4058d1021cfe7618d100357e7518d100057d7518d1002dbe7418d10005bd7418d10046de6318d10006dd6318d10005ee7218d10005ed7218d1003cfe76d8910004ff75d8910024fe75d8910004fd75d8910024fc75d8910004ff74d891001cfe74d8910004fd74d891001cfc74d8910044fe73d8910004fd73d891000cff71d8910014fe71d891000cfd71d8910014fc71d89102167f51d89102167d51d8910216ef21d8910216ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d891020ebf40d891020ebd40d891020eef20d891020eed20d89100bcfd7698910006ef62989100bdf5719891004df9709891003cff76589100057f75589100357c7558910005bf745891002dbc7458910005df7358910005dc73589100d5f77158910065fb7058910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe7458910004fd745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910044fc7358910006dc7358910044dc7358910006ef72589100d4ff7158910006f7715891004e7f515891004e7d51589100bcff7058910006fb705
  | 3 => 0xb704c92000df8704c92000dec764c920046ec764c92000cec764c92028def754c92028ded754c9200076f654c9202876c654c92003def734c92003fcf734c920007cf634c920046ee634c920046ec634c920007cc634c920046cc634c920005ef714c9202876f514c920007eb704c92000dee704c92000dec704c92014fe8704c92003eef604c92003feb604c92014faf404c92014fad404c92014fcf304c92014fcd304c92014fea104c920014fe76d852005d7c75d85200067f65d85200067c65d852004ef661d8520004ff75d85200067f75d8520024fe75d8520004fd75d8520024fc75d85200067c75d85200247c75d8520004ff74d852001cfe74d8520004fd74d852001cfc74d8520044fe73d8520004fd73d852000cfd72d8520014fc72d8520006ee32d8520006ed32d852004e7f51d852004ef621d852000cfe70d852003cfd70d852000cfc70d85200d6bf40d85200d6bd40d85200d6f710d85200057f755852005d7c75585200067f65585200067c6558520005bf7458520055bc7458520005df7358520005dc735852004ef461585200067f76545200057e76545200067e76545200047e76545200067d76545200057c76545200067c76545200047c765452027e7f64545201267e645452027e7d64545201267c64545200067f63545202767e63545200067d63545202767c63545200076e72545200076d725452011e7f62545200076e32545200076d325452026d7f715452005f77715452004e7f61545200167e61545200167c615452011e7f605452011f3f405452011f3d40545202677b205452011f6e205452011f6c205452011f78205452011f77105452011f7a1054520004fe76cc520004fd76cc520044fc76cc5200067f65cc5201167c65cc520046de63cc520006dd63cc52003dee72cc520005ed72cc520007cd32cc520004ff764c520004fe764c520004fc764c5200067f654c5200fe7c654c520005bf744c520055bc744c520046de634c520006dd634c520007cd324c52025dee76c852003eee76c852003def75c8520255ed75c85200076f65c852024f6c65c8520246ef64c8520246ed64c852003def73c8520005ed73c8520006ef63c8520006ed63c85200bded71c8520016ee61c8520016ec61c852004f6f51c852004f6d51c852003feb70c852000dee70c852000dec70c852003fe870c852003eef60c852003feb60c85200d7af40c85200d7ad40c85200d7ea10c852000cfc76485200067f65485200ce7c6548520005bf7448520055bc7448520006f76148520016f4614852003fe42148520005fb704852000df8704852003fe8204852000dec7648520016ec764852000cec764852023def754852023ded75485200076f65485202376c6548520007af744852022fac744852022eef644852022eed6448520
  | 4 => 0x95200067f43d95200067e43d95200067d43d95200067c43d95202a67f72d95202ae7e72d95202a67d72d95202a67c72d95200067f42d95202ae7e42d95200067d42d95202ae7c42d95202ae7e32d95202ae7c32d95200067f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067e31d95200067c31d95202ae7f21d95200067e21d95202ae7c21d95202a67f70d95202a67e70d95202a67d70d95202a67c70d95202a67f40d95202a63f40d95202a67e40d95202a67d40d95202a63d40d95202a67c40d95202a67f30d95202a67e30d95202a67d30d95202a67c30d95202a67f20d95202a67e20d95202a67d20d95202a67c20d95202a67f10d95202a67e10d95202a67d10d95202a67c10d9520044fe76d8d200067f65d8d200067c65d8d20055be74d8d20005bd74d8d20004ff75d8d20024fe75d8d20004fd75d8d20024fc75d8d20004ff74d8d2001cfe74d8d20006be74d8d2001cbe74d8d20004fd74d8d20006bd74d8d20004bd74d8d2001cfc74d8d20006de43d8d20006dd43d8d2003cfe72d8d2003cfc72d8d20014fe71d8d20004fd71d8d20014fc71d8d200067f51d8d20006de31d8d20006dc31d8d2003cff70d8d2003cfd70d8d2016ebf40d8d2016ebd40d8d2016edf30d8d2016edd30d8d2016efa10d8d2005d7e7598d200057d7598d200067f6598d200067c6598d20055be7498d20005bd7498d20006df6398d2014ded7298d200057f7558d2005d7c7558d200067f6558d200067c6558d2018def7258d20004ff7558d200067f7558d200047f7558d20024fe7558d20004fd7558d20024fc7558d200067c7558d200247c7558d20004ff7458d2001cfe7458d20004fd7458d2001cfc7458d20006df7358d2018cff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d200067f5158d2014cff7058d20006fb7058d2014ebf4058d2014ebd4058d2014efa1058d2016cfe7618d200067f6518d200067c6518d20046de6318d20006dd6318d2000cfe76cc92000cfc76cc92005d7e75cc9200057d75cc9200067f65cc9201a67c65cc920055be74cc920005bd74cc920006df63cc920046dc63cc92000dfa70cc920005f970cc92012dee768c92003eee768c92003def758c92003f6e758c92029ded758c92003f6d758c9200056d758c9200076f658c9202976c658c92003fae748c92003fad748c92014ded738c920046ee638c920046ec638c920005ed718c9202976f518c92000dee708c92000dec708c92003eef608c92003feb608c92016faf408c92016fad408c92016fea108c920044ff764c92000cfe764c92014cfd764c92000cfc764c9200067f654c9201667c654c920006df634c920046dc634c92003fcc324c920005f
  | 5 => 0x5dd7348530007cd3248530004ff7558f20024fe7558f20004fd7558f20024fc7558f20004ff7458f2001cfe7458f20004fd7458f2001cfc7458f2003edf7358f2003cff7258f2000cfe7258f2003cfd7258f2000cfc7258f2003ede3258f2003edc3258f20004ff7158f20014fe7158f20014fc7158f200067f5158f2003eef2158f2014ebf4058f2014ebd4058f2014edf3058f2014edd3058f2003def764cb20006ef764cb202e5ef754cb202e5ed754cb2003fcf734cb2003fcf634cb20046ee634cb2003eec634cb2003fcc634cb2003ecc634cb20005ef714cb202df6f514cb2000dee704cb2000dec704cb2014faf404cb2014fad404cb2014fcf304cb2014fcd304cb20004ff7558720024fe7558720004fd7558720024fc7558720004ff7458720006bf7458720004bf745872001cfe7458720004fd745872001cfc7458720006bc745872001cbc7458720004ff7358720044fc735872000cfe7258720014fd725872000cfc725872003eee3258720006ed325872003ef771587200667f515872003ef7215872003ef421587200bebf40587200bebd405872003efa205872003ef920587200bef710587200067f76547202667e76547200067d76547202667c76547202667f64547201267e64547202d67d64547202667c64547202667f63547202767e63547200067d63547202667c63547202676e72547200076d725472011e7e62547202676e32547200076d325472026d7f71547200777771547200667f61547200167e61547200667d61547200167c61547200676f215472011e7d605472011f3f405472011f3d405472011f6e205472011f7a205472011f6c205472011f771054720044ff76cc72003cfe76cc720004fd76cc720046de63cc720006dd63cc72003dee72cc720005ed72cc720007cd32cc720004ff764c720004fd764c72003cfc764c720005bf744c72006dbc744c720046de634c720006dd634c72003dee724c720007cd324c72003def76487202ceef76487202c5ef75487202c5ed7548720007af74487202bfac744872003eef64487202beed6448720005ef7348720005ed734872003eef6348720006ed634872003fe7714872003fe76148720016ee6148720016ec614872003fe461487200676f51487200676d514872000dee704872000dec70487200bfaf40487200bfad40487200bfe710487202b57e76d952005e7e76d95200247e76d95200067f64d95200067e64d95200067d64d95200067c64d95202a76f72d95202a76c72d95200057d71d95200067e61d95200067c61d95202a73f40d95202a73d40d95202af7b20d95202a76e20d95202a76c20d95202a77820d95202a77a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d
  | 6 => 0xf724c930047cf724c930007cf624c93003ede624c93003edc624c930007cc624c93003ecc624c930005df714c93032f5f514c930007db704c93000dde704c93000ddc704c93014fd8704c930046df604c930047db604c93014f9f404c93014f9d404c93014fda104c930014fe76d853008d7c75d85300067f65d85300067c65d853007ef661d8530004ff75d85300067f75d8530024fe75d8530004fd75d8530024fc75d85300067c75d85300247c75d8530004ff74d853001cfe74d8530004fd74d853001cfc74d853000cfd73d8530014fc73d853003cfe72d8530004fd72d8530006df32d8530006dd32d853007e7f51d853007ef631d8530044fd70d8530106bf40d8530106bd40d8530106f710d85300057f755853008d7c75585300067f65585300067c6558530005bf7458530085bc7458530005ef7258530005ec725853007ef461585300067f76545300057e76545300067e76545300047e76545300067d76545300057c76545300067c76545300047c76545303267f64545301267e64545303267d64545301267c64545300075e73545300075d735453011e7f63545300067f62545302667c62545300075f32545300075d325453026d7f715453008f77715453007e7f61545300167e61545300167c615453011e7f605453011f3f405453011f3d40545302777b305453011f5e305453011f5c305453011f78305453011f77105453011f7a105453031dde76cc530046de76cc530045df75cc530315dd75cc5300075f65cc53030f5c65cc530306df64cc530306dd64cc530005dd72cc530006df62cc5300eddd71cc530016de61cc530016dc61cc53007f5f51cc53007f5d51cc530047db70cc53000dde70cc53000ddc70cc530047d870cc530046df60cc530047db60cc5301079f40cc5301079d40cc530107da10cc53000cfc764c5300067f654c5300fe7c654c530005bf744c530085bc744c530006f7614c530016f4614c530047d4314c530005fb704c53000df8704c530047d8304c53000ddc764c530016dc764c53000cdc764c5302fddf754c5302fddd754c5300075f654c5302f75c654c5300079f744c5302ef9c744c5302eedf644c5302eedd644c530005df724c530006df624c530045df714c530047d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007f5f514c53007f5d514c530007db704c53000dde704c53000ddc704c5300efd8704c530046df604c530047db604c5300ef9f404c5300ef9d404c5300efd7104c5300efda104c530004fe76c8530004fd76c853003cfc76c85300067f65c85300e67c65c8530045de73c8530005dd73c853003eee62c8530007cd32c8530004ff7648530004fe7648530004fc76485300067f65485300ce7c6548530005bf7448530085bc7448530045de7348530
  | 7 => 0x953008e7e76d95300247e76d95300067f64d95300067e64d95300067d64d95300067c64d953034f5f73d953034f5c73d95300057d71d95300067e61d95300067c61d953034f3f40d953034f3d40d95303577b30d953034f5e30d953034f5c30d953034f7830d953034f7a10d95300067f74d95300067e74d95300067d74d95300067c74d953034e7f73d95303567e73d953034e7d73d953034e7c73d95300067f43d95303567e43d95300067d43d95303567c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95303567f32d95303567c32d95300067f71d95300067e71d95300067d71d95300047d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95303567f31d95300067e31d95303567c31d95300067e21d95300067c21d953034e7f70d953034e7e70d953034e7d70d953034e7c70d953034e7f40d953034e3f40d953034e7e40d953034e7d40d953034e3d40d953034e7c40d953034e7f30d953034e7e30d953034e7d30d953034e7c30d953034e7f20d953034e7e20d953034e7d20d953034e7c20d953034e7f10d953034e7e10d953034e7d10d953034e7c10d953003cfe76d89300067f65d89300067c65d8930085be74d8930005bd74d8930004ff75d8930024fe75d8930004fd75d8930024fc75d8930004ff74d893001cfe74d8930006be74d893001cbe74d8930004fd74d8930006bd74d8930004bd74d893001cfc74d8930006ee42d8930006ed42d8930014fe71d8930004fd71d8930014fc71d89300067f51d8930006ee21d8930006ec21d8930044fd70d893018ebf40d893018ebd40d893018eef20d893018efa10d893008d7e75989300057d75989300067f65989300067c6598930085be7498930005bd7498930006ef62989300057f755893008d7c75589300067f65589300067c65589300067f65189300067c651893003eee6218930006ed621893012dde76cc930046de76cc930045df75cc9300475e75cc930345dd75cc9300475d75cc9300055d75cc9300075f65cc93033f5c65cc9300479e74cc9300479d74cc93003ede62cc93003edc62cc930005dd71cc93033f5f51cc93000dde70cc93000ddc70cc930046df60cc930047db60cc93018f9f40cc93018f9d40cc93018fda10cc93000cfe768c93008d7e758c9300057d758c9300067f658c9301867c658c930085be748c930005bd748c93014ddd738c930006ef628c93003eec628c93000dfa708c930005f9708c93000cfc764c9300067f654c9301667c654c930006ef624c93003eec624c930047cc324c930005fb704c93000df8704c93000ddc764c93003edc764c93000cdc764c930335df754c930335dd754c9300075f654c93032f5c654c930045d
  | 8 => 0xdfbb60c85400d7af20c85400d7ba10c8540005bf7648540006bf7648540004bf7648540005be7648540005bd7648540005bc7648540006bc7648540004bc76485403a5bf75485400b5be75485403a5bd75485400b5bc7548540005bf734854039dbe7348540005bd734854039dbc734854020dbf7248540007ae6248540007ad6248540007ae3248540007ad32485400d5bf71485400af3f51485400af3d5148540397b721485400afae21485400afac21485400afb421485400bdbf704854000dbe704854000dbc70485400bebf60485400c7bb60485400bfb710485400bfba1048540004ff7558b30024fe7558b30004fd7558b30024fc7558b30004ff7458b3001cfe7458b30004fd7458b3001cfc7458b3000cfc7358b30046ef7258b30046ef3258b30046ec3258b30004ff7158b30014fe7158b30014fc7158b300067f5158b30046df3158b3014ebf4058b3014ebd4058b3014eef2058b30045df764cb30006df764cb3038ddf754cb3038ddd754cb30047cf724cb30047cf624cb3003ede624cb3003edc624cb30047cc624cb30005df714cb303875f514cb3000dde704cb3000ddc704cb3014f9f404cb3014f9d404cb30004ff7558730024fe7558730004fd7558730024fc7558730004ff7458730006bf7458730004bf745873001cfe7458730004fd745873001cfc7458730006bc745873001cbc745873000cfe7358730014fd735873000cfc7358730004ff725873003cfc7258730046df3258730006dd3258730046f771587300967f5158730046f73158730046f431587300eebf40587300eebd4058730046fa3058730046f930587300eef710587300067f76547302767e76547300067d76547302767c76547302767f64547301267e645473037e7d64547302767c64547302775e73547300075d735473011e7e63547302667e62547300067d62547302775f32547300075d325473026d7f71547300a77771547300967f61547300167e61547300967d61547300167c61547300975f315473011e7d605473011f3f405473011f3d405473011f5e305473011f7a305473011f5c305473011f771054730045df764c730376df764c73036ddf754c73036ddd754c7300079f744c7303679c744c730046df644c730366dd644c730005df724c730006dd624c730047d7714c730047d7614c730016de614c730016dc614c730047d4614c7300975f514c7300975d514c73000dde704c73000ddc704c7300ef9f404c7300ef9d404c7300efd7104c73003cff76c8730044fe76c8730004fd76c8730045de73c8730005dd73c873003eee62c8730006ed62c8730007cd32c8730004ff7648730004fd7648730044fc7648730005bf744873009dbc7448730045de7348730005dd734873003eee6248730006ed6248730007cd324873035d7e76d
  | 9 => 0xb60d85403d7b710d85403d7ba10d85403d7b510d85403ddbf7658540005bf75585400b5be7558540005bd75585400b5bc7558540005bf735854039dbc7358540006bf6358540006bd6358540005bf7258540395bc7258540006bf6258540006bd62585403d5bf7158540007b761585400aebe61585400aebc61585400afb461585400af3f51585403c5bf7058540007bb70585403cdbb70585403c6bf605854002fbb60585403c7ba10585400073f76545400073e76545400073d76545400073c76545400073f73545400073e73545400073d73545400073c73545400073f63545400073e63545400073d63545400073c63545400073f72545400073e72545400073d72545400073c72545400073f62545400073e62545400073d62545400073c62545400073f32545400073e32545400073d32545400073c32545400af3f715454026d3f71545400b73771545400af3f61545400af3e61545400af3d61545400af3c61545400af3e31545400af3c31545400af3e21545400af3c215454011f3f705454011f3e705454011f3d705454011f3c705454011f3f605454011e3f60545401273b605454011f3e305454011f3c305454011f3e205454011f3c205454011f3f105454011f37105454011f3e105454011f3a105454011f3d105454011f3c105454039dbf76cc540005be76cc540005bd76cc54039dbc76cc54039dbf75cc5400b5be75cc5403bdbd75cc54039dbc75cc54031dbe73cc54039f9e63cc5400079d63cc540395be72cc540005bd72cc54039f9f32cc5400079d32cc5400edbd71cc5400af3f51cc5400af3d51cc5400af9e31cc5400afb631cc5400af9c31cc540105bf70cc54000dbe70cc540105bd70cc54000dbc70cc540106bf60cc54010fbb60cc5401079f30cc540107ba10cc540005bf764c540006bf764c540004bf764c540005be764c540005bd764c540005bc764c540006bc764c540004bc764c5403b5bf754c5400b5be754c5403b5bd754c5400b5bc754c54021dbf734c5400079e634c5400079d634c540005bf724c540395bc724c5400079f324c5400079d324c540105bf714c5400af3f514c5400af3d514c54039fb7314c5400af9e314c5400af9c314c5400afb4314c5400edbf704c54000dbe704c54000dbc704c5400eebf604c5400f7bb604c5400efb7104c5400efba104c540395bf76c8540005be76c8540005bd76c8540395bc76c8540395bf75c85400b5be75c85403adbd75c8540395bc75c8540395bf73c854039dbe73c8540005bd73c8540395bc73c854025dbe72c8540397ae62c8540007ad62c8540397ae32c8540007ad32c85400bdbd71c85400af3f51c85400af3d51c85400afae21c85400afb621c85400afac21c85400d5bf70c854000dbe70c85400d5bd70c854000dbc70c85400d6bf60c8540
  | 10 => 0x8940057bb6058940457ba105894044dbe7618940395bf75189400b5be75189403973e75189400b53e7518940005bd75189403973d75189400053d7518940395bc751894039dbe7318940005bd7318940006bf6318940006bd6318940445be7218940396bf6218940397ae6218940396bd6218940007ad6218940006ad62189400adbe7118940005bd71189400adbc7118940006be6118940006bc61189400073f511894001dbf701894000dbe701894001dbd701894000dbc7018940436bf601894043fbb6018940437af2018940437ad2018940437ba101894039dbf76cc940005be76cc94039ebe76cc940004be76cc940005bd76cc94039ebd76cc940004bd76cc94039dbc76cc94039dbf75cc9400b5be75cc94039f3e75cc9400b53e75cc94042dbd75cc94039f3d75cc9400053d75cc94039dbc75cc9400adbe71cc940005bd71cc9400adbc71cc9404273f51cc94018dbf70cc94000dbe70cc94018dbd70cc94000dbc70cc94018ebf60cc94019fbb60cc94018f9f30cc94018fba10cc940395bf768c940005be768c940396be768c940004be768c940005bd768c940396bd768c940004bd768c940395bc768c940395bf758c9400b5be758c9403973e758c9400b53e758c94041dbd758c9403973d758c9400053d758c940395bc758c94014dbd738c94012dbe728c9403979f328c94039faf328c9400adbe718c940005bd718c9400adbc718c9404173f518c94016dbf708c94000dbe708c94016dbd708c94000dbc708c94016ebf608c94017fbb608c94016faf208c94016fba108c940005bf764c940005be764c940005bd764c940005bc764c94040dbf754c9400b5be754c94040dbd754c9400b5bc754c94039faf324c9403979e324c940005bf714c9400adbe714c9400adbc714c9404073f514c94014dbf704c94000dbe704c94000dbc704c94014ebf604c94015fbb604c94014fba104c940395bf760c940005be760c940005bd760c940395bc760c940395bf750c9400b5be750c9403fdbd750c940395bc750c94018dbe730c94016dbe720c9403979f320c940397ae320c9403979d320c94039fad320c9400078d320c9400adbe710c940005bd710c9400adbc710c9403f73f510c94012dbf700c94000dbe700c94012fba700c94000dba700c94012dbd700c940397b9700c940005b9700c94000dbc700c94012ebf600c94013fbb600c94012fba100c9403edbe76d8540005bf75d85400b5be75d8540005bd75d85400b5bc75d854039dbe73d8540005bd73d8540006bf63d8540006bd63d8540395be72d8540005bd72d8540006bf62d8540006bd62d85403c5bd71d85400aebe61d85400afb661d85400aebc61d85400af3f51d854001dbf70d85403e7bb70d854000dbe70d854001dbd70d854000dbc70d85403d6bf60d85403e7b
  | 11 => 0x6bf6458121006bc6458121005df7358121005dc73581210bef86058121005bf75d8d400b5be75d8d40005bd75d8d400b5bc75d8d40006bf65d8d40006bd65d8d40395be72d8d40005bd72d8d400adbe71d8d40005bd71d8d400adbc71d8d400073f51d8d4001dbf70d8d4001dbd70d8d4047ebf60d8d4048fbb60d8d4047f9f30d8d4047f9d30d8d4047fba10d8d40485bd7698d4039dbf7598d400b5be7598d40005bd7598d4039dbc7598d40465be7398d4039ebf6398d400079f6398d40395be7298d40005bd7298d400adbe7198d40005bd7198d400adbc7198d40006be6198d40006bc6198d400073f5198d40475bd7098d4039fb97098d40085b97098d40476bf6098d4009fbb6098d40477ba1098d40005bf7558d400073f7558d400053f7558d400b5be7558d40005bd7558d400b5bc7558d400073c7558d400b53c7558d40006bf6558d40006bd6558d400079f6358d4039ebe6358d40005bf7258d40395bc7258d40005bf7158d400adbe7158d400adbc7158d400073f5158d40485bf7058d40007bb7058d4009dbb7058d40486bf6058d40087bb6058d40487ba1058d4047dbe7618d4039dbf7518d400b5be7518d4039f3e7518d400b53e7518d40005bd7518d4039f3d7518d400053d7518d4039dbc7518d40475be7318d4039ebf6318d4039f9e6318d4039ebd6318d400079d6318d400069d6318d40395be7218d40005bd7218d400adbe7118d40005bd7118d400adbc7118d40006be6118d40006bc6118d400073f5118d4001dbf7018d4000dbe7018d4001dbd7018d4000dbc7018d40466bf6018d4046fbb6018d404679f3018d404679d3018d40467ba1018d40005bf75d89400b5be75d8940005bd75d89400b5bc75d8940006bf65d8940006bd65d894039dbe73d8940005bd73d8940006be63d8940006bc63d89400adbe71d8940005bd71d89400adbc71d89400073f51d894001dbf70d894001dbd70d894044ebf60d894045fbb60d894044faf20d894044fad20d894044fba10d8940455bd7698940395bf75989400b5be7598940005bd7598940395bc759894039dbe7398940005bd7398940006bf6398940006bd6398940435be7298940396bf6298940007af62989400adbe7198940005bd71989400adbc7198940006be6198940006bc61989400073f5198940445bd7098940397b97098940055b97098940446bf609894006fbb6098940447ba1098940005bf75589400073f75589400053f75589400b5be7558940005bd75589400b5bc75589400073c75589400b53c7558940006bf6558940006bd6558940005bf735894039dbc7358940006be6358940006bc6358940007af6258940396be6258940005bf71589400adbe71589400adbc71589400073f5158940455bf7058940007bb705894006dbb7058940456bf605
  | 12 => 0xd75d8d210067d75d8d210047d75d8d21024fc75d8d21004ff74d8d2101cfe74d8d21004fd74d8d2101cfc74d8d21006de53d8d21006dd53d8d2103cff71d8d2103cfd71d8d211767f51d8d211767d51d8d21176df31d8d21176dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006bf40d8d21006de30d8d21006dc30d8d21176f710d8d210cd7e7598d210057d7598d210c5be7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d21155ed7298d21005bf7458d210c5bc7458d21006bf6458d21006bc6458d21195ef7258d21004ff7558d21024fe7558d21004fd7558d21024fc7558d21004ff7458d21006bf7458d21004bf7458d2101cfe7458d21004fd7458d2101cfc7458d21006bc7458d2101cbc7458d21006df7358d21194ff7258d21006ef7258d21154ff7158d21006f77158d211567f5158d211567d5158d21004ff7058d2100cfe7058d2100cfc7058d21006bf4058d21156f71058d21174fe7618d21006bf6418d21006bc6418d21046de6318d21006dd6318d21014fe76cc921014fc76cc9210cd7e75cc9210057d75cc9210c5be74cc921005bd74cc921006bf64cc92119ebc64cc921006df63cc921046dc63cc921015f671cc921005f571cc921135ee768c92103eee768c92103f6e758c92103f6d758c92103def748c92103fae748c9214aded748c92103fad748c921005ad748c921007af648c9214a7ac648c921155ed738c921046ee638c921046ec638c921015ee718c921015ec718c92103eef618c92103fe7618c9211776f518c9211776d518c921005ed708c9214a7af408c921177e7108c921044ff764c921014fe764c921154fd764c921014fc764c921006bf644c92115ebc644c921006df634c921046dc634c92103fcc324c921005f7714c921015f4714c921015ec764c921046ec764c921014ec764c92149def744c92149ded744c921007af644c921497ac644c92103def734c92103fcf734c921007cf634c921046ee634c921046ec634c921007cc634c921046cc634c921007e7714c921015ee714c921015ec714c921157e4714c92103eef614c92103fe7614c9211576f514c9211576d514c921157cf314c921157cd314c921005ef704c921497af404c921157e7104c92100cfe76d81210c5bc74d8121006bf64d8121006bc64d81210befa60d8121004ff75d8121024fe75d8121004fd75d8121024fc75d8121004ff74d8121006bf74d812101cfe74d8121004fd74d812101cfc74d8121006bc74d812101cbc74d8121044fe73d8121004fd73d8121014fd72d812100cfc72d8121006ee32d8121006ed32d812103cfd71d812100cfc71d81210667f51d81210667d51d81210bebf40d81210befa20d81210befa10d81210057f75581210cd7c7558121005bf74581210c5bc7458121
  | 13 => 0x8131006dd32d8131044fd71d81310967f51d81310967d51d81310eebf40d81310eefa30d81310eefa10d81310057f75581310fd7c7558131005bf74581310f5bc7458131006bf6458131006bc6458131005ef7258131005ec72581310eef86058131004ff7558f21024fe7558f21004fd7558f21024fc7558f21004ff7458f2101cfe7458f21004fd7458f2101cfc7458f2103edf7358f21014fe7258f21014fc7258f2103ede3258f2103edc3258f211567f5158f211567d5158f21156df3158f21156dd3158f21004ff7058f2100cfe7058f2100cfc7058f21006bf4058f2103eef2058f2103def764cb21006ef764cb214d5ef744cb214d5ed744cb2103fcf734cb2103fcf634cb21046ee634cb2103eec634cb2103fcc634cb2103ecc634cb21015ee714cb21015ec714cb211576f514cb211576d514cb21157cf314cb21157cd314cb21005ef704cb214cfaf404cb21004ff75583210067f75583210047f7558321024fe7558321004fd7558321024fc75583210067c75583210247c7558321004ff745832101cfe7458321004fd745832101cfc7458321004ff7358321044fc7358321014fe725832100cfd7258321014fc725832103eee3258321006ed325832104e7f515832104e7d515832103ef6215832103ef5215832103efb70583210d6bf405832103efb205832103ef820583210d6fa10583214c5be76d91210c6be76d912101cbe76d9121006bf65d9121006be65d9121006bd65d9121006bc65d91214b7af72d91214b7ac72d91214b73f51d91214b73d51d91214bfb721d91214b7ae21d91214b7ac21d91214b7b421d9121005bd70d9121006be60d9121006bc60d91214b7b710d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d91214b6bf72d91214bebe72d91214b6bd72d91214b6bc72d9121006bf52d91214bebe52d9121006bd52d91214bebc52d91214bebe32d91214bebc32d91214b6bf71d91214b6be71d91214b6bd71d91214b6bc71d91214b6bf51d91214b63f51d91214b6be51d91214b6bd51d91214b63d51d91214b6bc51d91214b6bf31d91214b6be31d91214b6bd31d91214b6bc31d91214b6bf21d91214b6be21d91214b6bd21d91214b6bc21d9121006bf70d9121006be70d9121006bd70d9121004bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d9121006be30d9121006bc30d91214bebf20d9121006be20d91214bebc20d91214b6bf10d91214b6be10d91214b6bd10d91214b6bc10d9121044fe76d8d210cd7e75d8d210057d75d8d21006bf64d8d21006bc64d8d21004ff75d8d21024fe75d8d210067e75d8d210247e75d8d21004f
  | 14 => 0x506bf32d9131506bc32d91314febf71d91314febe71d91314febd71d91314febc71d91314febf51d91314fe3f51d91314febe51d91314febd51d91314fe3d51d91314febc51d91314febf31d91314febe31d91314febd31d91314febc31d91314febf21d91314febe21d91314febd21d91314febc21d9131006bf70d9131006be70d9131006bd70d9131004bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d9131506bf30d9131006be30d9131506bc30d9131006be20d9131006bc20d91314febf10d91314febe10d91314febd10d91314febc10d913103cfe76d89310fd7e75d89310057d75d8931006bf64d8931006bc64d8931004ff75d8931024fe75d89310067e75d89310247e75d8931004fd75d89310067d75d89310047d75d8931024fc75d8931004ff74d893101cfe74d8931004fd74d893101cfc74d8931006ee52d8931006ed52d8931044fd71d89311967f51d89311967d51d8931196ef21d893100cfe70d8931004fd70d893100cfc70d8931006bf40d8931006ee20d8931006ec20d8931196f710d89310fd7e75989310057d75989310f5be7498931005bd7498931006bf6498931006bc6498931006ef6298931005bf74589310f5bc7458931006bf6458931006bc6458931006bf6418931006bc641893103eee6218931006ed6218931135de76cc931046de76cc9310475e75cc9310475d75cc931045df74cc9310479e74cc9314f5dd74cc9310479d74cc9310059d74cc9310079f64cc9314ef9c64cc93103ede62cc93103edc62cc931015de71cc931015dc71cc931046df61cc931047d761cc9311975f51cc9311975d51cc931005dd70cc9314ef9f40cc931197d710cc931014fe768c9310fd7e758c9310057d758c9310f5be748c931005bd748c931006bf648c93117ebc648c931155dd738c931006ef628c93103eec628c931015f6718c931005f5718c931014fc764c931006bf644c93115ebc644c931006ef624c93103eec624c931047cc324c931005f7714c931015f4714c931015dc764c93103edc764c931014dc764c9314e5df744c9314e5dd744c9310079f644c9314df9c644c931045df724c931047cf724c931007cf624c93103ede624c93103edc624c931007cc624c93103ecc624c931007d7714c931015de714c931015dc714c931157d4714c931046df614c931047d7614c9311575f514c9311575d514c931005df704c9314df9f404c931157d7104c93100cfe76d81310f5bc74d8131006bf64d8131006bc64d81310eefa60d8131004ff75d8131024fe75d8131004fd75d8131024fc75d8131004ff74d8131006bf74d813101cfe74d8131004fd74d813101cfc74d8131006bc74d813101cbc74d8131014fd73d813100cfc73d813103cfe72d8131004fd72d8131006df32d
  | 15 => 0xd320c9511357f710c9510157e710c95113776710c95101576710c9511357d710c95126775710c95100575710c9510157c710c9511367f610c95114777610c95111d7e700c9510057d700c95111d7c700c9515473f400c95113777100c95111d7e76d81510057f74d81511257e74d81510057d74d81511257c74d81512757e73d81510057d73d81510067f63d81510067d63d81512657e72d81510057d72d81510067f62d81510067d62d81510257f71d815153f7771d81510157e71d81510257d71d81510157c71d81515367f61d815153f7761d815111d7d70d815111e7e60d815111f7a60d815111e7c60d815111f3f40d815111f7710d815111f7a10d81515377910d815111d7f76581510057f74581511257e74581510057d74581511257c74581510057f73581512757c73581510067f63581510067d63581510057f72581512657c72581510067f62581510067d62581515257f715815100777715815152d7771581515267f615815103777615815111d7f70581510077b605815111e7e605815111e7c605815111f78605815111f3f405815111f771058151004ff7558b31024fe7558b31004fd7558b31024fc7558b31004ff7458b3101cfe7458b31004fd7458b3101cfc7458b31014fc7358b31046ef7258b31046ef3258b31046ec3258b311567f5158b311567d5158b31156ef2158b31004ff7058b3100cfe7058b3100cfc7058b31006bf4058b31046df3058b31045df764cb31006df764cb3151ddf744cb3151ddd744cb31047cf724cb31047cf624cb3103ede624cb3103edc624cb31047cc624cb31015de714cb31015dc714cb311575f514cb311575d514cb31005df704cb315179f404cb31004ff75583310067f75583310047f7558331024fe7558331004fd7558331024fc75583310067c75583310247c7558331004ff745833101cfe7458331004fd745833101cfc7458331014fe735833100cfd7358331014fc7358331004ff725833103cfc7258331046df3258331006dd325833107e7f515833107e7d5158331046f63158331046f53158331046fb7058331106bf4058331046fb3058331046f83058331106fa105833150dbe76d91310f6be76d913101cbe76d9131006bf65d9131006be65d9131006bd65d9131006bc65d91314ff9f73d91314ff9c73d91314ff3f51d91314ff3d51d9131507b731d91314ff9e31d91314ff9c31d91314ffb431d9131005bd70d9131006be60d9131006bc60d91314ffb710d9131006bf75d9131006be75d9131006bd75d9131006bc75d91314febf73d9131506be73d91314febd73d91314febc73d9131006bf53d9131506be53d9131006bd53d9131506bc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bd52d9131006bc52d9131
  | 16 => 0x89510067f63989510067d63989515857e72989512667f62989510076f62989515957d71989512677571989510cd7571989515967f61989510e777619895111d7e70989510057d709895111d7c70989510067e60989510067c60989510073f40989515977710989510057f74589510073f74589510053f74589511257e74589510057d74589511257c74589510073c74589511253c74589510067f64589510067d64589510057f73589512757c73589510067e63589510067c63589510076f62589512667e62589515a57f71589510077771589510e57771589515a67f61589510cf7761589510057f705895111d7e705895111d7c70589510073f40589515a777105895159d7e76189512657f74189511257e74189512673e74189511253e74189510057d74189512673d74189510053d74189512657c74189512757e73189510057d73189510067f63189510067d63189515957e72189512667f62189512676e62189512667d62189510076d62189510257f71189510157e71189510257d71189510157c71189515867f611895158f7761189515876f21189515876d211895111d7e70189510057d701895111d7c70189510067e60189510067c60189510073f40189515877710189512757f76cc9510057e76cc9512767e76cc9510047e76cc9510057d76cc9512767d76cc9510047d76cc9512757c76cc9512757f74cc9511257e74cc9512773e74cc9511253e74cc95157d7d74cc9512773d74cc9510053d74cc9512757c74cc9511957f71cc9510157e71cc9511957d71cc9510157c71cc9511967f61cc9511a77761cc9511975f31cc95111d7e70cc9510057d70cc95111d7c70cc9515773f40cc9511977710cc9512657f768c9510057e768c9512667e768c9510047e768c9510057d768c9512667d768c9510047d768c9512657c768c9512657f748c9511257e748c9512673e748c9511253e748c95156d7d748c9512673d748c9510053d748c9512657c748c9511557d738c9511357e728c9512675f328c9512776f328c9511757f718c9510157e718c9511757d718c9510157c718c9511767f618c95118777618c9511776f218c95111d7e708c9510057d708c95111d7c708c9515673f408c95117777108c9510057f764c9510057e764c9510057d764c9510057c764c95155d7f744c9511257e744c95155d7d744c9511257c744c9512776f324c9512675e324c9511557f714c9510157e714c9510157c714c9511567f614c95116777614c9510057f704c95111d7e704c95111d7c704c9515573f404c95115777104c9512657f760c9510057e760c9510057d760c9512657c760c9512657f740c9511257e740c95154d7d740c9512657c740c9511957e730c9511757e720c9512675f320c9512676e320c9512675d320c9512776d320c9510074
  | 17 => 0x1367f5158432136f65158432006f55158432136f64158432006f54158432046f73158432046f4315843203ef7215843203ef42158432004ff705843200cfe705843200cfc7058432006bf4058432136f71058432004ff75580320067f75580320047f7558032024fe7558032004fd7558032024fc75580320067c75580320247c7558032004ff745803201cfe7458032004fd745803201cfc745803203edf325803203eee325803203edd3258032046ed3258032006cd3258032004ff7158032014fe7158032014fc71580320067f515803203cff705803203efb705803212efa5058032006f9505803212ebf405803212efa4058032006f94058032046fb3058032046f8305803203efb205803203ef8205803212efa10580320057f74d8d511257e74d8d510057d74d8d511257c74d8d510067f64d8d510067d64d8d512657e72d8d510057d72d8d510257f71d8d510257d71d8d515ce7f61d8d515df7761d8d515cf5f31d8d515cf5d31d8d5111d7e70d8d510057d70d8d5111d7c70d8d510073f40d8d515cf7710d8d515d57d7698d512757f7498d511257e7498d510057d7498d512757c7498d515b57e7398d512767f6398d510075f6398d512657e7298d510057d7298d515c57d7198d51277757198d510fd757198d515c67f6198d51117776198d5111d7e7098d510057d7098d5111d7c7098d510067e6098d510067c6098d510073f4098d515c7771098d510057f7458d510073f7458d510053f7458d511257e7458d510057d7458d511257c7458d510073c7458d511253c7458d510067f6458d510067d6458d510075f6358d512767e6358d510057f7258d512657c7258d515d57f7158d51007777158d51115777158d515d67f6158d510ff776158d510057f7058d5111d7e7058d5111d7c7058d510073f4058d515d7771058d515cd7e7618d512757f7418d511257e7418d512773e7418d511253e7418d510057d7418d512773d7418d510053d7418d512757c7418d515c57e7318d512767f6318d512775e6318d512767d6318d510075d6318d512657e7218d510057d7218d510257f7118d510157e7118d510257d7118d510157c7118d515b67f6118d515bf776118d515b75f3118d515b75d3118d5111d7e7018d510057d7018d5111d7c7018d510067e6018d510067c6018d510073f4018d515b7771018d510057f74d89511257e74d89510057d74d89511257c74d89510067f64d89510067d64d89512757e73d89510057d73d89510067e63d89510067c63d89510257f71d89510257d71d895159e7f61d89515af7761d895159f6f21d895159f6d21d895111d7e70d89510057d70d895111d7c70d89510073f40d895159f7710d89515a57d76989512657f74989511257e74989510057d74989512657c74989512757e73989510057d739
  | 18 => 0xe75586320247e7558632004fd75586320067d7558632024fc7558632004ff745863201cfe7458632004fd745863201cfc745863203cfc725863203edf325863203edd325863203ef771586321767f5158632176f6315863203ef7215863203ef42158632004ff705863200cfe705863200cfc7058632006bf405863203eef2058632176f71058632004ff7558232024fe7558232004fd7558232024fc7558232004ff745823201cfe7458232006be745823201cbe7458232004fd7458232006bd745823201cfc745823203cfc725823203edf325823203edd3258232004ff7158232014fe7158232014fc71582320067f515823203eef215823203efb705823216ebf405823216efa305823203efb205823203ef8205823216efa1058232014fe76d8532156f661d8532004ff75d8532024fe75d8532004fd75d8532024fc75d8532004ff74d853201cfe74d8532004fd74d853201cfc74d853203cfd73d8532044fd72d85321567f51d8532156f631d8532156f621d853200cfe70d8532004fd70d853200cfc70d8532006bf40d8532005bf745853215dbc7458532156f4615853200cfe76d813214efa60d8132004ff75d8132024fe75d8132004fd75d8132024fc75d8132004ff74d813201cfe74d8132004fd74d813201cfc74d813203cfd73d8132044fd72d8132014fe71d8132004fd71d8132014fc71d81320067f51d813214ebf40d813214efa30d813214efa20d81320057f75581321657c755813214ef8605813203fcf764c83203dcf764c832006cf764c83260fcf754c8325ffce754c83260fcd754c8325ffcc754c83203fcf654c83203fce654c83203fcd654c83203fcc654c832607cf744c8325f7ce744c832607cd744c8325f7cc744c83203fcf644c83203fce644c83203fcd644c83203fcc644c8325f7cf544c8325f7ce544c8325f7cd544c8325f7cc544c832007cf714c8325efce714c832007cd714c8325efcc714c83203fcf614c83203fce614c83203fcd614c83203fcc614c8325ffcf514c8325ff4f514c8325efce514c8325ffcd514c8325efcc514c8325f7cf414c8325efce414c8325f7cd414c8325efcc414c832007cf704c8325e7ce704c832007cd704c8325e7cc704c83203fcf604c83203fce604c83203fcd604c83203fcc604c8325ffcf504c8325e7ce504c8325ffcd504c8325e7cc504c8325f7cf404c8325f78f404c8325e7ce404c8325f7cd404c8325e7cc404c8325efcf104c8325e7ce104c8325e7cc104c832004ff7558432024fe7558432004fd7558432024fc7558432004ff7458432006bf7458432004bf745843201cfe7458432004fd745843201cfc7458432006bc745843201cbc745843203edf325843203eee325843203edd3258432046ed3258432006cd325843203cff715843203ef77158432
  | 19 => 0x87320067e75587320247e7558732004fd75587320067d7558732024fc7558732004ff745873201cfe7458732004fd745873201cfc745873203cfc7358732046ee3258732046ed3258732046f771587321967f5158732046f73158732046f43158732196f62158732004ff705873200cfe705873200cfc7058732006bf4058732046df3058732196f71058732004ff7558332024fe7558332004fd7558332024fc7558332004ff745833201cfe7458332006be745833201cbe7458332004fd7458332006bd745833201cfc745833203cfc7358332046ee3258332046ed3258332004ff7158332014fe7158332014fc71583320067f5158332046df3158332046fb705833218ebf4058332046fb3058332046f8305833218efa205833218efa10583320067f74596320067e74596320067d74596320067c74596321867f735963261e7e73596320067d735963261e7c73596320067f435963261e7e43596320067d435963261e7c435963203e7f725963203e7e725963203e7d725963203e7c725963203e7f425963203e7e425963203e7d425963203e7c425963203e7f325963203e7e325963203e7d325963203e7c32596320067f71596320047f71596320067e71596320067d71596320067c71596320067f41596320067e41596320067d41596320067c415963261e7f31596320067e315963261e7c315963203e7f215963203e7e215963203e7d215963203e7c21596320067f70596320067e70596320067d70596320067c70596320067f40596320063f40596320067e40596320067d40596320067c405963261e7f30596320067e305963261e7c305963203e7f205963203e6f205963203e7e205963203e7d205963203e7c20596320067f10596320067e10596320067c1059632006bf7559232006be7559232006bd7559232006bc755923217ebf7359232616be7359232006bd7359232616bc7359232006bf5359232616be5359232006bd5359232616bc535923203ebf725923203ebe725923203ebd725923203ebc725923203ebf525923203ebe525923203ebd525923203ebc525923203ebf325923203ebe325923203ebd325923203ebc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf51592320063f5159232006be5159232006bd5159232006bc5159232616bf3159232006be3159232616bc315923203ebf215923203eaf215923203ebe215923203ebd215923203ebc2159232006bf7059232004bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232006bc5059232616bf3059232006be3059232616bc305923203ebf205923203ebe205923203ebd205923203ebc2059232006bf1059232006be1059232006bc1059232004ff7558632024fe75586320067
  | 20 => 0x1001005400c0070008008002003001000400400400180100020010000000010002001000000c001003800c010000000802400c00200000100020050020004000000007800800c0020000000000001002002001c0000018028000005000803c002001001800000c015000000c00c00f002800400200a01c0054002001003000000200000a80080020010088024006007001801c00000500000200040080018010000003000000400002300280200020010000024000006000001c00201600380000020030000040014001002800003e007000000002a00a005000001e000000001c00600000e801002e000000001c0140000038004008003000800009202f004000000c000004801000a000009801c01a004000800c00e000005800001e00d00200080000050067f74597320067e74597320067d74597320067c74597320467f73597320467e73597320467d73597320467c73597320467f43597320467e43597320467d43597320467c43597321a67f725973262e7e72597320067d725973262e7c72597320067f425973262e7e42597320067d425973262e7c42597320467f32597320467e32597320467d32597320467c32597320067f71597320047f71597320067e71597320067d71597320067c71597320067f41597320067e41597320067d41597320067c41597320467f31597320467e31597320467d31597320467c315973262e7f21597320067e215973262e7c21597320067f70597320067e70597320067d70597320067c70597320067f40597320063f40597320067e40597320067d40597320067c40597320467f30597320465f30597320467e30597320467d30597320467c305973262e7f20597320067e205973262e7c20597320067f10597320067e10597320067c1059732006bf7559332006be7559332006bd7559332006bc7559332046bf7359332046be7359332046bd7359332046bc7359332046bf5359332046be5359332046bd5359332046bc535933219ebf7259332626be7259332006bd7259332626bc7259332006bf5259332626be5259332006bd5259332626bc5259332046bf3259332046be3259332046bd3259332046bc3259332006bf7159332006be7159332006bd7159332006bc7159332006bf51593320063f5159332006be5159332006bd5159332006bc5159332046bf31593320469f3159332046be3159332046bd3159332046bc3159332626bf2159332006be2159332626bc2159332006bf7059332004bf7059332006be7059332006bd7059332006bc7059332006bf5059332006be5059332006bd5059332006bc5059332046bf3059332046be3059332046bd3059332046bc3059332626bf2059332006be2059332626bc2059332006bf1059332006be1059332006bc1059332004ff7558732024fe755
  | 21 => 0x1200b0000000000003005800000000200600000000120028000000001001000c00800a006001000200a0000004016005005000000201100000080020000020004002001009801800600e002800001400200a0000002000001802000000000e800000e0060018008012003000000400800f000001c000004000803800c0000008028004003004000000c00400000000120070008000004000000000800400800080200020030010000004007000000401a003000000800c0020008000000002001801801600401180240080010000014004004000800400400c00500140060060028008004001001002000c007007000000a01f00780200040130010004000000000000000002a000002801c00a000002800c000002000c02600000200040000110008018000012000800000000100000000000000010044004000001801800801700000000220010000000002008000001800200000680000020010070004004012000001400c00b001803000e002008007400c004007000400a00c003001801c007000001400200000f0004002005000001400a000000802800c0320008074000008003000402a0000018008024000002007800800100080200140010000000000000001003c00a0010000000024005000005c0000030000004016011003800400200100a0000000003000002000600600000000020010018000000000000800002200a00e8000004002002000c00a040001801c002001002800000200a00c0094004001000000400c000000804800600c00180300080000000004006005001000c00000600000300020030000018004000000000001e005003004c006000000005401c0000010008006010002802c01a00500600000040060000010008000002801c0000060050004000002000804c00000b00500080000000068028002000002000c00000d000000400c00e001802800200e00000440020000000014018000001000000000501d0000000011000804000200800b8008000009003802800800f0018000000005003800000000200d800801800200080000000000010010000004000801c004008001800000200c001000000000000780080100010020000062005002800400000c000000000000b00600040000000000000000001000800002a00b015806c000000009000000000600180300180090010008002000001005400400300080000020050008004004001001003c00000000000080080000008004002009001800c000000005800400c005000002400c004001800400000000000040160020008000018009000000801c005005000401c00000e8034000004000800c00000d001002c00800c00100000080010018048032003001001c0040000440004002001000000000000f000800c000004000001c01a000000800c000
  | 22 => 0x56c200000000008fe0001768a7000000019e0824000b5b35518a8160000144000033e0002280e8c000af11dc8fe800036e0000001804000000000000000000000003140004fe8000000ccc5ad0000000000319000023a7810588000000a2b04ca2a5438beb16e8a38c60d0b30f837c01e8e16b383642c811146521ccdf27db00026ad3a6bc321900a410c0003fa80009420005fe00005e06624a22268ed062148d2b00d9ea1813f2540a7088967582fc00000041f9b4ca8ed2552236200008fe3b8800000000043a86a99beac10cead24b0ad502f28be5b5e4595bd0000000bf32319e4c72259904d86c95be13204405207da0070052089b46ce210f1ab50628db195a23c3fe2b629e1b05218db552cb11528e08d632a9b52ee92e01e89a8a58bf733ca77473c3f05dca620168d7000004380008f200017651886ce11701e98dc40d00016a442832c0002a000788023ac0f4d68009a1a02c0042e2ff45d872135a58c40b0ea8bd8b1f1fe863c7481a65cd0c45adc60d5fb08652c42d2335b0d539acd148e00d4206d4c4bf0480d0a95f24c31e536acad216a31d1a851863a2cb959646820114fc5fa0e7116800a004000001402e009000806c0000020060020008006000000000000000900080000110408020046008000003c000011001000001c0000000064002001005001400c0040000004000000003005800001a0018028006000002000000800e00000400060110028014000004000000002e004006000c01000a000002401600100100040040000028034008003000000000a00300c8004018000002000c0000030008004010010000801801c0000038000004000004001000200600280240000000010008006004008002c018003000001000e00400000100000000018000006010000800000a0030008008008009003800000000100400dc010001000000402c0030030000002000000800000e008003802801a000000006c0040000010000014001000803c004002000003c002001001800405c00000080480020000008000000004002000800600100200480160120000010000016006000801000100000080020000008058004001001000000200900600600020000020014024001001000400000a000002c00000a001804c00a00a000000c00000c0020038004002001002400400100180000000010010054012008001800800c020000000c000005000000800c00b003005001200100000540000000028000002001000001400c001002000000a0190008020004000000002c01c00800300000280000008010022005001000400000300000040000030018018002005000002404400800680000040000038024000006000801800400000680540020040108034010005000804801202900280000000010010010000015000000000200e001
  | 23 => 0x320d5da00018f9bb800040f0eb0e80fbe1ac43f99c90408b81592af8d7800033f00011724706302c1476600000002f40000003bb8000d109b03beaacdb8e53e37830ad770000359b4e98a675f55b909000000000018100000004892538296a8600000013425801a28a651f4000000000032e0002402074c34d494518ef0606a5000012ac99828459a203d9ce48123718000ea4e668385c9a8e0004e196dd5688ec698000196a65d0000001a2e0000000ad09f01e20762e9400012800010a077ad2c000264c00092544180001088c12d59eb80007d900014d00003660000cc40001735b98001b180005448000328b6300c8000000000522abe54d20000000c946e88e9000268c1ccca15c9955d6d8523000298d8e4c210869fc805ec0901634d862eb13249851081c000000352d24651c31a8b04ba6bb00002308cb07220001d810148482e79e18e6a17940016c0ee07c513d07700000e05841d790a20001b9b220daa550063ad9c0003d9256a8e10de92400003e916c00000035b0000990000131d4e60001bd800000036200035dc4da0003a609900000005f0119c3764cf5a6b3bcf7a4ae6078001a46a7a1a680000283615e425600003e90000000000db70000000d0e30d596b12800096500000000004ee5192c450f8bcf39b1fa497073849682b1a3466e6c9b5805547ff000000000000049a1dbdac600036600007c2834148800024402d5c380018026bf00000000005f160b85611b8bc7392238871c9b838f98156fa0001499e70bb40000000000eb20001f8800000034422f023c00033d0000424e342f660a03ccac01d065d329040425d00000014ba00000000017400000000008e7607865882600009a60b5800000000062d0fec00089900bb400d1800038a9f3833800028c80000000001c980000004d50000d5c5cc96e10d224c00035e34c800172c0000001bbc000b764662498b2a000000000123665544521380002bc0000af4e84d7a33600006de17b59988e59ec8125218b852e281a63519a8fd0cf35c68000bd60000210000ad00000003231278000260a7bdb160b510625448b842a40aac80000d8d3ba244426caa556e9da51ec85a4c60958d5846662ba09999e0512258000176b654bb2dfc00000010d8b207de4f613188ad2328ea1400000000b6919d0d947ecbf9000094d7e8d2606bacaca4eac45dba10451e4c53aeac793ca9e21a58f4809080e6658f1c00000007e135c00000034dac880000000003091012db426700013080000000000000b9237d98b8dbc97033880013a22f2336941519014a3eeb5655b01531b830ed0d8a98122b6e4d3caa86181620e1c0006dfb33802222000000e800030c46f0711510c0b29500000000000000000b1400000000000004ec0000c8098c07b0000000a809c41ae8000a96dc600020b
  | 24 => 0x64b00002a400000053b8000cca7c23ed00000000001ab0418a0881316188c40940c244588ec000000000000155800000000003dab2967414b40004ea0002d2d6049e30000f9973c26945888545d65095a702d8534ad3052a4192a492c000260d52ac0332004b106ca2d2eb08cc0565cb5ffabf51ee000613893582cbc4000083957a78909399fc14041b62eb41567ccc20000fa8ae60003b735a504e0005868000eb6000000000055a634174000120863345f32108669d71d3836c5767bc6a5057024ad316ba13d172098514b266811231308983e5a6a6c7089000105400000d20648f2bbb41708a88626f357d00000000a4000088c0000ed6cd8000af8a9d0f2359943e4520238d4cf5e87e000080000000008f8000000c314dd0001a7c351000000090edbb382a57000000039700dc000da223f35480006e3000000000097507f000130eb6d00023ec0000003f9aa440000000001e2c38cd7100013ad98a9c503f9dfc8eaa253a78238d50b2162c2e284e8a4e08401bc03e0001539ea42c6a6b00021618380005aa800166000022eaaf0000000180246193e0000000001b6400039e000000090f65f1d2188c64a00000000000004d700008749200ec35949185d44b49ca46980005021b75aa6a1d61928697c69315d71eb047c4306e635cc41e2fc1c2b359502a2e2cb000139e00000000000000001f918880000000001f856de00000000001701fd3680c713545e81faa3946d00004dd88340004b36be000000034a56193080000cf00000002ee7e40002d0c85800022c0000ca400062a22cc56a5e665a123825c4b53ba980400041404080000005286819f5d47e000000000073a3784fa8f193ee56329d27a4b062b70001bb0000b075f30000e3a6f40000288ca03d74cc32b0da251d4ec922097ecc108c91c4a82a490a8ad7c3369fb387a9f11be3a209a8b4cdb626f1da02a102ed55309858424670961a00000008af0000ca8f3c2e300ab50c000af711c339510a9f300005d59a858f000216586c7ef1531d2c9080002e4ac980003df316800147c00010980008f600062480000000004d3800051a000272a270a525bb0000b80e3619222417c80001ae0b70138000d0e00000012ba61e4b5116d5c000045d28a01d20000a333000000000000b44630a5a27daed0cc02945bba208f86525389859439200018927d8cc2c4b41badd16c097b1d3000159284a1ac9d7119c3100742aa542a5f65350cd87362875b9181d79cab104e0b587fc7474c12e0134a94550ca624fbca2a03098f833218e3859ba12269555338a08088201000000180c00056424514a27d41748b648d6ad967b8c9ce9a6e931c1ef8652caa0000899b9a4a9151878cc740ae45611510800000db95d889a7a42d08eb40e600061ea17c00000000032fc99a4640000000c2c00
  | 25 => 0x851991ac18986c61c12d5c78282919700000d200900006899664a50000cd4000ca84c0b2380005df1dfad180d66f2000000056647d00000000000000e3af04f9469f5f78bb861e405262240599000058ea2315c2ad50002210716cbd0002e70dbec950000000ab85de55b2578acc86013a82e8000a1e00035ec00072f45f89d8af4289031b5e4b9061c3fe9b94b162ac60910d9648d5760299f089ea5b629225cefcb3814c179100eb514d015c13f2c71000215190c00005cb6a15d26862bf80000000001d58000ad896f30cb47c91a668000000000011b164ae6cb7c7b009a322cc84c93425a8813a847c000000000092740fb6f4e0c00002095e1960d2d3e60ea0eecbf2476968d96450e080ace449e3d457a899594c3c015d23b98309b337588bc4428211ada7a8b80a075388f3523c052642800000019100000017320000000000cbeacc0002fc5414c596848000b1a262000000183a3eb00012d8fe08a20000e653b62ea3cea1b800000000015f40000000001ac5664d0d37c30f09e498e3ccb3a4e140013ad00000006120003035b54000151129c36683b00000000000004c01a700000005baa65800064e0db3608776b7b11830cc00000024780000005e70001c8126a708508310c000a6e1930000a04b660001a8000000032b80007a2000000000086a00033980000009bc20892800009fe6913484d2072b4cc9950000000000000109200015c800000000000000000000003f30e5c0989da3d3a8ec36854e0000f7434200053c00000006391338b8916e00018700014fc9072019860aaa00065100000002d500000000007d300035fd472cae092000000000050a000000014900000015401f42f4b5f5b9c0001a30731b328060001dec7f2c3e06e0000420a4600000000004bc0002c10422000518a6b00000002ac97180b661068ab0fd702b1a6b0816157448a1bf8001a30d8e2ed811400074e0000078e024344330000000a52087b6c0ab413149536690068921dd04094f676513905a4b783e051e8df47d0908264a4ed0d2d4d227000033c4693489d01af012f6e5aa48816a032ff110c1d600066b93b59ba05460ab04000088134b33900000766dd189d8e63ce3d29d145beb092c0b2ed7509480ab000032a5ff2fba8f06d68e3000000000033e1360cbc1889590000000000a270000000000a3a0000000c46bba24800017660805e50000d707fb2dcad75a1eadc0000001b4e00049f830d0285620000000f1a17f34d2f149582b82fdac388e664f29d8164fe88d63a808d8380bcc0ad21a0b48cc600003484d648259a9428000d280002a69a3801d61c945800076700000000000680000000e6600000000018f0000000000000000008e0000994000000000050616d4c880016500000001cd05eaa99000232d4000001d900003fc4e75c280
  | 26 => 0x164a23d50d89c4e3c54426580009f87c40b40e841ac2a9290ae8c00005c388999cdee5c400000018e0cde03ea4281920000000870b385c238b00b8000000113800078400000000000002af346800185ac62484a134ee4aaa6cc167c9a60ee0002340b240003aa8001a105c300009fc00044400008214840002da8000f7e4420dc15246329b960434d028e6280d8aa30000bed20e98955ac5fd0001a3c8342600000298d022063f52108000a410b000015c87566792d3c77000415400015e4c11509000100a00012380407005f31680000928abf563a8cd53c55100024e192299268880004900000a7b3e06664d60000f20f060004b00174000000436aa7000015e2888668be8c7600006e40000000002e6141a830000000192494c00000002e8d643c118392c89534a10d913c2921486a558f9e4612021a08e62c2c0f61100a24ac639636586b82356cba950a4c97c4628031b382cf1fbabb007c6b735295354bccfc4978001b200224c3225908e1d912f17a8580905000180c00028c5c201e400069565c0a9060abb20f7096559408329704b55d06ba00018a40000005b225240004bd532829c35aa2c20f0094bf20e26289d4868200058795c80000000002b6d9f48880000000960a8e152a29c0006c80000b080006a35d3947cc048242c88259516c8d0001a74fce41c66c9db429a00003f1d0d8aa1985df9aa57c25ad29b223938080400031412063e500000000000004390000a667d1033ada8000000060b0643f897a1ed2f5048429061c1e59a706201778000000000478036087a2db0e5097db3eced4cda43863659d69fb53cd2e624671b1d592c68461d2d88ae25ed3e58640e086924e516c9aea79500000001de20b00000002d4000242a0601c2c0a67085140005a700000002aa5b64f31c94f920000000018000c266ca328cc0c9eb5ec2d1d91440100000018b85ac332000093cc9a48004005c88552c700017f00000ac8000000d461bba3bd68a7f14e704e4000b8f11a0f2567489d23b800039a8f501da9d000000060030a88449391aa8be959c90217880000008624143380b9878731f8fb0000352623926cc58b8227402cc0006082d8abad9b80000fc17f013e17044f8e3d5147884351b5000000060fa5c9b828ae32980009c000057328bc07e1d2257aa35aec2504ce93f476accd5f42a10f9a91d50980000000650371eec286cda00029805d816c5ed8000dcc7274b9800000051300000010d60035d1104c000c770000000d8a1c54e62ca885e38658e061c7ac0004e0960883033b4d894bd0b8a5c0003094000aaf4e8146800000009518ac000aef000316c2704be00017e00001ea0000001164749400b624fc418400036b0cf46e20a11714de29f80490fb925005e5ac23248f43b00688244db800064c84fd3502f36c2000109e0
  | 27 => 0x9f23860034a860005af125571665c4eaa19c0003021baa500cf01dd000049800096150b0000b9495725902411ba00024d107c786d0a056800072a0e30de000178c0000002279ada9683fd150800063d0f5a39c94c6b942203d17e02ce3fc0894282b956e434916f0cff072af791e67c763780000002864858745a663d03058bd173e3af21c15dcf0a34809b99c11fe5dd2d50000dda71c1a7a56cc12000000221c0000000beb44c2308774231c0c00029b3b30000a2e8d96cf2c8d4fa0000003158f74dae0000c2c07035400023980003b6475ae0c0426ae6c00cdc82a7185e90de589ccc45fd9218a169ee46d11b0000b4c08229d88cab15432acf47b857b0000000a98bd000029586021df6d58754f1e1e856a29e4fc656a1c38000c3a4760000000ef28e84488000788c640000601a0200039fae8517a546370824dabaca053200000367ec39d12e8e20cb63fca14146a82b08a0fe002400009e0000000cb900032250c81a7000000133ed5e0000bed22a6ca0188001058be563f802c000a870002ef1256646000000000000000000015fe85611d17480000006db31987e89361bf04e800053d19f858800098d0000000b8e4166c901f0b680003cd8a2d31443b58800013e0ad256d35f8be0478421892c0000001c934ada2c000204073d03c3720000000000c1b0000000b2e00018a8001016da40000c8831a7736952f59364a750000f6d6ac000000140c000b311c609550100ea0f31b115ceafc1148904fee0000000001ad4c6159f9788f2811e00028a41e287a5e89abc8e4cf118300000004e153fb13522e0002ab2ff8dc0a010001489546b1713c000000097f000000084cbdc0280d4160c7c800026d0ed40000000d38000cfe13b8f600003be261936c8246174469705b8a6d768303d971c38a00019a493251e1cf961cafc05f18f00003de2684f0108cf622d82798970e320625fd00a8f564da000370d9b60005f70000f400403cd137932ed10443000168400000000000000002d0000154c00039cb0a0000000000096cffc12b58cb25d6b289567e89f54aa00021ba7b400001632415d460e8fc00027e8c86b376402e9050289033eb27195e0002543294d6a11038681d11ae0006e52b8800087b5aa06911e284c6a084cc40abfd47e800000052018ea7fcfa08d1606158468468b34182f96027a66df2f24a0010c2c996f4a627e00001bf800000049837009ba00063f0000ed845f120233d0c21d32bc8000000000391800000000006580014805353b0a7b000000000036f17180002f0080d5d49c2579962404c42030a8320d80d5f3e906bd28c25a3dc2dc46280006ab022c0382ca00000001aa02738387d54cc9e746699dc1780de6c193d40000006348000000000000000000015b54b80000002d40f3acb0dec1ce0000
  | 28 => 0x80019e0bb62d10001544778000000138c0000000944198a700002a084c200000009181184215a507802e200000000c816e2cd000363c0000000000000d7c0332778000000000000014c00083800009b8000d2f6408000000000000262c346c8766500012e80000002b78c921c327c9ed00000000002d20000000000191d33878c2e8b71155610a1c6a20064214e000307897633818b00006f80f22060000000cf9000184400000000000000000000001d2800021f45331b4b742ab4542c580004ff663a7d0c182660003698e0424e3e00000980c981cb29b00008941c080011481546a100000000000000be01e0c9046908119dc89835931119d800000000000000001d299d482e53900000017d28c33c9000061427307aa7203e093363da9305ce9d226c890db525376648c2400023f3a2013400000017baa58dce01800010249a072d627a52822a6984bc9b09ab00aa54a070806896b0c99cdc312c9e30a1ad8c784f032c811813abd93a32f9d3be9de0deaa0c686244571920db4000006320d40006f551b96798d8d4e669157cf50d9d5ce80008aa44606a22a85bcb7c32d85f884abb5000000000003000987c8ef80722a40d7c2168104699e115ae82501200006c0564617041c0004df47a1114356d9143a14c97800643bd1f5527a6d92170000a0c0000000001b0c0001920458814a5833b23e151ed814e4800055c68e6c3813da6e69364e96bc8b4af800029346601964c783383e2cf50a00a5c0002371428000a60ac25f12e241800b200000000000000fd000000000040619151c80000002f7540a0004aa159400000015882accb4cea1b62bb8f2e3cf3d10000000ac560380008d4ab56b787843b68b51f9b0100000000001d904f600000000010362fe16201b0b204e409d834132a2181a3a3e43bc0d31db8328000c2f2512c0c64667415000004f2abb5f521d8a9e73e26e3340000304351151400064457f21754d00000000001624baf2c20c68c6e9dc0001440ff87a3000000000082f55c80019f6000295a8980000006100c202f07d60ed0284000c4214f24891b0270090b474e24ca71f38000ea200045a000000000004a00012ccab0165a4412f0689163a534b3018232b272d542b503691d50abc96c2032dac09623c5b70001490a470c59e2822eafb631a83c8da5a500007ed8820002b68db5b2a4d43c006188781ba00007510f038807b8b184500000000000aa8b140000414000000501282097200000035ac0d40002f1975da049160001bfc4ae1be2d300017d8594000000000000041ea1c174c000318a6901bad855ae3120c985ae2ec26d95a0ae51b394349f400000025f400050f3ec000000a0005299668d92aae0000eb00000000a901240000000001a00d7a00055c020942e0000000001442bd363422c0000c13248a71cbea
  | 29 => 0xa283ae52fa84544451b24921c48561d731d9d890a49bf452911c498b5345583352964600f29ad02ce07148f80003962a10f9b70800000849f0ce586e9af0fca18cb66ab25bc86044646da22b32f10fa00062f0254832ce6620326cb0c7326070b68e82b970f4b4ecd4ca2341e12914de22457a101d9e87536821dad784a09549b4f1140c5f1e29979ac4552328a0e81c859b05780000000003450000000000380000118c1a9000109cadc000000308c00000000000000000000002ab5328726000323cbdc43e6860e611424895fa8000a0287914e92d107cbab2310000a0ec290af8b5c2f80000000155a88a244d119340009fc320800027a62f6d6b30c4f8a06000138daa2db3456a53c000b0c66c2c9c5606ea2f7b2087bca9b0a82f5c0001f7411af55460bda27f046925200016e0ea4000000051800096e22c1e627c44a84101c192c4000bad2f09f9437e0000d81fb96142c540880009c45741292ea4cc6a9f23a00012c60000000888ab6000000000000079f4b3abd86ec636000226d8f400e58c1bf4ccc00024e069400000039500000006e4000114c00035842282780000000002bc10a6d45172b5a036a000000182800000019690fc000bcb59e0000000db828616e000000000000019a600000000009167ed38a30899aa5081c48d240b44e93da8621b1405641c9d8c000a4b3db20c8d287984f40cd027c8d5499010c2ec9e406d1b60e7a3ca0000000d76b52000369442ca615c31129a9000026c00003823ff2e8346cf548bc65b96fc12e6a7094a6dc00044c527882977c9432b480002f4da14eb1f057c83842b7910595260f2e710a51c06cb0d000e5aa86a403300012b40001ca3464aba56b6991ee4762a0c000000031840069e9e406f449d000128c0002071cd1a8473800064a2c2caa60002248ff000002052baec48aebdf5c41d5cdf44c814f8000000a904a093c46c666f0002e517540000001898000000000125cdacc7d3dba0ccd9a00002b8a5435078e4069eb49ee46f000000141c35a000000168806024fab4546cb9100029290bc81c3ee021d26ed2768a08758d615d6ae09286e215726912592749bd59794558ce0ff4df186d59a2495b404c0cf6d1e15f35c9b622923fb008d6365dc4d48f88ace524655b481834aa459d80002de000228800000085b0003500000d126e4800000000053128d09540001f20000000a0b00015607c60005b834a465003603810e52da0c53d92d04e2e08a1e58000d8673037e1754f22721000000179a36a1450e400da4d10002cd80000000b30615a5c07739434e4f665a85392761758bbd2fd26780000f863e2b3d1803690c18960000a851091aac0000fd3e3215ca943d55bf000154e14c0fb00000000000000000fd6000000356c57e7a12e6b5680502cc07d
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf33325454044001e6464a8a8088003cc4c9515011000798192a2a022000db3874c540440017650e98a8088002ec21d3150110006d843a62a022001bb2864c540440037610c98a8088346ece15315011068dd8c2a62a022043bb3834c5404402bf270698a8088003e49cd3150110007c8b9a62a022000f93634c54044001f20c698a8088002ece093150110007c999262a022000f91324c54044001b670e90a8088002eca1d2150110005d843a42a022000db08748540440037650c90a8088006ec2192150110685d9c2a42a0220d0bb18548540440017670690a8088002ec60d215011020dd9c1242a022015fa3824854044001f44e490a8088003e85c92150110007d1b1242a022000fa0624854044001f446490a8088003e84c921501103563c3b6ea9822000b598518d30440017930431a60880026e613724c110006f110ee49822000b5985cc930440017a30399260880035ce1d514c110005b943aa29822000b70875453044001ae10ea8a608800b5c9d9514c110016b83b2a298220cfd7374545304419fae2e8a8a6088003d4a0d514c110007a8c1aa29822023d73735453044047ea6e6a8a6088003d4d8d514c110007a831aa29822000d73725453044001ea664a8a6088003d44c9514c11000d78432629822002cf0764c53044011da0c698a6088006f421d314c110016e843a629822001bd2864c530440037a10c98a6088023b4219314c11004769bb2629822002dd2764c53044005ba0ec98a6088023b41d9314c110675e9c2a6298220cebd1854c53044001ea6ea98a6088337d41d5314c110007c9c226298220ccf90844c53044197ba6e898a608832f745d1314c110005e9c12629822000dd3724c530440017a30690a6088003f04c9214c1102ae3c3b6ea90220009b984dcd2044001ba463b9a408800a3e2197348110005b4c28c49022000bc98318920440016d30b1924088002f86063248110006b9c3aa29022000b728754520440016e10ea8a40880035c21d5148110016b93b2a29022002d70765452044195ae6e8a8a408832b5c5d15148110006b9b9aa29022000d71735452044001ec504a8a4088003d8609514811011eb9b92a29022023f63725452044001ec6c4a8a4088003d81895148110007b1192a29022000f61325452044001ba2e698a4088003f04c9314811000d78432429022002cf076485204400fdc0c490a4088006f821d2148110016f043a429022001be28648520440037c10c90a408801fb8219214811003f71bb2429022002de2764852044005bc0ec90a408801fb81d9214811064df1c2a4290220c9be1854852044001ec6ea90a4088323d81d52148110007d1c224290220c7fa084485204418dbc6e890a408831b785d12148110005f1c1a429022000be1834852044001bc6e690a4088003785cd2148110
  | 1 => 0x90cb9a4288002e96106248510005e2c18c490a2000ba5848c921440017c3011924288056ec20773501100ad5d434e6a022000ab9869cd4044027970ed39a8088056eca067350110005d8c0ce6a022000abb865cd404402b5710cb9a8088002cee1573501101cd9c42ae6a022000bb3815cd404402b76102b9a80882372e1d873501101cd9d428e6a022000b39851cd4044001b32e639a8088056eca047350110005d8c08e6a02201dbb18198d40440013770eb1a80880166e21d63501100059dc2ac6a022039b388558d404400175704b1a8088002ea2096350110105d9c0ac6a0220d39ba8718d404402b3730e31a80880e6cea1463501100059cc28c6a022000e996318d40440017550431a8088002ea60863501100add840ee4a022015aba869c940440015730d39280880372e1da72501100add940ce4a022000bb1819c940440015770cb928088056ae21972501100059dc2ae4a022039b38855c9404400176702b928088056ec205725011043e5c3b0e4a022039b3a851c940440016730a39280880036a5c872501100add9408e4a022000bb1811c9404402f7630331280880026ee1d625011002cdc43ac4a022000b3b8558940440736710ab128088002e6e0d6250110005cc41ac4a02201abb38158940441a53750e31280880566e61c62501101cd9d428c4a022000b39851894044001735063128088002e660c625011000754b10c4a0220009ba87cc940440013730f99280880e6cea1732501100059cc2e64a022015bb281cc940440017630399280880026ea1e3250110004dcc3c64a022039b3a858c940440016730b1928088056eca063250110005d8c0c64a022015bb2814c940440015750c1928088002ae6183250110007c499064a022015bb2810c940440017630219280881f6eca1f71501100aed943ee2a022001bb286dc540440037610db8a80880576c9db71501100aed83b6e2a022000bb385dc540440017630bb8a8088002ec60f7150110006d9b9ee2a022000db173dc5404400176305b8a80880036cdcb7150110006d8b96e2a022000f33875454044001e650ea8a8088003cc61d51501100079843aa2a022039f33865454044047e650ca8a808808fcc619515011011f98432a2a02203ff3376545404402be64eca8a8088057cc5d951501100af983b2a2a022000f33835454044001e6506a8a8088003cc60d51501100079841aa2a022000f33735454044001e64e6a8a8088003cc5cd51501100079839aa2a022000f33635454044001e64c6a8a8088003cc58d51501100079831aa2a022000f33825454044001e6504a8a8088003cc609515011000798412a2a022000f33725454044001e64e4a8a8088003cc5c9515011000798392a2a022000f33625454044001e64c4a8a8088003cc589515011000798312a2a022000
  | 2 => 0xd628c91000c7a432e319220028f8865c232440010ff0abb264880121f215764c9100045fc22ec99220038bc845d932440011bf06bb264880023be09764c9100243f428ec992200087d851d9324400717d083b264880022f610764c91003c6e43ac69922007acc8258d32440111d90eb126488022b320d624c9100043fc2aec192200487c855d8324400117f08bb0648800e2f211760c9100446e41aec19220078ec825d832440011bb0fb1864880023b61f620c91000567432641922000acc864c8324400f99eec9906488003335d9320c91000c7a432e21922000dc5325c432440051f10cb806488003724c9700c91011db8406e6a8a2023a76869cd51440014eb0d39aa28808b1d1da735451011db9404e6a8a2000b71809cd51440014ef0cb9aa28808e9d21973545100059bc22e6a8a203fb34845cd51440016e700b9aa28808edc20173545105be3a3b0e6a8a203fb36841cd514400166b0839aa28808edca007354510005b8c00e6a8a200fb718098d51440012ef0eb1aa28801a5d21d63545100059bc22c6a8a203fb348458d51440016cf04b1aa288002d92096354510095b9c02c6a8a20d59768718d51440472eb0e31aa2880fecda1063545100059ac20c6a8a2000e556318d51440016cd0431aa288002d9608635451011db8406e4a8a2023a76869c951440014eb0d392a2880731d1da725451011db9404e4a8a2000b71809c951440014ef0cb92a28808e9d21972545100059bc22e4a8a203fb34845c951440016e700b92a28808edc201725451058e3a3b0e4a8a203fb36841c9514400166b08392a28808edca007254510005b8c00e4a8a2009b718098951440012ef0eb12a28801a5d21d62545100059bc22c4a8a203fb348458951440016af06b12a288002d520d6254510065b9c02c4a8a20d49768718951440472eb0e312a2880fecda1062545100059ac20c4a8a2000b568318951440016ab06312a288003995886254510004bb43e64a8a200097587cc9514407f66d09992a288002cd613325451011db940664a8a2000b7180cc951440012ed0f192a2880025d61e32545101fd9b42464a8a2000b35848c951440476e501192a288002dc602325451011db940264a8a2000a76860c951440014eb0c192a288003d14c8325451011db940064a8a2000b71800c951440476e50fb82a28808f5ca1f7054510015b9436e0a8a2002b7086dc15144047ae4edb82a28808f5c1db7054510005b9c26e0a8a2000b7184dc151440016e307b82a2880035cdcf7054510006b8b9ee0a8a2000b7182dc15144001ae6e5b82a2880035c5cb70545105065a3b6e898a2000b958418d314400178b0431a62880025d617724c510006f1106e498a2000b9584cc931440017a301992628825f2d1db7448510004bac2ee690a2000dd230dcd21440031e
  | 3 => 0x6a8a4000a3d84d8d51480010ff0eb1aa2900021f21d6354520006363b4e4a8a4047b65819c951480474d90cb92a29012ad9e057254520004b6c3c64a8a4023a6c864c9514809dc98c6992a29000e2fa1276cc5200045ec24ed98a40028de839db31480010ff0abb662900121f21576cc5200046fc3ac798a40018ec865cb3148011998ec99662900121fa17764c5200043ec2eec98a40038be849d9314800117b093b262900030f1d3654c5200061fb2ee898a4000c3c65dd131480051b90eb1a6290003331d9324c52000556c26c790a40008ef8758f2148001878e9b2a42901579908765485200061fb2ee890a4000c3c65dd1214812fb5041ba242901531b1db65485200073230eca90a4096cac76dd12148001b50e1ba242900025b617734852000c76432e690a4000aad84d8d21480051d90eb1a42900021fe1572d8d100243e42ae5b1a20008bf845cb634400717908b96c6880121fa1f7558d100043fc0eeab1a200087d81dd5634400187e81baac6880030f5037558d100045fc22eab1a20038bc845d563440011df04baac68801e3b2097558d100043f438eab1a20038be87dd1634400187eebba2c6880030f1d77458d100061fa8ee8b1a2000c3d51dd1634400117f01ba2c6880022f6037458d100043fc2ae8b1a200487c855d163440011df04ba2c68801e3b2097458d100045f438e8b1a2000c3f751d16344001878ea3a2c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031bd477258d1000636a8ee4b1a2000caf40dc9634400195a81b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100046fc3ac631a2000acc8258c634401199cc6b90c6880033358d7218d100043fc2ae7b12200487c855cf624400117f08b9ec48800e2f21173d89100243f43eeab12200087f81dd562440010fb03baac4880030fd0375589100061ea06eab1220008bf845d5624400717908baac48800237e0d75589100446e41aeab12200087e871d5624400717d0fba2c4880030fdd774589100061e3aee8b122000c3f51dd1624400187aa3ba2c4880022fe0374589100045ec06e8b12200087f855d162440090f90aba2c48800237e0d74589100446e41ae8b1220008be871d1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fa8ee6b122000c5d51dcd624400193e81b9ac4880032750373589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100066639ee4b1220018fa87dc1624400f99cc4b98c4880023be1d62189100056641ac43122000ccd73588624400f1bd073b6648801eb320963cc91000c7a432e399220028f8865c3324400f1dd053b46488022b320
  | 4 => 0x54800187908b8eca900030fd0171d95200061ea02e3b2a4000a3e841c7654800147b0838eca9000297a0c71d95200052ec18e3b2a4055a6e821c765480a94db0438eca901529ea0071d95202ad3cc00e3b2a400087e8790765480010fb0f20eca900021fa1c41d95200043ec3883b2a4000a5e8310765480014bb0620eca901569ba0841d952000536c1083b2a4054a7a8010765480014f30020eca900021fa1e31d95200043ec3c63b2a400087e870c765480010fb0e18eca900028fa1031d95200051ec2063b2a4055a6e820c765480014db0418eca901529ea0031d95200053cc0063b2a405487e8788765480010fb0f10eca900030f9d365d8d200061f3a0cbb1a4000c3f655d36348001878caba6c69000e2fa1375d8d200045ec26ebb1a40008bd879d3634800717f0eba6c69035e2fe0174d8d203945ec02e9b1a4000cba105d3634800793ce921ec69000e37e1d43d8d206b61f3a6a3b1a4000c3d74d47634800153b0818ec690002b360831d8d200056cc0063b1a4000c3e74d96634800187ce832cc6900030fd957498d200061e32ae931a4008c9c635d2634800193ae9b1cc6900021fa1f6558d200043f438cab1a400487e87dd563480010fb03baac6900030fd037558d200061ea06eab1a400087e871d563480010ff0aba2c6900121f2157458d200047bc0ae8b1a40028f4815d163480010fd0fa8ac6900121f21f5158d202b636b90ca31a40008df8758c63480ad0f90cbae64901521fe1f65cc9200043ec3ecb9924000c3e74d97324800187ecaba664900030f19574cc9200464e31ae99924000c9d74d8f32480a72d90cbac64900025be05758c92003e37b02eb1924007d6b605d63248001a5e80bac64900034b501758c920006b5082eb192400096f87d9632480abc9865b2a649001eb3a0b634c9202a6363b6ca9924008ace86d8d3248001c9eca31a649000393194634c9200053ac0eebb0a4000a75811d761480010ff0aba6c2900121f21574d85200043fc2ae7b0a400487c855cf61480090fd0dbaac2901521f21b75585200043f43ecab0a4000c3c74d9561480010fd0e32ac2900030f1d065585200061fb2ee8b0a4000c3c65dd161480018becbb9ac2900031719773585200062fb28e6b0a4000c5c651cd61480010fd0d3b2a2900029d60676545200063ac0ceca8a4000c3f409d9514800187a813b2a2900031dc4276545200051fc22eca8a4024a3c845d951480014bf06bb2a29013a9720d76545200053bc0aeca8a4024a3e841d9514800147b083b2a2900030fa1076545200061ec20eca8a4000c6d821d951480090ff023b2a2900121f604765452000637908eca8a4000c6d211d9514800187e803b2a2900030f50076545200063b880eca8a4000c7a101d951480018ea203b2a2900031e44076545201251f426c
  | 5 => 0x80030fd95748c9300061e32ae91926007cac625d2324c00195ae9b1464981ab930cb654c93034e2e3b6ca9926007ace86d89324c001c9eca312649800393194624c9300053ac0eebb0a6000a75811d7614c0010ff0aba6c2980121f21574d85300043fc2ae5b0a600487c855cb614c0090fd0dbaac2981a61f21b75585300043f43ecab0a6000c3c74d95614c0010fd0e32ac2980030f1d065585300061fb2ee8b0a6000c3c65dd1614c0018decbb92c2980031b197725853000637b28e4b0a6000c6c651c9614c0010fd0d3b2a2980029d60676545300063ac0ceca8a6000c3f409d9514c00187a813b2a2980031dc4276545300051fc22eca8a6024a3c845d9514c0014df04bb2a2981329b20976545300053bc0aeca8a6024a3e841d9514c00147b083b2a2980030fa1076545300061ec20eca8a6000c5d831d9514c0090ff023b2a2980121f60476545300062f988eca8a6000c5d311d9514c00187e803b2a2980030f50076545300063b880eca8a6000c7a101d9514c0018ea203b2a2980031e44076545300062e3b4e6a8a605fb55819cd514c0474b90cb9aa29818ad5e0573545301251f426c4a8a6000a3d84d89514c0012bb0f992a29808e9721932545302672631264a8a6000a9d84d8b314c001878e9b2a62981ab950c7654c5300061fb2ee898a6000c3c65dd1314c141b3061ba262981a7171db654c5300072a30eca98a609fc9c76dd1314c001b30e1ba2629800257617724c5300054ec26c498a60038be849db214c00117b093b6429800a3ba0a76c85300043fc2aed90a600487c855db214c0031b90cb9e429801f331d932c85300243f42eec90a600087d85dd9214c00717d093b242980022f61276485300061e3a6ca90a6000c3f65dd1214c001878cbba24298006372197348530006663b26490a6007ace83dd932c800117f08baac39000e2f211755872001c5f43ee8b0e4000c3f51dd161c800187aa3ba2c39025e2fa1c74587200055cc00e8b0e400487e85dcd61c80010fb0bb9ac390023331cd325872011d37416eca8e404cc6e72dd951c800147f08bb2a3900928f21176547200053bc0aeca8e40d8b67815c951c8099c98c6992a3900121fa17764c7200043ec2eec98e40018ee82dd931c800117f08bb2639000e2f211764c7200146e43ac698e4007ccc764c931c80012db0bb9a43900023be1973487200043ec3cc9b2a4000a5e8399365480014bb07326ca900021fe1d64d952005c3ec38c3b2a4000a3e84187654800147b0830eca9000297a0c61d95200052ec18c3b2a4000c7571187654800187ae83a6ca900028fa1373d95200051ec26e7b2a4000a3e849cf654800147b0939eca901569ba0873d95202a536c10e7b2a400087e8710f65480010fb0e21eca900028fe1171d95200051e422e3b2a4000c3f845c76
  | 6 => 0x1c5ec00ec90a8000caf201d9215000195a403b242a00032dc4076485400065d080ec90a8000cb5101d92150001972203b242a005a4fa1773485400049ec2ee690a80008bf865cd21500011790cb9a42a00032b1da624854022dd4c04c490a80159ac875892150001958ecb1242a015eeae01624854000556c346490a80159ac874c921500e7b18e699242a00022fe11755873001c5e422eab0e60038be87dd161cc00187ea3ba2c3980030f54774587305045f438e8b0e6000ab9801d161cc0090fd0bb92c3980021f617725873003e6639264b0e6023a5e83dd951cc09d8bce7bb2a3980028fe1176547301251e422eca8e6000a77815d951cc1b56af02b9aa39800257617724c7300243f42eec90e600087d85dd921cc0031bd07bb243980022fe11764873001c5e422ec90e60008df865cd21cc0051d90eb124398023331d932487300043ec3cc9b2a6000a6e82993654c0014db05326ca980021fe1d64d953008c3ec38c3b2a6000a3e84187654c00147b0830eca980029ba0861d953000536c10c3b2a6000c7571187654c00187ae83a6ca980028fa1372d95300051ec26e5b2a6000a3e849cb654c00147b09396ca981aa97a0c72d953034d2ec18e5b2a600087e8710b654c0010fb0e216ca980028fe1171d95300051e422e3b2a6000c3f845c7654c00187908b8eca980030fd0171d95300061ea02e3b2a6000a3e841c7654c00147b0838eca981aa97a0c71d953034d2ec18e3b2a6000a6e821c7654c0014db0438eca981a69ea0071d95303553cc00e3b2a600087e87907654c0010fb0f20eca980021fa1c41d95300043ec3883b2a606aa5e83107654c0014bb0620eca980029ba0841d953000536c1083b2a6069a7a80107654c0014f30020eca981a61fa1e31d95300043ec3c63b2a600087e87887654c0010fb0f10eca980021fa1c21d95300043ec3843b2a6000a3e84087654c00147b0810eca981aa97a0c21d95300052ec1843b2a6069a7a80087654c0014f30010eca980030f9d365d89300061f3a0cbb126000c3f655d3624c001878caba6c49800e2fa1375d89300045ec26ebb1260008bd879d3624c00717f0eba6c4983662fe0174d893039c5ec02e9b126000cba105d3624c00795ce9216c49800e3be1d42d89306b61f3a6a3b126000c3d74d47624c00155b0810ec498002b360c21d893000574c0043b126000c3e74d96624c00187ce832cc4980030fd9574989300061e32ae93126007cac625d2624c00195ae9b14c4980021fa1f65589300043f438cab12606bc5d73194624c0011df0eb10c4981a25721975cc930004afc0aeb9926008c5f605d7324c011ab6c0bae649800347d0175cc9300068ea02eb9926000d5a105d7324c0012bf0fb2e64981ae1f219758c93034c3fc3ecb192600087d87d96324c00187ce9b2c649
  | 7 => 0xb8805cf615002b17b0fb1ec2a00022fe1d63d85400049fc2ae5b0a801693c855cb615001b37700b96c2a00066e20172d85400ac5ec3ec5b0a80008bf8758b615000133f06baac2a01ce6720d7558540004d7c12eab0a80729ac825d5615000137700baac2a00022fa1f63585400ac5e43ac6b0a8073c9c7358d615000117d0fb12c2a00562f21d625854039656392c4b0a80019ba87dc161501bbb66e3b82c2a0002ce60376545400061fbb4eca8a8000b35819d9515000163f06bb2a2a0002c720d765454000597c12eca8a8000b2c825d9515000166f02bb2a2a0002cee0176545400061ebb0eca8a8076b35819cd515000147f0cb9aa2a00028f21973545403bd9bc0ae6a8a8000a3e861cd515000147b0c39aa2a0192ce60263545400049fc3ac6a8a800093c8758d51500df67700b1aa2a00024fa1c63545400049ec38c6a8a8000e1d6318d51500e966b03392a2a00028fe1972545400051e432e4a8a8075b37815c9515000147d0c392a2a00028f618725454027d9cc04c4a8a800093f8758951500012790eb12a2a016acee0162545400049f438c4a8a800093d871895150001c5ac4312a2a00024fa1f32545400049ec3e64a8a8000a3e86cc9515000147b0d992a2a00024fa1e32545400049ec3c64a8a8000a3e868c9515000147b0d192a2a0003c34c832545400ad9b40864a8a8000b35810c9515004767500192a2a0002ce60032545400accf41ced98a800093f855db315002d2790abb662a00026ee0176cc54039e4e3b2c798a80dcb9b8058f315000137301bb262a00030fd47764c5400061ea8eec98a8000cb980dd9315000197421bb262a00022fa1a764c5400049fc2aec98a801693c855d9315000135f04bb262a01ca6b209764c540004ddc02ec98a801693e851d9315000127b0a3b262a00030fa14764c5400061ec28ec98a8000c9d831d9315000187ea23b262a00030f544764c54001c5fc00ec98a80038bd801d9315000193e603b262a0003274c0764c5400065b880ec98a8000cba101d9315000196a203b262a00032e440764c5400064e3b4c698a805db998098d315002b3390eb1a62a0003271d9634c540365cdc02c698a801693e85dc9315000127b0bb9262a0002a761b324c5400acce43a6498a8072d8c724c9315002b35d053b642a00024fe1576c85400b49e42aed90a80009bb805db21500e5958ecb1642a036eeae0162c8540396c639a6590a80009b980dd9215000187ea3bb242a00030f54776485400065cc06ec90a8000cba10dd9215000117d0d3b242a00024fe1576485400b49e42aec90a800099f835d921500e733906bb242a00026ee0176485400b49f428ec90a800093d851d9215000187d0a3b242a00030f614764854000656c10ec90a8000c3f511d9215000187aa23b242a000e2fe0076485400
  | 8 => 0xab9ec4a005a4f21573d89403945ec38c7b128000a3d8518f625000193ae631ec4a01cf279cd639894072ed4b86c53128000a9d83186625000155b0430cc4a03934e5c351989400b49f43eeab12800093d81dd5625000187ec1baac4a00034ed8375589400069d086eab1280009bb805d5625000127d0e3aac4a005b0f1d765589403945e43acab128072aac8259562500e555d0531ac4a00022fa1c63589400051ec28c6b128072aae86d89625000337101b8ac4a00024fa1f51589400b49e43ea2b1280e3d3b70d456250001a76ebb82c4a00034e1d77058940716d5b96e0b128072c3f625d462500e587ac4ba8c4a00024fe0575189406be1fb02ea3128000d3b605d462500e5a5e40ba8c4a00034b48175189400069d082ea31280738bd87d8c625000187aebb18c4a0002ab60b63189400045fc3ac63128000c3d7558c625000135f0eb10c4a0386eae01621894039557c3ac43128000caf875886250001c5f0ab10c4a00038b2156218940397173aac43128072e2d7558862501af55f00b10c4a0003aae01621894070755082c43128000cad625c4625000187aeb308c4a00030f5d461189400054ec18c23128000aad82184625002d27f0fa88c4a00024f61f511894000716b16a23128000c3f519db325000717f013b664a000e2f60276cc94039e4f984ed9928000c9d309db3250001974213b664a00026ee0176cc9400061fa8aed9928073c9f315db325000197700bb664a00032e84176cc9400049fc0aeb99280d9c3f605d73250001a76c0bae64a01cf47cc175cc9400069d082eb992801693e855c7325000187ea33b464a000e2fe02768c94001c5ec04ed1928072caf209da325000195a413b464a00032e842768c940004ddc02ed1928000c3f515da32500e595e42bb464a00032ee01768c9400065d082ed192800093f815d632501af87ec0bac64a00034ed81758c94039697902eb1928000d3a105d6325002d27d0ab8c64a00026e603764c9400049fc2aec992801693c855d9325000136f02bb264a00566d205764c940004ddc02ec992801693e851d9325000127b0a3b264a00066e202760c9400049fc2aec192801693c855d8325000137700bb064a01cae3e1d320c940006c7c3a6419280dff0f514c832500e5b1ee099064a01cbe29c1320c9405e6c6b82641928072f89704c832501afd1ec099064a02fbe2d81320c9405e7c50826419280008bf865c432500011790cb8864a0003634c9710c94000cdd402e219280039ba865c032500073710cb8064a00034ee15700c9400069c42ae01928072d9b325c032500e5b5464b8064a01cb664c9700c94039ed4992e01928000d89325c0325000137702b8064a00034ed45700c9406f4ddc02ebb0a80019b8805d7615000127f0ab9ec2a005a4f21573d854009cddc02e7b0a80019
  | 9 => 0x30d91214bd5741061b224200aad820c3644852d56d02186c890802ad60430d91214b45f43c41b2242008bd87883644840187cebb26c6908030f5d764d8d210061f3a8c9b1a4200c3d7519363484010fb0f3aec6908121fe1d75d8d2176c3fc0aebb1a424c87d815d763484018ee20baec6908121fa1774d8d210043ec2ee9b1a4204c5e7594f63484091bf0ea9ec690bb30f9d740d8d210061ebae81b1a4200a5d850c3634840159b04186c690802b560430d8d210462e31aeb31a4200c3e75d92634840187aebb24c6908030f9d46498d210061eba8c931a4200c5d75d8e634840117d0fb22c6908022fa1c6458d210045fc22eab1a42038bc845d563484011f700baac6908063e2017558d2101c5f43ee8b1a4200c3f51dd1634840187aa3ba2c6908022f6037458d210045f438e8b1a42008be87d0163484071790fa02c690a632b5c86418d210046fc3ac631a4200c3c645d732484118b8c6bae6490a622f21974cc9214b45fc3ec999242008bd87d93324840187cebb2664908030f5d764cc9210062ebaec799242959ac865d2324840f95ec2ba4649081f69d85748c92100697a8ae91924200d2d515d2324840135f00ba4649080369c41748c921004d7c3ec91924297e8c32d91324852d958edb226490822b3a1b634c92100747b20c69924200e8c6418d324840117f08baec09080e2f21175d81210055cc06e9b024200ab9801d3604840117f08b9ec09080e2f21173d812101c5f436e8b0242968bc86dd1604840117d0fb22c0908030fdd764581210061e3aec8b0242008be87191604840187eea322c0908030f1d464581210064fb26e6b024200c9c64dcd604840193ec839ac09080327190735812139c5ec3ecbb1a8016c3e75d97635000127f0ab96c6a005a4f21572d8d4075eccb86c731a8000a9d83186635000155b0430cc6a03ab4e5c35198d400b49f43eeab1a800093d81dd5635000187ec1baac6a00034ed837558d400069d086eab1a80009bb805d5635000127d0e3aac6a005b0f1d76558d4039c5e43acab1a8073a9c8359563500e753d0db1ac6a00024fa1f5158d400b49e43ea2b1a80e9d3b70d456350001a76ebb82c6a00034e1d77058d40746cdb9ee0b1a8073c3f635d463500e787ac6ba8c6a00024fe057518d406ce1fb02ea31a8000d3b605d463500e7a3e60ba8c6a0003474c17518d400069d082ea31a800099f8758c63501cf73700b18c6a01cea7e1d6318d400064fc3ac631a8000e1f8558c6350001c390ab18c6a01cf879d56318d4039f0ebaac631a80d9a9f8058c6350001d3700b18c6a039ba68416318d400064eb1ae231a8000c3d75984635000187aea308c6a0002a760c6118d4000556c10c231a801693f87d44635000127b0fa88c6a00038758f5118d403945ec3ecbb128016c3e75d97625000127f
  | 10 => 0xb2262008bd878c3644c40117d0f106c8988022f61e20d91310045f43841b2262008bd87083644c40147d0a106c8988028f61420d91315054f41841b226200a9d83083644c53f56d02106c898802ad60420d91310061f3aec9b126200c3d75d93624c40187cea326c4988030f5d464d89310043ec3cebb12620487f875d7624c5dd0ff02baec49893a1f60575d89310063b882ebb12620487e85dd3624c4010fb0bba6c4988131b9d652d893102477c3aa5b1262ecc3e75d03624c40187aeba06c4988029b61420d893100566c1841b126200ae581083624c40f8d8c4bacc4988030f9d764989310061ebaec93126200c3e75192624c40187aea324c4988031b5d762989310045f43ec8b1262008be87191624c54393ae6320c4988023be1d62189314f4ce432e99926208c9f615d3324c411b2ec2ba6649880347d4574cc9310068ea8ae9992620099f805d3324c401b2e20ba6649880267e1f64cc9310061e322eb1926207c6c625d6324c5431790cba46498a7e2fe1f648c9310045ec3ec91926200c3e75d92324c40187aebb2464988031b5d7628c93150746196c8992629fc9c76d91324c40f59d0db126498803a3d90624c93100746320c499262008bf845d7604c40717908baec098802ae60374d81310055cc00e9b0262008bf845cb604c40717908b96c09880e2fa1b74581314fc5e436e8b0262008be87d91604c40187eebb22c0988030f1d764581310045f438c8b026200c3f75191604c401878ea322c0988032bd93725813100656326e4b026200caf641c9604c401958c8392c09881eb3a0f764cb210243f43eeab064200c3f40dd560c840187a81baac1909561fa1c75583210053ac08eab06420087f855d160c84090f90aba2c19080e2fa1373583210045ec26e6b064208ccc734c960c840117b0f32ec890802a7a0e65d91210054ec1ccbb2242008bf87597644843117b0e306c8908028fa1460d91210051ec28c1b224200a9e83183644840153b06306c8908032e5c060d91210061eba8ebb224200a3e85dcf644840147b0bb9ec8908028fa1673d91210051ec2ce7b224200c9f739cf644852f55d0439ec890a5aab60873d91210045f438a7b2242008bd8714f644840147f0ab86c8908028f21570d91210061fc2ae1b224200c3c855c3644840187ea2b86c8908030f54570d91210051f428e1b224200a3d851c3644840153d06386c890802a760c70d91214bd57410e1b224296aad821c3644852d56d02386c890a5ead60470d91210045f43ca1b2242008bd87943644840117d0e286c8908022f61c50d91210054f418a1b224200a9d83143644852f55d04286c890802ab60850d91214b55b408a1b224200ab581143644840117d0f186c8908022f61e30d91210045f43861b2242008bd870c3644840147d0a186c8908028f614
  | 11 => 0x5440127f00ba664a88034dc4174cc9511249f422e1992a20487f819da32544090fb033b464a89331bc86768c9510063690ced192a200c3f409da32544018ee213b464a88025de05768c9510063bc0aed192a200c3f405da32544998de40bb464a88031dc41768c95176e1fb0ae9192a200d37615d23254499a5e42ba464a88024fe01748c9510069b882e9192a22493e845c232544012eb03bb264a88024fe11764c9511249e422ec992a200977815d932544012f700bb264a888e5e201764c9511249f420ec992a20093d841d932544052e9033b064a88024fe11760c9511249e422ec192a200977815d8325449969f0e99064a880353e1d320c951266a7b8a64192a24cf46714c8325457ba9ae299064a8933d15c5320c95176f27b0a64192a2bff47614c832545e3e1e8099064a8af7d1c41320c951024bb432e2192a204974865c43254401a6f08b8864a88034d211710c951266ab992e2192a24cd66325c43254499aaa64b8864a893b594c9710c951006a2992e2192a200977805c43254401a6e80b8864a88021fe19700c9510043e432e0192a200d4d325c032544052ed02b8064a8bc25de0574d8151014ba40ae9b02a20093f845cf605444927908b9ec0a888a5de0573d8151014ba40ae7b02a22387d87d8f605449d8bce7b1ec0a88021fe1d63d81510049fc22e5b02a22493c845cb60544392ef02b96c0a880a5d20572d815111c3ec3ec5b02a24cc6e72d8b60544010ff0eb16c0a880257e0d7458151274ae41ae8b02a20096f825d160544992d904ba2c0a88025de0574581510043f43ec6b02a22387c8758d60544010fd0fb12c0a888e1f21d6258151014bd43ec0b02a2efd7371d8160544090fd0fbaac1988030fd0375583310061ea06eab06626a87e871d560cc4014eb023aac1988021fe1574583310243e42ae8b0662038be84dc960cc40117b09b92c19881f331c932583310045ec3ccbb226200aae82997644c40155b0532ec8988022fe1d65d91310f45ec38c1b226200a3e85183644c40147b0a306c898802aba0860d913100556c10c1b226200cb970183644c40187aea3aec8988028fa1772d91310051ec2ee5b226200a3e859cb644c40147b0b396c8988032bdca72d91315054f418e5b22629fa9d831cb644c40117d0e296c8988022f61c52d91310051fc2ae1b226200a3c855c3644c40187f0ab86c8988030f21570d91310061fa8ae1b226200c3d515c3644c40147d0a386c8988028f61470d91315054f418e1b22629fa9d831c3644c40155d04386c898802ab60870d91314fd5b408e1b2262a0ab5811c3644c40117d0f286c8988022f61e50d91310045f438a1b2262008bd87143644c54153d06286c898802a760c50d913100557410a1b226200aad82143644c53f56d02286c898802ad60450d91314fc5f43c61
  | 12 => 0x3b14c9415843200666996e0b0864008be87d01610c8071790fa02c219003a34cb40584320243f43eeab00640087d81dd5600c80187e81baac0190030f50375580322ac3f438eab006400a75811d5600c8010ff0aba2c0190121f215745803200667c3a64b0064bcccc874c9600c801c9eea992c019003931d5325803200765c0264b0064bcec8804c9600c80fd96e0992c0192f3b294132580325e747a0264b0064bceca404c9600c979d9420992c019003334cb71580320043f43ea2b00640487c87d45600c801c9a65a8ac01901e3e21d505803200764992a0b0064078f887501600c801d9264a02c01913a1f61f64d8d511261f3a6c9b1aa20093f845cb635444927908b96c6a8bef555c76398d510052ec18c131aa200a6d8218263545f5a6ae3a04c6a88924fa1f7458d510061fb0ee8b1aa200d3761dd1635440127b01ba2c6a88034dc437458d51004bbc0ae8b1aa20093e871d16354449878e9b22c6a893a1f21d6458d512752e41ac8b1aa200d3774dc56354401a68e9b8ac6a8be755dcf7158d510049f43e80b1aa22493c87d0163545f1a6ee3a02c6a893b0fd8d7418d512761eb1ae831aa2eec3f615d06354401a6ec2ba0c6a893b47cc57418d510068e98ae831aa20093f805d06354401a6e20ba0c6a880257e1d6318d517bdabc0ac631aa200c3d74980635440187ae8300c6a88029760c6018d5100536c10c031aa22493f87d00635440127b0fa00c6a89321f61f64d89511261f3a6c9b12a20093f845cf625444927908b9ec4a89321f61c63d89510051ec20c7b12a200c5d7318f62544994dd0431ec4a8bdb595c762989510052ec18c1312a200a6d8218262545eba6ae3a04c4a88924fa1f74589510061fb0ee8b12a200d3761dd1625440127b01ba2c4a88034dc437458951004bbc0ae8b12a20093e871d16254449878e9b22c4a89321f21d645895126536412c8b12a20087e8718d625440147b0831ac4a88034ddd371589510069a3a6e2b12a2f4d6772dc562544052e903b82c4a88024fa1f40589511249e43e80b12a2f3d3771d01625449987ec4ba0c4a89330f589741895176e1fb0ae8312a200d37615d06254499a5e42ba0c4a88034b48574189510049fc02e8312a200d37105d0625449d0fb0fb18c4a88030f5d363189512762f39ec6312a200a6d82d8c62544010ff0eb18c4a88030f5d16318951004b7c3ac4312a2f2b6781588625440187ae9300c4a88030f5d060189510052ec18c0312a200a6d82180625444927f0fa00c4a88024f61f40189510243fc0ced992a20487d819db325449d8be633b664a8803174c676cc9510061fa04ed992a200c77109db32544012ef02bb664a88031de0576cc9510061fa02ed992a24ec5f305db32544018ee20bb664a8bbb0fd8574cc9510069bb0ae9992a24ed1f315d332
  | 13 => 0x51ec2460b2c6407a6e828c1658c8014db05182cb190021fa1f10596320043ec3e20b2c6400a3e84841658c80147b09082cb1901e9ba0a105963200536c1420b2c640087e87041658c8010fb0e082cb190028fa1010596320051ec2020b2c64c3a5e83041658c8014bb06082cb1901e9ba08105963200536c1020b2c6400c3f759d5648c9fd55f04baac91901eab20975592327ed57c12e6b246407aae82d4d648c80155b05a9ac9190028fa1671592320051ec2ce2b246407aae829c5648c92955b0538ac9190028fa1471592320051ec28e2b2464c2a9e831c5648c80153b0638ac91901eaba08715923217d56c10e2b246400aba801c5648c8015730038ac9190022fa1f51592320045ec3ea2b246400c3e87d45648c80187b0fa8ac9193b78bc8751592322651ec2ca2b246407aae82945648c80155b0528ac91901eaba08515923200556c10a2b246400a3e858c5648c80147b0b18ac91901eaba0a315923200556c1462b246400a3e85dc1648c80147b0bb82c9190030fa1770592320061ec2ee0b246400c3f51dc1648c9af95e43b82c91901eaba0a70592327e556c14e0b2464008be87941648c80117b0f282c9190022fa1c50592320045ec38a0b2464c2a9e83141648c80153b06282c91901eaba08505923200556c10a0b246400ab681141648c80156b02282c9190022fa1e30592320051f42e20b246400a3d85c41648c80f55d05882c919002ab60b10592320045f43c20b2464008bd87841648c80117d0e082c9190022f61c10592320051f42820b246400a3d85041648c98553d06082c919002a760c105923203d5741020b246400aad82041648c8994eb033aac3193b69de0575586320243f42ee8b0c640087d85dd1618c8090fd0bb82c3190021f61770586327661f3ae80b0c64038be84dd5608c80117b09baac1191caae60274582326bd5dc02e8b0464038be84dc5608c80117b09b8ac11935b0f9d351582320043fc2ae1b0a640487c855c3614c80117f08b8ec09900e2f21171d813203e6743eec9906400e4e85dd9320c801c9b0bbb2641900333dd7764c83200666baeec9906400e8e84dd9320c801d1b09bb26419002b3607764c83200727a8eec9906400acd80dd9320c801d1e81bb26419002b3e19714c832005c7c22e299064beb8c845c5320c80159f0cb826419002d3e15704c8325fda642ae099064008bf845d5610c80717908baac21900e2fa1f74584320061fa8ee8b086400c3d51dd1610c80117b01ba2c21925e2fa1c74584320055cc00e8b086400ccf874c9610c97b9990e992c219003a3dd13258432007463a264b086400ec7814c9610c97bd8902992c21901fb1dc532584325ef27a8a64b0864bdec6514c9610c97bd8c82992c2192f7b1c41325843203c7a43aa2b086400ec532545610c80f1e90ea0ac219
  | 14 => 0xe8484165cc80147b09082cb9902297a0e10597320052ec1c20b2e640087e8704165cc8010fb0e082cb990028fa1010597320051ec2020b2e6408a5e8304165cc8014bb06082cb993169ba08105973200536c1020b2e6400c3f759d564cca0953f06baac999022a720d755933281d4fc1ae4b266408a9e83d4964cc80153b07a92c9990028fa1671593320051ec2ce2b266408a9e839c564cc93b53b0738ac9990028fa1471593320051ec28e2b266408a9e831c564cc86753b0638ac999312aba08715933200556c10e2b266400aba801c564cc8015730038ac9990022fa1f51593320045ec3ea2b266400c3e87d4564cc80187b0fa8ac9993bb87cc751593322751ec2ca2b266408a9e8394564cc80153b0728ac999022a7a0c51593320054ec18a2b266400a3e8588564cc80147b0b10ac999022a7a0e21593320054ec1c42b266400a3e85dc164cc80147b0bb82c9990030fa1770593320061ec2ee0b266400c3f51dc164cc9b393e63b82c999022a7a0e70593328154ec1ce0b2664008be8794164cc80117b0f282c9990022fa1c50593320045ec38a0b266408a9e8314164cc80153b06282c999312aba08505933200556c10a0b266400ab68114164cc80156b02282c9990022fa1e20593320051f42e20b266400a3d85c4164cc81153d07882c999002a760f10593320045f43c20b2664008bd8784164cc80117d0e082c9990022f61c10593320051f42820b266400a3d8504164cc81153d06082c999002a760c10593326255741020b266400aad8204164cc89d4eb033aac3993ba9de0575587320243f42ee8b0e640087d85dd161cc8090fd0bb82c3990021f61770587327661f3ae80b0e64038be84dd560cc80117b09baac1991ceae60274583326cd5dc02e8b0664038be84dc560cc80117b09b8ac19935b0f9d351583320061fba4e8b2c6501a6f825d1658c80f4d904ba2cb194029be09735963203d3741686b2c6400a6d82d0d658c80147d09b8acb190028f61371596320061f426e2b2c6400c3d84dc5658c9db8de41b8acb1901e9ba0a71596327fd36c14e2b2c640087e87905658c8010fb0f20acb190021fa1c41596320043ec3882b2c64c3a5e83105658c8014bb0620acb1901e9ba08415963200536c1082b2c6400a7a80105658c8014f30020acb190021fa1e31596320051f424e0b2c6400a3d849c1658c80f4dd05382cb1914a9b60a70596320051f420e0b2c6400a3d841c1658c9874bd06382cb190029760c705963203d37410e0b2c6430a6d821c1658c8014ed02382cb190029d60470596320043f43e80b2c640087d87d01658c80187d0fa02cb190030f61f40596320061fb8e80b2c64d7e2f20d01658c8e547b09202cb1901e9ba0a405963200536c1480b2c6407a6e82101658c8014db04202cb190028fa12305963200
  | 15 => 0x100200000000800201800b00700000000200100100100900000900200000600200000100100600800000000000200200600d00300100500100100300000400100200100100800100200100000300900000300800200500100000000100000800300200200200200200100301000200500000000300000100100000100200100200400100100201100300000000000100000900000000300200100100200100400000700000200200000800000800300000300000b00000000000000000600000101000000400100200300000000100500000600600000400300300201200100000700000300200400000003000400000000900500000700300200900400300100200100700000000200300000300300000000200100500200000000000300300600000000700600000300100000000100100200100b00a00100700400200000300d00000000000000500100100000d00000000000300200200401300000102800400100200000000100100000000100500900000200000100000000000100c00000600000400000000000100100200000400100000001100300400000100300600000000600000000800000200400100000000000500300000000000100200000000000000100000300000000100000500200000100000300100200700100200200800000000100000000000000001000100100000200100200300500900100100600000200000300200000500a00001100600100400000000100200200200100003100400200500e00200000100100000100000d00f00100500000a00400400100300800000000500201200000300500000300100100000400200700900200001400900200300000100b0080000030030010090010010061fba4e8b2e6507a5f835d165cc8114b906ba2cb9941a97e0d72597320452f41e84b2e6400a5d83d0965cc80147d09b8acb990028f61371597320061f426e2b2e6400c3d84dc565cc9dd8be61b8acb9902297a0e715973282d2ec1ce2b2e640087e8790565cc8010fb0f20acb990021fa1c41597320043ec3882b2e6408a5e8310565cc8014bb0620acb993169ba08415973200536c1082b2e6400a7a8010565cc8014f30020acb990021fa1e21597320051f424e0b2e6400a3d849c165cc8114bd07382cb9919e9760e70597320051f420e0b2e6400a3d841c165cc8114bd06382cb990d29760c705973262d37410e0b2e6400a6d821c165cc8014ed02382cb990029d60470597320043f43e80b2e640087d87d0165cc80187d0fa02cb990030f61f40597320061fb8e80b2e64d9e1f30d0165cc8e747b09202cb9902297a0e40597320052ec1c80b2e6408a5e8310165cc8014bb06202cb990028fa1220597320051ec2440b2e6408a5e8388165cc8014bb07102cb990021fa1f10597320043ec3e20b2e6400a3
  | 16 => 0x8b020001a797e80860000001104e2e2943489d805ca0001768834e5e74e00001940001500000adc0004f61c200000000000000f0ca1234813905f800078c0008000c4c00004c000013205d230800000000016d00000008542c720680000002098a8800037934c836c00075f22c8000000000393842864c00041580000000000001d1c6d40002350de81980003eaa0c000018627f83440005c641786380000000001b8c8ba2ef18c1f049ac4bf000175800000000002d0bc00000001bb00000001f2000000020a00017541a81963b110e000000014c893c0000001c60528b700001e900000008031370130c740003e71300eca0002c910600004050608e24000000000182c0008521be0fa46da6fb00000000003e300002b04880000548000000000000000000044f00005a0bbe00019380001d60000b891380665ff07383102c255e01412c018a71a00006c424000011d1440f1c0001d6802ced21fa11b0b88af02f600f80004bc6bc0ec93dceb627406d0000b4c5272b112e0e380000e38d90c7029510b800028a5411591cc00003f311797b83445381c797045a618432a86d468e1bf40720b02c60a23d409e05b008a05b214c7700001c894b423c26417d89a000068d311849c0000000001aa00ee0000000b0c0004ad2ba92640000352a6800000000033b855cc823b507e038103001416680000000001c185b844c36f0c58000000497080878d01a000000000000000022f137800000028b1860a840002d90fb40001d0000000000047a00000000007b12b28000000000117000047a10f00000004260000000000d1800000600000100000000200200000100c00201b00000400000000d00100800000100100200000000100500502501100100200100a00000e00500000300000000100000500000c00000100000000000300400000100000000100800301400200500000700800100400500000500000000600200e00000300700000000501200300000600000400200300600c00600400300000700402200500000000201200000100000000000200600400000000100d00000100100100700000000100600000400200300000100400100000900000300300600000200900c01100a00500000100000700000200300200000000000000000100000100300000000300101200000100100600100800100000000700000300000400200400800000400000a00100500600301000c00300300000000b00000000000000800a00000200000000300500500000000901000100300a00300100a00000400100300000000000000100000100800400900000000500800200f00c00000000200000500300100000000000100000100501400100000000100100300000400600001300000d00700200000300000000000000800100b00700000001c0010010080
  | 17 => 0xc0000000000000000000000070c2e496f0c140aa000026865e0a80000c205e81db0358000ff00001628378000000000000000000003d20100007020000a1800000031e8000000000119000000043000006cc42a0dd11a00c4b207ab3b58e00a782e105580001f07d93f7820c5c60003ca00007dc00000008cc1e258b00019a8dbe3591a98a9d0860003018000000000161100c9aa70b309004d062485382000047200012f9a14000000000025485031e1961254b5427918189a48f63a53f089187b067301709fccea4490e60000eae1ef374011c20c19113591ac34c7a507e95644e24af25000000005881da0534d46000000000017859c2fe90bcdde5183869c00df04f032201847760c900019b00000000000b000005262b215b8ec86da0a18000a8e2fc00000005a81c41d380000006e90000f2c00000041c12246a842e1420000edc0000001764f4640f2e90000c0c00000000002046433fb8cb800000000000000004c62ad05a9036000000000000068311f8e5c00060227304c09fc69b19e1660f001250350154e100000ee00000000ff1f611107020000000e70e526f2143800097a40731787784a608807180e013e0004120b900002dc000000000000000000006aa6ce3bc000000036e03b212c4960003c282903120000000734000398000200052e0001440000dca59d3ba8000c80000000163ce707d73be8000000471268800000022c00005d06406d3000000011837b0001e74cc40000001e3c62c2220db98a0d3a5d833c073d0240002998c8c2b039b00013600003f00e580a40001c800008d4b060341d312cc00000024700002585d700000000000003b80ffcc7c5cc0b8150c2de00033319bcc0247200000003464433108d58c262163fa87480004cb000058019c5bb17617c057009311c00000002703150000cac7950001a788c400000001b000011d0000fd80006e100015a4f922492ab93281ec7fc14914001be50d1d000000004a82de80000005050000000f880c700e1f0ce7a84800000000060002629e48e921400001084000000000035c000000000118c8d013807297f05620001a100007f000000011cc0002c4000000038a12f0000774e985a82be14d80007932d480000001ce000000000000000009340e600034a1c983786ee00000002bc00000000000a06b13f910d88342543fc80000006aa000008000000000000005e02de000000000018a0000000000000000078889651d000215884e67a0d08b3ccc653b3ba1b58bba0000a7017c7ee3a905f0cf8f644dc19b98940000000c0800082a51b3f61530c388390be00010884ac2128000a5820505d9a5c0000000000f4000000000006a00001a700000000006ac000000000000035f800000026316388900000002b4000000000000000000000000000000ce479a0001a8
  | 18 => 0xcae1ec2738000000015321000000065902300000e20000001ca000000000000000003130028000d5a00000000000000000001e780007ba33c87f4a18000388978c69a0000000000f6000000000007de00024f000000057e2f69830c561e517011a400042005015d80000001cc8f740001e938089b005a00031a800000082105c8124e263343eea0a80000002c300003c03e638d9cac0006f60cd8d0c6d622d115800062402717d0000a323510000a789f673517f9d1817e33a2b387d812e0000001d483683f100010c8000000000126c0006821571f182aa6052681e400f27eb25380007be4330000000ef43b30720f580000001e48904cdc66115a80000000000001194b7e0001e405fcfa80002a5800000000042800000007cd2289d98ad84ed13305c8f68085073000099000029900f08e02f529880200000001ba800000051c21180000006a000000906e82ee0ae0000d980003b899a0fd2000000172c00000000019c42ee5b42ba1d8507600037e00003940063bf800082818310f8ee491018507f00010181ea35099d8b120000f680000003462fa00b0f780000ed04b86ba000155920c78e0000d50e20000000000000000000000000000000000000000f1400022a079867061a07619181e00003ad00000002a411b9ff4000000000000000003d00000004986b51e11fc40361bd33e8d7000063936b987c8f800000000000005c3000000000075d000000000000011413c4ea01040a60a7400068e40b88240000cf3a992f8dee8451af0e0800084600000000000963e915bca724d20159a1000013a0000000d02000141800025200041e05cc2f21590001f9c00000000004640000000000000ef60003961cf00005ca0c3800000000019c9f1c000000000183d02050108a1bfc00083500000000000002a70000000000387a15400046000000009f20d214500dc0007dc00000000003a400006b466245c000000004a514295132400000000000000000000000000000000000000048a4640000490cd61a03618000e8200002c9de40003a1000103000055f2fb00007f640401f886073e45200c9ddc3d041718a93380c808f1c58bc851e6f42d199a47bc616382948070e00020882180444ea180854c0000d900011f8d2a0001878eb8f547a422f800000000025d10f4f361472aa80009680000001c50dda3ce3241db40007c00050ff83840003c4000025631d2d78cc0e420ae00016e433e2bc31b800108000039b9e884ce81500000007ea000000000000046f25318809ca0000f90000e9a000000014c57a6de1459cf8c1a0002c880000e0000100888473a0002b68c5c00025c404000000020b36e9a70d8a50724f99c06b42be2ca8eacf981fe1870a58a603953ac920027e2ca10d00000000000000000cb8000000000009e0000001a000005e
  | 19 => 0xf10be9db000063637580000000002368d606343fa00000008680001b80440b7c281317052c18c61900009f4000000004a0040004dd2f4a1240ae42c3a5018cd7a0000dc80000000000bd800000000002200000000000209a94410000000000000045a15293090507d303f97080005040001798a9e25114c12300007200000c94d9a06f1530d40a7e28d000193c310000034800000000000018006cc0000000000ab83b000008c000010d291800000021c10619502823e21011ea41f65fe0000388bea594000100104e5540000000e3e33f3148b58f020e90818938b9c01a041124090c51f07b800041e32a2bf961400026f00699f80002a8399880c00000026d006027600000000000000000000874d9241f0a496c4e1216d0039edc0005b50ad8000b0e5d00000000de200021492d800000007a9f2cdd46b421e000040c75118f800000000002e15407807ff2e417e49d07680dd8dc80006fd3c202c04ae6db2a4000023042229aa07807652f00000000bc0000000000a5000000000004007480000000a2600009b000078a7190000d00cce00000005acaf200000000006567a10000b6c00046617c859000012d0a8800000000000010401d47de0241c9000034a0001a2433a5f70c81e60ef83bc0e8800000000013d000800015200015802b40003d98000bb600000015f4a4a335279203c9ae5e410d9700da25530470e480c076738b0f80ffc83a0071ae09a8000000034c9225ad15d09cc16448436e000094a000000000032a61000000000000003eb1c40f7680933693305680003021f8800000009880000004b200000000006d82bb8d8100a3cd00000000004930fe1a1800000000007040006492958bac60400000014dc5fa84e357800087e68b22d915c0000003c100c84fc0002e8884400068f0858248c4e00007a00000008140001cc40000ba06a9ef43480001dfa15c0086b615180006ec72e0001f8000050200019300003060000f680004762748000be24c33e41b9c7542e725b9f44f161ff2a5000000062c00000000001c300000005ee5b32621c186fa81927700000000000000000000000000000000012200000000000000000aa46384f81ed91e00000000d7926000081f37f15241220000001eb40000000000000e6c445199183889a0000000000a0c00000000004544e2000000036435b3f5027000000c0fd9c60fbe20436a80000007bf15b029c0001f513501e000007b2ae800000000041a026c4840000000000b5c000000000004c3690000000000000000000109400026d813801e03e2dd00005000001599f8c9b22bb0000c303ae00012d00002cc7a601b000048e81d20302007621f314612b800076f31f89d478200020e00e80001ee1db903836c63c199800075e7231b88b745fc0000000000af677e0ba80000003f400000
  | 20 => 0x83d1368f181940002f98eb015a3cc1b40040aa21323a2964c0001f920f00000008110000000b00000000000000064a02589002ec7c51bc000000000000000000000a60ce14f84f853406c1fc0d665da0d4832092452200010345585ef3b99e246764ab2760ac0a80000290902c00007227a81a08626bb14d14906e68420000000440000000000000008100007c00000003aa800000000000000000000541f3800000012800010d400000000000000007fa00019900003283a1012802c0002b082cccb000040b0f9400000015f9d2cad411f31680000000000d717101dc300000158c0004c10001384aa466511f000000073900000000000000000000000000000000067a0000000000d3e1d8000000000000040e1b28ca600041b905871432100007dc000000168000000044c00000000000001a21c1cae23bd3271b04e8839a24580000000003af0e380000001e896880005e837980000000002050000a1c6d017485a499e743000000000032916b9dd82d80c02338ec873c25d36400009c00003530000d805e720480002ca08d0fc05882ba07409180006120002f091fcda88262d09f683c23523570000520393355865c0b6508000151842400000010b40000000000faccfe1ac2f5800016e53d01784d0b6c18c0579b1896a5b70000000a1612a00000000000000001b3c0001073c88e1411644719b07c413c73a0001ef86fe2523a001b49467253538274590608080142875011317511dc9c813335f15c044663129481f010875627d1004c9a6153d6032c53665a25200007b217a30d8c348746741839e1826e1ba3d38d04be401e34986786920580a795987a66cb3228db000007d29700000000000000000f061154119b900000000001a40d3085102102504b015400020c800060900000005aa5110000b7c00044600017946081d44058648d600dc2ea169c3aa00000000000c400000000000000003870000da46520000000bf679621b914c0000003fd80004320bd0828d88d8458a1828044bb877200000000000000000d14cf644008916640000000c9984474423b1ab9978fb020e31a028c19a00009e02c4978090000109800000042087d109a00033e109000000000000002343903d788c40005cd00013cc0005970000000c764eb1db00000000003ce000000028e1a600008040fa000000033279f27a20f888437e1fe9874e5406719696581d07f423c940c9343dc0909e5c00000037a8f840608060e9992cb366b7319969000058d32e80007a82c900000000006603c38000b606e63da800082461e25884f843c2761eb877c00000000000006286b92fc0000ad6000000123400000002291b82ac7b6319000097625620c8158f4018f010879c6ca10e000000000000000000000006d900000000003e81630000c442cb01c80001842
  | 21 => 0x6a409a9b801f200022814e85a484737d0fc8fdc5453911c54000000000000000074f00000000004390619b100000f200000000a25de0000c4400000037c800000030a0151e340000000001d50b581c912180000000000001f080000002041274a2e00004480006ee000000000083a00008b19440008360d81cb46165723f4137c00000038190a89fa4cd000092804600000007ac0000000c1160803a487271800054251539f80000005a50438a240000000000ff000000035d00000000000df00000000000508000000000000000059865f2e289dc21200000009640002b925491b0000000000051800000021580000004962cf81d4728000167191cc0e71200009840000000001f400000000000000a3c2270eb1940000000000000008010800000008901e40000bcc27a43b07680005a20000000e1800000025080007943960000000fe6000000000000000000000000000000000000b4000000000004ca6960dc000034a3a32ab0000d101483f28a8105c3cf00000001ac00014889ec000248000000000000031812a80006e22ac05e035600000000008b044a000000000073b343974c1de3ea0000c400003610000b640fc57a36391d47f281328d1f6c00000000000000005c73b502e091e62400001b80000003d70a7c44a11741493f00002293851ac80000000b3a08000000017300000000003fb0be00004a2142a0cc0002c118d8000288000000005c0006a941280000000000e315cc9026f023a0000a1e0001569d700000b500000004200000001f3c00032400017a8fc80000000168fda000000000000018d0000000000617000000091400008d8000000000000000024c82d14e00000000000000000cb600015789807aa28222b066800000022a84300003be10a0000bc469a1dd000000068a000166800069218c844409a01209c9ee40000000000000ec600012a8000b9e0000000470ab643e39a00000cc84c0c00d9cb5680a000094000079914980001e61c02cf0000000000000000000020724a00000008020000ba100e194000000000000000000000000001a583840000001e20000fcc7580528d3833032200000009a600000012e48360000001ee098e2aa30a0d7c9384821c6850904473238f08f04c484f0290000f944ef23e94482be00000000004b654400003406c671d000000000058441f80000000002c60
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x14c8964c9700c9100060d1d9841cd5144001a456360863545100060d1d9841c95144001a458358862545100241d25d860c95144001a45864c83254510006d04c9800c951440013339460f7054510004cce5182dc15144001838766147350110006645cd811cd4044001a896360863501100060e1d9851c940440019a1726047250110006a260d6218940440070b8976183250110006a2619320c94044001b81326043250110004cce5583dc540440013339560b71501100064ce1e8754540440016339661d5150110005c4e4d8754540440017109361d5150110005c8e498754540440017209261d51501100064c61c8754540440015339760d51501100054c25d8354540440015329720d51501100054c65c835454044001333985cd5150110004cc261735454044001332981cd5150110004cc660735454044001d11731cd5150110004cce616354540440733309858d51501100054ce5d63545404407f5309758d5150110005c8e496354540440017209258d515011085ccca606354540440473319818d51501108554ca5c63545404402b5319718d51501100078458c6354540440017229218d5150110005c86486354540440015339760951501100054c25d8254540440015329720951501100054c65c825454044001333985c95150110004cc261725454044001332981c95150110004cc660725454044001d21721c95150110004cce616254540440733309858951501100054ce5d62545404407f530975895150110005c4e4d62545404400171093589515011084ccca606254540440473319818951501108454ca5c62545404402b531971895150110005c4a4c6254540440017119318951501100078858862545404400133298cc95150110004cc66332545404400153297cc951501100054c65f325454044001332988c95150110004cc662325454044001532978c951501100054c65e325454044001632960c951501100058c658325454044001f01320c95150110004cc654874c5404402b390985cd31501100066421d734c5404402b5919718d3150110005e0648634c5404400133195e0931501100056465f324c540440013319521d2150110004cc65783485404402b3a0985c921501100066821d72485404402b5a1971892150110005e064c6248540440015a1978c921501100054c6508754530440475509760d514c11011cd46606354530440017419218d514c1100054c65372545304400135198cc9514c110357141db754c53044141a9086e11314c110004d4657824c5304400159194dc9314c1100054c65087545204400153194dcd514811011d5825d825452044047361981895148110005d064c625452044001361988c951481102af181db75485204412faa086e112148110004d86578348520440015a194dcd2148110
  | 1 => 0x3100000000002ac4407800000001e4100000223a80072000000116002e800008f2e0102410078009800591001000248007644000005000060000000002b800434a21c2ea430270120b1a0e8e02a182b40000132280038001840025000011a5336801305800000c600002849c6b000005c0000001344a550000000098001c9e230f0c41f4999d5e0d139a0000050068000619a490c3d0e2a0e26f4aa9c00000000000003b800f80741a891c00001086a5b4606ce80112060569b549b920592aa007e892b9b14a9f2d0bd3a161f144004716850042326958fa0000000d29900000227900000001505000c80000215106a0012c005e0000102210028c6400000000000330d8a8724880058003b0a4000022904be00329486e002413cfc973d864a07a559cc001d000010803581fc00000029800004b00158000000001008000c02030040a03058800607028004e011000000000200c04030700c02000180c000000000000c018000004000000600010441002058380a03000000212000000103d98dc740597320040f66351dc164cc80103d98dc740596320040f66351dc1648c801a0e85a13764c832005a2640744c9610c801645911d53258032006075d183180635440182d746086018d51006076117318f625440182d7460b6318951006075d183180625440182d7460860189510054c640845c43254401d07844c9710c95100741211325c4325440194532e01710c951007414cb405c4325440103d989d464d89310040f66275193634840181f87e156318d40006075d583184635000182d756086118d40006076157318f625000182d7560b63189400060be1f85588625000181d7560c61189400060b5d582184625000153191215700c94000742e15325c03250001d08854c9700c940006624cb815c03250001d0932d45700c9400040fe61761d9515000141c935d876545400050b249761d9515000141c9758c63545400050b25d621895150001b05326043254540006c24c9800c9515000181d8560c764c5400040f663511d93150001c9130440764c5400070cd45101d9315000182d8560876485400040f663511d92150001ca12044076485400070cd45101d9215000103e98d0171d95300040f66274197624c00181d8460c76545300040f663401d9514c001c33404407654530007144c5101d9514c00103e98d0171d95200040f66274197634800182d8460876545200040f663401d95148001c3340440765452000718485101d951480010cc985d9320c91000531259325c43244
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x31061b4020002a58080280e9000700001680d0108992e2192a200b40684854c9700c94000506351a8a203b262a0002831a8d45101d92150001418d4680880eca8a6000a0c6a340440765452000426752c390ea8a8088002910a361c8754540440014905130e43aa2a022000a442a1731cd5150110006c02c6c90c6a8a8088002920a85c8725454044001b00c9ac4312a2a022000d80659320c95150110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x3
  | 8 => 0x4
  | 9 => 0x98a
  | 10 => 0x98d
  | 11 => 0x98e
  | 12 => 0x150a
  | 13 => 0x150d
  | 14 => 0x150e
  | 15 => 0x9ca
  | 16 => 0x9cd
  | 17 => 0x9ce
  | 18 => 0x168a
  | 19 => 0x168d
  | 20 => 0x168e
  | 21 => 0xa0a
  | 22 => 0xa0e
  | 23 => 0xb09
  | 24 => 0xb0d
  | 25 => 0xb0e
  | 26 => 0x1549
  | 27 => 0x154d
  | 28 => 0x154e
  | 29 => 0xb49
  | 30 => 0xb4d
  | 31 => 0xb4e
  | 32 => 0x16c9
  | 33 => 0x16cd
  | 34 => 0x16ce
  | 35 => 0xbc9
  | 36 => 0xbcd
  | 37 => 0x3c9
  | 38 => 0x3ca
  | 39 => 0x3cd
  | 40 => 0x3ce
  | 41 => 0xcc9
  | 42 => 0xcca
  | 43 => 0xccd
  | 44 => 0xcce
  | 45 => 0x15c9
  | 46 => 0x15ca
  | 47 => 0x15cd
  | 48 => 0x15ce
  | 49 => 0x1709
  | 50 => 0x170a
  | 51 => 0x170d
  | 52 => 0x170e
  | 53 => 0x98956
  | 54 => 0x94995
  | 55 => 0x9c956
  | 56 => 0x949d5
  | 57 => 0xa0956
  | 58 => 0x94a16
  | 59 => 0xb0955
  | 60 => 0x94b16
  | 61 => 0xb4955
  | 62 => 0x94b56
  | 63 => 0xbc955
  | 64 => 0x94bd5
  | 65 => 0x1409
  | 66 => 0x128a
  | 67 => 0x1449
  | 68 => 0x12ca
  | 69 => 0xb0995
  | 70 => 0xb0996
  | 71 => 0x98b16
  | 72 => 0x154995
  | 73 => 0x154996
  | 74 => 0x99556
  | 75 => 0x209
  | 76 => 0xbcb
  | 77 => 0x19c9
  | 78 => 0xbcc
  | 79 => 0xbc995
  | 80 => 0xcc996
  | 81 => 0x98cd6
  | 82 => 0x15c996
  | 83 => 0x995d6
  | 84 => 0x1649
  | 85 => 0x134b
  | 86 => 0x449
  | 87 => 0xb1515
  | 88 => 0x150b16
  | 89 => 0x8a
  | 90 => 0xbd515
  | 91 => 0xcd516
  | 92 => 0x150cd6
  | 93 => 0xb49d5
  | 94 => 0xb49d6
  | 95 => 0x9cb56
  | 96 => 0x16c9d5
  | 97 => 0x16c9d6
  | 98 => 0x9d6d6
  | 99 => 0x249
  | 100 => 0xbc9d5
  | 101 => 0xcc9d6
  | 102 => 0x9ccd6
  | 103 => 0x1709d6
  | 104 => 0x9d716
  | 105 => 0x17c9
  | 106 => 0x134c
  | 107 => 0x5c9
  | 108 => 0xb5695
  | 109 => 0x168b56
  | 110 => 0xca
  | 111 => 0xbd695
  | 112 => 0xcd696
  | 113 => 0x168cd6
  | 114 => 0xa0b
  | 115 => 0xa0c
  | 116 => 0xa0b16
  | 117 => 0xa1556
  | 118 => 0xa0b56
  | 119 => 0xa16d6
  | 120 => 0xb89
  | 121 => 0x138d
  | 122 => 0x1849
  | 123 => 0x1489
  | 124 => 0x124d
  | 125 => 0x289
  | 126 => 0x3ca16
  | 127 => 0xa03d6
  | 128 => 0xcca16
  | 129 => 0xa0cd6
  | 130 => 0x15ca16
  | 131 => 0xa15d6
  | 132 => 0x170a16
  | 133 => 0xa1716
  | 134 => 0x409
  | 135 => 0x8d
  | 136 => 0x1609
  | 137 => 0x1889
  | 138 => 0xd09
  | 139 => 0x128d
  | 140 => 0x589
  | 141 => 0xcd
  | 142 => 0x1789
  | 143 => 0x18c9
  | 144 => 0xe89
  | 145 => 0x12cd
  | 146 => 0xccb15
  | 147 => 0xb0cd5
  | 148 => 0x15cb15
  | 149 => 0xb15d5
  | 150 => 0x160a
  | 151 => 0x148b
  | 152 => 0x40a
  | 153 => 0xcd555
  | 154 => 0x154cd5
  | 155 => 0xccb55
  | 156 => 0xb4cd5
  | 157 => 0x170b55
  | 158 => 0xb5715
  | 159 => 0x178a
  | 160 => 0x148c
  | 161 => 0x58a
  | 162 => 0xcd6d5
  | 163 => 0x16ccd5
  | 164 => 0xa4a
  | 165 => 0x124e
  | 166 => 0x198a
  | 167 => 0x138e
  | 168 => 0x3cbd5
  | 169 => 0xbc3d5
  | 170 => 0xccbd5
  | 171 => 0xbccd5
  | 172 => 0x15cbd5
  | 173 => 0xbd5d5
  | 174 => 0x170bd5
  | 175 => 0xbd715
  | 176 => 0x44a
  | 177 => 0x20e
  | 178 => 0x164a
  | 179 => 0x1a0a
  | 180 => 0xd4a
  | 181 => 0x140e
  | 182 => 0x5ca
  | 183 => 0x24e
  | 184 => 0x17ca
  | 185 => 0x1a4a
  | 186 => 0xeca
  | 187 => 0x144e
  | 188 => 0xcc3d1
  | 189 => 0xcc3d2
  | 190 => 0xcc3d5
  | 191 => 0xcc3d6
  | 192 => 0x3ccd5
  | 193 => 0x3ccd6
  | 194 => 0xd0c
  | 195 => 0xd4c
  | 196 => 0xe8b
  | 197 => 0xecb
  | 198 => 0xb09499d
  | 199 => 0xb09895d
  | 200 => 0xb09895e
  | 201 => 0x9894b1e
  | 202 => 0xbc9499d
  | 203 => 0xb4949dd
  | 204 => 0xb49c95d
  | 205 => 0xb49c95e
  | 206 => 0x9c94b5e
  | 207 => 0xbc949dd
  | 208 => 0xa094b1e
  | 209 => 0xa094b5e
  | 210 => 0x95295
  | 211 => 0x952d5
  | 212 => 0x95416
  | 213 => 0x95456
  | 214 => 0x19cd
  | 215 => 0x180b
  | 216 => 0x151556
  | 217 => 0x180c
  | 218 => 0x1696d6
  | 219 => 0x155515
  | 220 => 0x16d695
  | 221 => 0x139255
  | 222 => 0x198d
  | 223 => 0xcc3ca1e
  | 224 => 0xd0411
  | 225 => 0x9515
  | 226 => 0x151295
  | 227 => 0x19d515
  | 228 => 0x19c995
  | 229 => 0x128995
  | 230 => 0xe8591
  | 231 => 0xd695
  | 232 => 0x1692d5
  | 233 => 0x19d695
  | 234 => 0x19c9d5
  | 235 => 0x12c9d5
  | 236 => 0x180e
  | 237 => 0x19cb
  | 238 => 0x19cc
  | 239 => 0x139256
  | 240 => 0x184e
  | 241 => 0xcc3cbdd
  | 242 => 0x21556
  | 243 => 0x181556
  | 244 => 0x155416
  | 245 => 0x180b16
  | 246 => 0x140b16
  | 247 => 0x256d6
  | 248 => 0x1816d6
  | 249 => 0x16d456
  | 250 => 0x180b56
  | 251 => 0x144b56
  | 252 => 0x15c995
  | 253 => 0x15d715
  | 254 => 0x15da15
  | 255 => 0x15cb16
  | 256 => 0x15d716
  | 257 => 0x15d896
  | 258 => 0x1709d5
  | 259 => 0x1715d5
  | 260 => 0x171a55
  | 261 => 0x170b56
  | 262 => 0x1715d6
  | 263 => 0x1718d6
  | 264 => 0xbc9529d
  | 265 => 0xa09541e
  | 266 => 0xbc952dd
  | 267 => 0xa09545e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1383
  | 6 => 3535
  | 5 => 2136
  | 4 => 179
  | 3 => 14
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (56242+((h/461+packedAt gbK7 (51171+(h % 461)*11) 11) % 1826)*12) 12
  | 6 => packedAt gbK6 (184994+((h/1178+packedAt gbK6 (169680+(h % 1178)*13) 13) % 4667)*13) 13
  | 5 => packedAt gbK5 (134568+((h/712+packedAt gbK5 (126024+(h % 712)*12) 12) % 3412)*13) 13
  | 4 => packedAt gbK4 (13061+((h/59+packedAt gbK4 (12530+(h % 59)*9) 9) % 284)*9) 9
  | 3 => packedAt gbK3 (1154+((h/4+packedAt gbK3 (1134+(h % 4)*5) 5) % 20)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc3f0fff8f061f87f023f07f83fc5304f0dc4cf
  | 1 => 0xfc3f0e07007e1f87ffc7f83fc1cac1b4127b33
  | 2 => 0x3ff007ff801ff803f8003ffe330e38e38c3c
  | 3 => 0xffc00007ffffe00003ffffc0003c0fc0fc0fc0
  | 4 => 0x7fffffffffc000000003ff000fff000
  | 5 => 0xfffffff80000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x40121020202809080901080880100104c045
  | 1 => 0x44110420000200824042401201004094001112
  | 2 => 0x2aa04354801550129010a5b4130628630c28
  | 3 => 0xaa800085995540002324b680842c0b40b80e80
  | 4 => 0x22088116ee799e64b800230118bfb000dfe000
  | 5 => 0xf33cc9e00c110440c000c406213fedfe000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36318
namespace PEqualNP.Outside.L_meta_36318
open PEqualNP.Outside.L_meta_36318.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 26 := bs0_3_0
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
theorem bs0_4_128 : Interval s0Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 134 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 26 := bs1_3_0
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
theorem bs1_4_128 : Interval s1Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 134 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_3_0 : Interval s2Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 7 := bs2_3_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 7 := bs3_3_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 2 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 30 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_128 : Interval s4Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_160 : Interval s4Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_224 : Interval s4Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_256 : Interval s4Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_320 : Interval s4Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_352 : Interval s4Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_416 : Interval s4Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_448 : Interval s4Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_512 : Interval s4Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_544 : Interval s4Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_608 : Interval s4Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_640 : Interval s4Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_704 : Interval s4Atlas 4 704 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 712 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 (concat bs4_4_192 bs4_4_224)) (concat bs4_4_256 (concat bs4_4_288 bs4_4_320)))) (concat (concat (concat bs4_4_352 (concat bs4_4_384 bs4_4_416)) (concat bs4_4_448 (concat bs4_4_480 bs4_4_512))) (concat (concat bs4_4_544 (concat bs4_4_576 bs4_4_608)) (concat bs4_4_640 (concat bs4_4_672 bs4_4_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_64 : Interval s4Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_128 : Interval s4Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_160 : Interval s4Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_224 : Interval s4Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_256 : Interval s4Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_320 : Interval s4Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_352 : Interval s4Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_416 : Interval s4Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_448 : Interval s4Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_512 : Interval s4Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_544 : Interval s4Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_608 : Interval s4Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_640 : Interval s4Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_704 : Interval s4Atlas 5 704 31 := block_range (n:=31) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 735 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 (concat bs4_5_192 bs4_5_224)) (concat bs4_5_256 (concat bs4_5_288 bs4_5_320)))) (concat (concat (concat bs4_5_352 (concat bs4_5_384 bs4_5_416)) (concat bs4_5_448 (concat bs4_5_480 bs4_5_512))) (concat (concat bs4_5_544 (concat bs4_5_576 bs4_5_608)) (concat bs4_5_640 (concat bs4_5_672 bs4_5_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 42 := (concat bs4_6_0 bs4_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_7_0 : Interval s4Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_7 : Interval s4Atlas 7 0 1 := bs4_7_0
theorem alls4 : ∀ k ≤ 7, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
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
theorem bgb_4_160 : Interval gbAtlas 4 160 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 179 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160)))
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
theorem bgb_5_2112 : Interval gbAtlas 5 2112 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2136 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))))) (concat (concat (concat (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280))) (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568))))) (concat (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696)) (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824))) (concat (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952)) (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112)))))))
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
theorem bgb_6_3520 : Interval gbAtlas 6 3520 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3535 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)) (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)))) (concat (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)))))) (concat (concat (concat (concat (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 bgb_6_1952))) (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 bgb_6_2176)))) (concat (concat (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400))) (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624))))) (concat (concat (concat (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)) (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072)))) (concat (concat (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)) (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 bgb_6_3296))) (concat (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)))))))
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
theorem bgb_7_1376 : Interval gbAtlas 7 1376 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1383 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 (concat bgb_7_448 bgb_7_480))) (concat (concat bgb_7_512 (concat bgb_7_544 bgb_7_576)) (concat bgb_7_608 (concat bgb_7_640 bgb_7_672))))) (concat (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832))) (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))) (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184))) (concat (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)) (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8feeefeeafeeceee8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36318.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.or,[1,5]⟩,⟨.or,[6,7]⟩,⟨.and,[6,7]⟩,⟨.or,[4,9]⟩,⟨.and,[0,8]⟩,⟨.or,[10,11]⟩,⟨.and,[2,3]⟩,⟨.or,[1,13]⟩,⟨.and,[12,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36318

open PEqualNP.Outside.L_meta_36318 in
theorem PEqualNP.Outside.L_meta_36318 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
