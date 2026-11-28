import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36723.Model
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


end PEqualNP.Outside.L_meta_36723.Model

namespace PEqualNP.Outside.L_meta_36723
open PEqualNP.Outside.L_meta_36723.Model
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

def SBf (j : Nat) : Nat := [6, 3, 7, 7, 7, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 67]

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

end PEqualNP.Outside.L_meta_36723

namespace PEqualNP.Outside.L_meta_36723
open PEqualNP.Outside.L_meta_36723.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x284c1a40128080018076a1601806bf43bd43bf42bd42be41bc41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x180028810020025aa5a1c754f428ea98832d52107a060087808010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
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
  | 4 => packedAt s0K4 (244+((h/4+packedAt s0K4 (224+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s0K3 (170+((h/2+packedAt s0K3 (162+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfe03fffffffe01fffff80fffffff01fff1fe3f
  | 3 => 0xfffc03fc03fffe01fffff01fc07ffe07fe63c7
  | 4 => 0xfffffc0003fffffe01ffffe0007ffff81f83f8
  | 5 => 0xfffffffffc00000001ffffffff8000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x9604848428a224242450b162d48b628a26acdb
  | 2 => 0x2ba1292a51451d4948ac0ab56955115551562d
  | 3 => 0x4caba2329a69491d913d58198c66b4479a6346
  | 4 => 0x713233a3639191911dce6cd03078d9e11d83b0
  | 5 => 0x81c3c3c383e1e1e1e1f78f1e3e40e1861ff800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36723
namespace PEqualNP.Outside.L_meta_36723
open PEqualNP.Outside.L_meta_36723.Model
def s1K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (i*4) 4
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (5+((h/1+packedAt s1K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffd5f1c71f878f1e93
  | 3 => 0x66fe07e3f80fe31c
  | 4 => 0x78fff803fff003e0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff8010000008810025
  | 2 => 0x2a2caab1c52a5a92
  | 3 => 0x1945b496d44ccb18
  | 4 => 0x78926db666893c0
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 29 s1Pos s1Neg, 0xaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36723
namespace PEqualNP.Outside.L_meta_36723
open PEqualNP.Outside.L_meta_36723.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1610da02c000002800d24001d1802600c824420000007001200015a5589831f00a401800bc49114340004e0000e18a01902ab8baa423c01d02b4f000a0408008020000f0a040020024980ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1c0380000623d800c60000000b8280008c0616008e0861d41850003f30118000d051f46a1b40860964215800100b2b0d8d60020054246a2c800fe70340006e001d954a6790f8009e003b8007800000988a06160e400751500000002c000a000001b4006124040d86606000a2270491c887642000920027000000000000446e2a15cde3439190223e0b8686205070b4bc33079c4f03a001d0822f0c808422e2e880600000000000000000be52410c8003d000003c4c148000873339e8006512000000000000005a400000000001a4000025134f81300214fc252d82008180004341c040400741c20000010580008200804002400000c10000404140c001400040040281c0014027aa5a1cf947439f286873d5490eeea2a1dd14543cfa9a873f5250f6ea2a1cf14543da28a87345150e78a0a1cf950439ea9e853e51d0a7ca1a14f55242bba8a85745150a7ea6a16bd4942dba8a853c5150b68a2a14d145429e282853e5410a7ca9994f55332bb28e657551cca7ca9194f55232bb28c6575518ca7ca8994f551329f2a0653d540cb9a64194f54e419ea94833e519067ca120cf54c419ea90833e511076ca220cf940419f2a6633d54cc6dca598db54b31da20e633f548c678a918cfd51319e2a2633e540c67aa818ed104319f2a6433d54c86bca790d754f21da20e433f5488678a910cfd51219e2a2433e540867aa810ed10421bb28c8175519027aa7204f54a409f28c81b6519026ca3206d546409f284813d531027aa4204f944409f28081ba501027ca9984f553309faa4613c548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f553209faa4413c548827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310da20e213e548427aa9084fd51109e2a2215f53442b8a6885bd4910b629221b4414427ea8084f15010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xb0002800e00068091880641408000010003000000832a000c8002200001600000000000048000098ab9c01e0040020000408d18552d0e3661943438d18553d0a3661943428d185544ca3860551328d185540cb2652107318b588548c6356510431a558c410c71653107218758c54886356510421a958841086346154c408d185521023461553308d987548c23461553208d98754883145310510c9148414423661d50108758c540422d6215010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s2K5 (880+((h/16+packedAt s2K5 (768+(h % 16)*7) 7) % 69)*7) 7
  | 4 => packedAt s2K4 (3970+((h/44+packedAt s2K4 (3618+(h % 44)*8) 8) % 194)*9) 9
  | 3 => packedAt s2K3 (1036+((h/8+packedAt s2K3 (988+(h % 8)*6) 6) % 58)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 1 => 0xe07fffc07e0fc1ff0f83e0fffe1e0781d27ecc
  | 3 => 0xff83ffff800ffffff003ff07ffe007ffe38f0f
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x21000889100200002284a108802290a404b055
  | 1 => 0x4b199187249492cb05a168d3b214350cd256cc
  | 3 => 0x862aa2120d29315550425a4555404659630b0a
  | 4 => 0x145344244981a5a69968108669996011b80da0
  | 5 => 0x1863873871ce39f8ee739ce071118461ffe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36723
namespace PEqualNP.Outside.L_meta_36723
open PEqualNP.Outside.L_meta_36723.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x1523563c01b00289800010c1700793800e212030024c80207c0215044681007402600003000a4900000940142a014803868622040070b2c000080380007140200903ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x802b00108005a0298189a294030000198d0026970000000f2780068912849eaba4801e001d801d00001c95000100001a00282a800b23aa00001b8004221b29000380000da11f13089926259002a500078011ac802c1c000ea318968a00138015870a9a8b8021a8800820948627120c18110e0c800024000f979605001f82000042c0408080000000c1000000008b000183c0408000804000814040c00027ca3a1cf55243bba8a87745150f3ea6a1edd45439e28a87b45150e68a2a1cf95043bba8a85745150abca6215754c429f2a6653d54ccb3a87995d94732baa8e659d434ca7ca8194f550329ea9c833e51906bca620d754c41cf298833d531073aa620c754c419f28883b6511067ca998cf55331cea1e636e52cc6daa598ed107319faa4633c548c67ea898cf15131cea1a633e540c67aa818ed104319f2a6433d54c86bca790d754f21da20e433f5448678a890ed10421af29e815d53d02eca3205d546409f2a6613d54cc33a87184f950309eaa0619d430c2dca4185b54830bb2886175510c27ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb2884175510836883884f952109eaa4213f5444278a88857d4d10ae29a216f52442d8a4886d10510
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x6008000c16680792a9c00000000038050a00002002e9001260004220aca0031800000000000216946150f32c550d51cca946150d328d185540cb146154c41a518543cc70d4354b31a558c41cc726521073187195434c6356510431a558c41c871653107218758c544869563104218d18554cc2946150e30a5185430c30d4354830c550d510c29563107108758e54842956310510c514c41443245210510
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x1a80801020068238a86a96638158e521073182aed2988390d047150d520c20abb0a620a218158c5210510
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2670+((h/30+packedAt s3K4 (2430+(h % 30)*8) 8) % 130)*8) 8
  | 3 => packedAt s3K3 (998+((h/8+packedAt s3K3 (950+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s3K2 (302+((h/2+packedAt s3K2 (294+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 1 => 0xf03fffc07e0fc3fc3e0ffc3ffe1e07034e7ecc
  | 2 => 0xffc1ffff800fffffc00fffc3ffe007ff8f8f0f
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x20800889100200008a1280444022914810b055
  | 1 => 0x658c91872494852c1685a429d21432194656cc
  | 2 => 0x831522120d29225541094a82a54044b28b0b0a
  | 4 => 0xca29c4244981ab9a65a0622339996023e00da0
  | 5 => 0xc31873871ce33e3b9ce7330311180c3fde000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeaa0a0eaeae8e8eaeaa0a0eaeae8e8eaeaa0a0eaeae8e8eaeaa0a0eaeae8e8eaeaa0a0eaeae8e8eaeaa0a0eaeae8e8eaeaa0a0eaeae8e8eaeaa0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36723
namespace PEqualNP.Outside.L_meta_36723
open PEqualNP.Outside.L_meta_36723.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8000015000018d95247400b00013a24aac01c0030002343930a008c000082000f26a0c943001485005c19648003a03c01089007c8111a3c4080004040000240000ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x39500198000000b8000001f80000000010004800000001d80110422aa1c801913ac9c03000000000000002880000a88800c11921aac0c8000002b2aa1241d27a3001080019e00061f0d05a18f0a26a58f80002000001a00000000000000069400208980a60024a380000000298010000000000e800000180800251b2b95801b87a917020d8b179322270014800000000000000e001280002800000700029880050000000016891600001e80000001c04000c040c0408000804000000000004000400000004001408027ca3a1cf55243bba8a87745150f3ea6a1edd45439e28a87b45150e68a2a1cf95043bba8a85745150abca6215754c429f2a6653d54ccb3a87995d94732baa8e659d434ca7ca8194f550329ea9c833e51906bca620d754c41cf298833d531073aa620c754c419f28883b6511067ca998cf55331cea1e636e52cc6daa598ed107319faa4633c548c67ea898cf15131cea1a633e540c67aa818ed104319f2a6433d54c86bca790d754f21da20e433f5448678a890ed10421af29e815d53d02eca3205d546409f2a6613d54cc33a87184f950309eaa0619d430c2dca4185b54830bb2886175510c27ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb2884175510836883884f952109eaa4213f5444278a88857d4d10ae29a216f52442d8a4886d10510
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x39e2aa00692671a0120003080000020008ae000004a00016c2c51881000004028134302946150f32c550d51cca946150d328d185540cb146154c41a518543cc70d4354b31a558c41cc726521073187195434c6356510431a558c41c871653107218758c544869563104218d18554cc2946150e30a5185430c30d4354830c550d510c29563107108758e54842956310510c514c41443245210510
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x80180012a00a8238a86a96638158e521073182aed2988390d047150d520c20abb0a620a218158c5210510
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2670+((h/30+packedAt s4K4 (2430+(h % 30)*8) 8) % 172)*8) 8
  | 3 => packedAt s4K3 (998+((h/8+packedAt s4K3 (950+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s4K2 (302+((h/2+packedAt s4K2 (294+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 1 => 0xf03fffc07e0fc3fc3e0ffc3ffe1e07034e7ecc
  | 2 => 0xffc1ffff800fffffc00fffc3ffe007ff8f8f0f
  | 3 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x20800889100200008a1280444022914810b055
  | 1 => 0x658c91872494852c1685a429d21432194656cc
  | 2 => 0x831522120d29225541094a82a54044b28b0b0a
  | 3 => 0xca29c4244981ab9a65a0622339996023e00da0
  | 5 => 0xc31873871ce33e3b9ce7330311180c3fde000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae8eae8eaa0eaa0eae8eae8eaa0eaa0eae8eae8eaa0eaa0eae8eae8eaa0eaa0eae8eae8eaa0eaa0eae8eae8eaa0eaa0eae8eae8eaa0eaa0eae8eae8eaa0eaa0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36723
namespace PEqualNP.Outside.L_meta_36723
open PEqualNP.Outside.L_meta_36723.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x210a4c0000040a82000000d5000000006071b000000000004804c0000600000000000ca2180001c0028023520000428000242c0001102740000000903007800b000000000000004000000345d2804e7c0080e3c000000000001000c3810004001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930ef99261dd324c2fea2985f14530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa218778c430ee188617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83dc85907b50b20f719641ed32c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51883eca3105d94620bea8c41f551882eaa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42483dc64907b4c920bfa8a417c51483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2107b88420f6108417e50083de40107e88020f690041f920082fea9885f95310beaa6217c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c43ee83887d90710faa0e21f441c43ee63887d8c710fa98e21f431c43ee43887d88710fa90e21f421c43eea9887d95310faaa621f454c43eea7887d94f10faa9e21f453c43ee87887d90f10faa1e21f443c43eea5887d94b10faa9621f452c43ee85887d90b10faa1621f442c43ee65887d8cb10fa99621f432c43ee81887d90310faa0621f440c43ee61887d8c310fa98621f430c43ee41887d88310fa90621f420c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085d54610bf28421f710843f621085fd5110dfaa2213f54442fca8885f55110be2a221bc5444278a8885fd4d10efa9a215f53442fca6885f54d10be29a21dc53442b8a6885fd4910f7a92216f52442fca4885f54910be29221ec52442d8a4887dd0510fb20a21f541443e882887dcc510fb18a21f531443e862887dc8510fb10a21f521443e842887ec4110fb08221f7544436ea8887d95110faaa221f45444368a8887dd4d10eba9a21f653443eaa6887d14d10ea29a21f743443ec86887d50d10fa21a21f752443cea4887d94910faa9221f452443c8a4887dd0910fb21221f542443e884887dcc910fb19221f532443e864887dd4110f9a8221f740443ec80887d50110fa20221f730443ec60887d4c110fa18221f720443ec40887d48110fa102217f54042fca8085f55010be2a0217f53042fca6085f54c10be298217f52042fca4085f54810be290217e51042eca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32bf29065df320cbdc6419774c832f699065cd320cafca2195f54432bf280657d500cafca7a0f794f41af29e837d53d07baa7a0d754f41bf29683ee52d06dca5a0df54b41f6a96836d52d06fca1a0df54341beaa4837e53906faa720efd0e41dea1c837e52906faa520efd0a41dea14837e519077e8320fdd0641bf284837d50906fea6a0df14d41bfa92837c52507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083bf421077a8420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598fb94b31b7296637d52cc7daa598db54b31fba0e63f441cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63de438c7ba8718df94a31bea9463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f790c31eea18637e520c6faa418f7cc831ee990637e510c7ee8218fd10431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21ef29e435e53c86faa790f754f21aea9e437c53c87ee8390fd10721fb98e43f431c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ee42887da8510fb8ca21f6994437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c53487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fb90821f6a1043ee32087da6410df94421fba0843f441087ee6210fd0c421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa4817e53902faa7205f94a40bea94817e51903eca3205d94640bea8c81f551902eaa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a817c51503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3bc87987750f30bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c3eca3185d94630bea8c61f5518c2eaa318778c630ee18
  | 2 => 0xf5352a681ea3f4fc6f8001ed2d4668b49d1336888790b633c87d0a86e37e7100025a194b716f1020001506a02b36272ce4a3757490d039e0368a7d428a20000000017d0a670c000001201b4001f600082c468032e6848002843be0303d01456a2cc0009f14209c7986f4d045890000314000000d853c224681ca0126585e91e4c0a2c4c13831e0017200047c2740003b5b42941c000000a51489c50240005d8840000016c8fe3fc7b880a993c6b08bc1a8548280841ac1b87dc332d036e114f89674ee5b56b23c0001a46e8001ce2fc9500006c5b8f6141000568f4183000174b780024a00000166000044000002c8188a01620fe000000005a65d40005b000564002212f24cc098180101e0100000816058020280202806018080401e0100000004000180004a048060100c300060000004004000040480a03014000320081c1b802018000001e02804000000402e008060680a0300818800008060087c01040050020d800030040806c0600202006008020080e000080000200002008080780a0180805806028000080e0a002088160000600000000040080802016000040a80001004158260000c0101000800048000080007038000000100a008020102200820108000080011802008040280002006058120680207800038040882a00000020b40180a0383a04806000000180000000018020080a008080284200026000000380a0180000004048000802e0080000000048b80784c0207e00022108000b8000d0060480200800058000088e068300701214802128160081600df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543fba8a87775150ef8a2a1fd14543ba28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a85f75150aeea2a15f14542fa28a85745150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842d6a10857e5110afaa2215f94042bea80857f54ccafca9995f55332be2a665de43ccbba87995f94732bea8e657e50ccafaa1995fd5232bf2a4657d548caf8a9195f54e32bf29465ee428cbda851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265de434cbba86997b90932f6a1265ef324cbbc64995fd4532fba8a6577514caf8a2997d14532ba28a657
  | 3 => 0x54099c00075000000e0026000aa41e2234986f4001650a09616d874000000000000000cd2280000a3495418122000000000188000000001229f07c8a72f60d55d9321d67400c84b5a20000014424e5d904a64000a00002905680002501a27c0000006019c8a8d980008640c0010b100390000b80f60002e2ca0000000da8933a544000a8496b84002bf2d84d08980004a61c002484886e4eba39000af00000000000141170000000ca9f84b61644084110a57d6318c16e35d712111589a9139b839e3a00023656e38d0017e59600060000000001629710000003b0de0008cc418f80008f40027911c0015c956080000e40c11f616106a084d8315578780c20006d24a21e0211327448e154f7ac90003b8961fa382584c41a421c0a40000f1fe23c5a0494048ac959bc27e99546a1c4500c4399f94807d0f08be20c000d11d602e004001fd000028241151dab003591d2a02a930a3b0e4000001804e66846b19408ca295e90039a5c95605e238aacfd95c2240a0530631963c54e15852c6354ea1034a50cc300b49c0b40000015a08c9798b46a0fcaa8445063a42611900e11c579b2320a99591f35267500009b0f2b7c000820006256202015c3080021d5362c4000004d60010b9471de2ac0013d00048cdb0004ac9080001c000a20852cc26e614a11c7172754af000482000001f00004894710400000070000398ac56ba04074b396c04d0d0770cca0e2507a5191aa07c8e96a0e5198864bd0001b6b1c5487733037c1912906853cf518e25c00033968294760f2800236b5560abe3c46bc6308b40222096a343fe0dc0013124ca614ba703f85dcda8181603b102a594a23207d0f74280b1370cf4f60780e8f546283c461490d81490d1185a4435299c200c934ee9da3c8a30002253bc68cf91a7008a3d408b204841c002664c4278909db4401590c24645e0885d16012865c849ce55a444b58004d2764bf8704bc000001ab5464ed619ae290828151eb0008300985f50e0015502f4600394a9b019a31cce14b1aa74caa29210e8b5570151e09d87315320a649379ad470324d32b30c830d1227a02056c8f9e73224d8aba5c1f894967ac84924f0dda291b25148d05703e0c00021e1489fc8a2130b43a8dd1e60f8858a32500000b8a60fd0041f4921822e82704926d14686c9ca6354a1447a1174e24e806a553a4b343f14e4ae000002e310c3440010c54ea18be08a542001019c62c634ca90000009c8002b612a57498000326680000971788b0389354a88182122e49e610270004ea0852e8f61340000000016a1a8cf81612cb804c94d5449f55825f0729e0278000ca0015c0e21c224d6e9
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3534431c54d4d10d5587534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d4910d9587524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524436561149109d99741442d663d0510b558f414435453d0510b998b41442e562d0510d914b414433454905109d19541443375410510d514c414436452105109d99731442b664cc510ad593314433454cc510b998b31442e562cc510d914b3144354538c5109d1953144334540c510d5d4c3144364520c5109d99721442b664c8510ad593214433454c8510b598f21442d563c8510d514f214436452885109d19521443345408510d514c21443675208510ad99254442d66395110b558e54442e66295110b958a54442f16095110b5d8d54442d46355110b9d8954442e46255110bcd8154442b66515110cd994544439754d4d10e515353442b66494d10ad59253443345494d10b598e53442e66294d10b958a53442f16094d10add9153442b46454d10b9d8953442e46254d10bcd8153443345414d10b599453443566514d10e5d5053443565414d10d515053443945414d10c515053442776550d109d19543443954310d10b998843442e56210d10bc98043442f16010d10e9d5352443a454d4910f1d4f52443c453d4910ad99252442b56494910cd15252442d66394910b558e52443545394910b998a52442f16094910add9152442b46454910b5d8d52442d46354910bcd8152443345414910d514c52442e66514910d999452443a75414910d995052443645414910e915052443245414910f1d4c52443665314910d914c52443c45314910d114c524427765509109d19542442d66310910b558c42443a54210910bc98042442f160109109dd953244274654c910ad99032442b5640c910f14c832442f2600c910bc580324433754d4110cd153504435753d4110d514f504436752d4110d914b504437265d4110ecd5350443b054d4110f4d4f50443d053d4110f8d4b50443e052d41109d99640442766510110b598c40442d56310110b998840442e56210110ec5004044276658c1109d99430442b6640c110ad59030442e6620c110b958830443d1300c1109d99620442766508110ad99020442b56408110b598c20442d56308110f8480204427661d50109798c540425d63150109b988540426d62150109d984540427661d4c108f990530423d6414c109b988530426d6214c109d984530427661d48108f990520423d64148109798c520425d63148109d984520427561940109e596100427765440109ed9510043725144010
  | 1 => 0xc25e63150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d5454830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430c7552310c34d528c430d5546310c31d540c430d3548310c2d9600c430c7553300c34d52cc03097d95300c31d544c030d3549300c27b654c0309dd8554c827461553209798c54c825d63153209dd8553c82746154f208f99053c823d6414f20cb15142c834c534cb209d987548827561d52209798c548825d63152209d984548827561152209d987538827561d4e208f990538823d6414e209d98453882756114e208fd91518823c645462097d8d518825c6354620cdd9151883346454620d5d8d51883546354620d9544218825f63551209718d544827761551209d185544825e63151209758c544823f6454d208f19153482776154d209d185534823e6414d208f590534826c6550920cb151424826c654c920d314d324825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510832d5488420d354e21083655188420cb550210834d5308420ba580210832d54c8020d354f200826f6548020cb551200834d53480209ed95200825e63953109758e54c426e62953109b58a54c423e6494f108f59253c426e6294f109b58a53c423e6494b108f59252c425e6394b109758e52c42d663d0710b558f41c42e662d0710b958b41c42b664cc710ad59331c42e662cc710b958b31c42b664c8710ad59321c42d663c8710b558f21c42f160d5310b598e54c42d56395310b998a54c42e56295310bc58054c42f160d4f10ad99253c42b56494f10b998a53c42e56294f10bc58053c42776550f109d19543c43954310f10b998843c42e56210f10bc58352c42b66494b10ad59252c42d66394b10b558e52c42f16014b109dd9542c42746550b10b598c42c42d56310b10e950842c4277654cb109d19532c42b6640cb10ad59032c43c5320cb10b598c40c42d56310310b998840c42e56210310ad99030c42b5640c310b998830c42e5620c310ad99020c42b56408310b598c20c42d563083109798c548425d63152109b988548426d62152108f990538423d6414e109b988538426d6214e108f990528423d6414a109798c528425d6314a10cd587544423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d5
  | 2 => 0x6194032d34c9500cb576154f41d394e52d074d5394b41d394d52d074d5354b41d9d8552d066e6294e419b58a539071e5350e419798e529065d6394a41cb949429069d63d0641ab58b41906b76150c41add85421069d63d0441ab58b411063f65504419dd95411066e62d53319b58b54cc73761553319b98854cc66d6215331cb95252cc72d5494b31cb95152cc72d5454b31d9d8552cc6e662d0731d994b41cc7355410731d994841cc66e62952319b58a548c71e5450e318f992528c63d6494a31d3949328c69d64cc631b358b318c65d63951319b98a544c66d62951319dd85544c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c31c7151430c6d76150c31b5d85320c6d563d0431b998b410c6756510431e550c410c69d64cc431b358b310c65f654c4319dd95310c65e63d53219758f54c873761553219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f21d5d8553c863e6414f218f59053c86d663d0721d594f41c87355410721d594c41c86b664cc721cd95331c8736540c721d554c31c865e63952219758e548863e6494e218f592538872e5450a21d394d32886ad64c8621b358f218865e63951219758e544866d62951219dd85544863e6494d218f592534866d6294d219dd85534865e63150219758c540867a60150219e580540863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520866d6590821cb15142086e761508219b596320874c534c821b9d8532086d663d0421b958b41086756510421e950841086b664cc421b958b3108675650c421f14c831086ad64c8421b358f210866f65484219dd9521086776154f409d18553d02776154b409d18552d025f63546409718d519026f62546409b18951903576354640d518d51903676254640d9189519033551106409b988535026d6214d40c714d435025e63149409758c525032c5250940d394e521034d5394840d394d521034d5354840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440c754e411032d5290440cd546411031d5310440cb54841102b96010440c754f401032d52d00408fd95401031d5350040cb549401027b65500409dd8554cc27461553309b98854cc26d6215330c715143cc2776154b309d18552cc27661d52309d587548c26e62152309b588548c27661152309d584548c23f64546308f191518c26f62546309b189518c3376454630cd191518c3676254630d9189518c355510c6309bd89544c26c62551309dd85544c27461551309b988544c26d621513097195434c31c5450d308f990524c23d6414930d3149324c26e62d50309b58b540c27661d50309d587540c23d65950308f990540
  | 3 => 0x8008000000020100100000201c0200700000003803000004000000240000180101a0200000800005c00000002008000000140100680100803c0000804400c000010000140000d0000000480001600403804014000050010000040100000000000000002008040010080240180000202001001002008048060000080a0010180000e8030140000080000001c0100500000c01000000004058000120140300900400c000110080000000501e00005801014004000000140000100200e000058010060100000500202c010030000000080000402807004014018050020000000100000203800000002000020000180240100000000c00000020000000050020a4030000140000000000000c0180300000000801000024018060040000001b0020040080000602c00001008034010020080000000700400c0080100001800002004040000009d98650d0e7561943439d9865090e7561942439b98b5150e6d62d4543d998b5150f6562d45439d5835150e7560145439b9885050e6d62141439d9845050e756114143a75924310e3f6550c4397d954310e9f6550c43c7d954310f976150c43e51854310f8d4394843c750d5210e7761548439d1855210f8d4354843cbd0d5210f4e4354843cb50d5210f4d4354843c350d5210f676154843d91855210f1d43944439d9865010e756194043c750d5010eb46150f429d98650d0a7561943429d9865090a756194242c714d4350aac6250d42ad1854350a5e63d45429758f5150b5663d4542d558f5150a7560d4542cdd0c5150b3543145429d5805150a5e63141429758c5050a7661141429d5845050a776154c429d1855310b576154c42d51855310b1d53d0842ab5924210b4d53908428fd954210b1d53508429bd954210b4d5350842abd954210b2f6550842e394d4210b2d5350842e354d4210b0d5350842e9d854210ba46150842cb50a5110a7661940429d5865010b2d42540429d98754cca7561d5332c715143ccad46150f329d98650cca7561943329d987548ca7561d5232cb151428cae46150a329d986508ca7561942329d986544ca7561951329dd85544ca7461551329ed81544ca78605513297195434cb1c5450d32b3189434cad46150d329b195424cb2c5450932b318d424cb8d4350932b9185424ca3e64d45328f593514cb3664d4532cd593514ca7560d4532d590c514cb554314532d9908514cb6542145329d580514ca3e64141328f590504ca7661141329d584504ca3d65950329dd85540ca746155032cdd85540cb3461550328f990540ca5e63150329b988540cb1d54cc832cb552320cacd638c83297d95320cb1d544c8329bd95320cb2d544c832b3d95320cb4f654c832d3d51320cb8e544c832d3551320cb8d544c832c3551320cbc7614c832f1185320cb4d32944329d986500ca75
  | 4 => 0x6e9d8378955524698a03f4a6950fe8d13320ad7d000000000c43135f2000000e2358b38f5070000b30d4a0901e2e4ad8002823f97592c4b2348901384862f43a8f30006d5559710000015c9ca4da001178002307b8980004ea0014d00036c000f60df1ce744df1e6000295710004e493400000000000001750007353a12645c0000019d5d80000002f000000f380058a4b915ad422c3b800285012580788055dc000dd93c2de0001327352e7e8ee21542072d1f0d50002282b9920ee7a49cae52a423520800000601308002d23a8000a963084d030002f61000021d4300012b22157a09c828003780000030600000112a11000a7cbd06d3aac381a000404320498005a6455132892140a41ba6f06a000f78900c252c1109111229c2c00034aa044928f53a0011009b31e40c0c1d92c233cc9800000c54000000009700004d000001788485c228c00000312870c21360008d11b12a000001780780002500000030460458a5f0000011c913592001842dd58076150adf0ca000779b923e0746a2bb000218389e000094039800000ad007148000b1d83800200000fb0ae62027068000000b68000004ce5d00f0d8294ab8098002aa0008e80057ca500026b0222d82e8000000000014f0008ed4905100063812a8d320000001c40861503f00000014c248f54fc534cf9c2188318a3228306484271cf28835cfa20d37e9b8e90c95902b40580440e1540387f0ac62c000000000000030b60a89d8b84f42e658000000004207323103e384ab0005e86885f2353a8b701e2ac00000000083000a4cf9a2c0004f8a118550e8c94a8083f60ec7d2785fe444229281809a8979eb428a20000000009996ca0c2b25c09d9982d6035361b01b20003416e38e00000252000b5d300694c491caf8ec380578093001409dc9a9a655e001821ed000000000000006c800060000b60aa00000000158842116570a4ad2000a0c168ac000b580002e000000000005da0c145af63540000030a000b9c54311000131848c32d859400000054a108710f0ec0f423800546268f200000006cb3800148670002c14f61041980046600000000000000000000000015900047400043af74a2000000aa0386e000000000000001fe000a188a00023c0000000015e3a0030f63ee0e03180038a6800c83a000888e49241c68f440a085e66b4b31d74e00000000039800000000000000001ba1e42ec0012d0000018683919a8b4440e0000000282f84980015e00056cc3c0027f2ee000000000000017415a2380012b8000000003e0003ac8fc001290a4170cda040002754005f3b6040002d04ca000d7176000990001fc17823c2c8850fac64d78dd2a61293c80c2807c981800432bf4001b72c40020040100001200000004002024008000000000100a0020240001d0020000100100202000800
  | 5 => 0x6685aa55406000a8a2308848d029a7184bf0f8acb0002dc0020f4fa5e44607239c4d00003e3a60012d000584000000ce00000122800000a9c00000000000001de0000040030c22e3e0000c71b45cd7aa44000b10000001320000025e1944492790400000065800000000e82bf0005fc0022400000000000000000000000000017f0001f20000010700077d730000005f04b00017eb3c00000000000ac000048654000001f6bbc2310b480001512480000011e00056e98cd08f73467a033ade3f0080b22c61e000138ab0000000511f0236928a3a583c400c69a291684acbe8ba5c00b152a3837a4c891200000000d98002a01e54c000000050000000000000000000049c118005f6635500001420000000059aa58000003c60000021a1d2b5400080050000ca000062938002303500d85921b0008dc72aa424a7e43da9e55479400143386a309fa69624ae800066402acd0717800082d5300053287c75800000000002d150412d258002d48780000000000000000000a70608004f8000b18de0006d16d862204000c89332e40000018c00072032290000b280025b3b42087f9ff38c9241906e13ea28848172fc1a96199e5704f4599192d00014d8cc2ba858002b502a5387a00030e001050000008a974af2274000000fd11c16c830001da62898aa84d0a447e25d000000000001b600000000000000000c5604000ab9ab13c1798085a32e00835897424a38eea7a0001e8fa945218210109c155a784882e45d4358d20a629843400000000001231b10d8000000001c890800186000000b680a0000698b0ab000000000dc2022e00b074000b8c4c0b02
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4a001c53002d0033120029233e3d000a0000002400094227000000000055000000004432571d4d00112a563f00381a13505a0007000000002f3c00000000000000220031480000432b002630000000010521201800001716024500192e0000004036044103003a004b2c4e51004600283b54000035151e390e003400000000000c0010005908495200250000000000004c001b000b00064f0d00141f580f3747038001008103818001008003810001008001000100000183810000008000e15431855210f83b8a86a9087c11c54354843e0a87b0aa421f05431855210e9238aa6a1085c1dc55350842e08e2a9a842170553d854210b82a98c2a1085431d54350932c18caa1a84995847150d424cb42a18c2a1265c150d4214532a1aeb2a2641954471551320cb83b8aa899065c11c5544c832e0aa9b0a641970554185320ca86b94a6a1c83435ce5250a41a1ae52a28718d0d74949328c686b90a8a1863465c05450c31a1ae72a28510d0d7494d3288686b98a8a10434a5c05450821a1ae829a6410d497014d3208722318c4a8c81435c85350d40a1ae629284a0619535804110314a92c020881435c85450f30c48c8312a31850d72151434c286ba0a49926186551600c430c92a4b00621850d7315142c8286ba0a699641851906354620a1ae62a2849050d7414d3248314aa2c0108419254d6008420d0a86b1087886856350842c4342b2264196219114e62d0510c8cc629682886245498b3144313320a598a218515263c8510c2cc829e42886245498a534428b3a4a829a21519ca5414d10a28eaa188688464755884344342a1ac421a21a450d6010d10e08a829ea4886145498e524430b320a729221499d25414910a8ce72a0a48870454d4c52442933a4a629221519ce5314910e0ea8298a4887045414c524422a3aac621221491d54210910d0ac6a1084886a142580424421a3aac819221511d5320c910d0ac899064886c1325803244348b1a8020221a85894010110d22c898060886c1624c03044350b224010221b058d2008110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc9000001a0e12880b500860022a0686dc543548439078750f6154843a0686dc553508429078754f6150842a0686dc5544c83290787553614c832a048550d6210d10c047550d6210d10a048558d4210910c047558d4210910a0485591320c910c0475591320c910
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 741
  | 4 => 794
  | 3 => 91
  | 2 => 12
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
  | 6 => packedAt s5K6 (770+((h/14+packedAt s5K6 (672+(h % 14)*7) 7) % 96)*7) 7
  | 5 => packedAt s5K5 (22477+((h/247+packedAt s5K5 (20007+(h % 247)*10) 10) % 890)*11) 11
  | 4 => packedAt s5K4 (33076+((h/264+packedAt s5K4 (30172+(h % 264)*11) 11) % 1152)*11) 11
  | 3 => packedAt s5K3 (4699+((h/30+packedAt s5K3 (4459+(h % 30)*8) 8) % 160)*8) 8
  | 2 => packedAt s5K2 (740+((h/4+packedAt s5K2 (720+(h % 4)*5) 5) % 17)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc1ffffe0ffffff81fc3fc3fffc3ffffd11f1ff
  | 1 => 0xfe07c3ff03e1f0fe3fc3fc383fc38382eececc
  | 2 => 0xfff803fffc01ffffc003ffc03ffc03ff0f0f0f
  | 3 => 0x3fffffe00fffffc00003ffffc03f00ff0
  | 4 => 0xfffffc00000000ffffffffffc0000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x44100022080000000404404884048888005055
  | 1 => 0x8cb184463942a1161c41c4119c41191866c6cc
  | 2 => 0x1062aa8850d548aac222aa822aa822730b0b0a
  | 3 => 0x39453310a2906acd6aa8220433327023b00da0
  | 4 => 0x2186221cc3198cf1b333332702204043dda000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36723
namespace PEqualNP.Outside.L_meta_36723
open PEqualNP.Outside.L_meta_36723.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x7e1004658700430d68d17b87892094f44440001d519d6ec3c0401f52ae42a2eaa28050a630b002800000497472d6959b188365c4c84a1529808889300bc0300001348005592b100438b14084000214592121c0250024581080007ff5301dfd4c05fe5301ff54c017d53017f14c05fe43007f50c05fc4301ffd4803fe5201ff54803fc52017fcc803fe32007f4c803fc3201ffd4407fe51005f94407fd5101ff144077c51017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x9c200edfd4e1006ffca70803bfd5384001bea9c200dff14e1006ffc8708003fd438401bfe21c2004ffd8a10025fec508013fe62840037f3142004ff58a10005fac508013fc62840097e314200effd4a10067fca50803bfd5284019fe294200dffcca10067fc6508003fd3284019fe194200bbf58610077fea30803bfe5184001bf28c200eff54610077f8a30803b7c518401bff98c2000ff8c610007fa6308037fc3184019ff90c2000ff88610007fa4308033fc21840097f3042004ffd4210027fca108013fd5084009fe2842004ffcc210027fc6108013fd3084009fe1842004ffc8210027fc4108013fd2084009fe1042004ffc4210027ee2108003fb1084017ffb2a200bbfd9510006feca880027f6544017ff32a2003bf9951005ffaca8802efd6544017fe32a2003bf1951005ef8ca8800e7c6544001ffb1a2000bfd8d10007bec688002df6344015ff31a2002bf98d10007fac688002fd6344015fe31a2002bf18d10007b8c68800adc6344017ffa9a200bdfd4d10057fca68802ffd5344001bea9a200aff14d10057fc8688003fd4344015fe21a2000ffd8910005fec488003ef624400177b122009ff9891000dfcc488003fd62440017eb122009ff1891000df8c488003ec624400376312200bffd491004ffca48802ffd5244013fe292200affcc91004ffc6488003fd3244013fe192200bffd451005feea28802ffe5144001bf28a200bff5451005ff8a28802f7c5144017fa28a200bdd14510057fe6288003fe3144001fb18a2000ff4c510007ea628802bfc3144013ff90a2000ff88510007ec4288003fd2144001fa90a2009ff0851005ffea088013fe5044017fea822004ff14110057fe6088013fe3044001fe9822004ff0c11004ffe4088013fe2044001fe9022004ff08110007fe2088003fb1044009ff0822004fd84110027feca08012ff6504009ff3282003bf99410027faca0801efd6504009fe3282004bf19410027fec608012ff6304009ff3182002bf98c10027fac608002fd6304009fe3182004bf18c1003ffea60801f7f530400dff2982007ff54c10006faa60801bfc530400dff2182000ff50c10037f88608013ff62040097fb102004ff9881000dfcc408013fd62040017eb102004ff18810025f8c40801fff520400bff2902007ff5481002ff8a40801bff320400bff1902000ff4c81002ff86408022fe610400fffa882007ff94410006fca20801ffd510400ffe2882007df14410037fe6208003fe3104001fe9882006ff0c41002ffe4208003fe2104001fe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0x3fd5388001bea9c4013ff14e2009ffc8710003fd4388027fe21c4001bf58a2000ffea510007fe5288003fea944001ff14a2000ffe6510007fe3288003fe9944001ff0ca20027fec310013fe61880017f30c4004ff58620005fac310013fc6188029ffa8c4014ff94620006fca310053fd5188029fe28c4014df1462009ffe6310003fe3188001fe98c4013ff0c62000ffe4310007fe2188001f710c4001ff4862000ff84310007ec21880097f3044004ffd4220027fca110013fd5088009fe2844004ffcc220027fc6110013fd3088009fe1844004ffc8220027de4110007fb2088009fe1044004fe08220097feca9004aff6548001bfb2a40009fd9520097fcca9000efe6548025feb2a4012bf59520097f8ca9000efc6548025be32a40039f19520007fec690002ff6348023ff31a4002bf98d20007fac690002fd6348023fe31a4002bf18d20097fea69004b7f5348023ff29a4012ff54d20006faa690047fc5348023ff21a4000ff50d2008ff88690012ff6248003ffa924001ff9492000ffaa490007fc5248003ff9924001ff8c92000fdc6490007fd3248001f69924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148025ffa8a4012ff94520006fca29004bfd5148025fe28a4012df1452008ffe6290003fe3148001fe98a4011ff0c52000ffe4290007fe2148003fe90a4001ff0852000dfec09004bff5048009ff2824012ff54120027f8a090047ff3048009ff1824000ff4c120027f86090007ff2048003fd9024004ff88120027dc4090013fc2048009f61024001fe08120047fecb88022ff65c4011ff32e2003bf99710047facb88022fd65c4011fe32e2003bf19710007fec788002ff63c4021ff31e2002bf98f10007fac788002fd63c4021fe31e2002bf18f10047fea7880237f53c4021ff29e2008ff54f10006faa788043fc53c4021ff21e2000ff50f10087f88788003ff62c40017fb16200fff98b1000dfcc588003fd62c40017eb16200fff18b1000df8c588023ff52c401fff2962008ff54b1007ff8a588043ff32c401fff1962000ff4cb1007ff86588023ff51c4011fba8e2008ff94710006fca388023fd51c4011fe28e2008df14710047e8a3880237451c4021ff98e2000ff8c710007ec6388003fd31c4001fa98e2010ff0c71007ffe4388003fe21c4001fb10e2000ff48710007ea438803ffc21c4011ffa862004ff94310047faa188013fc50c4021ff9862004ff8c310007fa6188013fc30c401fff9062004ff88310007fa4188013fc20c4009ffb2c2004bfd9610027fccb0800efe6584009bf32c20039f99610027facb0803afd6584009beb2c20009f59610027f8cb08012fc6584009ffb1c2004bfd8e10027fcc70800afe6384009feb1c2000bf58e10027f8c708012fc638401dffa
  | 2 => 0x21007fac090803fc60484097e302421dffd41210effca090877fd504843bfe282421cffcc1210e7f86090807ff2048403fe1024204ffd9630025fecb18013fe658c0077f32c6004ff596300ddfacb18013fc658c0097e32c6004ffd9230025fec918013fe648c0317f3246004ff59230005fac918013fc648c0097e324601bffd52300defea91806bfe548c037feaa46000df552300d7f8a91800afd638c005ffa9c6002dfd4e30017fca71800bfd538c005bea9c6002ff14e30017fe871800bfe438c005fea1c6002ff10e30027fec518013fe628c0037f3146004ff58a30005fac518013fc628c0097e314601bffd4a300cffca51806ffd528c033fe294601affd0a300cffc8518003fd428c033fe2146002ffcca30017fc651800bfd328c005fe1946004ffd8630027fcc318002fe618c009feb0c6000bf58630027f8c31806fff518c037ff28c6000df946300dffaa31806ffc518c037be28c601affd0630007fc8318003fd418c035fe20c6002ffcc630017fc6318003de318c005fe98c6002ff0c630017b86318067ff218c001ff10c6000ff486300cff84318012fe608c009ffa846004ff94230027faa118013fc508c009ffa046004ff90230027f88118013ff308c009ef9846002fecc230027f86118013f8308c009ff9046004ff082300bffeca9805eff654c02fff32a6003bf995300bffaca9805efd654c02ffe32a6003bf19530007fec898002ff644c02dff3226018bf99130007fac898002fd644c02dfe3226018bf191300bffea89805f7f544c02dff2a26017ff55130006faa89805bfc544c0097fb1a6002ffd4d30016fea69800bfe534c005fea9a6002df54d30017f8a69800bff434c005ff21a6002f790d30017fa8698003dd434c005fe21a6000ffd8930005fec498057fe624c0037f3126000ff589300aff8c498006fc624c02fffa926015ff949300bffaa498057fc524c02dffa126015ff90930007fa8498057fc424c005ff9926002f7cc930017fc649800bfd324c001ee9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c02fffa8a6017ff94530006fca29805ffd514c02ffe28a6017df145300b7fe8298003fe414c001fea0a6016ff10530017fe629800bfe314c005fe98a6002ff0c5300affe4298003fe214c001fe90a6015ff08530015fec09805fff504c009ff2826017ff54130027f8a09805bff404c009ff2026000ff50130027f8809800bff304c005fd9826004ff8c130027bc6098013fc304c009ee1826002fe0c1300affe4098013fc204c009ffb2c4004bfd9620027fccb1000efe6588009feb2c4014bf59620027f8cb10012fc6588009ffb1c4004bfd8e20027fcc71000afe6388009feb1c4000bf58e20027f8c710012fc6388029ffa9c4014dfd4e2009ffca71005
  | 3 => 0xe1846202f70c23111ffe411888ffc208c445ffb2a6222bfd9531006feca988027f654c445ff32a6203bf99531117faca9888afd654c445fe32a6203bf19531116f8ca9880e7c654c401ffb226200bfd913110ffcc898862fe644c401feb226200bf5913110ff8c898862fc644c445ffaa26222dfd513110ffca89888bfd544c401beaa26221ff15131015fec69880bff534c405bfa9a6202ff94d31017faa69880b7d534c405fe29a6202ffd0d31017fc869880bfd434c405fe21a6200ffd8931005fec498883fe624c4037f3126200ff58931107f8c498806fc624c445ffa926220ff94931117faa498883fc524c443ffa126220ff90931007fa8498883fc424c405ff9926202ff8c931017fa649880bfc324c4057fb0a6222ffd4531117fca2988037e514c445fea8a6222ff14531116f8a298887ff414c401ff20a6200ff5053110ff8829880bff314c405fb98a6202ff8c531007bc629880bfc314c405ee18a6202fd0c531107fe4298883fc214c401ffb026200bfd8131007fcc098803fd604c401fe3026204bf18131117fea09888bfe504c445fea826222ff1413110ffe8098887fc404c405ff9826202ff0c131107fe4098883fc204c43fffb2c421fbfd96210fffccb1080efe658843ffeb2c421fbf596210fff8cb1080efc6588401ffb1c4200bfd8e210f7fcc71080afe6388401feb1c4200bf58e210f7f8c71080afc638843fffa9c421fdfd4e210f7fca71087ffd5388401bea9c421eff14e210f7fc8710803fd438843dfe21c4201bf58a2100ffea510807fe5288403fea944201ff14a2100ffe6510807fe3288403f71944201ff4ca21007da6510807fc32884037f30c421fffd46210fffca3108037e518843ffea8c421fff146210fef8a31087bff3188401ff18c4200ff4c6210f7f86310807ff2188403f790c4201fdc862100ff84310807f42188401ffb044200ff98221025fcc110803fd60884017eb044200ff182210fffea11087ffe508843ffea84421fff142210f7fe611087bfc3088403ff9044201ff0822100fd84110877ff654843b7fb2a4200dfd9521004feca90877fe65484077f32a421dff595210edfaca90877fc65484077e32a421ddf1952101cf8ca90803ff63484017fb1a421cff98d21015fcc690803fd63484017eb1a421cff18d21015f8c690877ff534843bbfa9a421cff94d210effaa6908037d5348439fe29a421cff90d21007fa8690873fc43484037fb124201ffd492100ffca490807fd5248403fe2924201ffcc92100ffc6490807fd3248403fe1924201bfd85210effea290877fe5148401bf28a421dff545210eff8a2908777c5148439ff98a4200ff8c521007fa6290873fc3148403ff90a4201fdc852100ffc4290803ee2148403fe10a4201fb0852100fe84290803ff60484017fb024200ff981
  | 4 => 0x8affc5050c05ff9828602f7cc143017f860a18abff2050c55fe1028629ffd953214dfeca990a7fe654c8077f32a6429ff5953214dfaca990a7fc654c8077e32a6400ffd9132005fec8990a3fe644c8317f3226400ff59132005fac8990a3fc644c8317e3226429ffd513214efea8990a3fe544c853feaa26400df55132147f8a899006ff634c805ffa9a6402dfd4d32017fca69900bde534c805fea9a6402df54d3214fbaa6990035d534c805fe29a6402ffd0d32017fc869900bde434c805fea1a6400f750d32017f88699006ff624c803ffa926401ff9493200ffaa499007fc524c803ffa126401ff9093200fdc8499007fd424c801f6a126401ff1093200ffe649900bef324c803ff1926401f78c93200ff86499007dc324c803f61926401f30c932007fec299002ff614c801ff30a6400ff58532007f8c299002fc614c853ffa8a6429ff9453214ffaa2990a7fc514c853be28a6428ffd0532147f8829900bff314c805fe18a6402f70c53200ffe4299007fc214c803f610a6400ffd8132005fec099003fe604c801feb026400ff18132025f8c0990a7ff504c853ff2826429ff5413214ff8a0990a3ff404c851fe2026402ffcc132017be609900bfc304c803ff9026401fbc813200ff840990037f639444fbf31ca200df58e51004fac72889f7c639444fbf21ca200df50e5113ef887288037f629444dbf314a200df58a51136f8c52889f7f329444dbf194a200df4ca51136f8652880f7e61944073f30ca203dd9865113efe632889f7c319444dbf90ca226df08651006fec1288037e6094401beb04a200df1825113efe612889f7c309444dbf904a226df0825112ffecb18896ff658c401bfb2c62009fd963112ffccb1880efe658c44bfeb2c6225bf5963112ff8cb1880efc658c44bbe32c62039f19631007fec918802ff648c449ff3246218bf99231007fac918802fd648c449fe3246218bf1923112ffea9188977f548c449ff2a46225ff55231006faa918893fc548c4057eb1c6202ffd4e31016fea71880bfe538c405fea9c6202df54e31017f8a71880bff438c405ff21c6202f790e31017fa8718803dd438c405fe21c6200ffd8a3111ffcc518806fe628c401feb146200bf58a3111ff8c518806fc628c44bffa946223ff94a3112ffaa51888ffc528c449ffa146223ff90a31007fa851888ffc428c405ff9946202f7cca31017fc651880bfd328c401ee9946202ff0ca31015fcc318897ff518c44bff28c6200df9463112ffaa318897fc518c44bbe28c6224ffd0631007fc8318893fc418c405ff98c6202f7cc631017ee631880bfc318c405fa18c6223ffc863111ff84318803ff608c401ff3046204bf98231007fac118802fd608c401fe3046225ffd423112ffca118897fd508c44bfe2846224ffd0231127f8811880bff308c405f
  | 5 => 0x640000100201c0000100a000018350000100180303a1280280701400003000044000000010080580780f04e0080000200006c0b816002008000090040040f80800000400000000010030110360640101400200005006002034000020020080180e00a000000000140040200d000068008020060480801e0080002880000800c028000260000180a00e0040000a0180680380000a00c0080b00003001000016014010010040380481601a0b4008030080040001c004030038230160080080702a000000050040241f0000000001180102e0700001400c0080a0010f80a00000000c03c0280001400401001018014178040040000080300005c01002008010018090060000001c00400801009024030018070940000100102600c04011000000190000120100700a004008008070000300180101000c0180000002401003000008008000000000680400e0000180000401c0000003c0280100202c010048010000500180800204c0000900406c05007002000090130080780001b044018300010180000000001604c02005000020070000020040002d0000080380102e02400006002028008110080140000e000000050080120780c803004000058000000001980e0060040f00000001c0001f006000008260160380080000c0180080702c01809816006000070010020080180002c00004804024008010030b009c0d80200200c00000000004000040020080680002000401bfb22a6009fd915316efcc8a98037d6454c5bbe322a602dfd8d53014fec6a980f5f6354c05bfa1aa602df90d53016f886a98037f6254c59bf312a600df58953166f8c4a98b77f4254c59bf212a62cdf10953016fe64a980b5f3254c05bf192a602df0c953006fec2a98037e6154c01beb0aa600df18553004f8c2a98b77f4154c5bbe20aa602dfcc553016f862a98b37f2154c59be10aa600dfd8153006fcc0a98037d6054c01be302a62ddfd015316ef880a980b7f3054c05be182a62cdfc8153166f840a98afff6550c577fb2a862bff9954301dfccaa18af7e6550c073f32a862bff5954315dfacaa18037d6550c013eb2a862bff1954301df8caa180aff6350c05ffa9a8602dfd4d43017fca6a180bfd5350c05bea9a8602ff14d43017fc86a180bbe4350c05fe21a8602f710d430173886a1803ff6250c017fb12862aff9894300dfcc4a1803fd6250c55fe3128601bf1894315ffea4a18abfe5250c57fea92862aff14943017fe64a180bdf3250c05ff1928602ff0c943007fec2a1802ff6150c01ff30a8600ff58543007f8c2a1802fc6150c57ffa8a862bff9454315ffaa2a18affc5150c57be28a8602ffcc543017f862a180bdc3150c55ff90a862aff08543007fec0a1802ff6050c01ff3028600ff58143007f8c0a1812fc6050c57ffa82862bff9414315ffaa0a1
  | 6 => 0xc6f2ad490215073034d0f06f4bb4b707407f8530586720fd4f1c6c81d484017c6b0e344d474cb04029294df10448441346ef15c0d07ecfdc5b6bbd29cf86d748a03b51cc8c056516122077c18a7507343900010006d416c5e6c6824c658d44b28516ab6468884f6a37a30423c0190846688e4c70c0cf490805be244b07224000f3cae0318fc81a8abc6acda9128582d0120aa54444ec4000c60d04900c0311464005108800128cf99174ed0724d282e838a4a2344b787b4baa988ee8e80eaa4c840c000000718000ee4d0800101d1d05900005b4bd60000d63c42ed244f1078aeae928e502582280840001dc4f4fe803626051431a5f4cbd0d4ff0128234b4822eea4422dbc2324beb1b024fb8f30ba40dec1e000a9c00000000103d27113871c000000c7cc8827cccc94c000ba82c8c18fc0000dd80000001c40003d52dcd7800000008e320ba087d0c4c440000004b72c02140010bc000d4c0008900d400049000010e55484c75c0009e41180001800945ea000000d5899076c0006e4da000cf7c15d0ec0348b50587543b9090f9c6f0d882cc5ed0e8b2cafb1dcd1060c86ea68f34804a44d71170825194e08800a3f288f14ae509d264bb868874505d11d0051fad6cd34b9c42c0f661c0011fef4d168496ac2808ce80002b83f892c2a47485ce5a8ac48b89b70409080c4542690000abe000bd037c5b8000074fccfd03887a0e0050ec36448b7520681825cb20f90ec03e2e1ca3c51c4bd104d205d85d52402c27d1280ecd1d86ec4d8000778264c6400049f1f91b20002dc7b0000c8c000bd2a98a8a5963281ec698c1a59312c4ca2252f4d18e3c4e88c40bd1fd1181946e2578c8044f1b4a5099400000059867e000230d5c0eeb64b409b4000000dac000e44bdc49450c0002a825ac40454334ce463a89c0002ee0d800085402e3e10b82980009500001b00005de0003100009a003c000860878000b68000ec8d54810242f5009a67c000262000cb48745286000fae4d0d01b867895927c550b18e30a1d0c03da096e147e029c82c0b9188aece048fc0003b0062ed85e0af602d1980007aaaf2af8d48834b50010acc09c23a22c9bc434d981492eca00a288e033000094878875800102cd7c0e65ca0f82228a40ac19e6210e2000b84c325c0ab47104281023c05cca712a80000009749e11200005a0000cd503018ced4ad8cdc0012160000000802e01003800008038000040000000800c00c0100100101c0000000c00a0ec030090042440d80801a0240105c00a0100000200c0000200104c0900380201e050020080180040880900200004000000028220000000140000908c0781080303e0901100800800c0180600400000003002010000090220f00780a002048050000040080000101008c008230000780300200600c0001200a00000003014
  | 7 => 0xa8c000fd8d84efc8d48d855c32200006870c3829e27d826927519067acda43831e96006d1e10f8000000000324000c6c00000099c7f07700012d4c2a0881e06d82b439c440210d0ccfe5407f4200b0f2c8aba58920cd2c630a78fae008000ee0fb20000000012bc0000000000001e8000bb00000002ea00116c000e105444a40fec20774a48000c26cc0000e432b01bc001202bc43d000028422b18283ab80ac02d058a00000000007c0002f8000000001218e2c00000042649a0005949fc0000b0184a240fc09200083e1072d12a50944b8738dccc90414a4c5204dcb005e2060090000000f64000000c1665c9c40006de3de9d0000000eacea829019a32c4ec000000000c344ce064c007283690fcd141f8b5a69523ca35180be012424a37400063ee88f54c3837200010ab6014c7850e400042076852493c3a10a000036f21a4245d66e70d800000100c00000080cb24bdabde250218000864944d68314a0404072ca805f026c00000013c0000005100006b2000c9c4f8354a4319cf44fa8e6ee0c8800980000007020006dc0005747a40003509ccb582e0fa06b8dc0b94ac8eb8000000000fb0000e48cc51782c0380fac63c37eb9e3941a492eb44f8cfc443cc540f2b16000044e980009dc51a17053517cb6c0000007ccedd0a4a8e00000021ec5c000000930252e8c000000706bac59d25d1645041c041045001cf60000f7015ad380007670a2e681040005e8c22608030b7c22681400068488ceb0000000000348998000eb438f0a6000418546fa6114e5d0743fc294a649183932b8000f84d40c0891d2b4452288618942001008920000d3000024e1c603a4fc000c1514c0a0c30870ad00551b8c130690b078d1bcbe820495c95421d034c0ec98b38a6c0001cd25436497a3ec5d0ffd2342543711e4416aee1592e8000bc84584c3284f7ed250e0e38fb6ce04e06f6000fa4bf512492a7a8a205a510002056d2911506360000660b4000e9cb1c6e0a85060300000000d65070000130c943983bc940644b5c00083c8388f83f08ac73d0a8cf890c10d22c04d1350ac8b09ac308b021ac910a930646be5c2000000000968000256db86bacf1298f7453c0145da3c81a0c507dca10000d3d1a00003dc6349f8eec2482389a4b3c36ca38a5c6c1142240488a149140012d8faaf782ad0380a8000f18000bd52e054a000ddcea0adc67238cebd146362000000000000000978fed1c4000000000de4650000a7526c6802f64005fce748987803e7028570dc4b122372a05084702bab141520e2f384608ec28c000848e704b0cd12cc2087c42205b0970d3a05c47800041e000764000c1d1a41600f0584000c0400062c001258480610dd0e784c40011ac3cc86cdd42f041ac10000f4a0000006e806a1d22782f4338a2d2c4ae21cee28f8b0b48f0aeaaa
  | 8 => 0xb5e6fa614048070e2036a68c9f4a0c5c6b90a60a7cda4b08156b0ce250c91482e4db12aca40120be400096c1f113f2010cc4ae581020d50000000000f6e9b8d8c0006710486b45ad1ba6ff2391e87be7d470ab0aa081988c84982f20011bedf83e82b0000000e410dc19c5383ad1b72e40e0675108ff4ba2a58ca0f5c00025e7145186b6f6cd9107c3400ecd600010980a517a45a0ea0f4cc82671c07fe4c666445600000070e00038724d1304e4f2913c85035800000000000008ce5917ee54c85230938afc4047a664845c85d10d2f00002a00003d8d1ce185d20000cc0006bc412000000c4c0001b423e89501858c000000001154000beccac7b8058001184000000ae835ecb00000012601009d8038000000b88654000cb8af42460000003f464c1881c8000000c0a7c02d8e6c4304840002be000366de8e600000000006f8ba6000000379208d80f58bf06fcaa09f011030c1911f06d05bc174f68b984c08dc000f80858d66b3081c6251b08285c89c0aa91ec1ca638dfd215212e64e9097c9800010104a04b48e846d1c86a48bc474cd84a70f486920ed9d014f2cef05591440011f28d04acca88204aaaf07ac16447d1f4464316f205eec2c18f050ca4decb54f82f082bc5601d0660001054642760cec00035c00000104c000ae631c44c984ff82701686c50783a40dc8cc62810848cbf91a9140000f88f00db4a960e84085c4dc8000bcc12c7986760006a8924c2e00000000079c4d0000000500786000000000c49228cfc0780000005687c8b8c3e4fe03848f45ba20c9349a8ef8004a90000a1811cc2506c54f21cbce5dc0012781401fc0000002d4bfe154888c740801e458e2fcde0000cf4a94e9400057cb34d94513158000fe4e7c7009d4000830000000000ede6cc396280000000ef4bc07120c8f40f251d40000e51109060007bc0da4cc0000240009c81792481d800015e548fbd250000c78ab054c69c704cc7268c06f0c708001204c3c98c9ec1967e4f327902b69e8b1006ef04716e846ea7e8a304b237696466cfb4df4f4e4f04baaa4138274bca7fd21003214433c794c58afefba49c360ab8c281923a84a86a0bfd08c41c9b00c0f942c4bd80006045f8000a8800000118c5e452c1f48a8b4c904
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf5358c10036de5358c10006dd5358c10036de4358c10004ff7258c1000cfe7258c1000cfc7258c10036df3258c10014ff7158c10014fd7158c10034fc7158c100067c5158c10036dc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10026f71058c10026f51058c100067f7654c101967e7654c100067d7654c101967c7654c100057f7454c101967f6454c1016e7e6454c100067d6454c101967c6454c1019d7f7354c1003f5f7354c101967f6354c100167e6354c101975e6354c100165e6354c100367d6354c101975d6354c100065d6354c100167c6354c101967f6254c101667e6254c101967c6254c100375f3254c100057c7154c100867e6154c101967e6054c10197771054c101977a1054c10197751054c10004ff7650c10024fe7650c10004fd7650c10024fc7650c1003d7e7550c100057d7550c10016de6350c10006dd6350c100379c4350c10004ff75588100067f75588100047f755881001cfe7558810004fd755881001cfc75588100067c755881001c7c7558810004ff7358810014fe7358810014fc73588100067f53588100067d5358810026ef725881002eee5258810006ed525881002eee325881000cff715881000cfd715881002cfc71588100067c515881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026f51058810004ff764c810024fe764c810004fd764c810024fc764c810016de634c810006dd634c8100075d534c81000eee624c810006ed624c81002fcc324c810005f7714c810005f4714c8100467f769441001e7e769441001e7d76944101867c76944100057d73944101867f639441013e7e63944100067d63944101867c63944101867f62944101367e62944100067d62944101867c629441018d7e719441003f7671944100467e61944101877a70944100077970944101867e60944101877710944101877a1094410187751094410084ff768c410024fe768c410014fd768c410024fc768c4100057f758c41003d7c758c410016de638c410006dd638c410086f6618c410025fa708c410005f9708c410084ff764c4100057f754c41003d7c754c410086f6614c41007cff7688410024fe768841000cfd7688410024fc768841000eee6288410006ed628841007ef66188410025fa7088410005f9708841007cff76484100057f754841003d7c754841007ef66148410025fb7644010006fb7644010004fb76440100077b7544010177787544010007db7344010007d873440101777b5344010007795344010007eb7244010007e87244010025fb7144010027f3714401017efa6144010027f261440100077a5144010177f25144010007725144010177f15144010177785144010
  | 1 => 0xc51000777754c51005df6754c51005df4754c5101d774754c51005d74754c51000777654c5101d774654c510005f7744c510005f5744c510007b7644c510007b4644c5101d777544c51000775544c510055f7734c510007d7734c510007d7634c510016f6634c510016f4634c510057d4634c51005777534c51005775534c510005f7724c510007e7624c510007e4624c510007f3704c510025f6704c510025f4704c510007f0704c510064fe76885100067f65885100fe7c6588510006df63885100f6dc6388510006ef628851000eec62885100077651885101cf745188510005f67688510066f6768851005df6758851005df475885100077765885101cf746588510005f77388510005f57388510007d76388510007d463885101cf77538851000775538851004df57288510007e7628851000ef6628851000ef4628851004fe4628851000ee4628851004fe63288510007e53288510025f67088510025f470885101c7e620885101c7e42088510024fc76485100057f754851005d7c75485100067f65485100ee7c6548510006df63485100e6dc6348510006ef624851000eec62485100077651485101bf745148510005fb7048510025f87048510025f4764851000ef47648510024f4764851000777754851005df6754851005df475485101bf74754851005d7475485100077765485101bf746548510005f77348510005f57348510007d76348510007d463485101bf77534851000775534851004df77248510007e77248510007e7624851000ef6624851000ef4624851004fe46248510007f37048510025f67048510025f47048510007f07048510014ff764c110054fd764c110014fc764c1100067f654c1100be7c654c110006bf644c1100b6bc644c110006df634c110016dc634c110006ef624c1100aeec624c110005f7714c110005f4714c1101b774514c11000cff764811004cfd764811000cfc76481100057f754811005d7c75481100067f65481100967c6548110006df634811008edc6348110006ef624811000eec6248110005f77148110005f471481101af745148110027e820481100067f65c41100467c65c4110006df63c4110086dc63c4110006ef62c411007eec62c4110025f671c4110026f761c41101a77451c4110025fa76c4110026fa76c4110024fa76c41100077b65c41101a77865c4110007db63c4110007d863c41101a77b53c41100077953c4110007eb62c4110007e862c4110025fa71c4110026fb61c4110027f361c41101a7f351c41100077a51c41101a77851c41101a7f051c41101a77051c4110007f231c4110007f131c4110007f221c4110007f121c4110004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c100c4fe7458c100c4fc7458c100067f5458c10026df7358c100367
  | 2 => 0x1c6ee30d89101c6ec30d89101c6ee10d89101c6ec10d89100057f755891005d7c75589100067f65589100067c6558910005df7358910055dc7358910006df6358910006dc635891004eec6258910007745158910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc73589100067f53589100067d535891004cff7258910006ef7258910064ff7158910006f771589100067c515891007cff7058910006fb7058910005ee761891004eee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d531891004fe571189101f6ef6118910007e751189100076c5118910007e451189100076451189101f7e610189101f7e41018910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91014e7c654c910006bf644c910146bc644c910006df634c910016dc634c9100075d534c910006ef624c91000eec624c91004fcc324c9101ef74514c9100057e76945100767e76945100747e76945100057d73945100067f63945100075f63945100065f639451013e7e63945100067d639451013e7c63945100075c639451013e5c63945100067f62945100076f62945100066f62945101367e62945100067d62945101367c62945100076c62945101366c629451005d7e719451005f76719451005d76719451018776109451006cfe768c5100057f758c51005d7c758c5100067f658c51012e7c658c510006bf648c510126bc648c510006df638c510016dc638c510006ef628c51011eec628c51000776518c5101e774518c510005f6768c51006ef6768c51000777758c51005df6758c51005df4758c5101e774758c51005d74758c51000777658c5101e774658c510005f7748c510005f5748c510007b7648c510007b4648c5101e777548c51000775548c510055f5738c510007d7638c510016f6638c510016f4638c510057d4638c510016d4638c51005777538c51005775538c510057d6438c510007d5438c510005f5728c510007e7628c510007e4628c510057d7328c510007d5328c510025f6708c510025f4708c5101dfd6308c5101dfd4308c510024fc764c5100057f754c51005d7c754c5100067f654c5101167c654c510006bf644c51010ebc644c510006df634c510016dc634c510006ef624c510106ec624c51000776514c5101d774514c510005fb704c510025f8704c510025f4764c510016f4764c510024f4764
  | 3 => 0xf6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d100075f5418d10006de6218d10006dc6218d10057d57118d10206df6118d10007d75118d100075c5118d10007d45118d10007545118d10207d61018d10207d41018d100067f7654d100057e7654d100067e7654d100047e7654d100067d7654d100057c7654d100067c7654d100047c7654d100057f7454d100067f6454d100073f6454d100063f6454d1016e7e6454d100067d6454d1016e7c6454d100073c6454d1016e3c6454d100557f7354d1005f5f7354d100567f6354d100075f6354d100065f6354d100167e6354d100567d6354d100167c6354d100575c6354d100165c6354d101667e6254d101667c6254d101666c6254d100575f3254d10007777154d100057c7154d10007747154d10005747154d10197761054d10004ff7650d10004fe7650d10004fd7650d10004fc7650d1005d7e7550d100057d7550d100067f6550d1015e7c6550d10006df6350d10016dc6350d100579c4350d10156ec6250d101ff745150d1000cfe76d89100067f65d89100067c65d8910006df63d8910006dc63d891004eee62d89100077451d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910014fe73d8910004fd73d8910014fc73d89100067f53d89100067d53d8910006ef52d891004eee52d8910006ed52d891004eec52d8910006ef32d891004eee32d891004eec32d891000cfe71d8910024fd71d891000cfc71d89100067c51d891004eef21d8910024fe70d891004cfd70d8910024fc70d891004eef20d891004dee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d89101c7e771d8910007e751d89100076c51d8910007e451d89100076451d89101c7e610d89101c7e410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d89101c6ef71d891004eee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d89100066c51d8910006ef31d8910006ec31d8910006ef70d89101c6ee70d8910006ed70d89101c6ec70d8910006ef50d89101c6ee50d8910006ed50d89101c6ec50d8910006ef30d8910
  | 4 => 0x9510014fe76d8d1005d7c75d8d100067f65d8d100067c65d8d10056de63d8d100075f53d8d100077451d8d10004ff75d8d100067f75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d100067c75d8d1001c7c75d8d100c4fe74d8d10004fd74d8d100c4fc74d8d100067f54d8d100567f53d8d10006df53d8d100065f53d8d10056de53d8d10006dd53d8d10056dc53d8d10006df43d8d10056de43d8d10056dc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10056df32d8d10006de32d8d10056dc32d8d10014fe71d8d10024fd71d8d10014fc71d8d100067c51d8d10056df31d8d10024fe70d8d10054fd70d8d10024fc70d8d10056df30d8d10055de76d8d10014de76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dc64d8d100075f54d8d10006de62d8d10006dc62d8d101dfd771d8d10007d751d8d100075c51d8d10007d451d8d100075451d8d101dfd610d8d101dfd410d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d100065f54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d101dedf71d8d10056de71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d100065c51d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d101dede70d8d10006dd70d8d101dedc70d8d10006df50d8d101dede50d8d10006dd50d8d101dedc50d8d10006df40d8d101dede40d8d101dedc40d8d10006df20d8d101dede20d8d101dedc20d8d101dede10d8d101dedc10d8d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d1020dbc7458d10006bf6458d10056dc6358d10005ef7258d1004dec7258d10007745158d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d100c4fe7458d100c4fc7458d10006bc7458d100c4bc7458d100067f5458d10054ff7358d10006df7358d100567f5358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d1006cff7158d10006f77158d100067c5158d10084ff7058d10006fb7058d10005de7618d10056de7618d10004de7618d100575e7518d100575d7518d10006d
  | 5 => 0x57f7454e101967f6454e1016e7e6454e100067d6454e101967c6454e1019d7f7354e100775f7354e101967f6354e100167e6354e1006e7d6354e100167c6354e101967f6254e101667e6254e101967c6254e1006f5f3254e100057c7154e100567d6154e101967e6054e10197771054e10004ff7650e10024fe7650e10004fd7650e10024fc7650e100757e7550e100057d7550e1015e7e6550e100067d6550e10016de6350e10006dd6350e1006f9c4350e10004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7358a10014fe7358a10014fc7358a100067f5358a100067d5358a10026ef7258a10066ee3258a100067c5158a10066ef2158a10024fc7058a10026ee2058a10026ec2058a10026f71058a10026f51058a10004ff764ca10024fe764ca10004fd764ca10024fc764ca1014e7e654ca100067d654ca10016de634ca10006dd634ca100075d534ca1000eee624ca10006ed624ca10067cc324ca10005f7714ca10005f4714ca101857d769461005e7d769461005c7d76946100057d73946101867f639461013e7e63946100067d63946101867c63946101867f62946101367e62946100067d62946101867c629461018d7e71946100777671946101867e6094610187771094610054fd768c6100057f758c6100757c758c61012e7e658c6100067d658c6101dedf638c610016dc638c610014ff764c610024fc764c6100057f754c6100757c754c6101167e654c6100067d654c610016de634c610006dd634c610005fb704c610025f8704c61004cfd76886100fe7e65886100067d65886101c6ef628861000eec628861000cff7648610024fc76486100057f75486100757c75486100ee7e65486100067d654861000eee6248610006ed6248610005fb7048610025f87048610025f976c4210006f976c42100277a65c42100277965c42102177b53c42100077953c4210027f271c42100077a51c42102177851c421005d7e76d951005e7e76d951001c7e76d95100057d73d95100067e63d95100067c63d95100067e62d95100067c62d951005f7671d951005f7571d951005d7c71d95101877610d95101877410d95100067f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067c32d95101867f71d951005e7e71d951001c7e71d951005e7671d951005e7d71d951005e7571d951005e7c71d951001c7c71d95100067f31d95100067c31d95100067f21d95100067c21d95100067f70d95101867e70d951005e7d70d95101867c70d95100067f30d95101867e30d95101867c30d95100067f20d95101867e20d95101867c20d95101867e10d951005e7d10d95101867c10d
  | 6 => 0x6438c710007d5438c710005f5728c710087d7328c710007d5328c710025f6708c710007f2708c710007f1708c710025f4708c7101dfd6308c7101dfd4308c710034ff764c7100057f754c7100457c754c71000776514c71023f74514c710005f7764c710036f7764c71000777754c710045f6754c710045f4754c71023f74754c71004574754c710005f7744c710005f5744c71023f77544c71000775544c710007d7734c710016f6634c710016f4634c71008777534c71008775534c710005f7724c710025f6704c710025f4704c710024fd768871000eee6288710006ed6288710007765188710237745188710025fa7088710005f97088710025f5768871000ef57688710024f57688710045f67588710045f47588710005f77388710005f5738871023777538871000775538871000ef6628871007fe66288710007e5628871000ef4628871007fe63288710007e53288710025f67088710007f27088710007f17088710025f470887101c7e620887101c7e4208871002cff76487100057f75487100457c754871000776514871022f745148710005f7764871002ef77648710007777548710045f67548710045f4754871022f747548710045747548710005f77348710005f5734871022f775348710007755348710007e7724871000ef6624871000ef46248710025f67048710025f47048710014ff764c310014fc764c310016de634c310006dd634c310005f7714c310005f4714c31022774514c31000cff764831000cfc76483100057f75483100457c754831000eee6248310006ed6248310005f77148310005f4714831021f7451483100067f73596100047f73596100067e73596100067d73596100067c73596100067e43596100067c43596100067f72596100067e72596100067d72596100067c72596100067f32596100067e32596100067c32596100767f71596100767e71596100067d71596100767c71596100067f31596100067c31596100067f21596100067c21596100267f70596100267e70596100267d70596100267c70596100267f30596100267e30596100267d30596100267c30596100267f20596100267e20596100267d20596100267c20596100267f10596100267e10596100267d10596100267c1059610004ff7558e1001cfe7558e100067e7558e1001c7e7558e10004fd7558e100067d7558e1001cfc7558e10004ff7458e100c4fe7458e100c4fc7458e100067f5458e10026df7358e1006e7f5358e1006ede4358e10004ff7258e1000cfe7258e1000cfc7258e1006edf3258e100067c5158e1006edf3158e10024fc7058e10026de3058e10026dc3058e10026f71058e10026f51058e101957f7654e100067f7654e100047f7654e101967e7654e101957d7654e100067d7654e100047d7654e101967c7654e10
  | 7 => 0xc120007cd324c120086de63d8f100077451d8f10004ff75d8f1001cfe75d8f10004fd75d8f1001cfc75d8f100c4fe74d8f10004fd74d8f100c4fc74d8f100067f54d8f10084fd73d8f100867f53d8f10086de43d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10086df32d8f10006f671d8f100067c51d8f10006f970d8f101dede30d8f101dedc30d8f10014ff7658f10086dc6358f10007745158f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f100c4fe7458f100c4fc7458f100067f5458f10006df7358f100867f5358f10004ff7258f1000cfe7258f1000cfc7258f10024fc7158f100067c5158f10086dc3158f10086df3058f100067f7654f100067e7654f100067d7654f100067c7654f100057f7454f100067f6454f1016e7e6454f100067d6454f1016e7c6454f100857f7354f100475f7354f100867f6354f100167e6354f100867d6354f100167c6354f101667e6254f101667c6254f100875f3254f10007777154f100057c7154f10007747154f10005747154f10004ff7650f10004fe7650f10004fd7650f10004fc7650f100457e7550f100057d7550f10006df6350f10016dc6350f100879c4350f10257745150f100457e75d8b100057d75d8b1007eee62d8b100077451d8b10004ff75d8b1001cfe75d8b100067e75d8b1001c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfc75d8b10014fe73d8b10004fd73d8b10014fc73d8b100067f53d8b100067d53d8b1007cfd72d8b1007eee32d8b10006f671d8b100067c51d8b10006f970d8b101c6ee20d8b101c6ec20d8b1000cff7658b1007eec6258b10007745158b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7358b10014fe7358b10014fc7358b100067f5358b100067d5358b10006ef7258b10024fc7158b100067c5158b1007eec2158b1007eef2058b10004ff764cb10004fe764cb10004fd764cb10004fc764cb10006df634cb10016dc634cb100075d534cb10006ef624cb1000eec624cb1007fcc324cb1024f74514cb1001e7e769471001e7d76947100057d73947100067f639471013e7e63947100067d639471013e7c63947100067f62947101367e62947100067d62947101367c62947100457e71947100477671947100457671947100077a7094710007797094710024fd768c7100057f758c7100457c758c710016de638c710006dd638c71000776518c71024774518c710025fa708c710005f9708c710025f5768c710016f5768c710024f5768c71000777758c710045f6758c710045f4758c71024774758c71004574758c710005f7748c710005f5748c71024777548c71000775548c710016f6638c710087d6638c710007d5638c710016f4638c71008777538c71008775538c710087d
  | 8 => 0x1675f3254d201676e3254d201675d3254d200057c7154d201667f6054d201677b2054d201976e2054d201976c2054d20167782054d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200957e7550d200057d7550d200067f6550d2015e7c6550d20016de6350d20006dd6350d2008f9c4350d2000dee7250d20025ec764c920016ec764c920024ec764c9200076f654c9202676c654c920005ef744c920005ed744c920006ef644c920006ed644c9202676f544c9200076d544c92000def734c92000fcf734c920007cf634c920016ee634c920016ec634c92008fcc634c920016cc634c92008f6f534c92008fce534c92008f6d534c920267cd534c9200074d534c92008fce434c920007cd434c9202676c514c92008fcc314c920007eb704c920025ee704c920025ec704c920007e8704c92000eef604c92000feb604c92008fcf304c9200957e75d85200057d75d85200067f65d85200067c65d8520004ff75d852001cfe75d85200067e75d852001c7e75d8520004fd75d85200067d75d85200047d75d852001cfc75d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d8520024fd72d85200067c51d8520006f731d8520006f431d8520066f621d8520066f521d85200957e75985200057d75985200067f65985200067c6598520006f7619852004df970985200057f75585200957c75585200067f65585200067c6558520005df735852008ddc735852007dfb70585200957c75185200067f65185200067c6518520006f56118520004ff75185200067f751852001cfe7518520004fd751852001cfc75185200067c751852001c7c7518520014fe7318520004fd7318520014fc73185200067f53185200067d5318520024fd721852002eee3218520006ed32185200067c5118520006f73118520006f4311852002ef6211852002ef52118520024fe7018520024fc70185201f6ee20185201f6ec20185200067f76945200057e76945200067e76945200047e76945200067d76945200057c76945200067c76945200047c76945200057d73945200067f639452013e7e63945200067d639452013e7c63945201867f62945201376e32945200076d329452025d7e71945200977671945200067f61945200067c61945201367f60945201377b20945201876e20945201876c2094520137782094520004fe768c520004fd768c520004fc768c5200057f758c5200957c758c5200067f658c52012e7c658c520006df638c520016dc638c520007cd328c520004ff764c520004fe764c520004fc764c5200057f754c5200957c754c5200067f654c5201167c654c520014ff764c12000cfe764c1200acfd764c12000cfc764c1200067f654c1200be7c654c120006df634c120016dc634c120005ef724c12000dec724
  | 9 => 0xf764c620004fd764c620024fc764c6200057f754c6200a57c754c620005ef724c62000dec724c620006f6614c620006f5614c6201c6ef6388620006ed638862029f6f53886200076d538862000dee718862000fe671886201c7e66188620006ed61886201c7e561886200076e518862029f6c51886201c7ea70886201c5ed7088620007e9708862000eee608862000fea60886202957e76d95200967e76d952001c7e76d95200057d73d95200067e63d95200067c63d952028f6e32d95200057e71d952028f7b20d95202876e20d95202876c20d952028f7820d95200067f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067e43d95200067c43d95202867f72d952028e7e72d952028e7d72d952028e7c72d952028e7f32d952028e7e32d952028e7d32d952028e7c32d95200067f71d95200067e71d95200047e71d95200067d71d95200067c71d95200067f31d95200067c31d952028e7f21d952028e7e21d952028e7d21d952028e7c21d952028e7f70d95202867e70d952028e7d70d95202867c70d95200067f30d95202867e30d95202867c30d952028e7f20d95202867e20d952028e7d20d95202867c20d95202867e10d95202867c10d9520014fe76d8d200957c75d8d200067f65d8d200067c65d8d2008ede63d8d20004ff75d8d200067f75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d200067c75d8d2001c7c75d8d200c4fe74d8d20004fd74d8d200c4fc74d8d200067f54d8d2008e7f53d8d20006df43d8d2008edc43d8d20024ff72d8d2000cfe72d8d20024fd72d8d2000cfc72d8d200ceee42d8d200cedf32d8d200cedd32d8d20004fe71d8d20004fd71d8d200067c51d8d2008edc31d8d2000cfd70d8d2008edf30d8d200057f7558d200957c7558d200067f6558d200067c6558d20005bf7458d2027dbc7458d2008edc6358d20005f77158d20005f47158d20275fb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d200c4fe7458d200c4fc7458d20006bc7458d200c4bc7458d200067f5458d200ccff7358d20006df7358d2008e7f5358d2008ede4358d200acff7258d20006ef7258d200aeee4258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d200067c5158d20274ff7058d20006fb7058d200067f7654d200057e7654d200067e7654d200047e7654d200067d7654d200057c7654d200067c7654d200047c7654d200057f7454d200067f6454d2016e7e6454d200067d6454d2016e7c6454d2026d7f7354d200975f7354d2008e7f6354d200167e6354d2008e7d6354d200167c6354d201967f6254d201676e4254d20
  | 10 => 0x45302ad7e71945300bf7671945300067f61945300067c619453013e7f609453013f7b30945301875e30945301875c309453013f783094530004fe7690530004fd7690530004fc76905300057f75905300bd7c7590530006bf64905300c6bc64905300079d4390530004ff7650530004fe7650530004fc76505300057f75505300bd7c7550530004fe7688530004fd7688530004fc7688530006ef628853000eec6288530007cd3288530004ff7648530004fe7648530004fc76485300057f75485300bd7c7548530014fe76501302a4fd7650130014fc7650130005df7350130015dc73501300079d4350130004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e200c4fe7458e200c4fc7458e200067f5458e20026df7358e2009e7f5358e2009ede4358e200aedf3258e200aedd3258e20004ff7158e20004fc7158e200067c5158e200aeec2158e20024fe7058e20024fc7058e20026de3058e20026dc3058e20026ef2058e20026ed2058e200067f7654e201967e7654e200067d7654e201967c7654e200057f7454e201967f6454e2016e7e6454e200067d6454e201967c6454e2019d7f7354e200a75f7354e201967f6354e200167e6354e2009e7d6354e200167c6354e201667d6254e201675f3254e201675d3254e200057c7154e201676c2154e201967e6054e201976f2054e201677b2054e20197782054e20004ff7650e20024fe7650e20004fd7650e20024fc7650e200a57e7550e200057d7550e20016de6350e20006dd6350e2009f9c4350e20004ff759862001cfe7598620004fd759862001cfc7598620014fe7398620004fd7398620014fc73986200067f53986200067d5398620026f67198620006f751986200067c5198620006f4519862000674519862007ef6219862007ef52198620024fe7098620026f61098620026f41098620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7358620006df7358620004df7358620014fe7358620014fc7358620006dc7358620014dc73586200067f53586200067d5358620026f77158620006f751586200067c5158620006f4515862000674515862004ef6215862004ef5215862004eec2158620024fc7058620026f61058620026f410586200067f76946201867e76946200067d76946201867c76946200057d73946201867f639462013e7e63946200067d63946201867c63946201367d629462018d7e71946200a77671946200067e61946200067d61946201376c21946201867e60946201876f20946201377b2094620187782094620004ff768c620024fe768c620004fd768c6200057f758c6200a57c758c6201dedf638c620016dc638c620006f6618c620006f5618c620004f
  | 11 => 0x179f7450d300079f6450d300c6de6450d300c6dc6450d300b79c6450d300c69c6450d300b75f5450d300b75d5450d30005df7250d300b79f4250d302cf5c5150d300b79c4150d30007db7050d30025de7050d30025dc7050d30007d87050d30016df6050d30017db6050d300b79f4050d3000cfe76d89300aeee62d8930004ff75d893001cfe75d8930004fd75d893001cfc75d89300c4fe74d8930004fd74d89300c4fc74d89300067f54d89300067d54d8930024fd73d893000cfc73d893009e7f53d893009e7d53d893009ede43d8930006dd43d89300aeee32d893009eed32d8930004fe71d8930004fd71d89300067c51d89300aeec21d8930014fd70d89300aeef20d89300057f75589300bd7c7558930005bf74589300b5bc74589300aeec6258930005f77158930005f471589302c5fb7058930004ff7650930004fe7650930004fc76509300c6be64509300073d5450930015de73509300079d435093000eee62509300afac4250930025dc764c93000edc764c930024dc764c9302bedf654c9302bedd654c930005df744c930005dd744c930006df644c930006dd644c9302bf5f544c9300075d544c930015df724c930017cf724c930007cf624c93000ede624c93000edc624c9300afcc624c93000ecc624c9300afce424c930007cd424c9302bf5c514c9300afcc214c930007db704c930025de704c930025dc704c930007d8704c930016df604c930017db604c9300afcf204c9300bd7e75d85300057d75d8530004ff75d853001cfe75d85300067e75d853001c7e75d8530004fd75d85300067d75d85300047d75d853001cfc75d85300c4fe74d8530004fd74d85300c4fc74d85300067f54d85300067d54d8530024fd73d853006e7f53d853006e7d53d853000cfe72d8530004fd72d853000cfc72d85300067c51d853006ef631d853006ef531d8530006f721d8530006f421d8530006f76198530055f970985300057f75585300bd7c7558530005bf74585300b5bc7458530005ef72585300adec7258530085fb7058530006f56118530004ff751853001cfe7518530004fd751853001cfc75185300c4fe7418530004fd74185300c4fc74185300067f54185300067d5418530024fd73185300367f53185300367d5318530036de4318530006dd431853000cfe7218530004fd721853000cfc7218530036df3218530006dd32185300067c5118530036f63118530036f53118530006f72118530006f42118530206de3018530206dc30185300067f76945300067e76945300067d76945300067c76945300057d74945300067f64945302b67e64945300067d64945302b67c649453013d7f739453013d7d73945301867f639453013f5e43945300075d43945300067f62945301367e62945301367c629453013f5f32945300075d329
  | 12 => 0xe725863000cfc7258630006ec725863000cec7258630026f77158630006f751586300067c5158630006f45158630006745158630056f63158630056f53158630056dc3158630024fc7058630026f61058630026f410586300067f76946301867e76946300067d76946301867c76946300057d74946301867f64946302b67e64946300067d64946301867c649463013d7f739463013d7d739463013e7d63946301367e62946300067d62946301867c629463018d7e71946300df7671946300067e61946300067d619463013f5c31946301867e60946301875f309463013f7b3094630187783094630004ff7690630024fe7690630004fd76906300057f75906300dd7c75906300c6bc6490630006f66190630006f56190630004ff7650630004fd7650630024fc76506300057f75506300dd7c7550630005df7350630015dc7350630006f66150630006f561506300075f758c6303075c758c6301dedf648c630006dd648c6303075f548c6300075d548c630006dd628c630015de718c630017d6718c6301dfd6618c630006dd618c6301dfd5618c6300075e518c6303075c518c6301dfda708c6301dddd708c630007d9708c630016de608c630017da608c630004ff7688630024fe7688630004fd768863000eec6288630006f66188630006f56188630004ff7648630004fd7648630024fc76486300057f75486300dd7c7548630005df7348630015dc7348630006f66148630006f561486300c4fe76d91300b6be64d9130004ff75d913001cfe75d9130004fd75d913001cfc75d91300b67f54d91300b6be54d9130006bd54d9130024ff73d9130014fe73d9130024fd73d9130014fc73d91302fe7f53d91302fe7d53d91302febf43d91302febd43d913000cfe72d9130004fd72d913000cfc72d9130006be42d91300b6bc42d91302fedf32d9130004fe71d9130004fd71d91300067c51d91300b6bc41d9130014fd70d91300b6bf40d91300b6bc64591302f5fb7059130004ff755913001cfe7559130004fd755913001cfc75591302a4ff7359130006df73591302a67f5359130004ff725913000cfe725913000cfc72591302a6df3259130004ff7159130004fc71591300067c51591302f4ff7059130006fb70591300067f76551300067e76551300067d76551300067c76551302ed7f74551300bf3f74551300b67f64551300073f64551300063f64551300c67e64551300b67d64551300c67c64551300b73c64551300c63c64551302d57f73551302d57d73551302de7f63551302d75e43551302e67e62551302e67c62551300b73f42551302d75f32551300057c71551302d67f60551302d77b30551302df5e30551302df5c30551302d7783055130025dc7650d300c6dc7650d30024dc7650d302cf5e7550d300075d7550d30015df7450d30
  | 13 => 0x85213176f53885210076d538852100dee718852100fe6718852100eef618852100fe761885210076e51885213176c51885210067f65d81210067c65d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121014fe73d8121004fd73d8121014fc73d81210067f53d81210067d53d81210067e51d81210067c51d812107efa20d81210ed7e75981210057d75981210067f65981210067c6598121006fb60981210057f75581210ed7c75581210067f65581210067c6558121005df73581210e5dc73581210067f65181210067c65181211c6ef6218121026fa6018121006f96018121004ff755923001cfe7559230004fd755923001cfc7559230026bf74592300d67f54592302a67f53592302a67d53592302a6bf43592302a6bd4359230004ff725923000cfe725923000cfc72592300d6bf4259230004ff7159230004fc71592300067c51592302a6dc3159230024fe7059230024fc7059230026be4059230026bc4059230026df3059230026dd30592300067f76552302de7e76552300067d76552302de7c765523030d7f74552300df3f74552302de7f64552300c67e64552300d67d64552300c67c64552302d57f73552302d57d73552302d67d63552302e67e62552302de7c62552300d73f42552300057c71552302d75c31552302de7e60552302df5f30552302d77b30552302df783055230004ff7558a300067f7558a300047f7558a3001cfe7558a30004fd7558a3001cfc7558a300067c7558a3001c7c7558a30004ff7458a300c4fe7458a300c4fc7458a300067f5458a300067d5458a3008e7f5358a3008e7d5358a30026ef7258a300ceee4258a300ceee3258a3008eed3258a30004ff7158a30004fc7158a300067c5158a3008edc3158a30024fe7058a30024fc7058a30026df3058a30026dd3058a30026ee2058a30026ec2058a30004ff7650a30004fd7650a30024fc7650a300c6be6450a30006bd6450a300073d5450a30005df7350a30015dc7350a3000eee6250a30006ed6250a300cfac4250a30004ff759863001cfe7598630004fd759863001cfc75986300c4fe7498630004fd74986300c4fc74986300067f54986300067d54986300867f53986300867d539863000cfe7298630004fd729863000cfc7298630026f67198630006f751986300067c5198630006f45198630006745198630086f63198630086f53198630024fe7098630026f61098630026f41098630004ff75586300067f75586300047f755863001cfe7558630004fd755863001cfc75586300067c755863001c7c7558630004ff7458630006bf7458630004bf74586300c4fe74586300c4fc7458630006bc74586300c4bc74586300067f54586300067d54586300567f53586300567d5358630004ff7258630006ef7258630004ef725863000cf
  | 14 => 0x67d73d95210047d73d95210067c73d95210067e43d95210067c43d95211367f72d95211367e72d95211367d72d95211367c72d95211367f32d95211367e32d95211367d32d95211367c32d95211367f71d95210ee7e71d95211367d71d95211367c71d95210067f31d95210067c31d95211367f21d95211367e21d95211367d21d95211367c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f30d95210067c30d95211367f20d95211367e20d95211367d20d95211367c20d9521014fe76d8d210ed7c75d8d210067f65d8d210067c65d8d210e6de63d8d21004ff75d8d210067f75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d210067c75d8d2101c7c75d8d210c4fe74d8d21004fd74d8d210c4fc74d8d210067f54d8d210e67f53d8d210e6de43d8d2111cff72d8d2111cfd72d8d2111edf32d8d2111edd32d8d2100cfd71d8d210067c51d8d210e6df31d8d2111eec21d8d21024fe70d8d21004fd70d8d210e6dc30d8d210057f7558d210ed7c7558d210067f6558d210067c6558d210e6dc6358d2132df77158d21004ff7558d210067f7558d210047f7558d2101cfe7558d21004fd7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d210c4fe7458d210c4fc7458d210067f5458d2111cff7358d21006df7358d210e67f5358d21104ff7258d21006ef7258d2132cff7158d21006f77158d210067c5158d210e6dc3158d21106ec2158d21004ff7058d21024fc7058d210067f7654d210057e7654d210067e7654d210047e7654d210067d7654d210057c7654d210067c7654d210047c7654d210057f7454d210067f6454d2116e7e6454d210067d6454d2116e7c6454d2126d7f7354d210ef5f7354d210e67f6354d210167e6354d210e67d6354d210167c6354d211667f6254d211675f3254d211675d3254d210057c7154d211667f6154d21167772154d211676c2154d21167742154d211967c6054d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210ed7e7550d210057d7550d210067f6550d2115e7c6550d21006df6350d21016dc6350d210e79c4350d2125d7e76945213267e769452125c7e76945210057d73945210067f639452113e7e63945210067d639452113e7c63945211367f629452125d7e71945210ef7671945211367f61945211377721945211376c21945211377421945211376421945211867c609452131cfe768c5210057f758c5210ed7c758c5210067f658c52112e7c658c521016de638c521006dd638c521014ff764c52100cfe764c521104fd764c52100cfc764c5210057f754c5210ed7c754c5210067f654c5211167c654c521006df634c521016dc634c521005ef724c52100dec724c5210076f65885213176c6588521006ef6388521006ed638
  | 15 => 0xc74d8e210067f54d8e21104fd73d8e210f67f53d8e210f6de43d8e21006ed72d8e2111eee42d8e2131cfe71d8e21006f671d8e210067c51d8e21024fe70d8e21004fd70d8e21014ff7658e210f6dc6358e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e210c4fe7458e210c4fc7458e210067f5458e21006df7358e210f67f5358e21106ee4258e21106df3258e21106dd3258e2100cfc7158e210067c5158e210f6dc3158e21004ff7058e21024fc7058e210067f7654e210067e7654e210067d7654e210067c7654e210057f7454e210067f6454e2116e7e6454e210067d6454e2116e7c6454e2126d7f7354e210ff5f7354e210f67f6354e210167e6354e210f67d6354e210167c6354e211667d6254e211676e4254e211675f3254e211676e3254e211675d3254e210057c7154e211667e6154e211676f2154e21167772154e21167742154e211967e6054e211676c2054e21004ff7650e21004fe7650e21004fd7650e21004fc7650e210fd7e7550e210057d7550e21006df6350e21016dc6350e210f79c4350e2100dee7250e210f5ef764ca21016ef764ca21014ef764ca21005ef744ca21005ed744ca21006ef644ca21006ed644ca213376f544ca210076d544ca2100def734ca2100fcf734ca21016ee634ca210f7ce634ca21016ce634ca21007cd634ca21016ec634ca210f76f534ca210f7ce534ca210f76d534ca21337cd534ca210074d534ca210f7ce434ca21007cd434ca21005ef714ca21007e7714ca21007e4714ca2100eee614ca2100fe6614ca213376c514ca210f7cc314ca211c5ec704ca210f7cf304ca211367f769462101e7e769462101e7d76946211367c76946210057d73946210067f639462113e7e63946210067d639462113e7c63946211376e72946210076d72946211376e32946210076d329462125d7e71946210ff7671946211367e61946211376f21946211377721946211376721946211377421946211867e60946211376c209462100cff768c621014fe768c62100cfd768c6210057f758c6210fd7c758c621016de638c621006dd638c62100dee728c621005ed728c621007cd328c62132cff764c6210057f754c6210fd7c754c62100dee724c6210fd7e75d82210057d75d82210fd7e75982210057d7598221006fb6098221004ff755822101cfe7558221004fd755822101cfc7558221004ff7358221014fe7358221014fc73582210067f53582210067d535822104eee3258221006ed32582210067e51582210067c515822104efa20582211c6ec2058221026fa6018221006f9601822125d7e76d95210ee7e76d952101c7e76d95210057d73d95210067e63d95210067c63d95211357c71d95211377721d95211376c21d95211377421d95210067f73d95210067e73d9521
  | 16 => 0x9131006f771591310067c515913134edc3159131004ff7059131024fc70591310067f76551310057e76551310067e76551310047e76551310067d76551310057c76551310067c76551310047c76551312ed7f74551311173f745513110e7f64551310c67e645513110e7d64551310c67c64551312d57f73551312d57d73551312d67f63551312e67e62551312e67c625513110f3f42551310057c71551312d67f61551312d77731551312d75c31551312d77431551312de7c605513100cfe76d89310067f65d89310067c65d8931106ee62d8931004ff75d893101cfe75d8931004fd75d893101cfc75d89310c4fe74d8931004fd74d89310c4fc74d89310067f54d89310067d54d89310f67f53d89310f67d53d8931106ee42d8931106ee32d89310f6ed32d8931014fd71d89310067c51d89310f6dc31d8931106ef21d8931024fe70d8931004fd70d8931106ec20d89310057f75589311157c75589310067f65589310067c6558931106ec6258931375f77158931004ff7650931004fe7650931004fc76509310067f655093136e7c6550931006bf64509310c6bc64509310073d5450931006ef625093100eec6250931107ac4250931005f77150931005f471509312ad7e76945313667e76945312ac7e76945310057d74945310067f64945312b67e64945310067d64945312b67c649453113d7f739453113d7d739453113e7f63945310067f62945311367e62945311367c62945312ad7e719453111776719453113e7f619453113f77319453113f5c319453113f74319453113f5431945311867c609453135cfe76905310057f75905311157c75905310067f65905313567c65905310c6be6490531014fe765053134cfd7650531014fc76505310067f65505313467c6550531005df7350531015dc73505310075f758c53133f5c758c5310075f658c53133f5c658c531006df648c531006dd648c53133f5f548c5310075d548c531006df628c531015de718c531017d6718c531016df618c531017d7618c5310075e518c53133f5c518c5310067f65d81310067c65d8131004ff75d813101cfe75d8131004fd75d813101cfc75d81310c4fe74d8131004fd74d81310c4fc74d81310067f54d81310067d54d81310867f53d81310867d53d813100cfe72d8131004fd72d813100cfc72d81310067e51d81310067c51d8131086fa30d81311157e75981310057d75981310067f65981310067c6598131006fb60981310057f75581311157c75581310067f65581310067c6558131005bf745813110dbc7458131005ef7258131105ec72581310067f65181310067c65181311dedf6318131026fa6018131006f960181310f6de63d8e2131df671d8e21004ff75d8e2101cfe75d8e21004fd75d8e2101cfc75d8e210c4fe74d8e21004fd74d8e210c4f
  | 17 => 0x75d32946312ad7e719463112f76719463113e7e619463113f5f319463113f77319463113f57319463113f7431946311867e609463113f5c30946310c4fe7690631014fd76906310067f65906313567c6590631015de7390631005dd73906310079d43906310067f65d82310067c65d823112d7e75982310057d75982310067f65982310067c6598231006fb60982310057f755823112d7c75582310067f65582310067c6558231004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff74582310c4fe74582310c4fc74582310067f54582310067d54582310567f53582310567d5358231056de4358231006dd4358231004ff725823100cfe725823100cfc7258231056df3258231006dd32582310067e51582310067c5158231056fa30582311dedc30582310067f65182310067c6518231026fa6018231006f960182312ad7e76d95311167e76d953101c7e76d95310057d74d95310067e64d95310067c64d95310067e62d95310067c62d953113d7c71d953113f7731d953113f5c31d953113f7431d95310067f74d95310067e74d95310067d74d95310047d74d95310067c74d953113e7f73d953113c7f73d953113e7e73d953113e7d73d953113c7d73d953113e7c73d953113e7f43d953113e7e43d953113e7d43d953113e7c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067c42d953113e7f32d953113e7e32d953113e7d32d953113e7c32d953113e7f71d95311167e71d953113e7d71d953113e7c71d95310067f41d95310067c41d953113e7f31d953113e7e31d953113e7d31d953113e7c31d95310067f21d95310067c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067c40d953113e7f30d953113e7e30d953113e7d30d953113e7c30d95310067f20d95310067c20d95310c4fe76d91311157c75d91310067f65d91310067c65d913110ebe64d9131004ff75d91310067f75d913101cfe75d9131004fd75d913101cfc75d91310067c75d913101c7c75d913110e7f54d9131384ff73d9131384fd73d91313867f53d91313867d53d9131386bf43d9131386bd43d913100cfe72d9131004fd72d913100cfc72d913110ebf42d9131014fd71d91310067c51d913110ebf41d9131386dc31d9131024fe70d9131004fd70d913110ebc40d91310057f75591311157c75591310067f65591310067c655913110ebc645913137df77159131004ff75591310067f75591310047f755913101cfe7559131004fd755913101cfc75591310067c755913101c7c755913134cff7359131006df735913134e7f5359131004ff725913100cfe725913100cfc725913137cff715
  | 18 => 0xd4359231004ff725923100cfe725923100cfc725923134edf3259231014fc71592310067c5159231126bc4159231004ff7059231024fc70592310067f76552310057e76552310067e76552310047e76552310067d76552310057c76552310067c76552310047c76552312ed7f745523112f3f74552311267f64552310c67e64552311273e64552310c63e64552311267d64552310073d64552310063d64552310c67c64552312d57f73552312d57d73552312d67d63552312d75e43552312e67e62552312e67c62552311273f42552312d75f32552310057c71552312d67e61552312d75f31552312d77731552312d77431552312de7e60552312d75c3055231125df7650e310c6df7650e310c4df7650e3139f5e7550e310075d7550e310075f6550e3139f5c6550e31015df7450e310179f7450e310c6de6450e311279e6450e310c69e6450e310079d6450e310c6dc6450e311275f5450e311275d5450e31005df7250e311279f4250e31005df7150e31007d77150e31007d47150e31016de6150e31017d66150e3139f5c5150e311279c4150e311dddc7050e311279f4050e310067f65d8a310067c65d8a3111eee62d8a31395f671d8a3100cff7658a310057f7558a3112d7c7558a310067f6558a310067c6558a3111eec6258a31004ff7558a310067f7558a310047f7558a3101cfe7558a31004fd7558a3101cfc7558a310067c7558a3101c7c7558a31004ff7458a310c4fe7458a310c4fc7458a310067f5458a310067d5458a310e67f5358a310e67d5358a310e6de4358a31006dd4358a3111eee3258a310e6ed3258a31014fc7158a310067c5158a3111eec2158a31004ff7058a31024fc7058a31004ff7650a31004fd7650a31004fc7650a310067f6550a3136e7c6550a310c6bc6450a310073d5450a31015de7350a310079d4350a3100eec6250a3111fac4250a31005f77150a31005f47150a3111ddf764ca3100edf764ca3100cdf764ca3138edf654ca310075f654ca310065f654ca3138edd654ca3138f5c654ca31005df744ca31005dd744ca31006df644ca31006dd644ca3138f5f544ca310075d544ca31015df724ca31017cf724ca3100ede624ca3111fce624ca3100ece624ca31007cd624ca3100edc624ca3111fce424ca31007cd424ca31005df714ca31007d7714ca31007d4714ca31016de614ca31017d6614ca3138f5c514ca3111fcc214ca311dddc704ca3111fcf204ca3113e7f76946312ad7e769463101e7e769463101c7e769463101e7d769463113e7c76946310057d74946310067f64946312b67e64946310067d64946312b67c649463113d7f739463113f5e739463113d7d73946310075d73946310055d739463113f5e43946310075d43946311367e62946310067d62946311367c629463113f5f3294631
  | 19 => 0xca511857c704ca5113f5f304ca511376f204ca5113d7e73d82510057d73d825113d7c73d82510067f63d82510067d63d82511357e72d82510057d72d82511357c72d82510067f62d82510067d62d825103d7e71d82510077671d825103d7671d82510467e61d82510477661d82510467661d825105d7d769825113d7e73982510057d73982511857c73982510067f63982510067d63982511357e72982510057d72982511857c72982510067e62982510067c629825118e7e61982510777661982511867f60982510077b60982510057f735825113d7e735825113d7c73582510067f63582510067d63582510057f72582511357e72582511357c72582510067f62582510067d625825105e7e615825105f76615825105e7661582510077b60582511867e605825113d7e73182510057d73182511857c73182510067f63182510067d63182511357e72182510057d72182511857c72182510067e62182510067c62182510457e711825118776711825104576711825118e7e611825103f7661182511857e70182511867f60182511877a60182511867d601825100779601825112e7e76d96310057d74d96310067e64d96310067c64d96310075d73d963113f5e43d96310067e62d96310067c62d963113f5f32d96312ad7e71d96310077671d96312ad7671d963113f5f31d963113f7731d963113f7431d963113f5c30d96310067f74d96310067e74d96310067d74d96310047d74d96310067c74d963113e7d73d96310065d73d963113e7f43d963113e7e43d963113e7d43d963113e7c43d96310067f72d96310067e72d96310067d72d96310067c72d96310067f42d96310067e42d96310067c42d963113e7f32d963113e5f32d963113e7e32d963113e7d32d963113e7c32d96310067e71d96312ac7e71d96310067671d96310067f41d96310067c41d963113e7f31d963113e7c31d96310067f21d96310067c21d96310067f70d96310067e70d96310067d70d96310067c70d96310067f40d96310067c40d963113e7f30d963113e7c30d96310067f20d96310067c20d963112d7c75d92310067f65d92310067c65d9231126be64d923135df671d9231004ff75d92310067f75d923101cfe75d9231004fd75d923101cfc75d92310067c75d923101c7c75d92313867f53d923100cfe72d9231004fd72d923100cfc72d9231386df32d923135cfe71d9231006f671d92310067c51d9231024fe70d9231004fd70d92310c4ff76592310057f755923112d7c75592310067f65592310067c6559231126bc6459231004ff75592310067f75592310047f755923101cfe7559231004fd755923101cfc75592310067c755923101c7c7559231006bf74592311267f5459231126be5459231006bd545923134e7f535923134e7d535923134ebf435923134eb
  | 20 => 0x57d74d8e512b57c74d8e510067f64d8e510067e64d8e510067c64d8e5113d7d73d8e5113e7e63d8e5113f5e63d8e5113e7c63d8e511357e72d8e510057d72d8e511357c72d8e510067e62d8e510067c62d8e5113f5f32d8e513ad7e71d8e510077671d8e513ad7671d8e5112e7e61d8e5112f7661d8e511857e70d8e510057d70d8e5113d7f7658e510057f7458e512b57e7458e512b57c7458e510067f6458e510067e6458e510067d6458e510067c6458e510075f6358e5113e7e6358e5113e7c6358e5113f5c6358e5113e5c6358e510057f7258e511357e7258e511357c7258e510067e6258e510067c6258e5101d7c7158e511167e6158e51117766158e5113f5c3158e510057f7058e511857c7058e510067f7458e510047f7458e510067e7458e510067d7458e510067c7458e5113e7f4358e5113e7e4358e5113e7c4358e510067f7258e510067e7258e510067d7258e510067c7258e510067f4258e510067e4258e510067c4258e5113e7f3258e5113e7e3258e5113e7c3258e511167e7158e5113e7c7158e5101c7c7158e510067f4158e510067c4158e5113e7f3158e5113e7c3158e5113e5c3158e510067f2158e510067c2158e510067f7058e510067e7058e510067d7058e510067c7058e510067f4058e510067c4058e5113e7f3058e5113e7c3058e510067f2058e510067c2058e510057f7650e510057e7650e510067e7650e510057d7650e510067d7650e510047d7650e510057c7650e5113d7f7350e5113e7d6350e5113f3e4350e5113f5c4350e5113f1c4350e510057f7250e511357e7250e511357c7250e5113f5f3250e510057f7150e510057c7150e512ae7e6150e5115f766150e5113f5c3150e510057f7050e511857c7050e5113f5f3050e5113d7e73d8a510057d73d8a5113d7c73d8a510067f63d8a510067d63d8a511357d72d8a511367e62d8a511376e62d8a511367c62d8a513a57e71d8a510077671d8a513a57671d8a510fe7e61d8a510ff7661d8a511857e70d8a510057d70d8a511357f7658a510057f7358a5113d7e7358a5113d7c7358a510067f6358a510067d6358a510076f6258a511367e6258a511367c6258a511376c6258a511366c6258a5101d7c7158a510ee7e6158a510ef766158a511376c2158a510057f7058a511857c7058a510057f764ca510057e764ca510057d764ca510057c764ca510057f744ca512b57e744ca510057d744ca512b57c744ca510067d644ca511357f734ca510075f634ca5113e7d634ca5113f5c634ca5113f5e434ca510075d434ca511357f724ca511376e424ca510076d424ca5113f6f324ca511375e324ca511375c324ca511376c324ca511374c324ca510057f714ca510057c714ca5125e7e614ca5114f76614ca5113f5c314ca511376c214ca510057f704
  | 21 => 0xd7550d320055d7550d32015df7450d320179f7450d320079f6450d320c6de6450d320c6dc6450d321479c6450d320c69c6450d321475f5450d321475d5450d32007cf7250d3200dde7250d3200ddc7250d32157cc7250d3200dcc7250d32016df6250d32017cf6250d321579f4250d32157ce4250d321579d4250d32005dc7150d323cf5c5150d321479c4150d32157cc2150d32005df7050d321479f4050d32157cf2050d320c6ec7650932014ec7650932007cf7350932015ee7350932015ec73509323bfcc7350932015cc735093200eef635093200fcf63509323bf6f53509323bfce53509323bf6d53509323c7cd53509320074d53509323bfce4350932147cd43509320078d43509323c76c51509323bfcc31509323bfcf305093214d7e75d85320057d75d8532145be74d8532005bd74d85320075d53d853232fcc32d85320077451d8532004ff75d853201cfe75d85320067e75d853201c7e75d8532004fd75d85320067d75d85320047d75d853201cfc75d85320c4fe74d8532006be74d85320c4be74d8532004fd74d8532006bd74d8532004bd74d85320c4fc74d85320067f54d85320067d54d853200cfd73d853232edd73d85323767f53d85323767d53d8532014fd72d8532376ed72d8532006f751d85320067c51d8532006f451d85320067451d8532376f631d8532376dc31d853232ef621d853232eec21d8532024fe70d8532004fd70d85320075d539853211fcc3298532006f761985320057f755853214d7c75585320075d5358532107cc32585320075d531853231fcc3218532006f56118532007745118532004ff751853201cfe7518532004fd751853201cfc75185320c4fe7418532004fd74185320c4fc74185320067f54185320067d541853200cfd73185323967f53185323967d5318532396de4318532006dd4318532014fd721853231eee4218532006ed4218532006f751185320067c5118532006f45118532006745118532396f5311853231ef52118532024fe7018532004fd7018532024fe76d81320075d53d8132277cc32d8132004ff75d813201cfe75d8132004fd75d813201cfc75d81320c4fe74d8132004fd74d81320c4fc74d81320067f54d81320067d54d813200cfd73d81322c67f53d81322c67d53d81322c6de43d8132006dd43d8132014fd72d8132276ee42d8132006ed42d8132004fe71d8132004fd71d81320067c51d81322c6fa30d8132276fa20d81320075d53981320cfcc3298132006fb60981320057f755813214d7c7558132005bf7458132145bc74581320075d53581320afcc3258132005f77158132005f4715813214d7e75181320057d7518132145be7418132005bd74181320075d53181323b7cc3218132005f67118132005f57118132026fa6018132006f960181322b57e74d8e51
  | 22 => 0x81432f79c43d8143004ff75d814301cfe75d81430067e75d814301c7e75d8143004fd75d81430067d75d81430047d75d814301cfc75d81430c4fd73d81432f67f53d81432f67d53d814300cfe72d8143004fd72d814300cfc72d81432f6df32d8143004fe71d8143004fd71d81430067c51d81432f6fa30d81430067e65981430067d65981432ff9c4398143006fb60981430067e65581430067d65581432a79c435814315d7e75181430057d75181430067e65181430067d651814340f9c4318143155ee7218143005ed7218143005f67118143005f57118143026fa6018143006f960181430c4fe76d9132146be64d91323ffcc32d9132004ff75d913201cfe75d9132004fd75d913201cfc75d9132154fd74d91321467f54d913200cff73d913200cfd73d91324067f53d91324067d53d9132406bf43d9132406bd43d9132014fd72d91323febf42d9132004fe71d9132004fd71d91320067c51d9132406dc31d91323feec21d9132024fe70d9132004fd70d9132146bc40d9132406df30d91323feef20d91320c4ff7659132146bc64591323eddf73591323f5ef7259132157cc3259132004ff755913201cfe7559132004fd755913201cfc75591323ecff7359132006df73591323be7f5359132154ff7259132006ef7259132004ff7159132004fc71591320067c51591323bedc3159132156ec2159132004ff7059132024fc70591323bedf3059132156ef20591320067f76551320067e76551320067d76551320067c76551323e57f745513214f3f74551321467f64551320c67e64551321467d64551320c67c64551322d57f73551322d75e73551322d57d73551320075d73551322e67f63551322d75e43551322e67f62551322e73f42551322e76e42551322d76f32551322e75e32551322e75c32551322e76c32551322e74c32551320057c71551322d75c31551322e76c21551322de7c60551322d75f30551322e76f205513214f5f7654d3201e5f7654d321675c7654d3201e5c7654d320075f7454d320055f7454d323df5e7454d320075d7454d323df5c7454d320075f6454d323df5e6454d320075d6454d323df5c6454d321675f7254d320074f7254d321675e7254d321675d7254d321675c7254d321674c7254d320175f6254d320165f6254d320174f6254d321675f4254d321675e4254d321674e4254d321675d4254d321675c4254d320075f7154d320075e7154d320075d7154d320075c7154d320055c7154d323df5f4154d323df5c4154d321675f2154d321675c2154d321674c2154d320075f7054d320075e7054d320075d7054d320075c7054d323df5f4054d323df5c4054d321675f2054d321674f2054d321675c2054d3200ddc7650d320c6dc7650d3200cdc7650d323d5df7550d323cf5e7550d323d5dd7550d320075
  | 23 => 0x57d71181530067e61181530067c61181531957e70181531967f60181531977a60181531967d60181530077960181531977a30181534277930181532ed7f765954315e7f765954301c7f76595432d57f73595430075f735954341d5f73595432d73e43595432d75c43595432d71c43595430067e62595430067c62595432d75f32595430077771595430057c71595430077471595430057471595432d75c31595432d75f30595432d67f73595432d47f73595430065f73595432d67e43595432d67d43595432d67c43595430067f72595430067e72595430067d72595430067c72595432d67f32595432d65f32595432d67e32595432d67c32595430067f71595430067771595430067e71595430067d71595430067c71595430047c71595430067471595430047471595432d67f31595432d67c31595430067f21595430067c21595430067f70595430067e70595430067d70595430067c70595432d67f30595432d67c30595430067f20595430067c205954300cfe76d894315d7e75d89430057d75d89430067e65d89430067d65d89433f79c43d8943156ee62d8943004ff75d894301cfe75d89430067e75d894301c7e75d8943004fd75d89430067d75d89430047d75d894301cfc75d89430c4fd73d89433f67f53d89433f67d53d8943156ee32d8943004fe71d8943004fd71d89430067c51d89433f6dc31d8943024fe70d8943004fd70d89433f6df30d89430067e65589430067d65589433bf9c4358943156ec625894315d7e75d85430057d75d85430067e65d85430067d65d854337f9c43d8543155ee72d8543005ed72d85430077451d8543004ff75d854301cfe75d85430067e75d854301c7e75d8543004fd75d85430067d75d85430047d75d854301cfc75d85430c4fd73d8543416dd73d854337e7f53d854337e7d53d854300cfe72d8543006ee72d854300cee72d8543004fd72d8543006ed72d8543004ed72d854300cfc72d8543006f751d85430067c51d8543006f451d85430067451d854337ef631d854337edc31d8543024fe70d8543004fd70d854315d7c75985430067e65985430067d65985433879c4398543006f761985430057f755854315d7c75585430067e65585430067d655854334f9c435854315d7e75185430057d75185430067e65185430067d651854335f9c4318543006f56118543007745118543004ff751854301cfe75185430067e751854301c7e7518543004fd75185430067d75185430047d751854301cfc75185430c4fd731854335e7f531854335e7d531854300cfe7218543004fd721854300cfc721854335edf3218543006f751185430067c5118543006f4511854300674511854335ef53118543024fe7018543004fd7018543024fe76d814315d7e75d81430057d75d81430067e65d81430067d65d
  | 24 => 0xd741855316d7c74185530067f64185530067e64185530067d64185530067c641855301d7f73185530157e731855301d7d73185530157c73185532ae7f63185533af5f63185531657e72185530057d72185531657c72185530067f62185530067e62185530067d62185530067c62185532af5f321855313d7e71185530067f61185530077661185530067d61185530077561185530077741185530077441185532af7631185532af7531185530077721185530077421185531957e70185530057d70185530067f74185530067e74185530067d74185530047d74185530067c74185532ae7f73185532ae7d731855301c7d73185532ae7f43185532ae7e43185532ae7d43185532ae7c43185530067f72185530067e72185530067d72185530067c72185530067f42185530067e42185530067c42185532ae7f32185532ae5f32185532ae7e32185532ae7d32185532ae7c32185530067f41185530067741185530067c41185530067441185532ae7f31185532ae7d31185532ae7531185532ae7c31185530067f21185530067721185530067c21185530067421185530067f70185530067e70185530067d70185530067c70185530067f40185530067c40185532ae7f30185532ae7e30185532ae7d30185532ae7c30185530067f20185530067c201855316d7e74d81530057d74d815316d7c74d81530067f64d81530067d64d815301d7f73d815301d7d73d81534367f63d815344f5f63d81531657e72d81530057d72d81531657c72d81530067f62d81530067d62d81534375f32d81530057e71d81530057d71d81530067e61d81530067c61d81534377a30d81534377930d815343d7d769815316d7e74981530057d74981531957c74981530067f64981530067d64981534457d73981531975d73981530bd5d739815319e7f63981530df5f63981531657e72981530057d72981531957c72981530067e62981530067c62981534475f32981530057e71981531977671981530057671981530057d71981531977571981530057571981530067e61981530067c61981531957e70981531967f60981530077b60981530057f745815316d7e745815316d7c74581530067f64581530067d645815343d7f73581530075f73581530dd5f735815343e7f63581530bf5f63581530057f72581531657e72581531657c72581530067f62581530067d625815343f5f32581530057f71581530057c71581530067e61581530067c61581530077b60581531967e60581534357e761815316d7e74181530057d74181531957c74181530067f64181530067d641815301d7f73181530157e731815301d7d73181530157c731815319e7f631815342f5f63181531657e72181530057d72181531957c72181530067e62181530067c62181534275f32181530057e7118153
  | 25 => 0x91532ee7e32d91532ee7d32d91532ee7c32d91530067f71d91530067e71d91530047e71d91530067d71d91530067c71d915316e7f41d915316e7c41d91532ee7f31d91532ee7e31d91532ee7d31d91532ee7c31d91530067f21d91530067c21d91530067f70d91530067e70d91530067d70d91530067c70d915316e7f40d915316e7c40d91532ee7f30d91532ee7e30d91532ee7d30d91532ee7c30d91530067f20d91530067c20d915348d7f76591532ed7f74591530073f645915316e7e645915316e7c645915316f3c64591532d57f73591530075f73591534855f73591532d67f635915315f5f63591530057f72591531657e72591531657c72591530067e62591530067c625915316f3f42591532d75f32591530057f71591530077771591530057771591530057c71591530077471591530057471591530057f70591531957c70591531657e76d895316d7e74d89530057d74d895316d7c74d89530067f64d89530067d64d895301d7f73d895347f5f73d89530157e73d895301d7d73d89530157c73d89534767f63d895347f5f63d89531657d72d89531667e62d89531676e62d89531667c62d89531675f32d89531676e32d89534776d32d89530057e71d89530057d71d89531957e70d89530057d70d89531657f76589530057f745895316d7e745895316d7c74589530067f64589530067d64589534657f73589530075f735895346d5f73589534667f635895314f5f63589531657f72589530076f62589531667e62589531667c62589531676c62589531675f32589530057f71589530077771589530057771589530057c71589530077471589530057471589530057f70589531957c705895316d7e74d85530057d74d855316d7c74d85530067f64d85530067d64d855301d7f73d855301d7d73d85534567f63d85533675f63d85531657e72d85530057d72d85531657c72d85534575f32d85530077741d85530077441d85534577631d85534577531d85530077721d85530077421d85531957e70d85530057d70d855345d7d769855316d7e74985530057d749855316d7c74985530067f64985530067e64985530067d64985530067c649855313d7d73985530075d73985531155d739855313e7f639855312f5f63985531657e72985530057d72985531657c72985530067f62985530067e62985530067d62985530067c629855313f5f32985532ad7e71985530067f61985530077761985531957e70985530057d70985530057f745855316d7e745855316d7c74585530067f64585530067d645855345d7f73585530075f735855312d5f735855345e7f63585531175f63585530057f72585531657e72585531657c725855345f5f32585530077761585530067e61585530057f70585531957c70585534557e761855316d7e74185530057
  | 26 => 0x38050014000006800000200d001000400c001000806c02a00b00080140000020090018012001005002402a0040038030024004007802c0200010028004000006000008000e043006805000c01700200180120080008010008006000810800a003005010c00800200080100060000000000004002000000801400c001800800000700081d802a0090098010010000004800c000000000800801a0080048014008001005003c022006004000003200800200d4010000000802000c0010040000000000006000c002004000803c04e0020098000012003000800000800200000200000000020028016009000001c002002003801c000001004801800400300000000000000000008020001000007800400300100040000000008000000000004800c004000002000004c0010048010012000001001404e00400380140000070000008002000001001c000009002806401e0150008000002000005801c00200c0000000000012005824c01000400680340000010030020002000001800000c00c0040000042001014000400a004000005400c005001002800000200300080040070008008000012004000c01c003000002c00000000f000c00e0090000008000002000000001e004000800000e007002801800000e007000000200500080000000020000054006000000002400800000080040000030018000000016002800c00200701c00a001000000500600020020008000000001008000c004000001000400e00000300680300850028090000003003800c0000030030000018009004000400a00b002801800a0000040004006002001000000600e030002000400000200a80020040000000002004001801400e001004001c00001a0020058034000000000c000012001800001200d0000048000006000009800600200180b80000040010000024002001801405400000a801404000700b0004008000005000000001201a001c018001001800402001700a000000c000000001c00a00000400140040050058014004002000002c01a00500c003c02e007009801001c00200000100000040000014000004000800000000349d7e76d91532d57d74d915316e7e64d915316f3e64d915316e3e64d915316e7c64d915301d7f73d91530157e73d915301d7d73d91530157c73d91532ee7f63d91534975f63d91532ef3f43d91532ef3d43d91531657e72d91530057d72d91531657c72d91530067e62d91530067c62d91532ef5f32d91530057e71d91530057d71d91531957e70d91530057d70d91532d47d74d91532ee7f73d91532ee7d73d915301c7d73d91532ee7f43d91532ee3f43d91532ee7e43d91532ee7c43d91530067f72d91530067e72d91530067d72d91530067c72d915316e7f42d915316e7e42d915316e7c42d91532ee7f32d91532ee5f32d
  | 27 => 0x6001000000c002013000002c04e0040010008004002001000000a004000003c002020007803c000003002001c03e00a002803401e00400000040040000048030000003000001c00000b002803800600000080100180080060000008013003000000200300b800000200000700c00020020000024000000002001806600301c00080000020018018002007001800401200000201a00020060068020004000008800c028000000801000e004000001c000007000002400000c000007c01400a00000000000080038000004000000000000400f002804000001d00080140180020030000000000003009c000045000800400600a0008010006007009001000a0010000000014004009800800202a000800000800b0000050018014002000400200700080100020020008014058001008002000800a0008000004000005803400600200080100080000058014006003006000c000006001800c000000008800405c0010000044002001001800800a001013800800c009003801c020001000801000002d0010024016002000800402a000001800000601c00b002c00000001200340000010008000000012006802c000002000002003201e00b000001e0010048004020000001002c0000160000000002008001000000c00400a00000000000000008000006000001001800c00b800c0200040018000002008001800800400200280000080000008000000008002802400c000012002002c000003807c00a000005000801400200600140000050078008008000000801802000000600200380000000000004000000000005e000008008000800000080040240010048018000000013804008400900c802c0000000000014000004000800000000500000100060020030000016004006000c000000001003007000c005002800e0070028000002008000803400200c019000c00202b00200c800000000000340000080040004012033001806400800100480600320030018000000000000000400201d00080040020020008038006000000002800600a000800c016006000800c000011001000000a00200280000000000028020002000000800c00003b0040000000005002000805400500580140000040000010000007000000804a002000800c0160010010030002002000800800000a004000000a00200000040080000058008000000007001401a001000802000000b001800000c005001800000a001001804001e0020030014000008002000401000c00f000000e0010020000002003005001400200800000000160010008014000000001000c002001021801800c00200800080020000010014004004001000c01c001001800800600400480180160080070000000005001803001c001001800002e000000000400600600b802c0140120020000002011
  | 28 => 0x1fb13e8152e77f01f665412563ba0a0c000183a00009180001a58222c000000014800001800f001800001600100000000280030000048000004000001400000300300000000050008018000006004802400e00c0030018006012005001800a006000000800c008000801800002b0000000026006001000400200800180140040080070000016001001800000a004003804c0d8002000006400000400000040040020000004008000000000c000000004805000000700000d0004007001802c00a0010038000000009003800000000a003801c00a0060020014000000000000000000b0000000000014001801400a008002800805600a00b0014000024000000000a01a0018000002012000800400e000000000000000500000000000000008008008000006800000001000300080020000128010000000003000c002008006800400e00b007800000200a00b002c006000000800c000021004801c00000f00080000960000030000008001000805800000100100000020090020004000007000002c000000006000800000402b806c000000001000c004002000001c012000005001800600000000000140000000030016003001800000600000a000800200000d002800a00000080180660000080004000000000800002a00a010800000000100080140000080018000000003004004c00000000e00000080010000004002001000805401c0000118050000001001800800200000f000002603a0008070000001000801c02a005002800400a000000002c0140020080030000004000015c002007006800002806b004800800802d00000000040070010010000002000804400c006005000800a00000480580020010000000038013002800c000000002002000e0070000024028010006801802401500b8040008004000001000600700000080120030018000004001001801400000000000180060000048000066004000801c020005001801c00e007001800003a0380010008000008000000800401a0000034000017002000400800c000001c02a001001808800c008001801c0060060088010008000000002c02a003000800c00a00505b803c00000100000300180020010028006002004800800800200c800000a00f00080040120000058030004001000003c002004000000400000700000040040020008000000001003000000800000000040000060000000006004000801801400600900100000090008014002002000000c002003007800c0000170078004000018008802c004006002800001600e001000400c0020018008000003006000c00a0010040000004001000816c01801300d80880040020028000006000003002c02200000180040040050010000002012001000c000001000000c03600a003002c006000006804401000001e800
  | 29 => 0xd1033c453d0b0ca867aa0ed038793fa01f4000039825302d12fa10ed3a834c0795700987c47700000d69c1a7c80e8a00000162899f8b735825a74700005ac8b3859e8b750b7129c6c820f03c68c6222a1a4e354000000017be37e80e327e90f40000000000000059a80002738000000000045e8000015dea40001cde0200eae193a192752c0000000000000000000004ec0a00fa269d1d9e0001ce80001a502ed0688000034d000148173d9f0a0fe21ec778957668b86e61e18c464ca174a10b4000524800055000007298000362800014c01e459293184fa040100012400001fc536c08d0000000000021a82110326355800040d800006f8000392800084580000000000196990c5eb91642c794d31492224573da8e33900006bf1f4416293e47f00cf25552086416c000578800089e13f91e985560000e7021d001c25e8e36234800023ca0e06a90bac0000b4f3254000000000026b0c8a0e3918672f072850a988e39b224e68086921cf1cb67ff1b2a6228a9c7bd0c9a2ef12d836194565a081983f84cdc0001cfe2605234742158e6b004b059b156a0001e6e0a284561fd8e1481913de19657246ff0ac271b094204d1d881a0042a69ec21024e8e1a02a109a7c009146f2c67c3b7187e267c0e06280f5c2bb95884a203b069f1bd6000000013f89534a100007a51a1240409b8523132c27cd1542649b640b101b75319c8a000000001d960d1759cc20000b8c6d0dbe458793005c9800043b11bd000044c510130800001a32864af07b781870101f465f38b2a44ca16e01ec00025814bf265000064da0d66c0d9761f51c5430a8da410e06ea3a200000001bb40000000000000016b000055a00000000bc56c0958288f00000000336329144465a14dc00000003b180005c8028608f83281199a482c0800000000006e680002234000426193a6400d9a32b8000662c06400010c2482096a67f86fa7671b300d4e1f63a19eb452a20683399f6a41207ec52790586049e06741c65c8b399d64549db07e2535c43cc779612094e4c28ada15043f6232a0b24e919064d583d078d80004f9d83e6f4800000004c70000000088c00073e145821a50814da8ca0338d112634000022309b01849f022031df517902e68689a7014f9b322ed87c90001d151edcb7300017bc40fd9aa22104ae406064b42d08b41a19dae0000c4c42c800000010ad702114e0001b1f0551cd800000003db80001fc84a300004316c5800000010c800019600ff601c0bf8a3a31800000001f5a3f6800035f82511179c7c49d0000348800056a0cb200001184b39248000000053f000000000000000b140000707000000022600004ae0000000000000021a000000003778000000048e000155e0000000000000010fc00023f80000001978564953a076961a2d31de500016365729b6e
  | 30 => 0x1e88bd040883924d2000048288205461bd43d68ade5f80000000169400008801961e66464023427417de000000056f0cfe3ea96f281c830e04b19a285c00004d621b40d590d600000000f214d15f89d05132878e0000fb00668eca4ab000008380005909ada2dc80001a1181e062400000018680001386796829f00280000000adb00004a600000002c9400000000000000000000000000012a000000005bf00001c1000043843146569ef03b78c764bbc6140e5c00000017d213a816200022e050600002d5007800013dc000000000020540000aa601f1dc085c8dc4000000000000001dc13bc8301b8c00000883b586e2000136809a400022f8f500000d2c00000004bb9134609172200c1d1a00017524698766780a0f8000117c80980e8776049e6ba9920551184402c8ce862400006c05dfd64f88ee25b0788687990e000099a78c9df647d9af03ef04a75c703cb583a0b02a30bda3f014fe63600007f562ba6139ca876020665dc97983fc82e23da0d6424e1e565dd0000632a00a6980fdf7599cb816a85456f0167c41b9fac8468b2600000001cc9eca0001e700538f7455b000000000004d6913000014340000000750000042b000027f92c6891042e2ad08540000ec26e219ea00014de00010fc7f2da474938324765800000000007a582220001bec1b0000043b8248400e06e0000d342aa10780f0d5dc7591346000000067a180a2c7c00068a96b57ae80001b21d48000000000001c20441b4962002400000b7e0000000000000037c8338000130476e0490684000000000000001a5a0001d9268a000030c098e5f504b600005c662c0ca600000007aa8000000000068b18ee0001eee22b01e02241ae64fc89a8541c000103229c25911ea000000000000007570a6227a940c0000e622bf000048a800058556465148d61605800000000008100000000000027f15504dc968c304d2d508f0a7e00000007bb176610293c482907100cd039d0630000000151a000000000000007c20ab87d992dc500046425c800015e000000000cb646c4083e689f7000213a56b824e40e85600880bca000000000001060000f022f203502de400020493ec7e015a00f78ee6136a02848b00006b81f60376c0000000afd0000f3a4ce09c8614123600000007071c4a0ba8000000000000000000000000000026c6f100006eb80000001de63af04a44b68000000124c00000003605dc60001cfa3231f82000000008c800019249326b796568849e5c23f00000000bdd320000060d887000002c01c391a00c6400070b800000017a634605c807c94f4000000000000001ec8c520000df1000126e00000002969da437b170e48000007b5095e57b00001a88e280b4a2bc34a0a881ee161c3d20c5452b1d0d5a116a2055930c0000b9a10622100d20b5c000000078b
  | 31 => 0x21f40000000000000075e000000008020000000799000000005060ca4ba08ac96662ce8e08115df27155208a71bd1163dd8f065429dc8794876a535000000011920001072000000008e4712000179c40e00000ec8000000034a89a06044c68c1a06080004a1449c16f9a5d39988b81ad96223a522f40000b4a432855c6299228000109e0000daa63b1118000183f0001b9641803b600019660000d4e5a95258000229659104922749aa2000102700002da3ed9a2651652c07d9400017f8b2b8579f4800004d489c80480000efc5191a78000000051cc0002f3c00009986e802e18be36959307f80000000226c0001ca039d8c184c40b86480800000000005658000643400012300000000298258ca4a58590c000013b8000000089f000000000000000cec0000636596800086a8000110000011e0000000149f2df01d43d121e42ccc00000000007ad8a425e2218008e981437a00004f607f9000000072e80001b100005780ed200000001308000000000045080000000f2c671000011a0b98766926c00019330001e21040800000000003cc00006e380004690000481810800000000f440001621a9e581941a03009a50001cf76208cf68b99ed60468db80ab1f3877d1dde32e1ddf5cf1c8040f9ef27e6e1d46df06be23d89dc786128e51d0d162661e8b0324b01000192a7569c482ee94ce00009f8000105e7689fe55ab09a700c997e286c8b24a61f5c7b38a681e2c38a7559105766000080400fc00010f66a740f61ec16c680b8000000050c2820d6600020c21fe97da26100003b3800054e000010540da3c38a7a00003eb6e81d283e2945400018b86ce47e2106800054f1a247801b108261b602f1000077c9c3712a9ff00001f257f116170118f3c42402bc0ee1da021f8b770df922e00001f77d78b06279210c54700001b86176000171e000000000012273b81b4c52b9135635926008299557db000027b0246650000005a09d81610000723000057685a480d0e8e237915c6cbd5b63608db324200005088d680000c9e372168024c0000642070c3ad505000000000001b470000ca880f000059d0000876800038485af1b24b0a5e1195e00007ae000039a5078000409a246899a0aa076e1000510af630b86b000015e45b711ac0d397c418f02a487880005fac0000000216461114413f12fc37d01863f9db2c06e82b231c816f5028722000000001a17d800019cc84b82e88a49c5e2a501a64c1a0484349ab06279eac35f0b9e1ae8db434258b25d682ba5bd8de40000000358800000001d8413800064b628e0001506350436c3750f8e5f00cea05c97940001f1602487196d4883e60ca29a0a98b182bd5caa67f14270000b640001ab217b95027a8947b481017c616565217997dc3fb88e77a41d346c490da65c8b500000000608846062e800
  | 32 => 0xc81dca1a4074176c310150b41080002659e235478f75000173658d18743270af800009be7b2c2e402300004cc8bd4000043779217b800009443cd00004e6010444d8b32000010c3fd9988536148a0ca886c4870a3436ac72e1f98f8c1dec00000003210e5000008b88f721dcba26fe8cf531390de4c9800026c800087722ae2cc4249498902400003ae30884671f7170c4bad63a7481ca423e80007491f1e6c8d23a364000005a81f400021c02a80d472a40b2262697e51bf0b76114130e5bc000005d80001f59c3400004ce308c0000000000117c00033e0ce12c119c0000102848648671779b540000d0c2ad528048320d852f06183a41a3021549166b48cc2431884a697908a0dc1946647059c43a1c1e7f09f1a692807e2131b801bb40000bc03d622b8cc400e0ad606ba21604a1aca073969000021fc4bf55c8000208e000077e34509867b100004ba202a21222cc000172e216219633395ce2268d9e53580000001886246921e000000000000000bf00005dd8f4c00022e20002204000000000006020c880006b10000728800075395201b3800016d00008ba000062b1878816902a2e49a0a3df81438bd8fe262a0c5e55e8d841bb84e673221ba1708b660170f6c0001f615d500004bf8aec0000b60000186068218de6c8481c7838bcc3dc92f2000035278c00006f9a21e036111e28400004ec1ce477100008aa88ec4d0a27600011727d58c6460c0c081ca820867802ec5e3961f000181800000dc5259a3f0001fc763c86a600007ca000000000000003bd0be01391074000000000000001ecda3400018e6053167880220a031b06ef77e979e033131232e8d4065515866c000d04a413f044194b22db961807f8db56c9000066b0b42607dbaa355002e8068ba46720bae2219d3a13d800603b87403f802ae78a1c063958e8c0000fa63a4400019d80003050000000008a50b062e695000054582702d100002b600176fb8efe37c2030359df21636800038801fd000000000000004ea80000001b66000000005f9bac00016aa831000000000001b74000262228a66c80000001de100006244bb00000001e1100000000001f0600016ce20d000074da078086800000002905cf9ee000000000bc85012d580000001e4c08d9057000028c0e61b1a0000b6b8ba86544cd469000000001ae40001ef073005b1a5606212bd575400054418e20000cd4000021e4d79b68431000013b800000000005e5800000000000000000820000000019ec42a811c346613c31e619a650a0e434f008225621ee86105920d8c0004a99922479982802f1d5e1d697406d88ad4219842413308e020a8900669000029c874257b9db245318f456c8dd61d3800053054621f19fa641a0e5a09a096888698c45330bc003c0ce05de87682b31fae31d09a00450a9a00008f500
  | 33 => 0xad000077c1c160000f8600000000001f9c0001ae21df409c000000039ec0004ac100424b904044b97785c1a084854097400004b77841d380f4d7e80000dee782000012218d753901ee7580000797909c0cb020489d05a034197ee72790566009e46468800061894bb24321cc0af8fae675158000001640000c1e7af99f023700723f980000000000000000006d400068e8790000000000022ac7fe812e38f97c81b9038b55096ae00006ca80780000000934000000047f0351429847c65284656bb08c821cc8cc33bc1a151e81800ed000011485121d313fe1b3057a11b8e1847f8000093c41667c8c340001e6048f030300000003a000005f5800000000004ca89bd77242606081fe626000000000c5632c111c000070b292049a215dea600000006bb947f3335a9a5a1db082e38000000000000000001bf916a000218e2cd00007cb000000000000000000499a0827a802640d24b121c000002731b78720a29e0490c9158991603b3c85e7f720cc53c10d00000df61ab860e3e00000000000036800000001120000216c736866444f95a60000e1f8ad8b5e5748e9e00000000eb0000425069c7080bc66af119a00004c547b054e76e8a500000fc229d04de1ae207c000209a5ec0d380000000000095434105530000000000077800000000000d70564154a76380006d58000043800000013840e7000000006f300012a2419000083a16d282706f852c12de1e7997088b1269000000000020360b2890e5f2923033580d20000f844080000733192e64b00007411f3228011e06ae043300013ba39488525bd174433290000001f5853b08f00000c280000e161a39428000214a5210dfe6770d6a718928c4be21045800fb87630000000000000000000038a22500e00c13804f46a622a666422c2000000023aa15c57c000000000000001a43000000001314d23f386da300800051200003f3000050c8f2a00011014b8000011c86b40aa80001eb011653d89f504a80004ed8000267900200015aa7a48000000000000022de00018d900005227ea00007ef01b800018fa000000079280000001c7a61b40005ed0000384000069006e07a60d0a837066862f001d018827271093eb1ddc1a40c780008a209bf0a880003218dea0320000000086200018ae5b29a040001504336000017e80008b20b0e0000cd27c3800068c80008b6218c0000de361d524b5004c006590d0b8698a6a5291c6818b1ae815086527d402b40a59fec07997f055c0a287f900006b5217e109800000007c70000e74000138e1f0800000022a03fd000000011ee72205fc742cb20000052816e83f251695225321a002b907ba127e2ca3f120061e6842f172800014e9aa100021d06d396c472119d86f20224236a0e234a99b02c407083c982b820508e822d856c1129296601859e0f004
  | 34 => 0x3e2200157440d15d06ad1fd2399c36d7e28eba63f0e9a8470a1c83188a66af8ea468181842da1bd01f78cfa82b82a064f5eda51298f0779228636c836e8b5a0144220ad91c6ce32206874855896c9104cf6a48904614cb84bc842223069f40a216c037c48e1f4c470dd8b073d8db709840e5fa8d121288cc847680201d889f615a8850503daaa0449e1c2625394131017001d009016081b252d0af30678fd40cb9fa4647986e2ab083a7d45b505b8829580114252af10dc897840033d13b24c801c088d140e1db1ec079d9b2514c9c2c8be9654154996e742a1d221d98f683e800083f029e0dd1b1e00b1e8c000000011e8ba57a78760242957e1ed80004490e5f309c39b6c51fbe51e0c8800007b900013c91bc443e142c34f08c0000439113a0001c3e7329fca00000003c203826791c767449e1434d9558062855e4d986c643393e02dc00005d58fd607a05f8205a1c4740c1c6000199600022da000043613e1e7e2d48393249000029e077463f8afe71c113c67b50b000012c21b400002c3059a1b5029a0b780005be066a588205023999585ad00006f700007445f260730432341dc382bd0d0e10a000072394262f6026a09f57a06f790664e81460000128d2cf99f8000000000000bf3700a16000000085d1a812f4938a54d1232828914867e927c12c93f867391707001d1e11d8d423af99d0000197a27ecd3d5a6800031f0d24894207a197451a00011940c69ba6193160a38f166e60109a466b86a8724969f000055152a970400015b87dc0aca745cb3c31e203e0001d327f8800000000001cf9f3c0001876789d2a749a9f4a0001d684de00008a5101c68391f219c80003516076500a0520f680000001b425da1d42000000064681217e496ea79d19da8721ad54e4964847d0e983fb1324661005850120ba0001c9c825081e00007260d61a840000c8e3f61bc67e60f4600000000ddcf1c0f1621432d000000017cc0c2223832e585c00000002e121820001bb0000079442b8cf000007a47474dba2a3989673017e7000000000007fe61bd3fb220cd0122e571646580000000ab671909a100000003fa1e7c00000000000b303d58000187800015983180000d0500a00002310e5c655840230d8000000000078300000000000000000000000000d505e01e6000088394e254a8b9476f9cb41048eee202227a0000a38000182c609886e7c405da0f80c32000157c2e5800007700000000c4a5f8cc0e4ffce6e00000006e094421d50000000000024b1096633159a0001610365000077491a80000000000184c00000ac80900007ac80003e58a40158925c15013c759704ac0001fc650c4ddd0001482489800014a800000004f03e7054a000000000000002fb0000000000088002d488d9c8600000003ec80004068590614800046ba08836b408e3
  | 35 => 0x81b0000000116827c003c4e7800000009367ee80006b41b0629d94b8072134400000000000000000000000004915f19e20678a1107cb800072b0aae0000000413da1c78f1e9c6ad800053e150852800000000b4671100001bddd4474d600e26f12d619d0aa21f4850a3bd91e438e9526378495683d1a6a68318dc88083ff690612c64e0dcc50a4d7d835058e388d5e68b91f5243f8c44328861078142012f0878a65a9b6a3aa834b2b821606918a6489a99c26ee933a58a09783de45865af0c9432584dc68f0ea22d6211235b862219b850269b168339097300fa582a7ed121854c9ef823c45a82569afd6339a6435718d51164d7a42909025e084103f4205c7ec1f8875284826bd80343a2572c73705504a1cbe4377000001b060a5b00b690000ea03564f104bc427641959980e64892471941114245167f31f342d20a1e86f06700e107ee6a7c3a27a4d43642482e038191fa1f6048043b616477b985689811aa3baa0004469ec215684ba43e800070a91f858f063a0001a2202e91bc05480e22cb53144678fc837490464bfc62800000006bc83fc733820c35680fe3ac1ad80000000369deb90001e86000000000001603828e00784c77a000191047495943b011e27fd1f4e3d81adc4638b8247612ae27561fe456210e347096626e86346df980816c89f93761e784c7000000000000f713520001870452978c4aa81d263e11ca74f09de7e51a367441e40000000000000000adc82c11d044669fc00000000006c61fea198db2e862843909093160000dc63a1cf404111556095833c4e30ecc70a00004f080007010a360da80003140000714201838b9a767d9000044b0f9413e9eb04f99dea000000000017b223080006e500005759e801295ffe1088e2a3fe9cd221a1528789987900006940bd1aa886400f47f20ce24609410496a26e7b480000570ffc6ee00002b24d2e1fe054c00980003eb21e6000162e000116e22f207e3d2880a79e90325bea28c0a39f545d8016e000011d208929a0000be60001a5f4a2d96c85986bc00010868489da8014000000e8000686950075497ac3bc02c75b0893e499205683280000000a0435b08d602049762fc98e4016a0384b312c82c9013c5b81ecf2c583a600014144f50d082f71fb374250a8603103c2b2013b33f053c000107c0fc0ed82be4afb7848cc01d79ec821181f91c707e805789e274a90e214798df74b21de0001a165c29b7024815fe6a408ce1ef99f4165961407288e20fb4a322f58c0444981b456b0a96215985e333091e2570bdb0818f00790400002597f865497f27e6400001081a058207fc0000000278047000000003c1133e75a9dfe4094a527e11e1a4b440003798000599049582a1aba00008e54d149f440c0c2603a8e717da21fa51a146673f056e2f880a4645958c6719
  | 36 => 0x5c4833800071000003ea000015f14e67f7cbc164908960000000031843d0079bf67bd800017a03a4000151400022640d7828825296a6000228209d049852216f300017a200004941f900000001c66788800059819268550ec4000000052f800052887097f8579a00010591d7172827181e200003756d181f80000000000000000000000000000000029c08b0000152000014200000000000128400085e9fde1d90fc63a5936221f22b0000108000020581a69d1406aa10a00003950000000000140d49ac000334209600013ea4661df9000000086d95e8000141606595520e20f1600011667b3400000001b000018810ef87ea000198e00000000001d7e46ecc0a05140004cc5f7e7e400001d2cd4c067155c351a0322ff1cf94f58ac100003d85ea043549485804b29b9284a00000d9808453811cc3900000092d2c483c846200018c83b920d07a0dd7c27a1fd670500003d08f5f6d2899c4d382ce7138e9c35d82cc7e791885da890686b92be00000005080000000000000007c02931c9a11b0e3482d01307ea8be81c692e477804d07148a3c79c81fb5bb98985d31a806a300aa7f0463829147f4190a0de56287240000c3e87c80003d9862a35e05dc1d104be2d68225000129e405e2066bf9e881300f0c0000a5c4b98d83000000056f800082f809f60400006601edc0001e845fb191861fc5f682322d01ea0bf84740904594107e415167044395de2608a925cd059850e15ba6f881425a70a2c09ed222000000000000006608000658c43a6dc91b83a0571000000003ed080629599860d895647fa1ac23d89c325fd000000000000000a4410add1944085050eaa2542b11f7200000007e3171a86f80005978e820000000000000044106a573fc9da00001de27bc93c0129f63000042c0001c985989388845000000000000000000174802a74f80003ab2198252214065100004f7457000015e50338f1275c8f243169640000000000000001071bce74380000000a2e000214884a937e1c58e44738000031610e641e823807fc73a0000f647940000000000054c146c75b8d3200000003c880001ed5d001a2800083f82fa000000021906df3379ba238b134a01111502aa8c662ea95845bb0e5e34751c25140606000000000003120310c6e000000066780004d900000000000000006e0001a7e00000006a0800004f80003e90bce6628ef865f22480011a388bb175800000005d780002631e5424a80005439f23006451d6e71fad0c592ed00014721e01b2844c479b000000000015120001b0486c864601c000000000005a183ee000000000003c75ee8e0c4af126800015c213611b60001c244e996e60000000576212600015d300000000f100000000000485d25e000053427348b00a489a300016a44c792f474621d8040000064d0202
  | 37 => 0xc1870e1c00008c026a9bfe0000c985d0a2f2052091c74986d27e3975c7ed81464ff05041b600001ed1a443e2cbee00020021eedcb26f8063d6a992a477280002cbcae63bb0d0363480003810000000000030e000000021343e7959c00022082ba0b6c00000000c080a600000000000928000066038396b0745882e00000005d900002839fc35ce164c07e994803e980049c137c74880006d70000163201669e4894191177c6b196d05e0216a0061f22000087500000004cd000006f054617c00002759b297c25a6e00006aa00016720000000000206a4a515b47759a620001c18000000049e95fa1ea99f633ccdb10001a86000000022a8000000189200009901aec000000117e00011ba0001b9e0a0a1ce89f99bc0fb1bca77a42f96b21f0c5a5c2788b1963253000000000000169c0001761b454e71a885139d4c12e025040bdd5800405b879107f000016e4075c33a11084e285600007fb80000001f9a0001d5339a941c0e340000001b052b888d8000088500000006db000083b92ba06d800000000004d040001498a8436f034c39f829107c00000001e4276d199c4d4220a19581a27dd0b9c64100006d10b9030e8ab0669a0a638c08a014b18a47ee04e884180e4006c92611a83ba74ad4f20000d0220114062e28bb00001c120b589501bb147c000120d65882545d204145719a5c2be80000000a4e180000000000001c0978a0000ace00011be0001cd400002dd0000458645136e2c6943a1f382940260f1e7f51d6c57d0c1c458870a14e0dce61c8f324fd0e7a5ff85202271bf274b8d963b202c26300cbc56c068217a80b00c290f15ae928655b92160090a585598e4c2828a2486c0b7822791b019f957850204c68111b4884c80944f40d7403b15f611383a863dd28967798fb6308e021d85d8a0480f9800002976ec8aff1868c420001b3a668000000005a644006f42cb01856b5a14e39403fa78900a02b19b8a7e80df86ab863083a8c1042d8da637f0c12192800046d00000000000355c0005e915a484e1ce60651ddc3780564003193c1f3199389011141bc98e826280000ff814a5490b40000000069a00007c61ae14700000740a14282e105232b00008558000000096e3e0805230f1b223241bc28531b762d88000377c45d7768f366a50d9c20a160464d44480000a120d91b583b1d06c0001f86389848a10f19a88898000000085c7541cf200000000001dbc1e08e610000000691400057e17142c01bbe00000007ec800077518c6000000026980006d7905c6880f2842f176e12596cc096107015621c61adca5401a8000000000014658405f4070600000007ba87c40001d0f7f243ce71e0b714eb865012a11de47113e940254ee20d94da000123e0000d8e7c5050d000000076b03e873b80002af9d5411f80ca49e12120ef031c000
  | 38 => 0x9000049f800073c0b1c0001c58664970220400006198ea88188aea7de85ae7c910a00000a493b2c7e01018d98346989c5a2800078ea144000000065d0d72694805600015c44e5851401796b700000004ab4922000060c62d8000442000085e000014ba0bc00011386a5800000000002cd80005b699b642e00000aec0000000000000000022880000000e240000750000100c0000d480000000000000042e87768928000000000000000006c300007c4801a5b2000000000004cd800043a800000014c200022b85c6000000012b24738000000000027ca12059a0d1b5310d1e0001af800019b851d9f285bf904a00000001738000000110c74fe22042fa2220001f3a22fdb0e896800000009ca274c5ec00003e469ca2c00a100006b38616679943c7d0000000000000000000000000089c00000001b980000b27699a22e570c00028a991d0f1981a68513ee4db21ea82d99ee0f98efa388878c2ac908257449d4268a25650b4803534000063a800017012f320980000001d9481d0853332d48669e89523614086000091283b2012222580e8620000000147e808995c2c862f8856948e4838b7408493404601e2e58f900649d83964f31bf43df00143ef97122745d061281ae4743000046c80000001ba83c61a180000f7818c942f7de00004a29f9676d93a2000000088e96240000e8447c021c000000000008c63de9a657a69aa355397f6668d06a0e81ecc42317903fc1746033c27c00000000000000000000000016eb000045c0000c2036b80004940fdc6448a021a30aa471b8000558228010c03723091572738822a6409c3610d1b7a57c977e1b70939092977014d84d27c7035c27986f040283ef5c0012258a9cb00c5417a024d6a81f200001219ebc6ed94ea36a16d60f49fce000002251780003030fe400005d052600003f48c7a7a2800070e8a3e00f98b40b421f0898881881c05740d8000025f13fd0ac00002710d88000000059d90f03d518e50b20d442da827e3b68caa04c888812d5f3e34fc0008b102e100000006e199284dd8648568953e1ac833000009625a613302ee145c116d4a600021528a112a90198fca47a19b4378819029b14b600000006ce018b84902281c5143061b10d800000006c99c5600000001f410765d3804e4331c1032480000cc80005ed9ff83ae0174511a1e87404e92020cbc78948a9e2860000744da4c47500000000a4644bd10a7d895fc36bde688af911051b837800000be5ce800009361ca60252140f8807f74c08bb17500000d1c41e761210288a8a064048f3e5ada11e6fa80600c120e609ad7924ba9a3e773a2d44fd8136000003636d832551a80002d3604e88c9cbe615de82000000054b1a8a51c0000108059422900e5000000000017501ce205e00002d8000203a00000000001e8e34e80000001ac
  | 39 => 0x150d3ed7e8871e27089b62ea0d3e4929f570c0162c3211e345c2222800003c98a6000021c86203fbcf38000000033b8000000154c27b9da6000000087592a800006966351f043d4816d5ca80004880824124c00045b182e0001daa71c80003e5d3db690925443816b37130d4a071051020f108e17c86ac58c1c220000838405818e0001efc86e1dc229c1e386fe000062889ae4ad15484ef8d5873d0e6b2a08dbe623000035489cf56780000000910000000071716de7038000213880e3318c704f00d5e1b783c26e913806dd00008a41b4044a80002fc183416f13b966308d421807a062208ba08ec0001cb22184f212d2350c07a4eb0cda62a83cc4628a60000088e6a6c26e6cf955a6e419323709fd871d1c0c5f09e1e7c1c4f217d22dc0001cd04918000000066c0000dac58b400070f00000001ed085f00006129f7c5250c7e0001e5809780000000c066ab16b86668e7853e8000000000000021307ca99be653051c2cb80000000000000000059f80003e41bcc4de921a00015987608d1732d922b7f8c75b00020ac5f9076e2e0142e0000ad500000001e7147500018381df06621a908f3000142b64280005f85aa012d1688000130245d19d2000094084d800000000000000000812800019995db50f83ea09718460001afa89091226fc0dda2ec80000fd0000000020007a886a00000000001f3635fdff64f38a208930c165b606087ae06a06fa1dd04039c0a002000000019940001f5f6cd815000000007fc8f2e6985d467a54a1415a00000e79e6200003464bd800058303067be9f423d6009a4ed187a0000def11684541bd86c249102db000000000012d45048da9358038c6b8dc7e7cc1ee6467024c3d78dd04e08ed402786401a60f920ad949a2519d553faa19c31a80c74a4883085a1c464aad5463fe00000f3d2f021086cb015219e4ad904377e000000006f532f80000000a1a0000c2c8278ccf1ebd0a2625015a49c800010122ee2ca000003788595a812e24630e4e000204288300006d69dcc88f89c000000000000000000000072587345e180000001c5a00000000e0087a368800000000004b400003c50bea00005a25d880002e2038639a1e0a6ef22d24cf03685f99b0a54d9b8406a08bd84621f82bc867821e1bd80000000000000000019ba0000000000115e23914246bfca6e43e1bda43c98540000f888368d924e683401dd417852703cd00006d634802f609101ac4dc0d8039600001d593da0008000305ce48000097e056000020c8752033400019e90622b40796178a06047582c63400391000000000018fd297885a312037a0d148827dd8e7200000005cc91462efa25c3a992824211fda3209ee20c311786bd16817f40d260001c608a917aa40b1c94221d34c62101d62c20ba61f68e605a78ffb4130b4e7b
  | 40 => 0x181c81194ba3ad874a5a48ac02ff9e2a8248a3075d800000002f8610821851f50d407b08f4118c00000005187bf944c00013ca58497fa0000e4600016d400000000001e6c00003207b18fde000000000000000000adc000000085180005750ffe4d8149059dd3c6887213e0001a9c83d8921000000000000000000000000105a00002f57b0c0007240bde5ff00002228000143800067283d400000000001d74653950c00000000000012896000000000006cf07840001374000000000000000000000000204c49080000001864000000000000002530000731800000000003f062a875c13548708000299800060f0000395000031a01fc7f7568e3631e3e45d80000000000000000009e800061a800000000000e4044403e1cae2a60000000000000015c03a5471873103443c8063e3728f7000005448bc05760000720000097000015ea00000003bc9cec00002267640a7c58e1a63094915a03506674f481661358f4e0c4065e39f00000000214593873604dd3902a2814012102fb71a80007b60000402011e0d5469e748c00000000005730000140000003c857e8651c307ab80ae03580001e49602000101426cc000000034200000b653a00001d1810a3ac9d7a000019221005724558000000000004e80004501f6e6a4800000022b40498f8f4dfdd6200000000000000000000048420900000b7a5200ad2189800000021ac6cd00002fe80008589ac90dd838f00000002a0132277a0e3879a9ee8532948340789b45a59dec6c9c5b61ff437111a51c88619faf80802ee0cf8bf480b11282ae800061616e840b9658354d6be7939d8673a9e163eea0d20f28bf61d602620aa0f0a61685cc3b88c5c030a1e00001e153991e046c7013823e18e08321e978a880
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x9768794521440618e8ed28a428809b9918a5148510186b8384a290a2000d7051dc121440172ed0fbaa428809b1d1db75485104b4bb43eca90a2030c7476d952144001cc8c5b2a428802e5d21773485100247a432e690a200b974855cd21440779a8edb1a4288003551d763485102066a3b0c690a2000d547518d2144001d88c431a42880025d21d53485101963a3b2a690a2001ce476dc921440719c8edb124288003591d76248510006b83aee090a2000d73751c12144071bc6e4382428802e5da17714c11000672316e29822000cd7631c530440019c8c438a60880021fa1b75481100062e31eea9022051c6c62dd520440012ed03baa408814a1fa1f654811028c3e43eca9022030e6820d9520440018beebb1a4088003171d7634811000637baec49022000c6c75d8920440172ed0bb8a40880033518f714811005cba428e29022000cd4631c520440019cec438a40880c69da0765c41100072a28ec78822000e6451d8b10440618f4edb2e20880ef369db63c4110007a828ec78822002cda7618f1044001ea0a231e208800b1e9d953c4110005b840aa78822038cea76d8b1044001ec0a3b1620880073a9d862c4110007b0288c58822042a7a8694710440078f4ed28e20880d2dca0651c41101a5b842c638822034b70854c710440696e10a90e20880029760f5458c100246e43aa6b182000a5d8314563040054b907bb2a60800297e0d7654c102ee2f31ee8a982003a5e8758d53040074b90eb1aa60800317dd16354c100052fc12c6a982032e571058d5304065caa20b1aa6081571798c7154c100062eb18e2a982095c76611c553040070fd0bbb286080021f6177650c102d62f31aeaa182000974815d543040091b90eb1a8608003175d56350c100c54e422c6a18200387e87dd562040010fb07baac4080021fa0775588102843f438eab102000a5d831d562040010fd0fa9ac40800e1f21f53588100043f43aa6b10200087c8754d62040058bce6a9ac4080123b21d52588100043f438a2b10200387c8714562040010ff0abb2640800e1f215764c8100246e43ac69902001acc8258d32040018beeca9a6408003175d9534c81016727312a699020048ec87589320400559906b1264080039354d624c8100047ac36e299020008f5861c532040c90ff0eb14a2080021f21d629441013e2f31eeb1882000c5f7558e31040091df0eb1442080133a9c162884100063c3aeec8802000c7b53dd910040018f0a3bb220080031eddb7544010185b840eea8802000cdb76dcd10040019b6ec39a20080031edd9534401000675bb6e48802000ceb761c910040632f50f28a20080031edda514401018db943ca28802094d72879451004061ae6ed28a20080039cdda5144010007a9b9ca28802000f50739451004001ec6e528a2008003d81ca5144010
  | 1 => 0xce3b1ca28800317e1f63945100062eba6c728a2000c5e71d8e5144001cace3b1ca2880021fe1d63945100051fc22c728a2056a3c8458e51440014df04b1ca28809a9b20963945100052f430c728a2000c5e7618e5144001c3ec831ca2880038719063945104ceab388c728a2026a6e86d8a51440018dcedb14a28800393d8f62945100072631ec528a2000d6671d8a51440018dae7b14a2880031b9c762945100073338ec528a200087f8758a51440014bf06b14a28809e9720d629451000537430c528a2000c6e7618a5144001c9ec6314a2880039318c62945104b6b3388c528a200087e86dd63144001878c9bac628809f1718f758c51000636316eb18a209997681dd631440070fd0fb2c628809e1f21f658c5100061fbaec918a2000c3c75d9231440018beebb1c6288003171d7638c51000637baec518a2000c6c75d8a314404fca8c728c628802e5da16768c5100053b436eb18a2000b5583dd6314404fca8c7bac628802e5da1f658c5100072a31ecb18a200b97485dd231440172e90aba462880034d1d7648c5100074a31ec918a2000d34751923144001d28c632462880025d21d548c5100069aba2a918a205ae546355231440055ad0db1c6288003359db638c510006aa3aec718a2000ad48650e31440172e90ab946288003591d7628c5100076231ec518a2000ce67618a3144001ac8ea3146288003a9190628c51000762318c518a2000ad4864ca31440630fd0dbaa62880030f193754c51013e2e31eea98a2000c6c62dd531440ab0fd0fb2a62880c21f21f654c5100061fbaec898a2000c3c75d9131440018beebb1a6288003171d7634c5101de6c386c698a2000c6f75d8931440018d8ebb1262882665da1e514c5101863a3b4a298a2027e54639453144061ae0e128a62880035c147704c51005cbb43eea98a2027c7476dd531441332ed0fb2a62880c31d1db654c5100072a31eca98a200b97485dd131440091e90cba2628802e5d215744c5104c65a3b6c898a2000d3475d91314412f968ec32262880034d1d4644c5100074a318c898a20009748755131440b78e8ecaa2628800b351db734c5101de6a3b6c698a2000d5475d8d31440719c8edb126288003591d7624c5101f6723b0c498a2000d64751893144001d48c83126288003b118c624c510006b83aee098a2000d73751c13144077ba6e6382628809b9918a518851000732316cb10a20008f686dce2144001d88c5b1c4288003359d8638851000762310c710a202ce646254e21440035cd0db144288003399db6288510005724326510a2000f45534ca21440630fd0dbaa42880031718f754851013636316ea90a203197681dd521440970fd0fb2a42880c21f21f65485100062fbaec690a2000c5c75d8d21440018deebb1242880031b1d762485101c674386c490a2096
  | 2 => 0x353589100062fb9ea6b122002c5c73d4d62440010fd0ea9ac4880021f21d53589100061fba2a6b12202dc3c7454d62440018bee6a9ac48800b171cd535891000637baee4b122000c6c75dc9624400199ee7b92c488003331cf72589100066a39ee2b12200087e8714562440018bee628ac488157171cc5158910006373b6ca3122000a6d83d946244001ccb03b28c488003995c7651891000476c3cca3122000a6e85994624400159d07328c488002b360e651891000477c3aca3122000acf83594624400159906b28c4880029ba186518910006373b0ca3122000a6d8319462440974d902328c488003999c4651891000732b88ca3122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000e4f85d8c6244001c990bb18c488003b15c7631891000476c3cc63122000a6e8598c62440014db0b318c488002aba12631891000556c24c63122000ace8398c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c4880029ba14631891000536c28c63122000ace8618c624400199cec318c48800393d94631891000726328c63122000e8f6418c6244001d18c8318c48800393a14631891000726c28c63122000ec58118c6244001d8ae2318c488273b184063189104e762080c63122000a6e86d4c62440014d90da98c4880031b9db531891000717b26a63122000e2c64d4c6244001c9ec7a98c4880039318f531891000537432a63122000a6c8654c62440018dceca98c4880038bd91531891000716322a63122000e4f6354c6244001c98c6a98c488002d920553189101f573436a23122000e6765d446244001d88c7a88c4880faf8a03511891000537430a23122000e4f631446244001c98c6288c48800399d94511891000762318a23122000b66861446244001ccd0c288c48826f999d85118910005b2c18a23122000f47631446244001cccc6288c4880039918c5118910007a2318a23122000e44631446244135ccec0288c48800e1fa17764c9100043ec2eec99220188be84dd9324400117b09bb264880031d147764c91000666194ec992200087f855d932440070f90abb264880022fe11764c9100c45e422ec99220008df835d932440011df04bb264880023de05764c91000666190ec9922000c74511d93244001c9865b2a6488003a30cb644c91000c6f43ec69922001ace82d8d32440014bd0ca9a648800297219534c9100062f3b2a69922000c5c7654d3244001c3ec8a9a64881ef87191534c91016726312a69922000b548154d32440051dd0fb12648800ab3a0f624c91000726a9ec4992202787c865ce5144001878c8b9ca28809f1718d739451000636312e728a200087f87d8e51440018bae7b1ca28809e97a1b63945100062f3b6c728a2000e1f64d8e5144001aa
  | 3 => 0x7b122000e8f64d8f6244001c9f0bb1ec4880039321763d89100053742cc7b122000a6d8598f624400155d0931ec488002ab61263d891000537c2ac7b122000a6c8558f624400155f08b1ec488002ab21163d891000537428c7b122000a6d8518f6244001c9eca31ec4880039319463d891000747b20c7b122000e8c6418f6244001c9d0a31ec4880039361463d891000762c08c7b122000a6e86d4f62440014d90da9ec4881371b9db53d891000717b26a7b122000e2c64d4f6244001c9ec7a9ec4880039318f53d891000537432a7b122000a6c8654f62440598dceca9ec4880038bd9153d891000716322a7b122000e4f6354f6244001c98c6a9ec488002d920553d89101c573436a3b122000e6765d4762440717c501a8ec4880029ba1851d891000727b18a3b122000e4c631476244001cceca28ec488002d9a1851d891000733430a3b122000b65831476244001e8ec628ec488003d118c51d89100057340eebb122038ae581dd7624400159d073aec488002b360e75d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000667b9ce7b122000a6e851cf62440014db0a39ec488002b9a0473d89101c572c08e7b122000a6d84d4f62440014dd03a9ec48800393d4e53d891000537c22a7b122000e4f8354f6244001c9ee6a9ec488003931cd53d89100053640aa7b122000a6e8590f62440014db0b21ec4880029ba1543d891000536c2a87b1220008ee8710f62440011db0e21ec4880029ba1443d891000536c2887b122000e8d4310f62440014df0ab8ec4880029b21571d891000567c1ae3b122000acc835c762440014db0628ec48826f999c451d891000732b88a3b1220388ee87cc762440011db0f98ec4880029ba1731d891000536c2e63b122000aae84cc7624400155b0998ec4880029ba1431d891000536c2863b122000a6e85dc362440014db0bb86c4880029ba1730d891000536c2e61b12200387e86dd562440018d8c5baac4880021fa1f65589100062e39ecab12200087e8719562440018b8e632ac48800317d9773589100062e32ee6b122000ccc62dcd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c6b122000c5c7518d624400193ee831ac488003271d06358910004bb438a2b122000d5773145624413baa8e628ac48800e1fa1f75589100043ec1eeab12200387e81dd562440011bf06baac48800a3720d755891000477c12eab12200087e871d562440051bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd62440018bf0bb9ac4880031721773589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100043f43ea6b12200387c87d4d624400187ee9a9ac48820f0f1d
  | 4 => 0x34400147b09bb2a6880b29ba0b7654d1000536c16eca9a200087e869d953440018b8c73b2a6880029760e7654d100062fb9ceca9a200087d849d953440010fb073b2a6880031760e7654d100062f994eca9a2000c75819d9534400147f08bb2a6880b68f2117654d100052fc1aeca9a2000a6f825d953440594d904bb2a6880021fa187654d100062fb98eca9a200087d841d953440070ff063b2a68800317e0c7654d1001c3ec18eca9a2000c5c831d953440018be643b2a6881561f2047654d100063b188eca9a2000c75311d953440010fd0dba2a6880b70f1937454d102ee2e31ee8a9a2000c6c62dd153440010f90fb22a6880030fdd36454d1016d1f436c8a9a2000c3e76d915344001878edb22a6880038718f6454d100061fc3ec8a9a2000c3c87d91534400187ee7b22a68800387dcf6454d100070f996c8a9a200087f8759153440010f90eb22a68800297e0d6454d100152e41ac8a9a2000a6f8259153440594d904b22a6880028fa186454d100061f3b0c8a9a2000c3c761915344001c38c6322a68800a97a1b6354d100062e3b6c6a9a2000e1f64d8d5344001c38c9b1aa68800317e1f6354d1001d2f43ec6a9a2003a5c87d8d53440018b90fb1aa68800317dd36354d100052ec16c6a9a2032a7686dc553440018ecedb8aa6880038d1937154d100072bb1ee2a9a2000e6462dc553440010fd0c38aa6880030fd907154d100061e320e2a9a2000c5f631c553440ab8b8c638aa6880031b1887154d100063b3b0e2a9a2000e34641c55344001caec638aa688003991887154d10004bb430e2a9a2000c76861c553440012eb0838aa6880034dd907154d100063b320e2a9a2000c74641c55344001a68c838aa6880030d1907154d1005cbac18e2a9a209dc77631c55344001aaec638aa68800315d8c7154d104ee3ab18e2a9a209dd54631c553440018ecc438aa6880031d1887154d1000632310e2a9a209dd57321c553440070fd0bbb286880021f6177650d1000c77416eca1a20008ed82dd943440018e8a3bb2868800e1f2167650d100064e21ceca1a200087f855d943440070f90abb2868800237e0d7650d1000477c12eca1a20018ec825d943440070fd0a3b286880021f6147650d100064e218eca1a2000c74511d943440010f90cbaa868816b1718d7550d1000636312eaa1a2000974815d543440010ff0fb2a86880021f61f6550d100070e21ecaa1a20188de87d8d43440018bcebb1a8688003175d76350d100c54f426c6a1a20048f581dd762440058b8e6a9ec48800e3be1d52d89100053742e65b122000a6d85ccb6244001c9aa7996c4880c71d5c451d891000536c1ecbb122000e6581d97624400159d0732ec488002b360e65d891000567c1acbb122000acc8359762440014db0632ec48800393d9763d89100072632ec
  | 5 => 0x80030f1d76458d1000656396c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d100066631ee4b1a2000976871456344001a6ee828ac68827f4d1d05158d10006b3b90a2b1a209bd647214563440070fd0fbaac6880021f6137558d100045fc22eab1a20188bc845d563440011bf06baac6880023be097558d1000c76412eab1a200087e871d5634403117d0fba2c6880030fdd77458d100061e3aee8b1a2000c3f85dd163440018790bba2c6880030fd4f7458d100061ea9ee8b1a2000c3f751d16344001878ea3a2c6880021fa1f5458d1001c3e43ea8b1a2000c3f74d516344031878e9aa2c6881f31b1cb5458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000c7743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc963440018dea9b92c6880031bd4f7258d1000636a9ee4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440019c8e5b8ac6880021fa1c5158d100061fba0a2b1a209ec3c7414563440018dee428ac68812f1b1c85158d100062f3b6ca31a2000a5d87d9463440014bb09b28c688003956076518d100072ab8eca31a20008dd8799463440014bd0b328c688002a7a126518d100054ec24ca31a2000ace82994634400159b05328c68800237e1d6518d100054fc22ca31a2000a9c84594634400159f04b28c688002b32096518d100052f430ca31a2000c5e7619463440014bf0e328c688002976106518d102ad2e408ca31a2000e56711946344001caae2328c688003279db6418d100070fb2ec831a2000e1c65d906344001c3f0bb20c688003872176418d100070f3aec831a2000e1d75d906344001d2ae3b20c6880023761e6418d100052f42cc831a2000a5d85990634400153d09320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc8259063440014bd0a320c688002976146418d100064f3b0c831a2000e1f651906344001c38ca320c688003879d46418d100070eba8c831a2000e957119063440014bd0daa0c6880029721b5418d100070fb26a831a2000e1c64d5063440014bd0b310c688002976166218d100054f424c431a2000a9d8498863440815ad0da88c68800395d975118d100074a326a231a2040bd280d4463440014bd0c288c68800387d905118d100070e320a231a2000e57651446344001d28c8288c688266d5e1c5118d104cdaac38a231a2000b56861446344001cad0c288c688277959d85118d10005aac20a231a2000f17641446344001cacc8288c688003951905118d100078a320a231a2000e14641446344001cacc4288c688003951885118d104af2bb00a231a202da3e84dd95
  | 6 => 0x43f43ea9b1a2000a5d83d5363440018baeba9ec6880031761f53d8d100052ec26a7b1a20038df8754f63440014bd0ba1ec6880029761743d8d100043fc2ae5b1a200387c855cb63440010fd0e28ec6880029760c51d8d1018e3ab88a3b1a2000a5e861d763440014bb09b2ec6880039560765d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100052ec20cbb1a2000e1f65d936344001c38cbb26c68800387dd764d8d100070e3aec9b1a2000a5e8599363440014bb0b326c688002b3a0a64d8d1000566c14c9b1a2000a5e8519363440014bb0a326c68800297a1b54d8d100052e436a9b1a205dc5e76d536344001c3ec9aa6c6880038719354d8d100052f42cc5b1a2000a5d8598b634400153d09316c688002a761262d8d101dd6b436a3b1a2000e5765d4763440777a501a8ec68800297a1851d8d100070fb20a3b1a2000e576514763440016ad0e28ec688002d5a1851d8d100072b430a3b1a2000b55841476344001e2ec828ec688002b5a0775d8d101dd6ac0eebb1a2000a5d84dd76344001cad03baec6880039560775d8d100062eba8ebb1a2000c5e871d763440014bb083aec68800297a0475d8d100052f42ce9b1a2000a5d859d3634400193ee93a6c688002b3a0a74d8d1000566c14e9b1a2000a5f855d363440014b90aba6c68800297a1474d8d100052ec28e9b1a2000ad6811d363440775ab023a6c68800297a1f54d8d100052e43ea9b1a2000a5e81d536344001c3ea92a6c68800317dd772d8d100052f42ce5b1a2000a5d859cb634400153d09396c688002a761272d8d1000667b94e5b1a2000a5f855cb63440014b90ab96c68800317dd572d8d100056b408e5b1a203bad5811cb63440011bd0e296c6880023761c52d8d100054f420a5b1a2000a9d8414b63440014bd0ba16c6880029761742d8d100046f43885b1a20008dd8710b63440014bd0a216c6880029761442d8d100052fc2ae3b1a2000a5c855c7634400153f08b8ec688002a721171d8d1000567c12e3b1a2000acc825c763440014bd0e28ec6880029761051d8d104ef2b388a3b1a2000e557114763440771bd0fa0ec6880023761f41d8d100052f42e83b1a2000a5d85d07634400159d05a0ec688002b360b41d8d100052f42883b1a2000a5d8510763440771bd0f90ec6880023761f21d8d100052f42e43b1a2000a5d85c87634400153d0990ec688002a761321d8d100052fc2ae1b1a2000a5c855c363440014bd0ba06c6880029761740d8d100062e31eeab1a200087e87d956344001878e9b2ac6880031b1cb6558d100043f438cab1a2000c3c7419563440018d8e432ac6880030fd977458d100061e32ee8b1a2000c9c63dd1634400187eebb22c68
  | 7 => 0x7d870c9658400147d08192cb080028f61032596100052fc1ae2b2c2000a5c835c565840014df04b8acb080029b20971596105253dc02e2b2c200087e87cc565840010fb0f98acb080028fa1331596100051ec2662b2c2000a6e82cc565840014db0598acb0803a1fa1c31596100043ec3862b2c2000c5f730c565840010fd0f90acb080021f61f21596100052f41e42b2c2000a5d83c8565840650fb0f3aac7080028f6127558e101952ec1ceab1c2033a5f835d563840070fd0bba2c7080021f6177458e100043ec3ea8b1c200387e85dc963840010fb0bb92c7080021f61c5158e100052ec18a2b1c200087d84dd953840070ff07bb2a70800e1f60f7654e100062f996eca9c2032c7710dd953840658ea21bb2a70800297e0d7654e100043fc22eca9c203387f835d953840018bf06bb2a70800317cc97654e100043ec36e8a9c200087e8759153840014bf06b22a70800a9720d6454e1001c3f42eeca1c200087d85dd943840070fd0abb287080021fe197550e10004ba40aeaa1c200087f8759543840010fb0eb2a87080038710d6550e100246e43ac6a1c2018a9c8458d4384001c9864b2a65080123721d634ca1000d66412c69942000a5f8654d32840014bb0ca9a65080b393989534ca100247643ac49942002acc835893284001c9aa6b1265080031d997714ca100063b328e2994202787f865ce518404f8bcc6b9ca3080021f61d63946100062eb9ac728c2000a5f8359631840010fb0dbaa630809e1fa1d654c6102ac3e43aca98c200087d86dd5218404d0fd0eb2a430812e1f21d65486101a53cc34a38842000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a200b87d8718f65440018bae631eca8800297a0e62d95100052ec1cc5b2a20a3a7681dcf65440614eb03b9eca880031d5c773d95100063ab8ae7b2a200087f845cf65440070f902b9eca88003175cc73d95105153b408e7b2a2030a75811cf65440010fd0f21eca880021f61e43d95100043f43887b2a200087d8710f65440014dd0421eca880029b60843d951050d3b40ee5b2a2030a7581dcb65440014bd07396ca880029760e72d95105053b408e5b2a2030a75811cb65440010fd0f996ca880021f61f32d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95101843f43e63b2a200087d87cc7654400147d0998eca880028f61331d95100053741663b2a2000a6d82cc765440010fd0e18eca8802e1f61c31d95101843f43e43b2a200087d87c8765440014bd0790eca880029760f21d95101753b40ee1b2a2008c7671dc365440010fd0f986ca880021f61f30d95100162f3b6a7b1a20009768714763440016ab0628ec6880123d60775d8d100052ec1eebb1a2000a5d831d763440010ff0aba6c68800e1f21574d8d100
  | 8 => 0x2b1ca2900029d2056394520185364326528a4027e4c634ca51480070fd0b3b462900021f616768c5200043fc2aed18a400387c855da31480070f90a3b462900021fa1b758c5200043f43ecb18a400087c87d9631480055990c9946290003339d9328c520006a7baa6518a400387e85dd931480010fb0bbb2629000e1fa16764c5200043ec2cec98a400387c851d931480010fd0dbaa62900021fa1f654c5200043e43eca98a40049cc874c930480095990c9926090007331d9324c120025e4402649824000b558314763c40014bb0628ec7880123d2057558f100052ec1ea8b1e200387e85dc963c40010fb0bb92c7880c71d1c45158f100052ec1ceca9e2000a5f835d953c40054bd07b22a7880029760f6454f101953ac30e2a9e2000c76861c553c40018eb0c38aa7880025d6107154f100063b320e2a9e2000c74641c553c40112eb0638aa7882571dd8c7154f104ae3ab18e2a9e2000c76621c553c40018e8c438aa78825755cc87154f10006b9400e2a9e2000d71801c553c40070fd0bbb287880021f6177650f1000c77416eca1e20008ed82dd943c40018e8a3bb2878800e1fa147650f100043ec28eca1e2000c74511d943c40012e902baa878806237a1f6350f100c54f426c6a1e200087d879d762c40070ff0ebaec5880021fe0d75d8b1001c3fc3ea7b16200087d87d4f62c40010ff0ea9ec5880021f61d53d8b100247a40aeab162031c747114562c40070fd0bbb265880021f617764cb100c45f426ec99620008bd84dd932c40018e8a3bb2658800e1fa16764cb100043ec2cec99620188be849d932c400117b093b265880031d144764cb1000c6f43ec69962001ace82d8d32c4059c98c4a9a6588002d5205534cb100147743ec49962002ace83d8932c4001c9aa7b12658800e1f61f629471017eb938ae128e2030c757694631c404fcacc728c63880035c145708c710044bb43eeb18e2027c7576dd631c40016ab07bac63880123d61b748c710044ba42ee918e2008974855d231c40012e90eaa4638816f1d5d9548c7100069aba2a918e2008974855ca31c4001ae0eab84638829a5da1e514c710044bb43eea98e200897485dd131c40112e90aba263880025d21d544c7101863abb4a310e2026e666294621c4001ae0a2b8443880123d61b73887101963abb2a710e2000f45534ca21c414b2ed0f28a43880225da1f7548710044ba42ee690e2008974855cd21c40012e90ea9a43880225da17714c310004bb40eea906200897685dc520c40112e90a38a41880021f61373596100062fb9ce6b2c200087e8790d65840010fb0f21acb080021fa1c43596100043ec3886b2c2000a6e8210d65840014db0421acb080031bdca72596100052f418e4b2c2000a5d831c965840010fd0f992cb080021f61f32596100043f43864b2c20008
  | 9 => 0x5158d204f61e3a0a2b1a4000a5d8314563480018eee228ac6900031d1c45158d200043f434eca9a4000a5d839d953480010fb093b2a6900021f60e7654d200062ec1ceca9a4000c5f329d953480018ba653b2a6900021fa067654d200051fc22eca9a402da3c845d953480014bf06bb2a6900029de057654d200053a40aeca9a400087e861d953480010fb083b2a69000e1fe0c7654d2001c3ec18eca9a4000c5f321d953480018dc643b2a690003174c87654d2000636990eca9a400087e811d953480010fd0dba2a6900b70f1937454d200043e43ec8a9a4000c3f74d9153480010ff0eb22a6900021f21d6454d200052fc1ac8a9a4002a5c8359153480014ef02b22a6900029d2056454d200043f430e2a9a400387e85dd943480010fb0bbb2869000e1f2167650d200064e21ceca1a400087f855d943480070f90abb2869000237e0d7650d200047bc0aeca1a40008f4815d943480070fd0a3b286900021f6147650d200064e218eca1a400087c865d543480012e902baa86900021fe1f6550d200043ec3ecaa1a4000a5d83d954348001c3887b2a86900623721d6350d200c54e422c6a1a4000ad48158d43480a18d8edb2a64900039318f654c92002476432e899240049e8805d1324800559907b226490003a390f644c9200147643ac89924002acc8359132480015c902b22649016f1b1d9544c9202d72631aa89924002ace86d8d3248001c9f0ca9a6490002d3a19534c920005a6432a69924000e4c8654d32480014990ca9a649000b93dd9534c920017263b2a69924000b4f8454d3248001c9ec8a9a649000393591534c920005a640aa6992402ce4f6054d3248059e96c0a9a6490002b3219434c920005a6c2a869924000e8d6450d3248001e92a7b826490003d254c704c9200943ec3ecbb0a4000a7681d9761480014ed0232ec29000e1fe1d75d85200043fc1aebb0a400387f87d4f61480010fb0fa9ec2900029da0753d85200043fc3aa7b0a400087d8754f61480014e902a9ec290002ada1331d852001c3f436eab0a405087c86dd561480010fd0fb2ac290003171cf65585200043f438cab0a4000c5c7319561480018becbb9ac2900031719773585200047bc3ac230a4000ad48358461480014ed03ba8c2900029760c75185200053b408ea30a400087f855cc61480070f90ab98c2900021fa1f53185200053b40ea630a400087c8754c61480058bce6a98c290003175cd53185200053a40aa630a4002ccc734c86148001c9aa6990c290002ada13311852000572c166230a4000ec5320c461480014ed03bb4a2900021f60e76945200043f430ed28a4000a76811da51480010fb063b4a2900031da0476945200043e432e728a400087f87d8e51480010ff0eb1ca2900021f21d63945200051fc22c728a4056a3c8458e51480014ef
  | 10 => 0xb0c4000c7775d4561880015cb05a8ac3100c21fa1c51586200062fb98a2b0c4055c5c7314561880018eeea28ac3100c29da1c51586200063b438a2b0c4000a75831456188001caee628ac310003951cc51586204df32390a2b0c4000a7681dda51880018ece3bb4a3100031d9c5769462018c3fc3ac328c4000a5f83586518804f4b906b0ca3100021fe15768c62001c3e42aed18c40048f58798631880018e8eb30c63100031d1d5618c6200156a41ac318c400087f855d931880070f90abb263100022fe11764c6200c45e422ec98c4000c747598531880091e90eb0a63100031d1d5614c6201f477c3ac310c4000acf835862188001ccac328c431004a1f61c63d95200051f420c7b2a4000a3d8418f65480018bae631eca900021fe1173d95200043e40ae7b2a4000a3e841cf654800147b0839eca90003175cc73d952028d37410e7b2a4050a6d821cf65480010fd0f21eca900021f61e43d95200062eb9c87b2a400087e8710f65480010fb0e21eca901469ba0843d952000536c1087b2a400087d839c765480018ee4338eca900031d08671d95200043f43e63b2a400087d87cc7654800147d0998eca900028f61331d952028d3741663b2a4000a6d82cc765480010fd0e18eca900021f61c31d952028c3f43e61b2a400087d87cc365480014bb07baec6900029760c75d8d200043fc2ae9b1a400387c855d363480010fd0faa6c6900029760f54d8d2001c3f42ce3b1a400087d859c763480010ff0ab8ec69000e1f21571d8d200045fc22e3b1a40188bc845c763480031d904b8ec6900021fa1c51d8d200043f43ecab1a4000c3c74d9563480010fd0e32ac6900030f1d06558d200061fb2ee8b1a4000c3c65dd163480018eecbb8ac6900031d1977158d200063bb28e2b1a4000c74651c563480019a8c638ac69000e1fa1f7558d200043ec26eab1a400087e81dd5634800117f08baac6900622f2117558d200047bc0aeab1a40008f4815d563480010fd0e3aac6900622fa1f7458d200061fbaee8b1a4000c3c75dd1634800187f0bba2c6900030f2177458d200061fa9ee8b1a4000c3d53dd1634800187eea3a2c6900030f1d47458d200043f43ea8b1a400387c87d51634800187ee9aa2c6900630f1d35458d200064e3a6e6b1a400387e85dc563480010fb0bb8ac6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031da177158d200063ac2ee2b1a4000c7754dc563480018eea7b8ac6900031d54f7158d200063bba8e2b1a4000c74751c5634800196ee838ac6900032d1d07158d200066bb98e2b1a4000ce7721c563480018ef0a38ac6900031d2147158d200063baa0e2b1a4000c77531c563480018eaa638ac6900033590c7158d2000673210e2b1a400087e8714563480070f90e28ac6900030fdd0
  | 11 => 0x4c0018e8e228ac8980028f61276551300051fc22ecaa26000a6f825d9544c0b94d904bb2a8980029de0576551300053a40aecaa26018a3e86d91544c00747d0fb22a89800e8f21f645513053e1fb9ec8aa260a7c3d73d91544c00147b05b22a89829f87ccb64551300061fb20e2aa2609ec3c641c5544c0012bb0638aa8980b7171d97550d302ed8fc22eaa1a602de1c645d5434c0016a902baa8698062a7a1b6450d300c61e3a2a9b126018c9c7450f624c0010ff0ab8ec49800e1f21571d89300045fc22e3b1260188bc845c7624c0031b906b8ec4980029760c51d893000672310e2b12600387e851d9424c0010fb0a3b284980030f9d954509300061e3b2a8a12605ce2e62551424c001938eca1a849801237219744c93000d66416c89926000e8e42d91324c0031b90eb226498006b3209644c9302de2e3b2a89926000e1f64551324c0b9c98c4aa26498006b3a1b624c93000566432849926000e8d64509324c001e1aa8a12649800e1fe1d75d85300043fc22ebb0a600387f87d53614c0010fb0faa6c2980021fe1d54d85300043ec3aa9b0a6000a7481553614c0011ef0eb08c298002b920961185300053a40aa830a6018c9c7450c614c0010ff0ab90c29800e1f215721853000e663926430a6000a5d83144614c0015ab07908c298003b14c821185300053b40eed28a6000a3f845da514c0ad47908bb4a2980029da0476945301852e4328728a6056e1c6450e514c0614b90c994a29809b93189329453001c3f42ced20a600087d859da414c0010ff0abb4829800e1f21576905302b61e326eb20a6000c3f75d92414c0315390ca1c8298003279d9439053001c3f42ceca0a600087d859d9414c0070fd0b3b442980021f616768853000d664326510a6000cce764ca214c0070fd0b3b242980021f61676485300254e43286a026002c9c7650d404c00973100a1a809800e1fa177158e200043ec2ee2b1c4000a5d8314563880014bf06bb2a71000297e0d6454e200152e41ac8a9c4000d64211c553880070fd0bbb287100021f6177650e20004ba40aeaa1c40048dc8758d438803153908b1a87100029d205539862018e3ac38a330c4000a75831466188063ce50028cc3100039c600519862001c3f43eeab0c400087d83dd561880618eb03baac31000237e0d75586200146e41aeab0c40028de87dcd61880018beebb9ac310003171d773586200064fba6e6b0c4000c5f85dcd61880018b90bb9ac3100033308773586200062fba8e6b0c4000c5c751cd618800193ee839ac310003271d073586200043f43ea6b0c400387c87d4d618800187ee9a9ac31020f0f1d353586200062fb9ea6b0c4002c5c73d4d61880010fd0ea9ac3100021f21d53586200061fba2a6b0c402dc3c7454d61880018bee6a9ac31000b171cd53586200053a40aa6
  | 12 => 0x21fa1d5458a300043e43aa8b14600387e85dc5628c0010fb0bb8ac5180021fa1c5158a3001c3e438a2b14600087f855d9428c0070f90abb285180023de057650a300047a40aeca1460048bc87591428c00355904b2285181738b9895450a300247643ac4a146018aac84589428c001c5aa8b1285180029d205549863018e3ac38a330c6000a7584146618c14d4ef0628cc31829a9d60c519863001c3f43eeab0c600087d84dd5618c0618eb03baac3180022fe1175586300c45e422eab0c60008ef825d5618c0031d904baac3180622fa1f74586300061fbaee8b0c6000c3c75dd1618c00187f0bba2c3180030f21774586300061fa9ee8b0c6000c3d53dd1618c00193863ba2c3180030fdd474586300061e3a8e8b0c600087e87d51618c0070f90faa2c3180030fdd354586300c61e3a6a8b0c6000a5d83d51618c0f98d8e5aa2c3180021fa1d54586300043e43aa8b0c6000c3f74551618c031878e8aa2c3181731b1c954586300053a40aa8b0c60018ee87dc9618c0018deebb92c3180031b1d7725863000657ba6e4b0c6000cac74dc9618c0018dea9b92c3180031b553725863000637a9ee4b0c6000c6d53dc9618c00199863b92c3180031bdd47258630006363a8e4b0c6000caf741c9618c001958e8392c3180031ddd751586300056ac1ea2b0c603087e87145618c00187ee828ac31827b0f1d0515863000637b90a2b0c604bc6c72145618c0018eeea28ac3180c29da1c51586300063b438a2b0c6000a7584145618c001c6ee828ac3180038d1d051586304cd3bc18a2b0c6099a7583145618c13bca8e628ac31800399dc8515863000732390a2b0c6000a7681dda518c0018ece3bb4a3180031d9c57694630004afc1ae928c600087f8758a518c0010f90eb14a3180c61fe1d61946300051fc22c328c6056a3c84586518c0014df04b0ca31809a9b20961946300043fc2aed20c600387c855da418c0091eb0f30c83180031d1d661906300063a3aac320c6018ab484586418c0010ff0abb2831800e1f215765063000477c12eca0c60018ec825d9418c0018e8eb30a83180123d21d61506300063a3aac2a0c6055b5681dd6318c0811bf0eb0c6318002a7e11618c63000567c12c318c6000e5561946318c001ab6eab84631800e1fa1776886300043ec2eed10c60048f587986218c0035c904b0c43180021fe15764863001c3e42aec90c60008bf845d9218c03117908bb243180031d1d661486300247a43ac290c6000c7475585218c00717f0eaa6c8980021fe1572d913001c3e42ae5b22600087f855c7644c0070f90ab8ec89800a3720d71d913000477c12e3b2260018ec825c7644c00147b0828ec8980023be09755913000c76412eab2260008f7815d5644c0011e902baac89800e1fa1771591300043ec2ee2b226000c777114564
  | 13 => 0x51f424c7b2a4200a3d8498f654843b0fb0e31eca90803175cc63d95210043fc22e7b2a4200c5d731cf65484010fd0f21eca908021f61e43d95210043f43887b2a420087d8710f654844d4dd0421eca908029b60843d95211343f43e63b2a420087d87cc7654840147d0998eca908028f61331d95211353741663b2a4200a6d82cc765484010fd0e18eca908761f61c31d95210062eb9863b2a4245a76811c3654844d4eb02386ca908021fa1f30d95210043ec3e61b2a420087e870c365484010fb0e186ca908028fa1030d95210051ec2061b2a4226a6e820c365484014db04186ca908029da0430d95210053ac0861b2a4200a5d83dd7634840147b083aec6908029760c75d8d210043fc2ae9b1a420387c855d363484010fd0faa6c6908021fa1c51d8d210052ec18a3b1a420087f855c363484070f90ab86c6908021fa1f6558d210043f438cab1a42a9c777119563484070fd0fbaac6908021f6137558d210047bc0aeab1a420087e871d563484010fd0faa2c69080e1f21f5458d210052ec1ea8b1a4200c7475dc563484010fd0e28ac690aa71ddc45158d210043f434eca9a4200a5d839d953484010fb093b2a6908021f60e7654d210062ec1ceca9a4200c5f329d953484018ba653b2a69080297e0d7654d210053bc0aeca9a420087e861d953484010fb083b2a69080e1fe0c7654d2101c3ec18eca9a4200c5f321d953484018ba643b2a6908031dc847654d210063a108eca9a420087e86dd153484010f90fb22a69080a97a0f6454d210052ec1ec8a9a420087f8759153484010f90eb22a6908021fa187154d215463bb08e2a9a420387e85dd943484010fb0bbb286908023b60b7650d2101c3e42ceca1a420087f855d943484070f90abb286908023ee017650d210247c402eca1a420387e851d943484010fb0a3b286908021f2197550d21004ba40aeaa1a420087f87d9543484010fb0fb2a86908038710f6550d210c46f43ec6a1a4218a9e84d8d434844f0f90cb9ca29089f1718d73945210043fc3ec728a4200c5d73d8e51484010ff0eb1ca2908021fa1b758c5210052ec1ecb18a42018df8758e31484970fd0dbaa62909561fa1f654c5211343e43eca98a4226e6761d9621484051df0eb1c429092e9ba1a5188521136b338ca310a4226e676194621484091e902baec090a6f1d5c4659812101c3f436eab02422687c86dd560484010fd0fb2ac090803171cf65581210043f438cab024200c5c7319560484018becbb9ac09080317197735812125e3ab88ca30242008fb8758060484070fd0bb8ac9180021f61771592300051ec20a2b246000a3f845d9548c001aa86238aa91800e1fa1f7558a300043ec26eab14600087e81dd5628c0a10fd0e3aac5180029760c7558a300043f43ea8b14600387c87d51628c0014bb07aa2c518
  | 14 => 0xf855c3644c4070f90ab86c8988021fa1f65591310043f438cab2262adc7771195644c4070fd0fbaac8988023de0575591310043f438eab226200c7475dc5644c4010fd0e28ac898ab71ddc451591310043f434ecaa26200a3d849d9544c4010fb093b2a8988030f61276551310043fc1cecaa2620087d839d9544c40187e853b2a8988028fe1176551310053bc0aecaa2620087e861d9544c4070ff083b2a89880e1f61076551310043fc18ecaa2620087d831d9544c40187e843b2a8988031dcc476551310063a188ecaa2620087e861c5544c5598eec238aa8988029760f54d89310043f43ecab12620087e87195624c5518eee232ac49880e1fa1776509310043ec2eeca1262008dd83dd9424c401c5885b2a84988062fa1f645093100d57416c8a126200a3e86551424c4014790caa284989738b18954509310c47743ec4a126218aae84d89424c401c5aa9b12849880a3da1b71509310063a32ee2a126200c74651c5424c4ad0f90cba4a29895b0f1917494531004afc1ae928a620087f87d92514c40187ae9b24a2988021fe1d64945310043f436eb20a6200a3d84d96414c53d0fd0fb2a829889e1f21f65505312ad2f436eb18a6255b5681dd6314c44faace3bac629889f95d87658c5310c46fc3ac918a6255a5e86946314c44faace328c629889f95d86518c5314ee3ab88cb302620387e86dd5604c44f0f90dbaac0988021fa1f65581310061e3a6cab026200c6c72d95604c4010fd0e32ac0988030f1d0655813100636390cab026200c3f65dd1604c401878cbba2c0988031bd9772581310063632ee4b026255c7571194604c4011f70eb00c0988023da0775d8e210052ec18a3b1c42abc767114763884014bb07aa2c71080e1fa177058e210043ec2ee0b1c4200a5d839d953884014ed033b2a71080297e0d7654e210152f41ec8a9c4200a5d83d9153885558ecc238aa71080e1fa177650e210043ec2eeca1c420387e851d943884010fb0a3b287108025d2057550e210c46f43ec6a1c4218a9e84d8d43884051dd0fb22651080ab3a0f644ca210156741ac8994425ac6f7655132884b5c9cc6aa2651080ab3e19634ca2100727c32a69944200e4c8654d3288405c9eeca9a651080b931d9534ca21005a7c22a69944200e4f6454d3288401c9ac8a9a6510802d3205534ca211672730aa6994422cf466154d328840159f0ca1a6510802d3615434ca2100747b228699442208ed86dc5328840135b09b8a6510803d154f714ca21007a2a98e29944226c6f765ca518844f4df0c994a31089f9398d3294621005b3c0a6528c42019cf874ca318840559f0c9946310807335d9328c621006a7baa6518c4200bc7814ca31884091eb03baac11080317dcd53582210162e39aa6b044202cce734c96088401c9aa6992c1108023ee1d601822100
  | 15 => 0x3b2a651880393087654ca3100727906ca99462018de87d91328c40359d05b22651880297e15644ca3100d67412c89946200a5e86551328c4b98beecaa2651880387591544ca312e727312a89946201acf86589328c401c9ecab126518802b3e19424ca3100727b2a849946200e8f64509328c401e1aa8a126518802f1205424ca310e46ec36e2994620099d84dc5328c44b0f90cba4a31880e1fe1f64946315743fc3ac928c622787c87592518c44f8beecb9ca31889f17e19739463113e2e432e728c620095f845ce518c44faaf02b9ca31889f55205739463113e2f30ae728c6227d56615ce518c4012bb0ea1ca31895a97e1943946312b70f3228728c6200b578150e518c4c90ff0eb14a31889e1f21d62946311352fc326528c6227c5c764ca518c44dc9cc4994a318802d5e0532946310051ec26cb20c6227c5e73d96418c4018becab9c8318862a7e1943906310164ebb28720c6200b978150e418c40147b0832ec1188028f61065982312ae3b388cb304625597681dd5608c4010fd0fb2ac118a669da0765582310043f438cab046200a3d84195608c4070fd0fbaac118a669da0775582310043ec26eab046200c5f32dd5608c4ab0fd03baac1188031da0775582310063ac0eeab04620087e87d51608c4070f90faa2c1188021fa1d54582310043e43aa8b046218c9e7450d608c4018beea992c118807339c932582310743f43ca2b04622787c87945608c4010fd0e28ac11880e1f21c51582310052ec18a2b046200a3d84194608c4011f70eb00c1188029ba0a64d953100536c14c9b2a622287d87193654c40187ae8326ca988028fa1262d95310051ec24c5b2a620087f835d3654c4010fb06ba6ca988030f5d074d95310051f424e5b2a6200a3d849cb654c44f4bd07396ca988029760e72d953100636b90e5b2a620087e87d0b654c4010fb0fa16ca988021fa1c42d95310043ec3885b2a6227a5e8310b654c4014bb06216ca9889e1fa1f41d95310043ec3e83b2a6227a5e83d07654c4014bb07a0eca988029ba0b41d953100536c1683b2a620087e87107654c4450fb0e20eca988030f5d041d953113c3f43e43b2a620087d87c87654c40147d0990eca988028f61321d953113d2f41e43b2a6200a5d83c87654c48f4ed02386ca9889e9d60470d95310043f43e81b2a620087d87d03654c4010fd0e206ca988021f61c40d953113d2f41881b2a6200a5d83103654c4014dd04206ca988029b60840d95310053b40881b2a6200a7581103654c4010fd0e106ca988021f61c20d95310051f42041b2a6200a3d84083654c44f4bd06106ca988029760c20d95310053b40841b2a6200a7581083654c40147b09baec8988028f61075d91310052ec18ebb22620087f855cb644c4070f90ab96c8988021fa1c51d91310051ec20a3b22620087
  | 16 => 0xd96310043ec3e81b2c620087e87103658c4010fb0e206cb1889e97a0c40d96310052ec1881b2c6200a6e82103658c4014db04206cb188029da0440d96310053ac0881b2c6227a5e83c83658c4014bb07906cb188021fa1c20d96310043ec3841b2c6200a3e84083658c40147b08106cb1889e97a0c20d96310052ec1841b2c6200a7681083658c4014eb02106cb18ac71d9c465d92310047b40eebb246200a5d83dd7648c4014ed03baec9188029760c75d92310053b408ebb24620087f855cb648c4070f90ab96c9188031d1d671d923158e3b388a3b24620087f855c3648c4070f90ab86c9188021fa1f65592310043f438cab24620387e87dd5648c4018be65baac9189561fa0775592310043f438eab2462038bc87551648c4010fd0e28ac91880e1f21c51592310051ec20a2b246200c3e649d9548c4012ed033b2a9188028f61276552310053b40cecaa46200c5d839d9548c4018be653b2a9188021fa0676552310063b40cecaa46200876819d9548c40147f08bb2a9188025da0476552310061f420ecaa4620387d841d9548c40187b083b2a9188031760c76552310062f218ecaa46200c3f421d9548c4010fd023b2a9188031da0476552310063b988ecaa46200c74311d9548c44b2790eb22a9188628fe1964552310061e3b2c8aa46200c3f87591548c40747d0eb22a91880e8f21d64552310061e43ac8aa4620383c87591548c56187ee6b22a918ac30f5cd64552310051fc12c8aa462b0e1f32591548c53d87cc838aa9188030f5907155231004aec18e2aa462afc76611c5548c4014b90cbaa87188b717dd97550e312ed8fc22eaa1c622de1e645d5438c4016a902baa871880317ddb6550e310058ec26caa1c6200e1e64d95438c4ab6ad03b2a8718862a7e196450e3134c6ec36e2a1c62009cd82dc5438c401aaaebb8a87188028f61065d8a315563b388cbb14620087e87d95628c4010fd0e32ac5188028f6106558a3101c3f43eeab14620087d84dd5628c4ab0fd03baac5188021fa1c7558a310051ec20eab146200a5d831d5628c4010fd0faa2c51880e1f21f5458a310043f43aa8b14620087c87551628c43187ce8aa2c518863279d14358a310043f438a2b14620387c87145628c4014bb0628ac51880e1fa177650a310043ec2eeca14620087f855d9428c4070f90abb285188038b10b6550a310051e432a8a146200c3f76551428c40187aecaa285189738b1895450a310064fbb286a146200c7465dc5428c4053ad07b8a851880a3d6187150a310063a328e2a146200d95431c5428c4018beedb2a65188039398b654ca312adab40eca9946200c5e87d95328c4018bb0fb2a651880297613654ca3100727416ca9946200e4d82d95328c44f8bee5b2a651889f93dcb654ca3100727216ca9946255a5e81d95328c401cad0
  | 17 => 0x1ca200a758110163944010fd0e102c7288021f61c2058e510051f42040b1ca200a3d84081639444f4bd06102c7288029760c2058e510053b40840b1ca200a758108163944018ecc3bb287288025da067650e510070e21ceca1ca200a76819d943944014bf06bb287288038710d7650e510062fc1aeca1ca200c5c315d943944012ed023b287288031d9847650e510043f436e4a1ca20087d86dc9439444d2dd05b8a87288025b60b7150e5101c3ec30e2a1ca20087e86dc143944010fb0db82872889a1f61f63d8a511343e43ac6b14a200c5f7358d629444f8b8e6b1ac52889a9b2096358a515f5b340ec4b14a200c7661dd932944012ed033b265288025da04764ca510063b308ec994a200a5f835913294401c9864b22652889a57a1f634ca51135a7416c6994a2bdb5681d8d329444d2b90ea1a652895b471d1434ca51135a641286994a22796c87509329444f69906a126528803c350d424ca512b49f426e2994a20093d84dc532944610fb0fb1ec128af29da0763d82511843ec3ec5b04a2bba7681d8b609444f0ff0eb1cc12889f179cd63982510062eb9ac7304a200a5d8398a60944018dae5314c1288029e60262982515d5b940ec1304a2a3a7681d8d60944610f90eb1ac12880317dcd635825113e2e39ac6b04a20087e87d8960945434ed03b12c1288c21f21d625825113636392c4b04a22eb7281d816094469ce4c3b02c12889f179cf63182512463b38ec6304a247c767158c60944010fb0f310c1288029760e62182515ce3b38cc4304a200c6d7218860945718ece2310c1288029e6006218251004bdc3ac0304a22fd727158060944014dd05326cb188029b60a64d96315be3b38cc9b2c6200c3d74193658c56d8ece2326cb188028fa1262d96310051ec24c5b2c62b5c767198b658c5698ece2316cb18803555ce71d96310052ec1ee9b2c6200a7681dd3658c40187ee93a6cb188030fd0d74d96310061ea1ae9b2c6200c5f325d3658c40187ae83a6cb188029760c74d96310053b408e9b2c6200a5f825cf658c4014bb07b96cb188029da0772d96310051f424e5b2c6200a3d849cb658c4014bb06396cb188031b5c872d96310053b408e5b2c620087e87d0b658c4010fb0fa16cb1889e97a0e42d96310052ec1c85b2c620087e8710b658c4010fb0e216cb1889e97a0c42d96310052ec1885b2c62b3c5d739c7658c4018ece938ecb188031d1d271d96315963ab9ce3b2c6200e55739c7658c4018ece538ecb188031d1ca71d96315972b994e3b2c6227a5e83d07658c4014dd05a0ecb188029b60b41d96310061eba083b2c6200a3e84c87658c40147b0990ecb1889e97a0f21d963113d2f41843b2c6200a5d83087658c4014bb07b86cb188029da0770d96310063b38ae1b2c6200a5d831c3658c4014ed02386cb188021fa1f4
  | 18 => 0xc953caae628ec2992a7999c851d853254732b90a3b0a6400c74515c3614c839a9ae4a9cc2990039554f6198532006a6196eab0a642995c8754d614c83da9ee4a9ac299002d520553185320047bc3ac230a6400a7485584614c801caaa6b08c299002d560c511853255fa2190a230a6400a7481550614c831938e8a18c2990632b1d1421853200716aa28430a6400e8d43508614c8014bb06288c299002b560c51185320063ac38a230a6400a7584144614c955cad06288c2992d29d60c51185320072ac18a230a6400a5583144614c955cac86288c2990039550c511853255f33210a230a6400e6542144614c8010ff0ab80c29900e1f21570185320045fc22e030a64188bc845c0614c8018e8a2b80c2990023de0575d81320047a40aebb026418c9c7450f604c831958e8a16c0990038b55142d813200746a1a85b02640087f855c7604c8070f90ab8ec0990029760c51d813208ea6b92a73026400e5953d82604c801a9865baac099003630cb745813214cae43aa6b026400d1f7454d604c8f7a38e8a9ac09904f53dc95358132006aaa9ee2b026400dc432dc5604c801aaaa638ac099003710c87158132006a6192ea3026400d8c325d0604c98b2bf0ea98c0990b25761d53181323de8f3a2a63026400d1d7454c604c801aaaa7388c099003710ca7118132006aaa9ae23026400dc4325c4604c8011f70eb00c09909e1f61f64d8e5113d2f41ec9b1ca2c4c7671993639440187ae8326c728b0f1d9c464d8e510051f424c5b1ca200a3d8498b639444f4bd07316c728b0b1d9c662d8e5113d2f418c5b1ca200c6d7218b63945838ece2316c72889e1fa1e6458e510061fba4c8b1ca227a5e83991639444f0f90eb22c72889e9720d6458e510043f438c8b1ca2c0b5681d8d639444f0fd0f312c7288028fa126258e510051ec24c4b1ca227a5e83989639440187e87ba2c728afe1fa077458e510062e18ee8b1ca200c3f749d163944014bb073a2c72880297e0d7458e510061eba0e8b1ca200a3e849c9639440147b09392c7288029760e7258e5100636b90e4b1ca20087e87d0963944010fb0fa12c7288030fdd34258e510043f43884b1ca20087d87109639444f4bd06212c7288029760c4258e5113c3f43e82b1ca20087d87d05639440187ee9a0ac72889e97a0f4158e510052ec1e82b1ca200a6e82d0563944014db05a0ac7288021fa1c4158e511143ec3882b1ca22787e87c8563944010fb0f90ac7288028fa132158e510051ec2642b1ca227a5e83c8563944014bb0790ac7288028fe117058e510051e422e0b1ca247a76811c1639444f4eb02382c7288021fa1f4058e510043ec3e80b1ca20087e8710163944010fb0e202c7288030fdd04058e5113d2f41880b1ca200a5d8310163944014dd04202c7288029b6084058e510053b40880b
  | 19 => 0x3531ca7054d32005ab40ce0a9a6400b55819c1534c8014bf0cb82a6990b2972197054d32005a7c12e0a9a642cb4c825c1534c801a9ee4b82a699217171d87054d32165a7410e0a9a6400b4d821c1534c801a98e4382a6990b7171d97550d322ed8fc22eaa1a642de1c645d5434c801a98e4baa8699002d52057550d320062fc32eaa1a6400c5c865d5434c8bb2bf08baa869900347e117550d32006a7c12eaa1a6400d4c825d5434c8b58bec4baa869916b53d897550d323de8fa12eaa1a647bd4e425d5434c801a3a84baa869900355e057550d32004ae40aeaa1a6400d54815d5434c8012a902baa8699003530857550d32006a7902eaa1a6418a9e86d91434c80339d0fb928699003535d77250d32004aec28e2a1a64019cc821c5434c801aa8a238a8699002576177050d3200ce6416e0a1a64029ce87dcd424c801a9f0ea9a84990035321d5350932016a73b2a6a126402d4c7654d424c99169f08a9a84991efc3a115350932645a6c22a6a126400f0d8454d424c859a9ee8a9a84990b3c3dd1535093200787b22a6a12647bf0c6454d424c80169902a9a84991efc310553509323df87a02a6a126401b8e8650d424c8037190ca1a8499063a3219435093200d4643286a126402d8e7650d424c831d18eca1a849900b231d9435093263dc7c2a86a1264c6f0e8550d424c98f71b0aa1a8499003c3615435093200586c2a86a126400b8c8150d424c98de18a2a1a8499002e3e014350932006a6192ebb0a6400d8c325d3614c97b2bf0ea9ec2990b25761d53d85323de8f3a2a7b0a6400d1d7454f614c8016a902a9ec299002d560c51d853254fa2190a3b0a64188be84dd7614c80117b09baec2990063760f75d853201476c16ebb0a640087d879d7614c8018bae73aec2990031b5ca75d853201c3fc3aebb0a6400c5d735d7614c8018dae4baec2990021fe1175d853226c3fc1aebb0a642c87d835d7614c8018ef02baec2990030f9d674d85320061ebace9b0a6400c9d739d3614c80195ae53a6c2990622fe1d74d85320061f3aae9b0a6400c3d755d3614c80193ae6ba6c2990032b5c974d85320061f42ae9b0a6400c3d855d3614c80187ea6ba6c2990030f54d74d85320064e18ae9b0a6400cac215d3614c8070ff0faa6c2990021f61f54d85320c61f3a6a9b0a6400c3d74d53614c8014bb07aa6c2991f3175cf54d85322ee36b96a9b0a640087f87553614c8010fb0eaa6c2990630f9d154d85320061eba2a9b0a6400a7481553614c8018eaeba8ec299002b560f51d853200572c16a3b0a649ec3e74147614c80187ae828ec29912f175cc51d85322ae36b90a3b0a6400c7575147614c8014eb0e28ec2990031d61c51d85320053ac20a3b0a6400e3674147614c801c6ae828ec2992d69de0c51d85325ad3ac18a3b0a64a8e5673147614
  | 20 => 0x7a40aebb02860387f875d76050c014e902baec0a1a0e1fe0d75d814316c3ec1aebb028600c5f325d76050c018ef02baec0a18021f20575d81430063a40aebb028600874815d76050c010ff0ab8ec0a180e1f21571d814301c3fc38a3b02860087d871476050d9b4bb0732cc0a1b338710d65981430053a40acb3028600a74815956050c070ff0cba8c0a196a1f61975181430068e21aea302860087d879946050d974bb07328c0a1a0f175ce651814300637394ca302860087f875946050d95c3886b28c0a18031b9c965181430053a40aca3028600c6e655c86050c018dacab90c0a18036310d72181430063b32ce23028600c75659c46050c01b2887388c0a18031d99571181430063ab2ae23028600d94435c46050c011f70eb00c0a18021fe1571d913201c3e42ae3b226400a3d84147644c8010ff0ab86c89900e1f21570d91320047bc0aeab2264008f4815d5644c8011f700baac8990123e201755913201c3f42ee2b22640087d85dc5644c8018eee228ac8990031d1c451591320051ec24ecaa26400a3f845d9544c8014ef02bb2a8990029d20576551320053dc02ecaa2645ba78805d9544c8b94b90cb9aa899326c7e1173551322e5a6412e6aa26400b54815cd544c8012bb0638aa899003530c87155132006aa188e2aa26400d64211c5544c9258b8edba2a6990b2d320b7454d32006a6396e8a9a645a95d84dd1534c801a9f05ba2a6990035320b7454d322ee2fb16e8a9a645dd4f62dd1534c8f7a9c85ba2a69900257a077454d32006a610ee8a9a6400d4f20dd1534c8014bf0cba2a6990b2972197454d3215e2e3b2e8a9a6400b4f825d1534c85969904ba2a699003531c97454d32005abc0ae8a9a6400b54815d1534c991c3cc9b22a699323871916454d323f5a7c12c8a9a642cb4e87dc9534c859a9d0fb92a69900ad3a1b7254d32015a6436e4a9a642cd4e76dc9534c859a98edb92a699002d36137254d32006a7ba6e4a9a6400d4d74dc9534c80169d03b92a699002d36037254d32165a7416e2a9a6400b4d82dc5534c801e8843b8aa6990b297a1a7154d320052ec34e2a9a6425c5c769c5534c85969d0538aa699002d360a7154d32006a7b94e2a9a6400d4c729c5534c8014bf0cb8aa6990b2972197154d32005a7c12e2a9a642cb4c825c5534c8eb8b8ec38aa6990b2d32087154d32006a7b90e2a9a6400d4c721c5534c801e884238aa699002576107154d32006a7c10e2a9a6400d4c821c5534c8ab8bec438aa69915753d887154d32006a7210e2a9a6400d57411c5534c801aa88238aa69900355c847154d32006a6108e2a9a6400d54211c5534c801a884238aa69900353c807154d32165a6416e0a9a6400d4f72dc1534c8594bd0d382a6990029761a7054d320de2e3b4e0a9a642cb4e829c1534c80169b05382a6990
  | 21 => 0x321c56550c018ef0038acaa18031da0071595430063ac00e2b2a8600c74801c56550c018ee6038acaa18031d8c071595430063a980e2b2a8600c74301c56550c010fd0f90acaa18021f61f21595432d52f41e42b2a8600a5d83c856550c018e8e390acaa196a97a0c21595430052ec1842b2a8600c74710856550c018e8e3b82caa18029760e70595430053b40ce0b2a8600a75819c16550c018e8e3382caa180297e0d705954300537c12e0b2a8600a6c825c16550c014ef02b82caa18029d20570595430063a38ae0b2a8600c74711c16550cb54bd07902caa18029760f20595430063a38e40b2a860087e870816550c010fb0e102caa196a97a0c20595430052ec1840b2a8600a76810816550c014eb02102caa18031d1c4205954341cafc1aebb128600d1c435d76250c010fb0f32ec4a1b4e9760e65d89430043fc3acbb1286d4e1c435976250c014e902b2ec4a18021f61e75d894369d2ec1cebb12860387f875d76250d070ff06baec4a18b61f60d75d89430043e40aebb12860087f855c76250c070f90ab8ec4a180e1fe1c51d89430043ec38a3b1286c8a5d839956250da5c3886b2ac4a18029d20565589430068e21aebb0a86d1a5d839976150d078bae732ec2a18031b9ca65d85436870e21acbb0a8600c6e725976150c014e902b2ec2a18031b99572d854300636b2ae5b0a8600d8c435cb6150c014eb0c28ec2a1ab7c510c51d85430c46ec1eebb0a86018ee82dd76150c011db05baec2a18021f61e75d85430062eb9cebb0a860387f875d76150c018bae6baec2a1a0e1fe0d75d854316c3ec1aebb0a8600c77815d76150c018dceb396c2a18031b5d672d854300666b9ce5b0a86018ef875cb6150c018dceab96c2a18031b5d572d854300666b9ae5b0a8600c6f535cb6150c018daa6b96c2a1803330c572d85430063abaea3b0a8600ad583d476150d3d8bae628ec2a192f1b9c851d854300636b90a3b0a8600c75751476150c014eb0e28ec2a18031d61c51d85435bd3bc18a3b0a86b7a75831476150d5bcace628ec2a1ab3955cc51d854300733390a3b0a8600e65721476150c018e8a2b86c2a18031d1d761985430068e21eeab0a86cfa5d839956150c014ed0332ac2a18ae1f21d65585436770e21acab0a8600a74815956150d072bf06ba8c2a18034710d75185430043ec3cca30a860087f875946150c011ef0eb08c2a18029d21561185430053ac30a230a86b1f14431446150c010fb0f3a8c2a180e1fe1d751854341c3fc1aea30a862d87d835d46150c018be64ba8c2a18031d20575185430063abaea230a8600a75871446150c018eb0e288c2a1ada9d60c511854358f2b990a230a8600c74515c06150d072bf06baec0a18034710d75d8143004ba40aebb028600a74815976050c010fb0f3aec0a18023de0575d8143004
  | 22 => 0x200c2a995697a0c40185530052ec188030aa600a6e821006154c014db04200c2a98029da0440185530053ac088030aa600e34411006154cab4bd07900c2a98029760f20185530043f4384030aa60087d870806154c0147d08100c2a98028f61020185532ad2f4184030aa600a5d830806154c014ed02100c2a98029d6042018553007321084030aa63287d87d936054c5b87ce9b26c0a98030f5d364d81530053a40ac9b02a63287d87d8b6054c598dce5b16c0a98029d20562d8153114aec1ce3b02a63287d871876054c018ece230ec0a9b6b175cf64981532ce2eb9ac9302a600a74815926054c0147b08314c0a98031de1a71981530063bb24e3302a600c75649c66054c678eec738cc0a980355d8e71981530063b314e3302a600c74629c66054c01aae6538cc0a98cb1dd8271981531963ab04e3302a600c77645c66054c018eac8b8cc0a98cf1dd8d7198153006abb1ae3302a600d57325c66054c018eae230cc0a9b67565cf60981531943e43ac8b02a62dc3c745916054c014e902b22c0a980a5720f72581530043f43ec4b02a63287c875896054c014e902b12c0a998317dce61581530063bb8cc2b02a6d8c5f731856054dafab6e7b02c0a9a4257e0d741815316c3ec3ec8302a62dc3e74d906054c0187ae9b20c0a98029d20564181530043ec3cc4302a600a3d841886054c4b2bf06b88c0a98031d9c461181530063ab88c2302a60097b875806054dad6b706b00c0a996ac7a1373595430068fba6e6b2a867ba5d839896550c018eeedb8acaa180355dcf71595430078a21ee2b2a8600d1c431c56550c018eeec38acaa180355dcc71595430078a218e2b2a8600c77861c56550c018eb0c38acaa180355e0c7159543006aa418e2b2a8600d36431c56550c01aa88638acaa18034510c71595430063b310e2b2a8600c74621c56550c01aae6438acaa180355cc071595432d62f43ee6b2a86d5c5f74dcd6550c01c3ee9b9acaa18029760b73595436af0fa16e6b2a8600a5d839c96550c014ed03392caa18029d60672595430052fc1ae4b2a8600a77815c96550c014e902b92caa18029ee0172595430053c402e4b2a8600c7773dc56550c01caee7b8acaa180395ccb71595430052ec1ce2b2a8600a76819c56550c014bf06b8acaa18031d5c471595430062f990e2b2a8600c75311c56550c014ed0e38acaa18031da1c71595430063bb98e2b2a8600e57731c56550c018eee438acaa18031d9c871595430063ab90e2b2a8600c74721c56550c01cae6438acaa18031de0c71595430063b418e2b2a8600c75831c56550c018e90638acaa18031d90c71595430063a218e2b2a8600c77821c56550c018ed0438acaa18031d60871595430063a410e2b2a8600c77321c56550c018ae6438acaa18031d8c871595430063a990e2b2a8600c74
  | 23 => 0x5855339e2fb9ac8b0aa600a74815916154dbdaaee7b0ac2a98b61f61f641855316e1f3a6c830aa600c3d74d906154c014eb03b20c2a98021f61e64185536e52ec1cc830aa600a77815906154c0187ae8320c2a98b21f61f621855316637396c430aa600a7581d886154db74bb07310c2a98029de0562185530051f420c430aa600a3d841886154d676ab07308c2a98021fe1d6118553004bbc3ac230aa6b2a77865846154dbb6af06b08c2a98029d61b4118553005aac1e8230aa600b6682d046154c014eb0d908c2a9802cda132118553005aac1e4230aa600b55830846154c372bf06b80c2a99d69760f74185530053b40ee830aa600c3f749d06154db94bb073a0c2a9a421fe0d74185530061f21ae830aa600c3c435d06154c018be64ba0c2a98030f5d074185530053b408e830aa600a7681dc86154db74bb07390c2a98031bdca72185530051f420e430aa600a3d841c86154ceb4bb06390c2a98029da0472185530053d400e430aa600a79801c86154c010fd0fa10c2a98021f61f42185530061eba68430aa600a7681d086154c014eb03a10c2a995697a0e42185530052ec1c8430aa600a76819086154c014eb03210c2a98021fa1c42185530043ec388430aa655a5e831086154c014bb06210c2a995697a0f41185530052ec1e8230aa600a6e82d046154c014db05a08c2a98029d61f41185530063ac3e8230aa600c7574d046154d5b4ef07a08c2a9adf95a0f411855356d3ac1e8230aa600e5583d046154c014ab07a08c2a98029da0b4118553007334168230aa600a6682d046154c01ccb05a08c2a9adf95ccb41185530053ac068230aa600c3d741046154c014eb0e208c2a98038da1041185530071b3a08230aa600c75741046154c01c6ae8208c2a9ac69d60c41185535b71ba188230aa6b6e35431046154c014ed04208c2a98038dd0841185535b72b9908230aa600a75801046154c0147d09908c2a98028f61321185532ad2f41e4230aa600a5d83c846154c014eb0f908c2a98031d61f21185530053b4264230aa600e3684c846154c0146d09908c2a98038d61321185530053a4264230aa6a8a7783c846154d6bcad07908c2a9aa29d60f21185530072ac1e4230aa600a5583c846154d6bcae65908c2a98029d60321185532ad2f4184230aa600a5d830846154c014eb0e108c2a98029da1021185530053a4204230aa6b4e56830846154d554eb06108c2a98039560c2118553007334104230aa600e66720846154c01ccae4108c2a98039990821185535a72b9904230aa6b4e66320846154d69cca64108c2a98029d60021185536c52fc1ae030aa600a3e841c06154c0147b08380c2a99d69760c701855300537410e030aa600a6d821c06154c010fd0fa00c2a98021f61f40185530061eba68030aa60087e871006154c010fb0e
  | 24 => 0x2001800400400200400120220038004020004004806409e01600180100620020050044034005005000400000b0020024000000000005800200a002801c00403e001003800a00000000d00400000008020004008003001c014000002800003c00500200000020090000030014001000000401800000180180300090000059cb4bb07316c8a98b61f61c62d915316d1f420c5b22a62595f835c76454c052b906b8ec8a997697a0e72d915372d2ec1ce5b22a600a3d841cb6454cbb4bd06396c8a9a4a9760c72d91530061fa1ce3b22a600c3d439c76454c018be6538ec8a98031d50671d91536fd2fc1ae3b22a65da5c835c76454cbb4bd0638ec8a9a4a9760c71d91530063ab88e3b22a60087e87c876454c010fb0f90ec8a98b68fa1321d91530051ec2643b22a65da5e83c876454c014bb0790ec8a997697a0c21d91530052ec1843b22a65da5e83dc36454d254bb07b86c8a997697a0e70d91536d52ec1ce1b22a600a76819c36454c014eb03386c8a997697a0f20d91530052ec1e41b22a60087e870836454c010fb0e106c8a98b68fa1020d91530051ec2041b22a65da5e830836454c014bb06106c8a98029da0420d91530053ac0841b22a62dc3f76d916454dc9a3ee9b9ac8a98b68fa1262591533cd2ec1cc4b22a62da3e841896454c01aaee7b8ac8a98031d61b71591530063bb1ee2b22a600d5763dc56454c01aae65b8ac8a980355dcc71591530063bc30e2b22a600c75861c56454c018ecc838ac8a98031d19071591530063bb18e2b22a600d57631c56454c018ecc438ac8a98031d18871591530069ba10e2b22a600d57321c56454d212bf06ba6c4a980a5720d74d89531643ec3ec9b12a62dc3e74d936254c0187ae9b26c4a98029d20564d8953014af41ce3b12a62295d839c76254c4b2bf06b8ec4a980a5720d71d89530dcafc1ae1b12a60295c835c36254c590f90eb22c4a98029d205645895371ea7b9ec4b12a600d5773dc56254c018eb0db8ac4a98031dd9371589530063ab26e2b12a600c7763dc56254c01aaec7b8ac4a980355ccb7158953006aa996e2b12a600d57731c56254c018ef0c38ac4a98031dd9071589530063ab20e2b12a600c77631c56254c01aaec638ac4a98031d98871589530063a310e2b12a600d57321c56254c01aaa6438ac4a9a4257e0d74d855316c3ec3ec9b0aa62dc3e74d936154c0187ae9b26c2a98029d20564d85530053ac3683b0aa600b5583d076154c016cd05a0ec2a98029d61841d85530053ac3643b0aa600b3684c876154c016ab0790ec2a9802d560c21d85530061eba4c930aa6e2a5d839926154c014eb03324c2a98b70f9d1649855370d2ec1cc530aa600c6d7298a6154c014eb03314c2a98028fa1062985530051ec20c530aa6e0d5573d866154c010fd0fb22c2a9b7f17dcf64
  | 25 => 0x2a04f0010000012003000000409c002000000001e003004800001a000003002800000d00000000000000138028004021001001400800b002811000602f002802c0ba00b005002400201d031803c00c000003001402a013003000c004002004000c00200301400a801c0010018000004006001002c00003700180000160020008020000007004004c000008006000403c001000000000600b0010020000021007802400a0040018004006000009000001a00f0028000018003004800805200800000e000000300101940020030000020046001001801c056000003000000001800080040000000008014026004005000407000d00e009000400600380000080000000004010001001801801e019000000001e00c03000680220060000008034003006800001400c0008038002000002801001001405b0050008008001807800e00001d8000008019013000000200b000800803600300a000000000a000000000a0040028038006000000000000e01f00000ec0000080000020000011002000002a0020018008008001000000000c0060040014046002000001400200200100100dc002001800c00600300000340020010010004014013007000400200c00700400020100210010006016000802c01e001007805401e00000100180020030018040002004003800000000e00b80180b800d0038048000002000003400801f01980440000010078008002007000800403c00000700140000060080000004000001000400200001580640000bc0060000000002003000400e007002006c01600500c000000000a003001400802200000a0034002000000001a02100a8004032003000002403e01801c001400a016004801c016001015803400000000080980060000000018020000000000007400700280340120000000018084001000800402a000001800000a00c001000001400902c8178094013000000000c0000108008000000035807000001c011003003a000005000000e0000060000002013012000804a007003001c006004003000404a0010078004000005002814400201d00080000040080000000008008001004401c00b000800c000004008801800000000500000020060000030000001000801001200b000800009a00d00080680000160000000118001010801001800b0000010024000005804c02a003000005401400000100d4006003000002c052000010808000400b00000000100010000008002001005815c000000001805000000400600080080020000010002004000000c006009005001c0080000000018000002003003c00000500f000000404700b001c000008003803c00001600c0030000000003000400400c005000400e00200001b4000000011003800e00a0010038054004001001c00a00000100000020120008008000000
  | 26 => 0xcb1b66100504a033c34580013c85910000000d6e0000000000bc14d01b11b6c0000003b531b4000c02de5d3b911835d0000eec9d9bab00080060010010000006003009803801800500b80140000010000044000007000000800001100380380b203b00b8010018003028801c00201e000800001400400000040160000000044000001001000001000500200a400e0020008000000002010000400400100100d400200301000000f400500100240080040008000000006007801800200600b0050000016006000002c03501d8014000000000005000000700c800000800000c000000400e0020028024009004006000e01100a0004050002000801401c0000000004000006000002c014001001800400400400000000000040008034000006000000000800400180080140000070000060006006804c000003005800401c02100080141880040000050050002001000404e00000080f4012000009001002001200000d802800301183f8000002000800411000e002800800e00000b8000000001004000401e006000003002a005000001000001b000000801000400000800060170040024112004001806400c00100b001c0120050010018002000001801404c0350018000002000000000001c00d0000004006007000801000001400b800c04e0090000004012006000800002800f02f8014000004000000c004002001806c04e00201080080160010018004000001001000000000000000fc004000005002000200d00b000002200f0028000010007002800000800900b0028040000003001c00200800d803400800a00080f00060010008004000000000000402c001001009002802d00a801000a00c007800c00201d002000000000a002006400200300b0004002020002002800c00002b00180120020068004000000000001c000008000802000c0840058004000014007800808a0040008008002004020800000a00300180d8058055001809c0020020000058000012001001c014000000001400600500000040020020018024002004001000000000100e802c05000100180040080140000018008017001801003a0300008118018004007000000001500001bc008005004000006200a002800400a00d000001c00200a008000001a007000000400000e005800000a00400180000120010000014016009006808800400500000000000060000070000019005802800a00000c002000e004001002001205c00e800001a000000002c0020000008000008003000000405a00e000000000400200a804c00001000f8000022008000000c0040210030000002000000800000a00d00280000aa001021800000800100400600060000068000002008000000c0000000010008010000005800400000500080000000000000020000000006000000400d004007
  | 27 => 0x49ded6d222651a94891641ef1ca24922fb7de27180485664665d1d709350b8d534aef91f813a50c2cc59f83ef4b48a2246257865180612e404429e0c712be4b153232806b60e114650ed998ab10691f98c2173e3ebae9c57c88d984150c36436b2941b7542e741413014c5160d35b4eb0d5d07d94991eac4de5ec4161694c22a4d09332c9168ae660705c57001c4147abbd57a8a20a3d7b514043c0f8af791ea1790d6b3540dec61430af349ec5950b62c30bc31cd278220d682d7d6062ca83b444f5372170b7c85b152102088592603aa290e0c19e262b5f183651f5671ed0698b96ebcb5205d06a92a4e561a24817e0eae1958286a46b2544a28104be396dc9600a92f48674a22230c36895c0027224e2030d6123b0a3ee6cf5f07ed44b004a666a3e3c4b3890e811f1ef8b68c5cd5944cd0ad93ecaa1ebb3d1ad8a1c6522dcd5b84506742ced40a1ed0855c29348c313fc1689a5e9c110729e445c95c42311ac97a0aa06b11c90c037727380d58729d80219edc3b61d408a93492149d231b0d3d6c12b702b295456045b355a35451745703c019d6c88cb2f34eb836b0c51ed07f272408b0a318016ca1405ee82541c656a1e80b3d8283d30398c093342e108ead0cfca15f0000000000000000020c000c2f5db80011fcb3645d0cb44063606260cf926246f0c10fa547209b41b8c3c0001df66480004fa2b4466975b20e00000027d80003ec64421507b800000012140000000410001a7cab800000140005e20002601090436068d070efca7c1f29698588ccf403ad8c00000031c255817038b1148fa82ba2095e4a9e967813f6ae2500cee00050f31a967e37f4aa26bc0cc7d500000000000003e49b0d1ed7090000c2c120d4a4598b4403ed302d8a4828b03c441780006180f569006343fc8675222894a6900027d800000000036424091d5af7426b0a48d800000019e00000e665f315800000034200004aa3de4e9b13d2ee1be800145e510c343b690b8a964e44062db97173a64bd00000cb6091751cde95a569294f068cb3ae22528001aa20005dc9fe434c0003492ab86ac3b800020cd9f2000057c02cdae5241f589fa176b9480022fa32300000025c4948a77471800000009251e8cd8fba0000000c84000748117c000000ce034c1dd4cb6620dec4984a9c1cc201adc69084a34d90f54cf462d00000008667da65e1a307b08b00002a85a680005b93431a7800020883040000002bcb204f8c94113726f126a1a54dcb0c8d10000556440055c00000031e000076500000019a46b50001f0554d0000000a4c492624000000030b0001a12f880000000001334000af938ba8652bc00010796112f6c4700000000ba1943892c193461d50002bac000d1a44680013e2000338daf591c77906f812cada71d800052600004f0dd35ec9e81784a60ae854
  | 28 => 0x40c1002f61b8abe17c471026000028300015b98ee1470002c98a4ece53570a143383ba60b5fc422c0ab0fb950520a0000990000a0c277422a3c91f00004855a4c0060004d48000c18000507903996800000017213ae1860002cf4b2c19f3ff6f46b7a2592a223ee000094b818000000d1c3e18a1200038c0000000000000000000111427f564c8007e8b0400020d4dc800000029d8808c7d31f94ad12912d00013948f08ee2bb29b51a6b29000145cf9654753da02c3c230000020ac45a5a9690a2100004c02891e609361f915f68bc5961de0b093b1a32bdc00004298070000002fad2de6e527900005ca000000000197e6aa443337052c45d40574cc00000000008d51945d906a4588d88cd73842c640004e23cf1a38000c5a29f800023421500007f0000b955000001a129c2178add0b7e8932ee0000ec211c0000afd4400001399e2cde432a3c1054e1b2000000324938c0000001e00a8c2324a580003e8b5f3952a4538000c0d0cb05650b1d4b734386da1310b80d5161eab0c8b1359266a312b3a2e04d23f90e89288a5c2460f220d0c1c0b50512dbd988b23b76b1183276b609129186287591b626d777465d26d223cbfc74b5040b2180fa661a70f4501e6993f4aedb78f18a615835b5e00f6207a3ada9eb185bc0a39a2a91929c091c1e8cd82d6ad361f238411f803d4a241f61243396a6603497a1cd9c22b5125899d27ecee4ba9cf4e97b08192a96828189d3ff87a4b48b5926233a97d11dd206866029e23b02a5ca493e50ad180ac96eac552e799705a443203a187846e00e0af11d57f7bf33b980846aad29058192caaa3b760c273d86083f2ff9c7cbc88445f074b551075f1f225680a22f8580b1d838191002401389fa6f62cc9f44bfa62105795e806e6722d523a045d1ab0231f816ce68d49c0330a521731b5017c5520c454ba3c147012c2d70968ffc1f61f00c5487e1125f34da180dcf8632b21d8d267c46c2f651772e2484cb284a84f50000e3577bb1110170842428e88fdaefe3213af50f80015996b129b5b6540f07901a452d17572e42d5684240c012fd2e958fe9dc048aff39fe7f2115eff6354501af1ae4092028013e1ec8f48799050b4059c6d370d22f4ca1098a16f8064a624febd300ac000b4820000004ec0002242dfce288bd648800000070c55a400032aa470002778e4120fead0d4c000bd1531958078a93e4291d744be87510c023c7ec50b255ae8d9dac8d30353281b8be74dc2a7cd680633770c612226018a4863a6f4106221b47ce888e02c521004195456068e68a3ca0b5aa90053020004e2a069694d6d0aad3750ac83d3a1a0a572c101cadaabc00092c55cb0d52748110eca62b28cc282b202ce59c29a38ab5398ea265550e6257b69bb04f32983053f34861be94964ce1c986e0a946a768292a4434ad30e
  | 29 => 0xf79d382fa4496633174b7235c54ec38340e20baf02e10d367ace4d0b1982649c4825568e464fce9929e04f223e2733475928ab7de1a5241635071d40da4cde66a61f888c479cca454870e932c044cc0a3edd4a684448c355ca3236a68000b8c79000000013fa3c2000230d7381b3336c000000892197af7f5a44b91de2d7572800022f9a5da888f4321818400002700020403067c82212e6ca7c9082d803751bc37b5968cd10b4bf0a4115309d3b7b6842b1e5463ff5b532085bf23d08222c4b045251faad9805c00000024686a440c63e00007127011038000db00003233278000b258002ab78408695e2b14800088a8002630000a6a689b20c84e00037c03733d6a7d245ad0836a00026bc00042c4be5faa6d17377eb289a824000ce90b3eec15683034bf9b7103ec4230802c52267960002c4828868a51d166ca7a6fe5ad800a8ecd496b085502489ba14e62b0bbe8686bb921c21e74ae05add9699ca25cf2d68e6c3194f51eb6a6e6b228b49597d207c43fa734448bc44d894646ca4ac141135ca12a7e5f3c5383085212470bb453e6405639ba0f1846848a039d72675a622b5d8000ba44f0b191ae26611ab86648a78c60000ed96e53e840980018960001021dc950e0800ba03958d80000d88d7d85a5035d313b4000c443f18a6c1a105700032e8ab60000002145414c853cd1384558c0a150a0c8486a4a08389054d8ab38000b22ee200052000002f65de592937ca1a1352c900001fb925693832d8c0abe5e310f850e5522e08af4bba53b43d8b9c00083600034501d577d00017b73cc0fb440c00067027460300005db6792b90ca587801a0000808762530000062102472b66723c36a2233bed9dc14fe060a1125404c4c595ea0a049d61dbc9cb56d46e292b140dc95d443013518f89d0cae508a3450cc00032f8000359000006e5d13a2ad900001940401a59b7a03825e000617000080a49507c65889400003e1141333d85366f88b788660fc81b274aba5570971ebcc402585cfddbd02a3ca66da094e928ae50b0fb79ee1273399bf42260002fb061c78038200000000004253df14e511c3135d413cc32e3db2a6e6f8b404cc000283410a22cb04289cbf0000145400082c94e1388000a0107738e59051720002a8ae205280001aec0015bc4cb0000576a148650518ba56a42af0001064d502fd5491b18d8200034f1c5974141505e1bacc3e8552d60908cae81b5f700004506150b033ed53906208a0230363000000000043e04a22f14740009f864c09f6000000303191181bb888262ecb7e279425d896ce8a4465ed00000005736120000a58a8b4690000682000629b408694a605625258fd000000000995aa40b2fcb0a262c82753a80000001cb494a12800099700007cc000c49639af58d040000faa2760fa5b50adadacb6438864989b4a
  | 30 => 0x662000000050af7e4f76619a55294afb225ae0890038f1301d9994e7a01d69ba473e5d231b80f031cc0bc3203807908be1060712c088faa779750f02b004410ef840c00034800000005ce21c0cec256c0ee079fb03240df927800121a9730e7934d7e84e6b1e0000c4a6393a8b3c11464c955de47419013360df5d044a6d303d8fed63e18f0b3a3a9876cd4613343436c6120442960bee253263ab6c62e34d2cd1e18f88bd08742c9c2127043d990a800037400000085fe1d660a9a5117e8d90adc0000009480f1a1c8d405e128c5d88b8603825e4000c56bcc0001ee18479932fdb41144661b1ce18175acc1e410116a4545cd35e13fc32666b68304e053c168c920fe18e2b1656c03008ce1ce2fe218826e452a498cb913231201bd37805411e61f25f435e48323721d827a98f5aae5f12463710fcee3c460cf14189ef48f40004e701419bca6b15da830000b2c43b9832be000032619580000000000335a865c710a20e00003ab0000d14394c09077400147e37d11b1afc5bc8a688580013f2011685a76cfb88f8c6f56040001fa398a3bc77a000000000000000000030e14525105a4a29d1d3bb522380709b0a2b3238d9c207a320001e7557518b07e4001a4c4aa0000bac30068534e2e801a2a990002ef400089a4ce0000df833720326b5408a8d6940e1c00097e24c10098f67d40302a8efce6590001b54a813b300007e254a0000000e44a393900002a6e00051c61e8bf0000bf98000000e2221580000006ecc5400020a800058f09b16e0000017000000038000011f7210764000000000032066d210836000052c80e9b3817491e47200000003fa000135a34fac68000001ad044a00003e197650fe9896ad47691c4902b258190003479050aee7fa09480000000000320a255544fe02000000009995c5a2dc000cfd01f14d95d247f5992940c84cf351080002fd08e60ec2d0b4ebed46e80350e20001ba9bcc8624e9560e02f672502b5d1c7a7dcbd22c621396c465a1099d1cf502fb00025a093c0003908000c46b2f0000000cfc7201d508ad53500051e1b598748c13aa16d17700002e98000000d6200000000001b769b00000005f2c9703c76ac0004808970000d1034388bc8588e153920200005c51798cb185816e427b10008acd60269c4cb122953660f897767ebd4b043166a0005580f8d7a00000001730000a8450702b08509365f604ed9cc7630d41f608aac3335c145995aa5618509d4c022d741f19a02c8d4702f06e75b483b0500d0d1da7cf5fc74b88f62b165b18c4000000035c0000e4bc120f000027d3c300024ec5540004c8b5bc12826b3cb8e615c6290eab2fca5807952b323e83d6b22e9f9cdd21c7a14f78001a4a000617645c42e7ef0d706c275f3ce32a2a668a4b7d63120b8fee5716342620f1a6a3216aa31638b2e2
  | 31 => 0x4d96c34d4805a25b000199a0003d180000a406c00019780000420000001a8000000000003a40000003218503c5b69d90f58100005d700005847bc38ac5702720005fc18d58384940000c881bd752000332cb0085f000250cd840006b80000000b686580bb1316000521210cea0ac60c4d1341d7000371a5745c300046f8536f100fa4fe1d902d08c900023f206c6279c50fb2af6bef48000a559815a3e02f3d5e60001321a0cce15490bfa86d4e20da401a759a580d458d0000782add2130b54000c4a3980000000be5589a0585eabee884e898c9c7ea23989393f428688d9b240009788a1c001799000000156400000033a14c8000c7200015f8c30505495b59c00059c33a85159a028418207c03c4963d55b554cb000036580ba0008aa0a900000000004c2970b2ce87d0001bdc0003e14d0ae74a1c3485c9400020624a05680000003a70002d30966a900001754a74000530afc60b2c050772b5c2b9cb85c5452b19003926105bc4a4a485f531e80009522752b1000000020041b51842a76b52bf4f6a4dc5121521a8a7ca3ae2c4136c48a51de5993986634798db8c04961633ad40bf703a5091074f7409f4032e261e674d55aa090c0fb6bc5780010f03e62509f8416c96c30a06454a696d1782bb4732a6f13d19fd95896419900b1a060004fb800000000009644413c6c9938381e8cce00000000011fe92258580948c63a584ba7b50080003050884f583c655b86af4b20bd2a6a2040000003a10000e98266000104d8fc2fa0001d547440a580000000e0b922d79ac0a083ac2860294da4af261b326ca3623a452a124298000155adf962abd510ca3b752a61726d9d191b69533651b4077b02f0a82970ced87a0cb06a4aea0553c527240007a76a62a68c6671d0002efc0002c70000000e68921126a90c2ccc5c0000000ef00000000000000000396800000099b5d1189841aa2e4879eed594a9d485c0015fc9b32a11700be459400000000000005478001a82283d760000000aa51162e7cf5caa91b98bb80000001dc90294750000030000000195c5a9cfd72b61913c17ba3ae8eb8001f4d1393090002a8874a1e61b19e1c0000004a6a5a80000002e212b882446a09f14b4c74d1133b0de40d6c2ca5e2d780000000ddf2700007184c225656880001da80000199ecaaa3580ef8c502e89f4800037c00000011bb7ad66d00000003d99ea108175e2ec82c40019ea344673a3a4dce5db30d0f499c800018f96380006ac6a900000000002f9a0f0e4c06819f84a12ae03402485a9530815df1f22c7526661469e703a65743bf89448e8a9c2148b5adf6bf944fd724c8a03244048733602f60ac800164258351999488a88fd441dddd0d6d5d5a31111328aac0e2f5610048c752b9ce915a4371f92acd03ac165afeab4360c5e04e4210b1040924bb478
  | 32 => 0xd0b00003fe9728000000000179d1166cf604c80e0121724d600015400ae00035a491e0001e60e8d82422200029cc5b89f42c980000008c5529306460299580024182b032601203419e400000012040003460000d615fe89826432a53ea0000000000010bf20b680000000002ed00000003d94d2ab90f62abf461c3fd447b3e15e0dc0934bc719383ac51b928334ab403185a842ca8b4d6f81c0002774e0a14100000a059a0f08001fec0005eb00000005cc00000017cefe88fb48daf8c98cd4b0000c18fc84771c3358d6040004f719eba3662f5018001245b8702e000000000015c00001bb0002a80d1d6a870e00ab259454812c02c1053aa31b0002b451cec663f5491289ca414b000c43dc7bfd1113e13044b73a51f7d8e08bc5be1bfc1f8abc9df92bd59a7efb4e82658a2b053c98814be2d6e0002d0179c0006a115f04100001a8a7210ba58500000000008140cd8000000b8518e856b59100042baf000000000002ef0abc00037600008533644554b256eea364c8000107421b034972c046a836bd34ad10a66e39d825814c00034d16180006860721b4437e0000aa80000000f74b28001a14a15229a6acf220d51ec58755e84790000760000548a5a029034d1a759014041940870001e14b3a000244ad5c000ac02b0981c000c9056140001d4424138077091a00060c7518000c5f2f2e1bc37cb24d4014ae82eab634faccd96a1418000b8d7c5b7dcc1b2cd030d165310c142300000a991680e27bd800000000071e0000000c764d96aa000000000000020780005020000c80000cc022e2c89536c228000000dea0000001b787024922dd84399d66a250e8000000abb0000000fecd075f7c6525e817e0002a145728091e68001002000000000000099e677aea8c1a2115935d80e6ab9846a18c8f987580001ab40000810002d3c00000024433740001772678000532a81230aa900feb970dda33c480bfa28c226c22f2ef4f60001528d24332c000c9e72c122800000e93c2c3914400000000000002cd0000002840000c6f000000080e0004069181752bcb0001fc04667192879da133ebc480009326c21fd800000058a0004e5800062003d07100005dd5565b9e2a0008113b40b2bc650b97b1e80009f278f3780000dc0bd8000267600056f6b9aeb184477a00000000001b468c1eaf25a4643732410f8a00000020e514c65193f0aa04380004d3b2c40001c64bc0b74d8004746215a07ffbf65c8a65460e21dcda8e788da3666b31f1aca0b345de52444f6d000cddd002ec1a121c99356d95ba2ec09b0a544401a01db932caba23e0fdd5ce213898234128eb7114e82f951409c30b6a9d1382344489889aea8803bb21b038f89052fb07c5301c15bca59ee5057d2cc29c0ae0b030b5ad60e0023c4fbc3bce70aa65f215fd1e2b91a2c9a581b62d6
  | 33 => 0x957a8ed050c0000002d8538694555ceb085983fd0db40c769c0f99c00bdd0fc00000006888ca00019e97d09a84d145b1aec425d780000676f720006b58000a68bb25f4015b25413c15b2a787fc188de427ccee8c950002ce1982cf62b5829c0000a812e848c0000005870fc473a3ed000106c8b71026a80001587b7a1a4b578488a655f026dce1a8ec558e42c66090dd7d2fecce0894221c30905ab70626aecd9124a0d592ffc01d1560e803f47ac000000006d3e40000c2a53d742b3a24300009e26160000a280008f60001da400000000019b0000b5eeb2b044000000613aed03349a25a3ae9f324000105837800000009fc766b1a4a4b708000e9eb6c0001d9d4920006b90318000c8a4108c44e4ea8945d8cd52607b6695212c1d84b54180528d2262c35799ed098af6324331c378b1430e28688faa026ab8920076afc26a9ea4ebc0002ac06b01fcacb0002e86000ca540b80000000002a5dd6c0006b91bc03c0e4a3a0254007821027221a345cd7c80542814cc0007840000000524cfe5d88001526000362a80497073c4440000de89a0000276400017a0000b0c00015120d2e0b8431bd0001e492301c82b1165d956c8010df344a003f045589a0d4a79f38e33b10500002f2823e1d23cb547000131a2a25ef8b503d00b746000002862dbcb5b2a1abe47e0000000c680005ee4000ea6bb18868000cc800000024dcc2500000026745c0000238000000000000002256960001ac83c927a00066cae0d4b680f9e78001714c072f418148467ce00018a4d9a37e1ca80003c00005f0954c0000000fc0e386486c71ee9ff04c6b230002c280448fdd5c42fc000c020002b14e04c6356f80000140005eba510f069d461181d83ce01302a31aceac0004b8127230d00060e4b6070a22733e800000000052280000001e55a6b4d576ca744118000000b2b4bca8b0c4e2e422b30dc06079b16826b81725234fd9db043c42f4d317985b176b5b68268f4a8d72c8000149e3e707880000000000c080017eec6e000182c00051a000000122a000000184ca4c0005030000000acf0000000e5e00000000000002efa5fa088000649118db7d92e5d6472a2780000005125f353e065101991a40b632b35334f4f5467100027fc2aea4c40357d4e3630e601af2945053502c242568a00032a80000000160000000fdc105000000043a1c557080012842fe443a0000003a100005a750cd6414633200001b380034e852ec13dfe86801df4ba1af30943e4c4e04ea6a8b66b6039c824c0fc56c62080000002124804b4d546be980034e17340000000000b5300000000003fd1014e8000005a9bd3f9a1e41648f75c71e8855a6534fc4ff15a8cb70000fe7a467e268785214ce8704b19c2c29a0000000000b7859f04300001ae1ff0000828f655ee0a100005f234b315031
  | 34 => 0x8ba3998f208d38780000209df423930d1f2d3951a0e0d01471a28aabc42f96a13fa94bceae58b2f653f05b678e5d6ae313ce1c2001e84d60e895059b120372163662a233648201493855e8c41252260b4e72c73337888e578402bcff04a888ac0021ab34c4701dadff07f4000bf04aa904000006a27d21789641c339920649c0c8f08c868c94e16917457a852264a0000000000154800000000054f67d31d10c668900000012ec84238800015789ca4f48f24fa03970000000dc42105fe0000df2aee00000003d8305aebae24cc4220000244962ec174e395706b41c70001500c60d2200030a8d0033a2460b5f3d0ac814e0ce45b249d238acdcbfb1751cd8c7949cb9900021053b4b1e126059591887c5c0afea83060f00000fd31c06e359a396312d533eb1981550a5d2db227cb46cbd09a247cac69876508d4000060dd2f2a080005d000032e40004a61501ec126889752a10e93c40ed5700444db444146d23317ccb3050a1594e489864df80000000cf0000e9000031a1d8279519c25e1481bbccca8a1407400098200046e278078ec575ae3160b3c1ea0451b505e40c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1466929907154f100041d660641c553c4001436949887154f100051564e621c553c400145593144764cb10006911888154d32c400124f9854f624cb100444d2617455231c4001531941d5708c7100055464c755c231c400705e97e0d6454e100058364843595438400160d940c9654ca100051564e651c5328400103f9461d63946104cc95a5a87147634400188f7460a74d8d1000495a4687d53634400188d84dca72d8d104cc95a47855c36344001614955c46418d1000591a4a641446344001255981905118d1000685610641446344001a15871905118d1000585a52621446344001455939907154d1000519a4a641c55344001075981907154d100070518c641c55344001835981907154d1000705cc8641c55344001c1764d8c7154d1000705193631c55344001436949887154d100051564e621c55344001c47321887154d1000711a4c621c55344001c45931887154d1000523648439d9434400148d9210c7650d1000525a44431d943440014999010c7650d100041d660511d94344001c14431447650d100061518c815d54344001864622057550d100041da4787d95434400160d9210f6550d100051524575d8d4344001a246420553d891000691d8c8154f6244001e046418c51d891000623613739cf62440012649161543d891000623a1d4310f6244001644956046318910005912557118c6244001a27642055318910006891908154c6244001a476320553189100069118c8154c62440016269498c511891000499660631446244001a458318c511891000691a18631446244001e076418c511891000781190631446244001a459818c51189100069161063144624400148d940ca764c91000523650321d932440014c6910c8764c91000532640321d9324400145593144764c910007110c8511d9324400160d940cb654c910004a3a6032d91324400185476205534c910006851908154d3244001a4462205534c910007059c46418e5144001c467118c62945100060da0464dd631440018668118b758c5100040fa6075d92314413345691dd7638c5100050765075d8e314400142d941d7628c51013c9525983dd63144001136981d7648c5100044d660751923144001c147518c648c5100061518c875523144017134985d1548c51000515a5875d8e3144001515941d7638c5100054965075d8a3144001466961d4628c510005496507518a3144001c2475190628c510007111d46318a3144001c147518c644c510007091d4641893144001c447518c624c51000691219534ca2144001c447518863485100061918a81dd520440016529614763c411000598a5851d8b1044001074916177650c100061598c815d5430400103d9421d535881001c172617654d320400124c9854d624c81000714ddb739451004001c6376dca5144010
  | 1 => 0x10058365032591329444d50c9750d424ca5113e4321d43509329440184d835ca6298251006159c5839886094401872716006218251006199c682993658c40183671a1262d96310050da47749d3658c40103f985d074d96310041da468710b658c401436949ca71d9631006199c682d07658c40183671a1321d96310051564c759c7648c40142d9299276552310060d992819d9548c40185732a0676552310050b64a841d9548c40105d9890c76552310040f663421d9548c40107598cc476552310040fa6076591548c40181e6460c715523100615dd8815d5438c401a16642057550e315be15a0776d95438c40160d929936550e315be85a0664d95438c4018367161065d8a310040f65287d95628c40160d9310b6550a3101c0f26176551428c401435941977150a310050d650651c5428c56b85681ddb654ca310058365262d95328c56ba468198b654ca310058365282d95328c40185687a07654ca3100691a0a81d95328c40125691a19544ca3100493a6365589328c40348e97d91424ca3100583a5954509328c401a0f86551424ca310060d9c584196608c4018367161065182310058364c42d95424c40143594194715093101c1764f87d92514c5558567160c51d8e2101513a5f6454d3288555a4661205534ca21004d12458550d328840528e98d91434ca2101523a5f6450d328840705c9760f6454d210058364843d95434840103d94e1f63945210048b26154589428c00141d93217745863000607dd183d51618c0012549160f54586300060ddd081551618c0018647220554586300051364f54dc9618c001c24741c851586300051564c75986418c001455931d561906304cd54a47755c2318c00181c6460c7155130006151d8815d5434c001a14642057550d3000529650621c5624c00348c97591424c9300068321954509324c001074916177650e200060d1d08154d6188001857732055358620007051d0731456188001435941d6618c6200050d65075586318800181d845cc63d952000607611731cf65480014959418c7158d200051564c851c5634800181c7460c5158d200061560c711456348001074916107654d2000523648439d9434800109d9810c7650d2000523648431d9434800107691e1f6550d200048766043d95434800160d9210f6550d200058365063d95324800124e96a19534c920004936508654d324800124e91219534c920004932636454d3248001a0f84d91534c920004932616454d324800544c97591534c920005912456454d324800124c96615434c920004d12458550d324800528c98591434c9200152325d6450d324800168491591434c9200040f6508754c614800705c985cd53185200051325d534c861480016449154d32185200040f65287d96314800144e96dd5328c5200051564e641c553c4
  | 2 => 0xc0146491595721814300463660435c86050c01c0d6510d72181430041d261659c46050c015859210e71181430051564e655c46050c01c156510d711814300561648435c46050c015919010d711814300543650321c5544c8015449308471551320054365082dd1534c801854762057454d32006511c8815d1534c80190d84dd37254d320055124574dc9534c80150d941ca7154d3200543650721c5534c80154691e087154d3200543650821c5534c801546912087154d3200552640821c5534c801546919087154d3200515a5b411c5534c80154692d047154d3200551a48411c5534c95545696c847154d3200545a53211c5534c951456960847154d3254551a58211c5534c801c46960847154d3200551640211c5534c80150d941ca7054d32006151da819c1534c80194472a067054d3200453a63725c1534c80150d941c87054d32006151d8815d5434c801a14642057550d32006511c8815d5434c801854862057550d3200651e08815d5434c801944822057550d3200651e48815d5434c801944922057550d3200651d88815d5434c801917422057550d3200651908815d5434c801915422057550d3200651508815d5434c80150d940857550d3200651204215d5434c80150d94c817550d3200651207205d5434c80114f985d77250d320055124575dc9434c801154916177050d321654325d8454d424c85960c966115350932005c12458454d424c80130d942055350932006c11048154d424c85ba0c8661543509322d7031d98550d424c80170491615435093200683e598550d424c801a0c966154350932006c1e458550d424c80130c916154350932006c12458550d424c801304916154350932004c36548150d424c801b04512054350932004c36578050d424c80150d940c975d853200463660325d3614c8019167420553d85320050764e855d3614c80181d7460f54d85322ee135c983d53614c8012549160f54d85320060d5d081553614c80150d940cb75585320049526153584614c8018578754d61185320049564c81550614c8016249155142185320068590d84144614c8012579460c51185320069190983144614c8012559850c51185320068961142144614c801a458350851185320078150d42144614c8014559314570185320054365032dd5604c80118e980cb74581320056165032dc5604c801585940c8715813200543650325d4604c80118d980c9741813200561650329c4604c801585940c9711813200570640325c4604c80183671a1262d8e510040fe61741d1639440181f7460f4158e510060bdd182d05639440181f7460c4058e510060bdd1821016394401837746044058e5100487660439d9439440160d9210e7650e510068510e819d9439440121e9810d7650e5100583648435d9439440105e980c57650e5
  | 3 => 0x5300685a1183c846154c01a158460f21185530049c640840846154c0162594a0821185530059164e820846154dcf645939c821185530059164e420846154c0705d93a1f40185530060d61c411006154c01a1583104401855300689608411006154c0186587084201855300689610210806154c01a4583084201855300598640210806154c014359418a71981530041d261645c66054c018347420564581532d44766374dcd6550c015169710f715954300585a5843dc56550c017059210f715954300447a60431c56550dcd81d8610c715954300543648431c56550c015169110c715954300545a5c431c56550c016169610c7159543005c1648431c56550c014569620c715954300515a58431c56550c015459210c715954300545a60431c56550c015149810c715954300545a58431c56550c01c169610c715954300705618431c56550c01d069210c715954300545648431c56550c01d059210c715954300541648431c56550c015159010c715954300545253321c56550c0145696cc0715954300545253301c56550c01455939c871595430051ce41721c56550c01470905c871595430050d653831c56550c0143694a0c715954300519a4a831c56550c0146592a0c715954300519a48431c56550c014659210c71595430051564e821c56550c014559320871595430051ca40821c56550c0147190208715954300705d0b321c56550c01436948c871595430050d652321c56550c01436940c87159543007114c8321c56550c0145793600715954300519e49801c56550c014649260071595430051564c801c56550c0146692200715954300519648801c56550c01434944c071595430041da60301c56550c01436940c0715954300519a48301c56550c01465920c0715954300615a0c71c856550c01855831c7215954300615a0c710856550c01855831c4215954300615e0c715c16550c01867821c5705954300619208715c16550c01856831c720595430061560c71c816550c010749161c20595430041d25d810816550c01077981c420595430041d660710816550c01856831c420595430061560c710816550c0111e9810d75d894300543648435d76250c01a144320565d89430068510c815956250c0150d9210d75d85430068510c815976150c018667220565d854300519245655cb6150c0118d9810d72d854300703594435cb6150c01a144361851d85430050b653535cb6150c01455931d761985430054364843dd56150c0111e9810d751854300543648435d46150c010779761851185430068510d861446150c0111e9810d75d814300543648435d76050c019144320575d814300615cc8815d76050c01a1443205659814300615dcc815956050c0150d9210d75181430068510c815946050c018667220565181430051364e655c8605
  | 4 => 0x5e8da3385c002ee000007c364a181084232f4202bdc00000009c93878144ce11848180571529a6a465a040028a6ca6ea8000002d61408600344f38007aa4a0032a0016a0000000182e3ac873800001f48d34e9b0000e8000000000302ae018000004400019e4733000000005a0000a00000000aaa610024e000000023a001eeb6b3ece90eec382c8cbe0034d00062f2800d69da590000000016baac695895800f480e0013d0031e9950100190b7a5b9f24677000afa41c3f7e00000bf80000329db9b021c5834821d30009453a6395a1f17ed1c00000b8e034671000000e682b34e48000005e00038a482aae814000004232f0004a518a600056ddaac000009cc68d983630826bd2e80032e50136001c0935887b19c100204f1f839e8ca232c94c90f1a670039ae887e059e200228ee2b300000d88e000000e597c00000000006b92ee70c0000008991c000003e3540000019242538a7ce6a8678007f29a03000000000008c00000002a9000006c400b1a82000002d98a74c300000000000763588ede82a8ff003220000028afc0030800000211b6000986a8002d0000002200278689b70000000000000003114800000f100000000002f06900097ca8d7a24ba800430007da68e9082968000008e000d800000393d83c15ebe51e002e6001123c8009ada60009a9640000000000003bab4001ccef8005c00000000c1000001fe844000021802000dd0004b16361178dc0d63e800c19d1eb2547282fd28b2a88241480000000d72148b066ca072a7846003cc00100000020300005c130180204c0a000030000402c0201c030100000400000000080000403008000040000000014030080702c080000200c0100401034040081206408004000240801022014000000301801038080000e0100400c0300c0002406014060380100803000010000001c070000500c040000100400014000000702005004020100d010030040000c0000406000000000000002010010080101802000020000000c040240300c0e00006000000040100000014050000201422008020140200003008000000002400018030100a000010180900002010000000000009014060200900c0100c02000020000000015000014369498871591530051564e621c56454c014369418871591530041de6164dc56254c0143594188715895300515259321c56254c01c44624c871589530050b648435d06154c0103f985d0741855301c1764e87d086154c01a4732a0b411855300691a0e82d046154c01a4583a0b411855300691a4e82d046154c01a4593a0b41185530069160d82d046154c0161593a1041185530058964a841046154dd1615939d041185530049564e821046154c0143597d08411855300495e4d801046154c01a1683a13211855300685cca84c846154c012559321321185
  | 5 => 0x99230c440a52bba1838ad4b129140000174e40cab92ec9d0000024000258499a394372ea326660b1490d412244320702719a00000000f64f80b00192da17d58ba04884c8e2bf97800c0c00b49c8221306fa5559e603428e71bae2b98cf02f2013405b096b0b1c9316b1b33627832838c6b881ac347a99b948d9a01e2529d8fc605949fa2a7cbb4a526f00800e9ad4002962f00077800001c20000098b1800000000000002e250002c0006e00000000c401e540a05c90a75305d580000074002207900000000db342002cc0008a0001c003bcb7ef88f8a4d80656b5ac75892818fe5b800002dc922c74aa4f0039e50800002dd0030a5bc0061ab0b2b98c4c00408068f00000000001320b00000000a433295c5f3a80000f20003d600000be9a8002c00fa43deb7cb40f4870000030b000ec0032400200b3a220d384eda6a0c4001aa703ece273684c530e3a35013c0000000ada16000542ebc80000055ab20021ae200011114a9843cec4e373c2eca2e049d2002bc00154bd9d00000000000418008e5a900000001e600128000000027a00000e1a1e8480010934ab800530000030c00143000de2e78c582cb2b2c47ebd4003000000075400daa98cc1041b800002e06e8760f29cc5a5c23c00a00f9415bcde1b4002d8cf080aad1a5db488220c45a6d00166
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x480098000001bb309c014045202e543cd0000e0517027602600a06ad3100632000160000c0dd60000e97b5c5b050c403a5467d5a172884ba66bcdb540548996e00f1988000001c4949c68f04002d2c001010a083850800100000c0080c1c28000080802200b01690624c871589530060c30ec8042100c2a980322184640210806154c01920c1b201084030aa600c036199210c715954300482d4c4c08638acaa1802505a2260431c56550c01288d0130218e2b2a8600d01a599210c715954300680d4cc908638acaa180340586648431c56550c0120b53129980e2b2a860094168894cc0715954300484b444a26038acaa1802a05a210c815976250c01502d108640acab128600a0569c4320565d854300540b4421902b2ec2a180300d98594435cb6150c0160250aca21ae5b0a8600a816884361851d854300540b4421b0c288c2a1802905a210c815d76050c01502d108640acb3028600a0569c43205651814300540b4421902b28c0a1802a11a010c815946050c01806cc2ca21ae43028600b012856510d721814300680acac9086b88c0a180341165640435c46050c012a0d0126108e2aa26400a4169072a067054d3200520b4849102baa8699002941a0248815d5434c801882ca10210aeaa1a6400c4165081c817550d320064090c48b0aa1a8499003204962458550d424c80118250b2bc0286a12640098168c91551421853200540b50a1a84288c299002a05a210e819d94394401412d14c940cecaa46200a0368a6460c715523100540b4532102baa871880220da4a6365589328c40130350d2caa2849946200a036886460c715513000540b4432102baa8698002244a16508654d3248001206d212ea9a6430a4000c05660431447650d1000580b44218a23b28688002c11a010c511d94344001602d2064288ec9922000b1068032144764c91000502b503a8c63246288002425a91d46418a3144001602d20ea318c518a20008836909854d624c810
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x2812098030005005b8a999210c7159543006005982856510d72d8543004807b76884361851d8543006005982856510d721814300600598688431447650d1000601198680431447650d10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4e
  | 8 => 0x138e
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x94e
  | 12 => 0x124b
  | 13 => 0x124c
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138c
  | 17 => 0x98c
  | 18 => 0x98e
  | 19 => 0x128c
  | 20 => 0x128e
  | 21 => 0x9cb
  | 22 => 0x9cd
  | 23 => 0x9ce
  | 24 => 0x5
  | 25 => 0x12cb
  | 26 => 0x12cd
  | 27 => 0x12ce
  | 28 => 0xb0c
  | 29 => 0xb0e
  | 30 => 0x140c
  | 31 => 0x140e
  | 32 => 0xb4b
  | 33 => 0xb4d
  | 34 => 0xb4e
  | 35 => 0x144b
  | 36 => 0x144d
  | 37 => 0x144e
  | 38 => 0x14cb
  | 39 => 0x14cc
  | 40 => 0xccd
  | 41 => 0xcce
  | 42 => 0xe8b
  | 43 => 0xe8e
  | 44 => 0xecb
  | 45 => 0xecd
  | 46 => 0x94056
  | 47 => 0x95396
  | 48 => 0x14c9
  | 49 => 0x2c9
  | 50 => 0xec9
  | 51 => 0x1a49
  | 52 => 0x138956
  | 53 => 0x98956
  | 54 => 0x9c956
  | 55 => 0xb0956
  | 56 => 0x1409
  | 57 => 0x140956
  | 58 => 0xb4956
  | 59 => 0x1449
  | 60 => 0x144956
  | 61 => 0xcc956
  | 62 => 0x209
  | 63 => 0xe8956
  | 64 => 0x249
  | 65 => 0x94d
  | 66 => 0x139256
  | 67 => 0x99396
  | 68 => 0x9d396
  | 69 => 0xb1396
  | 70 => 0x141396
  | 71 => 0xb5396
  | 72 => 0x145396
  | 73 => 0xcd396
  | 74 => 0xe9396
  | 75 => 0x2cb
  | 76 => 0xcc996
  | 77 => 0x1a4b
  | 78 => 0x168b
  | 79 => 0x98d
  | 80 => 0x1649
  | 81 => 0x134b
  | 82 => 0x14b
  | 83 => 0x141296
  | 84 => 0xa0c
  | 85 => 0x2cc
  | 86 => 0x14cd
  | 87 => 0xcc9d6
  | 88 => 0x150c
  | 89 => 0xe89d6
  | 90 => 0x104c
  | 91 => 0x1049
  | 92 => 0x104b
  | 93 => 0x1a8c
  | 94 => 0x180c
  | 95 => 0x130c
  | 96 => 0x1452d6
  | 97 => 0x1a89
  | 98 => 0x140b16
  | 99 => 0x24b
  | 100 => 0x154e
  | 101 => 0x16cb
  | 102 => 0xcd416
  | 103 => 0x144b56
  | 104 => 0xb8e
  | 105 => 0xb8c
  | 106 => 0x148e
  | 107 => 0x28c
  | 108 => 0x16ce
  | 109 => 0xd0e
  | 110 => 0x154c
  | 111 => 0x184c
  | 112 => 0x148c
  | 113 => 0xcd456
  | 114 => 0x20c
  | 115 => 0xe9456
  | 116 => 0x20e
  | 117 => 0x24e
  | 118 => 0xcb
  | 119 => 0xd0c
  | 120 => 0xd0cd6
  | 121 => 0xe8cd6
  | 122 => 0xcce96
  | 123 => 0xeccd5
  | 124 => 0x1a8b
  | 125 => 0x18cb
  | 126 => 0x188c
  | 127 => 0x178b
  | 128 => 0x160c
  | 129 => 0x10c
  | 130 => 0x16cd
  | 131 => 0x1a4d
  | 132 => 0x14c
  | 133 => 0xce
  | 134 => 0x198c
  | 135 => 0xa4c
  | 136 => 0x134c
  | 137 => 0x168e
  | 138 => 0x19cc
  | 139 => 0xbcc
  | 140 => 0xd4c
  | 141 => 0x15ce
  | 142 => 0x1a0c
  | 143 => 0x170e
  | 144 => 0x18ce
  | 145 => 0x194c
  | 146 => 0x178e
  | 147 => 0x74c
  | 148 => 0x5256
  | 149 => 0x2d394
  | 150 => 0x942d3
  | 151 => 0x289
  | 152 => 0x1489
  | 153 => 0x942d4
  | 154 => 0x2d393
  | 155 => 0x2c953
  | 156 => 0x24211
  | 157 => 0x2c954
  | 158 => 0x2cd
  | 159 => 0x2c955
  | 160 => 0x95416
  | 161 => 0x94216
  | 162 => 0x95456
  | 163 => 0x94256
  | 164 => 0x125396
  | 165 => 0x1382d3
  | 166 => 0x1382d4
  | 167 => 0x131054
  | 168 => 0x2d554
  | 169 => 0x2d6d3
  | 170 => 0x2c214
  | 171 => 0x2c253
  | 172 => 0x2d6d5
  | 173 => 0x2d854
  | 174 => 0x184e
  | 175 => 0x2c255
  | 176 => 0xb9054
  | 177 => 0x2c294
  | 178 => 0x2d4d4
  | 179 => 0x24b56
  | 180 => 0x202d4
  | 181 => 0x1542d4
  | 182 => 0x282d4
  | 183 => 0x1842d4
  | 184 => 0x21396
  | 185 => 0x155396
  | 186 => 0x124056
  | 187 => 0x138216
  | 188 => 0x138256
  | 189 => 0xcc256
  | 190 => 0xb0216
  | 191 => 0x28e
  | 192 => 0xb4256
  | 193 => 0x20256
  | 194 => 0x154256
  | 195 => 0x28256
  | 196 => 0x184256
  | 197 => 0xcd696
  | 198 => 0xe8d0cde
  | 199 => 0xd0cce9e
  | 200 => 0xcced5
  | 201 => 0xcd796
  | 202 => 0x104114
  | 203 => 0xced5
  | 204 => 0x105314
  | 205 => 0x12ced5
  | 206 => 0x104b94
  | 207 => 0xb4ed5
  | 208 => 0x105854
  | 209 => 0x16ced5
  | 210 => 0x104d14
  | 211 => 0x170ed5
  | 212 => 0x105894
  | 213 => 0x1a4ed5
  | 214 => 0xd2d6
  | 215 => 0x1692d6
  | 216 => 0x252d6
  | 217 => 0x1689d6
  | 218 => 0x1789d6
  | 219 => 0x24cd6
  | 220 => 0x24e96
  | 221 => 0x25456
  | 222 => 0x16d456
  | 223 => 0x179456
  | 224 => 0x16cb56
  | 225 => 0x144cd6
  | 226 => 0x144e96
  | 227 => 0x1715d6
  | 228 => 0x18d796
  | 229 => 0x178cd6
  | 230 => 0x58e96
  | 231 => 0x2024cde
  | 232 => 0x2824e9e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 1214
  | 6 => 4478
  | 5 => 3454
  | 4 => 493
  | 3 => 61
  | 2 => 6
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1376+((h/22+packedAt gbK8 (1222+(h % 22)*7) 7) % 80)*7) 7
  | 7 => packedAt gbK7 (50429+((h/501+packedAt gbK7 (44918+(h % 501)*11) 11) % 1805)*12) 12
  | 6 => packedAt gbK6 (237330+((h/1722+packedAt gbK6 (214944+(h % 1722)*13) 13) % 6820)*14) 14
  | 5 => packedAt gbK5 (220751+((h/1305+packedAt gbK5 (203786+(h % 1305)*13) 13) % 4701)*13) 13
  | 4 => packedAt gbK4 (36440+((h/193+packedAt gbK4 (34510+(h % 193)*10) 10) % 840)*10) 10
  | 3 => packedAt gbK3 (5102+((h/23+packedAt gbK3 (4941+(h % 23)*7) 7) % 91)*7) 7
  | 2 => packedAt gbK2 (558+((h/2+packedAt gbK2 (552+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe03fc07fc0fffff03ffffff44f3c7d11f1ff
  | 1 => 0x7ffc3ff83ff0780ffc1e0380bb4d39eeececc
  | 2 => 0xf83ffc0003fff800fffe003ffc38e3e30f0f0f
  | 3 => 0x3ffffffc000000ffffffc00fc0fc03f00ff0
  | 4 => 0x3fffffffffffff000000000fff0003fff000
  | 5 => 0xffc0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8400040044008a21002288a2001042c005055
  | 1 => 0x682c1d881d10506744141906194519466c6cc
  | 2 => 0xd0356c0422aad008aab40225cc28a2c30b0b0a
  | 3 => 0x4239b6ad68084010cf3997008ec0f803b00da0
  | 4 => 0x843e3b36733ce65c021004010f7e0003dda000
  | 5 => 0xe7102038403084600c2118060fffff78000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36723
namespace PEqualNP.Outside.L_meta_36723
open PEqualNP.Outside.L_meta_36723.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 14 := bs0_4_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
theorem alls1 : ∀ k ≤ 2, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 26 := bs2_3_0
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
theorem bs2_4_128 : Interval s2Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_4_64 : Interval s3Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 6 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 90 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 12 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 91 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
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
theorem bs5_4_736 : Interval s5Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 794 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352)))) (concat (concat (concat bs5_4_384 (concat bs5_4_416 bs5_4_448)) (concat bs5_4_480 (concat bs5_4_512 bs5_4_544))) (concat (concat bs5_4_576 (concat bs5_4_608 bs5_4_640)) (concat (concat bs5_4_672 bs5_4_704) (concat bs5_4_736 bs5_4_768)))))
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
theorem bs5_5_736 : Interval s5Atlas 5 736 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 741 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat bs5_5_96 (concat bs5_5_128 bs5_5_160))) (concat (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)) (concat bs5_5_288 (concat bs5_5_320 bs5_5_352)))) (concat (concat (concat bs5_5_384 (concat bs5_5_416 bs5_5_448)) (concat bs5_5_480 (concat bs5_5_512 bs5_5_544))) (concat (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)) (concat bs5_5_672 (concat bs5_5_704 bs5_5_736)))))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 6 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 61 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_480 : Interval gbAtlas 4 480 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 493 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 bgb_4_480))))
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
theorem bgb_5_3424 : Interval gbAtlas 5 3424 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3454 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832))))) (concat (concat (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)))) (concat (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696)))))) (concat (concat (concat (concat (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792)) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))) (concat (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)) (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112)))) (concat (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 bgb_5_2336))) (concat (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432)) (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560))))) (concat (concat (concat (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)) (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752))) (concat (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)) (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 bgb_5_2976)))) (concat (concat (concat bgb_5_3008 (concat bgb_5_3040 bgb_5_3072)) (concat (concat bgb_5_3104 bgb_5_3136) (concat bgb_5_3168 bgb_5_3200))) (concat (concat bgb_5_3232 (concat bgb_5_3264 bgb_5_3296)) (concat (concat bgb_5_3328 bgb_5_3360) (concat bgb_5_3392 bgb_5_3424)))))))
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
theorem bgb_6_4448 : Interval gbAtlas 6 4448 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4478 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))))) (concat (concat (concat (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344))) (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632))))) (concat (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)))) (concat (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048)) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))))))) (concat (concat (concat (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))) (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))))) (concat (concat (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880)) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)))) (concat (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)) (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)))))) (concat (concat (concat (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456)) (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584))) (concat (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 bgb_6_3712)) (concat (concat bgb_6_3744 bgb_6_3776) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872))))) (concat (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)) (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)))) (concat (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 bgb_6_4288)) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448))))))))
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
theorem bgb_7_1184 : Interval gbAtlas 7 1184 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1214 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 (concat bgb_7_384 bgb_7_416))) (concat (concat bgb_7_448 bgb_7_480) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))))) (concat (concat (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 (concat bgb_7_832 bgb_7_864)))) (concat (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024))) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 47 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0eeeaeae8eeeaeaa0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 4008372896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36723.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.or,[0,2]⟩,⟨.or,[4,5]⟩,⟨.or,[2,4]⟩,⟨.and,[6,9]⟩,⟨.and,[7,8]⟩,⟨.or,[10,11]⟩,⟨.or,[3,10]⟩,⟨.and,[0,13]⟩,⟨.and,[1,12]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008372896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4008372896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36723

open PEqualNP.Outside.L_meta_36723 in
theorem PEqualNP.Outside.L_meta_36723 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008372896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4008372896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
