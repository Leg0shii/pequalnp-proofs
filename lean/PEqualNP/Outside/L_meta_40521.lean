import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40521.Model
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


end PEqualNP.Outside.L_meta_40521.Model

namespace PEqualNP.Outside.L_meta_40521
open PEqualNP.Outside.L_meta_40521.Model
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

def SBf (j : Nat) : Nat := [7, 6, 7, 6, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40521

namespace PEqualNP.Outside.L_meta_40521
open PEqualNP.Outside.L_meta_40521.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x10cc0010c000104a0c97810c50800011800c8fc41fd40fe43fc31fd10fd32fc32fe32fd42fc10fe42fe10fd21fd41fc21ff42bc40bd43fe30fe40ff31fc30fc42fe20fe41ff10fd20ff43fe21ff32fe31be40ff20fd31bf43ff21ff40fc43ff30fd30fc20fd43ff41fc40
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1003800716300081200d002000180005c1912428a85000850000000044000000000400444d50c80200089004c000020020e013d53102bea6884f553329f2a0615e53d067ea890dd946329eaa0637b504877080186750c31da28a873e50d0eb8a6906750e31cf29881e521086bea6904fd5130af2988178504867aa9986e14143ba28a413d54c827ca818cfd51109e2a2211d531027aa8185b54a31b7a92613f54482dca518cf550329f2a6413f548c27ca9995b94810ba28a876c52442bca7a14f55243bc2828775518cb5ea4a1db54810b6292613c54482baa7a14f95330cea1a619d438ca7aa998edd45439e2a24377514833ea6a1dd94420afa9a437551082eea2a1eb14943ba28a615d53d0678a9185bd4943bda82879d43cc376a0a1e754c409f2a0873e54cc6b8a690e750c32aea98813d539027ca0205714d109f28481ba501027ca9884f141439f2a0653d54c437081985dd4530b7a9221385050e78a8985b14943
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa15880014430100032f2b5214143a6181430c6986050c32a6181438ca986050e31c3189531021c6550d30c550c514c2996310330cc1445050f0f6254c40b818121087146154c40ccd445050f0d4314930c91485150f0d4394a31c550e518cb176154c40ca1485050e1d63953108758e54c83186054c40a618143cc2396510030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x400005811886154c40a10e0a1ca518d107050e518cb04310c0a9881841846054c40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s0K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/58+packedAt s0K4 (2457+(h % 58)*7) 7) % 91)
  | 3 => 2*((h/15+packedAt s0K3 (950+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s0K2 (245+(h % 8)*3) 3) % 5)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffffc07ffff03fffffffff01ffe3ffe3f
  | 2 => 0x3fff01fffff80ffffc0fff01ffffe07fcf1fc7
  | 3 => 0xc07ffe03fffff01ffff03ffe03ffff81f3e3f8
  | 4 => 0xff800003ffffffffffffc00003fffffffc03ff
  | 5 => 0xfffffffc0000001ffffffffffc000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x429114288471224500b2cb4a94b08aaa156e1b
  | 2 => 0x13224c514890e48b2c0555295956a24ccb16c5
  | 3 => 0xb244289a512241d3555026ac526ad30963a368
  | 4 => 0x2470b163a244891c9a6980c1838d1c71bc01b6
  | 5 => 0x3878c183c3870e1ee38e38f1e00e1861fed800
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40521
namespace PEqualNP.Outside.L_meta_40521
open PEqualNP.Outside.L_meta_40521.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3000027bc40bd41de32ef32be40ec32cc32bf41dc32
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x30c0000c6aa0658c32507186420630cb419aa88818e540ca9ca519630ca40
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x9c10c9511020d650cb418359432102856195032
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
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
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt s1K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/9+packedAt s1K3 (216+(h % 9)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s1K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 2 => 0x81fc0fff83ffffff0783c1f03ff87fffd24e3f
  | 3 => 0xfe000ffffc0fc1fff803fe003fff8781e38fcc
  | 4 => 0xffffff001fffffc00003ffff801fc0ff0
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8828002300208000188442118a0088940490d5
  | 2 => 0x24519644194530cb032191a214c85568d2462a
  | 3 => 0x149aaa8928ea13556842f484a755060d638b4c
  | 4 => 0x59634d125283a5a6b5e8210939a66031bc0db0
  | 5 => 0x61838e1c630c39f8c67339ce01c44441fb6000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40521
namespace PEqualNP.Outside.L_meta_40521
open PEqualNP.Outside.L_meta_40521.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x30020200611814d00b048340880042200ff43dd43ff10de43fe30ff31ff42fc32de32ff20fe40fd42fe42fe20fd30fe21fe43fd40fc41fc30fc21fd41ff21fd32fc43f421fd43fd21fc10fc31dc32fc40fd31ff40fd10f721fe32fc20fe31fe10fe41ff41fc42ff32fd20ff30
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x307000000000100060205b0106052020000000020808a0000206000000200100070000380460000028000090030000000c00000080080004004000c0002c000030b5c53442bca419790c821aea9e813c544827ea8905d54440ae29a859e540cadea48857d4d21af294877551d0a78a8885754f42af298815e5310baa8610cf553309eaa0655d548cadaa5a0dd54620f3990435d53042baa921dd94821bb28861e421082e8a29057d5032af294655f548caf6a0a17394832bba8a655c53482f0a0a1710c821aea9883d6430873a86205dd4542af29c435e53d07a86590e755032b7a92635d53886bea6a15754c42af29e857651883ca8410d794e20afa9a219d43d0bac6410dd14532aeaa0657651ccbac6590d714943b6292639d43902dca4205d94440ae29a437751482baa7104755032eaa1e433e54cc2eca310db54840aea9e833f54442dca5a0db14910af29e815e53042eca3a15d14542ea19043e652086baa6205d54430af298835e5310ebea690730c821cea1a853e540cb3ea8a1f908620e619443e642086eaa3997590f21
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x3381220100000292828d640c821a559032086646254430b118d42087194314142c350d52102c7640c821e199032086c5640c821b81814208785435082187596540ca95640cb21e159032086a5640c8218759253883465308620a159032086c6628c821a359032886c46250c21
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x8000005057494c2188340a18c0a1043215da640c821
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => 2*((h/22+packedAt s2K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/75+packedAt s2K4 (2673+(h % 75)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s2K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/15+packedAt s2K2 (147+(h % 15)*2) 2) % 3)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe07fffffe03fff81fffff07ffffe07fcf8fe3f
  | 1 => 0xff80fe07ffc0fffe0f81ff87c07ff83f6733c7
  | 3 => 0xffff0007fffffffff001fff8007fffff87c3ff
  | 4 => 0x7ffff03fffffe0000007fffc3f803f8
  | 5 => 0xfffffff8000003ffffffffffff800003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x230a144023820880318a30094716426428561b
  | 1 => 0x452628ca448e519606a8d485892aca296332c5
  | 3 => 0x8a144d148914a22ad0416950124d149285c16e
  | 4 => 0x1c58b1e712283bcd6b6c0c452471e723f803b0
  | 5 => 0x1060c1861c30c3718c718e6638018403d6a800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaee008800eeaaeeaaee008800eeaaeeaaee008800eeaaeeaaee008800eeaaeeaaee008800eeaaeeaaee008800eeaaeeaaee008800eeaaeeaaee008800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40521
namespace PEqualNP.Outside.L_meta_40521
open PEqualNP.Outside.L_meta_40521.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x24090031000f421f710de32dd30de31dc31f510de43dc32f721df30dd43
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x208eaa0651d54cc2a8a2a1d914910
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
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s3K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s3K3 (108+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fffffc0fffff03ffff83ffffc0fffe7c7e3f
  | 1 => 0xf80fc0fff03f07fc3e07fc3e07ff0781b3b3cc
  | 2 => 0xfff000ffffffffffc007ffc007ffffffc3c3ff
  | 4 => 0xffffc007fffff8000007fff801fc03f0
  | 5 => 0xffffff00000007fffffffffff8000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x10a10804608221004628804a31484c94141615
  | 1 => 0x32629948a3942b2c1aa3a42c52d9450cb1b2cc
  | 2 => 0x4144a2910528845581054a8084a2926942c16a
  | 4 => 0xe58b3ce24a0eb79aedb06229273ce431fc03b0
  | 5 => 0x860c30c38c30c6e331c67331c0308041eb6800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40521
namespace PEqualNP.Outside.L_meta_40521
open PEqualNP.Outside.L_meta_40521.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x5c0003a8000110000100659f0400000400082536420c2040500ff30fe42fe40fc40fe20fd30df32fe10ff43fe21fc20de31fd40fd41dd32ff40fd21fd20fc10fc30ff31ff42fc41dc31fc31fc21fd10ff32fc42fe30fd43fd42fe32fe43fe41fd32fc32fe31ff20fd31ff21fc43ff10ff41
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xacd0268f0256ec3040e0c9000a14c0c006408604022831e5f9aa418d794431ea18e215c53886baa7195b548409eaa041755190abca7905b14910afa9a815e53102baa610d754831af298655d53c82daa418dbd4940ae29a215c53506b8a2994fd5110aea98856d5210eeea2a05794c20bb288415e53087aca218d754e42af29c21cf524cabaa7085794e42e699441d431c86bca3994f95020bba8a875e518c7a88218d7d4d10ba28a815d53d079a6590dd54630b7290636d52d06eca318750c510ea188435f53887aea2995794f41b62928175511039ca418dbd4910e699041cd32486daa5985514532aea9e4374514cadca421f3909329f2a6435e53c8678a8885b94840b72966177514cba8a2995d544209eaa6435d53082b8a6a07350932eba08636e52d06eca3215d14543ae29a435e5310a9aa418dd94440aea94635f53486bea6a0d754c40
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x4210000050cc0008000800000001000000024d6294e10935885350714540c510d154b410c6c4614c8209559431086c56190932c355132c87455210431d114831442c4614ca20d14c951082c5620c721951855310b464214532b118532c86c5620c7109319532486c5620c510d1508514cb446154831b198b410c716540c721c355132082546154f20
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x410080302aa0c299041115d8520c510c0aa830a6590e045458831443032a2c418e4311dd952d0431
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/35+packedAt s4K5 (704+(h % 35)*6) 6) % 44)
  | 4 => 2*((h/30+packedAt s4K4 (2430+(h % 30)*7) 7) % 90)
  | 3 => 2*((h/29+packedAt s4K3 (950+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s4K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf83fffffffffff03fe0ff07ffffffffc8c7fff
  | 1 => 0xffc07e1f03ff83fc3ff0ff8703e0ff0373b27c
  | 2 => 0xffff801ffc1fffffc000fff803ff0fff83c38f
  | 3 => 0x1fffe003ffffff000003fff003fc03f0
  | 5 => 0xffffffe0000003fffffffffffc000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8850801080100004601100918a111280414b5
  | 1 => 0x51931422394a152c1a5072822968aa1931b25c
  | 2 => 0x620a255450d453558148ab50425a8cd382c30a
  | 3 => 0x472c5998a2875b9aed6a0a40939cc863dc03e0
  | 5 => 0x84306110c31862e3318ccc64e0100082eb6800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40521
namespace PEqualNP.Outside.L_meta_40521
open PEqualNP.Outside.L_meta_40521.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc437d548c2fca21857d4d40efa1c61ef21087ee4290df94a10df2a0417e53d07f680a05f95043dea12817d538cbf661907dcc531bf28683bf40903ea83885f14141be2a0617d5190afca5195f54043bf290617f53082fea610df14f10fda04817e500c6f8a8985f94732bf28e8774515037aa8087794e42efa1861ef328cbea20085fd4540bea8e857e548cafaa6086f90140be29821df328cafca620774cb30ae29a837e50842f8a2a05f95330bf28487f910042fea9887b4c921bf29841bd4210afca7105f95041bfa92813c544c6f8a098fd50510ee21a65de53082fca1215f14520bea80657e510cafca520df14d10fd902416e520c6f8a898df54b43efa18637e51906fca5a05f14910df2a021f75150ef8a690dfd4520bf2a2417d54906f8a610df14930fc980617c5050aeaa2205f94d20fa20e637d51902faa110f754e42f7a12857e53486fca518dd94642bfa8263f8504caf8a4a1dfd5331f7a10417d5090ff660985f54a30fb28c61fb20882fca621fb4c832beaa6217f548cafaa118dd54630bea8e417d54c87ee83085fd5231ef21887ee20482fca6215f54343bf2a6437e52107dc6590f7d0d32ee99065f4514caeca2206f10f40bf296617d52d03e883087d14543bfa9c437d53086faa3985fd4810fd080217c5350b7a8621dfd5010de21885df32cc6faa4205f54232bf28c857d52906fca3a06f10d40de2a2657651082faa3187794c21fc18041df318c7f460185f94842be29c21f741cc7da84215f95221bea88817e5410bea6218fd4c521be2a6417d52c437e82a077cc930be2a2437c54443e88310fdd0621bea88857e51102faa221df94e40f690843f551083eaa2205fd5021be29e417f54442fca020fecc020fba8a81fb308c2faa12157d4d41bea9e857e5010efaa8907d94440bfa94217e51882faa910df94332beaa2217e51082fca310ef10e41af298437d53d02f8a8995fd5221bea8663bf41d02f8a2985f14132bf298657e54c82b8a6a05fd4d10ef99065f9200827ca9185f54e21fa28a817e50906faa921df54a10bea9c217e548c2fca010df94d10df212853d54083ec8220dfd4f21be28a857e540cbbe6498fd54432dea0e817c52043f2a020df54830bba8a657d540837aa9186f50540beaa243ef21887bea6a05e94041b6292817d5290efca521ded4132fba0c837e54cc6fca2085f54f21be2a4437e50d0ebca7215f94331bea96837f504cb7c87a05fd4f20bea9e217f505067aa8085f94f10beaa6617f52442fea8197ec4110fd100417f54c82faa5985fd4941bf2a0637e52d0ef8a790efd0641ef18a63ef42882fea2995f55010bea8e65ef4290afca2215f54d20ef99661f621086fca810df946439faa2657e510c6fea090fdd0431be2a6617e52903be8721df54620bea9a437c52c437c82a0d754e42
  | 1 => 0xc548c2fca3987710f32fba0a437f53503ee21085f54643be2a6437f54cc2fca118df15031bfa92617f53506fea8995f94221dfa18877e520cafea2985f14d41bf2a0217d5310adaa418df94421fa208637e50c86fca418dd14532bea80857d5490be88290df94240bf2a261ef324cabaa6107ec4210fb10e217c548cb78872177d0f32df21a87f55190afca4207710e31beaa6637e500cafca4107d54630bc282657e544c7ee63886f90d40dfa10857e52086fea990fb94831fb082217e54882fca0215f94720be2a2417d53c82fca7a05f94b41bea9c837d52cc6f8a9885f55220bf280213e54082bca6107d8c621de218833f544c7ee62885fd4142beaa0617c54042faa1a0fd94432df218857e54083ee6318dfd4b10bea9e837f5250feca2107dd0410bf2a4637e5110efca620f714d40bfaa2637d50ccbbe8718df94e10bf286857d50c86f8a5086f90e41b7a92813c544cafaa421dfd5020bfa8a857c548c7baa610df54a31beaa6657d50d0bbc64995f55031bea9c61ee320cbec42885f54c41fa208217e53886fca618ef50441be292837950107ee82a0fd50441bea80837f524c7d8a4a0778c130be292637c514cafca488774cb31be2a0417f5350af8a7107b4cb21fa188437e54103dc4290df14940be28287f641c43ee6390dfd5120beaa421f521086fca610efd0441ee98061ef208837ca9185f94631bfaa4417d531037aa810774c431bf28465ec42082faa9205f95121be29a81bf40102faa2185f54e42bf29485f721886fca99977cc431bb28c61f940442eaa2195fd4f10eea18877e50102f8a9105f95310fb28c857d500c6fca8885fd4c10be298417e528c2faa3a05fd4e10be2a0437e53d0abaa610fe50040ee29a837c540cafaa4087e90110f7210857e53c87ec82885f94f20fa18e437f53883b88618fd48710be28a87bd40102faa120fd0c710bf284417c54cc6faa898df94441beaa0657c54842fea690df54e31bea88417e5390afca0185f94630bfaa421fa40842faa9195f54432dfaa265dd324c6f8a9996fd0a42fd20081bf544c6faa7105f55130bf28e857e508c37e8721fb54831fca0421775150efca8185f54021bea8c657e5210efca598df95132be28243f631487ba64985d54420fb188637f5050efca9085fd5332bfa9a41df308c37c87215f94810bea9221755190afaa6885f94c30efa1a87f521442faa9907d0c510bea9c81bd42d02e8a2a1dfd5130beaa265df300c2f8a6907dd4532bba8a81dd53083b887185f94640bea944376510cafea9185fd5031beaa4637f5150efaa5107ed4132be29c43ed20083ee20086f90c41fd280837e5390efca6085f94632f7a9281dc430c2faa6105f54841bfaa0617e50082fca5885f55021fc18641df53507d885105f54a40bf29c837f544867aa9185f54831fa98
  | 2 => 0x11fd00001010070088805c0200000004060000000402000270780100814000050143b040010000201c0000006000080700100c00050770000e1ac0000006004000b4022280700812004360001c02001008560040000c090000f008612945800c06008bf01401014010042406c0039c320080c01c00018000e40200c010180000009010011b001000690dc0001000000051d0071c402010010104b4202003c00004002905c0540105c0600804028532484d00001000460080002c00000024143c0080008002050000381a26405024120a402564060140f0740003c0100008034010100c00c03064030080006c0402c1d00801040000140205c4107c050000200022018011c03b018e1090010002f0000205c041f0030140001c6e00c010841a250000683001007000010083109c85148010145903c020140c004ed07400000840100003c6d02003000390680002405bea8c21bc544c77e85a07dcc421f7900413e54042faa3a1fb8c921dfa12817
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1100423c6454f20b51854310e7661d5032bc58041cc71c6454c21d594e5190a766194332c7d4c435023c6454c219d997414874d5348421d5d0c5150e5c6355110ecd0540842776155131d594d5190a756114930d54c9510cad463504419b98b54cc2776544010ce505501067661d52309b988530867761551209d594410423d6595020a718d411067765484219d58652d0f7160145409798f54082776155110b9588310876532544329d986544ca3d64148108f99353886756114142c7d8d548c37051d4132cd551518c31d5494c209798e52d06776155332bc580410437351141329d58652d027561d53209758c520425d6594c209e580540873554c40109ed81544866e6214f10ce90d501074c524c9308fd91534435453d0541ad191314865d63d53219d9845050a7a60152218f99052042f06048510ad191318877351d413297d8d544425f63549109ed95401025d63d5020cd150514ca6d62150309d594410c74d52cc4319758e52d065c63549108f99250cc7365494630c758f544cb3461550109798f54c874c43548319dd95310c63d64d4c208f59053082756114c209e983538873843540419dd85540c2766194b439d98753082f16010521d654f300825d6314b109758f54842756195132b618132cc26f65508429e980540ca3e6414a109d984540ca5f63552219e580540cb944310431d3d0d520c676658c5219b189544c27661d50209d9875388275611523097d95320ca746154f40cb10c525025e63d5021cd951510825e6314b10d6181530825e6315020bc1854084355530c4219d987548ca5d631491097d8d540427661d4c109d984530827761551308f990530433454d4532dc546401033454cc5319d9865090e5e65d0d329d59731087584314132cd10c515033443946429e58353886796015031cd547401027661148108f99353c87b141501109d98754cc23e6494030cd147415031c5390541ce153504ca7a6015031d314f525035b4314132b918532c874f53d4940d594e510827a6095132bc58041842d46350710cd551510823d6494332d9549310c63e65151329d587540ca746155120d554c31c427661d5320ae98243502756115032d3d4c5250275611522097596530865e63d53109dd8553482f160104318fd91524425d6314a109bd95320ca5d63d5310d510c514cb6452145409798f540ca6d62150319ed95100423d6494331d5d4c515023e64d4c109e582544cae5620c7219d98652d03355444010d5d4f515033551500409e181544863f6550c43d554d510827661150109798c5244279601523197d8d548825c63552209d98454882746550510f14c9314863e64d4c209b19532486e5620c5109798c530826d6214c10d554d21086796584010c7d91530874c5314940cb5534208279650c020ced50504cb1c544c931
  | 1 => 0x853004500214838b031003bc480d0102408070200424021d8005c152d8a00a0c4d824608b0f052fe001c8050a087f0042205130380032308080a260e80476210a8004e000c0000c090400000312d0100005d9d48515031d5410e30a7191310c67865501109d984530875453d4540d9d4b515035553884218f993538831f63550109e181544ca3e64943329d587548cb573254432ad1854310e5f63551218f191534875453145409bd95210871d5310e429ed95200826f6254d109b98b540c7555394642cd90c5150e6d62d5330d554d5190a766115020cb90c525032c62550208f593530427561150209ed815348674654c5218f59353c876452d45409b988540c2766114f208f191534425f63551209dd85548823d64141219d1855310a5e6394b40c7951530833854141328f596540423f6454c21cd552518c27661149309758e52d033643145408f59353886746155030bc580418875743145329d587538825e6314c219b98b54c4365521043197d8d544c25e6314a10ce552100427960152218f992544c7364394642ae181425023d6414a109d58453c825e63d53209b58b54c425e63d52109bd9520082746154f20c718d540427661d50219d587548c2756194332c7551530823d64d4e208f593520423e64951329ed95300c23e64d4810ad191310c675650c4219dd95411073b54d41328f990504873554944208f993538429c63507408f191534823f6454f10d5185530873754145329dd8553c836552d04319b58b540c65d6510c319d584540c23f6550441cd550410423c6454f10cdd53514ca5c63551208f191524426f62551109718d540427561d5330d98c9510cb3654944209d185544ca5f654c4318f593538423f6454d218f990530827a60150218f592500c3365454630ced05501077141540419ed81544ca7465485108f990540425c63551219d18553482786054d219b189534423f65508429d5865090e5f654c0309e980540423e65151319dd85544ca3f6454f20b518532cc7646154831b958831c433554106219d185548835653544209d597410425f6355131dc545401027a60152319718d548866f6255130b398b434ca5d63d5320d554f310873554d04109d587530826d6214f109d185544c34d524c4318fd9540102d463505109798c520432c52d09409dd8553487574394630d354f210867461553329798c540867b6054d209dd8553d02776154c429758c540867561d5020d954a310c69c6350540d554e510826d65108209b988530425f6550c4397594430c27665cc5109b189544423e64150209d984540c26e6215031dc905501063d6414c108fd9153483c532cc721c7952530831c548c531d510e518c36452485109d984548c26f6255120dc144504cb1c54cc9319758f540865d63150209d996414431f5410d32ce55
  | 2 => 0x8e01838120406970000c18a0830352aa08104727800140a418080805000000687010145e4100020de010005c52611000c1e101a804041901004009f0f0000e20078047806028003e35008056e0704804081
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x3044088000288000804600020300040007985496010431d2086b008218e31545804188706322a498863461cd4154041a8ae229264986455358831c430a320c2a9843641cd415011098ae3316869951473550418868a3a2a618e21541cd4154041c48c8a926218cb1719824350322a9ac418843451d1530c421962e230284a0684644c93148718aa2c020821451cd5410410a8ae629242884b174181214430a318c2aa021c110d5210431
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x200600a048454d620c421a10835516010621e00435496010431a10835516010410a048454d620c710
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/268+packedAt s5K5 (16632+(h % 268)*10) 10) % 616)
  | 4 => 2*((h/145+packedAt s5K4 (15732+(h % 145)*9) 9) % 414)
  | 3 => 2*((h/29+packedAt s5K3 (1225+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s5K2 (300+(h % 8)*3) 3) % 5)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffc0fffffffffe07c3f07fc1fffffff8478fff
  | 1 => 0x7ff01f01fff07f803ff87fe1f0ffc0478f27c
  | 2 => 0x7ffffffe07ffffffc0007fffff07fff80ff8f
  | 3 => 0xf80001ffff8007fffffff8001fff8007ff03f0
  | 4 => 0xfffffe00000007ffffffffffe0000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x105215124412840140b849612518c5504384b5
  | 1 => 0xb2864d21c924ae58115ac2eb0b8d683458b25c
  | 2 => 0x43082844834822aa9402048c52a432a5805b0a
  | 3 => 0x622cb089120e3334da6310081cc620c6ad03e0
  | 4 => 0x8430c10e1c70c5c7238c67318008430376ec00
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0fee0a8a0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40521
namespace PEqualNP.Outside.L_meta_40521
open PEqualNP.Outside.L_meta_40521.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa282140040000089040027fd5001fd3100ff14005fe5200ff04001fd21007f88405ff21007f4c009ff53017fc8003fc40017f90801fe41017f8c805fc4200ff94009fe53017f08401fe43027f54805fc5201ff10409fd5100ff08007ff41027f14c03fe2000ff90003fc30007fcc409ff51007f50801fd41007fcc807fc43007f44009fd50007fc4007fc5400ff84009fe51007f8c401fd4001ffd0c01fd20027fd4809fc51027fd4001fd4301ffd0009fd5401ffd0801fc3101ff95005fc32007f4c801ff30027f54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x828435ffd4532017e84290816fc648840bfb20e202aff14b3101ff882a1827fd6190c71fe28e6409ffccb3101fbe8721817fe21c4059fea8e6209ff8c243087fe8298026fc64cc839ffa844202ff5093202ffcc720817fc3188413df21a860bff14b1000dfcc7980bfff6550413ff29c8609fd4c431067fe878800afe620c40bff18e2009ff1933202ffe4218803fd414842dffa9a8000ff589311a7f88299017fc658840bfe28a6205ff04121025f8ca8807bfc520c413fe1866403ffd5140017dc64908bbfe525040bff1886203ffd054104ffe861880fbf405080bfe0846205ff4871000ffc8090003fe4344017ff2162009ff9833201ff88121812fe6550475fe28a8415ff9894001fb886a180bff4248005fe2926405ff0c521005fac418806fc6048435fe2844205fec411004ffc65218ebfe6550865fea848200bfd91300c7f886908bbfe6250401feb128005ff0871002fbe62188a3ff508c43dff2106202bf9894002ff84218807fd50cc003fe9862034f710d32007fe6290827ff314c4297eb2e6004bf99431017ee4310817fd418c40bfe328620ebfd952001ff884a0823ff5444007fa20a8203ffd0d4304ff86098827fc314c001fe31a4003ff1094302df8c51880afe62c40017eb226219ffd412104ffacb2180bfe524c811ffa9a2009ff18732197f8a720826fe6388413feb2e6009ff54f3000ffc40a0002fd608842ffe2824201ff8c140007fac48803bfe6548007feaa48605ff5964100778c899017ff62c4003ffa826000ff9853204ff66098003fe4348059ffa8e6205ff50621017ee4290816fc65c40017eb246200ff50b311cff860a103bff5348071fea866400bfd814201df8c898816fc6388407ff2a48600ffd8d10177f8a4a080ffe42504017fb1a4003bf991300dff8871080fff435040bfe20e6200ff50e210b7fccaa0003fe63440037f3028605ff042211effecaa183bff544802dff29a8009ff54f3202ffca388027ff64cc407ffa128002ff1093204ff8a79800bdc32cc803ff2066000bf580311fffe4121802ff6050c01dea0a8000ff50e3102fec4388017ff21c4007ff2128625ff1423104ff887188f3fc5250c3fffa006201ff843101a7fe8699003ff634840bff2886217ff98121007fac29000bfd3288403fe2028001ff88110017f84299003fd6448455ff2966201ffd03100b7fea4a000efe640c401fea0a6023ff191310b7faa4a000afe628c40bff080623dff59543017fa649080bbc4250807de21a8000ff50d21127faa098812fe658c401fe9946200bfd894100ff8a098027fd6090c0b7fb1e2009ff14f321e7f842a1817fe6488401ffb028201ff5011004ffec12185bfc6550019fe2a62008bfd95101d7faa6a1016ff658c413fe32e6000ff59120127faa69880afc6250c0bff28a8209ff10d30
  | 1 => 0x7ed620c413ff32c8609ff8cb31017f84099026fc65cc801ff18a603abfd954202ffc8388026ff65cc413fe32e6410ffd0d301adfeca9900efe644c80bfe10c620eff14520007fe629003ffe424c0057e312202affc8331007fa83980effc2050c05ff2124205ff4c71004dfcc72180afd62cc801fe30a8605ff58a4102ffec1208effe5050c016fb1a8205ffd822100fe82088017fe410c449ffb2a6205ff0852102ffec910807fc50cc0037f30e2002ff0c932005fec690817fd310c403fe0866003ff50941007fa4298027fc43cc003fe1824003bf59241005fec888017ee620c413fea1e6005ff1071015ffca99883ffc214c00b7e32c8203efd0243015fcc598002fd644847bfe32a8600ff50b1004df8c6a0817fe1088401ff9928202bf98b3104ffcc598017ff51c400bff28c422fff5454102ff8c018807dc304c003fea822024ffd413102ff8c5880cbff5090445ff3126216ff14d401b7f8a199017fe518c411fe29a2005ffd443116ffc20a0827fd32cc013ff21a6200ff5083101dfac921803bf644c8017eb262004bf9971002ff82120816fc6150c0bff90c4227ffd0231007fac6a1017fc410c4017fb0a8609ff10f32025f8caa0823fd5344061fe1848204bf1953100ffaa090027fd43cc80bff28a4203bf1911001ffea92183bff65480137f31c823eff8824302ffc21188dbfc10cc87bfea8a8600ff50531005fac198806fe6090c75ffa828400ffd8943007fac898017ff218c413feb266005ff08541005fac199017f42188405ff9926400bf58a4300ffe8098007de30cc0037f302423affd954210ff8a098803fd604c807fea1a8402ffc85210bffc20908d7fd514c803ff202801bff15221025fcca90806fc60cc8057e3128200fdcc51002ffc82a080bee52480097f32e6205ff1964113ff8a91880efe648840bffa0c6211ff94530047feca88002fd64cc00bffa0c4229ff0833105ffca588027dc430c47bff32a8600bfd9121187f8a12083fff214c073fe282840eff54d2002dfecb88003fe6350403ff082601bffd022102ffcc788027fc434c40b7fb2c4229ff9433101ff8872087bfe520c4097f32a8400ff50d31057eaa388002fd6290431fe2a24203ff50e4100dfcc118847ff654c00bfe3246205ff0413104ffe63980bfff5150449fe32a6232bf596410a7f8a398027fd60cc807dfa0a8000ff4ca41077f8a690002dc6350423eea9a6009ff0cb31075faca90067fd6548401fe9926203fed0140005fec890003fd615080bfe20a8200bfd913202dfec988043fc544c001ffb1a4001ff901100c7fe809082ffc42c407bffa8a8609bf1973104dfcc61880ffe4350007fe21a8418ffd052104fbca79800afe62440017eb222009ff1833104ffec5988ebfc5350803fe1866005ff907310f7f88418806fe60cc873fe0
  | 2 => 0x4202ff8c418827ff53cc459ffaa66203ffd0d420fffca818827bc4350c0bfa20c8205ff08641067fca988017ff518c407ffa14863cff98943005fec4a0003fe414c045fe312623bff1814317ffca6a08cffe304c80bfeb046238ff947321effea4a1806ff614400bfe20c6213ff15330015f8c59800aff6148405ff2944201ff141100077a84a000bff21cc80ffe21a2009ffd83310cffea290827fe6190c6dff0866413ffd0730007fa8688077fc200c40bfe3046204bf19532007fa8498027fe534c807feaa28200ff98540017fea499007fc104400bffb006205ff1052103ff8c888027fe5350c53ff1066202ff08542007fa64880bbfe3250481fea848600fd0c51000ffe8198017fc63c400bff28c8209ff9933108ffea298006fc6090c0bffb28623cff8c94304f7e8721826fc635080bfeb2c6201bfd814002df8c9188cffc404c801fea0a4010ff105301ff7c85218dffc54cc853fe2066227f710e3104dfecb2180bfc424841bfe21a4040ff54a4302ffaa218807fc20c4001ffb222000ff9854217ffacaa080bfe324c803f61024003ff55143015f8c59889bfe528c40bfeb146205ff9453101dfec2a080bde32cc801fea1a402effc8141117fe4298803fd615002dfe28a8001ff94310177f864a0807fc5048003fe0824006ff98910007fe62a0017fe1090443ff0826202ff949211bffe83990d3df434c873fe3028405bf19031005fec099003ff635040bff90c8205ff99310017fa64900afff42cc4337eb2a4235ff5513201ffca8a0877fe500c4017bb0a6401ffcc31004ffc619880efe644c403fe1828002ff10a2102ffac788017ff640c40bffb2c8209ff14e4305ff86588027fc320c475ff28a8402fb8cb32007fa8699003fd614c079ff9028634ff9513207ffca498003ff6448007fe2a48223ff1513102ffc6290803dd324c013fe18e6005ffd8a31007fcc6908e7fe1050859fea966216bfd954016ff8c0a080fff4090407fe2a2842cffd4b31125feca9880bfc5288413ff29e6201bfd8110207fea521806fe605040bfe28a2000ffcc5100dffe871085bfd5350005ff9026400ff5911019ffca09908fff414c4017eb226405ff8c62111ffe809880fef4250801ff9962001ffd433002ffec710816fe618c4137fb2e6435ff5953202df8c299016fc658840bffa0c8200ff88530137f8a518847fd654c00bfea8e200fff1493013ffe8718827ff320c407fba0c8209ff1933104ffecb99063ff434841ffe2126002ff149211e7fca4a1817fe214844dff2146203ffd014200ff86088023fc6544005ff2144200f74cb3104ff864a180ffe4090c157eb2e202dff08141007ea8288027ff5390c0bef98c6203ffd0542167faa99888ffe644c471ffa866405bfd9641015fcc498807fd505005bff2828205ff08621077faca9001
  | 3 => 0xeb1a2000bf58a3104ffcc99800ffd42904075e3226407ff15110025fccb9800ffe435040bffa8c8205ff1064104ffac398017fd6488435ff2844205ff10531017fca599007fe20c40037eb066004bf19521007fec4a0827fe6090c3bff1006200fd8851004ffac598883fd520c4077f3266007ffd0510077fca290017fe658840bff32c8225ff0823104ff8a798803fe21cc0137f31a4202ff0c9211f7f8a121833ff42c4007ffaa28201ffd011002ff88310807fd40c4007ff2a28609ff90d431effea6a1883ff520c413ffb0e6401ff84120017fe4290012fe65904097f32a623eff042430077c8720816fe610c405fe194422fffd4d4102ffcc01880ffc41508517eb2c6202ffcca21017f84090827fe31cc001fe18a8002ff14b3204ffe8798017fe609047b7fb2a8612ff14b3004ffc8699007fe30c4005fe2166417ff94121005fac398077fc400c413feb148601ffd4140057fca7880027f6544001feb026200ff48730007fec09887fff420c40b7fb12420dff15120057faa588007fc204c045ff2926235ffd4d3200fec208800ffc4050463ff2948203ffd5143017f64090007fe504c015ffa962009bf18d4014ffc819884bfe42cc01df6a924031ff14a41015fec8a107bff200c413ff9946205bfd8e21007ba6498893fe654c4137e31a2009ffd0f321a7f8c899007ff4048007de20c8609bf19643097f8439800bfe42cc829ff28e6001ffc4110025fcca88037ff41480057eb144235ffd513200ffe6098002ff614c803fe2062002fbc853202ff86288003fd3250013fe1926004bf9953208dfaca9800bfe525085bff1028203ff1014301ff88520827fe64cc833fea8a4209ffd973002ffcc918816fc650c445fe2126209ff94c31017fe6490806fe604c805ff1026403ff10d40007fa6290803f4614c80bff20c6205bf98621017faa49900bfc21cc813ff992600bff8cb1002ffc8310826ff65cc0237fb2a6018ff191210ffbe861880bfd42484017fb028201ff04140015f8c498807ff5044045fe2926205ff4c62101ffe87208effe2050c037e3026405ff08531047eca288087fe604c4057f3128240ff14643007f8c6a0816ff6488401feb12600aff5531016ffc60a080fff4250413ff21e6211ff5453002ffc6298802fd644c005fea144202ff1094200ffa4188007fc5050013fea9c8623ffd0d3100ffc219800ffd435000bfeb206201bf98331037f8c488027fc6290c03fc1024005ff14641107faa818817fe414840bffa8c4212ffc873004ff86121803fc3148001fea0a2009ff59731007fa85188f7fd5250c117eb2a202fff549410c7fcc890806fc605085fffa928203ffd0943117fc84988beff6550407ff2148203f7d0d43017fe8499027fc62cc00bfeb162000ff4c5301bffe819900fbc4290c03ff9062002ff149
  | 4 => 0x97fe308c451fea946201bf1833104ffc6418826ff64cc805ef1926406ff10910007fa42a000bff5248413feb066203af1913108ffaa498003fc634405ffea828203ff15243187fca12080bfd5288405ffa944202ff5492104ff8c12180afe6290405ff2924017ff8c12101f7e84a00f7fd5350c43fe1026206ff14910187f84120857fc2150003ee1866001ff5013018ff86520803f64144005ff1924205ff8851000ffc8188007fa10c40017fb128619ff94d210bff8809080fff4090c13fe1866209ff0c9311c5facb9900fff4190c13feb2e6410ffd093002ffc6288073fe538847bfea828638ff5473202ff8c72081fff434400176b106201ff8c13004ff8a699037ff434804bfe2046202bb9883104ffa6398003fd635040bfe3044205ff1473104ffca718803fd6350001ff20e6039ff98142025f8caa180bfc4248005ff2128402ff08142007fec899007bc40500077e3224208ff99510007fa428805bfe515006bfea826411ffd4930037fc8488007f840500015fb226239ff94142017fc6510812fe6550c5ffe29a8200ff50b30125fac718867ff65484077f3224209ffcc93101dfcc890016ff645044fefa1c6205ff08510017fe4110873fd5488413fe29a8601ff4c110007fec0a180bfc3250805ff10a4026ff8ca310cff8ca908d7fd534c801de3226201bf1824100ff88098003ff329040bff3148214ffd473004ffca6980037f6544001ff21e203bff9814309ff88398003fe3148005fe2924005ff19310127faa298827fe65cc801ff31a8403bfd8d43005fec488016fe619040bfea8c8200ff585430affe42a0007fe1050033feaa24203ef951400b77aa8a0027fe430c40bfea8c4205bf18b10017fa8599003df6350405ff2124001bf1803104ff88721812fe65cc82dffb2a8002ff4852001ffc80a080fbf40504017eb046205ff59431057fea988002fd64cc44dff904621bff9522107ffc6498003ff6250075ffa8a8410ff191301c7fea399023fd6544013feb266211ff5513000ff06098103ff5090c05fe10a4003ff15140057fea7880ebfd51508037e3046237ff1073202fba621889ffe548c441ffaa06205ff5463100ffa6090027fc328c40b7f30c863cff18943017b86499003fe6150c0bff20a6202ffc812104ffea618817fe5144007ff2028602ff08221097fca598027fe300c4017fb026218ff9512100ffe80a0027fd53cc401dfb22620fff9893012ffca118827fe65cc0037f3048200ff1853219ffc8099007fe104400dff90a2000ff5093101dfcc99900fff4150003fd1866012ff10b3000fdc4090007ff5048001ee99660049f1951002ff8c120807ff204c013ef9966209bf98f10007ea4288003fe6148049ffa8a6205bf18540007da6490827dc43cc829eea9e6010ff951301edfacaa1816ff62c40017
  | 5 => 0x964300f7c80a00c3fe3090407fea128015ff94940007b8c6a080ffc4150013fe21a860eff5452002ffe638800aff634c813fe32c8600bf590311dff8a0a1893fd524c459ffa866205ff14431015fcc4980cbff529040b7e3106205ff18a311bfbe8799007ff20cc02dffa8a8001ff90130017fc6599017ff310c449ffa92623bff0414300ff861880cbfd5290405ffa128438ff55332005fec498887fc404c443fe3026202ffc8542007fc87108e7fe305085dfe3128209ff10d32007fa6288003f541c4001ffb0a862fbf59541017fe649000bec324c827ff2a66020bf5943102ffc8288027fe438c401feb1a4009ff94d31005fec2a10cffc104c80bde20a8202ffd49420077c86a0003fe434840bef18a6224bf59531007fac6908cbfe5390407fea0a8022ff8c931007be6498006fc60504017eb244201bfd8120007fa8488026fc64cc405fea928428ffd4e3102ff88288003ff624407ffe10c862afdc87311a7fcc899027fe434c013fe30e6003ff90a43025f8caa000bff20cc813ffb266005ff5883106ffcc890007f410c40057e3128009ff0c1320e7fea910823ff514401ffe3126037ff9533202fde431080ffc4050813ffb2e6205ff1971004ffcc399003fc615006b7eb2a6431ff8ca41167faa198803fd41cc475ff29a8400bf5824304fde6499003fe4148007feaa48209ff4cb31127faa898802ff61480057fb126400ff4c520007f8c6a0026ff64cc015fea9e2005bfd9431007fac0a0803ff6350803fea862000ffd854202ffcca188eafd6550813ff3166219ffd512116ff860a0816fc63c4013fe3066404bf9962100dfec098017fe62c40057f3148611ff1953000ff841980a7fc50cc441fea806200ff58121007fec298002ff6350005ff192841dff9003100ffca19800afe63cc807feaa28405ff98831127faca98847ff534c047ff2a26211ff9953004ff8879880ffc425000bffb106211ffd513004ffaa61888bff204c413fea1e6208df1951018ffe4120817fc10cc405fea124002ff88221007fac299097fe208c41dffa8a4000ff58d1001ffca920872fd658840bfeb2c4203bf993100057ec899017fe6088413fe1966005ffd8f10037fca4880d7fc514c81bfe20a402fff9954104ff860a180bfc20cc8077f3246200ffd8121207fca32182bfc53c4013ff32e6205bfd90311fffe43218dbfe50cc805ff902843aff59542007fc42a0017fd63884037f302843eff842430d7fc6110823f55144005ffa124200ff8c5400aff8a4a0002fd63c4003ff1026003bf99110017fc40908a3ff528c4077e3226003ffd0d4004ffec999003f731c4081deaa48603ff9514204ffecb2180fbe5490c29fea8e6000bfd854004ffe6598027fc530c4137fb266228ff55231005fac690017fe640c405fe196642fff54d4101ffc84a0
  | 6 => 0xbfb28e2003ffd054302ffac918812fe654c0077e322642affc873102ffacb880d3fc544c8017eb26641efdc8431005fac120817bf41904017eb122000f7cc93100fec2188003f7614c823ef29a6002ff8c92002ff8c910827ff53cc813ffb0e6001ffc811010ffc4098807fc304c00bfeb048238ffd533204ffac999017fd6390413feb166005ff1454103ffca888037fe544801dfeaa2403affd4d4200df8c0a1812fe654806bfe32a641cff5422100ff840a0002ff63440137f31a2005ff98e2102ffac110826fe634800bfe31c4205ff5071002df8c2a10d3ff404c803ff1066034ffd053210ffca098802fd6448033fea824203bf19120007fa8788007fe5050013fe29c623aff1954202ffa821883bfc6548001ffb226005ff59310005fac598806ff6248003ff9024000bf58b300aff864a0027fc62cc40bff28e6203bf9933100ffa8198003ff604c805ff1066419ffd4d21147faa71880ffe4350849ffa9a621cff54e2100ffc6198017fe65c400dfe192200cff10f1000ff8a18800fff54904017a30a6429ff8433104ffec598103ff5190c0bfe3148209ffd8643017fe8510803ff6350033fe29a4232ffd4e410eff8a018893ff544c407fe20c8601bf98221007fec2a0007fc10c4027ffa166009ff94f3004ff88618817fd600c401ffb126004bf19520017faa599027fd430c42dfea8a8000bf58e2102ffec520816fe61cc8017fb024209ffd833200ff84088007fd504c001fe9962019ff54d210a7faa598003fd6250c0bfe080621cff14e21005fac321803ff6148057ffa0e6200ffcc94000ffca088017fc10504057fb128433ff141320a7fea598003fd644c8057e3148605fb0852100dfec698017be4150423fea9a6009ff4c8311affea0990f7ff5050c13fb98c6202ffd0b3201ffea8a1027fc64cc021ff3226001ffcc11015ffe8198802fd62c4001fe30a8409ff8c33202df8c290017fe628c407fe2048205ffd823102ffccb18806fe600c40bffb2c6201ff10330005fec6a086bfc4088405fe1924009f710e4300ffe60900fffc5290c01ffb126230ff8824104df8c998012fe655000bffb262005fd0c7101eff8a2a186bfe4088413fe32e6202ffd4b3200dfac188027fe32cc07fff2948600ff4c540047faa288003fd605080bffb2e202dff1414103ffcc888017ee21484037e3026216bf5954000ff8409000ffd4350413fe29a6000ff58941007f8c690807fe504800bffb246200ffcc9100bffc80908d7ff654c855fa10e6225ff9023102ff8cb1880ff74150407fe21a8203ff905401b7f88199003fe614c007fe2148626ff10a3104ffca79908fff424c401fe9928201bf18221005fec6a1087fe304c407ffa148202ff881420a7faa9980bffc655040bfe28e2009ff0c0310e7fea71080fbc4390401fe30a6040bf5
  | 7 => 0x80384b00022c0880001a010040050ae0bc0906210a01800826132008068060040a0088670940100400c0c204c000fe00c00c000c80b80a01b857004014349d504a0000200008ae5c2a800016084060000040240a01a37007000000010054390020320000081002e0502080102c0941083200e1080085301a044450070080240500e002ce0000000000340101006e020b8033036004028c20180180d00f00686402800060000010050e20780180001a0680003902c028060c30320e82e00106831c020050000001501204e0080a93b03000c0080200050c010fb2a20000084c0020041d8000000dc009700120004191201a0340001b02c0300d00000e080350020047e40d009016134d706a00011c0000000800c0003e00e01818014006400008000160202e805078030138013e8000008030040a00000c1da0e00008803800c0a80500a004068010120002b81b0480140007800a1e00000200e000998001de168060150000140e0010040dff1912002df8c298003ff6050803ff1822007ffd0910007fa869805bfd655003ffe2a06232ff54e41017fc84990cffc604c8017fb22622aff90b3100ff82098003f521c4001ffb0a6435ff9953202ffe8388017ff658840b7fb246233ff9813200ffc6090003fc63508137e32e603aff5414200dfec8a0003fd324c003ff1024009bf18d211f7fca1218fbfc2090c0bfb1886205ff98231005fec498103fd5190c11fea922008ffd491002df8cb18827df32cc02bff1928036ff9033202ff84398817ff410c455fe2166209ff98a430177c84a1012fe6590c33ff32a4201fe04110007fcc690027fc6190c01ffb224203ff5514004ff8a698803fd644c45fffa828200ff5814300ffa8090017fc518c451ffaa46209bf18d2000ff8808800bec4250813ff21e601aff0c22104fee6298823fe53440017eb0e6405ff1462102ffe63108bbff215040bfa1086204bf1954204ff86521827fe61cc00bfe18e2001ff48110025f8ca980effe1050c79ff90a862fef55141005fac720827fd61cc805ffa92403dff9454302ff8c818866ff6548403ef1826005ffcc63104ffe879880bfd5248003fe2024002bf1893001ff8a8a0827fe43cc803ff902802dff9814102df8c988026ff6450c07ff2a28006ff8c9101dffc60a1816fe61cc001ffb226209ffd8a43007f8c290017fc51484037f3026235ff94532165facb9880bff214c80bffb1c8209ffd0e4310ffc8098823fd5444013fe1846227ffd0a3101ffc812080ffe4390407ffa028215ff1894004ffea79800ffe40508057f3128633ff841320a7fea998002fd6348407ffa028620ffd4031077fca6900affc54cc407fe2a28605bf18a4101f7ca8a0847fc514c013ff98a6001ffd4310147faa118802ff614c013ff3066217ff181210bff86090803fe635000
  | 8 => 0x980803c0180300013c0201381b000000090080120200a02400810ef700708200800804004a98000060000840000606600c0d0030000604980100c640068050020080280305a0e4268210000440c80300c0000019901a0000181e02a098238c0008000000010be238028330120442c8a63260080780b002000a281615a000012290061e02b0040260140001f00000c98039006004180260040940600407e00c568081ec0c00402302600c06851018060000010100018800b004010000020080040006001c2503f0320222201683d0000541a04200017c1b82302201c0001e15aea80000f08c02c008000000500580c00005402800000010008ff04a0482f80a0241f80280702e000080050520080000900604c00000090228000100000a8020030f40000b000004088008000ea6a4a384a0540100801400402000820018000590a167e0042400100203418005038018020050200a0058650540e803014000000170030000000a055010430fc00036216c2480001600c0480f00616c160170bc03000001018000188160000c015005006224000032480141a00c0da0000002f0120040281a03208
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc630c52002cfc7158e410067f65d89103d6dc21d8d41006df51d8d4104cfe76d8d100067f7558241006bd51d91320079f744c930086bc42d91302eebc41586431debd405933002ecd315883104ede7518d41004fd755933201cfc74d8d10405be76d9132006de20d8d41024fc7558b1002df47190f1030eef20d8940006bd545903102cfc7158231004ff7258331085bc745853002cfe71d814202ef7609051002cfc71d891009dfb7058d4000cfe70d85320f6f7201853204cfc7690d20156f742d85323d6df6318543006bd52d9131004fd75d854300dbe7090d4004ede634cb10086be545824302ddc71cc9313b4ff7159121006df4358a31006df6398d4116fb74050510006bd70d91311a6bc40d9132005bf744ca3100dbe7690d4001ef66450510006f575d8532006dc65d8d41016dc624c930006f65018532006df5118d413cfb431d9131004fd72d9110316bf40d9120156f473d8532014fc76cc521004ff755903104cfe73d9110014fe72582413d6df10d8d411bedc43d894304ede6318d41006de6018d41024fe755933001fbb6050940156f520d85321bede64cc931016dc624c93100dbe705054003dbc74589103c6dc2118d41004fc7650520024fc75d853000cfd715822102efb705823104eec3058831065fb7058540004fd71d8d201febf32d913204cff7690f103c6df1018d4101ebc6450d3004eef73588310067f73d9510004ff7458910004fd7558e2102cff72d9121006df6398d40005f771589430bff0704851000dde704c930007f370485100d6ed20d8910004ff7258730007b761505402f6f621d852002efb1058031004fd73d891000df8704c53004cdc735891000cfd74d8940005fb704c930004f7715913201cfc74d8931006bd75d91310cd7c75581210f7d6321853229e7c20d951004cfd74d8543007d7714cb30006f451d85322ddf57550710006bc745891004edd7118d41006bc60d91310057f7558d10014fc725873000cfd74d8540005f77150d10004fd72d91300bcfd76485101ff9c32d9132014fe735933202cfc7159221006f451d854029e7d30d951000cfe76d814201f9e7390e41006df72d8d41306dd32d8d20156f72158b31006bf6450931024fc7558e410457c7558d1015ebf41593312b6f563cc710024fc75d911000cfe70d91210067c42d951001ebe645073102ef76088510004fd7650d2000cfc764c5300067c7559110006bf64d893102ef81058241004fd74d8d2004cfe73d894128df77158910006be70d9132116ee32d89311ccfd74d912004edd7018d41005ef7258141006bd6450e3101fbb6090d40024fc75d8131134fe7618d21006bc6458532006dc63d814100cdc764c9303fcff73591321febe32d9132004fe76cc540014fc7259331396bf6590d40006bd5459110024fc7559031
  | 1 => 0x81310047f7559110006df638c540004ff7650d21006be42d91310067c65589100c5bc7458d21004fd76cc9410457e7598d10004ff7650b31004fd7558d10005f47158d20005df735083100cfc705912130cff7259120006f754d853204ddc7350831004ff764c940006be30d9132085bc744c5302efb64190f10004fd7558331024fe7558b313c79c311913112df6760c510004fd7690d2101dbe744854002ef6731853202ef46248710017e7614c921004ff735891004ebe43593312bdf57548710004fd76cc52002cfd72d912101fbb6050540014fc7650521006bd50d9132006bd6519131004ff725911013edc42d8d41006dd634ca41006dc2018d4104eec3258b3129e7d10d9510006f65418532007d4714cb302ef9e6390e4120ef763cc51004cfd70d8530004ff7650f1013edd54d8d41007cd32cc521004ff7559132004fd7558831014ff764851013f9f40d8d41007f3705051011ebe76191310fedd5418d41004fd73d81211f7ba7090d40004ff755824102edc3158e21004ff75d8132004fd760c5400debf405922102ef462cc71002cfc768c54002cfe7650b100067f6518d10006df5218d41004fd75593103e6bd6590e4102cff70d8d10156f452d853202cfc71d9110005df73505300067c65d8910004fd72d854000df8704c51002ee47158831004fd768853001dbe7390e4100cfc7158f10004ff7258d10005bf7458d1004fcf624cb310067f6558910007d532cc510006dc53d8d40345bf74cc54004ddf764cb3100cfe76cc510004fd75d8d21004fd7650b31004ff75d89310aeee62d89400debf40d894104ddc7350530006dc20d8d41006ef6248510004ff7558221024fc75d854200cfe7058a41006bf64505310ff9f4018d4102eed2158e2102ef71058a41004fd70d8532006f77158d21024fc75d81412efb67190e4101cfc74d8530004fe76885402d7b55450710004fe764c910155f77158d2102cff7459031004ff7458221004fe764c5400d6fa205822111ebe5458643006bc60d9132004ff7258031156f772d8532006f610d8532007d44318532024fe75d913004cff7690d2001cfc74d8d212b6f431d813104eef305883102ef4610c52032ddd754c930396bd6590d40006ed705883104cfc7690d103eef65318532156f573d853204cfc76cc5201e6ee42d8943006bc6519131006bd54d9130005f47159132007af6250940004fd768c520366bf655054002ed5731853200dde70cc9303d5df7350e31006f46418532006ef42d89101febc4258a4304eef3258a43006de2018d4104cff76cca41024fe75d8d41006dc32d8d41004df73591211a6bf41d913204eef325883104ef7315873004eec5358831005d47350510004ff75d9121006f56118543004ff7259231024fc75d8941014fc72d8d4102efb105822104ed
  | 2 => 0x2ebf7459031014fc725903102cfc764c931004fd765091001cff7650531024fc75d8132006f553d853221df57548510014ec7259110004fd71d8143004fe76cc940006dd63ccb10006bc71d913200cfe7059121005dc73505103cfb731d9131006bf6418532004fd7559330004fd76cc910006bc7458d211febd72d91320067e62d9510006df63cc940004ff7458331005bf744c5400c6bf405912104eef5358831006d4431853200cbc765094000cfc70586432a67e41d951002cfd70d9110006f740d853216ef860581411a6de644cb30006bd545923119cfd7698d2003fb443905100b57c755854004cff7690e2104eee4358831004ff75d8532006f63018532004fd7690d1004cff7690d2110efa60d813102cfc7650f10024fe75d913204edd7518d410247c75589101a5bc74585321e4ff7259132006f5611853202ebf415824126df5755051002df772485103c6de5118d41006df63d8141006dd634c91005eee3258b1002cfe71d913006ebc6459120015dd73d913219ef86058132004ff75d91200059c735054004cfe73d912104cfe76d8d4201cfe74d8d1002cfe7158e21024fc75d8543006bf64d813230def725912004cff73593303b6f621d85420fedf4359031006ed5058831004ff7558231004fd71d9130006ef725913201cbe76d9132004fc764854002eee3158831004fd7558b31007ac744c9210f6f7421853200cfe76d814101cfc74d812101cfe76d91210f6f5201853204edf60cc93004eee305883104cfc76cc94107eec21d8930006bc7458d2001ebc6450d3204cff7690d10006df73591301a6df4358a43016ec628853011dbc744c9312ad7e76d951002eef415883102cfc7158221156f652d85321bedf4359332014fe72582430057d7598d10004ff7458d2103dbc7458d100aeec62589401ffaf21d913204cff76cc910004ff7558d21004fc764c94104cdc735911003ebc4358241004fc7648530005f471589432eebc31d913100cfc7058d210057f7558520006df43d8d10004ff74583321a6bc54d913227df57590510016dc624cb30006bf53d9132006be6219131006dd75d8d411febc73d913202ff3605051002cfc7690f1034edf30d8d4002df7748851002cf47159132024fc75591212a67e21d9510005dc735812102cff72d8d2117d7c755814113ebc4259231004fd7650831156f77158b31024fe75d8931006ef755883100df4705071002fe7724871000dbc765054029e7c71d9510004fd72d8543004ff7258e4100ddc764c930005f574cc510006f761985420067e72d9510006f665185320067c6518d10006be40d9121016ee624ca3102ef7721853215ef641d854304cfe73d8141006bc50d913102ebc765054002ef81058231014fd71d8121006ec4058831006df52d8d41005fb704c530006bf64d
  | 3 => 0xf43d95102fedd30d8d20014dd73d9132004ff75d8d21005dc7358910004ff7159132006bd54d912113edf4359231004fd764cb10006bf7459131065bc744cb100067d72d9510097cf214cb30006f640d853201ebc6490520006be4358241016f66288510014fe76cc5213c6de4118d41004fe7650d2004ede76cc930006fb7058d20014fc72d854001cfe74d8d21006be50d9131014fc735933204cfe7690730006be6019131014fc7258f101e6ec6258943006dc73589102eebe71d913100cfe70d85200aeec52d894002ef461cc520006de32d8d1004edf3258730014fc764c521006ed5258a4300777658851002ef66118542004ff705913200cfc764c510335dd75cc930267b55450510014fe72583313f7e772d8532006ed52d893107eee62d8930005f4715813204edf7418d412b6f731d813101cfe76d9110024fc75d8d20024fc7558d10006de75d8d4102cfe71d8d2004cfc7690d21014fe72d8d1000cfe705923102fb77450710006b76418532007e7714c92104cfe73d894002df774505100f6df764cb31005fb704c510004fd74d812101cbc7458f10346bc43d8d40004ff7559330005f5729051001cfd72d85421febd52d9132006f7541853200cfc70d8943154f77158d21006de53d8d21006dd65d8d41024fe7559120006bd54d9120005f7714c9311a6de644cb3104edc7359332005bf7150940014fc7358332004fd75d8931004fd7558332006bd6450731006f543d853201cfc745873202df47150d3101ebc6490d21406bf6418d42004fd7559231006bf6490530006dd6518d41004fd71d8930004fd75d81322cdf575cc710416bc53d913202cff7158b10006be71d91323a6de43d8d4002df7740c510416bf30d9132004ff7650530006ed625083103dbc744c510176ef21d89410fedc4218d4104ede6318d101ccff7059120006df53d8d40066be54d8141006df7359132006ec545883119eef2058b3002eec7158831006df4358831024fc7558a4300dbc7050940004fe76885300057f7558121024fe755822129f7471d9510004ff75d9131004ff7559221417af32d913200df676cc51002ff3600c5101cefa60d8142345bc73509400757c7558d203c6de2118d41006be75d913116ebf405931000ddc704cb30006bf20d9131006f721d854302ef770185324079f731913201cfc7458b30007e76248510007bb70505402eebf73d913100cfc7158b1002ede3158f10115dd72cc9311febd42d9132014fe72d8131006fb50d8132004ff705922110edf3058f1002eed515883101cfe74d8530004ff7558f10016ec62885400f6f45218532006d7431853202cfc7159332024fe75d9121005df7350510006dc4358a310befa20d81213def641d8542416be73d9132036ec625891000cfc70d9132004fd7690e21366bd6550540
  | 4 => 0x8d4119ded7298d20004fd72d813104efb7058332015ee72cc52100cfc73d813119fd8704c93004ede7418d410ffd44118d41006f751d853212edf30d8d1004ef77158732006bf72d91310067c64d9510416bc31d9132004fd76ccb10004fd7558d2001cfc74d8131004fd7558b10006dc6018d41014fe7258d1004cfc76cc940115f57198d21004ff705913104edc63cc51002cfc7358b3104fcf724cb300067c73d951004ede6318d42005f7714cb1004edf7218d4102cfd70d8d103cebf31d9131005bf744c520085bc744c930006bd72d913101cfc74d8930006ec5058831014fc73d8930006df50d8d4104cfc7650731156f672d8532004ff75d894000df8704851004efb70583311f6fa4058243014fc7358732005fb7048510024fc75d91311bede64cc930006f5531853202ebe415923101cfe7458732006ef624c94001ebc6490d1004cfc7650730006dc43d8d10004fd7690f1036dbd755054000cfc70d8543007cd324c5210067f21d9510024fc75591311febc72d913204edc4359332016cc624c930004fd7559120006f474d8532004fe7648540086bf43d9130006f775d853200df67048710024fc75583310bef86058121006bd5459221006df63cc52116efa10d814111ebe54d913102cff7058031006df5018d41006be651913102eed4158831004ff75d8141006ec745883102cfd73d8931024fe75d812102ef470185321a79f43d91321cfb870509400079d54d8d41007776590510006f740185322eebc51d913100cfe7058a43006bf745912004cff70d9130005bf744c940014fc7258231004ff7559332014fe725933001cfe7458d1003ebc6459110006fb7058910004fc7650931117cc624c93107eec625893004ef7315873204cfd72d8132014fe76d89430079d5418d41004ff7558730014fe7259110157d7214cb31006df6398d201a6be64d913201cbc7458d21014fc725864329e7c10d9510006bc50d9132227746588510014fe725913011edd4358e41004ff7458e2104ede63cca41007b64390510006f5641853200cfe70d8d10004ff7650d2004fdb604c9300adee720c5400c6be64d912100df4705051001ebe6450e31014fd70d8520006ef705883102fe77248510004ff7458730004fd755824301cfc7458031004ff7558d103d6de21d8d410f6f53218532006dc72d8d413d6de41d8d41004ff7650931006ed624ca41004fd75d8d40014fc72d8d2001cfe74d8d2034cff7359130004ff75d813104ddf764cb30004ff75d854302cfc7159132006ed5258831004fd70d8542006bd70d913200cfe70d893100cfe7158b10024fc755922100df87050d3029e7d70d951000dfa70cc51002dee714c921004fd755873200cfe70d913201cfe7458d20004fd75d91200f6f65218532014fc7259330005bf744c9410067
  | 5 => 0x24fe75d8d403c69c4118d41176ec625894125df575cc510006df2118d4102df47150f1002ef810582212e6f77650710004ff7558831006bc52d913102cfc7158a31006df21d8d41005dc7359110116dd3258e21004fd71d894313f9c438c540006bf6490520156f752d853200cfc76cc510006df70d8d4100cfe71593100f6f4620c51002ebf74592211a69c644c93101cfd72d8d42024fc75d8d420079c644c93100cfc70d8532294ff715911000cff72d91201bedc64cc931016ef614c921006f554d8532005bf744c521036ec42d891001cfe74d8931006ef4258b3004ede7218d41004fd70d8941004ff735822100cfc7058a431febf20d9132004ff7458b31016ee6250831005ed720c54012efa3058231024fc75d8143004ef7259110006bf64589312eebf6590e4104edc4358a4302ff360cc51001cff7659120004fd7650a31004ff75593313d6dc10d8d4101cfc7458b10005f7714c93002ebd415824101cfc745873002ef575185320057f7558d2005fe6324871001cfc7458910004ff705903103ebf41d911000df6700c510006df7358d210079f64cc9310047f755891003df97098540006bc62d9131024fc75d893000cfd72d8520016de624c9310057f7559110004ff75d85401dcfd7650d30156f442d8532004ef7258d1001ebe6490e21156f420d853202ef81058031016de624c930004df73591103c6dc1018d4101ebc645052113edf71d8d41006df6398d2129e7c30d9510004ff765091000cfc7058a31154ff7158d21004fc765053002cfd73d8131006bc70d913100cfe70d9110014fc72d8d4002eec3158831184ff7459110024fc755933002cfc715903102ed43158f10005ef7258131024fc75d8520036ec32d89100079c744cb3104ede6318d4002cfc7159130004fd74d853037dbf7550940014fe76d894102cfd72d8d2102cfc7158a433d6df63985430067e32d9510156f662cc710006ec755883119ddd72cc93002cff7159310004ff7559120024fe7559310004fc764c520156f620d8532006f751d854004cfe73d9130024fc755912002cf4715883111ebf405864300cfe764851013edc74d8d4101ebc649053000df470cc71002df77588510006ef628853003ebc43d911001cfc7458d2004cfc7648730004fd75d9130006bd65d9132006f56118530004fd75d89300f6ee4258831007e4714c92102cfc71d8d1002cfe76d8540006f774d8532004fd70d8943006ef7258d10005ef7250d3227774659051004cfc735864302ef4614c53002cf47158d20006dc60d8d41296f710d8540004fd760c520004ff7650930004fd7690730024fe75d894304edc435903102df4714c931015ee7290d21346bc4359130156f432d853200cfe7059031004ff764cb1004edc435883111df57198d41006df6398d420fe9e541
  | 6 => 0xf4359231015ec7250521004fe764853000df6704851002eec41588311a6be54d913202cfc768853002cfe76d853000cfc7059132004fd75d9121006bc651913212cfe7618d10006de6518d4100cfe76d8131035ec7259110005f77158d20004fd7690d201a79e73d9132004fe7650520006f651d8532024fe7558643006de32d8d41006ee50588310deed42d8941016dc624cb31024fe7558910024fe7558b10007cd324853020ef5630c5103c79e4118d4104edf7018d4107fcc624c930006bd71d9131006dc30d8d4119cff7058d20005bf7458520024fc755933113edc4359231015ec7250d321a6be761913201ebc6450510006bd5458243004fd769053004eec735883100cfc735873002df4714cb1004edc7518d41006bf6490d1004cfe735824304ebc4359031014fe725903102ef71058831006be65d913202ebe4159031024fe75d8532006bd73d9131024fc75d912104cfc73d91300f6f6201853202ff360485101bedc64cc93002ef4751853200dfa700c5400067f65d9110024fe75d854302cfc715912002ef42158831006bf54d9131004fd73d85401debf4059330416be53d913216ff070505100f6f43218532006cf4358831006dd3258331004fe7690d21006f770d8532006df32d81310067f41d951002ef71059031024fe75d8530006bf644c93120df6738851004edc63cc9400079f6390d40006df630c5403479c43cc94001cfe7458b1002fe6720c510024fc755931029e7c40d95102eebf6418543136dd32d8d211a6bc41d91321c67c65cc910004ff7458d1000dde704cb3000cbe7690d4002cfc735933104ef431586430247c7558d2001cfc7458a3101cfd70d8940014fc725913101ef4649051004ede76cc93102cfc7158332006be50d91322eebc6190d40016f6624871002df77590510004ff75d8d40014fe72d8530176ee62d89411a6df43591320f6ef205883102ef472185320fedc5418d41006bd5459310407ac321913204cfd71d8131006de65d8d4100cfe7650d303fddf7359132014fd74d8142024fe75d8141006bf74591322a67e31d9510014fc7258e411b6fa2058332024fe7558d21015ef734c921005df7358520004ff765083123fd7430c510156f773d8532014fc7258241006bf7459110004fd73d89403c6bf6418d411ff9e32d91320067c43d951029e7f30d9510006bf651913200cfc70d8d10004ff735922100cfe7058732024fe7558e2102ef661185200067c75589101ad7c7558132005bf7458d20004ff7559121385fb7058940007db704c93029f7410d951000dbc7050540004ff75d854201cfc74d8d20346bf6390d4000df47088510004fd70d893102fb77450510156ef2158b31006ed624873001ef47650510004fe7690d1002cfe7158221004fd7558e4102efb70582410067f65cc910
  | 7 => 0x883100cfe7058b31006dd51d8d41004fd75d8910006dc6218d41004fc764c540004fd7650730006f7614c53020ff170cc51001dbc74cc5401fedd73d913220fd463cc5101febf72d9132007d4714cb312b6f576cc71016efa40d81410067c655911002edc3158f1000cfc7059031004fd70d8d4101ebc6490f10005bf745813213edc40d8d41006bf745913004fd761cc93101cfe76d9120004ff75d91300fedf4118d41006ed624ca310067e73d9510006bc64985323c6bf6319131014fe7650521004ff705873204fcc624cb31006ee7058831024fc7559132004fd70d9121004fd73d894101cfe745803104cfc7358243006df7358d2011dbc745893102cfc768c52004ede63cc910006bf6458131016f4764851001dbe74885400beef2058b10006dd6318d10007bb7050940004fd768873000cfd72d912002cfe764cb100067f6590d1001cfc745833204eef3258b31004fd70d913102cfe71d8930006f77158d10006be52d9131014fd73d8132005bf745812102ef7605051000df470cc51002cfe71d9132006bd53d91313d79e41d8d41005ef725853004edd7218d4100df4709051001ef6645071011ebf40d913104edc7418d41004ff7559131006f640185323d6dc71d8d41004fd7650b301feee4258a43016ec62cc910024fc7558b31004fd75d9110037e63248510006dd5118d4102cfc7158831014fc7259310004ff7258241295f7715911013ede74d8d41006f55418532004ff7458231006df32d8530005df735073000cfc7058a411febd20d9132024fe7558b30007b464d853204edc638c54029e7e30d951002ff010505100067f655911001cfe7458a31006f670d8532006f765d853201f9e7390d40157e432d8532006bd54586431f4ff74591300fedc4018d41006de72d8d4102cfc7158d200057f755813204ddc7350730004fd75d8542004fd72d8d4004edf7518d41004fc764c940004fd768c540005df73581210f6f44218532004fd75d9131004fd7650b1001cfc7458d10015ee720c52004efb3058031004ff7648530006dd6318d40004ff7059121024fe75d9110005f4714c93000ddc70cc930006be70d9131005f4715893002cfc764ca41005f7714c91004cfd72d9132006dc53d8d4101cff7650d30006dd53d8d2102fe5720c510355dd754cb301a79c434ca4101cff765073102df47150d1004edc63cc941004fd76cca4116efa60d8141006ef7258910006ef7258d200067c65d9110004ff7358a41006f5431853204edf7118d4104eee5358831004ff75d89100f6f4201853219efa30d8132114ff7258d21006be10d913110ef71058730006bf70d913101dbc744ca410aeec21d894002cfe715824102eec2158a41004ff75d89411e6ee62d89430079f744cb30024fe75d8d4202efb705803102ebe415922113eb
  | 8 => 0x2dec714c921006df63581410067f7558910024fc75d8d400f7e4321853204ecc43588310247c75591100047f7558d20006de70d8d41005f77158132014fc72d854301cfd70d8540004ff7559310004bf7458d2004cfc735912110cff7058d10346be435913002df4714c91000cfd72d8d20006be42d9110004ff7458a31005f5740c51001ebc6490d20006bd71d9132006f765185322ef9d6390e413fddf7350d32004fd74d8132004fd75d85201d67c6550910005ed7290d21014fe7258f10004ff70593310079c744c93100df670cc71000cff72d8d20006f7619853204cfc7358a43005dc7358542004ff7558b1001cfe74d8532006f7610c520006be10d9132014fc725803102cfd70d8910024fc7558730005ef724c521004fd71d9132024fc75d8d1002cfd72d81211febc52d913201dbf7150540006dc6518d4101cfc745822102cfd715931020fd4430c510285f6769051002cfd74d8d41004fd7558f10186bd40d9110006ef4258831006ef7258d210467e76d9510004ff76507300067f72d95100c6bc6459121004ff7458f100067c65d8d1002ebe4159310024fc7558221157c7214cb31006dc6358141004ff755833208d7c7558930006be40d913101cff7650d32004fd75580312b7d732cc710004ff7458732176ee42d894100cfd73d8930036ee62d8910004fd74d853204fcc3250d3202cfe71d8d420457c75589101febd21d913202ef7600c510006ed52d894103dbc744c91007eee32d8930024fe75d8930004ff75d894302cfe76d85421a69e73d913214efa1058331014fd70d8d20006bf7458f1001dbe7390d40006bc6458132006dd5018d41156f462cc510004fd7688540014fe72d9130024fe7558231005f77150e3113edc54d8d4102eec515883102ef47158f1001cfe76d9131004fd7650d2102fb44150731006bf6458532006f95058031004fd70d913204eef7258a4300cfc7359330024fc7558e2129e7f71d9510006f764d85320067f655091004cfd74d8943004fd7559121024fe75d913103fb464505100f7d57318532416bf31d9132006ee545883104ebe4359031006dc62d8d4116cfd7650510006bf645051002cfc7650e21004ff75582431a6dc435913200cfc7058e2100cfe70d8d4120df673905102b5f775cc71004edc634c5101febf42d9132024fe75d9120004be7619131024fc75582312067c6590d10004ff7558b300067f65d8d10004ff75d8d42024fe7558d20004fd7559110006bf6450d31006ef52d8940005f7714ca4116fb870505402ef9e31d9131005be7619131004fd76cc54010df57198d101defa40d8143004fe768c52000cfe76d813213edf41d8d41005ed720c520014fc7258d10004fd74d8910006df634c521016ee624873002ebc6150540007cf634c921006f465d853202eef725
  | 9 => 0xf7458910007d4735071001ebc6450931024fc7558910024fe75d8d10024fc75d853241edd43d8d42006df638c5200c6bc43d912129e7d40d9510004fd7558a4119ef850d81322edbd7190e4117e7c655051014cff7158d1002dde714c931004ff7259031014fe7259310004fd7558730004ff7058d2102df7750c51004ede7118d41006bd54d814113edd71d8d4101cfe74d8520006bc64d8931016dc62cc931014fe72d85401a6de644c9310c6bc40d912102df4714ca41004ff7058b3104ef83058332314ff7459120006ef6288540006bc72d9131006bc75d9132006f410d8532306df32d8d2013cff7359131006f76198543006bf7458d213ddf7715894102cff76907301febd73d913204fcc324c93102ef6611853029e7e70d951000dbe70509401febe52d913202eee2158a41004fe76cc941004fd73d814204ebe4359332406bf631913204eec764c92102ef6769051013edd42d8d41006be20d91312b5f47348710014fc7259130004ff7558b313cebc32d9131007d7714c93119efa60d8132024fc755913001cfc745883102cfe7690f1004cfe73d8540006bc65d913102cfc7650831006f46518532007cf624c930004df735891012ef571d8d1004ef83058031024fc755833210efa30d813100df47048710006bf51d913104edc73590310067f655051031dfb7059120004fe7650d2102dd4714cb312eebc21d9131006df7359221004fd75591302eebf10d913100cfe70d854200cfc7058e41024fc7558f1004cfc7359221006f76418532004ff7058a41006f761581323cebf71d9131004ff75d8142016f46248510004fe7690530004fd7558241006ef624c9310beed2058b10004fd73d912102dec764c921004ff764ca4102cfe71d8d1002eef7258a410befa60d812120ef563cc51001cff765051004ede6318d2004edc7018d41006dd50d8d4100cf4764851006ebc43d91202b5f47350710005bf7458d210057f755891003ebe64d9110006bf54d913204ef73158643024fe755824300cbc765054001cfe76d913002cfe76d8520086bc6459130005fb7050d30014fc72d9120005ef7259110086be64d913014ef710d8530004fd7650f10004ff7258243016de624cb31014fc72d8530006f421d8530006ef725912002eee1058831004fd75d814102eef3158831006f743d8532006de62d8d41005df73591101fdbe7619132006de6218d41016dc764c931024fc7558a41004ff7058e21004fd71d81420f6ec525883100cfe70592212ddf7755071013ede43d8d411a5be7498532004ff755911004cfd71d8931007b46418532005ef7258d10006b464d8532005f5720c51004eee735883102cff70d9110024fe75d8d20006df53d8d41006f750d8532024fc755883104cfe76d8d4002fb46450710004fd70d854304cfc7650b30
  | 10 => 0x8132005f57448710006dc5018d41006f47158d20005f9700c54002ef66118532157d7714cb3102dde714cb3120fd732cc51002cfe76cca4102df673cc510006bc64d853204edc630c540024fe7558331006be60d913111ebf42d9131006bf6490d20006ef40588313cebe53d9131006be42d9130024fc7559231024fe755913202ef7731853204edc644cb3100cfe7158f10156f632d85320fedd4218d4101cfd71d894104eef7258b3011cfd7650531024fe75591103f6f430d853204efb705824316fb54050710006be72d9131007af744c92102cfe71d9110006f74318532024fe75587301fcbe761913204eed5358831006dd5218d41006bf6450d32024fc7558b30004fd755922100cfe76d8143004ff7258643006ef745883100cfc7059331005bf744c93104cfc735891015df77158d41174ff7259121004ff75d814302ddc764c9311f6bd40d9130006b46418532005f7715083102df471ccb10006bc20d9131006be62d9131024fc75d8d410fedd4118d4102ef77518532004fe760c540014fe72d8d402bdf7754871002ee71058831006bd54d91312ef9c31d913102ee421588311e4fd7650d32014fc72d814113dbc744ca3102cfc7158e2132ddf754c930005f77158d4204efb30583321febe4258a43006f454d8532006bd53d91320067e64d9510376f641d8540004ff7058831157cf214cb31006bf6519131024fc75d8d2100cfe705933102ef6760c510024fc75d9130006f77159131005bd740c540006bf52d9131016dc62cc930006f5611852004ede7018d41014ff70d9120005bf744c530005dc73589410debc4359221005f7744871006ebe64d912018cff7459121004f77158d200247c75582412a67c31d9510096ec4258b301def86058143006f75018532014fc72d91103afcf434c921024fe75d8131005bd7290d40005fb7050510406bf621913202eef2158e2104cfe76d8d21006ee755883100cfc72d812102cfe71d8d4004eec4358831004ff7558a3101cfd71d81412fedf30d8d2004edf61cc931006bd65d9131004fd7558231036ef21d8910004fd7558b3020df775cc51000cfe70d8d2104cff764c51011ebc42d913104ede63ccb10006df634c9400f6ee5258831014fd71d9121116ee52d893102ef71059221006dd52d8d4100cfc764c930004fe769052002cfc7158a4101cfe7458d21007b7645051000cfc70d8d420067e42d9510007d7735071002edf3158a313479c430c5400bcff705891004cfc7359031006dd70d8d4104eec3258b304079c321913202cff768873029f7771d95100c6bf41d91212eebf6490f1000cfe76d81211a6bf40d91323bfb43119131004fd75d8530006df6398d1001cfe7458b301feee5258a4322df5758851002cfe7159031005f77250710004fd74d8d1016df57490510004b
  | 11 => 0x24fe7558332004bf7458d21006bf64d8532017cf734c921006ee7458831006f551d8532006f741d85320f6f72158831156f621d85323f6f443d853203ebe5459110005f7744851002cfc7650b10156f472d8532006f440d85320067c6598d1000df4700c5102a67c41d951000cfe7058d213a6dd43d8d4018ebd42d9121006bd6490e21004fd7559331005bd748c54002ebe615054001ebe6190e4102cfc760c54002cff7158f10156f732d85322eebe51d9131005f7714ca31005bf744c51029e7c70d9510116f6215873200df47048510007d7714c930004ff7359121006f570d8532006ef62cc9101febe6290e41006f470d853206dbc7458520006ee4058831024fe75d8132006bc64d8131004ff75d893001cfc745833104fcf724cb3102edf3158831005bd7498532006bf71d9132267746550510024fc7558732004fd72d9131014dc73593322c6f77648710014fe72d854302eef7258b103d6de71d8d41155f6761853214df77158d10024fc7559332174fd765052104cfe73d8142005bf745893102df47150e3102ef67218532006de30d8d41006ec7258d1001faf725094000cfc70d8d21006dc7359110004ff75d9110024fe755824102ef57418532006dd634cb1004edc7118d413f6f730d8532006ec705883101dbc744c540014fe7258e4126df7755051006dbc7458d2002cfe71d912004eed325873204cfd70d893004ef830582430f6f75218532376be54d85403479c6390d403debf40d854220df4735051000cfc70d894102ef670185320067f6598d10006dd63cca41326bd42d9120004fd764c91013ede42d8d411febe6290d4000cfc7159310004fe765093013fd441d8d413d6de51d8d4101cfc74d852002cec764c921006df63cc510004ff7650b101febf73d913202cfc7650e3129e7f20d951002fb76450710007776550510004ff7058643407af211913213edf7359231006ef725912102cfc715933004eed435883102cff725883102eed315883102cfc7158b303f6f453d853200cfe705883102ede3158e410067f755911002ef57318532004ff7158b300fede4218d41007d4714c931006f761cc520005bf745853213dde7618d41006bf6490d210fe9f4018d41004ff7158243006be40d9132004fd75589100057f7558930024fc75d912013edd40d8d4100cfc764851002cfe71d81430069d5418d41157d432d85320fedd4018d410079c744c930024fe755913104edf604c930004ff764854000dba7090d4000df670cc510024fe75d8941006ed624cb1001ebc645053102eec2158a31006f451d854302ef6741853202cdc764c9312eebf6390e41006ef5458831005bf745893002cfd74d8941006bc60191320067d73d9510004fd7558d2102ef760cc510006dc50d8d41006df63cc94101cfe76d9132006f4615
  | 12 => 0xf7550540004fe7650910116ec20d893100df670905100f6f7321853202fd673cc71000cfc70591311cefa40d814202df47388510005bf744c93000cfd71d891004ebf74593310eefa5058031006df735891000cfc705873202ff3608851029e7d20d9510004ff7158a4301cfc7458d210067f65cc5103eef453185320febe5459031004ff715933004cfe7358a4302edf7358e213d6df74d8d41004fc7650d21006dd325873000cfc70d852004cfc7359110006dc75d8d41004fe7650530004ff755891000cf47650510007d47350510086bc41d91300f7d432185321febc20d9132004fc765093004cff764c5210457c755911004eec3258831004fd75d8131006ee2058a43007cd324873002eec2158831006f630d8532024fc75586430c5bc745812102cfc735833140faf3219132014ff764ca3100cfc70d854204eec634c921006bc6418532115ec725813102cfd7158b10014fe725864302ebc415903104eec3258a43006f7619853002fd4314c521014fe76d8930114fd764c5212a67e71d9510004ff7259331004fd7558221005f57488510004ff7059332006f56118540024fe75591213bfb7311913104ede634ca4124774650c5100047f755824104ddf724c931024fe7559231007d773505100afac625094000df67088510345bf7590d40006df20d8d4135edf764cb30176bd42592212eebf6498d4102cfe7650e21006ee20d89313eef43018532024fe75d8910004fd70d8d21004ff7259310024fe75d8940005df73589410f6f6321853202df4715083104cfe73d8910014fe76d89312eebe21d9131005f7725051004dde73d91321cef860581420067c7558d20004fe76cc910006df2018d41005f77158930186fa4058241005f47158d420067e74d951001cfe745823129e7d71d9510006bc64d813202cfe7158a412a77b10d9510014fd74d8d42005ef725052102cfd74d8141006ec7259110004fd7650d10004fd74d8930006dc73592211febe20d91322f6f521d8520006df65d8d41004fd71d8940157d773d8532004ff7558643016be6250940006be65d91312fcfe7618d2000cfe705933204cfc7358241004fd75d853204f9c4350e3101cfc7458f1029e7f70d951004ef4315873201cfe7458332014fc7259231006be4259231006be60d913204efb305824304cff72d9132006bf51d9132006de7618d41006bc7458f1000cfc70d9131006f45418532006df6518d41004ff7158d20005bf744cb1000777650c5102b5f67348710004fd755913204cfc7359310006dd63cc910004fe7650931016de624cb30006f460d85321febc21d913202df576cc71020df47348510024fe7558a43004ff7358b10006bc51d913201ef664905100f6f6620c510014ec7258d10024fe755873202ef76048510004fe76cc5201fcff7459132
  | 13 => 0x8a43006f771591320f7e6721853234ddf735913002cff70d89101e6bf4259332015ec724c52102eec2158b10005bf72505402eebc71d9131004ff764c5401cefa20d814202cfe7690e21004fd72d8530024fe7559031006ed545883100cfc7650d303d6dc51d8d41014fc72d8131095fb7058d2002ebc4159231005dc73581410067f65485100079c73505401e6ee32d8943004ff725823111ebf43d913102ff3609051001cfe745822101dbc744c941006bd54d91323c6dc5118d4100cfc70d8d4102eef5158831006f4401853200cfe70d8941024fe755883102df776507103c69e4118d41006de53d8d41024fe7559332024fc7558d20004fd71d8d40004fd75d85403f7e732d8532024fc75d8910004ff705923104fdb60cc930024fc75d8931004ff7558a43006f460185320057f7558540004ff75d8d4102cfc76ccb1004cfd72d8532004df7359221156f542d853204ebf7459332014fe76d891004cfd71d91313d6dc41d8d41006bd75d913202dde71cc93111ebc6459131004ff7558331176ee52d894102cfc760c520005de76cc93104edc644cb30006ee20588311a6de644c930006ef52588310079f744cb31014fe72d91310fede5418d4102cfd73d9131005bf745891000cfc70d8931024fc75d81210067f42d9510116ee62d8931014fd7358b30006f76198520007d4714c9301febc32d9132014fe7358332117cf214c931024fe75d8143016e462485101feec2058a43006df63d894114df6730c510014fe72593311667c65cc510004fd74d8931004ff7159120014fc74d8940067b654507103afcc434c92104eed3058831005f57448510006f761d8132004ff7259130006bf50d913104fd4314c931006df43d8d21006dc63d894102cfc7690e21004ff7259131006bf7458910014fe76d8940006f675d8532007d763cc51002eee2158a310067c74d951024df5750c5101a5bc745813202ebf7459231006f77159110014fe725823101cfe7458b31006dc73591213eef730185320067f74d9510004fd75591310f6ec2058831004ff715833202cfe7650f10004ff75591300057f7558141006df7359131016ee624ca4116fb54050510005df7358910086be54d9130006de50d8d4104cfd70d913002efb10582410067d74d9510005f77150b31004ff7648730006f77159121014fd70d9120005f970cc5103eef4431853202ef4618c530004fd76905203f6f643d853204ef77158643006dd6318d4101ef464505103c6dc4118d4102cfc764cb1002edd3158a3121df77548510006f753d8532005e5720c51000df476485101febf52d9132016bc7650940316bd40d91203cebc4358e410aeee32d894001cfe7458910006dd6318d20157e472d8532005f572cc710016ee624cb1000cfc7059231006bf6450521345bc735054036db
  | 14 => 0x2edd315883100cfd74d8d40006dd32d8131014fe72d8d41004ff7650e21004fd7650e2102cfd7158f10004ff715913002eed1058831004ff75d8530006dd72d8d41024fc75d85400f6f76118d21006de5018d4100cfe70d9131004fd755864302cfe715922100cfc70d91210067f7558d20005f7714c941096ef2158b30024fc75580311a5ed7298d421257c755813100df67050710005bd744854013ede54d8d410047f7558d100067c62d9510024fe75d8540006df7359110006dd6318d42004fd75d81420057f755813104cfe73d8542016ec624c931004fd73d9110006df634c510024fe75d81420adec725854004ddf724c930014fc72d814302ef6751853202df47150b3104edc63cc521004fe760c5203eef6431853202eef7258a31006f721d853001cbc7458d20006f753185320067f654c91002ddc714c9311febe21d913200cfc76505103cebd6390e4102eee515883102cfe76ccb1004cfe73d8520004ff7650d10006bf21d91310077765cc5101ffac32d9132006f561185421a6df43d913202ef67688510035f9709852010cfd764c51000cfe768c5300247c7558d10156f662cc510004fd73d8542005ed7298d40005df735854201fb66190e41006bd545933204ebc4359332006bf75d91313bebf611913102cfc7650d3120df67348510014fe725873006dbc744c52001cfd70d8d401e6bd4259332004ff7458b10024fe7558e41004fe7690d20006df6358941005bd7488540006bf65d91321a73e7519132004fe764c940005bf744c91034ebd74d8d401a6dc644c93102ef763cc71001cfe745833102cfe71d8940006bf75d91320bdf5728851004cfc76cc54013ebe545923114ef676cc510004fd75d8121007e5324871001cfe74d8910004ff7558e412eebc10d91311b6ef20d8930004ff745883104eee32587320ce7c65485100067f7558d1000cfc74d81411a79c434c94000dbc76509401febe72d9132186bf40d9110175ec7258141004ff7650520005df7350731156f552d8532006be6019132235f67688510014fc72d9130006df7358d1018eee3258a411febc6290d400079f644c931006f55018532006be51d913201dbc744c940156f42158b31005df735052011ebe64d9131004fd71d912002cfc7158241004fd755903111ede4358e4100cfe73593303b5f7715912107dec72585300067c7558d1002eef1058831004fd73d85200079f73505401bebe5459332006bc601913100cfe70d8943004fd74d8131116ec625893104ebf745933004ddc735073101cfd72d814202ddc714cb31006df630c520004fe764c520006f550d8532005dc7350520004fd72d8d4102df4714ca31014fe72d8143024fc75d9132005dc735854000cfc7058b3129e7e10d9510006dc6358941014fd73d913200cfe7058e21004fd755
  | 15 => 0xc64cc93104cfc7650b31004ff73591101f6be7690d4004cfc765053113edf54d8d4102fe4214c521004fe768c5400f6e77158831024fe7558a4102eee41588312eebc6290e41006df634c94102ebf745931004cfc7358a4101cfd73d8143004bf7458d10004fd72d814129f7610d95101ff9d73d913202ede3158e21005bf7458131085f97098d40004fd74d85204079e3219132004fe764c94104ddc7350a3104ddf75cc93028ef710d852000cfe70d8d42006df735912105dfb705852000ddc704c93004cfc7358221007b764d85320067f6558d10006dc43d8d2104edc634c941016de62cc9313f6f673d853202ef43158f1001cfe74587300f6ec425883103fb6545051002ecf3158831006fb705913002ef77418532006bf70d913210efa10d813116cff7059110005ed72cc521004fd71d813201cfe74588311febf6498d42035ec7258d1007fcf214c9302b5f774cc710016f4628851004cfc76cc91001dbe748c540004ff7558a41156f642d8532006fb705912001ebf6090d40006bf7458d10007776548510136df32d8d2100cfe7058a3102ee67218532016ec624c94000cfc7058831426bc43d814301dbf725094010ef86058131016f6624851016ebd40593103c69f63191313cebc30d913104cfe768873006ebe54d912002ef4715883100cfc70d911029e7f40d95103c79e31191310c5bc744c521004fc7650d20016bc6250940014fc7650d32345bf74cc94000cfe765051001cfe74d812102edc3158e41116df3258e21024fe755803106ebc41d91203efe7321853204eef7258b3100cfe7358b30006bc645893102ef66118540005f572cc51010edd3058f10014fe7259131005dc735052137dbd7550940006be32d913100cfc7358b30005bf744ca41006de10d8d41004ff75d8520006f674d8532006dc5218d411be9c64cc93102cfe71d8132006dc52d8d4104ebc43593301a6dc644c93002fd6730c510007d743d8532004ff7558031004fd75d8940004fd72d8d1000df87050510006f660d8532005f7714c940016ec6248510006de1018d41006bc65d9132005df7350521006f574d8532376f541d854002fb4415051002df77648710014fd74d854204eee634c92102eee215883101cfd73d894301cfc7458231004fd75d8143006bc621913104edc634c940005f77150d3111ebc54d913104cfc7358b1002cfe71d89431ae7c654c91000cfe7058643005dc7358520006f450d8532004fd72d814313edf42d8d41006bf7458d20004ff735912002ef43158231006dc30d8d212577465cc510014fe7650d3204cfd7359330016ec624c930004ff7058e4102ef47418532006bd651913202efb105823101cff7650e31006f461d813201cbc7458910006ef725911002cfc7650a3104edc638c520004fd764ca41016de62cc930
  | 16 => 0x9332005f77159132024fe75d8542006dd53d8d4104cfe73d912004eef4358831006bf7459121347b97090d4001cfc74d8532005f4714c940004fe7650d10024fe75d8d210d6ef20d8910004fd76cc940005df735814101cfe7458e21005df73591210079f744c9310befa10d8121157d632d8532005bd7190d40006f6601853214ff270cc510004ff7058a4304ef8305833104ebe435933000cfe7058e4104ef4315873000df8704c93012edd30d8d1013edf40d8d411bdef7258d4208d7c755853001cbc7458d1002efb705822115cff7159131007e532485100fedf4018d4111dbc74581311a73d751913204cdc7359121014fc72d8d10006bf645813229e7e40d951002eee2158b1002cfc76905303cf9c43cca41004fc7650d104079c7319132005d47350710024fe7558d10014fc72d913111cff745913139dbd7590d4013f9e54d8d410079c744cb301ee7c6550d100247e76d9510326bf42d912002ef6611854301cff7650521024fe755933104cfc73591201267c654c51000cfc70d891004cfe7359031004ff755873211ebf41d9131006f475d8532136ee3258a310debe54592211b4ff7258d20006ef5058831004ff735931002eee7158831014fe72d8d20006f4715913201cfe74d8132006be75d9132006be651913200dfa708c53016fb740507100adee7298d40004fd75d8d1028cff7158910006f77158d20006ed74588313cebe73d9131024fe755922102edf7358e411defa60d8143006bc7458d10004ff755923102df4714c9410ff9e5418d41014fe72d81411a6bf43d913200df4765051001cfc74d8910006de52d8d41355df754cb30024fe7559130006f751d8543006de5218d41004ff7458b3004ede634c9100fedf5418d41004ff764c94102ef46450710016dc764c93004cdc7359221006f76198540005f77150f10156f761cc52102ef5701853204cfd74d81431defa30d814304fcf724c9312177465485100067f6550d1011ebc40d913101ebf6050940005df7350a3100cfc71d81210067c6558d100067c755824102cfc7159231006f421d854333dde76cc930006dc70d8d41024fc75d89431a6bc644c9311a6bc6459132004ff7558d2002cfe71d891004eef3258b303fedf32d8d4201dbe740c540006dd6318d213cebf30d9131004ff7650b30006dc32d8d100067f654c510024fc75591100c6ed4258a41004ff7258f10006ee20d8941006bf50d91320febf405903101cfc74d8132004fd7648730006bf6498532024fc7558a31005f9708c5303cebc53d913102ebc4159221006f7618c5301dcff705913004fd7614c9311bedf43d8943006ed755883138eed42d8940006dd32d853004edf325833101dbc74cc9401b5ef7258d20006fb705911004ede6318d2104edc7218d41006f664d85323cebf32d91310079
  | 17 => 0x1cfe7458f1001fb77150540006ef624c93004ebc435933102df67150b1002eef715883100cfd71d911013ede40d8d41006f77158910024fe75d8520005df73505313c79c4118d41006f464d8532014fe72d9110004fc7650910007b461505400d4ff725891000cfc7059221004fd75d8d4101cfc7458b31007e57218532006bd51d913104edf614c93102cfc769052029e7e20d9510007d443d85320fede4018d4101cbe76d913100cfe7059132004ff7650a31024fc7558d2100cfe764c510024fc75d8142005f574cc71002edf7358f1029e7f10d95100aeee42d8940006f654d853201cfe74d813100cfc705933218eee4258a41004fd75d8d20006bf53d9131004fd75d91323cebc73d91310eefa4058031176bf42592211f6bf40d913020ef7315823104ef77158730004fd7558a310067c32d9510004fc764c910006f676185321febf21d9132004ff7058a3113fd741d8d41024fc75582410057f7558530006f565185322a67c21d9510006f4501853218ebf42d912100cf676cc510006bd54d8540006fb7058d101feef2158a4304efb3058331004fd73d912000cf47158f1002ebc4159310004ff75d812113cdf735913102eec1058831004ff75d8d20004fd70d8d42024fe7558a310067c72d9510004fd75d8943014fe764c521116ef21d89310757c755852013ebf405923113edd43d8d41006df75d8d411fe9d73d91323f6f653d8532006f66418532004fd71d8d42014ff70d8d20004ff7458d20007d743185320f6f5421853219efa20d8132004ff72593303cfb57190e41004ff735824100cfe7059131005ef7258540007b76418532006bc6458131156f76198d2102ef4731853241ede43d8d42004fd74d8d21006be30d913104cdc73590310c6be54d9121004fd75d8941004fd75d8d4204ddc7350531006b764d853200dbc7090d40014fc725833120ef7630c510006bd50d9131006bf65d913100cfd735803107df97098d20005df7358540157d4214cb31006f441d8532085bc7458930006f665d8532024fc7558243004fd73d8141014fe72592312eebe31d913104cfe76d8d200f6f5521853201ebf605054000df670505101a6bf4058a43007d532cc710006f650d853229f7810d9510006de30d8d2104cfe73d8121156f720d8532006bc75d913104fcf724c93002cfc7158243176ec20d8941014fe72580310ffd74118d4101cfe74d8930006f564d8532007cf624c931005dc7359121006bc10d91320fedf4218d41004ff7458031426be43d814301cfc7458e21024fc75d89400f6f6421853203ebc42d9110014fc72591101a6dc43d9132014fe72d9120024fe7558f10004ff75d8d10004ff75d9132004ff764c5203d79c41d8d4111ef64158643037e46248510006bc70d9132006bf6450d3000cfe70d8910004ff715
  | 18 => 0x20030eb01d00600200007400002100f0120780010070002100870090301870170c000103400000301900800c02200b00008f01160f00000011800801900200600619e06400700b03701100801001300000601b08f00907105600f00f0040de00a00300400700001704006a00305f00f0d800300700500e00405c0010000010004a003806b00400200c00300800107600003600300100d0040030bf00402400000800000801400a00800500b07e00d08404900200c00809300b00d0070000ce27d94c0120021980dc0000170080000070070000860004910070a401400e0130050110050000010e21600052353a704400000600000000600e00104100003600000407d0041b70020010020000c233000400a21400400003a05000000c04600200001103801800008800004800000d00806100b1220000120210212cb0180060207c200001201600101c04d02200f13300305c00000b17400300000100102d03b00002a0582700193f82bc00200000900300000100f01001c04f00505001c11a04200400200700400000200300100002905403b3990010020fe08a03301000001c04745701500019800901720700573c00100a03d00200058800300200000a00400600f00004300c00700706d00301c0000770db02702d00d00602000901500e01a18105100400200100000100c01800203700100f00000f01c00b02d10103401400300a04300506700005c8200f90090360e80130ce00201400200000000b02800000000201501e00c05805809101200300309700500203502b01800100200004a0100010110290450010310d400c01d04d00201f01201800000300000a04952c00501907a00001100b00800002500a00a00100c00000101209502800002a03004601000000001301700e00001203400001209c00308315a02a00001900300000201500401d00302203902a00400700000700131b12008b08d4880040000680250030740031ad02c00003300100700003101b0480080400001750b800104500800900204e1ff2e700403b00700001b0000260050050fb00404500a01101b00100000200500200100000400e00000700705b0030d900400a01803700600000000106419101100300900500b00f00b00100700200100400a00202701f0c901702b00b0080c400100000b01906f00200401300200f00805802100607e00203b0f100200104f0120010000080070c40170000b100000001300c03a007007010013058000005022038002003000025305007cc634c921416bc30d9132004ff7558e21004ff764c91020df774cc51004cff7658d20004bf7458f1004edc634c521006de60d8d41066be5459310005bf7458530014fc725824302cfc768854004cff76ccb1000cfd73d913001ebc6450d3111dbe76d913100cfe70d8543006f565d8532
  | 19 => 0x40320132f000601307e00800009e00800d06001100000915b00200c04d00b00101002703400002c0000060010000052bd0040031ce00f00000001c05f00100903b00002504204000d00000500100700605c00800200400606001401e4da00801a01a00901400200000804704300301901d0010020061df00501200102203105100600300100006402303b00d00001500000b0016830000240b600400303500400756a00e00000801a00b02600001900004601f00a00000003801400100e7771540500d204003d0007cd0e100b00200101b00300418c08f0de00700000103e04100300b0e501400700500600a1bb00c01300005b00200000008934e0460030000060220000782f101b00100201800402c0040150000db00500400e00002d00100900400f02245a0040f700e05300000400267708800209546606c00e04500a00200203c00001102711900100110100d01500325600e1a608915600000e00000a02900400c58500800d00200200402a00600e00e04906b08a04700700000201c0e801100800103500002b00f06600000103600001300101423b00000c02b05400700200301700000301801400a0001fa00f00b73300e0d301c05600200000300c47203200b0000000030150090080130031c907700800000000203202601f12800104d04000614900501c00000000d00a00b03c00104501102b0030ee00a0430080210240210ee00000000d00001800401d0010ad0030030010068a90011ba00274300f0020a910100000d02302b00303d00000300000e00e00115f03403e00900200d06f00000317105c0030010a608f00e00c01601406c04800004a02200000b14b00702c01600a27200a00000060c00103e0110010000020125bc00601c0130220000e72a004b0060009460080050040330de0820080081c920f0020010140020910210
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc7476d9521440018e8ebb8ac69020aa7a0c75d91320045ec3c61b22640487e87dd560904010ff0abb286900031e5d750d813200667b9ee4b222082a9e83143644c8014bb0b90ec6a08031b1977258d100061e32ee8b1a20058ec8758932c4001968c9b8ac0990031d1977150d102ed5b408a1b226202ace82d8d325040155908b82c4188031bdd4725911000557410a1b226200c6c72195644400317908b9ec0a0826b3a0e755883115763b0a6598a427de568510c614c80b1d9053b062900031bdd47258d1000579c02ca30a64018f4815da43c400917f0eaa6c898002976166218d4100572c0ca0b106247d94641cd41440090f90abb482980029b61740588310063bbaec2b026400ab5819c3644c80196ee9b0ac0990030fdd47458d200f762310e29926000a9c8458c63440a94ed03b9eca88016b520e76185320047bc0aeab224000e3754953614c8011bd0fb1ac0a080297a1721d8d41416563b6e899242008be87d91604c4f593b09b9ac910802a7e115118d4120c7ac3ec318a6000e8c64d89324c401878e9b2a62880062f219748c5400ff0fc2aa831a82048bf87553644c43dd8ec231a64909e3b19c843185320043f43ecab1a2000c5c75dcd644400117b093b26290002ad60630d91314364e39aa8b206200c3c43dd5609040153d0dba26498802ade1165185320061fb2ee898a20058bc87551648850555b043aec8990121fa1f7558d1000578402ca30a64008bf845d5634800b1e902bb062900063da1b714c910006363aee4b1a2000a9d84d486350517d18872a2c41882637a1f735911002d7340e84b1062008df835d5644c40155d09a92c418802ada12301853200c7b40eeca16208ba9f855506350401968c9b8a64989571d5c465d8d103c64f308e6a0a8078c9c761cd4150001878e9b2a64880022f61c20d913101c5e422eab122000ae4864c921440014bd06396ca88002ada0630d91320043fc2aed20a4009c9c7359141cc4011df04bb284880033318f72581410053642ae0b106200a7685190614c8011f700baac690802ada1230d85320062ebaea7b1a8000c6f75d49620c4f15390caa0c6a0a37a50c864185320146e41aed9928200a9d84940635040156b09a9ec2990022fe11764cb101566a3b6e29926200ccf729cb635040156b08286c2990063d2197448510006ca3a0e2992627de968410c614c90b958e4aa2c888017351c5634cb103d56bc3e8630a64018f5819da4344001878ebba2c6882332d9d8641853200753b22e430a6400a7585193614c88fb2e8039a8288003171d463581410061fba8e8b1a2000cb764dc5324c43f53d09080c6a0803661cf70505400055b40cc032264008bf845d56348455d88c5b8a64980030fdd7645813201c7b436e29928200c9f741cd644400155b05328c89880237a1c6358941
  | 1 => 0x8ebb92c888002ad205651913200477c12eab226000c7775dc56348001878e9b2ac6881e2b5a1343185320071b428c9b0a6490ad78159463504f1b2ee839a82881e2b561c43185320243e42aed21a2000ccc73dc964440091bf0ea9ec6a0802ade0565191320070eaa6a431a8200e3754950614c8031790cba442a0016ad20554592210065bba6e2b1a4000c5f75dcd64440019a8e7b8ac48800327d90735052100566c1c80b1062008df8758c63484014bb0a100c6a0802b56042018d410046fc1ae9b12205dab681083644c4f51bf06bb287108023be09768c54000717a94a5b2262058f4815d932904a94ed023a6ca8800339d88714c9402ef1b28ea3b226200c3f65dd162440018b8cbb9ac8880032ddd061581320063bba8c2b0264028de87d8d325000117d0e086c899003271d3634c52129e3a3b6caa0a20038bc841d9315003fb36c039a82a00031d1d761581320062e3a8e6b222002acc8258f32440018b8ebb9ac4880031e1d77058d200051e42ae1b226482aad82dc3644c8011bf06bb28690802a76105018d4100c5e432e818a8000c5c65dcd624400117f08b9ec0908aaf1a0b43d85320062eb98e7b2a2000ce7721c5634800717d0fba2c4880abb198932cc710006caaa0e6a0a200087e87195634400117f08bb06290217271cd545933202c7c43aa0b0062008f7815d564440018beca39ac48800371d0d720c5104a56bc1ac830a6405ae6819c1620c43f53d09280c6a08aab560c70d853200566412c631a2000aae849d5620c4011f700baac690002ad60450d91310046f43ec6b1282018be86dd131500015cf02baac4188121fa1f75589100047bc3aca30a6400c9c641cd644400b5c903b82c41880297a166218d4101c5e422eab1e2047d96541cd414407f53b07b8ec8990031719473505100053742e80b1062008bf845d932440bb1790dba2c0989fb391db714c92100537428e8b1062008f687103614c80717d0fba2c78823ba560f64d853202c7b40cec99280098de87dcd64884015ab0610ec2a18029d215611854002ef1b02e418a20008bf845d5644c83d59b07ba2c4189e6a7a0c20d91310243f436eab122000ae482584614c0090fd0fbaac6901762fa1f53d91310051fc22e5b2a20008f7815cf6050807179083b264a00028f21570d913113d4f426a5b1a820087e871d564440a94ed02396ca88002ab60b54d913201567436c499260008be87147644c80159b06282c418802ada1265d85320053ac28c830a6400ab6849d7614c80153b09a88c6a08032b19372581311bd4e422c7992200087d85dd94344105938c7ba264a0002ad61353185320045ec26e6b044200a9e848c363484019c8e5b8ac68802637a1c5018d4102e6a3b0e29926253a75811d3654400195ec9b92c0988031d1d461581320061e3a6cab122053
  | 2 => 0x772591100066639ee4b1220008df835d564480131b906baac48800327dd373589100062fba8e6b222000caf741c963440011ef02baac8989eaa761075d8d410045ec3821b226488d97401cd41c407f55d043aec89900317d9773505100071ac28c9b0a6400acd83d51620c4f559b03a1ac418803271d3634c5104765b3b6c830a6400a6f855c1620c4018b8ca39ac888016b9a06405883100572c16a830a640487c855c364484014bb06396ca88002ab612755883100727a94a5b1a8200a3e859cb644c4015cb02282c4188130f9d554d8141006b3b2ae418a2078c9c611cd415007f53b063aec8991f73518c714c94046e4fbb0e8996625387e87c87654400717908bb265881fab5a0c50d85320054ec18a1b226400e9443d00614c80156b0332ec899002ada1260d85320045fc22eab1220008f687d85604c8ad3a906ba2438809ea7a1075d8d413ed6b41ea830a64098bc8755164cc8f553b09b96c6a08021fe1570d913102d7340ca0b106200a9d84d4f63500fb5ad06280c29900e2fa1f7458d100f672432e418a2000acd82994635040717908baac69007af1a0b43185320146e41aeab266495ea672d90614c80117f08bb28488002b520d611854204c6f43ee6b1220008bd87143644c80153b06106c89880a3b2097558d104164e21ee8b106200a75851d3614c8091df0ea96c4a0802976172118d4102d664326498a4205ae681141620c43f9a8ec39a82880031b1cb6558d100052ec2887b1a4200c3d75d53644c8f5d8843a1ac41880317dd7735891004c6e41aeab22420087f855d9324400156b0932ec29902637a0e76505200046fc3ac631a40058f687140614c8131d90ea92c52180237a1c50d8d410065a326e2b226405ce4615c831480d1b1886b9062a01067520d74885100043f438eab1a4005ce4761c532484f353d06396c898803271d373589103c64f39ce3b22643fcac62dd13250101938ec3a264981a26720d740c5404364e39aa8b222000ce572d8431480f19aec039a82880022fe117650d204af4ac1ec830a6400a3d859cb644c40193ee839ac890a0b2798f744ca41006aa328e6a0a2000c5f7518d60504bb53b06396c8988032b1d372589100243e42aeca1a400087e87d9564440015cb03202c418802ab60850d913100c7c402eab22420487c855da41480031e902bb665880063d2057558f100056a41ac230a40008dd8714063504031e902b9ec0908032d19071591322ec5e43ec899262038be849d932440031e902bb28788002ad60660191313ce4e39ec8a0a627aa9c86553635040153b07310c8988121f215760c5201556ac1ee9b0a640487c855d932440011df04baac6880162f21d54590310043ec2eeca12200087e871d562440014bd0a106c6a0802a761020d8d412ee5a38ec899262008bf845d563440018d
  | 3 => 0x4a106200c6d75d4b62500014bb07216ca881e3279cc71d913200477c12eab22201fa9e84d48635040157100b28c899203a3188744c9300071ac28c830a6400ab681143644c8011df04baac89014e9d60773d95100046ec1ceca0a4000ab584983614c8f59a8e3a1ac4188021fe1571d893000537428e0b106200ad58114363504011eb0e206c299237a55cc64185324370f3aaa831a8293ab686190614c91f9aee231ac4a08022fa1c645853202d7240ae8b10621eacd831c1620c4011dd0e282c4188123de1d51d85323c56b40c4031a820087f855d9424400199ec6b9062a025f27dcc645853200556c26a4b106292ab684990614c8090f90ab86c8990023de1d64185320071b428c830a64018f686dc5434400b1e902bb28690002b5e0d54185323d56b408a1b1a8209ace83901620c40b9a8e2b1a65209eab561f43185320046fc3ac631a8400a7685d03614c80b1e902baac8980031bdd77258d100061fbaee8b1a20058f8865c031500011df04bb28688233e1c84744cb3100567410a1b1a82008bd87994644c40153b08290c6a09e3a5dd0431853202cf243a6490a2000cb574d86614c91bd2884218c299016b920575588310054ec1cc032262008be87d91614c8014bd06316ca880032d1d361581320f573416a630a6400ab684980614c8051bd0fb1a64a0803651d0714cb3104e6639ac4a1062008bd87d4f644c40187ecbba264881ebb19cb43185320053b42e43b0a8600ab5818c3644c8014bd0b908c6a0802ad61050185320043f438cab122000e1d54140635040156b09328c299002ada0665191320045fc22eab226200ccc72d8d6050401968e9b8ac6908aab5a1b43d85323d66a38ec69928278e947410c614c915d8ee3a1ac41880237e1d6518d411fc5f43ea7b22640087f855c3644840156b03300c8990030f1d46458131006caa00e6a0a2091cd773185604c8018e8ea38ac6900023da1c50d85320070eaa2a431a8200a3e85988644c4015ab03100c6a080a3ba1f7258d100061e3aec8b026200cb4641c5604c81359d06382c4188029b614705883102c7a40ae7b028427a9e8408363504011ef0eb08c2a1802ad21165d85323cf0f29ea7b2262008df835d5644840156d03306c8990aa3de1972cc710344ce41ae890a8000ae5819d5620c4131dd0fa12c598002ab61352d89400055b40ce1b2264008df8758c63500018deebb92c8881762fe117650f100063abaea3b0a8609acc835d1620c40156b03386c8988029d61740d85320047bc3ac230a6409ace83d49620c40147908b9eca880023ee0175591210043ec3887b2a2000a3e8598b644c4f193cec32264988032b1d37258d100047ac38a1b0a64008f787584614800b78902992629080335dcc71591323aec63a26498a4286e8c43551620c4f1d2883908c6a08031b19
  | 4 => 0x34800717d0fba2c690002ada1353185320061fba8c8b026400a9f83594644c40717d0fba2c69080237a1c635814100567414cbb1a8200ab684994614c83d9c8c438a6498002aba1050588310056ac0ca031a8200c3d75d53644c4f1b2ee839a83881e32d1c47458f100fd4f426a031a8200ab581083644c4011bf0eb18c6a08172d185749853202477c3aa5b126234a9c8458d32c400156b09300c299002ad61230d853229e3b3b6cb98a2005ae4815c1620c4051bb07ba2c598003a5190714c9310054ec26a5b1a8200e6462d952144105938c7ba264a08021fe157690d1002d72414ec30a6405ae6819d5620c4f51bf06bb28398003175d475d8d4100c7ac0eebb1a2000cb474dc563480131b906baac8188030fdd643582410043ec3885b2a208de9632190614c8015a902b18c690002a76102018d410046fc3ac799220038bc845d5634400117f08baac788003741cf705051000667b98e4b1a2082aad821c7644c83f938c839a829089ea7a1050d8d4101c5e422ec18a4092e946410c614c8015a902b18c6a107ab9a0b54185320246fc3aa7b1a4200c3c751d163440031d90cb9062900032d1d061581320047ac3c6030a6400acd82143635040517d0fb2284988aab9a0850d85320245fc3aa9b22640087e871d5634407f55d04286c899002a760f54d913200476c38a0b10620087f855d943440f1938ec3226498816b9a0752588310045f438c8b0262808be87d91324c51bd2f06320c299003a5950431853200667b1ae531a8000c3c7419562440010fd0e216ca880032dd9371581324054e430e89926200ad583140614c80117b0fa9ec899177271db644c9310051ec2841b226205ae6811c1620c40317b093b662a0003a5193714c9310061e3a8e8b122000d95541cd41c400b1e902baac69000237e0d76509104364e39aa8b24425dab6819c3644c40196ee838ac69000b331c932d85300146f41ced992203fcac72d91434c8018eeea38ac69000237e0d75591100055a422c230a6400ab684043614c87f1790dba2c09900a3720d76cc9400066a39ee2b224280c9c761d1324c4f1b2ec839a8388002b360e75588310046fc1aeab122000e948155063505139aeec38a65980023de0575591303d76388686b106288d96541cd41c40018eecbb8a64880031d5d475d853204d6641aa8b1062008f587100614c80156f02b28c8988030f5d074d95102a43f438eab0482008bd87994644c8014eb0ba00c2990121f21571d89300061e32ee898a20788be86dd1324c4a74eb02396ca880022fa1c50d91310053ac2ee1b0a6400ab684d4f614c83d9c8c4b906288016b9205525883102c7a40aeab24428de964210c614c80157700b28c8990030f1d464581320074bc0aa831a8200c9c74dcd634403d9c8c438a64a00029da17401853202c7643ac
  | 5 => 0x18fea760c71d91320052ec2cc5b1a820087d87c87654407f53b07b86c8990163d204764c9100055ac08a1b226400e955410c614c83f53d08290c6a08023761c50d8d414154f418e1b22641fa9e84540635040156d08286c2990032ddd371591320065bba0e2b22645dcb471d91434c4011ef02baac690002b960850d85320051fc2ae1b226209e8e84d0d620c44f5ab03b96c6a080a3721d634c9100045f43ec8b026400ab6849c3614c80195ee9b92c68800393d4a5218d410055ac246030a641fa9e84080635040155b08282c4188263720d74d89103ef2ac288630a6454e3441d9541440090f90abb28488002b560c50d853202c5e43aa8b2462008f5878c3614c84f5ab02386c6a0802ad61275d85320046fc1aeab226000ab484594614c80b5c902aa2c4188036510c714c9401fd4ec1eebb22640087d85dd9324400b1ed03b9ac11080317d9473505100047ac3cc830a6400ae5819d1620c43f53d09a88c6a0802abe11705883102c7a40aeab2062018f581dcd608840b5cd02202c4188023de05755933202d7340ce8b10627ac9c76dcd41500090f90abb2868820aa7a0f75d913229c3e436eab122079a9e83143644c47f95cc5ba2652080333d8f725814101476412eab2220058bf8759243884055cd0db1242881e7a30cb644c9310055a40acbb2264058f687100614c8f55ad02106c6a08163d20575591320046ec384031a8200c3c65dd1624400b1790eaa2c988003271d0735891001c5e422e7b024200c3c7419563440010fb0bb82c9988028f61662191313c56bc388630a643fc9c76dd1324c103958ec3a26490816b321932cc52100536c28e8b106200d94741c5324c0015a90c99662880063d60676cc9100061e3aee8b122000c5c75d8d605040147b0b316c8988023761c20d8d410061fb2ee8b1a2000a3f855c3644c8f153902aa0c6a08031bd977258d100051ec2e43b22627acd7631c56250cf1d28623a2c78800335dcc7158d200047ac3cca30a6400c6c72d9564440011eb0e280c299003a9191721853200557420e0b1062018f4815d932c400917f0eaa6c8908121f21576cc9101a54f436c899262018be86dd1325000187eea3a2c4880031b1d47258d100064e3a6e6b1a4254c3f41dd560904090fd0bbb284881531d1c7654c9100062e328e6b12207ae5651d4763504011bf06bb442a000e2f211764c9100064eb28e6a0a80008be87d91624c4d133906ba442a0002b560e40185320062e3a8e6b122000ae582d4c614c8031b906bb28398002ab60850d91323c6e9b00e6a0a2000a7685dc3614c80b9c8e2b1284189fb3518f714c9412ed5b40c61b226200a5d8318b654410553f08b18c6a100327190735912104c6e41aeab24422a8f7815d932c40018dae4396ca88002a76132118d410055bc0acbb226400c3c75dd16
  | 6 => 0x2c7a40aeab106200a9d8414363504018eaeba8ec299026b3a0c505883102e7238ac49962000ab684140614c80317b093b664a01fb9594f53d85320046fc1aeca1a2000ab584147614c801d18c5b2264988023de1d61185420243f42eeca1a2000ccf731c96444001c68c9b2a8288002a761353d8d4104e6631ae418a4000e976410f614c8011bf06bb264880163d20575591200043f438cab22201fa9e8488063504f559f03a1ac418802ae20165d91320046fc1aeab244254a79801d3654400b1d90ea92c4188122f21d545911000572c10a030a647ead6831c3614c80117d0e322c099003b14cb21d85304174621ee8b106278d94641cd41c40559c8c5b8a64988031bdd6755883113e4e326e6a0a6278ad681080635040917f0eaa6c89000359195720c5100045fc22eca1a20018f8805d563484011f700baac8990023d606764c94002c76432e521a4200ad58114063504015cb02202c41880365dd0714cb31006abb28e6a0a2000a5e8390b654400153f00aa0c6a080297a1662d8d411547bc0ae7b024200e1d54940635040156b03328c899026b320d70588310047bc0aeab22641ead686d0c614c801958e5b22c098802aba0a6519131006663b26490a6000c3f75dd162440f15ad03280c6a08121f21571d894001c5f424ec98a4000c5f75d8d605044f938e9b1a64a08031719773505100074a3268630a64098dc831d9414c00193ee839ac4880d2a7211634c9100046ec3cca31a8200c9e84dcd64884010ff0abb062900021fe1571d89400064fb20e6a0a20098dc835d5644400717908baac69081739d81720c5100243f42eec992201e8f4865c8314400156b03306c89900237a1c20d8d4100c7d436e090a201ece7865c8314400b968e2b2287188029761420d8d410065bb20e2b026400ab681997644c80147f08b9eca880038bd52545883101476412ed18a8000aae82997644c48f5ab03300c6a08028fa1721d91310045ec3c61b226200ab58414761500f15ad02280c6a080317d97735911000656390c8b02620487c855c3644c4015cf02aa2c4188022fa1f52d91310047bc0aeca1a427aa9d841c363504051eb03baec89087ab9a0850185320056ac1ea830a64008f7815d9324400193cec32664988031b1c86558d100065bba6e2b1a4200ccc7218d6050401b2a8039a8388002ab61070588310062fba8e6b1220008bf87594644c80199ee6b1284188ab351db714c9300063a3aee2b2220028ee87dc9644400159d04280c6a080a3b2097650d1000477c12ec9922078ec57210c614c80117d0e106c898802a760e65191310f572c08e0b1062008f687185604c8014ed0a3a6c29900297a142018d414170f29ea7b226400a3c845cb654400195ee8392c8880022fe1d65191310243e42aed21a4000c5f65dcd62440f55af06b08c2a
  | 7 => 0x5d75d4f635044f53d08386c6a0802b360a65d8d4102c7a40aeca10620087d85dc562cc001b30e1b9a82a01ebb11c7435883104e6631ae531a8053a7a801d365440ef53d0db266498802a76122018d4102c6e43ac69962000e1f65550635041359d07aa2c418802ad61051d85430243f42ee2b16600087f855da414c00117b0e28ec8990022f61f52d91310261e3aaa8b048600e976410c614c8015e700b2ec29900a3760f75d91320061e3a8e8b1a401fc9c641cd414400155b0532ec8988263720d765091000566c10a031a82008be87191624c4010fd0fb2ac4880031d197714c91013e6a3b6e6a0a2000ae5819c1620c4011bf0eb18c688002b3a0a6518d4104c6e41aed10a807de5653d4c614c83f53d09908c6a080e2fa13735822120cea41ae818a2000c6c751c964440131bd0e100c6a08023de1d61185400146e41ae9b1260018f8805d5644c8051d904baac898002b3e0d545883102d7340c40b106278d94411cd41440010ff0ab86c89921327d8073505400fd4e422a231a827dad683900614c8011ef02bb286901eab5a0470d8d410056ac1843b0a6086e1d75550635043f53d08280c6a08121fa1770593310055bc22cbb0a6400d94741c532cc001958e8392c6880dea721163ccb100061fbaee8b1a4000ab5849c3614c8018decbb92c888002bc20165d853200667b1ae418a4041dc4435c8314400147d0a106c8988273318d720c5400055b420a3b0a6400c3d751d7644c90f8eee232ac888237a99c864185320043f43887b2a2000a9c8458c6348401998c439ac48800365d90735051002c7a40aeab266400ce4621c5624c0011ef02baac690802a7a0e42d91100045fc22eca1a4254c3d41dd560904131b906baac8900ff271db744c9310055bc22c230a643fcac625ca4350001878ebb22c099177a50c77458f104b56ac1cca30a64058dc8758d32904010ff0abb664880022fa1c50d913204c6f43ee6b224202acc8258d32440011ef0eb08c29800317d9473591103ed6a41aa830a6400c3f75d91604c4fd5af02b18c6908167321d324c5210045ec24ec99220018bc865d1215011df0e43ba265988022f61c50d91310065a3a0e2b1a4009ace83dd1620c40156b09a8ec2a00030fdd4645813100673b10e29926000cb674d86614c81359d09a1ac418a13a310f40588310053b428c9b0a6400a9d84d4063504031bd0db9a8298002aee0165d91320166639264b0662018bd84dd7635003d9a8ec38a64980fea760c70d913202c7743ea4b10620087f855da4348001878cbba2648800335d8c714c9400064fb28e6a0a8081e8c431d1620c4f153d02aa0c6a08ffa318b744c9300055ac2021b0a6400ad58108363504bb968e3ba2c7880030f5d475d91310072bb2ec798a2095e9573d90614c87f17d0f186c899002a76121018d410
  | 8 => 0x10000380740200b0120000000303c140378000000441f0610220042704b0380301f00400003c060001ae0140300003c030000070260440000700e00c128011d00080100305a36c2a00f0000000008105c030190000580640300200623c01810004020000000002140f01a67000001821016188008020ec07812841000004260f900c0380b3080001300001c000004058040200a40180300e0400f88d0240000001908c00c0180113407c09ac30020004e8170a00640000000a2bc0c01d00421401015000028020000920000505b0980002082d0040100984400e00c0a80004c35800000072014000010060000200002015c0001302802c3100203e068001a500e0080d0070040181080201201413800004304270120003500088d39854c0b0040600380400207e38c080010060001994301608002004004078008c50060b001807206168000240080181781905c0340482208416c0203d00800802872000a0c00006170000220d300a000080160120003282200800c0980000a0640a0000040100800a00a4fc000050020080000002810c018110c00a8000020b8008008070000400200b02a0200a00326600402893020098168110480840000000401c0f85c00e000000000000081a0060400000682a0003ec1d80000002c0083903e12c1d8750061701a821002044010050040000202200000000012000010a785910c0000214d000008c58240da0440000f074028098020142f00200109000000000234000030000680e80802b0000540c80d04600c0000004215c0002600666398e4b222000a9d83143644c4019cac5b8a84189067520d74485100243f43eeab222000c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x200400c0400c01a158510f4018532006835518214063504f149497190714c9310068310d851d1620c51bc846210c714c9400fc87e61549406350401a148361464185320060761d541406350401a0c43617405883146f21188741c5324c11ba86821934318532
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x94b
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x4
  | 10 => 0x138e
  | 11 => 0x138b
  | 12 => 0x138d
  | 13 => 0x98d
  | 14 => 0x98e
  | 15 => 0x9cb
  | 16 => 0x9cd
  | 17 => 0x9ce
  | 18 => 0x168b
  | 19 => 0x168d
  | 20 => 0x168e
  | 21 => 0xa0b
  | 22 => 0xa0e
  | 23 => 0xb09
  | 24 => 0xb0d
  | 25 => 0xb0e
  | 26 => 0x1409
  | 27 => 0x140d
  | 28 => 0x140e
  | 29 => 0x249
  | 30 => 0x24b
  | 31 => 0x24d
  | 32 => 0x24e
  | 33 => 0xb49
  | 34 => 0xb4b
  | 35 => 0xb4d
  | 36 => 0xb4e
  | 37 => 0x1449
  | 38 => 0x144b
  | 39 => 0x144d
  | 40 => 0x144e
  | 41 => 0x16c9
  | 42 => 0x16cb
  | 43 => 0x16cd
  | 44 => 0x16ce
  | 45 => 0xb89
  | 46 => 0xb8b
  | 47 => 0xb8e
  | 48 => 0x1489
  | 49 => 0x148b
  | 50 => 0x148e
  | 51 => 0xcc9
  | 52 => 0xccd
  | 53 => 0xcce
  | 54 => 0x1709
  | 55 => 0x170d
  | 56 => 0x170e
  | 57 => 0xd09
  | 58 => 0xd0e
  | 59 => 0xe89
  | 60 => 0xe8b
  | 61 => 0xe8e
  | 62 => 0x1789
  | 63 => 0x178b
  | 64 => 0x178e
  | 65 => 0x94c
  | 66 => 0xb0956
  | 67 => 0x94b16
  | 68 => 0x140956
  | 69 => 0x95416
  | 70 => 0x209
  | 71 => 0x24955
  | 72 => 0x24956
  | 73 => 0x94256
  | 74 => 0x16c956
  | 75 => 0x956d6
  | 76 => 0xb8956
  | 77 => 0x94b96
  | 78 => 0x148956
  | 79 => 0x95496
  | 80 => 0x289
  | 81 => 0x1549
  | 82 => 0x1849
  | 83 => 0x14c9
  | 84 => 0x134a
  | 85 => 0x2c9
  | 86 => 0x138c
  | 87 => 0x138b16
  | 88 => 0x4b
  | 89 => 0x1396d6
  | 90 => 0xb9396
  | 91 => 0x138b96
  | 92 => 0x4d
  | 93 => 0x178a
  | 94 => 0x124b
  | 95 => 0x15c9
  | 96 => 0x12cb
  | 97 => 0x1889
  | 98 => 0x1609
  | 99 => 0x180b
  | 100 => 0x130b
  | 101 => 0x9ccd6
  | 102 => 0x9d716
  | 103 => 0x3c9
  | 104 => 0xa0c
  | 105 => 0x18c9
  | 106 => 0x168cd6
  | 107 => 0xcb
  | 108 => 0xb8a16
  | 109 => 0xa0b96
  | 110 => 0x124d
  | 111 => 0xa0d16
  | 112 => 0x150d
  | 113 => 0x128d
  | 114 => 0x178a16
  | 115 => 0xa1796
  | 116 => 0x12cd
  | 117 => 0xccb15
  | 118 => 0x184b
  | 119 => 0x28c
  | 120 => 0x58a
  | 121 => 0x148c
  | 122 => 0x18ca
  | 123 => 0x154d
  | 124 => 0x179496
  | 125 => 0x20c
  | 126 => 0x154c
  | 127 => 0x18cb
  | 128 => 0x58b
  | 129 => 0x40c
  | 130 => 0x160c
  | 131 => 0x15cd
  | 132 => 0x180c
  | 133 => 0x104b
  | 134 => 0x104c
  | 135 => 0x2d851
  | 136 => 0x25395
  | 137 => 0x240d3
  | 138 => 0x18c253
  | 139 => 0x194c
  | 140 => 0x596d3
  | 141 => 0x58253
  | 142 => 0x1796d3
  | 143 => 0x25555
  | 144 => 0x259d5
  | 145 => 0x252d3
  | 146 => 0x24593
  | 147 => 0x25793
  | 148 => 0x258d3
  | 149 => 0x178253
  | 150 => 0x24ed3
  | 151 => 0x59453
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1693
  | 6 => 3091
  | 5 => 1116
  | 4 => 11
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
  | 7 => 2*((h/571+packedAt gbK7 (62641+(h % 571)*11) 11) % 1693)
  | 6 => 2*((h/1058+packedAt gbK6 (148368+(h % 1058)*12) 12) % 3091)
  | 5 => 2*((h/414+packedAt gbK5 (65844+(h % 414)*11) 11) % 1116)
  | 4 => 2*((h/17+packedAt gbK4 (770+(h % 17)*4) 4) % 11)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe07c07e03ff01ffffffff04f918f8478fff
  | 1 => 0xf807f8007ffc1ffe0f83ff001b66e76478f27c
  | 2 => 0x7ffff80001ffffffc1fffe387078780ff8f
  | 3 => 0x7ffffffffe0000fffe000fc07f807ff03f0
  | 4 => 0x7fffffffffffff0000000fff80007fffc00
  | 5 => 0xfff800000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x28740140164125209286312a002808284384b5
  | 1 => 0xb09658022ad50b6a85a35a060962636458b25c
  | 2 => 0x102aa9a8010128d29690cd462870585805b0a
  | 3 => 0x22334eb4d1a40080e718818b407b806ad03e0
  | 4 => 0xa445c73471e39cf1c0021060dff8000376ec00
  | 5 => 0xc7800038018200c100400080ffd5d6d0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40521
namespace PEqualNP.Outside.L_meta_40521
open PEqualNP.Outside.L_meta_40521.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 5 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 91 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := bs0_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 9 := bs1_4_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 99 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := bs2_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 6 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 90 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := bs5_6_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 11 := bgb_4_0
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
theorem bgb_5_1056 : Interval gbAtlas 5 1056 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1116 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat bgb_5_864 (concat bgb_5_960 bgb_5_1056))))
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
theorem bgb_6_3072 : Interval gbAtlas 6 3072 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3091 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 bgb_6_672))) (concat (concat (concat bgb_6_768 bgb_6_864) (concat bgb_6_960 bgb_6_1056)) (concat (concat bgb_6_1152 bgb_6_1248) (concat bgb_6_1344 bgb_6_1440)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1632) (concat bgb_6_1728 bgb_6_1824)) (concat (concat bgb_6_1920 bgb_6_2016) (concat bgb_6_2112 bgb_6_2208))) (concat (concat (concat bgb_6_2304 bgb_6_2400) (concat bgb_6_2496 bgb_6_2592)) (concat (concat bgb_6_2688 bgb_6_2784) (concat bgb_6_2880 (concat bgb_6_2976 bgb_6_3072))))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 61 := block_range (n:=61) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1693 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)))) (concat (concat (concat bgb_7_864 bgb_7_960) (concat bgb_7_1056 bgb_7_1152)) (concat (concat bgb_7_1248 bgb_7_1344) (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632)))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0feeaeeeafee0a8a0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276136096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40521.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[0,5]⟩,⟨.or,[1,4]⟩,⟨.and,[3,8]⟩,⟨.or,[2,7]⟩,⟨.and,[2,9]⟩,⟨.or,[1,11]⟩,⟨.or,[9,10]⟩,⟨.and,[6,12]⟩,⟨.or,[0,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276136096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276136096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40521

open PEqualNP.Outside.L_meta_40521 in
theorem PEqualNP.Outside.L_meta_40521 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276136096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276136096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
