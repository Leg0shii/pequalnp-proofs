import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36839.Model
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


end PEqualNP.Outside.L_meta_36839.Model

namespace PEqualNP.Outside.L_meta_36839
open PEqualNP.Outside.L_meta_36839.Model
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

def SBf (j : Nat) : Nat := [8, 6, 6, 4, 7, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 84]

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

end PEqualNP.Outside.L_meta_36839

namespace PEqualNP.Outside.L_meta_36839
open PEqualNP.Outside.L_meta_36839.Model
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
end PEqualNP.Outside.L_meta_36839
namespace PEqualNP.Outside.L_meta_36839
open PEqualNP.Outside.L_meta_36839.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1073850093c020b04c40a34308018304061df43be43bc43dc439c43be42bc42de32dc32be41bc41de31dc31bf40bd40df30dd30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2400d034a18014750038000f20b0010114cc0801000000120000088008004794e438f290871e5110e3aa021c794e429b28c851e548caaca31947150328f29c832e529063ca918d394a318e2a0631c5350258a4a04d145408e2a6611c544c298a4985514530
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x1064000859865210e0e6294443831895010e146154043
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
  | 4 => packedAt s1K4 (297+((h/5+packedAt s1K4 (272+(h % 5)*5) 5) % 23)*6) 6
  | 3 => packedAt s1K3 (609+((h/7+packedAt s1K3 (567+(h % 7)*6) 6) % 33)*6) 6
  | 2 => packedAt s1K2 (156+((h/1+packedAt s1K2 (152+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffff03ffffffffffffff87ffff
  | 2 => 0xfc0fffc0fff80ffffc1ff03ff03ff81ff9ce73
  | 3 => 0xfff03fff03fff01fffe0ffc0ffc0ffe07e739c
  | 4 => 0x3ffffc00001fffff0000ffff00007f83e0
  | 5 => 0xffffc0000000001fffffffff000000007ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x844108482092040400a5245124510a8a0294a5
  | 2 => 0x2922948649215a8b2c0a522a522ad055394a52
  | 3 => 0x30a4a5121a4542b355409a889a88e5415c6318
  | 4 => 0xa2cb3a2490766cdd9a730c30ef3c41866f83e0
  | 5 => 0xc30c3c38e3878f1ee39cef3c0c30861877fc00
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaa0aaa0aaa0aaa0faa0aaa0aaa0aaa0faa0aaa0aaa0aaa0faa0aaa0aaa0aaa0faa0aaa0aaa0aaa0faa0aaa0aaa0aaa0faa0aaa0aaa0aaa0faa0aaa0aaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36839
namespace PEqualNP.Outside.L_meta_36839
open PEqualNP.Outside.L_meta_36839.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xe00000c50a58001808468000001201c800000000180000788000400040002bf43de43bd43dd439d43be42bc42de32dc32be41bc41de31dc31bf40bd40df30dd30
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x2000502c003040038069129880000247552438e292871c5150e3ea0a1c754c428faa4651d540ca3aa620c7d52318eaa0631d53d023aa9984755130
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xb010085987548ca0e62d523183189544c2146155130
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
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
  | 4 => packedAt s2K4 (302+((h/5+packedAt s2K4 (272+(h % 5)*6) 6) % 37)*6) 6
  | 3 => packedAt s2K3 (371+((h/4+packedAt s2K3 (351+(h % 4)*5) 5) % 22)*5) 5
  | 2 => packedAt s2K2 (155+((h/1+packedAt s2K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3ffff83fffffffc0fffc1fff83fffffe78f1ff
  | 1 => 0xc0ffffc0fff83fff07ffe0fffc1fe07f9f3e73
  | 3 => 0xff03ffff03ffc1fff83fff07ffe0ff81e7cf9c
  | 4 => 0x3fffffc0001ffffc00007ffff0001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4108888209210402948094901292a282850a5
  | 1 => 0x922911064920608b02952092a4124154932652
  | 3 => 0xa4a22121a44031550265204ca409505458b18
  | 4 => 0xacb3c4a49076b5e69cc318c7739c0619f80de0
  | 5 => 0x30c38738e38739f8e73b9ce063181861fef000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xee88ee88ee88aa88ee88ee88ee88aa88ee88ee88ee88aa88ee88ee88ee88aa88ee88ee88ee88aa88ee88ee88ee88aa88ee88ee88ee88aa88ee88ee88ee88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36839
namespace PEqualNP.Outside.L_meta_36839
open PEqualNP.Outside.L_meta_36839.Model
def s3K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*3) 3
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (4+((h/1+packedAt s3K3 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 2 => 0xefbc
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 2 => 0x1828
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 7 s3Pos s3Neg, 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36839
namespace PEqualNP.Outside.L_meta_36839
open PEqualNP.Outside.L_meta_36839.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x3e0000600000000000d023a0160406796ae1a311a62a65288383921b00003800001489281400b624000a009c0004000018024402f2ca098054491001e84bb0000002b0000001830a0400c10001810a00000ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x138769d001780000000c800000000000000000000000019c000000058000000000f40000000964d390005800480003000000000026351b80000002912c782c9108000288000000418746a4f00044004712930e6000023c001b4fa2502001ba2826523b1acfa5a000012600219dd0e8e1c270d200070b4344200000cc7c4a0e47c1e0f8a542414d800c488110009400000011a003184800792d8c00000000000000008000000000080000000f0e22700218ac002f8700000001f800000c80000002e000002e4a94c0000000010a0000190008200001342a08000004619914002418a644000000d8000000000000002001460000000003f48800743424800aea242000d800378001200001fc00000000c0000038000000001200000000000070001d442000002800002c15418000001400980a800006100000468c1e83c002b00000000040180f6684b800e8280002ca0650005c100636a481a5d1795140004f22c28000000200008141c000100c0000008080200010080002000141400018000000008000001008040004018040001000001200008000200008000002000040600004f94e439ea94873e5190e7aa121db94843b6a90873e5310f3ca621eb948439ea9087ad5210e5aa421cf944439ea80873e53d0a7ca3a14f543429eaa4855e5390abaa7214f14d42d7a92853c5150a7ea0a14f95042af298855d5310a7ea9994f15332cf21e659c43ccb3ea9996715332cfa16659d42cca7ca9194f55232aea9c65ad428ca7ea8994f15132cf21a659c434cb5a849967d5132ce2a265cf524cb3e84997390932cea1265cd424cb1a84994f950329eaa0655e530cabca720d754e419f29c839e539063ca720e754e419ea94839f329073a6520cf946419ea84833e531067aa420e7cc841ce990833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918cfd51319e2a2639c434c67ea818cf150319f2a6433d54c86bca790d754f219faa4433c548879a6510cfd51219e2a2433e540867aa810d794c21aea9843cd32086f4a010de540219f29e813d52d033e65a0674cb409f28e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409fa92819f325033a64a04f14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f20e6996413e548827aa9104f951209eaa241cd324827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xe0e1e00edd0b288daac20484af4c10002520121700ac6b26c5800000a8025321c01d420000f50c401a0a88a8000d00130c3840014dcda76680018604568300057390030f800024048270000302000028a00141810000600c394d5210f0e63548438798e51d0a1c63543428d98754cca8d62d5332a598754cca8d62153328b195424ca8d6490932a3995424ca8c6550932a3185424ca8f60509329358a539062d6294e41a358a539070e6294e418758a539070d6294e418358a539061f65cca4187d95329070d524c8418718d501068d6210f31c310d52cc68d6210d318798f540c62d62150318e580540c61e63d5221c3d51328861e63d5121c355132087493254021c354932d021e639474093588535022d6214d40a3588535030e6214d4087588535030d6214d4083588535021c65cc94087195325022d6215330a3588438c21d6510c30a3588430c30c4354830c510d510c30d544cb208718d548821c63551208d185544830d544c9208798f54c421c6355210
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8a0404c70240419c4282b8cc6a9087219c6655093281ae431aa020c0d7298f5448606b94c728e81415c84354430818ecaa26490504715513248206b94c7aa621035c86355210
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => packedAt s4K5 (912+((h/16+packedAt s4K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s4K4 (4950+((h/55+packedAt s4K4 (4455+(h % 55)*9) 9) % 316)*9) 9
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 80)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 1 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 2 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 3 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x14000408402040004402404802504088045045
  | 1 => 0x212108848148040a0a20841220849414312512
  | 2 => 0x421251102a9220d4a1112a8554092941828a28
  | 3 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36839
namespace PEqualNP.Outside.L_meta_36839
open PEqualNP.Outside.L_meta_36839.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x493009c2003aa109b305411e0094585188d32c40418241a0000028005195a440071c180005400f80245ce0300ac001002188f0059480348802e5e0a1c20a060030100040801234000ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x7e6f24958046c418681e84469cd42910da4ce08f0014c6e002e1a9380950074ea000015110170018884660023000003f0d914260880070000006094760419460151625000004a9780000300d1205d4280064330389c0048338700c002f91d302818a38325210000023a32138725b00000d6780028c006d2d22488040010c427d0013c00921ea683c9f051dc481f43100206e4b154063c229f0d046158505c000000000233c9a44a0006984e4993a140187f00104b200001e8263e1da900000000000081459305e0002888e2000012d449b00000000b000009a00000010e001aa0852000b0393c12401ec00512c0005a2a2b98d3a97038c0004000388020100830003060380838301800081820000838081858700008003048a09018280840402078300008109000681840003cf94e439ea94873e5190e7aa121db94843b6a90873e5310f3ca621eb948439ea9087ad5210e5aa421cf944439ea80873e53d0a7ca3a14f543429eaa4855e5390abaa7214f14d42d7a92853c5150a7ea0a14f95042af298855d5310a7ea9994f15332cf21e659c43ccb3ea9996715332cfa16659d42cca7ca9194f55232aea9c65ad428ca7ea8994f15132cf21a659c434cb5a849967d5132ce2a265cf524cb3e84997390932cea1265cd424cb1a84994f950329eaa0655e530cabca720d754e419f29c839e539063ca720e754e419ea94839f329073a6520cf946419ea84833e531067aa420e7cc841ce990833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918cfd51319e2a2639c434c67ea818cf150319f2a6433d54c86bca790d754f219faa4433c548879a6510cfd51219e2a2433e540867aa810d794c21aea9843cd32086f4a010de540219f29e813d52d033e65a0674cb409f28e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409fa92819f325033a64a04f14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f20e6996413e548827aa9104f951209eaa241cd324827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xec0281ec069a004c000001d7a16a39b0252b9515000002c00c401d720119f1078e26000000522041b34480d9400000242401d104e182003094b996e01a0a122d90c56e0b2d000804184080c102021800e06143860000183c394d5210f0e63548438798e51d0a1c63543428d98754cca8d62d5332a598754cca8d62153328b195424ca8d6490932a3995424ca8c6550932a3185424ca8f60509329358a539062d6294e41a358a539070e6294e418758a539070d6294e418358a539061f65cca4187d95329070d524c8418718d501068d6210f31c310d52cc68d6210d318798f540c62d62150318e580540c61e63d5221c3d51328861e63d5121c355132087493254021c354932d021e639474093588535022d6214d40a3588535030e6214d4087588535030d6214d4083588535021c65cc94087195325022d6215330a3588438c21d6510c30a3588430c30c4354830c510d510c30d544cb208718d548821c63551208d185544830d544c9208798f54c421c6355210
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1400000202000818047324128282b8cc6a9087219c6655093281ae431aa020c0d7298f5448606b94c728e81415c84354430818ecaa26490504715513248206b94c7aa621035c86355210
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (912+((h/16+packedAt s5K5 (800+(h % 16)*7) 7) % 67)*7) 7
  | 4 => packedAt s5K4 (4895+((h/55+packedAt s5K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s5K3 (2420+((h/20+packedAt s5K3 (2280+(h % 20)*7) 7) % 80)*7) 7
  | 2 => packedAt s5K2 (505+((h/3+packedAt s5K2 (490+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 1 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 2 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 3 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 4 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x14000408402040004402404802504088045045
  | 1 => 0x212108848148040a0a20841220849414312512
  | 2 => 0x421251102a9220d4a1112a8554092941828a28
  | 3 => 0xb556225281aa96733542207992c0c45d80f80
  | 4 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36839
namespace PEqualNP.Outside.L_meta_36839
open PEqualNP.Outside.L_meta_36839.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1c000340140000880004924000000114000000170000000000c0003b095c000000063a7c68b004600f0000000000000002aa000003a00000000000058200009a028800000fcc380005280d610a4000058000150032000000000000609000000000009400026300144e0052a108e00000440000000027800000000b40005c90c803c6ee50b8015805d0118036014e5800000d80000000040000001408000000080008040004000c0000040005fe54007f55005fc54017fd0c01fe43006f90c01fd43017f10c01bc43017fd0801fe42007f50805fc42007fcc801fe32007f4c801fc32017fd0401fe41007f50405fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc2100ffd0003bf4000ff90003fd4000ef50003fc4000ffcc003fe3000ff4c003fc3000ffc8003fe2000ff48003fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c4200ff90e210077c8710803fd4388415fe21c4200ef10e2103dfac51082bff4288409ff2144200ff50a21027f88510803ff3288409ff1944200ff4ca21027f8651080efe6188407ffa0c4203ff9062101ffa831080ffc4188407ff98c4203ff8c62101ffa631080ffc3188407ff90c4203fbc8621027ee431080fff60884077fb044203ff9822100dfcc11080ffd60884137eb044203ff1822100df8c110827ff4088413dfa044209ff9022104ffa8110827bd4088413fe2044209ffcc22104ffc6110827fd3088413fe1844204ffc822104ffc4110827fd2088409fe1044203ffc422101fee211080ffe1088407fe8844209fd4422101ff82110803ff64484017fb224200efd91210057ec890823fe64484057f3224200ff59121005fac890823fc64484057e3224200ef1912101578c890823fe5448401feaa24208ff15121007fec690802ff6348401ff31a4200bf98d21007fac690802fd6348401fe31a4200bf18d21047fe8690803fe4348401df21a4200ff50d21047f88690803bc4348411ffa124204ff90921007fa8490813fc4248401ff9924204ff8c921007fa6490813fc3248411ffa0a4203ff90521007fa829080ffc4148401ff98a4203ff8c521007fa629080ffc3148409ff90a4204fdc852101ffc429080fee214840fffb024207bfd812103ffcc090806fe604840ffeb024207bf5812103ff8c090806fc604840fffa024207efd012103ffc809081ffd404840fdea024207ff1012103ffe609081ffe304840ffe9824207ff0c121027fe409081fef204840fff1024207ff4812103fda4090813fc2048407ff8824207fdc412103ffc209081ffd104840ffa8824203ff0412101ffec81080eff6408407ff3204202bf9902101f7cc81080abe6408407feb204200bf5902101f7ac810802bd6408407fe3204203bf19021037fca810803fd540840dfe2a04203ffd8c2101dfec61080ffe63084017f3184203f798c21005bcc61080ffd63084017eb184203f758c21005bac61080ffc63084077e3184206ffd0c21007fc8610803be4308401fea184206ff10c21007788610812fe6208409ffa104204ff90821027fa8410813fc4208409ff9904204ff8c821027fa6410813fc32084077f3084203ffd042101ffc821080ffd4108407fe2084203ffcc42101ffc621080ffd3108407fe1884203ffc842101fde421080ffe2108407fb1084203ff4842101fda4210813f52108407ffb004203bfd802101ffcc010806fe6008407fd3004201be9802101ffac010816fd6008407fcb004200be5802101ff8c010806fc600840bffa004205efd002102ffc8010817fd400840bdea004205ff1002102ffe6010817fe300840bfe9804205ff0c021027fe4010813fe2008409fe9004204ff0802101ffe201080ffe1008407fe8804203ff04021
  | 1 => 0x7fe544c401feaa26211ff1513108ffe8698803fe434c401df21a6200ff50d3108ff88698803bc434c401ffb126200bfd8931007fcc498803fd624c401fe3126204bf1893108ffe8498803fe424c401fea126211ff10931007fe6498803df324c401ff1926200ff4c931007ba6498803fc324c423ffa0a6203ff90531007fa829880ffc414c401ff98a6200fdcc53101ffc629880fde314c421ffb026210bfd8131087fcc098806fe604c421feb026210bf58131087f8c098806fc604c421ffa026210efd0131087fc8098843fd404c421dea026210ff10131087fe6098843df304c421ff1826210ff4c131087ba6098843fc304c421ff9026210ff88131087fa4098843fc204c407ff8826210fdc4131087fc2098843fd104c421fa8826203ff0413101ffec81880eff640c407ff3206202bf9903101ffac818802fd640c407fe3206203bf19031077fca818803fd540c41dfe2a0620fbf98c31077fe8618803fe430c401df2186200ff50c31077f88618803bc430c407ffb106203ff98831025fcc41880ffd620c4017eb106203ff18831077fe8418803fe420c401fea10620eff10831007fe6418803fe320c401fe9906200ff0c83101dfcc21880fff410c407ff2086203ff5043101ff8821880fff310c407ef9886203ff8c43101fec621880ffd310c407ee9886200fd4c43101ffec01880eff600c407ff3006201bf9803101ffac018836fd600c407fe3006201bf1803106ffe8018837bf400c41bff200620dff5003106f7a8018837fc400c41bff980620dff8c03106ffa6018837fc300c41bff900620dff8803106ffa4018837fc200c407ff8806203ff8403101ffa201880ffc100c409ffb264204bfd9321027fcc99080afe64c8409feb264200bf59321027f8c990812fc64c8419ff2a64200ff55321067f8a990813ff63c84097fb1e4204ff98f21005fcc790813fd63c84017eb1e4204ff18f21025f8c790833ff43c8401ff21e4200ef90f21007fa8790833fc43c8401de21e4204ffd0b21027fc8590813fd42c8409fe2164204ffccb21027fc6590813fd32c8409fe196420cffd072101ffc8390803fd41c8407fe20e4200ffcc72101ffc6390803fd31c8407fe18e4204ffd8321025fec190813fe60c84037f3064204ff5832105dfac190813fc60c84037e306420bffd032105f7e819082ffe40c8417fea06420bef5032105ff8819082fff30c8417ff186420bff4c32105ff86190813ff20c8409f79064204ff88321027fa419082fed20c8409fe1064203ffc432105ffc219082ffd10c8407fe0864203ffd922101dfec91080ffe64884057f3244203ff59221005fac91080ffc64884077e324420aff95221007faa91082bfc5488407ffb1c4203bfd8e2101ffcc710802fe6388407feb1c4200bf58e2101ff8c71080efc6388415ffa
  | 2 => 0x410b7f8a6a08037c5350405ffa1a8202ff90d410077c86a080bfd4350405fe21a8202ef10d41007fec4a0802ff6250401ff3128200ff58941007f8c4a0812fc625042dffa928200ff94941007faa4a085bfc5250405ffa128202efd0941017fc84a080bfd4250401dea128202ff10941007fe64a0803fe3250401fe9928200ff0c941015fec2a085bff5150407ff28a8200ff5454101ff8a2a080bff4150405fba0a8203ff9054101f7c82a080ffc4150407de20a8202fd105410affec0a0856ff605042bff3028201bf981410affac0a0856fd605042bfe3028201bf181410affea0a08577f505042bff2828215ff541410aefaa0a0857fc5050405ffa028202efd0141017fc80a080bfd405042bdea028202ff101410affe60a0857fe305042bfe9828215ff0c1410affe40a0857fe205042bfe9028215ff0814101ffe20a0857fe105042bfe8828203ff04141007fec998802ff64cc429ff3266202bf99331007fac998802fd64cc429fe3266202bf193310a7fca998803fd54cc429fe2a66214ffd0f31007fc8798803be43cc401fea1e6214ff10f31007788798803ff62cc401ff3166204bf98b31007fac598802fd62cc401fe3166214ffd0b31007fc8598803fd42cc429fe2166200ffccb31007be6598803fe32cc401fe9966200f74cb31007f86598853ff41cc407ff20e6200ff5073101ff8839883fff60cc41f7fb06620fff9833100dfcc19883ffd60cc41f7eb06620fff1833100df8c19883fff40cc41fdfa06620fff9033107ffa819883fbd40cc41ffe206620fffcc33107fbe619883ffe30cc41ffe986620ff74c33107ff8619883fff20cc41fff106620fff4833107ff8419880fff10cc41fff086620fff4433101ff8219880fff648c4077fb246203ff99231015fcc91880fbe648c4055f3246203ff59231005fac91880fbd648c4015eb246203ff1923101df8c91884ffe548c401feaa46213ff15231085fac71884fff438c401ff21c6200ef90e31007fa871884ffc438c401de21c6203ffd8a3101ffcc518812fe628c407feb146200bf58a3101ff8c51884fff428c401ff2146200ff50a3109ff88518803ff328c401ff1946200ff4ca31007f8651880efe618c407ffa0c6203ff9063101ffa831880ffc418c407ff98c6203f7cc631007ee631880fff608c4077fb046203ff9823100dfcc11880ffd608c4257eb046203ff1823100df8c11884bff408c425dfa046212ff90231097fa811884bbd408c425fe2046212ffcc231097fc611884bfd308c425fe1846212ffc8231097fc411884bfd208c425fe1046203ffc423101fee211880ffe108c407fe8846212fd4423101ff82118803ff644c4017fb226200efd91310057ec898847fe644c4057f3226200ff59131005fac898847fc644c4057e3226200ef1913101578c89884
  | 3 => 0xeb0a6400ff1853201df8c29907bff414c83dfe20a641dffd81320edfec099077fe604c8037f302641dff581320edfac099077fc604c8037e302641dffd01320ef7e8099077fe404c83bfea02641def501320eff88099077ff304c83bef982641dff8c1320effa6099077dd304c83bfe1826404ffc81320efde4099077fe204c83bfe902641dfb48132027f84099077ff104c83bff082641dff441320eff82099013ff640c8097fb206404ff99032015fcc819013fd640c8017eb206404ff19032025f8c81906ffe540c801feaa0641bff150320e5fcc61906fff430c801ff2186400ef90c32007fa861906ffc430c801de2186404bf98832027fe8419013fe420c809fea106404ff10832027fe6419013df320c809ff1906404fb8c832027fa6419013dd320c801f69906404ffd8432027fcc21900efe610c809feb086400bf58432027f8c21906fff410c837fe2086404ffd8032025fec019013fe600c8037f3006404ff580320d5fac019013fc600c8037e300641affd00320d77e801906bfe400c835fea00641aef500320d7f8801906bff300c835ff180641aff4c0320d7f86019013ff200c809ff1006404ff48032027f8401906bff100c835ff080641aff440320d7f8201900fff65904077fb2c8203ff996410bdfccb2080ffd65904017eb2c8203ff1964101df8cb2080afd6490405ffaa48219efd5241017fca92080bfd5490405fe2a48202ef1524101ffec72080ffe63904017f31c8203ff58e41005fac72080ffc6390433ffa9c8200ff94e41006fca720803fd5390433fe29c8200df14e41017fe872080bfe4390401df21c8202ff50e41017f8872080bbc4390407ffb148203ff98a41025fcc52080ffd62904017eb148203ff18a410cffea520803fe5290401fea948219ff14a41017fe852080bfe4290401df2148202ff50a41017f8852080bbc4290401ff9948200ff8ca41007fa6520803fc32904077f30c8203ffd464101ffca32080ffc5190407ffa0c8203efd0641017ee832080ffc4190407fa20c8203ffd824101dfec12080ffe60904037f3048203ff582410c5fac12080ffc60904037e3048218ffd42410c6fea120863fe5090431fea848218df542410c7f8a12080bff4090405dfa048202ff90241017fa8120863bd4090405fe2048218ffcc2410c7fc6120863fd3090431fe1848218ffc82410c7fc4120863fd2090431fe1048203ffc424101ffc212080ffd1090407fe0848200ffd9541005fecaa08037f65504013fb2a8216ff995410bdfccaa0803fd65504017eb2a8216ff195410bdf8caa08037c655042f3e32a8203bfd9141017fea8a080bfe5450405df2a28202ff551410077aa8a080bfc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8200bf18d410b7fea6a0803fe5350401bf29a8200ff54d
  | 4 => 0xbfe4350801df21a8402ff50d42017f886a100bbc43508057fb128423ffd4942027fca4a1003fd5250809fe2928402ffd0942017de84a1013fe4250809df2128404ff109420277884a100bec4250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8403bf1854211ffea2a108ffc5150805ffa0a8402efd0542017f882a108bff60508457fb028422ff9814200dfcc0a108bfd60508457eb028422ff1814200df8c0a108bff5050845bfa828422ff94142117faa0a108b7d5050845fe2828402ffd01420177e80a100bfe4050805fea028422ef50142017f880a108bff3050845ff1828422ff4c142117f860a1013ff2050845ff1028422ff48142027f840a108bff1050845ff0828422ff44142117f820a1003ff64cc8017fb266421ff99332015fcc999003fd64cc8017eb266421ff19332015f8c999087fe54cc801feaa66421ff1533210ffe8799087df43cc801ff21e6400ef90f32007fa8799087fc43cc801de21e6421f710f32007388799087ff42cc809ff2166400ff50b32027f88599003ff61cc801ff30e6403bf98732007fac399002fd61cc801fe30e6421ffd073210ff88399073ff60cc8397fb06641cff9833200dfcc199073fd60cc8397eb06641cff1833200df8c199073ff40cc839dfa06641cff903320e7fa8199073bd40cc839fe206641cffcc3320e7be6199073fe30cc839fe986641cf74c3320e7f86199013ff20cc839ff106641cff48332027f84199073ff10cc839ff086641cff443320e7f82199013ff648c8097fb246404ff99232015fcc919013be648c8055f3246404ff59232005fac919013bd648c8015eb246404ff19232025f8c919083fe548c801feaa46420ff152320edfac719083ff438c801ff21c6400ef90e32007fa8719083fc438c801de21c6404bf98a32027fe8519013fe428c809fea146404ff10a32027fe6519013df328c801f79946404ffd8632027fcc31900efe618c809feb0c6400bf58632027f8c319083ff418c841fe20c6404ffd8232025fec119013fe608c8037f3046404ff582320fdfac119013fc608c8037e304641fffd02320ff7e811907ffe408c83ffea04641fef502320fff8811907fff308c83fff184641fff4c2320fff86119013ff208c809f79046404ff88232027fa411907fed208c809fe104641fffc42320fffc211907ffd108c83ffe0846400ffd9132005fec899003bf644c8015fb22641eff99132015fcc899003fd644c8017eb22641eff19132015f8c899003bc644c8055e322641eff95132007faa89907bfc544c83dffa1a641ef7d0d32007fc8699003be434c801fea1a641eff10d3200778869907bdc434c801ce21a641effd0932027fc8499003fd424c809fe2126400ffcc932007de6499013fe324c809ef1926400ffd8532005fec299003fe614c801f
  | 5 => 0x8943005fec4a1803fe6250c01feb128600ff18943025f8c4a18abff5250c55fe2928602ffd0943017f884a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c077e30a862affd4543157f8a2a180bff4150c05fe20a8629ffd814314dfec0a18a7fe6050c037f3028629ff5814314dfac0a18a7fc6050c037e3028629ffd414314efea0a18a7fe5050c53fea828629df5414314ff8a0a180bff4050c05dfa028602ff90143017fa80a18a7bd4050c05fe2028629ffcc14314ffc60a18a7fd3050c53fe1828629ffc814314ffc40a18a7fd2050c53fe1028629ffc414314ffc20a18a7fd1050c53fe0828602efd94430177cca2180bbd6510c05de3288602ef98c431457cc62180b9e6310c4fdfa988600ef94c430067ca621803bd5310c4fde2988600cf14c430177ec42180bbe6210c05deb108602ef1884313f7ea42189fbc5210c05dfb088602ef984430177ac22180bbc6110c4fdfa888627ef144430177ec02180abf6010c05df3008602ef580431357ac02180bbc6010c4ddfa808626cfd40431377ca02189bbd5010c4d9ea808626ef140431377e602189bbe3010c4dde9808626ef0c0431377e402189bbe2010c4dde9008626ef080431377e202189bbe1010c4dde8808626ef04043027fecb21012ff6590809ff32c8417bf99642026fccb2105e7e6590809feb2c8400bf59642026facb210027d6590809fe32c8404bf19642015fac92100bff5490805ff2a48402ef95242017faa921003bd5490805fe2a48404ffd8e42027fcc721002fe6390809ef31c8400b798e42027fac721002fd6390809eeb1c8400b758e42027f8c721097ff5390801ff29c8400df94e42007faa721097fc5390801be29c8402ffd0e42017fc8721003be4390805fea1c8402ff10e42017788721012fe6290809ffa948404ff94a42027f8a521013ff4290809dfa148402fbd0a42027f88521013ec4290809ffb0c8404ff9864201dfcc321013fd61908017eb0c8404ff1864212ffea321097fc5190805ffa0c8402ff10642017788321013ff60908097fb048404ff9824200dfcc121013fd60908497eb048404ff1824200df8c121093ff5090849bfa848424ff94242127faa1210937d5090849fe2848402ffd02420177e812100bfe4090805fea048424ef50242017f88121093ff3090849ff1848424ff4c242127f86121013ff2090809ff1048404ff48242027f84121093ff1090849ff0848424ff44242127f82121003ff65508017fb2a8423ff995420bdfccaa1003fd65508017eb2a8423ff195420bdf8caa1012ff6450805ffaa28423efd5142017fca8a100bfd5450805fe2a28402ef15142007fec6a1002ff6350801ff31a8400ff58d42007f8c6a1002fc6350847ffa9a8400ff94d42006fca6a1003fd5350847fe29a8400df14d42017fe86a1
  | 6 => 0x80180000000200000080100080aff6455005ff2a2a802df95154017f8a8aa00bbc54550059e2a2a800ffd8d54005fec6aa003fe6355001feb1aa800ff18d54005f8c6aa00bff4355005fe21aa802ef10d54007fec4aa002ff6255001ff312a800ff58954007f8c4aa012fc6255005ffa12a802ff109540177884aa003ff61550017fb0aa800ff98554007fac2aa003fc61550077e30aa802ffd05540177e82aa00bfc4155059ffb02a82cbfd8154167fcc0aa006fe6055059feb02a82cbf58154167f8c0aa006fc6055005ffa02a802efd0154017fc80aa00bfd4055059dea02a802ff10154167fe60aa0b3fe3055059fe982a82cff0c154167fe40aa0b3fe2055059fe902a82cff08154167fe20aa0b3fe1055059fe882a82cff04154007fecb21802ff6590c57ff32c8617bf99643007facb21802fd6590c57fe32c8617bf19643015fac92180bff5490c57dfaa48602ff952430177ca92180bfd5490c01deaa48602ff1524301778a92180afe6390c57ffa9c8600ff94e4315ff8a72180bff4390c05dfa1c8602f7d0e43017f8872180bdc4390c01ffb148600ff98a43025fcc521803fd6290c017eb148600ff18a4315ffea5218affc5290c05ffa148602efd0a43017f8852180bbc4290c01ffb0c8600ff9864301dfcc321803fd6190c017eb0c8600ff1864315ffea3218affc5190c05ffa0c8602efd0643017f8832180bbc4190c51ffb048628bfd8243147fcc121806fe6090c51feb048628bf58243147f8c121806fc6090c51ffa848628dfd4243147fca1218a3fd5090c51bea848628ff14243017fe812180bbf4090c05ff2048628ef90243017fa81218a3bd4090c05fe2048602ef10243147fe61218a3fe3090c51fe9848628ff0c243147fe41218a3fe2090c51fe9048628ff08243147fe21218a3fe1090c51fe8848628ff042430077ecb218afbe6590c01deb2c862bef196430157cc7218afbf5390c01df29c8600cf94e4315f78a721803bf6290c01df3148600ef58a4300778c5218afbf5290c57de2948600efd86430077cc321803bd6190c01de30c862befd464315f78a3218a3bf6090c515fb048628ef982431477ac1218a2bd6090c51de3048628efd42431467ea1218a3be5090c51dea848628cf5424314778a1218a3bf3090c51df1848628ef4c2431477861218a3bf2090c51df1048628ef482431477841218a3bf1090c51df0848628ef44243147782121803ff6550c017fb2a8600dfd9543004fecaa18abfe6550c2f7f32a8600ff59543005facaa18abfc6550c2f7e32a8600df195430bcf8caa180aff6450c05ffaa28602ff95143017faa8a180bfc5450c057fb1a862affd4d43007fca6a18037e5350c01fea9a862aff14d43017fe86a180bdf4350c05ff21a8600ef90d43017f886a180bbc4350c05ee21a8600ffd
  | 7 => 0x2ca01700000000e1900000000000000000000000003df0000000f30441842074f20003a419e80058a00000000016000000000100000000180380700180200080180400080200080400100080180000000000080080900080100280200080200180180000100080000000080000000000000480200080100000080000080200900080100200100380200180000280500580f00000200000000000280000300000080000000000300180080100700000700080380000180080000380300500080000180080000080080000080100000000280000000080300080000100180000180080280080000000100080000180000500400080100180100100100000080180200080080000180180300100100100200180200080400200000480100000100280000500000f80000000600080000000480000000100000000100580400080680b00200700100000080080000000000100080000080000000080700680280200180300000000000000100880180000000100000080180380100180300100180080180080000480180200700000080180000000100080080080300000300180080080080180080100100e80500100000000500680280600100080000180280180080100380000000100080000580000000080280b00080080080200100900c80280180000200280080880000100080000700300100000180000080000000480280000100000380080400280000080080300200480100600300080200180100080100080080500080000180100200300100000000180080180280180100180300000380080080400000000300280280000080000000080080080080080000000000100080080000001080000680200380080000000180200000000100000380000180080000080000000200200d00100000100100000080000480000000780280080000100300080000900000080080000080000080600100000080a80100080080280100000080100000080080380000000000100100000080080080180000080180080400480000100380000100380100400180200080100180400100600180200680080000000380900000000280280380480880380000180000180180000080080280000a00000180000000280380300000100280b80180000100100300100080080080200000100280080000000f00100280000100200480080000200000000000180080000380480180080280100000080000100000280100280000a80000001900b80000000000000080080000000000080380180000500180080000000000000000600280080000400080000080080280480080280000000100000000100180000500000080100300100000080080000000100000000180000f00200800000200080b8030008008040060000020000008010020008018000010040008
  | 8 => 0x3f92553849295b9242ddc8e8b2844917c0338004a71575f60000000002c837e25858c00049c0000003133809e721a45780043d00000000000053f09d0000000000a45be43700000000011200053e00000039080038d9d6d853af00000021d00000000000024a8000d127db4d53a2511c20e9def1dd00048f100d830000ac2088004ba8000000000000004c22f04020000000000005070004414bb4b900ea092fd14e2e35eb8000003990000001b680000010900000000041080000000055d4ac0000000001334ed0005090000003458000ec5d90000114791fe80000002b0d71ef21800000058200016a2f51985a258e3fb0f0cdc000000147c7b0051483784f10735d7122c049191a8a1f3973d50000000000ed80844e1a40275544eb1f842e00000012f04eb3c8000000693888003372ce00000000055715a19e0001fc45d00002400017d54c3c9a2180009a5e938c8000000000005d651632d000296c3900000012000129434720650b00015626f5ead3d0005e60000005500005e0000000000240ae70000000000000bb3042d40002360003005910000000000003c0800142a3880035280000046c1cb43600038e37a1f20000001970002293ea56f00000047d3560000000000002714290001c44130003b516c3d240e54737b51322c8000f04b318a00011c3cf5385b40c42a40000000000000daaa20000004500000000000cc80000000056952a0000000001b205100026a5dd9a62990005bd5ab19180000034113180016213285b0a580000033a4850000003248000004aa00000025a00000000000000000029880000000000044600000024c03b4a10003d89a156300000000000000000000013f2a800025c00000008a8003f332e35000000006bd650000000000000000000001762d000019d4ee13d60300042000000022f288df45185fe95b0003c50a72c20003acbbe3f600012608b4cf4c51f73dd247c1e00000000009e18c8000000000000000000360000000001be00000000030704a12431f8000003580000490003431d60e93b60000000005c1414dad13c1b40005a908883a957d6a5bf14600034cbecc05c890001004b625e20aa0220300a3d180008180035100041d00023257443a000541000000385a122dfc2704d92d0003925e500000040600000000019a0530a11aa0dcd590000000000000003a780c01300000000000000000033e00000000000000000000000000000017a0005f54de1581304be58805e266000000297606401a3a1883c700054412fbf89b02693023bb050143d000000000d3a8206731c0000d01852890000000002b70000000000000000000000000000c300000000000000000059831a00000000042a0ca00000027800008508f0003c25420620a826e41135343e00000047223d1ca06b087df11752f800
  | 9 => 0x3783500038f0000004d000000000000000000022e80015200000000004d190d3bb0b08156c5ac0703659b38a3afcca915c415be759d3fd25d484323cd71fd9a93a909f2b33429ab800000173c3420780000007d0000002e84a400033d36833f921bd68000002df40540a2a64ab80019f9324650003263ee8003595f01745b3000068c54b4d9bf2d621341634b4875204310000000001efa8f35d0e22ef0000dc2ec19327cd3f9ec48b4a208c15e3abb0690824cbf84c311993900004e3c6a1c4a00000001161e600012e3c100028157c0000000003291c80000001650000003c380049309241a2442341110ce0e435400050127ed620000000000000de0000000002200548000000000000000904f70002368000000000880000000004da3e981d0420e700050800000022a0e600d3938970000001950001780003b40000000005f80002cd2054732525375e45c90db9a200040700000004b0650000002f25d00000000000000155bc50c2cc0001ba80000047a0b34d144d4e74568005c300006300044300000000000034aa9660524e26548d4d40001f921fb032ff0004e10754a85b62d30b54012d91dacb004c0004e000000054800000033140fc7e00010c11d44b9a5000291057dae24d10494c130b4fad20a320e3e52220004cd06138722d1810213b80001e907eb813390000000000002ab31600000006c3fa2145115c29640003ced9f0000000000000001143e22c72880000002170001e517680000056145f000000000000000000000000000398a7a39596c80200000000050e1598001100000005fa2f443f0b75701d58ed48312527056b5f4d512e9c560003f00002105020001c3c6d38b23007f00024a00038a45c0ffb9c3e10005050003f7837b8692300f9fb2e65ea3ed1f60b9bbd48055e5250712cf2543d8069b2c0a48c60724f380011f0005f90000a000000003804101c4740003600000000000000000000000000000d980000000025b4fe6085b84770000000001f14f80d40ecabe0000000000d6a09d9560ab635b5136175a9500000046a0140004c827f23b00011b2bc03480000000000043014b00000032f25f0000000004acc171d208608fa8e4702875a10cb82c8000bf3ea80060000036f4168000000000000001d049a0fc00048a12e800000568000000243178856abb0000934af4b71b4de35fc0200002750000000fa0001a0b5e0005e1b438003742da1f34e90003d30002c508d0910002de8000004f33653ad00416ed905965ee00000000026b00000000004fce840bb9e5ec3d4cd61355531cf3ff45b3012643f51e69c0dcb0004581d95b100b000000392d355a71c28000000000000f83b20001bb960c138c7111a4639322610315355a27424903c26103105c24530c0cf1273c78be40815d36788924e80f2e08761c5
  | 10 => 0x2ae45a2353828000000005600000000000004181e78000000000000003ca396d723bf5da244a4da8302c3a10000000000003de3694420000000001128003aa0005a00a298e80019c0000000000000000003c18000005dc5f380048210702832180000000000052300000017b25900058b0000000000003cb53c0aa00019100000024209fc3c0001a052725700000000010600c8003d15cd2dd0003243d000036d0002de18300000005f00000001b3640564ca55b00018600030919b0b8b1848809dce21e00d8839000000351d940000005eb0003a99eb4ae31b28d57900016e49b54d00038c10e000534000440000256202dbb4c600049500000040f0d95de44727723845211524f26000017e5af08c8001962731a33ac2b803412da0c2e000037048c3d7b140540ea9c30003360808000000003fc00000039f4a60005ff0000000000000d58000000000000003a300000029a8000000950000001ed0095e20cdb5210b1721715771555e0d281cc0000000000005fd80029d00009b00055811700000000700000016dc154614620000005ed0f40005f58000000000460001b107700000039a55620d0003790e026334f04840794000027b2e1c570004ba49e48e3552e200028c2b40ee8003d28ad0000002a48000000004b139405800042124b248ad11423fe16800617000002980000000043551b0000002391b601055546b0005210b4000000423383b6680029e00000056700000000000034500000000000000000000034b8000000dd0000d221e1bd29b2805c60000000000003840b80003950bc06f01a0005ca00000000000000038e8005c75cf0d4a470000000000003db00000000002a2275260000000000003ba00000029300031208ea06b6b0000000002ad1441b91c680dc3837faf14e31b800050a00017bbc90000000001b580000034900057f2fa3f246600034837280059b2db0004254ce0006098f600055c0000005400960000000000000003448004c00000868000001890000000b79fb800602000083000146b1d00047c0001e88000a0a8507803216bd764f004518c3cd403cdb31f07e0593d911fc098ba3574fa57129f2a3113b984bd4b4161163b3303c9f50cc42d3cc4555d300009ed454c90000c100000004f0002110ae4040740000475aa3c8b620000005492b544c0001340003ef20ec680000000b10005e80003a50c83ff800158b890000002ac3d080000037c1ad35b055c4500003a23fa4fa20ca98000001870c50003663a700000028780037ebf70001c70000004ff4e50000000ea00000018e0000a90000000000000000000002400000000000000f10002048000000000000005f332100000000000008a00024b8000000000000000003da80006d80009c4f28000005120000004df29c4710001bec1030a1bc5332fc2
  | 11 => 0x1924c42bd1da000350c6322b1511e80000000000000000005315ecb638000000000001040000004bc1131ce5870000af5172792842984ad0ca9053c35293960b90000001798001d10000000000000000993850f75ba4092b600009858d0000004124030000000004dd0000000000fb00051d37700010f00036c08d8000005d44588000001c48000000000001940a62b00001ff49f3b90001c90000000001df26d06600037f000000433050bc45db0cb0bd00033400021b2fe0f260a54e13820400000000049000000000000000000000006800020b5ce18d5e75fe23f49435f40d0000b6a334194cb222c0c00025032003e0000005df00000000035c33000016a9459ba412c62d9200040881e0004d800000033500000034a00004002354334042c38d00003982b89cc9622e4c74540003e600000000000000016b2a153660100013153ad9a53258f0000000002f62fbd140000000e3249bd70000003e900044f00000056635a0d30ddba8581000000000053aaa00000052406a0003718001628000002a558436714f0eb1fd4a300029a51e21ddde8000004643ce0000220000000000000e548600000015a80044b0001210000000000000df32b4910000efa080000db2410004d53065e100000051c22857d43b52217f0a1afb28600030507a0000003e400006c9bc8005d500000008b80000027d00014923c50f31500054f3900004d30001e20873eb5d85b013a604089a011af2721e40002372000000001c60003d42bf364a8a1b298f8000000000ab0000000003ae12c41b1fc80034180012b2b11410d63228002058000004811d300007fac11b33115a45d100021952b00012080003b8004d216f00045e42215f4e45190003edb9b34200057800003d4a50fd40694521620c8000000000003d39aa9d53b1453161c0037d0000ef57534e402bbc00038980003f0000004265990000000003aad2f0ff3c580044a2d800000050600039133e8000000001a1cf659c0000328000000000004973c622321552e37527f82f09432eb7629056d5042c30001f422ba671dc0ee052a2107b31000020dcc15460000293b03862af1bf8000000000000001c18004d947800026c08214485739480019900000059e54a00000002d18209a8002764b84281d70000003c2c7642b5c0135b2718b4695a63175c25030004b500050d4e651f14742f0005f21011593b6800000174a2c2cb0000000000b62eb2f957580013b0004ec49258631e4991771b714a30e3802e400040a8001a7203a1e8550843f113e4f51540e805d26241c1d9c7534618f00033b1fa8000000003d647f11e9a9aa00000002e500039d32210d41f40e903d891f033d9c12ee2922799f286e0000006070370c00000002a9000011dc800013700000000011a00000000011c8000000003a65c1d1
  | 12 => 0x16fdfb3978002f33192f8c321d89f980032d8003da1283a23e832357a0004593381661501fa11ddc44441e14fb40b12a3080000002256069029c58000000250005a50000108000000000000001693b7248038aea4fc00000000038196d3ec033411b8783599f55f57311e2dc06ac008a69de56e0000000000190000a50d85dd241b823a04144511791f18babb5a7c22dbcfd2c3ab36a0002d500004c80020a2a718da2406d02a88051a05260923e11bccc20b9e9b7d8000000003208120003320e11670000000605970cd00000000029990a000114b712b900000000000016307c0000645300000005390002fa8000000005b20002c036e52d0003eb8000c93d9da81c057e00027e0004481a807900000009b80014d1cd25346000000000034c34e8000000001b79db1ac0b5ae12f754b4ab05a3ee3a8b3c0f520f32a000346c9d4f4aea8001d43f43732c4000134d935150000003e04f40001ae0000003e30260162e930f0000da00000049817797a8001fe0fe00005182e1ee3d58000435cc1b55b74b20005d20001bd8001d80000a201f04bb610003441221f09183918f90004fd4ea0000000000000000000001021bb2d75c50000d53dc3c03cab830003881ea00000011a8000000004adddfb68dfc80000000000000057b2438005f700000000000046e00026846f0ebac95a330d1800304bf4f90000000b200000000000028b1ab0000185fd00300037200014332500000000008e0003c80005524672b233f0000b038fac60001d79e3101a35aa38005640004246089732310000c22ed00000053b0004ef1338002ba0000004bb8005800000000003b3
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7690c2101cfe7690c21004fd7690c2101cfc7690c2115e7e6590c210067d6590c21196bf6490c21016be6490c21006bd6490c21016bc6490c21006de6390c21006dd6390c21025ee7290c21005ed7290c21146fa6090c21195bf7690c2118ebf7690c21004bf7690c21196be7690c21195bd7690c21006bd7690c21004bd7690c2118ebc7690c21196bf6590c2115ebe6590c211973e6590c2115e3e6590c21006bd6590c211973d6590c210063d6590c21196bc6590c21175be7390c21196bf6390c2118ebe6390c211979e6390c210069e6390c21006bd6390c211979d6390c210069d6390c2118ebc6390c210073e5390c211b7ae7290c21007ad7290c211b6be6290c21196be6190c21197af2190c21197b62190c21197ad2190c211b7b52190c211adbf7090c211adbd7090c21196bf6090c21146be6090c21197ba6090c21146ba6090c211a6bd6090c21197b96090c21146bc6090c211a73f5090c211a73d5090c21004ff7650c2101cfe7650c21004fd7650c2101cfc7650c210057f7550c2119d7c7550c211567e6550c210067d6550c21016be6450c21006bd6450c21006de6350c21006dd6350c2114efa6050c21175bf7610c2118ebf7610c21014bf7610c21176be7610c21175bd7610c21036bd7610c21004bd7610c2118ebc7610c21176bf6510c2113ebe6510c211773e6510c2113e3e6510c21006bd6510c211773d6510c210063d6510c21176bc6510c21195be7310c210379e7310c21176bf6310c2118ebe6310c211779e6310c210069e6310c21006bd6310c211779d6310c210069d6310c2118ebc6310c210073e5310c210073c5310c21186be6210c211879f3210c211879d3210c21176be6110c21177af2110c21177b62110c21177ad2110c21187b52110c21035bf7010c2117dbd7010c21176bf6010c21136be6010c21177ba6010c21136ba6010c2116ebd6010c21177b96010c21136bc6010c2116f3f5010c2116f3d5010c21006fb7458021006fa7458021006ba7458021006f97458021006b97458021006f87458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb4358021006fa4358021006ba4358021006f94358021006f84358021006b84358021026fb7258021026fa7258021026f97258021026f87258021026fb4258021026fa4258021026f94258021026f84258021026fb3258021026fa3258021026f93258021026f8325802101efb715802101efa715802101ef9715802101ef8715802101efb415802101efa415802101ef9415802101ef8415802101efb315802101efa315802101ef9315802101ef8315802101efb215802101eeb215802101efa215802101ef2215802101ef9215802101ee92158021026f1215802101ef82158021
  | 1 => 0x9021026bf2059021026be2059021026bd2059021026bc205902101ebf105902101ebe105902101ebd105902101ebc1059021004ff765502101cfe7655021004fd765502101cfc7655021016be6455021006bd64550210373c5455021166fa605502118ebf7498c21014fe7498c21004fd7498c21014fc7498c2118ebc7498c2101cfe7398c2101ede7398c21006df4398c21006dc4398c21024fe7298c21024fc7298c21026de3298c21026dc3298c2101cfe7198c2101cfc7198c2101ede3198c2101edc3198c21004ff7098c2100cfe7098c21004fd7098c2100cfc7098c21006bf4098c21006bd4098c21006df3098c21006de3098c21006dd3098c21006dc3098c21006df7498c210069f7498c21006de7498c21006dd7498c21006dc7498c210069c7498c21006de5498c21006dd5498c21006dc5498c21026df7298c21026de7298c21026dd7298c21026dc7298c21026df4298c21026de4298c21026dd4298c21026dc4298c2101edf7198c2101ede7198c2101edd7198c2101edc7198c2101edf4198c2101ede4198c2101edd4198c2101edc4198c2101edf2198c2101ede2198c2101edd2198c2101edc2198c21006df7098c21006de7098c21006dd7098c21006dc7098c21006df4098c210069f4098c21006de4098c21006dd4098c210069d4098c21006dc4098c21026df2098c21026de2098c21026dd2098c21026dc2098c2101edf1098c2101ede1098c2101edd1098c2101edc1098c21004ff7458c21006bf7458c21004bf7458c21014fe7458c21014fc7458c21006bc7458c21014bc7458c2101cff7358c2101edf7358c21006df4358c21006dc4358c21024ff7258c21024fe7258c21024fd7258c21024fc7258c21026de3258c21026dc3258c2101cff7158c2101cfe7158c2101cfd7158c2101cfc7158c2101ede3158c2101edc3158c21004ff7058c2100cfe7058c21004fd7058c2100cfc7058c21006bf4058c21006bd4058c21006df3058c21006de3058c21006dd3058c21006dc3058c21006df7458c210069f7458c21006de7458c21006dd7458c21006dc7458c210069c7458c21006de5458c21006dd5458c21006dc5458c21026df7258c21026de7258c21026dd7258c21026dc7258c21026df4258c21026de4258c21026dd4258c21026dc4258c2101edf7158c2101ede7158c2101edd7158c2101edc7158c2101edf4158c2101ede4158c2101edd4158c2101edc4158c2101edf2158c2101ede2158c2101edd2158c2101edc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df4058c210069f4058c21006de4058c21006dd4058c210069d4058c21006dc4058c21026df2058c21026de2058c21026dd2058c21026dc2058c2101edf1058c2101ede1058c2101edd1058c2101edc1058c21004f
  | 2 => 0x73c6510d2113e3c6510d211d5be7310d210479e7310d21006bf6310d2118ebe6310d21006bd6310d2118ebc6310d210073e5310d210073c5310d21047ae7210d21047ad7210d21187b72110d21177ae2110d21045bf7010d211cdbd7010d211c6bf6010d21136be6010d211c6bd6010d21136bc6010d211c73f5010d211c73d5010d211c7af2010d211c7ad2010d211c7b71010d211c7b51010d2101cfc76509210067f655092111e7c6550921006bf6450921016bc6450921005f7715092101df4715092101cfe76cc921006bf64cc92110ebc64cc921006df63cc921006dc63cc9210079c43cc92101df671cc921005f571cc921027e421cc92101cfc764c921005bf744c921045bc744c921006bf644c9210f6bc644c921006df634c921006dc634c9210079c434c921005f7714c92101df4714c921014ff7650521044fd7650521024fc76505210057f75505211bd7c75505210067f65505210b67c6550521006bf6450521016bc6450521005ef7250521025ec7250521024fe76cc521006bf64cc5210a6bc64cc521006df63cc521006dc63cc521025ee72cc521005ed72cc52101fe421cc521004ff764c521004fd764c521024fc764c521005bf744c521045bc744c521006bf644c52108ebc644c521006df634c521006dc634c521005ef724c521025ec724c521004ff75590210bcfe75590210bcfc755902101cff745902101ebf7459021006bf5459021036be5459021036bc5459021004ff7359021004fc7359021036bf4359021036bc4359021024ff7259021024fe7259021024fd7259021024fc7259021026be4259021026bc425902101cff715902101cfe715902101cfd715902101cfc715902101ebe415902101ebc4159021004ff705902100cfe7059021004fd705902100cfc70590210067f50590210067d5059021036bf4059021006be4059021006bd4059021036bc4059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021004bc7359021006bf5359021006bc5359021026bf7259021026be7259021026bd7259021026bc7259021026bf5259021026be5259021026bd5259021026bc5259021026bf3259021026be3259021026bd3259021026bc325902101ebf715902101ebe715902101ebd715902101ebc715902101ebf515902101ebe515902101ebd515902101ebc515902101ebf315902101ebe315902101ebd315902101ebc315902101ebf215902101ebe215902101ebd215902101ebc2159021006bf7059021004bf7059021006be7059021006bd7059021004bd7059021006bc7059021006bf50590210063f5059021006be5059021006bd50590210063d5059021006bc5059021006bf3059021006be3059021006bd3059021006bc305
  | 3 => 0xc64d8d21014fe74d8d21006be74d8d21014be74d8d21004fd74d8d21006bd74d8d21004bd74d8d21014fc74d8d21004ff70d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006bf40d8d21006bd40d8d21006de30d8d21006dc30d8d21006ef20d8d21006ed20d8d21006f710d8d21006f510d8d21045be7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d21014fe7498d21006be7498d21014be7498d21004fd7498d21006bd7498d21004bd7498d21014fc7498d21004fe7398d21004fd7298d21006ed7298d21004fd7198d21006f57198d21004ff7098d2100cfe7098d21004fd7098d2100cfc7098d21006bf4098d21006bd4098d21006df3098d21006dd3098d21005bf7458d21045bc7458d21006bf6458d21006bc6458d21005fb7058d2103df87058d21004ff7458d21006bf7458d21004bf7458d21014fe7458d21014fc7458d21006bc7458d21014bc7458d21006df7358d21004ff7258d21006ef7258d21004ff7158d21006f77158d21004ff7058d21006fb7058d21004fb7058d2100cfe7058d21004fd7058d2100cfc7058d21006f87058d2100cf87058d21006bf4058d21006bd4058d21006df3058d21006dd3058d21006ef2058d21006ed2058d21006f71058d21006f51058d21004fe7618d21006bf6418d21006bc6418d21006dd6318d2118ebf7418d21014fe7418d21004fd7418d21014fc7418d2118ebc7418d21006de7318d21024fe7218d21024fc7218d2101cfe7118d2101cfc7118d21004ff7018d2100cfe7018d21004fd7018d2100cfc7018d21006bf4018d21006bd4018d21006de3018d21006dc3018d21004ff7690d21004fe7690d21004fd7690d21004fc7690d210067f6590d2115e7c6590d21006bf6490d21016be6490d21006bd6490d21016bc6490d2118ebf7690d21005be7690d21006be7690d21004be7690d21006bd7690d21005bc7690d2118ebc7690d21004bc7690d21006bf6590d210073f6590d210063f6590d2115ebe6590d21006bd6590d2115ebc6590d210073c6590d2115e3c6590d21045be7390d21006bf6390d2118ebe6390d21006bd6390d2118ebc6390d210073e5390d211b7b72190d21197ae2190d211d5bf7090d211d5bd7090d211debf6090d21146be6090d211debd6090d21146bc6090d211df3f5090d211df3d5090d211dfaf2090d211dfad2090d211dfb71090d211dfb51090d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d211bd7c7550d210067f6550d211567c6550d21006bf6450d21016bc6450d2118ebf7610d21005be7610d21046be7610d21004be7610d21046bd7610d21045bc7610d2118ebc7610d21014bc7610d21006bf6510d210073f6510d210063f6510d2113ebe6510d21006bd6510d2113ebc6510d21
  | 4 => 0x9121004fe73d9121004fd73d9121046bf43d9121046bc43d9121024fe72d912101cfd72d9121024fc72d9121046bf42d912101cfe71d9121024fd71d912101cfc71d9121046bf41d9121004ff70d912100cfe70d9121004fd70d912100cfc70d91210067f50d91210067d50d9121046bf40d9121006be40d9121006bd40d9121046bc40d9121045be76d9121014be76d9121006bf65d91210073f65d91210063f65d9121006be65d9121006bc65d9121005be73d91211ffb721d91211f7ae21d91211f7ac21d91211ffb421d9121005bf70d9121005bd70d9121006bf60d9121006be60d9121006bd60d9121006bc60d91210073f50d91210073d50d9121007af20d9121007ad20d9121007b710d9121007b510d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121004be73d9121006bd73d9121006bc73d9121006bf53d9121006bc53d91211f6bf72d91211febe72d9121006bd72d91211febc72d9121006bf52d91211febe52d91211febc52d91211febe32d91211febc32d91211febf71d91211f6be71d9121006bd71d91211f6bc71d9121006bf51d91211f6be51d91211f6bc51d91211f6be31d91211f6bc31d91211febf21d91211f6be21d91211f6bc21d9121006bf70d9121004bf70d9121006be70d9121006bd70d9121004bd70d9121006bc70d9121006bf50d91210063f50d9121006be50d9121006bd50d91210063d50d9121006bc50d9121006bf30d9121006be30d9121006bd30d9121006bc30d91211febf20d9121006be20d9121006bd20d91211febc20d91211f6bf10d9121006be10d9121006bd10d91211f6bc10d91210057f75591211bd7c75591210067f6559121046bc6459121004ff75591210067f75591210047f75591210bcfe75591210bcfc75591210067c75591210bc7c7559121044ff7459121006bf7459121004ff7359121004fc7359121046bc4359121054ff7259121006ef7259121064ff7159121006f77159121004ff705912100cfe7059121004fd705912100cfc70591210067f50591210067d5059121046bf4059121006bd4059121005be7619121046be7619121004be7619121006bf65191210073f65191210063f6519121006be6519121006bd6519121006bc65191210073c65191210063c6519121005be73191211eebf62191211e6bf61191211e7b721191211efae21191211efac21191211e7b42119121045bf7019121005bd7019121006bf6019121006be6019121006bd6019121006bc60191210073f50191210073d5019121007af2019121007ad2019121007b71019121007b51019121004ff7655121004fe7655121004fd7655121004fc7655121006bf6455121016bc64551210473c5455121045be74d8d21005bd74d8d21006bf64d8d21006b
  | 5 => 0x5bf744c721065bc744c721006de634c721006dd634c721005ef724c721025ec724c72101fd4314c721004ff75592210067f75592210047f75592210bcfe75592210bcfc75592210067c75592210bc7c755922101ebf7459221056be5459221004ff7359221004fc7359221056bc4359221056bf425922101cfc715922101ebe415922101ebc4159221004ff705922100cfe7059221004fd705922100cfc70592210067f50592210067d5059221056bf4059221006bd4059221004ff765522101cfe7655221004fd765522101cfc7655221016be6455221006bd64552210573c5455221014fe7498e21004fd7498e21014fc7498e2101ede7398e2101cfe7198e2101ede3198e2101edc3198e21004ff7098e2100cfe7098e21004fd7098e2100cfc7098e21006bf4098e21006bd4098e21006df3098e21006dd3098e21004ff7458e21006bf7458e21004bf7458e21014fe7458e21014fc7458e21006bc7458e21014bc7458e2101edf7358e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e2100cfe7058e21004fd7058e2100cfc7058e21006bf4058e21006bd4058e21006df3058e21006dd3058e2101ef71058e21006f51058e21004ff7690e2101cfe7690e21004fd7690e2101cfc7690e21196bf6490e21016be6490e21006bd6490e21016bc6490e21025ee7290e21005ed7290e2118ebf7690e21196be7690e21006bd7690e2118ebc7690e21196bf6590e2115ebe6590e21006bd6590e21196bc6590e21196bf6390e2118ebe6390e21006bd6390e2118ebc6390e210073e5390e21007ae7290e21007ad7290e21197af2190e211b7b72190e21225bf7090e21225bd7090e21196bf6090e21146be6090e2121ebd6090e21146bc6090e2121f3f5090e2121f3d5090e21197b71090e2121fb51090e21004ff7650e2101cfe7650e21004fd7650e2101cfc7650e210057f7550e212157c7550e2118ebf7610e21176be7610e21056bd7610e2118ebc7610e21176bf6510e2113ebe6510e21006bd6510e21176bc6510e210579e7310e21176bf6310e2118ebe6310e21006bd6310e2118ebc6310e210073e5310e210073c5310e21177af2110e21187b72110e21055bf7010e2120dbd7010e21176bf6010e21136be6010e21206bd6010e21136bc6010e212073f5010e212073d5010e21177b71010e21207b51010e21014ff7650a2101cfc7650a21016be6450a21006bd6450a21005f77150a2101df47150a21006de63cca21006dd63cca210079c43cca2101df671cca21005f571cca21005bf744ca21055bc744ca21006de634ca21006dd634ca210079c434ca21027cc324ca21005f7714ca2101df4714ca21014fe76d9121046be64d91210bcfe75d9121004fd75d91210bcfc75d9121006bf54d9121046be54d9121046bc54d
  | 6 => 0x7764c431004f7764c431007b7744c431007b4744c43101df7734c43101fd7734c431266f6634c43101fd6634c431007d6534c43100756534c431007d5534c43118fb6434c43118fb4434c431007d6324c431007d4324c43101ef7604c43125ef5604c43125fb7404c43125fb5404c43125fd7304c43125fd5304c431004ff75593210bcfe75593210bcfc7559321026bf7459321006bf5459321066bc5459321004ff7359321004fc7359321066bc435932101cfc7259321026be4259321026bc4259321066bf4159321004ff705932100cfe7059321004fd705932100cfc70593210067f50593210067d5059321066bf4059321006bd4059321004ff7655321024fe7655321004fd7655321024fc7655321256bf6455321016bc64553210673c5455321014fe7498f21004fd7498f21014fc7498f21026de7398f21006df4398f21006dc4398f2101cfe7298f21026de3298f21026dc3298f21004ff7098f2100cfe7098f21004fd7098f2100cfc7098f21006bf4098f21006bd4098f21006df3098f21006dd3098f21004ff7458f21006bf7458f21004bf7458f21014fe7458f21014fc7458f21006bc7458f21014bc7458f21026df7358f21006df4358f21006dc4358f2101cfc7258f21026de3258f21026dc3258f21004ff7058f2100cfe7058f21004fd7058f2100cfc7058f21006bf4058f21006bd4058f21006df3058f21006dd3058f21026ef2058f21006ed2058f21004ff7690f21024fe7690f21004fd7690f21024fc7690f211b6bf6490f21016be6490f21006bd6490f21016bc6490f2118ebf7690f211b6be7690f21006bd7690f2118ebc7690f211b6bf6590f2115ebe6590f21006bd6590f211b6bc6590f211b6bf6390f2118ebe6390f21006bd6390f2118ebc6390f210073e5390f2124dbf7090f2124dbd7090f211b6bf6090f21146be6090f21246bd6090f21146bc6090f212473f5090f212473d5090f211b7af2090f21247ad2090f21004ff7650f21024fe7650f21004fd7650f21024fc7650f210057f7550f2122d7c7550f2118ebf7610f21186be7610f21066bd7610f2118ebc7610f21186bf6510f2113ebe6510f21006bd6510f21186bc6510f210679e7310f21186bf6310f2118ebe6310f211879e6310f210069e6310f21006bd6310f211879d6310f210069d6310f2118ebc6310f210073e5310f210073c5310f21187ae7210f21067ad7210f211879f3210f211879d3210f21065bf7010f2123dbd7010f21186bf6010f21136be6010f21236bd6010f21136bc6010f212373f5010f212373d5010f21187af2010f21237ad2010f21014ff7650721024fc76507210057f755072122d7c7550721016be6450721006bd6450721005ef7250721025ec7250721006de63cc721006dd63cc721025ee72cc721005ed72cc721
  | 7 => 0xc531265f570cc5312a7b740cc5312a7b540cc5312a7d730cc5312a7d530cc531004ff75590310067f75590310047f75590310bcfe75590310bcfc75590310067c75590310bc7c755903101ebf7459031076be5459031014ff7359031014fd7359031074fc7359031076bc4359031004ff7259031024fc7259031076bf425903101cfe715903101cfc715903101ebe415903101ebc4159031004ff705903100cfe7059031004fd705903100cfc70590310067f50590310067d5059031076bf4059031006bd4059031004ff765503101cfe7655031004fd765503101cfc7655031016be6455031006bd64550310773c54550310a4ff7690c3101cfe7690c31014fd7690c3101cfc7690c31016be6490c31006bd6490c3101df67190c31005f57190c3118ebf7690c3118ebe7690c3118ebd7690c3118ebc7690c3118ebf6590c3115ebe6590c31006bd6590c3118ebc6590c3118dbe7390c3118ebe6390c3118f3e5390c311b6be6290c3118fb67190c3118fb57190c31196be6190c3118f9f3190c3118fb63190c311979d3190c3118dbf7090c3129dbd7090c3118ebf6090c31146be6090c31296bd6090c3118ebc6090c312973f5090c312973d5090c310a4ff7650c310057f7550c3127d7c7550c3118ebf7610c3118ebe7610c3118ebd7610c3118ebc7610c3118ebf6510c3113ebe6510c31006bd6510c3118ebc6510c3118dbe7310c3118f9e7310c3118ebe6310c3118f3e5310c3118f3c5310c31186be6210c3118fb67110c3118fb57110c31176be6110c3118f9f3110c3118fb63110c311779d3110c3118dbf7010c3128dbd7010c3118ebf6010c31136be6010c31286bd6010c3118ebc6010c312873f5010c312873d5010c312879e3010c3118f9c3010c31004ff7458831006bf7458831004bf7458831014fe7458831014fc7458831006bc7458831014bc7458831006be4358831006bc435883101eef725883101cff715883101cfd715883101edf315883101edd315883101eee215883101eec2158831004ff705883100cfe7058831004fd705883100cfc7058831006bf4058831006bd4058831006ef2058831006ed2058831024ff769083101cfe7690831004fd769083127d7e75908310057d75908311f6bf6490831016bc6490831005de7390831005dd7390831026ee6290831006ed6290831004ff7650831004fd765083101cfc7650831016be6450831006bd6450831026ee6250831006ed6250831024fd76cc831276de63cc83118f9c43cc831026ee62cc831006ed62cc83101df671cc831005f571cc831004fd768c831075be748c831005bd748c831004ff764c831005bf744c831075bc744c83126ede634c8310079c434c831026ee620c831006ed620c831007cd320c83101df6710c831005f5710c83101df7764c431006f
  | 8 => 0x1779e3110d3108dbf7010d312ddbd7010d312d6bf6010d31136be6010d312d6bd6010d31136bc6010d312d73f5010d312d73d5010d312d79f3010d312d79d3010d312d7b71010d312d7b51010d31006bf64d8931006bc64d8931014fe74d8931004fd74d8931014fc74d8931006be43d8931006bc43d893101cfe71d893101cfc71d8931004ff70d893100cfe70d8931004fd70d893100cfc70d8931006bf40d8931006bd40d8931006df30d8931006dd30d8931006ee20d8931006ec20d8931006f710d8931006f510d893108dbe7498931005bd7498931006bf6498931006bc6498931006ef6298931005bf745893108dbc7458931006bf6458931006bc6458931005fb7058931085f87058931006bf6418931006bc6418931026ee6218931006ed6218931004fe7690931004fd7690931024fc76909312ad7e75909310057d75909310067f659093112e7c6590931006bf6490931016bc6490931005de7390931005dd7390931004ff7650931004fe7650931004fc76509310067f655093111e7c6550931006bf6450931016bc6450931004fe76cc931006bf64cc93110ebc64cc9310079e43cc9310079c43cc931005de76cc931006de76cc9310079f64cc93110ede64cc93110edc64cc9310079c64cc93110e9c64cc931026de62cc931026dc62cc93101dde71cc93101ddc71cc9312b5df70cc9312b5dd70cc9312cedf60cc9312cedd60cc9312cf9f40cc9312cf9d40cc9312cfd710cc9312cfd510cc93101cfe768c93108dbe748c931005bd748c931006bf648c931106bc648c9312c5dd738c931006ef628c931026ec628c93101df6718c931005f5718c93101cfc764c931005bf744c93108dbc744c931006bf644c9310f6bc644c9310079e434c9310079c434c931006ef624c931026ec624c931005f7714c93101df4714c93101cdc764c9310079f744c9310079c744c9310079f644c9310f6de644c9310f6dc644c9310079c644c9310f69c644c931007cf724c931007cf624c931026de624c931026dc624c931007cc624c931026cc624c931007d7714c93101dde714c93101ddc714c931007d4714c93101dd4714c9312c5df704c9312c5dd704c9312bedf604c9312bedd604c9312bf9f404c9312bf9d404c9312bfcf204c9312bfcd204c9312bfd7104c9312bfd5104c931004fe760c931006bf640c9310debc640c9312b5de730c931014ff765053108cfd7650531014fc76505310057f75505312ad7c75505310067f65505310b67c6550531006bf6450531016bc6450531005df7350531005dc7350531006bf64cc5310a6bc64cc53101dde73cc53101edf63cc53100cf676cc531007b764cc531007b464cc53101df673cc53101ef763cc53101fd763cc53118fb643cc53118fb443cc531007d732cc531007d532cc531265f770c
  | 9 => 0xd73d9131014bc73d9131006bf53d9131006bc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006bc52d9131006bf71d9131196be71d9131006bd71d9131196bc71d9131006bf51d9131196be51d9131196bc51d9131196be31d9131196bc31d9131196be21d9131196bc21d9131006bf70d9131004bf70d9131006be70d9131006bd70d9131004bd70d9131006bc70d9131006bf50d91310063f50d9131006be50d9131006bd50d91310063d50d9131006bc50d9131006bf30d9131006be30d9131006bd30d9131006bc30d9131006bf20d9131006be20d9131006bd20d9131006bc20d9131196bf10d9131006be10d9131006bd10d9131196bc10d91310057f75591312ad7c75591310067f655913108ebc6459131004ff75591310067f75591310047f75591310bcfe75591310bcfc75591310067c75591310bc7c755913108cff7459131006bf745913109cff7359131006df735913108ebc4359131004ff7259131024fc72591310a4ff7159131006f77159131004ff705913100cfe7059131004fd705913100cfc70591310067f50591310067d505913108ebf4059131006bd4059131005be761913108ebe7619131004be7619131006bf65191310073f65191310063f6519131006be6519131006bd6519131006bc65191310073c65191310063c6519131176bf63191311779e31191311779c311913108dbf7019131005bd7019131006bf6019131006be6019131006bd6019131006bc60191310073f50191310073d50191310079f30191310079d3019131007b71019131007b51019131004ff7655131004fe7655131004fd7655131004fc7655131006bf6455131016bc645513108f3c5455131005df7355131005dc735513109cfe7690d310067f6590d3115e7c6590d31006bf6490d31016be6490d31006bd6490d31016bc6490d31005be7690d31006be7690d31004be7690d31006bf6590d310073f6590d310063f6590d3115ebe6590d31006bd6590d3115ebc6590d310073c6590d3115e3c6590d3108dbe7390d3118f3e5390d311b6bc6290d311979e3190d312edbf7090d312edbd7090d312f6bf6090d31146be6090d312f6bd6090d31146bc6090d312f73f5090d312f73d5090d312f79f3090d312f79d3090d312f7b71090d312f7b51090d3101cfc7650d310057f7550d312ad7c7550d310067f6550d311567c6550d31006bf6450d31016bc6450d3108f9c4350d31005f77150d3101df47150d31005be7610d3108ebe7610d31004be7610d31006bf6510d310073f6510d310063f6510d3113ebe6510d31006bd6510d3113ebc6510d310073c6510d3113e3c6510d312edbe7310d3108f9e7310d312e79f5310d3118f3e5310d3118f3c5310d312e79c5310d310071c5310d31186bc6210d31
  | 10 => 0xe31327b51090e31014ff7650e3101cfc7650e310057f7550e3130d7c7550e311567e6550e310067d6550e31016be6450e31006bd6450e31005f77150e3101df47150e31175bd7610e3109ebd7610e31176bf6510e3113ebe6510e311773e6510e3113e3e6510e31006bd6510e311773d6510e310063d6510e31176bc6510e3109f9e7310e3118f3e5310e3118f3c5310e31186be6210e311779f3110e3109dbf7010e3131dbd7010e31176bf6010e31136be6010e31316bd6010e31136bc6010e313173f5010e313173d5010e313179e3010e313179c3010e31177b71010e31317b51010e31004ff7458a31014fe7458a31014fc7458a31006be4358a31006bc4358a3101eef7258a3101edf3158a3101edd3158a3101eee2158a3101eec2158a31004ff7058a3100cfe7058a31004fd7058a3100cfc7058a31006bf4058a31006bd4058a31006ef2058a31006ed2058a3101ef71058a31006f51058a31024ff7690a3101cfe7690a31004fd7690a3130d7e7590a310057d7590a3112e7e6590a310067d6590a31016be6490a31006bd6490a31005de7390a31005dd7390a31004ff7650a31004fd7650a3101cfc7650a3111e7e6550a310067d6550a31016be6450a31006bd6450a3110ebe64cca31006bd64cca310079c43cca3109dbe748ca31005bd748ca31106be648ca31006bd648ca31026ee628ca31006ed628ca3101df6718ca31005f5718ca31024ff764ca31005bf744ca3109dbc744ca310f6be644ca31006bd644ca310079c434ca31026ee624ca31006ed624ca31005f7714ca3101df4714ca310debe640ca31006bd640ca31007cd320ca3101df576cc631006f576cc63101fb664cc63101fb564cc63101fd673cc631007d653cc6310075653cc631007d553cc63118fb643cc63118fb443cc631305f770cc631305f570cc6312ffb740cc6312ffb540cc631014fe76d913108ebe64d91310bcfe75d9131004fd75d91310bcfc75d9131006bf54d913108ebe54d913108ebc54d9131014fe73d913101cfd73d9131014fc73d913108ebf43d9131024fe72d9131004fd72d913108ebf42d913108ebc42d913108cfd71d913108ebf41d9131004ff70d913100cfe70d9131004fd70d913100cfc70d91310067f50d91310067d50d913108ebf40d9131006be40d9131006bd40d913108ebc40d913108dbe76d9131014be76d9131006bf65d91310073f65d91310063f65d9131006be65d9131006bc65d91311979e31d91311979c31d9131005bf70d9131005bd70d9131006bf60d9131006be60d9131006bd60d9131006bc60d91310073f50d91310073d50d91310079f30d91310079d30d9131007b710d9131007b510d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131196bf73d913108ebe73d9131014be73d9131006b
  | 11 => 0x1cdd76ccb3110ede64ccb3110edc64ccb31026de62ccb31007ce62ccb31007cd62ccb31026dc62ccb3101dde71ccb31007d671ccb31007d571ccb3101ddc71ccb31345df70ccb31345dd70ccb31276df60ccb31276dd60ccb312779f40ccb312779d40ccb310a5be748cb31005bd748cb31005bf744cb310a5bc744cb310079e434cb310079c434cb31005df764cb31006df764cb310079f744cb310079c744cb310f6de644cb310f6dc644cb31007cf724cb31026de624cb31026dc624cb3101dde714cb3101ddc714cb3133ddf704cb3133ddd704cb3126edf604cb3126edd604cb3126f9f404cb3126f9d404cb3126fcf204cb3126fcd204cb3101cfd760cb31026ee620cb31006ed620cb3101df6710cb31005f5710cb31014ff7650731014fc76507310057f75507313357c7550731016be6450731006bd6450731005df7350731005dc7350731004ff75592310bcfe75592310bcfc755923101ebf7459231006bf545923109ebe545923109ebc545923109ebf4359231004ff7259231024fc725923109ebf425923109ebc425923101cfc715923101ebe415923101ebc4159231004ff705923100cfe7059231004fd705923100cfc70592310067f50592310067d505923109ebf4059231006be4059231006bd405923109ebc4059231006bf7559231006be7559231006bd7559231006bc7559231006bf7359231006bd735923109ebc7359231006bf5359231006bc5359231006bf7259231006be7259231006bd7259231006bc7259231006bf5259231006bc525923101ebf715923101ebe715923101ebd715923101ebc715923101ebf515923101ebe515923101ebd515923101ebc515923101ebf315923101ebe315923101ebd315923101ebc315923101ebf215923101ebe215923101ebd215923101ebc2159231006bf7059231004bf7059231006be7059231006bd7059231004bd7059231006bc7059231006bf50592310063f5059231006be5059231006bd50592310063d5059231006bc5059231006bf3059231006be3059231006bd3059231006bc3059231006bf2059231006be2059231006bd2059231006bc205923101ebf105923101ebe105923101ebd105923101ebc1059231004ff765523101cfe7655231004fd765523101cfc7655231016be6455231006bd645523109f3c545523108cfd7690e3115e7e6590e310067d6590e31196bf6490e31016be6490e31006bd6490e31016bc6490e31195bd7690e31006bd7690e31196bf6590e3115ebe6590e311973e6590e3115e3e6590e31006bd6590e311973d6590e310063d6590e31196bc6590e3118f3e5390e311b6be6290e311979f3190e3132dbf7090e3132dbd7090e31196bf6090e31146be6090e31326bd6090e31146bc6090e313273f5090e313273d5090e31197b7109
  | 12 => 0xe740c941005bd740c941014fe7654541374fd7654541014fc7654541005bf7454541015bc74545410073d54545413357e75d93310057d75d93310a6be64d9331005ee72d9331005ed72d93310bcfe75d93310067e75d93310bc7e75d9331004fd75d93310067d75d93310047d75d93310bcfc75d93310a4fd74d93310a6be54d9331006de73d9331024fe72d9331006ee72d9331024ee72d9331004fd72d9331006ed72d9331004ed72d93310a6bf42d9331006f571d9331196be41d9331196bc41d9331004ff70d933100cfe70d9331004fd70d933100cfc70d93310067f50d93310067d50d93310a6bf40d9331006bd40d9331014ff76593310a6bc6459331004ff75593310bcfe75593310bcfc7559331006bf7459331006bf54593310a6bc545933101cfc73593310a6bc4359331004ff7259331024fc72593310a6bc42593310a6bf4159331004ff705933100cfe7059331004fd705933100cfc70593310067f50593310067d50593310a6bf4059331006bd4059331004ff7655331004fe7655331004fd7655331004fc7655331006bf6455331016bc64553310a73c5455331005df7355331005dc735533101cfd7690f31016be6490f31006bd6490f3101df67190f31005f57190f3118ebe7690f3118ebd7690f3118ebf6590f3115ebe6590f31006bd6590f3118ebc6590f3118f3e5390f311b6be6290f3118fb67190f3118fb57190f3118dbf7090f3136dbd7090f3118ebf6090f31146be6090f31366bd6090f3118ebc6090f313673f5090f313673d5090f3118f9f3090f313679d3090f31074ff7650f310057f7550f313357c7550f310a79c4350f3118ebe7610f3118ebd7610f3118ebf6510f3113ebe6510f31006bd6510f3118ebc6510f3118f9e7310f3135f9f5310f3118f3e5310f3118f3c5310f3118f9c5310f3118f1c5310f31186be6210f3118fb67110f3118fb57110f3118dbf7010f31355bd7010f3118ebf6010f31136be6010f3134ebd6010f3118ebc6010f3134f3f5010f3134f3d5010f3118f9f3010f3134f9d3010f310a5be74d8b31005bd74d8b310a5be7498b31005bd7498b31006ef6298b31004ff7458b31014fe7458b31014fc7458b31006be4358b31006bc4358b31006ef4258b31006ec4258b31004ff7058b3100cfe7058b31004fd7058b3100cfc7058b31006bf4058b31006bd4058b31006df3058b31006dd3058b31006ef2058b31006ed2058b31026ee6218b31006ed6218b31024ff7690b31004fe7690b31004fd7690b313357e7590b310057d7590b31016be6490b31006bd6490b31005de7390b31005dd7390b31004ff7650b31004fd7650b31004fc7650b31006bf6450b31016bc6450b3101cfd76ccb3118f9e43ccb3118f9c43ccb31026ee62ccb31006ed62ccb3101df671ccb31005f571ccb31
  | 13 => 0x4d413cf3f4014d413c73d4014d4101cbe7690d41005bf7590d41005bd7590d41006bf6590d410073f6590d410063f6590d4115ebe6590d41006bd6590d4115ebc6590d410073c6590d4115e3c6590d41015be7390d410179e7390d41006bf6390d410079f6390d4118ebc6390d410079c6390d410069c6390d410073e5390d410073c5390d41005bd7290d411b6bc6290d4101dbe7190d41007b67190d41007b57190d4101dbc7190d41016bf6190d41017b76190d413bdbf7090d413bdbd7090d413b6bf6090d41146be6090d413b6bd6090d41146bc6090d413b73f5090d413b73d5090d410067f65d89410067c65d89410bcfe75d8941004fd75d89410bcfc75d894101cfd74d8941004fe73d8941004fd73d89410067e53d89410067c53d8941006be43d8941056bc43d8941056ee42d8941056ed42d8941004ff70d894100cfe70d8941004fd70d894100cfc70d89410067f50d89410067d50d8941056bf40d8941006bd40d8941006ee20d8941006ec20d89410b57e75989410057d75989410067f65989410067c65989411f6bf6498941005de7398941005dd7398941006ef6298941045f571989410057f75589410b57c75589410067f65589410067c6558941065f771589410067f65189410067c65189411eebf6418941026ee6218941006ed6218941004fe7694941004fd7694941024fc76949410067f65949410be7c6594941015be7494941005bd74949410073d5494941005de7394941005dd7394941004ff7654941004fe7654941004fc76549410067f65549410be7c6554941015be74549413af3e545494101cbc7650941005bf7550941005bd75509410073f655094111ebe655094111ebc65509410073c655094111e3c6550941005bc7350941006bc63509410073e53509410073c5350941015bf7250941017af7250941007af6250941026be6250941026bc6250941007ac6250941007b7715094101dbe715094101dbc7150941007b47150941016bf6150941017b761509413a5bf70509413a5bd705094139ebf605094139ebd605094139f3f505094139f3d5050941004fe76cc941004fd76cc941004fc76cc9410067f65cc9413967c65cc941005bf74cc941015bc74cc941006df63cc941006dc63cc9410075c53cc94110f9c43cc941004fe768c941004fd768c941024fc768c9410b57e758c9410057d758c9410067f658c94138e7c658c941015be748c941005bd748c941006ef628c941026ec628c941004ff764c941004fe764c941004fc764c9410057f754c9410b57c754c9410067f654c9413867c654c941005bf744c941015bc744c941006df634c941006dc634c9410075c534c9410f79c434c941006ef624c941026ec624c941004fe760c941004fd760c941024fc760c9410067f650c94137e7c650c941015b
  | 14 => 0x1cbc7655141015bf75551410173f75551410073f65551410bebe65551410bebc65551410b73c65551410be3c6555141005bc73551410b73c5355141005bf7255141256bc62551410b73c5255141007b7715514101dbe715514101dbc7155141007b47155141016bf6155141017b761551410b73f515514142dbf705514142dbd7055141426bf6055141426bd60551410b73f50551414273d50551410b57e75d8d410057d75d8d410067f65d8d410067c65d8d410bcfe75d8d410067e75d8d410bc7e75d8d41004fd75d8d410067d75d8d410047d75d8d410bcfc75d8d4101cfd74d8d4109ede43d8d4109edd43d8d4109ebc43d8d41024fe72d8d41004fd72d8d41004ff70d8d4100cfe70d8d41004fd70d8d4100cfc70d8d410067f50d8d410067d50d8d4109ebf40d8d41006bd40d8d41006de30d8d41006dc30d8d410b57e7598d410057d7598d410067f6598d410067c6598d41006df6398d41005ee7298d41005ed7298d4108df57198d410057f7558d410b57c7558d410067f6558d410067c6558d410a5f77158d410067f6518d410067c6518d41006dd6318d4118e7f7518d410bcfe7518d41004fd7518d410bcfc7518d4118e7c7518d4118ebf7418d4101cfd7418d41076be5418d41006bd5418d41076de4318d41076dd4318d41024fe7218d41004fd7218d41076bf4218d41176be4118d41176bc4118d41004ff7018d4100cfe7018d41004fd7018d4100cfc7018d410067f5018d410067d5018d41076bf4018d41006bd4018d41006de3018d41006dc3018d41004fe7694d41004fd7694d41004fc7694d410067f6594d410be7e6594d410be7c6594d41015bc7494d413f73e5494d410073d5494d410b75f5394d4118e7f7694d410057e7694d410067e7694d410047e7694d410067d7694d410057c7694d4118e7c7694d410047c7694d410073f7494d413f73c7494d414167f6494d413cd7e7394d410067f6394d4118e7c6394d413f73c4394d4141e7c6294d413f73f4294d413f67f6194d413f7774194d414173e4194d414173c4194d413f7744194d4140d7f7094d4140d7d7094d413fe7f6094d414067e6094d413fe7d6094d414067c6094d413f73f4094d413ff3d4094d41004ff7654d41004fe7654d41004fc7654d410067f6554d410be7c6554d41005bf7454d41015bc7454d4118e7f7614d410057e7614d410b67e7614d410047e7614d410b67d7614d410b57c7614d4118e7c7614d410bc7c7614d413cf3e7414d410b73d7414d413e67f6414d413f57e7314d410b75e7314d410067f6314d4118e7c6314d413cf3c4314d413ee7c6214d413cf3f4214d413ce7f6114d413cf774114d413e73e4114d413e73c4114d413cf744114d410b57f7014d413dd7d7014d413c67f6014d413d67e6014d413c67d6014d413d67c601
  | 15 => 0xc43cca41024ff768ca4101cfe768ca41004fd768ca410cd7e758ca410057d758ca41015be748ca41005bd748ca41004ff764ca41004fd764ca4101cfc764ca410057f754ca410cd7c754ca41005bf744ca41015bc744ca41006de634ca41006dd634ca410075c534ca410f79c434ca41024ff760ca4101cfe760ca41004fd760ca411fdbf740ca41015bc740ca410bcfe76d95410b67e65d954101cff74d9541014fe74d954101cfd74d9541014fc74d95414467f54d95414467d54d9541004fe73d9541004fd73d95410b67f53d95410b67c53d9541446bc43d9541024fe72d9541004fd72d95410b67f52d95410b67c52d9541014fd71d95410b67f51d9541004ff70d954100cfe70d9541004fd70d954100cfc70d95410b67f50d95410067e50d95410067d50d95410b67c50d9541446bf40d9541006bd40d95414357e76d95410bc7e76d95414573f74d95414473c74d95410057e73d95414473c43d95414473f42d95414477741d95414573e41d95414573c41d95414477441d95410057f70d95410057d70d95410067f60d95410067e60d95410067d60d95410067c60d95414473f40d95410073d40d95414567f74d95414467e74d95414467d74d95414467c74d95410067f73d95410067e73d95410047e73d95410067d73d95410067c73d95414467f43d95414467e43d95414467d43d95414467c43d95414463c43d95410067f72d95410067e72d95410067d72d95410067c72d95414467f42d95414467e42d95414467d42d95414467c42d95414467f71d95414567e71d95414467d71d95414567c71d95414467f41d95414567e41d95414567c41d95414567e31d95414567c31d95414567e21d95414567c21d95410067f70d95410047f70d95410067e70d95410067d70d95410047d70d95410067c70d95414467f40d95414463f40d95414467e40d95414467d40d95410063d40d95414467c40d95410067f30d95410067e30d95410067d30d95410067c30d95410067f20d95410067e20d95410067d20d95410067c20d95414567f10d95410067e10d95410067d10d95414567c10d95410b67c655954144df77159541374ff7459541006bf7459541004ff7359541004fc7359541376bc4359541004ff7259541024fc725954144cff7159541006f77159541004ff705954100cfe7059541004fd705954100cfc7059541376bf4059541006bd40595414457e76195410b67e76195414447e76195414373e74195410b73d741954143e7f641954143e3f64195410057e73195414373c43195414373f42195414367f611954143777411954143f3e411954143f3c41195414377441195410b57f70195410057d70195410067f60195410067e60195410067d60195410067c60195414373f40195410073d401954101dbc76551410bebc7655141
  | 16 => 0x4e4118e7e6394e410067d6394e413f73c4394e4141e7e6294e413f73c4294e414167e6194e414173f4194e413f7774194e41417744194e414957f7094e414957d7094e414167f6094e414067e6094e4148e7d6094e414067c6094e413f73f4094e4148f3d4094e41004ff7654e41004fd7654e4101cfc7654e41005bf7454e41015bc7454e4118e7f7614e413e67e7614e410ce7d7614e4118e7c7614e410cf3f7414e413cf3c7414e410cf5e7314e4118e7e6314e413e75e6314e410065e6314e410067d6314e413e75d6314e410065d6314e413cf3c4314e413ee7e6214e413cf3c4214e413e67e6114e413e73f4114e413cf774114e413e7744114e410cd7f7014e414857d7014e413e67f6014e413d67e6014e4147e7d6014e413d67c6014e413cf3f4014e4147f3d4014e410cdbe7590e410cdbc7590e41196bf6590e4115ebe6590e41006bd6590e41196bc6590e41015be7390e410179e7390e4118ebe6390e411979e6390e410069e6390e41006bd6390e411979d6390e410073e5390e410073c5390e411fdbe7290e411b6be6290e41197b67190e41195bd7190e41007b57190e41016be6190e41017b66190e41475bf7090e41475bd7090e41196bf6090e41146be6090e4146ebd6090e41146bc6090e4146f3f5090e4146f3d5090e41004ff7558a410067f7558a410047f7558a410bcfe7558a410bcfc7558a410067c7558a410bc7c7558a41006bf5458a41046bc5458a41004ff7358a41004fc7358a410067e5358a410067c5358a41006be4358a41046bc4358a4101eef7258a41046ee4258a41046ed4258a411febc4258a4101cfc7158a4101ebf4158a4101ebd4158a4101eee2158a4101eec2158a41004ff7058a4100cfe7058a41004fd7058a4100cfc7058a410067f5058a410067d5058a41046bf4058a41006bd4058a41006ef2058a41006ed2058a41024ff7694a4101cfe7694a41004fd7694a410be7c6594a41015be7494a41005bd7494a410cf3f5494a41005de7394a41005dd7394a41004ff7654a41004fd7654a4101cfc7654a410be7e6554a410067d6554a41005bf7454a41015bc7454a413af3c5454a410cdbe7590a411ff3e7590a410cd3e7590a411ff3d7590a411fdbc7590a411f6bf6590a41006bd6590a41005be7390a411ff9e7390a410059e7390a411ff9d7390a41006be6390a410073e5390a410073c5390a41015be7290a41017ae7290a411f6bf6290a411f7ae6290a411febd6290a411f7ad6290a411f7b67190a411f5bd7190a411ffb57190a41016be6190a41017b66190a411fdbf7090a41465bd7090a411f6bf6090a4145ebd6090a4145f3f5090a4145f3d5090a41004ff76cca4101cfe76cca41004fd76cca41015be74cca41005bd74cca41006de63cca41006dd63cca410075c53cca4110f9
  | 17 => 0x18ebd7610c3218ebc7610c3218ebf6510c3213ebe6510c32006bd6510c3218ebc6510c3218dbe7310c3218f9e7310c3218ebe6310c3210e9e6310c3218f3e5310c3218f3c5310c3218fae7210c3218fad7210c32186be6210c3218f9f3210c3218fae3210c321879d3210c32176be6110c3218dbf7010c324b5bd7010c3218ebf6010c32136be6010c324aebd6010c3218ebc6010c324af3f5010c324af3d5010c32025ef764c832006ef764c832004ef764c832007af744c832007ac744c832025ef734c832027cf734c8324a6ee634c832027ce634c83218fae434c832007ce434c8320078e434c832007cd434c83218fac434c832026ef604c83249eed604c83249faf404c83249fad404c83249fcf304c83249fcd304c832004ff7458432006bf7458432004bf7458432014fe7458432014fc7458432006bc7458432014bc7458432006be4358432006bc4358432026df3258432026dd3258432026f77158432026f72158432026f42158432004ff705843200cfe7058432004fd705843200cfc7058432006bf4058432006bd4058432006f71058432006f5105843201e7f75596413767f54596410cebf54596410ce3f54596413767d5459641376bc5459641004ff7359641004fc73596410ce7c5359641376bc4359641004ff7259641024fc72596410ce7f5259641376bc425964101cfe715964101cfc715964101e7e515964101e7c515964101ebf415964101ebd4159641004ff705964100cfe7059641004fd705964100cfc70596410ce7f50596410067d5059641376bf4059641006bd40596410bcfe7598e41004fd7598e410bcfc7598e4118ebf7498e41006bf5498e410a6bc5498e4101ede7398e41006df5398e41006dc5398e410a6de4398e410a6dd4398e41024fe7298e41004fd7298e410a6bc4298e4101cfe7198e4101ebf4198e4101ebd4198e4101ede3198e4101edc3198e41004ff7098e4100cfe7098e41004fd7098e4100cfc7098e410067f5098e410067d5098e410a6bf4098e41006bd4098e41006df3098e41006dd3098e41004ff7558e410067f7558e410047f7558e410bcfe7558e410bcfc7558e410067c7558e410bc7c7558e4101edf7358e41006df5358e41006dc5358e4108ede4358e4108edd4358e4108ebc4358e41004ff7258e41024fc7258e4101cfc7158e4101ede3158e4101edc3158e41004ff7058e4100cfe7058e41004fd7058e4100cfc7058e410067f5058e410067d5058e4108ebf4058e41006bd4058e41006df3058e41006dd3058e41004ff7694e4101cfe7694e41004fd7694e410be7e6594e410067d6594e410be7c6594e41015be7494e41005bd7494e410cf3f5494e413f73c5494e410cf5f5394e4118e7f7694e414167e7694e410067d7694e4118e7c7694e413f73e7494e410073d749
  | 18 => 0xd7110d320f79c7110d324ef9f5110d324ef9c5110d320f79f7010d320f59f7010d320f79e7010d320f79d7010d324e59d7010d320f79c7010d324df9f6010d324df9e6010d324df9d6010d324df9c6010d324df9f5010d324df1f5010d324df9e5010d324df9d5010d324df1d5010d324df9c5010d321879f2010d324df8f2010d324df9e2010d324df9d2010d324df8d2010d321879c2010d324df9f1010d324df9e1010d324df9d1010d324df9c1010d32014ff76509320f4fd7650932014fc76509320067f655093211e7c6550932006bf6450932016bc6450932005df7350932005dc73509320075c53509320f79c4350932027ac4250932027cc3250932006bf64cc93210ebc64cc932025de73cc932026df63cc9320079c43cc932007af64cc932007ac64cc932025ee73cc932026ef63cc932027cf63cc9324d7cf43cc93218fae43cc93218fac43cc9324d7cc43cc9320078c43cc9324a5ef70cc9324a5ed70cc9324cfaf40cc9324cfad40cc9324cfcf30cc9324cfcd30cc932006bf64d8532006bc64d85320079c43d8532014fe74d8532004fd74d8532014fc74d8532006be43d8532006bc43d8532004ff70d853200cfe70d8532004fd70d853200cfc70d8532006bf40d8532006bd40d8532006df30d8532006dd30d8532006ef20d8532006ed20d8532006f610d8532006f410d85320f5be7498532005bd7498532006bf6498532006bc64985320079c4398532006f76198532005bf74585320f5bc7458532006bf6458532006bc64585320079c4358532005fb70585320edf87058532006bf6418532006bc64185320079c431853201ef66118532006f56118532004ff75590320bcfe75590320bcfc7559032026bf7459032006bf54590320debc54590320dcfc73590320debc4359032024fe7259032024fc7259032026be4259032026bc4259032004ff715903201cfc71590320debf4159032004ff705903200cfe7059032004fd705903200cfc70590320067f50590320067d50590320debf4059032006bd4059032004ff7655032024fe7655032004fd7655032024fc7655032256bf6455032016bc64550320df3c545503210cff7690c32024fe7690c32014fd7690c32024fc7690c32016be6490c32006bd6490c32025ee7290c32005ed7290c3218ebf7690c3218ebe7690c3218ebd7690c3218ebc7690c3218ebf6590c3215ebe6590c32006bd6590c3218ebc6590c3218dbe7390c3218ebe6390c3218f3e5390c3218fae7290c3218fad7290c321b6be6290c3218f9f3290c3218fae3290c321b79d3290c32196be6190c3218dbf7090c324c5bd7090c3218ebf6090c32146be6090c324bebd6090c3218ebc6090c324bf3f5090c324bf3d5090c3210cff7650c320057f7550c3237d7c7550c3218ebf7610c3218ebe7610c32
  | 19 => 0x91320067c75591320bc7c75591320f4ff7459132006bf7459132104ff7359132006df73591320f6df43591320f6bc43591320f6dc435913210cff7259132006ef7259132004ff715913201cfc7159132004ff705913200cfe7059132004fd705913200cfc70591320067f50591320067d50591320f6bf4059132006bd4059132005be76191320f6be7619132004be7619132006bf65191320073f65191320063f6519132006be6519132006bd6519132006bc65191320073c65191320063c65191321879f73191320f79c7319132186bf63191320079f53191320079c53191321879e32191321879c32191320f5bf7019132005bd7019132006bf6019132006be6019132006bd6019132006bc60191320073f50191320073d50191320079f30191320079d3019132007af2019132007ad2019132004ff7655132004fe7655132004fd7655132004fc7655132006bf6455132016bc64551320f73c5455132005df7355132005dc73551320f79c4355132104fe7690d320067f6590d3215e7c6590d32006bf6490d32016be6490d32006bd6490d32016bc6490d320f5de7390d320f79f4390d32005be7690d32006be7690d32004be7690d32006bf6590d320073f6590d320063f6590d3215ebe6590d32006bd6590d3215ebc6590d320073c6590d3215e3c6590d320f5be7390d320f59e7390d325079f5390d3218f3e5390d325079c5390d321b79e3290d32196bc6190d324f5bf7090d324f5bd7090d324febf6090d32146be6090d324febd6090d32146bc6090d324ff3f5090d324ff3d5090d324ff9f3090d324ff9d3090d324ffaf2090d324ffad2090d32024fc7650d320057f7550d323857c7550d320067f6550d321567c6550d32006bf6450d32016bc6450d320f5df7350d320f79c4350d32005ef7250d32025ec7250d32005be7610d320f6be7610d32004be7610d32006bf6510d320073f6510d320063f6510d3213ebe6510d32006bd6510d3213ebc6510d320073c6510d3213e3c6510d324f5be7310d320f79e7310d324ef9f5310d3218f3e5310d320079e5310d320071e5310d320079d5310d3218f3c5310d324ef9c5310d320071c5310d321879e3210d32176bc6110d320f5bf7010d324e5bd7010d324debf6010d32136be6010d324debd6010d32136bc6010d324df3f5010d324df3d5010d324df9f3010d324df9e3010d324df9d3010d324df9c3010d324dfaf2010d324dfad2010d320f79e7610d320059e7610d320f69e7610d320f79f7510d320f79e7510d320f79d7510d320f79c7510d320079f6510d320071f6510d324ef9e6510d320079d6510d324ef9c6510d320071c6510d320f79f7210d321879e7210d320f79d7210d321879c7210d324ef9f5210d321879e5210d321879c5210d320f79f7110d320f79e7110d320f79
  | 20 => 0x1873d6510e320063d6510e32186bc6510e321079e7310e3218f3e5310e3218f3c5310e321879f3210e32176be6110e32105bf7010e32525bd7010e32186bf6010e32136be6010e3251ebd6010e32136bc6010e3251f3f5010e3251f3d5010e32187af2010e3251fad2010e32025ed76cca32006ed76cca32027ae64cca32027ad64cca32027ce73cca32007ce53cca320074e53cca32007cd53cca3218fae43cca3218fac43cca32515ef70cca32515ed70cca3250faf40cca3250fad40cca32004ff7458632014fe7458632014fc7458632006be4358632006bc4358632026df3258632026dd3258632026f77158632026f72158632026f42158632004ff705863200cfe7058632004fd705863200cfc7058632006bf4058632006bd4058632026ef2058632006ed2058632006f71058632006f51058632014fe76d91320f6be64d9132025dd73d91320f79f43d91320bcfe75d9132004fd75d91320bcfc75d9132006bf54d91320f6be54d91320f6bc54d9132024fd73d91320f6dd73d9132024dd73d91320f6bf43d91320f6df43d91320f6dc43d91320f4fd72d91320f6bf42d913201cfe71d9132004fd71d91320f6bf41d91320f6bc41d9132004ff70d913200cfe70d9132004fd70d913200cfc70d91320067f50d91320067d50d91320f6bf40d9132006be40d9132006bd40d91320f6bc40d91320f5be76d9132014be76d9132006bf65d91320073f65d91320063f65d9132006be65d9132006bc65d91320f79e73d91320079d73d91320079f53d91320079c53d91321b79e32d91321b79c32d9132005bf70d9132005bd70d9132006bf60d9132006be60d9132006bd60d9132006bc60d91320073f50d91320073d50d91320079f30d91320079d30d9132007af20d9132007ad20d9132006bf75d9132006be75d9132006bd75d9132006bc75d91321b6bf73d91320f6be73d91320f69e73d9132006bd73d91320069d73d9132006bf53d9132006bc53d9132006bf72d91321b6be72d9132006bd72d91321b6bc72d9132006bf52d91321b6be52d91321b6bc52d91321b6be32d91321b6bc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006bc51d91321b6bf21d91321b6bc21d9132006bf70d9132004bf70d9132006be70d9132006bd70d9132004bd70d9132006bc70d9132006bf50d91320063f50d9132006be50d9132006bd50d91320063d50d9132006bc50d9132006bf30d9132006be30d9132006bd30d9132006bc30d91321b6bf20d9132006be20d9132006bd20d91321b6bc20d9132006bf10d9132006be10d9132006bd10d9132006bc10d91320057f75591323857c75591320067f65591320f6bc64591320f79c4359132004ff75591320067f75591320047f75591320bcfe75591320bcfc755
  | 21 => 0xe1010f3253f9d1010f3253f9c1010f32014ff7650b32014fc7650b32016be6450b32006bd6450b32005df7350b32005dc7350b320075c5350b3210f9c4350b3210dbe74d8732005bd74d873218f9c43d873210dbe7498732005bd74987320079c4398732006f761987320079c4358732004ff7458732014fe7458732014fc7458732006be4358732006bc4358732004ff705873200cfe7058732004fd705873200cfc7058732006bf4058732006bd4058732006df3058732006dd3058732006f71058732006f5105873218f9c431873201ef66118732006f56118732004ff75592320bcfe75592320bcfc7559232026bf7459232006bf5459232106be5459232106bc5459232106bf4359232024fc7259232026be4259232026bc4259232004ff715923201cfc7159232106bf4159232106bc4159232004ff705923200cfe7059232004fd705923200cfc70592320067f50592320067d5059232106bf4059232006be4059232006bd4059232106bc4059232006bf7559232006be7559232006bd7559232006bc7559232006bf7359232006bd7359232106bc7359232006bf5359232006bc5359232026bf7259232026be7259232026bd7259232026bc7259232026bf5259232026be5259232026bd5259232026bc5259232026bf3259232026be3259232026bd3259232026bc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006bc5159232026bf2159232026be2159232026bd2159232026bc2159232006bf7059232004bf7059232006be7059232006bd7059232004bd7059232006bc7059232006bf50592320063f5059232006be5059232006bd50592320063d5059232006bc5059232006bf3059232006be3059232006bd3059232006bc3059232026bf2059232026be2059232026bd2059232026bc2059232006bf1059232006be1059232006bd1059232006bc1059232004ff7655232024fe7655232004fd7655232024fc7655232016be6455232006bd64552321073c54552320f4fd7690e3215e7e6590e320067d6590e321b6bf6490e32016be6490e32006bd6490e32016bc6490e321b5bd7690e32006bd7690e321b6bf6590e3215ebe6590e321b73e6590e3215e3e6590e32006bd6590e321b73d6590e320063d6590e321b6bc6590e3218f3e5390e321b79f3290e32196be6190e32535bf7090e32535bd7090e321b6bf6090e32146be6090e3252ebd6090e32146bc6090e3252f3f5090e3252f3d5090e321b7af2090e3252fad2090e32014ff7650e32024fc7650e320057f7550e3238d7c7550e321567e6550e320067d6550e32016be6450e32006bd6450e32005ef7250e32025ec7250e32185bd7610e32106bd7610e32186bf6510e3213ebe6510e321873e6510e3213e3e6510e32006bd6510e32
  | 22 => 0x933210edc43d9332006ed72d93321b6be42d93321b6bc42d933201cfe71d9332004fd71d933210ebf41d9332004ff70d933200cfe70d9332004fd70d933200cfc70d93320067f50d93320067d50d933210ebf40d9332006bd40d9332014ff76593320057f75593323957c755933210ebc6459332025dc735933210f9c4359332004ff75593320067f75593320047f75593320bcfe75593320bcfc75593320067c75593320bc7c7559332006bf745933210ebe5459332024fc735933210edc7359332024dc735933210edf435933210ebc435933210edc435933210ebf4259332004ff715933201cfc715933210ebc4159332004ff705933200cfe7059332004fd705933200cfc70593320067f50593320067d505933210ebf4059332006bd4059332004ff7655332004fe7655332004fd7655332004fc7655332016be6455332006bd645533210f3c5455332005df7355332005dc735533210f9c4355332024fd7690f32016be6490f32006bd6490f3210dde7390f3210f9f4390f32025ee7290f32005ed7290f3218ebe7690f3218ebd7690f3218ebf6590f3215ebe6590f32006bd6590f3218ebc6590f325679f5390f3218f3e5390f3218f9c5390f3218fae7290f3218fad7290f32196be6190f3218dbf7090f3255dbd7090f3218ebf6090f32146be6090f32556bd6090f3218ebc6090f325573f5090f325573d5090f3218f9f3090f325579d3090f320dcff7650f320057f7550f323957c7550f3210ddf7350f3210f9c4350f3218ebe7610f3218ebd7610f3218ebf6510f3213ebe6510f32006bd6510f3218ebc6510f3218f9e7310f3254f9f5310f3218f3e5310f3218f9e5310f3218f1e5310f320079d5310f3218f3c5310f3218f9c5310f3218f1c5310f3218fae7210f3218fad7210f32176be6110f3218dbf7010f32545bd7010f3218ebf6010f32136be6010f3253ebd6010f3218ebc6010f3253f3f5010f3253f3d5010f3218f9f3010f3253f9e3010f3253f9d3010f3218f9c3010f3218f9e7610f3210e9e7610f3218f9d7610f3210e9d7610f3218f9f7510f3210f9e7510f3210f9d7510f3218f9c7510f3218f9f6510f3254f9e6510f320079d6510f3218f9c6510f3218f9f7210f321879e7210f3210f8e7210f3210f9d7210f3210f8d7210f3218f9c7210f3254f9f5210f321879e5210f321879c5210f3218f9f7110f3210f9e7110f3210f9d7110f3218f9c7110f3254f9f5110f3254f9c5110f3218f9f7010f3210d9f7010f3210f9e7010f3210f9d7010f325459d7010f3218f9c7010f3218f9f6010f3253f9e6010f3253f9d6010f3218f9c6010f3253f9f5010f3253f1f5010f3253f9e5010f3253f9d5010f3253f1d5010f3253f9c5010f321879f2010f3253f9e2010f3253f9d2010f321879c2010f3253f9f1010f3253f9
  | 23 => 0x6dd6318d420bcfe7518d42004fd7518d420bcfc7518d4218ebf7418d42024fd7418d42006bf5418d420debc5418d420dede4318d420dedd4318d42186be4218d42186bc4218d4201cfe7118d42004fd7118d420debf4118d42004ff7018d4200cfe7018d42004fd7018d4200cfc7018d420067f5018d420067d5018d420debf4018d42006bd4018d42004fe7694d42004fd7694d42004fc7694d420067f6594d420be7e6594d420be7c6594d42015be7494d42005bd7494d4211f3f5494d423f73c5494d4211f5f5394d42025ee7294d42005ed7294d4218e7f7694d420067e7694d420067d7694d4218e7c7694d423f73e7494d420073d7494d4241e7f6494d423cd7e7394d420067f6394d4218e7c6394d423f73c4394d420076e7294d420076d7294d423f67f6294d423f76f4294d4241f3e4294d4241f3c4294d423f76c4294d424167c6194d423f73f4194d425957f7094d425957d7094d4258e7f6094d424067e6094d4258e7d6094d424067c6094d423f73f4094d4258f3d4094d42004ff7654d42004fe7654d42004fc7654d42005bf7454d42015bc7454d4218e7f7614d4211e7e7614d4211e7d7614d4218e7c7614d4211f3f7414d423cf3c7414d423ee7f6414d423f57e7314d4211f5e7314d420067f6314d4218e7c6314d423cf3c4314d423ce7f6214d423cf6f4214d423ef3e4214d423ef3c4214d423cf6c4214d423e67c6114d423cf3f4114d4211d7f7014d425857d7014d4257e7f6014d423d67e6014d4257e7d6014d423d67c6014d423cf3f4014d4257f3d4014d42024be7690d4211dbe7590d4211dbc7590d42006bf6590d4215ebe6590d42006bd6590d4215ebc6590d42015be7390d420179e7390d42006bf6390d420079f6390d4218ebc6390d420079c6390d420069c6390d420073e5390d420073c5390d42025be7290d42007ae7290d42025ae7290d42007ad7290d42025bc7290d42016bf6290d42017af6290d42005bd7190d42196bc6190d42575bf7090d42575bd7090d4256ebf6090d42146be6090d4256ebd6090d42146bc6090d4256f3f5090d4256f3d5090d42014fe76549423acfd7654942014fc7654942005bf7454942015bc74549423af3c54549420bcfe75d8542004fd75d85420bcfc75d8542024fd74d8542004fe73d8542004fd73d85420067e53d85420067c53d8542006be43d8542066bc43d8542066f641d8542004ff70d854200cfe70d8542004fd70d854200cfc70d85420067f50d85420067d50d8542066bf40d8542006bd40d8542006f761985420057f755854211d7c755854211d7e75185420057d75185421f6bf641854201ef66118542006f5611854210ebe64d93320bcfe75d9332004fd75d93320bcfc75d933210cfd74d9332006bf54d933210ebc54d9332006de73d933210edf43d
  | 24 => 0xe6314e420067d6314e423ef5d6314e420065d6314e423cf3c4314e423ee7e6214e423ef3f4214e423cf6f4214e423ef6c4214e423e67e6114e423cf3c4114e4212d7f7014e425cd7d7014e423ee7f6014e423d67e6014e425c67d6014e423d67c6014e423cf3f4014e425c73d4014e42005bf7590e42005bd7590e421b6bf6590e4215ebe6590e421b73e6590e4215e3e6590e42006bd6590e421b73d6590e420063d6590e421b6bc6590e42015be7390e420179e7390e4218ebe6390e421b79e6390e420069e6390e42006bd6390e421b79d6390e420069d6390e420073e5390e420073c5390e421b7ae7290e421b5bd7290e42007ad7290e42016be6290e42017ae6290e421f5be7190e42196be6190e425bdbf7090e425bdbd7090e421b6bf6090e42146be6090e425b6bd6090e42146bc6090e425b73f5090e425b73d5090e42004ff75586420bcfe75586420bcfc7558642046be5458642006bd5458642004ff7358642004fc73586420067e53586420067c5358642006be4358642046bc4358642024fc7258642026bf4258642026bd4258642026f77158642046f641586421f6bc4158642026f72158642026f42158642004ff705864200cfe7058642004fd705864200cfc70586420067f50586420067d5058642046bf4058642006bd4058642006f71058642006f510586420bcfe76d954211e7e65d9542015be74d9542025bd74d954211f3f54d9542024ff74d9542024fd74d954211ebd74d9542024bd74d95425a67f54d954211ebf54d954211e3f54d95425a67d54d95425a6bc54d9542004fe73d9542004fd73d954211e7c53d95425a6bc43d9542014fd72d954211e7f52d95425aebe42d95425aebc42d954201cfe71d9542004fd71d954211e7c51d95425a6bf41d9542004ff70d954200cfe70d9542004fd70d954200cfc70d954211e7f50d95420067d50d95425a6bf40d9542006bd40d954211e7c65595423af3c545954259def72595423acff7459542006bf74595423ae7e54595423aebc54595423ae3c5459542004ff7359542004fc73595423aebc435954259cff7259542006ef7259542256be4259542256bc4259542004ff715954201cfc71595423aebf4159542004ff705954200cfe7059542004fd705954200cfc70595423aebf4059542006bd405954211d7e75d8d420057d75d8d420bcfe75d8d420067e75d8d420bc7e75d8d42004fd75d8d420067d75d8d420047d75d8d420bcfc75d8d42024fd74d8d42106de43d8d42106dd43d8d42106bc43d8d4201cfe71d8d42004fd71d8d42004ff70d8d4200cfe70d8d42004fd70d8d4200cfc70d8d420067f50d8d420067d50d8d42106bf40d8d42006bd40d8d42006df6398d4210f9c4398d420f5ed7298d420057f7558d4211d7c7558d420f79c4358d4210def7258d42
  | 25 => 0x8e42026df2098e42026de2098e42026dd2098e42026dc2098e42006df1098e42006de1098e42006dd1098e42006dc1098e42004ff7558e420067f7558e420047f7558e420bcfe7558e420bcfc7558e420067c7558e420bc7c7558e42026df7358e42006df5358e42006dc5358e420f6de4358e420f6dd4358e420f6bc4358e42024fc7258e42026de3258e42026dc3258e42004ff7158e4201cfc7158e42004ff7058e4200cfe7058e42004fd7058e4200cfc7058e420067f5058e420067d5058e420f6bf4058e42006bd4058e42006df3058e42006de3058e42006dd3058e42006dc3058e42006df7558e420065f7558e42006de7558e42006dd7558e42006dc7558e420065c7558e420f6de7458e420f6dd7458e420f6dc7458e420f69c7458e420f6df5458e420f6de5458e420f6dd5458e420f6dc5458e42026df7258e42026de7258e42026dc7258e42026df5258e42026de5258e42026dd5258e42026dc5258e42026df4258e42026de4258e42026dd4258e42026dc4258e42006df7158e42006de7158e42006dd7158e42006dc7158e42006df5158e42006dc5158e420f6df4158e420f6de4158e420f6dd4158e420f6dc4158e42026df2158e42026de2158e42026dd2158e42026dc2158e42006df7058e42006de7058e42006dd7058e42006dc7058e42006df5058e420065f5058e42006de5058e42006dd5058e420065d5058e42006dc5058e420f6df4058e420f69f4058e420f6de4058e420f6dd4058e420069d4058e420f6dc4058e42026df2058e42026de2058e42026dd2058e42026dc2058e42006df1058e42006de1058e42006dd1058e42006dc1058e42004ff7694e42024fe7694e42004fd7694e420be7e6594e420067d6594e420be7c6594e42015bc7494e423f73e5494e420073d5494e42006de6394e42006dd6394e4212f5f5394e42025ee7294e42005ed7294e4241d7f7694e4218e7f7694e420047f7694e4241e7e7694e4241d7d7694e420067d7694e420047d7694e4218e7c7694e420073f7494e423f73c7494e4218e7e6394e4241f5e6394e420065e6394e420067d6394e4241f5d6394e420065d6394e423f73c4394e4241f6e7294e420076d7294e4241e7e6294e4241f3f4294e423f76f4294e4241f6c4294e424167e6194e423f73c4194e425dd7f7094e425dd7d7094e4241e7f6094e424067e6094e425d67d6094e424067c6094e423f73f4094e425d73d4094e42004ff7654e42004fd7654e42024fc7654e420be7e6554e420067d6554e42005bf7454e42015bc7454e42006de6354e42006dd6354e423ed7f7614e4218e7f7614e420bc7f7614e423ee7e7614e423ed7d7614e4212e7d7614e420047d7614e4218e7c7614e423cf3e7414e4212f3d7414e4212f5e7314e4218e7e6314e423ef5e6314e420065
  | 26 => 0x3ae7c43596423ae3c43596420267f72596420267e72596420267c72596420267f42596420267e42596420267d42596420267c42596420267f32596420267e32596420267d32596420267c32596420067f71596420067e71596420067d71596420067c71596423ae7f41596423ae7e41596423ae7d41596423ae7c41596420267f21596420267e21596420267d21596420267c21596420067f70596420047f70596420067e70596420067d70596420047d70596420067c70596423ae7f40596423ae3f40596423ae7e40596423ae7d40596420063d40596423ae7c40596420067f30596420067e30596420067d30596420067c30596420267f20596420267e20596420267d20596420267c20596420067f10596420067e10596420067d10596420067c1059642255bf76552420bebf76552420bcbf7655242015bf75552420173f75552420bebe65552422573e65552420be3e65552422573d65552420bebc6555242005bc73552422579e63552422579d635524212f3c5355242255bf7255242007af7255242257ac7255242016be6255242017ae62552422573e52552422573c52552421f5bc715524212f3f51552425edbf70552425edbd7055242256bf60552425e6bd605524212f3f50552425e73d505524218e7f7598e420bcfe7598e42004fd7598e420bcfc7598e4218e7c7598e4218ebf7498e4210ebe5498e42006bd5498e42026de7398e42006df5398e42006dc5398e4210ede4398e4210edd4398e42024fe7298e42026bf4298e42026bd4298e42026de3298e42026dc3298e4201cfe7198e42004fd7198e4210ebc4198e42004ff7098e4200cfe7098e42004fd7098e4200cfc7098e420067f5098e420067d5098e4210ebf4098e42006bd4098e42006df3098e42006de3098e42006dd3098e42006dc3098e42006df7598e420065f7598e42006de7598e42006dd7598e42006dc7598e420065c7598e4210edf7498e420069f7498e4210ede7498e4210edc7498e4210edf5498e4210ede5498e4210e9e5498e4210edd5498e420069d5498e4210edc5498e42026de7298e42026dd7298e42026dc7298e42026df5298e42026de5298e42026dd5298e42026dc5298e42026df4298e420269f4298e42026de4298e42026dd4298e420269d4298e42026dc4298e42006df7198e42006de7198e42006dd7198e42006dc7198e42006df5198e42006dc5198e4210edf4198e4210ede4198e4210edd4198e4210edc4198e4210e9c4198e42026df2198e42026de2198e42026dd2198e42026dc2198e42006df7098e42006de7098e42006dd7098e42006dc7098e42006df5098e420065f5098e42006de5098e42006dd5098e420065d5098e42006dc5098e4210edf4098e4210e9f4098e4210ede4098e4210edd4098e420069d4098e4210edc409
  | 27 => 0xc7694c43605bd7594c4318f3e6594c4318f3d6594c4318dbe7394c4318ebe6394c4318f9e6394c4318f3f5394c4313f9f5394c4313f1f5394c4318f9c5394c43185be7294c43005bd7294c4313f3f5294c4313f3c5294c43175be7194c43005bd7194c4313f3f5194c4313f3c5194c4318dbf7094c43135be7094c43625bd7094c4318dbc7094c4318ebf6094c4361ebd6094c4313f3f5094c4361f3e5094c4361f3d5094c4313f3c5094c4318f3f7694c4318f3e7694c4318f3d7694c4318f3c7694c4318d3e7394c4318f3e6394c4318e3e6394c4318f1e6394c4318f3f7294c4318f3e7294c4318f3d7294c4318f3c7294c4318f3f6294c4318f3e6294c4318f3d6294c4318f3c6294c4318f3f7194c4318f3e7194c4318f3d7194c4318f3c7194c4318f3f6194c4318f3e6194c4318f3d6194c4318f3c6194c4318f3f7094c4318d3f7094c4318f3e7094c4318f3d7094c436253d7094c4318f3c7094c4318f3f6094c4318e3f6094c4318f3e6094c4318f3d6094c4361e3d6094c4318f3c6094c4318f3f3094c4318f3e3094c4318f3d3094c4318f3c3094c4361f3f2094c4361f3e2094c4361f3d2094c4361f3c2094c4361f3f1094c4361f3e1094c4361f3d1094c4361f3c1094c43605bf7654c4315ebf7654c4315cbf7654c4318dbf7554c43615bf7354c4315ebe6354c436079e6354c4313f9f5354c4318f3e5354c4318f3c5354c4313f9c5354c43005bf7254c43185bc7254c43005bf7154c43175bc7154c4360dbf7054c43135be7054c4360dbd7054c43135bc7054c43606bf6054c435febd6054c4313f3f5054c435ff3d5054c4318f3e7614c4318f3d7614c4318f3c7614c4318f3e6314c4318e3e6314c4318f1e6314c4318f3f6214c4318f3e6214c4318f3d6214c4318f3c6214c4318f3f6114c4318f3e6114c4318f3d6114c4318f3c6114c4318f3f6014c4318e3f6014c4318f3e6014c4318f3d6014c435f63d6014c4318f3c6014c4318f3f3014c4318f3e3014c435f71e3014c4318f3d3014c4318f3c3014c4318f1c3014c435f73f2014c435f73e2014c435f73d2014c435f73c2014c435f73f1014c435f73e1014c435f73d1014c435f73c1014c430267f75596423ae7f54596423ae7d5459642004ff7359642004fc735964212e7f535964212e7c53596423aebc4359642024fe7259642024fc72596420267e52596420267c5259642004ff715964201cfc715964212e7f515964212e7c5159642004ff705964200cfe7059642004fd705964200cfc705964212e7f50596420067e50596420067d505964212e7c50596423aebf4059642006bd40596423ae7e74596423ae7d74596423ae7c74596420067f73596420067e73596420067d73596420067c73596420047c73596423ae7f43596423ae7e43596423ae7d4359642
  | 28 => 0x95433f67d40d95430063d40d95433f67c40d95430067f30d95430067e30d95430067d30d95430067c30d95430067f20d95430067e20d95430067d20d95430067c20d95430067f10d95430067e10d95430067d10d95430067c10d95431567c6559543615df7359543604ff7459543006bf7459543614ff7359543006df7359543606bc4359543004ff7259543024fc7259543004ff715954301cfc7159543004ff705954300cfe7059543004fd705954300cfc7059543606bf4059543006bd40595433f57e76195431567e76195433f47e76195433ce7f64195433ce7f63195433cf5f43195433cf3c43195433cf5c43195431557f70195430057d70195430067f60195430067e60195430067d60195430067c60195433cf3f40195430073d40195433ccfe7694d433f67f6594d430be7e6594d430be7c6594d431575f5394d433f79c4394d433cd7e7694d430067e7694d433cc7e7694d433f67f6394d433f75f4394d4318f3c4394d433f75c4394d433f71c4394d4341e7c6294d434167c6194d436457f7094d436457d7094d4363e7f6094d434067e6094d4363e7d6094d434067c6094d433f73f4094d4363f3d4094d43014fe7654d43604fd7654d43014fc7654d43005bf7454d43015bc7454d436079c4354d43006bf6590d430073f6590d430063f6590d4315ebe6590d43006bd6590d4315ebc6590d430073c6590d4315e3c6590d43015be7390d430179e7390d43016bf6390d430179f6390d4318f3e5390d43635bf7090d43635bd7090d4362ebf6090d43146be6090d4362ebd6090d43146bc6090d4362f3f5090d4362f3d5090d430067f65d89430067c65d89430bcfe75d8943004fd75d89430bcfc75d89430067e53d894310edf43d8943006be43d894310ebc43d894310edc43d894310eee42d894301cfe71d8943004fd71d8943004ff70d894300cfe70d8943004fd70d894300cfc70d89430067f50d89430067d50d894310ebf40d8943006bd40d89431557e75989430057d75989430067f65989430067c6598943006ef62989430057f75589431557c75589430067f65589430067c65589430067f65189430067c65189431b6bf6418943026ee6218943006ed62189430067f65d85430067c65d85430bcfe75d8543004fd75d85430bcfc75d85430067e53d8543006be43d85430a6bc43d8543024fe72d8543004fd72d85430a6f641d8543004ff70d854300cfe70d8543004fd70d854300cfc70d85430067f50d85430067d50d85430a6bf40d8543006bd40d85431557e75985430057d75985430067f65985430067c6598543006f761985430057f75585431557c75585430067f65585430067c65585430067f65185430067c6518543196bf641854301ef66118543006f5611854318dbf7694c4318dbe7694c4318dbd7694c4318db
  | 29 => 0x18f3e53d86431b5be72d864318fae72d8643005ae72d8643005bd72d864318fad72d8643005ad72d864318ebf62d8643006bd62d864318dbf70d8643145be70d8643005bd70d864318dbc70d864318ebf60d8643006bd60d86430073f50d86430073d50d8643005bd769864315dbe75986431973e759864315d3e7598643005bd75986431973d75986430053d7598643195bc7598643006be6598643006bc6598643176be639864309f9e639864318f3e53986431b5be7298643005bd7298643006be6298643006bc6298643196bf619864318fb76198643195bf7098643145be7098643005bd7098643145bc7098643006bf6098643006bd60986430073f50986430073d5098643197b71098643007b51098643005bf755864315dbe755864315dbc7558643006bf6558643006bd655864308ebe635864308f9e635864318f3e5358643005bf72586431b5bc7258643006bf6258643006bd625864318fb76158643196be6158643005bf7058643145be7058643005bd7058643145bc7058643006bf6058643006bd60586430073f50586430073d5058643007b71058643007b5105864315dbe7518643005bd751864318dbc7518643006be651864318ebc651864318f9e731864318f9e631864318f3e53186431b5be7218643005bd7218643006be621864318ebc6218643195be711864318ebf611864318fb66118643196bd611864318fb5611864318dbf7018643145be7018643005bd701864318dbc701864318ebf6018643006bd60186430073f50186430073d50186430bcfe76d95431567e65d95433f4ff74d95433f4fd74d95433f67f54d95433f67d54d9543014fd73d95431567f53d95433f6bc43d9543024fe72d9543004fd72d95431567f52d95431567c52d954301cfe71d9543004fd71d95431567f51d95431567c51d9543004ff70d954300cfe70d9543004fd70d954300cfc70d95431567f50d95430067e50d95430067d50d95431567c50d95433f6bf40d9543006bd40d95433cd7e76d95430bc7e76d95433f75f43d95433f73c43d95433f75c43d95430057f70d95430057d70d95430067f60d95430067e60d95430067d60d95430067c60d95433f73f40d95430073d40d95433f67f74d95433f67e74d95433f67d74d95433f67c74d95433f67f73d95431567e73d95433f67d73d95433f67f43d95433f67e43d95433f67c43d95433f63c43d95430067f72d95430067e72d95430067d72d95430067c72d95433f67f42d95433f67e42d95433f67d42d95433f67c42d95430067f71d95430067e71d95430067d71d95430067c71d95433f67f41d95433f67e41d95433f67d41d95433f67c41d95430067f70d95430047f70d95430067e70d95430067d70d95430047d70d95430067c70d95433f67f40d95433f63f40d95433f67e40d
  | 30 => 0xf72596431b5bc725964315f3f5259643005bf7159643195bc715964315f3c5159643005bf7059643145be7059643005bd7059643145bc7059643006bf6059643006bd605964315f3f50596430073d505964318dbf7694e4318dbe7694e4318dbd7694e4318dbc7694e4318f3e6594e4318f3d6594e4318dbe7394e4318f3f5394e4315f9f5394e4315f1f5394e4318f9c5394e431b5be7294e43005bd7294e4315f3f5294e4315f3c5294e43195be7194e43005bd7194e4315f3f5194e4315f3c5194e4318dbf7094e43145be7094e43655bd7094e4318dbc7094e4318ebf6094e4364ebd6094e4315f3f5094e4364f3e5094e4364f3d5094e4315f3c5094e4318f3e7694e4318f3d7694e4318f3c7694e4318f3f6094e4318e3f6094e4318f3e6094e4318f3d6094e4364e3d6094e4318f3c6094e4318f3f3094e4318f3e3094e4318f3d3094e4318f3c3094e4364f3f2094e4364f3e2094e4364f3d2094e4364f3c2094e4364f3f1094e4364f3e1094e4364f3d1094e4364f3c1094e4315dbe75d8a43005bd75d8a4318dbc75d8a43006be65d8a4318ebc65d8a4318f9e73d8a4318f9e63d8a4318f3e53d8a43195be71d8a43005bd71d8a4318dbf70d8a43145be70d8a43005bd70d8a4318dbc70d8a4318ebf60d8a43006bd60d8a430073f50d8a430073d50d8a43005bd7698a4315dbe7598a43005bd7598a431b5bc7598a43006bf6598a43006bd6598a43186be6398a431079e6398a4318f3e5398a431b6bf6298a4318faf6298a43006af6298a43195be7198a43005bd7198a431b5bf7098a43145be7098a43005bd7098a43145bc7098a43006bf6098a43006bd6098a430073f5098a430073d5098a431b7af2098a43007ad2098a43005bf7558a430073f7558a430053f7558a4315dbe7558a4315dbc7558a430073c7558a4315d3c7558a43006be6558a43006bc6558a430f6be6358a430f79e6358a430f69e6358a4318f3e5358a4318faf6258a431b6be6258a43005bf7158a43195bc7158a43005bf7058a43145be7058a43005bd7058a43145bc7058a43006bf6058a43006bd6058a430073f5058a430073d5058a43007af2058a43007ad2058a4315dbe7518a4318f3e7518a4315d3e7518a43005bd7518a4318f3d7518a430053d7518a4318dbc7518a4318ebf6518a43006bd6518a4318f9e7318a4318f9e6318a4318f3e5318a431b5be7218a4318ebf6218a4318fae6218a431b6bd6218a4318fad6218a43195be7118a43005bd7118a4318dbf7018a43145be7018a43005bd7018a4318dbc7018a4318ebf6018a43006bd6018a430073f5018a430073d5018a4315dbe75d864318f3e75d864315d3e75d8643005bd75d864318f3d75d86430053d75d864318dbc75d864318ebf65d8643006bd65d864318f9e73d864318f9e63d8643
  | 31 => 0x9643004fd71d96433f6bf41d9643004ff70d964300cfe70d9643004fd70d964300cfc70d96433f6bf40d9643006bd40d96430bcff765964315e7c6559643015bc745964315f3f54596430067f75596436067f545964315ebf545964315e3f54596436067d5459643606bc5459643014fc735964315e7c5359643004ff7259643024fc725964315e7f5259643606bc4259643004ff715964301cfc715964315e7c5159643606bf4159643004ff705964300cfe7059643004fd705964300cfc705964315e7f50596430067d5059643606bf4059643006bd405964315dbf76552430bebf76552430bcbf7655243015bf75552430173f75552430bebe655524315f3e65552430be3e65552430073d65552430bebc6555243005bf73552430079f73552430079c7355243016be63552430179e635524315f3c5355243005bf72552431b5bc7255243256be625524315f3c5255243005bf7155243195bc715524315f3f5155243665bf7055243145be7055243665bd7055243145bc705524365ebf605524365ebd605524315f3f505524365f3d50552430bcfe7694e43014fd7694e43015be7494e43005bd7494e433f73e5494e430073d5494e433f73c5494e433f79f4394e43006ef6298a430057f7558a4315d7c7558a43004ff7558a430067f7558a430047f7558a430bcfe7558a430bcfc7558a430067c7558a430bc7c7558a43006bf5458a430f6bc5458a430f6df4358a430f6dc4358a430f6ee4258a431b6bc4258a43004ff7158a4301cfc7158a430f6bf4158a43004ff7058a4300cfe7058a43004fd7058a4300cfc7058a430067f5058a430067d5058a430f6bf4058a43006bd4058a43006ef2058a43006ed2058a4315d7e7518a430057d7518a43026ee6218a43006ed6218a4315d7e75d86430057d75d8643005ee72d8643005ed72d864315d7e75986430057d7598643006f76198643004ff75586430bcfe75586430bcfc755864308ebe5458643006bd5458643004ff7258643024fc725864308ebf425864308ef64158643196bc4158643004ff705864300cfe7058643004fd705864300cfc70586430067f50586430067d505864308ebf4058643006bd4058643006f71058643006f5105864301ef66118643006f5611864315dbd75d964315ebe65d964318f3e65d964315e3e65d964318ebc65d964318dbe73d964318f9e73d96430059e73d964318f9e63d96431b5be72d9643005bd72d964315f3c52d9643195be71d9643005bd71d964315f3f51d964318dbf70d9643145be70d9643005bd70d964318dbc70d964318ebf60d9643006bd60d964315f3f50d96430073d50d964315dbf765964318f3f655964315ebe655964315ebc655964318f3c655964315e3c655964318dbc7359643606be63596436079e635964318f3c5359643005b
  | 32 => 0x80000000005000000900040020004000000000300080040000000003c00000180000020003001000c001800100040080018001001000300080020000000000c0020004004000000200140070014000002400500000020020001000401100040060000000000000100000070000002000000f00040000044013003000200180060000000003400200000000000000000c0010004001000000600080010004013000c00e000c002000400300140030004006000400b000000700000000000020000000000040040020001003c00200080000000001000001b00540010004000000000000080020004000001800300080150004000000000200000080004000000400000300040004009000000f0014004000800a0004000002400000340000020009002c000000c0080000005000400200000010038012000000100000000018009003400000080000018002000800000280080024001000000000040000014013000400600000006173c54d8d540bcfd74d8d54686bd74d8d540065e53d8d54616de43d8d54616bc43d8d54024fe72d8d54004fd72d8d5401cfe71d8d54004fd71d8d54004ff70d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54616bf40d8d54006bd40d8d54006de30d8d54006dc30d8d543f73c5498d54006df6398d546073c5458d543cf3c5418d54006dd6318d5418ebf7418d540bcfd7418d543ce7e5418d543cebc5418d543ce3c5418d543cedd4318d5418ebc4318d54024fe7218d54004fd7218d543cebc4218d5401cfe7118d54004fd7118d543cebf4118d54004ff7018d5400cfe7018d54004fd7018d5400cfc7018d543cebf4018d54006bd4018d54006de3018d54006dc3018d54024fe76d895459f3c54d89540bcfd74d895467ebd74d895459e7e54d895459ebc54d895459e3c54d8954004fe73d8954004fd73d895459ebc43d895459eee42d8954256bc42d895401cfe71d8954004fd71d895459ebf41d8954004ff70d895400cfe70d8954004fd70d895400cfc70d895459ebf40d8954006bd40d89545a73c5498954005de7398954005dd7398954006ef62989543af3c54589546773c5418954026ee6218954006ed621895401cfe76d855444f3c54d85540bcfd74d8554004fe73d8554004fd73d855444ebc43d8554024fe72d8554004fd72d855444ef641d8554004ff70d855400cfe70d8554004fd70d855400cfc70d855444ebf40d8554006bd40d855466ebf64985544473c5498554005de7398554005dd7398554006f761985543773c545855466ebf64185544373c541855401ef66118554006f5611855415e7e65d96433f73e54d96433f73c54d96433cdde73d96433f67e54d96433f6bc54d96433f63c54d96433ccfe73d9643006de73d9643024fe72d9643004fd72d96433f6bc42d964301cfe71d
  | 33 => 0x300300040000000000c000001c0090008000000400000380130000000000c00000080020034004003c01d001000000000120000004002401000000010030007000400700000050008004001800400080090008012000800000fc0000000006000000500000020014011000c00a00000030000000000000000080040058000001000f00080030000000000000b0008003001400200000070054000000000a000003500040000000000000c00000000160018000000000500000030008000001c000001800c000c00b00140020000005004c0030000000000400100240040008000000400500180070010000000c00000000010004007000000d00280000018001001401e000800000080010000003003400300000000000004001800300480020098006001401100080010024005004c008001000200080040004001000c0000008000001c0010008004000000200000020088006000000000040010054003000000000000010000003001c00a000000600580030000008002c003001c0000004000003800800000010004000000000600000100030001002800800040060024000000c00300040070000003000c004002c002000c000001c003000000500000020000003000000600340030034000001000100080000010013007000000380000000017000400100000090050001000400000280050008000001c004000000d0000001000800500540000004000000000d00040020000013000000000100030000000000c00000280030000000000c000000c0040008005000c00000040020004000000400500040280008004000c00500080010000009001400500100020008009000000000180040000004000400500280020048007000400100000000000000001000e000c0030000000000c00800540050040000001800100000020014000004000a0014002002c0080000007000400200000040008001000c0000014005000c00a000c00d0020002001c001000400b00080020000007000000c000000300440210000000000800a002800d00380010000000000000e00000000008001000000900000010004000001400b00180040008005000800300080010008015000c00600000060004000000000100000000030000000400a0000002000000b002c000000000000000020004000000c0020004008001800100000000008001000000500100000000001000c0000000003000c00100000030000014000c0050040008004400100000020000003001400a00000000000002005c0040004001000c002002c01400a0002000000e000400100040000004001001400f00080020004000001000000800000004007003400000200010008001000000000000010010003000000c0000004000c000001400100080000008000000400c000c00100000000
  | 34 => 0x800000300180008001000000000000080000000000000000200040038000000400000440000008000000000500480000000004000c0010000000000000600100010000000000000000000000004011001800700080080000010004400100040000004000000400200080010008000002000c0004004001001300300010000005001000000080050000000000c001003400100140010000002000000b0008000002c00e000400b000800a002400100300020010000000c00f000c01c0004001004000000040000008000000c0020008001001c0000024000000000d0014005000000c0000001000c0030004000001c00000300000004006001400f000c00700080110000002000c008000c00c00000100010002000c003003c00000080000004000004400000000000000007006800200040020000002000000c0008005003c00800000010020000000000000c8000002401c000c0040000006001400f000000300040030014001000400500140000008002000c000000400a0014002001000000000000000005001000b0000000000c00300000050004001000800200200010000000000000100040020058004000000100180000004003000000d000000b002000b00080000008001003c00d00000000010000001800000000010000000001000600380000000000000000200040030014000000000300e4000000000a00000020008003002c0110010000000c00c004c00000080040008001000000d00300000014002000000000080050010001002800b000000100140020000001000400a0000000001c0020014003000000200000000000001000800200040000010002000800800040020020008000000000000060018002001400000ac0050004000003c0000004008000400100080030000005000800200240220004000000c002000000d0000003000800a0010000000c00a0038002001000300000060004000000800100080000008000000c0030000001000c000000c001000c000004000900080050014002002c000000c0090000000003400200500020004000000400e00400030038011000800d001c00e0020000008c00a000000700000060014015000c0000014000002c001001c00900000080010008000c0000004001000400200000020008000001c000001400100000010014001007c000001c000000800c000c000000c0000004001000800600000070004005000400000000020014012002800000000070028000001c00c000400800200380008004004c0000020002000000000000030004004000001d0000002002c0000054001000000000100150000000002400b000400d001c00300540010010002000000000040000008004000000100140130008012002800400040000000008000c006007c000001000b00140010038
  | 35 => 0x1000000000040040000003000000500000070000006002c00000040020048001003800200140030014000000400000000160000001000c00200040000000004000000f0010005000400000040000000002005000200100000048003000400000140000050003001400100000000004001002800600500000000003000000100380000000003000c02b000801a00100020014003000000100000040000000001800600000000000001000001100140050004000000000900000040038000000400900380100000001000000100000000038008002c01800040010004006000000100080020000006000000100000000034003000400200000040000008001800c003c0070014003000401100200010000005002000c0008000000400200080030008002001000000040010010002001800000040030000003000000400080000004001000400100000010000002000c000009c00b0018005007000600000090000001004c00300080010038002002c0020000001002000500080010018003000400100240000014000000800500080000010000000400000180000004001000400300000060034003000000600040040004000003400000000010008000001800300080000004000002c000000800600000000000000000800500180040008005001800700680060004000001000000080010000007001400e000c012000000000140000004009002400000000000010000001400900600060000005001400b000001300000050018000000000f0010003005c001001800b000000400200000000017000800000000030008009001400000000010010000000c00900180000004000002000300140020000009002c001000000b0008002000c00000580080000000000401900240000004007000c001000400b000c001000800100000050000005001000100000000084004000800000000010004007001c010009c0010010000000c00200100010000001000000000000050020000000001b00000030000000000800000040090048008001800b000000a00080050010007000c00200000000000000002800b000400200000060000005001400000000000000006000c0000004005001400300040030018000000c0000000003001c000000000c000c00300040000014005004000000080020000005005000000040010004000001c00600040020068009001c000001c00000380000008006004c00300000030000000000800400180010014000000000000180000008001000000600ec0000008000000401a0010000004c00e0000002000000f00000080004005007c00100180000000000000c001000800200000050008001000c01b00240050024002000400000040020004005003c001000c000001000200200040014008002c001000400a0000000
  | 36 => 0x4000074b78fc00049399b61798d9a00000009cdc3301be22c4000000087f80005d880008f4a8185e68ac66dd123c5a800002ac09f200024981b91e3e0000ace0002b7fa929848a88a17d6391704a3987ba3a1905900016aa7840edf22428e861493167af241e0be984233a00412138cdc0000f9c5acc176000045350c253e8568000000194e9a8800000026a4000136800000000002a5684bd89d85f800000009be00000d60d827e600000003db8fe00000916572000000000004830a4289297fc1e900000141cde1448c3600009ab000000042e112600000009380000a3eab309988000a1022ea38516b400007b96c417b300007b4a47800068b86c143b11d060490287230b750000000000130273d09360da4e240000000a2a8000000014c617027258a40002ab11f0000120600018264e0a8c417d067e0000000165e1bc27e9ca83699bce00011f8aac81b16b695f84a382124532b5e00013a4010048b00000008528000000132e6d30000231aac2218a9169d984b300000000a7aa060d989440002488910149a857923886a000000020caa9c000000007a2000000057693200000ee0a1d98147548000000000000029964f680007a6000034c98f4a62499645505ca1f10ec280100000000000678060a407800000029b689600006f50652000000045440000001250000000077620321b027b8000277c0bc91f2a0d62382e0464a5228d6024a1f969c415992c400002744bb00ff114e79b19af9b200008f7a3ec9960000000062438997b47eb096476fa3d0103593447b00005b000008cfa6faa31c3ec1a64828018030e718400000000d9911863e4969b4e1409478343972a0001d88000104d0000000343253474b6a6267a8fa82eea674000000000029582d0c0000001797471000000000000001cee60f800000012f00f5160400d400000006ee3cd000000007b7960146400080020004003000800a0004003002c01d000000000040080028000000000100000010000000000402100380020004009001400200000000004000000c002001c000000001900000290000001000400100200040044012000c00c008c00500000000008007003400d00040000018000000c000004c001000403700080000000002000800100080060000005000000700080010008000000c0040018000001c00000000030018002000400000000050004001000400100080040014002000000b0004000000400200000040030006000000000000030000002000400000000020018001001c00600080000000002000c00a000000b0000001000400b0014000000c0000000008000000300340010044001002000300000020004002001400700200130008000000c0010010002005400400300060000021004000200100030000003000c007001000100100000000003002
  | 37 => 0x682870f38000000000092f06a20001dc65e7000090ea0f48a492e22c74bdc45498d42b60c445b3000095c800047dd7bc00019c19f0ab3c74c0574693968a0001afa5d1921c5ba00008cea54900001ed6b5869d000250b34b13729120000000000000000003e9a97a49c90d022300000000000000000014989ca70e800001c8c528219c2025e9fa08dd0ffe3fed08e56ea686923654a4c719482259ad8176548404286c661a8afa705df2e0bf2ada00027c000020d0a2c97847458134000000000000000000d9e4ed9ffe7b2800025080004d800000000000000071a0000000901a58897080006118834867eb7e66900003b623d47f8000057126f623e240a7ac800025d800000027e803d000000000000000b51000235a55c00005661068705a1e8743000026b98720b10000aa62b0492b00002a5800030faa3013f854d2071a489520ea4052c9027569da564c800000028a16da0000000035c000000036500003128000000167000001160000000ad5daa839d196e0c3000000012a00001700000000051d8000000000038d84aba92682a3b4400000026d81d100006940f6269e08d12919e627a480000001ce883c90c202a00000000bde7ac168c00018de651000000000000001f7686808f40000a5f2cc541e000000000017940000f1600009d60e100000d911ba902033a84604e22328f768e199f63ed9482367020437243429e000000001af83b680000002112ae1629e119073896190ae00000003a81f8289908f180196fc4a01a9087c079a8db9fee1585db46ef16ee25b294c149d0b22eb400010404e765c103a37a1f94000249c9879c092cd21de1391a4415b8000000000097c000068720a800024d800000001f90000000000000006d29dd1b045db6a7a0000b8800022f400000002d0800000000000000000000000063f07d03ff12f20001e864318000000000090a80000000000000074000022ac00000001e4000076612de20b000000000000000db5a34000046203a638e0000148e4f993710bc402cd8c000021a55b0522666144f79517a9000281c000000094b1c9857d18d30000f4c078263a000000085d0abc4e1a7a81c09590ac380008fd878c12900123d7220a4c187b325d0c220caaacc5d9260000000000001d685c39f6405d00a42ac5c7600000005cd0bda7b800000000de29e55ffc433c000a6d05d686218700000ce2000218482080009a5000062d000000000006f0c000add000096a17426ba0c17000000000000000e580004e0003c5ee8aa55c680000b70ec012ca19609f97e22e1964e00009ba10f80000000000000000033a8000196127a97000000000000000000038480008538000605935099f167606c0cc8acde1fc0d94dee9dda64a084000000000aaad5400037510537b31f2362e0fce2f2000014a17a295fa0a
  | 38 => 0x90a33208a99304ad01ea9e421c893a381875600000004b280008898bca7b39b5023686cc06c8d4091d23c851083a547b98d06ea8000a2d9a0c0be139aaa69e9e78988646f55b82a619087a3cd9a264b880c59e06e01de133c0911f3833020c436d8000a8e98f26a0103c0000185000054913a400000000004e4119a70d8f30709000074e000000000002a4880a93c04aa10110c8742811b589250c9e98000000193000014c20000f3c4421fc290d18342da04ac000000000000d20000000932000007b80000000000000000000002e04cfc000a209dba00001ce00008d90002a1da94224c000000000016403070b22419a16469d000023340002e100000000000788aa78108800000000000000bb781b1aaa00000000000000000000001d80003a5859661792d27ef83c0000000000000000000000000108aa75a4c200022ec00000000000000a974000ade1cb6396891400006b4adc28e46080a2e8dc809e2ee40000001ce47d196b26978f98000282286f9ba30000000000227072795b20d00000740800000000008da143ea2708ec138e28e126000000002276b1a1209c10000313000004f26d65500e563de804285e89461b723581a98c8700000002a72b6b00000000002378013876687306e285b0144718dde20001f7a68093980002a3292d8b197020d809c193226ac066a7dc1710231d6ab38c1b724448cbe13962960a10eb486998861368f2e355ccb094884ae3a5051faa897c64b188d201c08501a408ce9c999ae50b29da1edab5886d415a04111f9000005f4de839415125a46fb8000000010882003b007d40001170000000077765523f400000000000e3e72a80002c5000000005062eb0000000134a0000e1700005146570266740031a8bba7ca9651b160fcd88c8821c80add959c6d4dda02fe92b896ca46c018aa640f31d9a5b10b546d62b3827e5ad41e08f0290311a459f1096811a7ac7f194d80000ba6ad90a7800001939f396148280000776800013158a10cb80f858d8c5024ccf0400006de9849c1a0000000090951ca8e416830520609d0263247a1ea66b909b62858b322829fd833992e83558fca5b5806a7fc8fb82e0a60c782a4fe102ea6a000243c0000000000000034280000000000a2000000002002a180c6a76297de1a7800025280000001d310000000a7a80009b780a60002b600a400003d5899c5b7a4ea000000000016e21dc00003d112ac0fc868694a8000000000031a40009070000000000000000000002b4425ed9765331b9c747400000000002f3a12e9598e8298d105262110b0732ab090000000518ab80381c0003b140000000485ac9c00000000002e14000850a4260000000a3d646828f047268ec7fd9c31af602c906c00000000001b702c540004ea967e5f215e0a948f3845a000024b00005fa800028
  | 39 => 0x52b20a48800022214523b240009c38c1d478a5cc63e000000013e6584a3840001ca2401a7a20000414a69000009c01f061fa76e000183a78a10de07d80009d6210c8d5837612ea322aab0a7e8c91aa68790d6c5cf80000555faa3a380002a915b800021c6a3bea912d7000043d88425e80000000114a0000000000000000000000000c3200006cf19dab547ec02160001cae0000000000000004da83067154bc2ab800070613e21d14cc471500000000000000280e14f52e779c0000000000088d01c43c8a18a7bd4a36000096d00000007a200009190f48a33a6729e600008be804656b00008ed000058ac02600023b687c9b600dc8e6289b800000000000000000566800000000002eedf4c00008af000094c0000bb600020840000b94301aa5f000000086a8000000000000000007ada66d32e400000000000002a360000000030a9e6104800041f80000000000000152600c400000000008b7800000000001b380000b60fac0e34904a2301942aa28040175ab22fb80000001ae600000001ba07f00b921bd4a30b626c68ae308a046e00000005df41f17784b3c1162a8645e192275b897c9cb80005520000000000000013d6812a648759884c0001a9eadc99b86900f6614d8c8600003ef6cf800000014fa0001e740001ca40002100000197a00028ca0000000a91cc1000000000001e002c600000000000488813fa870000320a91845f80000af800000015167a593310000b2959c80cc19727fe00015d210e0000000073074dc00022a0000211936a6de800000008e45e61984139904a5d22a1600000006a30000000000084f0bdb00027080f7098228b00007b900008d300000001cd00000aef161879c00000009068000000287c00000004bb0000288800021f00000ce00000000283982000000026900000000000000000000009e792e400000000ecc00006580000f62ae0a220000000125200017d00000cd46630000941e4e2748800032799daa7b130e622aa4600005320002a3c8ac8000000000076989b2561800091d54483b19ef08ab84691c496bc1b58e044bd0786226111834d82d62ca07aa00000009ca0eec39f80000000764000222a000285000027bc00000002c28a3280987ce9e900e47281e2c22926541e526a679680002c4437023cd8d147e88b4178949273b10e20bd22d85ae15126ae4000000000000000008ff27cc00009c8000000000000003fc80004154000000005b0000000a92c00053480008b8000000018310001c8aa4c8000415928a000252826416ca0000000000137c07a43b241002aca88c000000000031d159646810be0aa9893689255c000000018a800000015ae3d5000000011008738c2a361a4be2018a4100000387da80009438000ae08c9c0e38000ab49bba87707f469c9b240000000151e9fe0000f
  | 40 => 0x1ca951964104b01f845c94f600ca80a93e97120e4852c065400000000005b20000000000050680000000000000000000000000000cfa0002af8a9ca54b83e87af7df868077a8000000009d0000fdc905ab1000001b68144d4632aaa9c5d6a0384612650ac9a3424e71cc4a300920000000020dc00020f1dd65429205a250dbc06d000067f800042880000001a82000280823780009d200006f88c2e000061e000000001240003e1233463768286ce8670954c2a80000bd0719800088c086a6b087be7590e57a5f9aae09743c60000000000000068194ae4d10000000250050b873c047c00093d0cf700007ec1f4a66e00000004f800a24fa059c00024aa0000b8c4a8e09e59d263813400009e680000000c94000000000000000664000000143c000000083600006c088527250000328239c75da06e4c60000000011c0002abead0947a86d0ba508084701e61408487800000000007b18034450000004255a4146000002719d200001fc7d3a0ae474800078324f213720b86f1a2780000000731800079781898bf16da000000027797c30000fe42b8a94000002ca510000000025fc95a84440000a6e33f00a045427942cc000025aa72c000000000000009b398d6000000000000000000000451a64000017605a480009d11158000000040e40bf382975e1348000000145432921485a705531df8000305a092000085600000007fd8000000101a000027a94b8a30670eafe8b5a0d400005ba0001bbb0000000000000036a8000000000000000000000000000082e39c0758860000004ca8f8000000022ea6c4000000033926460001cc841804d4084423c34a00000000000000029100000004a91b2ea1c000000005ae0f111f52e6a5a24cb4afc67d000039019020d62910000197e00000002041c88000285437f0b5a15e013e667982c000000000007460c780002a3a13e539000045749f80000e763b49bdc000080e815c000000011846b8000000000000007b27d21c561e56aa800004a663484b8785293c000000000000be0001fc33ba400060200000001f6c00010320000da22f180009b400000000000120c0000000000006cbe200000007d9a2e880f416e00000004af9ef240000006089fba86300c800029788cc1435000049426b27625080000000165205a94904a894c100000003ecc0006d9996c5e7cb041998db48dc095691f6aad73ea01a00029f200000004168000000000000009ce0000000263c0001e2800031f037a6e417580001a084c7811e93181c2037053e38898fa00006fb00013740618000000117a000163c000000018c0887a8616af6278b2f2aca45274b179b8159f9000000003c01db08e9a4a634f1ba40002a7caa402ee00000003b20fe68bd9bf839a08040000000000253540b8000467072684703569230c72760154e8
  | 41 => 0x1e7c0000ea2166dc821d51cd8485170c1180478949018e736800000000000001d626770000000000000000002ec94ba6531d2062d801f825265610247c000024a5a6715d000008768379bc118d02de0002b4d00015ea25bcb449b927f40001f790001a5c2980d6431995fa291290a07d17ae17724a16a4826c00225be5d000004281a2d34f8aa690880000000b1740922841959eb4123284a4222438a3881d60000000000000059700000002b3535880ee00000005032505a37000052303336efcb6c9a706169a7991e292244533180008f8000095f0000302800054f07ae8db011437d5bc838f22e66300cce8670000000051d0000c70aa5270a0000b0ca059f5a00000007bf00000f240002a604de16e000087e25187c020f89180fa200000008aa1bac98280d01651fb70001b0897495b00001f720122042000020c62c995a00021f49caab4c00000009bc054f5f605b6270e36a1c9259e2e91e1a2dadc4a93a1bea00017e40000000000258e96a800017b800033f8be644105f000000005f3833ca0000003938ca232f5d2439627c89ef94fc6f608f72229c845ac15368871bfd77800e80d3020fa67a90626a5a00996a5d6359800051584e03a79da100000000000e4a56be1269bc9a429c89d8600018ec44583ee0000b6600000000000eea3c81f041200000000000000012b260100000001c860002814763800000010040001a70000000000000004928000000000000008a018b96c985808f27940791000000010c0be09fc800000722ca7fd125c3b9942d47f97b068c826e0640374a032146000028500009c20000184000000001b8a00000046383b2b1b4430c0048d800000015c61e810575ca0ae6317800000000009204000000076b35f096901a000097d0000294a9334a18000504a19218704fb354800043100e200012b000000000000000000131400000007a000000000000342000000018b0abc9910379d81e00000025340000683ea4f69d95a000000002fa2a10340a6e00f0811a000178a61b000000028f9000117700000000000000a43880251812466101ea09340222114282c000000000000001bb2b4e00000001a84b58a269da8000145a54bab1600000000000000986800022d8ec479b800000022b400013460000000a1caa3400000005d391e42d9e3043ba2a0248b81a8064978206fc34a55a25ee627c7322c226ac5a0812600013303cd8fc49ed973c36b8e5288b9fca4660cd89e0800000026a884898285a88432a35a73b27a1552000047e59500004d61e080000000000000047200000001e2440414b26f48133131000000029c400000008ff80000000ae834788dc2cb8000499000007286029b00b7a72f000082a800000000006f5e5c874f8000000000000000000000ed41608000326a75403a8e001931d7a74be
  | 42 => 0x7ed0b1e000000074ec00047680006bd09a06d28a0e0001d270000000000000009ecf1468d1b223080df2ac74281969800000000000000000657621a000101800002e82f8cd3091dc8fa146603424f16ea190000000000001c28000a73800089727dc140c68400025a090624af00017fe20d80008338000746d99600025e00002b0796d05900a219aca0682980001a68272d48800000002b105cc00000000000c0991ae96c30e0acc00017166a386c26ef800097a99b9000259a0ffc00000013f70000e9870380b823091ac6f92a2e00015b774e98cd65e00161f808008f09c1c9a22b0a00000000f2801a3348c42352a9f08fe2a0c3e00cda9a1d4361bd29a01caab1c0000b9c0001a2837dc57269327967498fc647edd580000d06000000000000000000f8e593000003257ac1c3800059e888604a0280a350000000056488b08e20000df42e5a8100000a14190a0a20590000682978628e1dac98fa1a10001ef79e4950889b19085881d4a2da855763fd53480720b051784fc4b000000000000000037d000262c000132c00011d82dc462846c99520001bfe0e283a914704886650000000000053780005050000220a5682a015b40001c0000025620001b5a000033e00019e40000e2031680006d12389000122011029541c30000712dd2a67200000000b4f00000000000030ad5800041883d2000282e58600000000de4545c0003fb80000001ded00000b33bca6e81c226c688d8e9a54ea7f613a1aba0002530486000032b1fecaa9c43c971000022714a28c080005a0ddbc4ad0328604000000916ec91c19e8a3c40004b680007ba80003858db10de0000822000005e8ccc46e27c47f680000051f187a40000000000069c4000898246d8978b704240000373c00000000000550b2aab40d8200000009af8000000000000000000000b6000021c500cc00000000003680b634ed26ca69600000000ad436496c2000213450080000000ab32160000371d10e72696ae8e3000001f91674701c7482c8268000244e0000000000000084793d8000000000023a2000000096b2ac400014720000000334069c2448c61875028e77c223a3470000a2798bda910de624e0000a430000000000025440008d180008938aee0a0a8065a4037e7f303880f9960c1991f1000012560000000000000000005aca7480003eaa8d8489a432869026223f0000aae0f4005c0dce814000000007e200000008ee199c5ebd1020000a5600022228c60aca00000000ff849300000001e480009b307ca27c17f41be8c1838a1d320000000000000010443bb7aaa1029bb166e68f97a700dd0fa0001e68758040e0000200a6a1dd400009d200019ab85a00009981f0c00000000000000000252068a80000002a76000190e9a112cc1c892d66f240000000000011c000
  | 43 => 0x666089c7279914281380003fd939297e0000083400000019500000000127979e0a8210966b58cf10b400000000000001c2865a958c6599cd4598800037a97b17ed9fc001680008f6906aa8216c609d2af100000005fba664000059f0cfc00015a19b49cd0000000221047d00009d94000a6f80004960c4e36e14f8514400097d40004ffa31a9e18456941800000013d494f464e000262e12c081a34400004298000000126c39e00008b200002840dc08161bcc4398000000143a52f8fd80d1800000000000000f4a56a88fe45b8000000260600000008b6800000015a21d8011277d00008e229e251a00006ff08e63dd0f3a633a47100000000000dd87e18b7e00000001c715fe00005a00bb01870af1f9f2872b4f00019b2000000000007ac000000000000006ab0130a249294859a6fc54ca38a0c48b380a18000953ab59281157483f000000000000000000000000022e000000000009cf00003380000000286e13d8000629d0720d0e49687ea06a000247f00000007e3191600028648dfc12a0208c60000000021158502b72b8300004ea000025c1028d50a4490508359fe6441800000000004c4800000000000000d538e06b3a91e40000000eb614580002f0871d0000e729a680005d70ef46c302400000fcd235c76a4268000032a2240cdc95c5e59aea71895106e3a5fa8dedc014981bb76ec295c46c26f41941d4caa98138091c4ec0a2421c85ba2d23d600007d78000000130411455305fc8eba6a623f020819faa7ea0655c600000001e603f08822936a0e828d0784738a0b42e40ebc8a29044adf40006e84df8000000082f80000000000708800007900009f50000000000024600000688af83d1ab690000000a729e32000084417b21d05139abc82f104c11aa62400015dc644e27c92e00002c028acaa48000000000030cc000000000055e24b2921d086aa2046700021d60352ab627400000000000000207c863a6764a480003f840001bfd520963023e00023169e700002c99bb67331cc000012ea0ba80000000db000000006b397f00a680004be10949478b40000261000019066b40000696824600004965dd000000000000000a4a096237a7cd8efe23aa8e000017141a280741dd6b7c36f80004d3814a2ddc0007cd2a891c3402c254116000000003be00000001f0600025ae8fca14c159a61c8650d540dac93d18384f8935a9702a8934877a2a120000eae00006c90ef14044a2176a00000002ae8edea04a3062818ddd3f5e6b47d81e4262596686c19174557a47249c255206aa0307b6a63c7b6231c00000006a8800000026ae7479fd6000037c000093100006fea3d86da0e180000000000a11941833d07c8131888e04b9bb23db1a1326c19049778f8200018583b416d45af68c600027a000000001a500008950000a5d203c000
  | 44 => 0x39882995221ec000050cc000525a27625014fe3620b69129c5d8abbab5a9cd9fea3ec400000000005679a174578000ab2000058d0000000118b79210d461d9960a76000000000000001d541978cba25c140096595a892784b57ec9aec0ae9a6239e8e1100022427eb81d001e1bca9348e2c6d08000233dd127d890cd4eb20403b880004a4046d00018a225800008a982201dba37ea631c14000187829746a85119e2a196aa8c77baa6827897a61748fd230222a0975108337291e13ca8e6682a40f276300008e00000000153845900001580000743a01200017080001aeea5800005ee28981018000753a8f770c04a2000287e9640000aa926ba260180ea09800030e966c307957c9739bc0062161c0151780917026015aa45e43713d0556a75a0001c0400016588eb9e180fdc0008ec0000000000037b0000a6880000000d2e7018a72a10878000023103b90df158180000000000000000000009265a0444c96e8954a86c520000000000020220000e057c480000000bb15090d1a8b0067aacd09480000a64000053b5218b2b0000000000108c525083fab98000a7422fe95e00003bf0000535000049087cc62ac0002b6a7d000023fa000000078e06480000000626e67f53d10f00001b7e55a832c00009c4000000000027c62998a3a03980007451b1e6640b4a13d1b5e57588ada70a1b831500009470d78958060418687ff5b81c705e445592f740e01c41d086129d364f017500000c7899ac000986113c000000000003f619193887bd80000002290619272480284be90b24a0000078d00000002638df032c8d8a9202972714249400016ba021286865b422300000000000504a86990a30f12480001b3855e8000641e34a5dec56c00005a219c9dc420f89a8ad89134a3a8ac80000332074a982000267e62a12e01cba83e72e00006431bec000000000018e09bb800086e80001308000ab6e2988e600004bc40000a71ea400000006c700000000dda000000000000002ea9d2b2d1400000000002d7800000000000000000000294a26228fc80b2af4000000098452446619790977000070d19884781ba6181a0dc13e4000000278449a0000acca04f2899b000e8000000000003d918f59218000000019e230250990092320000324000202400017e68948dd22dd8e6a000054887740001218b4c000234066480001aa91a847599c42f84d982bc000000000001500dba00021ee74fc36a9dca29a2250c045cb80004688f1273a9a758c480000002886a4a800000004f5000195e7ab00009ffc52d00001e81a800005a51f6e8df40006ad0000896a38b27015180e4000075b000000017cc000273a00023be95600000001e20000000084a01a40879b14767a06866a800000023ba42de88e000000037715d817217f85540e48ab502a600024ee5e31e1
  | 45 => 0x4f044c87a67ca3e29da1132aa28000188000000000000001f8e8f000000000000000000000020d24cd80002d0400035a86d000013a6799800055980000000000000000006f4d4e4b7000092c4000018c00000000002af8a8870a9daa0b982370000fea000000081d800000005b400000000001d280000c1a1e753ee0000c130000b332a500006e01c021e3c93054397be00027e43fea2b000007363461fd28032b4718998be000135ea902af05b420da205a9521779428000098c0000abb000217c1ea08ef0588e10000036e000057a9459666326015c49e14f21361b844aaa2be0258df627f8f865c880869609d44000155818f06f232d400029d0000ad9a630000000000013dd413e7da9d48f060002b1a00020964902396761052900014ca68e61043228576a091c40639dbf47d2973847293940001c4274448eb00019f09532ac09b091442fb1d1a730a3ea157a7b0a6a8b1bac185c60c2800086400000000aaa00000001d380007130e8aad298db078a28c614c09a6f81e34427150c10dab2b8668d202ed02d2ad190261e5800057880000000789685441832b8000584074a27f18a51c580007d600000001f526354000000291447ccac51ae91304f09dfe09799be4f90aec9f81c590542820000017100008e006700000000ad089100000000000000215c0000ff400004ee000058e00006440000f1c7df268a8c21d062dc90ce1f5a2946168f501a48238000000000000001ff98e6717933232100903fc1ed23868a037440bcb1c8000000000007a69b987f200004bf8000000000000000000001b6a0001ab600004c868f24f5000100e00022d47cd512e91e88122c490479be254403d91977e21940aaa805682da83856a639a77ea84e0a9000029b16ac0000000ab3aae84a117f669e9cf85be8148000000000018a440dcb4e99c220e60f00000000a841d680c645240009d0930a67003671329fd02f58000112a37c00018ea000000000000000000000000268941e0e1c30082791af9a6e000000000012c400004d600010200000598000189c1db1d358e41dcc62200008f617993a7688a37415b59fa9ce6aae54e0849073e77414a811680002a1905e66800002f485c243b83e20228c628d8982e157c20b0001a888a700007774bc400020ee61883e80001b180d48e6c7a324c400003de4f290465bc8100a320e59a410000000295662007de000054e1e7800048380000000000000000000000000000000a465c0a00000004e8a5143c7996841380000001b9a144018a77da71a50180008d98c67055854b0001d7e511eae4075027c3718fd33e91a22007693a85600004328000560800056f0000988200034d0000570cb6e4d9042451340000000a4c000116600007d80001d34000000000018660b0a03e8cb9b8a64a97b66b3031c00023ee00
  | 46 => 0xeb0bab96e00000000868000123a96480000fea86900005aa000160a855a1066bf004a479841c00000003af800080200002cb169e8d8000000000003cc8000000277e170000000028344a080002ce9f9a2c0964633c9c7c2cf800071f80009f593ea93e04914aba300000217200a828f5db096e7690000228c000ac64000000219e632c5e09d2800053382f024aa93039058c61f9800070f9de4000025a081a282000101500000000c8a5127fa21da555a490421000028f800039782cc3fa0ee753005be0d4016c2a083f857c000052aa3995ea000000018914f70000460000000020c208b1ae2271400000010ac4d4800072f800000028b09a600000fc000073386b289d271e5c28c2c000000003e8000695800098aaa5a00013be00000000000cf005bc00070fc00011983a30000000573a6920000000839a02a000000027b18a60001bc20001a77000004400015f6ac30cb472980004c908c10c200000002b18469c00000000001a5677a00001eb0000000000000040729f696f00000000000000000000025981ac00000001b287c8052e2de2b364ec886e909124ca4d155489e9f4422015eca6e8cec950a4583c980b087829de2310420a1b089217a834e21c26e26992b3e3f2482a2e4d75495e8ff80001e7686606b82b819cc1da16f650985e491988309288eee0ab8f109d19efe812439e000000067780004e120ac9da9b46a718000232d8999a0172c093120046480006f9ab02ab88afe0266716831a3ac3982063447847669a89946cb02074bf251129516962eb919e349aa2a98dca9000a13ef3a3077a7d0000043f10b671a8a9e514000068e87062d1dd4200017951a3000000006a4000085a6ee1c5200000000000b1c2769776000035e15197fb0824218a40a73e47f0e46681285a9719d720000000296018200000000001d3c77a400026a8000000186800001e638e9656235800003b00000000dc40002a4c000000054781780e9000011d210818000000002a3e000052a00018985c980001e4c00014c030487626689ac800055900008f39e46793800001703820001e1ea588000000008c00009e021500008a9221eaca80006e81edc00000000261cdc2900000a51205e000000000026360000000000000083aa4b0000293e94f0000000000000000000000000000000000026141d080007a8800048d1bb425c80667501e5c13c8d846280fd6520019a0002b680000d24600154636a116c2488908a898000000000084c01587991f5c2751e3a000000099e000054fd3e50000000383a68c15310ba260441e6a528fe9c0923e0079b3c0000762a1e0000689aa1400014a00001971000113a763e8f2650874c8c50f2469e4f6a81980cf4af177824f971c447028c991158892b8f88000235c58b8468025dbd660181ec1dd1dde64b1f2853702
  | 47 => 0x1b60001b7c2b000001dd973256f80000002116625197369f80007410a20ab280008e5204c2e798ae02ea652000152c4a5a89031599f84020484116e7d2a8785e83ab0fd41c246ca00019c20001194682de8a6b826b8099129800013d20002a8e72d00000000253000165e000122a000055100018ac337a46700004620000f9a45200000002444000000000007c653a98eb0000de5712170249fce2e886194600000005b91c466092b52031cf4e8e6c00031a093249f08f600002c0000000044500004ff040c9ee8c7e5a39db27f50c907bd16d250c8000000000019a0e0d000232a97c9dd27bf40000fd4d0400023c400013007cb05213ec000052d89a600022f012bcf0e4c31b484191f3a950084a0fa9e828e4a6aa7be87f60b6a35e02b000097299d62dce7fa946d45c652866c4739e72565001814040006d500003e507da8ce00005af842c000113843000008b309588c3091c000000059a8000adbab0800003364ad800068c51de5359f0a770059d67b1d1c58c80000000000a5a89844b400000001cd6878a8ae00022e2a4000005f68ba20000000a079fb32020e8862683d646aa00e0000a9a11500005f5a9f4049c0009d5889e0001e23aa8068281229c000015bb26e174a4848e0c88f800000000001820000456800093783f400000fc0001d467b00baf52d0000854887e387800062489b48f196f045f0d8e3ed294607c80004360d12a421ee8781800060611823744fda750c00000025e200881ac17fa8ba4fac7b87959afe61b80003692a60a5780006af80003249882000255468c2604000000000025e689a8cc28c29f56861946a51b11ea0000000000053a00001c84e8274e8172a9d8589db6a3d161e4fd0d4caaee06793023260eba8025e49db82618f2800003b60b393566798f1a8390ad6000024b6a187049d7107c00000000000000816800000000000000000000000083da02096716e64bba5b000008ac00027b200021ec67b800000002b86a9055b000000000000009db1f1c83826bc2d42280685a1e64008ca899a9c969fe25380001b64000000000008c900000007ae014e1ec513670400002145fcea1d234400017b7abb1d9073d9fc490400006981ba848a00004f10e640000eb000029b84f39f9e81ca1b0477132805809c90a280bc00016a85de980c00003a29bb4cf882698560001ddc410cc5846f9c4e394003e85a9cac019000000001f3000000000006228d41e8e760800002b983207701fe5e39bcb4e58c6e00022506db800048b19e2a0e9b7854ccc1b1fc83160000000631ce083451d9c777c000018610baa0000000029d4475256400000001548c880f40f7258a04032099576a63668e790220611965d86e48dc8000000072e982a000296462ec00041c0d1653c2ad600011200fc59d8000121614e29844fc918e0
  | 48 => 0x12f133e54a00000000000000000081d22283c2aa9e79f80047079c4421029215570fbaa9600000002aea9ac19386152aae0000fd03df9ec84d519a93c300000000d962078af25fa16449e2000016f0fbe746126e912899202223e6000248315c238e2fca39e04329b000000002ee00006918ae4000000000004ce00000000000dfeac90000000000040580000000000770a0975c81648000136200017ca000000000000000001602000000029d8000a72063a0002a740001de60001bf700008b20000300000298e000000000024baaca0c40000000000000000000d58a4b0ac20000000692800000000007160ecc000261300000009eb9a380000110623c010000296e000129e0001b6c0000f967098000a6b10a8000000006f14ac2206ae5613800000012740001d3967400000000b1a24380002bd8000000000000008140000000658800058b166400021ea000049a00005840681c7a00028f0000000055f9a100001be8498800050881062689542904857e710c0000001cd20001fa17f91f7805f22e46ee66fe32ec1a701940000c09d3d0000000000004c0000000000047c0001fa200018e8108e2dc0001f08000000000014ec00023dc16209344fc00b6356800014ac0000000000000066e03697aaa935f160000bdfa780a8c00e8b645004bfc0ad8e8f000024916482c8a291d48552a9287bb0000000164a0001ac0551090000000c4000063643a988e7bba12a000183000020160000e900001f3c9ea88c80001f0e00017dc076991a38a40000002afc0000978396c00068498ca727000079e000000018da09427f00a5000000029ae000107b60e00002314818a4d80001d0c000000000000000007d0800049f94e665a48cc3049eae000103e000174440b040295401a60001c9023e4000986400028480004a70aa786cd7706fca09867f0a4e7d5100c0000e4c91a8c345f0658406e00fe0b890982ed40008b08df306bc000236125e2c80000671874f2e6217687d9fb968828de3328eb241222c6461944486880001108ab40000000054800024fc2489ff20cc32d95242a295a600000000000000000000000000000001a1a000000064528ff00016a64089fa48b39f264a98000000220400027b46b2800000011b695d00004025ce0000000000000ce6e8800053195728af091e91b89d329a24ec00016420178696465800018508480b4098b32140006b1000000002781b9ab41000000000012baa62a696a64800066f0000000255640d8a5029ea87aada8b1365f0e9c585800000014da27aa1320000fdf078c00043f80000a497a42a8137e51f1d2984d9d9236269480000ceeaa12a4151317065d328be00000000000000000000000000000000a620001736000199a23a46ea3df0000851279007328ec19516dc39f4000000000000000001282
  | 49 => 0x25da63223529fb1fa60ef80007ae8556a5d9f2a34008ee000059e281c1808e0a9dc91300066181560016665e146800092115628e80000000083a3e48000000284c0bf9f2179a8ea8000000011e9f1a57506104808000516129a00010b497b00006131bc40d510b30000000279000000000008d90b92462800000000000000508000138e3f6d5e6113822a00005fc40aa246350a1140001c32ab5c0004892262773a7ee9330455000105847083b962a8de0933954b4440558624000044a969aa7f187a289000028a98ba0894ab61208517000000054100000002476920926625a00a70ac8000000000043300000000f5a32384a8000000051b93df00005a600014340001ed48cb00000c980007a72576a198a0c703275e946a0649808fb27aa00001a3887f00000000162a8204e80000ad1b340002942124000000000003ff400041da53aa49938c000000000022f2376c00004915ee0000efa981400064480009158b2d46d134c176a83ca1700004eea0628ea83b4000000000000000002a66000000091400005f480006e5800000000004116532564a3a48321cf20001df8a259c2ca6517936e797668c800000000c283aaa67a00000008a208d400000006b2192400018f000015e81098000804090c4d0273800001833b38000000074894081ad46f04c79e3a1d200000005db80001fe90f20000d5c7ee0f5e00017d400000002860000572991c00017ec8d3800000028a6000295a4de07ea3a00ef03825f020002570000240443694a64db80000c19e8442918ee10b8c3049a8ba808b800000003baa8b1cfe53a000035c804b5452504000024d854000000000000000000482800000000002f959a60001366471a2ba991c6883d828b84d08f0814f242000005a48fa1a9638086ae5c78a1e000008f00009cd6c380000002ab4000250a9898e42043899e4152a9607e9756008292085c0d7a273cc80309998ea828f2c5058cd6655a510a280000817d31a000048e9ba901400000000000ba0000264e3de0698000000003788ae00000006eb800000026a01300e34000135c4dc183600000001dc800000004fa249000094d8c8c75c01c639742f699b1e30000000000000000002b1308ce96875d203a871161a588aadc482286a2b8647c4f7aaeb6d725d02104d7064a2b40a730045000020868d8000900000005f8bf43b5932a49500000000000a8380005df000064800000000000000149800000000001ffa75780007fc000000026b600006ac7be1ebeab646782c1892e05b5ade22c03aa5a9140a3520000a0d92d817c9a7c0f903c805c894e259d8c420c96ce5a01e4aa2d01d80946b7a29f223c9dc27509268eb86fe800000000000000000000000022fdf145389f3e38757a1307eac600016fe8b400005f09e580149a6cad40f8c9b6a7323a0cc64
  | 50 => 0x317660e0001a147dfc0001ad80000001f50000133a00028bc9b51d7800024e614912812808b8a000202883c000034aa1c23c623e40e027180002b53000042b00007bc0001f1e00019ce9d3278ca891f30241a8483a1cc7aa7a29bc277000083f800050e037f716885c0002b1e686109297f9fbc3f780000e30bf02e3800035a08e80064cbc000268200012f600010744278000a490000acb888491085541b1cf6835d00007da01200000dcc6729d7c0001e4100018e90001bf67651bda000000092d00007e28000527875e391058c0001e020002acba1789622ff891a3f1e8561569e3773c276071905348d2231ea9b0a8b02507019e290f854a9b0aa640000000000057792306069b862d20000883121a84e00005a11ad2000000084ac00018493bc000256e3b2875010e9ab843d1f9264f156e00000004c980007e601be00000003d4800091ec00000008a600006601e6c0000000000885007c80b80008ef0af111499806461584ab7a1543e792d455320a11f08fe2a4e62b60cd136c0000b2400000000000beaa8101980d8800000000000000000846800088080000000ab852e23760000000942242861f04ef2fd800000017b200021c828f400000000c036c88aa8ae293864987d442a80000001276ac0023453b9e361b515b65cc1a8a62b64fc4358700adb014658c10499d9000000000000028000000227ea368b5680785001fe0000282000077f0000579000000000003e29162000255e9c800005c92852000000000000000001b1200000008061f740a88000000042a2b4c000000000000000000000000000000076b878b95b18c241ea8c207855c003c06f693ec4084b9a11038c854a1438141036205400000004c405557f898dca9fa91c000114b00000000000000a6200002f9000000018fd0001a2c464400042082520000000000000005ad17d2f65ee263300001270c0e4f200009248ea60e9e7de1e380000000000000000000300000ee08d0a21245a4c96998580061819d00009229ec21b1000071a27d844fa92e9c00fc86d59ed0830163a8270ba34e2898a1bf067c0000bc9000012200004160000000000000008d8000ac495571fb97884b0a2660000dde0000000aae9c5c7f799db9628b8025780005e7694e4841297000000027300008f5824a08512a886b8434000083b133087451f82b00c6224036b14c80000fd50001e7a29a800000013381c5000000000004dd96f40000000000000099718e50000ca61988000a9722488849e442ba9c6022686d83030bd80b51ede54f87188be1b9493d993600000002dd2b5c4429038000000000019d4699800000000004730000438000000000005fdc75c90c2b2204095809f14ade9c500001d493fa0da090a00000004108000000000039f002e000268500024730f69b360000bc01df
  | 51 => 0x18fdd000118c4f300009859a9a106a665000180a62a517006ea07085dc1c005980007812b2563cd7c400d8bcc09a80003f31ee60002b14990a48500029b290f90e47871128000000031d81ae3cf873a000228608e80000632ad881e9af297d88240db0e182ef85ce57c800061d0c24000023547d93b882e800000000003bd80003758000000000000014c422f99ba397180200024e40001c7800000000000d5e000000077c800032594b000022006a7112271ca08c45a8000404a07821849980000000000000076580000d6aa000001bf0254a40e18b21b2640094f0950a5e09580001c798bc70ba97c00000006f784eb0000000010dfad35d8f428f297fa0000000000000000000000000b160000d90395400000000000000000000000000005a8000198a00024a87c894748d5247e0001f8402ac00072480000000314000000009380000001cfc0000000abd8000636262877b0492217947085e06f013b581c5ce9b301f70e3f34ea844382c1eaa60046c5ed64d44cd283208e68eea18800000021cf4d68d225df8320000242e4b3a0e24ec0e2aa85648e72c93f62c397e0162915c31b1c8e0778093aac24ca523ab86059c000412c734754010f7c92478000212c6e300000002afa00006c800000009b481b315f000026f1f807fe0000570800024429666111bd021991560001bbd00008bc93dc229824039a000016939529500000c5c2fe000000023cc6b7045e60d50308cf221600015fc895a06180fdc3815883440a58fd99f8965057319b0a289e1f1600fec50424695da165a383c0005dc9698a87ea489de11767b59e12aaf40000000e6e00024a4a950edc78b8000000000000000000001b2a84293a80000b4670496260d2051e150a03658e07fc40d0000154069a58380000000000000008e000000000026e602480005f016b610000001e2000000000000000000000000050a83100b1a2a2000027612a50d2ad2119000000006dd800e0000000000151a6cc8000000000010a0000638db52000000000000000000000000000000000000002b291ca271205009f646980000000af43e8141c417000051280003f2c99a2d9400007be05200025e86591e5286080000000b3628a14a466a00807e70000582207e00000000000000000000068380b42df0000a6989d87728000a1628d25be0638000086000000007f700007ea2a20083958a4c22a5e0000d6e1669c6c00000001cb1dc816c8fae84e88f0a7b810d72c08a2870149c17529f86c9a730000000000000000f8000000000000002b2c656271c000020a000000017e8000000204400000000001e0e000222000000000000d7e6e2019713c100a0000df925f850c63f8c7b638895a0001d2e91501ab7930a5aa90a2aa2a363281118f7064f848a8ea09632135b6200010800ea00000899b2
  | 52 => 0x87891bdb400001752519822408c21400002436a4689ee0001a54101daf018304f7222c0006a805f68c38000000000000026dc00005c40000a70757000078f0838503aabc92ae10e26905d064e8d443a4a55b9998c4863dc0002af59720001d560000000449000012d00004b2000017e015e00000000000bbc157000037087e80000000000000000000004c7439d146d3c644b19bd00001a900025e40000000319550633d8000632400000022689051da29188e8419e5ec44e7aa9b11219740002332000168670f000071b962a1e9814234e23b241b850a0002336117c00000000007f3c000000299a6a100003ef262212d89f40001f32949896689ca23268780004810000000163e01b00000002a4e00000000001500113c0002f51ddb4fb000000021ac4fe0232a8e10e85b60000a8a1502a2a111aa9ba08e1af0cb818c8fc021b025f2d49d6a5fad8f64eb8dfa5639a520000a5c000255a94365b600000005a200004be98513118ad2ae11e940e70ac716c166027
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87c8759543084071790eb2286108030fdd56450c210061e3aac8a184200c5f7598d43084018b8eb31a86108c727dd26350c2101c6e43ac6a184200c5f7558d43084018b8eab1a86108c62fa0d7610c210064f41aec218422ec9d835d8430846317906bb086108c327cc97610c211864e992ec218422ecaf215d8430845d95a42bb086108022fe017610c210045ec02ec2184200c3f505d8430840187aa0bb086108c68f20d6510c211961f39aca2184200e1e735944308461c3e64b2886108c3874c96510c210051fc02ca2184200a3d80594430840187ee0b2886108030f5c16510c2118d4fc3cc62184231c9f8798c430846353b0f31886108c72721e6310c2118f0fc2cc62184231e1c8598c430846393ee13188610803275c26310c210070fa84c62184200e1d5098c430846517f0eb1886108028fe156310c2113d1e42ac62184232c9e7358c430840153f0eb1886108cb27e1d6310c210070fc2ac62184200e1c8558c430846353f04b1886108c2a76096310c210064fb82c62184200c9d7058c4308401c3ea0b188610803875416310c2118d1fc34a62184200a3d8694c430846387eed29886108030f5da5310c2118f0f31ca62184200e1d6394c4308587c74c129886108c70fdd85310c210061ebb0a62184231e1e6314c4308401c3ac62988610afb8e9805310c210053d42ee8b004200a7985dd160085ab5730f3a2c0108038e9d674580210055d41ce8b0042d3eab219d160085a7d64433a2c010b4faa48674580216bf5890ce8b0042d6aeb825d160084095d104ba2c0108032ee1d74580210071d3aae8b004200e39755d1600840157106ba2c010803aae0974580216a754412e8b0042d5eab215d160085abd6442ba2c010b57aa48574580216a75890ae8b004200a7a851d160084014f30a3a2c010b4eaea1074580210071daa4a8b004200e3954151600840157509b9ac010802ae61373580210055dc22e6b004200ab8845cd60085a55d704b9ac010812ba209735802168d79c0ae6b004203af0815cd60084015750839ac010802ae610735802102575410e6b004205ae9821cd60084075e50239ac010816bc60473580210053d42e86b004200a7985d0d60084095d50521ac010802ba60a43580210055dc3c86b004200ab98790d6008401c74eb21ac0108038e5d643580211755d41c86b004200e3a5390d600846dd550521ac010803aa60a43580211975590c86b004232eb22190d6008465d524321ac0108dbac48643580210053dc2a86b004200a788550d60084015770e21ac010802ae61c43580210071d3a886b004200e397510d60084655750621ac010803a6a0c43580210071d29886b004200e385310d6008461d366421ac0108c3a64c843580211775590886b00422eeb22110d600845dd524221ac0108c3ac4844358021
  | 1 => 0xeeba02c610b6b0f1d74058c210054f41e80b1842008be8750163084011790ea02c6108030fdd54058c216ce1e3aa80b184200a9c8350163084071bd0f182c610802a7a123058c210054ec2460b1842018dc874c1630840153f08982c610802a72113058c210054f42060b184200a9d840c1630840959d04182c61080eb5a043058c210070fbaee8b184200a9d80dd163084014bd0b3a2c610802976167458c211754f424e8b184200a5f855d163084014b90aba2c6108caa7a1c7458c210064f438e8b184200e1f751d16308401c38ea3a2c6108c327dc87458c211864eb90e8b184200a9d801d16308401c3ea92a2c610803875505458c210054f424e0b184200a9d849c1630840153f08b82c610802a72117058c2100567c12e0b184204acc825c163084015af02b82c61080eb52057058c210054f420e0b184200a9d841c1630840959d04382c610802b36087058c2101d6b408e0b184200ad5811c1630840153d0fa02c610802a721f4058c210070fbae80b184200e1c75d016308401c3ea1a02c61080297a164058c210052ec2c80b1842d5a9d84901630840153d0ea02c610802a721d4058c210070fbaa80b184200e1c755016308401d3700a02c61080387d414058c210070ea8280b184200a5e8510163084014bb0a202c610b4ea7a104058c2102477416ed21842038dd835da43084098dce4b2c861080e2fe1d6490c2118d4e41ac92184204cae7259243084071bb0f31c861080aa72116390c2100636b2ae52184200cad645ca430840199cc6b9486108c727a0f7690c2118e57416ed21842318bf80dda430840117b01bb486108030fd437690c210061ea86ed2184200c9e735da430846317d06bb4861080327a0d7690c211964ec1aed21842318bc835da430840117f00bb486108022f6017690c210061fa82ed2184200c3d505da430846347906b2c86108bb0f9cd6590c211b717392cb2184200a3f80596430840147b00b2c86108030fdc16590c210061eb82cb2184231a9f8798e430846353b0f31c86108c787e166390c2118f0e42cc72184231e8e7298e430846393ee131c8610803275c26390c210070fa84c72184200e1d5098e430845d17f0eb1c86108028fe156390c2115d1e42ac7218422ec9e7358e430840153f0eb1c86108bb27e1d6390c210070fc2ac72184200e1c8558e430840193ee0b1c8610803275c16390c210070fa82c72184200e1d5058e430846387eed29c86108030f5da5390c2118f0f31ca72184200e1d6394e4308593c74c129c86108c72bdd97290c2100716b2ae521842d8d8e735ca4308463d1cc6b94861085e1f2177650c2101c5e426eca1842038dc83dd943084010ff0abb2861085e1f2157650c211945fc22eca18420087d86dd543084fd87cc9baa86108031e9837550c210043f43acaa184200
  | 2 => 0xf53590210070f29ea6b2042318be83dc164085ab17b0f382c8108028fa1670590210051ec2ce0b204200aaf825c1640840955904b82c8108c62f20d705902100657c12e0b2042d4cac825c1640840197700b82c810b4e2fa1c70590210051f428e0b204200a3d851c1640840147d07a82c8108030f1cf50590210061fb86a0b204200c3d70d41640840117d0f282c8108022f61e50590216e51ec2ca0b204200a3c835416408401878e6a82c8108038ee0150590210061fb82a0b204200c3d70541640840117d0e282c8108022f61c50590216dd1f428a0b2042318bc87cc1640840117d0f182c8108022f61e30590210051f42c60b204200a3d858c1640840117f0e982c8108022f21d30590210051fc2a60b204200a3c854c1640840117d0e182c8108022f61c30590210051f42860b204200a3d850c1640840955d04182c810802ab608305902101d5b40860b204200ab5810c16408401878a9bb2a8108030f151765502101c5e43ac8aa04217a3c8559154084010ff0aba4c61085e1f2157498c210052f42e873184200a5d85d0e630846353d09a1cc61080e3761c4398c210045fc22e131842028bc845c2630846317d0fa04c6108c62f21f4098c216d61e3ae813184231a9e83d0263084631790ea04c610b670f1d54098c2118d4e41a8131842018dd87cc2630840153d09184c610802a76123098c210054fc22613184200a9c844c263084071bb0e184c610802a7a103098c210054ec20613184204ace820c263084075ad02184c610812b3a0b7498c2118f0fbaee93184231e8e82dd26308463d1b05ba4c610802a76037498c210052f42ce93184200a5d859d263084014bf0aba4c610802972157498c2118e4f438e93184231e1f751d26308463c38ea3a4c6108c727dc87498c211864eb90e93184200a9d801d26308401c3ea92a4c610803875505498c210054f424e13184200a9d849c2630840153f08b84c610802a72117098c210054f420e13184200a9d841c2630840959d04384c610802b36087098c2101d6b408e13184200ad5811c2630846353d0fa04c6108c6a721f4098c210070fbae813184200e1c75d026308401c3ea1a04c61080297a164098c210052ec2c8131842d5a9d84902630846353d0ea04c6108c6a721d4098c210070fbaa813184200e1c755026308401d3700a04c61080387d414098c210070ea82813184200a5e8510263084014bb0a204c610b4ea7a104098c210145f43ee8b184200c3f75dd1630846317d07ba2c6108cb2760f7458c2118c5e41ee8b1842008bd80dd1630840187eea3a2c6108030f1d47458c2101c6f43e86b184200a5e85d0d63084014bb0ba1ac61080327dd04358c210045fc22e0b1842028bc845c163084091d904b82c61080e3d2057058c210045f43e80b1842028bc87d01630840187
  | 3 => 0x721a4200a3f8558e43484574790ab1c8690802aee016390d211455c402c721a4200c3e7694e4348463878ed29c869085e1fa177650d210043ec2eeca1a421787e859d943484010fb0b3b286908022f6127650d210043fc2aeca1a421787c855d943484011f700bb286908063e2017650d210bc3e428eca1a42028bc841d943484010fd0dbaa86909fb0f1937550d210043f43ecaa1a420087c87d95434840187eebb2286908030f1d76450d210054f41ec8a1a42318be869d8434846317d073b086908c62f20e7610d210045fc04ec21a42008bd809d8434840187ea13b086908030f5427610d2100657904ec21a4200cad209d8434840196e213b086908032d4427610d2118d4f41eca21a4200a9d83d94434844f47d0db2886908030f9db6510d210061e3b6ca21a4200b1e83d94434846347d07b28869080387a0f6510d2118d0f41eca21a4200e1d83d94434840187ce7b288690803879cf6510d210051fc06ca21a4200a3d80d94434840187ee1b2886908030f5c36510d210045fc3aca21a42318bc87594434840147d0c32886908030f9d86510d210061e3b0ca21a42008bd87d8c434844f47d0bb1886908028f6176310d210045fc3ac621a4200a3f8558c434844f4790ab188690802aee016310d211355c402c621a4200a3e8694c43484634790d29886908030f9da5310d2118e1e3b4a621a4200c3e7614c4348463878ec29886908c78798c5310d210070eb18a621a423ecb471d91424846353d07b266490886a7a1363cc9210054f430879924231a9c8610f3248401c3eca21e6490aa78719443cc921187c2108879924200cd4635c7324847b17d0dba264908030f197744c9210045f43ec8992423e8bc87d91324840187eebb2264908030f1d7644c9210054f41ec8992421ea9e84d8d324840153d0c21a649087aa7218434c9210070fb2886992429de1c6510d32485bd0fd0dbaa8290a230f19375505214343f43ecaa0a42dd87c87d95414840187eebb2282908030f1d764505211fe56396c8a0a4200cac645cb3148401998c6b96629080a2fa13764c5210045ec26ec98a42008bf845d9314840517908bb262908023ee01764c52100c7c402ec98a423c8be86dd13148401878cbba262908022fa1f644c5211fc5e43ec898a4200c3f75d913148401878ebb2262908063ba1b724c52101c5f43ea8b204200c3f75d51640842f0fd0bb9ac8108021f617735902100c5e426e0b2042048ec825c1640840197680b82c81080e2fa1e40590210051f42c80b204200a3d8590164084031790ea02c8108032edc140590210061fbaceab204200c3d751d5640840147d0bb9ac8108028f617735902102557414e6b204200a3f855cd64084014790ab9ac8108c727cc873590211864e990e6b2042008bd801cd640840117d0fa9ac8108022f61
  | 4 => 0x348401dc240886c6908030f9d76498d210061ebaec931a4200c3e75192634840187aea324c6908030f9d67498d210061f3aae931a4200c3d755d2634846387ca6ba4c6908c70f14d7498d210045fc02e931a4200cae745ca634840517d09b84c6908022f6137098d210145fc3e8131a42008bd87d0263485b587ceba04c6908030f5d74098d210045fc3a8131a42008bd8750263485b387ceaa04c6908030f5d54098d2100c6ec3e6131a423e8bc86dd1634840117d0fb22c6908030fdd76458d210061e3aec8b1a4200cb870d91634840117d0e322c6908030fdd46458d210061e3a8c8b1a4200cb8701916348401976c9b82c6908032e1937058d210061fbaee8b1a42008bd80dd1634840187eea3a2c6908030f1d47458d210065dba6e0b1a4200cb874dc1634840197709b82c6908032e2137058d210045fc22e0b1a42028bc845c163484011bf06b82c6908023be097058d210047bc0ae0b1a4200cbb741c16348401970e8382c69080336dcc7058d2100675b90e0b1a4200cf3711c1634840117d0fa02c69080a2f21f4058d210061fbae80b1a42dac3c75d016348401976e1a02c6908072e1c34058d210045f43a80b1a42008bc87501634840187eeaa02c690b670f1d54058d210065db8280b1a4201cb87050163484011bd0f982c690807361c33058d2100c6e43a60b1a4201cd8704c163484011dd0f902c6908073a1c32058d2100c7643a40b1a4201ce87048163484011ed0f882c6908073c1c31058d2100c7a43a20b1a4201cf0704416348401dc240882c69080a2fa127618d2118d4f41ec831a4231a9e8319063484011bf0eb18c690802b62016318d210043fc2ae831a421787c855d0634840117f08b80c69080a2f2117018d2118c5f43e8031a42318bc87d0063485b5878eba00c6908c6a7a0f4018d2118c5e43a8031a42d9c3c75500634846353906a00c6908023761e3018d210046ec386031a4200acd820c063484015ab02180c69085e1fa177690d210043ec2eed21a42008ed82dda43484010ff0abb4869085e1f2157690d2118d4f41ec921a4200a3f8559243484574790ab2486908c6a720d6490d2118c5f41ced21a4200cae219da4348401958433b486908022fe027690d210045ec04ed21a4200c3f509da434840187aa13b486908032bc827690d2100656904ed21a4200cb7109da434840196a213b486908028fe157690d2115d1e42aed21a42008be861da434846393d063b486908c62fe007690d210045ec00ed21a4200c3f501da434840187aa03b486908ae8fa1b6590d210061f3b6cb21a4200c3c76d96434846347d07b2c86908028fe036590d210051ec06cb21a4200c3f70d96434840187ae1b2c86908022fe1d6590d2118c5e43acb21a4200c3e761964348401878ec32c86908ae8fa176390d210051ec2ec
  | 5 => 0x8fead60470d91210051f41ea1b224200c3e73d43644840187ee1a86c8908030f5c350d91210045f43ca1b2242008bd87943644840147906a86c8908030f9cd50d91210071dc02a1b224200c3f70543644840187ae0a86c8908022fa1c50d91210045ec38a1b2242318bf87cc3644846393ce7986c8908022fa1e30d91210045ec3c61b224200a3e858c3644840147b0b186c8908022fe1d30d91210045e43a61b224200a3f854c364484014790a986c890803279cd30d91210045f43861b2242008bd870c3644840147d0a186c8908028f61430d91211fd5741061b224200aad820c3644847d56d02186c890802ad60430d91211f45f43c41b2242008bd87883644840147d0b106c8908028f61620d91211fc5f43c21b2242008bd87843644840147d0b086c8908028f61610d91211f75808221b224200c3c64dd5644842f0fd0fbaac8908c61fa0f75591210061e21eeab22420087d80dd5644840187e81baac8908030fdd774591210061e3aee8b22421787e85dcd64484010fb0bb9ac8908021fe1570591210bc3e42ae0b2242008bf845c164484011bf06b82c8908023720d705912100477c12e0b22420087e87d41644842f0f90fa82c8908021fa1d50591210043e43aa0b2242018bc87501644840187eeaa02c890b670f1d540591210065db8280b2242008bd809d8644840187cedb28c8908028fa0f65191210051ec06ca3224200c3f70d94644840117b0f328c8908028fa1665191210045fc3aca3224200c3e76194644840187ecb398c8908030f19673191210061fb2ae03224200c3c655c0644840117f0fb00c8908032e5c360191210045ec3cc03224200a3e85980644840147b0b300c8908022fe1d60191210051fc2ac03224200a3c85580644840153f06b00c890802a720d601912100557c12c032242028be87180644840117b0e300c8908028fa1460191210051ec28c03224200a9e83180644840153b06300c8908032e5c060191210051f436a03224200a3c86d40644840187ceda80c8908028fa1950191210051e432a03224200c3e76540644840155d0d900c8908f6ab21920191211e55a432203224200fa1204406448401878a93b2a89080237a0e76551210046ec1cecaa242008bf845d95448401878a83b2a89085e2fa1f64551210bd1f42ec8aa242088bd87d93634840187cebb26c6908030f5d764d8d210054f41ec9b1a4200c3e75193634840187aea326c690802a7a0c64d8d210061f3ace9b1a4200c3e755d3634840187aeaba6c6908022fe0174d8d210145f426e1b1a42008bd84dc3634840517f0fa06c6908022f61f40d8d216d61f3ae81b1a4200c3d75d03634840153d07a06c6908022fe1d40d8d210045ec3a81b1a42d9c3e75503634840187aeaa06c690802a720d40d8d2100566c1061b1a4200ad5810c36
  | 6 => 0x61e3aac8a0e4200c9c7498d31c8401938e8b1a6390813331c9634c7210bc3f43eeab24423187e83dd5648840187887baac9108021f60375592210061fa06eab244287c3f741d5648842f0fd0bb9ac9108021f61773592210043fc2ae0b24421787c855c164884011bf06b82c9108023720d70592210043f43ea0b24421787c87d4164884010fd0ea82c9108021f21d505922100c5e43a80b244200c3f7550164885b3878eaa02c9108032edc1405922166c5fc22ecaa442038bc87591548842f4790ab22a9108063761f3098e210145f43ee8b1c4200c3f75dd1638840117b01ba2c7108030fdd47458e210061e3a8e8b1c42008bf845c1638840517908b82c7108022fa1f4058e210145e43e80b1c4200c3f75d0163885b5878eba02c7108022fa1d4058e210045e43a80b1c4200c3f7550163885b3878eaa02c7108063721d3058e2100e7838220b1c421787e85dda43884010fb0bbb4871080e2fe1d6490e210051fc2ac921c422ba3c85592438846353906b2487108022fe1d6590e2118c5e43acb21c422e8bf8758e438840147f0ab1c87108ae8f2156390e2118e563b4e521c4231aaf865ca43885c3b1ce6b9487108021fe157650e210bc3e42aeca1c42328bf845d9438840117f0eb2887108c62f21d6510e211945fc3ac621c4200a3f8558c438844f4790ab1887108c78798c5310e210070eb18a621c4223a3c85591428844353908b1e651087aa7211634ca2101e6a38ac69944200c3d75d5364484010ff0ab9ec89085e1f21573d91210051f42c81b224200a3d85903644840317f0ea06c8908032e5c140d91210061fb2ce7b224200c3f655c36448401972e1b06c8908028fa1660d91210051ec2cc1b224200a3f8558364484014790ab06c890802a7e0d60d91210054e41ac1b2242088bd87183644840147d0a306c8908028f61460d91210054f418c1b224200a9d831836448401972e0306c8908028fa1b50d91217061f3b6a1b224200a3e8654364484014790ca86c890b7f0f9d950d91211f55643241b22423fab4864436448401d60c0886c890803e848110d91210054f41eebb224200a9d83dd7644840187eeb3aec8908030f5d475d91210051f42ee7b224200a3d85dcf644840193ee739ec890803278c673d912118e4e18ce7b2242008bd809cf644840147f0ab9ec8908028f21573d91210045f43ea7b2242008bd87d4f644840193ce7a9ec8908038794f53d912118e4f398a7b224200a3f855cb64484014790ab96c8908fa2fa1f52d91210045ec3ea5b22423fe2e52d4b644847dc6ca3a8ec8908c62fa0f70d91210051f42ce1b224200a3d859c3644846317906b86c8908032ee0170d91210051f428e1b224200a3d851c3644840153d06386c890802a760c70d91211fd57410e1b22423eaad821c3644847d56d02386c89
  | 7 => 0x9e83dd1620c40193b07ba2c4188022f60374588310061fba8e8b106200c3c751d1620c44117d0f21ac4188030fdd6435883115e1e3ac86b1062008be8710d620c40187eea21ac41889f0f1d443588310045fc22e0b1062028bc845c1620c40117d0fa02c41880a2f21f40588310061fbae80b1062dac3c75d01620c40117d0ea02c4188022f21d40588310061fbaa80b1062d9c3c75501620c40153906a02c4188063b21d20588310246ec1aed2106204c6e625d6420c46393ec939c84188c727192739083100636baac52106202aac8458a420c40199ce6b1484188021fe1576508310bc3e42aeca106223a3c85591420c4071d90eb1284188c7a310d62cc83118eca21ae39906231cb643dd9310c46396887bb262188032dd03764c4310065aa06ec9886200cb776dd1310c40196eec3a2621880335dda534c4313e5ab43ca69886231d568794d310c463aaeed29a621880395dda534c4310062bbb4a69886200f177494d310c401e28e929a62188c6d5e02534c43171daac04a69886231e576094d310c5c5caac129a6218b8bc5d02534c4317178aa04a69886200cd77654d310c4636af0aa9a6218802b561a324c431005aac2c6498862048be87d5164c840187eebaa2c99085e1fa1773593210043ec2ee6b2642018bc8750164c8401976e0a02c99085e2f61376553210061e2a6ecaa64200c3c545d954c84010ff0aba4c79085e1f2157498f210052f42e8731e4231a9e84d0e63c84091bb0e21cc7908c6a720d4098f2100c6ec3e6131e4200a9c844c263c840517d0fba2c7908030fdd77458f211b64ec1ee8b1e42008bd80dd163c840187eea3a2c7908030f1d47458f210246f43e86b1e4200a5e85d0d63c840193ee821ac7908022fe117058f210145e422e0b1e42008be87d0163c84051790fa02c7908030fdd74058f216d61e3ae80b1e42008be8750163c84011790ea02c7908030fdd54058f216ce1e3aa80b1e4200a9c8350163c84031b90e982c790802a72113058f2100e7438240b1e420087f855da43c842f0f90abb487908122fe1d6490f2118d4e41ac921e4200a3f855da43c84574790abb48790803279cd7690f211845fc3ac721e4200a3f8558e43c84574790ab1c87908c3279cd6390f210043fc2aeca1e421787c855d943c846d17f08bb287908c6a7e1e6310f2118d4ec3cc621e4231e8e7298c43c8463d1ae531887908c727dc26310f210064eb84c621e4200e1f5098c43c8401c3aa131887908da2fe1d6310f210051fc2ac621e4227a3c8558c43c840153f0eb1887908db27e1d6310f210070fc2ac621e4200e1c8558c43c840193ee0b188790803275c16310f210070fa82c621e4200e1d5058c43c8461d1e40b188790803a34816310f2118f0f31ca621e4200e1d6394c43c8463c3cc629887908038758c5310f210
  | 8 => 0xc02988698afb871805310d317278b880a621a62e4f151014c434c4010ff0aba6c49885e1f21574d89310070e29887b126200acd83083624c4015cb02106c4988073c1c110d89310077110221b126200c3e75d92624c40187aebb24c4988030f9d464989310061eba8c931262008be87d91624c40187eebb22c4988030f1d764589310065c386c8b1262008be87191624c40187eea322c4988030f1d464589310065c380c8b126200cbb64dc1624c401970c9b82c4988023be1d621893100574402c4312621787c859da424c4091b9073b484988021fe1576909310bc3e42aed212620087c865d6424c4eb878c8bac84988021fe1f65909310043ec3ecb2126200c3e75d92424c40187aebb24849880317d9673909310062e32ce72126200c9f649ce424c443938c939c849880317d9573909310062e32ae72126200c9f645ce424c43d938c8b9c849885e1fa1776509310043ec2eeca126200a9e8690f324c559c38cb21e649880387d9443cc93154f0e328879926221a9e86d93324c401c3eca32664988038719464cc9311745e432e91926200c3c655d2324c40117b0fb2464988030f9d7648c9310061ebaec91926204ce4625c6324c45d17d0dba264988030f197744c9311845f43ec89926200c3f75d91324c401878ebb226498802a7a1a434c9315070e32c869926236e8c6290d324c465b28e321a6498973471d4434c9310070fb2886992629de1c6510d324c461d18c421a64988bb651c4434c9310074621ec49926200a9e86dd1324c46d938edba2649880387197744c9311b746316e89926230c9c761d1324c401a38ea3a2649880387194744c93118746310e8992621ea9e86d91324c465938edb2264988cb651c7644c9311764e3b0c89926200e1f65191324c401c38ca32264988bb651c4644c93100567436e4992629ae8c64dc9324c40959d0db126498803a3193624c93100747b20c49926200e8c64189324c4073ad0fb8a649880365dd0714c931006ca3a0e2992620087e86dd5414c511878c9baa8298a1a1fa1f65505314443e43ecaa0a6200c3f75d91414c401878ebb22829880327d9073505311965b3b6c998a6202cb676193314c42f0fd0fbaac8188c61fa0f75590310061e21eeab20620087d80dd5640c40187e81baac818a1f0fdd075590310043fc2ae0b20621787c855c1640c4011b906b82c8188021fa1f50590310bc3e43ea0b20620087e87541640c4010f90ea82c8188062f21d40590310061fbaa80b2062d9c3c75501640c40153906a02c8188032edc1405903166c5fc22ecaa062038bc87591540c42f4790ab22a8188028fe156490c3115d1e42ac92186231a9c83592430c58517f0eb2c86188c62f21d6590c310045fc3aca21862318bc87594430c40517d0fba2c4188030fdd774588310054f41ee8b106200c
  | 9 => 0x20d91310055ac0841b2262008be87843644c40117b0f086c8988028fa1610d91310051ec2c21b226200c3c64dd5644c42f0fd0fbaac8988030f10f75591310043ec06eab226200c3f40dd5644c40187eebba2c8988030f1d774591310043fc2ae0b22621787c855c1644c40117f08b82c89880237e0d705913100477c12e0b2262048ec825c1644c4010fd0fa82c89885e1f21f50591310043f43aa0b22620087c87541644c4031790ea02c8988030fdd540591316ce1e3aa80b226200cbb70501644c40117b013b0c8988030f9db65191310051ec06ca3226200c3f70d94644c40117b0f328c8988028fa1665191310045fc3aca3226200c3e76194644c40187ecab80c8988030f19570191310045fc3ec03226200cb970d80644c40117b0f300c8988028fa1660191310051ec2cc032262008bf87580644c40147f0ab00c8988028f21560191310054fc1ac03226200aaf82580644c40155904b00c89880a2fa1c60191310045ec38c03226200a3e85180644c40147b0a300c898802aba08601913100556c10c03226200cb970180644c40147d0da80c8988028f21b50191310061f3b6a03226200a3e86540644c4014790ca80c8988030f9d950191310054f43660322622ea9c864c0644c4015690c880c898803ac18110191310061e2a4ecaa262008bf845d9544c401878a83b2a89885e2fa1f64551310bd1f42ec8aa262038de86dcd544c4018becbb9aa89880327d90735513173e8e2a0e6aa262038bf87592434c40147f0ab2486988ae8f2156490d3118d4e41ced21a6231c3e539da434c463878a73b486988c72dcc67690d3118e5a18ced21a62008bf809da434c40117b013b486988030fd427690d310061ea84ed21a622ecb7109da434c40196a213b486988ae8fa1b6590d310061f3b6cb21a6231a3c83d96434c40147f01b2c86988028f6036590d310061fb86cb21a6200c3d70d96434c40117f0eb2c86988030f9d86590d313e43f436eaa1a627ec3c64dd5434c4f30fd0fb2a8698a0a1f21f6550d310070e21ecaa1a6200c3f75d91434c401878ebb2286988cb2d1c76450d3118e1f29cec21a6231c3c539d8434c46396e633b086988c72d0c67610d310045fc04ec21a62008bd809d8434c40187ea13b086988030f5427610d311965b884ec21a6200cb5109d8434c45d53b07b288698b9b87d4f6510d3113d1f436ca21a6200c3e76d94434c46347d07b288698b9b87a0f6510d310070ec1eca21a6231a3c83d94434c40187ce7b288698803879cf6510d310051fc06ca21a6200a3d80d94434c40187ee1b2886988030f5c36510d310045fc3aca21a6200a3e86194434c40187cec32886988c6c720c6510d310068f3b0a621a6231e1e7614c434c463c3ec229886988c7c5d845310d3118e8fb80a621a62e5d1d7014c434c57dc3c
  | 10 => 0x2146200c5d659ce428c44393cc939c8518803275927390a310062f32ae72146200c5d655ce428c43d93cc8b9c8518803275917390a3101c5e426eca1462a9e1e6510f328c401c3aca21e65188022fe19748ca310061f32ae919462008bf87592328c40187ceab2465188030f5d5648ca310045ec36e89946200c3e65dd1328c4611790eb2265188030fdd5644ca310061e3aac8994629de1e6510d328c401c3aca21a6518803a310d624ca3101e7238ac49946200e8d644c8328c5056ab0d29e63188c79561a53cc631416aabb4a798c6231e557694f318c505e2cc929e6318a0bc559253cc6317478ba04a798c62e8f154094f318c4636af0aa9e63188030f5d754d91310043fc2ae5b22621787c855cb644c40147d0b206c8988028f61640d913100c5fc3a81b226200cb970503644c40187ecab86c8988032e5c360d91310051f42cc1b226200a3d85983644c40147f0ab06c8988028f21560d913100557c12c1b226200aac82583644c42317b0e306c8988028fa1460d91310051ec28c1b226200aae82183644c40155b04306c8988032e5c060d91310051f436a1b2262e0c3e76d43644c40147d0ca86c8988028f21950d91316fe1f3b2a1b226232a9c864c3644c401d60c0886c8988caa760f75d91310061fbacebb226200c3d751d7644c40147f0ab9ec8988028f21573d91311945f43ea7b2262008bd87d4f644c401c3ca7a9ec8988028fe1572d91310051e42ae5b226200a3e851cb644c40147b0a396c8988caa760c72d91310045f43ea5b2262008bd87d4b644c40147d0bb8ec8988028f61771d913100557416e3b226200aad82dc7644c465c6ca3a8ec8988c62fa0f70d91310051f42ce1b226200a3d859c3644c46317906b86c8988032ee0170d91310051f428e1b226200a3d851c3644c40153d06386c8988caa760c70d913100557410e1b226200aad821c3644c46556d02386c898802ad60470d91310051f41ea1b226226c3e73d43644c451878e7a86c8988030fdc350d91310061eb86a1b2262008be87943644c40117b0f286c8988028f20d50d91311361f39aa1b226228c3c73543644c401c7700a86c8988030fdc150d91310061eb82a1b2262008be87143644c40117b0e286c8988c62fe1f30d913118c5e43e61b2262328be878c3644c40117b0f186c8988028fa1630d91310051ec2c61b2262268bf874c3644c4511790e986c8988028fe1530d91310051e42a61b2262008be870c3644c42317b0e186c8988028fa1430d91310051ec2861b226200aae820c3644c40155b04186c8988caada0430d91310055ac0861b2262008be87883644c40117b0f106c8988028fa1620d91310051ec2c41b2262008be87083644c40117b0e106c8988028fa1420d91310051ec2841b226200a9e83083644c40153b06106c8988caada04
  | 11 => 0xcc4071bb0c39aa9988c727d90735533174e8e2a0e6aa66231a9c8359243cc46353906b288798802aba136298b310bc3f42ee8b16620087d85dd162cc463c38a621ac5988029ba174258b3100c7643a40b166201ce87048162cc4011df0eb10c5988030f9d56490b3110e4f324e72166200c9d649ce42cc42f0fd0bbb285988021f6177650b310245f43ec8a166223a3e85d9142cc40955d05b2285988c7a310d62ccb3135e8e3a8869966200d1c751d132cc401878eab22839880e2fa1f54592310061fbaea8b24621787e85dc9648c4010fb0bb92c91880e2fa1e40592310051f42c80b246200a3d85901648c4031790ea02c9188032edc140592310061fbaceab246200c3d751d5648c40147d0bb9ac9188028f61773592310051fc2ae6b246200a3c855cd648c40117d0fa9ac9188022f61f53592310070f29ea6b246200a3e85dc9648c40147b0bb92c9188028fa1672592310051ec2ce4b246200a9d839c9648c40117d0fa92c9188022f61f52592316ac5ec3ce0b246200a3e859c1648c40147b0b382c91880eada0670592310055ac0ce0b246200a9f835c1648c40153906b82c91880327e0d70592310064e41ae0b246200cbb805c1648c5a717d0e382c9188028fa1470592310051ec28e0b246200a3e83d41648c40187ee1a82c9188030f5c350592310045f43ca0b2462008bd87941648c5b947b0b282c9188028f20d50592310071dc02a0b246200c3f70541648c40187ae0a82c9188022fa1c50592310045ec38a0b2462dba3e85141648c40117d0f182c9188022f61e30592310051f42c60b246200a3d858c1648c45117f0e982c91889a2f21d30592310051fc2a60b246200a3c854c1648c42717d0e182c9188022f61c30592310051f42860b246200a3d850c1648c40155d04182c918802ab608305923101d5b40860b246200ab5810c1648c40117d0f102c9188022f61e20592310051f42c40b246200a3d85881648c40117d0e102c9188022f61c20592310051f42840b246200a3d85081648c40153d06102c918802a760c205923101d5b40840b246200ab581081648c401878a9bb2a9188030f151765523101c5e43ac8aa46217a3c85591548c45d87ce6b2c87188028fe016590e310051ec02cb21c6200c3f70596438c40187ae0b2c87188021f61b7550e313f61f326eaa1c627e87e87595438c4f30f90eb2a87188030fdd56450e310061e3aac8a1c6200cb564dc5438c46587ce6b288718803879cd6510e310051fc02ca21c6200a3d80594438c40187ee0b2887188030f5c16510e310bc3f42ee8b14620087d85dd1628c40153906a02c5188063b21d2058a310077090220b14621787e855da428c4010ff0cbac85189d70f9917590a310043fc3acb214620087d87596428c40187ceab2485188030f5d56490a310062f32ce7
  | 12 => 0x80317d9673989410062e32ce7312823fc9f649ce62504018becab9cc4a080317195739894102666312e73128200ccd73d8a62505150f90dbaac4a08021fa1f65589410043f438cab128286c3e7419462504011df0eb10c4a08122f21276949414461f3a6cb2928200a6d82d96525040187ecaba4a4a088f0f19574949410149fc3aa92928217a3c86552525040187cecaa4a4a080317d9673949413962e32ce72928200d1d549ce52504018becab9ca4a09c31719573949410bc3e428eca928200c3e541d9525050f17d0dbaa84a088f0f197755094101c5e432eaa128223c3c655d5425050d47d0db2a84a0a2b0f1db655094143e1f3b0caa128287c3c761954250401878ca39a84a08028fa1a535094111d1e430a6a128200e2c65d8942504010ff0abb664a085e1f21576cc94118d2f41ecb99282eee1c43d97325040717d0dba664a08030f19774cc94101cdb40ee99928272a5e85d8f325046393ee831e64a080297a1853cc94118d2e430a7992821787c859da3250409179093b464a08021fe15768c9410bc3e42aed192820087c865d632504010ff0fb2c64a08021f61f658c9414461f3a6cb1928200c3f655d23250401878caba464a08032b5d3628c9410bc3f42eec992820087d85dd9325042f0fd0b3b264a08021f616764c9410bc3e428ec99282028bc841d932504010fd0dbaa64a08021fa1f654c9410043e43eca9928288c3c74d9532504014bd07b2a64a0bb78710f654c9410061fb2ee89928200c3c65dd1325046d958c5ba264a09c297a17634c9410064fba0c69928200a5e8614d32504e14b90c29a64a09f793188534c9410072629ec499282ece8c43d8932504010ff0abb064a085e1f215760c9410061e32ae81928200c3f65dd15150433878cbba2a2a080e8f21954545410161e3b2a8a8a8203b3481551515040195cc9396c99885e1fe1d75d933118e1f21aebb266231c3c435d764cc4010ff00baec9988030fd0175d9331006373ace5b266200c6d759cb64cc4018dceab96c9988031b5d572d93310066739ae5b266231c6e535cb64cc4638d8a6b96c9988c72b10d72d933100657a02e5b26621787e85dc364cc4010fb0bb86c9988123ba0b70d933100476c16e1b26621787f87d4364cc4010fb0fa86c998baf1b9cb50d933100636b96a1b26620087f8754364cc4010fb0ea86c998bab1b9c950d933100636b92a1b2662018bf8750364cc5b387ceaa06c9988030f5d540d93316a65739281b266200cad7250364cc401972e0a06c9988028fa17745933100557416e8b266200c3f75d5164cc42f0fd0bb92c9988021f617725933100c5e43a80b266200cbb7050164cc401878a9bb2a9988022f612765533102477414ecaa662008ed829d954cc401878a8bb2a99885e2fa1f64553310bd1f42ec8aa6624aaae82d9154
  | 13 => 0x61e3b6caaa28227c3c651cd545047b17d0db92a8a0b3f0f19772551414569bba8e2aa2821687d87d9763504014bd07b2ec6a080297a0c65d8d4113e1f3a4ebb1a821787f875d7635040187886baec6a08021fe0175d8d410061fa02ebb1a821787e85dc363504010fb0bb86c6a085e1fe1f50d8d410043ec3ea1b1a8200a5e83d4363504010ff0ea86c6a08021f61d50d8d410052e41aa1b1a82268bf8750363505b387ceaa06c6a08030f5d540d8d410054e41a81b1a8200a9d840c3635040159b04186c6a0802b560430d8d4100637b2ce531a8200c6c659ca635047f95ec9394c6a08031bd957298d410063632ae531a8200ccf635ca63504010fd0fb2ac6a08021fa1c6558d4118d2f41eca31a8286c3c7419463504634bd06328c6a080237e1d6318d4118c5e43aa831a8217c3c7555063504010ff0ab90c6a085e1f2157218d410043fc2ae031a821787c855c0635040517908b80c6a08c61fa1f5018d4118c3e43ea031a8231a5e83d4063504630f90ea80c6a08c69720d5018d4118c5e43a8031a82d9c3c75500635046353906a00c6a0802a76123018d4100566c106031a8200ad5810c0635040187ca93b4a6a08c697a0f6594d410052ec1ecb29a8217a3c86552535040187cecaa4a6a08030fa127694d410061ec24ed29a823187e839da5350401878873b4a6a08030fd0a7694d410061f20ced29a8200c3c419da53504010ff013b4a6a08021f6027694d410061fa04ed29a8200c3d409da53504010fd0c3b4a6a08c717a0c7694d4118e1e218ed29a823187f801da53504010fb003b4a6a08030fd007694d410061ea00ed29a8282a3e86dd2535040187cedba4a6a0802c7a0f7494d410145e420eca9a8288c3c74d95535040187ecbba2a6a08af0f1977454d410061e21cec29a820087f809d853504010fb013b0a6a08030fd027614d410061ea04ec29a82038be86dd64350457878cbbac86a0a1e2f2197590d4115e1e32aeb21a8286a3e86d96435051587cedb2c86a08c68fa0f6590d414461f39ecb21a8288e1e73d96435040147f01b2c86a08028f6036590d410061fb86cb21a8200c3d70d96435046353906b2c86a0a228fa186590d4143e1f3b0cb21a8287c3c76196435042317b0fb1c86a08ae8fa176390d410051ec2ec721a8200e1f65d8e4350401c3eca31c86a0803871946390d4118f0fc28c721a8231e1c8518e4350401c3ea031c86a0803875406390d410051f434a721a8231a3c8694e4350401c3ec729c86a08c78718e5390d410051f430a721a8231a3c8614e4350463c38c629c86a08f62f2197290d410049fc2ae521a8200c3c655ca4350401938c6b9486a08db2b1897290d4118f4a31ce321a8231e94635c643504010ff0ab9ec4a085e1f21573d894100556c2041b128200acd8308362504015cb02106c4a0
  | 14 => 0xe7314e4290401c3cc629c852085e1fa1776cca410043ec2eed994821993c855d3329047f33906ba66520803275d263cca413952e42ac79948231c5f7614f32904018baec29e65208021fe15764ca410bc3e42aec9948200c5c7598d329040193ee931a65209c297215634ca410062e3aac69948204acc8258d32904018beec29a6520803175d8534ca410043fc2aec194821787c855d832904639388739ecaa080a2f21173d95410145e422e5b2a8200a3d8494365504030ff0ea86caa08031e5c150d95410068e21ce7b2a8200c7970d8365504014bf06b06caa08029720d60d954100537c12c1b2a8200a6c82583655042d0fb0e306caa08031e5c060d95414551e43281b2a8286c3e765036550401c76c0a06caa08038e18140d95414551ec26e7b2a8200e1c439cf65504018be8739ecaa08c70f10e73d954118e2e21ce7b2a8231c1c439cf65504010fb0139ecaa08030fd0273d95410051fc22e7b2a8288a3c845cf6550401c3886b9ecaa0803175cc73d95410051fc22e5b2a8288a3c845cb655051547b08396caa080297a0c72d95410052ec18e5b2a8200c6d721cb65504630fd07b86caa08030f10f70d95410061fa06e1b2a820087d879c3655051147d09386caa08028f61270d954118c3e41ae1b2a8200c3c435c365504018f700b86caa08030fd0170d95414451f420e1b2a828aa3d841c3655040147906a06caa08030f9cd40d95414451fc0281b2a8288e3b80503655040187ee0a06caa08030f5c140d954118c3fc3e61b2a8288a3c84cc365504010fd0f186caa08021f61e30d95414451f42461b2a8200a3d848c365504010ff0e986caa08021f21d30d95410051fc2261b2a8288a3c844c365504010fd0e186caa08021f61c30d95414451f42061b2a8200a3d840c365504014dd04186caa08029b60830d95414553b40861b2a8200a75810c365504010fd0f106caa08021f61e20d95414451f42441b2a8200a3d8488365504010fd0e106caa08021f61c20d95414451f42041b2a8200a3d8408365504014bd06106caa08029760c20d95414553b40841b2a8200a758108365505110fd0f086caa08021f61e10d95414451f42421b2a8200a3d848436550515ce020886caa08031794f73595410045fc22e0b2a82008df835c165504011b906b82caa08023be09705954102476412e0b2a82018bc875016550401976e0a02caa08670fd9273195410ce1fb22e032a820087f87d8065504018f2e1b00caa08021f61e60195410051ec24c032a820087f87580655040147f08b00caa080297e0d60195410052e41ac032a8200a6f8258065504014d904b00caa085e1fa1c60195410043ec38c032a8286a3e8418065504018f2e0300caa0a1e8fa19401954143d1e4328032a8288c3e765006550401c76c0a00caa085e8fa1b655514145
  | 15 => 0x9a9cc72080387d505398e4174f0e2a0a731c8200cac425ca63904634b906a84c7208c62f21d4098e4100c6ec3e6131c8200a5c854c2639040153f08984c72085e1fa1f7558e414162ec1eeab1c8200c3c43dd563904010fb01baac7208030fd037558e4113e1e3a0eab1c8200c5f75d4d639040153b09a9ac72080317dd45358e410043fc2ae0b1c821787c855c163904010fd0fa82c72085e1f21f5058e410043f43aa0b1c820087c8754163904014b906a82c72089a2f21d4058e410061fbaa80b1c82d9c3c7550163904031b90e982c720802972153058e410061faa6ed29c82048ee82dda53904011db05bb4a72080297e0d6594e4118d2e41acb29c8200c3d655d253904018bce6bb4a7208c70fdd97494e413e43fc3ac729c8231a5f8798c53904634bb0f318a7208c787e126314e4118f0e424c629c8231e1f7498c5390463c38e9318a7208029760a6314e417970e214c629c827ce1f4198c53904f9c3a83318a7208c717dc26314e410062eb84c629c82f2e1f4098c5390401c3a81318a720a0a1fe1d6314e410052fc3ac629c8282c5f8758c53905e3c3908b18a72080297e096314e410062fb82c629c8200c5d7058c53905e3c3e80b18a720803875016314e410ce1e3aacb21c8200c9e7598e4390463938eb31c87208c7a59c66390e4118e4fb84c721c8200c9d7098e4390401c3ea131c8720803875426390e411745fc3ac721c8200a3f8558e43904574790ab1c87208c78798e5390e410070eb1ca721c8231e1e6314e4390463d2cc6b8c87208030f1537558a410046f41eeab1482008dd83dd5629042f0fd0fbaac52080297a0f7558a410061f426eab148200c3d84dd562904630fd07baac52080317a0f7558a410042f41eeab148200c5d83dd5629040187887baac5208030f90b7558a410061e216eab1482f0c3f41dd562905e187a83baac5208021f6037558a410061fa06eab1482008be87d51629040187eebaa2c52085e1fa177358a410043ec2ee6b14820087e8794d62904630f90f29ac5208021fa1c5358a4118c3e438a6b148200c3f7590d6290457878eb21ac5208021fe157058a410bc3e42ae0b14820087e87d41629042f0f90fa82c5208021fa1d5058a410043e43aa0b148200c3f7550162905b3878eaa02c5208063b21d2058a410061faa2ed2948272c5c659ce52905dfa3ea939ca5208030f5977454a410045fc3acb2148219c3e75596429046393f0d39c85208c72721a7390a410068fc2ce72148200d1c859ce429040193ecb39c8520803275967390a411fe4fb14e7214823fc9d629ce429047993cc339c8520887659867390a410064fb04e72148200c9d609ce4290401a3ea139c8520803475427390a410061f3acc72148231c9e7398e429040127b0f29c8520803479ce5390a410cc9fc38a72148200d1
  | 16 => 0x610d32006c6904ec21a64f9e1e65d94434c93b63d0db288699003479db6510d320070f3b6ca21a6400b1f80d94434c80163b01b28869900347dc36510d320068eb86ca21a6400f0f20d94434c801e1a41b28869900267e1d6510d32005c7c12ca21a6400b1e86194434c93bc3d0c3288699003479d86510d320070f3b0ca21a649db1f80194434c80163b00328869900347dc06510d320068eb80ca21a6400e1e60194434c801c38c03288699003c3c806510d3200786900ca21a647095e85dcd424c80193ec839a84991f7c310853509321b54f430879926400e1f6510f324c953c38ca21e64990c6e320c64cc932005c7430879926431e8e8610f324c801e1eca21e6499003c319443cc93218dc7c008799264f8b8d8010f324c863b1ee021e64993df635c043cc9327b787a808799264f6f0d5010f324c801c38ca21ec2990038714c43d853200e7438241b0a6400ee120843614c8015ab06086c299002b960810d85320061f3aec930a6400c3d75d92614c80187cea324c2990030f5d46498532004cec388730a649dd1e7510e614c801a3aea21cc2990da2f21b74585320045f43ec8b0a6400c3f75d91614c801878ebb22c2990032e1c364585320045f438c8b0a6400c3f75191614c801878ea322c2990032e1c06458532004cf43886b0a6400d1f7510d614c93ba38ea21ac2990038719443585324decc38086b0a6400cbb64dc1614c801970c9b82c2990036610f70585320047bc3ac230a6400e9443584614c8015e100b08c2990122fa1f54590320061fbaea8b2064018bc87501640c801976e0a02c81905e2f61376550320061e2a6ecaa06400c3c545d9540c86353906b2486190132b9c96490c320066729eec9906400c4e53dd9320c80199aa7bb264190c72b90f764c83218e5621eec9906400caf40dd9320c80195a81bb264190032bddb744c83200657bb0e89906430b8e8790d320c863b1d0f21a64190c763dda434c83200747bb4869906400f0f7590d320c801e18eb21a64190c6e3e02434c8327adc6c04869906431e8f6090d320c9e9d1ac121a64193d3c3d42434c8327a786a848699064f3acf8650d320c80169f0aa1a64190c6e3e11434c8320145f43ee8b086400c3f75dd1610c80117b01ba2c2190030fdd474584320061e3a8e8b0864138be8790d610c80187eeb21ac2190af0f1d643584320045f43886b086400c3f7510d610c84f878ea21ac2190022fe1170584320145e422e0b0864008be87d01610c8051790fa02c2190030fdd740584326d61e3ae80b0864008be87501610c8011790ea02c2190030fdd540584326ce1e3aa80b0864018f487441610c80187ea839acb208030fd5370596410061faa2e0b2c820187c87541659040147f08a82cb208031edc150596410cd1f42a80b2c8200c3c545d6639040153b0
  | 17 => 0x226400a3e85980644c80147b0b300c8990022fe1d60191320051fc2ac03226400a3c85580644c80156f02b00c899002ad20560191320145f438c032264008bd87180644c80147d0a300c8990028f61460191320055b408c03226400ab581180644c801972e0300c8990028fa1b50191320051e436a03226400c3e76d40644c939a38e7a80c8990028fa1950191320051e432a03226400c3e76540644c80163906a80c899273471cd50191320f4ce43e60322643099c874c0644c8615390c980c899002c72153019132186c639e403226400aac86480644c939b18e6900c899003aa18120191320061e2a4ecaa264008bf845d9544c801878a83b2a89905e2fa1f64551320bd1f42ec8aa264048de86dcd544c8018becbb9aa89901273a0b73551320064fb20e6aa26501d1c541cd544c801c3e87b2c86990daa760f6490d320f64f39ec921a64048bf87592434c80147f0ab2486990ae8f2156490d3218e1f29ced21a6431c3c539da434c86395e653b486990c72b0ca7690d320045fc04ed21a64008bd809da434c80187ea13b486990030f5427690d3218657904ed21a6400cad209da434c86d53b07b2c86993f387d4f6590d3215d1f436cb21a6400c3e76d96434c9f9c3d07b2c86990038760f6590d320051fc06cb21a6400a3d80d96434c80187ee1b2c86990030f5c36590d320045fc3acb21a6400c3e76196434c8fb0fd0dbaa86991fb0f1937550d328068e21eeaa1a647987e87d95434c9070f90fb2a86990038710f6550d320061fbaec8a1a6400c3c75d91434c86d958e5b22869926b6310f7250d3218e1f29cec21a6431c3c539d8434c86395e653b086990db274ca7610d3218e56194ec21a64008bf809d8434c80117b013b086990030fd427610d320061ea84ec21a6436caf209d8434c80195a413b086990c2a760f6510d327cf0fa9eca21a6427a3e86d94434c80187cedb2886993e787a0f6510d320070ec1eca21a6400c3e73d94434c801c3ce7b2886990028fe036510d320051ec06ca21a6400c3f70d94434c80187ae1b2886990022fe1d6510d320051f430ca21a6400c3e76194434c86363906328869909f879965310d3213f0e32ca621a6400b1e8694c434c863c3d0d2988699003479da5310d3218f0f3b4a621a6431e1f6294c434c863e1ec529886990c6c7e025310d327fd8ec04a621a6431d1f7094c434c9fda3ae129886993f7c3c825310d327ef86904a621a64fc99f8754c434c8615390ca9886990c6c7e155310d320068f3b0a621a6431e1e7614c434c863c3ec429886990c7c3d885310d3218e8fb80a621a64fbd1d7014c434c97dc3cc029886992fb871805310d327d787900a621a64faf0d2014c434c83d93d0d3b0869900267e027610d32004cec04ec21a6400d1f509d8434c801a3aa13b086990db63c827
  | 18 => 0xc801d50c0906c8990daa760f75d91320061fbacebb226400c3d751d7644c80153d063aec8990daa760c75d91321b557410ebb226400aad821d7644c80147f0ab9ec8990028f21573d91321864fc3ae7b226400e1f855cf644c801c390ab9ec8990da2fa1f53d91320045ec3ea7b226431c9e73dcb644c80147f0ab96c8990028f21572d91320f64f39ae5b2264008be87d4b644c80117b0fa96c8990db8b94b52d91320051f42ee3b226400a3d85dc7644c86d53b07b8ec899002ab60b71d91320051f42ce3b226400a3d859c7644c86d53b0638ec8990022fa1c51d91320045ec38a3b226400a9e83dc3644c86d53b07b86c899003275cf70d91320064f41ee1b226400c9d83dc3644c80147d0b386c8990028f61670d91320064eb9ae1b226400cbb805c3644c80147d0a386c8990028f61470d91320054f418e1b226436a9d831c3644c86d55d04386c899002ab60870d91320055b408e1b226400ab5811c3644c80147d07a86c89940f879cf50d91320070eb9ea1b226400c3f70d43644c80187ae1a86c8990022fa1e50d91320045ec3ca1b226400a3c83543644ca05c3ce6a86c899003875cd50d91320071dc02a1b226400c3f70543644c80187ae0a86c8990022fa1c50d91320045ec38a1b2264368be878c3644c80117b0f186c8990028fa1630d91320051ec2c61b2264268bf874c3644c8511790e986c8990028fe1530d91320051e42a61b2264008be870c3644c83d17b0e186c8990028fa1430d91320051ec2861b226436aae820c3644c80155b04186c899002ada0430d91320055ac0861b2264008be87883644c80117b0f106c8990028fa1620d91320051ec2c41b2264008be87843644c80117b0f086c8990028fa1610d91320051ec2c21b2264008be87043644c80117b0e086c8990028fa1410d91320051ec2821b226400a9e83043644c80153b06086c8990daaba0810d913200556c1021b226400c3c64dd5644c801a3887baac8990038710f65591320bc3f43eeab226400c3c43dd5644c8010fb01baac8990030fd0375591320061fbaee8b226400c3c75dd1644c8010ff0ab82c89905e1f21570591320045fc22e0b2264008f7815c1644c8071e902b82c8990021fa1f50591320bc3e43ea0b22640087e87541644c8010f90ea82c8990062f21d40591320061fbaa80b2264d9c3c75501644c80153906a02c8990032edc140591321b64ec1cec32264008bd809d8644c80187cedb28c8990038760f65191320051ec06ca3226400c3f70d94644c80117b0f328c8990028fa1665191320045fc3aca3226400c3e76194644c86133d0fa98c8990c2a7a1b53191320070fb2ea63226430b8e82d4c644c801c3eca298c8990030fd9570191320061e32ae0322649c99c835c0644c80117f0fb00c8990032e5c360191320045ec3cc03
  | 19 => 0x38794f53592320051fc2ae2b246400a3c855c5648c80955904b8ac9190028fa1471592320051ec28e2b2464008be87145648c80117b0e28ac9193522f61e70592320051f42ce0b246400a3d859c1648c80955d05382c919002ab60a70592320065dc02e0b2464d78be871c1648c80147d0a382c9190028f61470592320051f41ea0b246400c3f70d41648c80187ae1a82c9190022fa1e50592320045ec3ca0b2464eaa3d85941648c80147906a82c9190038ee0150592320061fb82a0b246400c3d70541648c80117d0e282c9190022f61c505923275d1f428a0b2464008be878c1648c80117b0f182c9190028fa1630592320051ec2c60b2464288bf874c1648c84d1790e982c9190028fe1530592320051e42a60b2464208be870c1648c80117b0e182c9190028fa1430592320051ec2860b246404aae820c1648c80155b04182c919002ada0430592320055ac0860b2464008be87841648c80117b0f082c9190028fa1610592320051ec2c20b2464008be87041648c80117b0e082c9190028fa1410592320051ec2820b246400a9e83041648c80153b06082c919012aba08105923200556c1020b246400c3c54dd9548c801878a8bb2a9190122f21d64552320bd1e42ac8aa46430c3e73596438c80147f00b2c87190028f6016590e320061fb82cb21c6400c3d70596438c8010fb0dbaa87191fb0f9937550e323f43f43acaa1c647987c87595438c80187eeab2287190030f1d56450e3200656b26e4a1c6436c3e73594438c801c3ce6b2887190c387cc96510e321870e992ca21c6400a3f80594438c80147b00b2887190030fdc16510e320061eb82ca21c6505acd8694f328c90769b0d29e65190c79361a53cca3200526c34a79946483d4d7694f328c863c9aed29e651920fc399253cca3241f86b24a79946504f0f4094f328ca09e1a8129e65190c6d3e1553cca3200c7a43a20b0c6400ee120441618c80187aebaa6c899002a760f54d913200556c16a9b2264048dd83dc3644c9d78bae7a86c8993ab175cd50d91320051f42c81b226400a3d85903644c80317f0ea06c899353275cd40d91320065cb8281b226430c9e765cf644c8016390ab9ec89900387d9573d91321b5c6412e7b22640099d87d4f644c86d53d0da9ec89900387d9753d91321b5c7416a7b226400e1f6514f644c80187ecab86c8990032e5c360d91320051f42cc1b226400a3d85983644c80147f0ab06c8990028f21560d91320055bc0ac1b226400ab481583644c83d17b0e306c8990028fa1460d91320051ec28c1b226400ab681183644c80156b02306c8990032e5c060d91320051f436a1b2264e0c3e76d43644c80147d0ca86c8990028f21950d91326fe1f3b2a1b226400b1c83543644c93933f0e986c8990daa721930d91320058e42a61b226400e98604c3644
  | 20 => 0x6fc3ac631a8400c3c545d463508010ff0ab88c6a105e1f2157118d4218d2e41aa031a84318bc87500635080187ea83b4a6a120e8f6136594d4218d2f41ecb29a8400a5d83d96535080187ecaba4a6a100a3b2197294d4200637b2ae529a850bd2c545ca535080147f08bb4a6a10c68f2197494d4218e1e3b2e929a8431c6f769ca5350801a5ae9394a6a10c69b2197294d4218e363b2e529a8400d2e745ca5350a17a9ce6b94a6a108f0f1d76590d425ae57396cb21a8423c3e75596435086353906b2c86a112b2b9c96590d420f45ec3ec721a842ba3e85d8e435080147b0bb1c86a107a6761f6390d420070fa80c721a8400e1d5018e4350801c3ec729c86a10c78718e5390d4241e97394a721a8431e1c6314e43508fba5ce429c86a10c72bdda7290d4218f4631ce521a84049af875ca435083db1ce6b9486a10c7a318d7290d421e45e432e321a8400c3f65dd152508639388739ec2a10021fe1573d85420bc3e42ae7b0a843ec3f645d461508011ef0eb08c2a10030f5d754d933218d4f41ea9b266431e8c435cb64cca15c3887a86c9994278710d50d933200c5fc3a81b266431a9c8350364cc801972e0a06c9990c657a0f75593320068e21eeab26641787e87dd564cc8018b8e7baac9990c61fa0f75593320061e21eeab26640087d80dd564cc80187e81baac999003171cc75593320061e3aee8b266431c9c73dd164cc8010ff0ab82c99905e1f21570593320246e41ae0b26640087e87d4164cc82f0f90fa82c9993af171cf50593320043f43aa0b26640087c8754164cc9d58b8e6a82c9990062f21d40593320061fbaa80b2664d9c3c7550164cc80153906a02c999353271cd40593320065db8280b266400c3c549d954cc8071ed033b2a9990023d60676553320045fc22ecaa66400c3c541d954cc82f1790eb22a99905e8f21564553322554e41ac8aa664048dd861cd54cca11a38a839aa9990028fe156490f3215d1e42ac921e6431a9c8359243cc863a98a6b9487990c76310d7290f326145fc3acb21e64318bc8759643cc86353906b2c879941f4710f7550f320045fc3aca21e64318bc8759443cc86353906b28879941a67e1d5310f32004cfc3aca21e643199c8759443cc8474790ab228599012a720d6450b32394af42ee6a166431d1c535d361cc80133b0e21cc3992a7479d443987320068eba88730e6431e1c5310d61cc8031e90e882c3990073c1c110587320047bc3ac230e6431e944358461cc80917d0faa2c9190030fdd754592320245f43c80b246400a3e85901648c80147b0b202c9190062f21d40592320065db8280b246400c3f759d5648c80955d053aac919002ab60a75592320061eba8eab246400a3e85dcd648c80147b0bb9ac9190028fe1573592320051e42ae6b2464008be87d4d648c80117b0fa9ac9190
  | 21 => 0x4058e5390801c3a80b1ca7210c71bdd97294e423f596422e529c8400d2c745ca5390a21a9ce6b94a7210c79398d7294e423ae1e3a2caa9c842bc3e65dd1539080187acbba2a72100327dd26354e4210e4e3a4c6a9c84048dc8758d539080193ee8b1aa72107b271d16354e420062f41aec29c847dc5d835d8539080187886bb0a7210031bd097614e423ee36212ec29c847dc5f325d853908fb8ba64bb0a7210021fe017614e420043ec02ec29c8400c3f405d8539080187a80bb0a7210c697e1e6314e4218e2fc3cc629c8431a5d8798c53908638b90f318a7210c787e126314e4218f0e424c629c8431e1e7498c5390863c3ae9318a7211f787d0a6314e423ef0ea14c629c850fe1c4198c53908638bee1318a721003175c26314e4287f0fa04c629c8400e1d4098c53909070ff0eb18a72100297e1d6314e4241e2fc3ac629c850ee1c8458c53908018bee0b18a721003175c16314e428770fa02c629c8400e1d4058c539085787ccbbac87210022fe197590e4215e1f32aeb21c8431a3c83596439086187ce6b2c87211d7879cd6590e421b717392cb21c8400a3f80596439080147b00b2c87210030fdc16590e420061eb82cb21c8431c9f8798e4390863c3f0b31c87210c7872166390e4218e4fbacc721c8400c9d7598e4390863d1ce531c87210db275ca6390e420064f38cc721c8431c9f7098e439080193ae131c872100387d426390e420070ea84c721c84308bf8758e439080147f0ab1c87210ae8f2156390e421054fc3ac721c8430c9f8758e4390801c3f0ab1c8721003872156390e420064fb82c721c8400c9d7058e4390801c3ea0b1c8721003875416390e4218d1fc34a721c8400a3d8694e4390863c3cc729c87210038758e5390e4218d1fc30a721c8400a3d8614e4390863c3cc629c87210038758c5390e4200716b2ae521c841ed8e735ca4390863d1cc6b9487214362f21d54586420be1f3aaa8b0c841787e85dcd61908010fb0bb9ac3210063d21d10586420061faa4e7b2a8431c9c439cf65508018eca2b8ecaa10122f61370d95420061faa6e1b2a8400c3f545c365508030ff0ea86caa10028fe1150d95427561eba2a1b2a8400c797054365509a917b0ea06caa108e8fa1540d95423ad1f42ee8b2a8400c5e53dcd6550801878a839acaa14338b15372595420061e2a6e0b2a8400c3c545c165508011bf06b82caa10023720d70595420047bc0ae0b2a84038f4815c165508031790ea02caa108e8f21540595420065db8280b2a8427c3e749d7635082f0ff0ebaec6a10030f10d75d8d420043fc02ebb1a8400c3f405d7635082f0fd0bb86c6a10021f61770d8d420bc3fc3ea1b1a840087d87d4363508010ff0ea86c6a10021f61d50d8d420052e41aa1b1a84268bf8750363509b387ceaa06c6a10030f5d540d8d42004
  | 22 => 0x182c721002b5a043058e420056ac0860b1c8400e1c74dd563908014bb01baac72100387d037558e423ed2f42ceab1c8400c5f759d5639083d53d093aac721002a76127558e420054fc22eab1c8483a5e871d563908018bd0e3aac721003871d07558e423ee2fb90eab1c8400a5d801d56390801c3e803aac72100297a167158e420052ec2ce2b1c8400a9d849c563908014bf0ab8ac721002972157158e420054fc22e2b1c841ea9e84145639080153b0828ac72107aa72137058e420052f42ce0b1c8400a5d859c1639083d53d09382c721002a76127058e420052fc2ae0b1c8400a5c855c1639080153f08b82c72107aa72117058e420052f428e0b1c8400a5d851c1639083d53d08382c721002a76107058e4202567410e0b1c8400acd821c163908015ad02382c721002b56047058e420052f43ea0b1c8400a5c87d416390a07c38e9a82c72140f87d035058e420f54f424a0b1c8400a9d8494163908014bd0ea82c7210029721d5058e428170e3a2a0b1c8400e5b805416390a05c3e80a82c72107aa7a105058e420054ec20a0b1c8400a9c875016390801c3eeaa02c721003871d54058e426bd4fc0280b1c841ee9b805016390801c3ea0a02c721003875414058e420052f42c20b1c8400a5d85841639083d53d09082c721002a76121058e420046f43820b1c84008dd8704163908014bd0a082c721002976141058e420f54f42020b1c8400a9d84041639080959d04082c721002b36081058e420062fa9eed29c84048ee82dda539080187ca8bb4a72100317d4d7694e420052fc1acb29c8431a5c8359653908098dce4b2ca72105e8fe195494e420061ebb2a929c844ad2e7255253908091bb0f31ca72105e97a166394e4218e4e3a4c729c8512e1e5498e5390801c3aa931ca72105e97a156394e420bd2e42ac729c8400c6d655ca539080535908b94a7210034b9517294e420066731ae529c8431c5e83dda539086387887bb4a7210c71ba0b7694e4218c3fc06ed29c840087d80dda539080187e81bb4a7210030f5037694e420062f39aed29c8400c3f845da539080187908bb4a72100317a0d7694e4241e2ec1aed29c843187c835da539080187886bb4a72120f0fd097694e4241e1ea12ed29c8400c3c415da53908010ff00bb4a7210021f6017694e420061fa02ed29c8400c3d405da539080187aedba4a721002c7a0f7494e4200697396e929c8431a5f8798e53908634bb0f31ca7210c787e126394e4218f0e424c729c8431e1f7498e5390863c38e931ca7210c7939ca6394e4241f0fa14c729c8483e1d4298e5390a25c388331ca7210c717dc26394e420062eb84c729c8512e1f4098e5390801c3a8131ca7211f61fe1d6394e420052fc3ac729c847dc5f8758e5390a23c3908b1ca72100317dc16394e420062eb82c729c8511e1f
  | 23 => 0x98e4218f0e3aee931c8431e8d82dd2639080153d03ba4c721002a76037498e4218d4f43aa931c8431a9c87552639096b53f0aaa4c72108787e155498e420070fbaaa931c8400e1c75552639089553f04aa4c72112aa76095498e422570f292a931c844ae1c52552639080153902aa4c721002a7e015498e420054ec26e331c8400a5e859c663908014bb0b38cc721002a76127198e420052fc2ae331c8400a5c855c6639080153f08b8cc721012b3a087198e4210d4f426a331c8400a9d84d466390801c3aa9a8cc721086a7a105198e420054ec20a331c8513e1e54146639086353909b84c72100297a167098e420052ec2ce131c8421a9e849c2639080153b09384c72100297e157098e420052e42ae131c8400a9f845c2639084353908b84c72100297a147098e420052ec28e131c8421a9e841c2639080153b08384c721012b3a087098e4200566c10e131c8400ad6811c263908015ab02384c721086a7a135098e420054ec26a131c850ae1e54d426390801c3aa9a84c7210c697a1f5098e4218d2e43ea131c850ae1e84d426390801c3b09a84c72100387dd35098e428570e3a6a131c84ebe1f42d4263909d7c3a85a84c72142b871075098e428570fa06a131c8421a9e84942639080153b09284c721086a7a115098e4284f0f2a2a131c8400e1d5454263908634bd0ea84c7210c69721d5098e4284f0f422a131c8400e1d845426390801c3ee8a84c721427871d15098e427570fa12a131c84eae1d425426390a13c3882a84c72100396e015098e4284f0fa02a131c8421a9e84142639080153b08284c7210c6a7a1d4098e4218d4e43a8131c8400a9f85502639080153b0aa04c72100387dd54098e420070e3aa8131c84d4a9f8250263909a953b04a04c721002a72054098e426bd4fc028131c8421e9b805026390801c3ea0a04c721003875414098e4210d4e4262131c8400a5e8584263908014bb0b084c721086a7a121098e420054ec242131c8400a9f84442639084353908884c72100237a1c1098e420046ec382131c8400a5e8504263908014bb0a084c721086a7a101098e420054ec202131c8404ace82042639080159b04084c72105e1fa1f7558e4241e2ec1eeab1c8400c3c43dd563908010fb01baac7210030fd037558e4213e1e3a0eab1c8400c5f75d4d639080153b09a9ac72100317dd45358e420043fc2ae0b1c841787c855c163908010fd0fa82c72105e1f21f5058e420052f41ea0b1c840087e8754163908010f90ea82c7210029720d5058e421345e43a80b1c8400c3f7550163909b3878eaa02c721002a720d4058e420052f42c60b1c8400a5d858c1639080153b09182c7210063721d3058e420052fc2a60b1c8400a5c854c1639080153f08982c72100297a143058e420052ec2860b1c8400a9d840c1639080959d04
  | 24 => 0x28632c3f645d66150dcf8bae632cc2a19fa1f21b75585430043f43ecab0a860087e871956150c011ef0eb08c2a18022fe197294c4318c5e432e52988631d1c535ca5310c01a5ca4b94a6218c74714d7194c430069b28ae32988600a3d8494165908030f90ea82cb210031edc150596423ad1f426e6b2c8400a3d84dcd65908018bee739acb210129ba0a73596420051fc22e6b2c8431c3c431cd65908fb8ba6439acb210021f60073596420061fa00e6b2c8400a3f845c565908eb47d0838acb210028f610715964218c3f41ee0b2c8400c3c43dc1659080187e81b82cb211d68fa1270596420051ec24e0b2c843187c835c1659080187886b82cb210031ee0170596420061fa02e0b2c84eb87e871c165908eb47d08382cb210028f61070596420051e41a80b2c8400c3c7350165909af47f00a02cb211d78ee0140596420061fb8280b2c8400c3d7050165908630f90f982cb211d68f21330596420043f43c60b2c840087d878c165908eb47d09182cb210028f61230596420043fc3a60b2c840087c874c1659080147f08982cb211d68f21130596420043f43860b2c840087d870c165908eb47d08182cb210028f61030596420253741060b2c8400a6d820c165908014ed02182cb210029d60430596420043f43c20b2c840087d8784165908eb47d09082cb210028f61210596420043f43820b2c840087d8704165908eb47d08082cb210028f61010596420052f41820b2c8400a5d8304165908094dd04082cb210029b608105964213e1f328e6aa484b3d2f75dc954908631790eaa4c72105f0f1d55498e4218d4e41aa931c8400a9d84d4e639080153b0829cc721423879505398e420070eaa0a731c840087f855c6639082f0f90ab8cc7210021fe157098e420bc3e42ae131c843187e87d4263908630f90fa84c7210c697a0f5098e4218c3e43aa131c8431a5c8354263908631790ea04c7213670f1d54098e4218d4e41a8131c84018dd87cc263908014bd0b184c721002976163098e420054ec246131c8400a5f854c263908014b90a984c721002a7e113098e420052f4286131c8400a5d850c2639080153b08184c721002b5a043098e420056ac086131c8400e1e54dd6639080959d05bacc7210c787e137598e4218f0e426eb31c8431e1c74dd66390863c9d05bacc7210c79360b7598e4241f0fa16eb31c8483e1d42dd66390801c3883bacc721002976037598e420070fa06eb31c8400c5f759d6639084353d093acc721002a76127598e420054fc22eb31c8421a9e841d6639080153b083acc721003879507598e4218e2f438eb31c8431e1e841d66390863c3b083acc7210c7871d07598e423ee2eb90eb31c847de1f421d663908fbc3a843acc721003871047598e420052ec00eb31c8400e1f401d6639080153b0bba4c7210c787dd774
  | 25 => 0xc651790eb12c3218028fe1562586431b656392c4b0c86288bc875816190c01976e0b02c3218c66d21d1058643146d838220b0c8631c3c655d46190c0117b0f328c3218c70fdd665186430049fc2ae430c862b93c855c86190c0117b0f310c3218a22f619701864318e5db02e030c8628d3a705406190c01a72e0a80c3218031b94972d95430063b28ae3b2a8600a3d849436550c018f2e1286caa18061fe1d50d95430063cb82a1b2a8600c7970d836550c550fb0e306caa18031e5c060d95433ce1f3b281b2a8600b1c835036550c01c76c0a06caa18028fe1172d95433f51e422e5b2a8600a3d841cb6550cfd4bb06396caa18031b5c872d95430051ec26e3b2a867ea3e849c76550c0147b0938ecaa18031d5c471d95430061e21ee1b2a8600c3f40dc36550c010fb0f386caa19fa8fa1270d95430051ec24e1b2a8600c3c435c36550c018f700b86caa18030fd0170d95433f51f420e1b2a8600a3d841c36550c018f2e0386caa18028f20d40d95433f51fc0281b2a867ee3b805036550c0187ee0a06caa18030f5c140d95433f51e42661b2a867e87e878c36550c010fb0f186caa19fa8fa1230d95430051ec2461b2a867a87f874c36550d010f90e986caa18028fe1130d95433f51e42261b2a860087e870c36550c550fb0e186caa19fa8fa1030d95430051ec2061b2a8600a6e820c36550c014db04186caa18029da0430d95430053ac0861b2a860087e878836550c010fb0f106caa19fa8fa1220d95430051ec2441b2a860087e870836550c010fb0e106caa19fa8fa1020d95430051ec2041b2a8600a5e830836550c014bb06106caa18029da0420d95430053ac0841b2a860087e878436550c010fb0f086caa19fa8fa1210d95430051ec2421b2a860087e870436550c010fb0e086caa19fa8fa1010d95430051ec2021b2a8600a5e830436550c014bb06086caa18029ba0810d954300536c1021b2a8715c5f75dcd6550c0117f08b82caa180237e0d705954300c5e43a80b2a8600cbb705016550c5787ec8b80caa18021fe1f60195430063cb86c032a860087d879806550c0147b09300caa18021fe1d60195430051fc22c032a8714a5f835806550c2f0fd0e300caa18021f61c60195433cd1f420c032a8600c79701806550c0147d0ca00caa18028f21940195433f61f3b28032a8600b1c835006550c01c76c0a00caa18c78710e7694d430061fb2ee8a9a862bc3c65dd15350cf347d0db2c86a19fb87d8f6590d433f61f39ecb21a867ee1e73d964350c0147f01b2c86a18028f6036590d430061fb86cb21a8600c3d70d964350c2f17f0eb2c86a19fa8fa186590d4383f0e21ca7b128600a9c835036250c6d87ec8bacc4a1c03175cf659894380e2eb98cb312869accd73d8a6250c010fd0fb2ac4a18021fa1c655894300477c3ac431
  | 26 => 0x2abe096598a431b556c3ec53148631cad87d8a6290c0155b0bb14c5218c6aba0f6298a4318f4741ec53148631e2e53d8a6290c63c58a7b14c521802aba076298a4300556c06c5314860093f855c66290c572790ab8cc5218c66b2097198a431445fc3ac13148600aaf825826290c01972e0b04c5218038bd8b5098a4300717b12a13148631aae864826290c6333d07baac5218ae4fa1f7558a4318d8f41eeab148600e1e63dd56290c6327d07baac52180347a0f7558a4318c8f41eeab148600d1d83dd56290c6327907baac5218030f98f7558a430068f31eeab148600c3e62dd56290c01878c5baac5218024f6037558a430070f318eab1486368be879956290c0187eeb32ac5218daaba0a6558a430045f438cab148600c3f751956290c0153d0632ac5218daaba086558a430049fc2ae0b14862b93c855c16290c0187eebb02c5218030f1d76058a430054f41ec0b1486288bc875816290c0187eeab02c5218030f1d56058a430065db82c0b14860093e87d416290c572790fa82c521c0f8798f5058a430049f43aa0b14860093c875416290e05c3cc6a82c521c5fa398f2058a4318cd643a40b148716e8e634816290c6387cc6ba8c5218c74798d7518a4318e97312ea3148631d2d625d46290c0127f00ba8c5218c70fd817518a430045fc3aca314862bc3e755946290c63976c0b80c5218030f9d56018a430061ebaac0314862b93f87d406290c0127b0fa80c5218024fe1d5018a430049ec3aa03148631d1e635d76190c0127f00baec3218c70fd8175d864315e1f3aacbb0c8631caf659cb6190c0195acb396c3218c72b98e72d864318ec731ce5b0c8631d2e539cb6190c63a58a7396c3218032b98672d864318e5630ce5b0c8631caf609cb6190c63b1cc6b96c3218c74b94d72d864318e9629ae5b0c8631caf605cb6190c0147f0ab16c3218030f9d562d86431b657392c5b0c8631cbb605c36190c0187ceab06c3218030f5d560d864300657392c1b0c8600cad725836190c5727f0fa86c3218024f61f50d864300697396a1b0c8600d2d72d436190c0127f0ea86c3218024f61d50d864300697392a1b0c8600d2d725436190c6327d06bacc3218c64f20d75986431761f31aeb30c8600d1e635d66190c6587ec2bacc3218cb0f58575986430049fc02eb30c8600c3d759966190c0156b0332cc3218030f5d4659864300557410cb30c8600c3d7598a6190c0195ae5314c3218028fa1462986430061eba8c530c8600c3e75d826190c0187aebb04c321802a7a0f60986431445fc3ac130c8600c3e755826190c0187aeab04c3218032e5c1609864315c9fc3ea130c860093d87d426190c0127f0ea84c3218024f61d50986430045f43ecab0c862bc3e75d956190c0153d07b2ac3218ca2f21d655864315e1e3aacab0c86008be87d896190
  | 27 => 0xfa04a7b1aa8178bd84dc3635504d17f0ea06c6aa3662f61d40d8d540161ebaa81b1aa800a9c835036355001c3ca6a06c6aa0029761630d8d540054ec2061b1aa800acd820c363550015ab02186c6aa00237e1d6318d548c54fc22c631aa800c3c545c8635500195884b90c6aa0030f1537018d540061e2a2e031aa8318bc87500635504f4790aa00c6aa0c6a720d4018d540054ec246031aa91ce1c548c06355237c38a8180c6aa002b36083018d540056ac086031aa800c3c549cf625502f17b09b86c4aa0030f15370d89540061e2a2e1b12a8d98bd87503625519f4790aa06c4aa00b0f5d540d89540068e2a4e7312a800d1c545ce625523595ae9b14c4aa0023be1d621895466e4fb24e730aa800d1c549ce6155001a38a8b9cc2aa0023de1d611855466d5bc22c230aa919e1c549cf6590c01878a8b96cb218031b94972d96430061e2a6e1b2c86008de83dc36590c01878a8b86cb218062fe1d40d964315d1e42a81b2c8600cb9705036590cfd878e9baacb218030fd5370596430061faa2e0b2c860187c875416590c0147f08a82cb218031edc1505964315d1f42a80b2c8617a3f865955490c63878ecb2aa921b022f61b735524318ccf43ee6aa48679d1f751cd5490d9f87ccbb92a9218030f5957494e4318cce41ae929c8617a3f865525390c0587aecaa4a721802c7e0d5494e4318d8e41aa929c863195e83dd56290c01878a9baac52185e1fa1f7558a438752f41eeab148600c3e84dd56290c0187b09baac52180317a0f7558a430062ec1eeab148600c3e42dd56290c0187885baac5218030fd077558a430043ec06eab148600c3f40dd56290c0117d0faa2c5218030fdd75458a431b557416a8b14860087f855c16290c2f0f90ab82c5218021fa1f5058a430bc3e43ea0b14860087e875416290c010f90ea82c5218030fdd54058a436ce1e3aa80b1486018ec874816290c098dcc4ba8c5218023be1d6218a4300636baac431486f3cce735886290e1b1790eaa2c32185f0f9d5545864300c7a43a20b0c8601cf0704416190c011ef0eb08c3218c747e1673d964318e8e42ce7b2c8631d1e659cf6590c63a3acb39ecb21c634714a73d96438c68fa8ce7b2c8718d1f509cf6590c0187ccab96cb218034b94972d96430061f32ae1b2c8631cbb605c36590c5747d0ab06cb218a24fe1d50d96430051fc32a1b2c8600d1e735436590c01a72e0a86cb218030f19770596430061e32ae0b2c8631a3c85d816590c511790eb02cb218ae8f21560596430065db82c0b2c863193c875416590c634790ca82cb218034edc150596431045fc32e529c86318bc865ca5390c63a38a6b94a7218034b9497294e430069b28ae329c8631c3c655d76290c6387eeb32ec5218c72ed8170d8a4315e1e3aecb314862b8bf875966290c5787ceab2cc52180
  | 28 => 0x20008000000000200040020000001000800100040030008002002000000100000000000000000200040050008001000000500000020000000000c0000000000000000a000400000000000000000000c00000080010004001000400000000000000002000800400080000000000000400200000030018000000400500000020008005000000b000000000000030000000000800300080000004000000c000000800000040010000000000000000000000000000000800000100030024000000000000000000010004000000000000010008000000c0040000002000c0010000000000800000000010008001000000000000010000001000000000040000000002000000000000000004000000400000000000034000000000100080020014001001c00300300000008001000800000040030008001000c000000000300040040000003000400000000020000000000800000000020008000000c001000400c00000010004009000800000000040000000000000000000000008002001c00100000000008002000000100000000024001000400000040000000000000400200000010000001000000b001400600000000000000000000000000070000001000c00200000000000001000800200000000004000000400500200000004000000000500000000000000000400200000010000000000800100000010004001000c0000020000001c0020000003001c00000000000000000000000a000400800300000000000000000000140030000000000400000000010004001000800000000000010001000000100040000004000000800000080000000000000000100000000000002000800100080020000000000400000000010004000000000500040020004000000000500000010000000000c0020008000001000000000080004001000c00100000000000000000400000000010000000000000000000000000000000000000040000004000000400100000010008001000400100040000004000000000000040000000000000000000000000000000001c004000000000000010000000000400100140040000002000400100000010000002000000000000020000000000c0000000000000400600000000000000002000300000080008002000400300000020000002003000800000010018003000000400080000018002000400000040000000006000c00100080020000000000400100000010004000000000000040000000001000000000180000008000000c00800000020004003000400200000000000000000800300080000004000000000000000040000004000000100000050004000000000800000010000000000000000040030000000000400100000030052ec3ca7b1aa82ac5d8794f635523bc3ce929ec6aa343875d253d8d548ef0
  | 29 => 0x20008000000000100080000000000000400100080000000000000000000000000000001000000000040000014000000c000000000000140000008003000000000000000000000000800100100000000001000800000080000008002000c001000800000040020030001000000000040010000000000c007002c0010000000000400000000000000000000000100000020000000000c0020018000000400000080030008000000800000000010000000000000000000000000000000800000000000000000000000200000000000000000800100000000010002000800100100020004000000000400000010008003000800000000000000000000c00000000000000000001c000000c00100000000018000000400500000000000000001000200000000004000000000000100000000000000400000040040018000000400000000000000000000400200040040014000000800100040000000002005c000000000000000000004001000400500000000000004002400000000000004003000c00100000030010000000800100080000000001000000000040020000000001c001001400000000000000000000000100040020004003000000100240010000002000000500000000000001001c00000000010000000000400000080000008001000000000080060008001000400600080000000000000800700080000000003000000000000000000000000c0000000000000400c00040010000000000000100040000000000000800000000010000001000400100000010004000000400100000010000000000001400040000000000000000000140000000002000400200040030008000000400300040040000000000400000000000008000001c0000008001000000400000020008000000000000040010000000000000f000000100040040000006000400100040010000000001400000000070008002000c0000000005000000100000000000000000000000000010000000000000300180000004002000400000040000000000000400000040050000002000800000080010000000000000000000000000000000400000000000020001001c0000000000000000000000000004004000000000080000010002000400200000000000001004000100100000008001000c0010000008000000000040000014002000000000000030000002000000000080010000002000000100080030004000000c0000004000000c00500000000004000000000100000000000000000000100180000004000000400000040000000000000800300000000008000002c001000800300000000004000000800000000020000004000000400040000004000000800000000010000000000400100040020010004000400100140020014000000000400000010000002000
  | 30 => 0x24c780015b200069b1d7c0007341ea23c58fa0000003b1532a00058eb791a5ae2b3ed165516a4d5f53a3fc0000000002c1007ea6d00038b4a7862a20600001142f98000000000730000000000000000000000000000000001712000749b5340000000002c380008d70000ffc86a0001dc8f3000000072b8f58000000000000000057900000004220003768f2600000000000000000000e08000000d7938700000000004898001a1400019980000000000002d3ab3a000000000081e00000007f813e56600000000000001e3067800054e80036400000000003ac00003e0800000000000000000000000000000ef96f20cb0000000000c5e288e20dd7c000000000101c00000000000000002e70000000929420000138400000000000000000fb4000000000000255a00000000025300005001978001032927000000000000000001b8892b685438000a2c9090000000000000000000060e00000000000000000000add31800000007680000000000000000000256a17000000036332b8a8800059986d8000415638800000000013b800074f00033e8000000f290000df80000000001360000000000000000000000008d00008c700000018921fb8000000000dbe56580005e4000400100000000000000000c000000000100040000010000000c000000000100080000000002000000300080000000000000800000100000000004000400100000000014000000000000000000000004000400300080000000002000000100000020004000000800100000070000000000400500000020000007000000000000000000000001000b000000300040000004005000400200040000000002000000000000000000001000800000000050000000000000400080010000000000c0010000006000000100000000000003000c008000000100000060000000000000000040000010000000c001000800200000020004001000000e00140010020000000800500080010000000000800000000020008003001000000000000020000000c00300040050000000000000300000000000001001400000040000000000000800100000000000000000000000000000000001000000400000000014000000c00100040020004001000000000000000000000002800000000000004000000c00500040000000000000000000000000004000000c00700100040000003000800000000020000001000c0000004000000800000040000014001000000000040010008001000000100040010004000001c00000000000000000000000000000000004000000000100000000000001000000000000000000000000000100140010000000000400000040000000000000c000000400300040000000000000c0020004000000c00000040000000000000c00400040000004001000000
  | 31 => 0x8c04bea425180017ae00000002740000000002f1c000000000334c000d9a71825560000003bdacdc0000000000000000000000000000000008b9ed001ae5800000007a6af70000d5dd82110d1291f400000000000000000000000208ede2df77d8599c580a20001ce8d2ead1000000000000000000000000000002c06b8c0002a832fc0000ab8003300e220003689888000e0e16340001aa0d000000013a06f3433000000000038d800000000000025740000000001a840a05bd643ac64000000208ba6000019419b8000006948577bc858dc00029306f80000e513dea3a0000db800000000000058780000001238002e900009b700031d400000000000000000000001bf000022f0000000000000324a500000af167e933400000000000000000fb57100015ac0000000000b5a2fc00009614fc00000000000000000000000dae1614bc0000000000000000000043039e80016b826362700586900000862c40000bbb00024dc0000860001dc000002b9cbf17151300000000000000000000e20e98000000000000000019e9818000000000145c00000073580000008cd0948000d0e0000002bd40000006d900013887aa6b4000000000000000014560005238000000a8d000269800000000000000000000000000000cc93b08000000e47000139ab985040002cc400000015e00000000001a6aa6c000414b1680000009c700000016f000000019b00002234058000000140000000079eaf980000019ce27dd0e8001bae000000138997800034f10b60003d800024a866400000000019ea1f440d8000000ed5000183a00000021fc00000000056a2402604923000000073600073b14f82ba2c515cf76c0009a40e5964c0000000000000000e3451b80000000af0003cb0b220005860000974000309cc40588f236440000000000000000000000000000000000000000000c680004c0000054e00000006640000000000f04000b726b30000000bd6799b4080000000002ff0000000000000000000000000000000006ef84c000013d00000011840004e313b60000000000000000000000000000004564b26f47545348002aa8f140000000000000000000000000000034eb72c000cfc53f800000076d00000000002b80000a313220004ea0000000a7c00000000000000000000000624000000000000000000000a50000de937894200000000000000005530000000c51000329000000044780000004c30001a900000000000ee00004bd0000000000000000000000000000000000000000100000000000000000193e2e00000ce52ae0004ba80015ae3130000000000000000000000000000000000008200000000db0000418c0009d20000000000000000515354c80c0000000000000000000000011200032f00007ceb5300000000000000002ac800003
  | 32 => 0x1ee96100007d05f82752000000000000173cd87000000000000000000000009f23078000000ed8016665c00000065a00000000005329e3800000024e80000002ff0000000000e4a4e0abb00000000000e64000000000000000000000014140000000000a04000bd2000011800030e00000000000000003488c72c8d00000005f530600000000000000001c94eb600000000000000000003bcc000000000121254200000000000000000000000000bed000000027f5b100000000000000000c7d9600001a393dc74a29e0001d1381ae6f00014bc000000000000000000049585720000002290000a68000000000000000000000000000000e5000000000000028580009e600000000000000002b8c000907117000000041338c08cae14bc844480000000000000fd40000004b080000000000000db400000000000000000000002b140008dc800000000000000015d4000d4218a80000004730000daa00000000006140006e000018582720003a8185072a00000008f26c801d0000000000000000000000014a0338000000bf900000000000000000001c3e000000000000000000036003000000000000000000000000164cb2c0000001116000202379c00000000000000005d100009e80000000003740000000000000000000000000000000000000000000eb958c030424a295800000164a0000000000dd876b2bc00000000000000000c9800001cac68ee200000031e8000ced23100000003bd3d280001160006ba1eb800000000000000007e50001f596960000000e811020005068990000b7d00018ad8b000000032b400060a50fb074000ecf09f400000000000000014900000000000000c200000000c0a000000000000061901700000009b40000680000caa00002984e4979000000000079e0f280006a00000000000000000545400000000000000012e87750000000000000000000151eb8e00000004a20000000000000c9900000018e800000000000000002f427e5902bd02330320342ae4264b52ce1e68b0001631842000000000000000053900000000000001b8800000066a9f300000000000000d06e7700032814480000001a800000002a936f400000000000006a221000030452b40bb000294000000000000000005ed0000000ed09ad00000000000000000000000e8d17dcc285a60000000000e44000000000000000000000015d00000000000748d6400014a16129bc00038940007820002ba413f00043980000000000002a100d00000b4b2480000007410000e1000024ca25185194f00025ed522450bf38aac00000000035100001d000013e0202c460000000000d8c0002f9a000000053800000000000000009ca00077d3b24d108baa8e0e740000770000000000000000204c00099a60240000000000fe80000000000001c
  | 33 => 0x2a94000000000000000000000000000005f163800016ee00018b0000000432400b871d680001c885bc00034e0000000000000000185c000000000160400000000026cdd5df181a281c5566000000000000000055e000000000005680000000006e0850a0000003b4c000e56000000000000000000001d200000000000015e08d42e42e419ca9180730dbd96c0332a554f559a00000000000000000000000000e1700000000003fd80021f899e000036c0000004b2701bb50b1f0001fb80000009a25c10000000000000000000000029933080000000000af91be609d74c798000db63d578a9b1a0005b4800000000066e25080008d61350001ae610880037e13c0d6f0000000000000000000000000000000000000000001915c1400000007f20000006da73ac00000000000000000000002e2d1f20006f10001e1400000000000000004928153354c19224341d8589b52692df85cc93c30c000000000006c40000000000000000000000000000000000000000000000000000001ac00006b4a00cf420004c1c0005222840000000000443d6d380800013a0d1a78441ecd95cb0000000208000000000000061f8000000a9304bbcc90480f20001d753720000000000000000000000000000000036fc58600000000000000005080f7a0000000000000c8c000748912800000000038d8915000275400018647800000003a29a08000000e9c0000ad40000000000000000000dd267180003b82ba000246542600000000013142858000000000000000000000000000000d800084d0000000bc81744728000000000000000000004300000000000000001c40000b4d00000000c500027c800184824b22aab18000bc2000000163e12c8000000000000000368d94a706447000000000042f12dd098c7f00019c0000c0f6cf00000b100003a91740002f29db80009728bb3cda411d66000666000135827800000000000000000000000b9156115e97be0004c168e5264000000349844155700000000000000002ae8000000000000088c0002c1295600000000000000000000000000000f1e0000001ddd4a533f0000000000000000000000000000018b20000003ad57860006ffaadc000110000358800000000000000000000000000000a450002e0c0000000000000000e4c00024e000000017b80000000000000000506000000272ce800000000000d740006d806de000000116c000da000042080000000000001560ba6000000000000000000000000000000000000000000389a8d13464c1097ebd80001b90000000000093195114e00096400010fdb5ca8e5c9800000000000000000000db0b28000c9c000476800000000000025182170000000c3000058a470414d98e0000000000000e7a01b80000004ab0000e709a01d280000000000
  | 34 => 0x6ed0000a210000000bccba84cc4c580000005ff000000000068a32c4000000000000096800000032e800000000000035c8d50000000000000000000000000000000000000000000292464000000070790ed458a3a02400006e20000003b400000000000df00000000000a02680bdb1e509bd5923a93d01008fb8931de60510482871437a76c0000000d880000000006cc002e0003d5800033c00009cf8e8001626eb200005916000006e1b3fcd6c0000000834fb000000008594223cb00000000001c2000000000000052300000000000000000000c5b00000000000000000001a4e000000000000084b498bcba0007d300000000000273591290000000000016a000a0800000000000001a900000000000003c980000004794000000a351c800003ff0d856721f13f45721d55aa4ae20003e11eb7c740eabb98000000000000000000000000000000000000000d2c0000000000e0c0000000000000da8000159ab3c0008a4000000005b736000000000000000000000000004f880000000000001e9c00000007b8000000000000346102c74b513b69ebc43635d08001c1ad4100029e00005eb347800000000035100000000000000000bdf5123bf800000000000030c96740004b90000a668ddedced1c23761d05f0000000000617a2c54f2000000000000000000000000000001f780003f500047c000000000000000000000000e840000000000000000b5e00000000000000000000001e3800000000007a1cc14800000000000000000000000009600010aa0001019ca5d4c7ee161c0000005ae26ab134000138000000194ca6000000000006c504d00000000000000000000000000000191c00047183c6cbe8e16f780013037315a7af849da5aa0001bd486e000000000000071627cc0000000000001590000000000000000000000030f10920000002228000000000000000000000000000000002c38001b8e49500011fe00000000000000000000000484000e6d57980000000000000000b5800000000000000005ca80012e088721c19c400000000000004760000000001c820006c2800000000000000000000000000000000000737000071c8b2160a589312d5b7558000000000688000000000000000000000000000000000000248000089a966d190000960000000000000000000d230a000000050896c0000001473ab413600000006741f4000507800000041b00032bd97200000009d8ff2000000178000000070381b47490000000001514000000000000000000033e000000000030d175e00021a4e32000000000000000000000018303c0aa000000000000000000000000ae000000000000000000f6e0000006be924c80b0004558000000a28000000112e0000000001530aab7201df56c884a000000070800045b000156af2cb708
  | 35 => 0x800000000000000000000000000001a40db70000000000f1000003a8fc200020c00000000002f900000000000000000000ded000043c000dd500de96c0000000001d15aba09e000108dbe40004e9118c32cef400000019940000000000c5c000000000000000000000006e8d3a0000000e4c9a10000000000d4e00000000000cc52780008ac99810200000002675d18000000db32e785d5cf000000030e000054008e000000800000000000000000b880003d854e79880000009450002560b780000e18270000000265800000000006d038a0000000000ca0000c481bd40000000006cc800000000000000009220000be800000000000039c89cc1c90a0dc480000000001ca00000001a5248b1b8893292ab1ce7600000000000009ab000000000000000016860000000003a880007a33499adc00000000000000004b3000000000000000000000000000000580154000000000000051000000000003a764280000000003da8000000000000211c000a2f27b000083a00000000000006cf00000011888cf000087d4708da00000000008723220ea6000000261000000096c0dd4000000c020000000000000000000000000000000000005b30000000000000000113c00033c14e000000017f03e00000000000000f380003c000025282da9148001e642dc000000000000000000000000000000000000f2000021987e963600000000013fa00061322f73e6c0a16f12249efd8f3de8000f1683c1268000000733043800126c000000000000000000000016a219c0000000000000000000000000067a0000b6a0156049c115860000000001b6800010d15200000001f01855d7a0000000000000567000169c3300000000000000c1c12f000033e2d218e80012c3b033868000000f010003cb8000000000178750000000000000000000000000000cd000000000000004b1c000bb400000000000000000002ea00000002bd8000fdee080000001cc03b60002d6c00063d00000010ac0000002dce0006500001035e5400016171400001ee0000000d7c00009700000000000000000000000000000000054d4f70b58000a563811d9c00000063600000008350001f78f1800000008d3179e660000000000932b1900013bc8c8000304854648e4e6c000000000000000000000000000000000000002dd80000000000000ccc0000002e18048afb000000000000011110e4000a124460001964c275fd00001e800000000000000000a68000000d7e00000004801af0000000000000266d9b80000001ca0b547f9000146c0000005f006500010500000f5400000022880000000000000003a040000000001d8c6cc0000b980000000000c10000000000405000150600017e400000000000000014cc0003f6000000000000000000000001452c920000001fb0000000
  | 36 => 0x68016923789eb54cc00000000032e00000000000003af1ac251b17b07518a66f90000000968c520001f1800000000019f6000000000000000023a80010f8152b20000300000000000011f00000000000000000000000000000000000000000008ae00019fd1380000000000000aff77511041f200000000000000000002364520bb200000000000000000000e0100000000000000000000000d58000593bc640000000ff40000000005f00001886be49100001b980000000000000000000000000000000015f00000000000000000000000000000000000000000000a400000000000180000001dda00000014a80000000000000000000000000000000000028c0000d8b00000000000003598cd800059a524ba2400000000034dc00000072322a8000000783c0002d0000000000110485a00000000009660800814000000000000170232214c8000aba000000000000000033b8000000c5f1ad129c000cba00015f51e1be20000000000bb94bd35b90ec00018f26d80000005fb000000000000000000000000001bdc00000000000000000000001e586f44df0000000000277f7a80000000000000ff0000000773b6540000000000000c6069c006c0000007f100000000000002d080000000000000000000000000000000048c0000e886f000057296f8000d7a00000000000000002d88b160000000001d2a0120000001a2275780000000000000a70001bd00000002fa400033b00000005c4000000000000091c000232c00000000000002120002b4000000000066280000000004128000421000292000000086c0001c64000000519afdc000000269878860a0000000000afc1132b280000002490000000000000000048800079f1f9286c000000000000045a0000000000000000000000000000006f8000000a6a0000000000688e98acf00000000000000000000000207c0000000001b6800000000000000005c346700015f400000000007f50000000001d700000000000000000611aa6200060d000000000050d800000000000000000000000000002031df2000000000000000000039100000000000c5000057308113200000000002a5000000000000000006688003608000c8a000130000042b00030720004640ad800000000000000000008170000000000dee0000001e100000000000000ce23ef859e0000000000000000000485000040100000025222c400021020c000000065f38440000000032bf60009a500000000002460000000000adf14a800000000000000000001330eec0000000003580000c0658e0000001cca000115800000000000000000000b8800260c0000000c08000000ef00002e298ac42e8000000000963000024e00000000000000000000000000000000313000000000000011d3e436370000000000a3c722
  | 37 => 0xf00012ce87d00000004050002994a494d90000000000f881a857b40000000001c9800020c00000033980001a745e13900004b8000000000000064a00000007b077180012da0006bd80000000ae00000000000000000000000000000000000000000000003ba0000000000210000000000000000000029f4000000000000000017600000000000000000001210bae00010bc00000000000000000006a48000000000000000161400016f40000006a3000000000000000000000004690000000f48000000000094423555f04f8000837000247e6b035e298800000000000034e44c1000000042c6227ea4791c9c000000000000000091a805400000000046c1b6c0000000000000000d14000000000000000021800000003212b000000002cc8000f2200000001e40000000ab800000000000030d8a8e0000000000374953000000050a5c926e8000762431800202000000016b80000000000000ab800000000000000009a70000000000000000000162a0000000568000000000000000000072d0000000000000000000000000000000000000002ad80001c60000950000dcd0000f4e0000000000000551000000000007a67330d8000000cc60000a4c54c2f46ea00000000004440045a5842e43a0000000000000000000098200000000000004d78000000ade2378b910a415c531800000000000003b4000b71000176d9080000000000000000000000000000000000017aa000000000000000000000000000003908000b3c00059aa1e800086500000000000000000000000000520747c000000000000000000000000011d114b36181accd20003fb3698000000000000000000000037e992a0002750000000b6d0000000ca20000000000000000100c000bb80005a800000000000000001abc000000179211e9df61280008b62825412f05dae9336a013bdae0000129000000021305d00000000002860001c9200000000016d80006461710000a0e6620000000aef80000000e80cd13400015f200000029c4120000000000006272f1694ac4a046b93218000c2041c0000000000000000000000000000000010ee0007968001c84ee4551000000000000022440008fe0000001bb000023f8000c2400000000017b800007e00000000000000000000000130e99cb726e952091680006564824000000000000000000000000008dc00000000000000000000000000000f140000e5c170000000000000000079583f40000000000000000c2a0000000edc55b340800030640b5aa00000000007350020f9a0000e9800000039e0002cac00000000000000000bc0fcc0009f4000000000000000022440010723d228d006c00000000038013f858900037746d21200000b2ddb400000036e1d967c05ec800075800056080000000000f3ab6c000000481000000
  | 38 => 0xed0000000e8400000000000000000006c98000000298d2923ea000d0d02b0001670403166aa3000000000000000000000000000000cfe00022fc0000b40000f24000d97000000010059200017dd4bcb99000000000000000015b80000000000000000000000017498ee9a0001af0000aa100000000000006ba80000003ea02497e40000000003adcea2463cf1958c318bc500000000000004b280000000c68000000d18109800000130fea100000000000000000000000000462c0005360000000000000128000083865c0002d591b00000000000000000e6900000000000000000000000000000000000000070280000009cf0000001b58167000369c400b0b0a380000000000000160000000000257b69800021866588e01b822c8d4d6c22940f4dc0042806417380000001ac0179d540000001f54000000be800000000000004e896dcfea0000f88001590baa113615c000000000000000095017a4000000665000000152f000000000000082334c80000000000ec000139c5879aa0001cd8000000383182500002501f9c9a000000392001200000000000000000000000000000000381000000025880002b70002f6120a000c78000000000000000000000000000690000000000000000000000000029690a00003ff00000006c963387b470900005cdfcccc406a0000000000ab10001eec000abf00012205d20000000000000000620bc900009cc000028739d00000000000000000002f601400000003c34000000000397571e58eb0e00000000005da0000a0c000000000197a0002fd04c600092800010383d000019f0181ada0000000000cb400000032680000004a68000000a4a00036585f600000000004cc86e62a0000e5b0003d300019ee0005c223563980910000001bac37f6918aa79e0000000000000024f0a0871c04aa0115a000000000002200000000000003b6c00000032594fcf3ae51037d5689fa0002df800013d64f0000c841240000000000a72a230000000a5200024280009d700000012989e605b0001f64eb45e7000000000034900000000000000000aefa52ad30002d1000034f69e1c31b880b649106690884796ce8000000c5500002b61fc3bf00000000000ac0000000000000000000000000043d80000006fc800000149a0000002d657ccd452dc0a320009248000a6178c0000002da8000000469b0d40004f1b37977596e1d94e433c9d88e5659800006c00000000001aa000000021740000000000000eb028f000000000000000000000000000000000dac0000fc800000043d00000000007570000000000c9c0d6b8987b2000000226000000000031c800000049780006ee00052f82aaed253b0000000cf40002a5afc50fee230000001a3cd0148a0001db80000000000000000761b0a5ab4396605800000000051
  | 39 => 0x59000000000000000000000000000000563984b7391b92fa2b900028006d400000000000002d0800031800000069ea3ba18a00000029a17d420c154800167c4e369c0000070dea000000000000010d81540000000002b3000000070a80019f2000000000118c000000000000000000024900003ce800000153a000000000119100000000008880000002bfa7a0000000000000000000000000003d70001184000000000000000000070a39ec0009ec00000001ae000000112e000000000000000000000000000001f703c000081500000000000000004ca00000000000000000000000000000000000014f8000000a70000000000023a0000001546db6c31245800000000000003b600000000000000006c880009370c4d311a3844c63b51da5587bb6890000000bca3ff800177c0000000000000000000000134600000000007ec044000000000016a000000000000053000004da0003e22a0818c0000000002c5800000016d8000000000213a764000a8dbc080014d829a00017bc0000000000000a3f00000000000000004d00000000000000002de0c00000000000000000001f3c0007af00000007b82f84b4560d756c61000000000012b000000009a2c8416a10c000000000311d3e800009880000000000002ca42a04120000000000ccd216b61000000000000000000005fda2dc6dc00000cd6c0000b286bb2572e9200060380000000005a480000004340000000000000000187c75600062b859200037b24b37987aa000000000096c96f221000000000000000000000000001801d5c00000000000000000f780000000000003449222cf100019640000000000001b7600000000001450003de0ecd1c827500000000000000000000000e8f000000000000063cb76431ee3f00005dc6004710000001d8e00068607ac0004a2800000000000000000000000001f58000000000000000124100009b80000000000fac0000000007188000000000000000000000000017f80000006d5334800053a2fe80000000000da80000000000002c48000000000000000000046bc000b9b00061c80000000000000000000000000000044b0005b800016e80000003bfc0000000d9800160e7f265480000000001f080000009732900000a1e00033a800000026c0003c140000000000fb8000000793db00ded0000000000467a5713114b151000000000000000004f49b9000000017700000000000001abd1ce00000025f01d200000000a4000a9c00000019d0ea50000000000af200000006460000000000000000000000000000000000010c2c833dc38bc00000079800000000d4543125f5ce26000004e2718000410800000000000000000000000eb13d5b1ce8624d3a202a66d9c60013000078400000007b44aa1048000000ab431e03cec0425529b00008
  | 40 => 0x20c0000003290000000b4337728f49280004ade3a8e7200000034a0d7e00022d400000000015917649018a203d0001bc6df039f80009d67ab0003c10000b7b000000117200061ba11400000072a00009080da800000000000000000004940000000001524000000000000004c800000088e0003e90001d408146498000000000000112c0973730000000000000000266e00000007970a000000000000017440000000001cf21780000a46000bc02ac8000f7c0000000000000000000000000000000000008b92366d018790d29bf000004c0006ea000000171800019d263928e000151401c000a0200000000000000002234000b8880013cf5f800044d8000000000000000000038af450778000d590002d58a4400013d80009c79d2cb5b46538f000039c00000000000032ccf8245800000000000000141d712920000000000000b052340cd4000000000195400000017681ba00000000000000000000000000000cdb1a8616cc250000000000000d15000000000000053a800000000022299800000000000000938000000184c00000000000000000000000000000000732000000000000000000009410e1c000000000000000000000000000000000004e28000000000295575c0000000000e1800000000000000000000000000c7c00000000000000003af000078a00040e8000000a1c0000b5000038b000385800000000000011fa7a946f19857e60660a486c8046c3e0002448000000000080e000a0c00025480000000000000000000000000000000031c2e9ca12bf200000000000000000000000c8f76f9428e7093580030c0000000000018400000000034d4000ec200000000000002bb914c00063f00035fc0000004bb00000000004a2000182acfb0000d6400000000000005ba000000294c000a5c00000000004868000001171000000000136000000000000000000000000000206000000048400000000012bcb4600000013330000000000000000000247c000535000000000057f0000000ef00000fb10a4000000013000118a5de000017000097e3ba0000ef4ee84eb33bcfd6680000228d74a0000002570c0fda90000001c440000001b2c0003f88000000000000000000000000000000000000000000000000601000000000000000000000001e580000000002b60000344b8acf332a00013fce324ccb9d0284c0800000000000001868d9d4dc0000000000000000738b4f8a2900000000007240000000000286000483007d234000000000000028a800000177e0003fc02c400000000000013d4000000000000048a1270f08b2cd34000000124b0000000001646000000000000000000000000001892ea80000007e20000000000e8c26e000000000000029cc00045100000000006c100000000000002a48000a3eb660
  | 41 => 0x2f5000000000000000000000000000002bad70a00013f80011d600000007118c00006220000000000000000000000074c95b00000000000000aa2000634800000000000000000000000000000e12000000140ca2621e00039540000003d1000000000068700000000003f800000000000000001cc200000000000000ef000000000041a8000000000000000000000000000000000000000000000128efe000000000089e000000000092045780004e293a00000000000000000001da28634f780005120004e98000a2800000000000000005cd0000000000000000074db2f00000000000000000000000000000000000000059cbaa5462000000181c714000000000000000000000000000000000000000853000000000000e000000000000000000000000000c700000001b0000386c0006c467d0000d300000002144000000369000000000000000000000004199e00d2070537fa6743c10000001181ae200000008f0b760002868a1831a5e110e9822d1a0000000000bd16250000000d620006a1800000000005820bd1a2000000000000000000000000000000000000000f1200000000000001650000e5c4a966b00000000000001bf400000012e0001962d7800000000000001fe8001d940004dd0000000000153ed5c80a3c7000094c0000000000000f58000000184400012300000011a400044b00014288f6791c000000d1600000000000000000000000c3a00030b8000c1f00003d8385000000000000000000003d400000066f33840000000001a7c000000000203400000071e12d4000c896398a5c000000000000121e00000023d200000000000000000000000bf4d9a0000000f44ea4c7b0000001e2500036f8000000000000371539a74a0000000000000000293000000002f0001a642af00038690b200044900707786786a38000000e1e0000000000aea80000000000000f7400000000000000000000003a4000000000000000011f80000000000000ebb00000000000002108000f66000320800000000000000000009712e094205a00000000001d0600000003081800006e109140760000000000000000000153c0000000000000000000000000000001000000000004e718c0001e2b6ad0a280000490000002bea00000000000000000000000000a32000000000000000000016c9e0605f00020ac000842000000000084f0001c91ad42882ef6240b4000000031300000000000000b0c0005050c9000000000007d40000000000dc00000000420000000000000000000000000000000000000001278000cdf000000107e71c3e50a91000cd47878000000b3d0000000ac48700000000f6775946617a40005b40003c019760000002dac0000000002d28000d890000000000000000000000005a00018bc0007ce0440b26
  | 42 => 0x95110000002fe10642c63a6c00021c61a2c46ea40000003a0800000000000039486d60b6800000016e4e80001cc800066a6ff3bc82e40002630001bf6d5f363800000000000000012360003d889b800000000008c80001ce0000000000935000000000000000000000005d03042a7800000061119e4000c7c10d77b0d956d900000000009f7000000000011e000000000000000009400000000003a740000006e8800102417a000000032e00002bd5b400000052215180000005fa8734000c10000000000000000011518ca000000000000025f000280c0005600003c58d2a00000000000008e000000007f000000000000002d8000000000000070ca150414206945eecc000000000000000000000000008ae0000af95580002bd72716a0000b24000000000000021b00000000005ae80016820005eebc370bebad0000000b940000000000000000000000000038500000000000005cd800000000037a288000000000000000006cc000000000000000000001ce00049f306022df1bca3c0000000000000000000000000000000032555685ac66800005f8000000000000000000000039026495c200016e0000b7b0000000196000000236800000065b0000000000000000000000000000000000000001eb7694000000185800021a00000011a8000c3b00009f40000006d78000000f2f0158000b0a00027d988000042400000000000000003c4c00000000011940003e800016a40000e4e929d0c88b0000000000f640005db80000002cf0000000000000000000000000000000001d06745f6000195854d80000013800000001a020000000000000000e35000000000001880033740000000000000000000000000000000000030300000005ca00000000006f8800000000029680004ff0001c78fe800000000000000000000000000000aed3a9ad8000000000000000002ac000107c000915a195e200000000003ba40003760000c109930006dd000000000051300000000000000000000d2b000000000000031a8a1c0003ad1b0b29c00000000000000002fa18c8000348744000000052c76c000355000024c0000000000943000000000054f8c580000000000001d9800000000000000000000000000000000000000000000000000000000000000001e1c00000004f0000a9a0001f6c324d58256c5640004da5c38bc40000003e1877c000a7a00000000000000000001e40cee318b93c2fc00000000000002e10000001bca000000000000000000000000000000000000000ee0486d65c00000000000000000000000000000af400000000000005771a680009850000001970000000000040f5d86ae05f07304984780000000000000000000031c00034213ce3c84bfd68c46b9b254282760004260e018100007a8000209c00000002cc91c000000
  | 43 => 0x9000000162e0005cb800000000000017d47e6a970003728000e8500000003cd0006cf800000030100007f600000020500000002120002ed800005233400000000005650000db88e600000000007ba4fc35b0cec0000000000dd000000023d00000004cdb1a00000000000000000e940000000000e39000000000000000000000000000000fd363c00028384d00c1501257044b8d65700000000000000000157db6242fa1d00001926a500000000006a7601c000000000552241a55f65800005551003652d291ac00000017809200000000000000000000000149c0000001e94000000000777800000000000000014cd8be38d0001cb80000000bb028177274ba47800006c2fe000000000000000000000000002299d80000000016e6562e34ce0376f7210723931d99445a611080013f60000000e008ea0000000001a1e00074b10b13b441e0289cd50584f20000000ad207f000000000000000000000000000000000000000000000000087900000006aa000000000131a1160000001386e5024da21400000000000000001d5000129eb38000000000000071e0000cb18c811923bc0000000000000000000000000371945ccab000000061081a010afaddeea4000000000000000000000000000000000067051d00038180000005971df0000e924b487486827870270000000274000000135232600000000000000001438ec80000000001cfa00000000006ba7e86fb83902144c58000fc40000000000ba000000000000000000000000eb82b0000163800000000078b800108c0ee00013f1527f284012e740000000000000000a590001660000000000000000000014e40000000000000000000000000000000000000000000005905e7800000000047d80000e02a4800360517fafe373000044a00025d94843e100028a8001a54df54ad8001aca2240000000000d8300000012d0000000000000000000000000000000000001bd2c040000000c4600023f00000000000000000000ecd000000000000000003e000000000000009ae04f2f71280d04d860933780c1c0000000c6dd58bde29b92f816682a0000000000d1a0000001bf2ad0000000100c0006bb8001d080004dd800000000000000000000000000000000000000373c3e4000357c0008a000000000000007fc0000000000000000000045f118241dae00000000002faa3bddce00016900000000001ffc0000000000000000000544800000023980000000000000000000000a990000000d6a686689840c0000000000000c420000000c24aa6000000000000021900000000000000001b8c8621f380000006ac4c5000075600000000000005a27460000001d2044a80028b4000000000000000072c800000000000034a2275a940000760000000000198250e0004080000001452000511351
  | 44 => 0x99243000302c4c80f6abd00000011d972a0000000000a431a1b9f81c697f000000000000000024c20000000000000000000000000091a00000000000000000000f340001840002c7000000017580000000000000f2a00000000000000001158001e4c0000003a6978c000e5f0000c5d81c00011c93c05166148001a6c00000013440000000000000415c7a3b4187babcf1e00000000017240002fc000000000000000000000000000000000000000000000000000008a000083d000181a000eec00000000000000000000000000000000000000000000000002a227704ba0c40003fb800085428f800000199ed92372a2a054a000000038f1ea000000000000000000000014d67373550000000bee55c0707182000000345d5529b08000000000000000000000000020a0000000000000011c00000000000000000000000000000000000000000055c0002d2122a00024191300000006f5950c00000000006451601aa00010640003a8092000152000000000000002c249e80000008580000000e8707200000ef703e10000399c00000000000002ac62800000000000004868000a300005a0000000092d800000000000000000000000003bc8000000a7b684800021900056c000193679ae2500000005fb00000000004bf000000000000004680000000005f78000000d9401622699ec7070000000000000465299000a8e9000353cd56233719ac19c7603e48e861c0000ce0000000000081396125c9a7000000000013000000020e1a5cf02000000000027000000000000003db00000000000002040ec0000665ade8000000000000000030305280002e0000000274e5670006619824000b5e43200000007fa4fb386000090100033a429e2beb7d00017c80000003c5400000000000000000000000d8800034c00000000000000000000000041709800195000064bb8a00000001cd00000000000000001a900005ac295000000027f000000000005e857600081500000015ccce000000004c2000000082d884d56324336140800062e885445413b0000000000000000000128d1c480000000000007928000000895000240d6de1ff4242ab1740989a270e357a600000000000000000428001bc24ef8000e240000003366d949c500057c00aa00000000000000000001f800005f200000000000000000001025276166c5d369127e5457728aa90d60142563c7c00035c5f2a2e11b700071bb8b8000c862008000000ec651b2ee0000000070000000000000000000000002db0000000000000000056a71d2c6800193a00000000000000003ab0000000000000000000000000000000000000820000000151459a3b10ce000615800048600000024140000000e400013b80006d40a340004ec00000007af5ed8001a480002f6b7b120000000077590947d8e5
  | 45 => 0x218a60a001b80000002ef400000000000000000001ef00000000005ad00001b222a8001f900005f60000000000000000000000000000000000004220c500016dc0000003688000bce00038a40000001d640010d0977061c00000000000000000001c5000101c00000000000000003e61d79a58000000005000000000000000000000000000000000b020000000c8000000000000000000000000d760fa800000194600000000000006536909b4c000000000000000080700000000005c0000000000000034280000000000000000000000000000000000000000000000000000000d94000000000105c000000366c0000000dd80000003a350330b43c2000584cee94e8901800000000000000026f9e1800076f0001a769dd70929380003fb3610000000000000000167e12d000139e000000000000000000000000000000004fa8000000c0611c312d7b4987193ae000000000001708000000000000000000047bb20948423f00000009240001f2b06c00000000f0000000a4b50a80000000004b1400000000047f4001a98d33001267915a00000035f000000000000000000000000001758143800000000000004700000ab8f3122000000000000000000000005ba865565a00072f00000007c8233af4437e44d80000000001cfcb70000000eba00000000008040000001774000000000025e74080036f000000000000010680003e28000000000000000000000048800000002da00000000002cc63301f400000000000000002ef0000001ba67890d7000000000056e8000000000029c0000002cc8000000000ad9ba125504e611b00012a000037900000000000003a7b078000b52c188000000000000010141232d2a500000003958000afcfc65800000b3800000000000000000000001ff436e0000002c8891e00000023b80000000000000000000000313c00000000000000000000000000000000000018e00000000002d600000000000000000000000000000c900001bc4000000000000000000053480013aa04b000000000000000000001e20004ec16e89e8bfe2ca25641bc00000000000000003c30001535000000000000027e51d4000000ee6000000024b8d560d0d1000000000000000000000000000000000000163c00000000000000001f000037000000000000001b3859b35a2580ade5a200000011ad0005a8c000000000134800000000000000000000001dd80009ace7500036adad6b674c0868822a02a00000006ea0078000000000000000000000000000000000004770003aa827e00000039f000000000017d000000049a00000000000e34000000000000000000000000000012d40000000000000000000015000092b8000001e22aae0003c1d3083df4a88000000d041a30000a1f0000000000000000000000000000001e24
  | 46 => 0x45e8001e340004c434741d7000000000000000000000000000000000ab40000000000000000000000000000093907840019ae000198a430000ed32b0a861ddc92d000275c00048b0a90000e060000000d6c00000010080000000000000e8bda44ca800052a0000000001fec0000004c31e3529c106800097400000000000000003b0000000000021837800000000005620000eec00062d0001826000000000000000077897837c68a92e6861996ab083e58000000ea300000000007ad000000000000000000000000003fa00000009e868e36280007940002e7c00000038a000000000066880004ae000000000000000059095220000002e5a57e00002d00000000000003f00000bacad200000000006330000000000aea0000000000bc46a90ece33600034245500000000000000e020000000000c9400026c8001dba00039f000000000000000000000003e8a37400000011f000000200000000000000000c40000000482000257c000000510982c12a000725800000000000000002af0e10000000000000000389cc9a000000000000000000000017ce0000000000634000000000088f0000000000000a5821e00000000000000000000000000227d8280007540000cae0000000000000000000243800000000000000009304f11e0c00000000000000000f3385b0c4000e87000000028c0000000000000000000250a00012722f80000000c4000237e0000005d300000000000000000000f0933231dd79a92c766000000000000000000602c000000000002aac52bad8d086ef37c00000000000eb9efc000000000000000000029440009b6000758800000016c31d00000000000000001b720002788000000000000000000000000011ee0002128000000000dfc000341426ae9f00000018fc0000000001a0600000014453920ff00000000000000af0b72000000000000000000003b000000000000027b4000ee100000000000000d9e85d362adc7400e048e8e0b4d16aec7da0b9331abf47887175a72ef8bd4e6843ab1bc0000000002302000b0b800000188a4280f18000000440000000000000000000000007e67470001e44627408800034aebf00000000000000000001bec0000000000ba43820000c8110c000000000000029480023c600000061980000000000000000000000000000000000000000000000000000001dec0000000000a16111000000000066d00000000000730000000000000000000000000000000014ba00049759f19d8b420000bf80000003cc0000fba0000003be000000019480000008c954fafd026f67b5aa80007f20005e50000000000000000000000013e0231a0c0000000000000000000000000000000000000000000000000000000000000000080f0001b7400000045a25549e1a957101bf823e1
  | 47 => 0x3720000000000000000355400022b9eda30c000000000000000000000000000000003e4a13800000000015d80003b200000000004bc000000000000000000000000000bdae3400000000000000000000002a0521600000027c03c80000000cfc00000008929dc000eba8003724000000000000000000000034c000000000003c0000000000013a00000009504513fe0000001344000b634742d2715800031600000007b76b19068dbc000000000000099f77f74fc000000000148c00000017280000000000000000d2200050c8000000000335904000000000000000001ea6350000000000000000000000000000019c8000000000000000000013fc1baa0700000000000001540001c48000000000000071517500000000000fc00017a8000000005c0000000710000fa800000000000000000001c7c0004af0000000000000000000000000071f087000057411600000000001a109ac0000000000000000762000228000077e3eb9cf08f600000014e0000000000000100a00000000000000000000000000000000346c0000000001e540000000002c4400058874580000000000b18958000000000298400000000000000000b48000001d3600000006ac00000000000011ed0001f202580000000000000b3eb01000000000000000000011bd5c7101000045203a0000000de40000000001b100007640000560e2141d1d1d320e9e13cf4bd24200043c245d3ca3870000000000d4180000000000000000000000000000000000000020000000000005fe80000ae00077e0000000000000000000037d00000007fcdb535a7684000bb513282a0c8ed0b0000000abc0005b985200b200000000000000001b6000000000027026cf14200000000000000000000000000f1b0000000a98000000000101200000015ac00006f6fa37cd628a511af873c000bc941f00000000c70003b88000000000000187a1a614f400000000070e80000000000000000000000000000058300000029d8000000000000000094b000000000000073800018c6000000028dace000000003c5409b8000000000000000000d5326554297185790000000000000000000000030000c6200008c47860000000001e170000000000000b0d000000125537b8002ef00ca9a835ea8787c6385800000026c0000000000000ca100000000007c7000000000000000000000000000000000b67a6f44208f535c0003c931b4368aa700000015aa000000000000000052a834c9a8dde00033200000000000000000000000000000011a8000000000b520000000000000000000000000000038e08ec44300032612c1000000000000031200000000000000002abd41600041da36c000000000000000000000017cd730629075aec5c86b5f41100000000000000001b900000000000000e630000
  | 48 => 0xab15d8000000000000100200000000019c800000000000013c8000021000046d9d18002ca800000016cb33800000003480019d400000000011a0ece00000643f8bcb3f4a997d3841600000000000000000000000000000349000000003940000000000001ddc132000000000000000000000017380000000000000ab000023e800000000007b2aaa000000000000000073f8000000c01054400000000000000000009ca00000000002a08001bac0000000000000d4c00000000000000000000000000000000300c32686a00024b874c00047100009dde73000000000000000013100000000001384df68182f31508f0ab322439218cce00000000015160000000000cf98a7265394c0000006d680000004b0800000000011d0000000000000000000000000044c9b3820f000051dd94f34b3b793800000000060b00000000005d8089c3d2000000354400000059a000000081c0000001db200000000000000000001fb48b8000000000000000059b00d050d00054b21b4ea839f7310000c6c0002958000000b7f000000000000000015a9dfa00000000000000001039da800000000000000000002409ab8000000000324400017960bad14000a3f14eb36876a8ef0d4ae2104c00000010ce00000000000000000000001b544bd0001180000a3c0003642aa000000000000000000006458000f2ed57000000000000000009e400000064f00000000000000000000000000000000000010b8964000b7c00000002d481e39687cd880c050000000000a1a00005620000d6000105c0000000000001dac00000000000003680000000592e5b6fe93384da000000000000000000020a40000000003770000e01704800000047a00000000000000000000f3828ec1b2ae4faabff5aac46893e3f400000009e545e50280007d20000000001e160000000000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40181c54a0f7558a4100607a1283dd5629040181d84a0f7558a4118e07e5283dd5629046381c94a0f7558a4100607d0683dd5629040181d41a0f7558a4118e07a0c43dd5629040103d9890b7558a4100507a4e42dd5629040181e8390b7558a4100607a0c42dd5629040181e83d037558a4100507a4f75d51629046341e93dd64358a4118c17a4e87d41629046305e93a1d5058a4100507a4f75501629050f03f985977454a4118e07e18859ce429046381f8798c5390a41005072557498f329040121e93e1172d954118e07a0c43dc3655046381c839cd40d9541006079d483503635040142d92a127694d410040f663429da535040103d981067694d410050724d409d8535040103e96e157290d410040fa60655ca435050d03c989d9549494139507259549ce525050f8368119774cc9410060710e87d95325040181c74a0f654c9410050b656649cb64cc46305c9361772593310040f66054dd954cc40103e98151765533143e0720c545d954cc40103f985d475592310040fa6054dd9548c40103e981517655231005a864860443644c40103f985d475d913178c87a4f855cb644c4016a19218110191310040f660549d9544c40103e98150765513118d0724d509d8434c46321e93e036510d3118e07a0c43dd5640c40181c7520d405903100507a4f751d1620c40181c7520d405883100705d037694d310c401c1540dda534c43100705ddb7494d310c401c17761d2534c43118e15e177654d310c49503d9815376553210040fa60545d954c840181c7520d4058f2118c87a4f855da43c840121c985416310f2118e07a0c43dd5648846341e93d9673d91211f5a825920443644840141e93dd675d91210040fe61751d7644840141e95dce73d912100507a56319cf644840121e93e1572d912118e0720e73543644840181c859cd30d912118e07a0c43dd5644840103d98152765512100607152839d9544840103e981507655121006079d683d93634840181e7520d40d8d2100d3825d2044163484038e0874811058d210052a640219da4348401ca1204427690d21006071d683d91434840141c935427610d2100728481109d8434840181e76a0f6510d2118e071da83d94434846321e93e036510d2118e07a0f70d94434846381e835c36510d2118d07a4e7614c434857d6189058c5310d21006071d683d91324840141e97d94434c9210040fe61751d5640846381c831cd50590210040fa6054dd9540840103e98151765502100487e6154152630846381c871d54098c21006071d483501630840121f985505458c210060721c75501630863d48d92a0d7610c210050724d505d8430840160d929cd6510c2118c8724d80594430846321c985426310c21004872615058c430840123b9855054580210058624d7510d600840168992a0c4358021
  | 1 => 0x318c47a4e87d416290c6311e93a1d5058a430060798c875416290c0142d9598672d864318c87a4f8558b6190c0182e72e1562d86430050e642755836190c0182d75a086598643006079d683d826190c6311c9361d509864318c87a4f855896190e4521c93219401954318d43a4e525ca5310c63516939457194c4318e0720c435c1659086381c831cd405964218d07a5e54dd6639086321e981077598e4200487660411d6639080121d95a077498e4218e0721f75552639089560e92dd55498e4290c87e6154d46639080141c976115098e4200586e4184542639086309c976154098e4218e0721c75502639080121d952054098e42006071d483501639080181c7421d5058e420060721c755016390a1742d969517294e4200703952635ca539080141e93e117694e4200507a4c845da539080142d922117694e420040fa60415da539080181d76a0f7494e4218f0398e72dd2539080112e981d17294e4200543a4c745ca5390863c0e631d17294e429051364a835d8539080141c935017614e4218c872614098c539097d21c985016314e42005076567198e4390a3fc0e735957290e4218c0fa63549cf655086341e93d5273d95420040f66354dc3655080103d98d5170d95420050e643545c3655086303e98150735954218d07a4c541cd655080103e9815370595420050e64054dc1655080103e98151705954243e0d204545c1655080181c5420d70595420040f663541da535086344e93d957294d4218c87a4f845da535080142e969d17294d428050765f6394e43508eb03d98d977454942006071d48350164cc80103d98152765533243e0da04549d954cc80103d9815076553320040fe61751d5648c80103e9815376552320040fa60545d9548c801a0f4061a53cca32006835018694f328c8016a19118120d91320040fe61751d7644ca1d21e93e1572d913200507a5c43d95644c80181c7520d40591320062c60570180644c80121c932195019132005a864460480644c80103d9815276551320040fa60541d9544c86341c935427690d3200507a5c43d95434c863c0f629da5310d320048766060194434c80141d971806510d320058564460194434c801a19801806510d32007065c060194434c80160c964806510d320078218120194434c801a0e86d9443cc932007061c06510d614c801a904320161185322540f66054dd9540c80103e98151765503218d13e5553dd9320c801c0e53d03764c8320070394d40dd9320c801c0e53dd8744c83200703ddb7590d320c86303e98d50735964118d07a4f541cd659040103e98d5370596410050e64354dc1659040103e98d51705964143c0fa5f84541659040103d98d537694e4118e1314d82dda539050f03c985957494e41006831098298c539046321c985026314e415f4872614058c5390
  | 2 => 0x382f5042bc53a310c0d0951608e9002b0e8be21432000d22c0df00000428d8000e216600168f81d8002340019c00001060010b000e92491000000000420c00029400000bb00000040bf0003b000e5128873709e03872290b60001231c000000036d051405d1bc430fc1780ecc02cc218c0015cb53a0522282138400000e70010f000c8206f100000246000000000000000000000000002334c88f0c111400204c01d49d1b09a288abadc373d4033061f1a03fbdc911641b00090000001e415a62d411c8f38cc30d89c37800000002a40a0008f8002d1b40000077064881f907400640348880000344000a06b2587c2b0b128c1e2b8e00e440ba8c6188080caff0f6fd2c8b8340001e80003c510304843422006d90009b3f0000004e20061158943c01c1fc014040527cfe104493c85532cca09411170c4000b92983517c741b8003750e00046150b4134d3018731a4f9060003e8240100720c00000000000005ce43b8fb198ab2e8c9238c5280000a829074a8000cf1e097000274084b1c07b210132a85b3acda13ad72242e22c332f00035903000898008b800b30001280093098f4054ed30a2c3cc0000014000821107d194a10002300000000ec0000029cce0bcf6232712b50908053354864206a13ce60000918000000ef0584c2601a000000f80031600264310005e0f4000480400000481402000380c06000702800040381c0634000004000090041c04008280c01000140a06000001208060301c000380028020001000010001c020b010200801028102400000040200000001606020940a150780008010001c0003000101c0f050381c3a028144802070080103e981517218d540050b254425c8635506303e981537018d540040fa60545c06355001a0c546083018d5400685151810c0635506303e9815273d89540040f66054dc3625500103d9815170d895400507a58549ce625500141e96151739895400507a58549ce615500141e9615173985540050ba48545cb6590c6344e9394972d96430060715283dc36590c0103d9815170d96430050e640545c36590c0103e98d5370596430050e64354dc16590c0103e98d5170596430040fa5f845416590cfd03c985957494e430040f66242dd56290c6305e93a1d5058a430050ba4a655cb6590c6350e9394972d96430040f662655c36590c014399099570d964300607e1a735436590c0103e9819770596430050e64065dc16590c0103e98195705964318d43a4e525ca5390c0122d95a076298a430040f66062dd56290c0141e9318b7558a430060ba0b751956290c0181c75a0f6058a4
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x264500007300000038011840318c03946cc0a8b86c4aa0c640ea3a4a655cb6590c6380731d303a2e529c8431903a8e969d17294d4200642322c00c03288699003411915c060194434c801700d08c0900ca21a6431807ea68390b7558a41
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x5
  | 3 => 0x2
  | 4 => 0x3
  | 5 => 0x209
  | 6 => 0x20d
  | 7 => 0xb09
  | 8 => 0xb0d
  | 9 => 0x1409
  | 10 => 0x140d
  | 11 => 0x1549
  | 12 => 0x154d
  | 13 => 0x249
  | 14 => 0x24d
  | 15 => 0x16c9
  | 16 => 0xb49
  | 17 => 0xb4d
  | 18 => 0x1449
  | 19 => 0x144d
  | 20 => 0x16cd
  | 21 => 0xb89
  | 22 => 0xb8e
  | 23 => 0x6
  | 24 => 0x1489
  | 25 => 0x148e
  | 26 => 0x3c9
  | 27 => 0x3cd
  | 28 => 0x1709
  | 29 => 0xcc9
  | 30 => 0xccd
  | 31 => 0x15c9
  | 32 => 0x15cd
  | 33 => 0x170d
  | 34 => 0xd09
  | 35 => 0xd0e
  | 36 => 0x1609
  | 37 => 0x160e
  | 38 => 0x589
  | 39 => 0x58e
  | 40 => 0x1789
  | 41 => 0xe89
  | 42 => 0xe8e
  | 43 => 0x178e
  | 44 => 0x1049
  | 45 => 0x58211
  | 46 => 0x58a
  | 47 => 0x20591
  | 48 => 0x58b
  | 49 => 0x4
  | 50 => 0x178a
  | 51 => 0x20e
  | 52 => 0x178211
  | 53 => 0x21791
  | 54 => 0x178b
  | 55 => 0xb0e
  | 56 => 0x58b11
  | 57 => 0xb0591
  | 58 => 0xb1791
  | 59 => 0x178b11
  | 60 => 0x28b
  | 61 => 0x40a
  | 62 => 0x160a
  | 63 => 0x148b
  | 64 => 0x59411
  | 65 => 0x140591
  | 66 => 0x140e
  | 67 => 0x179411
  | 68 => 0x141791
  | 69 => 0x154e
  | 70 => 0x59551
  | 71 => 0x154591
  | 72 => 0x179551
  | 73 => 0x155791
  | 74 => 0x104b
  | 75 => 0xb4251
  | 76 => 0xb56d1
  | 77 => 0xcd6d1
  | 78 => 0x1716d1
  | 79 => 0x24e
  | 80 => 0x58251
  | 81 => 0x24591
  | 82 => 0x178251
  | 83 => 0x25791
  | 84 => 0x16cb51
  | 85 => 0xb4e
  | 86 => 0xb5711
  | 87 => 0xccb51
  | 88 => 0xb4cd1
  | 89 => 0x170b51
  | 90 => 0x58b51
  | 91 => 0xb4591
  | 92 => 0x58b56
  | 93 => 0xb5791
  | 94 => 0x178b51
  | 95 => 0x16d451
  | 96 => 0x1456d1
  | 97 => 0x144e
  | 98 => 0x59451
  | 99 => 0x144591
  | 100 => 0x179451
  | 101 => 0x145791
  | 102 => 0x16ce
  | 103 => 0x16ccd1
  | 104 => 0x16d711
  | 105 => 0x596d1
  | 106 => 0x16c591
  | 107 => 0x596d6
  | 108 => 0x1796d1
  | 109 => 0x16d791
  | 110 => 0xbcd
  | 111 => 0x3ce
  | 112 => 0xcce
  | 113 => 0x15ce
  | 114 => 0x170e
  | 115 => 0xd0b91
  | 116 => 0xb8d11
  | 117 => 0xd4d
  | 118 => 0x178b91
  | 119 => 0xb9791
  | 120 => 0x5cb91
  | 121 => 0x5cd
  | 122 => 0x5c9
  | 123 => 0xb85d1
  | 124 => 0x5ca
  | 125 => 0x5cb
  | 126 => 0x17cd
  | 127 => 0x17cb91
  | 128 => 0x17c9
  | 129 => 0xb97d1
  | 130 => 0x17ca
  | 131 => 0x17cb
  | 132 => 0x104b91
  | 133 => 0xb9051
  | 134 => 0x2cd
  | 135 => 0x74a
  | 136 => 0x14cd
  | 137 => 0x19cd
  | 138 => 0x194a
  | 139 => 0x161491
  | 140 => 0x149611
  | 141 => 0x179491
  | 142 => 0x149791
  | 143 => 0x5d491
  | 144 => 0x1485d1
  | 145 => 0x17d491
  | 146 => 0x1497d1
  | 147 => 0xcc3d1
  | 148 => 0xcd711
  | 149 => 0x583d1
  | 150 => 0x3c591
  | 151 => 0x1783d1
  | 152 => 0x3d791
  | 153 => 0x170cd1
  | 154 => 0x170cd5
  | 155 => 0x58cd1
  | 156 => 0xcc591
  | 157 => 0x58cd6
  | 158 => 0xcd791
  | 159 => 0x178cd1
  | 160 => 0x178cd6
  | 161 => 0x1715d1
  | 162 => 0x15d711
  | 163 => 0x595d1
  | 164 => 0x15c591
  | 165 => 0x1795d1
  | 166 => 0x15d791
  | 167 => 0x59711
  | 168 => 0x170591
  | 169 => 0x59716
  | 170 => 0x179711
  | 171 => 0x171791
  | 172 => 0x179716
  | 173 => 0x178d11
  | 174 => 0xd1791
  | 175 => 0x5cd11
  | 176 => 0xd05d1
  | 177 => 0x17cd11
  | 178 => 0xd17d1
  | 179 => 0x1a0d
  | 180 => 0x164d
  | 181 => 0x194b
  | 182 => 0x179611
  | 183 => 0x161791
  | 184 => 0x5d611
  | 185 => 0x1605d1
  | 186 => 0x17d611
  | 187 => 0x1617d1
  | 188 => 0x105611
  | 189 => 0x161051
  | 190 => 0x5c591
  | 191 => 0xec591
  | 192 => 0xecd
  | 193 => 0x58ed1
  | 194 => 0x1a4d
  | 195 => 0x17c591
  | 196 => 0x597d1
  | 197 => 0x178e91
  | 198 => 0xe9791
  | 199 => 0x17ce91
  | 200 => 0xe97d1
  | 201 => 0x17d791
  | 202 => 0x1797d1
  | 203 => 0x105791
  | 204 => 0x179051
  | 205 => 0x1a8a
  | 206 => 0x44d
  | 207 => 0x188e
  | 208 => 0x18ce
  | 209 => 0x216d1
  | 210 => 0x21711
  | 211 => 0x180a
  | 212 => 0xa0b
  | 213 => 0xa0a
  | 214 => 0x21891
  | 215 => 0x180b
  | 216 => 0xcc215
  | 217 => 0xa0e
  | 218 => 0x180e
  | 219 => 0x198a
  | 220 => 0xa4a
  | 221 => 0x14cb
  | 222 => 0x2cb
  | 223 => 0xa4d
  | 224 => 0x198d
  | 225 => 0xcd415
  | 226 => 0x17cb4259
  | 227 => 0xb4257d9
  | 228 => 0x5c58b59
  | 229 => 0x5cb4599
  | 230 => 0xb4596
  | 231 => 0x5cb55
  | 232 => 0x17d6d459
  | 233 => 0x5d6d5
  | 234 => 0xa4b
  | 235 => 0x198b
  | 236 => 0x140cd5
  | 237 => 0x14ccd5
  | 238 => 0x14d715
  | 239 => 0x171496
  | 240 => 0x164a
  | 241 => 0xb45d5
  | 242 => 0x16c5d5
  | 243 => 0xcd715
  | 244 => 0x178cc3d9
  | 245 => 0xcc3d799
  | 246 => 0x5970cd9
  | 247 => 0x58cd719
  | 248 => 0x170cc599
  | 249 => 0xcc596
  | 250 => 0x5c58cd9
  | 251 => 0x5ccc599
  | 252 => 0xcd796
  | 253 => 0x17c58cd9
  | 254 => 0x17ccc599
  | 255 => 0x58cd7d9
  | 256 => 0x17ccd5
  | 257 => 0x5ccd5
  | 258 => 0xa4cd5
  | 259 => 0x198cd5
  | 260 => 0x17d715d9
  | 261 => 0x170cd6
  | 262 => 0x171796
  | 263 => 0x17d715
  | 264 => 0x5d715
  | 265 => 0xa5715
  | 266 => 0x199715
  | 267 => 0xccd16
  | 268 => 0x1a0d55
  | 269 => 0x28e
  | 270 => 0xcc5d5
  | 271 => 0x1705d5
  | 272 => 0xcd616
  | 273 => 0xcd7d5
  | 274 => 0x1717d5
  | 275 => 0x2d715
  | 276 => 0x5d2d5
  | 277 => 0x1a57d5
  | 278 => 0x98cd5
  | 279 => 0x150cd5
  | 280 => 0x59796
  | 281 => 0x5d7d5
  | 282 => 0x188d16
  | 283 => 0xc5d5
  | 284 => 0x12c5d5
  | 285 => 0x17da55
  | 286 => 0x20cd5
  | 287 => 0xd4cd5
  | 288 => 0x160cd6
  | 289 => 0x1702d5
  | 290 => 0x5c0d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 1547
  | 6 => 5572
  | 5 => 3892
  | 4 => 273
  | 3 => 8
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
  | 8 => packedAt gbK8 (1398+((h/22+packedAt gbK8 (1222+(h % 22)*8) 8) % 170)*7) 7
  | 7 => packedAt gbK7 (65159+((h/660+packedAt gbK7 (57239+(h % 660)*12) 12) % 3163)*12) 12
  | 6 => packedAt gbK6 (297612+((h/2154+packedAt gbK6 (267456+(h % 2154)*14) 14) % 9383)*14) 14
  | 5 => packedAt gbK5 (250320+((h/1478+packedAt gbK5 (229628+(h % 1478)*14) 14) % 11408)*13) 13
  | 4 => packedAt gbK4 (20001+((h/99+packedAt gbK4 (19110+(h % 99)*9) 9) % 394)*10) 10
  | 3 => packedAt gbK3 (663+((h/3+packedAt gbK3 (648+(h % 3)*5) 5) % 22)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe0ff03fe07ffc1ffff80fff033d19e8cf3cf
  | 1 => 0x7ff0ffc0ff81ffe0e03ff03f0ccee67733d33
  | 2 => 0xf83ff0000fffe0fff003fffc0f0f307983ce3c
  | 3 => 0x3ffffff00000fffffc00000ff03f81fc0fc0
  | 4 => 0x3fffffffffff00000000000fffc001fff000
  | 5 => 0xffc0000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8a4022011202290012a080514011408a045045
  | 1 => 0x48505440488124204092a02a0448624312512
  | 2 => 0x502a5020895540b5a01254a8070a3051828a28
  | 3 => 0x403399aaa04100f9c95806082ba03b01d80f80
  | 4 => 0x863ceef3cfe79c1080601830cdffc001eff000
  | 5 => 0xe70000c301861821018060c30efffdfe000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36839
namespace PEqualNP.Outside.L_meta_36839
open PEqualNP.Outside.L_meta_36839.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 13 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 17 := bs2_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 60 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_160 : Interval s4Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 165 := (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 50 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 10 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 60 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_160 : Interval s5Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 165 := (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 50 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 8 := bgb_3_0
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
theorem bgb_4_256 : Interval gbAtlas 4 256 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 273 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256))))
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
theorem bgb_5_3872 : Interval gbAtlas 5 3872 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3892 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928))))) (concat (concat (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152))) (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664))) (concat (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792)) (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)))))) (concat (concat (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 bgb_5_2144))) (concat (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 bgb_5_2272)) (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 bgb_5_2400)))) (concat (concat (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496)) (concat (concat bgb_5_2528 bgb_5_2560) (concat bgb_5_2592 bgb_5_2624))) (concat (concat (concat bgb_5_2656 bgb_5_2688) (concat bgb_5_2720 bgb_5_2752)) (concat (concat bgb_5_2784 bgb_5_2816) (concat bgb_5_2848 bgb_5_2880))))) (concat (concat (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104))) (concat (concat (concat bgb_5_3136 bgb_5_3168) (concat bgb_5_3200 bgb_5_3232)) (concat (concat bgb_5_3264 bgb_5_3296) (concat bgb_5_3328 bgb_5_3360)))) (concat (concat (concat (concat bgb_5_3392 bgb_5_3424) (concat bgb_5_3456 bgb_5_3488)) (concat (concat bgb_5_3520 bgb_5_3552) (concat bgb_5_3584 bgb_5_3616))) (concat (concat (concat bgb_5_3648 bgb_5_3680) (concat bgb_5_3712 bgb_5_3744)) (concat (concat bgb_5_3776 bgb_5_3808) (concat bgb_5_3840 bgb_5_3872)))))))
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
theorem bgb_6_5568 : Interval gbAtlas 6 5568 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5572 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)))) (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152))) (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)))))) (concat (concat (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696)))) (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))))) (concat (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))) (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)))) (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))))))) (concat (concat (concat (concat (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912))) (concat (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008)) (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)))) (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264))) (concat (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360)) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456))))) (concat (concat (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616))) (concat (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712)) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)))) (concat (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968))) (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)))))) (concat (concat (concat (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320))) (concat (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)))) (concat (concat (concat bgb_6_4544 bgb_6_4576) (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672))) (concat (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)) (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864))))) (concat (concat (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024))) (concat (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120)) (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)))) (concat (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376))) (concat (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472)) (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568))))))))
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
theorem bgb_7_1536 : Interval gbAtlas 7 1536 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1547 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))))) (concat (concat (concat (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928))) (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))) (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))))))
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 44, 60),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8fee8eee8eee8eae8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 56 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276678376 * 2 ^ 32 + 4008241896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36839.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[4,5]⟩,⟨.or,[1,3]⟩,⟨.and,[2,7]⟩,⟨.and,[3,6]⟩,⟨.or,[0,1]⟩,⟨.or,[2,10]⟩,⟨.or,[0,9]⟩,⟨.and,[8,13]⟩,⟨.and,[11,12]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4008241896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4008241896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36839

open PEqualNP.Outside.L_meta_36839 in
theorem PEqualNP.Outside.L_meta_36839 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4008241896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4008241896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
