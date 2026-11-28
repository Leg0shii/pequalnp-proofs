import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36292.Model
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


end PEqualNP.Outside.L_meta_36292.Model

namespace PEqualNP.Outside.L_meta_36292
open PEqualNP.Outside.L_meta_36292.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36292

namespace PEqualNP.Outside.L_meta_36292
open PEqualNP.Outside.L_meta_36292.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x20bf43bd43
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (34+((h/1+packedAt s0K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x80ffffc0fffffe07ffffc0fffe07fffcf8fe3f
  | 2 => 0xff03ffff01fc0ff83e0fff07fff83e034f1fcc
  | 3 => 0xfffc0ffffe000fffc00ffff83fffc0038fe3f0
  | 4 => 0xffffffffffffff000003ffffffff003ff
  | 5 => 0xfffff00000000fffffffffffc0000003fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xa6082046244842014a12c42946214a98186e15
  | 2 => 0xa58c48a1c915658168555259aa92c294b16cc
  | 3 => 0x14316914483a6aaac109a6b12d3588528da370
  | 4 => 0x58a28e2091230d34a5a0308431c63163e001aa
  | 5 => 0x60c30c38e1c38dc739ce38c601842183f6d800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36292
namespace PEqualNP.Outside.L_meta_36292
open PEqualNP.Outside.L_meta_36292.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0xf1a08d9924010005001100562d788283800922291a7544c3a5300ca843c192103a8402c029801a380001f1800bad00582ae5254078010008020205c045180ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x31800706e33800003641800482538874124e0503c785a2112820482b8002433341808e21001c000402800068770000000752a9e4e80435104540017130ac842f1a400061f974e6302780038182916c34113e8c8061b149441600000987c8141014b22f1014c9a7639198264400a14f4780010cc2373d924d67c11038286c0005c508011858de3922820000025800fe1f1689c560c039b43c540a800000200034323a320b0000018960be3d001186a0032988765c3f00448000008000c1000001c08145000140c000000000c8c089400002400081c0080143c6408048804180404827ca5a1cf947439ea86873d5490f3ea6a1cf149439e28a873f5050e7ca821cf54e429f294853e5190a7aa1215794c42aea98859e5310a7aa6216754c428ea98853e5210b5ca4214f944429ea80853e54cca7aa9996750f32bb28e657551cca7ea9194f152329faa2653c544cb3a86994f950329eaa0653d539067ca520cf946419ea84835e53106baa620e794c419ea98839d531063aa620cf948419f28883b6511067aa020cf953319eaa6639d43cc6dca598db54b319faa4633c548c67ea898cf15131cea1a633e540c67aa818cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cfd51219e2a2433f5408678a810f948421af29e815d53d033ca7a04f54f40cea9e811d53d027ca5a04f947409eaa4813f5350278a4a04f14540dda82813e541027ca9984f553309f2a4613d548c33a87184f951309eaa2613e540c27aa8186750c30b7290616d520c2eca2185d544309faa6413c54c827ca9104f552209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2cb843946a2300008028018420026016c92a9c2b001e0060020241142000090028758e5190a1f6354242c550d51cca3661d523287195434ca8c6250d328758e529061f6354241c350d52cc62e62d523187195434c6946150d318758c544861d63150218e580540861d63149408758c515021d63951308b189544c2346155130c350d520c31543544308758c54c821d63952208758c54c421d6395210
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
  | 4 => packedAt s1K4 (3970+((h/44+packedAt s1K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s1K3 (1036+((h/8+packedAt s1K3 (988+(h % 8)*6) 6) % 35)*6) 6
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffff0ffffffff81ffff07ff07fffffe78f1ff
  | 2 => 0xf07fff03f07e1ffe1e0ff87ff878383fa73e93
  | 3 => 0xff83fffc007fe1ffe00fff87ff803fc1c7cf1c
  | 4 => 0x3ffffff8001fffff00007ffffc001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x800010208010000044120088008a0a10085025
  | 2 => 0x2519221924a430960a854853485090aca32692
  | 3 => 0x432a44486949032aa109950595012585458b18
  | 4 => 0x6a5388924c0d55cd33a0c446e6658109f00dc0
  | 5 => 0x8c630ee38e7199f1ddcee660c4460631fef000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaaaaa0faaafaa0faaaaaa0faaafaa0faaaaaa0faaafaa0faaaaaa0faaafaa0faaaaaa0faaafaa0faaaaaa0faaafaa0faaaaaa0faaafaa0faaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36292
namespace PEqualNP.Outside.L_meta_36292
open PEqualNP.Outside.L_meta_36292.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1111b420122e00004230aac000121c01000483000000000000009128a40300000031006879926a80183c010003e00e800000000000058004956954c701972ca06a758bc70c14020c08d000008806047024650003ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32ee32fd32ed32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x5ca102898ba0b1f27948370f8ec40762c00026160f000000a369d4c2562f83c94001c00000880ba2c68003609c740046a3c000000001067800000062f288f400000000000004b80000234a1f8120000001386a00000c6911a8b0e4000e194aa0000000009b06801460027248c43f4d16c0032370a8002d320905600000008a6803a1096330027ca01a2ba60f293210c0367b3e850eea214800007329074b8592d0f0d2465014c4285000000c9000039328c2f00018124323800673e000fe22189c48e0027a0008600a911127a2490ca86f000412c48000e4001100204e8821b0093a00269044a95041c10e8a3586080660c930500100810100000000018000860b028005068301008001808a000b158192038c018100008082078006018284078200818581008205800100024f94b439f28e873d50d0e7aa921db94a43b6a94879f5350e78a4a1cf145439fa82873e5410edca421db548439ea9c853e5290a7ca3214f54242af298855d5310b3ca6214f54c42cea98851d5310a7ca4216b948429f288853d5010a7ca9994f55332cea1e653f548ca78a9196b90a32d621465af548cb58a9195b54e32d7a1c65ad438ca7ea8994f15132cea1a65ae424cb5884996bd5132d62a265cf534cb5e86997390d32d6a1a65cd434cb1a86994f950329eaa0656e520cadca520db54a419ea9c833e529075ca520cb94a41d6a9483ae329075a6520cf946419ea84833d531067ca420eb8c841d6990833e511076ca220cf540419f2a6633d54cc6dca598db54b319faa4633c548c79a6518cfd51319e2a2633e540c67aa818db94831b6a9063cd320c6f4a018de540319f2a6433d54c86bca790d754f21d6216433e548867aa910cfd51219e2a243ac424867ea810cf150219ea9e813e52d035c65a06b4cb409f28e813d54902dea4a05b149409fa9a81af5250278a4a06b149409629281ae325035a64a04f14540dda82813e541027ca9984f55330b7296616d52cc39a65984f952309eaa4613e544c27aa898734c9309f2a0613d540c2dca4185b54830bb2886175510c27ea9904f153209f2a4413d548835885104fd51209e2a2413e540827aa8105794c20aea9841ac42082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xc19b84095b2262e942a3a000322e0d70048d01110c002a90000d0d3c7dd8c5600826145048e423c000000139b242c0006e000002a61680004c0000e000355ee40002c016010000c88008c00438080118106040020800101160c00200010828b98a51d0e2c6254343c39895310b0d53948428d987548ca8d63d5232a9987548ca8d631523287195434ca8d6490d32a3995434ca8c6550d32a3185434ca8f6050d329358e529061d6394a41a358e529070e6394a418b58e529070d6394a418358e529062f658ca418bd95329070d534c8418b189501062e62d5231c3d51328c62e62d5131c3551320c7493254031a358c42c870d5310b21a358c424862e62d50218758c54086396015021c354d32d022e62947409358c525021d6314940a358c525030e63149408b58c525030d63149408358c525022c658c9408b195325030d544cb308b189548c22c62551308d185544c30d544c9308758c54c828d6310a208b594420828d6310820c354c420832442544208b98b54c422c6255210
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x1000409cc02800000d00024401682b8cc4a9885219c66550d3281ae6312a020c0d7398b5408606b9cc528e81411c5544c93081aeca988410505731095108206b9cc5aa621035cc6255210
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (912+((h/16+packedAt s2K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s2K4 (4895+((h/55+packedAt s2K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s2K3 (2420+((h/20+packedAt s2K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s2K2 (505+((h/3+packedAt s2K2 (490+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf0fffc3ff87fffc1fc3fc3fe1fc1fffe98f27f
  | 1 => 0xff07ffc1ff87c3fe1fc3fc3fe1fe1c1f673d93
  | 3 => 0xfff87ffe0007fc7fe003ffc7fe001fe187ce1c
  | 4 => 0x7ffffff8007ffffc0007ffffe001f80fe0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x14000408408100004404804802408508085025
  | 1 => 0x20510884900a040a0841441220940854232492
  | 3 => 0x423351143554a0d6a2226a87540c52c5858e18
  | 4 => 0xaa462212440a96532a8220599294081d00b40
  | 5 => 0x8cc643b9c6673279df33b32110318319fef000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeee88eeeeaa88eeeeee88eeeeaa88eeeeee88eeeeaa88eeeeee88eeeeaa88eeeeee88eeeeaa88eeeeee88eeeeaa88eeeeee88eeeeaa88eeeeee88eeeeaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36292
namespace PEqualNP.Outside.L_meta_36292
open PEqualNP.Outside.L_meta_36292.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4d785320158d5400fae0e6141e008c011140078000000000000000000002c0001131345419700180004c100120000720527402d000000028848000494e0012592000000400606c0804e0058c00000000108286810000280002c000ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32ee32fd32ed32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x85281a8806019800000033800e08b1a17c000000124c64e16168c40500000000000000000000024ac77178e1140052000b8001d8a800001f800b0001708c348d00000204500000000049a45309526800829900000000000000162400000d800071a5020025910249e2c800000000284a49a08a1cbc0f24028561d3da7caa00001841086000002e0200000d00000000000000000009d2a0f91200000000c3d0010800844d86074043d22078000b000020c0180000a000064946d000006c301a974444606800380000000002000258fc1e289fce67d37998ea57480a52800000e46e003293d44820f9904a000a25c002100000000000000004c000000026460000053038a0e27c470006400000003631239d000001680000000009c001551800005b00000000000000006e09801067235a48ec000023d000021a70f200001e000000000200018000000000000001008100001040140404028000600008000a010100002020181800070000c0a02018100605000000000018000201008000400014f94b439f28e873d50d0e7aa921db94a43b6a94879f5350e78a4a1cf145439fa82873e5410edca421db548439ea9c853e5290a7ca3214f54242af298855d5310b3ca6214f54c42cea98851d5310a7ca4216b948429f288853d5010a7ca9994f55332cea1e653f548ca78a9196b90a32d621465af548cb58a9195b54e32d7a1c65ad438ca7ea8994f15132cea1a65ae424cb5884996bd5132d62a265cf534cb5e86997390d32d6a1a65cd434cb1a86994f950329eaa0656e520cadca520db54a419ea9c833e529075ca520cb94a41d6a9483ae329075a6520cf946419ea84833d531067ca420eb8c841d6990833e511076ca220cf540419f2a6633d54cc6dca598db54b319faa4633c548c79a6518cfd51319e2a2633e540c67aa818db94831b6a9063cd320c6f4a018de540319f2a6433d54c86bca790d754f21d6216433e548867aa910cfd51219e2a243ac424867ea810cf150219ea9e813e52d035c65a06b4cb409f28e813d54902dea4a05b149409fa9a81af5250278a4a06b149409629281ae325035a64a04f14540dda82813e541027ca9984f55330b7296616d52cc39a65984f952309eaa4613e544c27aa898734c9309f2a0613d540c2dca4185b54830bb2886175510c27ea9904f153209f2a4413d548835885104fd51209e2a2413e540827aa8105794c20aea9841ac42082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x75400182d1396601a00005c2806c0031236003ae10ecd312c246b840900001e0138054bc0022a10000744d68000016110060f816085490649928e14011996e79a9c060001456420400700041000000284021400004040008b98a51d0e2c6254343c39895310b0d53948428d987548ca8d63d5232a9987548ca8d631523287195434ca8d6490d32a3995434ca8c6550d32a3185434ca8f6050d329358e529061d6394a41a358e529070e6394a418b58e529070d6394a418358e529062f658ca418bd95329070d534c8418b189501062e62d5231c3d51328c62e62d5131c3551320c7493254031a358c42c870d5310b21a358c424862e62d50218758c54086396015021c354d32d022e62947409358c525021d6314940a358c525030e63149408b58c525030d63149408358c525022c658c9408b195325030d544cb308b189548c22c62551308d185544c30d544c9308758c54c828d6310a208b594420828d6310820c354c420832442544208b98b54c422c6255210
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x60214e030500000404940282b8cc4a9885219c66550d3281ae6312a020c0d7398b5408606b9cc528e81411c5544c93081aeca988410505731095108206b9cc5aa621035cc6255210
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => packedAt s3K5 (912+((h/16+packedAt s3K5 (800+(h % 16)*7) 7) % 88)*7) 7
  | 4 => packedAt s3K4 (4950+((h/55+packedAt s3K4 (4455+(h % 55)*9) 9) % 288)*9) 9
  | 3 => packedAt s3K3 (2420+((h/20+packedAt s3K3 (2280+(h % 20)*7) 7) % 80)*7) 7
  | 2 => packedAt s3K2 (502+((h/3+packedAt s3K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf0fffc3ff87fffc1fc3fc3fe1fc1fffe98f27f
  | 1 => 0xff07ffc1ff87c3fe1fc3fc3fe1fe1c1f673d93
  | 2 => 0xfff87ffe0007fc7fe003ffc7fe001fe187ce1c
  | 4 => 0x7ffffff8007ffffc0007ffffe001f80fe0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x14000408408100004404804802408508085025
  | 1 => 0x20510884900a040a0841441220940854232492
  | 2 => 0x423351143554a0d6a2226a87540c52c5858e18
  | 4 => 0xaa462212440a96532a8220599294081d00b40
  | 5 => 0x8cc643b9c6673279df33b32110318319fef000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeee8e8eeeea8a8eeeee8e8eeeea8a8eeeee8e8eeeea8a8eeeee8e8eeeea8a8eeeee8e8eeeea8a8eeeee8e8eeeea8a8eeeee8e8eeeea8a8eeeee8e8eeeea8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36292
namespace PEqualNP.Outside.L_meta_36292
open PEqualNP.Outside.L_meta_36292.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x7001a000000a0030a8f006ce80000089300480000aa4b0648001213c014102860000327c0014c00000000072000944800000027460058d0e1000300000084400017000000080000000010100020000007ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xa81bf525035ea4a06f94940dea9281bc5250358a4a06fcc940df19281bd325037864a06fd4540dba8a81be515037aa2a06f14540da28a81bf315037c62a06f4c540de18a81bf215037c42a06f48540de10a81bf5050376a0a05f950409f2a0817e53102faa6205f94840bea90817e51102faa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc3be6398774c730dfa0661bd40cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa71877d0e30ee21c617e528c2faa5185f94630bea8c617e508c37e81186f50230ef98461fb308c2fea8985f95130beaa2617c544c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c37e80986f50130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa88617e500c37e80186f50030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f719641ed32c82fca3905f54720f790e41ed21c837e81906f50320bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885105f94620bea8c417e508837e81106f50220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc64907b4c920bfa8a417c51483de42907b48520dfa0241bd40483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf29041ef42083d884105f94420fb288417651082faa2107d54420baa88417e500837e80106f50020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c43ec43887d48710dfa0621bd40c42fea9085f95210df2a4213e54842faa9086f552109eaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e508437e81086f50210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec62887d4c510fb10a21f5214437e80886f50110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dd0410fa208217e500437e80086f50010fb88021fa10043ea20087e44010
  | 1 => 0xf540cafca8195f55032be2a0657e530cafca41977cc832f719065dd320cbda6419734c832bf28865f6510caeca2195f54432faa886575510cafca0195f54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83be43907788720df94a41f7294836e52906faa520fb54a41b6a9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331efa1e63dc43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631fba0c63f4418c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c7be8698f710d31bfa92637c524c7be6498f74c931fba0a63f4414c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a90637e510c7be6218fd8c431ee98863f5310c7aa6218df94031bea80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43ef42c87d88590fb8cb21f6996437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21bf28c43f741887e88310fd8c621fa98c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43ef42487d88490fb8c921f699243f741487e88290fd8c521fa98a43f721487dc4290dfd4121be282437f54086fca810df55021be2a0437f53086fca610f794c21af298437d53087baa610d754c21be298437e52086fca210fbc8421fb10843ed21087ea4210f948421bf280437d50086fca7a05f54f40dfa1e81be43d037a87a06f10f40bf296817d52d037e85a06f90b40dea1681bc42d02fca3a05f54740dfa0e81be41d037a83a06f10740dfa9e81be53d037aa7a06f14f40dfa9681be52d037aa5a06f14b40df99681be32d037a65a06f0cb40dfa8e81be51d037aa3a06f14740df98e81be31d037a63a06f0c740df90e81be21d037a43a06f08740beaa4813d54902fca7205f54e40bf294817d52902fca3205f54640bf28481bf40903f681205fd4d40efa9a815f53502f8a6a07714d40ae29a81bf435037c86a06f50d40de21a817f52503dea4a05bd4940be29281ec52502d8a4a06fd0940df21281bd425037884a05fd4540fba8a817751502f8a2a07d14540ba28a81bf415037c82a06f50540de20a81fb405037c80a06fd4d40cfa9a81be535037aa6a06f14d40ce29
  | 2 => 0xb31ae0b89d800000000e688b3c670c590bb586328c285e252958a1a771306f01a8fd1c02b0060a451a0c93eaa50303c47a27336400016051004001569131f856461081544000e40004b473c511511d00210a800000000000fa10e6bca482657018c2280054e8a8f7a9a4721a8b812f00069c8ca74412955210ef30c97d1e0000002b9241fb07c8846c9325b4a28c422f47e0a9041824fe3e0cb1b64f438c6893556624cffa0306c56c4b03c2728b0fc1ed326860c610e48a000001170001997100000000140042000000c490d00000127ab54945bc001d05c86b8208002940007a9ba59e2e0681751102940193a2e25b55d02d3ee80000152000b2caf88f48e0005380033c0540503004800030000280e0800a000180d8640c804030100080c010260300c0004c178140001402800010040580204804008000582c0400017024000440103c0300a050000000600800048040283c000080080a000020003a02800028b0268041481c0180400000008123b88207002030080900c0100000028008040481a0e8020000200002020040e804018060600a0482200008028020000001020000020800e018000000001000220180080002000040000f80400022018220300800004058280a802078020a800030100100000800000020a00a08814010300081e1f004040001081a2a0320502e108040a00801014008380180000004020000003201008068121e000050100d806030000083401002068000001a0300e090360b8000b00405810028100081a000080001e078100100a0085e02df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290fdca521db94a43bea9487ed5290edaa521df94643fb28c87765190efaa321fd54643baa8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e857e51d0afaa3a15f94342bea86857d5490afca7217794e42af29c857d5390bbaa7215754e42df21c85bc4390afca5216fd0a42f7a14857e5190beca3215d94642bea8c85f55190aeaa3215f94242bea84857f5350af8a6a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ee21e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cafca5197bd0a32f621465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a89977d0d32ee21a65ef424cbd884997bcc932ef192657f514caf8a2995fd4132be282657
  | 3 => 0xca184058001140010d0800865e46e1e6000628000950be000000524e0041460000005d9328d63204f16806b3be00169069000a605e2c45686610f8b722c0100011e15400000000562264f91ad1dc470e00e54280003680042455c1e8534024b57083719625cf61444f2b4c0000000000037a2d2143d8001b4202000c3800000000000003e83840000029649c0011a000474000002f8944a103819eb80759002fa000000343ce725281f609a7e49f04e000000b09a55aa42c000005848800002b248a64b60741080cc548250aa8ad4e886254000000c6000530489360009e0001d939c6c07c8005385a4000001e60011a89b0006cc7f19556c0013104c398000b515e2d6ac05b2d61b6afd4a8b9416304ba1f3504aa54a15335209d430460624115219a02e080000000ac934000f023e8c40011154236971aac0000011d94d000760e10003c4a146c2a0306000418004088b8648004920000015831a5711b20f0600013705a3384180026b03e1c0e0ac159c0011c1c711c4c16e1f11e465d5e000250a2c9e9a60f01ed20a0e43a3fc388b10468652e97e5be96cf804b1c49b5088754ec3914826f2e459062a4c13ca44a2a3401a9b0e98c41cca78e502f24c66c3f2923424c512a834c6910322975904e0460be3fc784970495ae67c361154f8a38642c712807533a8838c550eb9a319a004088163a42740a0580c4638bbab73004ac8384a198644a78282f09d56313f4c29981f93300081451800466aa03701c0a884cda81e000088e590c0000492a1a200040cd209a48c000109f50b6948a71221d2028c58000520010f0005365747d9125546fc282232c400039000452170de800000a3c0012c000650e880f24a8e90bad10000002c8df5b04602400019c9a5498ed204a1c6a10913e30033a27000888000002acaf8540241bc2e80017a000870002263c0a7c002d40002413f2890f258000000418354000131a66a8002ab0001f1661683d22342bacd28c8dd321ea1603a8490a657a06d6c9e50000e8f417b15e768238762428f48a2281ce2d455ac52909c91220755e648c795535048d272dd1404212ba0652c5cc0724b4bc9ec4109c012790dc1b115a94d5711038a101202b2186770509505b69652e1a04d401cef0bd37c019219ee2ce014301ac0d0774878dd0000000d165000000f58003fa31c001db5922fca3940000001420004c0b28ea941576568c08443566dd6f2101a41e83b85d2c60008da3241a86d180190fa1fd1f20a3885b844a020002152c17f2cc6641d8002400e4ea2a637661138a165723dc002680e613cfe2c01d8000ce9373722d0002a320a758001340007e9408
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x5548833461552208f993538823d64d4e208f990538823d6414e209d98453882756114e20cb550428825f63551209718d544826f62551209dd85544827461551208fd91534823c6454d209dd8553482746154d209d98453482756114d209b195324834c534c9209798c514825d6314520d9145214825e63d50209758f540827661d50209d587540823d6595020cb189540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d584530832d54d0820d354f420826d6510820d354c42082e96010820cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420d9d09510836442544208f992500823d64940208f597400831e53d0020c754f400833651d0020cd547400823f6550020c794d400831d5350020cd94540083355150020d354f200836551c80209bd95200834d5348020d954520083a940480209ed95200825e63d53109758f54c426e62d53109b58b54c423f6454f108f19153c426e6214f109b58853c423f6454b108f19152c425e6314b109758c52c4354534c710d914921c425f63552109718d548426f62552109b189548431f6355210c718d548432f6255210cb189548433761552108f993538423d64d4e108f990538423d6414e109b988538426d6214e108f993528423d64d4a108f990528423d6414a109798c528425d6314a10cd550418425f63551109718d544426f62551109b189544427761551108fd91534423c6454d109bd89534426c6254d109b988534426d6214d108fd91524423c645491097d8d524425c63549109798c524425d63149109d1953144354534c5109d195214436452485109798f540425d63d50109b98b540426d62d50108f596540433461550108fd81540423d60550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d984520433554d0410d554f410436552d04109d59441043555310410d954841042f160104108f992500423d64940108f597400431e53d0010c754f400432e52d0010cb54b400423f6550010c794d400431d5350010cb949400432d5250010d554f100436552c40109e59610042776544010d554d10043655244010ec501100427b6544010
  | 1 => 0x3545314540d9d4851503645214540cd90c51503344314540cd90851503344214540cd147415029e6390540a758e415031c5390540ab98a41502ad6290540cb14a415031c5310540cb14841503375110540a798e53502ae6294d40ab58a53502b66194d40ad58653502b96094d40abd8953502ac6254d40add8553502b46154d40aed81535029e6514d40c7994535038f53d4940e314f525029e6394940a758e525031c5394940ab98a52502b66194940ad58652502b96094940a7d8d525029c6354940add8552502b46154940aed81525031c5314940ab994525032e6514940e3d4c525032e5314940cb14c525038c5314940c314c525023f654c9408f195325038d320c940ad98432502b5610c940ae98032502b9600c940e5d4f515039453d4540e9d4b51503a452d4540a798e515029d6394540c714e51502ae6294540ab58a515032c5294540ad98651502b96094540a7d8d515029c6354540abd8951502ac6254540aed81515031c5314540cb14851502b66514540cd99451503975314540cd94c51503345314540e514c51503145314540e9d4851503365214540cd14851503a45214540c9148515023f654c5408f19531502ae620c540ab5883150395310c540ae98031502b9600c5408fd95215023c6548540a798c215029d6308540e948421502ba6008540ae580215031f53d4140c714f505032f52d4140cb14b505033751d4140cd147505039b53d4140e614f50503ab52d4140ea14b50503b351d4140ec147505023f65500409ed95401033a54500409b98b54cc26d62d53309d98754cc27561d53308fd9152cc23c6454b308fd9151cc23c64547309bd89548c26c62552309dd85548c2746155230c7d8d548c32f6255230cb189548c3376155230cd185548c31d5410e3097d8d544c26f62551309b189544c27761551309d185544c27661149309d584524c34c524c9309b988514c26d6214530d5145314c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30b6580430c32e5494830cb552520c32e5454830cb551520c34f4354830d310d520c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c3574354430d510d510c23e64940308f592500c23d65d0030cb94b400c32d52d0030cd947400c33551d00308fd95400c32e5250030cb549400c3365150030cd545400c34d52cc030d5547300c25f654c030d3549300c355514c030e6501300c27b654c0309798f54c825d63d53209d98754c827561d53208fd9153c823c6454f209d98453c82756114f20d314d32c823f64547208f19151c825f63552209718d548827761552209d185548831f6355220c718d548832f6255220cdd8
  | 2 => 0x614c9319d997414c6d663d0531cdd50414c79443105318f990504c63d64141319b988504c66d62141319798f540c66e62d50319b58b540c67661d50319b988540c66d62150319e980540c67960150318fd91520c63c6454831cbd91520c72c6454831d354b310c6d5638c431d954a310c65f654c431d3549310c677654c431d9549310c6d7654c431d5d95310c797644c431e5191310c756544c431d5151310c7c6524c431d5549310c7c5524c431d1549310c63e64940318f592500c75531540319798f54c865d63d53218f99353c863d64d4f21ab19132c874c534cb218f99250c863d64943219798f548865d63d52218f993538863d64d4e21ad1913188754534c6218f992508863d64942219798f544865d63d5121c798f544871d63d5121cb58b544873561d51218f583544863e64951218f994544863d60151218f992534863d6494d218fd91534863c6454d219ed8153486786054d219b99742486e661d0921cbd50424872c548c9219b19532486ac644c921cb151324874c534c921b9185324867665d0521b998b41487375410521e91084148734548c5219d19531486b4644c521cd1513148754534c521b918931487c5324c5218f990504863d64141219798c504865d63141219798f540865d63d50219b98b540867661d50219798c540865d63150219e9805408679601502197596530863f6454c218f191530871f6454c21c7191530865e6314c219b98853086766114c21d354f21087555388421b958a210866f6548421d354d21086776548421d554d21086e76548421d9d9521087a76448421e919121087665448421d915121087675348421f194d21087655348421f154d210874553484218f992500863d6494021d9485500866e6294f409b58a53d02766194f409d58653d02ae6290f40ab58a43d02b66190f40ad58643d025e6394b409758e52d02766194b409d58652d029e6390b40a758e42d02b66190b40ad58642d025e63947409758e51d026e62947409b58a51d029e6390740a758e41d02ae6290740ab58a41d02b960d4f40ab98a53d02ad6294f40ad98653d02b56194f40ae58053d02b960d4b40a798e52d029d6394b40ad98652d02b56194b40ae58052d023f654cb408f19532d038d320cb40ad98432d02b5610cb40ae58351d029e6394740a758e51d02ae6294740ab58a51d02b960147408fd9531d023c654c740ab98831d02ad620c740e54c431d023f65487408f19521d029e6308740a758c21d03a52108740c714f43502ae6290d40ab58a43502b66190d40ad586435031f5310d40d3d4f525034c53d4940d3d4c525034c5314940cb90c525032c4314940cb14b425029e6390940a758e425031c5390940ad98642502b56190940c714c425032f5210940d5d4f515035453d4540d9d4b515036452d4540d5d4c515
  | 3 => 0x8010060000040180000000c000000020000100000600000800004004008000000000000600400800805000000010010000040080500a000000020060000200100000001803000004018000000000000000000c00000000000020000020000100000400c01000000004008030020180000000e0000080200001000000008000000030060080000100a000000000000100180300200c0180000000000802000000000020040000100200000402000002000000010020040080100a00000003002000000080020000080000200000801000000008010120080080100001c00000000004000000000100280600000000000002010000020020080100600800800000002000000000020000100000200000001000000000020000000080400a000010000000000080000800800000000000000040020000000200200005800006000000009d98652d0e756194b439b98a51d0e6d6294743d3d0d5290f665294643d954a5190f665254643d95495190f574354643b358a4310ed56190c438fd954310e5f6550c439d98653d0a756194f429798e51d0a5d6394742ad9864390b1d5310e42d354f4290b565394642d554e5190b364394642cd10e5190b565354642d554d5190b674254642ab58a4310ab66190c42b358e4210ae561908428fd954210a6f65508429d98754cca7561d53328f99250cca3d64943329d987548ca7561d52328f992508ca3d64942329d987544ca7561d5132c758f544cb2d62d5132cd987544cb3561d51328f583544ca3e64951328f994544ca3d601513297997434cace62d0d32c7d50434ca6e65d0932b398f424cb2f5410932e310c424ca3e64141328f590504ca7661141329d584504ca5e63d50329b98b540ca7661d50329d587540ca7661150329d584540ca7a60150329e580540cacd638c83297d95320ca6f654c832b3d95320cb4f654c832e3d91320cb8c644c832d3951320cb4c544c832f14ca510ca3f64544328f191510cb4d3254432f14c9510cb376454432cd191510cb573254432d98c9510cb553254432d94c9510cb4532544328f992500ca3d6494032d34c9500ca6e6294f419b58a53d065e6394b419758e52d06ae6290e41c754c439074e5394a41d354e529072e4394a41cb10e529074e5354a41d354d529069e6390a41c794e429071e5310a41cb548429075553d0641d954b41906ae6290c41ad586431069e6390841ad58642106d56390441b958a411063f65504419dd95411066e62d53319b58b54cc69c644cb318f99250cc63d64943319b98b548c66d62d52318f992508c63d64942319b98b544c66d62d5131c758f544c72e62d5131cb58b544c73561d51318f583544c63e64951318f994544c63d601513197997434c6d661d0d31c7d50434c71c54cc931a7191324c71c544c931d3149324c6d4
  | 4 => 0x1c6386000000000000000000000000164800540c280000040c760001ee0000000010e5283a0da93d0000011f1bc4c60342b2110006cc00000206000000003f68d8a6970522be00000000008000000000000d58000004c029878000000000000000000000000073ce7000000000001c44700000005e23e000000000000000000013600000000000000000c2000420001f10000fc002ae606000408000002900000000075462800000b5d7b23d556000000005ac000000002766a9569403841c4258000000000019d31a414002ed000804000005c87a800173000000960000000000013a000001248000000000004f0f2000000005740000000000007c0604300000069800000000001e000000000000000000000002ce9f887ab65ba0000000056e0014180003800000000000000178000008dc002aa0000010d30752404d0f8d82dc000000006180000026a0000005e000344938000000000000000000000000180000160b508a000000000000000000001e000000000000000000000000089c00000000000000000000006f8005864a8000001986d0dc00003400003800000000000000009540013c000000001be3ae474002260003286b82d00000000000582a30001de1a0000ef8095d8000002f15a23ad218000460000000038e8840000041a69000000174000000000000000025c4cac140000000000000004000000000000000015f0000003701416145c00000000000c24000000fcacc0000018614063800000000000000000000000000000145000000a94c091b48899c000000006b92fa8d000894000001ec00069000000000000002f8888c200051c0010f000000009610000000000000058e1290980020e0000000010e00000000000001620004620004b00000000064143000b9c00000000b5485123000944000ee000a041f000000264229164e68308d24f4c4c54ed264180a200000000000000000000000000f302000000000000000000004ae000002ff1689e0710ea5002404a90d12456d71abb580044c61a504c000a7800392000000000000000000036e30400000000000000000000000000000000000000000000001491f6959859410000b80008628c060000001c8000000000007280000036400000000452658320005ca0013a800000000000004e0bf800000000000000005440009b80002c748002c8000000900e14f254c001260003fc00000000745390b90004bc000120009c4dd800000000000000000014c00013057cee8f95b0a6d658d620c2080000000000000000232000ff80019c000eb00000000000312000130e09ad00080c0000027e0007928213c00109000122000000ad09c19d361db400000ee00050800000802004008010008000000000000000000801004004000000000000080180000400003005
  | 5 => 0x4000088000cd00000040000000ba40000017655400000000000000000009fcea08526a00000254000000a28000000003b800000c10000000000000000000000000000000ae000000000a780000032a5980000000013400000000000000000001497d0000000000000063000000000000000000cf2c800000000000000002a64ba00096800000a5851800000000002a4440000360000002880000000072d0411e0006280000030c3f44f8763d2998b611107a2b8000000000000000011e2d569006224700000000000d000102334000188000000003e0722900000000000066000000000c1800000036a3d680880e82a090957000000000f10000010e80015400154000476a9c000005ee000000000001a80012e0000000000000000030000000000000000006a00b8a601c494000001aa0009a2d451662d742184f60000000000000000000458bbc0024218c7a0002ea0060005000000000000000000c58000000005e00000000063d15a460000000000000002c000000000012d8000003240000000000000000000000000001162b00000011a00053994000528a20000002d8000000000001d1364a64704189a5b8000000373e0000000000000000000000017c5b8616202bca607f0008c0d01693244540000006666400000454c5ca59390008f000000000000000000002380000055ea680000000032c0020e1eaafc748000000000027c000000002b250e4302881958c740000a5000168000000d0a24002094a03e0000000009dc000000000000001400000000000000001168000000007a000000000001eb000084002970000011a99b1de000d0800000000001f200000000216000a4c0000000000000000600000b5800390231588005e8054001ed0008cc000001623b0002f90000000000000051c000002666154f9a90000009c0650006398880042018cb4000000000000000aa000d600037e000b00000000005f8003f0000000d9000000000000000004e8000000001387b0f40016d0006320000004700000080000000000002cc000000000000000000000032649c000000000000000000000000177000000000006269312f17b000000000001ba2c000038000b280014e1eead0000000000016f8000000000000000000000032000000f986d00000024000000984d7a1c494b98e6a7d6102a5561560000000000050a5fd6ca0a2c60014e800000000000000008a00000034e0003580000025c0027637400000000464000000005a600000179000000000a1000000000000b200000000000000001b02b4aa4001e60000000009c0008fc00000000c38310000002f4002ee0000000000a0006f40025800000084a7a5f800000000000000f38000000000025a2f40c0499fd00000000000000794ac15e000000c100034c001208000005d1508350
  | 6 => 0x2e40000000057a5f8001b90009b8ff1500007886d889000a40000e5202b6c7e02a0000010d99c0009480027422000059118000000a1000000000000f03981bc000390fa2f80029545ec50000000000000002933e810000001a800023066000000000fa2debf4002e2538b34001870000001e0000003b570000000000000da000764acaf340a6400000000098000217472490e98362bab780000000007400000572000000005ea0002b800000000000000000000012861ac3c000004680000000030681c00000000000f79b100000000094264170558000000006f0001fc9a4f0800000000000b8000000002cf2ec110001f44de92111800416125758e60100000013100000000000000000e28000000015180022645c6224000000000ab00005b4be82c0000157d80000083c001f7000549268d147465c0015101e09000000166000f18000004a400000000000000004d08090a80027c6d82a0250d255095a454d642d70abc00092c000003d81b8000002e2000000002ca7f1368003f291c15800000000002f00e0bc80000000000000259000000000000000008a189000000001a30000ec00000000000000006040000015c0005d4c88000000000000000085039962000174910000001080000059c6780000000041000000000000000001c6000001885320000005b3ea7e8000400007d800000000000000e0000b14001e4000ad4000000000003a84100021000000000864003011cea180022
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xc323719010f3554530002511846000030004c00004e2613160e00563828402a152e002122550a473c441d00500010432707004b0048004900003a003b3d0d341a061245424d241e0000361c000000000025000b0000000000390059000000312d20142b23000000004a00000000003e5800002f0000043f09521f332c4f00000008294100575a00001b110017000300050183040000868080020282811200800002810001030200000280008700004c57198b434ca62b8cc7a1265515c4544c832a92e02a2641960c644c9510cb83ba264a8865c11d13254432e0ec8992a219704644c9510ca62b94c3a1a63315ca63d0531a8ae42a26218d5170151310c68a3a2a498863c1dd1524c431e08e8a926218f0764549310c782322a498863315ce61d092198ae73168290d44754c9314872232a6498a43611d1324c521d08c89926290f04544c931486a2b98a890843585c05448421a8aeb29a4210d247454d2108783ba2a690843c11d15348421e0ec8a9a4210f046454d2108742992c219681a1589310c740d0ac690843a05267190c525030a29cc321281499ca4314540a2ce7210a2a060c5398a4150307318a520a818514e6194940a1ce7298a4a05267194c52502863aa64192810d1d5610c940d0a64b0864a0689325803250382298a5a8a818314e6294540c1cc6294a2a05167394c5150293394a628a81c114f5214540a2ce7290a2a0526729485150383a98a428a81c114c5214540858eab1062a0514754c43150342b126218a81a44c5600c540838eab1842a0524754842150342b1a4210a81a84856008540c48c430aa91854571149324c2a2b90a298a61525c04354830aa2e021aa21870952501300c388a8a8098061515c4534cb20c28c630aa9105457114d32482a2b98a290a419254d6010820ac2e0212a210709535012008390a8a8090041515c8534c710a8ae6292438860c6318954842a2b90a698a21515cc5248510ca2a6b008208661525804104388a9a8088021c85494044010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x92002c680008a30005000e00040000a0a0686dd1325443290687d913254432a0686dd1524c43190687d91524c431a0686dd1534842190687d915348421a04854c9610c940c04754c9610c940a0485589310c540c0475589310c540a048558d2108540c047558d2108540
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 741
  | 4 => 794
  | 3 => 91
  | 2 => 12
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
  | 5 => packedAt s4K5 (22477+((h/247+packedAt s4K5 (20007+(h % 247)*10) 10) % 890)*11) 11
  | 4 => packedAt s4K4 (33076+((h/264+packedAt s4K4 (30172+(h % 264)*11) 11) % 1853)*11) 11
  | 3 => packedAt s4K3 (4699+((h/30+packedAt s4K3 (4459+(h % 30)*8) 8) % 146)*8) 8
  | 2 => packedAt s4K2 (740+((h/4+packedAt s4K2 (720+(h % 4)*5) 5) % 22)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe0fffffffffff81e1e1fc3ffffffffc063fff
  | 1 => 0x3ff07fc0fc3f0ffe01fe3fc7e1e0f07e39ce93
  | 2 => 0x3fff83ff003ff0fffe003ff8fe00ff83c1f31c
  | 3 => 0xc00003ffffc000ffffffc000ffff0003fe03e0
  | 5 => 0xfffffc00000000ffffffffff00000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2800048200800004040480902281420021425
  | 1 => 0x942518864952549608aa15427142a15a18ca92
  | 2 => 0x1843291219a445aaaa082590b504cb0ac16318
  | 3 => 0x916a5224910666cd2d2c8100d99682136c03c0
  | 5 => 0x218c6038e2388871d1d13a2400180c61b7bc00
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee8fee8aaa8aaa8fee8fee8aaa8aaa8fee8fee8aaa8aaa8fee8fee8aaa8aaa8fee8fee8aaa8aaa8fee8fee8aaa8aaa8fee8fee8aaa8aaa8fee8fee8aaa8aaa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36292
namespace PEqualNP.Outside.L_meta_36292
open PEqualNP.Outside.L_meta_36292.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x400b80500cc800e4408d2c0059238a508456a93180c9c8003c00793406829500204a3363001400740243e2910e4a00a04e6070031530c6200ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x661dd32cc2fca3985f54730ef98e61dd31cc3de43987b48730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461de328c3b865185f94630bea8c61df318c3ba63187bc8630f690c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930ef99261dd324c2fea2985f14530ef98a61dd314c3de42987b48530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa418778c830ee190617e510c3eca2185d94430bea8861f5510c2eaa21877cc430ee98861ef210c3da42185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83be6390774c720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f621441ef32883d865105f94620bea8c41df31883ba63107bc8620f690c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483dc64907b4c920bfa8a417c51483be6290774c520f790a41ed21483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf29041ef42083d884107bcc820f6190417e51083eca2105d94420bea8841f551082eaa21077cc420ee98841ef21083da42105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c43dca5885b94b10bea9621ed52c42daa5885f14b10fb20e21f541c43be63887d8c710ee98e21f531c43aa63887bc8710fb10e21ed21c43ea43887948710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21f741843e8830877cc610ee98c21ef21843da43085f94210fd20421f940843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443be62887d8c510ee98a21f531443aa62887bc8510fb10a21ed21443ea42887948510fd20221f940443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f741043e8820877cc410ee98821ef21043da42085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe324c7ba6498f70c931fba0a63f4414c7ee6298f78c531bfa82637c504c7bea898f795131eeaa263dc544c7bea498f794931eea9263dc524c7be8498f790931eea1263dc424c7bea298f5d4531efa0a63d7414c7bc8298f750531ee20a63d4414c7bea098f794131eea8263dc504c6fea818df95031beaa0637c540c6fca618d794c31bf29063ee520c6dca418df54831f6a90636d520c6fca218f7cc431fb18863dd310c7ea6218df94031bea80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43ef42c87dc8590fb50b21f621643ef32c87dc6590fb4cb21f619643df31c87ba6390df94321bea8643ef54c87dca990fb55321f62a643ef53c87dca790fb54f21f629e43ef43c87dc8790fb50f21f621e43ef41c87dc8390fb50721f620e43ef31c879e6390fb8c721f698e43cd31c87d86390fbd4321f728643ed50c87d8a190dfd5221bf2a4437d54886f8a910dfd4e21bf29c43de53886bca710df54e21eea9c435d53886f8a710df54a21b6a94437e51887ee8310fd10621ef98c43f631887ba6310fd4c621ea98c43ef21887ee4310df94221bea84437f54486fca890df55121be2a2437f53486fca690df54d21be29a43ef42487dc8490fb50921f621243ef32487dc6490fb4c921f619243f741487e88290f7cc521fb18a43dd31487ea6290f54c521fb90a43ee21486fea090df14121f7aa243ee54487daa890fb15121f7a9a43ee53487daa690fb14d21f7a1a43ee43487da8690fb10d21f7a8a43e751487de8290f9d0521f720a43ed41487d88290f910521f798a43cf31487dc6290f98c521f698a43cd31487ca6290f14c521f618a43ef50487dca090fb54121f6282437f54086fca810df55021be2a0437f53086fca610f794c21af298437d53087baa610d754c21be298437e52086dca410df94421ef98843dd31087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740ef98e81dd31d03de43a07b48740beaa4817e53902faa7205f94a40bea94817e51902faa32077cc640ee98c81ef21903da43205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40dfa1a81bd43502fea4a07bd4940b7a92817c52503d8a4a05b14940dfa1281bd42502fea2a07dd4540bba8a817c51503e8a2a05d14540dfa0a81bd41503be62a0774c540f790a81ed21503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa22077cc440ee98881ef21103da42205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99
  | 2 => 0x200802000006004010000060380180800e000038010020040000001800007802000014010010000000200400400c00006018074000060120080000503000c0000600400afca5a1fb94b43b7296877d52d0fdaa5a1db54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf29487ee5290edca521df54a43f6a94876d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a17794f42af29e857d53d0bbaa7a15754f42bf28e857d51d0afca1a15f54342beaa4857e5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3217d94642bb28c857d5190beaa3215d54642bf284857d5090afea6a15f14d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbbe87997710f32f721665ed42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7197790e32eea1c657e528cbde85197b10a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f7a1265ec424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cafaa8195f15032bf29865de430cbba86195f94832f721065ed420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cafaa0195f94f41bea9e837e52d06faa5a0df94341bea86837d54906fca720f794e41af29c837d53907baa720d754e41bf29483ee52906dca520df54a41f6a94836d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a837f52506f8a4a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d53106fca420fb94841b7290837d52107daa420db54841bf28883bf41107ec8220ef50441faa08837e50107f4a020de94041bea8083f950106f2a020dfd5331bf2a6637d54cc6f8a998f7d0f31ef21e63dd43cc7b88798df94b31bea9663df32cc7bc6598f74cb31ee196637e50cc6faa198f7d5331ef2a663dd54cc7b8a998f7d4b31ef29663dd52cc7b8a598f7d0b31ef21663dd42cc7b88598f7d0731ef20e63dd41cc7b88398f7d4331ef28663dd50cc7b8a198dfd5231bf2a4637d548c6f8a918df54e31aea9c637e528c7dca518db94a31bea9463ed528c6daa518df94631fba0c63f4418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f790d31eea1a63dc434c6fea498df14931ef99263d
  | 3 => 0x29cc97127000d10000005ca9d40009a6c400153868038b2d352e41c21144a2ee52c1751a0bf19c570001f4000000001930000000000037899800000000ba17d000000000002ca000000000005880000027851e2c4000000006f5340000008a80022262c000000e00000000000e51c00000000000000002b53001391e2bf61cd7cb00000000003ea5b4086c8001986783600010221483c0035b000001498fe5760015f03a00000000000000a1d050000007a8000002de00169800000550000d52d0708e7082346cb0a01770000347f800656c5c14ac14e0000f6800000000daadc000539178a4000c4d140005060000000006259000000000001759610009f020a08000001750000008d400242000514f00921321d80000000a000c729b6daa980000019450d7f0001be0007a000000000000001729389800053eae40016e630d695700020e094000002f80000000000000094800000540ac09f672a782aa0e264a2c0007338e0000000000014dae800000000450003dea957380049e000d80003aa4d4002c260c3a45a80000000191000000b78ba0006840ed7c0b222eb00a523946cdc408a6c3706bc848222c63e43221c0002393088149a0303527e29e42c002d6000000001fd000000000564ae2980000015c0000fa582084b4258006bc000818005562f00000006012400000000000ad800000728c3a0257a7799532f48e26001af6342d61aa05267aa90000003a000000000586000bc32d4f60418e1e7000b3c000000000004b8a835677ccf00018c00000000000ccc0016d0008900007500043c000000000016a8002b48480000068e8b07c0323ca03d221c51b89f4eb147000000002796f09c94c0795e20d462800000d18fd00043ec1400000000000000ba2cc4c40000008604d768002360002f0000000000000046ea4400000000000002202765640012a430234b5800018000054038000000040580400a024028000000040000200800407801006048000000020240800000001001800002010008040120000400000005c008000020000080000800401002026008048070080000001301002000001006000000000000000180100001800001006008008000080100000001400400801010000000030020000000201201c03000000070000020020000080900000000004004004018020020000200600000c010000080000000000c0000200100a0080000a000030000010000040400702e000000000060000000100200c0080001601406800002004000030000100000100600c0080100600c000000000040000300001803004028030038020000000200000000c00802000020000010060000200000001000004000000000020080000000a000008008060180380080201200000002000000000090040080280300000001807006000000000
  | 4 => 0x660000330f7504548093731867719a058000000032503504494ba153d80004601d6e4d819d98f000000000cf0000f00024a66cb300034500032c00000000001680005e0588b9800000000a48a1000520003252565e4003404962d00023d000ca400000000a70000001b2000000000be578000000008c55810024c25431b242e03b0cca2b51ac85a62235fa09151847570001a58c700038db8262000001b580038c87537a5332cdb01a17b5c63c4691751ac000901330003b890b070000010196a000a50b29360000008621602c13ceda63000d040000023000000182398a880c80000000168800000000001e86d40fc552d25b2698da0006081fd8d00034a001b22c60004717a80015a000fcb5955e72dab15f0007987d34a0001b51681416e0015e0000003500000002a001a48da0f0724538f528286800000000061879890005597780040200060a432ce1c11f87b6004d1aa8572268512a8000d6c3482aa962806c0029d00000000000000a84e080011ecc40021e50a194640000000000027f2589e91d800000001bbae200e004c2800198d98119f869a444000001cc7682cb230009d8000004ac001430006128e9a71c80000016c2d4122130d69f20c200193000000001850005f6964d897d3ee000758002746100019213a12155000000000000004363917027720c6440029962465cdc80059a3c17625200020c13b530000012f0ed44221574b61314301ba00040c000000000004f81724623c0014d000334950d4800000000001c00000008c840000c300000000000000183000000db0003e66346d8001000b154226000ad000209640d4800000340000d20000003440013800000000000000ce0f4914000a497320d5e60ac000774e200000000518a419a9d133ab24d50000000984422e000d2000232000cfc94000016b204f2b137e5f9672810008400009065c000000000d2000000000c00001e800000000003030000000014263e000020000000012f96c22c1d185ac709a14400008000000669ee6dc99c00000000000001e40005a472800108001b28000000000004a000420ea000000270002f2000dbcd38671bad0c438a2000000ff800248000002ad166001b40ea6f254c8719b0000011c062152000000b600000120000202970d7000050688000005f8001199cd15600800137000c64a689b52a84c0000000000000000498a80000000000000024923a4e56d9dd2ec6edb38000009441c93f15e5108d0000000000006f3100d877b111e4c096299f0009a4881fe02e90537351602dd9400000660bc0000003491400337452c41563280007c4698000e475d841eb0000002219c1ae32400000000c9c458004c800000000000001088000000005c1d8000000002300140015b3320000017b800000000000003185e96b8371bc168ab9e25f
  | 5 => 0x1b48001400018d85c3200005f35c22a99570b634d62b0610001e60007e12351439d9d1d324424c8f8e8012119bab1e1c45c8431ac0b6adc928bb2a27651398b3c200000195416001599b30004f42a33e6a0bd051800278d3cf82885be000fa9cf0000000031d0001092e994418d5cb88003c692000217000bfc0023e374530150962969b4002893026dc109d23f6ae8370000a01b03f0b0070001028bd000000001fc000a10869c30f43d81680037cb747d8000001f09780003c001129461a0b693025a2aac54000001fa000528890001c4001c4000310fb219000000bfab20000000015d000000100000008010380007c6193a000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xb31c42e5628c710d954a31c434e524c710d354931c4356534c710d954931c42d7654c710d5d9531c4356544c710d515131c4357524c710f194931c4355524c710f154931c4345524c710d394f21c434d53c8710f14c721c42d56388710d554e21c434e5348710d354d21c43c73148710f14c521c43555348710d994921c42e76548710d9d9521c43665448710d915121c43675348710f194d21c43655348710f154d21c4345534871097d8d548425c63552109bd89548426c62552109798c548425d63152109b988548426d62152109bd89538426c6254e108f990538423d6414e109b988538426d6214e1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10bc58041843c53148610bc18540843b3415021097d8d544425c63551109bd89544426c62551109dd85544425e63151109758c544426e62151109b588544423f6454d108f191534426f6254d109b189534426e6214d109b588534423f64549108f191524425f63549109718d524425e63149109758c52442766590510b558e41442e562905109d19541442d5638c510b958a3144274654c510d5d953144354654c510d59513144354544c510d5d493144355524c510f4d8131443d0604c510f14c721442d56388510b958a21443c73148510f14c521442746548510d9d9521443646548510d995121443645448510d9d4d21443655348510f8d8121443e06048510f44c640443e121901109e19540443b14150110f44c540443e12150110f44c710443e121c41109798f540425d63d50109b98b540426d62d50108f596540433461550108f990540425e63150109758c540426e62150109b588540427661150109e980540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c1097d85530425d6154c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520426f61548109b585520423e64148108f590520425e63148109758c520426e62148109d984520425e63944109758e510426e62944109b58a510427565d0410cd553410435553d0410d954b41042756510410cd55041043555310410d954841042f1601041097597310431e54cc410c7553310434e52cc410d354b310425f654c410c7951310431d544c410d3949310434d524c410d5945310426d65c8410cb953210432d54c8410d394f210434d53c84109bd95210432e5448410cb551210434e5348410d354d21043665148410f14c5210433554c4010d554f100436552c40109e596100433954840109dd9510043355444010d554d100436552440109ed9510043395444010
  | 1 => 0xc32e5448430cb551210c3665148430d9545210c3c53148430c7553300c34d52cc030d5547300c25f654c030c7551300c2cc624c030d3549300c355514c0309ed95300c25e63d53209758f54c827661d53209d58754c825e63953209758e54c82766114f209d58453c82cd6390b20b958642c834c534cb209798e51c825d6394720d594531c8355514c720d954721c83c5314872097d8d548825c63552209dd85548827461552209798c548825d63152209d984548827561152208f990538823d6414e209d98453882756114e20b398f428834f530ca20b9584328825e63946209758e5188356514c620d554531883665148620d954521883c531486209798e544825d639512097d8d544825c63551209bd89544827761551209d185544825d61d4d209798e534826f6254d209d98453482756114d209799453482d56114d20d358853483566114d209758453483556114d2095584534826e6590920b358e424834c5390920b9586424826c6550920d314d424826e658c920d314e324826c654c920d314d324825e63145209758c514825e65cc52097197314825e654c52097195314834f53c8520d314f214834f5348520d314d21483675148520f14c5214834c53881209798f540825d63d50209d987540827561d50208f596540832c62550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530825d6194c20c7951530831d5454c20d3189530825f6154c208f990530823d6414c209798c530826e6214c209d98453082756114c209b597420832d54d0820b398f420834d53d08209b594420832d5410820d354c420826d65cc820cb553320834d53cc8209b594320832d540c820d354c32082e5610c8209798e510825d6394420cd95251083355494420d594e51083555394420d598e51083556394420cd95151083355454420d594d51083555354420d598d51083556354420d998951083674254420d910951083673254420d90c9510825f65cc42097597310831e54cc420c7553310835651cc420d5547310825f654c42097595310831e544c420c75513108356514c420d5545310832e54c8420cb553210834e53c8420d354f210836551c8420cb951210832d5448420d394d210834d5348420d994521083c53148420cb553200834d53c8020d9547200826f6548020cb55120082cc6348020d354d200836551480209ed95200825e63d53109758f54c426e62d53109b58b54c425e63153109758c54c426e62153109b58854c426e62d4f109b58b53c43566194f109b98853c426d6214f109798f52c425d63d4b10d394e52c434d5394b10d998652c434e5354b10d354d52c425e6314b109758c52c42d56390710b958a41c434e52cc710d354
  | 2 => 0x514c540d51453150397414c5409b997215026c65c8540d3d4f215034c53c8540d9d47215036451c85409b995215026c6548540d3d4d215034c5348540d9d4521503645148540e9d0521503c5314854097586531025f6154c40d394e521034d53948409b586521034e5354840d354d521026f61548409798e511025d63944409b98a511026d6294440d594e51103555394440d994a51103655294440d598e51103556394440d998a51103656294440d594d51103555354440d994951103655254440d598d51103556354440d99895110365625444097d97311025d65cc440d394b311034d52cc440d5947311035551cc44097d95311025d654c440d3949311034d524c440d59453110355514c4409bd97211026d65c8440d394f211034d53c8440d9947211036551c84409bd95211026d6548440d394d211034d5348440d994521103655148440f14c5211031d53d0040cb54b401033551d0040dc546401023f6550040c754d401032d5250040cd545401027b6550040dc545401026e62d53309b58b54cc27661d53309d58754cc26e62953309b58a54cc2cd6290f30b558643cc26e62947309b58a51cc35551cc730d994521cc3655148730f14c521cc26f62552309b189548c27761552309d185548c26e62152309b588548c27661152309d584548c2ce62d0e30b5584328c26e62946309b58a518c356514c630d5545318c3665148630d9545218c3c531486309b98a544c26d629513097d8d544c26f62551309b189544c27761551309d185544c25e6590d30b358a434c2d56190d3097195434c26d61d49309d984524c2756114930b9584524c34e4314930d350c524c36661149309b584524c365611493099584524c25e65cc930d314b324c34c524c9309b988514c26d6214530d3d4b314c34c52cc530d3d49314c34c524c530d5d45314c26e65c85309b197214c26e65485309b195214c3c53148530d314a304c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c23e64150309798c540c26e62150309b588540c27661150309d584540c25d65d0c30c7553430c2ce62d0c3097594430c31d5410c30cb952520c32d54948309b586520c32e5454830cb551520c34f4354830d310d520c26f615483097596320c31d548c830d354a320c31d540c830d3548320c2d5610c8309b98a510c26d6294430cd952510c3355494430d994a510c3655294430d998a510c3656294430cd951510c3355454430d9949510c3655254430d598d510c3574354430d510d510c3666254430d9589510c3563254430d50c9510c31e54cc430c7553310c34e52cc430d354b310c35551cc430c7951310c31d544c430d3949310c34d524c430d5945310c26f65c84309b597210c32e54c8430cb553210c36651c8430d9547210c26f65484309b595210
  | 3 => 0x121b958654486e76155121cb55054486ae6494d21ab59253486e56194d21b9d85534874d5314d219b997434866d65d0d219b996434866d6590d21b998643486e56190d21b9d8543486e46150d21b998443486e56110d21b999351486e563d4521b958351486e665d0521b919741487a754d0521e915341486e563d0521b9583414866e6590521b398e41486cd6390521b9986414866e6510521b398c41486cd6310521ba98041486e96010521b999441487666510521b999041487a66410521f198c41486e56310521f158c41486c56310521f898041486e56010521f858041486e16010521f1d4731487c741cc521f1107314866e658c521b358e31486e6658c521d999631486e6648c521b919231486e5638c521b158e31486e5608c521f1d8531487c7514c521f1d0531487c6414c521f150531487c4414c521b999531486e4654c521b999131486e4644c521f1d8d31487c7534c521f114d31487c7434c521f190d31487c5434c521f110d31486e7604c521f1d9531487c6654c521f159531487c4654c521f1d9131487c6644c521f159131487c4644c521f1d5131487c6544c521f155131487c4544c521f1d8131487c6604c521f158131487c4604c5219b99431486ce630c521b998431487c5310c521f14c750487c53194121abd9150486ac6454121b3d8d50486cc6354121f14c550486ae6414121ab59050486ce6314121b358c50487c531141219798f540865d63d50219b98b540867661d50219798c540865d63150219b988540867a60150219e580540866e62d4c2197596530865e6314c219b98853086766114c219798e510865d639442197597310874e52cc42197d95310874e524c421d5945310874e53c8421d354f210875553884219bd95210874e5348421d354d21087c531484219dd9521087555348421d9949210866e6294f409b58a53d02766194f409d58653d02ad62d0f409798e52d025d6394b409d98652d02756194b40a758f42d025e63947409758e51d026e62947409b58a51d0397414c740e9d0521d03c531487409bd89539026c6254e4097d8d529025c6354a409798e519025d63946409b98a519026d6294640d59453190355514c640d994521903655148640f14c5219025d61d4d4097584535031c53d0d40ab58b435034f53d4940d314f525026d61d4940d3d4c525034c53149409b584525029d63d0940cb14b425035753d4540d514f515036752d4540d914b515035763d4540d518f515036762d4540d918b515025e63145409758c515026e62145409b58851503575314540d514c51503675214540d914851503566314540d558c51503666214540d958851503716014540cd147415025e65cc54097197315034f52cc540d314b315035751cc540d5147315025e654c54097195315034f524c540d31493150357
  | 4 => 0x7151434c6d46150d31b5986324c74c524c931b5984324c67665d0531b598c414c6e56210531bc580414c6ce628c531b358a314c63e64141318f590504c66e62141319b588504c6ce62d5131b358b544c6ce6295131b358a544c6d56195131b5d85544c71d5415131a7992524c69d6494931b5586524c6d76154931d3548524c65e65d093197597424c65e659093197596424c6d66190931b5586424c6d76150931b5185424c6d66110931b5584424c6d664d4531b558b514c6d560d4531b5997414c6d465d0531e5d53414c79454d0531b558b414c6d560d053197996414c6ce6290531b358a414c6d6619053197994414c6ce6210531b3588414c6da6010531b6580414c6d66510531d5994414c6d66410531e5990414c7c66210531b5588414c7c56210531b1588414c7d26010531b5580414c7d16010531b4580414c69f6454131a7191504c6cf6254131b3189504c69e6414131a7590504c6ce6214131b3588504c65e63d50319b98b540c66d62d50319d987540c65e63150319b988540c66d62150319e980540c6796015031d394b310c74d52cc431d954a310c65f654c431d3949310c74d524c4319dd95310c756534c431d9549310c65e63d53219758f54c865e63953219758e54c863e64d4f218f59353c86ce63d0b21b358f42c86ce6390b21b358e42c872d5410b21d314d32c874d530cb2197d8d50c865c6354321b398f54c86cd63d5321b958754c86ce6395321b358e54c872d5415321b958454c86ae64d4f21ab59353c86e561d4f21d354c53c86e56114f219b99743c866d65d0f219b99643c866d6590f21b998643c86e56190f21b398e41c86cd6390721b398c41c86cd6310721e950441c86ea6010721ba58041c87c7614c721f1d0531c87c4414c721b3d8d50c86cc6354321ab99050c86ad6414321b398c50c86cd63143219798f548865d63d52219798c548865d63152219e98054886796015221d5986538875553d0621cd55041886d56310621d554c41886f16010621d594d31886d7654c621d5d953188756544c621d5151318874e53c8621d354f218875531542219798f544865d63d51219798e544865d63951218f992534863d6494d219b99742486ce63d0921b358f42486ce6390921b358e42486e661909219b195424872c5450921b9185424866e65cc921b9987324866c654c921d314d324874d530c921b9984324867665d0521b558c41486e66210521bc58041486d5638c521b998a3148674654c521f1cc931487c6324c521f14c931487c4324c521d5d953148754654c521d59513148754544c521f1d8931487c4624c521f1d0931487c6424c521f150931487c4424c521b398e21486cd6388521f14c6214875531d41218f990504863d64141219798c504865d6314121b398f54486cd63d5121b398e54486cd6395
  | 5 => 0x53d0b556194f429558653d0a5f6154f429798e51d0a5d6394742975865390b4c6254e4297d855390ace63d0a42d354f4290a5e63946429758e5190b565394642d554e5190b566394642d558e5190b565354642d554d5190b566354642d558d5190b666254642d9d095190ace63d09429798c5150a5d63145429798c5050a5d63141429d9845050a756114142b358e4210ae561908428fd954210a6f65508429798e5110a5d639444297d8d5010a5c63540429d98754cca7561d5332b398b43ccacd6390b32b958642cca7661d52329d587548cacd6290e32b5586438cace63d0a329d987544ca7561d51329758e544ca6d629513297997434cace62d0d3297994434ca6e65d0932b398f424ca6e65109328f990504ca3d64141329d984504ca7561141329798f540ca6e62d50329d987540ca7561d50329d984540ca7561150329e980540ca79601503297596430cacd6290c32b5586430ca5f6550c329b596420cacd6390832b9586420ca6f6550832b358e320ca5f654c8329bd95320cacf654c832d3d95320cacf644c832b3591320cb4e544c832d3151320cacf614c832b3181320cbc53294432d34c9510cbc53254432d598d510cb564354432d550d510cb666254432d9909510cb654254432d5cc9510cb663254432d54c9510cb653254432d14c9510cb4d32540329b98a53d066d6294f419798e52d065d6394b4197d8d50d065c63543419bd8950d066c6254341d394e529074d5394a41d394d529074d5354a41d554f419076552d06419b98b535066d62d4d419798f525065d63d49419798c505065d63141419b988505066d6214141d5986531074e5394841d354e52107666194841d394d521074d5354841b558e41106e562904418fd9541106776550441d694e50107595394041da94a50107695294041d694d50107595354041da94950107695254041ced0550107724154041ce505501077141540419b98b54cc66d62d53319b98a54cc66d6295331b398b43cc6cd62d0f31b398a43cc6cd6290f31c755043cc74d520cb319bd8950cc66c6254331b398b54cc6cd62d5331b558754cc6ce6295331b358a54cc71d5415331b558454cc69e64d4b31a759352cc6d561d4b31d354852cc6d56114b319799742cc65d65d0b319799642cc65d6590b31b598642cc6d56190b31b398a41cc6cd6290731b398841cc6cd6210731e550441cc6da6010731b658041cc6cf6254331b318950cc69e6414331a759050cc6ce6214331b358850cc66e62d52319b58b548c66e62152319b588548c67a60152319e580548c7666194a31d954b418c7355410631b9588418c7655210631bc580418c74e52cc631d354b318c66e62d51319b58b544c66e62951319b58a544c65e65d0d31b398b434c6cd62d0d31b398a434c6cd6290d31b5986434c65c6550d31c
  | 6 => 0x3a4c80a80027311ba7e23ea5409000000000000027c96b9d413290585f9a99450288848ca18a97917d10119f0d7984a9880008f8000001298128000408ab0002908270c880f95203c9ea1b61c5a87a918bf2891dc0a980000002b9312109e21778001169528001519240001fc0518000000b30000b600008180000000013e1660000000001e78060241ef1aa1830f08810002052802772849028000b08fe80000d1da1208002329b114b00008da5d8461171068ac2080931398a40db1500008000260b40581d00e0140100e0020d402031000004020090080600000b0080040400003a000018010040040000b0020240901400a0000200f000004150000040040000e00c000030030020100180600c00c0000000a0380000e00a0000000001000001005096080000530120080480500a0000000601e04c008030000640000000a00c0e80a0040703782a0100100002f08000c0c0010120100a80a0160500000c034010010160000500100802606c00812002088088000000000080403000c0380001800401005000000008040020340280002c00c0200100e0a00000800a0200100600400c0000402800021034006018020180020840c800008024038020020040e0070060100100004a0040480f0020040a8010020100000402e000010000181180381101800401000002014048000020300400100a0280200502000003800006030018030100040181d01203c0180000e000008020000080380000a02c000040060700000100c0280200000005c0d80b05001c008040120000000202c000008000020000300a002008028020020141500400200400000000058070060840580b00800000c0282c00e00c0000000a0100000000604c0000100a0200580900c0081600900601010810078028000090140280601f000004080020060080a80101c0740080000a0080003001e0240a8010000041900e02e0000701200601c0080100e04c018080000000003d010000000020020780180f0140200080202807400809000000088010060100002003a07c120000040280580501a00c000110000000980d000050028090120080e80001a00c0080c00000401800010004000260180000101d9d98652d0e756194b43b958652d0f666194b439b58652d0f656194b439958652d0e6f6154b439b98a51d0e6d6294743b398b4390e6d6194a43d3d0d5290e6f6154a439b98a5190e6d6294643d994a5190f655294643d998a5190f656294643d99495190f655254643d598d5190f574354643d99895190f656254643b398b4350e6e62145439b5885150e6e62141439b5885050e7661141439d5845050ecd6290c43b55864310e3f6550c4397d954310e6e62944439b58a5110e6f62540439b1895010e766194f429d58653d0ad56194f42d358a53d0b566194f4297586
  | 7 => 0x1910cd9ab0249198000000001f421320f2779cc26092d00000014a26b00000001014f1ec00b0f5a82a7f00014800021aa9980006f8001a780000017880002e1221ed97c8831eb8be09da7d8c280d8f3136a9b8002078098001c18ec96f0000000002200000728a800008680026a12629387e2358088749649410c481a2309992118f892f1e980012a15c80001b8002781c922282f8000079ae8ae83f85b1352128ce9a080000006414d80026fa1f9af25009528116e0179270c92921cb9d61d389c9a6829a170e18a7a069939d1a1e9759c50998a22550bd20982da3f228a6990c13a1851d6a7f909046a84083a6f035a529b38c3a361cd1ac9baa2827094e84c1be1330e78d2a2fa0a22f12a8f11ce0500001dda6c81b1e18001f080027613ba9da0d97a0b696c255a1827882916b0522459699d52278878149d90e70450a592e0c584187998c83c0d400089700325b0e881c0ca8731e601180ea341878ff09a8ad82f1279ee9f70e206925c0a08fa9958068ea95a8f4954076a1b00e14f9fa1a42508b48541db01f2942251610001d98c98fc9560be9008c800024a0002422868f00000f500c0000000d700017180010b99700011224986107b88b9f285e272a928539f68ee82b22a80003185318e1b412b8002369459ed15b23c218a2307589410a80026b8da9050870350e39982851822150021a580003e8b78e28000000000000141a100000001fa31214a4c1288d105f28626500591893f8a280000025e99f86a9679bc00022694284e00717f062a2119a20e0db9710110df8001f585d8001ffa539fc95e2980679b9205868a959359c41d00001988000921f01b31930840738d81419708978a19a92469e895382216a00023a9b08130fe1588e48348f28aa90ca160e699695914717b1948a323ca94a13a338c40a926388e00018703204f8199469ad04f24821b8b18e40dd033a6927e80016f8ec1ee05c8a60e58000a49eb23195d0371099729e41118ce0fd28e8018529268420fb07b11499027b8001442740001739731f300000005781aa9b21da8a0000919fe9f888015300000014398d9619629f3a4a8630001b2120000271a8b09399d9ba0f71c10001af8d524316880028385c0508001fe24280020e83b07c91a08d08880005b9d28de0720001a01162060baa4b1e4925a61a9304d2808001ca27688c91c8308488002688260f18968cc2898000b5223a7480000000000019c0c00e60959309a2a5a80003d0c304d80002c8e300000000016529725f19b25ba3fa51a5824d92c80000000026a80003f0b99be8040001800002579e0a9a8000002018000000000000c18e100023d94780006510d09e1742790d19ac0ab8601829580000c50000001f480029924713e8c080020f9e70001060410b224b90413c9379489770400ed934a5f80010
  | 8 => 0x2c0002271cb0001f20dca0295ba54a0c87510f1cea521658ad0a88909c395da301b01b299527a2910ee29a1e91998990dc1f98d907094a87d81e84798889a08e9138dd95c257258a410430eba4f87893f20aa1d1c68791b992b0fa06f2398f98ae1d88ed08202a0c79839d20280c711780829612f8001b690000005916c80023527a9df172110185a6c09f23b1919319e308a21ca2ea6297b8af1fa86d89c06c1ea8cb0f608b1bf22926d0d021915f1701bb8172298aa0ac85592da022400891a828a92308a9dc97e0ef9da9280bc99c82d1c29211159aa8d98570001d780006b9d480024d07f23313390800020b0000389b81fb2110440000000001929ae01d87e80019e1370001f186a0000001e00001c485a9dea198c6a2080014014d2049818550002671810561ad9140052220238b10000498258328d310d84a0b712186980029c25d09b912a2622da830001d087c1760000000a50f401622b08c23728883e074058825160866a449908f80b900000011d9c9800296a3ba60197a1592ea9d01085484498b93d8bd80025e208a65a4f0c61e518800007611b2002032039c79cd81597ea2b83b8af877963a241f900025311915a0cf9fd28200f0b01e5a218001020d88bb1bf83106c8f798a20d00010b01e18607a8369c222a1de2569490e997d95701529018081919a8379291cf8039b48f3a661752169e11558a70b58ff9bb000000004a8f0981549768510b29920ea28d00002aa669c8a5122c908a5c9d58362461669fd9c60bc13c08f0d61079a31efa819ec9dd14600000c88980021e19d2721b51cc894862061813a1790e04903da321c307fa0c2738fc16a8e818d0000d4a4080014b8001f119612527b0001131e68658000002010cd24e14c0eb03400000008080014314c98e9a49048cb9622681a88229300182478d219ea5628ba378000001ab8438a691e0d09940fba621798b40d680023d23891080a00000018f901a489a50f22798cc9db8e902182c00017486489d17818424383300000009284ba5985a00000004e9578001f82248711c025a13d1e8085a380001a3938989a4190a1ff0010000002710f686800017a80015e97f9a628c8001341fb85800019b8ba07a03a00b9891b180000003007180004a82013211c00000018c0f90000d390701880015682111126d9380b880000023908528d8480268001550001f600000011d00007000013a8000c100013b0e096308286b2591d121a00000000000000003980007d28c06e9b88000000cf066009212056a8711f22585e9e28d58599150000000bb820a4503929781c96d000000000144a1f21c1bd1b78da00018f2090000a0016a1427d2700880e520406d03a9670c20910231e391e939063a6480009616e8671031cf1ca845a0723e0a10000000000001d7000086027800000000
  | 9 => 0xef1d311804292396815086e00000003809e9bd924a75a2c26e98b0a384b13614e26310e9a704c95989f95f8608472610b3a8597c0000fd91f80028816901d1b580000002e80280027c1c0a9c8001c80002640000001f50000001510121bc9409d809b0df244000267a2d122a4ea00a9528e1601b70771df80000026e0000780000de9f7a349a1949a1014209885d11aa0b80028fa2e0001869640b80e00002750001c716d9a20bf90fa4923a0000001
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x90cc573185424872232a6498a43459d3654c5218aced2a26290cc67690931486a23aa8498a43c1151424c52198ae331ea890cc5739935148663b9ac1a8a4331dcd60d0521d82c73008290e62655804148751322c020a43b098d6010521d82c6b008290dc1701073148670b80c918a43319da414c521a8ceb20a6290dc27010531486e0b808298a43299d2654c5218cceb3226290d467590d31486623b28698a43a1191434c521b0ce9b2a6290d8574d9531486c33a4ca98a43615d2654c521c8aca32a6290d4675d9131486a2baec898a43519d6644c521a8aeb3226290e856419131486633b6a898a43315db544c52198ced2a26290cc5769513148782aa0a898a4361dd1604c521b08e8b026290d467518131486c33a0c098a43615d0604c521d0ec898aa090e84644c55048663bb26228243a19913114121d0ac8988a090c6571189539022ab88c6a9481515ca514c640a8ae728a432064763d8b5150322b1ac428a819458d6014540cc2c4b00a2a05457114931502a2b90a298a8185197414c540a8ae229a42a054573145215031232e8290a81519d53148540a88ea98a42a0646654c5215032232a6290a819158d6294440c8ac6b12a2205457194931102a2b94a298881515c65348440a8ae728a4220547754c521102a2baa629088191d953148440c8aca98a42204657198a54cc262b8cc5a1c61515ca514c6308cae3314a8985457190c524c32339ac229261915cd6114930c8c86b08a49864543584524c2a2b88a599261515c4524c930a8ae2296629854571149314c32332a6290a61515c4528c130c1aa931686184c57198b430c30aaa2c21906191549610c830a8ce5a1aa21854571949310c2a2b94a29886191d953148430e0ca898a4218705544c5210c306aa0c498061315c4624c030c88c4a8a60184557198e54c82a2b88a699641315c663d0a20c8ea6b08651054573945218822ab8cc72a241915896114d20c8ce4b08a690645725845348226bb0a721241515c45390920c88a6b0c84905457114d42482a2b88a719241515c4534c920a8ae229e42905457114d21482a33aa6290a41515c45388120a8ae2312a61060d5498f4208262b8cc7a104113dd953d0820c4aa8b0864106455358432082a339e84a8841515c65348420a8ae728a4210547754c521083832a26290841c15513148420c1aa831a40104c57118d20082263b2a6900419118d5148020a8ae42a263885457315121c42a2b90ca98a21515c8544c5108a8eca9262885147454931442c8ba0c098a21515cc6548510a8ae62a242884647654d21442923a2a690a21685d06048510ca0ca98a8088660654854044318aa2c0208219454d6010410cc2a4b0082085457294531042a2b8aa690821515ce5148410a8eea98a4208647654c521043832a26290821c15513148410
  | 1 => 0xd00000001b9cc0000000004aae2f1ac00003f00000005c0d534ac0000c00000000056004409c8aa90030928000c00164334eb30004803b25b8db5c9b9ac962837da6000000058a50000000000006c9e0020800000a0ab496a003000000000000000bd00000000000380005a310000004342780000000017e17061700000001e4000016800000048a4c0000001c95ed45f31c0014329a800322b0000077608a1ba5b1b0fc98a06d0012e001c314008f2e8442c0b001a400000000000000007c5e7000204004e5d95c00240027c7664000b800001c8815a0f339d84600002100000438e8008646001ae54622d000e34a8000000001d4a600000010400552480acd598014e0d508007a0000000000004000001210b008c0000000008b25b3d368d0000000d531aac386c36adcde0000000000000038007b000994c904500000003a0011cc3218a80099002917800001fcbe000000000830f0019c300000000006c9240c4a6808826b01a0008800001456c5571199123e00000f8000000000a30091cb2003d00000000038400800000000004e1c40000650f0c2000eb18523108000120058800f00268a1432c82032c00423e93400d800260a40054000b0006f289740100000000008408000000808040080000040000802000300002000180c08000000400010082c040103000060000000140001000080300000000502008000201000000b000040001000180000018201201000140200c8ce6b0ca5a1e457358652d0e62b8cc5a1c87519cb435464398ae331686a1c65711895010f22b12c329e85919c96194f42c8ae4b0ca7a1545711895390a62b8cc7a1485519cf425464298ae331e84a14557118d5010a62b8cc5a1e65315c663d0a3298ae331686994c57198f424ca62b8ec899065139da544c832c1ec92a2641954571151320caa4b80a899065235d0604c83298ae23026419547714c9510caa3baa64a8865455d26354432a8ae521aa21952574989510caa2b9c84a886551dd93254432a8ee8992a219545744c9510caa238264a8865545ce4154041ac2e520aa020cc57198a54cc722a92c229663a45056010731c62a8b008318e6152580418c662b94c321a63315c86150d3198ae3316a898cc572993514c663b92c1a8a6331dc960d0531d82c53008298e5265580414c749322c020a63b09896010531d82c4b008298cc57198e54c8722a9ac229e43a85056010721b82e020a6390e31545804188728a9ac020c43545c0544c62198ae730c84
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x30082ad2a0000411c2068cc0146da05849cd6194b43a05849c96194f4290584dd9325443284586dd13254432905841c13254432a05849cd6114930c05545c662d0c30c05545c4624c030a05849c96114d208458714d6190920c05545c663d0820845869cf4254420c05545c463480208458718d5148020
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s5K5 (27286+((h/296+packedAt s5K5 (24030+(h % 296)*11) 11) % 1421)*11) 11
  | 4 => packedAt s5K4 (55826+((h/446+packedAt s5K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s5K3 (11856+((h/76+packedAt s5K3 (11172+(h % 76)*9) 9) % 400)*9) 9
  | 2 => packedAt s5K2 (860+((h/4+packedAt s5K2 (840+(h % 4)*5) 5) % 18)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3fe1ff0ffffffff83861f0fc1fffffff024fff
  | 1 => 0xc3fe1ff1e0f0f0ffc07e3f1fe38787878db293
  | 2 => 0x3ffe001ff00ff0fff803fe003f807f8f1c31c
  | 3 => 0xfc000001ffff000fffffc00003fff800fe03e0
  | 4 => 0xfffffffe0000000ffffffffffc000000fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x200010200000000000402400088080000425
  | 1 => 0x8944468246252548c22a1508c1c51516849292
  | 2 => 0xb188caa48a66c45b5a8836414ad42672b1c318
  | 3 => 0x191d94c914c4666dab6c840293667424de03c0
  | 4 => 0x221118001888888634512893180040406b6800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8feeeaaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36292
namespace PEqualNP.Outside.L_meta_36292
open PEqualNP.Outside.L_meta_36292.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1c01300364463b12894805a08b1d3e00986006002c4801faa6a41e946ea053a1e202994200084700191c78343ab2e0139200000250001a3900cd89e00d9f002a0178b460002e066903005001c001009418b0e24000000c9920438880027fd50097f54027f95009fd54025f55009fc5402ffd4c07fe5302ff54c07fc53027fd0c07fe43027f50c07fc4302ffd4805fe5202ff54805fc52027fd0805fe42027f50805fc4201ffcc805fe32007f4c805fc3202ffd4403fe5102ff54403fc51027fd0403fe41027f50403fc4101ffcc403fe31007f4c403fc31017fc8403fe21007f48403fc2102ffd400b7f5002ff9400bfd50005f5400bfc50027fd0009fe40027f50009fc4001ffcc001fe30007f4c007fc30017fc8001fe20007f48005fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24006ff88120037dc409001bfc204800df61024002fe0812007ffe209001bfc104800dffb2c2006bfd9610037fccb08016fe658400dbf32c20059f99610037facb0803afd658400dbeb2c20009f59610037f8cb0801afc658400dffb242006bfd9210037fcc908012fe648400dfeb24200bbf59210037f8c90801afc6484017ffaa4200bdfd521005ffca90802ffd5484017beaa4200bff15210037fec70801aff638400dff31c2003bf98e10037fac708002fd638400dfe31c2006bf18e10077fea708037fe538401dfea9c200dff14e1005ffe8708037fe4384017fea1c200dff10e10037fec50801aff628400dff3142002bf98a10037fac508002fd628400dfe3142006bf18a10077fea508033fe528401dfea94200cff14a1005ffe8508033fe4284017fea14200cff10a1006ffe6508033fe3284001fe994200cff0ca1000dfac308007ff5184003ff28c2001ff5461000ff8a308007ff4184003ff20c2001ff5061000ff88308007ff3184003ff18c2001ff4c61000ff86308007ff2184003ff10c2001ff4861000ff8430801afe608400dffa842006dfd4210037fca10801bfd508400dbea842006ff14210037fe810801bfe408400dfd2042006ff5021005ff2810801bfc408400dff9842006ff8c210037fa610801bfc308400dff9042006ff88210037fa410801bfc208400dff8842006fdc421000ff6210801bfc108400dfc084200affd9510055feca8802bfe654400b7f32a200aff59510055faca8802bfc654400b7e32a2009ffd911004dfec888027fe64440097f3222009ff5911004dfac888027fc64440097e3222009ffd511004efea888027fe5444013feaa22009df5511004ff8a888003ff63440017fb1a2008ff98d1001dfcc688003fd63440017eb1a2008ff18d1001df8c68802bff5344011ff29a200aff54d10047f8a688027ff4344011ff21a2009ff50d10047f88688003ff62440017fb122007ff98910015fcc488003fd62440017eb122007ff18910015f8c48802bff524400fff292200aff5491003ff8a488027ff424400fff2122009ff5091003ff88488023ff324400fff1922000ff4c91003ff8648801aff6144003ffa8a2001ff9451000ffaa288007fc5144003ffa0a2001ff9051000fec8288007fd4144013faa0a2001ff1051000ffe6288007fe3144003fb18a2001ff4c510007ea6288007fc3144003ff90a2001ff8851000fec4288007fd2144001fa90a2001ff0851000dfec08802bff5044015bfa822006ff94110057faa0880037d504400dfe2822009ffd0110037fc8088027fa4044013fea022009fe50110037f88088023ff304400dff1822000ff4c110037f8608801fff204400dff1022000ff48110037f84088007ff1044003fd8822006ff84110037ec208801bfc104400dfa0822001fe04110
  | 1 => 0xffe214c001fe90a6017ff0853001dfec09806bff504c035bfa826006ff941300d7faa0980037d504c00dfe2826019ffd0130037fc8098067fd404c00dfe2026003ffcc13001ff6609801bfe304c00def1826006ff0c130037b8609800ff8304c031ff9026006ff081300bffe209801bfc104c00dffb2c4006bfd9620037fccb10016fe658800dbf32c40059f99620037facb1005afd658800dbeb2c40009f59620037f8cb1001afc658800dffb244006bfd9220037fcc910012fe648800dfeb244015bf59220037f8c91001afc648802bffaa44015dfd52200affca910057fd548802bbeaa44015ff15220037fec71001aff638800dff31c4003bf98e20037fac710002fd638800dfe31c4006bf18e200b7fea710053fe538802dfea9c4014ff14e200affe8710053fe438802bfea1c4014ff10e20015fac51000bff5288005ff2944002ff54a20017f8a51000bff4288005ff2144002ff50a20017f8851000bff3288005ff1944002ff4ca20017f8651001bff618800dff30c4001bf98620037fac310002fd618800dfe30c4006bf186200b7fea31004ffe518802dfea8c4013ff146200affe831004ffe418802bfea0c4013ff106200a7fe631004ffe3188001fe98c4013ff0c620017fe431000bfe2188005fe90c4002ff08620035fcc11001bff508800dbfa844006ff94220037faa11001b7d508800dfe2844006ffd0220037fc811001bfd408800dfe2044006ffcc220037fc611001bfd308800dfe1844006ffc8220037de411000bfb208800dfe1044006fe08220037fe211001bfc1088025ffb2a4012bfd9520097fcca90016fe6548025feb2a4012bf59520097f8ca90016fc6548023ffb224011bfd912008ffcc890012fe6448023feb224011bf5912008ff8c890012fc6448023ffaa24011dfd512008ffca890047fd5448023beaa24011ff15120007fec690002ff6348021ff31a4003bf98d20007fac690002fd6348021fe31a4003bf18d20097fea690043fe5348025fea9a4010ff14d2008ffe8690043fe4348023fea1a4010ff10d20035fec49000bff5248005ff2924002ff54920017f8a49000bff4248005ff2124002fb90920017fa8490047ed4248005fe2124002ffcc920017fc649000bee3248005fe9924000fb4c920017f86490003ff61480017fb0a400fff9852000dfcc290003fd614801ffe30a4001bf18520097fea29003ffe5148025fea8a400fff1452008ffe829003ffe4148023fea0a400fff10520087fe629003ffe3148001fe98a400fff0c520017fe429000bef2148005ff10a4002ff48520007da429000bfc21480057fb024012ffd4120096fea09001bfe5048025fea824000df54120037f8a090047ff404800dff2024011ff50120037f88090043ff304800dff1824000ff4c120037f8609000bff2048005fd9
  | 2 => 0x5010efcc6a80037d6354043be31aa022dfd0d5010efc86a808b7d4354043be21aa000dfd8950106fcc4a80037d6254041be312a022dfd0950106fc84a808b7d4254041be212a021dfcc950106fc64a80037d3254041be192a000dfd85500fefcc2a80037d615403fbe30aa022dfd05500fefc82a808b7d415403fbe20aa021dfcc5500fefc62a80037d315403fbe18aa020dfc85500fefc42a80037d215403fbe10aa005dfd815002cfec0a80177b6054045bfa02a006df90150116fa80a801b7c4054043bf982a006df0c150106fe40a801b7c205403fbf882a006df04150037fecb1801aff658c00dff32c6005bf99630036fccb180167e658c00dfeb2c601ebf59630036facb180027d658c00dfe32c6006bf19630037fec91801aff648c00dff3246004bf99230037fac918076fd648c00dfe3246006bf192300effea9180777f548c03bff2a4601dff552300eefaa918077fc548c0077eb1c6003ffd4e3001ffca71800ffd538c007fe29c6003ffd0e3001ffc871800ffd438c007fe21c6006ffd8a30037fcc51800afe628c00dfeb146000bf58a30037f8c51801afc628c03dffa94601cff94a300f7faa518073fc528c03bffa14601cff90a300effa8518073fc428c007ff9946003ff8ca3001ffa651800ffc328c00dffb0c6006ff9863000dfcc31801bfd618c0017eb0c6006ff18630035f8c31807bff518c037ff28c601eff546300dff8a318077ff418c037ff20c601dff506300dff8831800fff318c007ff18c6003ff4c63001ff86318073ff218c037ff10c6000ff486300dff8431801afe608c00dffa846006dfd4230037fca11801bfd508c00dbea846006ff14230037fe811801bfe408c00dfea046006ff10230037fe611801bdf308c007fd9846006ff0c230037f0611801bff208c00dfe1046006ffc4230037f8211806bff654c0357fb2a601aff9953002dfcca9806bfd654c0357eb2a601aff1953002df8ca98067ff644c0337fb226019ff99130025fcc898067fd644c0337eb226019ff19130025f8c898067ff544c033bfaa26019ff951300cffaa8980677d544c033fe2a26006bfd8d3001ffea69800ffe534c007fea9a6003ff14d3001ffe869800ffe434c007ef21a6003ff50d300cfba869800ffc434c001ffb126000bfd89300c7fcc49800afe624c001feb126018ff18930015f8c49806bff524c031ff292601aff549300c7f8a498067ff424c031ff2126019ff509300c7f8849800fff324c007ef9926003ff8c93001ffa6498003dd324c007fe1926000ffd8530005fec29805ffe614c0037f30a6000ff585300bff8c298006fc614c035ffa8a6017ff945300d7faa29805ffc514c033ffa0a6017ff905300cffa829805ffc414c007ff98a6003f7cc53001ffc629800ffd314c001ee98a6003ff0c5300c7fe429805
  | 3 => 0xe1826402ffc8132017de409900bfc204c853ff8826429ff04132147feca988a2ff654c401bfb2a62009fd9531147fcca98816fe654c451feb2a6228bf59531147f8ca98816fc654c451be32a62059f1953113ffec89889eff644c44fff3226204bf9913113ffac89889efd644c44ffe3226204bf1913113ffea89889f7f544c44fff2a26227ff5513113efaa89889ffc544c4037fb1a6203ffd4d31147bea69880ffe534c407fea9a6203ff14d3101fb8a69880fff434c407ff21a6203f790d3101ffa869889fdd434c407fe21a6200ffd8931005fec49889bfe624c4057f3126200ff58931137f8c49880afc624c451ffa926226ff94931147faa49889bfc524c44fffa126226ff9093113ffa849889bfc424c407ff9926203f7cc93101ffc649880ffd324c401ee9926203ff0c93100dfec298807ff514c403ff28a6201ff5453100ff8a298807ff414c403ff20a6201ff5053100ff88298807ff314c407fb98a6201ff8c53100fbc6298807fc314c403ee18a6201fd0c53100ffe4298807fe214c403fb10a6201ff08531007fec098802ff604c401ff3026200ff58131007f8c09881afc604c451ffa826228dfd4131147fca0988a3fd504c451fe2826227ffd013113ffc809889ffd404c44ffe2026203ffcc13101fbe609880ffc304c44dff9026226ff0813100ffe2098807f7104c403fe0826225ffd952112dfeca908037f65484013fb2a4225ff9952102dfcca90897fd654844b7eb2a4225ff1952102df8ca908977c654840b3e32a4224ffd9121125fec890893fe64484097f3224224ff59121125fac890893fc64484097e3224224ffd5121126fea890893fe5448449feaa24224df55121127f8a890803ff63484017fb1a4223ff98d2101dfcc690803fd63484017eb1a4223ff18d2101df8c690897ff5348447ff29a4225ff54d2111ff8a690893ff4348447ff21a4224ff50d2111ff88690806ff6248405ffa924225fbd4921017fca49080bfd5248405fe2924202fb14921017fe849080bfe4248405f72124202ff50921127da849080bfc4248405ff9924202ff8c921017dc649080bfd3248401f69924202ff0c92100dfec290807ff5148403ff28a4201ff5452100ff8a290807ff4148403ff20a4201ff5052100ff88290807ff3148403ff18a4201fd8c52100ffa6290803f53148403fe18a4201ffc8521017ee4290807fe2148403f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024206bf1812112ffea0908977f504844bff2824225ff5412112ff8a090893ff4048449ff2024224ff50121127f8809088fff3048447fe1824202ffc8121017de409080bfc2048403ff8824201fdc412100ff8209088b7f64540453fb22a022df99150116fac8a808a7d6454045be322a000dfd8d
  | 4 => 0x18080078ca700029a480a851b1495e6378001a2142121e03bb1440000037400065c2500000040c73b85000000002672b2aa4c78b96000000020d60e0d0458000ae000ae8c80001240401f000df0b18f126e36d938830000004f000000d45c41ff37ac48aa2232fe00065b9e12676d4e82d158d7d1ba60034aa04d2792aaa2c4e000630050000005fa09c80b1c2cc001a12b700002401000802006010038080040000000400803004003012010040000000140d00b000000008000000000001b00c04c020230000080200e0340040000b020000000040020040000003a004030260120240200f0080140680400801c0e8000060a00406700200c1f00e00e05000815000004098000840000c8170060000180200001c0801702600009800000008010070080480002c0000000180303800410020030074050070000000e81200003c00826002024058040040140000600e014030120060000680000000c0000200405c1f85800802c0780002c000008000000400280a018028128060240c4000000140040400100400c2c8060000140600000000c2500b0340100002200c0380a001000038040300060380002700202801832000014120050020040100401e0000200c00a040010010760100180d00002c09802034000040010cc0000280100602400000014008000050000000101300a0000080d008014008030060000000000405c000230040280200204600c0080100400003800006008000030000041180000c094090000000042d8000200040b0170000280c00300000c0d8010760000100700201c0500302e050030010000040200000000857ffb2a642bbfd9532006feca990027f654c857ff32a6405bf9953215ffaca990aefd654c857fe32a6405bf1953215ef8ca990167c654c855ffb22642abfd9132157fcc899012fe644c855feb22642abf59132157f8c899012fc644c855ffaa2642adfd5132157fca8990abfd544c855beaa2642aff15132015fec69900fff534c807ff29a6403ff54d3201ff8a69900fff434c807ff21a6403ff50d3201ff8869900aff624c805ffa926402ff94932017faa49900bfc524c805ffa126402ff90932017fa849900bfc424c805ff9926403fbcc932017fc649900bde324c805fe1926402f70c932017d8649900bcc324c801ffb0a6400bfd853214ffcc299006fe614c801feb0a6429ff1853200df8c2990afff514c853ff28a642bff5453214ff8a2990abff414c853ff20a642aff5053214ff8829900fff314c807ef98a6403ff8c53201ff8629900bff214c805f790a6402ff88532017f84299003ff604c8017fb026400ff98132007fac099003fc604c80d7e302642bffd413215efea0990affe504c857fea82642bff14132157fe80990abfe404c855fea02642aff1013201ffe609900fdf304c807f
  | 5 => 0x6cd640906e58c0000000061a9695524455e310078000008240014200045c00361000455612ab3e69fc00315000451cbaa5690001d58b57268780024f7589a01220f42cbc80023f548528152736443d11e8a56bce2d1a8000000000001c51c14529831222281e280000004181800000001d40004ca000a88d00001380010d03c3f0430ea000bd8cda48574e8c85918000df8beb4f48c194003af0004c1ac1da2bc4e09eba6000ba4df8d80e4001ce1d152e1e4f18b4000589c693e000668450e110491c5e83d000938203067980011983c462291600a37040005bb4518e000000004869a80000044c304e38410aa1150c92024a08978a131369e0000d71f0f442f2220009b42380021e0e5ae93219ee3d0636e30c239d38ae15a5ccd68005964e8f002e15ec680c251414ba19ea882a60d45591e000bb94036763e1cd6bbc9006000303284280dd6c12636e61d490bc47c2645d80037c319321c366800149a94582ed5b894101a21491000392e7d0e8923406e0ab98975c000a41fd1d02d8a7abe0fecc12a8002ec000dc8ce1babad4319c1ca1d96607523834d7bab6070634140006224b0f79a14002fdd996e778001e5a74000efc550006c8de9362c85b89f138800000754001772f26740024200097c0025014e2e84017b3b8000001dd4b2000bd0002d4700021e74340013580065800153b24112f080004d000548000dc3106f1990062d80019035440800000000666764ea0e43d257d810d26f2c3c76a777303add01d202cafc342ca58812d66bb438c3bca61b44720acf31f9570474d5000686dfc2da212b6bd47d0d63ae8c1b001328ace053206316d1dc880134e25d9fb700d65105f0fe320c214180009ee5400136680b79730004644c40034a7547289c8003cadac000004a86ac000005fc000e70000006440894d3a0a8d933631aa025143cd268428003357325596d34c152400e133c5b6c14ec3492207e08100000044d15000000cbc1639d62eaf52f06300000146b370320010804c24227d5ca990001492c1ee11a0016b33a0ee86c99800000dc8010000009ed6f898772e109724d45eb1d2083055a369102d05daa31be93b448808c52e71a8250798661d2e289499e5a4c29ae1271c41bcfe2fa6562a1bbbbd22c6c95a80050a68db3000000001d68000004b50e1e22181f540b3b3d81850710e0007d48c83b4986bd8f12334c1e9d2905540e0ccfb550ac108000460a698400000086a3c0011b0000011c069000b0c003b00005c8002d4000ec80008c000001588900008ed1e3b14dce89dc11a0005684389679c01ca3128458d48b5afc2126103d9966da87ce60b30425840b85801c3ed3f3756d26b93d0887343993aa76616e001f0ec36ab946f9df30ae482e0c9468638f6b5042e89c7bbc36f6d69898360001b4002455c6e38e41c4256
  | 6 => 0x3f65acc4d2304000000058000b4a4101800788c25b5000186000b3a870f0b900534455ca1148a2b2867c92585d7744a85c36202a5d4dda890e05d0d62c541000000257366000002153ec4bcef000000a7cb206c592140000ca2b000047abb000000103b70000000009d2da924000003acd190933e26a948b89fe0004f0f0af92f082c890004c6580b2968568815751503d01912ea2e4fae6cf5ba92de7c16a8b22d2a29862256a6ac8a002562c9986cad93c8bec7b05f742a6c6110643074c701ea39ee31ab92420e7c5b7b1b7a0b3c2cb2310251c0025b1e47ed8834e652661c49823521c47e9f739ad04db394422715780003608040035b160af151180180e91e42a6632ac0ccb395581f8e095c79e60d34b254949c94b390350334b82074e0b75698323e838da583a504d35711a52fce054c2f44dede114b563746c570a9e5d8651688264ac189bb36c0881a814b650e80cd4a8f55f008c62b68036c847f9811f23b97000c63a6499b1fa0a8001e39087821f159aef32a000822ff396ef9c322d72ccb802b871622118a23a4c40bc0ebca0ce5387832a23e4fc48b7300064c6625c59c0000014b0005f000000000001870d112a630000007
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc75589100067c755891002c7c7558910004ff7458910006bf7458910004bf7458910024fe7458910004fd7458910024fc7458910006bc7458910024bc74589100067f54589100067d5458910004ff7358910006df7358910004df735891001cfe735891001cfc7358910006dc735891001cdc735891009cff7258910006ef725891003eee4258910006ed425891003eee325891007cff7158910006f7715891007ef631589101a4ff7058910006fb70589100067f5058910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100557c754c91001ede634c910006dd634c910016ee624c910006ed624c91003fcc324c91000df6714c910035f4764c51001ef4764c510034f4764c51000777754c51019774754c51019df7744c51019df5744c51018f77544c51018f75544c51000df7734c51000fd7734c510007d7634c51001ef6634c51001ef4634c510047d4634c510197d7534c510047d4534c510047d6434c51018fd5434c510005f7724c510006f7624c510006f5624c510047d7324c510007d5324c510007f3704c510035f6704c510035f4704c510007f0704c51000ef7604c51000ff3604c51019777504c51018ff2404c51018ff1404c510047d7304c510035f47648510016f47648510034f4764851000777754851017f747548510185f77448510185f57448510177775448510177755448510005f77348510005f57348510006f76348510006f5634851000df7724851000fe77248510007e76248510016f66248510016f4624851003fe4624851017fe7524851003fe4524851003fe64248510177e5424851003fe63248510007e53248510007f37048510035f67048510035f47048510007f0704851000ef7604851000ff3604851017f775048510177f24048510177f1404851003fe7204851002e7f76541100fe7e76541100fe7d765411002e7c765411016d7f745411016d7d74541101667f64541101167e64541101667d64541101167c64541100067f635411010e7e63541100067d635411010e7c63541100067f62541101067e62541100067d62541101067c62541100077771541100ff7471541100367f61541100ff7641541101677541541100ff7631541100077531541100ff7621541100077521541100357f70541100577b70541100367f60541100377a40541101677940541100377a30541100377a20541100ff7b105411003776105411003774105411003778105411003770105411001cff764c11000cfe764c1100bcfd764c11000cfc764c110006df634c11001edc634c110005f7714c11000df4714c110007d5314c11000779504c110014ff764811000cfe764811007cfd764811000cfc7648110006ef6248110016ec6248110005f7714811000df47148110007e52148110007795048110
  | 1 => 0x8e1006edf3258e100bedf3158e100bedd3158e10034ff7058e10034fe7058e10034fd7058e10034fc7058e100367f5058e100367d5058e10036de3058e10036dc3058e10036f71058e10036f51058e10004ff7558a1002cfe7558a10004fd7558a1002cfc7558a10004ff7458a10024fe7458a10004fd7458a10024fc7458a100067f5458a100067d5458a10004ff7358a1001cfe7358a1001cfc7358a10036ef7258a10066ee4258a10006ed4258a10066ee3258a1007eef2158a1007eed2158a10034ff7058a10034fe7058a10034fd7058a10034fc7058a100367f5058a100367d5058a10036ee2058a10036ec2058a10036f71058a10036f51058a10004ff764ca10034fe764ca10004fd764ca10034fc764ca100057f754ca100757c754ca1015e7e654ca100067d654ca1001ede634ca10006dd634ca10016ee624ca10006ed624ca10067cc324ca1001cfe76d8d10046de63d8d10004ff75d8d1002cfe75d8d10004fd75d8d1002cfc75d8d10004ff74d8d10024fe74d8d10004fd74d8d10024fc74d8d100067f54d8d100067d54d8d10014fe72d8d10004fd72d8d10014fc72d8d10006de32d8d10046dc32d8d10034ff71d8d1000cfe71d8d10034fd71d8d1000cfc71d8d100dedf31d8d100dedd31d8d100def621d8d10034fe70d8d1000cfd70d8d10034fc70d8d100067f50d8d10046df30d8d100057f7558d100557c7558d10005bf7458d1004dbc7458d10046dc6358d10005ef7258d1003dec7258d101adfb7058d10004ff7558d100067f7558d100047f7558d1002cfe7558d10004fd7558d1002cfc7558d100067c7558d1002c7c7558d10004ff7458d10006bf7458d10004bf7458d10024fe7458d10004fd7458d10024fc7458d10006bc7458d10024bc7458d100067f5458d100067d5458d100dcff7358d10006df7358d10046de4358d10006dd4358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d10046df3258d100bcff7158d10006f77158d100bef62158d101acff7058d10006fb7058d100067f5058d10014fe76d891003eee62d8910004ff75d891002cfe75d8910004fd75d891002cfc75d8910004ff74d8910024fe74d8910004fd74d8910024fc74d89100067f54d89100067d54d891001cfe73d8910004fd73d891001cfc73d8910006ef32d891003eec32d8910034ff71d891000cfe71d8910034fd71d891000cfc71d891009ef631d891009eef21d891009eed21d8910034fe70d891000cfd70d8910034fc70d89100067f50d891003eef20d89100057f75589100557c7558910005bf745891004dbc7458910005df7358910045dc735891003eec62589101a5fb7058910004ff75589100067f75589100047f755891002cfe7558910004fd755891002cf
  | 2 => 0x85dc735852007ef461585201ddfb7058520004ff764c520004fe764c520004fc764c5200057f754c5200957c754c52001ede634c520006dd634c520015ee724c520007cd324c52000ef6614c520035ec764852000eec7648520034ec76485200076f75485201c76c754852012eee654852012eec65485201d5ef74485201d5ed74485201ceef64485201ceed64485201cf6f54485201cf6d5448520005ef7348520005ed7348520006ef6348520006ed6348520015ef7148520017e77148520007e7614852000eee614852000eec614852007fe4614852007fe63148520007e53148520007eb7048520035ee7048520035ec7048520007e87048520016ef6048520017eb60485201c76f504852007fe7104852002e7f76541201067e76541201067d765412002e7c76541201bd7f74541201bd7d74541201b67f64541201167e64541201b67d64541201167c64541200067f635412010e7e63541200067d635412010e7c63541200076f72541201076c72541200367f62541201076e42541201b76d42541201076e32541200076d32541200067f61541200fe7e61541200fe7c61541201076f21541200076d21541200357f70541200977b70541200367f60541200377a30541201077b20541200376e20541200376c20541200377820541200376820541200377a105412001cff764c120014fe764c1200c4fd764c120014fc764c120006df634c12001edc634c120005ef724c120015ec724c120007cd324c12000779504c1200067f74596100047f74596100067e74596100067d74596100047d74596100067c74596100067f73596100067e73596100067d73596100067c73596100067f43596100067e43596100067d43596100067c43596100067f72596100067e72596100067d72596100067c72596100067f42596100067e42596100067d42596100067c42596100067f32596100067e32596100067c32596100fe7f71596100fe7e71596100fe7d71596100fe7c71596100fe7f41596100fe7e41596100fe7d41596100fe7c41596100fe7f31596100fe7e31596100fe7d31596100fe7c31596100fe7f21596100fe7e21596100fe7d21596100fe7c21596100367f70596100347f70596100367e70596100367d70596100347d70596100367c70596100367f40596100367e40596100367d40596100367c40596100367f30596100367e30596100367d30596100367c30596100367f20596100367e20596100367d20596100367c20596100367f10596100367e10596100367d10596100367c1059610004ff7558e1002cfe7558e10004fd7558e1002cfc7558e10004ff7458e10024fe7458e10004fd7458e10024fc7458e100067f5458e100067d5458e10036df7358e1006ede4358e10006dd4358e10004ff7258e10014fe7258e10014fc725
  | 3 => 0xf3158e20034fe7058e20034fc7058e200367f5058e200367d5058e20036de3058e20036dc3058e20036ef2058e20036ed2058e20004ff755862002cfe7558620004fd755862002cfc7558620004ff7458620024fe7458620004fd7458620024fc74586200067f54586200067d5458620004ff735862001cfe735862001cfc7358620036f7715862009ef64158620006f5415862009ef6315862009ef6215862003ef52158620034ff7058620034fe7058620034fd7058620034fc70586200367f50586200367d5058620036ef2058620036ed2058620036f61058620036f41058620004ff764c620004fd764c620034fc764c6200057f754c6200b57c754c6201467e654c6200067d654c62001ede634c620006dd634c620005ef724c620015ec724c62000ef6614c620006f5614c62001cfe76d8d20086de63d8d20004ff75d8d2002cfe75d8d20004fd75d8d2002cfc75d8d20004ff74d8d20024fe74d8d20004fd74d8d20024fc74d8d200067f54d8d200067d54d8d20006df53d8d20086dc53d8d20086de43d8d20006dd43d8d20034ff72d8d20014fe72d8d20034fd72d8d20014fc72d8d200e6df32d8d200e6dd32d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006de31d8d20086dc31d8d200e6ef21d8d20014fd70d8d200067f50d8d20086df30d8d200057f7558d200957c7558d20086dc6358d201fdfb7058d20004ff7558d200067f7558d200047f7558d2002cfe7558d20004fd7558d2002cfc7558d200067c7558d2002c7c7558d20004ff7458d20024fe7458d20004fd7458d20024fc7458d200067f5458d200067d5458d200e4ff7358d20006df7358d200c4ff7258d20006ef7258d20004ff7158d2000cfe7158d2000cfc7158d20086df3158d200c6ef2158d201fcff7058d20006fb7058d200067f5058d20035ec764c92001eec764c920034ec764c9200076f754c9201e76c754c9201f5ef744c9201f5ed744c9201ef6f544c9201ef6d544c920015ef734c920017cf734c920007cf634c92001eee634c92001eec634c920087cc634c92001ecc634c920005ef714c920087cf314c920007eb704c920035ee704c920035ec704c920007e8704c920016ef604c920017eb604c9201e76f504c920087cf304c92000cfe76d852007ef661d8520004ff75d852002cfe75d8520004fd75d852002cfc75d8520004ff74d8520024fe74d8520004fd74d8520024fc74d85200067f54d85200067d54d852001cfe73d8520004fd73d852001cfc73d8520034fd72d852000cfc72d8520066ee42d8520006ed42d8520066ee32d8520006ed32d852007ef621d8520066f521d8520034fe70d8520014fd70d8520034fc70d85200067f50d852007ef710d85200057f75585200957c7558520005bf745852008dbc7458520005df7358520
  | 4 => 0x853006edf32d8530006dd32d85300bef631d853006ef531d853001cfd70d85300067f50d85300bef710d85300057f75585300d57c7558530005bf74585300cdbc7458530005ef72585300c5ec72585300bef4615853022dfb7058530035dc764c53000edc764c530034dc764c5300075f754c5302175c754c530146de654c530146dc654c530225df744c530225dd744c53021edf644c53021edd644c53021f5f544c53021f5d544c530005df724c530006df624c53001ddf714c53001fd7714c530007d7614c53000ede614c53000edc614c5300bfd4614c5300bfd6214c530007db704c530035de704c530035dc704c530007d8704c53001edf604c53001fdb604c5302175f504c5300bfd7104c530004ff7648530004fe7648530004fc76485300057f75485300d57c754853001dde7348530005dd7348530016ee6248530007cd324853000ef66148530007d5314853002e7f765413010e7e765413010e7d765413002e7c765413020d7f745413020d7d74541302067f64541301167e64541302067d64541301167c64541300075f735413010f5c73541300367f635413010f5e43541302075d43541300067f62541301067e62541301067c625413010f5f32541300075d32541300067f61541300fe7e61541300fe7c615413010f5f31541300075d31541300357f70541300d77b70541300367f605413010f7b30541300375e30541300375c30541300377830541300375830541300377a20541300377a10541300067f74596200047f74596200067e74596200067d74596200047d74596200067c74596200067f73596200067e73596200067d73596200067c73596200067f43596200067e43596200067d43596200067c43596201067f72596201067e72596201067d72596201067c72596201067f42596201067e42596201067d42596201067c42596201067f32596201067e32596201067d32596201067c32596200067f71596200067e71596200067d71596200067c71596200067f41596200067e41596200067d41596200067c41596200067f31596200067e31596200067c31596201067f21596201067e21596201067d21596201067c21596200367f70596200367e70596200367d70596200367c70596200367f40596200367e40596200367d40596200367c40596200367f30596200367e30596200367d30596200367c30596200367f20596200367e20596200367d20596200367c20596200367f10596200367e10596200367d10596200367c1059620004ff7558e2002cfe7558e20004fd7558e2002cfc7558e20004ff7458e20024fe7458e20004fd7458e20024fc7458e200067f5458e200067d5458e20036df7358e200a6de4358e20006dd4358e200c6df3258e200c6dd3258e20004ff7158e2000cfe7158e2000cfc7158e200a6d
  | 5 => 0x10e7e315963010e7d315963010e7c31596300067f21596300067e21596300067c21596300367f70596300367e70596300367d70596300367c70596300367f40596300367e40596300367d40596300367c40596300367f30596300367e30596300367d30596300367c30596300367f20596300367e20596300367d20596300367c20596300367f10596300367e10596300367d10596300367c1059630004ff7558a3002cfe7558a30004fd7558a3002cfc7558a30004ff7458a30024fe7458a30004fd7458a30024fc7458a300067f5458a300067d5458a30036ef7258a300e6ee4258a30006ed4258a300e6ee3258a30086ed3258a30004ff7158a3000cfe7158a3000cfc7158a300e6ef2158a30034fe7058a30034fc7058a300367f5058a300367d5058a30036df3058a30036dd3058a30036ee2058a30036ec2058a30004ff755863002cfe7558630004fd755863002cfc7558630004ff7458630024fe7458630004fd7458630024fc74586300067f54586300067d5458630004ff7258630014fe7258630014fc7258630036f771586300def64158630006f541586300def63158630046f531586300def62158630034fe7058630034fc70586300367f50586300367d5058630036df3058630036dd3058630036f61058630036f41058630004ff7648630004fd7648630034fc76486300057f75486300f57c754863012e7e65486300067d6548630005df734863001ddc7348630016ee6248630006ed624863000ef66148630006f56148630014fe76d89300c6ee62d8930004ff75d893002cfe75d8930004fd75d893002cfc75d8930004ff74d8930024fe74d8930004fd74d8930024fc74d89300067f54d89300067d54d8930034fd73d8930014fc73d8930006ef52d89300c6ec52d89300c6ee42d8930006ed42d89300c6ee32d89300a6ed32d893000cfe71d8930004fd71d893000cfc71d89300a6df31d8930006ee21d89300c6ec21d893001cfd70d89300067f50d89300c6ef20d89300057f75589300d57c75589300c6ec625893024dfb7058930035dc764c930016dc764c930034dc764c9300075f754c9302375c754c930245df744c930245dd744c93023f5f544c93023f5d544c93001ddf724c93001fcf724c930007cf624c930016de624c930016dc624c9300c7cc624c930016cc624c930005df714c9300c7cf214c930007db704c930035de704c930035dc704c930007d8704c93001edf604c93001fdb604c9302375f504c9300c7cf204c93000cfe76d85300bef661d8530004ff75d853002cfe75d8530004fd75d853002cfc75d8530004ff74d8530024fe74d8530004fd74d8530024fc74d85300067f54d85300067d54d8530034fd73d853000cfc73d853006ede43d8530006dd43d8530014fe72d8530004fd72d8530014fc72d
  | 6 => 0xc324c9501076c324c9501074c324c9500057f714c9500fd7e714c9500fd7c714c95010f5f314c9501076f214c9500057f704c9500357e704c9500357c704c9502867f604c95015f7b604c95010f5f304c9501076f204c9500fd7e76d85500057f74d85501157e74d85500057d74d85501157c74d85500067f64d85500067d64d855010d7e73d85500057d73d855010d7c73d85501057e72d85500057d72d85501057c72d85500fe7e61d85500ff7661d85500fe7c61d85500077741d85500ff7441d85500357e70d855002d7d70d85500767f60d85500777b60d85500ff7710d85500057f74585501157e74585500057d74585501157c74585500067f64585500067d64585500057f735855010d7e735855010d7c73585500057f72585501057e72585501057c72585500fd7f71585500077761585500fe7e61585500fe7c61585500ff74615855027d7f70585500077b705855027d7b70585500567f60585500577b60585500057f764c5500067f764c5500047f764c5500057e764c5500057d764c5500057c764c5500067c764c5500047c764c5502757f744c5501157e744c5502757d744c5501157c744c55026e7f644c55026e7d644c5500fd7f734c5500075f634c55010f5c634c55010f5e434c55026f5d434c5500057f724c5501057e724c5501057c724c55010f5f324c5500075d324c5500fd7f714c55010f77314c5500ff5e314c5500ff5c314c5500ff74314c5500ff76214c5500057f704c5500357e704c5500357c704c5502567f604c5501477b604c55010f5f304c5500ff77104c5500057f76485500067f76485500047f76485500057e76485500057d76485500057c76485500067c76485500047c76485502657f74485501157e74485502657d74485501157c744855025e7f644855025e7d64485500057f734855010d7e73485500057d734855010d7c73485500fd7f72485500076f62485501076c62485501076e424855025f6d42485501076e32485500076d32485500fd7f71485500ff7631485500077531485501077721485500ff6e21485500ff6c21485500ff7421485500057f70485500357e70485500357c70485502567f604855012f7b60485501076f20485500ff7710485500067f74596300047f74596300067e74596300067d74596300047d74596300067c745963010e7f735963010e7e735963010e7d735963010e7c735963010e7f435963010e7e435963010e7d435963010e7c43596300067f72596300067e72596300067d72596300067c72596300067f42596300067e42596300067d42596300067c425963010e7f325963010e7e325963010e7d325963010e7c32596300067f71596300067e71596300067d71596300067c71596300067f41596300067e41596300067d41596300067c415963010e7f3159630
  | 7 => 0x8121004fd75d812102cfc75d81210067c75d812102c7c75d8121004ff74d8121024fe74d8121004fd74d8121024fc74d81210067f54d81210067d54d812101cfe73d8121004fd73d812101cfc73d812100cfd72d81211deee42d8121006ed42d81211deee32d8121006ed32d8121014fd71d81211a6f631d8121006f531d81210067f50d81211defa20d81211a6fa10d812112d7e75981210057d75981210067f65981210067c6598121006fb60981210057f755812112d7c75581210067f65581210067c6558121005bf7458121125bc7458121005df735812111ddc735812112d7e75181210057d75181210067f65181210067c6518121125be7418121005bd741812111dde7318121005dd7318121036fa6018121006f9601812110d7e76d8d500057f74d8d501157e74d8d500057d74d8d501157c74d8d500067f64d8d500067d64d8d5010e7e63d8d5010f5e63d8d5010e5e63d8d5010e7c63d8d500075f43d8d5010f5c43d8d501057e72d8d500057d72d8d501057c72d8d500075e32d8d5010f5c32d8d500fd7e71d8d500057d71d8d500fd7c71d8d5010f5f31d8d500357e70d8d5002d7d70d8d500f67f60d8d500f77b60d8d5010f5f30d8d500057f7458d501157e7458d500057d7458d501157c7458d500067f6458d500067d6458d5010d7f7358d500075f6358d5010e7e6358d5010e7c6358d5010f5c6358d500057f7258d500076f7258d500056f7258d501057e7258d501057c7258d500076c7258d501056c7258d500057f7158d500fd7e7158d500fd7c7158d502a57f7058d500077b7058d502a57b7058d500d67f6058d500d77b6058d501057e76d89500057f74d89501157e74d89500057d74d89501157c74d89500067f64d89500067d64d895010d7e73d89500057d73d895010d7c73d89501067e62d89501076e62d89501067c62d89500076f42d89501076c42d89500076f32d89501076c32d89500fd7e71d89500057d71d89500fd7c71d89501076f21d89500357e70d895002d7d70d89500b67f60d89500b77b60d89501076f20d89500057f74589501157e74589500057d74589501157c74589500067f64589500067d64589500057f73589500075f73589500055f735895010d7e735895010d7c73589500075c735895010d5c73589501057f72589500076f62589501067e62589501067c62589501076c62589500057f71589500fd7e71589500fd7c715895029d7f70589500077b705895029d7b70589500967f60589500977b60589500057f764c9500067f764c9500047f764c9500057e764c9500057d764c9500057c764c9500067c764c9500047c764c9502957f744c9501157e744c9502957d744c9501157c744c95028e7f644c95028e7d644c9501057f734c9501057f724c95010f6f324c9501075e324c9501075
  | 8 => 0x2f67f31d95212f67e31d95212f67d31d95212f67c31d95212f67f21d95212f67e21d95212f67d21d95212f67c21d95210067f70d95210067e70d95210067d70d95210047d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95210067f30d95210067c30d95212fe7f20d95212fe7e20d95212fe7d20d95212fe7c20d95212f67f10d95212f67e10d95212f67d10d95212f67c10d952101cfe76d8d210067f65d8d210067c65d8d2111ede63d8d21004ff75d8d2102cfe75d8d21004fd75d8d2102cfc75d8d21004ff74d8d21024fe74d8d21004fd74d8d21024fc74d8d210067f54d8d210067d54d8d2114cfd73d8d2111ede43d8d21006dd43d8d2100cff72d8d2100cfd72d8d212eedf32d8d212eedd32d8d21014ff71d8d21014fd71d8d212dedf31d8d212dedd31d8d21034fe70d8d21004fd70d8d210067f50d8d2111edc30d8d212eeef20d8d212def710d8d2101cff7658d210057f7558d2112d7c7558d210067f6558d210067c6558d2111edc6358d212d5ef7258d212e5f77158d21004ff7558d210067f7558d210047f7558d2102cfe7558d21004fd7558d2102cfc7558d210067c7558d2102c7c7558d21004ff7458d21024fe7458d21004fd7458d21024fc7458d210067f5458d210067d5458d212dcff7358d21006df7358d212d4ff7258d21006ef7258d2114cff7158d21006f77158d21004ff7058d21034fc7058d210067f5058d2111edf3058d21136ef2058d2114ef71058d2100dec764c92101eec764c92100cec764c9210076f754c92112dee754c92112dec754c9212bf6c754c92112d6c754c9210076f654c9212bf6c654c9212cdef744c9212cded744c9212c76f544c9212c76d544c921015ef734c921017cf734c921007cf634c92101eee634c92101eec634c92111fcc634c92101ecc634c921007e7714c92100dee714c92100dec714c92114fe4714c921016ef614c921017e7614c92114fcf314c92114fe6314c92114fcd314c921005ef704c9212bf6f504c92111fcf304c92114fe7104c921015f4764c52101ef4764c521014f4764c52100777754c5212af74754c52100777654c5212af74654c5212b777544c5212b775544c52100df7734c52100fd7734c521007d7634c52101ef6634c52101ef4634c52111fd4634c5212afd7534c52111fd4534c52111fd6434c5212b7d5434c521007e7724c521015f6724c521015f4724c521137e4724c52100ef7624c52100fe7624c5212afe7524c521137e4524c521137e6424c5212b7e5424c521137d7324c521137e6324c521137d5324c52111fe5324c521007c5324c521005f7704c5212af77504c52111fd7304c521137e7204c521034fe76d812112d7c75d81210067f65d81210067c65d8121004ff75d81210067f75d812102cfe75d
  | 9 => 0xf74d8931024fe74d8931004fd74d8931024fc74d89310067f54d89310067d54d893100cfd73d8931136ee42d8931006ed42d8931136ee32d893132eed32d893101cfd71d89312d6ef21d8931034fe70d8931004fd70d89310067f50d893132edf30d8931136ec20d89312d6f710d89310057f75589311457c75589310067f65589310067c6558931136ec6258931325f7715893100ddc764c931016dc764c93100cdc764c9310075f754c931145de754c931145dc754c93130f5c754c9311455c754c9310075f654c93130f5c654c93131ddf744c93131ddd744c9313175f544c9313175d544c93101ddf724c93101fcf724c931007cf624c931016de624c931016dc624c931137cc624c931016cc624c931007d7714c93100dde714c93100ddc714c93114fd4714c93101edf614c93101fd7614c93114fcf214c93114fd6214c931005df704c93130f5f504c931137cf204c93114fd7104c931034fe76d81311457c75d81310067f65d81310067c65d8131004ff75d81310067f75d813102cfe75d8131004fd75d813102cfc75d81310067c75d813102c7c75d8131004ff74d8131024fe74d8131004fd74d8131024fc74d81310067f54d81310067d54d813100cfd73d813122ede43d8131006dd43d8131014fe72d8131004fd72d8131014fc72d813122edf32d8131006dd32d813101cfd71d81311aef621d81310067f50d813122efa30d81311aefa10d81311457e75981310057d75981310067f65981310067c6598131006fb60981310057f75581311457c75581310067f65581310067c6558131005bf745813113dbc7458131005ef7258131135ec72581311457e75181310057d75181310067f65181310067c651813113dbe7418131005bd7418131135ee7218131005ed7218131036fa6018131006f960181313057e76d952112e7e76d952102c7e76d95210057f74d95210057d74d95210067f64d95210067e64d95210067d64d95210067c64d95210067e63d95210067c63d95212ff6e72d95212f76d72d95212ff6e42d95210076d42d95212ff6e32d95212f77631d95212ff7721d95212f76e21d95212f76c21d95212f77421d95210057d70d95212ff6f20d95212f77710d95210067f74d95210047f74d95210067e74d95210067d74d95210047d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95212f67f72d95212fe7e72d95212fe6e72d95212f67d72d95212f66d72d95212f67c72d95212fe7f42d95212fe7e42d95212fe7d42d95212fe7c42d95212fe7f32d95212fe7e32d95212fe7d32d95212fe7c32d95212f67f71d95212f67e71d95212f67d71d95212f67c71d95212f67f41d95212f67e41d95212f67d41d95212f67c41d9521
  | 10 => 0x8532004ff75d853202cfe75d8532004fd75d853202cfc75d8532004ff74d8532024fe74d8532004fd74d8532024fc74d85320067f54d85320067d54d8532014fd73d853201cfd72d853214ef631d853214ef621d8532034fe70d8532004fd70d85320067f50d8532326df30d85322e6ef20d85320057f755853215d7c75585320067f65585320067c6558532137cc325853214ef46158532034fe76d813215d7c75d81320067f65d81320067c65d81321ffcc32d8132004ff75d81320067f75d813202cfe75d8132004fd75d813202cfc75d81320067c75d813202c7c75d8132004ff74d8132024fe74d8132004fd74d8132024fc74d81320067f54d81320067d54d8132014fd73d813201cfd72d813200cfe71d8132004fd71d813200cfc71d813224edf31d81321feef21d81320067f50d813224efa30d81321fefa20d813215d7e75981320057d75981320067f65981320067c65981320e7cc3298132006fb60981320057f755813215d7c75581320067f65581320067c65581320c7cc325813215d7e75181320057d75181320067f65181320067c6518132155be7418132005bd741813234fcc321813214df67118132005f57118132036fa6018132006f960181323457e76d95311467e76d953102c7e76d95310057f74d95310057d74d95310067f64d95310067e64d95310067d64d95310067c64d953133f5e73d95313375d73d953133f5e43d95310075d43d95310067e62d95310067c62d953133f5f32d953133f7731d95313375e31d95313375c31d95313377431d95313377621d95310057d70d953133f5f30d95313377710d95310067f74d95310047f74d95310067e74d95310067d74d95310047d74d95310067c74d95313367f73d953133e7e73d953133e5e73d95313367d73d95313365d73d95313367c73d953133e7f43d953133e7e43d953133e7d43d953133e7c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067d42d95310067c42d953133e7f32d953133e7e32d953133e7d32d953133e7c32d95313367f71d95313367e71d95313367d71d95313367c71d95313367f41d95313367e41d95313367d41d95313367c41d95313367f31d95313367e31d95313367d31d95313367c31d95313367f21d95313367e21d95313367d21d95313367c21d95310067f70d95310067e70d95310067d70d95310047d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d953133e7f30d953133e7e30d953133e7d30d953133e7c30d95310067f20d95310067c20d95313367f10d95313367e10d95313367d10d95313367c10d9531014fe76d89310067f65d89310067c65d8931136ee62d8931004ff75d893102cfe75d8931004fd75d893102cfc75d8931004f
  | 11 => 0x100300200100200400600000600200500000300901801300400100203f00000900001b00700500301100000900700000400000700100400101100000500000000b01300400300600100000200200500800a02d00000300400900b00500000a00900701201801800300600000c00b00000400000300001300000500300302600100100000000300c01100000400000500900200300000201700400002803600000400900600200200001901e00100000600300100000000a01800a00600500000200a00300700800000300403601c00800000100101000000700201400600100300800101a00700000700700200703200100300000800000400900300404700600000202200701202800d00102b01a00900003c01300400000401902503300d00200000700400000e00400400000000000800400200601102000e00800500000100b00200400000000101c00200700d00a02700500100004200500001a00a00003a01a00102100000000800d00000201100500800f00a00503700800100000100300500a00800400400e00101900000100501a00a00900c00000000100100b01700600d01501201e00500e00100b02000000200000000000300700001100000700e00100101101300000200500100f00000800900001301800501002f01400a00a00000b00000702100c01802200000b0100010060000193657e76d953215e7e76d953202c7e76d95320057f74d95320057d74d95320067f64d95320067e64d95320067d64d95320067c64d953235f6f32d95323575e32d95323575c32d95323576c32d95323574c32d95320067e61d95320067c61d953235f5f31d95323576f21d95320057d70d953235f5f30d95323576f20d95320067f74d95320047f74d95320067e74d95320067d74d95320047d74d95320067c74d95323567f73d953235e7e73d95323567d73d95323567c73d953235e7f43d953235e7e43d953235e7d43d953235e7c43d95323567f72d95323567e72d95323567d72d95323567c72d95323567f42d95323567e42d95323567d42d95323567c42d95323567f32d95323567e32d95323567d32d95323567c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067e41d95320067d41d95320067c41d953235e7f31d953235e7e31d953235e7d31d953235e7c31d95323567f21d95323567e21d95323567d21d95323567c21d95320067f70d95320067e70d95320067d70d95320047d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d953235e7f30d953235e7e30d953235e7d30d953235e7c30d95323567f20d95323567e20d95323567d20d95323567c20d95320067f10d95320067c10d953200cfe76d85320067f65d85320067c65d85322e7cc32d853214ef661d
  | 12 => 0x6ac3c5988688de03aa56a0ea4237214616662073e000416596000824424d7a0089d681ceca056c3aefa7c8438bec4bc5262804de09ed5ebae50e1e46747b07fee782760220000009da3bc26e9a00007100000008c00003be0000002a25aa440000000000874bb40003e6cc44f83da000000b76b2ee3a772000f463680a6000000e086eaa721766401003d4000000f2cdb8b8c00007200030c7ba1880700005b0de62c26908b20009509cc0000008c600027e250a369cec66000210cd698c000000e3407ce00000000c06e620000d4000d80418a5a6f6000654d946600006e445a0b2000d7e8a40000007840000001b600012407e47aad48b4c2239a7a400077e8c4eba09216ea7e6425ae718580060b6e80a000966000000bac000a0a000918738ba629ac5a1d8ab0b0cf1a9ee162074b969a458eee46ae3b4a600d84a42b4b4046ab52460bc62941745b81f4488de8b1294847084c00013e000ed08e64aaabac76102ce4b7202a770d9cc26b9487c0000007809d25ca0e4a008089ec00a000f2e5acae20000cc8aa0008d65f4f20e2a34ad9a84e000f40b5a3345520008440aaa2078c32ca9ab802d2b46866dc0894262108aa23643ce78660c30e670b9ad5478ad3863c6e2646b56000e246c46d6c82d0a0004d662c9f8d580cab78a96308d6c4eab740007503ba1329a819a65c000d766069e0f262b6876c2c248dfe00084298e0007ae7405142cacaa23e22e32ac0c000930bd21d66c2a4ed3253c00040021842600100b00500000b00400200002d00600101800400000100000000300100100000200e00000300100100300400604a00500200001500000000800200500802d02300600600104c00500400f00c00000f00701700300700100102500500102900100b00a04700900100000b00100000300600100c00300000300901400000300101000700000101c00200c00001f00300000a00d00400201a00100400e00002c02400000500d00100b00000101301400400e00e00c00000900000801900800000400e00100e01801900700000c00600900500101a00000b00200a00000700601700100100002900002b00900100200100000a00900000000000000000b00600000b00200f00003200005001a00100100100f00100001100000501100100100100200004700200000001800800c00000500000e00400100d0010010010040000010060000450a500000000000600702400300000201900003200900000000f00a00200902900200800d00900600200900100200c00300000b00200100000501600101c00006500002100700000003c00400200600000000500000002100200500900300900903500000100a01a00800300000200101400200000000202000c00c00500201500001300100a01301d00500300002101000000100000f003010
  | 13 => 0xee1068e06672a5dea80a30cb20000000000000000001e80007aa000bd6000a885560004f6096356000000be6000d5ce48000df40000001580acc0400000000063a000000d569525a86f80007b25bebc8c6059c1c2270f12e901423b2a22d60000858de039204aa0ceb8354e74c9a6e67c04109449966a83aa00004e716000b2ae941ca8a2822c9e2da96474c7d8000000d1690e000a980003eaf22eb4e6cf520002b812c87224ea34eeca1c5c894c006562d90000ab42020000005d0a481dc1983f80dcdcae80762806000cb0c843a856059028ed9261a9c0000000000382bda00070a4520b045e0000da73c0004f0000000000a904e6f0a000a02126000746000140ac84b8000000000d123ae0000009f290818e9360005100000007ca0009dc0004ae0000000000be4cc0004c200037a0005706a62e2000000000000000668b184b433a0f26fe0006a20001226dce141deafeae6a102a45fc93a0007dc94e350b168b6dd603825472c92a4ce000000000c48000000db47244eef16540000532902e82bdecc27567be09c016320f1478eea23ca736c4608a24c87a4ec020840346000000c96a1ea529943c44e889e394a16edce3c728ac4cfc0000002eae1ad78c0a386a7c63ec564a667add4000e706caa9cb3234c6d8efeb283d22e8a3800038c256494a3aae8c1cebe6baa8633858699ae7c89c2e61ac7a2c0ea14286d468e0a5e9bac42406520a12264c8a7e4000000e5eac6000ab84d8cac5b4000630b3817a000e3e84634000031455e2fe00043c000bbabe40005e0990c98deabe2ec2d2c7920000d6da64ac7a81700d20b60004480001ec000490422de2e320000a2204cb6000030cc879a0004726d0aaceda306b5c0344caaf4000000d2ac4400000000085e81e000bf8e1600000046c00000070411005083af0896e6da90c0003b0000000f10cf496a000c7e8cc1bc89094650200049a0107967ea0a0f38eae89600000058a34452ccf2a62e7625a3047647e8194da0d2e06c5346f442ec0021453e1ee000000000bfed0675c55c05e2d04468fea589ac10ef004ba0028020003ec2bc7fa2de64c0000000000000d0358152274000e4c33656ee2822472241aef400052add0000e2ed2600e63260e000cfa9bc000000cca000000d62156000e4a8f0b20c5cd0e00033e54631e2300003e20009b8bd09e8924180f42b92f4c75830259292e6d44f4b641c813a00088c1b2cd200018abc46ee47839c1bed14b90928ca006243e6fc42c000d72c64984000e601c642064e000310c1a1502084805389c8000ed87e0960d444b091e564a40ed44741e25f8bfc568d52800238efc000b6c9c400406e000000a6e0f001c000ac2b225cc462046ef2c9c60a1169b47d223ac86000000e66000b7cf1c38e12007a6de2ae8ac9e4a9e90423ccd000074a5fe2
  | 14 => 0xc80848e18dc64c40584688640001f6e0a45c9e6d880a83c6d8e00066a504aeee6ea68e8cb4c7b83c8a2aaa6a8a5a2978ab61e09748ecd4e9d027c0006122c69b0ed2cec696650d709a2b54c6c6ce0c6b04ca6b02f344b67f2f068bc000db01da34e5ce988000000524528838d22000eaaacc0fa1440003a6bb2ce650a4bea088f412e8127827e6c548d26242d452e3dcaea682754d3a2f2ecea94d745ea3f057ce7ac2aa44856c722585c6300eccb5e4c0000000cdccfe67ee12666160ad05e65548104da92c7988ceb0e942d48b4200037868c38474425cda41d299210c44254abd413ce58ee29144540007028baf2a7f000036c000000000d8c97e000daa882a92b361fce86bfa3889622aae2c8f68b8d34d8a54ceea000086a3c0448ca1aa898dba33caa85c2d00972000c7a000790000774920000000d6800000000085a0000000b89987fceacb681683cc5f057441e742dc20eaef851ed0850cba209890a00c1d4000db2e68abe21ac701787d6e9c97a6000009ca0008c8e6a00000098a000b10000ee8e46e506fa5e41344a25a08365ecdda2b200064a688714f5628455a0781f2cee11ed50eb60003a44dc2b0afcec4608aecce27945c018679ea4c3325082204120002ba112ba02fa862190000ae4e442905940002269aa66269a36291a732000000c40d1e2bea6a1ea4043f6f0cb4e1a0ea65d61ce0e8938000000b82f040008ee39e4fe000ee6000e42cde25e70e4e4d3e7082fc0003b6bf4caeaca0000002eedaec329543ac000d100000000000005ee000000d3c000e0e000900000000432826042f3cc8e86c558c881a6cb811cbf67683760005f294053a106e3820c6e83dec24726700ad66a0aaea78b8e6b60008b0d025f6000000a28daccbc3a20004440ba00031c83040e20ea6ce88d7c618f24b242727b4200e5459a0000000009ae000054000cba0007f6d36bea29ccd40005840003d8c94c3e88a000b8659e000dfc0000000003280007f8b600002e00000004fc3fac180008f8bb09226b2f4a86e000628000dfac289f027a000000e060002682884c872e91614c0f8000f367ee0ae00000037021ee0c6866646b0ef08e4000a764340e0032ca20009582a8a2449c41c01ab3abdc42886076e5d27c40008aeb481a8000aa0dcc0002ec12862629ec926980000000005fa8f2e04a260ce5ba1ae28a182464b881a4ddc9c640215e81a43a05a37ce8a414934e927344822f0ea014a3f2e9622251aae08be430d28cccbe84a0000684d96d4a000000196b986384b2184678ade0009fe828b26cd8c5298600019e0006bc000000e229c296c7e2000e209de000000000000eb24362d61b430a1c0e3005c4d4776832c5ea8e11ab008885005a607665eb58b8470608c24288416c636602d30aa435e5183746f09fc00000077ca2e760a841f
  | 15 => 0xe28a69fa20abc2694c4eea4064000db6f32a742360009e2616ca8000d98ede292dd280cd5ac0287800044eb0a6c6676e52ad206835abca65ad04c20f183d622a544000cea000ce00489321d028c69edf60c882a0f402c082b303d0b1af4475aee019c8ea75e56ab3c0fee5a342e1ee0216447c2c07d408012a03edec5b65363c0d1c0bca8283471a7ec1048040b43e41f00de5bcdde6e009a1147b6c3453033000062ee269b668044adf880e0002ce6ccd84476b4aa546c0cc0e36f0263400032e5061fa7cc0006563fc748234de4cb4abc014000af62f86580001b0af0ab2ed6f0ebce850bee17cc3667c70c9768544080007200001c4c30000000e5691249e0003a000073a000000b62622b14232000318acead8b1c2d8b7e278a4ac2e138d24360f1eb06bbe6b8f3ec6e0c0bf21726d23b892684aec602e8a8cc602669ce64b66df2e4e73085279cba40408e286a93e49661cc6a99e4d2380af282e0a4da2bd82a62dc778dce712e8457862a06a18c83eb3ec148da4d0d4248e32655013644cada02483c7ac296522e5cc8ccda312d82a1aa04b4421688e9105e26aa61e7d08925b282ca4622c4585d8298dbc4669eadee6c8ce8dd87522f6f50648d0c0006acd18766582a2cf4890695ee72f549be9b2d4c04c40c604492e9e154e98adc3226a4cf6000c6856c0ec090f3a7bcc08252e7e8807da4e0eeea8c1e6a70192b70816c38b5057a6f2240bf0ea866eac0e1cef62cc54eb6aa5015c95cb1e390486c4cc1e352ebc31a0c254866c48c09436a77a6b43e00003249a6a669f64f235ca3e6be7c67dee9a886d9ed6e01271ca5cca498210a8fcdc40c4bb6a325d451c3c2c163e899c088e40572206bcce8e3f402846e2442a00521a291c2c49f4a06644cbeafada803cd86bbc15a3fe36eaf88a0512246eb0d203667f40004841f80fcaaa6ecf3014e5dc5e868ab7acf86529d8282212b8a45097034842a71e036542c4a9d482089a7a6f2826621cc6200017eb08d6600026cd1a148b345da57e87e0e6cce0eec908d84c6d648dc5666107c21b87ce000c788d0c5894a47e0007a0df0dbeec06920000005a4818a7a3ee0000002608fa97c00048a0000002acf4e40a37e2f400000000000000000000061424a456c7c00000095ac120000840000005c4d40316bc05885164e20002e401e8d400038a0004fa000b9e93cb9c7880001cc2c800000081400074e00076a000018000baaa6400000039616ac743980f61ba8e8dc876c96885c130870672cf0ba8bb8c5008e22858c4a8118ec80005769569804988c2d6ac10000b2ca18be0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9c7450d6344001c3aa8a1ac6881cb331c94358d100147743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000c6f54dc963440018daa9b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100043f43ea0b1a200587c87d41634400187ee9a82c6881bb0f1d35058d1000637b96a0b1a2050c6c72d41634400187ee8aa6c4880130f1d154d891002c3f43eeab12200087d84dd5624400117f08baac4880122f21175589100046fc1aeab1220038dc835d562440010fd0e3aac4880122fa1f74589100061fbaee8b122000c3c75dd1624400187f0bba2c4880030f21774589100043fc2ae8b12200587c855d162440011bf06ba2c48800e3720d74589100045f438e8b122000c3f751d16244001878ea3a2c4880021fa1f545891002c3e43ea8b122000c3f74d516244009878e9aa2c4881c7171cf54589100043f43aa8b12200087c87551624400187ee8aa2c4880130f1d154589103862e39aa8b1220038de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bea9b9ac4880031755373589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100066639ee4b1220048ec875096244009958e8a12c4880038b551425891037e6639a84b12200087e87d41624400b0f90fa82c4880030fdd350589103761e3a6a0b122000c5f73d4162440db8b8e7a82c4880161fa16764c9100043ec2cec9922000ccc329d932440010ff0abb264880161f215764c9100045fc22ec99220048bc845d932440011bf06bb264880023be09764c91000666190ec99220028dc8758d324400559904b1a648800e3b21d624c91001d6641ac49922067c7476dd53144001d8e65b12628800e3d21d624c510195aa42a6498a2000ec5624c93144001ae6ea3826288002ec610704c5102fe3a3b6ea90a20068f4865cd214400d3e100b9a4288003b18cb63485100147a43ac690a202fb64854c92144001d8ac699242880035cdd47048510005d8c20e090a200087f8758d504400b0f90eb1aa0880028fe1163541101151e422c6a822000a6f8258d50440414d904b1aa0880021fe1d625411002c3e43ac4a822000a3f84589504404547908b12a08800297e0d625411010d2e41ac4a822006a7686dc5504400d6e501b8aa0880025d21d31541100353a43262a822006b70804c550440012e90e90aa08801a9d2192154110035b840242a8220069d4874c5304400d5a90c98a608801af4201314c1100fe3c3b2a09822021e5863541304403fae0e2a826088003d44c5504c1100347b436e290220069e487485204400d5c90c90a408801af820121481100fe3c3b2a09022020e6862541204403fae0e2a824088003d84855048110
  | 1 => 0xd0db1a64900035add4704c9200046fc1aebb0a40038dc835d761480031d904baec2900038b55142d852001e6639a65b0a400587e859d931480010fb0b3b262900063721d634c5201452e42ac698a4000ccc764c931480bd8d8edbaa429001a3b21973485200076318ec690a40018ec8758d214804b4d90ab1a4290003b158d3148520006b5ba8e090a400087f8758d504800b0f90eb1aa09001adaa037254120004b643a64a824006a6c864c95048043c98c6992a09001ada2013254120004b643a42a824006a6c86485504800d6d10090aa09001a7321d324c12003566432649824002ccc764c9304800d7910099260900831e1d9504c12010f2c31aa09824020d68725413048001e9264a8260900161fe03745961002c3ec06e8b2c2075c3f40dd165840eb87a81ba2cb081da1f61e74596100061fba4e8b2c2006a7a809d165840ef4f3013a2cb0800297e0d74596100052e41ae8b2c2000a6f825d165840014d904ba2cb080029de0574596100fd3a40ae8b2c2000c3f845d165840018bf06ba2cb080031720d745961000637c12e8b2c2000c6c825d165840018ef02ba2cb080031d20574596103b43fc02e8b2c207687d805d165840eb0fd0e3a2cb0800317dce735961000537c12e6b2c2000a6c825cd658400147d0839acb080028f61073596100043f43e86b2c200087d87d0d658400187ae9a1acb080029ba0b435961000536c1686b2c2000c3d7450d65840010fd0e21acb080021f61c43596100052fc1ae4b2c2000a5c835c9658400147d08392cb080028f61072596100043f43e84b2c200087d87d09658400187ae9a12cb0800297a0f42596100052ec1e84b2c2000c3d7450965840010fd0e212cb080021f61c42596100fd3b40864b2c2000a75810c965840011df04baac70800a3b2097558e100346e43a86b1c2000e1d5450d63840011bf06baac50800e3720d7558a100347643a84b142000e2d54509628400b0f90bbb265080021fe15764ca1002c3e42aec994200087d86dd532840010fd0eb2a65080021f21d654ca1000726192ca99420068dc8758d328400559904b1a650801a3b21d624ca1001d6641ac49942000c3f745536344009878e8aa6c6880161fa1f7558d100043ec26eab1a20008bf845d5634400917908baac6880023be097558d1001476412eab1a200087e871d5634400917d0fba2c6880030fdd77458d100061e3aee8b1a2000c3f85dd163440018790bba2c6880021fe157458d1002c3e42ae8b1a20008ef825d163440051d904ba2c6880022fa1c7458d100061fba8e8b1a2000c3c751d163440010fd0faa2c6880161f21f5458d100061fba6a8b1a2004c3c74d5163440e98d8e5aa2c6880021fa1d5458d100043e43aa8b1a2000c3f745516344009878e8aa2c6881cf1b1c95458d100246e43a86b1a2004
  | 2 => 0xc41596300043ec3882b2c6021a5e83105658c0014bb0620acb180029ba08415963000536c1082b2c6006a7a80105658c0014f30020acb1808697a0c21596300052ec1842b2c60068ec87509628c001c5aa8a12c5180030fdd154586300261e3a2a8b0c60068f487505618c00b0f90bbb243180021fe15764863002c3e42aec90c60008bf845d9218c00917908bb243180021f61b75486300043f43aca90c600087c87595218c00d1d90eb12431801a3d21d614863002477c3a85b126000e2d5450b624c00159b0710ec4981ab171db754c93035726316ea9926002ace86d89324c001ab6ea38264980063720d75d853000477c12ebb0a60028ec825d7614c001c3aa8a1ec29800b331c932d85303362e3b6ea98a6000ec621d89314c001ab6ea38262980161fa1676485300043ec2cec90a60068dc865cd214c001998ec9924298087179db7354130035ad406e6a82600095c874c9504c00d4b90c992a098083931893254130035ac40264a82600095c874c5504c00d4b90c98aa09801ad620131541303ae1fa06e8b2c4075c3d40dd165880ed0fb0f3a2cb100030fdd274596200052fc1ae8b2c4000a5c835d165880014df04ba2cb100829b20974596200053bc0ae8b2c4000a74815d1658800187f08ba2cb1000317e0d74596200062e41ae8b2c4000c6f825d165880018d904ba2cb100030fd0974596200061ea12e8b2c4000c77815d165880018e902ba2cb101d61fa1c74596200062fb9ce6b2c4000a6f825cd65880414d904b9acb100028fa1073596200051ec20e6b2c400087e87d0d65880010fb0fa1acb100030f5d343596201053741686b2c4000a6d82d0d658800187ae8a1acb100021fa1c43596200043ec3886b2c4000a5e839c565880014bb0738acb100829ba0a715962000536c14e2b2c400087e87d0565880010fb0fa0acb100021fa1c41596200043ec3882b2c4000a5e8310565880014bb0620acb100829ba08415962000536c1082b2c4006a7a8010565880014f30020acb100829ba08315962000536c1062b2c40068dc8750d6388001c3aa8a1ac7100030fdd154586200261e3a2a8b0c40068f487505618800b0f90bbb263100021fe15764c62002c3e42aec98c40008bf845d9318800917908bb263100021f61b754c6200043f43aca98c400087c87595318800d1b90eb1a631001a3d21d614c6200246fc3a87b1a4000e1d5450f634800159b0518ec6900161fa1f7558d200043ec26eab1a40008df835d563480011df04baac6900021fa1c7558d200043fc2ae8b1a400587c855d163480011ef02ba2c6900063d2057458d200043f43ea8b1a400587c87d5163480010fd0eaa2c6900021f21d5458d200062e3aee6b1a4000c6c75dc963480010fd0fa82c6900161f21f5058d2035e363b6ea992406be4c63dd5324800759
  | 3 => 0x6b12a000d5b60dcd62540018beec39ac4a8003531cf6258950006adb9ee0b12a000d5873dc162540f3ad6e5b82c4a80025e603764c95000726196ec992a00087f84dd932540010fb09bb264a80031e603764c9500043f434ec992a000d4c329d932540012bf06bb264a80025be09764c950004bdc02ec992a02293e841d9325400127b083b264a8003530c8764c9500051ec20ec992a000e4c321d932540010ff083b264a80030fa10764c9500043ec20ec992a000c3d841d9325400107b083b264a80031bcc8764c9500062f190ec992a000c5c321d932540018d8643b264a8003130c8764c9500062f988ec992a000c6f211d932540018be603b264a80031bc80764c9500fc3ec3ec9b0aa022c3e74d93615400187ae9b26c2a807e9d20564d85500053ac3683b0aa07587c86dd161540012bf06ba2c2a80865720d7458550004b7c12e8b0aa02096c825d161540012ef02ba2c2a80025ee0174585500fc3e43ac8b0aa000c3f745916154045878e8b22c2a807e9d20564585503c6b9b8ee0b0aa00097980dd931540010ff09bb262a80021f613764c5500062f41eec98aa000c5d83dd931540018f301bb262a80021fa1a764c5500049fc22ec98aa02293c845d931540012df04bb262a80825b209764c550004bdc02ec98aa00087f841d931540010fb083b262a800317cc0764c5500063b880ec98aa01f95e87d8d31540018beedb1a62a807ed5a07634c5500fcae43a6498aa000a5c864c93154041a98e499262a80025e60376485500043fc26ec90aa00087d84dd921540018dd05bb242a80031b60b76485500063cc06ec90aa00087e869d9215400127f08bb242a808a4f2117648550004afc1aec90aa02195c835d921540012f700bb242a80021fe1076485500043ec20ec90aa000c6f201d921540018ee203b242a80021fe1973485500043e432e690aa01f96e87d8921540018deedb1242a807ed9a0762485500fcb643a6490aa000a6c864c92154043a98e699242a80825d21d3148550007a29926290aa075c3f40dd1658c0eb87a81ba2cb181da1f61e74596300061fba4e8b2c6000a5f835d1658c0434b906ba2cb180029be09745963000536412e8b2c6000a77815d1658c0014e902ba2cb180030fe1174596300062fc1ae8b2c6000c5c835d1658c00187e86ba2cb180030f50d745963000637c12e8b2c6000c6c825d1658c0018ef02ba2cb180031d20574596303ac3f438e8b2c6000a5f835c9658c0434b906b92cb180028fa1072596300051ec20e4b2c600087e87d09658c0010fb0fa12cb180030f5d3425963010d2f41e84b2c6000a5d83d09658c00187ae8a12cb180021fa1c42596300043ec3884b2c6021a5e839c5658c0014bb0738acb180029ba0a715963000536c14e2b2c600087e87d05658c0010fb0fa0acb180021fa1
  | 4 => 0x34840b0f90faa2c6908021fa1d5458d210043e43aa8b1a420087e87d41634840b0f90fa82c6909b25ba1f754c92135e363b6ea992426be4c63dd53248401ac8e3baa64909fe5ba1f654c9212f6363b6ca9924200e4c63d95324840759d0db1a6490803591d7714c92112cb642ee09924267c7476dd53148401ac8e5baa629097f1d1db654c5210072a31eca98a4201bc4874c93148405b890e9926290806f1a19324c52100de24326498a4203ec4864c93148407d8eec992629080b719d9324c521016e23b26498a4203ec4764c93148405988ec9926290803d1e15324c5212ade342a6498a4255bc4854c931484f9e890a9926290956d1215324c521007a3baa6498a427cf44754c93148401e8eca99262909f3d1195324c5213f5e3c226498a427ebc5844c931484fbe8ea899262909f7d1551324c521005e3c026498a427cf47504c93148401b8a65b8262908063b60b75d81210053cc06ebb024200a79801d760484010ff0aba6c0908161f21574d81210043f43ea9b02420587c87d5360484010f90eaa6c0908021fe1573d812102c3e42ae7b024204cac7450b6048401c5aa8a16c09080f331cd32d81210076299263b02420587e86dd560484bd0f90dbaac0908021fa1f65581210061e3a6cab024200c5c73d9560484010fd0e32ac0908030f1d065581210062e398cab024200c3f65dd16048401878cbba2c09080317d9773581210062e32ee6b02422587d87d94604840187ce9b28c090803179cf65181210053cc06ca3024200c3e7419460484018bce6328c0909831b5c865181213de3ab88ca3024200a7980194604840187ecaba0c0908030f19574181210062fb2ae63024200c5c655cc60484011f70eb00c0908861f61f64d8d501161f3a6c9b1aa000c3d74d9363540434bd07b26c6a80030fdd164d8d5010d2e41ac9b1aa000a5d86d0f6354001c3ac9a1ec6a8002d3a0b43d8d500052ec3465b1aa00095f835d163540012df04ba2c6a80825b2097458d50004bbc0ae8b1aa01f974815d163540012f700ba2c6a80031b1cb6458d5010c3e43ac8b1aa000c3f7459163540018d8e4b22c6a80825ba1f7258d5000637b26e4b1aa000c6d64dc963540018dec1b92c6a80035ad837258d5000637bb0e4b1aa000d4f731c963540f5ab6e7b82c6a80035adcb7058d50006b4396e0b1aa02087d87d93625404587ce9b26c4a80030f5d364d89500061fba2c9b12a020a6c8259362540014db0da16c4a80038b59342d8950005a741e85b12a000a6d86ccb62540012bf06ba2c4a80865720d7458950004b7c12e8b12a000977815d1625403f2e902ba2c4a80025ee0174589500062e39ec8b12a02087c87591625400187ee8b22c4a8003171cd645895010536412c8b12a02195e87dcd62540018bec9b9ac4a80031759373589500062fb06e
  | 5 => 0x88161f21f54d81310043e43aa9b026204c9c7450f604c401c3aa8a1ec0988021fe1572d813102c3e42ae5b026202ccc724cb604c40b0fd0dbaac09899a1f21b75581310043f43ecab026200c3c74d95604c4018d8e5b2ac0988021fa1c65581310061e3a0cab026200c6c72195604c40187ecbba2c0988030f197745813100637b2ee4b026200c6c65dc9604c4510fb0fb28c0988030f9d3651813100637396ca3026200a7980d94604c40187ce8328c0989a3175cc651813100637390ca3026280c7571194604c4014f300328c0988030fd9574181310061e32ae83026200c6f655c8604c4018d8cab90c0988023ee1d60181310043f436e9b2a420587f87d93654840187ae9b26ca908021f61e64d95210052f41cc9b2a4200a5d8399365484010ff0eb26ca908961f61c64d95210061eba0c9b2a4200a3e8498f654840147b0931eca9097a9b21942d952100697ba285b2a4200e2c6450b65484bd6c902a16ca9080297a0f74d95210052ec1ee9b2a425fa6e82dd365484bd4db05ba6ca908031b5cb74d95212f53b40ee9b2a425fa7581dd365484018bd07ba6ca908031760f74d952100637416e9b2a4200c6d82dd3654840187e85ba6ca908030f50b74d95210063b40ee9b2a4200c7581dd365484010fb01ba6ca908021f61e74d952100636b92e9b2a4200c3f845d365484010ff00ba6ca908021fa1c74d95210061eba0e9b2a425fa6e821d365484bd4db043a6ca9097e9ba0b73d95212f536c16e7b2a4200a3e849cf654840147b0939eca90803175cc73d95212fd37410e7b2a425ea6d821cf65484bd4ed0239eca9097e9d60473d95210043f43e87b2a420087d87d0f654840187ee9a1eca9097e9ba0b43d952100536c1687b2a4200c3f7450f65484010fd0e21eca908021f61c43d95212fd37416e1b2a425ea6d82dc365484018dae5b86ca908031b5c970d95210043fc22e1b2a4200a3e841c3654840147b08386ca9080297a0c70d95210052ec18e1b2a425fa6e821c365484bd4db04386ca9097a9da0470d95212fd3ac08e1b2a420087e87d0365484010fb0fa06ca908030f5d340d95210043f43c81b2a420087d8790365484010fb0ea06ca908030f5d140d95210043f43881b2a420087d8710365484014bd06206ca908029760c40d95212fd3741081b2a4200a6d8210365484bd4ed02206ca908029d60440d95210043f43861b2a420087d870c3654840147d08186ca908028f61030d95212fd3741061b2a4200a6d820c365484bd4ed02186ca908029d60430d952100c76c16ebb1a42048df8750f6348401c3aa8a1ec6908021fa1f6558d210043f438cab1a420587e87dd563484010fb09baac6908021f6037558d210043f438eab1a420087f855d1634840b0f90aba2c6908023ee017458d210347c402e8b1a420087e87d516
  | 6 => 0x2c3f436eab02646a87c86dd5604c801a9865baac0990021fa1f65581320043f438cab026400a3d84195604c90b8bee632ac0992131bdc86558132006a6192ea302642b87d87d94604c80187ce9b28c0990031d9c765181320053cc06ca3026400a3d84194604c80187ce8328c0991b3175cc651813241636b90ca3026483e4c32194604c8018ece2328c0990029e60065181320061fb2ae83026400c3c655d0604c801b1864ba0c0990031dd9571181320063a32ae23026400dc4325c4604c8011f70eb00c0990021fa1b74d953102c3fc3ec9b2a6200c3d74d93654c4010fb0f326ca988029ba0a64d953100536c14c9b2a620087f87593654c4510fb0e326ca988030f5d064d95313352e43287b2a6200d1f7450f654c401c38c8a1eca9899ad520543d95310051f424c5b2a6200a3d8498b654c4cf4bd07ba6ca9899a9760f74d95310062eb9ee9b2a6200a6e82dd3654c4014db05ba6ca9899a9da0774d953133d3ac0ee9b2a6200c5e83dd3654c4018bb07ba6ca988030fd0f74d95310061ea1ee9b2a6200c6e82dd3654c4018db05ba6ca988031da0774d95310063ac0ee9b2a620087d80dd3654c4010fb0f3a6ca98803175cd74d95310061fc22e9b2a620087f805d3654c4010fd0e3a6ca988030f5d074d953133d2f418e9b2a6266a5d831d3654c4cf4bd07b96ca9899a9760f72d95310051f424e5b2a6200a3d849cb654c4cf4bd06396ca9899a9760c72d95313353b408e5b2a6267a75811cb654c4010fd0fa16ca988021f61f42d95310061fba685b2a6267a5e83d0b654c4014bb07a16ca988030fdd142d95310043f43885b2a620087d8710b654c4cf4bd07b86ca9899a9760f70d95310062eb9ee1b2a6200c5d735c3654c4010ff08b86ca988028fa1070d95310051ec20e1b2a6267a5e831c3654c4cd4bb06386ca988029ba0870d953100536c10e1b2a6266a76811c3654c4cf4eb02386ca988021fa1f40d95310043ec3e81b2a6200c3d74d03654c4010fd0f206ca988021f61e40d95310043ec3a81b2a6200c3d74503654c4010fd0e206ca988021f61c40d953133d2f41881b2a6200a5d83103654c4014dd04206ca988029b60840d95313353b40881b2a6200a7581103654c4010fd0e106ca988021f61c20d95310051f42041b2a6200a3d84083654c4cf4bd06106ca988029760c20d95313353b40841b2a6200a7581083654c4031bb07baec4988123be1d42d893100716aa285b12620087e87d95624c4010fd0e32ac498a0a57a1f754c9313562e3b6ea992626ae4c62dd5324c401aa8e3baa6498a0657a1f654c9313362e3b6ca9926200e4c62d95324c40559d0db126498803551d7714c931144ae42ee099262018dd83dd7604c4014f301baec0988029e60075d81310043fc2ae9b02620587c855d3604c4010fd0faa6c09
  | 7 => 0x60000000000000010040000010000000000010000000010000000000000020000000000010020000010000000000000010000050030000000020000020000000000010010010000030000000010010000000000000010000000030000000000000010030000000030000000010020010000010000000000000010000000020050010030000060000000010010000010000010040000000010000000020020010010020000000020000000010000000000000000000000000030010040000000000000000043f436e9b2a6400d4c32dd3654c801a9864ba6ca990161fe1f64d95320061eba6c9b2a648be4c32d93654c8010fb0f326ca990030fdd264d95324552ec1cc9b2a6489a6d82993654c8010ff0eb26ca990030fdd164d953244726192c9b2a642b87d87193654c80187ae8326ca99003530c970d953235d2f41ee9b2a646aa5d83dd3654c8d54dd05ba6ca991ae9b60b74d95320053b40ee9b2a6400a7581dd3654c8018bd07ba6ca990031760f74d95320061fa1ee9b2a6400c3d43dd3654c8018dd05ba6ca990031b60b74d95320061fa16e9b2a6400c3d42dd3654c8018ed03ba6ca990031d60774d95320043ec06e9b2a640087d879d3654c80187ee93a6ca990030fe1174d95320043fc02e9b2a640087e871d3654c80187ae83a6ca991ae97a0c71d95323552ec18e3b2a646aa6e821c7654c8d74db0438eca990021fa1f41d95320043ec3e83b2a640087e87107654c8010fb0e20eca991ae97a0c41d95320052ec1883b2a646aa6e82107654c8014db0420eca990029ea0041d95320053cc0083b2a640087f845c3654c80147d08386ca990028f61070d953235d2f418e1b2a646aa5d831c3654c8d54dd04386ca991ae9b60870d95320053b408e1b2a6400a75811c3654c8010fd0fa06ca990021f61f40d95320061eba681b2a640087e87903654c8010fb0f206ca990021f61d40d95320061eba281b2a640087e87103654c8010fb0e206ca991ae97a0c40d95320052ec1881b2a646aa6e82103654c8014db04206ca990029da0440d95320053ac0881b2a640087e87043654c8010fb0e086ca990028fa1010d95320051ec2021b2a646ba5e83043654c8014bb06086ca991aa9ba0810d953200536c1021b2a6400a3d84197614c9058b8e632ec2991b31b1c865d853243f26190cbb0a6404c3e74553614c80187ae8aa6c299003530cb75585320043f43ecab0a640087e87195614c80147b0832ac29921b930c865585320051ec20cbb026400a7980dd7604c80147b083aec0990029e60075d81320043fc2ae9b02640587c855d3604c8010fd0faa6c0990161f21f54d81320043e43aa9b026404c3e74553604c80187ae8aa6c0990021fe1571d813202c3e42ae3b026400d4c325d6604c80147b0832cc099217930c865981320
  | 8 => 0x32442e0ee0000000000000000003820000000000000000000000001280000000000006d40006a625000069c0007d200000071a3d00002de1ca0000000000000000000006a20006fe4c264600000005800000000000059c28400000000000000000000011016e51a00000000000038a48c6160000000000000005928200003e427c0000000000000000003b646a00000000000000000044a00000e0000000007620000000000000000000000000000000000000000000007a20000003c800000000037c00000007a45a1940000000007f86c00003060000000000006d200000074a0006fa6fc0000006720000005ea0000000007380005e20005bc0000a400000000000000000000000000005c0000000000000004201580001440000000006ce0000006f20000000000000000007a400000000056600000000000000000032e16c35c0003da0000000866e60006925e80000006ea64000006c00076e83c6220a20005600000000000006080000000004e273000084c6b400028e00086e8745620001ea00000019622600000000000057c0000000004da00000000002627060c65000000000000027a00059800000000027e82820c00010e6b00000000000000000003d20006a82a419200000018200000000000000000029200070c2cc73683023e1d800032a00078200000000000000000000031800000018a7da3044c61b60007720000006640000000000000000000000000001560000000000000000000000006bc0005fc4be5020000006c800000050e0005ec2083201004d63bc7140000006d60000200000000000000000000000002f400000000000053400000000000000000000015c0000000000000000000000000000000000000000000000000000000000002d66de00017c0000000000004660000000000000006d00000000000000000020020000020000000000020000040000030000000000000000020000000000000010000000000000010000000000000000070010000000000030000030030000000000000020000000000000000000010000000000000040000020000010010010000000010000030020000010000000020000000000010000030020040010020000000000000000000000000010040040020040000000000000020020000010050010000020030000010000000010090000010000000000000000010000000000000000000010000010000010000030020000000000010010010010000010010000050000000000000010010000030000000000000000000000010000000000010010000040000000000000000020030010040000000000010020000000000010010010000000010000000010000000000000020020010000000000000010000000000000060010000010010000000000000020000010
  | 9 => 0x24632c0000ce2160000007e247c00000000000000006e0002e03e01080000000000008660000000000006e424c00000073e0000000000000000000000000000000000000000000000000000006320000000000000000000003400000002b084e3e81d450860454a17800000000000008c0000000720000e200000000066269040249c4a43707cc5e400000000000000000000052c00009e0005180000003ea00000000000000000008e4405840008020000000000001de00038400022074e5a40000000000c00000000000002c60007100000000000001546200001a05160001167760000000005d200000000072800013200078c0003080fe0000000000000002620000002147600000000480000003ce0001e43ca0007860bc3c000078a0000000004a60000002560000000003744ec00000000000033e00000000000000000062e0000000000000004c82280002ae0000000000002320000000000007de0004fa0000003620000000c200000043c2a62760520000000004680006ba00000000067e0000000000000000000000000a00002c40000000000000000000000004ce1ba00000000000026600000000000000000000000000000000078414a19000048651e50c00030e1260003f20000000001200000744cc72674000000006a36a1ce2e40ec0000000e871649a34403c0000002e82c20000000000000000000004485ce46e0007027522ee1b40000000000c80000000004aa0000000100000003d62300005380380000000003b000087000000000000000000054800000000000000000000000000000000000000000000000000000000000000046c0007d80004700000000000000000000000000000000004840000000000000002b400000085a1460001b00000000000004d868825e5cc09826c0000000000000001b800052200000000000000000000000000000054c5be00000038009400000000000000034c3140000000000006285403a883400000000052e0000000002ec0000000000004124000004160000007e80000001660000000000000b874c0000000000aa0004640000000000000000000000000001f46004f800010a5260000000000000000000000000000000002dc0002820000004760000000000000000000000000320002b200000000000000000000082a0000002d831c77c78800000000063a5780000000004140000000000000007940000002800003c60000000000120000000000000007f20003267e40000000000000000000000000004e07e00001f65c400042600000000039225a3d47b00002240cc00000000001600000000040c07861c00000000077e15e2440000000005700000006340000000000005e600000000060200000000000000045058a2900000000002b600000000000000
  | 10 => 0xc68167501d26ac0000000907b483800022a6102fa5820360000007dc6e85ba00000036445c0000000000000000000000000000000ea0000c60008080000000000003100002e28220000008140000000000000000000000000000000001ee00000000037800045600013a00000000000058c0000003ba0005b600010600000024e00000000c0000005d80000000000007ca00000066e00045e0001f80000003f80000000000006da0843d800000021c0000000000000007a000000000000000000082458e00001839800000000000000000080c0005c800000000000066c0020000000001300000000002ce0e66360005d400084462c0000007ac0000000000000000003b800000014c0007c867a0004540000000004a80000003be00000000000000000000000053c81800000000000000000035423a6603564b66aa00004284024078078e00000000000040a6b200000081005a0b200020a1705a60000000007980001401a44a220400000000000000000000000000086c0002a20000000000000000000001844b82540000000000000000001f034e00084a0000de64400000075e00028a4960000003884580000000007ba0000006f00000000000000001683580000680000000000000000005500000007ee0000006ae0000000f837673200000000000000000022243000000029c0000000000000000007fc0000fc00000011c35e72208000068e6785587f00001bc7ec0005a80ac1728680000000002520b628c00083200068a12400000000000026800000000000000000000076a0000000000000000000004720000000000000000000000000000000000000005300005ac00034600000000046200000000071c0005000000000004d000000080e2f00007684180000008125ca0005060005560000000002387242c06260000000004e849800000000000000007600000053e2f85ae00000000063e0000000000d602c0000000dc0000000001e600000000064a00043e00056a0000000000000000000000000005760000003720000005740f400041c0000004ac0000000000004ae0000000000000000000000000000005c00003300000002ac6800000000000000000000000007a832856e0003a40000000000000ae0000000000003f40000000000000008480000000002e60000000000000000000d00000004e400019e0000000000000000000000000000000000005104601ae6303c229e7922da5fe00035a0008520000000000000001d073c00000000057a0000001dc61a00000000000059000000000000000000005400000000000000080a0000000000000000000000000007ae0000006e000000000000000000052470800000000000000000036e03a0000000001500000000000000000000000000000001f2000000000000000000000
  | 11 => 0x9239400000013800074201e51264c27218c0a600037a00000000000000000000000000000022e13e5dc0003e67ea6b600000002e00000000000021a4220000000000000000000000000007d600065800000000006017e0000000002ea4c421207e00029408800000000044e00000000000000000000002a7960000000000000000006560000000004ee00000000000000000000000070673a2d26b80000040000000000000000000000000000004742b800000000000000074600600000000000000000055a0a80000000000000000000000000000000000f60000000000b43a600001c3ac0000003485f200000055404c0000000000000003500006cc0000000001040007aa00000000000000000024a33a0f20002368582f20000000000000007b20000000007be0000000001a600000000000014226e00069686a00039000000000000000000018e0000006740007740000000000000000001c23380080000000004b00000003860000000000001b21d60000000000000000000000000003ec1e800000000031a56470066616400000000000039c0007580004c000038e00000000000000000000036000000015200047e5f600000000000000000012e45200000000047a00000000000026a0000000000000000002a01ec0000008040000000000000000000007f40000000000000000000000006684ea00000000000000021000072000000000000082c0005f81120000000004dc00068c6ca4f400013c00000083e60a6e200000000000000000031e2ca44c00029600004600033c00008220e00055e1fe4360000000ba63800000064200018000043a0000fa11a26061400065476c33441a7fe79e0000000000000000000000000000004060000000000003fa63c0000000000000000006860008720000000006767d40000300000000000003b20000000000000000000005e00000000000000007180003c400000000000000000000000000000000000000001a0000005324b400000000000000000000000058800000000022c00000034200000077a0000000000003a05aa0000000000000005d600083656800000082600000000000000000000004e00000000016a0000000000001cc70400000049e0000000000000000004ca0000000000000000000440000000000000008460005da00023454e52800000000000006407c2d40000000002a840e0000000000008060001a800000050400017600069a00029a00000000000072c0000002fc0003320566f600000000000033600000012a0007b600000000005e00000000000000051475c0000000000001c00004fe0000000000220000000000000000000000000000006f800028800000000000000021e38c0000000002bc3dc00000051c70a00000000000000000000000027400000048e5
  | 12 => 0x48a4f273400000000000008a00053a0000000007ce0001c859e0700000003160000001ac00000059a0000000000000000000000000000000000000000000003cc0140000000000000000000000000000000000e085c0000005440000006a000000000000028617465c1da00019a5363b40968000e469e00000000067000012c00030c0d40000000000000000000000000001c46c200072a00000010c0005422ba0006be00000000055c0000000000000000000000000000000000004f02180000000000000000006247c40000000000000000000000006ec36c4420000000000000000000000000004d24fc85400000000000000000062a1861be0000001885206520ca0000005945c200019c00004a0001c60000000000000006a40000004460000000000000000000006943aa2f62067f664e30236810200000020249282e0004bc0000003520000000000004a000000000000000000000000000015a71239e0d80000000004b23a200042a0f00005b40004040000000000000000000000000005b00000000000000000007fa39600000000066a1340008625b200000000000000000000000000000075600009a0000000660000000003660d20000000000000000000000000000004084100005f45520000000000000000000000000003f600041e16049000029800019800000000057e0000004de0000000000000000000007783e234a7d000061e0000000000000002aa84200060e00000000000000000000000000000081e7a600000081c2581fa00047800000039a00000000000000000000000000000000000000044400000000000000003400048800000000000068209c0004345ee0000001366180000000000000000000000000007440004287540b04947c60000002641e214e68442c0003f00000000000000007c05720000000000000000004f60000000000000000500000000000000000000000000008640000000002d06060000005d00000000000000000008600000000000000000000000006d800012200000079000000000000000000000000000000083a00000081a0000001e000004000000000000000000000000000000000000000079c0000000000005960003de0000000000000000000000000000003ee0000000005a03220006f46ee00000000000000000000000000069800000000000000067c00000000076400014800030a00000000000000000000058000000071e0000000000000000000000000000001aa00000000000000000000000085e0622000000000000000007c24320002fe00016200000077065e0000007bc0006c43ae37e00042400000000000000000000000000000000000000000000000000000075a0000000000000000000000000000001140000c44800000004d45fa00000000000048217a00
  | 13 => 0x5b80000008500002c80007e600000000000000000000000070e0000000000000000000000000000000000000000000000001180003000000000008760005460000000005f000043861200000000024223c0000000000000000000008563fc58600000000000000000000056c00000000072e00052a6dc5de03e0000000001a20da00065a1fc0004ba00027800000050a0005a211e3fe0007480007660000000000000000000000004e60000000000000000000000000000000000000007b800000079a00000002800000000000000000025c0000000000000000000000000000000003120000000000002be00002400a0000000006480000000000000000000000000000000000000000000000006c60000000be248000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8014359419571181320051c640655c4604c8011c5980c9711813200711194325c4604c80141e96dd143d95310050b64b43dd3654c40181f7460f42d95310054565075dc5324c40141c9755143d81310051a640655c8604c40142e96dd142d95210050764f42dd3654840182f7460b43d95210054965075dc5324850334698e15324c5213565121f854c931484d7a4486e15324c521357111db854c9314850334698dd5324c5213365121f754c931484cfc4476dd5324c5213fcd1a63654c931484bda4486d95324c5212ff111db654c931484ab34495e01324c5210050b25d5450b604840145990195731812100613208735916254001645910cb764c9500059264032dd93254001545910ca764c95000552640329d9325400190d840c8764c95000551644321d93254001549900c8764c95000683610321d93254001645910c8764c95000592640321d9325400103d98a10764c95000607e4d841d9325400181c93610764c9500060be49841d9325400182c92610764c9500060b613321d9325400181d848c8764c95000513a4a321d9325400181d840c8764c95000515644321d93254001459900c8764c9500060b610321d93254001465910c8764c9500051a640321d9325400184f840c8764c95000703a10321d9325400184d840c8764c95000703610321d9325400180d840c8764c95000711a44321d9325400144d910c8764c95000711644321d93254001445910c8764c95000712a40321d9325400144d900c8764c95000712640321d93254001449900c8764c95000607613311d9325400182d84c84764c9500051324f211d9325400181d84cc0764c9500060b613201d9325400144c93c80764c95000487650864c9315400184c72219324c5500048b650864c9215400184c7321932485501065121d324c52154001644964c931485500050b64b435d1658c001864822057459630006075d183d09658c00111d9421d325413000613188874c9504c00141d93d0974596200061520c815d1658800182d7460b43596202ad91255634c5214800112d9421d32541200061318c874c95048001348984c9504c1200355225d32541304800d648964c9504c120107121d932541304800184c8320974596100060b5d182d0d658400181d7460f42596100040f65087595328400184c870c9654ca100059164432595328400141c975514358d100260721d5450d634411bc0c725514358d100050b25d54509624400982c875514258910467031cd5450962440014c5910ca764c91000433660321d932440014c5910c8764c91001d3125d624c9314400193375610704c5100153125d634c92144001933756107048510004d426131541304400d550974c5504c110035942593154130440013609848550481100355825d21541204400d660964855048110
  | 1 => 0x199c864500000008d00054549200000e077350dc1a003b0000000000006283481eca4623e0390e401e801121b2b800d0304125400001982088000b93c121d0023c00482613800250102cca754b004002d088107800378005200000008e0000000440f000000000000010a0040818fa1c2f168006b000006c32399507c640f928841412041107105064000c3000000002304cd200002440051000005c4d15878f4182b000d8000b17c007200000740047085140009000008c208ecdc592e000706d2e8000a23430004c39000bcf2931625050633f00000783a06800000016c968000000cc00000000000000000055000010800000000e2700000a600458007e00280d4680000080920000000c2583f808002018046000000c540430081400040c0000040c2408000804000c0414000c000808182410040000101c3800280800000401545910cb74d953200551644325d3654c801c0c325d364d953202c0fa6374593654c801c0c32dd164d95320040fe6174193654c801545910c970d95320050b64b43dd3654c80141d93d0b74d95320040fe61741d3654c91f81c7361065d85324760b1c984197614c801a0c3261065d853200513a5832dd5614c801545910cb7558532006830c984195614c80b03c985d154d813200551644325d6604c801a0c3261065981320055164432dd5604c80181f7361065581320060bdc984195604c801545910c9751813200552640325d4604c80103f976106518132006075cd84194604c80182d726106518132006830c984194604c80103d989d065181320060d61271194604c801a4832600651813200703194325d0604c801585910c9741813200562640325d0604c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x7a0054443e64402400004e120000006e04783852005e680a141a00762c583a001e2a26600e00701c306a32624a0000062042000000005a2e3c027448161800720028566c3480463650004c0000100008225c7c7e660c000c001000c0030a2018108005820000c050400851ea1910cb74d953200580b42192e9b26ca9900280ea80cb74593654c801602d0865ba2c9b2a6400a816843261065d853200540b421930832ac299002a05a10c984196604c801406d3864c20ca3026400a816843261065181320054134019308328c099002849a70c980194604c801520d0864c00ca3026400d01195910c97418132006810cac8064ba0c09900304598194325c4604c801602d20ca192e23026400b10680650c9711813200620b08c88643b264a800310984640321d93254001902c2322190ec992a000c82611900c8764c95000501d45c9b083b264a800280ea3e49841d9325400180ac2322190ec992a000c06611900c8764c95000604b08c88643b264a800302984640321d93254001406d4508190ec992a000c03ea5840c8764c95000601952c20643b264a800380584a44321d93254001806c2322190ec992a000e01611910c8764c95000608f08c88643b264a800340684644321d93254001822c2322190ec992a000d01611910c8764c95000600b08c88643b264a800380984a40321d93254001a20c8d20190ec992a000c03611900c8764c95000701308c80643b264a800344291640321d93254001a20c8b20190ec992a000c12e11900c8764c95000681508c80643b264a800304984640321d93254001a04c2320190ec992a000c02611900c8764c95000601b0849e423b264a8002449a024f211d93254001806c2127900ec992a00091168493c80764c95000601b283910c99262a800300d941cc864c921540018224392c9926290aa000981690964c9314855000601b283110e992a098002845a1188874c9504c001806ca0c643a64a824000a116846321d3254120006090ec4c264a826090002309a4261325413048001406d210e192ca9942000c1121d910c9654ca10
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x20e50630000400058a40001e000698000000480802701140000004407b968432dd164d953200600598690650c9711813200604198680650c97118132004805b1a8b93610764c950004805b1a8f92610764c950005005b12a5840c8764c950005009b02a5840c8764c95000700184646900c8764c95000700184a45900c8764c95000700184645900c8764c9500060098468093c84764c9500060058468493c80764c95000600487690964c93148550006005946846221d3254130006005946846321d325412000600876690984c9504c120005005b421d910c9654ca10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x1
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x124d
  | 12 => 0x124b
  | 13 => 0x124c
  | 14 => 0x124e
  | 15 => 0x98a
  | 16 => 0x98c
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x128a
  | 20 => 0x128c
  | 21 => 0x128d
  | 22 => 0x128e
  | 23 => 0x9ca
  | 24 => 0x9cb
  | 25 => 0x9cd
  | 26 => 0x9ce
  | 27 => 0x12ca
  | 28 => 0x12cb
  | 29 => 0x12cd
  | 30 => 0x12ce
  | 31 => 0xa4a
  | 32 => 0xa4b
  | 33 => 0xa4c
  | 34 => 0xa4d
  | 35 => 0xb0c
  | 36 => 0xb0d
  | 37 => 0xb0e
  | 38 => 0xb4b
  | 39 => 0xb4d
  | 40 => 0xb4e
  | 41 => 0xcca
  | 42 => 0xccd
  | 43 => 0xcce
  | 44 => 0xa4955
  | 45 => 0x94a55
  | 46 => 0xb0955
  | 47 => 0xb0956
  | 48 => 0x94b15
  | 49 => 0xb4955
  | 50 => 0xb4956
  | 51 => 0x94b55
  | 52 => 0x150a
  | 53 => 0x168a
  | 54 => 0xa4995
  | 55 => 0x98a55
  | 56 => 0xb0996
  | 57 => 0xb0995
  | 58 => 0x98b15
  | 59 => 0x138b
  | 60 => 0xcc996
  | 61 => 0xcc995
  | 62 => 0x98cd5
  | 63 => 0x168b
  | 64 => 0xa49d5
  | 65 => 0x9ca55
  | 66 => 0xb49d6
  | 67 => 0xb49d5
  | 68 => 0x9cb55
  | 69 => 0x138c
  | 70 => 0xcc9d6
  | 71 => 0xcc9d5
  | 72 => 0x9ccd5
  | 73 => 0x150c
  | 74 => 0x198a
  | 75 => 0xb0a55
  | 76 => 0xa4b15
  | 77 => 0xb4a55
  | 78 => 0xa4b55
  | 79 => 0x138e
  | 80 => 0x198b
  | 81 => 0xcca55
  | 82 => 0xa4cd5
  | 83 => 0x150e
  | 84 => 0x168e
  | 85 => 0xb4b16
  | 86 => 0xb4b15
  | 87 => 0xccb16
  | 88 => 0xccb15
  | 89 => 0xb0cd5
  | 90 => 0x170a
  | 91 => 0x15ca
  | 92 => 0x16cb
  | 93 => 0x144b
  | 94 => 0x164a
  | 95 => 0x14cb
  | 96 => 0x44a
  | 97 => 0xccb56
  | 98 => 0xccb55
  | 99 => 0xb4cd5
  | 100 => 0x154c
  | 101 => 0x140c
  | 102 => 0x17ca
  | 103 => 0x14cc
  | 104 => 0x5ca
  | 105 => 0xcb
  | 106 => 0x17cb
  | 107 => 0x164c
  | 108 => 0x5cb
  | 109 => 0x198c
  | 110 => 0x198d
  | 111 => 0xd0c
  | 112 => 0x104c
  | 113 => 0x1a8c
  | 114 => 0xe8b
  | 115 => 0x104b
  | 116 => 0x1a8b
  | 117 => 0x1a89
  | 118 => 0x1049
  | 119 => 0x124a16
  | 120 => 0x139256
  | 121 => 0x151296
  | 122 => 0x1692d6
  | 123 => 0x2cb
  | 124 => 0xccb4b1e
  | 125 => 0xccb4b1d
  | 126 => 0xb4b0cdd
  | 127 => 0xb0454
  | 128 => 0x2cc
  | 129 => 0xb45d3
  | 130 => 0x44c
  | 131 => 0x5c0d3
  | 132 => 0x45294
  | 133 => 0x5d2d3
  | 134 => 0x5cb53
  | 135 => 0x5d6d3
  | 136 => 0xe97d3
  | 137 => 0x164d14
  | 138 => 0x17ce93
  | 139 => 0x1797d3
  | 140 => 0x104d14
  | 141 => 0x104e93
  | 142 => 0x154e
  | 143 => 0x16ce
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 978
  | 6 => 1964
  | 5 => 1084
  | 4 => 151
  | 3 => 65
  | 2 => 17
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (39772+((h/326+packedAt gbK7 (36186+(h % 326)*11) 11) % 1174)*11) 11
  | 6 => packedAt gbK6 (102120+((h/654+packedAt gbK6 (94272+(h % 654)*12) 12) % 2357)*12) 12
  | 5 => packedAt gbK5 (68288+((h/361+packedAt gbK5 (63956+(h % 361)*12) 12) % 3370)*12) 12
  | 4 => packedAt gbK4 (10970+((h/50+packedAt gbK4 (10570+(h % 50)*8) 8) % 242)*9) 9
  | 3 => packedAt gbK3 (5412+((h/21+packedAt gbK3 (5265+(h % 21)*7) 7) % 86)*8) 8
  | 2 => packedAt gbK2 (1594+((h/5+packedAt gbK2 (1564+(h % 5)*6) 6) % 34)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc1fe0e060fc1fc07ffffffffc53018f024fff
  | 1 => 0x3fe1ff007f0fe1ff838781e07cac8e738db293
  | 2 => 0x3ffe3fff800ffe0003f801ff8330f07cf1c31c
  | 3 => 0xc0003ffffff0000003fffe0003c0ff80fe03e0
  | 4 => 0x3ffffffffffffc00000003ff0000fffc00
  | 5 => 0xffffc000000000000000000003ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x48024000001002402008a02820010085000425
  | 1 => 0x14a0a3022504a09301c5054158048632849292
  | 2 => 0x26d42d6a840ed4050ad409970930b058b1c318
  | 3 => 0x808036b376a0800a13665d0212c0db00de03c0
  | 4 => 0x21018dc58cb192c5800100403fa00006b6800
  | 5 => 0x3b190018108210306000601863ff6def000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36292
namespace PEqualNP.Outside.L_meta_36292
open PEqualNP.Outside.L_meta_36292.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 2 := bs0_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
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
theorem bs2_2_0 : Interval s2Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 10 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 60 := (concat bs2_3_0 bs2_3_32)
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
theorem bs2_4_160 : Interval s2Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 165 := (concat (concat bs2_4_0 (concat bs2_4_32 bs2_4_64)) (concat bs2_4_96 (concat bs2_4_128 bs2_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 50 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 60 := (concat bs3_3_0 bs3_3_32)
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
theorem bs3_4_160 : Interval s3Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 165 := (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 50 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 12 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 91 := (concat bs4_3_0 (concat bs4_3_32 bs4_3_64))
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
theorem bs4_4_704 : Interval s4Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_736 : Interval s4Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 794 := (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat bs4_4_288 (concat bs4_4_320 bs4_4_352)))) (concat (concat (concat bs4_4_384 (concat bs4_4_416 bs4_4_448)) (concat bs4_4_480 (concat bs4_4_512 bs4_4_544))) (concat (concat bs4_4_576 (concat bs4_4_608 bs4_4_640)) (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 bs4_4_768)))))
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
theorem bs4_5_704 : Interval s4Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_736 : Interval s4Atlas 5 736 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 741 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat bs4_5_96 (concat bs4_5_128 bs4_5_160))) (concat (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)) (concat bs4_5_288 (concat bs4_5_320 bs4_5_352)))) (concat (concat (concat bs4_5_384 (concat bs4_5_416 bs4_5_448)) (concat bs4_5_480 (concat bs4_5_512 bs4_5_544))) (concat (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)) (concat bs4_5_672 (concat bs4_5_704 bs4_5_736)))))
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
theorem bs5_3_64 : Interval s5Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_128 : Interval s5Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_160 : Interval s5Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_192 : Interval s5Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_224 : Interval s5Atlas 3 224 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 228 := (concat (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96)) (concat (concat bs5_3_128 bs5_3_160) (concat bs5_3_192 bs5_3_224)))
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
theorem bs5_4_768 : Interval s5Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_800 : Interval s5Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_832 : Interval s5Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_896 : Interval s5Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_928 : Interval s5Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_992 : Interval s5Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1024 : Interval s5Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1088 : Interval s5Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1120 : Interval s5Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1184 : Interval s5Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1216 : Interval s5Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1280 : Interval s5Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1312 : Interval s5Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 bs5_4_192) (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)))) (concat (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 (concat bs5_4_416 bs5_4_448))) (concat (concat bs5_4_480 (concat bs5_4_512 bs5_4_544)) (concat bs5_4_576 (concat bs5_4_608 bs5_4_640))))) (concat (concat (concat (concat bs5_4_672 bs5_4_704) (concat bs5_4_736 (concat bs5_4_768 bs5_4_800))) (concat (concat bs5_4_832 bs5_4_864) (concat bs5_4_896 (concat bs5_4_928 bs5_4_960)))) (concat (concat (concat bs5_4_992 bs5_4_1024) (concat bs5_4_1056 (concat bs5_4_1088 bs5_4_1120))) (concat (concat bs5_4_1152 (concat bs5_4_1184 bs5_4_1216)) (concat bs5_4_1248 (concat bs5_4_1280 bs5_4_1312))))))
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
theorem bs5_5_768 : Interval s5Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_800 : Interval s5Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_832 : Interval s5Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 890 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat (concat bs5_5_96 bs5_5_128) (concat bs5_5_160 bs5_5_192))) (concat (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)) (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 bs5_5_416)))) (concat (concat (concat bs5_5_448 (concat bs5_5_480 bs5_5_512)) (concat (concat bs5_5_544 bs5_5_576) (concat bs5_5_608 bs5_5_640))) (concat (concat bs5_5_672 (concat bs5_5_704 bs5_5_736)) (concat (concat bs5_5_768 bs5_5_800) (concat bs5_5_832 bs5_5_864)))))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 17 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 65 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_128 : Interval gbAtlas 4 128 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 151 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
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
theorem bgb_5_1056 : Interval gbAtlas 5 1056 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1084 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))) (concat (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896)) (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056))))))
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
theorem bgb_6_1952 : Interval gbAtlas 6 1952 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1964 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960))))) (concat (concat (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184))) (concat (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440)))) (concat (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696))) (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 bgb_6_1952))))))
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
theorem bgb_7_960 : Interval gbAtlas 7 960 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 978 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448)))) (concat (concat (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 bgb_7_576)) (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 bgb_7_704))) (concat (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 bgb_7_832)) (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 bgb_7_960)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8feeefee8feeeaaa8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075688 * 2 ^ 32 + 4277054120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36292.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.and,[0,1]⟩,⟨.or,[2,3]⟩,⟨.or,[0,5]⟩,⟨.or,[0,1]⟩,⟨.and,[8,9]⟩,⟨.or,[7,11]⟩,⟨.or,[4,12]⟩,⟨.and,[10,13]⟩,⟨.and,[6,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4277054120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4277054120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36292

open PEqualNP.Outside.L_meta_36292 in
theorem PEqualNP.Outside.L_meta_36292 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4277054120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4277054120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
