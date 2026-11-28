import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36350.Model
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


end PEqualNP.Outside.L_meta_36350.Model

namespace PEqualNP.Outside.L_meta_36350
open PEqualNP.Outside.L_meta_36350.Model
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

def SB : Nat := 7

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 49]

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

end PEqualNP.Outside.L_meta_36350

namespace PEqualNP.Outside.L_meta_36350
open PEqualNP.Outside.L_meta_36350.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x62a2ab00582998e9dc0d9d1fa10004000740b40c1eca52066c10078809000004ac036b9a0163140b80000421c004308200228bff42bf42fe42fd42bd42fc42ff41fe41fd41fc41fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fd41083f882107f8c420fe98841fc31083fe42107f88420fe90841fc21082fca0107fd0020ff20041fd40083f880107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7887f94f10bf29e21fd53c42faa7887f14f10be29e21ff43c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c437e85887f90b10fea1621bd42c43f885887fccb10ff19621fd32c43f865887fd0710ff20e21f641c43fa83887d50710fe20e21ff31c43ee63887f8c710fe98e21fc31c43e863887fc8710ff10e21f621c43fa43887d48710fe10e21ff40c43fc81887f50310fe20621ff30c43fe41887f88310fe90621fc20c43fea9085fd5210ff2a4217e54843faa9085f55210fe2a4217c54843fea7085fd4e10ff29c217e53843bca7085794e10fea9c217d53843baa7085754e10fe29c21ff43843fc87087f50e10fe21c21ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff428437e85087f90a10fea1421bd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21fe41843fa83087f10610ff98c21fe31843fa63087f0c610ff90c21fe21843fa43087f08610bf28421ff40843fc81087f50210fe20421ff30843fc61087fc8210ff10421fa20843fa41087e48210fe10421ff10843ee21087ec4210ffaa2217f544437ea8884fd5110ff2a2217e54443faa8885f55110fe2a2217c5444378a8884f15110ffa9a217f53443fca6885f94d10fea9a217d53443f8a6885f14d10ffa1a21fe43443fa86887f10d10ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221bf42443fc84887f50910dea1221fc42443fe64887f8c910fe99221fc32443fe82887f90510fb20a21fd41443ea82887f10510ff98a21f731443fc62887f4c510fe18a21f431443fe42887f88510fb10a21fd21443ea42887f08510ffa0221fe40443fa80887f10110ff98221fe30443fa60887fc8110ff10221fa20443fa40887e48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021fd52042faa4087f14810be29021ff420437e84087f90810fea1021bd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0x950086f2a010ff14021ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a06fd0b40ff21681fd42d037a85a07f10b40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fc63a07f4c740fe18e81ff21d03fc43a07f48740fe10e817d54903fea5207f94a40bf29481fd52902faa5207f14a40ffa1481bf42903fc85207f50a40dea1481fc42903fea3207f94640bf28c81fd51902faa3207f14640ffa0c81fe419037c83207f50640fe20c81bc41903fc63207f4c640fe18c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940dfa1281fe42503fa84a06f50940fe21281ff51502fea2a07f94540fea8a81fc51502f8a2a07fd0540ff20a81fd41503f882a07f8c540fe98a81fc31503fe42a07f88540fe90a81fc21503fe80a07ed0140ff20281be40502fca8207fd4840ff290817e52103dca4205b94840fea90817d52103daa4205b54840fe29081ff421037e84207f90840fea1081bd42103f884207fd4440ff288817e51103eca2205d94440fea88817d51103eaa2205d54440fe28881ff41103fc82206f90440fea0881fc411037882207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9905fd5320ff2a6417e54c837ca9904f95320feaa6417d54c837aa9904f55320fe2a6417c54c83fe85906fd0b20ff21641ee42c83fa85906f50b20f6a1641ad42c83f885907fd4720ff28e417e51c83faa3905f54720fe28e41ff41c83fc83907f50720fe20e41fe31c83fa63907f0c720ff90e41fe21c83fa43907f08720ffa0641fe40c83fa81907f10320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220bea9441ff428837e85107f90a20fea1441bd42883f885107fd4620ff28c417e51883faa3105f54620fe28c41ff41883fc83107f50620fe20c41fe31883fa63107f0c620ff90c41fe21883fa43107f08620bf28441ff40883fc81107f50220fe20441ff20883de41107ec8220ffaa2417f54483fca8905f95120feaa2417d54483f8a8905f15120ffa1241bf42483fc84907b90920fea1241bd42483da84906b50920fe21241ff51482fea2907f94520fea8a41fc51482f8a2907fd0520ff20a41fd41483f882907f8c520fe98a41fc31483fe42907f88520fe90a41fc21483fe80907f90120fea0241fc40483fe40907ec8120ff10241ee20483fea8105fd5020ff2a0417e540837ca8104f95020feaa0417d540837aa8104f55020fe2a0417c54082fca4107fd0820dfa1041fe42083fa84106f50820fe21041ff51083fca2105f94420fb288417651083faa2105f54420faa88417551083f8a2107fd0420ff20
  | 2 => 0xc7fca518df94a31fea94637d528c7f8a518ffd0a31dfa1463fe428c7fa8518ef50a31fe214637e518c7fe8318ff90631fea0c63fc418c7fe6318fdcc631ffa8463fe508c6fca118ff54231bea8463fc508c7fea898dfd5131ff2a2637e544c7faa898df55131fe2a2637c544c7fea498dfd4931ff29263fd524c7f8a498df14931ffa1263bf424c7fc8498ff50931dea1263fc424c7fe8298ff90531fea0a63fc414c7fc6298f78c531ffa82637f504c7fca098ff54131fe282637c504c7fea818dfd5031ff2a0637e540c7faa818df55031fe2a0637c540c7fea418ff94831bf29063fd520c6faa418ff14831ffa1063bf420c7fc8418ff50831dea1063fc420c6fca218ffd0431ff20863fd410c7f88218ff8c431fb18863fd310c7ea6218f54c431ffa8063fe500c6fca018ff54031bea8063fc500c7fea990dfd5321ff2a6437e54c877ca990cf95321feaa6437d54c877aa990cf55321fe2a6437c54c87fea790dfd4f21ff29e437e53c87faa790df54f21fe29e43ff43c87fc8790ff50f21fe21e43ff42c877e8590ff90b21fea1643bd42c87f88590ff8cb21ffa0e43fe41c87fa8390ff10721ff98e43f731c87fc6390ff4c721fe18e43f431c87fea190ff94321bf28643fd50c86faa190ff14321ffaa4437f54887fca910df95221feaa4437d54887f8a910df15221ffa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21ff21c43fd43887f88710df54a21ffa1443bf42887fc8510ff50a21dea1443fc42887fe6510ff8ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310fd8c621fe98c43f531887f86310ffc8621f790c43f721887fea110ff94221bf28443fd50886faa110ff14221ffaa2437f54487fca890df95121feaa2437d54487f8a890df15121ffa9a437f53487bea690d7d4d21ff29a437e53487faa690df54d21fe29a437c53487b8a690d714d21ffa1a43fe43487fa8690ff10d21ffa1243bf42487fc8490ff50921dea1243fc42487fe6490ff8c921fe99243ff41487fc8290ff50521fe20a43ff31487fc6290fd8c521fe98a43f531487f86290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043be540867ca810ff55021beaa043bd540867aa810ff15021be2a043ff53086fea610ff94c21bf29843de53086bca610ff54c21bea9843dd53086baa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410efd0821ff21043fd420877a8410ff10821ff99043fe32087fa6410ff0c821bf28843ff41087fc8210ff50421fe20843ff31087ee6210ff8c421fe98843fc31087e86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fa50086f4a010ff54021bea8043f
  | 3 => 0x803c00402400405c02c01000000c00000000400000000000c00002006001801401804800006c0000000180540c800400405c01400c01400c00400000000000401000c00c00c05003804003c00806800000402002400000804006c0040480b403400000000800c00400400400001000c00000401800005800814c00c0180c800004402800400403400404007800c01000409c00000000405c00000000006800400000001000405006c00000007800403c03800400000401000c00400001800c06c00800000c00000000000800000c00000000800002400c03800800c00000c00403001800800402411400800c06c00002c03005400c00801000c00c00400006007c01800000400000004ffea3a17f94742bf28e85fd51d0afaa3a17f14742ffa8685fe50d0afca1a17f54342bea8685fc50d0b7ea3a16f94742dea8e85bc51d0b7ea1a16f94342dea8685bc50d0afaa9214f55242bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa1285ef4250bfc84a16f90942ffa8a857f5150bfca2a17f54542fe28a857c5150bfea0a15fd4142ff28285fd5050bf8a0a15f14142dfa9285af5250b7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050afca8214f95042bf29085ff4210b7e84217f90842f721085fd4210b7a84217b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea0217f94042bf28085fd5010afaa0217f14042ffa9e83fe53d06fca7a0ff54f41bea9e83fc53d07fe87a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d077e85a0ff90b41fea1683bd42d07f885a0ffd4341ff286837e50d07faa1a0df54341fe286837d54907fea720ff94e41bf29c83fd53906faa720ff14e41ffa1c83fe43907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483bf42907fc8520ff50a41dea1483fc42906fca320ffd0641dfa0c83f741907fea120ff94241bf28483fd50906faa120ff14241ffa9a837f53507fca6a0ff54d41fe29a837c53507fe86a0ff90d41fea1a83ff52506fea4a0ff94941fea9283fc52506f8a4a0ffd0941dfa1283fe42507fa84a0ef50941fe21283ff41507ee82a0ff90541df20a83ff50506fea0a0ff94141fea8283fc50506f8a0a0df95041ffa9883fe53106fca620ff54c41bea9883fc53107fe8620ff90c41fea1883fc43107fea420ff94841bf29083fd52106faa420ff14841ffa1083bf42107fc8420ff50841dea1083fc42106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df15231bea9c63ff438c7fc8718ff50e31fe21c63ff528
  | 4 => 0xf58001fd9164000f19cf236c00229c000001778000189c400012997097540010600000000019087b4000898721b50261025fd0de8b6a1c000055c0002780000019011485a61200003487cc0008f8001671a98000001f7c311ac0001dc8000a9a365a21e71b0cfe9810f700000011fdff8ab52d80004e4c34ba84d0ec0d31de0000d50fa179a220a6985d0a8ea0139c955e4d890313f1f784fd3ed425058119c8a215a911193d060c001cc8bb0bf227ca78d6d080089508f992496b8328b010f9f8955d8ba2c80003d9c012f1c582d0d01e312b8b2572862c5998a0000000c405ba248000000000000000400001929e50e88eecfd1110c6c0016fc00000000178c638000d981ed9221e0d68508c900000000000012e80000000000000000015700020300003722b2018b1dfb0ee80000013300000000017680000008916d8001170450000001539c30ab920163208075de905c40000010a140c83d9486c43ea10ccd0000000002338000001c1c000000000000000f6000136d3dc001581940b28001d756485047e9001831281021394dd8b38cb0f80b340015b94c0ce8001cd80009f800000182a05203df6e331a402da21814e0a2079ea1e58af423096d688d088387fd23c4c4d24a60c31069fc0c104dc001c08e9400115e205440e6146103c635730074000f35f686d21094b80004208b9039be1eb8f2a0e803c002128a815c400401c00401001000801400400001c03012401000400401000000c00000000802000008c0280240a400c00000401404400000002000402c00000001400008400800803002801000000006c0000000080b002400800400401c03c0540580340000100540200080140040200100cc00000000800006402400804001808803400802000000c02800800000000000000c01005c04c00000000001800002802c01c01001005c00400c00000003400001c03802c00000800800000401400005c00001002400002801c0000180300bc05400404400000401803000400002400c0000000200040140180100000080400080040000300100bc04002400805002800001401800403000000000000400001004400000001801401805401401801800000800003800001400c00402403002c01401400009000408001800001405c00401800000000402c00800800801800000000400001000000001801801801005000800800800401000010004000c00000800000001c0400000180880a001800c00000801c01403c05800000400004800406400001c00c00000400000000806c01c03400404c00400c00806c00002000400c01401800c00401802002802001400001000000000c00400800400000005c0280000580100d400c0000140000180000680040100100b016801001802400002801000000804c0080180f803000800000001c00
  | 5 => 0x518d05d1381205d6d4d87a836807a07211014424a2e93a8d416e1b221683847e1b722809f1eca0998dc59d7e58649114b19fc050d80218eb102cd210b9b58860700ce1121685668abc5320485504e81a91393b9a0942a0362e0e90934d3a1a99f82980000000840000002b4c3c0000000000023540015ec0f00000018e920c4e0ac46e0a0a0f400086a020f90ea8e59dccb488d000219c769d094a84fa2008f0628b880021c92707a10f15bd79404c98000098e35c8095501b400000213917871611c0000000018900000020e0000000000001cc1c506dc000d92209aa800057205975dd48c760540000021a40015d0000000000000001265a29358001f803b800117c844e280001400013f80000000019b8e4a21c991f387817a15e1c918740000023010100000016593740000000007d40015dd3c147214a260728938081064000800000ff00001098c1aa0d9c2f0114d753b08a9049d560b85c07c8318009d1a119575eb1e7e1598bd5acc20ef577c491a00b18d3500a1e82b9ab0048b21cb93d49d91a227085a230268c01fb97480f85003c91151f146858882c12df1200a0b0ba0d2cc19716195cd1ba9388f21968210330840238da5600f794ece9d9607f44689752d17b0001cf899c4c122c000ae589800065874d8704da311e289286500000015f5f1a26a29057a0f037a329e00aa87c60c8730774a58ea415c001c84f04000db8f1cb51e21300000000d8d06d5495cdaf5b30689d710c06800000000013282094912380a89bce306ee044af1341df9c2554179c3962f00012b21062d9045df148a1d9e61e881f15222943d06fde19db044875918dc71a111c03b57d92887f8f2db899f4128958fc07797d12600009680005293e00cc398a3829d7812f8ec819c00025c00000084d0e0c60c55d980014f9d891600019887908a16c81e9b60ffcc818a91e82e01a0000c7942029030998235a08976e2b8000000f01c461f80000000005a8000000b2c0000000000000000000019ddd800010040000000018e07e46686602819d92a8000b79710c0c000000f39be88d80015fc0006200013496280003f02a09940000000000000000000004ccd55209bd9ca4ac1e817a4514ae1228ef80000000000011e15f8ec4c15b998f96d1b499d07040008e8c5ca503400019e95100018cd7200c8624a88d1a1b8f41bf93780e04651d02fd398da00009b5d646e5a78001fa0000001f28060a90afd48d244854e803551b23698605b4001c8d758000d61c221d161a02c001881599f49ad1ec07d913ccca0f8e19c98548df85609e894ced83640007b8a31240000000af813c000388000dc00000000020601902945d44987080000006b9f5c9195a86b1a7008e31a0c0f500015b43a1055e40000001d3914c2a80000000000017e0002345c34350fb8f440017f1
  | 6 => 0x20c680005205180000013214f00017380018b4600002189b017745f800093e001d300000010347b12520a8a18000b31199818c883f453842a2580000000020294100021b00000000020d09c000000043000000000105c000b080980013184d40000000000007c0000000c447ece51fe09440000000000000000016c0001ecd4e88940000000000020922d08c4bc09d2238001168000001b280000000000018d4000001d69ab8000db0000a4800000176174038dce9a045bd8546f11b937d5010180000006d634dc295b01b141d4300009a9029fa847400187c000000160e212e0000000e416214802ac50d1095e955400000112a288410b14dc9b08000eacd3c1109d5f6618154cc298f1d40b60610c70158d12210fa8f59f08c38d94264631ee8a283906093c9d016f5dd8e71f91ac8000001ae427c000002068001675a691556ec0000003fc9ac000000000001e5d181478121f618ed3d80015a43e1f31274a1156228c479611c3c172190250830590000000000000000001d102580012a1150000000c59cb0000065744754d7c0000003c47ac001820b71186284000a700008c9e79a885a07484a0000070aed578029d918155587706d9e10f150b0964b8018db6816800138cf8800222923625035d2785e0b99da17a85d87bcd852680013f40000009cc7118c4000920a421008e08880011a8000000094045dbc0004f1b10c84001d509b9088001451a80f2500c4a80009a0f3c78a2a0001bc0000970374000e78cc1ee00001a6309d5cfd800000000125dafc0021780009e10fc000000001db80000000000007d0000c982f8e096780000000005de039135f00c1d448011a501342c00010d9ea9e399c0a218f5634000be984082048a1f4000001c68201ed97c8dd16f0000000001158018f319e5ef80000006799582e8000ad1368efc0d83b06705822f400000139131043824230c82904c002241771219951d7c5cc001c380009a4de0cd9a61ad80411f9850a0116c0918381f87f13a0ab1a0da19789879ca8125af07619f08c19a0155a490715c0bc92c9c785586983040e95a13083e46c8960738690d5c6c04f5dd12109404bcac9f74f68001849f99101d2a305da8cb89c4b100dc5104c9984fc83c18893e98096b2130130001a58424871bd0ed46e80009000009b00012540018ad999f700018b163807c5686f8055640849ff15297c046097c909190001dc4810001e6c418000000cf8c640003f8000000000e10000000000002350df05b000000114601125a2c0000ee479800000000097800000127c0000000001ac000001a38000000000694000f10002114001680818000000151fc8358000000274001409ae22a8220998ee0000000fb00000014e054458c0016e90980019e0e68ca90d0441690b0586831524c0b0069405d600d13
  | 7 => 0x300000880bd0ecc320cf0ef00021f1698228d70000c4d43876d42c649fe8001918bd8640289105ce1fbd459991cd4e019c9e65765661bba20c0003395d8e39aec000000f0c1c22f83a8001911c7c00000000000000156910d49d934c7cc491d89323615320d81fdc48594b0da31f41221f20ad9ba00000007dc001230000ae8000148002151400000000000001d214d109000070dbb02bc26cca00013fdc601b99edaf8001e08d2926c952274d78198001750751c198c94185ac1e10c83ede84e980395f06a8ff40006a05c80300000c51c9050001b18718271d58002160000000000058000000da98d979010d4ca041971f55c8000037dde811d5885f1ca1978fe0f08000740100c04618be11305e8f489499b0470b901d80009c93380010417004b0000d661fd6504b94354a0bf88b22fdbe627980000006e198381939b80001f50408000edde9a1ad0740003600016a822c0000021700008795c9bc8001b79b39930c50b40001d782b00000000000000019cdbf039d7b80019a81d16f9175c2dec40000002f4000bb912c0000021a149a32018000054dae92c0459ed171861cace04c0c2298000ff9ef2341291370b580013cc36d18800000121400031c0a160a3498580000017fa140000d48000000c081c80002c8984d590e97e8aa1079e68001e48284850eb9b918e5b04179dc0001591e755d4ed00b9360541c10001b402a55180009893e56a20fd14048
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x4320427c650c810af99032042bd640c810bd98432042f5610c810be98032042f9600c8109f992510427d64944109f58e510427e62944109f58a510433f4294410cf50a510427d65d04109fd96410427d6590410cf952410433d5490410dd94641042fa6090410be582410427f6550410dd945410427f65104109f594410433e5410410cf55041042fa6010410be580410427d65cc410dd947310427f658c4109f596310435e538c410d754e31042fa608c410be582310427f654c4109fd94310427d650c410d794c310435d530c410dd94431043d5310c410be98031042f9600c4109f59721042be64c8410af593210427f65884109f596210436e5288410db54a21043765188410be98221042f960884109fd9521042df6348410b718d210437651484109fd94210427d6508410af99021042bd6408410b798c21042dd6308410db948210436d5208410be98021042f960084109f992500427d64940109f98e500435e63940109798e500427d6394010d758e500425d63940109f98a500427d6294010cfd0a500433d42940109f586500427d65d00109fd96400427d6590010cf952400433d5490010bd98640042f561900109fd95400427f65100109f994400427d65100109f194400433e5410010cf55040042de6310010b758c40042ee6210010bb58840042f66110010bd584400427d65cc010d7d4f300427f658c0109f596300435e538c010d754e30042f6618c010bd586300427f654c010afd9130042bc644c010d7d4d300427e650c0109f594300427c650c010bd98430042f5610c0109f59720042be64c8010af59320043ad42c80109fd96200427d6588010db94a200436d5288010bd98620042f56188010de942200427f6548010eb509200437a50480109fd94200427e65080109f594200427c6508010af99020042bd6408010b798c20042dd6308010db948200436d5208010bd98420042f56108010dd597100437754c4010dd553100437653c4010dd14f100437752c4010dd54b10043b742c4010ed50b10042de6384010b758e10042f56184010dd94610042f96584010de59610042796584010f698e10043d96384010ded4a10043795284010eed0a10043b94284010be586100437a5184010fc946100427f6544010afd9110042bc6444010bdd95100437765440109dd9510043b76444010ed19110043775444010dd55110043765344010dd14d10043775244010dd54910043b74244010ed50910042f76044010dd94110043f34044010fc10110043f23044010fc4c110043f22044010fc48110042fb6544010ded95100427b6544010eed9110043b86444010ded4910043795244010eed0910043b94244010bed8510043f36144010de94510043f25144010fcd0510043f04144010fc8c510043f13144010fc88510043f12144010
  | 1 => 0x427e64d4c109f593530427e62d4c109f58b530437661d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c10af99053042bd6414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430427f6590c109f996430427d6590c109f196430435e5390c10d754e43042f66190c10bd58643042fa6090c10be582430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d430427f6510c109f994430427d6510c109f194430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810af99252042bd6494810dbd4a520427e6494810cf992520423e64948109f592520433d64948108f592520427e63948109f58e520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427661148109f980520437a60148109e980520427f65d08109f997420427d65d08109f197420433f54d0810cf953420433d54d0810cf153420433f65d0810cf997420433d65d0810cf197420433f53d0810cf94f420433d53d0810cf14f420433f52d0810cf94b420433d52d0810cf14b420427f65908109f996420427d65908109f19642042bd6490810db94a420436d52908109fd95420427e65508109f595420427c6550810cfd51420433e5450810cf551420433c5450810db949420436d5250810bdd8542042f46150810bed8142042f86050810cfd95420433e6550810cf595420433c6550810cfd4d420433e5350810cf54d420433c5350810ebd89420433f5250810cf94942043ae5250810cb949420433d5250810eb549420432d5250810cf14942043b76150810ed18542043bb6050810ee181420427f65108109f994420427d65108109f19442042be64108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc8109fd96320427e658c8109f596320427c658c810af99232042bd648c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c810bdd8532042f4614c8109fd94320427e650c8109f59
  | 2 => 0x6048510fc181214427e6508510af99021442bd6408510cfd50214433c5408510b798c21442dd6308510bd98421442fa60085109f997404433f54d0110cf15340442f661d0110bd587404427e6590110cfd52404433c5490110ed906404427f65501109f595404427c6550110cfd51404433c5450110bdd8540442f461501109f994404433f5410110cf15040442de6310110b758c40442ee6210110bb58840442f66110110bd58440443b64110110ee500404427e65cc110cfd53304433c54cc110d7d4f304435c53cc110bd98730442f561cc110f50c7304433f548c110cf15230442f6618c110bd586304427d654c1109f195304433f544c110cf15130442f7614c110bd18530443d4314c1109f99720442be64c8110af593204433f54c8110cf153204436f52c8110db14b20443ad42c8110bd98720442f561c81109f996204433f5488110cf15220442fa6588110de99620443bb5488110ee152204437b5388110de54e20442f96288110de94a20443785288110eed0a20443b94288110fcd8620442fa6188110fc18620443f24188110fc50620443f33188110fc0c620443f22188110fc486204427f65481109f595204427c6548110cfd51204433c5448110dbd49204436c5248110eb50920442f76148110bd18520442f86548110de19520442786548110eed5120443b85448110ded4d20443795348110fad8920443eb5248110de94920443785248110fa14920443bb4248110fa90920443b94248110fa50920443a94248110fcd8520442f86148110fc18520443f24148110fc50520443f33148110fc0c520443f22148110fc485204427e6508110af99020442bd6408110cfd50204433c5408110b798c20442dd6308110bd98420442f56108110be980204433f54c4110cf15310443bb54c4110ee15310442fb62c4110be58b10443bb42c4110ee50b10443f241c4110fc50710443f331c4110fc0c710443f221c4110fc487104433f5484110cf15210442de6384110b758e10442f76484110bd59210443b75484110ed15210442f66384110f598e10442d66384110f558e10442f76284110bd58a10443b74284110ed50a10443f35084110fc88210443f120841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109d984540427e6015010de980540
  | 3 => 0x9109f997324427d65cc9109f197324433f54cc910cf153324435e53cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910af99232442bd648c910cfd52324433c548c910d7d4e324435c538c910bd98632442f5618c910be98232442f9608c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910d794d32442f7614c910bd185324427f650c9109f994324427d650c9109f19432442be640c910af590324433f540c910cf150324435f530c910d714c324436f520c910db14832442f6610c910bd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f996414433f5490510cf15241442f66590510dd99641442f56490510edd5241443765490510dd15241443b45490510cd15241442f66390510bd58a41443b74290510ed50a41442f660905109f195414433f5450510cf15141442fb6050510be181414437465505109d19541443b76450510edd5141443765450510dd15141443b45450510bd18d41442f76250510edd0941443b54250510fcd8141442f46050510fc18141442f060505109f994414433f5410510cf15041442f66110510cfd53314433c54cc510d7d4f314435c53cc510be98331442f960cc510dd99731442f764cc510bd59331443b754cc510ed153314437753cc510f5d4f31443d453cc510bd58b314437652cc510dd14b31443b742cc510ed50b31443d732cc510f54cb31442f660cc510fc98331442f260cc510fc583314427e658c510cfd52314433c548c510d794e314435d538c510bd986314433f544c510cf151314435f534c510d714d31442fb604c510be181314427e650c510cfd50314433c540c510d794c31443d5310c510bd9943144376650c510bdd9031442f5640c510edd5031443b4540c510bd98c31443d6630c510ddd4c31443d6530c510dd54c31443d5530c510d554c31442f5620c510dd9483144374520c510edd0831443b5420c510f58c831443d4320c510bd980314427e65c8510af99321442bd64c8510cfd53214433c54c8510dbd4b214436c52c8510be98321442f960c85109f996214433f5488510cf15221442f66588510dd99621442f76488510bd59221443b75488510ed15221442f66388510bd18e21443775388510dd54e21442f56288510dd94a21443745288510edd0a21443b54288510fcd8221442f66088510fc182214427c6548510cfd51214433c5448510b7d8d21442dc6348510dbd49214436c5248510bed8121442f86048510dd19521442746548510bdd9121442f56448510edd5121443b45448510f5d8d21442f66348510bd18d21443d46348510b518d21443775348510dd54d21443e76248510f9d4921443765248510dd14921443e45248510edd0921443b54248510fcd8121442f4
  | 4 => 0xf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534427f6254d10dbd89534426f6254d109f189534436c6254d109b18953443776154d109fd81534437b6054d109f994534433f5414d10cf150534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427c6114d109fd97434427e65d0d109f597434427c65d0d10cfd53434433c54d0d10bd98743442f561d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10bdd8543442f46150d10bed8143442f86050d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10bd98443442f56110d10be98043442f96010d10cfd53524433c54d4910cfd93524427e64d49109f593524433c64d49109f98f524427d63d4910af99252442bd6494910cfd52524433c5494910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910cfd51524433c5454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910af99052442bd6414910cfd50524433c5414910b798c52442dd6314910db548524427e6414910cf990524423e64149109f590524433d64149108f590524427e6314910d798c524425e63149109f58c524435d63149109758c524436e62149109f984524437561149109f184524427e6014910de580524427c60149109fd97424427e65d09109f597424427c65d0910cfd53424433e54d0910cf553424433c54d0910bd98742442f561d0910cfd9742442be65d0910cf997424423e65d0910cf59742442bc65d0910cf197424423c65d0910cfd4f424433e53d0910cf54f424433c53d0910cfd4b424433e52d0910cf54b424433c52d0910ed98742443b561d09109fd96424427e65909109f596424427c6590910af592424433f5490910cf15242442f66190910bd58642442fa6090910be582424427f65509109f995424427d65509109f195424433f5450910cf951424433d5450910cf151424433f6550910af995424433e65509108f995424433d6550910af195424433c65509108f195424433f5350910cf94d424433d5350910cf14d42443af6250910cfd49424433e5250910cf549424433c5250910ed98542443b561509109fd94424427e65109109f594424427c6510910af990424433f5410910cf15042442f66110910bd58442442fa6010910be580424427f65cc
  | 5 => 0x218435d5388610b7d8d21842dc6348610d794d218435d5348610db949218436d5248610bed8121842f86048610af99021842bd6408610b798c21842dd6308610d794c218435d5308610be580218435e53d0210d754f408433e5490210cf552408435e5390210d754e40842f66190210bd586408435e5350210d754d408433e5410210cf55040842de6310210b758c408435e5310210d754c40842ee6210210bb58840842f66110210bd58440843b94010210d794f308435d53cc210bd98630842f5618c210af99320842bd64c8210d794f208435d53c8210eb50b208435e5388210d754e208436e5288210db54a20842f66188210bd58620842f96588210de596208437b5388210f694e20843795388210f654e20843595388210de94a20843ea5288210fa54a20843785288210eed0a20843b94288210be98620843f26188210fc586208435e5348210d754d20843ad4248210bed95208437b6548210ded4d20843da5348210de54d20843d95348210d654d20843eb6248210de94920843785248210eed0920843ea4248210ee50920843e94248210ea50920842f86148210af99020842bd6408210b798c20842dd6308210d794c208435d5308210db948208436d5208210bd98420842f56108210d794f108435d53c4210bd597108437565c4210ddd53108437554c4210dd94f10843d653c4210d594f10843d553c4210ddd4b108437552c4210edd0b10843b542c4210be597108437965c4210f694f10843d953c4210bed8b10842f962c4210eed0b10843b942c42109f98f544427d63d51109f98b544427d62d5110af58b54443b761d5110cfd8f544433e63d5110cf58f544433c63d5110cfd8b544433e62d5110cf58b544423d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f54951109f992544423e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110cfd91544427f63551109f18d544427f62551109f189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544437561151109f184544427e60151109f18054442be6515110cf994544423e6515110af58854443b56115110cfd8c544433e6315110cf58c544433c6315110cfd88544433e6215110cf588544423d6215110cf188544433f6115110cf58454443356115110cfd80544433d6015110cf440544433f54d4d10cf153534427e64d4d109f593534427e62d4d109f58b534437561d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6294d109f58a53443756194d10de58253442bf6454d10af191534433f5454d10c
  | 6 => 0x27d6510e10d794c438435d5310e10be98043842f96010e10b798f52842dd63d4a10d794f528435d53d4a109f993528427d64d4a109f98f528435e63d4a109798f528427d63d4a10d758f528425d63d4a10dd587528437a60d4a10af99252842bd6494a10d794e528435d5394a10dbd4a528427e6494a10cf992528423e6494a109f592528433d6494a108f592528427e6394a109f58e528437a6094a10d794d528435d5354a109fd91528427c6454a109fd8d528427c6354a10dbd8952842be6414a10af59052842de6314a10b758c528435e5314a10d754c528436d5214a109f990528433e6414a108f990528427d6414a10cf590528423d6414a109f98c528435e6314a109798c528427d6314a10d758c528425d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428433f54d0a10cf953428433d54d0a10cf153428435e53d0a10d754f428433f65d0a10cf997428433d65d0a10cf197428433f53d0a10cf94f428439e53d0a10c794f428433d53d0a10e754f428431d53d0a10cfd4b428433e52d0a10cf54b428433c52d0a109fd96428427e6590a109f596428427c6590a10d794e428435d5390a10db94a428436d5290a10be98242842f96090a109fd95428427e6550a109f595428427c6550a10cfd51428433e5450a10cf551428433c5450a10d794d428435d5350a10db949428436d5250a10bdd8542842f46150a10cfd95428433e6550a10cf595428433c6550a10cfd4d428433e5350a10e794d428431e5350a10cf54d428439d5350a10c754d42843af6250a10cfd49428433e5250a10eb949428432e5250a10cf54942843ad5250a10cb549428433c5250a10edd8542843b46150a109fd94428427e6510a109f594428427c6510a10d794c428435d5310a10be98042842f96010a109fd97328427e65cca109f597328435e53cca10d754f328427f658ca109f996328427d658ca109f19632842be648ca10af592328435e538ca10d754e32842fa608ca10be582328427f654ca109f995328427d654ca109f195328435e534ca10d754d32842f7614ca10bd185328427f650ca109f994328427d650ca10af99032842bd640ca10d794c328435d530ca10bd98432842f5610ca10be98032842f9600ca10cf953418433d54d0610d794f418435d53d0610be98341842f960d0610cfd52418433c5490610d794e418435d5390610cf951418433d5450610d794d418435d5350610bed8141842f86050610cfd50418433c5410610d794c418435d5310610d794f318435d53cc610be98331842f960cc610d794e318435e534c610d754d31842fb604c610be181318435e530c610d754c31843d5310c610af99321842bd64c8610d794f218435d53c8610db94b218436d52c8610be98321842f960c8610d794e
  | 7 => 0x30c710f594c31c4375530c710f554c31c4355530c710bd58831c4376520c710dd14831c43b7420c710ed50831c43d6320c710f50c831c42f6600c710fc98031c43f1600c710af99321c42bd64c8710db94a21c436d5288710be98221c42f96088710dd59621c42f76488710bd59221c42f66388710bd18e21c43755388710dd94a21c43e65288710f954a21c43745288710edd0a21c43b54288710bd98221c43f26088710fc58221c42df6348710b718d21c42f76548710ddd9521c42f76448710bd59121c43d76348710bd98d21c42f46348710f518d21c42d46348710dd54d21c43e76248710dd94921c43745248710edd0921c43b54248710bd18121c42be6408710af59021c42de6308710b758c21c436e5208710db54821c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c433f5490310cf15240c43b64190310cf95140c433d5450310bdd8540c42f46150310cfd5040c433c5410310b798c40c42dd6310310bb98840c42ed6210310bd98440c42f56110310ed90440c42f661cc310bd58730c43d431cc310af99320c42bd64c8310db94b20c436d52c8310eb50b20c42f661c8310bd58720c436e5248310db54920c43ad4248310bdd8520c42f46148310af99020c42bd6408310b798c20c42dd6308310bd98420c42f56108310b798f54842dd63d52109f98f548435e63d52109798f548427d63d5210d758f548425d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548433f64552109fd8d548427c63552109fd89548427c6255210cf55054842de6315210b758c54842ee6215210bb588548433e64152109f98c548435e63152109798c548427d6315210d758c548425d63152109f988548436e62152109b988548427d6215210db588548426d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e10d7d52538435e5494e10d7552538435c5494e10d7d92538435e6494e10d7592538435c6494e10d7d8a538435e6294e10d758a538435c6294e10d7d86538435d6194e10d7982538435c6094e109fd91538427c6454e10d7d8d538427f6254e109f189538435f6554e10d7d51538435e5454e10d7551538435c5454e10d7d91538435e6454e10d7591538435c6454e10d7d89538435e6254e10d7589538435c6254e10d7585538435e6054e10d7181538435d5314e109fd97438427e65d0e109f597438427c65d0e10d794f438435d53d0e109fd96438427e6590e109f596438435e5390e10d754e43842f66190e10bd586438427f6550e109f995438427d6550e109f195438435e5350e10d754d43842fb6050e10be181438427f6510e109f9944384
  | 8 => 0x10d794f43c435d53d0f10bd98743c42f561d0f109fd9643c427e6590f109f59643c427c6590f10cf95243c433d5490f10be98243c42f96090f109fd9543c427d6550f109f19543c42f76150f10bd18543c427f6510f109f99443c427d6510f109f19443c433e5410f10cf55043c435e5310f10d754c43c42f66110f10bd58443c427e64d4b109f59352c427e63d4b109f58f52c437661d4b10de58352c42be6494b10af59252c436f5294b109f99252c433e6494b108f99252c427d6494b10cf59252c423d6494b109f98e52c427d6394b10dd98652c427f6454b109f19152c427f6354b109f18d52c436f6254b10af99052c42bd6414b10b798c52c42dd6314b10db54852c427e6414b10cf99052c423e6414b109f59052c433d6414b108f59052c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cfd5342c433e54d0b10cf55342c433c54d0b10bd98742c42f561d0b10cfd9742c433e65d0b10cf59742c433c65d0b10cf94f42c433d53d0b10cf14f42c433f52d0b10cf94b42c433d52d0b10cf14b42c43b661d0b10ed58742c427f6590b109f99642c427d6590b109f19642c42f66190b10bd58642c427f6550b109f99542c427d6550b109f19542c433f5450b10cf95142c433d5450b10cf15142c42fb6050b10be18142c433f6550b10cf99542c433d6550b10cf19542c433e5350b10cf54d42c433c5350b10ebd8942c433f5250b10cf94942c433d5250b10cf14942c43b66150b10ed58542c43bb6050b10ee18142c427f6510b109f99442c427d6510b109f19442c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c435e53ccb10d754f32c427f658cb109f99632c427d658cb10af99232c42bd648cb10bd98632c42f5618cb109fd9532c427d654cb109f19532c435e534cb10d754d32c42f7614cb10bd18532c427f650cb109f99432c427d650cb109f19432c42be640cb10af59032c42f6610cb10bd58432c42fa600cb10be58032c433e5490710cf55241c42fa6090710be58241c43756590710dd95241c43b65490710ed55241c43745490710bd98e41c42f56290710edd0a41c43b54290710bd98241c43f26090710fc58241c42f76550710ddd9541c43b76450710dd95141c43745450710bd18d41c42f76250710edd0941c43b54250710bd18141c433e5410710cf55041c42fa6010710be58041c42f565cc710dd59731c42f764cc710bd59331c437553cc710bd58b31c437652cc710dd14b31c43b742cc710ed50b31c43d732cc710f54cb31c42f660cc710d794e31c435d538c710be98231c42f9608c710d794c31c435d530c710f54c431c42fa600c710be58031c42f7640c710bd59031c43d66
  | 9 => 0x996310827d658c420cf952310833d548c420d794e310835d538c420dd9463108375518c4209fd95310827d654c4209f195310833e544c420cf55131082ef624c420bb1893108376514c420dd545310827f650c4209f994310827d650c420cf950310833d540c420dd9443108375510c420f54c431082be64c8420af593210833e54c8420cf553210835e53c8420d754f210837651c8420dd54721082fa60c8420be583210827d6588420cf952210833d5488420d794e210835d5388420dd546210827f6548420cf951210833d5448420b7d8d21082dc6348420d794d210835d5348420dd94521082be6408420af590210833e5408420cf55021082de6308420b758c210835e5308420d754c21083765108420dd54421082fa6008420be580210827e64940209f592500833f4294020cf50a500827d65d0020cf953400833d54d0020dd947400837551d00209fd96400827d6590020cf952400833d5490020bb98a40082ed6290020dd946400837551900209fd95400833e5450020cf55140083765150020dd545400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb58840082f66110020bd58440083765110020dd54440083b94010020af99320082bd64c8020cf953200833d54c8020ebd0b20083ad42c8020dd947200837551c8020eb99320083ad64c8020dbd5320083ae54c8020db55320083ad54c8020cb55320083e651c8020f9547200833e5488020cf55220082ed6288020db94a20083765188020dd54620083ba5488020ee55220082f96288020de94a20083ea5288020eed0a20083b94288020fc94620083795188020fc546200837151880209fd95200833e5448020cf55120083af4248020eb50920083765148020dd54520082ef6548020dbd95200826f6548020dbd5120083ae5448020db55120083ad5448020cb55120083e65148020f954520082ef6048020db94120082fb6548020ded95200827b6548020ee95120083b95448020bed8920083eb6248020de94920083ea5248020eed0920083b94248020fc94520083795148020fc54520083715148020b798f54c42dd63d53109f98f54c435e63d53109798f54c427d63d5310d758f54c425d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c43766195310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c42be64d4f10af59353c435f5394f109f99253c427d6494f109f98a53c427d6294f109fd9153c427c6454f109fd8953c427c6254f10d754c53c427e6414f109f59053c427e6214f109f58853c43766114f10de58053c427f65d0f109f99743c427d65d0f
  | 10 => 0x40827d62550209fd85540827c6155020cfd95540823f6255020cf989540823d6255020cf189540833f6155020cf985540833d6155020cf185540833e6055020cf181540833c2055020af990540833d5415020bd98454082f561150209f990540833e64150208f990540827e6215020db988540826e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f992520833e64948208f992520827d6494820cf592520823d64948209f597420833f54d0820cf953420833d54d0820cf15342082bd65d0820cf597420823d65d0820cf94b420827f65908209f59642082bd6490820cf952420833d5490820db94a42082fa6090820be582420827f6550820cfd51420833e5450820cf551420833c5450820db94942082bf6550820cfd95420823f6550820ebd89420833e5250820cb949420827f65108209f59442082be6410820cf950420833d5410820be98042082f96010820af99351082bd64d4420cf953510833d54d4420b798f51082dd63d4420cf952510833d5494420ddd46510827e64944209f592510827e63944209f58e510833f4294420cf50a51083775494420dd95251083b65494420cd95251083755494420ed55251083355494420dd15251083775394420dd94e51083d65394420d594e51083b74294420ed50a51083776494420dd99251083756494420dd19251083776394420dd98e51083756394420dd18e51083746294420ddd0a51083374294420dd90a51083754294420cd50a51083744294420dd98251083746094420cf951510833d5454420d794d510827f64544209f191510827f63544209f18d510833f4254420cf50951083776554420ddd5151083765454420ed95151083365454420dd55151083b55454420cd55151083745454420ddd4d51083765354420f594d51083565354420dd54d51083d55354420d554d51083b74254420ed50951083776454420dd99151083756454420dd19151083776354420dd98d51083756354420dd18d51083766254420ddd0951083374254420dd90951083754254420cd50951083744254420dd98151083746054420dd08151082be6414420af590510833e5414420cf55051082de6314420b758c510835e5314420d754c51082f66114420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420d794f410835d53d0420dd947410837551d04209fd96410827e65904209f596410833e5490420cf552410835e5390420d754e41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420d794d410835d5350420dd94541083755150420bed8141082f860504209fd94410827e65104209f594410833e5410420cf550410835e5310420d754c41083765110420dd544410827f658c4209f
  | 11 => 0x6e6590920bb59242482ad6490920db952424836c5490920bb982424827c6550920cfd51424833c5450920bed8142482f86050920cfd95424833e6550920cf595424833c6550920ebd8942483bb6050920ee181424836c65509209b19542483af6450920ebd51424836e5450920db15142483ac5450920fad8142482ec6050920fa18142483af6550920cbd9542483ac6550920cb19542483af6150920eb98542483ad6150920eb18542483af6050920ead8142483ae6050920eb58142483ac6050920ea181424827e6510920af99042482ee6210920eb50842483ad42d45209f993514827d64d45209f98f514827d63d4520cfd0b514833d42d4520eb50a51483775194520afd9151482bc6454520b7d8d51482dc6354520eb50951483ad4214520dd544514827e64145209f590514827e63145209f58c514833f4214520cf508514837960145209f997414827d65d05209f19741482ee62d0520bb58b41483ad42d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf15241483ad4290520be98241482f960905209fd95414827e65505209f19541483ad42505209f994414827d65105209f194414833f5410520cf15041482ee6210520bb58841483ad4210520ddd4441483745110520be98041482f960105209f996314827d658c5209f196314835f538c520d714e31483ad428c520be98231482f9608c5209fd95314827e654c5209f19531483ad424c5209f994314827d650c5209f19431482ee620c520bb58831483ad420c520ddd443148374510c520f54c431482fa600c520be580314827e65c8520af99321482bd64c8520eb50b21483ad4288520ddd4621483745188520be98221482f96088520b7d8d21482dc6348520eb50921483775148520dd14521482fb6048520be181214827e6508520af99021482bd6408520b798c21482dd6308520eb50821482fa60085209f997404833f54d0120cf15340482ee62d0120bb58b40483ad42d01209f996404833e5490120cf55240483ad42901209fd95404827d65501209f195404833f5450120cf15140482ef6250120bb18940483ad42501209f994404833e5410120cf55040482ee6210120bb58840483ad4210120bd98440482f56110120af99320482bd64c8120eb50b20483ba64c8120ee59320483bb42c8120fa90b20483b942c8120fa50b20483a942c8120be58720483af4288120eb50a20482ef6488120bb59220483eb5088120bd98754082f561d50209f98b540836e62d50209f987540837661d50209d987540827d61d5020dd587540827561d50209f983540837a60d50209f596540833f54950209f986540827d61950208f596540833e6295020cf18a540833f6195020cf986540833d6195020cf186540833e6095020cf182540833f64550209fd895
  | 12 => 0xd0320cf95240c833d5490320eb50a40c833e5450320cf55140c82ef6250320bb18940c83ad4250320cf95040c833d5410320bb98840c82ed6210320eb50840c82f66110320bd58440c83b94010320db58b548827e61d52209f587548837a60d5220cfd52548827e61952209f586548833f64552209fd85548827c6155220cf55054882f66115220bd584548833e6415220db588548827e6115220dd984548827661152209f584548837561152209d584548837a6015220cf953428833d54d0a20be98342882f960d0a20cf997428833d65d0a20ee98342883b960d0a20cf951428833d5450a20bed8142882f86050a20cfd95428833c6550a20ebd8942883bb6050a20ee18142882de63d4620b758f518837751946209f992518827d64946209f98e518827d6394620cfd0a518833d4294620de98251882bf6454620af191518827f6454620cfd91518823f64546209f191518833c64546208f191518827f63546209f18d518833f4254620cf509518837551146209fd97418827e65d06209f597418827f65906209f996418827d6590620cfd52418833c5490620dd94641883755190620be98241882f960906209fd95418827d65506209f19541883765150620dd545418827f65106209f994418827d6510620cfd50418833c5410620be98041882f960106209fd96318827e658c6209f596318835e538c620d754e31882fa608c620be582318827f654c6209f595318827c654c620bbd8931882ec624c6209fd94318827e650c6209f5943188376510c620dd54431883d5310c620be98031882f9600c620af99321882bd64c8620dd94621883755188620be98221882f96088620b7d8d21882dc6348620dd94521883755148620bed8121882f86048620af99021882bd6408620b798c21882dd6308620be580218833f54d0220cf153408833e5490220cf55240882ee6290220bb58a408833f5450220cf151408833e5410220cf55040882ee6210220bb58840882f66110220bd58440882be64c8220af59320883af42c8220eb50b20882ed65c8220db59720883ae64c8220eb593208836f54c8220db55320882f965c8220de59720883ba64c8220ee59320883bb42c8220ee50b20882f961c82209f987544827d61d5120cfd52544827e64951209f58a544836d62951209f986544827d61951209f58254483796095120bdd8554482f46155120cfd91544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f988544836d62151209f188544827e61151209f584544827e65d0920cfd53424833c54d0920be98342482f960d0920cfd97424833e65d0920cf597424833c65d0920ee98342483b960d09209f99642482bd6490920bb99642483
  | 13 => 0xee505401036e62d53209f98754c827d61d5320de58354c833f5495320db98a54c827e61953209f58654c83ae6295320cf98a54c832e6295320cf18a54c833f6195320cf98654c833d6195320cf18654c833f6095320cf58254c833f64553209fd8554c827c6155320cfd9554c83ae6255320cf98954c833c6255320cfd8554c833e6155320cf58554c833c6155320cfd8154c833d6055320cf55054c833e6415320db98854c827e61153209f58454c83796015320cfd5342c833e54d0b20cf55342c833c54d0b20af59742c833d65d0b20cf95242c833d5490b20be98242c82f96090b20db59642c836e5490b20eb95242c83ad5490b20db15242c82ee6090b20fa98242c83e96090b20cfd5142c833e5450b20cf55142c833c5450b20afd9542c833f6550b20ebd8942c82ef6550b20dbd9542c83af6450b20ebd5142c836e5450b20eb95142c832e5450b20eb55142c836c5450b20eb15142c82ec6050b20ebd9542c82af6550b20cbd9542c83af6150b20eb98542c83ad6150b20eb18542c83af6050b20eb98142c83ad6050b20eb18142c833e5410b20cf55042c83ad4210b20be98042c82f96010b20af99351c82bd64d4720cf95351c833d54d4720eb50b51c833e5494720cf55251c83ad4294720ddd4651c827e64947209f59251c827e63947209f58e51c833f4294720cf50a51c833e5454720cf55151c82df6354720b718d51c83ad42547209fd9151c827c64547209fd8d51c835f635472097d8d51c827c6354720d718d51c825c6354720cfd0951c833d4254720af99051c82bd6414720cf95051c833d5414720b798c51c82dd6314720eb50851c837551147209fd9741c827e65d07209f59741c833e54d0720cf55341c82ee62d0720bb58b41c83ad42d07209fd9641c827e65907209f59641c833e5490720cf55241c83ad42907209fd9541c827d65507209f19541c833e5450720cf55141c83ad4250720bed8141c82f860507209fd9441c827e65107209f59441c833e5410720cf55041c82ee6210720bb58841c83ad42107209fd9631c827e658c7209f59631c833e548c720cf55231c83ad428c720dd94631c8375518c7209fd9531c827d654c7209f19531c833e544c720cf55131c83ad424c720dd94531c8375514c7209fd9431c827e650c7209f59431c833e540c720cf55031c82ee620c720bb58831c83ad420c720f54c431c82be64c8720af59321c833e54c8720cf55321c83ad42c8720dd94721c837551c8720be98321c82f960c8720cf95221c833d5488720eb50a21c833e5448720cf55121c82df6348720b718d21c83ad4248720af99021c82bd6408720cf95021c833d5408720b798c21c82dd6308720eb50821c83765108720dd54421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c83ad42
  | 14 => 0x8851102ed6214440db948511036d5214440bd98451103755114440d794f411035d53d0440db94b411036d52d0440dd947411037551d0440be98341102f960d04409f596411035e5390440d754e411036e5290440db54a41103755190440af596411033d6590440af98e411039e5390440e754e41102bd6290440eb94a411033d5290440eb54a411032d5290440af98641103b65190440cf54641103b55190440cd54641102bd60904409fd95411035e5350440d754d411036e5250440db54941103765150440d794c411035d5310440db948411036d5210440dd94441103755110440be98041102f96010440af98c411039e5310440e754c41102bd6210440eb948411033d5210440eb548411032d5210440af98441103b66110440ed944411033d5110440ed54441103ba6010440af58041103b96010440ae580411027f658c4409f996311027d658c440af99231102bd648c440d794e311035d538c440db94a311036d528c440dd9463110375518c440be98231102f9608c4409fd95311027d654c4409f19531102bf644c440af191311036e524c440db5493110376514c440dd545311027f650c4409f994311027d650c440afd9031102bc640c440db948311036d520c440dd9443110375510c440f54c4311027f65c84409f997211027d65c8440af99321102bd64c8440d794f211035d53c8440db94b211036d52c8440dd947211037551c84409fd96211027e65884409f59621102bf6488440af192211035e5388440d754e211036e5288440db54a21103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440b7d8d21102dc6348440d794d211035d5348440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421102be6408440af59021102de6308440b758c211035e5308440d754c211036e5208440db54821103765108440dd54421102fa6008440be580211033f4294040cf50a501033e4194040cf106501036e52d0040db54b401037651d0040dd54740102bd62d0040eb94b401033d52d0040eb54b401032d52d0040af98740103b651d0040ed54740102bd6490040cf952401036e5290040db54a40103765190040dd54640102f96490040de95240103ba5490040fa94a40103e95290040eed0a40103b94290040fc94640103f15190040ee90640103b841900409fd95401036e5250040db54940103765150040dd54540102bf6550040cfd95401023f6550040afd8940103ae5250040cf54940103ad5250040cb54940102bc6150040ed94540103b55150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103ea5250040fa54940103ba4250040ee10940103f25150040fc54540103bb415004
  | 15 => 0x502f860505409f994415027e658c5409f596315027c658c540ddd463150374518c5409fd95315027e654c5409f1953150377514c540dd145315027e650c5409f594315027c650c540af99031502bd640c540f54c431502fa600c540be580315027e65c85409f597215027c65c8540af99321502bd64c8540ddd47215037451c85409f996215027d65885409f196215027f65485409f995215027c6548540b7d8d21502dc63485409f994215027d65085409f19421502be6408540af59021502de6308540b758c21503775108540dd14421502fa6008540be58021503bb42d0140ee50b40502bd6290140cfd4a405033c5190140eed4240502f661d4840bd587521036f52948409f986521027d6194840eb992521036c6494840dbd86521036e6194840db586521036c6194840db982521036c6094840cf991521027f61548409f185521036f6554840eb991521036e6454840cb991521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840bb988521036d5214840bd98452102f56114840cf953421036e52d0840db54b42102fa60d0840be583421033e52d0840eb94b421033d52d0840eb54b421032d52d0840af98742103ba60d0840af58342103b960d0840ae583421027d6590840af592421036d52908409fd95421033e5450840db94942102bf6550840cfd9542103af6250840cf94942103ae5250840cb94942103ad5250840af18542102bf6050840af990421036e5210840db54842102fa6010840be58042102de63d4440b758f51102ee62d4440bb58b511036e52d4440db54b511036e5294440db54a511037751944409f98e511027d63944409f98a511027d6294440cfd0a511033d4294440ed19251103775394440dd94e51103d65394440d594e51103775294440dd94a51103e65294440d994a51103755294440f954a51103655294440dd14a51103b74294440ed50a51103746494440ddd8e51103766394440dd58e51103746394440ddd8a51103766294440dd58a51103746294440ddd0a51103374294440dd90a51103754294440cd50a51103744294440dd98251103746094440d794d511036e5254440db549511027f63544409f18d511027f62544409f189511033f4254440cf50951103776554440ed19151103775354440dd94d51103d65354440d594d51103755354440f554d51103555354440ddd4951103765254440f994951103665254440dd54951103e55254440d954951103745254440edd0951103b54254440dd99151103776354440dd98d51103756354440dd18d51103776254440dd98951103756254440dd18951103774254440cdd0951103764254440dd50951103354254440dd10951103766054440dd18151103744054440b798c51102dd6314440d794c511035d5314440bb9
  | 16 => 0xe65c87409f59721d02be64c8740af59321d027f65887409f99621d027d65887409fd9521d027d65487409f19521d02df6348740b718d21d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740b798c21d02dd6308740be98021d02f96008740dbd4a529027e6194a409f586529033d6454a409fd85529027c6154a40db54852902f66114a40bd58452902bd65d0a40cf597429033e52d0a40af98742902bd60d0a40db94a429036d5290a40be98242902f96090a40db949429036d5250a40bed8142902f86050a40ebd89429033e5250a40eb949429032e5250a40cf54942903ad5250a40cb54942902bc6150a40afd8142903bb6050a40ee18142902de63d4640b758f519037751946409f98e519027d63946409f98a519027d6294640cfd0a519033d42946409fd8d519027c63546409fd89519027c6254640cfd09519033d4254640dd54451903765190640dd54641902fa6090640be58241902be6390640af58a419033d5290640ed946419033d5190640ed54641903ba6090640af58241903b96090640dd94541903755150640bed8141902f86050640af594419033d6510640af98c41902bd6210640cf54841903b66110640cf54441902bd60106409fd96319027e658c6409f59631902be648c640af592319035e538c640d754e319027f654c6409f595319027c654c640afd9131902bc644c6409fd94319027e650c6409f59431902bf640c640af1903190376510c640dd54431903d5310c640be98031902f9600c6409fd97219027e65c86409f59721902be64c8640af593219027f65886409f996219027d6588640afd9221902bc6488640dd946219037551886409fd95219027d65486409f19521902bf6448640af19121902df6348640b718d21903765148640dd545219027f65086409f994219027d6508640af99021902bd6408640b798c21902dd6308640be98021902f96008640af597409033d65d0240af58b409033d52d0240af98740902f965d0240de597409033f64d49409f987525027d61d4940dbd4a52502f76154940bd185525036d52149409f984525027d61149409f99742502be65d0940cf997425033c52d0940af98342502bd6490940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f86050940ebd89425033f5250940ebd49425032f5250940cf14942503ac5250940eed8142502bc6050940ee18142502b860509409f99442502be6410940eb508425027e63d45409f58f515027e62d45409f58b515033f42d4540cf50b51502de6394540b758e51503775194540dd544515027e63145409f58c515027e62145409f588515033f4214540cf508515027e65d0540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141
  | 17 => 0x4021de95250087ba5494021ce95250087795494021ee55250087395494021de152500877b5394021de94e50087da5394021d694e50087795394021f654e50087595394021de14e50087bb4294021ee50a50087f33194021fc0c650087eb2194021fc88650087e92194021fc486500877b6494021de99250087796494021de192500877b6394021de98e50087796394021de18e500877b4394021de90e50087794394021de10e50087786294021ded0a500873b4294021de90a50087794294021ce50a50087784294021decca500877a3294021de4ca50087783294021de186500877b4194021de90650087794194021de106500877b3194021de8c650087793194021de0c6500877b2194021de88650087792194021cf951500873d5454021d794d500875d53540219fd91500867c64540219fd8d500867c6354021cfd09500873d4254021ddcc550087743154021dd88550087752154021ded95500877b5454021de95150087ba5454021ce95150087795454021ee55150087395454021de151500877b5354021de94d50087da5354021d694d50087795354021f654d50087595354021de14d50087bb4254021ee50950087f33154021fc0c550087eb2154021fc88550087e92154021fc485500877b6454021de99150087796454021de191500877b6354021de98d50087796354021de18d500877b4354021de90d50087794354021de10d500877a6254021ded09500873b4254021de90950087794254021ce50950087784254021decc9500877a3254021de4c950087783254021de985500877b4154021de90550087794154021de105500877b3154021dccc5500877a3154021de4c550087783154021dc0c5500877b2154021de88550087722154021de48550087712154021de08550086be6414021af590500873e5414021cf55050086de6314021b758c500875e5314021d754c50086fa6014021de540500876f5294b409f98652d027d6194b40cf99152d027f6154b409f18552d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40cf94b42d03ae52d0b40cf54b42d03ad52d0b40cb54b42d02be60d0b40ee98342d03b960d0b40afd9542d033f6550b40ebd8942d03af5250b40cf94942d03ac5250b40af18142d036e5210b40db54842d03ad4210b40be98042d02f96010b40ddd4651d027e63947409f58e51d027e62947409f58a51d033f4294740cf50a51d027f63547409f18d51d027f62547409f18951d033f4254740cf50951d03755114740dd94741d037551d0740be98341d02f960d0740dd94441d03755110740be98041d02f960107409fd9631d027e658c7409f59631d02fa608c740be58231d027f654c7409f59531d027c654c7409fd9431d027e650c7409f59431d02be640c740af59031d03d5310c7409fd9721d027
  | 18 => 0xbd586320867f654c821cf951320873d544c821d794d320875d534c821bdd85320867d650c821cf950320873d540c821eb50832086f6610c821bd584320867e64944219f592510867d6394421cfd0a510873d42944219f597410873e54d0421cf553410875e53d0421d754f410867f65904219f596410873e5490421cf552410875e5390421d754e41086ee6290421bb58a410867f6550421cf951410873d5450421d794d410875d53504219fd94410867e65104219f594410867c6510421cf950410873d5410421d794c410875d5310421bb98841086ed62104219f597310873e54cc421cf553310875e53cc421d754f31086f565cc421dd597310867565cc421ed95331087b554cc421ddd4f31087d653cc421dd54f31087d553cc421d554f31086f562cc421dd94b31087b742cc421ed50b31087d732cc421f54cb310867f658c4219f596310873e548c421cf552310875e538c421d754e31086ee628c421bb58a31086f6618c421dd946310867f654c421cf951310873d544c421d794d310875d534c421dd945310867f650c4219f994310867d650c4219f194310873e540c421cf550310875e530c421d754c31086ee620c421bb58831087d5310c421bd5943108775650c4219d59431087b6540c421ed55031086f6630c421f598c3108777530c421f594c3108775530c421f554c3108755530c421f998831086f5620c421f95883108776520c421edd0831087b5420c421f58c831087d4320c421af99321086bd64c8421cf953210873d54c8421d794f210875d53c8421ebd0b21087ad42c8421eb99321087ad64c8421eb95321087ad54c8421f394f21087cd53c8421f9cc721087e431c8421cf952210873d5488421d794e210875d5388421bb58a210876e5288421ed95221087b55488421bd98e21086f46388421ddd4e21087d65388421dd54e21087d55388421d554e21086f56288421dd94a21087e65288421edd0a21087b542884219fd95210873e5448421cf55121086df6348421b718d210875e5348421d754d21087af4248421eb50921086ef6548421dbd95210866f6548421eb95121087ad5448421f3d8d21087cc6348421f394d21087cd5348421bbd85210876e5148421f990521087e54148421bdd95210877765484219dd9521087b65448421ed55121087d76348421bd98d21086f46348421f518d21086d46348421ddd4d21087d65348421dd54d21087d55348421d554d21086f76248421f9d8921087765248421f994921087b74248421f990921087b54248421f950921087a54248421af99350086bd64d4021cf953500873d54d4021b798f50086dd63d4021d794f500875d53d4021cf952500873d5494021d794e500875d5394021ded42500867e64940219f592500867e63940219f58e500873f4294021cf50a500877b549
  | 19 => 0x3530873d64d4c218f593530876e62d4c21dd987530867e60d4c21de983530867a60d4c219f583530877960d4c219e583530867d6594c21cf952530873d5494c21d7d4e530867e6494c219f592530867e6094c219f582530865d6594c21d7d52530875e5494c21e7952530871e5494c21d7552530879d5494c21c7552530875c5494c21f5186530875f6494c21d7992530875d6494c21d7192530875e6294c21d718a530875e6194c21d7186530875f6094c21d7982530875d6094c21d7182530873e5454c21cf551530867f6454c219f191530875f6354c21dd185530867f6054c219f181530875f6554c21d7d51530875e5454c21e7951530871e5454c21d7551530879d5454c21c7551530875c5454c21f5185530875f6454c21d7991530875d6454c21d7191530875e6254c21d7189530875e6154c21d718553087546154c21d7085530875f6054c21d7981530875d6054c21d718153086be6414c21af590530873e5414c21cf55053086de6314c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6214c21db988530867e6114c21dd98453086766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c21d794f430875d53d0c21bb98b43086ed62d0c21bd98743086f561d0c219fd96430867e6590c219f596430867c6590c21cf952430873d5490c21d794e430875d5390c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21cf950430873d5410c21d794c430875d5310c219f992520873e64948218f992520867d6494821cf592520863d64948219f98e520867d63948219f597420873f54d0821cf953420873d54d0821cf153420875e53d0821d754f42086bd65d0821cf597420863d65d0821cfd4f420873e53d0821e794f420871e53d0821cf54f420879d53d0821c754f420873c53d0821cf94b420867f65908219f59642086bd6490821cf952420873d5490821d794e420875d5390821bd98642086f561908219fd95420873f5450821cf951420873d5450821cf151420875e5350821d754d42086bf6550821cfd95420863f6550821cfd4d420873e5350821e794d420871e5350821cf54d420879d5350821c754d420873c5350821ebd89420873e52508219fd94420867d6510821af990420873e5410821cf550420875e5310821d754c42086f66110821bd584420867d65cc821cf953320873d54cc821d794f320875d53cc821eb50b320867f658c8219f59632086be648c821af592320873e548c821cf552320875e538c821d754e32086f6618c821
  | 20 => 0x867e65d0521cfd53414873c54d0521d7d4f414875c53d0521bb98b41486ed62d05219f996414873e5490521cf552414875f5390521d714e414867f65505219f595414867c6550521cfd51414873c5450521d7d4d414875c5350521bbd8941486ec62505219f994414873e5410521cf550414875f5310521d714c414875f53cc521d714f31486ee62cc521bb58b314867e658c521d7d4e314875c538c521bd9963148776658c5219d99631486f5638c521f5d4e3148776538c521dd14e31487d4538c521d514e31486f6628c521edd0a31487b5428c521f58ca31486f5608c5219f595314875f534c521d714d31486ef624c521bb18931487d7634c521f5d4d3148776534c521dd14d31487d4534c521d514d31487e7624c521bd18931487e4624c521edd0931487b5424c521f5cc931487d5324c521bdd81314867e650c521d7d4c31486f6610c521f54c431486be64c8521af593214875f53c8521d714f21487b664c8521ed59321486f763c8521bd58f21487d753c8521dd94f214877453c8521f514f214875453c8521edd0b21487b542c8521bd583214875f5388521d714e21487af4288521eb50a21487cf5388521f314e21487e75188521f98c621487e53188521d7d4f504875c53d41219f993504867d64d41219f98f504867d63d4121cfd0b504873d42d4121b798e50486dd6394121d7d4e504875c5394121ded4250486bf6454121af19150486df6354121b718d504875f5354121d714d504875f5314121d714c504877950141219f990504867d64141219f98c504867d6314121cfd08504873d4214121b798f54086dd63d5021be98354086f960d50219f98f540875e63d50219798f540867d63d5021d758f540865d63d50219f98b540876e62d50219f987540877661d50219f983540877a60d50219e983540867d60d5021de583540867960d50219f596540873f54950219f98e540867d63950219f982540867d60950218f596540873f6395021cf98e540873d6395021cf18e540873e6295021cf18a540873e6195021cf186540873f6095021cf982540873d6095021cf182540873f64550219fd8d540867c63550219fd81540867c6055021cfd95540873f6355021cf98d540873d6355021cf18d540873e6255021cf189540873e6155021cf185540873c2155021cfd81540873e6055021cf581540873c6055021af990540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150218f990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e58054086be64d4c21af593530873e54d4c21cf55353086fa60d4c21be583530867e64d4c21cf993530863e64d4c219f59
  | 21 => 0x6454221cfd91508863f64542219f191508873c64542218f191508867f63542219f18d508873f4254221cf509508877950142219f98f544867d63d51219f983544867d60d5121cfd5254486de6395121b758e544867e64951219f98e544875e63951219798e544867d6395121d758e544865d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf550544873e64151219f98c544867d63151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21d7d53534875e54d4d21d7553534875c54d4d21f5d87534875f64d4d21d7993534875d64d4d21d7193534875f62d4d21d758b534875f61d4d21d7587534875f60d4d21d7983534875d60d4d21d7183534875f5394d219f992534867d6494d21db58a53487756194d219f982534867d6094d219fd91534867c6454d219fd89534876f6254d21ddd85534867f6054d219f181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d21b7994534875e6514d2197994534875f5414d21d7950534875d5414d21d715053487d56114d21d7d90534875e6414d21d7590534875c6414d21d7d88534875d6214d21d7d84534875d2114d21d7d80534875e6014d21d7580534875c6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d219fd96434867e6590d219f596434867c6590d21d7d4e434875c5390d21bd98643486f56190d219fd95434867e6550d219f595434867c6550d21d7d4d434875c5350d219fd94434867e6510d219f594434867c6510d21d7d4c434875c5310d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf153424875f53d0921d714f42486f661d0921bd587424873f65d0921cf997424873d65d0921cf197424873f53d0921e7d4f424871f53d0921cf94f424873d53d0921cf14f424879c53d0921c714f42487b661d0921ed587424867e6590921af592424875f5390921d714e424867c6550921cfd51424873c5450921d7d4d424875c5350921bdd8542486f46150921cfd95424873e6550921cf595424873c6550921cfd4d424879f5350921c7d4d424873e5350921cf54d424873c5350921e714d424871c5350921ebd8942487b76150921ed185424867e6510921af990424875f5310921d714c424867e65cc921d7d4f324875c53cc921bd98732486f561cc921af99232486bd648c921d7d4e324875c538c921eb50a324867c654c921eb50932486f7614c921bd185324
  | 22 => 0x721bb18931c873e540c721cf55031c87d5310c721bd59431c8775650c721ed95031c87b5540c721f598c31c8777530c721f5d4c31c8757530c721dd54c31c87d4530c721bd58831c87b7420c721ed50831c87d6320c721af99350c86bd64d4321cf95350c873d54d4321cf95250c873d5494321ded4250c867e64943219f59250c867e63943219f58e50c873f4294321cf50a50c873e5454321cf55150c867f64543219f19150c867f63543219f18d50c873f4254321cf50950c87773154321dd0c550c86be6414321af59050c873e5414321cf55050c86de6314321b758c50c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d6015221d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538867f6054e219f181538875d5314e219f990538867d6414e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f59743886ee62d0e21bb58b438867f6590e219f996438867d6590e219f19643886f66190e21bd586438867f6550e219f595438867c6550e219fd94438867e6510e219f594438867c6510e21bd98443886f56110e21cf953428873d54d0a21bd98742886f561d0a21cf997428873d65d0a21cf94f428873d53d0a21cf14f42887b661d0a21ed587428873e5450a21cf55142886f76150a21bd185428873f6550a21cf195428873e5350a21cf54d428873c5350a21ebd8942887b76150a21ed18542887ad42cca21bd98732886f561cca21af99232886bd648ca21cfd53418873c54d0621cf952418873d5490621bb98a41886ed6290621cfd51418873c5450621cf950418873d5410621bb98841886ed6210621d794e318875d538c621bb98a31886ed628c621dd94e31887d6538c621f554e3188774538c621bd98a31887e6628c621f958a31887b7428c621ed50a31887d6328c621bd58231886f7654c621ddd9531887d7634c621f5d4d3188776534c621dd14d31887d4534c621d514d31886f4624c621edd0931887b5424c621f5cc931886f7604c621d794c318875d530c621bb98831886ed620c621f54c431886be64c8621af59321887af42c8621eb50b21886ed65c8621db59721887ae64c8621eb59321886f565c8621dd59721887b664c8621ed59321886f763c8621bd58f218877653c8621dd14f21887b742c8621ed50b21886f560c8621b798e50886dd6394221ded42508867e64942219f592508867e6394221d798e508865e63942219f58e508875d63942219758e508873f4294221cf50a50886bf6454221af191508867f
  | 23 => 0x5909310c7d5424c431e5509310c7d4424c431f5d81310c6d7604c431f5981310c7d5604c431f5181310c7d531d4031f54c6500c77b50940319f992500c67d64940319f98a500c67d6294031cfd0a500c73d4294031afd91500c6bc6454031f54c5500c67f6454031cfd91500c63f64540319f191500c73c64540318f191500c67f62540319f189500c73f4254031cf509500c6be6414031af590500c6ee6214031bb588500c7d53114031de540500c67e63d53219f58f54c876e62d5321dd58754c867e60d53219f58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd8e54c873e6395321cf58e54c873c6395321cf98a54c873c6295321cfd8654c873d6195321cfd8254c873e6095321cf58254c873c6095321cfd9154c867f63553219f18d54c867f60553219f18154c873f6555321cfd8d54c873e6355321cf58d54c873c6355321cf98954c873c6255321cfd8554c873d6155321cfd8154c873e6055321cf58154c873c6055321cf55054c873e64153219f98c54c867d6315321db98854c877561153219f98054c867d6015321af99353c86bd64d4f21cf95353c873d54d4f219f99353c873e64d4f218f99353c867d64d4f21cf59353c863d64d4f21db98b53c867e60d4f219f58353c873e5494f21cf55253c875f5394f219f99253c867d6494f219f98253c867d6094f21cf95153c873d5454f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c86be6414f21af59053c873e5414f21cf55053c875d5314f21be98053c86f96014f219fd9743c867e65d0f219f59743c867c65d0f21cf95343c873d54d0f21bd98743c86f561d0f219fd9643c867e6590f219f59643c873e5490f21cf55243c867f6550f219f99543c867d6550f219f19543c873e5450f21cf55143c86f76150f21bd18543c867f6510f219f99443c867d6510f21cf95043c873d5410f21bb98843c86ed6210f21cfd5342c873e54d0b21cf55342c873c54d0b21af59742c873d65d0b21cfd4f42c873e53d0b21cf54f42c873e5490b21cf55242c86f66190b21bd58642c873f5450b21cf95142c873d5450b21cf15142c86bf6550b21cfd9542c873f5350b21cf94d42c873d5350b21ebd8942c873e5410b21cf55042c86f66110b21bd58442c873e548cb21cf55232c87ad428cb21bd98632c86f5618cb21cf95341c873d54d0721bb98b41c86ed62d0721cf95241c873d5490721cf95141c873d5450721bbd8941c86ec6250721cf95041c873d5410721cf95331c873d54cc721d794f31c875d53cc721bb98b31c86ed62cc721ed95331c87b554cc721f594f31c877553cc721f554f31c87e662cc721bd58b31c87e562cc721edd0b31c87b542cc721cf95231c873d548c721d7d4e31c873e544c721cf55131c875e534c721d754d31c86ef624c
  | 24 => 0x414c73f54d0531cf153414c6de63d0531b758f414c67e65905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c67e6510531ed504414c6dd628c531d714a314c79f428c531e750a314c7d7518c5319f993504c67d64d41319f98b504c67d62d4131cfd0b504c73d42d4131d78c7504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c67e62141319f588504c73f4214131cf508504c67e62d50319f58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c73f64550319fd89540c67c62550319fd81540c67c6055031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c6be6494831af592520c76f52948319f992520c73e64948318f992520c67d6494831cf592520c63d64948319f982520c67d60948319fd91520c67c64548319fd81520c67c6054831af990520c6bd6414831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cfd53420c73e54d0831cf553420c73c54d0831bd987420c6f561d0831cfd97420c73e65d0831cf597420c73c65d0831cf94b420c73d52d0831ed987420c7b561d08319fd96420c67e65908319f596420c6bd6490831db94a420c76d52908319fd95420c67d65508319f195420c73f5450831cf951420c73d5450831cf151420c76e5250831db549420c6f76150831bd185420c73f6550831cf995420c73d6550831cf195420c7af6250831cf949420c7ae5250831cb949420c73d5250831eb549420c72d5250831edd85420c7b461508319fd94420c67e65108319f594420c6be64108319f992510c67d6494431cfd0a510c73d42944319f597410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c67f65504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431bd58e310c6d5638c431dd94e310c7d6538c431bd98a310c775528c431edd0a310c7b5428c431bd582310c67f654c431bdd95310c777654c4319dd95310c6f7634c431dd94d310c7d6534c431f5d0d310c7d6434c431f550d310c7d4434c431bd189310c775524c431edd09310c7b5424c431bdd81310c7d7654c431b5d95310c757654c431f5d91310c7d6644c431f5591310c7d4644c431f5d51310c7d6544c431f5551310c7d4544c431f5d89310c7d6624c431f5589310c7d4624c431b5189310c7d7524c431f5949310c7d5524c431d5549310c7d4524c431f5d09310c797424c431f
  | 25 => 0x73e6415231d758c548c67e62152319f588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31cf951438c73d5450e31bdd85438c6f46150e31af992528c6bd6494a31dbd4a528c67e6494a31cf992528c63e6494a319f592528c73d6494a318f592528c67e6094a319f582528c67f6454a319f191528c67f6054a319f181528c6be6414a31af590528c76d5214a31be980528c6f96014a319fd97428c67e65d0a319f597428c73f54d0a31cf953428c73d54d0a31cf153428c6de63d0a31b758f428c73f65d0a31cf997428c73d65d0a31cf197428c79e63d0a31e758f428c73e52d0a31cf54b428c67f6590a319f996428c67d6590a31bd986428c6f56190a319fd95428c67d6550a319f195428c73f5450a31cf951428c73d5450a31cf151428c6df6350a31b718d428c73f6550a31cf995428c73d6550a31cf195428c79f6350a31e718d428c7af6250a31cf949428c73d5250a319fd94428c67e6510a319f594428c6f66110a31bd584428c73e5490631cf552418c6de6390631b758e418c73e5410631cf550418c6de6310631b758c418c7b54110631bd597318c77565cc631bd58b318c77652cc631edd0b318c7b542cc631af993508c6bd64d4231ded42508c67e64942319f592508c67e62942319f58a508c73f4294231cf50a508c67f64542319f191508c67f62542319f189508c73f4254231cf509508c7773154231de540508c67e62d51319f58b544c67e60d51319f583544c73f5495131bb98a544c6ed62951319f992544c67e6295131db98a544c66e62951319f58a544c76d62951319b58a544c67d6195131dd586544c67e60951319f582544c73f64551319fd89544c67c62551319fd85544c77761551319fd81544c67c60551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c67e64d49319f593524c67e60d49319f583524c6be6494931af592524c76f5294931af990524c6bd6414931db548524c6fa6014931be580524c67e6414931cf990524c63e64149319f590524c73d64149318f590524c67e6014931de980524c67a60149319f580524c77960149319e580524c67e65d09319f597424c67c65d0931cfd53424c73e54d0931cf553424c73c54d0931cfd97424c73e65d0931cf597424c73c65d0931cfd4b424c73c52d09319f996424c67d65909319f196424c6bd6490931dbd4a424c76c5290931bd986424c6f561909319fd95424c67e65509319f195424c73f5450931cf951424c73d5450931cf151424c76f5250931db149424c73f6550931cf995424c73d6550931cf195424c7af6250931cfd49424c7af5250931cbd49424c73c5250931eb149424c72c52509319f994424c67d65109319f194424c6be6410931bd984424c6f561109319f997
  | 26 => 0x390d41d714e43506f66190d41bd58643506f76150d41bd185435073f64d49419f98f525067d63d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be181525076d52149419f98c525067d63149419f980525067d60149419f99742506be65d0941cf997425073f53d0941cf14f425073c52d0941af98742506bd6490941dbd4a425076c5290941bd98642506f56190941dbd49425076c5250941bdd8542506f46150941cfd4d425073c5350941ebd89425073f5250941ebd49425072f5250941cf14942507ac5250941edd8542506bc6150941ed185425067e6510941af99042507b742d0541ed50b41506f560d0541af58a415073f5290541edd46415067e63d41419f58f505067e62d41419f58b505073f42d4141cf50b50506de6394141b758e505077b5094141de540505067e63141419f58c505067e62141419f588505073f4214141cf508505073e4114141d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f189531067f6054c419f181531075d5314c41bb98853106ed6214c41be98053106f96014c41d794f431075d53d0c41bd98743106f561d0c419f596431067f6550c41bd98443106f56110c41dbd4a521067e63948419f58e521067e60948419f582521073e64548419fd8d521067c63548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521073e54d0841db94b421076d52d0841bd98742106f561d0841cf94f421073d53d0841cf94b42107ae52d0841cf54b42107ad52d0841cb54b42107b661d0841af58742107b561d0841af983421067d6590841af592421067f6550841cf95142106bf6550841cfd95421073e5350841cf54d42107af6250841cf94942106bf6150841af18142106be6410841db948421076d5210841bd98442106f56110841cfd0a511073d4294441af58b411073d52d0441af98341106bd6490441cf95241106f56490441dd95241107b65490441edd0a41107b542904419fd9541106bf6550441cfd95411063f6550441afd89411073d5250441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441edd0d41107b54350441ded42501067e63940419f58e501067e62940419f58a501073f4294041cf50a501067f63540419f18d501067f62540419f189501073f4254041cf50950107764154041dd50550106de6314041b758c50106ee6214041bb58850107795014041be983548c6f960d5231d758f548c67e62d52319f58b548c77661d52319f983548c77a60d52319e983548c67d60d5231de583548c67960d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c62552319fd81548c67c6055231cf550548c
  | 27 => 0x429fd954210b3e5450842afd954210b3f65508428fd954210abf6250842cf9494210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842cb9514210b7751944429f98e5110a7d6394442cfd0a5110b3d42944429f9825110a7d60944429fd8d5110a7c6354442cfd095110b3d42544429fd815110a7c6054442b798c5110add6314442dd5445110afa6014442be5805110b7b5094042cfd0a5010b3d42940429f9865010a7d6194042cfd095010b6e4254042cf5095010b6d42540429fd855010a7c6154042bd9845010af56114042de5405010aee62d4f41bb58b53d075f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d06f661d0f41bd58743d06de63d4b41b758f52d076f5294b419f98e52d067d6394b419f98252d067d6094b41cf99152d067f6354b419f18d52d067f6054b419f18152d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41cf94f42d073d53d0b41cf94b42d07ae52d0b41cf54b42d07ad52d0b41cb54b42d06be61d0b41ed98742d07b561d0b41afd9542d073f6550b41cf94d42d073d5350b41ebd8942d073e5250b41af18542d076e5210b41db54842d06f66110b41bd58442d077b50943419f98e50d067d63943419f98a50d067d6294341cfd0a50d073d42943419fd8d50d067c63543419fd8950d067c6254341cfd0950d073d4254341b798c50d06dd6314341bb98850d06ed6214341de54050d06fa60d4e41be583539075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c53906f66190e41bd586439076f5294a419f98e529067d6394a419f982529067d6094a41cf591529067f6354a419f18d529067f6054a419f18152906de6314a41b758c529076d5214a41be98052906f96014a41af597429073d65d0a41cf94f429073d53d0a41cf94b42906bd61d0a41af983429076e5290a41db54a42906f66190a41bd586429076e5250a41db54942906f76150a41bd185429073e5350a41cf54d42907af6250a41cf94942907ae5250a41cf54942907ad5250a41cb54942906bf6150a41edd8542907b46150a41af18142906bd65d0641cf59741906bd62d0641cf54b41906be60d0641bd597419077565d0641bd58341906de63d4241b758f50906de6394241b758e509077b50942419f98e509075e63942419798e509067d6394241d758e509065d63942419f98a509067d6294241cfd0a509073d42942419fd8d509067c63542419fd89509067c6254241cfd09509073d4254241de540509067e62d4d419f58b535067e60d4d419f583535075f5394d41be98253506f96094d41d754c535067e6214d419f588535067e6014d419f580535075f5
  | 28 => 0xd4651d0bb75194742af98251d0abd6094742afd8d51d0abc6354742edd4551d0b3e5154742afd8151d0abc6054742af98c51d0abd6314742eb58851d0b3f5114742ed94451d0b3d5114742ed54451d0abe6014742af58051d0bad62d4342af98750d0abd61d4342af98650d0abd6194342cf94650d0b3c5194342cfd4250d0bbb5094342afd8550d0abc6154342eed4150d0b3e5054342eb58850d0abe6114342ed98450d0ab66114342af58450d0bb56114342ad58450d0b3e5114342cf14450d0b3f5014342ee94050d0b3d5014342ee54050d0b395014342af5974290b3d65d0a42bb5974290b6d65d0a42bb5834290b7751946429f98e5190a7d6394642cfd0a5190a7e60946429f5825190a7f63546429f18d5190b3f42546429fd815190a7c6054642b798c5190add6314642dd5445190afa6014642be5805190b7b5094242cfd0a5090a7e61942429f5865090b3f42542429fd855090a7c6154242bd9845090af56114242de5405090aed60d0942ebd4a4250abe6190942af5864250abe6090942af5824250a7e63d45429f58f5150a7e60d45429f5835150b775194542b7d8d5150adc6354542bed815150af86054542dd5445150a7e63145429f58c5150a7e60145429f5805150a7e61d41429f5875050b7b5094142bdd855050af46154142bd9845050af56114142de5405050a7e6114142dd9845050a7661141429f5845050b7561141429d5845050abe61d4942af5875250abe60d4942af5835250baf61d4942eb9875250bad61d4942eb1875250baf60d4942eb9835250bad60d4942ab5835250bac60d4942af98f5150abd63d4542cfd4b5150baf52d4542af9835150abd60d4542af98e5150abd6394542eb58a5150baf5294542af9865150b3f5194542edd465150abe6094542af5825150abf6354542e7d8d5150a9f6354542af18d5150b9c6354542a718d5150baf6254542ebd495150bb75154542cf9455150abf6054542eed815150abb6054542af1815150bb86054542ae1815150abe6514542af98c5150abd6314542cfd485150baf5214542cfd445150bb65114542cf5445150bb55114542af9805150abd6014542ebd8b5050b3f52d4142ebd4b5050abe61d4142af5875050bad6294142ebd4a5050abe6194142af5865050b3e5194142cf1465050abe6094142cfd425050bbb5094142ebd895050baf5254142afd855050bb76154142add855050abc6154142ed1855050ab46154142eed415050b3e5054142af9945050bad6214142cfd485050baf5214142af9845050bb66114142ad9845050abd6114142ed5845050ab56114142cf9445050b3c5114142cfd405050bba5014142cf5405050bb95014142ce5405050b3e6195042cf5865410b3e6095042cf5825410abd6490842cf9524210aed6490842db9524210bae54908
  | 29 => 0x2002400a001400d000000a001c0000050005001c001000800300000050000011000001300140000004006001000f0004000001c00a008001500100000000003000c003001c00200080060028000000400200000000000002000400a00000030010000000800200040000000000003c003000400000000040000000000400800000010000000001000e0030000000c000000000f001400200700020000003002000100000090018011002c0030004000000800e00140030010004000000600080020018003000400a000800a0004017001000700000150000003002c0080008001000400000100010000007000000000080130018005003c00b00080060000005003000300080000004009002800100080030004004000000100000060000005002c0080018001000c000000000c00040030000000000000700100000000002000800100040050004000000c0000008006000400100140060000002001c0040050004000000400080040000000001000000040040000000000c004004400000100000008002004400000140000010001000800a002c00300000010018002001c015000c02c000c000001400300040000000014000000800180000020000005400d0004000002000000000010034001004800f0000003000800000000030000001000c001006c000000400000000000000000000000000500020000001000c0010018002000000000b8000002000000000050024008000001000080060000008000c003000c0020000005003c00400100020000009000c001001c00b00000050000000001c00100340000000001000800600080000010004000801200240020004004000400b000000700140020000000006800b0004006000000300000040000002000400200000000014000001c0000000000000c000000c0050000000000400000280000000004001c004000c00000200000000006002400c00280030004012001c000000000100080150028009000c001000c00100000020000000001c0030028000001400000580000008004002c0000008000000400100040010028001000400b00040000028000001c0010000006000c00a0000008000000200000000024002000400300200010000004001c0020000004001c0040004001005c003000403000400010010000000c00000040070008000000000100000010004002001800000000000028007001ede63d4742b758f51d0b7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c63547429fd8151d0a7c6054742dd54451d0b7b50943429f98650d0a7d61943429fd8550d0a7c6154342bd98450d0af56114342de54050d0abe63d4742e798f51d0a9e63d4742af58f51d0b9d63d4742a758f51d0bad62d4742af98351d0abd60d4742af98e51d0abd6394742cf
  | 30 => 0x200400030000001000000000240010000012000800800040010000009000000b0000000000800100140000004001001c007000001b0020000000c000000c000000c003000000600280060004001000000c000400000100020004000003c00500000030010004002c00100100150008004002400100080060004001001400100040000000006001c000000c003000000a00040070014005000c00300000120018000001000200000030018001001800000080000000001000400c000c002000c000001400100040010004000004c0020004000000000200100090004000001400000000050000004000000900080030000002000000100000000014000000c0020044001000400400040100004000000c00200000010000000000c00200240000010007000000000040040010006000800000600010004001000000300000000004000000000100000020028007003800700700000000001000c007001c02a0000000003c003000400b0024000001c003000000000380000008000000c000000002400000030000000000800100a00000008003000c0000004000000800000000000000000001800600000040008000000800700040010008000000000300040000008005000400400180030000003000800500040010000001001000a000800000000010000005000000000140000008004002800600200010000003000800800000060000009000000200a40050004000007400b0010000000000800000000000020009400000180000004004001c0000004005000800900080000000001003000600040040000005000c007001800000000100034002000000b0000000000c000001000000000010000000001800b0010000000401800080010000002000001500000010000000001000700000030000007001400200000000000007000000a00000170010024001400600040270004004000400e0028007000c005000c00200040010000004000c00100080010000008000400a00180050004006000c000000c00700340020014000004400b0004000000800f0030001000000500040000010000003c00100000070038001000000b0000006000000000040000008000000000900040000000002000c000000000000100180014001000800b00000020030001003c001008c005000000b000c0000008004000400a002c010000000a000000c005400000000140004000006000600000010004000000c0010000003000000700000020060011000000a0004000000c00a0004004001400000100030058000000000200500030000001000400200040020010005000400400000040010000001800300000020000000006800000300010000000001000100040060000000000400100080020054005002c018001c001000c00c00300070008001000000000
  | 31 => 0x4000000000000000050004001000c001000000b00180000000000000800100000020004002009800600240000004002000801400000000030005000800300080040008000006c021000c00700840050000000001800000000010004001001400100040010000000000000000240000008005001400000000000010003000000000080080004011001c00200240000014000000000e008400400100030000002006c00100800010024002005400000240070058009000c0000008009001000300000160018007000400a008000200000000008000003c015000000000080000014007000400700140000000000000800400100000000000000800500080130000000002c000000c004000c0010008000004c0010004002001400200000010010000000c000001800200000000010008003c00c000400000000000000005002c002000400000000050094002000000000100090008009000c003000400c001000d000401c00240250000006000000000080040000000001802500180000000003000800900000000024003000400200000010018001000001200000000020001000001100140010004002000c0080004000000000300000000008009004c00000100010000002000000200000000008001000400000040020018000000000000000130004001000800500080000000002000400200080060070002000001f00140040008009001400d001c0000004001001c0060000002000000d0000009000c00f002c0000004000000000200140020000003000800100100020008008001000600000000014012000400900080120000002000000200480000000000000c0030004000000000100040000004000001400c0000005000400b00000000020005001c03200040010000009000c000000400b000400100000000000001000c00200180040010018000c0000014000000000b0000000000401c00080000028002000c00500100050000006000c0010000005000c001001000200240000018006002c00200280000020002001400e000000d0018005005800000140030000002000c00100140000004002000c000001000000040000014000000003900100020004001000000b000001100740090000002001000000000000000000000000000240030000001000c00300080020010001000c005001800100000000004002000000e008000000000020014003001c00000080010000000000000a000800000000000018002003c00900440000010003000000000000030000014001000c000800a0030005000c0000060004003000700000010050000000402600080010004003000400800000040008007000000000000010010000000c00a007000a0004000000c006001000800040000048001000000d00b800100000040008000000000100000
  | 32 => 0xa000c000001800100000000004000002800e00180050004001000000f00080010000002000c001000000c000000000040000044001000c0010000047000c00000000010034007000000300000030010003001000a002800200140020004000000400100100090004001000400200040030008001000800300000030014006000400000000000004012000000300180090010000000800500040000020001000800200140060004000000400c000400b00000080004006003400600000000000010000800200000000034000000c00000000000000019000c0000004001001000100000000000001001c00000000000000003000001c000c012004800000040030008002000c0000008001000c00a00240020000000001800900000000004007000c000000c0020004003000800000000190000003002000000000130004003007400000240000004001003000b0020000000000100000030008002001000000000020004000006800200000020000003000400d00080000004005001800e00000000000000000000100000000010008001400e00000010004000000800900180010000000000c0030008002001c000003800200100000004000001000300080000010000001800100080000024000000000000000000000005003c00b00040010004005002c0000000002000c00b000001600000010004000000400e0008001000c012001000500000040010001004c01d0000003000000100000060004001000000000000020004002000000c0004001001c00b000000a00080000018003001800000000040008009000800000180080000007001400000000000000001000000000f4000003800200040000008004004400000000140000006000800200040000004000000000200340080010001000c002000c00c000c00400100010010003001000100280000038000000000e00000000008001001c00100000020004009002c00900380030030000000000000040000004000000000a000c00400000050024001000400100000010018005002c00400080000000000000000100a00010064001000001e0008001002c003003800a00200000010019000000c000000100080000000007000400300480000004000000c006000800200100000000003000801a001c0070008002002c002004000000240070000013000400500040000004012000c0010000004000801600000010004001002800b002000300000020004005001000a002000300040000010001000400200000010000002003000000840010008002000000300100020004000000401100380010034002000c00000340030000006002000300000000000000000002f00100010024000001803100040000000004000c00400000040004003000400200740040004005003800c00040000
  | 33 => 0x16162c2869ad808c4035e07c8e760002ff746b0000000303a0000dc200000006f70000000082e0000000000189300000000002c20a5f9dfa1fde5dc87580003a4000000008acc3d40000000000170863888517026cf05d600006630001e0269b6cdc000000007130f3000109447a0ac4000045800000000000000394c00006c40008cc0000000000000000000000000bb580002cb96425ed5474361d308b089666bfe48055ee468338361e0000266a0001354143ade82f000e96da15662008222a94a2da582c0000001ea4186ada60000c8c0f4800000004e532b9f3f0842d4a9dd96c1bf400000000000019a0ae2f8000084fa5ae39e4a7ebffefdb2de2fa424f8000b94019571229d467758b09a188cc2249afa00022d80000b265a769b401316ea5161ee8ae02ace17327ce00000ef3d493dc93a0a9823126e61a299e2a5400006e8307400027f2af6000017729e2160a8b60000d320000b154d800007bfa4b212b12984a383da97f0bd442123c4a4315509b825d01b300042d514285f1a73c70e7050baf907bbf316de4c6867033a0433ad693942e299ec9d08ea86ba1c4080340000001d727030a0e97c9d5c7c81de20000bee000118329d1908971800200040020008003000000c0000002000000300000000000000000000700040000004000003801b00000030000004002c00000000190010000001000000000020044002000000b000c000000800000280060020008000c001001c00e000800600040050000002003c0000014000001c0110000000000000900000030000003007c0000044000001800b000400e000000000040000000009000c00a003000c001400a00100030000017000000800340000000000000400000280010000006002400e00000260000001000801e001400800080010000004000c0000074000001c005000c0000000000001800000000010008009000800000000080020001001800500040030000001001c0000000006000000600200000004004004000e000000a00380010008006000400200140050010000001800a0004000000400200180020000000002800200100010000007001400100000020000001002c008001000d000000200000010004000003c0000000016000000a000403a001c00600040000000005000400b000400500000080000000000000100040000014002000801300280000004000000000500280060000007000000100000010004003000801e00140010008000000c00c00040000000001001400000000010000007000c000000800c00040000000000002c00100040050014000000000000000000020000003800100000000000003001801100200020030004000c00000300010004001001001500040020048001001c00400000030020007000c003001801a003000a00000000040
  | 34 => 0x2c8800000004f028b86c611e1209400086b91a25db000056e07860002e428191116529000000010920000000000101f2394000000000026ff0b01da96f75219a7602280000000405bd204b30000408285106e00000006f20a5256499dc5a00000a58800000000000000000a3e24cc520684c19953d9a480000000053537c023b05e00007410000000025a619007e0000c86b0330200000000a668000c3cabb18bc517c0001cd361580980000fca39ada1c01c279600000003ee2694c301188a6ba96a7378000ac82e32c25a4be4e0188e8bd94ae448959a7901718b780b7285e8420a2297480921cbc0cf81687b123ef668cd862830938a381fe06063076ba897cb05ee37335028fc63002157648c2c2c255261235a833859e4a1ffa6840001dee00011101ae04dc00011bf000000067a2f94150800032a2f4e0d10000000253a9a82e4e44f218c00021d40cb0000adda5a40000b3e0000e5275989244b1e43a000000000000000000c7007b000000022ec00023d1000000066980007fcd86119e45fd000000065d1d6ec0aafb20b091b200000004bb0406495a60294c0a9c0000fec000000065b924a000240b0000000a9f800058e97eb0000000c3e8e5c8a402eb00000009da80005ad1bd0000140e0bd9460672a8fd13a0cea754918c000000047f0b309620000000070b55c8000000000002a800090880006c780004078ea64090ae88bb9f0600024d425c5260abf8000000203e0e18000000116200030fb1e62e08017213c56b1b9c0001cb0b6c998c22200009f9800089780006764000000000000012fc00027ea0002edf0001b06000206e3f89a5f0001126aabaf1067c8aec22e9a348c30fda2f700004f4915421a932e0001d300000746592819c80c4b4e290a22e0001762000109f000000002740000000d840002d41000000040a000084e800000000001d9000043e62f40000dfd1b7807c3a6a80c38bd02c5a6110c4ca0000760815500029f90000000c0b97ca17e2e385b4dc6a2af1d4c5f4230e7f0842727c81a80000e7400000000000000658853266c5a320000000274400069e8000000000000011d427f84480002c770282162891a04f00026d644743840000a3f281858000002f862700008bc1fe1000000000000b90000000000150f0002af034400002b20000b92b0d41458c1052f05ac00000004742f180000e2017b2dda00000000003094afb899800030180bca53c802c6ca5dc0a710000000824ecee5fa80005fc22ae87183ae218800086b115c0d45eb8c4198360000000000000046482202c6ab0e02c00000000000147202b0000d7b0001b047e4b0de2f3e850a081d489608be938f20f6be7800000000002b680003078e9c130e5bb5a91e262f3883000018047fa9d6892d05e50b9c0001fa104a333000000005fb7dde878
  | 35 => 0x5e3000069f80000002d6e00000007e74000000000000000000000000000000000012ba0001e82523c2b2a1a2f8300020921180e8517d9f96649678c38b20adc288aea5ee0cc749184524ce96f9a679f268251a1a77215b1b1c00246c38b4a00027be26380000002dd0b2400001a70a467ec259680e91685aa0000000000058b80001dc250c000080c0000000177400000000007cb0426491000049f07ec8ad00004cdc000000000065a12bc000000031b8000b590000000000081100002ac57200000f28ae32f473b7164833ce80620584c466526e400019f80000de400000000000000acf40000001a897d09f9800000004e140003d588280001c704c6000072645700000000bc391f23ec1c5ba9180444a594000cc034a06d48b698daf7e00001400000a189540000000071ebf600000002f9008b90eb3d99bdf0fa8000a4f8000000000018600006a4800000016fa42aa1240000c74b0f04619731a7800005c05878000275a9ce000000000013a1000000000000cc00000005a7000035fd6e6a2eaf5a09f00000001fe200019d80002d4000000be130892843e18bda7e2c0ab3206bf00000001719c64000256100027e20001bc60001ba905d806b20be7450001895ae694ca00000009bc0318000000018f0b02000237100005687f468e4000000000000c700005b8bde40007be00007280bf2c296dfc93e136e61c5a660001dac00000000001e12000236c0000b3313f186f000000000000009d6aa8c0002bbb00013ca0001ac6605a1e84b0265c70a98f74260ebc7f9c04a8488da663d59b0bed17b785e062a8a21d5a15291484692ba435b11981c9242a00000003f1d283230070576da07489c29cc8442894a38c000000000082689f800022f721d0c34bd9d4ba0000000000058fa938000045c107000011000018b27adadb600000009e5000095ae1ca64cd7733d4193500000000000000202c000b5ce0b00000000aba024a4e5efbe000081e3fd800000000000001a7b88b2d5200000004e30000c10e5862fa800027a8000a1fa73259a800000000000001abc58e52f053e125e0002d7e0000f9300000000000595000099d594a9540001088b691b86a277016b808b606cb80b374a1e5224523940000ce6b9b15580c689b88d0634e88cb0ac000174205a80000001e74000168a4e091aa740800029b8000000000051f800000007be00000000000965000000000000b60fa0e183c3000008b40000000ef58152ab6a7aa65a29ce5f937ad7b09c15cc00598f884f8009a00007318e580000000284417000000000008de0000434471f708c680b91075056e8ee8c0da8ed50bb0b665d5b504241b9910eaef4430944c8a68ed24b880c670d2dd6000308c6454d3e00029c60000000000177908501ab00000000000af92b711d3000154723603d80e9
  | 36 => 0xe80002ee0000000000070514714a0abc0042b045adde87c31f0c32000243400000004ca873a13031101f30661680aa0550498c80000000760053e53100006b40b8000000004000000000261600002e00000000a31928f5e18f32b9c01062df00008f0d25175000006140d660a315a45941f234e480008102b582950b7e79691001bf4000407212b9d0c8f038d0590bf92b2a3ad0b002388a7f31400c81d7eed09348fc90001e200001104680017a7e0000050680000001e449ef29fb000255a000000000014f782cdc286550000498e43f685800000000000001f5d00020e8631b07c000096b7c29c1c83d01986358000000000000024ae0000000b6fa2bf5fde152b56103aab200008ac1e9aaeb80000002ede284898a67b9a880000000545019e6db98948f417080000628a4a13d418126a200018f491380000000000000000000000000001cd20bbc0000001f2900000008148d36000000002022e20e599cf6c68f97000108a1a5000094104904926bd271a2f00b4180007db00008901afc00000001bd283e046abf078b8b0e00000005ed8000b1e865e22f02cc0000dda371118000014a6000058b5ea9f042548d694388600b538b384cf11a833c840f408400000001c2391ab84b4d946f0000530537014992d43e025eab0601b936216cc00028aa24c021e12f62a9e7e0000520b6eab366dd0a5c4ad084ca9449ca3c2689aaf501121188000000227a00000001000000608892a4d8682800000000000000a680000a2a2ff671804fe09b00e32c153381402306b9d8000aa188260b709c200030ec2ae1b1c00020d57a82b3e3dab0260000000977a43e3678000650a02e3589a64419c0000002c2c81a172ead4553626d8809bbba696000008cb1100007fa5bce4f7800035bca0484795001ca6daa8c5815b2dd977559f5312b969a5c4c1a05a67dd7cd00000000000000b47ae1c00002710000000000000000000000000000000000000026384b5048c000253e000230200000007092034383258c000105a000000042c1332967048058469ec5fdab7800027fe00018027cd400000015b49538000000198f0000000a86800000015f700000daaac2a073d38000c35ae289e282cd00024775ce00000001f9075d27dc00000006afb10cc00e1f62218eca6d6178e3604f9a000128022880007f780005fb6e12c0d18b10292cccbcb00000002d1862bc07646b884d00000000bb0ade00019404d8e49a000000000024ee67f59903c85fa40002a1726200007ac018eb4f0000000008e3340cb16891ade2f2a45a45e4ded1c293780c5951c6666fcab7ea6e366346787495c06a929050a6f2ce600020ac2b94a22000113400000009110000b88aa0c259108ba5d3010bd5181a06a98201704f10aaf40002cddbbb0000e4700016380000000467a39855b800
  | 37 => 0x749616e2a000000090a5c3800017f2a160e6c4ae4000355a976000123c000042945865b138dc082636df628678000ac080009c2d480635daec00000000000000000000000000001c34a84000147056fc738000000073a9ce4000081f6fa0124ba61c6e2b1597c0b6db20577016c0b38e32b8b91e9a8aa40429b60b1000000014eaa940e6a57a0ecc1cda2f461eaf78000000084ac3f9ed26ee14884f896ca00211fa553288c678c3bc00029785620000322a8fa6739bea5670c900002f228d4800000000002a80d7c4d7873207f2bc45b60b0c3c7a2e800001e500001c5853990b2392a54000000000000001d82c7b311000000000003596f7a438c000000030e511800052124460000cb7000000000006967dd00004c504b5000102000015e20000634097af7c00000000002cf8a170e93ab1af7d00012be63905f500026d10c52b4667ac00000029de63a9b6600000000000000678065f0000000b640000000000003b80003d18eda7450000601d616bfd069a98d1370049ab7a00000003e1a40e000000028ce720aac800020eaa821580f000000000c128000c1682ae13c8a9e0900df87219c639561a8a25b0ab95698f072418000285ac320001afe9b3f00621012b87d2529e0271c4c17240003b880002558000c2e9ef2be009227bd1c3676c000000011cba10968800017cc0000000000020200003e2737c00079080002c8abd0a8193ee9899304c23e20897480000000000000247c449000066040000000e4c781000000000000002d7aa3689668c44000093000000001cc03d00003018f120af0e4b9d990800002fac0002bbc00023b21f200008d15c6f4810000000000083c000000005bb34ab07800000005a9c00014880005a81eda0000000000000000000cb00023a400017060fd0a8800001c87df4d3c0d617ec1848bb6209c89c92a800000000007aaa533000000000001cf0000c820002b6b00000007c22832036264c00c2222923000000000cf00023cb00000000002480b4b800000006667d18000a2024867668daa0000000adab04d5475f0e0b7800069c9506c3196d400019552b540004b3ab940000a208bcab6c636800000000000001b6723fa6ba0002fcd6018000000000000018f6ad9800000020ca96ce1889a6e822685000099d2be0090dc62351079a000029829bd80c69102ee0a586be81f9d2aa41155a000085e00011c69fc000028f00000000c0c18b87ce57d1e9606a520021226c759591b6404251473a1b9a5e12d985c5024ec2e2c9e5902ac44cb000016f80007aca15048b0000b60aa500000000072800000028ae2f1aa1ca7600008c480003a9115a51a8a28ba10d955741e9806593ecbc048240001d1f10506e10002055c37094259e8d46af302749e21384919ed3aa2b5980ada000054b420e8e008f272d210c23
  | 38 => 0x9aac00074800005c1002b1c000000000e4e357c000672184047385ba9c98fe40000b0841d0b680000762000068c000000007805442bd2ff83898000334c000888168d0000000000000000006cfbff4000000000000000005100000172800000000002cd000000027780000000ba780000000000ac100004ec40000000da50000c4263b463367c0fdc63ac000379dcfc109625266bef5ebf103b499085c83f99326835e3aa88321a20000000000000000018dc000000078d1ee60001340000000000023720000b4b00000002e700004f304b6a94c8383dd80000000000b5100000fc20509178844000154000000008f0000037812fe84398f800000006a90c3865e40f60001ebc3f192922cf15c70001fe80ca8a6600000003a65b00553850c000000018816c085b00004c589706ff961494c80744a518731f50ca2000000023780008a080000002a0b07e2a1e0001efc12485de0002d0e00018f9000079200022fa0001281000295ec184f3c0000000000000001a22aa0000000000000036a0f0654b0000484993794a0c08647e26e7c011694a200001b8283400022db5a0c2f09a6800092f14acab710e800003a8000000000000008d31b8200015f20002522000027237220331c992d639461c09ea1e9e3c8d6d73e487d26a044f8619d83842196c30001728000000002a0ec0000183ec24400060380006ca1ef679614a8787000000009d0b9500000001e1898291ee000296e84011450000000000000032f99a20002628b38932277d11773576b2c00000005d4a31c10e00000000000000244882f092600000000000172000307a9b1b08873b800009700000002db8a8001fe9262e0cc3680000002be8000000000005dfbe28000661000065f400000028af7f00000bd62d2c07beb6706dcbe15259c5626f29f02800000583800000000005988c0e00003f83f600005968000b0585fe00000002292d8a11680005fe40006d0800000000000001be400019780000000a86c00000000000000000c2907e600000000002c14293212ca548d549d700008d7933e32d0000ac3e8f30000192945956297113e66e790a6266d5c62d691e2000298c2d1d5ce5deafd90000e3f9ed9dae368800000000000002cd0a058d2c14d0cc01f100000000973be15f8800000ca75c00000000000000000083e4e1200000001f18000c2a18ecae40000ab604b7171edf7aae8de9215800062d000000023840000b0b00000000002202103a9fa38414550000000ac986061ed8000000000040580000000000000141087200c000000006f68000a15982454626d20000000000000067980007c7cdcc000228a00023b30002090000256021f192a420507100029004ec80000000000000000000000006b380000002d9647f8ffa0000000000000011be84e00013
  | 39 => 0x7dc0002ba0b8f18caa59028aa66000000000002d58b8400000b50000cf0675c09900006726980000000000000000002fa0db2adc84d60000abe0002c5b662800080200000d000008cca08e000000063c001614782fc4b420ba88eacfe56c800091601840b22c80472519d80c28ac0c558fc0000dbc427934c00000000000000000127138d9f7fbcc000076400005d2800047d113e00024fc8a025b032a9f724100000246000020400004968faa1fa80009340190ba480007971ca6666000054107fc0000000833b056add000065b2166b7c8aa86f30000b2e9e3a33808f4000000083880002c4855200000000001f4401a95807a728db00016510fe87098c940001d490b763b87a2310000000005fc00000000000000000000000013b000000000001f78000000000000006d3a45669c0e42a68aef200000000002886000015100002fe000180f9558000a310000c310000000107c972000035c0000ad40000000000081a4cbc39923794318000c0f10047da40001cd15fe3de800000000000000f406aa205865c8b327529a3e4ba1f38260a42c11330e600000000000000000034e807800000000ec205c0000000ce711bab3c5ae4684365c3077c0a1aa2bf800059d153206291a04b18000000306c00025800000428433112b000069200000000000000155a13476800009c90f829460000b410000c240000000081a62da494479000000023442f88000bb622c49d9070c5fe162a007a0b227140005b8ab28003030c93c932773201e6b480a6c671897899582613fe1aac72d8e828c52fa24d92f2428c196615e91b945e1a1e8f858b30002c7648c0e1a6dbd11cb6c000009ea04600000000000000000000000003550ac01570000238000000000018960000094a1100003138000b568000bac9675a278b74380e3cd448211a0000b4ca4657681591a752560cd804e8cd5915d2506790cde11ca4ec7f98000b9c8c460000a0200000002c821b600000003ea148e000304600020c81fe2c210002a686fe00000000497259db8e0e7800032e00005ef22d400003282a2a3e560714f670680001c201e700005720000910980180911127c04bb80001599c1e9399262b1f1722289859e000000000006141cb00009ad527a0000000000000000000007a02f537e3000000000008b9a8a0a29937577c8000617e8f662b0ab66105d6026f80007890000000029ca2fa00e7cf135660fc459069400011f24a09ec00000002cbd3e56af40b585ae89f0000000000000000000000000a6700003d52ff1000000000000007108000b2a0dfaaa1261474400000002ea60001621a8e096fab5000095228aa851800010d09eca3c0698101f01a41599db70b800059c4000a0408ae3fcac240002401000000053e46d00e728c000000000000bf458d0000000000000000000
  | 40 => 0xb8418680dcafbc79b8000bd9704b61ba97c461896a0000000657400043381bc64d00007341a0c654a4707d0000000008b80000440196000038a87484009520bb300e6b6a2520b868000c1ac6a472ca0bec3e000000000000141ca4b58000000018e6c19000000004ea0dc0000b63a9b88ef00000000000000000084aa605b0a00006eb000000013a05b127237169dce6a88bd645c42ca8d40000a42200c27ba23813d8c889ee1416a3fab693c0849600000000000000bf18000000229c0000000000252c222971a0eb088426900a2a9923beb0183ff99d98a29b0a5100a080000a2204a4c4000057b00000000000ad1e8ea00001ba9cd80007081e6657f4a906e5113b000153888a036c21b000000000002c6061c28280005f7060c00023b600000000000000a8821fa8410000494effe00000003070bfe36da2840000f4cb5d000030000002d01b8000019500000a6812e5bbd88f0000a26c000334abfe9598000000000a8a80000baf25fa00000000daabf200025ba06f80d38da0402a5c12708368b8c7779b1040cec98877974c56409dca571fa05dfa13873e9dc616123f452ceafc77483c429698427a32f629b2041e7b5006d211ad1c7e29522940289012086fc5a1aa4045394d80000000ad8275e41a400000028660000000449400014680006570000694075a4be992c0001a482309932901b001b0e2f630001da6a3b908d2bb83823b39fdd8f0818f037a85a90421f2000000003900000000000000184ec010b1e4b0a9c2942139ca5c8367bc69ac4a9800003478ccd48722a2a29c000136000095b8000ab00afca43842400029b000015443310bf600028f2000143e0002cecabe00006be000054d00006020000bb9800000010220002aea0002256000000040f5f2b0002e183f4000000027ca00000000001f7a949a8184ed1f83c29ea9a3f54000674d8e017ea8d00000d20907000045926302e600000002d38000216dbc296700000000a2ca7ba0000000000000008aa6fe0338875171224a03aa752567d5c900a000038c000000000b200026c4b4a06f00001f5800003d00622e68869c26a00002320000cb382f40007028000253035028d800098701b4054d9da24c80000000000aa903e60002ba84f60c12000281c00000000000c9800022dc00022642c6400017b80001f0d7ce3e980000000000423af2600000000246d700000000000000062283d400000006acd4b20000000366306aa7294b84a7c0000000eb039129304c810ac78581a7b791a30086176907d1a6e8fc83ca000239c7ede0ee000020f83ea3e400019730001c728f2aa8e00025a2c11e5a82feae80000000000005ce7d8226c9b2a92a3a10e6a5fb800046e99aeafb0d22ad100007aba3f3c40af9b21ba1820002b7e2ac27620cf05f725006ae290efde8e980000000
  | 41 => 0xa0b8a1d000000023f867ec15d00008f80002dd2b209ffc40d4000000071200000000000000589917b00006ff164d85e5c92388766309c762000026980000000000a2c000090c000017a80006e40000000181e00026dc8392f4d684d33570c99120000000ac70000ab400007c8aa9c83800005da8000886a8a2308036e46152ad97d80000002d140895f6e50301608ce23e08ea0bd1a358cc2979400000000002244000afd2fb081c2c8c8461240b03a12e5f6122e0d68a32b1317e2633c77ec28065640fdff545a800089200003d620cc1d326ce42894180002a664512feb43653cf025cc48000049c21691767016bc16a9800081303b8000176ba69b01438ac5d32db8000000000000000ae7c7983a999000000017c8000000000025b6000166719d16fc47e2ffc7ca129500022be1f2898496d003e000000000000001b6d03000000ba00000002d2000067d800023f1881000000083600006735bd300001318bf4000a478000000092eb5dc00000005b4201c00078a00000002cfa6408000898836871f92afc1700000002a6a810c0003620c2200000000000022c34a108000185b000000074300000001ac06164000078a02c00008e852370932d887de000198b9d3000e6d51958000000056de84a1f5a5ed5cca2fe39b80007a4134800000004fc800000000000002c720000000674a8d13b30ed86c900000000000956eb420000c5200000000000000739977ca3c5ddaa33000011080005bd4e7a917300254aa5f7640283a2b522e35cc0000c2d169361c190e572000000000003199e1e0000000b00014ebda294685700000001df5a29635d6ea857c0000a7c654c00000008721c0800000001f000003780000000000000000009b01b18ce213680000001c150000000000136a0b680008ff8fee000244061b4904454aae60fb21ec2bfda2cbab29b69b792938109814c45045691e2a4cb4c18f30000000444929caa62a6c9cb23264cd9160a85800000007e268aa0c44098c6a179d660751800000022fc000000056853dab30840a00000004652936b160000442ac5c4291e5670f9f3a000073000017d70001e2c00000002e4a286620116f315800025800000002984000000050d188664c6ccebfc0000ac40000000000000018ddc43a0200c183aa3f8072e7b288b042e41b24ac1135c2cacbe9f51422a7ba14000024c8000000000f13440001fbe0000000adcc00024d0c64c33279c96680008301774c1999640000000b4928dea1c0000000155e0000018000254a000239a67580000000d600000000c12000000004de47b1072bb46c500000000000000055e231e309c1ebbc5043c91fa46cb1828c72eb800000028d84609ac2aa2000095a1cc60d81c6b06e1190854e55d1440c047170000a0c148a279ab700002cbc117934e029d2068c61a62
  | 42 => 0x644c8000000000000010ec000003600000000000000000000000000006c0ddc03a300007b400007e9800072fb0af43d1a5a65155bcbee993fc208bf500004b2333a5f4a4700007a38e62180800076315e896f8000068416e51e00009ba800000000008a49e1469a128a65e8e227ed8a4073122d36cd224e42f163c5841a9e3f21a424baac107990946717856c00023367dd86bd0002e90432194d0372c5e0001ede8caac6a7dc255500019cc51e4e981a984d2095cef47df0a787ecd7a6648b08060d2bb612b692c9ec9db89b84502462a076bddd2aa0002fd47c68f086bc064e5836218017921a00011389c28bc10000000000016200009fc7e149ac00000000000c3a00000000001783b9e00001828000233e7564b8005a6f815a8b7c24cebca0d7a7e794263e78bde33e08061e02d780568f960001b7c2ec153b5de263c81ae244b97971c4705390b0616024fd8d4e5932c94514969f3bc8e48634849a00000000002d170000000000296672bae0e0000e5e89600005f4acf01ca800037a935a166a2de9dc124b0001bf095d800093116b60000000000000074228a40c798f287f000000000008ba421b524800074880009d1063266dc000000000064d84fa000124c9df268a00009e23369238081450a2b02c9d14b04a31fc6087000135000b80e800012903700e540002472000000049840004fc175d00000000aa000004c24023448000c249c8500024ea000000049a8eb20002f745d34312bf72dc65aba3ce92b1661c402e96700abca5e5d3c86f88d9f000000031a00004da0000000000000000002668000000000000000000b49f3625f40003508000000150a00021688659cdc9d1d94c00009722d191562a51a5200030f10001dcc519a4e00001a4cb770aaa0000000610ec846470b2800003fe64827800454e78000000000016aa2c29d9409c09f49e60c58000005600000007228000318800000000007e896a62281f54519ef8e6434000470c00000011071e38064bcdd07e6d014065f64ba800010660002da0000266283180000000000885a2d200000000000000081d7ac99f83201a7800053a80006d68000b3a000000000003a5a70c00020c169d15a02a580f34a8ab536fd0b1c20387ee4a10437bfa0e8d5bcddd02ef80009d60000068e6a8be8112952d4000000141c0000fb3970126cbb6837e2f4a40c000154b1a5ef398a6248211917fe00000000000000a32952470e91da85f1fae7f6af3a00000000000000bb0960c0000000000167984c000079322bab07882a323800027e95686669b6c000277299408da63bd61a6ca9cd66ab9f5c0002343a9e00003e004c10438bec6d94000000000000000000000e9e00006dc00020060000dec62b400000021580000dd08af1ba200006b270200ac0ae17a000015ab65663e26ce1edc5e5
  | 43 => 0x380009bd069300000006a5115069e4000b6b9acc96284a820b22ea8b9e74e3a898ba01819be978a9d0b14a62cb32910d306a1166b884f443f0104366c4198ca15ae437a95ab45aade2ea9c9cbe21f4d837225a980f1045e225ee6a3815c4030eea3dc09f6000275b0002854066c000958d3e4000000034e000000017be1294ffc0f21bb05f6d4f44c3855e0000212000103200000000001cceb32497500000003d298d31551a7ca71ebc86a821720001e0000019760001ecc9af4000000156a00000000000000ae080004ad96cc000000000004a600000000000000343152500025ca6e49bb6b5d8436069000000013668c28e80becd30251e94b00000000000000000000000001c7c66d992e1632c3e87f8902b54000000021da000010944b4969b42a24f9eb1068b1580002b9a39d00000e01b5a2c8000000094dae40909103c27100005750b88aa980000000000485888ec3400000000d920cd1b7e000151200000000d0ab750518fd4807047000007823878000682119680040000002a1300000007fe8fba50c8000117c83e10ac0003ed5bb31ef091e4fa073e66cd3f4788aa74776157031e80000000000a898000a6c9f550000000000000063a00001bc40001f6230849d5bbe000000000011ca0000000856aa3c00020108f186d2c1300001ac6e86a27de5473086422b5a7de00015de00016181c5c54c64525408f4a55c0100f74103411c0ce00005a5017e256975a31e11136b506304d95b44a8129be0b985d59bd89791ea0000000208ca970388219000000026e80000000413629e000000008d0a5000027f8b50927e00029380001210aed23c82d60bbc07601d290a000000017f4473706000000000001aca9060032581af8c0002ef62b4ceac0002fe0acba8ef7c62ef50bd6eddc04800052d24167da80008db8f2e000266e035e8a165ec5e8ab0aff23281a9022a8e0b2cfe33e9bf0000bf4a0a6b7b21dc2ca91d50081c500000000c0b021100000000001b140e82a480ceee669e3d208a65096e7de41ea21da4145d6c7d089a1fbc00018830001758ad7aecf8da80007cb85e6af9010c80a95861621ff0acd2ffb736aa1f51b26bf5b540004e563f600020480001bb40000000000062c8ee00004fe249e000190907a00f05a68a3e7a1944a40601a6761189a98380000001ea23029810a53a4904aadcd5000000000019de08d80000000000000000000000000002b540000000adbdd1e88c06a00c700003f31ce063123a00000000000241200028966c5c0000000d24b1faa1148a957e4efc000000081ca4c906aa8480003b9af45360a77e42d92d80768c80000000000016d900000007d789b460280003c50000000174b000114361c815845cd6d00000000272e1a8000000066b6af60000000c108000b292cd4b73d9ea000054e00001f
  | 44 => 0x940002c1c6c09cd482d80005890000000106f50219c000026ec027800082280007f62faaace1c8c06bab1605f49c09f1802cbc0a2e462e293b67552f686c800038e9a8004b9de676caeaf7f3ea5e112ca56000000000018be1db800030f00000000000b1900004464b9415aa2a6b0d86ce08b06363df221e395acb478c1e6065aa0deb3d2658364104f24287f5a442a2458740005d92eca00015486a34ce4000000054f2bf892a13ac0000bfc0000354277eb6459b400058c30a90000000887185d2764000852acae000274f00000425c02db400016000e300004bd06822b800000000c4c559041a9a9af3666c907872a80008b00000000000000017ba47c0000bc798e96e229a422c800000a8abab11800090ca49237a26b47e6b0f438f41935a16bdab100bdf58ec00043028cf147c6d40001d7ebe8400024f1a4fadf68640002c4800000000000cb571a58a46411f6897b0a6264a2f691526cf2aea8ad816a9d2100000000002c260002f160000000993a4170000000a48800056e400000000000000000c100cec133cb5c6cb206c2ba502a967a12666a15b311cd6201334b9a9ca8a7a871129d00014d67e0afea8e4969e0a004e49c887950000286a9d8000c3f16e8a02270e9ca00003668b5098a8d526bb8cf6a808000a581ba875b0000ae7134583440008fc2bd676196c686514a0720873b81f2f9901180b734b86686e589163890758c4490d28ce877cbaaa224466ec2e402704e5ae0078471593b0bd2ed39429c9a45ac0008fb093a1820b2c000158400000003b1275400026ee00000006208000000263a00016900002ef8431076624380000161924b9a8a445ddede1a0a90f660f00009068df40002f9a69283dc0000da0b669565000000063eb10a00000000002496191231f0b4000089faf51000267839a00000000000000246a6441e0e97fc000000031000015a30000e88576126e9ff0aa43d1220e8d7ec8a3afb0c829dac54724545c6c21d8e74f155679d80000e3a1a0057803f800c093b1fd87c8b140001a54e581bb9facb2494c07729a8792ea86ea8c879cab8a8ab3b59e4605522c636911667cc838a890a62eae2a3158642a3665dc4182a55cac69008665b3a95861aae2cbf8a294a911c92b2b0000627800081ca56cbdc1ff23b80000000000000000000001c3066b117091900000000000000000000000008ad90b40002b960000000000000000021cc6ad9793b85a2125028e0e613174400000005a3261e00015cc5afc000232271a00000000000000bb826e700000000000380ab680b84798000c02c0000000000b98913a0001a6c0000000000138a00000000000000800acd681397999fd2a70a118ce51218e2841b2260000030a51c92b20000bc805b575939c23e86e2979525225705e3c7680001a3782d0000000000027
  | 45 => 0x94a062574a8c150906ea95e1bf60a480f800012762a6a86000023d459f1b3a85a69c06d6c4aa0000eaa45ff070844adee0000000000000000000006c5af340ad0000213800023dc686000100bc23b0e858c919c4722b980630d0a19fad026a60ff08dbd1b0ae051bca82a93ab380000b4f8a86000300d0001236a88800006880000000000464c6ba8665ca298600005e880007988000bc18000ace80000000000bae86c17386d089f2132408c5c8ea45a1b409199d1711a5a67539cb80000b8e000125c8b3975e0d982244335b894a453a8995270d68418a03386b437fff000337cf0e4ed80000002ea02de80001949ffe00006b60000000b0d0000861800004f817c71e110e0002bb5520c000bae237e6de800035e2c3ac161ccc5660000bb712660811ff87586f3c000027600006907b09f9c3df9a828670e662c58bf05f92e6436b00001f02ece5ab23d65d7cd8c6c9a354771116c7d42ec00001ed8000079001eb09e73d2eb6000000017512ac7cc07fa000013600000005009dd49d280005244000a45ed48ad28eec64e80007540c726e8caf80001d9c0002ec6418a9ac595cbc42c10c9e8450ddc32c13d6099e39f0000bd0593400067f8c2415d8012000195b192800000020d6000279a00000000000dd494b80000000000000000091500000000000be980005888000af9ae2500000000000000ba3269dbc4ae14728d038a851a3a000000001fc0005aea93c1eb94c23ec9e7200021ea0000ae2200c2a38cb00000000dde0e4c00048988080002c3000030a69d55bd593d9f163bc1d270002e3400011b8393e0a438245db0000000579ad7157d8f5a1e319b800001d580a00000001f2a3c5979200029aa90b8000000000000008800001c26836c2ff3ce0000aaa90e080d82546522f033f494e6000000000000000001726000076c000260c00000000000d029bc800082340007ec50460e5400009425538c0c000000269f538112e5bf8f18b5f1c1691948d48b4000015195a2ba9117a073a86a2a4c1345289fb8000187d000000083f2484000000000005a4000191a7160000a7deca28f78a10c1104ae30b979817cc258371800008e8000bd908960000000a148e38ba20cdc74680a63c4d9185b22c861d2e8e14749c1835a0000b9ea5ac6f2961310a800000000004782466a8d20780000faca2d0000b258000a3940005970000000173abdad4c80002366070701c49d1442a8b81480452aee263400000000000000000b921b6a000195a4fcc0000001de4984400091d0000211e939000000000000000000000000021c1f08000a7480007b3a43c1c5a4d71031d7abca86919db40000000e0299a0d042929c6617c825300000005f68d64426c852ac3183d000200443d5cbfa012ee41ae44a26dc91b435b8ae4a38b04181957fa4dc800000004
  | 46 => 0xca4962c7451ed9d08ab0000000000000000000002bc68660cee1782f420002de6c22dc6c86faaca00000001d0c00083ecba000000009ab18fe78400000001e84000236100000007688000000000048d15c434500000001c127ded242415048464e1a8c00000000000000715193e53b80003d2000000019c400021bc61b000014a05f98be09ba87d309fad25b469a70c7e0000000000000022603c68000000b1b982c5b15a0a00005b274cb00900001741138814a83905e20800007629f48c039ae45279fcc0002e5600015f849e126f00014fac078e8a00030ea30c190618407e03f0929a139914b166e44c5e92cfc44630f034680c21284000bfb435260023746d65fe45b68e31bee104caef800002400000001453a5a1be6179280e6ee9eea59a25396b49c7a0000c5a9a6172c8eb85e10e4946453519fc558236098800007149772000269e34a10a1b5180009181d447d6ef72000000000000000000000b37800032ea10600023ea69790fb59ee90a0348f3a15d000050e80002640d58133897c4b484660000d930001a960002df80001e08a780f94bfbc00022797e666a818263330ae14e041200000003c0c00000000000000000000232e5bc800000000000001dd6579111f06529c8ba08000a7d800000000000000000000000000005f092d8af20000e948532a09b82a75319b8be61c42b3254b8000000139325ded6f7a5000037c8a80346000051b444a0c9951a9b4288493c00008c8c00000025a000000000001ae900016a20000000b78a452000055f8db40006de31082f6000079e87e444240000000000368d24d286aacb6e993130000800000000095940006919b22a865b6264c26ae1d506409308feb00000006b62cb600023ee00025620001f410000c1f4508000a60a37f038800045c86d8000136c531ae2400026a9000233c373858d19f603c84a5e2a000000000007b8000214800008706cf80000000000000000009ba57e91080d4a32e066000170a56a800000008780000000000042d6dc298a39ceeec97c50f0082000000006d3a9697b2684800000028c27ea00007eea31a3f0153053a0000000298e42c98bc00013f5725192661f84bc9900dba5f5271878d855c2c75fb44ee294884a201341ea4503f5ced4a2fcf1d58dabaf6361ac547a99474808cf49d204c671296f01d0a71013320d4325971e8d70f3e4f2c6bc363830b0ce98788b2a57c65280f57b009503cc22964e1a34041828a9a101eee8de98de1118d5a50f182308c2a103d919d40ff2ab4091027532f6f7b3650116075166c6086f6a8f9d9ba00000002e0ac65ac9000000028363d800002550a4ebe48ab3273e99000000003bcc6e79b52c02696dc21095b022a28e01aa769b322e8875ebfeaaa2b4d0000aafa9e852d847858200007e3978dc030e139978000b
  | 47 => 0x2d7aacd3c70dae000237516d88ec3748a35362ae8e055a6b86d7c000138eb7c59ca5741088d4c83f400028c59076b70000b819ee928b84ba036eb4b0001576000032e000058625a000004206f90000ec65388f2c4be00000000bf843e9be70000d0676a1604ab806260000e8100000000002f5cb18a9490c21254366579e1e10b44000242646980004921c0e000000000000008e4442c000000000000004e78000c09138eace673e79425b83870000ac5103e0000f723fb44d1b3100009c02729b7d9147098c0000b000007c85b8c06b10087591b5205293d00b51a777df88f6a04aa087d3aa7a57ea3e377a05bd000057e738ac9c75e217095e62008799d181fca09c6b980003c90bbac21e1d000000002f6a94bb9186c86c48a245d827147fd27380000af01c197e09ed203292393a4bb480000002a3e079000000000002ad000000017fb000000023280000001a5d0446aa04c3000000015b66d29d7c8e7ac6874b0000000151e9c2000000003b6ba29f3e3f6c7185ff2cc1351df9470f00000000d5e00004320000e5a0000000000200fbf3a2e0c3e400000000000000000000000000000000001f8f00000009998000000000000000005b480000000c847c500002e9adca9358ec2000000061100005911aea00017460000cc879c2b52a65a346a805782185800030a6f04809a906127a2a8268a8ff1ec9cba359c2d8b6484b437f22f96ae800033e80004aec00088aa76fa3a50a900023fcb0ab09a00018570002d880002cbf0001d5e20d8000b26800068b80000002f44b9fa46e73d890c68a20a0b30094e00014ec000000073b043e58f86c0b4c86f83e29830b2e2e745cd1750501000047440008c1000000026aa30593a7b391f5200017d500000004d1c00000013a6000000000010d39fa1944a51078a1dd80004160bb400024386f480000002eb17d1c00064280000000000989250621fa250a5014381a3c000478e1c25bb0fce1b761840000000ac00000196874e494804e2da85240001f6400027405260d50299270261e80521d4c48a635263e83c9ab74a9a136332909a4368b3ab9f2f38ba7003441c00000530118ab5a64816ac000be711417ea800000006b000017c401c80d0ad32cc600010b8000164e0f92bad000000000000000001e3c00027177ec8000000000000000000e400000001a4e1498bcc0000fde4b294cc66463dc66d4d30be5855b2c06ca0c15235abdd85d23e61fc470023ac22a023c6232d2b38b8fa43ef1fdc28f400042300007194e5b4f38d5c621000000024620001ec6bd2c00077e208821706222a8dfd65960000000000026c92183cc43d669a8000000000078300000001ad60003013000012c00002523ab800000000000002a96665c1d10000000a644cb26b68454b77973e2c192e6b9becb20001d960001
  | 48 => 0x79600000000000000027eba2000211c0ba80002af6ecd00030723602e3e0001bc4000053c3498756b6528b160a962cae1846d5269946000000000000007d980009ac16b00702b5f0001d120001fca0002b3b00000000000000457c52e000144845d703e42accac7b58d086d82590547d0e40b112dd2ab0c9296b48cb000066495929d61d29454bd30000000155200029343c8863a56faf9873f8000000000064f672e114286c4c783130002ec4000000025780000002362b36a58e0ef80002721ffda449fdf57000009318266000060e00000000000f0b6ad1c766fb95c15432f2e8b32dd82a081de80483565528aae00000004b10000000000000019e500000000a698e22d080008df2abc08e4a6a07590481ba0000399c000331809541e4000000000000026b20002eeabd3d4d000004a093884880a900009f09ff656791de507848eb5aacaa427185a83aa94aa09942a0000000000000008a1199c1f8000a1c80003964000406c1b60000ac20002dc41de835c76f856e00000000001ebebd4a7ae67a48d05708e143e442784418000000026078e00000000000063400000000006188000000000040193344f12a9ec1b8000ad380000c000000000000000116eb9300263981d389760a2d6cd800000003f22a48000ac296054d19dbc0002cc3bbf1ab254f80000002bed4dd9a8692c26b60a826cd397c00000009940000f0ac18a5b200000005b800000000000000150200000000001d5400000005d383480002992976a8f43298d7e04f16978399d06b3170f6271d8d585086548364ad2437c8ee8828e7e4050d7d0af8f5e4b72dfe51d8a1e96f0251085a0a277f90d64b911672c525aaaafedc8b96261a08280001eea4f43b42d2abe180001c810527a48000463c000000213200000001ad00003bf80000009d3e9dd0ee4bc8000089c862796bc00016c56a52e5868e3e3800000019b45ca87145505dec2a991c224015d696523d8c2f2730c3800008d58000000000000000000001f25b7020960000b1069500004d481ee000000004e1c4e0000c14000218ec25636459640007bb066c9d42712000191e00025c39a0800044a08125a08000b5d537f0a7a06a61480001341858335800057691a39ce8000b40111a126543000000000001f813edaf3e8a9049f39ca9147c3137c000280abc729c44cc0000024b0846342bb7000000080625920001c888744000021000073c826400000000000f26000150e07dc00066205d744cc5a181819a5000000083fa892031267236e1fb5035863e000000090d80009c78000000000011a053600014e40002512000000019712f20001b5e50813aa08300007b200000be95e094694fe1e914360346ea811709742784860a260000000176e9e9800000023e639f0000ba502680f01b5c0000000b19903499b2e9a
  | 49 => 0x25700001c9d52800024fe42ea48a0002d62000071a00000000000a8300000005dda94c00000004a30000b8d80000002ae4bbf8000c391c2c2e915fc3e880000d8d462000265200019f400007dabe123243b21aa792900003cd02aa000171614a85b00d316840002a56bd2a69200000002d927922a387948b7d0cf8394c5e000000055f25fe0dd80b488f955c0000000000000020c8e27000014433f00e734715f0591b098000000000000000000000039518e0001f454ebc26200028ce00000000002aec46fa5f000000009a20000984000000000000001f4a55093c2668281e000000053c80fa126000000027e019fe1561c3800000000008b945a2ae22d9c037559b88190642978fea7ab1082b7a86c20bce9e40fb875765803cc0e9ad22663a76838180003c699f976780005c3902e00000008e3800053495ff000000061d1c17000000000000002bd800019a8a8b9be04ec83407f6000134a0000000000179a0000000051f0f72d1700881eaf507c90000000080a0002b3000013963ed2d72ac480002241f376838d6a36700001568000bdb24681aa8100b169a0468821e472a050800000000000150c0de40893906ec00000007c42c4e78f93fa511000016a0000000000082a0000ae99a9ac1480000002a1da221e6817668d72e789a000014aa43620226f7a2760000d830000fd60001ab822504f00001c74551a54200007f41b68a1c22d047ea8e978a00027d800009de35d25543c81d00168c000b46ae609e112728dc06626958a083e7021900015110f7800000000000000dd64732b08404b0bebbe9c9e0000000000199e9532ed421ce9fc85f800011d80008f300000000ccf000064c0000000b730000132161f000000000000000152d5400004b819e94828dd9e4eb1b137dc0286240000000089966f46112ae16f1676000000000026bc26324da8ec05125052d5602198d160cc46a000000000000000002be2000182535e40005cf1da477a8b5200000006b77015046e7d673c117e10580a100027600000000000000000000000000a7b00030680bc4b9000000000000000966074030dafec5a2c000000281a467d4f066f00008e8a7c4b530000b5b00001e780000002d26b048000000179400029240000f6c0000eb6ac34efa000000009f800000025389cf509d00000002665c800cc98761350000000000000400008dacc94696000000010f70a85f5a00000001942ab8000000000000000592c6708f9bd606189da75aa6fa68d80000002c08000000000000004e61b0c0001adb8208a58000000000005187f4a88225f80003821fedc3896921de288e7088000000013311d40000002cd200000006984128000067500017de00027aa446c000006ab5c30089d82749d587868de600025440e622d66128ce30001e32b6316d186e96be000
  | 50 => 0xe2154000174074980000a898c223800009f406a2583d0ff7ce6fcb00000001fcca3804c998285830ca1cf14569aed30a2658d00c2ad2a8aff000037ee28e7aa171083a4c3e5991fc60000000b8c0000bb200004a801c6b8ea017077000085100004ef80000000000000000000026d8525110b0002c59b31d04e3db97d600000006fe8000000001416255546d923874b30048a1883743a38bb21c880001a206a70f39fef750976672402490000000bc200000000000000000000000000000000bd5a769527000000017853a190eea77173693e8e4a06690a80000d76220a1640000000000117d0001866bf01df60000a3a98480001e991d87d31ac8234a8e800013a292701f1000000094a80001540000665a488914683c9c105cb3292e1e2e1899e6e609d736461ee830897600000000000000244800000029e700028024d7000000000000000000afe80003a540000002b484eb9d360ec2dac05bc0006aa8102000037c0002eae0000000000268c0002e5c59b8aa211d29020adada25d59af2000156c58a0506bea00000000000279000000000008260bc226a000003f93c64c0067683b16f63caa0f899806f6c339ea600005d09f69096a601b5633d5970b1b5d244eea680410914068615eebd803246f088d632d8c4a7fbad5c161df1292994909dbafda07e846c00000004a1800079a80000e511c4689958e6ef119ac21a02401b04cb176a0560001a9c9d196546f60b6c975800078281e1000154d0002f6148a21d890792df1c6c00098240004e22b8e16700003bb91309a4256a387d136aec2236201000010725ce26700000002fe643ca3229471bf29e1a8e70001a4dbba0000c2761b088d0bcb00000000002d0c5e40aadb67822b166161cacfdc71483ae0454e6d1035c96968acaaac36c21a45c491b7420c728544210a44a8000471d6e421a27a05ebac4200001701922bb800027f6000158c000000000000008739224b12968ea178000a2700000000000645a64a88426c000030050001daa8c8186000000003ae80000000ab2000000061700001d340008ee8000032547c080089abf080005e725847b80df19b55c848e6c00000000002b41af4912878826007ffae79ba400013ea7260d34991800047ae5e71fc23860000000adb8be4000088c611ae26493c25b0002af23182bf606800006e8635847723dabad23fa7c9c00080523481b88e0ab7080a369aea903729a3ca559e7cb3d875c777036481700000548000a2f27790002226a3480000000dbe3f6668e0000000050a476445000000013fc97a114a7f510e5237101d0000000beb9dba0000000000164f000209e821000038107aac03eeb059f80000000088442000043500007e180009e0812a000308d7f38d4800000000000000000000000000000001d560002a300ab0ea081ec00
  | 51 => 0x1bd400017e800027ec0000000648e9e6406800074d1921345981f711219274e89629e9282e0001eb453f202f3800772000190c954871c402a918000240352f982844080000000f9000007a010c195720f0000ae480000002080c0a1fc83c4680021e8000a7c80001be86a1162806294082e41380000b88c41724da1802d980000000d6b6ebb039834a4dc0ec8000000282c6ff188816500008e2a7900002706000175400001d02c91ab055e99a4aeb28dc00024a258497a83e106cbaec8c2600016c237614de0000000000000000015ca00000000000000164800044b00000c10f42000000000000000000000613c000000189059e2aa827a000000009ae00010fe000000000000004b205d8000000048c882229ca38c447ac04a508000000000043aa1f03586fee2c8cf3699ea5e69c721b8517abba48890be025a51e0002534a96000000014680002ef73be08427a2000033740009a900007040cfe02f4bd7000197e49cd3f136d037abcc84e2208cd4a246ac1a4b79b4899c142c2be80000000000a322a18000000000000000000000000000000005a659794691d8ea722a7400012c23b427c000089a96f4afa800019800000a4000052300000000000000000056589c9ad880003eba5e45168000000000000003c20000c2a37f8efc3ae07360002f820002926047a7fa0000c54000000000028761dd225c000123e56c2afa22f80000000000a5b00002399e4800015179490f780001d62655af464deafd68ae1a2200000000000000000000000018ce4d628ec15e2400a63e39043403a26150acaa6eb0ee00000000001b19000218a0000000a62277a85d1d0e7010000660d1494372a2cbd992b3bd266d324c158a0a984ee9b680f2c2b4a79b6f170c79b04a43e800005458c2839419a7a1e86a31c110e665792a90002d84b3a8ff412ad9c292e000000006c40000000000000015000000002266000000009080bf0000000ad023675b7003800011580000a600000000000000000028d300023824df800002f00000000294a7f80002140000000000003f0000000000000000003bda34a7d0deba0000df77b903f64ef4ff797500006c14000000308a0002d66000016b0000834a7d00000000cd48408000745a838a7240000879d76bbc1fd019cefc899f000000000000315af686240002160bc30002f7800007440000000866ac8e4224fe8000000000000003da00001040336000303066726063439146805a76cad5aa8a3ef800053680009f91bc00000acc000036210ba54657aaf400000a48365a05e644e4d85e00000a091f3417d00006b809e00000000643cc5c0c88000ac6000062980008ffc0009708000261b038178b0aa24815a500000000001d1c0000000000000087e00001ed1e78513997138f8180000182689d1a843cac00068
  | 52 => 0x2d68000159d4644000b448c9c0002b1a9810120597c000000201d604508f00011a1115d5ad0d1993c0000000000120c0ee80006260a2c80e07ac000121e991159400018924990000000000019180009b30000a350f8c1bf800000005044f3400000024de0002bdc00000000001f57a46a15e3d7000045311c06dd92b1ab3000000015670ba279e482800000189aaac78ffe3fe6716378b0d84ded6f8aa49d2e7be9dc2b7d16ee4880000a5e9c967fb12683c11a065ed0000bc3094a271ae005f01b0a0002dce00000000001ee200000000002c78672ca854939de00000c180001bb2c224000000240f98882e277f0e9216819fa797800085b892ca6a2a6200010e11451574000000000020aa12f8a37000116d0000000383ecb062a2cd800000004e2400062b800051b9b300000f625b589ccaf08944000000085d800000009924ffaa6e24700009e8a572c17821a0000000a12000000e80000000000000000019740000001b4c0c080009fb94ce40d960a0000000848278e9cd0000000131c0000b70653800000000000002986af3840442b8103bedab229f31f5600000000000e409af88180002ee27a28deea0506819b88df68b86b3100008c62cd93ef00700000002a7cb29800000000009821f84000000037bc28e82180007c708ce00000006fb1450000000000024ca0002d5eb7521e254ea55e000233400000003b78a700000000000067c955c000b8800002a300004e460910001d0a08fc6f22b19812000198927500008c9e92e9c1d2a4a8a00004d9c0004110ace4e68000aa000000002d86a9088a685a96b200000006e100000000562802800000006a8000115e41d8c6c000000045d250e1b9ae6e60c97c231da63240390a08810d3a7bc11cfc30a5f876d15088d08a3400000000002f6e0000000000230089e228c736000047d820648e8c9a90801b000000005d700000001342560800016a49080001e061521b6177c06e400000003f10558000247a0001cf8475998604880002a6d97f48500009300000000146b97828e616580008748000000199200013bc0002b13ab484ca00016bc00000000001cca358c00021525ea5b6c10b2eb22549028000000000011e80001ab058e61200000b1b032000000000000004b6800000027d20aea5db1ec182e23a800000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x853671149420429d380a4a10214d5d76150810e4aa5b0a8408535751854204392a90c2a1021ca54b6050810a72ea3028408639651814204394a90c0a1021ac184605081087ce9b28840845e73194420422eb98ca210211d9c465108108f4e0328840847671997320421f3a0cb990210f5d065cc81087ce9b2c640843d74d96320421f3a0cb190210f5d0658c810c5ac9294640862d6454a320423bb8aca990210f9d0654c81087ae832a640847575185320432b298c2990219554c614c810ccca430a64084f170185320421f3a6ca190210f5d3650c8108eae2b28640843e74194320421eba0ca190211e9c0650c8108f2eb300640843e7498a510421eba4c528821179cf65904108bae7b2c820863954982410421f3a6cb188210f5d3658c410cb2a730462085557154c31042aab9ca21882155dd5310c4108f6eab04420865463945210421f3a6ca108210f5d365084108bce7b28420845d73d94210423cb82ca108218b5925208410c9ac7290420862d645482104326b1aa4108219a54a600841087ce9314a00843d7498a500430f31e85280218758f4294010c3cc6a14a00861d6350a500431731285280218b589429401087ee8b0ca00843c74586500422f39ecb20021175cf65900108eeeab0c800845e73d94400422eb9eca200211b9cb65100108dae5b28800847571594400422f398ca20021175cc65100108dce4328800846d72194400430f2a2c620021875516310010c5ca8b10800862d54588400431aaa4c2200219594e618c010caaa730c600843e74194300421eba0ca180211b9c8650c0108dae43286008477755843004316b2a8590021179cf65880108bae7b2c40084777558620042acb9ca1100218bd954248010ab2e7282400872942941200421f3a6ca100210f5d365080108bce7b28400845d73d94200423ab8aca100210f9d0650801087ae8328400845e73194200422eb98ca100218b5925208010c9ac7290400862d645482004326b1aa4100219954a61080108eaedaa620085357414f10042b2b90a7880211d5db52c4010e4aa4a16200847576946100432b31ca308021965966384010cb2cab1c200847976d4a100431cb2e85080218e5954284010e52a4a14200847976946100431bb2ec8880218dd9464440108ecedaa220084767614d100429aba0a688021595c853440108eceda92200863765d09100425a3b284880218dd954244010e4aa4a1220085567394110042b8ba88088021cc5504044010ba2e620220085e17210110042b8bac60880216c1d13044010ea0a698220087615288110043d0a1240880218ed976444010c76ca322200847a76d49100431db2e84880212e1d94244010c76caa1220087295250910042e8b9ec2880211e9da5144010ae2eba0a2008573754c510043b0a94428802174dcd2144010
  | 1 => 0x1044370b144388221741cd21c4110c3ea931c208861c5498e104430faa2c7082218715163841109ace7b2420886975498e104434a2a4c708221359cf6284110d2cc7a1420885347550a104434b31a8508221a95894284110da4c7a8420886d2638821044370b144108221b498d2084110f4284904208845d73983540421fbb2a82a021875516315010c5aa8b10a80861e6458c540432731cc42a0219358e6215010c5cc8b10a80864e635885404326b1ac42a0218b9d16215010cacc7308a808655639845404333314c22a0219958a6115010cb2c7300a80866962980540421f3a4c5a98210f5d262d4c1087ce9314a60843d7498a530421f3a0c4a98210f5d06254c108ece2312a60847a70189530422fbb2a629821875915314c10c9aa6b10a60843d72990530421fb92c8298210f9d26214c1087ae9310a60862e649885304316b24c4298218b9d26214c10c5ae9310a60862e645885304316b22c4298218b9d16214c10c5ae8b10a608635649845304332b14c2298218e5926014c10cd2c5300a60846e721974304236b90cba18211d9c66590c108dce432c860846d72196430423bbaac3218211e9c26550c108dce432a860846d721954304237390ca218211b5c86510c108f4e0328860845d739835204317394c9290211d1c5639481087ce831aa40843d7418d520421f3a6c2a90210f5d361548108b8e6b0aa40843e74d81520421eba6c0a90211bdd95214810c5ac8a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c5204316b24c4290219358e6214810c6cc9308a40863564984520432b31cc2290219558e6114810c74c9300a40863964980520432d31cc0290219658e60148108bce632e840845d73197420423b388cba1021479cc54d0810a3ae62a68408536711534204296b96cba1021479cc65d0810a3ae632e840852d72197420429b388cba10210f9d853d081087aec29e840852e7214f4204296b90a7a1021479cc52d0810a3ae629684085367114b420429d380a5a1021179cc65908108bae632c840847671196420423d380cb2102117dcd65508108b8e6b2a840845e73195420422eb98caa10211d9c4655081087cedaa2840852e72d51420428f398a8a1021475cc5450810a5ce42a284085367115142042973a4a4a10211d5d761508108eaea30a840847975181420431caa0c0a10214b5ca6550810a3ee6b2a840851c735954204297b92caa1021479cc6550810a3ae632a8408536711954204297396a6a10214b5cb535081087cec29a840843d7614d4204297390a6a10214b5c85350810a5aebb12840843e769494204296baca4a10214b9da5250810c5ced292840852e7654942042963b2a4a10214bdc15250810a5ae0a92840843e76149420428f398a4a1021475cc5250810a5ce429284
  | 2 => 0xc090a218e15060485108e8eab2242884d4735912144278382c890a219519763485109ace731a42884f27098d214432a328c690a21959d46348510caaea31a42886975418d214434a2a0c690a211d9db5348510ca8c7a9a42884747654d214432a31aa690a21591c95348510d88c7a92428865463949214423b3b0a490a21555cc5248510ca8c62924288727541492144362318a490a214d9d74248510c68cba12428869463d09214429a3aa8490a218d1954248510d28c6a12428872452509214436831ec090a21b4d8c604851087eedaa0428843d76d50214421fbb0a810a210f5d85408510a5ae42a0428861f5498c214430e2a4c610a2187d516308510c38a8b18428863b54980214431c2a4c010a218d15261d0110c6ccb20c808863754185404430faa4c620221871526310110c3ea8b18808861c5458c4044317aa4c4202218b1526210110c5ea8b10808862c54588404431baa4c2202218d1526110110c6ea8b08808863454584404431b32c8220221a958a4110110a70eaa0080886a96250040442d838a80202218d15261cc110c68a8b0e608865453587304431baa4c3182218d152618c110c6ea8b0c608863454586304421fba2ca982210f1d1654c1108dee4b2a608846c72595304421f3b6a8982210f1db544c11087cec2a2608843c76151304432ab2862982210f9d664c8110878eab26408843f76d53204421ebb6a9902210fdd854c811087aec2a6408852d721532044296ba0a5902214b9d542c8110a58eaa1640884d473587204431d328a9102215a1c95388110ab2e6294408853a75d0a204429c3aa8510221749cf6188110ae4ea30c40884f07650620442793b66310221d454c3188110ae0ea90c40885d073486204421f3a6ca902210f5d3654811087ee8b2a408843c74595204422fb9aca902214b5c85448110a5ae8292408852e7550920442963aa84902218d1536148110c68a830a408863865d51204431c328a8902216a5c854481108f0eca9a408847a7614920442acb98a4902216a5d05248110a74eba12408863865d0920442d4ba484902214e1d54248110c70caa12408872b7550920442d53aa84902216a1d54248110e50eaa12408872b65509204439432a8490221cad4d4248110e52a6a1240887a27150920443d0b8a8490221e850b6148110f428430a40887a14290520442783b28290221e850941481109e4ed98a408867065cc520443d0a1662902219c1943148110ea2a618a40885e1720c520443d0a1062902219c1962148110f428510a408857075485204433832a4290221741cd2148110f428490a408843f76d50204421ebb6a8102210fdd8540811087aec2a0408861f5498c204430e2a4c61022187d516308110c38a8b18408863754984204431a2a4c2102218dd516108110c68a8b0840885387550b
  | 3 => 0xd165cc910878e8b2e648854d7314b324421f3a6cb192210f5d3658c91087ee8b2c648843c74596324421f3a0cb192210f5d0658c91087ceb324648843c75592324421fbb6a9192210f5db548c91087eec2a4648843d761523244296b90a9192210f9d3654c91087ae9b2a648843f74595324421e3a2ca992214b5c8544c9108bced29a648863754d85324431a2a6c2992213c9c3614c910c6ea830a648863454185324432b298c2992210f9d3650c91087ae9b28648847970d94324421fba2ca192210f1d1650c91087ce8328648843d74194324423b388ca192210f9d6640c910878eab20648843f76d50324421ebb6a8192210fdd8540c91087aec2a0648863754984324431a2a4c2192218dd51610c910c68a8b08648865753584324432a29ac21922199d49610c910c76a9300648863854980324423c3aac0192218ed51600c910c70a8b00648865b53580324432c29ac0192219ad49600c910c70a9306828863665d524144279384c720a214d1d54290510d4ac4a1482884d673982414431daa0c0a0a218d19764505108ecec2a2828863465d09414429a3aa84a0a218d1954250510d4ec4a1282886b36418141442793a8c0a0a219c9d46050510d66a830282886b0541814144278b90c0a0a21acd086050510d6284302828863454984414431c2a4c198a218e15160cc5109e4e1b2662884757694b314423abb0a598a21555cc52cc510a6ceba1662885347550b31443a22966598a21551d532cc5109e4eb3066288672759833144359aa4c198a21ac15260cc5109e2e530662886b3429833144358a14c198a21531c9538c5108bcec29a6288717544c4314438a2a26218a211d9d7640c5109e0e0b2062886366515031442e8b84a618a211ddd9530c510ac8e4a9862884d77654c314438baa2a618a21c5151530c510b88e4a9862885d37054c31442abbb2a618a2195dd9530c510e2ee8a9862887147454c31443a3b92a618a21551c9530c510e88e4a9862885447254c31442abb82a618a21d4dc1530c510caaa6b10628847576948314423abb0a418a21555cc520c510a6ceba10628871553d08314429a3aa8418a21c554d420c510d4ac4a1062884d5768c831442abbac6418a21745c2320c510aaaea1906288744520c831442e8b806418a210f9d664c8510878eab26428843f76d53214421ebb6a990a210fdd854c851087aec2a6428845e73996214422eb9ccb10a214b5c854885109ace732c428855573996214423b3aec910a213c1c16488510c6cca2a442885a5721522144279384c710a211d5db53885108eeeca9c42886546354e21442b2392a710a21555cc5288510a6ceba1442885347550a214426b39cc110a215c9d46088510c3ea9b1a428861c54d8d214430faa0c690a21871506348510c98c7a92428864c63149214431c2a6
  | 4 => 0x5ea8312a68862c54189534421eb96c8a9a210f5c86454d10c5ec9b12a68862c64d895344317ba6c4a9a218b1d36254d1087ce8312a68843d741895344317b20c4a9a218b1906254d10c5ce8312a68862d741895344334b80c4a9a219918b6154d108beeca98a68854c7254c534421f3a4c429a210f5d26214d108dce5b2e868846d72d97434431a2a4c3a1a213c1c161d0d108dee4b2a868846c72595434431baa0c2a1a211e9d76050d10c76a8302868846e721944344236b90ca21a218d1526110d10c68a8b08868863854980434423c3aac021a218e1516010d10a5ae5b26a48852d72193524421f3a4c7a92210f5d263d491087ee8b1ea48843c7458f52442aa39ac3292210f9db545491087cec2a2a48861f54d8d524430e2a6c6a922187d506354910c38a831aa48861f64d8d524430e326c6a922187d906354910c38c831aa48864c63d89524431a326c2a92219518f6154910c70c9b02a48852d72d505244296b90a82922187d526314910c38a9318a48861f5458c524430e2a2c6292211bdd95214910a98e6a90a48861e6498c524430eb24c629221879916314910c3ac8b18a48864c7258c524432bb8ac629221951c56314910c6cc8b08a48863564584524432b31ac2292219558d611491087ce8308a48843d74184524431d322c0292218e5916014910cb4c6b00a488659635805244338b0ac0292210f9d0601491087ae8300a48845e73d97424422eb9ecba12218d15261d09108e8eab0e8488634545874244278382c3a1221479cf65d0910a3ae7b2e848852d72d974244296b90cba12218b5c865d0910c6ae232e848843e7694f424421ebb4a7a12210fdd953d0910878eca9e848852f7254f4244296392a7a122147dcd52d0910a38e6a96848851e7314b424428eb98a5a12218d19661d0910a68eab0e84886346558742442d8382c3a1221179cc65909108bae632c848863754986424423a3aac3212218ed5260909108f0eab04848845f73595424422e39acaa12211ddc565509108f6e0b2a848843e76951424421e3b2a8a12210f9d66550910a5ae532a848843d729954244316b94caa122147dcd6550910a38e6b2a848852f72595424429bb8acaa12214edc16550910c6ae232a848843e7694d424421ebb4a6a12210fdd95350910878eca9a848852f7254d4244296392a6a12214b9c85350910a5ae429a848843e76949424421fbb2a4a12210f1d95250910a3ee6a92848851c73549424421f3b0a4a1221479cc5250910a3ae6292848853675985424431a32cc2a12214d1d56150910c68cab0a84885947358542442d8382c2a12210f9d065109108bce6328848845d73194424421f3acc8212210f5db541091087eec2a0848863454984424423a3aac2212218e15260109108f0eab00848843e74d97324421eba6cb992210fd
  | 5 => 0x865953982328432ca9ac1194219594f614ca10caca630a650865553185328421f3a6ca194210f5d3650ca10c3cc9298650861d6494c328430f322a61942187591530ca10caca7308650865553984328432b29ac2194219554d610ca10cb2a7300650865a53580328432ca9ac0194214b5c8549061087ced2a2830865953d81418432ca98c0a0c210f5db5410610a5ae42a0830865a53583318432ca9ec098c218799253c8610c3ac929e430861e6454f218430eb22a790c218b59252c8610c5ac8a96430865953983218432ca9ac190c21175d763486108baea31a430845e7694d218422e3b2a690c21175da5308610c3cc9298430861d6494c218430f322a610c21875915308610cb4a6b00430865953580218432b29cc3204219594d61902108baeb318810845f7558c408422ebb4a62042117dd95310210c9ca7310810864d5398840843172a2c4204218b5516210210c9ca6b10810864d53588408432b29cc2204219554e6110210c6aa8b08810865653584408432aa9ac220421c654d4010210d52c4a00810865653986308432b29ac3184218799253c8210c3ac929e410861e6454f208430eb22a790421c394d42c8210e1aa6a16410865653986208432b29ac310421965965388210cb2caa9c41087495354a20842acb98a510421c654f4288210e32a6a14410870e535092084386a9a8490421d254f62482108f4ec292410855973149208438ca9e8490421d254e4248210e32a6a12410872a5250920843a4a9a8490421cadd54248210e50eaa1241086ab655092084395b2a8490421cad4d4248210f14a6a1241087295350920843c4a9a8490421c254d4248210f46e2a1241087a071509208422ebacc61042117dd563082108baed298410861e6494c208430eb24a61042117dd95308210c3cc8a98410861d6454c2084316b24a4104218b5915208210caca7308410865553984208432b29ac2104219554d6108210ccaa4b08410855673d53108432ab2ca7884219559553c4210aace7a96210871653d0b108438b29a8588421c954942c4210cb2cb29e21086596554f10842cb39ec3aa2214d5c763d5110a72e1b1ea88851e7318b544428eb98c5aa2214d5c462d5110a72e0316a88851e73d87544428eb9ec3aa221479cf60d5110a3ae7b06a88843f765505444237390c02a2211b5c86015110a6ae3b18a88852e7218c5444296b90c62a2214d5c46315110a72e0318a88853571d88544428f398c42a221475cc6215110a6ae2310a88853970188544428f39ec22a221475cf6115110a5ce5b08a88852d72d84544431bb12c22a2218d589611511087ce9316a68843d7498b534421eb94c929a210fdc96494d1087ce9314a68843d7498a534431b322c329a218e9916094d1087cedaa2a68843e761515344317aa6c4a9a218b1536254d10c
  | 6 => 0x484316aa2c42a4219398e6215210c9ac7310a90862e64588548432731ac42a4219358d6215210c5ce8b10a90865663584548432ab1ac22a421999896115210ccac4b08a90843e7498b538421eba4c5a9c210f9d26294e1087ae9314a70854e7215253842a6b90a929c21555c76494e10ab4e0324a70851e7498a538428eba4c529c2155dc56294e10a3ce8314a70851d7418a53842aab88c529c21569c06294e10a3ce9b0ca70851d74d86538428f3a0c129c21475d06094e10a9ce4304a70854d72182538421f3a0c4a9c210f5d06254e108bcedaa2a70845e7615153842a7390a8a9c21535c85454e10ab0e0b22a70851e74989538428eba4c4a9c21569c26254e10aaee2b12a70851e74189538428eba0c4a9c21555c46254e10ab4e0312a70851f74585538428e3a2c2a9c2153dc96154e10a98e4b0aa70845f7654c5384237390cba1c211b5c865d0e10caca730c870865653586438432ca9ec0a1c219654c6050e10cb4a6b00870865663587528430f324a729421875925394a10c3cc8a9ca50861d6454e5284317394c9294218e9926094a10c72c9304a50845d7694c528430f324a629421875925314a108beeca98a50861e6454c528430eb22a6294211bdd95214a10c5ac8a90a50861e6498c528430eb24c629421879916314a10c3ac8b18a50862d64988528431b322c2294218d5916114a10cacc6b08a50865563584528432cb1cc0294219c5866014a108bce732e850845d73997428422f398cba1421175cc65d0a10a3ce7aa6850851d73d53428428f398a9a1421475cc54d0a10a5ae5b2e850851e73997428428eb9ccba1421479cc65d0a10a3ae632e850852d72197428428f39ea5a1421475cf52d0a10a3ce6296850851d7314b428422f39ccb21421175ce6590a108bce632c850845d73196428432ca9cc1214219654d6090a108bce732a850845d73995428422f398caa1421175cc6550a10a3ce7aa2850851d73d514284297396a8a1421479cc5450a10a3ae62a2850852e7215142842973a4a4a14219594f6150a10caca630a850851e73995428428eb9ccaa14214b5ca6550a10a5ee4b2a850851e73195428428eb98caa14214b9cb5350a10a5ae5a9a850852d75d89428438729ec4a1421c354f6250a10a3ce7a92850851d73d49428421f3b4a4a1421c394e5250a10e1aa7292850852e7694942843173b4a4a1421ca9c25250a10e1ca6a92850870d5354942842973b2a4a14214b1d95250a1087cec292850851e73149428428eb98a4a1421c594f6150a10e4aa5b0a8508716531854284392a90c2a1421179ce6510a108bae7328850845e73194428422eb98ca214219654e6010a10cb2a6b00850843e74d96328421eba6cb194210f9d0658ca1087ae832c650861e6494e328430eb24a71942187991538ca10c3ac8a9c650
  | 7 => 0x89004199d965148020e4aa928a4010667655452008392aa2a290041d154d5148020c5aa9b02401063b65951200831db2aa890041ca5525248020a72eba12401063b65d09200829dbaa84900418ed954248020e54a4a124010673659452008339b2aa290041cc9515148020e62a8a8a40107525354520083a8a9aa290041d8d895148020e6684a8a401073142545200832ab1cc3aa6219698d60d5310ce4c2b06a98851e73d5254c428f39ec8aa6210fdd95415310a3ce9a9ca78843e7498a53c421eba4c529e210f9d06254f1087ae8312a78845f7654c53c421f3a4c429e210f5d26214f108dce5b2e878846d72d9743c432aa9cc3a1e213c5c66090f108dce4328878846d7219443c431b324c3296218d5926194b1087ce9b1aa58843d74d8d52c4237bb2a429621879926314b10c3ac9318a58861e6458c52c430eb22c629621951c56314b10caac7308a58863a6458052c431cb22c0296219698d6014b10cb2c6b00a5886726158052c422f39ecba1621175cf65d0b108bce732e858845d7399742c428f39ea9a1621475cf54d0b10a3ce7b2e858851d73d9742c4296b96cba1621479ce65d0b10a3ae732e858852d7219742c428f398a5a1621475cc52d0b108bce632c858845d7319642c422f39ccaa1621175ce6550b10a3ce7aa2858851d73d5142c431daa0c0a16213c5c46050b10a3ce732a858851d7399542c4296b94caa16214bdc96550b10a5ee4a9a858852c7254d42c4297390a6a16214b5c85350b1087ced292858843e7614942c428f398a4a1621475cc5250b10b28e6b0a85885b07058542c431d328c0a16216c5c46050b10d64c2302858845e7319442c422eb98ca216210f9d265ccb1087ae932e658843e74d9632c421eba6cb196219594c614cb10caaa630a658843e74d9432c421eba6ca196210f9d0650cb1087ae832865886a56250a41c42d83828520e21359ce60907108ecec2a283886a76250941c431d2a2c020e213c9c364cc7108eaed29663884757614b31c42aab98a598e219694d600c710aaeeca9863886577654c31c42aa392a618e219554d620c7108eaed29063885557314831c438aa9e8418e21c554d420c710d4ac4a1063884d5768c831c42abbac6418e21555d4320c710ba2e019063884777654e21c432a31aa710e21555cc52887109ace730443884d47359121c4278382c890e2195d946348710caaea31a43886d27018d21c4368b80c690e219518d5348710ca8c729243884767614921c42aab98a490e219518c5248710d28c7a1243886946350921c43922928490e219a5496008710a3ce7aa4818843e7695140c421ebb6a820621479cf5410310c5ea8b10818862c5458840c4352b1482206214b5d252c83109a8e6b0e418852d7494920c432b31ac3aa4219658e60d5210ce2c3306a90843f765505
  | 8 => 0xe6054420a6ce8102a2105357408151082aab9840a88410f5da541442087eecaa0a21061e5498c510830eaa4c628841879516314420c3aa8b18a21045d7694c510830f324a6288418759253144208beeca98a21061e6454c510830eb22a6288418d9526114420c6aa9308a21065653984510832aa9cc2288411ddd95114420c6cc8a88a21063564544510832b31aa2288419558d51144208bce732e821045d73997410822f39ccb20841175ce65904208bce632a821045d73195410831caa6c0a08419654f6050420ce2a3b028210659531814108338a88c0a0841179ce65104208bae7328821043e74996310821eba4cb188410f9d0654c42087ae832a621062d54d893108316aa0c498841551cd514c420ccec4a8a621043e74994310821eba4ca18841555ce510c420aaeea9886210555754c4310832bb2a621884195595310c420e2ca89886210715544c431082e239262188410f5d664c842087eeab26421043d76953210821fbb2a9908418799253c8420c3ac929e421061e6454f210830eb22a7908418d99251c8420c6ac928e421063664547210831ab22a3908419654e60c8420cb2a6b06421067151583210830f2a6c690841875536348420c3ca831a421061d5418d210822e3b4a690841179d95348420caec728a421065463945210821ebacc8108410fdd5640842087aed2a0421043f76550210822ebacc610841879526308420c3aa9318421045f7558c210830f2a2c6108418755163084208baed298421061e6494c210830eb24a61084117dd95308420c3cc8a98421061d6454c210831b324a2108418d5925108420cacc7288421065563944210831b322a2108418d5915108420cacc6a88421065563544210831d2a4c0108418e5526008420cb4a73004210659539802108338a8cc0108418e9516008420c72a8b00421065a53580210832ca9ac0108419c9456008420c5aa9314801046f7558a4008316aa2c5200418b5526210020c5ca8b10801062d54588400823abacc2200418d9526110020c6aa9308801047775584400831b2a2c2200418d55161100208eaed288801065663944400832ab1ca2200419998a5110020ccac5288801047776544400832b31aa2200419558d5110020cccc4a88801066562544400831cb2a8020041cc545401002087aed2a6401043f76553200831b324a3900418d59251c8020e4a8528e401063664547200831ab22a390041c950951c8020a5eecaa64010725549472008392aa2a390041d154d51c80208daed29440104797694a200829cbae85100414edd54288020e64a8a8c40107315454620083a929aa310041d454d5188020e6684a8c4010731425462008296bae84900418bd974248020c5ecaa124010725429452008392a12a2900411b9db5448020a5aeb2a2401062f659512008317b2aa
  | 9 => 0xeeca88a2905347454451482aa39aa228a41c95095114520a58eaa14829062d6550a414826cb9cc120a41aa50a6090520d5284b04829062f65509414822fb9aca20a41171cd65105208bce6328829045d7319441482963aa8420a41995885110520d52853008290638545804148354a12c020a41aa50a608c520d5284b04629062f65509314831632a8498a410fdd1650c520878e8b28629043e74194314821eba0ca18a412b5d2620c520c5ccaa10629062d6550831482aab98a218a41559d5310c520aa8ea98862906c5624c431483c2a126218a41aa50a600c520d5284b00629067051580314826cb9cc110a41aa50a6088520d5284b04429068f63509214834631a8490a419518f5148520ca8c628a4290725421452148354a16c090a41a398d4208520d1ac6a1042906a94298021482963aa85a02414d1c55490120c5ccaa14809043e7615140482963aa84a02418bd954250120a72e12a0809043f76550404829a38aa8202418b9516210120c5aa8b10809062e655084048352a14c220241a95096110120b56eca1640906ab7650b204826db9ac390241aa50961c8120cacc730ea81065663587540832ab1ac3aa0419c58660d5020a6ce3aa4a81053571d52540829b388c12a0414d5c46095020a6ce3b22a81053571d91540829c382c2aa0414d9c46055020a6ae2302a81043f76550540831aaa4c22a0418d5516115020c6cc9308a810656639845408333314c22a0418d9916115020cacc6b08a810655635845408333312c22a0419c5866015020c5ce5324a41053671d53420829ab8ea9a10414d9c454d0820a6ae22a68410639545824208297396a8a10414d9c75450820a6ae3aa2841043e761514208297390a8a10414d9c45450820a6ae22a2841052e749494208297b96caa10414b9da525082087eecaa0841063a54580420830f2a4c7a88418755263d4420c3ca8b1ea21061d5458f510829b3a6a3288414d5d35194420aace7a8ca21055573d4651082ab39ea928841555cf5494420aace62a4a21055573152510829b3a6a7288414d5d35394420e2ca929ca2107155494e510829abae8528841c594f4294420a6eeaa14a2107165350a510832ab18c7288414d9d06294420a6ae8314a2105567318a51082aab98c528841c9dc94294420aace7304a21055573982510823b3b6a8a8841559cf5454420aaae7aa2a2104767615151082ab398a8a8841555cc5454420a6ce9a9aa21053574d4d510838b2a4a6a8841c55525354420e2ca8a9aa2107155454d510829abae84a8841c594f4254420e2aa7a12a21053775509510838b29a84a8841c554d4254420ae0e0b22a2105647258d510832ab18c6a88414d9d26254420a6ae9312a2105727090951082b8b8484a8841c9dc94254420ae4e0212a2105717010951082ab39cc0a8841555c
  | 10 => 0x43d7419531c8317b2a8498e418b195424c720aa8e6a8a639043e7499431c821eba4ca18e412b5d2620c720c5aa9310639062d5458831c831732a8418e418b595420c720aa8ea9886390657654c431c832ab2a6218e41c5951310c720e2aa898863906c5624c431c83c2a126218e410f5d664c872087eeab26439043d7695321c821fbb2a990e41551cd51c8720d5284b06439061e54d8d21c830eaa6c690e41879506348720c3aa831a439068f6350921c834631a8490e410f5d6640872087eeab20439043d7695021c821fbb2a810e41879526308720c3aa9318439061e5458c21c830eaa2c610e41a398d4208720d1ac6a1043906556394421c82aa39aa210e419558d5108720e4a84a88439063a5498021c831caa4c010e418e9516008720c72a8b0043906a94258021c8338a8ac010e418b95162d0320c5aa9b1281905a87050940c8316aa4c4206418b9516210320c5aa8b1081906365498440c831aaa4c220641a950a6110320c6ca8b0881906355458440c8352a12c220641aa589401032087eecaa0a910656639845488332b14c22a4419598d6115220caac6b08a91066562584548831caa0c0a14413c5c46050a20a6ce232a85105357119542882d8b88c0a1441559cf5194620c6ae2322a31043e76d09518821e3b284a8c411ddd951146208bce7b2c831045d73d96418822f39ccb20c41175ce6590620a6ae22a4831053474546418826cb9cc120c418e151601062087ce9b2c631043d74d96318832ca9cc118c410fdd1654c620878e8b2a63104e970189318821fba2ca18c410f1d1650c620aaae72886310557754c431882aabaa6218c41711c9310c6209b2e7304431065463945218832a31aa290c410f9d8545022087eecaa0811062e545884088316aa2c4204418b59664c8220c5acab26411063965993208831cb2ac99044136dcd61c8220caec7b0aa89063764185544832bb18c2aa2419518c6155120ce0c3b02a89043f76550544829a38aa82a2418e15160d0920a5ae5b2e849053771597424829a38acba12418e19560d09209e2e2302849052f7259542482973aec4a12418b1976250920c72ca30284905b17118142482373b0a8a1241785c46050920b52e1b2a849052d70d954248394b86caa12414b9d66150920c58cb30a84905aa7098542482d4b84c2a12414b1d56150920b1ee6b0a849058c7358542482d5b82c2a12416a1c16150920c58ca30a84905aa7018542482d4b80c2a12418b1976050920d50cbb0284905a971d8142482973acc0a12416a9c26050920d56c130284905a77158142482d238ac0a12414b9d46050920b4ce230284905a57118142482d53b0c0a1241aa9d86050920b54ea302849072a7518142483d1388c0a12416a5c46050920f42e230284905a1711814248347b1a84a8a41a318d42545208e
  | 11 => 0x1022e39aca90881179cc65484408bae632a422045d75d8d211022eba8c690881179da53484408b8ed29a422045e7654d211022e3b2a69088193d8e5248440c98c7292422062f645492110316322a49088193d8d5248440c98c6a92422065763945211032a31ca2908818dd915148440caec6a8a4220654635452110334a96c0908819c54760484408bce7b28422045d73d94211022f39cca10881175ce65084408baeb318422045f7558c211022fbb4a610881175da5308440c3cc9298422061d6494c211022fbb2a610881175d95308440c3cc8a98422061d6454c2110316b24a4108819398e5208440c9ac7290422062e645482110316b22a4108819398d5208440c9ac6a90422063664944211031ab24a2108819598e5108440caac7288422063664544211031ab22a2108819598d5108440caac6a88422065a53980211032ca9cc0108819a54a6008440ce2a3300422065a53580211032ca9ac0108819a9496008440cd2a4b004220672515802110338a8ac0108818b58952d0040c5aa530e802072552947401038aa9aa3a0081c954951d004087aed2a480204797695240103a8a9aa320081d8549519004087ae5b2a802062f65949401021f3b2a4a00818bd895250040c5ecaa92802062e765494010394382a4a00818b5486150040c6ecb28a802072552945401031bb2aa2a0081c554d5150040e4aa4a8a802066b659494010335b2aa4a0081ca9515250040a72eb21280204ba761094010339b2ca2a00819cd955150040ea2a6a8a802076152545401025d3b682a00814d9c46295320a6ae2314a99051e73d8654c828eb9ec32a6414b9cb6195320a5ce430ca9905367198954c829ab8cc4aa64147dcd6155320a38e6b0aa99053b7058554c829bb8ac0aa6414d1c5605532087eecaa0a9906395498242c821f3b0a8a16416a5c35450b20c5ecaaa2859046e7615142c82573b0a8a16414b5d66150b20a5eeab0a859058f7358542c82c639ac2a16416adc16150b20b50e0b0a859062f65d8142c8317b2ac0a164169dc56050b20b48e2b0285905a67118142c82d2b88c0a1641aa5806050b2087eecaa0859063a5498042c8354a12c0216412bdd942d4720c3ca9b1aa39061d54d8d51c830f2a0c6a8e41875506354720d1ec6a12a39068c6350951c830fb1e84a8e418718f4254720c3ec6a12a39061c6350951c821ebb4a828e410fdd95414720c3ca9318a39061d5498c51c830f2a2c628e4187551631472095eeca10a39068e6350851c8346b1a8428e411ddd95114720aa8e6a88a3906556354451c8392a12a228e41179cf65d07208bae7b2e839062e5458b41c8316b2a8520e4117dcd65507208b8e6b2a839062f6550941c8354a16c0a0e418e5506050720c5ca8b10839043e7499631c821eba4cb18e41551cd518c72087ce832a6390
  | 12 => 0xa8881c519153544408eceda92a22055673d4951102aab9ea4a8881d194e5254440e8aa7292a220726749495110392324a4a8881d194d5254440e8aa6a92a220726745495110392322a4a88811d9d85254440aace6292a22055573149511038b29e84a8881c554f4254440e4aa5a12a2205b170d09511038b29a84a8881c554d4254440e4ca4a12a22072552509511029b3a4c6a88815c9c26354440a68e8b1aa2206556318d511029b3a4c4a88814d1d16254440aaee6b12a2205547358951102b8382c4a88814d9d06254440aace6312a2205557318951102b9380c4a88814d9db4254440a68eca12a2207277250951102b938084a88815c5c04254440aace7302a2205557398151102aab9880a8881599c84054440acae4202a22045d7694c511022fbb2a6288819394e6214440c9aa7310a22064e535885110326a9ac4288811b5da5214440c9cc7290a22064d639485110237bb2a4288819398d5214440c9ac6a90a22065653984511032aa9cc2288819994a6114440ccaa5308a22047776544511032b31aa2288819558d5114440cccc4a88a220665625445110338a8ac1a08812e5c26390440c3acaa9c82204bb7058a4110316b12a5208818b5955290440e1ca6a94822070d5354a4110316bb2a5208818b98d5290440c6acb28c822072552946411038b29aa320881c554d5190440e4ca4a8c822072552546411031ab12a3208818b5496090440cb2a7300822066952980411032ca9ac0208819a5496010440ce4a2b00822062d62548411038729aa420881c354d5210440c5ceca90822062d76548411031731aa420881c954a6110440e4aa52888220715535444110392a92a220881ca54a6010440c5aa4b00822072952580411035930ac0208812edd56010440c76eab00822069a53580411034ca9ac020881aa9496010440c72a4b0082206a9525804110314a92c020881ac9456010440d62a2b00822046e729963110236b94cb1888187991538c440c3ac8a9c622062e6454a3110316b22a5188818d592518c440cb2a7304622066952982311032ca9ac1188819a549608c440ce4a2b04622046e721953110236b90ca988812e5c0644c440c5ec8a92622062c64549311031bb22a298881551cd514c4408dce5328622046d72994311021ebaec8188812b5c8640c440972e0320622062f645483110316322a418881555ce510c440aaeea9886220555754c4311032bb2a621888195595310c440e8ca49886220745524c4311022f39ccb90881175ce65c8440972e1326422061e6494f211030eb24a7908818799153c8440c3ac8a9e422062d6494b2110317322a5908818b59152c8440c6cc928e422063564947211031b322a3908818d59151c84408bce732c422045d73996211025cb80c9108818b1915288440c6ec8a8c422045f7359521
  | 13 => 0x60d0b40b52e1a9285a04ae7614942d0354a12c0216818b5894294740c5ec4a12a3a04777654451d022fb9aca90e81171cd65487408bce7b2843a045d73d9421d022fb9ac329481171cd6194a40a68e2b22a52046f7654852902973b4a4a14818b9da5250a40e52a5b0285207295218142902ab39ea328c81179cc62546408bae6312a320477765445190316b12a420c811bdc9654c6408d8e4b2a63204ad72190319025cb80c818c81555ce510c640aaeea9886320555754c4319025c3a2c018c81179ce65886408bae732c432045f73595219022e39aca90c819518e5148640ca8c6a8a432045e73d94219022eb9eca10c818b58952d02408bce730ea4a045d739875250237bb2a429281cad4b6050940e56a430284a04ba75181425031d3a8c0a12818ed486050940d64e230284a06b171181425031732a84212819558f51945408eeeca88a2a045f73588515022e39ac428a814e1c14214540aace7a8a62a046e721943150236b90ca18a810f9d6640c540cacca98862a0654654c4315022fb9acb90a81171cd65c8540970e0b2642a063564147215022f39cca90a81175ce65485408bce632842a045d73194215031ab26a210a819558f5108540caac628842a067351580215033828ac010a818b58b5290140acce3a94a42056571d4a521022fb9ac329081171cd6194840a5ce9b0ca42054f7358652102a639ac3290814b9d06194840a9ce630ca42054d7318652102b5380c329081599c46094840acae2304a42045e73185521022eb98c2a90814b9c66454840e52e1322a42052e74d8552102963a2c2a908153dcd6154840a98e6b0aa4205687058552102973a0c2a9081539cc6154840a9ae630aa42056a7018552102b3388c0a9081595c460548408deeca90a420665529845210332a92c2290819a54960d0840c5aa530e8420729529834210316a92c1a1081ca54960d0840976eab06842063b755834210355292c1a10818e54960d0840d52a4b068420629525834210317b2aa4a10812e5c06150840cd4a4b00842064e6394b5110326b1ca5a88819398d52d4440c9ac6a96a22055673d4651102aab9ea328881599cb5194440acae5a8ca22045f7358a511022e39ac528881599cb5394440acae5a9ca22055673d4a51102aab9ea528881d194e5294440e4ce9294a2207465354a51103933a2a528881c91915294440aace6294a2205557314a511038b29e8528881c954b4294440b62e1a14a2207165350a51103932928528881c95494294440a6ce9b1ca22057270d8e511032ab18c7288814d9d26294440aaee6b14a2205547358a511029b3a0c528881559cc6294440aaae6314a2205727018a5110393b928528881559ce6094440aaae7304a22045e73189511022eb98c4a88814d9c74254440acce5a9aa22056572d4d511038a324a6
  | 14 => 0xe8194a010d39740ca50086b938865280435c5c43294021ea26218ca010d3a74c86500869cba6432804356dcd2194021ab0e690ca010c5e73191500862eb98c8a8043551cd2154021e4a8490aa010c7a76d5150086ad39ea8a8043565cf54540218f4ec2a2a010d5a7315150086acb98a8a80431e9db5354021a74e9a9aa010d3974d4d500878d2a4a6a8043c65525354021ea0e329aa010f1a5454d500878caa2a6a8043d41c553540218f4ec29aa010d3a7414d500869cba0a6a80434e5d74254021e34a7a12a010f1953d09500869dbaa84a8043c694d4254021e32a6a12a010d7175cc550087992a662a8043cc5533154021ea4a798aa010f5153cc550087992a062a8043cc5503154021ea4a618aa010f51530c55008794aa642a8043d254f2154021e64a910aa010f315488550087a929c42a8043d454e2154021ad6ea90aa010f295448550087a4a9a42a80435cdd52154021e64a890aa010f315448550086e839a42a8043d494d2154021ea2a690aa010fa14248550086b838ac8a8043569cc6454021ab2e6322a010d6a7219150086b9388c8a80435c9c76354021a76e8b1aa010d387458d50086b4392c6a80435c1c56354021ad4e5a1aa010d6972d0d50086b938e86a80435c5c74354021ae6e2a1aa010d707150d500869d3a4c4a80434e5d26254021ae4e3212a010d71719095008795b9284a8043ca9894254021ae4e2212a010d71711095008794a1664a80434e9d23254021a72e9192a010d72718c950086b8b8c64a80435cdc53254021ae0e2992a010c7a760c9500869d3a064a80434e5d03254021e5284192a010d72710c950086b8b8864a80435a9c84154021ad2e420aa010d7172cc55008799a1662a8043cc50b3154021ea66598aa010f5132cc550086b539062a80435a5c83154021ea26218aa010f52730c550087a931862a8043d458c3154021ec4e418aa010d71720c550087b0b9062a8043ccd083154021e628418aa010f52320c550087a819062a80434e9d32154021a72e990aa010f2942c8550086b939c42a80435c1ce2154021e668510aa010f314288550086adb9a42a8043561cd2154021e528490aa010f537348550086b939a42a80435c1cd2154021ea0e690aa010d507348550087b1b9242a8043ccd092154021ec48490aa010f314248550087b0a1242a8043c85092154021a74e810aa010d397408550086ad39842a8043565cc215402187aed2a0a010c3f76550500870f2a4c628043875526314021c3ca8b18a010e1d5458c500862ebb4a628043879925314021c3ac9298a010c5f7654c500870f322a628043875915314021c74a9300a010e3954980500872d29cc0280439654e60140218f6eca80a010e3a64540500871cb22a0280439698d5014021cb2c6a80a010c6f7654852d0394a94c1a1681ca549
  | 15 => 0x15535083108752b128418843355da320c421aaeeb1906210d55750c83108762b106418843e1508320c42187aed2a64210c3f76553210870f324a7908438759253c8421c3cc8a9e4210e1d6454f2108786a9a8590843c355153c84218daed2944210d7170d4e210863bbb2a7108439598d5388421e2ca8a9c4210f155454e210872bbb2a710843951d953884218eaed2944210d3575d0a210878aa9e85108434ddd54288421e2aa6a144210e1e54d8d210870eaa6c690843879506348421c3aa831a4210c5e7694d210862e3b4a690843179d95348421c5ecba124210e2f65509210874631a8490843c354d4248421c9ee7b2a4210e4c73d952108717b2ca8908438bd955448421c9ecbb1a4210e4f6518d2108727b2ca69084393d955348421e1aa8a9a4210e5773d95210872a39eca908438dd965448421c6ecaaa24210e5765d8d210863abacc690843359ce6348421caeca31a4210e557518d210874b2a0c690843a555063484218eceda9a4210e5463d4d21086b8b86a690843351da5348421aaaeb29a4210e576594d210863a3b2a6908439518d53484219a8eca9a4210e576554d210878b2a2a690843c55515348421caeeca9a4210d567654d21086aa3b2a690843951d953484218a8eca9a4210e5553d8921087a2a9ec4908439518e5248421b4ae92924210ec463949210869abae84908438dd974248421d28c7a124210f1553d0921086d2ba48490843b118e4248421e8aa72124210d3775509210871bb2a8490843a518d4248421e2aa6a124210ec46350921087a2a9a849084369dd54248421e4eeaa124210ea7655092108793b2a8490843e1d8d4248421d4cc6a124210ea46350921087c231a8490843a118d4248421e4ea6a124210f86535092108792a9a8490843e154d4248421e0aa6a124210e1e5498f500870eaa4c7a80438795163d4021c3aa8b1ea010e1e6494f500870eb24a7a80438799153d4021c3ac8a9ea010d3a74d42500869cba6a128043569cf5094021ab2e7a84a010c3f7458e500861e3a2c728043569cf5494021ab2e7aa4a010d5a7315250086acb98a9280434e9d35394021a72e9a9ca010f1a5494e500878caa4a728043c69515394021e32a8a9ca010f507154e500869d3a0a7280434e5d05394021a72eba14a010f1a53d0a500878ca9e85280434edd54294021e34a6a14a010f195350a50086b8bae6328043d454f3194021ea2a618ca010f515388650086b5baa43280435cdd52194021ba0e690ca010f515348650087d0a124328043569cc6494021ab2e6324a010d6a7219250086b9388c9280435c9c76394021a76e8b1ca010d387458e500869d3a0c5280434e5d06294021ab4e6314a010d597318a5008795b9285280434e9d23294021a72e9194a010d73714ca50086b838a65280431e5d83294021a74
  | 16 => 0x863abacc3a18439554e61d0c21c6ca8b0e8610e5553587430863d384cb218431e5c26590c218f4e032c8610c7970196430863d384caa18431e5c26550c218f4e032a8610c7970195430871aaa6c2a18439554f6150c218eaea30a8610e5553185430863d384ca218431e5c26510c218dce43288610c7a70194430863cb80ca21843479cf54d0821a3ae7aa68410d3a70d53420869cb86a9a1043479cc54d0821a3ae62a68410d3a70153420869cb80a9a10430f5db53d0821a74e1a9e8410d3970d4f420870eb2ca7a10438759553d0821e28e2a9e8410c3d7614f420869d380a7a10434e5c053d0821caaa730c8410e3554586420872aa9ac321043479cf5450821a3ae7aa28410d3a70d51420869cb86a8a10430f9d85450821a3ce62a28410d1d73151420869d380a8a10434e5c0545082187ceda9a8410d3a70d4d420869cb86a6a1043475d65350821c3ecb29a8410e1f6554d4208786392a6a1043c51c5535082187cec29a8410d2e7214d420869b388a6a10434e9c05350821a72e029a8410f0e53d894208786a9ec4a10430fdd95410821c3cc92988410e1e6454c420872aa9cc2210438d9516110821caaa6b088410e2d6550b3208786a9a85990430f9d3658c82187ae9b2c6410c3d75992320861fbaac9190430fdda548c82187aed2a46410c3f76552320861ebb2a91904387992538c821c3ac929c6410e1e6454e320870eb22a7190439554e618c8218eeeab0c6410e5553586320871b2a6c2990438d553614c821caca7b0a6410e5553d85320861fbb4a8190430f5da540c82187eecaa06410c3d765503208716b2a84190438d952610c821c6aa93086410e3654584320871aaa2c2190439594d610c821caaa6b086410ea5425843208716aa2c520843179ce65104218bae73288210c5e73194410862eb98ca208439354e6210421c5ca8b108210e4d53588410872b39acb988438d59654cc421c6acaaa66210d7170d4f310872ab2ca798843c595153cc421e2aa8a9e6210e555358b310869abae85988438d59742cc421e2aa7a166210d377550b310871ab2a8598843c554d42cc421aaaeb9966210e5565ccb31087c2a16659884355dd532cc421caaca9966210e4d5358a310861f3a4ca188430f5d2650c42187ce83286210c3d741943108716aa4c4188438b551620c421c9ca6b106210e57654c4310872ab2a6218843c5951310c421e2aa89886210e3565950310871ab2aa818843555d6630c421caacb3186210d7170d4c31086aabaca61884395596530c4218eeeca986210e566354c310872ab2aa618843c5951530c421e2aa8a986210d577654c310872bbb2a61884355dc1530c4218eeeab106210e5553588310876331ac4188431d5da520c421a6aeba106210e3565d08310878aa9e84188434ddd5420c421c6acaa106210f
  | 17 => 0x8a43b1d8c624c521e28a7a126290f145350931487523128498a43551d5324c521d88c49926290f85424c9314872a29ec098a438799353c8521c3ac9a9e4290e1e6414f214870eb20a790a439558c53c8521caaec29e4290f166414f214878ab20a790a43c514f42c8521e28a6a164290e5453583214878629a8510a43179ce64d41218bae7326a090c5e76d4d504870fb26a6a82438719353541218bcec29aa090e1f6414d504870e320a6a82431edd95014121a70e8a80a090e5563987540872d31cc1aa0439658e60d5021cb4c6b06a810e5963583540873930ac1aa043479cf5495021a3ae7aa4a810d3a70d52540869cb86a92a0434b9cb6395021a6ce3b1ca810d1e73182540868eb98c12a0434b9c86095021a6ce2304a810d1e73d91540868eb9ec8aa0434e9c36455021a72e1b22a810c5e73181540862eb98c0aa0434d1c56355021a68e2b02a810d1e73181540868eb98c0aa0434b9c86055021a6ce2302a810c3f76550540870eaa4c62a043875516315021c72a9300a810e3954580540870f324c62a043879916315021c9ac7310a810e5563984540871d324c02a0439698e6015021cb2c7300a810e3a64580540872d31ac02a0439658d6015021cd4c4b00a810e7261580540871d2a4c1a98438e55260d4c21c74a8b06a610e3954583530871d324c1a98438e59260d4c21c74c8b06a610e3964583530873930ac1a9843479d35394c21a3ae9a9ca610d5a70d4e53086acb86a7298430fdd16094c21878e8b04a610d5a70d5253086acb86a929843569c05494c21ab2e02a4a610d1e7498a530868eba4c529843479d06294c21a3ae8314a610d5a7018a53086acb80c529843559c66094c21a3ee8b04a610d1c74582530868f3a6c6a9843475d36354c21ab4e1b1aa610d5970d8d530862f3b6a8a9843569c35454c21ab2e1aa2a610c5e7615153086ad380a8a9843565c05454c21e2ca830aa610f155418553086a7394c8a9843559c66454c21aa8e2b22a610d1e74989530868eba4c4a9843479d06254c21a3ae8312a610d5a7018953086acb80c4a9843959886154c21ca8c430aa610d1e74085530868eba042a9843951876054c21aace3302a610d1f74581530868e3a2c0a9843531c96054c21aa8e2b02a610c3d76950530861fbb2a829843879526314c21c3aa9318a610c5f7654c530870f322a629843875915314c21c74a9300a610e3954980530872ca9cc0298438e9516014c21c72a8b00a610e5953580530861f3a4c4298430f5d26214c21c5ac9310a610e3664984530871ab24c2298438e9926014c21c72c9300a610e7261980530871d322c0298438e5916014c21cd4c4b00a610e7261580530863d384cba18431e5c265d0c218f4e032e8610c79701974308636bacc5a18439354e62d0c21c5ca8b168610e4d5358b430
  | 18 => 0x14e21878e8b00a710c7a70d96438863cb86cb21c431e9c06510e218f2e03288710c3e76151418861fbb2a820c43715cb534c6218ecec29a6310cd67614d31886ab3b0a698c43959d8534c621e8ae429a6310e54531893188678b80c498c43c514f424c621e28a6a126310ea46250931887c2a166498c439514f604c621d8ac49886310e2d659932188716b2ac990c4335dcd65c8621aa8e6b2e4310e3565993218871ab2ac990c439558e53c8621caec629e4310e1e63d0a508870eb1e85284438798d4294221c3ac6a14a110d2d721915088717390c8a84438b5c86454221c6ce2322a110e3571191508861f3b684a84430f1d942542218f6eca80a110c5e73983544862eb9cc1aa2439398d6295121cacc6b0ca890e5463d85544872db1ec0aa2439618f6055121c76c8302a890e5b63181544872c318c0aa2439cd846055121ce2e2302a890c3f76550544869c382a82a24356dc154d4d21ab0e0aa6a690d1e74d87534868eba6c3a9a43479d360d4d21a3ae9b06a690e5b6098353486aab88c1a9a4317dd95314d2187ee8b00a690c3c74580534862ebb4a829a4317dd95414d21ab6e0aa0a690d587055053486aab8ec829a43535c86414d21aaae2320a690d5a7019053486acb80c829a43479d36114d21a3ae9b08a690d5a70d8453486acb86c229a43555c76014d21aaae3300a690d1f74580534868e3a2c029a43479d06014d21a3ae8300a690d4d7218053486aab88c029a43965806014d218dae5b2e8690c7a70d96434863cb86cb21a439514e6190d21ca8a6b0c8690c7b70595434863c382caa1a431e9c06510d218f2e03288690e4c5398843486363aac421a439314d6210d21ca8a73088690e5453584434872a29cc3a12439514d61d0921a3ce7b2e8490d1d73d974248696b96cba124347dcd65d0921a38e6b2e8490d3b70597424869c382cba1243c514e61d0921e28a6b0e8490e5453d85424872a298c2a1243479cf6550921a3ae7b2a8490d1f73595424868e39acaa12434bdc96550921a5ee4a9a8490d1e7514d4248786b90a6a12434b9d76250921c58cbb128490f0f53d89424878629ec4a1243699c76250921e28a7b0a8490f1453185424870f326a6212439514e61cc921ca8a6b0e6490e1e64d4e324870eb26a71924387990538c921c3ac829c6490f0c5350a324871632a849924395d4c614c921ca8a630a6490ea542185324872629cc5a0a439314d62d0521a70e0aa48290c5d73d95414862fb9acaa0a430f9d8545052187eecaa08290d3870550414872629cc598a4395dce658c521caccba9c6290e545398a314871b32e8518a43c514f428c521c6ccaa146290f145350a314872b32c6518a43e150a328c521ca8a6b046290e4f5318931486ab3aec698a431d9d8534c521aacec29a6290e567614d3148678b80c49
  | 19 => 0x4a126218e9776509310c74a3b28498863a5d95424c431e2ecaa126218f8772509310c7c3b128498863a5189424c431f08c4a126218e8462509310c7c32928498863c5549424c431f0aa4a126218f0552509310c6ab3a88498863555d4424c431b2ce82126218cd672d81310c72aa96c098863a5d0b604c431d2a85b026218d5575981310c6abbaac09886365dd1604c431b28e8b026218dc772581310c6e2392c09886335dd931d40319aeec98ca018dd3704c6500c61f3a4c5280630f5d26294031c5cc4a14a018e2d6250a500c656b90c8a806335dd93154031d2ec898aa018e94644c5500c6e9b8262a80630f5cb64540318dce4322a018c6d72191500c696b90c8a80638b9c8645403187ae4322a018e2d72191500c616b90c8a80638d9c46454031c6ae2322a018e3970191500c61f3a0c4a80630f5d0625403187ceda12a018c3c76d09500c61f3b284a80630f1d942540319aeec988a018e96644c4500c74ab226228063b19893114031d8ac4988a018c7b76540500c71cb22a0280639a5895014031ea262a80a018d3571d8e54c8697390c72a643479cc6295321a3ae6314a990d3a7018a54c869cb80c52a643479cf6195321a3ae7b0ca990d1e7318254c868eb98c12a6434b9c86095321a6ae2304a990e396018254c862f398c0aa643175cc6055321a6ee2b1aa990d3b7058d54c869c382c6aa643479ce6255321a3ae7312a990d3a7098954c869cb84c4aa64347dcd6155321a38e6b0aa990d3b7058554c869c382c2aa64347dcd6055321a38e6b02a990d377158154c868f398c0aa643475cc6055321a5ce4302a990d357118154c871cb00c0aa6430fdd95415321cccc4b08a990e2d6498b53c861fba2c129e430f1d16094f2187aed2a0a790c3f7655053c862fbb2a629e438e9526014f21c72a9300a790e3a5458053c871caa2c029e439654d6014f21c6ca930e8790c7b7059543c863c382caa1e438d5506150f21c5ca8b108790c3d76d4f42c871aaa4c3216430f9d85450b2187ceda9a8590c3f7655042c871b2a4c2216430f5da548cb2187eecaa46590e2e5458b41c8716aa6c4a0e438b553624c721c5aa83126390f16544c431c878aaa26218e438d596540c721c6acaaa06390c7576d4c31c866abb6a618e43c5953530c721e2aa9a986390dc672d4c31c86aabb6a618e43955db530c721e2ce9a986390f1574d4c31c87a3396a618e43555c3530c721b8ce42986390dd17014c31c872ba9ac418e43c5d4f420c721e2ea6a106390ea56250831c87c2a146418e430fdd16394321878e8b1ca190e57630c550c861ebb4a8286430fdd95414321c3ca9318a190e1d5498c50c870f2a2c6286438755163143218f6eca80a190e596354050c862f39cc1aa443175ce60d522187eecaa0a910e6562984548862fbb2a629c430fdd16
  | 20 => 0xc72551424c6973a0a4a12635a5c05250931a5ae532a8498d2f72595424c69db82caa12634e1c16550931a5cebb128498d2e76d49424c6963b6a4a12634b5c35250931a74e02928498d3970149424c6d4b80a4a12634b9d85250931c5cec2928498f2a70149424c696b80a4a1263ca5c05250931a52e02928498c7a70194424c63cb80ca21263351cd6110931c9ac42946298d597014a314c7862928518a631b9ca64d41318dae5326a098c3e7498b504c61eba4c5a82631edd9501413187ce9310a098c3d74988504c71731284282638b58942141318dce4302a818c6d72181540c61fbb2a82a0638b5516215031c72a8b00a818e2e64588540c7173a2c42a0639958a6115031cd4c5300a818e6962980540c71d322c02a0639a9896015031cd2c4b00a818e7261580540c717394c9290630f9d0605483187ae8302a418c6f76548520c716b22a4290639a5496014831a74e02a68418d3970153420c66ab9cc3a10634b5cb65d0831a5ae432e8418d3a70197420c69cb80cba1063655ce61d08318f6e0b2a8418c7870595420c63d380caa10631e5c06550831a5ce5aa28418d2e72151420c69d380a8a10634e5c05450831a5ce92928418e3554185420c66ab98c2a10634b5ca6550831a5ee4b2a8418d3b70595420c69c382caa10634e9c06550831a72e032a8418d2d75d89420c6973b4a4a10638b9da5250831a5ae12928418d2e76549420c6963b2a4a10634bdc15250831e4aa5b0a8418e3565185420c6cab98c2a1063c95486150831c3aa931c8218c757694e310c733312a518863c9549428c4319e2e03126218e6462549310c71bb2e84988638dd95424c431d48c4a126218f2552509310c72abaeca98863359cb654c4319aae1b2a6218e5676d95310c6aab96ca98863555d6644c431b8ce53226218dc572991310c6abbaac898863359db544c4319acec2a26218f1554151310c6e3390a898863715c8544c431ba4e02a26218dd170151310c6aabacc498863659d2624c431b2ae93126218d5775589310c6cb3a0c498863655d0624c431ba4e03126218dd170189310c72aba8c498863a59d0624c431d2ae83126218ed270189310c66ab80c498863b45c0624c4319a2e03126218cd676d49310c66a3b4a498863659d2524c431b2ae92926218ec462949310c66a3b2a498863b1189524c431aaceca926218d5476549310c72a3b2a498863d1d89524c431ca8c4a926218f4462549310c722312a498863359d8524c431b2ce82926218d9574149310c6e9380a498863745c0524c4319aceda126218cd576d09310c74b3b68498863a55db424c431d2ecba126218f1765d09310c74a3168498863c554b424c431aaceb2126218d5575909310c6caba48498863b118a424c431e8aa52126218cd776509310c66a3b28498863b1189424c431e8aa
  | 21 => 0xb4ab1ac228285a95896114142c6ea4b08a0a16a7525845050b58382c2282858d5865114142a72e0288a0a143f765405050a9a38aa0282852edd95014142b60e2a80a0a153b765405050b1dbb2a028285cadc95014142e52c4a80a0a1733715405050a9c38aa028285cc1c55014142a60e2a80a0a1732615405050b98b0aa0282850f5da54908428daed2a4842145e739825110a2eb9cc1288851ddd95114442caac6a88a221671515805110a3dbb2a0280859c5855014042a9ce5a9ca7a0c5f7654c53d06a739ea529683179cc6054b418bae6302a5a0c6f7654852d0792a94c3a1683c954961d0b41a5ae529a85a0e2e6250a50d0716b1285286831edd95014341ab4e1a9ca720c7a70189539063cb80c4a9c8317dd95314e41a70e0b22a520c6f765485290697b82a4a1483c954b6150a41e4aa430a8520cb5711814290716b12a5a0c83569cf5094241c3ee8b1ca120e1c7458e509070f31e85284838758f4294241c3cc6a14a120e1d6350a50907173128528483179cc62542418bae6312a120c7b76540509072da9ac129a8317dd95314d418f4e131ea4a0c797098f525062f39cc1a9283175ce60d49418deeca90a4a0d2d70d494250793a96c2a1283c9d486150941c5ac5a9482a0e5963d42505063dbb2a0282838b98942141418f4e0312a620c7970189531062fbb2a6298839354d6214c41cb2a6b00a620c7a7018d521063cb80c6a9083179cc60548418bae6302a420c6f765485210726b1aa4290839a5496014841e4aa530e8420f25525874210697b92a6a10838b58952d044187aed2a48220c7576952411061eb96caa08830f9d95250441c5ec4a928220e2e6250a5010716b128528083179cc62540418bae6312a020d3870509501063dbb2a0280839658d5014041cd2c4a80a020e5563987548c72cb1cc1aa463965ce60d5231ce4c2b06a918d3a70d52548c69d386c8aa4630fdd95415231caac7308a918c3e74d81528c61eba6c0a94631bdd95214a318f4e132e8518c7970997428c69d386a9a14634e5c354d0a31c3ca8b1e8518d2d72d97428c69d384cba14634e5c265d0a31a5ae432e8518e1f6558f428c69d386a8a14634e5c35450a31a5ae532a8518d3a70995428c69cb84caa14634bdc96550a31c3ca8b188318e656294b318c69d3a6a1284630f9d2629423187ae9314a118e2e6250a508c716b1285284630f9d0625423187ae8312a118c7b76540508c717aa2c52a2638b9d16295131cccc4b0ca898c3f76550544c696b94c82a2630fdd160d4931878e8b06a498e2d64d4a524c637bb2a4292638b9ca6414931c74c9300a498e3964980524c71d322c0292638e5916014931a5ae5b2e8498d2d72197424c69d380a5a12634e5c052d09318f4e032c8498c7970196424c6b4b80a521263351cd6190931a5ce52a28498d2
  | 22 => 0x2f001803c00200100000000340010060014004008003804800000e003000001000400100180da008001800001a002004803400000000b804004c00a000001001001400180000180000000000002000008801800200300200000000080148000000004006000c000000001002c00000500c0010018004000802c002013000000400000b00400040160010030108002000000002c000031004001400401e0130018028000000801c07a00200680000540000110004006000001800c0000000020004000000004000c004000012800401400a00a000c000002003000000201101d003002a00e001002000801400200240000040010004000001009801c004009010003000400c00080900020110048044000005000000400000f0028010014005000801000a009001000401200c0018000006001002800000200700e8000000048000800800600b000007c0000020108020008005002000803c0010000018000003004801c00c00000b80f00200040000004000000009000401e000003006c00400e004800003e0000020084002001000801c07400200000040240020040044002024002802404a001aace7a8ca3a145e7398251d0a2eb9cc128e851ddd951147428bce7b0aa1a145d73d8550d0a3dbb2a028685a398d62d4742d1ac6b16a3a159673d4651d0a4f39cc128e85275ce6094742b2ce7a8aa3a143f7654451d0a5bbb2a228e85279cf615434293ae7b0aa1a16966398450d0b52b14c228685a598d6114342d2ac6b08a1a16a56258450d0b1ab0ca2286854e5c0511434287eeca80a1a14bb7654050d0a9dbb2a0286858edd95014342e52c4a80a1a17326154050d0b98b0aa028685179ce60946428bae7304a321477765445190b2ab1aa228c859c54560146428f6eca80a121671615405090a3bbb2a228a85551cd5114542ae0e0a88a2a145f735875050a2e39ac3a82851edd95014142ae0e2a80a0a1656639845050b2b31ac2282859558d6114142c6ee8b08a0a1634745845050ac739ec3a9285635cf61d4942d4ec330ea4a15a6711835250ad2b88c1a9285279ce609454293ae7304a2a168f63d895150b4631ec4a8a85a3d8f5254542d18c7a92a2a169463d455150b4db1ec0a8a85a618f6054542d56c5b02a2a16ab72d815150b55a96c0a8a85a6d8c6054542d30c6302a2a16ab621815150b54b90c0a8a85aad486054542d66a2302a2a163a511815150a1fbb2a228a854e1c1511454296eeca88a2a1594735445150ad8382a228a856a5c352d414293ee6b0ea0a149c735875050b4bb1ec2a8285a9d8b6154142d4ea5b0aa0a1697631855050b4a318c2a8285a9d886154142d4ea430aa0a16b061d415050b1a30ca0a82854e5c35214142b52e1a90a0a1696639845050b52b14c2282858dd4a6114142d4ea5308a0a1696635845050
  | 23 => 0x400000e000801c0040110080038004007000800400803301600040880000078000000001005800001c0010078068002003015800000600700000140000020038000000000000000801000b00000140400050100078000001003802c00002d00000000080020008000004000000000400a0030000000000011000800400000600180140420060000010004004000801400000800380480100040000028016006000001000200c000800005c001002002c0000020008000014017000000000c000005800c03800f001804c006000014801c002004002800408c0000028010002001000000000c00000000940000050008004002004003807400c00900580100080000020024002002007005c030000002000000600400280240000040068000006000008803000005600580080000000020000004003001003001400b01a004c000000011000403a0100070004006006000003002c00b000806000800902b8008040028003002000400100a8008000002000000000003200b001c00600a001002c01001a002002c0000030028018054007000802401400200680080000090010114016016000000000200a006800801e004000800c01200003d801401400a000003800003c01400000000060030028000000000800401000000e808400800a0280000000003001800000200100d002c01a002005801007a00000580000000110000000012001000801c0060000030014000002000000405e0000000004010000003800000200100480000940030000000006002007801c01c000000000000000700200000000020018020000005004000000200c0088000006008000000800000a018800c066003000800000e012015801400401800180040be00001c0010000000015000800e000002800c00000200300000060000020024000018001000000002b000800000202c00200180060030028000000008002003c010008001800c01e000004801000000700e8020014021000001000000a00000100660000038018038004000001c00001b002800c01a0060130044000009008803401400a0010000000000008800800e0050018018100001006801401600100100b0008003000800000800b000000400000100f800002a00a001003000000000000000180260008008058005001801001e018000805c0000010008078012003004806401a00000a000001000200d802000a02d00000100020130000000006000003000c00000600e8004008014006000801601d0018000002005000002c040003000800000a005002000000400d0168058016002000802c00c0030010038032002000001001a01c009801402000300b000c00e00200a808000002f0190030000000000000401c000000000000a00600000c4002001007000001c00e0000000004000001802c00e
  | 24 => 0xc626a7a975cfbca477d800313fd96a7bc000000173000000000019b687ce7c0b213ec00000028617e00001e241808382ea51828ac6a495a46c80009ba640f4139e4000e68800163800000031beec12989a4000000107c00009e0ded4cc0002040b15688000027167c3ee10300021100000004872208b2071954c7a0085a8ce2d38006000016803800400000880140580040018034000060003003801000200280b000e0070008000004010001004000000700300040120000000000014001012800400000200580440000000110048000001000802c000003000802c000004004802806603f0038000010012006800400800f012001807c00000480240060000068000008009002000c010000008000000801200200200120020018000002000004000000200000100d40140030068000002008005005000400a000000003c009000000006e00c000005c04400c005004803200d005807000e001002003000e00f00600000000020008084002000000005c00201e0000024006003000800000000c005800c0040000008010000010002812000002d00a800c0040010090008002052004011000c00a000000c02a001002803400a000005815800000300c001400201200100000040030048000002000005802000000900100080000010030118006005000801c00a001000800401800000400000180020048004000015000002402c008000800400a00a0000008002004000000400c00000d000000e02800580580100020030000002001000009401e0080020038000001000009c00000e00500000020110038014006001000002001000300a8004002000002002c00000b0020000036003000002c000000002003c028001002000801000a000001401000c002000002a03c00e800808801100100600020070050050006002001005c00002b0058070004001000000400201a00a800400e00000200280000030000090000001013800801603500000100000010000014000005004800c004000002804400600100000e400000f000800000a031004001800a0000050000000036000001001c052012801407c00100000000000040000010000000000800000a012000003c002001001803c0120050070014000004000000000003f032800c006002001002402800000c800800600300e006c01a000000800c00001e00100a4000007000800001e016001805800000500200100060000010050008001003001802200200a804801e0000010000000000008000c0140120030090000000001004803a007007800005e001004004401200501f800800c027000800c01e000009800400000d000000800000f007000000000100200080140000088018000000003802002201300b001c04e0030060000000000000000c012000002000000800a0010000010002000
  | 25 => 0x80001d3192269635f641519e27b053932559c8ca5b0eaa16383cb5f0b5555f0c3e3b5187e2c6cd26131e915340001f09ea000034404d14e979eb4e10c9cc0dd208f5fb26003c6046a238ff178657c498b3753c6c45276b19d68003d7448908cce7bd05c388c3302f0557a3d4000750303b9901ded77611abf4dd44552352af5c949b84018001beeb703698d94cba79d5ab973e0f47324791c340cb88d51d18742c484b00037598162941d600015a223f43a80a400000054bf1943125a8751084574c10063180010a1ddd7460001392638625206414db915802835ae437500020341e67611b02e80404dc637640153c01d540dabd444e5f592fa4b40007f9b040000c5a68b30900007e02ccce41278da2ca000000005c00ba69b2a0e0007cf17e16ac0000000001ccda3c000179b1c5a7abd50000000000e5c0000000e001af000327400000000000018640000658001a6e2453b9b9440000006592388cc46f4cf89799226acf000253c3ae2a631589786dc56480031f1a508b2674000176a7ad11a74280000000000f80dba81e00012d40e832e000364972e8130001b2d87a8240000001593204c7680000002de0002b4a3a800050da3c4c682588000000000a833da0f0c0007ea0000159c0ceb35ac195282421371226253fe24ab6db820000972000128c00057e4d3b6d405e3045df398d0fabbc56daf200000000002554c06d7030f8d4098ae47000114d12d0002fdd15d182d5fefaa5b40007f469f80014ce4fc26001d4c16286294c8d4b40000359e63d536df63d2b3a400000010d0001346b454a90000000d7300006b95c2d394ac12688907a96138f9dd7437423e00000db0bc02403b00004d215809bbc24806230a870172886000000104671b53201120d266e4860001ac4d021a08854000e6a37b78e4060bb410e00995c45ca000000041217680027842620e42b480016e20003f7924512900000036910ca8328000fdc5a38fc34550906d296c98109b4ca467a5c013ad98ae440001e426282d2578ba3925ca8d4b62d1a0006bb8000d21c7aa5d4c8800194400066a3738120b43e0b8444fee83384114000000000002bf8436eb907b1e52000b47ded00000009b5586831086cbb91428e51cf65370000c28346e1f10198429248aa0002060896987000000190400021d000000052ac36b0a47829c708eac8cbd220c50b94f91fa05119c06b479210663800facaec77587b43d8fa05d940a8a186800000008f200078900000002cd00000ea9b147c05844a9e45308ea16a9246d57daafee5c2ec0000000000f98000b4c2d30000d19a080000000d5977a00008dcdd644369280000006a05922348d7bcbc6f0af6af2a06480000000005f1100c647c7887accaba546f8b5915e05995581505704fd8bce2c220a01e1c936b475c36b4ef94a0000001
  | 26 => 0x1d09a4d0b483fd2c80000000007468001b988ecd8f2680000dac5021d801ba72e2908448000b9e000357a39a2713b888886a226f6fd959080497f58300000000003e01bbccda000000306c67200070ca26f57e6292b398ffcd807f562025c00068e2fe5b0527405c13700000008492c6b948aac0005c605e0a5c8cb83c695000000039b0000b8e2582f400010841b900022cdba697100003180cc0005640630000010649b41193001f08a8689abed856e4017d4841973244000e96e92420c0014cae7e5c1968ceb5aa10003074000000000000148263a8000000000cd925c0d2c00000035774e0fe6666000123c4d4c25661356e160c7953a8a910b80002bc2f6c74821580000001d29d351a0000000000294983322800018b800016a000000379c04f1a148a8b851c200031e90dc000c3c000057a2480002ca204559ad663bb33b0da800007c000096423267c8ab8000000052a5ae000a7b3dd81f57ab1de00000013d2611b1f08e8e169121ad2eb86742c654522248e27a240b988f39e04f0000cc816edb200000003a08156e82b5fbc63292992891d48ad73c80001d14000000399a0003d2d101271c1a7e369398080006a62b335d95ad00025d8110e76c20283800109d055800235a0bc79467e80000008ea0002df00000000001394148d4c4ff04781fb0000002888dda1d30002cb02e60003cb0001982cc65b09e040001f330e06c459241a626000011ab752c235380000000000000000a622ee0b9c35288f1f52cf8a26e0a2358b41c97e7759d935c00098138d0001d60a825c415ecfa410500011d164ade4331503d5ec3a81770001aa5eade158264fe0a500001d219c86d23963879496a510fa2b00a985304a6b7a11d057134d292847200d45071b9b9edf10002590b78e6a800091c95a3a30000000000861742a575a3a62f697956eb5a0a33a007a00000002ce1df1cdce938001630c02b4318480001132d362f0000a56e21282a36dbc46e6bbea7e8115b9c0bf38317fc45c45b10ec03c7cc2919a7cd4aada16ba9e9bf8aa35a47a9d15c0006cf4205b3b2c71a2815c6ac27a18d057178c592361b190ef102d3b19d943b2bb60d800019c6e4d94d8614c5b540366aa1853a00000008901f220e122081949ed7126d8628000a9e1f1b0893d84d50000399c04c690128411b5694704c12db792b423ed1b8ce869e25c33844c696912ef56058ad9d93d616cc2287c90208da91900c33adc0018b3c0600000011decf233cda4a00000056580000001898ec5e0d8240003a4ace8b30c140d92981b9600043913d49a1572000086000000001a1e190a62105c594d9d7a99369922e0000e2d44cb064c78d65581190448607737f24dd7dc03b9240e98f0ba8156497c298756081c8dbce3ec0c191b3fc7082575d18a70d7200000005007c452
  | 27 => 0x490f3119ca4527c208000013837838ba0d9395000092ad8d0c4d5b5f940000005c34bda03000402e08c0bad23e6e440b2a0a0ebcbd5eca9e6c6e15e0b78cb0000807c6a0f143ea10f3b64b740000003ef3728cac30e1510d9cd3cbaf0001ad70f40006b49258e0a3ae58baf9317554b22516ec52c7dc6b74065d6a087a462fb5b2e6bc44f37bc76237f04431e17ac40b73d27747a4000000384164c22a0020000e8a000000298d64de8b37f8000000b4a000000168c5c40001ecccc82b50bd0ab0cd81c44560bb02124345f75a1da18beb338ac61160607aea9be48187144fa26f8d3ab4759820b131a5f64d90001b180001a44f698b80006dfb3808e600072117a98cc2f60003388b82adf15a18c4366a484cc861c0000000000100000da664f83457930004378000000000148a0c5bf05cd0000ec87400000002a7090624d62c064d38a00008d33f912edc026d1f6c51c076341e8a805b1cf2a1f711be56762c99275294bedcd80bc5c164002d10280706bfb0358b58f94c7f31ab3cc28834009f3a7d72018330727505fa2b203ceee1c98b8d09521f98925b81a6036010d55b2df02a985ee151fda27cd2e33c49980adccf7f5026394fab436854590ac0009af3838000c408591981b8053e00010410f1cfe0f00000000201d874f6859c06278b185b024ae80003270000cee89f8144eb4a20b8928a0000a909bc0ba0000a3800063d1df9a220e2aa2125533e0001d80000a1aa70cb5920812db821cd9bd6c8523e80036000dfcdfb35800155c76b629e5e4144a0b0000a789882e4000169112fbc2322b8b07e820104010fc71cdc72a720a0fb25c91131778b9cd645e68000000a2d0000e60f885358002e740000000002008dc4cde751530399a5c5680a7d49585479ec96a451455e27bb4f873acd05c2954c9b28a75701e6cd0a4461b300000001d83f20000f0ab647240785664000608abbd7fe53deb52d788061606c80e7d4de78730c9c9cd0c81432f3664ab2ddb656176962ce55c07957412896261808ba7566fc0da9d7da42b79580b30039c6de435619f3ac8585030594fda1ab057158465420b6448bed65cbe73fdb7bfa2662213909c1c9d986273a46987647f1a70658a8a99a3b96ea4932a39287142c632a10727a380b587f23c7ba0cc55663119b2a91f079924493048f2016ab440dc0e48e408fb4a469a4b146f0b50cbea85eefba798be13a00002c86e20004529b1507679a0000acc50e85029bf7a595e56a1ef5f040003850001189bd800009684fc13c8b54201a60d5a00066d0e000005a17071cbc000e1800033d93389e70b200006d6000236a216ff22c1b0da07d214000000000000000013580000000006933464d32bb70001c28a7dbf20000000bf800000017db9f80002aa86da00000000000015f4000000099000005558580
  | 28 => 0xc783accbf00036340000002bd312c0005589dd9fb000096d80028d8000000000000034e0715500a2c9160000000000000b7b6a337617621d149780001b25eb0f3b26c000b7658816780005432fa8b3cadc555f328691d2274a00008a00000d28000000000ccf2b7800031c14a5f0d74dd406aa6aa18148605bd09021f1a9ae761e8e0dd95c4e9b442ba06764c62e424447903e830a871c205a772e836c0caae1a5a432c50869cd404a973633370031d1499026255c7837956542216cb4352520004376420c141e51a48000620cdf0a480015b8000000239410a0861f714bdbda00061088635d6c483b700004e6ad97188000000950000000048c00030000013d67700002fe9b820eb00017600001ec10d58185c42400b2f63cc9ac9946381e4e7ee3f548a704693a6e1dc1a540006f3d4903019347ab5ca0748c1a86bcb1b6cdb0816c73c1e4844a1c2aaf800000027851314d509a77751936328cc2f84a707fd8d08af000000031aab40001f84000eac2a3bac41ca4e92db800095603fd9c82749029173dc30d9078b491e9a228000c7b46109fa3d61900f5d4f57ffc924d28b449941357307a744c412e070211c5749d252f0e181e819a22f2cf4b680000000000686c5903df4cca940455ca8e9c000428140f15800080718d845da0c0dd8a42dc8000065193ba611cc0003d18498cb886c000348800000053ea3d00b60001f987f44670003d380010db6b33ee928924016e2f2ed88df686a2eb4001d6cc5fad8a960ee49f82641cac97ec1821013512f8e334c106090ba14c542b1811261910cd804d0ce38f7112244c8c2bd03940006daa2490fa0e50f689c3efabf17fd74200019449863ec43c1a252123f14abb6803820003fe8000000d573260de4c5423b01d4175cfa59d11f0cd8e5435e6db1b24f2f0002cda95967e759ee48f67a20628864af5cc6472558629e5d2320053f9454624e454f9960c7ac4404961011532696c4876a1aa610753e04a0000bf1800230c0002615938d093fa0003080000d46000041a96d8728b75e626ac96c44d4e327304f265341d09f44f363ddfbb7ad48a38218e08fedb868a19a77655fe9ef4818c7c998a745ef2ba5cbf00000019006b246c65dab0800000000023e8000c0320f04840009c23c457e5a924d3259b3c11240e81aa0b7d66e80e144127c3022ed2068e95b269457456add7b8a87096383ced0a3f4401d04650ab545ee1a40c800003439896cc9e8000217810ed1a6c515042b464847b80218dec1f17a070000097027f3aec7d26e8bae0880cf264900022ace1e1c53a397ba0006edbf01ca4ba43b3388b4015988735d618ce04d4b74f280019e8974293f2e00006b800018fd2b64c2717818ad588dd0b0f5730e958600008872cc8326c72f1b116c750b804ad01616a000000000000068f8039344e
  | 29 => 0x22e06911f4a3c48e36428f4c7493264e2a4c71f3473942250656a576c35d4ceba4772321358d6c0006171ac5548d0507bb358a62b4b19475809e07640ceb04c0001455b3aa1e0007565728ea89e4012600079612451a1f21c7085889e80002d8edae7c311baa117e00070e94b0efba3500025a955aa6d2719c4d32893d4b4a9dac89d8308c93e16a249b136137c000000000000000000000000000000000001b3812c0000000000f600005d28db1adee7200000000b598c304809c00000040200cd99470269192d19482550002c68000c85067800194e4930e6354523c0004da05480004782624001b160015c22f2200000000000011b40002f29044bc0e5a8002c851f6a7245432793f200014261fed5c2fea4a3689cd0d6300000000000004920000954a3c8000f018080000f680011acbaa3c6313c4427f10db107d7a60000000f73a5c786d958385c820006a9c975c3897656184dcf2600044ce2f264cd745294001cbd35c2c584402641c841829d982a58a4812b9390eb1d4f30c8802849a800385daaf8f3800149ac840003ba00011d854d861d66969ed4728615f56f08270d53a05c4051b4e5a8647a89de2cbab76456add0a1aca1950504245000161cbe374b00011760005d91a7e2be22f46206541a0e072760f198f58a62a84ed454e4a60e5b2c10c8ac7346d7bd96671275f098144ab5b735a458908a1271b8545be467300000006947261d4d05d72c4be5f4aac95a44b780008ef6c00590369ae60009974688000f8e3066a5b986960b9b57daaf884a7065441afc3f80005012728000000029b5ed81eddc1a79b97d550006ed00018ba1470458d85b7000000004397c502e8002b180007b567aa17ca30aa24efaf61b22c6b35b904d866d35431b0a9ba25b649f17b84c6a8e00010a95789fc736608497a0002e58001a5ab6518f2c5431f2e34f90000b5e0000b0949ca9dd897571abc4ac1b407f17e2f5c0003d8a334d180003b335625aa3bc5820001238881605257d7de3b911e25f807c5225798000a7200000000002040005a905a45464a92281b98aa7ca36a500ed0540e349084f41946c73e10b985de0363401fad61700031716e40004ba000227705c0002a9518087c5f367057c00004543e294fd81000044380008ec00000037780000003ad052c60ae6900029393660005e890bc023bf338b1c2404893870200004eaaca0002b58aa800049a8d880004630000000000d863bbc000f4ce1306b3a5092000000003f39a200028b0bfc05f93b5b427eda125f4d94d85d652238000183a8883e552d1ea8246a95ae11a4937438c0a7000063018653c2a600002a870196a87522b65fc91c1288da16de00015dce9ab78dcd0000b0927eb620b127b641105e738668122880016d2c163abb6f8fec5ed86b85f03102ca0000905c00cd868a9
  | 30 => 0x2ccc42f769166ac7c00000000008c02363f80003972000bea6530561c36e6000000003df284000015313aab00000000000c6c6e6b6dc602d445529793142630800375c000cc30000001ab2bd06b3937952828902a1d6d0f292305fb608e44003240028a0181da6959e1e42899b675003c57280a43f662884605eaa697373b4c8a6be14e0ab537d704a4a0aa08f620315cd724a718b6b5600b9e6f2ce6aec0c297774c808ce301e443819610b66f2b27906d742083be42fd443a13934d50e148825a80015b09de86f952800000002c1fd0000d7c9aa45cc000d5617759b13980e0c2d4dda76ce5adf42daa46177ec4473697595e8a0a6bf331cc1b0c728c9a40ba16270a6b149b5c0fd272389c4fe9730611e78c4278837e80002ba17f635000000000042616016820002a3494c40700072cad51572b6c2ae5a7108126537d315c77a0356238a5442c25117aac28abbe3530c19f47202da088ee917a3a273bc2684ab8600d4d78e00425e3be186651fe3973349dbca85d5e1dd176443c337535a648f3000b36d13a0ce40476269f18fa227e6d8b0687be52480029a1cbeac58c78000a0486e1ee86a1208936000157e0007e800000007fc0003ae7239035bf11aa90e59ca20444b02a43be5634a02340a767ce69d13e40001c65c701a94c2036ab2f68c13664b000000117a000683ad40a2462c80019e00001f916c159f1085762a909283cd2f90001d880a40003183aa4e787800003780000c0d5bea7119923630000e34d5266f2b0ec6cfaaaa746308f75e400072a334daf02cb06357fd2c288c330215ba280001290925d208cc9b982ac0005cc621b67942211c6cea8c5467ceb5952cab43cc5a6b62cc4e7088e5c52eb4000c96750c828c77bcb62a000000084fc38b8c83160202b173b8dc2bc06662f1d28244e6da05d5be69595ad2289068a1d589000135a54f32a1bc42e47034c584edd4a1b73fe1bb1baad6d4441bd10fe01ca1319d592046972f06005068b935217e9900c425d3a660e9ea9575e22803e4876a46a5f40006ba58c80002609070000000ab04a80666bde6be7cd6d384a4000aed0b940000126652818b381ce6943c50518df051d0fc1e08518b2d1ef2d711a63dc312687ce8c73a2d826591ae0e5abb90d400002800000010a2c8827880008020fc0000001b2a0003bfaf738a239e0000001c8cade00000000000d35fa3afd8ff0c5465a1040000007132139cac75e00024c105e41501e0000094c1032812604460ee13b8ccd7c000028bb1d83ec00052e396edaa7973cb4f090ab3ff0000ac4270000000000000000024dc001c86bd6ee102cc640ac135d942872a6c01282678daecba1bb9e8588086b6d7b4c0dec0113798f6c2ae9782ca98b0ada01a14134207ae7445bba0149a24f474baac3070098b73b234b640f2156b3ecf74
  | 31 => 0xa9d76f815180007514b434b00004ce00ed215b02eaf5de80001b40000002114000a268002f042a800030f0001626c8c51d82c5788237c869c05b8a4d85a98304659542540f9ae46c00006a87ec70e9b73020088168bc4a0700017c89f0000178cc88771847136740ee846dd163cd1a2f680000016be035beba86800062980011f92906a851e2040000a9d02d0efc000c3a037a3adcc22bf5201491670a144a4859f3dc7e908455956aa95355c05088b24ee3bd849c0000001e630e026c0ad308800156c00035115a0cb22af753000000000000023c11d2acca84b9750ee41d03387ceece5750f88611c76a3846bf1b476e32d51ba814d4fa84485a12921e7e222110c4114609afda1583c01e49603449bf2015725400199003f000000141884f647a8c6000878eae000110a6c646a854c2f2a15000219a0005795049b640543000000558c930000fd08a4bc50000d6000057600002820fd3aa7d6000109d5f2eab59a3a3d397638c26ea679da9dc6cf93ec03838b72827dc1b800009d7a712cac974a5b5755a8b5624333c474406e1c0a6b8c7d00a56163310ec925000290d90c0431551b9f2682b7558adb8588456318ea52175c7265bbac9a682d7df10b3071089b40939020b36830f535b8fdc80125e01ed2329d13df117d7a830c07dada888aa46547aa3f4260634dc80008b04333680000cf692b08580014060db630800142c52a43420747dad967029700000cf763a08b4c6c5490c92154000a0f3d000010d3801d0700000008be0e18d740003242878000fca0000001ac80000006bf8000d9e3be6a811ec000a536deb7a85ee90625380000004c7000322c0000005248554c6b20724b800137e00018698ec26651092e0000832e6600010a40003b61d5ce4544625400da37c47a0896d285a051a64a54b301c2184e20000f29bfc0002a8c00095e4cf3104e2800000073a2f38000d9a00039c513000055a476f9ce62400017e77ca0fbd828670eaa7155cd0c208de0000001c3800079f0001d643d2d6b3dc8106214bc50001de594acb931e75d5518be81325774384000725af287122315d41c90812a6a0000058000b7e5b5989effc2904ec20a4e200a1544a8b8f1c83500018beafe37e0cf28049423e7cc2aacc108e010f126a000000057519846c810d714b894000c532ab80e08ba73d72bb251d1300000000018aa0bd42a69a43ba848720313800031d5fc018986222c65a0000e6a990554ab1bb368f2f5181ffb86b7a74307c0000d0b1ab990c6b60be0002dbc51e4e146e301568b24e15f32b4dd5cd7570c67ccfec244130fad2ce07300000000006e86f2ba4d5205f819f177e1ad1a632d1552f385f7f2640009101fe571ae04d178a445494f0d08e28307c0e92dc4652cc9bb8eeab746208c1c9e6b5d569800000000012db3e85d2010e01
  | 32 => 0x880e6cf800000000014e00173508060a108662f0937029ea4c6671898c1ea55670a0f566aa290ad8be948e528caae241c6cca1239023672c82b36506fda800002f12a7dc5cd4343a013400096f2cb10c9380d9869d83a85002976dd84bcb741ee44d09656da2a195c3078ff440a5dec0008b65824c18459756bc1e9e000000052016d892c5824053c226b18fc0002528ebc000dd4000000000073e00000014e7b22d913004ba730f349ccc50a43c7217000127210ca0c2eecffe92a41980009d406c530c00000061a6bd1498000029ac3af7c00033f00039619cc75864201f8d6a6d84c429c46f44071cd39c149a8e70dd96fd99600022d05ac64a31565b30712eacab06fa58176682031414e2ed8a970000a6037a0002830420fce70c58385ec724dd225200007383ce0003520a6602cf2d1412000000692058b4fc000000353c0000003db80009f400000038d155b0000000cf40001be588a0701583d50001efc0005db4ae044c0005e6c168330d987235c383500848b454dc8d18b6a732a8b7f5a543e89343ad1178093172a36068c69b3aa09b35eedff338161569a1db6ce23223709bd227ae8986e35843cd96dbf400066e05043401ef07a80019061ca6b4000000043d00019a0be460c59e20698c47390001bc041a9106a28f3d6db0000002a36e4200070a0fe4000a212b834580adda909a2bb10aeca90002e640008462d70000000000134b1408ea8b7afe86e9d5427400017b0dbe67e265b4c400073171f113073294331980010a8b031edc6f0e3a9b668babc066abdd49e09315cc9222108001d5953430b08d6534db95551a08542d6100025586429b155300006e4d792808a802fa0003d79645bdc334000092e5b8e65bec67a8bbe6e53d93a1d90d112f29a5509677d4718158040aae761f8c44a8b74e3c68ff59886c4412ab6055626774d22c4edb5d13fc2cbc096e4d7338338dee44171501242476b6b9b83fc00000007d249c0002662e300007ea6b01e22ff518ab7f45d099b1c61c90001f41a382c35fe3adc34a00035e91e8be80000000000000d03000348133aad532380000005a500026a4000d180640dd81e2e2b6a1297c00007c4e7000000051f00017f8bc8b9317f202000095e00031ccb1000047c97b41dab73000173cc2648705790582b2c8ab26da5761097a57227411dcc2c2fb9340e4055a70b2d8a5328a34d30650526e731e69a3d55dc0e6f30404de4e9b66aaf984b481fd8a39544eccef17bd8e414c3f264aa79186ad7d37ab9d40002f25a2400185021bca10771180ac5071218128c7521ec175c000a0022481f2d4ecbe519885ce9a4e01e89c1122f562335240531c000517b11813e67441042a02e235336b28b150056b449ee7c9724f601922470599266d52086ba808c0669deb1921763f300005245f1c8023cd23
  | 33 => 0x3650f963032d9c10f5a0bba2573504a5a46e0912f487a02aca343ab455204c9078001aac5252668cbca22e5b02fd8514a40005f2c00115a00055d093c000d0e68da3f8768e3a3840e4d27e53684a8000f07316555a001640e4e744000003d0004418244fa606ec3940000006c25f601185d02124a
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x92154021d40735092154021f03735092154021d22735092154021d20735092154021f00735092154021d00735092154021944825d5310c640c91735c46050940a4582195310c540d21525c34294440d11535c34254440d21525c34254440a2b805d95290440a298098d5290440e21529856010440e0a535496010440e09535496010440e21529456010440e11535456010440e21525456010440a2980191524c440a2980191520c440a298099152c8440a29801915288440b21811c15250040aa0815806050b20d04735095114720e0563509511472085487595310c720c4475589310c720e0554589310c720d0475509310c720e0565509310c720d04735095108720e05635095108720a50835456008720e214254560087209c1801c9310c620989839c26150920c28655c0615092098b835c76050920d82735c46050920d81735c46050920d04735095114520c897350a6090520c4475589310c520d0475509310c520c897350a6088520e04635085148520a29809516210120a24815516210120c8b7350961c8120a448258c6354420c45651c9310c420d05541c9310c420a1a83d506050b10a1a839946050b10a448254d620c710b048254d420c710e0553589420c7108558718c5248710b05831494248710e04631494248710a0e83d516210310e09535894010210b09831d54248210c29745c06254d10a0d821516314910a258219661d0910c14651cd6150910c30651c16150910a2582150614c910a30855086050510a458614b32cc510a308550a60cc510ca17250a60cc5108e1821c1640c510d07541c9530c510d04541c9530c510d07741c9530c510d04741c9530c510c45861c9530c510d06841c9530c510d05841c9530c510d41801c9530c510a448254d620c5109178754f420c510b048254f420c5109148754d420c510b048254d420c510e0553589420c510c26655c85488510c44631c95388510c44631c953485108558718c5248510e075418c5248510c167518f4248510c147518d4248510b05831494248510e04631494248510a0d821516308510c28755894010110ca1621c5401011082d821d8544c110a4482594314c110b408254c3188110a25821506148110c28655c854481109288754d4248110a288654d4248110b22859c54248110aa0865c54248110b20855c54248110d20755c54248110b80835c54248110a508654c3148110d41535c83148110f01535083148110c50651cd2148110b20855092148110e20655092148110d80735092148110c147598d4284110c24755894284110b20855092084110e82635092084110a18835946050810a31851846050810e21521846050810d097350a5048010c24765494244010d11545cc4044010d21545c84044010b118414d3044010b418214d3044010c28765494244010
  | 1 => 0x1d05545c8544c431d11545c0544c431c15759d0624c431c15755d0624c431c51759c0624c431c51755c0624c431c92745c0624c431c91745c0624c4318d1801da524c431c857418a524c431ac18018a524c431ac180189524c431a5180189524c431b0584189524c431b4180189524c431a4687189524c431c4687189524c431e0684189524c431e0584189524c431e4280189524c431a4580189524c431e4180189524c431a4180189524c431a918018b424c431e046254b424c431c457518a424c431ac18018a424c431ac180189424c431c4476549424c431a8686dc9424c431a9180189424c431b8180189424c431a8687189424c431c8687189424c431e0585189424c431e8280189424c431a8580189424c431e8180189424c431a8180189424c431a8486949424c431e0462549424c431a8486549424c431b0686549424c431b0486549424c431e0486549424c431e0776549424c431e0476549424c431e055250b604c431a85821913154031c25729c46454031c25725c46454031c29725c06454031e11644c55014031e41624c55014031a18835806055321d05549cb530c721c45769cb530c721d05749cb530c72191587d4f420c72191687d4d420c721e0753589420c721c46765c8534c621c50535c0624c621e0453189424c621aa180189424c621c25729c4645422190d821d16014d21c19745806014d21c49725806014d21d04539c76250921e0453508614c921e066550a328c521a4685d8c624c521aa180189424c521ac180189324c521d0475509324c521a51801886154c21b09801c95350821d04721c55350821e0553509610c821d057550b32cc421e056550b32cc421a458598d620c421e0553589420c421857855da320c421c4575588320c421d0575508320c421c50635c35348421c14769515348421c14765515348421856869d95348421c857418e5248421c157518f4248421a148654f4248421a448654e4248421c177518d4248421a148654d4248421a448654d4248421a868398d4248421e058518d4248421c877518d4248421e077518d4248421e0463d4d4248421b2180d4d4248421a848694d4248421b058594d4248421a248654d4248421a848654d4248421e078654d4248421b068654d4248421b048654d4248421e048654d4248421a048654d42484219508754d2194021d80735092194021f01535092194021d04735092154021d12541cd2154021d11541cd21540219508794d21540219508754d2154021d23755092154021d80735092154021f02535092154021f01535092154021d21425c43254021f0142ccb3154021b408258c3154021d42735c83154021d21725083154021951878c83154021d41720c83154021f01420c83154021d08735092154021d1073d092154021d40739092154021d107350
  | 2 => 0x22c000484e10c6833914154e130ce52300540c000aaa32b4bf3785e4580b000f6130ec000511b8890cc3036cc430b0f0c86927081068e71e0501c80d32458180e33683b8a05f0f264468f725c9e0b829318fd2d91cc62922849d2ed14c110e40055b7aff245180f46f430f945d22011243b4ba454261f04145aa0000881fc20000083c85ea28002981b0006d47c1d118ef46e7d2d4001f21c0e04a198000002f320be440f340839174742e05412cd129f0d388a9214dd3b883200fe2bc700f0bd958444746f891063405202217328c7c21211ba962682a1f80a2c43f2e48f33c6c0640024000001133c5201c4004140010837000c3b1cd507c771709f000940000008c2d0c4c4b140029b01088cc0d515c7a6b2651e0010a36002448a405075038763805b41c4737c178d8a82b0fa184b20ac0f000d73423b0f91b2f062044002acf424c003702c2f4003a800000fb0004f3981e48a10168d2492271cc25444000588618c82364c232c40030e40010b334c9a1059000f834c003a4062a8d6000001e849302b0424b4000153d4ae2cc06c8ceb260a726c07114000011900067000c0000000000021c000000000000254e82fe18120c1000000d0002ba790011a800a20000013400000091948e2340008401000530e8d437f119ec001a8a52dc003f013000003c0002320000c001fa004705712e8d82410030588814060006c02160182400080480c0c080200002020180c0200018800210018bc0a010181002000c06002020d06000000000012010e008001f038200201000080616008482a150300400010085000000201800070004408090781c280500004023a0001026040f888140001044001f0003c1a42018040200e21629855014342e11635855014342e21625855014342a8683d8661d4942aa1821c16114142c2b765895014142d13731c55014142d10731c55014142d21621c55014142930879855014142d10739855014142930875855014142d10735855014142e11635855014142e21625855014142b0980149428c531a30805946150831d05735486150831a6180189524c431aa180189424c43
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x8003e75162000090d004c00218504a4942cb080638b630a8400f0000080006000000900200e00e1b2e007463c680152200004006421250000000030200c060421d635855014142c1043ac4b0aa028285c0073589615405050b102e8c00c52926218e80a1180189524c431d00c2300312a4988636019018952d09310c7082eac00c52126218e8061680189424c431d00c2b0031284988632819021a52509310c6c0320312a4a126218d01a5f53589420c721d0029b003128498c43501901c87154d42087400c6c06a6a124210c81a5a8654d4248421a804baa6a1243280435009794d4248550086a012ea9a8490aa010d0125d65509310c720d0041a84a8ac010e412059818c5250921c430410ab92853066288601619841c9530c510c20c3300392a618a21901846007254c314428092ea9ac4a106288481660631494248510c10430eab8a84902219007520d71509204428812ca9ae418a40884c0261535083148110b004b2a6a106290221900851cd4248520443800ca39a8490a4088680216635092084110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 29
  | 6 => 1134
  | 5 => 6283
  | 4 => 3776
  | 3 => 293
  | 2 => 37
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | 2 => packedAt gbK2 (i*71) 71
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (548+((h/14+packedAt gbK7 (464+(h % 14)*6) 6) % 56)*6) 6
  | 6 => packedAt gbK6 (36858+((h/520+packedAt gbK6 (30618+(h % 520)*12) 12) % 2061)*12) 12
  | 5 => packedAt gbK5 (274958+((h/2586+packedAt gbK5 (238754+(h % 2586)*14) 14) % 11268)*14) 14
  | 4 => packedAt gbK4 (203770+((h/1442+packedAt gbK4 (185024+(h % 1442)*13) 13) % 5192)*13) 13
  | 3 => packedAt gbK3 (18579+((h/111+packedAt gbK3 (17580+(h % 111)*9) 9) % 400)*10) 10
  | 2 => packedAt gbK2 (2705+((h/13+packedAt gbK2 (2627+(h % 13)*6) 6) % 60)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff87fffc0f8ff1c38f8fc7fff1c1f83c19f4f3
  | 1 => 0x7f83e3ff00ffe3c0ff1f8e07e01ffc0e6c8fc
  | 2 => 0x7ffc03ffff1fffff001ff007ffe3fff070f1f
  | 3 => 0xf800003ffffe003ffffe00007fffc003f80fe0
  | 4 => 0xffffffc00000003fffffffff80000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10918404611022008182412330444898085471
  | 1 => 0x71328848a324c04c0690c8455208938862c8b4
  | 2 => 0x8200109104010011100112080490242105010a
  | 3 => 0x20652d224a0864a6ab240012692d0112b80ec0
  | 4 => 0xc44630038c4d893b4c49a49c00300623d7a000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0feeaf8e0, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_36350
namespace PEqualNP.Outside.L_meta_36350
open PEqualNP.Outside.L_meta_36350.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 37 := (concat bgb_2_0 bgb_2_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 293 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 bgb_3_192) (concat bgb_3_224 (concat bgb_3_256 bgb_3_288))))
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
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1504 : Interval gbAtlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1568 : Interval gbAtlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1600 : Interval gbAtlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1664 : Interval gbAtlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1696 : Interval gbAtlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1760 : Interval gbAtlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1792 : Interval gbAtlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2656 : Interval gbAtlas 4 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2720 : Interval gbAtlas 4 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2752 : Interval gbAtlas 4 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2816 : Interval gbAtlas 4 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2848 : Interval gbAtlas 4 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2912 : Interval gbAtlas 4 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2944 : Interval gbAtlas 4 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3008 : Interval gbAtlas 4 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3040 : Interval gbAtlas 4 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3104 : Interval gbAtlas 4 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3136 : Interval gbAtlas 4 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3200 : Interval gbAtlas 4 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3232 : Interval gbAtlas 4 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3296 : Interval gbAtlas 4 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3328 : Interval gbAtlas 4 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3392 : Interval gbAtlas 4 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3424 : Interval gbAtlas 4 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3488 : Interval gbAtlas 4 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3520 : Interval gbAtlas 4 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3584 : Interval gbAtlas 4 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3616 : Interval gbAtlas 4 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3680 : Interval gbAtlas 4 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3712 : Interval gbAtlas 4 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3776 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416)))) (concat (concat (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)) (concat (concat bgb_4_544 bgb_4_576) (concat bgb_4_608 bgb_4_640))) (concat (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768)) (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 bgb_4_896))))) (concat (concat (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat (concat bgb_4_1024 bgb_4_1056) (concat bgb_4_1088 bgb_4_1120))) (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 bgb_4_1376)))) (concat (concat (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472)) (concat (concat bgb_4_1504 bgb_4_1536) (concat bgb_4_1568 bgb_4_1600))) (concat (concat (concat bgb_4_1632 bgb_4_1664) (concat bgb_4_1696 bgb_4_1728)) (concat (concat bgb_4_1760 bgb_4_1792) (concat bgb_4_1824 bgb_4_1856)))))) (concat (concat (concat (concat (concat bgb_4_1888 (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 bgb_4_2080))) (concat (concat bgb_4_2112 (concat bgb_4_2144 bgb_4_2176)) (concat (concat bgb_4_2208 bgb_4_2240) (concat bgb_4_2272 bgb_4_2304)))) (concat (concat (concat bgb_4_2336 (concat bgb_4_2368 bgb_4_2400)) (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528))) (concat (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656)) (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784))))) (concat (concat (concat (concat bgb_4_2816 (concat bgb_4_2848 bgb_4_2880)) (concat (concat bgb_4_2912 bgb_4_2944) (concat bgb_4_2976 bgb_4_3008))) (concat (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136)) (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)))) (concat (concat (concat bgb_4_3296 (concat bgb_4_3328 bgb_4_3360)) (concat (concat bgb_4_3392 bgb_4_3424) (concat bgb_4_3456 bgb_4_3488))) (concat (concat (concat bgb_4_3520 bgb_4_3552) (concat bgb_4_3584 bgb_4_3616)) (concat (concat bgb_4_3648 bgb_4_3680) (concat bgb_4_3712 bgb_4_3744)))))))
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6080 : Interval gbAtlas 5 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6112 : Interval gbAtlas 5 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6176 : Interval gbAtlas 5 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6208 : Interval gbAtlas 5 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6272 : Interval gbAtlas 5 6272 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6283 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))))) (concat (concat (concat (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))))) (concat (concat (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496))) (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)))) (concat (concat (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784)) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104))))))) (concat (concat (concat (concat (concat (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)) (concat bgb_5_3232 (concat bgb_5_3264 bgb_5_3296))) (concat (concat bgb_5_3328 (concat bgb_5_3360 bgb_5_3392)) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488)))) (concat (concat (concat bgb_5_3520 (concat bgb_5_3552 bgb_5_3584)) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680))) (concat (concat bgb_5_3712 (concat bgb_5_3744 bgb_5_3776)) (concat bgb_5_3808 (concat bgb_5_3840 bgb_5_3872))))) (concat (concat (concat (concat bgb_5_3904 (concat bgb_5_3936 bgb_5_3968)) (concat bgb_5_4000 (concat bgb_5_4032 bgb_5_4064))) (concat (concat bgb_5_4096 (concat bgb_5_4128 bgb_5_4160)) (concat bgb_5_4192 (concat bgb_5_4224 bgb_5_4256)))) (concat (concat (concat bgb_5_4288 (concat bgb_5_4320 bgb_5_4352)) (concat bgb_5_4384 (concat bgb_5_4416 bgb_5_4448))) (concat (concat bgb_5_4480 (concat bgb_5_4512 bgb_5_4544)) (concat (concat bgb_5_4576 bgb_5_4608) (concat bgb_5_4640 bgb_5_4672)))))) (concat (concat (concat (concat (concat bgb_5_4704 (concat bgb_5_4736 bgb_5_4768)) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864))) (concat (concat bgb_5_4896 (concat bgb_5_4928 bgb_5_4960)) (concat bgb_5_4992 (concat bgb_5_5024 bgb_5_5056)))) (concat (concat (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152)) (concat bgb_5_5184 (concat bgb_5_5216 bgb_5_5248))) (concat (concat bgb_5_5280 (concat bgb_5_5312 bgb_5_5344)) (concat (concat bgb_5_5376 bgb_5_5408) (concat bgb_5_5440 bgb_5_5472))))) (concat (concat (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664))) (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856)))) (concat (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))) (concat (concat bgb_5_6080 (concat bgb_5_6112 bgb_5_6144)) (concat (concat bgb_5_6176 bgb_5_6208) (concat bgb_5_6240 bgb_5_6272))))))))
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
theorem bgb_6_1120 : Interval gbAtlas 6 1120 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1134 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 29 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfeeefeeefeeaf8e0feeefeeefeeaf8e0feeefeeefeeaf8e0feeefeeefeeaf8e0feeefeeefeeaf8e0feeefeeefeeaf8e0feeefeeefeeaf8e0feeefeeefeeaf8e0
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4277074144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36350.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.and,[1,3]⟩,⟨.and,[5,7]⟩,⟨.and,[2,3]⟩,⟨.or,[8,9]⟩,⟨.or,[5,7]⟩,⟨.or,[6,11]⟩,⟨.and,[1,6]⟩,⟨.or,[10,13]⟩,⟨.or,[0,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36350

open PEqualNP.Outside.L_meta_36350 in
theorem PEqualNP.Outside.L_meta_36350 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
