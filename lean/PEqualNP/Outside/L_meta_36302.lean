import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36302.Model
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


end PEqualNP.Outside.L_meta_36302.Model

namespace PEqualNP.Outside.L_meta_36302
open PEqualNP.Outside.L_meta_36302.Model
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

def SBf (j : Nat) : Nat := [6, 5, 7, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36302

namespace PEqualNP.Outside.L_meta_36302
open PEqualNP.Outside.L_meta_36302.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1180a02800bf43bd43be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2270a0a1e610030
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
  | 1 => 0x3fffc0fffffe0c1ffffe0fff07fffe00f3f3fc
  | 2 => 0xc1ffff03f07fffe0f83ff0fff8780fff4c7ccf
  | 3 => 0xfe0ffffc007fffff003fff0fff800fff8f8f0f
  | 4 => 0xfffffff800fffffc0000ffffff003f00ff0
  | 5 => 0xfff0000000000ffffffffff000000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x84204628a0101005284e0113008a621811b15c
  | 2 => 0x94448a1904a484a05a1290a54850a4a94454c5
  | 3 => 0x8a914406949094b04252a0a950149528a8b0a
  | 4 => 0x294e20924c0dae729681888ce6658063e00ea0
  | 5 => 0x318c38e38e71cf9ce739ccc0c4460183ff6000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36302
namespace PEqualNP.Outside.L_meta_36302
open PEqualNP.Outside.L_meta_36302.Model
def s1K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x10a801820002f995d32be6374c6f185c30
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x10c209541cca350b318d420c2550430
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*4) 4
  | 3 => packedAt s1K3 (i*15) 15
  | 2 => packedAt s1K2 (i*26) 26
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (5+((h/1+packedAt s1K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s1K3 (98+((h/2+packedAt s1K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt s1K2 (107+((h/1+packedAt s1K2 (104+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 29 s1Pos s1Neg, 0xfaaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36302
namespace PEqualNP.Outside.L_meta_36302
open PEqualNP.Outside.L_meta_36302.Model
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
end PEqualNP.Outside.L_meta_36302
namespace PEqualNP.Outside.L_meta_36302
open PEqualNP.Outside.L_meta_36302.Model
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
end PEqualNP.Outside.L_meta_36302
namespace PEqualNP.Outside.L_meta_36302
open PEqualNP.Outside.L_meta_36302.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x8000000000018e9f2840e0000200244eac01e0030582003d40a1a9400008000112aa4396340150524641984c6c02240011890084b931c112394084040000240000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x817e51102faa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc2fca5985f54b30ef99661dd32cc2fca3985f54730df20e61bc41cc3be6398774c730dfa0661bd40cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7185f94a30bea94617e518c2faa3186f90630de20c617e508c37e81186f50230ef98461fb308c2fea8985f95130beaa2617c544c2fea4985f14930ef99261dd324c2fea2985f14530df20a61bc414c3be6298774c530dfa0261bd404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861be410c37882185f94030dfa0061bd400c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83dc65907b4cb20bf28e417d51c837c83906f10720f790e41ed21c837e81906f50320bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106f90620de20c417e508837e81106f50220fd18441f930883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f719241ed32482fea2905f14520df20a41bc41483de42907b48520dfa0241bd40483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841be410837882105f94020dfa0041bd40083de40107e88020f690041f920082fea9886fd53109faa6217e54c42faa9885f15310de2a6213c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c437c83886f10710fb18e21f531c43ec43887d48710dfa0621bd40c42fea9085f95210df2a4213e54842faa9086f552109eaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610df20c21bc41843e883086d10610bf28421bf408437a81087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53442fca6885f54d10be29a217f52442fca4885f54910be29221be414437882887d8c510fa98a21f621443ea42886fd0110dea0221fb10443ec20885fd5010bf2a021be540427ca8085f55010deaa0213d54042f8a8085fd4c10bf29821de53042bca6085f54c10eea98215d53042f8a6085fd4810bf29021ee52042dca4085f54810f6a90216d52042f8a4085f94410fba0821be410437882087d10410da208217e500437e80086f50010fb88021fa10043ea20087e44010
  | 1 => 0x7415077c82a0dfd4141be282837e54106fca620df54c41dfa1883be431077a8620ef10c41bf290837d521077e8420ef90841dea1083bc42106fca220efd0441fb20883bd41107ea8220df94041bea8083bf531077ca620ef54c41de29883bf521077ca420ef54841de29083bf321077c6420ef4c841de19083be511067ca220ed94441dfa8083be501077aa020cf54041de280837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a6637e52cc6faa598ef90731de20e637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31bf294637d528c6fca318fdd0631df20c63bc418c7e88318ed10631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa92637c524c7ee8298ef90531de20a63f4414c7688298fdcc531ef18a637f504c6f8a098dfd5031bf2a0637d540c6f8a818df94c31bf290637d520c6fca218ef90431de20863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e437d53c86f8a790ef90721de20e437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21bf28c43f7418877c8310ef10621fa20c43b441887ec6310fd4c621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21fba0a43be41487788290fd10521da20a43f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843be41087788210fbc8421fb10843ed21087ea4210df94021bea80437e53d02faa7a06fd0f40df21e81bd43d037887a05f94b40bea9681bf42d037c85a06f50b40de216817e51d02faa3a06fd0740df20e81bd41d037883a06fd4f40df29e81bd53d0378a7a06fd4b40df29681bd52d0378a5a06fccb40df19681bd32d037865a06fd4740df28e813e51d037aa3a06f14740df98e81be31d037a63a06f0c740df90e81be21d037a43a06f08740beaa4813d54902fca7205f54e40bf294817d52902fca3205f54640df20c81bc41902fca1206fd0240fda04817f53502f8a6a06fd0d40df21a81bd435037886a05fd4940be29281bf425037c84a06f50940de212817f51503eea2a05dd4540be28a81f451502e8a2a06fd0540df20a81bd415037882a07ed0140df20281bf535037ca6a06f54d40de29a81bf525037ca4a06f54940de29281bf325037c64a06f4c940de19281bf515036ea2a06f94540dea8a81bc5150278a2a06d145409a28a81bf315037c62a06f4c540de18a81bf215037c42a06f48540de10a81bf5050376a0a05f950409f2a0817e53102faa6205f94840bea9
  | 2 => 0xa01701a00e0000b8010060080000400401c048090680040100502a0100200b00201c0181301405001818008014080020040000000600e0000680600c0000080002c0000100200402c00812000004020000040080080500a004000040040000700e0100000300c01202c000020080000480603c0180080f026000020080020100000200e0140180a004024000010260040080509a0400800a0040540082206400c0681500c0040480200e000080060060240d8230140000682a0000001600a01c014208320040141480a008004000000080080000a00000c00804000014028020000140c0000000040000101201c00806000020018010000100203c0020000080000a04c0d014000060000030040280d000016004000070020080180100a00001000000018000150000080000e00c0040600901605400000004004008020000380080000a064058000060340181e0660142180900c00c000030040140080e028008000020140040080503c00efca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485ef4290afca3217d94642bb28c857d5190beaa3215d54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216f90c42de218857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e837e52d06faa5a0df94341bea86837d54906fca720df54e41dfa1c83be439077a8720ef10e41bf294837d529077e8520ef90a41dea1483bc42906fca320efd0641fba0c837e50906faa120efd4e41df29c83bd5390778a720efd4a41df29483bd5290778a520efcca41df19483bd32907786520cf94641dfa8483be509077aa120cf54241de284837f53506f8a6a0dfd4941be29283f
  | 3 => 0x83bd4689e5d4850fa2075de9b02209d000a3d118000000e4e10e51d09746fac153c83d0da9252048d0593212cc3d49ab22ba6c02a87e1e0284d88c91f8a989627c1f054ce88d22321a8c08ac3da150c98dc0c63a4140f71027954118f52c6a40011700000000000000001130003b28308727f552000772660000005e0004c6950000000000016109b00000000000046800001e000000013274000000000001905bd0b0000007010a8703f6900002e4000000c926d0008e079aec57aadcf09bd0002c06011d46a264349490c00c8002101eabc164217252c81260000008881c0003325f8dc9f032000cc42ee010178f517640c67c002434c842962000000000750cc0fa44805974164b1c002095ae2fc00000000000c52d9536000001e60009bca41b8000bd4000975323140018d2be9ac000000000005a1a55c6000000001460007ea395808741603609e0000008860a4ecb600016cb307f0314e2000569064309c1788155ec83421a3b094000b1245000000000000007b80000000000000000392be5558984820008fa2019c04cb20004d471d3d00d02256c6193f3423043e1c83b6c7c0c800000000000160b8000001bc540b398f2b93fe0006b27d1c0accb888a0008b8c39bf358b7884a5c000580810d02d07e0da800000c84002a71ba75d87000008000001332780012d800622000a70005babf5148873f4ad174942000bcc0007920e0011680063487cea0fb4f2b2c000200a4289842d83e20011b996388308359861b42ec3893a32e7ad290004fcc516a27b506001089da26e0000021e0007405b9d800002923a082e0570aaa0401869c26800000000000000008ac000002caa2980aeb4b40000019a00011913a6156022d8329523c2383111c0240dc631ce248790fe883386510fb2a251c33cbe880262328cc15835eb192f9aa0a60695217c27038c391631622552a94500016870817562a61488d7028c2c3a28450ec24d6adc000335188660e600171280340a502c00044a2ac28b0d1d8aed4bafb6320152315a0ae298502e62964992ca670ba44016a536207a53700031cbe02603a5383fd44a3a3ac9e0c49be35074c1a000000084aa0000ce8c122061000af183adb2f6b283f83e1aa6b81d80023467189aa35b40043204e394001091112f03e815aa846c2940026200000003840000a68860006381151980040ac58000755da0000028c59ac5cb999d2e4121429503bc460e6800600000a18003c438800147494000c180015ca2c788d8000000f7ac534c000521a33ea000bc8eb1daaa83612b5c07056a94c356b442da504e400000191000868ee0000000015b20e1ec000002560002f8000000000011f000328000f3ae10000006990b0007140d800484000a080000c9a4448a70ec4118c000000000000000002681e80017444c000180040
  | 4 => 0xa47a2032420000024b0444e4fe0000000003416a59eab0001bb5100000000000000068a772dc9806a0000002bc002734144500031b000001160002ee000f60004ea041740000006300707a000000001080825d57b8595ac4b89687b00000000000128000a6a2163a8fd248000664f8941d5000000620004bc1bca92010004bc0f1850605ad5c0b80006118122a3040011e8b91545980009c374494c5ad30001242fa4d4320007cabf32ab0c4317a344578d98e71048d12c00208eb7d0e1b210a9a09800045000000000396be800000000920372ae2b2074000002d200000000000001408000eeb24829cf55ead4490cb0001400023c22c55c002a51c8938000001cc5449028630009c001464ca000488000000006f10103800000000000000000006141589a2ba5e8455690932da8bc210db118748869004a26903294f3d0b9c079f911e6d11930433612c5aa9f280af9792ff06ac0cff0a862427d7f1b74040a81227636c7c8ab10305cb94911c62fe07d680b33ee210a503c3ba46c9aa24000364f986d15284c9396153a0bd569e362a2f4cf00026c0fc001df18e93c950256183c92b93d12059c878090f0bf15088d39
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xe41083365190420cd546410823f65104208f594410831e5310420c754c41083365110420cd544410823e64940208f592500823d65d0020c794f400831d53d0020cd947400833551d00208fd95400831e5350020c754d40082b46150020cd94540083355150020d354f200836551c8020d654e200826f6548020d354d20083655148020ea501200827b6548020d654d200833661d5310ce58354c43366115310ce58054c423e6494f108f59253c423f6454f108f19153c423e6494b108f59252c423f6454b108f19152c42b96090710ae58041c4334548c710cd15131c43345488710cd15121c42b661d0310ad18540c433761552108f993538423d64d4e108f990538423d6414e109b988538426d6214e108f993528423d64d4a108f990528423d6414a109798c528425d6314a10cd55041842b56510610cd59441843375310610cd54c41843375210610cd54841842b56010610ad18540842b464c42108f992544427761551108f994544423e61151108f184544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524423e65905108f9944144334548c5109d1953144334544c510cd15221442746548510cd151214423e65d0110ad987404423c6550110ad185404433454841109798f540425d63d50109b98b540426d62d50108f596540433461550108fd81540423d60550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d984520433554d0410d554f410436552d04108fd96410423d6590410c794e410431d5390410cb94a410432d5290410ad98641042b960904108fd94410423d6510410c794c410431d5310410cb948410432d5210410ae58041042756510410d554c41043655210410bc58041043366510410cd59441042356510410cdd4c41043965310410cd54c41043955310410c554c41043375210410e994841043355210410e954841043255210410ec98041042b56010410ec58041042b160104108f992500423d6494010cd106500423d65d0010c794f400431d53d0010cb94b400432d52d00108fd95400431e5350010c754d400432e5250010cb54940042b46150010ad193100435553c4010d954b10042796584010ec10610042776544010ad19110043555344010d954910043b140440109ed9510043b24144010
  | 1 => 0x27b6550040ce951401027661d53309d58754cc23f6454b308f19152cc23f64547308f19151cc3365110730cd54441cc394414c730ad18540cc23e61952309dd85548c2746155230ad185548c33761552308f185548c33461552308d185548c23f64546308f191518c23f65906308f596418c23f65106308f594418c2b96010630ad185408c26f62551309b189544c27761551309d185544c23e64149308f590524c27661149309d584524c34c524c9308f993514c23d64d4530cdd44414c3345110530ae580414c394414c530b6181314c2b461501309b98b540c26d62d50309d987540c27561d50308f596540c23e61950308f185540c23e64150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d5454830cd952510c3355494430d994a510c3655294430cdd92510c33464944308fd91510c23c6454430cd951510c3355454430d9949510c3655254430cdd91510c33464544308fd96410c23d6590430cb94a410c32d5290430cd946410c33551904308fd94410c23d6510430cb948410c32d5210430cd944410c33551104308f992500c23d64940308f597400c32e52d0030cb54b400c33651d0030cd547400c23f6550030cb949400c32d5250030ad185400c3365150030cd545400c34d52cc030d5547300c369528c03097d95300c34d524c030d5545300c399404c0309ed95300c369524c0309d98754c827561d53208fd9153c823c6454f208f99053c823d6414f209d98453c82756114f20d314d32c823f64547208f19151c83365110720cd54441c83a44148720ad18540c823e61952209dd8554882746155220ad185548833761552208f185548833461552208d185548823e64d4e208f593538823e6414e208f59053882766114e209d584538823f64546208f191518823f65906208f596418823f65106208f59441882b96010620ad185408825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f59053482766114d209d584534826c654c920d314d324823e64d45208f59351483375110520cd14441482b96010520e910521482e86048520ad1854048278654c120f24c9304825e63d50209758f540827661d50209d587540823d65950208f986540823c61550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c530826e6214c209d98453082756114c209e98053083365494420cd55251083565394420d554e51083376494420cd192510823f64544208f19151083365454420cd55151083565354420d554d51083376454420cd191510823f65904208f596410831e5390420c754
  | 2 => 0x6014f219e58053c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f59253887366510621cd59441887375310621cd54c41887a66210621e958841886b56010621ad19131886b664c86218f992508863d6494221cd106508873561d51218f583544863e64951218f994544863d60151218f992534863d6494d218fd91534863c6454d219ed8153486786054d219d99741486e662d05218f99641486b661905218f99441487375410521ad99441487366510521cdd4c41487355310521ad5804148734548c5219d19531486b4644c521cd1513148754534c521b918931486b664c8521e9106214863e64141218f590504865e63141219758c504873441141219d987540865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f59053086766114c219e98053086796014c218f992520863d6494821cd944410866f6548421e9905210867765484218f992500863d64940219d98653d02756194f40ad98643d02b56190f409d98652d02756194b40ad98642d02b56190b40cd94441d03355110740ae58353d02b66194f40ad58653d02b96014f40ae58352d02b66194b40ad58652d02b96014b408fd9532d023c654cb408f99432d023d650cb40e34c832d02b6610cb40ad58432d02ba600cb40ae58032d02b960d4740cd54451d02b960147408f99731d023d65cc7408fd9531d023c654c7408f99721d023d65c87408fd9521d023c6548740cd94641902b66190d40ad58643502b66190940ad58642503376414540cdd0c51503364314540cd50c51503344314540cdd0851503364214540cd508515033442145408f997415033451d0540cd14641503345150540cdd4441503345190140ad98653502b56194d40ae58253502af6254d40ab18953502b76154d40ad18553502bb6054d40ad98652502b56194940ae582525029f6354940a718d52502b76154940ad18552502bb60549408fd95325023c654c9408f994325023d650c940e34c832502b6610c940ad58432502ba600c940ae58032502b66194540ae58251502bb6054540cd54451502b66514540cd99451503375314540cd94c51503355314540cd14c51503375214540cd94851503355214540cd14851503376314540cd98c51503356314540cd18c51503376214540cd98851503356214540cd18851503373214540cd8c851503353214540cd0c851503376014540cd580515023e65cc5408f597315033451cc540cd146315023f654c5408f1953150334514c540cd14431502ba600c540ae580315023e65c85408f597215033451c8540cd146215023f65485408f19521503345148540cd14421502ba6008540ae580215033751d4140cd14750503b351d4140ec147505023d6590440cd944411023f6550040ad185401
  | 3 => 0x3329d58754cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548ca3f64546328f191518ca3e64942328f592508ca7661d51329d587544cab661d51328f987544cb3661d51328d987544cb3561d51328f583544ca3e64951328f994544ca3e61151328f580544ca3e64d45328f593514ca3e64141328f590504ca7661141329d584504ca7661d50329d587540ca7a60d50329e583540ca3d65950328f986540ca3d60950328f185540ca3f60550328f990540ca7661150329d584540ca7a60150329e580540cacd638c83297d95320ca6f654c832b3d95320cb4f654c832e3d91320cb8c644c832e3951320cb8d544c832cd952510cb355494432f14ca510cb376494432cd192510ca3f64544328f191510cb365454432cd551510cbc53254432cdd91510cb3464544328f992500ca3d6494032ce952500cb395494032f24ca500cb725194032dc546500cb3a6494032ce592500cb4d3254032ce951500cb395454032f24c9500cb725154032dc545500cb3a6454032ce591500cb5b3254032da8c9500cb593254032da4c9500cb493254032c794d439072e5250a41ab98b53906ad62d4e41ad987539071f5394e41ad984539069e63d4a41a758f52906b661d4a41cbd4a52906b66114a418fd95329063c654ca418f994329063d650ca41e34c832906b6610ca41ad58432906ba600ca41ae580329069e6314241a758c50906ae6214241ab58850906b56190c41c754c43106b56110c41ad586421072d5210841ad584421063f65504419dd9541106b661d4c41c754c53106ae6214c41ab58853106b66114c41ae98053106b96014c41ad987521069e6314841a758c521072d5214841ad98452106ba6014841ae58052106b661cc841ad58732106b6618c841ad586321063f654c8418f195321063e650c8418f594321078d320c841ad98432106b5610c841ae98032106b9600c841cd98651106b56394441ad58a51106b66094441a798c501069d6314041ab98850106ad62140418f58254cc63f60553318f99250cc63d64943319b98b548c66d62d52318f992528c63d6494a31cd994418c7356510631e598c418c7956310631cd548418c6b56010631ad993318c63e64942318f592508c7344194231cd587544c63d60d51318f992544c63e65151318f580544c67665d0531b598f414c63e6590531ad986414c63e6510531cdd50414c6b66510531cd994414c7375210531ad580414c6b664cc531e5106314c63e64141318f590504c66e62141319b588504c73441141319d987540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63f64548318f191520c736511043197d95310c796414c4319dd95310c63e64940318f592500c63d60953218fd8154c863e64d4f218f59353c863e6414f218f59053c867a
  | 4 => 0xd0989f2fc7505c8002bcd642f0000009f8ab00050e0000000047e00020a1000000000347000000000525946458280069c1bc00000406351120a2000220841124e624867025000871290001b60008e00037a0003a000000000000430000004d800482001aa06b5a8000d413e0503b8000000002a0000000005280000000092007000000000288005e0000000003c02680000063c03c002702ecc51980002c200018201000a5856a640760000007b0000000000000030c000003703a40b9572f87b000151000000001060ec7ec00000000000e5aeb3c2968102ba5420010513412e000001480000004c88311e7d1491b5000000003260006f0000002de4699b8000000000001c580000508360000f98c8004e2238a100050c4c80008a6b0c44e38000000000000000015445a090fcba08894d32e2f8848cd2e08ec768aa2e2be88cad10a6604899d65727e00d93662acad188000a89e800235000000001e80000000013102ab6c612f73ce2dd1c31a52245c03b4a0007f53492521ca9c0b15462445473800000b897d80000000074183058b0cce17b53a1cd8b2ea0003445b18058e250df927000a14f92930000000000036ecb04a8720c8964000006bc000002b84600148f999248000f68f73684f05a0c6630741160696204d4018f92f07697f9f11b8160052580dc12c001ae54c3659f14c55a0000c00049c0000000065cda42f84a640110b00002020160000100000001010000002008000020060000e800010000010000020040000301c008018000040040001300600005800004004000030420100100200600400000000004000000020200000300001c0000300a00007806002000008090000000180500e01c0000701a0000400400e000018000020040000500401c0000201e00002803002000018080120580180000204c0000100400000800000000000000200000080500000c0080c0160100000000e0140580000000401803008000000000020200000302c03c0180700007801801014000020000000080000000200400001000000008070000080580000a02402802018000018030000000000300003001001000000010010000080180f00e000000040060000080000a0000c8080100280000000600c0000703800c018000000080300500201c040020040040380d00200800800004008008020080000000600e03c0080300e0000000400602c00003000004058020000240000f0020840000300000800002000010008030060040080000e0080000000a008000000060040300200001e766194b439d58652d0f376494643cdd0e5190eb66190d438fd954310e5f6550c439d98653d0a756194f42ad9864390b376494642cd90e5190b344394642cdd0a5190a3e65d0d42ad9864250a3d6590c42ad9864310a3f65508429bd954210a7661d5
  | 5 => 0x2b00e8000c2001b28000006500016a1e83d833000000000000000000000028f026000d3b71636d840035627a00000000068c4c00000000000002b2354b640000057abd00a185410000002f31aa000002d03660001aaa33a400064800000000000001bc4140000040e0010f37000000000000000000002900000016934c2049e174800000c2c00000000000002e1000d4c000000000008b00067ac30003570000002b28e69659c000c514c00184a020000000002a4d46113080000064c000d800000000283000b90000001640f40028a38c188000003ba57d6b0061466b18bb072d08393a000364c8d1585d2b4001878090007bd2298200096c000794404b80000043e3208f26f2800000015c0f0b3cdf11b4ac5a55f8000000019c047644000170f50000000036b0006b57aae0000084d280000000000000000998002f8000000000000001180013f6ce07886000000bf921a4c434a50120eb0ce000bcae5156d10000003b0dbd4c86d0320016332f0a07fc782f128c124c827b19692cea9370000009400023a588708f124452cba05764a5491536e0004a8e89c83c8000001f640a98c001ca1d89a116800000000001f33cc1d40027d318000818000000016d17533c000878000009e400000000da0001180003ecb629f0c675c822170000c4000da000278be97f000000b3000000341469393b68840000045e00090a06000ad440955010270190003f42940017a00061d5d8c12825400026b4ce2c45d90a4ae0007280000000000000070a800000002000154b64000000ee276000001400005609240080025a8d8a78000004e90b22900000199082000ad0c93010008f400000000000dc933000710ddac207e2f5608006a000000093000b999c80000000000000000524001ee1520092e800312a609d800638d55989ab33a909840006e4000000686d800152a5c67600000196000898001c53eecf0002cc00000166965140a68a3afd6c633c2018d502c10001074c45c89c0dd668c74001b63d6240001c04360016f800024000001100000000019500078c5f82d3f858c000006b81dcdd000148d35952b1000ad8b9b241f8abc6ba39034910002374640002c8e26c467d28000000000000af0004359a8a73863bc002970004c0ff0000003480004e0080010692647c00000000000000001590006880000031e89400000000001938000000004285b0000014ab46200000000000001311e20b56e00000000000311269a00001a8000001fa1940014e0000000025f000114000000006c4003510e06c0000006d40004029c480660002c80004516292f39e855671ea60c1b000000000690001a655092941000000ca03d1231f00000033f000000002840000000019a400328e72f90001080016b12c00000000000000fc85c3a607c7236d54868c000005dcb2
  | 6 => 0x558000003606528d00015d566874002d53be0000022361491d870004e437d6ba045ce0017b000000000242600000010c000000000b734304613400000000000700000005b4000000007a5a78001fc2d5a4b216ba000719de05e0f0d49433ea4b02d0005b8bb09482611a1f4000001f400000000000000e48000004ad1d1c21d4560c500009e59157000000bf07920c000638000000002c0002116802300027f0000019b2530000a555a462ee31d361534caa8879b4565a301768cc0f889d69b5f3e0bbdad3033369f13b98b600c7c5d098000a6c0003739a8b80022213ab79462e30000003f8000000001c8711a66bd278ae0000000000000000000000398b7400348000515550225101800600021621c1d0864aa0cc000000000012a1880224805e15b450b606b3024bc85136a75016d05b333a3c4244f2af201a70400352000a2459a9e57c8ccd082b1cc7655e000000000000844a200000000424b1000000000000002c90000000000068483d998b84dc0007f80000000000000432c3413b5b00051145986112
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xf0000000000e0000000000008a00361c000650c180642d0000000000005c006e2c800007a31210b60000000d24142800000c40000c2150021d1a54001240048290bcd6740f17516893698ca65c000000000001302c57000b80000109987c000901000605000500000600010002000004000300040009000000000205050203000000010302000f00060207000000a4ce5b24a321d1673d925190a1a38ac9286650d1c56494232868e2b00a89943471582540cac338ec899065c15513254432868e2b24a01953071592500cb852a264a8065c25513254032e826528aa01974132545500ca9838ac8a8065c2dd13254032e10e8992a01970a644c9500cb84b2264a8065439cb5394e41a1ce7a94a520d0f754c83290744992c0194838354d6214c41c32a6b00a620e0d635485210714a92c0290830e5c0654c841c1aca9906420e89325803210692b94ca20c63895884114131a62e0208a098d15739944188698382a620a438558c4114121a62e0208a090c3671d91530861b38eca99681a24c9600cb40868eab0c86a043475586425028b39ec828a81455cf6414540a4ce5b20a2a052572d90515021b38eca992810d1c5650c940a18ea99064a0434755843250344992c01928149dc95314540a48e4a98a2a051773548515028a39aa428a818558c6314540a4ce4318a2a05257218c5150298b80c628a81459cc6214540a2ae6310a2a0625621885150298b80c428a810d9d8321454086aec190a2a0705320c851502993806428a814c5c03214540c60a330062a063051980215021b38ec8a96618c1456010530b22e020a62984c972181314c348208c098a61899486150030c4aa430a801843476945400c21a3b2a2a0061c2549404c030b20e2a02601871151501300c21b38ec8a9e410d1c564d4e20c60a2b0082905a1701052148264b98c090a41a81046048520c90ca992609061653185400830aa98c2a00410d1da5150020868eca8a80107095350120082d038a8090041c85454048020c64c2b00a988619535804104314a92c0208219454d6010410cc2a4b008208515739944104292b94ca208210d5db5310410a4ae5a9882085157594c410421abb6a420821455cf5210410a4aeb290820870553948410438329aa420821c154d5210410e22a7300820872152980410421bbaac0208218554d6010410c4aa4b008208711535804104390a92c0208212cdd56010410c66eab00820863353580410434929ac0208218c54d6010410d22a6b008208611535804104319a92c020821a89496010410c62a4b0082086a1525804104310a92c0208218594c6150010c2aa630a8008626521854004312a90c2a00210d5d464c4010c28c8a9e20086246454b100430a322a688021891915244010960eca022008711535011004390a9280880212c9da4144010
  | 1 => 0x3517cb029250748e7333804bc003e0e8885a159dc007600000684308028000000000322725800006800000001f0003800093e8000000271fcfc00020340064000002225010fc00000021806081b0b078380a0000000442308c060023834003d8000000478e40055000000000378d416132008c00500900000811b8000a22000c054002100000512786c0000000000000100f400003c1c80e0000000005645000000000000000000090f200000005000410ec4c0041800e233269d4620
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x70a900000000012c80400580780a000001806ae000000320098c2c3a6204022a94040043000081905859c7644c832b0281dd13254032908875913254032b00815913254032a0b854c9600ca41c21625c04114131c11635c04114121c05635c86314540c11635c06314540c05735886214540c21625c06214540c05764c83214540d01325c03214540c8172104604c530d01521c5404c03091087545404c030c81731046048520d01531c54048020920875454048020a2182d4d6010410a1183d496010410e01539496010410e02535496010410e01535496010410c107654d4044010c20765494044010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 802
  | 4 => 883
  | 3 => 144
  | 2 => 26
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
  | 6 => packedAt s4K6 (788+((h/14+packedAt s4K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s4K5 (24591+((h/267+packedAt s4K5 (21654+(h % 267)*11) 11) % 1059)*11) 11
  | 4 => packedAt s4K4 (36788+((h/294+packedAt s4K4 (33554+(h % 294)*11) 11) % 1410)*11) 11
  | 3 => packedAt s4K3 (7440+((h/48+packedAt s4K3 (7056+(h % 48)*8) 8) % 251)*9) 9
  | 2 => packedAt s4K2 (1608+((h/8+packedAt s4K2 (1560+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fe1fff0fc7ffff071e3f8ff1c1ffffc18f0ff
  | 1 => 0xe1fe1fff007c7c7f81fc7f1fe01c387ce73c93
  | 2 => 0x1ffe0ffff807f8ffe007fe3ffe03f8307cf1c
  | 3 => 0xfe0000ffffff800fffff8003ffffc003f80fe0
  | 5 => 0xffffff000000000ffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x80280010209010001040902404050a20085025
  | 1 => 0x4c44c6221928a88380a4290b20c89158632c92
  | 2 => 0x50804a4448094014a2004a4149402509058518
  | 3 => 0x4151488904009294529000292928012b00ac0
  | 5 => 0x9919980ee272724e79d2749003030663def000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee8fee8faa8faa8fee8fee8faa8faa8fee8fee8faa8faa8fee8fee8faa8faa8fee8fee8faa8faa8fee8fee8faa8faa8fee8fee8faa8faa8fee8fee8faa8faa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36302
namespace PEqualNP.Outside.L_meta_36302
open PEqualNP.Outside.L_meta_36302.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa817c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa418778c830ee190617e510c3eca2185d94430bea8861f5510c2eaa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef32883d865105f94620bea8c417e50883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc84907b50920f719241ed32482fea2905f14520f790a41ed21483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bcc820f6190417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e50843f481087e50210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fb18a21f531443ec42887d48510fd20221f940443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f741043e882085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe4250afea2a15f14542bfa82857c5050afca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbdc85997b50b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65de438cbba87195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865de430cbba86195f94832f721065ed420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e837e52d06faa5a0df94341bea86837d54906fca720df54e41dfa1c83bd43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41be29a837f52506f8a4a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077e8620ef50c41bf29083ee52106dca420df54841f6a90836d521077e8420ef50841bf28883bf41107ec8220ef50441faa0883b541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c7dca518db94a31bea9463ed528c6daa518df94631fba0c63f4418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7bc8698f750d31bfa92637c524c7bc6498f70c931fba0a63f4414c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21f721643ed42c87de6590fb0cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621fba0c43f441887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f721243ed42487de6490fb0c921fba0a43f441487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9
  | 2 => 0xbc2a816a1947a0007b00035a001250000000013d8000000a0b911d3824c811000000000ec15e198774e9aa0000168a60003ea0000017a0003980014a000280000000009312f8000000000017d23853c0000025e9d0000002e66c4261da000000000830000800015f28c564091571d264c0029f394638839fc4ac7ec002a10000000000000046553000000001348001120000005f0000000000034c0012211a0001ec02a473ae1d4058ff00082c349d6038001380e70005885da0a000420001a5000884000000000001897134e5e06d11509a5747a917000a34190004a80012ca515120000014400000000214386000000ae00c7200000016c158001980a284c6b9db134920000a7222770040c64840007880008a8909894d48a000002125505ad1d8610004e00006516e51529800458064c40f046e630a726b282a4cc10a253c738000003e8714d4800240000000001e85d43800007e6640f15600077c2e0001040f466800380000000000006100000000025c00007370000000363c00000000043e1b9132730688d03699410a9b4802231b09bca98c91dc9d82011b2c82786a9cd42a9f85e9764ae0005c2a437e428a1204138a3c598fd000248001eb4c48e000067000550940d04ee000000002b631cb71180127d93e03e5283790ea7248206c0780047c000000040002c000180100c000040901c0001000008150080002c0502000004000400100403008010102000005020000200000005004020000204404000000000401004008000080400008008010041500c0600c00000010040000400034040000300c000141701400000031640002c0800c0303c020000a000000000004c00000000000003c0501803014040240d0240000001050000040203c0d0000100c0104405004010040100c1103c000040102c0c00404058050000a0000002000000020000002c0004401054030003300000000040440c000000301a0080501c00004060100400008018000000002c0800003004040000000c0001402008000000102407004010580300000004000300901805000020003d0140100401006fca5a1fb94b43b7296877d52d0fdaa5a1db54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a17794f42af29e857d53d0bbaa7a15754f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c85f65190aeca3215f54642faa8c85755190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285b
  | 3 => 0x26a0007b0620000462b54c1430000009c80000000000000486a14000004747307280044a6a07099c2245440000030007c00000074808a58f300033d078bc1583e82d8c14ca8194606b4c88bc85a4d01a680001ea0001dcd20d3088a1c9a01533c2502aa3110867c2c0bf1da73cb612e376328e58383fe3dd2e17b00032c31000336a20b022b1d46c85aa8b3ce80cfb8b01a46841509827405c8712b100410020002b00080013c0c0a58139495220008f8000000000029b402000000000008885927132a0840800044e30d27800000000000130003a0498884b4000000003602e8000e23f4a28001d53a2000c18740000007e00000061c0007d21a000000003c8001148000f28a00004f0000000020800092d2e990508138e48961e45003f84102237029a5200048c00000000778330000005993d00018a061481030e4000000ec000000001d00000008810c000000000df4fe97855a630c87989113f0006b87ca35000750b8209000570001a213e1f800000000764908000008c00026000059c0027803a00136000000000cb0000000b02829d54a998db2a900643c2a18b358000759b9000000000003c6000241c71328313700e1906d0a814708c9411019212a0bcb79e54542052d9ba2f21650b8004226dc439be3e6984001f9000000d9a164208781b8001b2000a9000000000548db084748291630000c05a0f84d045850a3f3fa5a892283034000002970564dd168004ea5a4bb96d30a218aa936388a382487a05c0d4ba0d63142405799d3dc1a0f100011c22c7f1af000000001910f086c6004714c0000003b492000e12073fc000000000007c09d9ef00000000000000718001093f000000000000a040000000000083000000128721261a88f09829a07227500000000000000b132e0010c0000001c54e0003da0000017f2d00010700002c000120253e44147799a0145f81493d24a6d551135000634002993568cc7195a3468b8318b914612cc487c54e7a102a550008343506c0000cd2c2804381bc0600019c99c000c20008d82b8000000014113e50c0005f0000002440a0002660000003c1186f0000000002a1200261ba5209512c3e2000c30d10007850d0002c29f452873000000f48a400000400000000001231142f8174b28e037aa8c8088f4f2a543b23911444c8f09b30200000043000a48000fb0008c84680049c0009380035463c000002044b4948
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5424834c53509209b996324834c538c9209b195324834c534c920ab593214834c53c8520d314d2148358538c120f28ca3048278654c120f24c9304834c53881209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c20d3189530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c209b597320832d54cc820d354f320826d650c820cb550320834d530c820ba58032083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083673254420d90c9510832d54c8020d354f200836551c8020d654e200826f6548020cb55120082cc6348020d354d200836551480209ed95200835953480209798c54c425d63153109b98854c426d62153109b98b53c426d62d4f108f99253c423d6494f109798f52c425d63d4b108f99252c423d6494b10cd15141c42e5628c710b558e21c425e63152109758c548426e62152109b588548426f6254e109b189538423e6414e108f590538426e6214e109b588538425f6354a109718d528423e6414a108f590528425e6314a109758c52843375410610bc58041843b04190210bc18540843b341502108f992544427761551109798c544425d63151109b988544426d62151108f994544431e6315110c758c544432e6215110cb58854443356115110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d52442766590510cd15241442746550510cd1514144334548c510b958a3144274654c510cd15131443345488510b558e21442746548510cd15121443385490110ec90640442786550110ec505404433454841109798f540425d63d50109b98b540426d62d50108f596540433461550108f990540425e63150109758c540426e62150109b588540427661150109e980540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d984520427565d0410cd553410435553d0410d954b41042756510410cd55041043555310410d954841042f16010410cd553100435553c4010d954b10042796584010ce55210042776544010ad19110043355444010d554d100436552440109ed9510043395444010
  | 1 => 0x867661d50219798c540865d63150219b988540867a60150219e580540866e62d4c218f990530863d6414c219d984530867a6014c219e580530863e64948218f592520865e63944219758e510866f65484219dd9521086766194f409d58653d02ad62d0f409d98652d02756194b40a758f42d026f6254e409b189539025f6354a409718d52902b96010640ab58b435029d63d09409798c515025d63145409b988515026d6214540d598c51503556314540cdd0c51503354314540d998851503656214540cdd0851503354214540dc580515023e65d0540cd14741503345150540cd146405034e5394840d354e521034e5354840d354d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d9549511023d6590440c754e411032d5290440cd546411031d5310440cb54841103355110440ae580411031d53d0040cb54b401033551d0040dc546401023f6550040c754d401032d5250040ad185401033551500409ed95401037151500409d98754cc27561d53309b98a54cc26d6295330b558643cc26e62947309b58a51cc29d64cc7309dd85548c27461552309b988548c26d62152309d984548c2756115230b6580328c23f64546308f191518c26e62951309b58a544c26f62551309b189544c27761551309d185544c2d56190d3097195434c23e64149308f590524c27661149309d584524c32e6414930cb590524c34e4314930d350c524c3666114930d9584524c369601493097997324c34c52cc930d3149324c29d64cc530d314b314c34c524c530d314a304c26e62d50309b58b540c27661d50309d587540c23d65950308f990540c25e63150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d545483097596320c31d548c830d354a320c31d540c830d3548320c2d9600c830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430d58c9510c3543254430c7553300c34d52cc030d5547300c369528c03097d95300c31d544c030b3189300c34d524c030d5545300c27b654c030da549300c27661d53209d58754c825e63953209758e54c823e6414f208f59053c82766114f209d58453c82e56190b20d314d32c825e63947209758e51c82ad64c87209dd85548827461552209798c548825d63152209d984548827561152208f990538823d6414e209d98453882756114e20d3d4c32882e9600ca208fd91518823c6454620f20ca30882e8624c220f2cc9308825e63951209758e544825f63551209718d544827761551209d185544825e6394d209bd89534823e6414d208f59053482766114d209d584534825e6514d20c7990534831d6414d20d358853483566114d20d558453483596014d20d314e42482e561909209b19
  | 2 => 0x654c832d3d95320cacf644c832b3591320cb8e544c832e3551320cacf614c832b3181320cb365494432cd552510cbc53294432cd951510cb355454432f14c9510cb564354432d550d510cb664254432d9509510cb3a5494032ce552500cbc93294032dc946500cb715194032d34c9500cb3a5454032ce551500cbc93254032dc945500cb715154032d690d500cb594354032da909500cb694254032d6cc9500cb6a3254032d64c9500cb693254032d24c9500caad62d0e41a758f429066e62d4d419b58b535065e63d49419758f525065e63141419758c505066e62141419b58850507566194c41ab58b43106b561d0c41c794d431074e5394841d354e52107666194841d394d521074d5354841cbd0d521072d4354841a758f421071d53d0841ad587421071d5350841cb94942106b564904418fd9541106776550441add9541107376550441add8d41107965350441e554d41106b76250441e994941107a55250441ad181411075a5394041d654e501076a5294041da54a50107b14194041cd505501075a5354041d654d501076a5254041da54950107b14154041ced0d50107394354041ced0950107394254041ced0550107724154041ce50550107714154041cc505501066e62953319b58a54cc71e6395331cb98a54cc72d6295331c795143cc71d548cb31a759032cc71d540cb31d354832cc6d9600cb319b98b548c66d62d52319b988548c66d62152319e980548c67960152318f992528c63d6494a31cb992528c72d6494a31d9986528c76552d0631cd550418c6e56210631d9548418c6f16010631d394b318c6b664cc6319b98a544c66d6295131b5986434c65c6550d31a7590324c6d6610c931b6580324c67665d0531cd550414c6d66310531e550c414c6e56210531bc580414c6b664cc531b398a314c63e64141318f590504c66e62141319b588504c67661d50319798c540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65f654c4319dd95310c65e63953219758e54c871e6395321c758e54c872e62953218f99353c863d64d4f218f99053c863d6414f219e98053c86796014f21cb95142c872d54ccb21ab59032c872d540cb21d354c32c86e9600cb219798f548865d63d52219798c548865d63152219e980548867960152218f992538863d6494e21c7992538871d6494e21d5986538875553d0621cd55041886d56310621d554c41886f16010621d594d318874e53c8621ad993218865e63951219758e544863e6494d218f59253486e661909219b195424866e65cc921ab590324874d530c921b998432486e9600c9219d99741487355410521b558c41486e66210521e950841486f16010521b998a3148674654c521f10c931486b664c8521b398e214863e64141218f590504865e63141219758c504
  | 3 => 0x9c068000009000b8001d603d351f5444000001d62280002a06518849cbb0bf0725dc060d0574524559c2410500f49cd31c6ac581ac000190ea00052452d389b000035c3b2c9198970220000d06b4c02c847a0008a80000085cea8c72142f82a95241e8ccf5a8658007d368dd0000001e8c8238aa88609436c78d31249042a0000097208000e7a470cc000d1000000678000b33540007c0000009a0000000004c81c0005369e80022046e89c0009e0de4cc002a43662b0001bb000334042a80003ed2c2a932c0013b8000007c43a8000000000022f0004f41d99c23c60c000000009182396c1c40014e09311c0f16118c5340008c8000001dd0e99126cac48ba421be890632c615e090a12510f828cb08de42a5bcd20c90366d4bc1750000014702e0002f039888000000fd81d0003040000000000000000504000fa0f2302000004000000080000100200a00c0900101600000003000050000000260000000000000000000006008008060000040080100e00800808000010038010080000080000e0040c0020180040000000c018000080020040080200806000001000040060020020040000001000c0200200608001816006008000000020000000700c00c018050060000c0000020100200300200000002000050058000020100002100202c01800002010010040000140000501201401006000000028000160100000902801c028010180000500100202c018000040080000000c010000000000080280805a0080080000000801001004004000050020000000100e0040000000c078068010000140480700c01c000050000280000101a0100180d00400c0480100004000015022090030000000040300500001c020030020080000300800c010040080000b00000003800001000002766194b439d58652d0f666194b43d958652d0ece62d0e439b98a5190e6d6294643cdd0e5190f666294643d958a5190ece62d0d43ad9864350e6e62141439b5885050e7661141439d5845050e3f6550c4397d954310e766194f429d58653d0b566194f42d558653d0b1e5350f42b398f4290a5e63946429758e5190b566394642d558e5190b374294642ab98b4350ace63d0942ad9864250a5e63141429758c5050a7661141429d5845050a3f65508429bd954210a7661d53329d58754ccae56190b329d987548ca7561d5232b5586438ca7661d51329d587544ca5d63951329b58a544ca3e64d45328f593514ca3e64141328f590504ca7661141329d584504ca7661d50329d587540ca7a60d50329e583540ca3d6595032c798e540cb2e62950328f990540ca7661150329d584540ca7a60150329e580540ca5d6590c32b358a430cad56190c32c7951430ca6d6590832b358e420cae56190832cb951420cb8d4350832b358e320ca5f654c8329bd95320cacf
  | 4 => 0x298001208da20c8fc7b92328a3a03d9f01403d4002350005445c13b000000458d5000001590a2320a0d4a0000004bc460002f8000000000fc3611880029e2ec5d1570584a0e381c4f859468a484c84e81819932668d43a191369c91084841a95d4ca2e0f40000021e39004128124000511370715580007300000021c000000503e8f01b752c224002901300003c97a3c41840029e000000c300000000109000000000df0dc4f6574ae00054a000000000004b800000000000968fd0b08b49e24f3083488c19200e728b198209200025000206000b68001c2270628003800004d12c4a60008b01252e69d499200dca8c889ee0221e05a12a0143d0bd81341c6b9488ee00015d5800032a024b805b4de740002be0163b1619c14880012b2d3000578a9956122a745386000000c0028f2345f8f205d106088bc8021547e485a6b000a20020002ce0000000031a0015a9cc3865654c0f13501a83180602cb45381fe56c12d5301a194200ca02d0a0484b11db58a8a12280000000133000000000000000000009f8e90008f00014750a8980006900047cff8b10000a4001f60009a400000000aed1d1890682b91c0f9000000ce9a54ea00000000000000f084d24c0008400006a0003586d0009e0eba2920e000001f30d884c17a730bc9680027d2442340f0000000000029f000000cd08a000aac002bd0000015709f0fa0000005920a000f780016c5f4a50004ce000000000640000c0000000000000000080811aa7000974d30d42820fcb98000007496a0001b61152f2bf000000000ea4ec000de8cb00000000000578938c79a133e1708113806e3f8001d3000000001dc00a4491b000000724000404062d4002d0000000a400000033c3800009c4e50b00000066041000598000568004462856900027c000479d80009fcf524d30e000001292b4158d793532e000dc284396ab4290812564c50e2c1286000189a045686c002c73787b51d8001245180024a2c0000868002d4000131fa000000001ec5140011a000000001671884aa000000002b00000002b212539081c40007640011d464001009df4d80007385a40a590000d31e0b34000000003804b0004c00047688400056d598a40000011c97441830c530002aa9e48080000000000000000000c28002fe79cd90000827dc0004f000108dd1b90003580021f4868940c800512000000b9000001328001500d88700007cb10778744e8738729b10000009800055e43d3f1fd0009488980000046c7e08500062c2300000000000000000000002b92e41c87224b4300e9409b40008c0001bf000000000e32cc3d8000003cc0014680000054000043516000b72a038c8b000000000a892fab822014cf902a336000590d929a0546121413a4d0f28144982a50496b4a8254b400001c000ee9e83525c52ca1140
  | 5 => 0x928900be2dc261370400000015f3a2000000250a28286028c0c47e0000000000cd651de0000012da0b0001fd1f1da00019d020bd00033967a1a2003fcc50f30000015b8002d2ad04ca954c60000000040e0016580000000052a2a40c001509fc4c2550e2886
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x17000000240480001008a2801d079a0f320027918001801a8e0d16ab232a0d8c288a9fad99219385a1310b2e10981e09aa92a5038a122c8caf800015a98727002d1c800016300300000000001480281980001b32800429142b95248ea6b19db08b9100812389130520a597861c0000069eaea008001b8faf22002c18800002801f02000026000180404340028100428300800480000185004b40004000430081424681c0c0410242662b8ec899065235d3614c83291ae830264194c571181320cb82aa264a8865c150d4254432e14a8992a019709544c9500cba0994a2a8065d04c95154032a92e521aa0195517190d500caa4b9c84a8065585c64254032e1286a12a019548764c9500caa5ba264a8065525d13254032a96e2992a0194a572d8d411064ab9ec4a0883c154d525044192ae63028220ca572181411078929a82a8083c454d4154041e44a4a0aa020f21525055010694b9686a80834c5c74354041a32e7a12a020d3171d0950106983b282a80834cdcd4154041a66e4a0aa020e195458032cc724a92c0196638c5516010631cc2a4b008318e8543588414c718aa2c020a63a450d6010531c52a8b006590e495358032c8718aa2c020c439454d6010621c92a6b006490e85635084148718aa2c020a43a85096010521b0ae81926290dc1700c93148692b968628a819158d6214540a2ae7a10a2a0651635805150330b12c028a818654d6010440c52a4b008220615531854010312a90c2a0081515c64314930c4ac8b08a49862964580524c330b0ac0292618359052cc530c32a8b006418551700c9510c306aa0c49806191189514c030c96a6b0065104ca76cc9308830ab22c229a41865916014d20c92c4b00a69065161580534832229ac3212418359053c8520a94eb1946090648654c93048314aa2c0190419254d600c820ac2e0192a21060d5418d20082263b2a6900419118d5148020c66a8b0083084b276d054084306b1ac42a2218658d6015110c52c4b00a8886316158054443122a2c518a21851516388510a64eb20c8088630655054044318aa2c0208219454d6010410cc2a4b00820843476551100430a322a688021891915244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x33880280021180000001909841d93254032941811d9325403294181dd1325403290984dc53254032911831d94154041921821d9415404192182dcd415404191183dc94154041
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 725
  | 3 => 102
  | 2 => 8
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
  | 5 => packedAt s5K5 (20684+((h/227+packedAt s5K5 (18414+(h % 227)*10) 10) % 990)*11) 11
  | 4 => packedAt s5K4 (30201+((h/241+packedAt s5K4 (27550+(h % 241)*11) 11) % 1053)*11) 11
  | 3 => packedAt s5K3 (5270+((h/34+packedAt s5K3 (4998+(h % 34)*8) 8) % 135)*8) 8
  | 2 => packedAt s5K2 (490+((h/2+packedAt s5K2 (480+(h % 2)*5) 5) % 22)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3f8ff1fc7c7fff0c63e3f07c707fff0930ff
  | 1 => 0x1fc7f1fe3f8071c7f07c7c7f8f8071c736cc93
  | 2 => 0xe007fe003fff81f8ff807f800fff81f8c70f1c
  | 3 => 0xfff800003ffffe00ffff80000ffffe00f80fe0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2008002040080000000809000101040001025
  | 1 => 0xc491246048192288302424230c832496124c92
  | 2 => 0x41a204a4912825015480690525250132470518
  | 3 => 0x8810694922504092a969000a4a4a4c04b80ac0
  | 4 => 0x1124498003624924ce52524c600c0820eda000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36302
namespace PEqualNP.Outside.L_meta_36302
open PEqualNP.Outside.L_meta_36302.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x118718818e099680010a09001d87848b160002180a9d001b9aa013941900149c1f04008e9e82801b1e030580050020800c1983901c92128817159f9a0b8d0d8f151306068010801108800c800000178f84060a10502160008e0e4818a0010008160820001ffd50077f5401ff95007fd5401df55007fc54027fd4c05fe53027f54c05fc5301ffd0c05fe4301ff50c05fc43027fd4803fe52027f54803fc5201ffd0803fe4201ff50803fc42017fcc803fe32007f4c803fc32027fd4409fe51005f94409fd51027f144097c5101ffd0407fe4101ff50407fc41017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc21027fd40097f50027f94009fd50005f54009fc5001ffd0007fe4001ff50007fc40017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200effd9110075fec888003bf64440015fb22200eff9911001dfcc88803bfd644401d7eb22200eff1911001df8c88803bbc64440075e322200effd5110076fea88803bfe544401dfeaa2200edf55110077f8a888003ff63440017fb1a200dff98d10015fcc688003fd63440017eb1a200dff18d10015f8c68803fff534401bff29a200fff54d1006ff8a68803bff434401bff21a200eff50d1006ff88688003ff62440017fb12200cff9891000dfcc488003fd62440017eb12200cff1891000df8c48803fff5244019ff292200fff54910067f8a48803bff4244019ff212200eff50910067f88488037ff3244019ff1922000ff4c910067f8648803fff514401fff28a2000df9451007ffaa28803ffc514401fbe28a200effd0510077fc828803bf6414401dfea0a200efd50510077f88288037ff3144001ff18a2000fd8c510007fa6288003f5314401bfe18a200cffc8510007fc4288003f62144001fe90a2000fd48510067f8428803fff504401fbfa822005ff9411007ffaa0880037d504400bfe282200effd011002ffc808803bfa404401dfea02200efe5011002ff88088037ff304400bff1822000ff4c11002ff86088033ff204400bff1022000ff4811002ff84088003ff1044001fd8822005ff8411002fec2088017ff650400b7fb282005ff99410025fcca080177e65040093f3282005ff59410055faca080177d65040013eb282005ff1941002df8ca08017ff640400b7fb202005ff9901001dfcc808017be64040075f3202005ff5901004dfac808017bd64040015eb202005ff1901002df8c808027ff5404013bfaa02009ff9501004ffaa8080277d5404013fe2a02005ffd8c1002dfec608017fe63040057f3182005f798c10015bcc608017fd63040017eb182005f758c10005bac608017fc630400b7e318200affd4c10047fca60802bfd5304011fe2982009ffd0c10047fc8608027fd4304011fe2182005ffd881002dfec408017fe62040037f3102005fb9881000ddcc408017fd62040017eb102005fb58810005dac408017fc620400b7e310200affd481003ffca40802bfd520400ffe2902009ffd081003ffc8408027fd420400ffe2102008ffcc81003ffc6408003fd320400ffe190200bbf98410057fea20801bfe510400dbf288200aff54410037f8a20801b7c5104013ffa082006ff9041004ffa820801bfc4104011ff9882006ff8c410007fa620801bfc310400fff9082006ff88410007fa420801bfc210400b7f3002005ffd401002efea008017fe500400bfea802005df5401002ff8a008017ff400400bff2002005ff5001002ff88008017ff300400bff1802005ff4c01002ff86008017ff200400bff1002005ff4801002ff84008017ff100400bfb8802005ff8401002ff42008017fd100400bfa8802000fe44010
  | 1 => 0x7f8204800dffb2e2016bfd9710036fecb880027f65c402dff32e2004bf997100b7facb8805afd65c400dfe32e2004bf19710036f8cb880127c65c400dffb26200bbfd931005ffcc98800efe64c4017feb26200bbf59310037f8c98800efc64c4017ffaa6200bdfd531005ffca98802ffd54c4017beaa6200bff15310037fec788002ff63c402bff31e2002bf98f10007fac788002fd63c400dfe31e2002bf18f100b7fea788057fe53c402dfea9e2015ff14f1005ffe8788057fe43c4017fea1e2015ff10f10037fec588002ff62c4029ff3162001bf98b10007fac588002fd62c400dfe3162001bf18b100b7fea588053fe52c402dfea962014ff14b1005ffe8588053fe42c4017fea162014ff10b100affe6588053fe32c4001fe9962014ff0cb100b7fea38801bfe51c400dbf28e2016ff54710037f8a38801b7c51c4017ffa0e2006ff9071005fec838802ffd41c4017faa0e2006ff107100affe638801bfe31c4001fb18e2000ff4c710007ea638801bfc31c4029ff90e2006ff88710007ec4388003fd21c4001fa90e2006ff087100b7fea18805b7f50c400bff2862016ff54310006faa188017fc50c4017ffa062005ff9031005ffa8188017fc40c402bff9862005ff8c310007fa6188017fc30c4029ff9062005ff88310007fa4188017fc20c400bffb2c2005bfd961002ffccb08012fe658400bbf32c20049f9961002ffacb0804efd658400bbeb2c20009f5961002ff8cb08016fc658400bffb242005bfd921002ffcc90800efe648400bfeb242010bf5921002ff8c908016fc6484021ffaa42010dfd5210087fca908043fd5484021beaa42010ff1521002ffec708016ff638400bff31c2002bf98e1002ffac708002fd638400bfe31c2005bf18e1009ffea70804bfe5384027fea9c2012ff14e10087fe870804bfe4384021fea1c2012ff10e1002ffec508016ff628400bff3142001bf98a1002ffac508002fd628400bfe3142005bf18a1009ffea508047fe5284027fea942011ff14a10087fe8508047fe4284021fea142011ff10a10097fe6508047fe3284001fe9942011ff0ca10075fac30804fff5184027ff28c2000df9461009ffaa30804ffc5184027be28c2010ffd0610087fc8308043fd4184021fe20c2012ffcc610007fc6308003fd3184025fe18c2011ffc8610007fc4308003fd2184023fe10c2005bf9821002ffea1080177f508400bff2842005ff5421002efaa108017fc508400bffa042005ff9021002ff48108017fd4084021fca042005ff1021002ffe6108017fe308400bfe9842005ff0c21002ffe4108017fe208400bfe9042005ff0821002ffe2108017f71084001fd884200fffd951007dfeca880037f65440013fb2a200fff99510025fcca8803ffd654401f7eb2a200fff19510025f8ca8803f7c65440093e3
  | 2 => 0x300fffaa0980037d504c00bfe282601effd013002ffc809807bfd404c00bfe2026002ffcc130017f66098017fe304c00bef1826005ff0c13002fb8609800bf8304c03bff9026005ff0813002ffecb10016ff658800bff32c4004bf9962002efccb100127e658800bfeb2c401cbf5962002efacb100027d658800bfe32c4005bf1962002ffec910016ff648800bff3244003bf9922002ffac91006efd648800bfe3244005bf192200dffea91006f7f5488037ff2a4401bff552200defaa91006ffc548800bffb1c4005bfd8e2002ffcc71000afe638800bfeb1c4000bf58e2002ff8c710016fc6388039ffa9c401aff94e200e7faa71006bfc5388037ffa1c401aff90e200dffa871006bfc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944005ffd862002ffcc310002fe618800bfeb0c4000bf5862002ff8c310073ff5188039ff28c4000df946200e7faa310073fc5188039be28c401bffd06200dffc831006ffd4188037fe20c401affcc620007fc6310003fd3188035fe18c4001ffc862000ffc4310007fd2188003fe10c4005bf9822002ffea1100177f508800bff2844005ff5422002efaa110017fc508800bffa044005ff9022002ffa8110017fc408800bff9844005ff8c22002ff46110017fd3088001fc9844005ff0c22002ffe4110017ef2088003fd9044005ff0822002ff04110067ff65480337fb2a4019ff99520025fcca90067fd65480337eb2a4019ff19520025f8ca90063ff64480317fb224018ff9912001dfcc890063fd64480317eb224018ff1912001df8c890063ff5448031bfaa24018ff951200c7faa8900637d5448031fe2a24000ffd8d20005fec69005ffe63480057f31a4000ff58d20005fac69005ffc63480057e31a4019ffd4d200bffca690067fd534802ffe29a4018ffd0d200bffc8690063fd434802ffe21a4005bfd892000ffea490007fe5248003fea924001ff1492000ffe8490007fe4248003f72124001ff509200c7da8490007fc4248003ff9924001ff8c92000fdc6490007fd3248001f69924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148033ffa8a4019ff94520006fca290067fd5148033fe28a4019df145200c7fe8290063fe4148031fea0a4018ff105200bffe6290003fe3148001fe98a4017ff0c52000ffe4290007ef2148003ff10a4001ff48520007da4290007fc21480037fb024019ffd41200cefea090017fe5048033fea824000df5412002ff8a090063ff404800bff2024018ff5012002ff8809005fff304800bff1824000fe8c120007fa6090003f9304800bfe1824001ffc812000ff64090017fe204800bf71024005ff0812002fd8409000
  | 3 => 0xea1aa024df10d50006fec4a808f7e6254001beb12a023df1895012efe84a808f7e425404bbea12a023df10950126fe64a808f7e3254001be992a023df0c950006fec2a80037e6154001beb0aa000df18550004f8c2a80977f415404bbf20aa025df5055012ef882a80937f3154001bf18aa000df4c550126f862a808f7f2154001bf10aa000df4855011ef842a80137f60540093fb02a004ded815012efe80a80177e405404bbea02a005df10150126fe60a80177c3054047bf902a005df0815002ffecb18016ff658c00bff32c6004bf9963002efccb180127e658c00bfeb2c6022bf5963002efacb180027d658c00bfe32c6005bf1963002ffec918016ff648c00bff3246003bf9923002ffac918086fd648c00bfe3246005bf1923010ffea9180877f548c043ff2a46021ff5523010efaa918087fc548c0057eb1c6002ffd4e30017fca71800bfd538c005fe29c6002ffd0e30017fc871800bfd438c005fe21c6005ffd8a3002ffcc518006fe628c00bfeb146000bf58a3002ff8c518016fc628c045ffa946020ff94a30117faa518083fc528c043ffa146020ff90a3010ffa8518083fc428c005ff9946002ff8ca30017fa651800bfc328c00bffb0c6005ff98630005fcc318017fd618c0017eb0c6005ff18630117fea31808bfe518c001bf28c6022ff54630117f8a31808b7c518c043ffa0c6021ff9063010ffa8318087fc418c005ff98c6002ff8c630017fa631800bfc318c041ff90c6000ff88630007fa4318083fc218c00b7f3046005ffd423002efea118017fe508c00bfea846005df5423002ff8a118017ff408c00bff2046005ff5023002ff88118017ff308c00bef9846002fecc23002ff86118017f8308c00bff9046005ff082300fffeca9807eff654c03fff32a6004bf995300fffaca9807efd654c03ffe32a6004bf195300f7fec89807aff644c03dff3226003bf991300f7fac89807afd644c03dfe3226003bf191300f7fea89807b7f544c03dff2a2601eff551300f6faa89807bfc544c00b7fb1a6002ffd4d30017fca69800bfd534c005fe29a6002ffd0d30017fc869800bde434c005fea1a601ef750d30017f88698003ff624c0017fb12601dff9893000dfcc498003fd624c03bfe3126001bf189300fffea498077fe524c03ffea92601dff149300f7fe8498077fe424c03dfea12601dff10930017fe649800bdf324c005ff1926002ff4c930007ba649800bfc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6000bf185300fffea29807ffe514c001bf28a601fff545300fff8a29807f7c514c03dffa0a601eff905300f7fa829807bfc414c005ff98a6002f7cc530017fc629800bfd314c001ee98a6002ff0c5300effe4298003fe214c001fe90a601dff08530015fec09807fff504c03fbfa826005ff941
  | 4 => 0x803fc604c40b7e302622effd4131176fea0988bbfe504c45dfea82622eff1413116ffe80988b7fe404c45bfea02622dff10131017fe609880bdf304c405fe182622cffc8131167f8409881bff65884577fb2c422bff99621025fccb108affd65884577eb2c4206ff19621025f8cb1081bff64884557fb24422aff9922101dfcc9108abfd64884557eb244206ff1922101df8c9108abff5488455bfaa4422aff95221157faa9108ab7d5488455fe2a44206ffd8e21005fec7108a7fe63884057f31c4200ff58e21005fac71081bfc63884057e31c422bffd4e2114ffca7108affd5388453fe29c422affd0e2114ffc87108abfd4388453fe21c4201bf58a2100ffea510807fe5288403fea944201ff14a2100ffe8510807fe4288403fea144201ff10a2100ffe6510807fe3288403fe9944201ff0ca2100dfcc3108afff518840dff28c4206df9462115ffaa31081bfc518840dbe28c422affd0621037fc83108abfd418840dfe20c4229ffcc621037fc6310803f63188401fe98c4200fd4c621037f86310807ff2188403f790c4201fdc8621037f84310807f4218840dffb044200ff9822102dfcc110803fd60884017eb044206ff1822115ffea1108af7f5088457ff284422bff5422115ff8a1108abff4088455ff204422aff50221157f881108a7ff3088453fe1844201ffc822100ff841108a3ff65484517fb2a4200dfd9521004feca908a3fe65484097f32a4228ff59521145faca908a3fc65484097e32a4228df19521024f8ca9089fff644844f7fb224227ff9912101dfcc89089ffd644844f7eb224227ff1912101df8c89089fff544844fbfaa24227ff9512113ffaa89089f7d544844ffe2a24200ffd8d21005fec69089bfe63484057f31a4200ff58d21005fac69089bfc63484057e31a4228ffd4d21137fca6908a3fd534844dfe29a4227ffd0d21137fc869089ffd434844dfe21a4201bfd892100ffea490807fe5248403fea924201ff1492100ffe8490807fe4248403f72124201ff5092113fda8490807fc4248403ff9924201ff8c92100ffa6490807fc32484037fb0a4228ffd4521147fca2908037e5148451fea8a4228ff14521146f8a29089fff414844fff20a4227ff5052113ff8829089bff3148401ff18a4200fd8c521007fa6290803f5314844dfe18a4201ffc852100fee4290807fe2148401f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024205bf18121147fea0908a37f5048451ff2824228ff54121147f8a09089fff404844fff2024227ff5012113ff8809089bff304844dfe1824201ffc812100fde4090807fc204844bbfb22a0259fd915012efcc8a80977d645404b3eb22a025df19150006fec6a80937e6354001beb1aa024df18d5012efe86a80937e435404bb
  | 5 => 0xc132017f86099007ff204c803f79026401ff08132036fec9288d27f6494469bf324a234df592511a4fac92881b7c649440dbfb1ca233df98e51006fac72881b7c6394469bfa1ca233df90e511a6fa87288cf7c439440dbfb14a232df98a51006fac52881b7c6294469bfa14a232df90a511a6fa85288cb7c4294467bf994a232df8ca51006fa65288cb7c329440dbf30ca2049f98651026ecc3288d37f419440dbf20ca234df50651036f883288cf7f319440dbe18ca232dfc8651036f8432881b7f6094401bf304a200df58251004fac12881b7c6094469bfa04a234df902511a6fa81288d37c4094467bf984a233df0c251196fe41288cb7c209440dffb2c6231bfd963118ffccb18812fe658c463feb2c6231bf59631037f8cb18812fc658c40dffb246230bfd9231187fcc91880efe648c461feb246230bf59231037f8c91880efc648c461ffaa46230dfd5231187fca9188c3fd548c461beaa46230ff15231015fac71880bff538c405ff29c6202ff54e31017f8a71880bff438c405ff21c6202ff50e31017f8871881bff628c45fff3146201bf98a31007fac518802fd628c40dfe3146201bf18a3118ffea5188bffe528c463fea94622fff14a31187fe85188bffe428c461fea14622fff10a31017fe651880bfe328c405fe9946202ff0ca31015fcc3188c7ff518c40dff28c6206df9463118ffaa31881bfc518c40dbe28c6230ffd0631037fc83188c3fd418c40dfe20c6202ffcc631017be631880bf7318c40dfe18c6202fd0c63117ffe431881bfc218c40dffb046200ff9823102dfcc118803fd608c4017eb046206ff1823118ffea1188c77f508c463ff2846231ff5423118ff8a1188c3ff408c461ff2046230ff50231187f8811880bff308c405fe184622fffc823117ff841188bbff654c45d7fb2a6200dfd9531004feca988bbfe654c4097f32a622eff59531175faca988bbfc654c4097e32a622edf19531024f8ca988b7ff644c45b7fb22622dff9913101dfcc8988b7fd644c45b7eb22622dff1913101df8c8988b7ff544c45bbfaa2622dff9513116ffaa8988b77d544c45bfe2a26202bfd8d31017fea69880bfe534c405fea9a6202ff14d31017fe869880bfe434c405ef21a6202ff50d3116fba869880bfc434c401ffb126200bfd8931167fcc498806fe624c401feb12622cff1893100df8c4988bbff524c459ff292622eff54931167f8a4988b7ff424c459ff212622dff50931167f8849880bff324c405ff1926202ff4c931017f8649880aff614c45dffa8a622eff94531006fca2988bbfd514c45dfe28a622edf1453116ffe82988b7fe414c45bfea0a622dff10531017fe629880bf7314c405ff18a6200f78c531017f8629880bdc314c405fa18a622cffc8531167f84298803ff604c4017fb026200ff98131007fac098
  | 6 => 0x40081080000601401400801024040000090000040000201a0180380a000000010010020100180002c000000070040200080301001c0000701e004038020100040380000a0200100001201008801006008038040020040001a012040018090000040a004008010008000060140b003000000000280080680a81d00a01c088140000100000000800000002012008038130120000700f0080480f81e03c02002006036000018010040040000d0000200000000400400007000024020000120080080800c01c000020040500100401205c028000000000000300804800804006014018070000080481c00000009018014024040010140440681e0060000180a01c0000000000002811801028010020000580080a80500e008088020040000f009000018008020120b8000010020280100003204c01021004000060000020200201200005c04016004004008000020340a80401c01c0000000a000010010000341302904c024048000080300100c04c0100480001a0000b80e01800c03008000004018000060000e8000040000080f0240140500d01200c050000020000100502600c0000600a000058060040100980000c010010000000200380400002404823000008070010020080880000200000000002000008430040080480100807c088130000000001001a038008000000000000c0080140102301203c0580f0000800000100600000801006000008040000100180301e01c050000120200080c0080140280700a03c0400500e0000382100001806800006044068150000040480000000c01813000064020000000140103700200000003004004048000040000000300001c02800000028010021b7feca990daff654c801bfb2a64009fd95321b7fcca99012fe654c86dfeb2a6436bf595321b7f8ca99012fc654c86dbe32a64049f195321affec8990d6ff644c86bff3226403bf991321affac8990d6fd644c86bfe3226403bf191321affea8990d77f544c86bff2a26435ff551321aefaa8990d7fc544c8037fb1a6402ffd4d32017fca69900bfd534c805fe29a6402ffd0d32017fc869900bfd434c805fe21a6401bfd893200ffea499007fe524c803fea926401ff1493200ffe8499007fe424c803fea126401ff1093200ffe649900bef324c803ff1926401f78c93200ff86499007dc324c803f61926401f30c932007fec299002ff614c801ff30a6400ff58532007f8c299002fc614c86dffa8a6436ff945321b7faa2990dbfc514c86dbe28a6435ffd05321affc82990d7fd414c86bfe20a6402ffcc532017f86299007ff214c803fe10a6400ffd8132005fec099003fe604c801feb026400ff1813202df8c0990dbff504c86dbfa826436ff941321b7faa0990dbfc504c86bffa026435ff901321affa80990d7fc404c805ff9826402f7c
  | 7 => 0xe000000094c82a0000007580000000d20000d00007143c829835400000000000026e0000000007a400090e0008987de3be23a0b067e114a2e0287940007c2000ac6000000032848aa0a8c9360003d46ec4443580004a61e82a27e888c45400000061e22800073a3765de000abc9425c8a342fe0d40000007082dca504049960005ec000a943fa74a146520050a660000002c2686ae06b4ae40f05949f095a0009de3f08a8b0e9e60082c483295c254a366500008e87823cc5c63ee9c634e00033a6bc000a6866e0000000006047786f87ee67217808c8b88d68900007d676800092c5da7a62089940aa8209ea2442764d47260006101a22fc3847060003f6a780002ae5467165765989fc4663bab06ad600012603e6f681e3eca2465a3dc64483e78863600062612e53011c21000000003803069e4fc5323c200042a97000000050e87e9042420000001966e40ac41e1860b23900000020527b01481a448e5423720002e6000000a9ea1e9180005ee0ca7660008681dca40b0087a0008604220007c644a33227e39270e8b01ea6609a87fc77257200000011e0005e20000341e6a568386ba9600004be0000008f68be1882682be6d60008083da0006e2a100001ee9ee75c0000000000820003ea0ccaa4a3864a0000007fa000926416af22887f262a6fa044a1412243800013600035c47672463e68c4065042f047c98692e58e35600003646e0000005aa0005e629c0000001d600088e77e62c0004dc49022e20e6d40006224d60000005d20007d408435a0000001160000001faa2002a00052c000af6000000000b089b80003225140007a0000000aac0001fca9a000a060009fa00073886e07e102a5e72a00074400001a9404fe0000006f44720009f2656000966000a6a0008fe0b4a462d04282d809055817c6cc00068a82640e1989888ba14204c8dc51a43480695e22c9d81e22c660200a7e4470a7c66a4822f213089c000ae6080a86a2aa5c000340aee9c824a7e2156062000a8089e47459a06e1625caa8e64c0000000006828faaa893a0000000007b431400070c60a00078c8560000000008a433c4680000000000000008ac0008742c8000000350544000382266000ad200096c7b600e0f68da0005060000003ca00044253c534aba8245bc00000050000045800000039400000014a9aa2e02cc054afa84c5ac9748b2a6c55a1f62800000004c25e4a280004dea5a4f897a00070200004a00048aae81404246ea7427ca76286cad82860000003b0000000000000000a600003bc00029a4b63800c60004ec53871a4aa00000021e00000071c0000000002c00009580f2000000000000a0c00035e0000006b236008a1800000940001766ac0000006086b86ce6c84020000080100a0000200000202600c0100400c00c0200b08e0000680100400
  | 8 => 0x40009b024c6fc250af813e0009f40000000008d00000000008580007800006c06dc17e2380000de00079c6d21928c656223681009274e3865f24400000000000000003e00000000000000004940861b656a1c25a64500be6a2a1c29417215806423e2ca76468e28c00000000077474061483a4620007ae0007048fc90a4f0a9642e26c21402600011284483062422a47a6586481941844f66666a4a480988e60000004da2340e20e000082e0881b80004e60000000000c08e41c436aa3c17400044eacc58a2a021c0001ec1c64126340002740000006400000000003de48600000092a000000000a327560000003984cc0002ba00080c94a2784c48f274c1f02ac8c206c98c2f640c82216016a8ec82c0e44568e28362d48d82002269547b89345d80000003fc8ca85ea7431844c01e77a1064ac5e03c405a688138a181c814e0721baa26310adc892366a307d84a091646409e34a7849d29721da61c8661aa9243d68147709484ca0002aa37e16c25c7da00436c91a2e86127cc97e89464e75a4969fe26249886272817a0005188a6a2255e76e9be000a8200008e9e28d46527ec1bc6a85280748b48f43288841acb0299a6803ce976a00a080a04f292031c59c8002400b85ce09a9ae44665c19c4a23361283aa4b4302a3a9b23b203aa8a7485405b62927767903a075e63c04200090c3f85ba63a5127985508463c6a0a27c9562bc45c16e13441a5d6afc76c0000000004ce0007b232e1b29c478a71000000000053600079e00000000000000000062ea6e69c0007f47500005a2548aa60000000005920000000006427000003a40006a660e0fa0120000007127a200000000009c5e817057a6921080000004c093e6380000006686f2a926b61b400000000010401cad030a5c473c9a252a00049cade42c05800099010c3b8ac843a910b0a6164e25a876a2b40001e069a0e622494e000478a042f86783a86c24d02e21f2ab878666c49a6c69dc0000000005ea0006aa7d2ac49e40003380008f848000034c8a20000000000000001320000007c0a7a31a39a27a4180e80f400c04015406065e8721188aa20a43e5829e81de72caa2a588783249ba6da0a68f07bc8d21a666202c11a31238a0000a2ada00088a02e2162585745220001be81c45a84a56c89636e85400091c3462484007dc9cea987ac41c3a63c00000006960002d296e0000009f80000000000000003700d6a9086a0a49020a8000232100a028b66ca0009780002de0003e401886415205e0000007fe0003f48880000000001a800000024e59e7d00001c00000000000008c41f40ce31e330000a1280e2640009ec676aca25e6fe84ead49f62a849e5b20ae4105d00004a847e9080d813c296000000a1a378ac053e00084270a6a06d046c4d228e46aaea54a720abe50c40a2840002b28
  | 9 => 0x78e000ac22b038815c54c15e63285006a2520000006905080000684480000c80007609823e89bc93253a07a5f65f43269ca34200067a796a640000002ec1ca000000000000492aae8cc000000962396000000968000816000000b0c20c8822209a452ea4430040893824692248813a2da99830c2061641fe0460706ae000000000a7605c15059083c63007c80218a0ee5c094427015a51c5020669001cc3f2ace56e43019a4bc3e67ea9daae20005ae4fa94691e0205a0ab00b610a2a40766be3744c604e9d41445540006f0000a3e98a96aaaa4eea4a4b2a84b046b08a03160000ba4ba56018c20210e19e4364149b42ea6e602238e4b02f45783d89127e633e7f05840001ae000568000694a886e000000072298000026085a81812c8ce18e620752a4e078a9c3521240000000000000002040002123d058c0da0004521820f87ba0107be5f04b85dc48400051050a3082901b04a426a7c43fe0008ae32a0969c077c4ae9b645e6ee51e3207f6000566166afe0000007aa55c4e80c25881f81907f80009a00ea006000674a624264e000042048c87c306618000552a0e28a00099e3aeaf08806d80000000008bc00000043280a1e40dc8c00000000000004e429e0000004605be73e0000003b6000a1671e7340000000000002560c421a2722e46541680ec75489a99267c3628763d230e59679a9a65a497ca527a82faab61206983687e0000000000af4a7200000023c23099c3045800001d437c4c89282b657e6c40008ee600000a709509309649cc5fa000730a4c6063441ce2ee000aec9845f83ac00000083400085200038c7360006849065cc0000009142b884073266400079234885c61a8c89d04d81d80008127c89525b84f40fe6462ce000a7e54e586870110a54ab2a4257067082898e7466280002d614c8de0161d09d6056ab457c3a26e82228ea0000008043642180000245fc00037a000000a2c5245d45165b00002a63e20009c23b455643c0004ea9e00fc00000032c6de00000000000071872e5c200000012a5b439c1a003c0bc9ac8861d27ce00000000052639e28260c00001456404893c5fe00081a00000000025a33
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd5458810004ff7358810014fe7358810014fc735881002cff725881002eef7258810006ef525881003eee5258810006ed525881003eec5258810006ef425881003eee4258810006ed425881003eec4258810006ef325881003eee325881003eec325881000cff7158810034fe715881000cfd7158810034fc71588100367e51588100367c5158810036ee2158810036ec215881002cff705881002cfe705881002cfd705881002cfc705881002e7f505881002e7d505881002eee205881002eec205881002ef7105881002ef51058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef54588100066f5458810006ee5458810006ed54588100066d5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881003eef7158810036ee7158810036ec7158810006ef5158810036ee51588100366e5158810006ed5158810036ec51588100366c5158810006ef4158810036ee4158810006ed4158810036ec4158810006ef3158810036ee3158810036ec315881002eef705881002eee705881002eed705881002eec705881002eef505881002e6f505881002eee505881002eed505881002e6d505881002eec505881002eef405881002eee405881002eed405881002eec405881002eef305881002eee305881002eed305881002eec305881002eef105881002ee7105881002eee105881002eed105881002ee5105881002eec1058810004ff764c81002cfe764c810004fd764c81002cfc764c8100057f754c8100557c754c8101b67e654c8100067d654c8101aebe644c810006bd644c810016de634c810006dd634c81000eee624c810006ed624c81003fcc324c8100acff764c4100057f754c4100557c754c4101767e654c4100067d654c41016ebe644c410006bd644c410016de634c410006dd634c410166ee624c410006ed624c4100aef6614c4100a4ff76484100057f75484100557c75484101467e65484100067d654841013ebe6448410006bd6448410136de6348410006dd634841000eee6248410006ed62484100a6f6614841002dfb7644010006fb7644010004fb76440100077b75440101c778754401002f7a654401002f796544010007bb74440101bfb8744401002efb644401002fba64440101bef9644401002fb96444010006b964440101bf7b54440101bf79544401002fda634401002fd9634401002fea624401002fe9624401002dfb714401002ff37144010036fa614401002ff261440100377a5144010037f251440100377251440101c7f15144010037785144010037f241440101bff14144010
  | 1 => 0x9010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bc325901004ebf7159010036be715901004ebd7159010036bc7159010006bf5159010036be51590100363e5159010006bd5159010036bc51590100363c5159010006bf3159010036be3159010036bc3159010006bf2159010036be2159010036bc215901002ebf705901002ebe705901002ebd705901002ebc705901002ebf505901002e3f505901002ebe505901002ebd505901002e3d505901002ebc505901002ebf305901002ebe305901002ebd305901002ebc305901002ebf205901002ebe205901002ebd205901002ebc205901002ebf105901002eb7105901002ebe105901002eba105901002ebd105901002eb5105901002ebc1059010004ff7558c10024fe7558c10004fd7558c10024fc7558c10004ff7458c1001cfe7458c10004fd7458c1001cfc7458c100067f5458c100067d5458c1002cff7358c1002edf7358c10006df5358c10046de5358c10006dd5358c10046dc5358c10006df4358c10046de4358c10006dd4358c10046dc4358c10004ff7258c1000cfe7258c1000cfc7258c10046df3258c10006de3258c10046dc3258c10014ff7158c10034fe7158c10014fd7158c10034fc7158c100367e5158c100367c5158c10036de3158c10036dc3158c1002cff7058c1002cfe7058c1002cfd7058c1002cfc7058c1002e7f5058c1002e7d5058c1002ede3058c1002edc3058c1002ef71058c1002ef51058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c100065f5458c10006de5458c10006dd5458c100065d5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c10046df7158c10036de7158c10036dc7158c10006df5158c10036de5158c100365e5158c10006dd5158c10036dc5158c100365c5158c10006df4158c10036de4158c10006dd4158c10036dc4158c10006df2158c10036de2158c10036dc2158c1002edf7058c1002ede7058c1002edd7058c1002edc7058c1002edf5058c1002e5f5058c1002ede5058c1002edd5058c1002e5d5058c1002edc5058c1002edf4058c1002ede4058c1002edd4058c1002edc4058c1002edf2058c1002ede2058c1002edd2058c1002edc2058c1002edf1058c1002ed71058c1002ede1058c1002edd1058c1002ed51058c1002edc1058c10004ff7558810024fe7558810004fd7558810024fc7558810004ff745881001cfe7458810004fd745881001cfc74588100067f54588100067
  | 2 => 0x12e7c64541101e73c645411012e3c64541100067f63541101267e63541100067d63541101267c63541100067f625411011e7e62541100067d625411011e7c62541100077771541100357c715411000774715411000574715411002e7f61541101e77641541101e775415411000776315411000775315411000776215411000775215411002d7f705411007f7b705411002e7f605411002f7a40541101e779405411002f7a305411002f7a205411002f76105411002f74105411002f78105411002f701054110014ff764c11006cfd764c110014fc764c1100067f654c1100fe7c654c110006bf644c1100f6bc644c110006df634c110016dc634c110005f7714c110005f4714c110007d5314c11000779504c11000cff7648110064fd764811000cfc76481100067f65481100ce7c6548110006bf64481100c6bc6448110006ef624811000eec6248110005f77148110005f47148110007e521481100077950481100357f75c41100357c75c41100067f65c41100b67c65c4110006bf64c411005ebc64c411002df671c411002ef761c41101df7b50c41100077950c411002dfa76c411002efa76c411002cfa76c41100377b75c41100377875c41100077b65c41101df7865c4110035fb74c41101d5f974c4110007bb64c41101cfb864c41101cf7b54c41101cf7954c411002dfa71c411002efb61c411002ff361c41100377a51c41100377851c4110037f241c41101cff141c4110037f231c4110007f131c4110037f221c4110007f121c41100067f74594100047f74594100067e74594100067d74594100047d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067e32594100067c32594100567f71594100367e71594100347e71594100567d71594100367c71594100347c71594100067f41594100367e41594100067d41594100367c41594100067f31594100367e31594100367c31594100067f21594100367e21594100367c215941002e7f705941002c7f705941002e7e705941002e7d705941002c7d705941002e7c705941002e7f405941002e7e405941002e7d405941002e7c405941002e7f305941002e7e305941002e7d305941002e7c305941002e7f205941002e7e205941002e7d205941002e7c205941002e7f105941002e7e105941002e7d105941002e7c1059410006bf7559010006be75590100063e7559010006bd75590100063d7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf725
  | 3 => 0xd70945100367f609451025f7a409451025f794094510257761094510037741094510094fe768c5100067f658c51018e7c658c510006bf648c510186bc648c51003776518c51003774518c510005f6768c510096f6768c51000777658c51024774658c51024df7748c51024df5748c510007b7648c51023fb4648c51023f77548c51023f75548c51006df5738c510016f6638c510016f4638c510005f5728c510006f7628c510006f5628c51002df6708c51002df4708c510036f7608c51024777508c51023ff2408c51023ff1408c51002cfc764c5100057f754c51007d7c754c5100067f654c5101767c654c510006bf644c51016ebc644c510006df634c510016dc634c51000776514c51022f74514c51006fd4314c510005fb704c51002df8704c51002df4764c510016f4764c51002cf4764c51000777754c51022f74754c51000777654c51022f74654c510235f7744c510235f5744c510007b7644c510227b4644c51022777544c51022775544c51006df7734c510007d7734c510007d7634c510016f6634c510016f4634c51006fd4634c51006fd6434c510227d5434c510005f7724c510006f7624c510006f5624c510007f3704c51002df6704c51002df4704c510007f0704c51022f77504c510227f2404c510227f1404c51006fd7304c51008cfe76885100067f658851015e7c6588510006bf6488510156bc6488510037765188510037745188510005f6768851008ef6768851000777658851021774658851021df7748851021df57488510007b7648851020fb4648851020f77548851020f755488510005f77388510005f57388510006f76388510006f56388510065f5728851000ef6628851000ef4628851002df6708851002df47088510036f7608851021777508851020ff2408851020ff1408851002cfc76485100057f754851007d7c75485100067f65485101467c6548510006bf644851013ebc6448510006ef624851000eec62485100077651485101ff745148510067e42148510005fb704851002df8704851002df4764851000ef4764851002cf476485100077775485101ff7475485100077765485101ff746548510205f77448510205f57448510007b764485101f7b464485101f77754485101f7755448510005f77348510005f57348510006f76348510006f56348510065f77248510007e77248510007e7624851000ef6624851000ef46248510067e46248510067e642485101f7e54248510007f3704851002df6704851002df47048510007f070485101ff7750485101f7f240485101f7f14048510067e720485100267f76541100b67e765411007e7d765411007d7c76541100267c76541100247c76541101ed7f74541101ed7d74541101e67f64541100073f64541100063f645411012e7e64541101e67d6454110
  | 4 => 0x8d10034fe71d8d1002cfd71d8d10034fc71d8d100067c51d8d1006edf31d8d1002cfe70d8d1006cfd70d8d1002cfc70d8d100067f50d8d1006edf30d8d100057f7558d1007d7c7558d100067f6558d100067c6558d10005bf7458d10075bc7458d10006bf6458d10006bc6458d1006edc6358d10005ef7258d10065ec7258d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d10004fd7458d1001cfc7458d10006bc7458d1001cbc7458d100067f5458d100067d5458d1006cff7358d10006df7358d1006ede4358d10006dd4358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d10094ff7158d10006f77158d100067c5158d100acff7058d10006fb7058d100067f5058d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910066ee62d8910004ff75d8910024fe75d8910004fd75d8910024fc75d8910004ff74d891001cfe74d8910004fd74d891001cfc74d89100067f54d89100067d54d8910014fe73d8910004fd73d8910014fc73d8910006ef32d8910066ec32d8910034fe71d891002cfd71d8910034fc71d89100067c51d8910066ef21d891002cfe70d8910064fd70d891002cfc70d89100067f50d8910066ef20d89100057f755891007d7c75589100067f65589100067c6558910005bf7458910075bc7458910006bf6458910006bc6458910005df735891006ddc7358910066ec6258910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe7458910004fd745891001cfc7458910006bc745891001cbc74589100067f54589100067d5458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc7358910064ff7258910006ef7258910066ee4258910006ed425891008cff7158910006f771589100067c51589100a4ff7058910006fb70589100067f5058910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c91007d7c754c9100067f654c9101b67c654c910006bf644c9101aebc644c910067cc324c9100057e76945100367e769451009c7e76945100357f74945102657d749451025e7f64945100073f64945100063f64945101a67e649451025e7d64945101a67c649451025f3c64945101a63c64945100067f639451019e7e63945100067d639451019e7c63945100067f62945101967e62945100067d62945101967c62945100357e71945100377671945100367f619451003776419451025f75419451007d7
  | 5 => 0x63c64d95100067e63d95100067c63d95100067e62d95100067c62d95100357c71d95100077641d95100077541d95100077a40d95100077940d95102577610d95102577410d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067c32d95102567f71d951007e7e71d95100347e71d951007e7d71d951007e7c71d95100347c71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f31d95100067c31d95100067f21d95100067c21d95100067f70d95102567e70d951007e7d70d951007c7d70d95102567c70d95100067f40d95102567e40d95100067d40d95102567c40d95100067f30d95102567e30d95102567c30d95100067f20d95102567e20d95102567c20d95102567e10d951007e7d10d95102567c10d9510075be76d9110076be76d911001cbe76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110006be62d9110006bc62d911026fb771d9110077b471d91100073c51d9110007bb70d9110077b870d91100073f50d911026fb610d911026fb410d9110006bf75d91100063f75d9110006be75d9110006bd75d9110006bc75d91100063c75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bc32d911026ebf71d9110076be71d9110076bd71d9110076bc71d9110006bf51d9110006be51d9110006bd51d9110006bc51d91100063c51d9110006bf31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d911026ebe70d9110076bd70d911026ebc70d9110006bf50d91100063f50d911026ebe50d9110006bd50d911026ebc50d9110006bf30d911026ebe30d911026ebc30d9110006bf20d911026ebe20d911026ebc20d911026ebe10d9110076bd10d911026ebc10d9110014fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d1006ede63d8d10004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d10004ff74d8d1001cfe74d8d10004fd74d8d1001cfc74d8d100067f54d8d100067d54d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d1006edc32d
  | 6 => 0xe71596100067d715961009e7c71596100067f41596100067e41596100067d41596100067c41596100067f31596100067c31596100067f21596100067c215961002e7f705961002e7e705961002e7d705961002e7c705961002e7f405961002e7e405961002e7d405961002e7c405961002e7f305961002e7e305961002e7d305961002e7c305961002e7f205961002e7e205961002e7d205961002e7c205961002e7f105961002e7e105961002e7d105961002e7c1059610004ff7558e10024fe7558e10004fd7558e10024fc7558e10004ff7458e1001cfe7458e10004fd7458e1001cfc7458e100067f5458e100067d5458e1002edf7358e10096de4358e10006dd4358e10004ff7258e1000cfe7258e1000cfc7258e10096df3258e100067c5158e10096df3158e1002cfc7058e1002e7f5058e1002e7d5058e1002ede3058e1002edc3058e1002ef71058e1002ef51058e10004ff7558a10024fe7558a10004fd7558a10024fc7558a10004ff7458a1001cfe7458a10004fd7458a1001cfc7458a100067f5458a100067d5458a10004ff7358a10014fe7358a10014fc7358a1002eef7258a1008eee4258a10006ed4258a1008eee3258a100067c5158a1008eef2158a1002cfc7058a1002e7f5058a1002e7d5058a1002eee2058a1002eec2058a1002ef71058a1002ef51058a10004ff764ca1002cfe764ca10004fd764ca1002cfc764ca100057f754ca1009d7c754ca101b67e654ca100067d654ca10016de634ca10006dd634ca1000eee624ca10006ed624ca1008fcc324ca102557d76946100367d769461007c7d76946100357f749461028d7d74946102567f64946101a67e64946102867d64946102567c64946102567f639461019e7e63946100067d63946102567c63946102567f62946101967e62946100067d62946102567c62946100357e71946100377671946100357f70946102557d70946100367e60946102577a409461028779409461003777109461003778109461006cfd768c61018e7e658c6100067d658c610014ff764c61002cfc764c6100057f754c61009d7c754c6101767e654c6100067d654c610016de634c610006dd634c610005fb704c61002df8704c610064fd768861015e7e65886100067d658861000cff764861002cfc76486100057f754861009d7c75486101467e65486100067d654861000eee6248610006ed6248610005fb704861002df8704861002df976c4210036f976c42100377b75c42100377875c421002f7a65c421002f7965c4210035fb74c421027df974c42102777b54c42102777954c421002ff271c42100377a51c42100377851c421007d7e76d951007e7e76d95100247e76d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d9510
  | 7 => 0xc7100057f754c7100b57c754c7100367f654c7100367c654c710036df634c710036dc634c71003776514c71003774514c710037d4314c710005f7764c710046f7764c71000777754c7102d774754c71003777654c71003774654c7102e5f7744c7102e5f5744c7102df77544c7102df75544c710037d7734c710037d7634c710016f6634c710016f4634c710037d4634c7100afd6434c7102dfd5434c710005f7724c710006f7624c710006f5624c71002df6704c71002df4704c7102d777504c7100afd7304c71002df57688710036f5768871002cf57688710037776588710037746588710035f774887102cdf574887102c77754887102c7755488710035f77388710005f57388710036f76388710006f5638871000ef66288710037e66288710037e56288710036f4628871002df67088710037f27088710037f1708871002df470887102bf77508871003cff76487100057f75487100b57c75487100367f65487100367c6548710036ef6248710036ec6248710037765148710037745148710037e42148710005f7764871003ef776487100077775487102a77475487100377765487100377465487102b5f774487102b5f574487102af7754487102af755448710005f77348710005f57348710006f76348710006f56348710037e77248710037e7624871000ef6624871000ef46248710037e462487100a7e642487102afe5424871002df6704871002df470487102a77750487100a7e720487100267f76543100357c76543100267c76543100347c765431029d7f745431029d7d74543102967f645431012e7e64543102967d645431012e7c64543100067f63543101267e63543100067d63543101267c63543100067f625431011e7e62543100067d625431011e7c62543100077771543100357e71543100357c715431000774715431003574715431002e7e615431029776415431029775415431000776315431000775315431000776215431000775215431002d7f70543100b77b705431002e7d605431002f76105431002f7a105431002f741054310014ff764c310034fc764c3100067f654c3100fe7c654c310016de634c310006dd634c310005f7714c310035f4714c310007d5314c31000cff7648310034fc76483100067f65483100ce7c654831000eee6248310006ed6248310005f77148310035f47148310007e521483100067f74596100047f74596100067e74596100067d74596100047d74596100067c74596100067f73596100067e73596100067d73596100067c73596100067f43596100067e43596100067d43596100067c43596100067f72596100067e72596100067d72596100067c72596100067f42596100067e42596100067d42596100067c42596100067f32596100067e32596100067c325961009e7f715961009e7
  | 8 => 0x367d72d97100367c72d97100067f42d97100067e42d97100067d42d97100067c42d97100067f32d97100067e32d97100067c32d97100367e71d97100367671d97100367f41d97100367e41d97100367d41d97100367c41d97100367f31d97100367e31d97100367c31d97100367f21d97100367e21d97100367c21d97100367d70d97100367970d97100067f40d97102567e40d97100067d40d97102567c40d97100067f30d97102567e30d97102567c30d97100067f20d97102567e20d97102567c20d97100367c10d9710034ff75d8f10024fe75d8f10004fd75d8f10034fc75d8f10034ff74d8f1001cfe74d8f10004fd74d8f10034fc74d8f100067f54d8f100067d54d8f100acfd73d8f1000cfe72d8f10004fd72d8f10034fc72d8f10036f671d8f100367e51d8f100367c51d8f10036df31d8f10036f970d8f100067f50d8f10014ff7658f100057f7558f100b57c7558f100367f6558f100367c6558f10036dc6358f10004ff7558f100067f7558f100047f7558f10024fe7558f10004fd7558f10024fc7558f100067c7558f100247c7558f10004ff7458f1001cfe7458f10004fd7458f1001cfc7458f100067f5458f100067d5458f10036df7358f100aede4358f10006dd4358f10004ff7258f1000cfe7258f1000cfc7258f1002cfc7158f100367e5158f100367c5158f10036de3158f10036dc3158f100067f5058f100aedf3058f10034ff75d8b10024fe75d8b10004fd75d8b10034fc75d8b10034ff74d8b1001cfe74d8b10004fd74d8b10034fc74d8b100067f54d8b100067d54d8b10014fe73d8b10004fd73d8b10034fc73d8b100a4fd72d8b10036f671d8b100367e51d8b100367c51d8b10036ef21d8b10036f970d8b100067f50d8b1000cff7658b100057f7558b100b57c7558b100367f6558b100367c6558b10036ec6258b10004ff7558b100067f7558b100047f7558b10024fe7558b10004fd7558b10024fc7558b100067c7558b100247c7558b10004ff7458b1001cfe7458b10004fd7458b1001cfc7458b100067f5458b100067d5458b10004ff7358b10014fe7358b10014fc7358b10036ef7258b100a6ee4258b10006ed4258b1002cfc7158b100367e5158b100367c5158b10036ee2158b10036ec2158b100067f5058b100a6ef2058b10004ff764cb10034fe764cb10004fd764cb10034fc764cb100057f754cb100b57c754cb100067f654cb101b67c654cb100a7cc324cb1002df5768c710036f5768c71002cf5768c71003777658c71003774658c710035f7748c7102fdf5748c7102f777548c7102f775548c710016f6638c710037d6638c710037d5638c710036f4638c710005f5728c710036f7628c710006f5628c71002df6708c710037f2708c710037f1708c71002df4708c7102ef77508c710044ff764
  | 9 => 0xe71945200cf7671945200067f61945200367c61945201976f21945200057d70945201967f60945201977b20945202576e20945202576c2094520197782094520004fe768c520004fd768c520034fc768c520006df638c520016dc638c52000dee728c520005ed728c520004ff764c520004fe764c520004fc764c5200057f754c5200cd7c754c52000dee724c52002cec76485200076f754852033f6c754852034def744852034ded7448520346ef6448520346ed64485203476f54485203476d5448520005ef7348520005ed734852000def714852000fe77148520007e76148520036ec6148520007e461485200076e514852033f6c5148520007e63148520007e53148520007eb704852002dee704852002dec7048520007e8704852000eef604852000feb604852033f6f50485200267f765412011e7e765412011e7d76541200267c76541203357f74541203357d745412032e7f645412012e7e645412032e7d645412012e7c64541200067f63541201267e63541200067d63541201267c63541200076f725412011f6c725412002e7f625412011f6e425412032f6d425412011f6e32541200076d32541200057c71541200067f61541200067c615412011f6f21541200076d215412002d7f70541200cf7b705412002e7f605412002f7a305412011f7b205412002f6e205412002f6c205412002f78205412002f68205412002f7a1054120325fa768c12002efa768c12002f7a758c12002f79758c12031f7b548c12031f79548c1200edf9738c120016fa638c120016f8638c12002feb728c12000dfa728c12002df8728c12002fe8728c12002efb628c12002feb628c120107ea428c12031fe9428c120107ea328c1200bfe9328c1200077a518c12031778518c120107eb218c120007e9218c120014ff764c12000cfe764c1200ecfd764c12000cfc764c120006df634c120016dc634c120005ef724c12000dec724c120007cd324c1203077b504c12000779504c12002fd8304c12002fe8204c12000df8764c120016f8764c12000cf8764c12030f7b544c12030f79544c12002dfb734c12002fdb734c120007db634c120016fa634c120016f8634c1200bfd8634c1200bfda434c12030fd9434c120007eb724c12000dfa724c12000df8724c1200efe8724c12002efb624c12002feb624c1200efea424c12030fe9424c1200efdb324c1200efea324c1200efd9324c1200bfe9324c120007c9324c1200077a514c12030778514c1200bfdb314c120007d9314c1200efeb214c120007e9214c1200367f74d97100347f74d97100367e74d97100367d74d97100047d74d97100367c74d97100367f73d97100367e73d97100367d73d97100367c73d97100067f43d97100067e43d97100067d43d97100067c43d97100367f72d97100367e72d9710
  | 10 => 0xc220397d9434c22000dfa724c22000df8724c2200efdb324c2200efd9324c2200077a514c22038f78514c2200d7db314c220007d9314c220014fe76d8d200bede63d8d20004ff75d8d20024fe75d8d20004fd75d8d20024fc75d8d20004ff74d8d2001cfe74d8d20004fd74d8d2001cfc74d8d200067f54d8d200067d54d8d20006df53d8d200bedc53d8d200bede43d8d20006dd43d8d2002cff72d8d2000cfe72d8d2002cfd72d8d2000cfc72d8d20106df32d8d20106dd32d8d20034fe71d8d20004fd71d8d200067c51d8d200bedc31d8d2000cfd70d8d200067f50d8d200bedf30d8d200057f7558d200cd7c7558d200bedc6358d20385fb7058d20004ff7558d200067f7558d200047f7558d20024fe7558d20004fd7558d20024fc7558d200067c7558d200247c7558d20004ff7458d2001cfe7458d20004fd7458d2001cfc7458d200067f5458d200067d5458d20104ff7358d20006df7358d200ecff7258d20006ef7258d20004ff7158d20034fc7158d200067c5158d20384ff7058d20006fb7058d200067f5058d2002dec764c920016ec764c92002cec764c9200076f754c92036f6c754c92037def744c92037ded744c9203776f544c9203776d544c92000def734c92000fcf734c920007cf634c920016ee634c920016ec634c9200bfcc634c920016cc634c920005ef714c92036f6c514c920007eb704c92002dee704c92002dec704c920007e8704c92000eef604c92000feb604c92036f6f504c9200bfcf304c9200cd7e75d85200057d75d8520004ff75d8520024fe75d85200067e75d85200247e75d8520004fd75d85200067d75d85200047d75d8520024fc75d8520004ff74d852001cfe74d8520004fd74d852001cfc74d85200067f54d85200067d54d8520014fe73d8520004fd73d8520014fc73d852002cfd72d852008eee42d8520006ed42d85200067c51d852008ef621d852008ef521d85200067f50d8520006f76198520065f970985200057f75585200cd7c7558520005bf74585200c5bc7458520005df73585200bddc73585200a5fb7058520006f56118520034ff7518520024fe7518520004fd7518520034fc7518520034ff741852001cfe7418520004fd7418520034fc74185200067f54185200067d5418520014fe7318520004fd7318520034fc731852002cfd72185200367c5118520036ef2118520036f6211852003ef5211852002cfe701852002cfc70185200067f50185200367f76945200067e76945200067d76945200367c76945203657f74945203657d749452035e7f64945201a67e649452035e7d64945201a67c64945200067f639452019e7e63945200067d639452019e7c63945201976e72945200076d72945202567f62945201976e429452035f6d42945201976e32945200076d32945203557
  | 11 => 0x2e7f705962002e7e705962002e7d705962002e7c705962002e7f405962002e7e405962002e7d405962002e7c405962002e7f305962002e7e305962002e7d305962002e7c305962002e7f205962002e7e205962002e7d205962002e7c205962002e7f105962002e7e105962002e7d105962002e7c1059620004ff7558e20024fe7558e20004fd7558e20024fc7558e20004ff7458e2001cfe7458e20004fd7458e2001cfc7458e200067f5458e200067d5458e2002edf7358e200d6de4358e20006dd4358e200eedf3258e200eedd3258e20004ff7158e20034fc7158e200067c5158e200d6df3158e2002cfe7058e2002cfc7058e2002e7f5058e2002e7d5058e2002ede3058e2002edc3058e2002eef2058e2002eed2058e20034ff75986200367f7598620024fe7598620004fd7598620034fc75986200367c75986200347c7598620034ff749862001cfe7498620004fd7498620034fc74986200067f54986200067d5498620014fe7398620004fd7398620034fc739862002ef671986200367c5198620036f64198620006f54198620036f621986200a6f5219862002cfe709862002cfc709862002e7f509862002e7d509862002ef6109862002ef41098620004ff75586200067f75586200047f7558620024fe7558620004fd7558620024fc75586200067c75586200247c7558620004ff7458620006bf7458620004bf745862001cfe7458620004fd745862001cfc7458620006bc745862001cbc74586200067f54586200067d5458620004ff7358620014fe7358620014fc735862002ef771586200067c5158620006f64158620006f54158620066f62158620066f5215862002cfc705862002e7f505862002e7d505862002eef205862002eed205862002ef6105862002ef410586202557f76946200367f76946200347f76946202567e76946202557d76946200067d76946200047d76946200367c76946203b57f74946203b57d74946202567f64946201a67e64946203ae7d64946202567c64946202567f639462019e7e63946200067d63946202567c63946201967d62946203a57e71946200e77671946200367e61946200067d61946200367c61946202557d70946202567e60946202577a30946202576f20946201977b2094620257782094620034ff768c62002cfe768c620004fd768c62018e7e658c6200067d658c620036f6618c620006f5618c620004ff764c620004fd764c62002cfc764c6200057f754c6200e57c754c6201767e654c6200067d654c620016de634c620006dd634c620005ef724c62000dec724c620006f6614c620006f5614c62002dfb764c22039efb764c22002f7a654c22002f79654c2203977b544c22039779544c22002fdb734c22002fdb634c220016fa634c22002ef8634c22002fd8634c2200d7da434
  | 12 => 0xc7458530005ef72585300edec72585300adfb7058530006f56118530034ff7518530024fe7518530004fd7518530034fc7518530034ff741853001cfe7418530004fd7418530034fc74185300067f54185300067d541853002cfd731853000cfe7218530004fd7218530034fc72185300367c5118530036df3118530036f63118530046f531185300067f50185300367f76945300067e76945300067d76945300367c76945303f57f74945303f57d74945303ee7f64945301a67e64945303ee7d64945301a67c649453019f5e73945300075d73945302567f639453019f5e43945303ef5d43945300067f62945301967e62945301967c629453019f5f32945300075d32945303e57e71945300ff7671945300067f61945300367c619453019f5f31945300057d709453019e7f609453019f7b30945302575e30945302575c309453019f78309453002cdc764c5300075f754c5303cf5c754c5303dddf744c5303dddd744c5303d6df644c5303d6dd644c5303d75f544c5303d75d544c530005df724c530015df714c530017d7714c530007d7614c530036dc614c530007d4614c5300075e514c5303cf5c514c530007db704c53002dde704c53002ddc704c530007d8704c530016df604c530017db604c5303cf5f504c530004fe7688530004fd7688530034fc7688530015de7388530005dd7388530006ef628853000eec6288530007d53188530004ff7648530004fe7648530004fc76485300057f75485300fd7c7548530015de7348530005dd7348530007d531485300267f76541301267e76541301267d76541300267c76541303c57f74541303c57d74541303be7f645413012e7e64541303be7d645413012e7c64541300075f73541301275c735413002e7f63541301275e43541303bf5d43541300067f625413011e7e625413011e7c62541301275f32541300075d32541300057c71541300067f61541300067c61541301275f31541300075d315413002d7f70541300ff7b705413002e7f60541301277b305413002f5e305413002f5c305413002f78305413002f58305413002f7a205413002f7a10541300067f74596200047f74596200067e74596200067d74596200047d74596200067c74596200067f73596200067e73596200067d73596200067c73596200067f43596200067e43596200067d43596200067c435962011e7f725962011e7e725962011e7d725962011e7c725962011e7f425962011e7e425962011e7d425962011e7c425962011e7f325962011e7e325962011e7d325962011e7c32596200067f71596200067e71596200067d71596200067c71596200347c71596200067f41596200067e41596200067d41596200067c41596200067f31596200067c315962011e7f215962011e7e215962011e7d215962011e7c2159620
  | 13 => 0x8630004ff75586300067f75586300047f7558630024fe7558630004fd7558630024fc75586300067c75586300247c7558630004ff7458630006bf7458630004bf745863001cfe7458630004fd745863001cfc7458630006bc745863001cbc74586300067f54586300067d5458630004ff725863000cfe725863000cfc725863002ef771586300067c5158630006f64158630006f5415863006ef6315863006ef5315863002cfc705863002e7f505863002e7d505863002edf305863002edd305863002ef6105863002ef410586302557f76946300367f76946300347f76946302567e76946302557d76946300067d76946300047d76946300367c76946304257f74946304257d74946302567f64946301a67e649463041e7d64946302567c649463019e7d63946301967e62946300067d62946302567c62946303a57e71946301177671946300367e61946300067d61946300367c61946302557d70946302567e60946302575f309463019f7b3094630257783094630034ff768863002cfe7688630004fd768863015e7e65886300067d6588630036f66188630006f56188630004ff7648630004fd764863002cfc76486300057f75486301157c75486301467e65486300067d6548630005df7348630015dc734863000eee6248630006ed6248630006f66148630006f5614863000cfe76d89300eeee62d8930004ff75d8930024fe75d8930004fd75d8930024fc75d8930004ff74d893001cfe74d8930004fd74d893001cfc74d89300067f54d89300067d54d893002cfd73d893000cfc73d8930006ef52d89300eeec52d89300eeee42d8930006ed42d89300eeee32d89300d6ed32d8930034fe71d8930004fd71d89300067c51d89300eeec21d8930014fd70d89300067f50d89300eeef20d89300057f75589300fd7c75589300eeec6258930415fb705893002ddc764c93000edc764c93002cdc764c9300075f754c9303ff5c754c93040ddf744c93040ddd744c9304075f544c9304075d544c930015df724c930017cf724c930007cf624c93000ede624c93000edc624c9300efcc624c93000ecc624c930005df714c9303ff5c514c930007db704c93002dde704c93002ddc704c930007d8704c930016df604c930017db604c9303ff5f504c9300efcf204c9300fd7e75d85300057d75d8530004ff75d8530024fe75d85300067e75d85300247e75d8530004fd75d85300067d75d85300047d75d8530024fc75d8530004ff74d853001cfe74d8530004fd74d853001cfc74d85300067f54d85300067d54d853002cfd73d8530096de43d8530006dd43d853000cfe72d8530004fd72d853000cfc72d85300067c51d8530096f631d8530096f531d85300067f50d8530006f7619853006df970985300057f75585300fd7c7558530005bf74585300f5b
  | 14 => 0x12d7c74885504467f64885504467d64885500057f73885501257e73885500057d73885501257c738855011d7d728855011d7e71885500367c618855000776318855000775318855011f6f218855011f77218855011f74218855002d7e70885500057d708855002d7c708855042e7f608855015f7b60885500057f76485500067f76485500047f76485500057e76485500057d76485500057c76485500067c76485500047c764855043d7f744855012d7e744855043d7d744855012d7c74485504367f64485504367d64485500057f73485501257e73485500057d73485501257c734855011d7f724855011f6e42485504376d424855011d7f71485500367c614855000776314855000775314855011f7721485500076e214855011f6c214855011f7421485500057f704855002d7e704855002d7c704855042e7f60485501477b604855011f6f20485500067f74596300047f74596300067e74596300067d74596300047d74596300067c74596301267f73596301267e73596301267d73596301267c73596301267f43596301267e43596301267d43596301267c43596300067f72596300067e72596300067d72596300067c72596300067f42596300067e42596300067d42596300067c42596301267f32596301267e32596301267d32596301267c32596300067f71596300067e71596300067d71596300067c71596300347c71596300067f41596300067e41596300067d41596300067c41596301267f31596301267e31596301267d31596301267c31596300067f21596300067c215963002e7f705963002e7e705963002e7d705963002e7c705963002e7f405963002e7e405963002e7d405963002e7c405963002e7f305963002e7e305963002e7d305963002e7c305963002e7f205963002e7e205963002e7d205963002e7c205963002e7f105963002e7e105963002e7d105963002e7c1059630004ff7558a30024fe7558a30004fd7558a30024fc7558a30004ff7458a3001cfe7458a30004fd7458a3001cfc7458a300067f5458a300067d5458a3002eef7258a30106ee4258a30006ed4258a30106ee3258a300beed3258a30004ff7158a30034fc7158a300067c5158a30106ef2158a3002cfe7058a3002cfc7058a3002e7f5058a3002e7d5058a3002edf3058a3002edd3058a3002eee2058a3002eec2058a30034ff75986300367f7598630024fe7598630004fd7598630034fc75986300367c75986300347c7598630034ff749863001cfe7498630004fd7498630034fc74986300067f54986300067d549863000cfe7298630004fd7298630034fc729863002ef671986300367c5198630036f64198630006f54198630036f631986300aef5319863002cfe709863002cfc709863002e7f509863002e7d509863002ef6109863002ef4109
  | 15 => 0x9709855007d7970985500b67f60985500b77b60985500057f74585500073f74585500053f745855012d7e74585500057d745855012d7c74585500073c745855012d3c74585500067f64585500067d64585500057f73585501257e73585501257c73585500057f725855011d7e725855011d7c72585500077761585500067e61585500b57f70585500077b70585500b57b705855007e7f605855007f7b605855009d7e76185500057f741855012d7e74185500057d741855012d7c74185500067f64185500067e64185500067d64185500067c64185501257e73185500057d73185501257c73185500067f63185500067e63185500067d63185500067c631855011d7e72185500057d721855011d7c72185500067f62185500067e62185500067d62185500067c62185500067f61185500077661185500067d61185500077561185500077741185500077441185500567f60185500577b60185500367f74185500347f74185500367e74185500367d74185500047d74185500367c74185500367f73185500367e73185500367d73185500367c73185500067f43185500067e43185500067d43185500067c43185500367f72185500367e72185500367d72185500367c72185500067f42185500067e42185500067d42185500067c42185500067f32185500067e32185500067d32185500067c32185500367f41185500067741185500367e41185500367d41185500367c41185500367441185500367f31185500367c31185500367f21185500367c21185500367f70185500367d70185500067f40185503a67e40185500067d40185503a67c40185500067f30185503a67e30185503a67c30185500067f20185503a67e20185503a67c20185500367e10185500367c10185500057f768c5500057e768c5500057d768c5500057c768c5504757f748c55012d7e748c5504757d748c55012d7c748c55046e7f648c55046e7d648c5501257d738c55011d7e728c5500057d728c55011d7c728c5501257e718c5500367c618c5501275f318c55012777318c55012774318c55002d7e708c5500057d708c55002d7c708c5504567f608c55018f7b608c5500057f764c5500067f764c5500047f764c5500057e764c5500057d764c5500057c764c5500067c764c5500047c764c5504657f744c55012d7e744c5504657d744c55012d7c744c55045e7f644c55045e7d644c5501257f734c5501275e434c55045f5d434c5500057f724c55011d7e724c55011d7c724c5501257f714c5500367c614c55012777314c5500075e314c5501275c314c55012774314c5500057f704c55002d7e704c55002d7c704c5504567f604c5501777b604c5501275f304c5500057f76885500057e76885500057d76885500057c768855044d7f748855012d7e748855044d7d7488550
  | 16 => 0x81211257e76d8d500057f74d8d5012d7e74d8d500057d74d8d5012d7c74d8d500067f64d8d500067d64d8d501267e63d8d501275e63d8d501267c63d8d5011d7e72d8d500057d72d8d5011d7c72d8d500075e32d8d501275c32d8d500057e71d8d500057d71d8d5002d7e70d8d500257d70d8d501167f60d8d501177b60d8d501275f30d8d500057f7458d5012d7e7458d500057d7458d5012d7c7458d500067f6458d500067d6458d501257f7358d500075f6358d501267e6358d501267c6358d501275c6358d500057f7258d500076f7258d500056f7258d5011d7e7258d5011d7c7258d500076c7258d5011d6c7258d500057f7158d500057c7158d504957f7058d500077b7058d504957b7058d500fe7f6058d500ff7b6058d5011d7e76d89500057f74d895012d7e74d89500057d74d895012d7c74d89500067f64d89500067d64d89501257e73d89500057d73d89501257c73d89500067f63d89500067d63d895011e7e62d895011f6e62d895011e7c62d89500076f32d895011f6c32d89500057e71d89500057d71d895002d7e70d89500257d70d89500e67f60d89500e77b60d895011f6f20d89500057f745895012d7e74589500057d745895012d7c74589500067f64589500067d64589500057f73589500075f73589500055f73589501257e73589501257c73589500075c73589501255c73589500067f63589500067d635895011d7f72589500076f625895011e7e625895011e7c625895011f6c62589500057f71589500057c715895048d7f70589500077b705895048d7b70589500ce7f60589500cf7b60589500057f764c9500067f764c9500047f764c9500057e764c9500057d764c9500057c764c9500067c764c9500047c764c9504857f744c95012d7e744c9504857d744c95012d7c744c95047e7f644c95047e7d644c95011d7f734c95011d7f724c9501276f324c95011f5e324c95011f5c324c95011f6c324c95011f4c324c9500057f714c9500057c714c9500057f704c95002d7e704c95002d7c704c95042e7f604c9501b77b604c9501275f304c95011f6f204c9500057f74d855012d7e74d85500057d74d855012d7c74d85500067f64d85500067d64d85501257e73d85500057d73d85501257c73d855011d7e72d85500057d72d855011d7c72d85500077741d85500077441d855009e7f60d855009f7b60d85500057f749855012d7e74985500057d749855012d7c74985500067f64985500067e64985500067d64985500067c64985501257e73985500057d73985501257c73985500067f63985500067e63985500067d63985500067c639855011d7e72985500057d729855011d7c72985500067f62985500067e62985500067d62985500067c62985500557e71985500067f619855000777619855007d7d70985500077
  | 17 => 0x1cfc7458d210067f5458d210067d5458d2117cff7358d21006df7358d21164ff7258d21006ef7258d214f4ff7158d21006f77158d210067c5158d21004ff7058d2102cfc7058d210067f5058d21136df3058d21166ef2058d213557e76945210367e76945213547e76945210357f74945214ed7d74945214e67f64945211a67e64945214e67d64945211a67c64945210067f639452119e7e63945210067d639452119e7c63945210367f62945211976e42945214e76d42945210357e71945210377671945210367f61945211977721945210376c21945210377421945210376421945210057d70945212567c60945211976f20945214dcfe768c5210067f658c52118e7c658c52103776518c52103774518c5214ddf6768c5214d6f6768c52100777658c5214c774658c5214cf77548c5214cf75548c521165f5738c521016f6638c521016f4638c52100df6728c52100df4728c521036f7628c52117fe6428c5214cfe5428c521005f5708c5214c777508c52117fe7208c521014ff764c52100cfe764c521164fd764c52100cfc764c5210057f754c5211457c754c5210067f654c5211767c654c521006df634c521016dc634c521005ef724c52100dec724c52100776514c5214b774514c52100df4764c521016f4764c52100cf4764c52100777754c5214b774754c52100777654c5214b774654c5214bf77544c5214bf75544c52117df7734c521007d7734c521007d7634c521016f6634c521016f4634c521137d4634c521137d6434c5214bfd5434c521007e7724c52100df6724c52100df4724c521167e4724c521166f7624c521167e6424c5214bfe5424c521005f7704c5214b777504c521137d7304c521167e7204c5210076f658852149f6c6588521035ef74885214aded74885214a76f54885214a76d5488521035ee7188521037e67188521036ef618852100fe761885210376e51885210376c5188521037e63188521007e53188521005ed708852149f6f50885211457c75d81210067f65d81210067c65d8121004ff75d81210067f75d8121024fe75d8121004fd75d8121024fc75d81210067c75d81210247c75d8121004ff74d812101cfe74d8121004fd74d812101cfc74d81210067f54d81210067d54d8121014fe73d8121004fd73d8121014fc73d81210a6ee42d8121006ed42d81210067e51d81210067c51d8121006f631d8121006f531d81210067f50d81210a6fa20d81211457e75981210057d75981210067f65981210067c6598121006fb60981210057f75581211457c75581210067f65581210067c6558121005bf745812113dbc7458121005df7358121135dc73581211457e75181210057d75181210067f65181210067c651812113dbe7418121005bd7418121135de7318121005dd731812102efa6018121006f9601
  | 18 => 0x7508c6214f4ff764c6210057f754c62115d7c754c62103776514c62103774514c6214f5f7764c62150ef7764c62100777754c6214ff74754c62150777544c62150775544c621037d7734c621016f6634c621016f4634c62114fd6434c621507d5434c62100df6724c62100df4724c621005f7704c6214ff77504c62114fd7304c62115d7e75982210057d7598221036fb609822102ef86098221036f86058221004ff7558221024fe7558221004fd7558221024fc7558221004ff745822101cfe7458221004fd745822101cfc74582210067f54582210067d5458221004ff7358221014fe7358221014fc7358221034fc71582210367e51582210367c5158221006f63158221006f53158221066ef21582210067f5058221006fa4058221006f94058221066fa2058221036fb1058221036f810582213557e76d95211467e76d95210247e76d95210057f74d95210057d74d95210067f64d95210067e64d95210067d64d95210067c64d95210067e63d95210067c63d95211976e42d95210076d42d95210357c71d95211977721d95211976c21d95211977421d95210057d70d95211976f20d95210067f74d95210047f74d95210067e74d95210067d74d95210047d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95211967f72d95211967e72d95211967d72d95211967c72d95211967f42d95211967e42d95211967d42d95211967c42d95211967f32d95211967e32d95211967d32d95211967c32d95211967f71d95211467e71d95211967d71d95211967c71d95210067f41d95210067e41d95210067d41d95210067c41d95210067f31d95210067c31d95211967f21d95211967e21d95211967d21d95211967c21d95210067f70d95210067e70d95210067d70d95210047d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95210067f30d95210067c30d95211967f20d95211967e20d95211967d20d95211967c20d9521014fe76d8d210067f65d8d210067c65d8d21136de63d8d21004ff75d8d21024fe75d8d21004fd75d8d21024fc75d8d21004ff74d8d2101cfe74d8d21004fd74d8d2101cfc74d8d210067f54d8d210067d54d8d21136de43d8d21006dd43d8d21034ff72d8d2117cfd72d8d2117edf32d8d2117edd32d8d2100cfd71d8d210067c51d8d21136df31d8d2102cfe70d8d21004fd70d8d210067f50d8d21136dc30d8d2117eef20d8d210057f7558d211457c7558d210067f6558d210067c6558d21136dc6358d214f5f77158d21004ff7558d210067f7558d210047f7558d21024fe7558d21004fd7558d21024fc7558d210067c7558d210247c7558d21004ff7458d2101cfe7458d21004fd7458d21
  | 19 => 0x8931006ed42d8931166ee32d893114eed32d8931014fd71d89310067c51d8931166ef21d893102cfe70d8931004fd70d89310067f50d893114edf30d8931166ec20d89310057f75589311757c75589310067f65589310067c6558931166ec62589314d5f771589313e57e76945310367e76945313e47e76945310357f74945315457d749453153e7f64945311a67e649453153e7d64945311a67c64945310367f639453119f5e439453153f5d43945310067f62945311967e62945311967c62945310357e71945310377671945310367f619453119f7731945310375c31945310377431945310375431945310057d70945312567c609453119f5f30945310075f658c5315275c658c531035df748c531535dd748c53152f5f548c53152f5d548c531035de718c531037d6718c531036df618c531017d7618c5310375e518c5310375c518c531005dd708c5315275f508c5311757c75d81310067f65d81310067c65d8131004ff75d81310067f75d8131024fe75d8131004fd75d8131024fc75d81310067c75d81310247c75d8131004ff74d813101cfe74d8131004fd74d813101cfc74d81310067f54d81310067d54d81310aede43d8131006dd43d813100cfe72d8131004fd72d813100cfc72d81310067e51d81310067c51d81310067f50d81310aefa30d81311757e75981310057d75981310067f65981310067c6598131006fb60981310057f75581311757c75581310067f65581310067c6558131005bf745813116dbc7458131005ef7258131165ec72581311757e75181310057d75181310067f65181310067c651813116dbe7418131005bd7418131165ee7218131005ed721813102efa6018131006f96018131034ff75d8e21024fe75d8e210367e75d8e210247e75d8e21004fd75d8e210367d75d8e210047d75d8e21034fc75d8e21034ff74d8e2101cfe74d8e21004fd74d8e21034fc74d8e210067f54d8e210067d54d8e21164fd73d8e21036ed72d8e21034fe71d8e21036f671d8e210367e51d8e210367c51d8e2102cfe70d8e21004fd70d8e210067f50d8e21014ff7658e21036dc6358e21004ff7558e21024fe7558e21004fd7558e21024fc7558e21004ff7458e2101cfe7458e21004fd7458e2101cfc7458e210067f5458e210067d5458e21036df7358e21006df5358e2114edc5358e2114ede4358e21006dd4358e21166df3258e21166dd3258e21034fe7158e21034fc7158e210367e5158e210367c5158e21036de3158e21036dc3158e21004ff7058e2102cfc7058e210067f5058e2114edf3058e21035f5768c621036f5768c62100cf5768c62151f77548c62151f75548c621016f6638c621037d6638c621037d5638c621036f4638c62100df6728c621037e6728c621037e5728c621035f4728c621005f5708c6215177
  | 20 => 0x367c71582510347c71582510067f41582510367e41582510067d41582510367c41582510067f31582510367e31582510367c31582510067f21582510367e21582510367c21582510067f40582512567e40582510067a40582510067d40582510067940582512567c40582510067f30582512567c30582510067f20582512567c20582510367f10582510367b10582510367c105825103678105825100cff7658a31036ec6258a31004ff7558a31024fe7558a31004fd7558a31024fc7558a31004ff7458a3101cfe7458a31004fd7458a3101cfc7458a310067f5458a310067d5458a31006ef5258a3117eec5258a3117eee4258a31006ed4258a3117eee3258a31136ed3258a31034fe7158a31034fc7158a310367e5158a310367c5158a31036ee2158a31036ec2158a31004ff7058a3102cfc7058a310067f5058a3117eef2058a3118d7e75982310057d7598231036fb609823102ef86098231036f86058231004ff7558231024fe7558231004fd7558231024fc7558231004ff745823101cfe7458231004fd745823101cfc74582310067f54582310067d5458231004ff725823100cfe725823100cfc7258231034fc71582310367e51582310367c515823106edf31582310067f5058231006fa4058231006f9405823106efa3058231036fb1058231036f810582313e57e76d95311767e76d95310247e76d95310057f74d95310057d74d95310067f64d95310067e64d95310067d64d95310067c64d953119f5e43d95310075d43d95310067e62d95310067c62d95310357c71d953119f7731d953119f5c31d953119f7431d95310057d70d953119f5f30d95310067f74d95310047f74d95310067e74d95310067d74d95310047d74d95310067c74d953119e7f73d953119e7e73d953119e7d73d953119e7c73d953119e7f43d953119e7e43d953119e7d43d953119e7c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067d42d95310067c42d953119e7f32d953119e7e32d953119e7d32d953119e7c32d953119e7f71d95311767e71d953119e7d71d953119e7c71d95310067f41d95310067e41d95310067d41d95310067c41d953119e7f31d953119e7e31d953119e7d31d953119e7c31d95310067f21d95310067c21d95310067f70d95310067e70d95310067d70d95310047d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d953119e7f30d953119e7e30d953119e7d30d953119e7c30d95310067f20d95310067c20d953100cfe76d89310067f65d89310067c65d8931166ee62d8931004ff75d8931024fe75d8931004fd75d8931024fc75d8931004ff74d893101cfe74d8931004fd74d893101cfc74d89310067f54d89310067d54d8931166ee42d
  | 21 => 0xf7358e510375f6358e5119e7e6358e510367c6358e510375c6358e5119f5e4358e510075d4358e510057f7258e511957e7258e511957c7258e510367f6258e510075e3258e5119f5c3258e510357e7158e510357c7158e510367e6158e51037766158e510375e3158e510375c3158e510057f7058e512557c7058e510367f6058e5119f5f3058e510357f7658a510057f7458a511a57e7458a510057d7458a511a57c7458a510367f6458a510067d6458a510057f7358a5119d7e7358a5119d7c7358a510367f6358a510067d6358a510357f7258a510376f6258a511967e6258a510367c6258a510376c6258a511976e4258a510076d4258a510076f3258a511976c3258a510357e7158a510357c7158a510367e6158a51037766158a510376e2158a510376c2158a510057f7058a512557c7058a510367f6058a511976f2058a510057f764ca510067f764ca510047f764ca510357e764ca510057d764ca510357c764ca510067c764ca510347c764ca515557f744ca511a57e744ca515557d744ca511a57c744ca5154e7f644ca5154e7d644ca511957f734ca511957f724ca5119f6f324ca511975e324ca511975c324ca511976c324ca511974c324ca510057f714ca510357c714ca513567e614ca511b776614ca510057f704ca512557c704ca5119f5f304ca511976f204ca510357d76982512557f74982511a57e74982510057d74982512557c74982510367f64982510067d649825119d7e73982510057d73982512557c73982511957e72982510057d72982512557c72982510357e71982510357c71982510367e61982510377661982510357e70982510367f60982510377b60982510377860982512577a40982510077940982510377b10982510377810982510357f76582510057f74582511a57e74582510057d74582511a57c74582510367f64582510067e64582510067d64582510367c64582510057f735825119d7e735825119d7c73582510367f63582510067e63582510067d63582510367c63582510057f72582511957e72582511957c72582510367f62582510067e62582510067d62582510367c62582510357e71582510357c71582510367e61582510377661582510357f70582510377b60582512567e60582510367c60582510377860582510077a40582510077940582510377b10582510377810582510067f74582510047f74582510067e74582510067d74582510047d74582510067c74582510067f73582510067e73582510067d73582510067c73582510067f43582510067e43582510067d43582510067c43582510067f72582510067e72582510067d72582510067c72582510067f42582510067e42582510067d42582510067c42582510067f32582510067e32582510067d32582510067c32582510367e7158251
  | 22 => 0x953255e7e42d953255e7d42d953255e7c42d953255e7f32d953255e7e32d953255e7d32d953255e7c32d95320067f71d95320067e71d95320347e71d95320067d71d95320067c71d95320067f41d95320067e41d95320067d41d95320067c41d95325667f31d95325667e31d95325667d31d95325667c31d953255e7f21d953255e7e21d953255e7d21d953255e7c21d95320067f70d95320067e70d95320067d70d95320047d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d95325667f30d95325667e30d95325667d30d95325667c30d953255e7f20d953255e7e20d953255e7d20d953255e7c20d95321b57e75d85320057d75d85320067f65d85320067c65d85321adbe74d8532005bd74d85324f7cc32d8532004ff75d8532024fe75d85320067e75d85320247e75d8532004fd75d85320067d75d85320047d75d8532024fc75d8532004ff74d853201cfe74d8532006be74d853201cbe74d8532004fd74d8532006bd74d8532004bd74d853201cfc74d85320067f54d85320067d54d853200cfd73d8532014fd72d85320067c51d85324d6f631d85324f6f621d853202cfe70d8532004fd70d85320067f50d85324d6df30d85324f6ef20d85321b57e75985320057d75985320067f65985320067c659853217fcc3298532006f761985320057f75585321b57c75585320067f65585320067c6558532167cc32585321b57c75185320067f65185320067c65185324dfcc3218532006f56118532034ff75185320367f7518532024fe7518532004fd7518532034fc75185320367c75185320347c7518532034ff741853201cfe7418532004fd7418532034fc74185320067f54185320067d541853200cfd7318532014fd72185320367c5118532036f6311853250ef53118532036f621185324def5211853202cfe7018532004fd70185320067f501853202cfe76d81321b57c75d81320067f65d81320067c65d8132387cc32d8132004ff75d81320067f75d8132024fe75d8132004fd75d8132024fc75d81320067c75d81320247c75d8132004ff74d813201cfe74d8132004fd74d813201cfc74d81320067f54d81320067d54d813200cfd73d8132014fd72d8132034fe71d8132004fd71d81320067c51d81320067f50d8132416fa30d8132386fa20d81321b57e75981320057d75981320067f65981320067c6598132107cc3298132006fb60981320057f75581321b57c75581320067f65581320067c65581320efcc32581321b57e75181320057d75181320067f65181320067c65181321adbe7418132005bd7418132327cc3218132005f67118132005f5711813202efa6018132006f960181320357f7658e510057f7458e511a57e7458e510057d7458e511a57c7458e510367f6458e510067d6458e510357
  | 23 => 0x401e00e0030018048004000001400400300e0018000015002001800002500100440000090020004002001001800002800000080080040040008000002002001800402a002000800006a00601180080c8000001801800201a0008000002001003804c00000200a803c0cc00000b8000020000003000800001601b00040020030010018008004002002801200001180000180350020014002001007000800200700a0000004007005800000c00100280040160020000028024001000000c01e0010008000000007004000000000100a800c00001a004001c00c00300100380000020008004002003002800000200a000800400600f018007002000c0018018020003000000000e001000800402800f001000c01e000002000001c000002004c0280090018004026001000001c060006006000003e008003808800c00400100280880070018000012004000803c0480000018000078006003000800600000200140160000008030002009001001800a01400d801c008009000800400400d00b8004000000002002c004002011007800c005003000800a030007800c01600000080040000210050034006024006800c03a0000020014002013000000000e007000806000400500400380040230008048004005000003002800e00400a0050000002000800c0010008058000029001800c00600600180080020000030034020000000000000a03a0020044010019000000001e00c000000400a007001002000a0070008000012000001000004600000c801402a02f002800000001f0000000004002001000c002025009000800000100a803000c0120000008008000000800c03000000480d00020050000088008001001803400001a001803800400a003800400a0000000000000000001801000e003003800000800600000b4000004002007400200200080280bc00001980000060020010014004016000002801000300381780000000090008008067001807c006004003800802a0000098000030000000000000000002b8000014001016000401a006001000000a0160018000008015000001001200b0018004026000001002002a00000d00080000000060024000001002800000c00a56d7e76d95321b67e76d95320247e76d95320057f74d95320057d74d95320067f64d95320067e64d95320067d64d95320067c64d95325676f32d953255f5e32d953255f5c32d953255f6c32d953255f4c32d95320057e71d95320057d70d95325675f30d953255f6f20d95320067f74d95320047f74d95320067e74d95320067d74d95320047d74d95320067c74d953255e7f73d95325667e73d953255e7d73d953255e7c73d95325667f43d95325667e43d95325667d43d95325667c43d953255e7f72d953255e7e72d953255e7d72d953255e7c72d953255e7f42d
  | 24 => 0x201680680060000020000000001000003800e000001800400400200f000000002801b000406000400080000060080010000020004008000c02600300280080040060050058000002000001401600000c801c00e002000000000e00200200040320090030014000007000800000c00500100100020000010010000000007001002c00300180240480020010000026006000002801a000009000800a0040120000004000000002000000001480040000040008010008038002801000000c01080a0000000000009c00400d005004000800e020808c01a040000800c00403e000800000e000001005c002000002800000e00000200300000000008004000005000000000e001000000000600100980040100080000008010000000800000000e001809000a007009801001a009003002400400300000a0000001000000c000001000804800400b00580000000110000044000003004804002200000b800800000101c000c0060020020014016000009000400800d000001c00800700080200040000000008006003000002400a012001803c00a0010110004002001004801800000800d001802a004000809c000000009005002c0000058004030000004800400e0040048040030011000806800000e01180c005a0060008030006000000002402c000003803c00001f000001800001200400b8000003002801c000000000002800400a007003000000f00c006001c001000801001c0030090004000001000002400c000000801c000003003801c00a00000201bc016001013002c00404400b8014040007006004800200a001003c00000000780040100000008004002023005801000000f00380d40060000000014038003000800001200500800b402c00c000000806c024000001800400200b80140500030000004000009002800000a01c0030034002002013800002802600180000040080070018018003000002c006003007801000600e00d801c0000010028000006007000000403c0000048014008019005001400c015001800000000300c000c032001000803800400800000a4000003000802403200d00600000ee000007800003c0130250044020001008000006a00000b00080100090018008012021010800400601000e000000a00901d000402804500a004800004200100000080000008000006000013000c0000000008000016002008000002a0020000000000032002000001e00500080000200160030008014000002800c02200100080c001803b000800c01c0000000050010008000003c01800000b00000000090178004004002009800001602a005000c008001004000800a025007801000c00f00000040100550008068002005000801401c0040088000030008003800000400900e0000000023001800800600000280080160000008
  | 25 => 0x55638ad68e0000000001656b6f35c00008d8147646285442898025520c86d41b84298f899bc21a000287800000000000000001a9034113dc6a1b3000000193627539c0000838d101d2af9d39e8a73649efd5060c02e9039175af0869d02c0b36f190d5a87c9ba00000036680008a202bae2000097400016f40004c76f18000fca557559bda437c89f000060002e1d753f2565136cfe59437a1e342210000ff17f0e3a5159d0000000034302d00000001b48000864d1157d2124000b1b516179085e07d5f225092285465ddb46489853d3db138011a09c000350d90a00014a0000000f3835581447aa5b05f6849157c4092a521e5916db30001bb9980000647382800076d00030e5c4485a45600015bc00d7b722240ba98831b80000007512590000eea41a24409c84c81af6baaf18000e6638d15e40003653e81d64928a8479d3b0079a96b621ac18cf63a93fa92596425f74a73dd11c8d7337f310479e3e37028a953845a80b93735cdc5544d5019906c92b299b97d8f4ed50e10d799f2a8a1319f15d640e76fb229851a2b44e893bc206da6578a3d459210406f000082a02c6c12d840000e94b90591b56db251dac7487273b6d3915ca685bf49e800160800000000010266384cf1d1d640335000194927297b00038c1b260000488305c920873a606d5998b941a8810800000000034fccec0004b8a9d9b5c000401b89107c8835a52b20cce7910003c38b9e01844200019e865e1b9800002a00070600000004625f9a07ca34bc23712e7cc7c0610000001a620000003b880000000000000d7e000296125cd5af4a4baa4e00fe83703b3995708b125f8a2e070a7030829b543fa66f3cf80cd88e1e338baf05e0a2235e021ec0009de76bbcfc1700000eaa61c26c7dd2f7b17449e78410d8b8da025dd6d1ac9807218f1b71eb8000ceb00000007cc0b34ff2064da2dd518403094406976929a914b6d5e3732574f34f3451a8a49d48012001c00200200b800c000013004800c04e000001005c01602a000001c01a00b007809400c00700900240000100000038012032004000007c0010060004024002004802001400a0008000000008000004400a000010800400000000680240020020008004004000002800c00000f001001800200d000000c01600600000180080210040004010018000001001c000000802402600100000c001001f0000004038001002000c00800300b006c00000701c0000006006003004000a004004002c00000000000280020000008020034000003800000a008001000803e00a0050064000011000005001a013018804801e00800a000401200d00480dc000015007000802c0080018010002006000003400000200d000c00c0030000038006016000004400800a000000002e00d001802400000400000000000440038004004
  | 26 => 0x85e0001ac8000b871852054000e1c555162048c0003bb0139be69a61361f21ed67b135500015bac042d2969951add651f80007dec3f08099400001396ff95301f400043e87e41d40000002cd8000efc370a4a4e10000000000074c0007b9167d55a72800000011e675a32211200007fb5d8344c0000005130e280000006630ac198400016d800000000000000008262320000000d6a24753f846c000000247800074483c567b49c00034d6cc834810aced59e00013eacd32502728c0434f0131288cf083d439a5d9d34f7031c97ec9aa00026232c45b87a062928408f2981606b484c163ac695a668a60b5a60d0a7c000f6850319955c61436dc042400045000199554ba2d71d7813cf0611041a919d542460000221979c2bd15233c886eb2f45bae6d44ee906351610000dfc5301f9d3180f60000fcc4846170bf2b68000b1e470800000031170800015a284b0001439502bcf6543724a642585609af8ef47e932d8dd5770a4a2ac9745bd494672a82c567e1da672a5a981cf4d090a5c05967ce433a3fd2340005622020134abc6b50f11d2e1e53968358f3ce8e3bbb255c80cc40a884b98925ff0d70e2c4b293a3f93b9d03cb1a764060c9862062e180000e80002b58000f2879507fb82c00000057eb7780000000000314a6ac2938b3000956c7151a184d4ce000000053deca18b40bad18c8a00008f9b0c9c811c1b7b554f885660001fc0a0c5734da9a548d29c40cbb6f83a89dc0e7000147c54402e0001958603022244c67acd65dbac71cee8c85fa842896ec7e2cc010168213d06c87bc1d682d5521400e743810ba02fc00046d53524c4472d4b2582171316282709266c000ea776b3b797d80205d0186d05c9c03c402f5762a54143a319484b5556a2aa50dee23511800000090232d38edd627a44950a4da82621431057d4e687853316294f6d1268e10611f65360000000b6a0003c38000000da1506348051e52b11d12392c46e873f0e656449531b0271c1a8daa47f24340f805f1ff000075000000039d8e3c090000339d632de435c8000000000296973144433c430290405c1500001000916b511c380004fe000175094497e00009286fdd6c6960000000a6e2fd4150631e181f64ab80016fc951790887466000004b94ed3582c65e42a3000043043f9c90000d5b201bd5c2e2027000112c0c8af25f4aac1102f6718a0000d2400026c0d68000c9e69c8001266bfc15727d10c29ae0d826a169ad290b5826da289323b234307484e35b90c406a40cf6cf07994785fd36f36c41085072649ba5134b084df3085324da57912284f9e0704678fb0bc4c6913f12e000043d413ab6c0006da58ab8d81da2f73ff178d6ba7556a52e351e8bac1bc1680978a0861607810cc3f50e78fc152200072e9d2037af440190000bb69901da8001d30f46
  | 27 => 0x5d980000000003891750ea4dc819413056be5945bbb99d66600033fb0498a80002162824d2200051888acc4c2534b301c98f03071aa1ef4ce4bb6616a42052e0d752b0000000b43783316c7782863f1830c3085237b993b5c085993908000eac2b200024243722cc2c18e4507e76b00025b11f8bea406ad3c00000077898ed948deb6f83ce4630db452cb94d812a0500021e85ce3eb210896834203f769800003a77e5328001e4e5a76300b0800047a00000000009a446fa41d4dcdc55ad8a0001013a6690000000eee4090dc09ee1e46ef8001c64c890cb25e0d8c0fc7799158ff2ec22d6a7a5c688c06f132746084c05cf10f893092757c0278de62da1b89e9867e06e00030e9db00864af2c8c486e254b7164151c85d5d58928fe664a46f082d0ca0005458d0da0aaaf2021858b76830077a985a5ab5c2bd3db455263c3a282d424e7374d480c578616013d0000eb000000019a1104d3c07c0000dacd5376300001be1ca00000019fabe2349b4f4922a0f07c83f80003f22328000000ed93b38124c280004d8a6f54ee000259babca3e1310d51c7d2b06f022893c40ee6712930b4197229d2419f5d938b6b3779e04000000000280d6ac000708a5240005202be0001bf4ee152d1be406cbaf69600004a06cc05916dc88cf23000a920ca6c960000000000af361218b97ba3720003a7400023f00004ad2c6000000000000055352180013c2a9e6b8a0e8efaeb541c35082d86b42890c8118470e0a91b09d4684007a8948b18bda7acbcc500ca2d51c0c380007860a739a05f2eca497a85cd18e8b0000000d344416858000d9c26b19a04a5e140437bb86919c2d380002414c58bc40c83a1939a1ec06596340de4e83e015a465aaa34239134712dce3b331555246700b71831dca468508b5459e65cd36c3531cb4e4824eadc01e048a481a9f5ea4df278e0e5936e70d47921d000000000000001e6db01e826c8ea8d7a197a7e079494c16ab5e0f781172b88c6dba80694c9bd01d5af284cc9d744f28981e90000b729486f3b9305d805560100009f8255774000000000049d842044a9dd6d13268ff474b1381ec0f46a520c9340109e55100005040002ad000153c0005682f73a80000acd14c045143089163700009f60000ee17ac0000002e43b504cc69d27a1fb0000aa7000155964ed092420addde045911b00502dec4e2b6939d8ea1882ea80004260002449c7400000026c800117a0004ed10a9eacab66b72ec92fc2ba48e319da14d03746a68c4cec7f388bc01cfab7842800000006a84fd0000e3800033193d5b3067965f0c702ea1cb67b3adcfb28771220668ca8af50db85500004ea150ab959f88421a4202983c39c75e9e3881ee0751b8088b0e0005fba9d0000ae4223811d4dab490003b10fd08b018b8281492e781bd88803141e1026000
  | 28 => 0x1c7c3da46ea0ec128a1c5b880000000112c90001d92a1d3b00399b6a6876671fd926a0416369b900000005d332bc0b62c374d8914f8e6f21829bc46968c10001f0d1b0000713b3ec000cbd1bf0000000dcc0ddbb7c66c0002ce31086f800042f80000000004de00000000001311719986ded53d0ed08a414400234ccbd48be1a097094148d935b07016c66ba46581e97fedb96ed232858a2c770b80010409d24733cdc1e400000000000000002f83949d828b2066108ca50e313bdaa8083e5f23f13710cd83553db9584dba1345c5163940045f37db7743e21b166384004ba93f5220bd47d47f7055a2654bca8f01402e40009c65862d20d4c27104789854160005f1a615570d670edbd512fea164f2ad9148a39410b23b482edbc0a6800073c94b000256d86a0006c580e929a13824f92d9c0200000000000009ab000272ce5e00009620b1668bd25fb1e715b260700027c400026a3d4a5f08442f10ae80000006880003ba40b0eae6b19574326d8549f13787bc00012f99e8052c133c60000740c826ba0000d0030c4078f380acbaa000081c2242497b623e40f2b3a064398d9a043a51424d04b8e963863044dca7ea0a10cdceae4022e029c1ab200000000000001f04688bbd4d6d8c6328934f00f120ef1a3d328ca70bd14409b617d60c364930cea601800010b23ba52326d8bec52e56baaf4506de01303d99d60e826282a20df48e2659859c4cac800fe03291e003e4cb3094a42bd95592791974a395bd8095c28d4524105e0cc2d246e7928c90ee451eb8c1894ab655fa31994c46b13001b2c3fea2963184397fc59a55a2f5db5e8ee77696d8c4ebcd32334d487666905491c4a2236c2ba8d5de8edf834a3d7505e589400ac7c1ba66a78f2510c1ac1d172a1314ae44a1ce98e84226061b32a5d35a63d34dbc2cd762b97970ad94422af70a8000b2e57400030d859c0003ed8c340006eb74200000000fb00030e1cd206c7ac00009989551ab3bdddc0ee365800000000003d3bc2520c4731dc92ecee0f2c654a97c818c0705bb2a965cac56fe800190e62b78fa65ca960e55ca80007920006a39ca800000000025dcef88ea20424640005ec68ab23ce0805e707b740338c984d79500ef02fa6731318f502bc0fa9accafc8fd7018000cda1ea0e89c005d63382cb0720d32cc54128c90d389d514623a501222c69d9920fb41950002cf4000d3000006507f0b894fe824822c7d12f2800021824b65e2e591626d90c7281c9a2098000048865c0004740000a7ef1d4089d7d03af2b00000002aa2a67b2270512604b167b56000079b00007b400051943492700700002b828bcd203830000000e0e64262208080000001d526e8f1e0000002bece7ac2f000089034e9ea087bc0c0004490b319d4000e3c4b4ab24996c590090479bb682300d2bd800075
  | 29 => 0x6d6488000d020590000fe8000d8a75da9a55c247d00030880007447a422edc943c75bb056c000485000000000012300010f00004a939b1c3d80612d00000017243a10002cf9ea0000000000000000c44a800000000024a80016d225630900006f2d70097890041cc2a2b92935ce4eda0003d700000005278d30000a7121280000002e939f0614ec60001bd0001ba2b425ea1399150285000116cd8ae0d2101e0987a5220000000bb41915e5800068c68510e2229e5206b52c1a88312a8000030adc0c00075f1a8419a33e36fac3c8b45bc14412bd31400028200003643137b51e34e8668b5818b04e941c55b31d187961a24c1818060692c5ea8000000000000206c57e9c903100000000002509f0400064325a31d017c00027c87310285cb0000205af6b5772690d9c6ef203d1284ccf856c22e1d342b47d839726880003d3308a9e128a6982aab9511729682a680283f6130454b364a28d9077a82597beba5797b1b03e81fe1f48efced40004d02f2982a82b2a8345913cae703a80011aa1b6055218d6167ee2e98001734c455da3548da63314c7b6ec4a8f1634682ec26e9ec1df3ad00000001063d44f2e107000229401cd643d926c05f05385a62f4564a7301082efc7fef35335b13165a2d91783b15664a1b05693e98b0cea0a585ed38a76821a10fc402ce819d20a00002d607424114c63ad00038b064a0731068000ea62ed6139935d38a0e218a4842b06ed52e0000000f170b80001c1cd44569000137e00023f1160e4428a670000038859e22a800154c8cd2d700000000005e80000000268406150c0003b25d70dd8d4e1e2274a0880d40007a1352011295c000000051c0004478000b26a4057a387c6e82050000000000273000395d038000727997041e00000000000000006990d75e2a16900000010d80004e41c9c00056e1598774a5e1d80000001ef200050d0001bca0000001ea865273c0002549584d360120e9caca55f7400319ca2bfd11b9ca58507200000001c52bcc649b674ff846e00020a5aa8eec6e30a251accb77a28e8cc2a9bb0620001068549445a50c9d8d040000000d884e172ca25189a9b400026103ee27c293b9d4b480000528000000c344f1000000013f7af8b7420c33200000000002d215113fc00000000021c800000024f3bf80007313a12ee4ebc772588a1f9860a64289b749c720000a4ae3996c0004c715a8000efa0002a18000818000000000000064c8001928000049b43d90c0000000ad59e297d5c18000000e621af93ac4b600070c8fb445e5086f63120294e08554221d9240500000001d1e3ab2039234000c900001bd05e600048d9bd5c9cd1d0003d893ee0005180298a1a00000039b1774aeb40b0d0000014c34fb065e6cf4955fb90c3ce5ce0003c6de781763fa1b4109ab5458680013b04e575c80
  | 30 => 0x984fcc4f25a81588f300006e1ad88078ba70000000000d950000b2000057d38c80019bad062c5951479053a17b0af9b2c2904109cac0006db5d41fc53a6d9f7758d90fc063f4f301156a61eb00000000000007558000000ddc051808d48ebe85d206d0f6a9f643801e0ab44387142bb125a86a0ab1ed05e47963e5361033ac0839a1c4c7bad5f114b7f96e65a308d02640000006b580000000001e29298000aef237b5bdcac6c75c992e9174c575989f257b8b6c000000172234e58487a0dfa3c0799249049caca6b29af48ec4923a71d25e60ef20b29111eaa000652a57ca8e2d3126000002cc163b98679d183775809b291ae3f600018745d0d94277000157267e3301b200005765d196b12ac0006bf800188c49000010288200006a719887b24540002e18150000000000000093c5558e40454a9b6910000000de15090c98c9ed76000216d69c0006e0800000028462998c00001f8000000171ec724288bb92a8d0e5ef031c0007de4c10d29224a140003b2c12ab14000245c00068a2cab6d824c7742682580e58eef16a1f84ffa9980002128a0a8ab38a1200c642bb767223947a9ff1e8800966051d42213290165802d8a3ac24082649737c5af2af91bf89dc7f2ad623931f4f9ae7036b9be0eb8965004a42dd10d5056596d19b82e27173345576e7b0003ccc3364d20002ef918e7c218caea438eb7d54b000000000027800000000000000001bcc9404c4903958000068d8001b520006500d4c6ce9914072805c300000001454e36a7964206a18a276561887e9202ace00032ad1de02d519bb492184c54f9b3210daae06ec94f98be00026e0d141b6be10001bdde9c6e71cb8000000ed10682460f24eac0bc80000000483d698907ca8bf759800155ce936a4b37c000ad87af1f908808e00002ba897a010185b2352e65ba17d8c05ec65421acac5c8f657b4879ef97923c66b62a549a83444f5af4cbb82c04e714919c4f4c5f2aad4df895a7bb3289b123f757f06f1cd4d576ce33342c6e5e1dd919918639545ab84d8461155debca981665101aa47553a000000118cf1632b74284749f091f3573af1716beb0efa1ac7e2e3d4233c9184cedb285956d81edf46fba2cc55666e0a2aae8f7000500004c93381ba561889d12cc321c2380803c470000000096a5fa6f48000ee2858000340846617f79f13f519801b0000d09b500007323c3c3021134f43c113dc0000003205654ac6763800007ae4640220000005ed4ce8000000e7f6a3158c522d62773277c0004260001685e0e8f101798699fe6a03f7b961d1429a464b38d22035c32f9dfd020f436ae0e6d8360d829500000000000003a540000004ec80001b4433625000129e8a34bd0eb96d0c76316baa07c0d870000000000d9700031bc0004ce47b1478e6450148aa58490ca3613c1904000d
  | 31 => 0x2e4657349921c2f413ea891c4c4931503584b449d65ac8bf99de080319a9a071e7055c08d41dfee09750add52de8e7046000000000000000001ee0000003bec00067d00028a9138f3d4578800dec300000179d31a718000259c0007b925f292c460f4123f8000f20c170000000000ca30002f800007394698e3400056f0eb12a0254dfb06487342ee8bc20337e4fa6c0157f8ee0000f0175128e80000651813d3c1c641443e35a463a3cc32396cc85037d5c61778fa84f60000f0c000e415bfa3700000006c028b8000e730001a2459ad2a10f29c863cec367b82b0f74ae602d00001b89e70000618000ee40003700f56c614029b801c28075b5161929464c6381190a729d733a2214aee6e37b021b8658dd75fd89b81107af2e51abc7c84cf3119580c1cbb574cb604c4a5c7544b8796040ee06721a0b70ef95b6aa40948a9400033540000001edac4ce020000ae39e4832b105850000a363d83c9b74d97e4e26c88000d04000165248871c83146d1de4c50f5a58c276d26e6b700027511ca2b870d8e196b08d045a2fc15b88e30b694719f007e14cb8b43dc7022bc3a955d050f04727c9b48c20625ad14990ad009984d55f85fe61e3ae9742c402fe1938e12ce96060578bd02744f18ce59d82767750ca8ed26665528c49e202d85710b45d3e8ae52800ada1aab739fa2b48e878a07112690ac1020c6a94c42ae924cfbd4de4c00010c08b9838475000020d8d60005ce3221d9885211c1b3dc42000208959d408bbc0be0000afe8904f78000000000000000186e0002e2abb55049640002504b889ed440123034ab3956a9c2ceb6c5c07a1959996e003562e6144a363170a9448a651700016c9a5e0000002bdc81a46110fa280000bd81d80e49cb88ec5f72138734d770338a8d03458200031a000000000000000000000002d10e46c9f00039c4c6c00000015396f20003519d880000000000001d9ee6d0001369bb000000018c400022668f08ed250e3f057bc5160ec0544bb9094d8e6b32eb3684bc629768269450245e0000d880001191ac008578eaf04d3b5f1ac00006f72a7c76c8aa1cfba047a81f2766a190c9653139331cdbea90a01b9bfda305f3000003c000000302946083a0006de85845be04d2f0360d50e649258aac4b52677627b159a50a326c7829080a3dc6e380001e2c0646723e000036b6ab1961eb6cb53ea807088a3e83cea9f1dba00000022340000000001e845c002a1fa2008a9061c000210d50a7f82af2314a1449b4b696f9e1a84104e963cbbe0a23e31db1a6888c0002930000ea90002c00fb800020f2274cae5d96f791758202e61fe8810000d720003bd8b0a85409da1c4ba0a0203684f84100b610bbd85720e872168000d4a0000000000000e7414e000000012807e80000000000039bb00000000e0ae0884ec620003
  | 32 => 0x3178a599c87a50b9aa68958c7c269b634718b854981db96dceaa1db882524ae2a1b68d6d49c2a723539401a2a6f1efb48dc88ccf4fdbcb5b0cc7b70b2c580a4ad3717975c9e6b353151704be8b52235bdbc14e1872811359e04c3b08882f0cb287537508c5072da05871cccc087105be0c7d28eacc6453de1c345f50e4a730c3e9950231a10ab0cd8744ad9c38c5f8592392d95a0e02c8bbf433ee7c48b10ad41a3bd7238cec5581e90a0236c8520ba4492f58ce666418d054c290000392b36d7cc4df4fc8a7937231661f1505e3023411e1b359dc27b30f2a65cf4c5e0058da0b5e8a40858e013661d05c010595d241b719a685670a9c4fe00004da00043b3be000042e66090059767cb6a7bb71c405ab0d01fad8ee1ac39aa3100000002273574c806106e5a48d73a0000c120cc000dc2684056499adad01d8588f32bef67d1e15e966c168bb41c3307d66a005a8432f116ad2a4c000222678320c332c3345b0000e82cd40003535b9450c04f834c7262aa38a800000000003da7c19920000003dc52405640000000000c1f6c71c187ce21200006b40006b02ceaa880006013e90000ab891e29e10900001682ec0d1c69274f0ab814c000845000316852a2b100cb2c93860002fc9494000000253b5f97f400028180009fce6f17e30b8fda5e608691080003d61918000c30f75444102dafab741241881d7e00025cb25d94c3fb68d000000008225685195dc4352408e21a5c5e11141c28db80000002cdcc14b6060a2c143a6b9900fab1c00060f74188f8f584125af0aa000060856fb3288f030f34f396cc322030250ccc0008fa00000009840005cb910c000b3b48880018c80000762fe5b365091b080000000000d18001c3a6d44f01604d5200014d80189ae7df0000150000a981d98a2c000d1f0001f300005526dd0000000b2c5ed88b50aa00041200000009b860536b0414d3e23b89bc000e9469bb285e26f3b134af140003272d504613a000003180003e668330482b870451677a38e1432b4001a1eec34c2411f700011a86c000000014ea31511eb2e00e2a5516f022c762cf50003ae00003c235e2fc9accd881f0a5401144ae2eb0c24a523c13d997a4f1247c49b1d84be2979191212046ab4b1cc02842786354690c85e4ad6865a0b10c442574932ca45feba236907498f25c974f215d9ae68e0e1a4001aae60748a3dcc687ff3b7804d6f4dbf24c8765b6e
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa6d859d1620400159d073a2c408002b360e745881000537428e8b102000a6d851d1620400d4dd03aa2c40801a9b207545881058537c06a8b1020b0a6d80d516204161cce21aa2c4082c399443545881058d36c2ca8b102000e2f5495162040015cf02aa2c40801ab9205545881000717c22a8b102000e2e745516204001c5ae8aa2c40800399e0554588100353740aa8b102006a6c815516204001cc902aa2c40801a99205545881058d37c02a8b1020b1a6d805516204163cce20aa2c4082c799441545881058537428a8b102000a6f855cd62040014d90ab9ac4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac408003335cc735881003573408e6b102007ae5811cd620400b5d50039ac40801eba600735881000557420a6b102000aad8414d62040011dd0fa1ac4080023b61f43588100053742e86b102000a6d85d0d6204001c5aa9a1ac4080038b55143588100053742886b102000a6d8510d620400d4dd0ba8ac40801a9be1551588100053742e82b102000a6d85d05620400dcc8a3a0ac4080029be1541588100053642a82b102000a6e85cc562040014db0b98ac408002aba13315881000556c2662b10200487c85dd9320400b1b907bb264080163b20b764c81000666196ec990200087f855d932040090f90abb26408003330c9764c8100043ec36ea9902000c3e64dd532041598bcc7baa64082af1b98b754c8100043f43aca990200087c875953204001c9864b2a64080030fdd5644c8100061e3aac89902000e8c32591320400b1b90eb1a640800317dd5634c8100062e3aac69902001acc8258d320400b1d90eb1264080031bdd5624c810006363aac49902002acc83589320405d0fb0dbaa62080030f993754c41019e2f31eea9882000c6e62dd531040010fd0eb2a620802a1f21d654c4100061fbaac89882000c3c7559131040018beeab1a6208003171d5634c41000637baac49882000c6c7558931040510fb0dbaa42080030f99375484100062f31eea9082032c6e62dd521040010fd0eb2a420802a1f21d65484100061fbaac89082000c3c7559121040018beeab1a4208003171d5634841000637baac49082000c6c7558921040018f0ebbb220080032e1d376440100373928eec8802000c7b85dd910040018f10bbb220080032ee1376440100065c426ec8802000c7b54dd910040018f2a9bb2200801b1e94776440100363c28eec8802000c7b76dd5100400d6e103baa20080032eddb744401057f9928ee88802000aba87591100406f5710eb2220080038ea1564440100071cc2ac88802000e3b755911004001c70eab22200801baca05644401057758c0ac88802005cbb71591100400bd66e2b22200801b8e94564440100375928ac88802006e32515911004001d62a2b22200801b8e1456444010
  | 1 => 0x902baac8082c68fe01755901058d1ec02eab2020b1e37105d56404163c7420baac8082c78d44175590105851f428eab202000a3e85dcd640400147b0bb9ac8080030f5d7735901000557416e6b202000aad82dcd640400187aeab9ac8080028fa1473590100051ec28e6b2020008be8714d640400117b0e29ac8080028fa1772590100051ec2ee4b202000c3d75dc9640400153d07b92c808002a760f72590100061ebaae4b202000a3e851c9640400147b0a392c8080022fa1c52590100045ec38a4b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202006ab6810c9640400156b02192c808016aea0032590100055cc0064b202006a3e85d45640400d47f0aa8ac8080262fa1f31590100045ec3e62b202000a3e85cc5640400147b0b98ac8080262fa1f21590100045ec3e42b202000a3e85c85640400147b0b90ac80800f0f9d15458c100061eba2a8b182006a7481551630400b1bd0fa9ac6080163721d5358c1002c6f43e86b182000a5e85d0d63040014bb0ba1ac608003875534358c100056741686b182000acd82d0d630400b1b90ea1ac608003875514358c1002c6f43c64b182000a9e841d5630400153b083aac60800297a167458c100052ec2ce8b182000ace829d1630400159b053a2c60800297a147458c100052ec28e8b182006a5e81d51630400d4b903aa2c6082c297e035458c105852ec06a8b1820b0e5710d516304161caa21aa2c6082c6976165458c100070faa4a8b182000ad781551630400d5a902aa2c60800387e115458c100070f3a2a8b182000e1d745516304001caf02aa2c60801a97a055458c100352e40aa8b182000e5481551630400d4a902aa2c6082c697e015458c1058d2ec02a8b1820b1e57105516304163caa20aa2c6082c297a145458c100052fc2ae4b182000a5c855c963040014bd0a392c608002976147258c100054f420e4b182000a9d841c9630400199ae4392c60801ab5a047258c100456ac08e4b182005ada801c963040115b300392c608002a7a105258c100054ec20a4b1820008de87d0963040011bb0fa12c60800297a174258c100052ec2e84b182000e1d54d096304001c3aa8a12c60800297a144258c100052ec2884b182006a5e85d45630400d4bf0aa8ac60800297a174158c100052ec2e82b182006e5451d0563040014bf0aa0ac608002972154158c100052f42e42b182000a5d85c85630400153d0990ac608002a76132158c1001e1f3a2a8b102000c3d74551620400d4e902aa2c4080163ba1f525881002c7643aa4b1020058ee87d0962040014dd0ba12c4080029b617425881000716aa684b102000ace83d09620400159b07a12c4080163b21d425881000716aa284b1020058ee87cc9620400155d083aac408002ab61075588100053742ce8b102000
  | 2 => 0x364541100043fc3ac6a82200487c8758d504400147f08b1aa0880968f211635411000537c12c6a822023a6c8258d50440010ff0eb12a0880121f21d62541100051fc22c4a822025a3c8458950440014bf06b12a0880929720d6254110034bb43ee2a822000e3464dc5504400d8ecec38aa0880038d1907154110254bb430e2a822006c76861c5504400d2ef0838aa0880025d61071541100069bb20e2a822000c76641c550440018e8c838aa0880034d19071541100061a320e2a822006c77601c550440e9ae48038aa0880035c500715411002db840462a822000974874c5504400b4e90c98aa088016dc201315411002db840442a82200097487485504400b4e90c90aa088016dc201215411002cea43a629822005ad4864c5304400b7a10098a608807e9e219504c1101263c3b2a09822024e58635413044001ae0e2a826088003d44c5504c11002c7b436e290220059e487485204400b5c90c90a4088016f820121481100cd3c432a09022023c78765412044047cd0c4a8240880035c1c55048110007b090aa0902200687e87d97104400d0f90fb2e208801a9e60365c411057e1fbaec988220afc3c75d93104400d4f10ca8620880171e9d950c4110035b840aa18822005d727154310440958f4edb2e20881372e9db64c41100343f40ee8b28200687c81dd165040090ff01ba2ca080121f603745941058c3ec3ce8b282000c3f749d165041674ef02ba2ca0801a9d20574594100061fc22e8b282000c77815d1650400d0fd02ba2ca0801a1f20574594100063a40ae8b282006874815d165041630ff00ba2ca082c61f60174594105843f438e8b282000a3e841cd650400147b0839aca080021fa1f43594100043ec3e86b282000c3d74d0d65040014dd05a1aca080029b60b43594100061eba286b28200087e8710d65040010fb0e21aca080028fa1072594100051ec20e4b28200087e87d0965040010fb0fa12ca080030f5d342594100052f41e84b282000a5d83d09650400187ae8a12ca080021fa1c42594100043ec3884b28200087e870c965040010fb0e192ca080028fa1032594100051ec2064b282006a76810c965040014eb02192ca080169ea0032594100053cc0064b28200a87e87d0565040010fb0fa0aca0801b1d1c741594100043fc3a82b28200a87c8750565040150fd0f98aca080021f61f31594100051f42662b282000a3d84cc565040150fd0f90aca080021f61f21594100051f42642b282000a3d84c85650400187eeb3aac8082c68f61e75590100351f40ceab202006a3c819d5640416147f013aac8082c28f60275590105871b884eab2020b0e3a109d56404161c6a213aac8082caade0575590100355a40aeab202000c3f875d56404001c6f02baac80801a8fa0575590100351e40aeab202000e34815d5640400d46
  | 3 => 0xab1220038be87dd1624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd162440010ff0aba2c4880121f21574589100046fc1ae8b1220028dc835d1624400117d0e3a2c4880030fdd474589100061e3a8e8b12200087e87d5162440090f90faa2c4880030fdd3545891001e1e3a6a8b1220bac5c73d5162440010fd0eaa2c4880021f21d54589100061fba2a8b122003c3c7455162441738b8e6aa2c48800a37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062faa6e6b122000c5d54dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001998e7b92c48800e3b21d425891000716aa284b1220b8ccc7350962440010fd0e28ac4880030fdd051589105be1e3a0a2b122000c5f7314562440f98b8e628ac4880021fa1f50589100243e43ea0b122000c3f74d41624416d878e9a82c48800317dcf50589104562e39ea0b12200487e85dd932440010fb0bbb2648800e2fa13764c9100045ec26ec992200487e859d932440010fb0b3b26488003330ca764c9100043fc2aec992200487c855d9324400117f08bb2648800e2f211764c9100046fc1aec99220008ef825d932440090f90a3b26488003330c8764c9100043f436ea9922000c3c64dd5324400d2ed03baa64880021fa1f654c9100043e43eca9922000e4c32d95324400187eebb2264880030f1d7644c91000746196c8992200687e869da5144001878c93b4a28801b1ed827694510036b8084ed28a20b5a3e86d92514400187cedb24a2880030fe1f649451057e1e43ec928a20afc3e71d92514415fc6ce3b24a2880030f5c364945100043fc3ac728a2000a3f8458e514406947908b1ca2880029be09639451019536412c728a200087f8758a514400147f08b14a2880d28f21162945100052fc1ac528a2033a5c8358a51440055a906b1462881d21fa1b754c5100061e326ea98a207c87e87d9531440950f90fb2a6288003950c7654c5100061fbaec898a2000c3c75d9131440958e8ed28a62880cf9518e514c510256b8384a298a2033c7476dd531440958e8edb2a62880039518f654c51026e5a3b6c898a20028f4875893144001ae6ea3826288002ec610704c51000d72412c710a207487e86dd52144001878c9baa42881aa1fa1f65485102543e43eca90a2000e6421d95214400187eebb2242880030f1d764485102563a3b4a290a2032e64629452144095ae0e128a42880cb1d1db75485102563a3b6ca90a2000e6462d95214409b968edb2242880163d219734851002cf8402e690a20018f48758d2144001ae6ea3824288002ec61070485105a51f436c8a822000c3c76d91504409be6021b22a0882bf0fe1f64541100061e43ec8a8220afc3c71d91504409b87ee1b22a0880038edc
  | 4 => 0x44400153f06b96c888002a720d72d911021d5b408e5b22204dab5811cb644400117d0e296c8880022f61c52d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100055b40865b222000ab5810cb644409b57500196c888002ae60032d91100051f438a3b2220afa3c87147644415f47d0228ec8881362fa1f31d91100045ec3e63b222000a3e85cc7644400147b0b98ec8881362fa1f21d91100045ec3e43b222000a3e85c87644400147b0b90ec8880deada0770d91100051f43ea1b2220afa3c87d43644415f47d03a86c8881368f60350d91100061fba2a9b1a2003c3c7455363440010fd0fb2ac6880030f1d36558d1000636396cab1a200087e871956344001878e832ac6880031b1c86558d100061fb2ee8b1a2000c3c65dd1634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac7219163440018decbb92c6880031b1977258d1000657b26e4b1a2000cac64dc963440090fd0fbaac6880021f6137558d100045fc22eab1a20038bc845d563440011df04baac6880063b2097558d100043f438eab1a20038be87dd1634400187eebba2c6880030f1d77458d100061fc2ee8b1a2000c3c85dd163440010ff0aba2c6880121f2157458d1000477c12e8b1a20018ec825d1634400117d0e3a2c6880030fdd47458d100061e3a8e8b1a200087e87d5163440090f90faa2c6880030fdd35458d1001e1e3a6a8b1a20bdc6c72d5163440010fd0eaa2c6880021f21d5458d100061fba2a8b1a2003c3c7455163441798d8e4aa2c68800e3721d4358d100070eaa286b1a20bbccc7250d63440031dd0fb92c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031bd537258d1000636aa6e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440010fd0e28ac6880030fdd05158d105be1e3a0a2b1a2000c6f7214563440d58d8e428ac6880021fa1f5058d100243e43ea0b1a2000c3f74d41634416d878e9a82c6880031bdcb5058d1042e36396a0b1a2000c3f745536244007878e8aa6c4880121fa1b75589100043f43ecab122000c3c74d9562440018b8e7b2ac4880021fa1c65589100061e3a0cab122000c5c73195624400717d0dba2c4880030fd9774589100061e32ee8b1220008be87d91624400187eebb22c4880030f1d764589100064e39ec8b1220008be87191624400187eea322c4880030f1d464589100064e398c8b122000c5f65dcd62440018b8cbb9ac48800327d9373589100064e326e6b12200487e87dd562440010fb09baac48801a1fa0775589100045fc22eab1220038bc845d562440011bf06baac48800a3720d75589100043f438e
  | 5 => 0x800387a0c64d95100070ec18c9b2a2000e2e821936544001c5b04326ca880038d60464d95100071cc00c9b2a20b5c3f70193654400187ae0326ca880028fa1263d95100051ec24c7b2a2000a3e8498b654400147b09316ca880038d19241d95102553a43283b2a2000e38649036544001e6483206ca88003cc50540d95100343f40ee9b2a200687d80dd365440010fb0f3a6ca880030fe1174d95100343e40ae9b2a200087f805d365440010fd0e3a6ca880030f5d074d95100052f418e9b2a2000a5d831d365440014dd043a6ca880029b60874d951060d3b408e9b2a204aa75811d365440954f5003a6ca880029e60074d95100051f424e7b2a2000a3d849cf65441814ed0239eca8812a9d60473d95100043f43e87b2a200087d87d0f654400187ee9a1eca880029ba0b43d951000536c1687b2a2000c3f7450f65440010fd0e21eca880021f61c43d95100051f424e5b2a2000a3d849cb654417f4ed02396ca8812a9d60472d95100043f43e85b2a200087d87d0b654400187ee9a16ca8800297a0f42d95100052ec1e85b2a2000c3f7450b65440010fd0e216ca880021f61c42d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95100053b40865b2a2000a75810cb65440954f500196ca880029e60032d95102543f43e83b2a200087d87d07654400d0ff0f20eca8801a1f21e41d95105bc3fc3a83b2a204a87c8750765440010fd0e20eca8803e1f61c41d95100052f41883b2a2000a5d8310765440014dd0420eca880029b60841d95102553d40083b2a2000a798010765440950fd0f98eca880021f61f31d95100051f42663b2a2000a3d84cc765440950fd0f90eca880021f61f21d95100051f42643b2a2000a3d84c8765440714ed03b86ca8801b1e5c370d95100043f43e81b2a200087d87d0365440010fb0ea06ca882fb1e5c140d95100051f436ebb222000c3e76dd7644400147d0c3aec8880030f9d875d91100061f3b6cbb2220008bd87997644400147d0b32ec8880022fe1d65d91100051f430cbb222000c3e76197644400147d0b31ec8880028f61663d91100051f42cc5b222000a3d8598b644400147d0c28ec8882d70f9d851d91100755d436e1b22204ddb371dc3644416987ceda86c888002cda0750d911057d1f40eebb222000a3d80dd7644400147d0b3aec8880030f5d475d91100051f438ebb222000c3e871d7644415f47d023aec8880028f60075d91100061fbaee7b222000a3e859cf644400147b0b39ec8880028fe1573d91100051e42ae7b222000c3f755cf644400155f04b9ec888002ab20973d911024d5b408e7b22204dab5811cf644400117d0e29ec8880022f61c53d91100061fbaee5b222000a3e859cb644400147b0b396c8880028fe1572d91100051e42ae5b222000c3f755cb6
  | 6 => 0x43fc2ae8b16200487c855d162c40010fd0faa2c5880121f21f5458b100043f43aa8b16200087c8755162c400d1d90ea12c5880038b5514258b100043f43ea0b16200487e85dd932c40010fb0bbb2658800e2fa13764cb100045ec26ec99620058f681dd932c40010ff0abb265880121f215764cb100343f436ea996200697681dd532c40010fd0fb2a658801a1f21f654cb1000726196ca99620009b584dd931c400136b09bb2438831a1f21d635431062c3e43ac4a862005a75868c550c40012e90e98aa1880169d61a2154310004ba43a42a8620059d4874c530c400b3c90e90a41882c30fd0374596105861ea06e8b2c20b187d879d1658400187ee93a2cb080169ea0274596106253cc04e8b2c2000a77815d165841874e902ba2cb080030fe1174596100063bc0ae8b2c2000c74815d165841610fd0e3a2cb080029be09735961000536412e6b2c2000a3e841cd658400147b0839acb080021fa1f43596100043ec3e86b2c2000c3d74d0d65840014dd05a1acb080029b60b43596100061eba286b2c200087e8710d65840010fb0e21acb0800297e0d72596100052e41ae4b2c2000a3e841c9658400147b08392cb080021fa1f42596100043ec3e84b2c2000c3d74d0965840014bd07a12cb080029760f42596100061eba284b2c200087e8710965840010fb0e212cb080021fa1c32596100043ec3864b2c2000a3e840c9658400147b08192cb080029da0432596100053ac0864b2c2005a7a800c965840014f300192cb080028fe1171596100051e422e2b2c20c2a7b805c565840010fd0fa0acb080021f61f41596100061fba482b2c203487f87505658416f0f90ea0acb0804e1fa1c41596100043ec3882b2c2000c3f7410565840014bd0620acb080029760c41596100053741082b2c2000a6d82105658400b4f50020acb080029e60041596100043f43e62b2c200087d87cc5658400147d0998acb080028f61331596100043f43e42b2c200087d87c85658400147d0990acb080028f613215961000477c12eab1c20018ec825d563840014e902aa2c7080163721d4358e100070eaa286b1c20008df835d562840051b906baac5080029d2055458a1002c7643a84b142000e2d5450962840090f90bbb265080021fe15764ca100243e42aec994200087d86dd532840010fd0eb2a65080021f21d654ca1000726192ca99420058dc8758d328400359904b1a65080163b21d624ca100156641ac4994200087d86dd531840670fd0eb2a63081f21f21d654c6100043ec36ea90c203287e8759521840d50f90eb2a43080021fa1b74d95100243fc3ec9b2a2000c3d74d9365440010fb0f326ca880021fe1d64d951007c3ec38c9b2a2000c3d7419365440014bd06326ca880029760c64d951000537410c9b2a2000a6d82193654400187b0e326ca8
  | 7 => 0x798014563480010fd0fa82c6900121f21f5058d20566363b6ea99240ace4c63dd5324800559d0db1a64900026b613714c920006b5ba8e0992400487f875d761480010ff08baec2902161fe0175d85200243f42ee9b0a400087d85dd361480090ff0faa6c2900021f61f54d85200043fc3aa9b0a400087d8755361480014e902aa6c29000f2b9d142d852000716aa285b0a400487f87d4361480010fb0fa86c2900023de1d611852001e1f3a2a830a4000c3d74550614800d4e902aa0c2900021fe1573185200243e42ae630a4005c6d72d4061480010ff0eb1ca29001a1f21d639452003536432e528a400096f874ca51480954d90c994a2900cf9318d32945200243f42ced18a400087d859da314800d1ed033b462900121fa16764c5200043ec2cec98a40058ec865cd21480d52dd0f28a429001b991865148520006b5ba8e090a4000bc9831c121480010ff0eb1aa0900121f21d635412002db5406e4a82400096c874c9504800b4d90c992a0900939318d325412002db440264a82400a87e87d8550480470fb0fb0aa0900025b21d215412002d3643242a824005b688048550480017970690c60900167321d324c12002d66432649824001ccc764c9304800b79100992609032fd2d41324c12011e3c3b2a09824024e58635413048047ad0e4a826090003d24c9504c12002de443a649824001dc8874c9304800b7950c9926090016f2219324c12001764432649824002ecb764c93048003b94ec9926090007721d9324c120017643b2649824001cc8764c93048001e970a992609032fd2215324c12066de5c226498240cdbc9844c93048199e96a89926090333d2551324c120005e5c0a6498240cbf48514c930480658f0ed28a6090003d24ca514c120005e4c1a429824000fc131485304800d87f08ba6cb8801b0f90574d97100361e20ae9b2e200687e87d0f65c40010fb0fa1ecb8832b0fdd343d97100053741687b2e2000a6d82d0f65c419387ee8a1ecb8801a1fa1c43d97100043ec3887b2e200687e87d0b65c40010fb0fa16cb883230fdd342d97100052f41e85b2e2000a5d83d0b65c418f87ee8a16cb8801a1fa1c42d97100043ec3885b2e200687e870cb65c40010fb0e196cb880028fa1032d97100051ec2065b2e2006a76810cb65c40014eb02196cb8812a9ea0032d97100053cc0065b2e2000c3d74d0365c400187ae8a06cb8801a5da077558f100243f43eeab1e200087d84dd563c400d0fd03baac78801a1f2077558f100043f438eab1e200087f855d163c40090f90aba2c7880021fa1f5458f100243e43ea8b1e200087e8755163c40010f90eaa2c78801a3721d4358f100070eaa286b1e200087e87d4163c400d2ed03baac5880121fa1f7558b100043ec26eab16200687e81dd562c400d0f903baac5880021fa1c7558b100
  | 8 => 0x2ba2cb100030fe1174596200061fa12e8b2c4000c3d425d165880018ef02ba2cb1001a1f20574596200063a40ae8b2c4006874815d165881610fd0e3a2cb100169ea0273596206753cc04e6b2c4000a6f825cd65880474d904b9acb100028fa1073596200051ec20e6b2c400087e87d0d65880010fb0fa1acb100030f5d3435962011d3741686b2c4000a6d82d0d658800187ae8a1acb100021fa1c43596200043ec3886b2c4000a3f845c5658800147908b8acb1001b1d9c471596200043f43e82b2c400087d87d05658800d8e8e3a0acb1001a1f21e41596200061fba482b2c400087f8750565880010f90ea0acb100021fa1c41596200043ec3882b2c4000c3f7410565880014bd0620acb100029760c415962011d3741082b2c4000a6d82105658800d8e8e220acb100169ea0041596200053cc0082b2c400087e87cc565880010fb0f98acb100028fa1331596200051ec2662b2c4005a7a800c565880014f30018acb100163721d4358e200070eaa286b1c400487e85dc563880010fb0bb8ac7100029e6005158e200043fc2ae930c400487c855d2618800d0fd0faa4c31001a1f21f54986200343f43aa930c400687c8755261880010ff0ab9cc3100121f21573986200243f43eeab0c400087d84dd5618800117f08baac31000e2f211755862001c5f43ee8b0c4000c3f75dd16188001878ebba2c3100030fe1774586200061e42ee8b0c404dc3f50dd1618809b87aa1ba2c3101372bc83745862026e56906e8b0c400087f855d161880090f90aba2c3100030fdd474586200061e3a8e8b0c400087e87d5161880090f90faa2c3100030fdd3545862001e1e3a6a8b0c400087e8755161880010f90eaa2c3100030fdd1545862001e1e3a2a8b0c404a87e87145618800187ee828ac3102df0f1d0515862001e5a3a482b0c40058f48750561880010ff08bb4a3100021f61176946200343f40aed28c400687c815da518800d0fb00bb4a31012b1bc81769462025636902ed28c407487f87586518800147f08b0ca3100d28f21161946200243e42eec98c400087f855d931880090f90abb263100022fe11764c62001c5e422ec98c400087d86dd531880010fd0eb2a63100021f21d654c62002c7a43ac298c4000bcb824c530880071bf0ea1ec6900038755143d8d200043fc2ae3b1a400487c855c7634800117f08b8ec69000e2f21171d8d200053cc00a3b1a400487e87dd563480010fb09baac69001a1fa077558d200046fc1aeab1a40008ef825d563480010fd0e3aac6900021fe157458d200243e42ae8b1a40008f7815d1634800d1e902ba2c6900021fa1f5458d200243e43ea8b1a400087e8755163480010f90eaa2c690003171d77358d20006363aee4b1a400487e85dc563480010fb0bb8ac6900021fa1c5158d200343e438a2b1a4000a
  | 9 => 0x41596300061fba082b2c6024a5e83105658c0014bb0620acb180029ba08415963000536c1082b2c6006c7471105658c00b4f50020acb180029e60041596300043f43e42b2c600087d87c85658c00147d0990acb180028f613215963002d3d40042b2c6000a7980085658c00b1d90ea12c5180038b5514258a300243f42ee2b14600087d85dc5628c0014f30028ac5180021fe1574986300243e42ae930c600687e87d52618c00d0f90faa4c31801a1fa1d54986300343e43aa930c600087f855ca618c0090f90ab94c3180121fa1f75586300043ec26eab0c60008bf845d5618c00717908baac31800e2fa1f74586300061fbaee8b0c6000c3c75dd1618c00187f0bba2c3180030f217745863026e1fa86e8b0c604dc3d50dd1618c09b93e61ba2c318137274c374586300043fc2ae8b0c600487c855d1618c00187eea3a2c3180030f1d474586300043f43ea8b0c600487c87d51618c00187ee9aa2c31800f0f1d354586300043f43aa8b0c600087c87551618c00187ee8aa2c31800f0f1d154586302543f438a2b0c6000c3f74145618c16f878e828ac31800f2d1d2415863002c7a43a82b0c600087f845da518c0010fb08bb4a31801a1fa0576946300343e40aed28c604ac5f305da518c0958ba60bb4a3181d21fe1d61946300051fc22c328c6034a3c84586518c0090f90bbb243180021fe1576486300243e42aec90c60008bf845d9218c00717908bb243180021f61b75486300043f43aca90c600087c87595218c00b1e90eb0a431800e3be1d42d893000716aa285b12600087f855c7624c0090f90ab8ec4980022fe1171d893001c5e422e3b126000a7980147624c1578b8edbaa64982af9318b754c93000d67436c4992600099d84dc5324c001ab6ea38264980121fe1d75d85300043fc22ebb0a608a87f805d7614c0090fd0bba6c2980021f61774d85300243fc3ea9b0a600087d87d53614c0010ff0eaa6c2980021f61d54d85300053a40aa9b0a6003c9e7450f614c001c3aa8a1ec2980121fe1f50d85300043ec3ea1b0a60008f787584614c00787ce8aa0c2980030f5d154185300353a40aa830a600087f855c8614c0090f90ab90c298017175cf50185300352e432e728a600095f874ca514c0954b90c994a2980cb9318932945303e4af43ca298a6006e5461945314c001ab6ea3826298002f2608704c5300243f42ced10a600087d859da214c00d1ed033b442980121fa1676485300043ec2cec90a60058dc865cd214c00b6b501b9aa0980025721d325413002d2e43264a826023e4c624c9504c00b6b100992a09802a1fa1f61541301243ec3ec2a82600095c874c5504c00b4b90c98aa098016d620131541300343f40ee8b2c40b0c3f40dd1658816187a81ba2cb102c61f61e74596200061fba4e8b2c4000a77815d165880014e9
  | 10 => 0x30aa00087d87d0c615400187ae9a18c2a80029ba0b431855000536c168630aa0cae3441d0c615400d4ed03218c2a80029d60643185500061eba28630aa000a778150c615400d4e902a18c2a83278d10543185500343f4388630aa00087d8710c615400d0fd0fa10c2a80021f61f42185500061eba68430aa000a5e83d0861540014bb07a10c2a83238d10742185500353b40c8430aa000a7581908615400187ae8a10c2a80029de0542185500353a40a8430aa0c7e3441508615400d0fd0e210c2a80021f61c42185500043fc3a6430aa00687c874c8615400d0fd0e190c2a80021f61c32185500051f4206430aa000a3d840c86154001c9a64190c2a801a9da0432185500053ac086430aa074a7a800c861540014f300190c2a801a9d61f41185500063ac3e8230aa006a7684d04615400dc6d09a08c2a801b1ddd341185500063aba68230aa000a7580d04615400d0fd0fa00c2a80021f61f40185500061eba68030aa006a7481d006154001c6e83a00c2a801a1fa1d401855067c3ec3a8030aa000c3d7450061540014ef02a00c2a801a9d20540185500071ba0a8030aa0cfc797050061540472dd05bb462a80025b60b768c550004bcc06ed18aa00097b805da31540012f301bb262a80021fe13764c5500043ec26ec98aa000c7980dd931540010fd0d3b262a80024fe11764c55012c9e422ec98aa00096f825d931540472d904bb262a80025ee01764c5500043fc20ec98aa00087d841d931540018be603b262a809257a0f7688550004aec1eed10aa00097980dda21540012f700bb442a80021fa1b73885500043ec36e710aa023975878c621540012f301bb242a80021fe1376485500043ec26ec90aa000c7980dd921540010fd0d3b242a80024fe11764855012c9e422ec90aa00095f835d921540492b906bb242a80025ee0176485500043fc20ec90aa00087d841d9215400d0f9023b242a80031bc8076485500043fc32e690aa00087c865cd21540472e90e98a42a801a1fa0774596305861fa06e8b2c60b0c3d40dd1658c1630fb0f3a2cb180030fdd274596300053bc0ae8b2c6000a74815d1658c00187f08ba2cb180030fd0d74596300061ea1ae8b2c6000c77815d1658c00d0f902ba2cb180031d20574596300343a40ae8b2c60b087e871d1658c00b4f501392cb1818a9e60272596300052fc1ae4b2c6024a5c835c9658c00147d08392cb180028f61072596300043f43e84b2c600087d87d09658c00187ae9a12cb1809297a0f42596300052ec1e84b2c6000c3d74509658c0010fd0e212cb180021f61c42596300051fc22e2b2c6000a3c845c5658c00d8ece238acb180021fa1f41596300043ec3e82b2c6006c7471d05658c00d0f90f20acb180030fdd241596300043fc3a82b2c600087c87505658c0010fd0e20acb180021f61c
  | 11 => 0x540012f301bb264a8003930cb764c9500043fc26ec992a00087d84dd9325400d0fd03bb264a80031e603764c9500043f434ec992a000d4c329d932540012bf06bb264a80025be09764c950004bdc02ec992a02593e841d9325400127b083b264a8003530c8764c9500051ec20ec992a000e4c321d932540010ff083b264a80030fa10764c9500043ec20ec992a000c3d841d9325400107b083b264a80031bcc8764c9500062f190ec992a000c5c321d932540018d8643b264a8003130c8764c9500343f408ec992a000c5f301d932540018de403b264a80021fa1b714c9500043ec36e2992a02593e84dc5325400127b09b8a64a80165ea00714c950004bcc00e2992a02587d87d93615404b87ce9b26c2a80030f5d364d85500053a40ac9b0aa000a7586d0761540014eb0c20ec2a80038dd9041d8550005b8c0083b0aa00097980dd2615400187ee9b24c2a80970f1d364985506ae3cb86c930aa000c3d74992615400d4ed03324c2a80029d606649855012c3fc3ac930aa000c3d74592615400d4e902b24c2a82fb1e5c164985500353b40cc730aa024c5e7358e61540014df04b1cc2a80029b20963985500353a40ac730aa000a3e8418e615400147b0831cc2a801a9da0662985500052fc1ac530aa000a5c8358a61540478dce4b14c2a801a9d20562985500051f420c530aa000a3d8418a61541a9ae2e1b0cc2a801b9c18570985505843e436e8b0aa02593e87dd1615400187f0dba2c2a80030fd8374585500069db06e8b0aa00087f865d161540012ef02ba2c2a80025ee0174585500049f438e8b0aa00087e87d91615400187ee9b22c2a80970f1d3645855012c3e43ac8b0aa000c3f74591615404b878e8b22c2a80029d20564585500069a3a6c2b0aa000c3f749856154001878e930ac2a80034edd370585500069c3a6e0b0aa0d3d7371dc1615404b0fb0fb20c2a80970f9d364185500061eba6c830aa006a7681d9061540014eb03b20c2a80021f61e64185500053bc0ac830aa006a748159061540010fb0e320c2a801a9da0464185501243ec3ec630aa006a7681d8c61540014df04b18c2a80029b20963185500051f420c630aa000a3d8418c61540018bae6318c2a801a9da04631855011c3ec3ec430aa006a7681d8861540014bf06b10c2a80029720d62185500051f420c430aa000a3d8418861540018dae4310c2a801a9da046218550695b8c04c230aa00087f87584615400147f08b08c2a80028f2116118550004bbc3ac230aa000b348458461541a36e700b08c2a80029d61b4118550004bac388230aa006a77861046154001c6ec8208c2a80038d1904118550005b8c008230aa006c3f845d0615400d8e902ba0c2a801b0f90574185500361e20ae830aa006c74415d061541a10ff00ba0c2a801b1dc4174185500343f43e86
  | 12 => 0x8021f6137558d210043ec06eab1a420087e871d563484010ff0aba2c6908121f2157458d210047dc02e8b1a42058f8805d163484010fd0faa2c6908121f21f5458d210043f43aa8b1a420087c8755163484014e902aa2c6908021fa1c5158d210043f43ea0b1a420487c87d4163484010ff0eb1ca29092a1f2197094521036b210ae128a424ac78605c2514840dae620b84a2909aa1fa1b754c5213e43f43eca98a423287c87d9531484658e8ed28a62908cf9518e514c521196b2394a298a4233c7476dd53148401ac8e5baa62908cb1d1db654c5210072a31eca98a4206de3105c221484014f301baec0908029e60075d81210043fc2ae9b02420487c855d360484010fd0faa6c0908121f21f54d81210043e43aa9b02420087f855cf60484090f90ab9ec0908038b55142d81210043f43ca3b024200a798094760484010fd0e28ec0908029e60051d81210243f436eab02423287c86dd560484010fd0fb2ac0908030f1d365581210062e39ecab02420087e871956048401878e832ac090803171cc65581210061fb2ee8b024200c3c65dd160484018becbb9ac0908031719773581211443ec3eca3024200c3e74d9460484018bce7b28c0908029e60365181210061f3a0ca3024200c5e7319460484d58eae2328c0908029e60065181210061fb2ae83024200c3c655d060484018becab98c0908031719573181210047dc3ac0302422487d87d93635404b87ce9b26c6a80030f5d364d8d500061fba2c9b1aa000a748159363540014bb0d196c6a80165ea0271d8d5007cbcc04e3b1aa00093f845c7635404b27908b8ec6a80025be097458d5011cb6412e8b1aa000977815d163540012e902ba2c6a80025ee017458d5000636396c8b1aa02487c87591635400187ee8b22c6a80031b1c96458d500053a40ac8b1aa02396e87dc963540018dec9b92c6a80031b5937258d5000637b06e4b1aa000d6b60dc963540018deec392c6a800353dcc7258d506beadb9ee0b1aa000d6b72dc16354001ad0e5b82c6a808e1f61f64d895012e1f3a6c9b12a000c3d74d93625400187ee8b26c4a80029d20564d895011c3ec3ec7b12a000e4c32d8f62540010ff0eb1ec4a808e9b20963d895000536c3665b12a00597a809c7625401f2f30138ec4a80024fe1171d895012c9e422e3b12a00095f835d162540492b906ba2c4a80025de057458950004ba40ae8b12a00097b805d162540018b8e7b22c4a808e1f21d64589500061fba2c8b12a000c5c7359162540014e902b22c4a809257a1f73589500062fb26e6b12a000c5d64dcd62540018bec1b9ac4a800356d8373589500062fbb0e6b12a00087e87d8d62540498b8e7b1ac4a808e1f21d63589501262e39ac6b12a023a6c8258d6254001a98e7b12c4a800356dcf7058950006ac39ee0b12a0d6d6b72dc162
  | 13 => 0x61e3a0cab026200c6c72195604c40187ecbba2c0988030f197745813100637b2ee4b026200c6c65dc9604c45d0fb0fb28c0988030f9d3651813100637396ca3026200a7980d94604c40187ce8328c0988031b9c865181313e63ab88ca3026200a7980194604c40187ecaba0c0988030f195741813100637b2ae43026200c6c655c8604c4011f70eb00c0988021fe1175d8e210343f40aebb1c420687c815d763884010ff00baec7108121fe1f54d8e210043ec3ea9b1c420087f8755363884010fb0eaa6c71081a9d20554d8e210243fc3ea1b1c420087d87d43638840d4e902aa2c71081a37a1f5358e210346e43a86b1c4200e1d5450d638840187ee8aa2c11080f0f1d154582210243f42ee6b04420087d85dcd608840d1f10ea02c1108021fa1b74d9521034bb40ee9b2a420487f87d93654840187ae9b26ca908021f61e64d95210052f41cc9b2a4200a5d8399365484010ff0eb26ca908a21f61c64d95210061eba0c9b2a4200a3e8498f654840147b0931eca908034bdd142d95210071632285b2a42d9a7681dd365484654eb03ba6ca908030fd0b74d95210061ea16e9b2a4200c7681dd365484018eb03ba6ca908021f60374d95210043ec3ce9b2a4200c3f845d365484010ff00ba6ca908021fa1c74d95210061eba0e9b2a4232a6e821d365484014db043a6ca908ca9ba0b73d952100536c16e7b2a4200a3e849cf654840147b0939eca90b629da0473d95211953ac08e7b2a420087e87d0f65484010fb0fa1eca908030fdd343d95211953741687b2a4200a6d82d0f654840187ee8a1eca908021fa1c43d95210043ec3887b2a423287e87d0765484010fb0fa0eca908030f5d241d95215bc3fc3a83b2a423287c8750765484010fd0e20eca908a21f61c41d95210061eba083b2a4200a5e8310765484014bb0620eca908ca9ba0841d952100536c1083b2a4200a7a8010765484014f30020eca908ca1fa1f31d95210043ec3e63b2a4200a3e84cc7654840147b0998eca908021fe1170d95210343e40ae1b2a4200a3e841c3654840147b08386ca9080297a0c70d95210052ec18e1b2a4232a6e821c365484014db04386ca909529da0470d95211953ac08e1b2a420087e87d0365484010fb0fa06ca908030f5d340d95210043f43c81b2a420087d8790365484010fb0ea06ca908030f5d140d95210043f43881b2a420087d8710365484014bd06206ca908029760c40d95211953741081b2a4200a6d8210365484014ed02206ca908029d60440d95210043f43861b2a420087d870c3654840147d08186ca908028f61030d95211953741061b2a4200a6d820c365484014ed02186ca908029d60430d952103476c16ebb1a4200a748155363484071bf0ea1ec6908038755143d8d210043f43ecab1a420087e8719563484090fd0fbaac690
  | 14 => 0x8745016094401c7686a02c1288038e50d40582510071da1280b04a200e3942501609440d4f502a02c12881a9e20540582510071da0a80b04a200e3941501609440d4e902aa2c51881a3b21d4258a3100716aa284b146200c3f74551608c407878e8aa2c1188121fa1772582310043ec2ee4b0462068f887501608c4010fd0dba6ca9881a5da0774d95310243fc3ec9b2a6200c3d74d93654c4010fb0f326ca988029ba0a64d953100536c14c9b2a620087f87593654c45d0fb0e326ca988030f5d064d95310068fba287b2a6200e1c6450f654c40147d09316ca988028f61262d95316d53b40ee9b2a6233a7581dd3654c40187e87ba6ca988030f50f74d95310063b40ee9b2a6200c7581dd3654c4010fb01ba6ca988021f61e74d95310061fc22e9b2a620087f805d3654c4010fd0e3a6ca988030f5d074d953119d2f418e9b2a6200a5d831d3654c4674bd07b96ca988029760f72d95310051f424e5b2a6200a3d849cb654c53f4ed02396ca988ce9d60472d95310043f43e85b2a620087d87d0b654c40187ee9a16ca988ce97a0f42d95310052ec1e85b2a6200c3f7450b654c4010fd0e216ca988021f61c42d953119c3f43e83b2a620087d87d07654c40187ae920eca98ade1fe1d41d953119c3e43a83b2a620087e87107654c45d0fb0e20eca988030f5d041d953119d2f41883b2a6200a5d83107654c4014dd0420eca988029b60841d95310053d40083b2a6200a7980107654c4670fd0f90eca988021f61f21d95310051f42643b2a6200a3d84c87654c4010ff08b86ca988028fa1070d95310051ec20e1b2a6233a5e831c3654c4014bb06386ca988029ba0870d953100536c10e1b2a625aa76811c3654c4674eb02386ca988021fa1f40d95310043ec3e81b2a6200c3d74d03654c4010fd0f206ca988021f61e40d95310043ec3a81b2a6200c3d74503654c4010fd0e206ca988021f61c40d953119d2f41881b2a6200a5d83103654c4014dd04206ca988029b60840d95310053b40881b2a6200a7581103654c4010fd0e106ca988021f61c20d95310051f42041b2a6200a3d84083654c4674bd06106ca988029760c20d95310053b40841b2a6200a7581083654c4014e902aa6c49880e3be1d42d893100716aa285b12620087e87d95624c4010fd0e32ac49892a1f2197094531036aa18ae128a624ac78605c2514c40dae620b84a29881b74c41708c5310053cc06ebb026200a79801d7604c4010ff0aba6c0988121f21574d81310043f43ea9b02620487c87d53604c4010f90eaa6c0988038755143d81310043fc2ae5b02620487c855cb604c4010fd0f28ec0988029e60251d81310043f438a3b026200a7980147604c4090fd0dbaac0988ce1f21b75581310043f43ecab026200c3c74d95604c4018d8e5b2ac0988021fa1c655813100
  | 15 => 0x5bb26528803170cb764ca5100636196ec994a200c4c32dd9329440d0fd03bb2652881a1f207764ca510043ec06ec994a200c5f30dd932944018de41bb26528803530c9764ca510043f438ec994a200e4c321d9329446927d09b8a65288024f613714ca511a43fc3ac9304a234c3e74592609440187ae8b24c1288038e59140982512543f43cc8b04a24aa7a8099160944950f90eb22c1288030fdd164582511a61e3a2c8b04a24a87e8798d609440147d0931ac1288028f61263582510062fb9cc6b04a24aa7a8098d60944950f90eb1ac12892a1fa1e62582510051f424c4b04a200a3d8498960944018dee5312c12892a1f21d62582510353d43480b04a206978875016094401c74c8a02c1288038e59140582510343f40ee8b04a20687c81dd1609455f87c83ba2c128abf0f10774582510053cc04e8b04a200a7b805d1609440187f08ba2c12881a1f20574582510063dc02e8b04a20087e871d1609440187ae83a2c12880297a0c74582510052ec18e8b04a200a6e821d160944014db043a2c12881a9da0474582512553ac08e8b04a200a3e849cd609440147b0939ac12880317dce73582510053cc04e6b04a200a7b805cd609440d4ed0239ac12892a9d60473582510043f43e86b04a20087d87d0d609440187ee9a1ac1288029ba0b435825100536c1686b04a24aa7a80d0d60944014f301a1ac1288030fdd143582510043f43886b04a20087d8710d60944954f50021ac1288029e60043582510051f424e4b04a200a3d849c960944018dee5392c1288029e60272582510053dc02e4b04a206a76811c960944954eb02392c1288021fa1f42582510043ec3e84b04a200c3f74d0960944014bd07a12c1288029760f42582512553d40684b04a200a7980d09609440187ee8a12c1288021fa1c42582510043ec3884b04a24aa7a8010960944014f300212c1288021fe1d32582510043e43a64b04a20087e870c960944010fb0e192c1288028fa1032582510051ec2064b04a200e4d320c9609440d4ed02192c1288029d60432582512553d40064b04a200a79800c960944950fd0fa0ac1288021f61f41582512553d40682b04a200a7980d0560944010ff0ea0ac12892a1f21d41582510053dc0282b04a24aa7880505609440dce620a0ac12892a1fa1f31582510043ec3e62b04a200a3e84cc5609440147b0998ac12892a9ea0331582510053cc0662b04a24a87e87c8560944010fb0f90ac1288028fa1321582510051ec2642b04a24aa7a80c8560944014f30190ac1288030fdd340582510053d43c80b04a24ac7a87901609440d4f503202c12881a9e206405825157f1d20c80b04a2afe3841901609440187ee8a02c12892b8e10140582510353d43a80b04a206a788750160944954f708a02c12892b8ee1140582510071dba280b04a200e3
  | 16 => 0x5d85320051ec20cbb0a6400c3e74197614c9c3c986432ec2990029da0465d85320061fb2ae9b0a6400c3c655d3614c801b1864ba6c29900e2fa1375d85320045ec26ebb0a640087d879d7614c8090ff0ebaec2990021fe1175d85320043fc02ebb0a640487e85dd3614c8010fb0bba6c2990022f61e74d85320061f3ace9b0a6400c3d759d3614c80717f0eba6c2990030f9d574d85320061ebaae9b0a6400c3e855d3614c80187b0aba6c29900327cc174d853200657902e9b0a640487f87d53614c8010fb0faa6c29900f0f9d354d85320061eba6a9b0a640087f87553614c8010fb0eaa6c29900f0f9d154d85320061eba2a9b0a64b7c3e74147614c80187ae828ec2990121fe1f50d85320043ec3ea1b0a64b6c3e74d43614c80187ae9a86c299003530c975985320051ec20cb30a64dfc5d73196614c9c18dae432cc299003530cb75585320043f43ecab0a640087e87195614c80147b0832ac29937f930c865585320353b40eca30a6400a3d84194614c80d4ed02328c2990023de1d61185320043fc2ae830a640487c855d0614c80d0fd0faa0c29901a1f21f54185320343f43aa830a640687c87550614c80787ce8aa0c2990030f5d154185320043fc2ae030a640487c855c0614c80d0fd0fa80c2990028f61065d81320053cc06ebb026400a3d841d7604c8014f3003aec0990021fe1574d81320243e42ae9b02640087e87d53604c8090f90faa6c0990021f21d54d813201e1f3a2a9b026400c3d74553604c8010ff0ab8ec0990121f21571d81320043f438a3b02640687c87147604c801a9864bacc0990028f61065981326f726190cb302640487e86dd5604c9570f90dbaac099003530cb75581320043f43ecab02640087e87195604c80147b0832ac09937b17dcc65581326ee37b90cab026400d4c325d4604c86d0fb0fb28c0990030f9d365181320053cc06ca3026400a3d84194604c80187ce8328c0992b7175cc65181326e636b90ca30264dbe4c32194604c8014f300328c0990030fd9574181320061e32ae83026400d8c325d0604c8018eecb388c0990031d1967118132006e2194e23026400c77655c4604c8018e8cab88c099003710c971181320047dc3ac030264c9c3f645d163944670f90eb22c7288030fdd16458e511a61e3a2c8b1ca20695c8750d6394593c3ec8a1ac72881a57a1e3258e510352f43464b1ca2c7c3f645d162944650f90eb22c5288030fdd16458a511a61e3a2c8b14a23287c8758d6294401c9864b1ac52881a5b21d4258a5163f17b2284b14a20696e87cc9629440d4dd0d992c5288d24fa13764ca510049ec26ec994a200d4c32dd9329440147b09bb26528803930cb764ca510043fc26ec994a200c3e84dd932944010fb09bb265288030f613764ca510041ec26ec994a200c6f32dd932944018bc6
  | 17 => 0x1080380001e00000780080000380000100480000080000181400700780e00000100700000100000480580000000480080000680881100000280280200500100101900380180080081a80e81c01200500180000780880000100200300000000100200300200300481080000100400301b80000080080080880201300000080780280400e00000000500080b00180880200000180280001600380000000100c80080380180a00400300600c00700280780a80000200a80200000400300280000380000100000680380200b00600400180400600480400d80880400200000480400500080c80280180000300000000480000100d80580280880400080000300000080000c00480300280700000d80080000480680180000100080000000280000900900700080100000100500200280f00000c00200382600280280000080100200080080000380180100d80580003c00000580100400000c80100100000100180301b80200680480700e00300b00c00080000500080680100180500080400080800280200e0088020020000040030008021fa1b74d9532006a6196e9b2a640097681dd3654c801a9864ba6ca990121fe1f64d95320061eba6c9b2a64e5e4c32d93654c8010fb0f326ca990030fdd264d95327252ec1cc9b2a64e3a6d82993654c8010ff0eb26ca990030fdd164d953271726192c9b2a643687d87193654c80187ae8326ca99003530ca71d9532006a6192e1b2a6400a7681dd3654c8014eb03ba6ca990030fd0f74d95320061ea1ee9b2a6400c3f42dd3654c80187a85ba6ca9901a1fa0774d95320063b40ee9b2a640687681dd3654c8018eb03ba6ca990021f60374d95320043ec3ce9b2a6400c3f749d3654c80187f08ba6ca9901a1f20574d95320043fc02e9b2a640087e871d3654c80187ae83a6ca990028fa1371d95320051ec26e3b2a6406c76711c7654c8010fd0fa0eca990021f61f41d95320363b38e83b2a640687f87907654c80187ae920eca990021fe1d41d95320043e43a83b2a640087e87107654c8010fb0e20eca990030f5d041d95325652f41883b2a6400a5d83107654c9574dd0420eca990029b60841d95320363b38883b2a6400a7a80107654c8014f30020eca990021fe1170d95320343e40ae1b2a6400a3e841c3654c80147b08386ca992b297a0c70d953255d2ec18e1b2a64aba6e821c3654c9594db04386ca990029da0470d95320053ac08e1b2a640087e87d03654c8010fb0fa06ca990030f5d340d95320043f43c81b2a640087d87903654c8010fb0ea06ca990030f5d140d95320043f43881b2a640087d87103654c9594bd06206ca990029760c40d953255d3741081b2a6400a6d82103654c8014ed02206ca990029d60440d9532006a6192ebb0a643687d87d97614c80187ce9b2ec2990029da076
  | 18 => 0xef2154be440901ba46cc483d60129e180786f72fd9c4463e4811471e401680003848a2421c61c000000011a7211759310d4008e3221880b981bc0001b280004de3ef93b400094f00023a43200003aaa4691c00790d313040000000001bb800054b0001088a7c00031380002e4458494800084000000010840002dd00000003d62b24a921610ea39e3a9000062e82f47a1a252a80000ca9c746d43061e787dced24a7333a124dbc6d425596c0c0c8ac3f0a4e891242e31d946cace48e0e19cdc0e422f1a917144ba00000080200000e00300080000b80000680180200000000501380200000201c00000580100000600b00000600e00580300e80000480080000000100000000000680000000300000901680100000000400000200080000580500200000080000680100000002781080000800b00000080100580080000100100200380700080180200080200080200000d80080280100001c00180080000100000900080201080480200600080200f80281280f80d80100000000000001e80100280180980580000f80100180080d80000080080000300300080000200001580001480080603380080080000c80300000180080880480980200000e80000100200b00000880280000300100680000480180280280a80102700280e00000780380280001600280700b00000d83980000100100280300380000080000d00400180000a80200b00080900780000180280101580180200301580080300000f80880281100400380580100000100180300000080080180080180180080981d80000480000000501480080000381200000000000300180180100180600000180000000800c00080800000500700200180500000000000d80580380401200700480300003700781480000280080000880500100b80480000180000080000080280080080e00100a80000000200100b00600180380000200903602480080180d80000400000480100800000000480000301100200000d00081600d80380d80800000000100080400080700600180000000200000180100500000a00300900080000000700780001400080500080100000080200000180480000402400200380180780100380100280900200080081780a00000880101a80000200000000180d01000080500100100000480380800680000180680b00800083180200080080000000000200b00300080980200180580800280000000980000002080580500600381880000100001980700100000900000b00200600000001600c80080600280000c80000800400100000100402380380000200080480280000600280180000700000400000500000100680000380280080080180100100200280280100900101f80c00080000080080080000880480900080000300080500800c00081c0028008000050
  | 19 => 0x86562af24c242422262c28c89c4ece34604e081456800002789e0a9448707b139cb4c34e3fd1f2087c2e315b04945b249d4908dbc86c6340b200000000001c613c40002c236f957414a71f4c5001c9dc928200075072e000000000070e41a0001f5008400019224f09065a311f0bdcbd23842a99568d805d80bb1c64fe600047f0000d8200035e1974f4600029100300d07100b00000a8874535c21a11f2067281869c0002ab30400000003440000000516589469a06807400030104f108a9820000000b3600018917086b2388000064400050e000223c0005b509fa5b092c5cf00000000000002d89e7867e4cd18291281409220948e50e0c0824841de0c966693d618e81948c81181138b0851129813e80804464610dfcafc00010600008c21cc45c85a08fe45c0000e688c04ac38d20710542f800000011069454378c20b2c76e3c621b43000214bd0c8d01c9873559504bb4149287843500c61a46b9e287e80834438f5423c0110851cc4be02583b2a4cc0e243d466165d1aa19a000039cec491235a078417a7fd05b11b827600000000045a85e6000054c8d01e545b25d80008b3081a0cd1d000028903589a036704480000005bf24f8bc8eba76f2db881c0004e63f69e092940000ff08e82e008543d8ae05143b80dd08b88984be2588e3c3380004719d409f041f1cb0e4c43213245c0e3418400032c1f6403c28d4a6055879c0644668c2528c79b24b800062a0e6140000100e5f44b5800028e17700011d467649214c8d54892766000000047a7cb178099d15e000000194514e0001d517047f84cf47704bc8141d037920f8b888e62c91490a161f34a200b06ca5982ab19c0b6686939d91e8ed439d2b10af400c25148021f87249843c9245d00a2be1cc8eed30a7dd0d41fbc00079119b02680008221d820e854e00029707040006383a793acd4e4354739cd88328474710bb50a619233d8c34e3c212134a3e8dcc4e4153243c9c206a39d0d344a67f621ba0d8dd443936d032d13a53512822f029411502c800001a1d900002051445af370a178db03e5075213c96c19418388b0e4c03049f829019a0320a80dd0a0a6cc2080eac9c06b631592803dc40e25e1a90a9e000346a33cd6e60c4930410f6c73013119dc39491447d83149fe25f2f607b45dc0dc0e49abc00094932e1c1023416b379935c00068b00022a04760000001b709a29800710874e0017c13a19c43086c8000116c0c490634b000075e0000000ed06c695e3d38a08f5a26c000000000000027e07887e01ae3a20a7879063e45a092820200e38b240c9326e20000cc0ea837e019857d21a0ac0a090ac1a68c1000000071668705d98b50a800000016a800048b0001cb51a06ac00019e88da7f11ed9d18c025ca3d494248ae7d31008f34b8e15b07000007846682b02245248913
  | 20 => 0x6496027402a7c30cc878c00000001fa2a4af00000c98fe07522350001f4501e000000000125c4670930ac000000038a2314ad40002f10ba400024d3108a8c6382e237893f505850700010e86520000fa0000eb60002f384a09468da03d037868a19849911992e26ef3b022d4000000000034000079c3099fac1de22938a8f5017c1420001efc3c815124520500004884ba818116218814d258856280c39a978d2b6839018960890a00048c044c33c7ea0ac0d004ee2c81398138c24860054000000089642f800099229b439834882c00024da1703f460f2d29dd430e2360e59f1c69658312f1ed09d28ca3e9161400061d47f8bf08287d81b407b004059d000085c3360b14270000cfa44308484e40000002fe087c5cc0000001500dc61690000fb8852179000117c2aa1590001b10f163a52a904ac0000001f31ee52c063d1e48b802685fe30f83c43044724be147430a33530f0000662000201a4ac3f61d61418acc000000000161d1ac0003850c9436c2fa0000000a5897e2931190ac83890001a6906842a342046ccbc40119d00590e27610de97b87ae8a03d0938c8e20000000c4117a1240f0088c4160000000d7d08021841b993087685243589fc8c64ba1a48a952aa94e18507e0f4a18343110b4f320a631a8250c0696525420c0a92441314944cb8c7b12b1a3701260ce00e9008d7424927f0e990485d224a09482c447b1278fe91083274269d2893479a37b07fd0e40ff33199c83404d404812d06f83722a280009a411c25c1b1c05670303987a40000f43f48f7c0007ec37403180000173f1a1dc5ca2954b8008c31c52713408c8e3891c181186000036d25f8958a840001aa12840009403d20e6d1120002b911b096a21c3bda27c6847344622294d0660b1b89f300004af16803e87044c02098fc834655f493a118e4e1780000ef45ea0873350cf47da0771f7939400a5a035916f8ca02a90da8f308e81f04b088e06bc0122ec95d4d3e7772b80000a1a50821887707c07f829b95d03b000026e10209aa1c445f980000823f0ef83b4f888b00cb155c90000000007f0db247c000131c07610f3db9d68a4203940e80008d400009f0000f9c91d478a0f0cda3a2000014800013600016a509654700025b4ff821136300006c890b4600f2c634425005857035e0003629f9c00041e1508000f282633c014402dc02e01a0364e707980bd9ab475a4d344c0fdc2de9073890deca620001670d6911800000002c80000000000000000000000172cfc42ec36880000007d035a8000f10000470800107a7071901f788aa81f2fb880c2ba79f00014950c26530000ddc17e000196a374a52240445a16c00000017880012fa0002cc8000bca7bd000032420a4623c221fd2683a32ea15840d88d22fc1ec0a086760e312c928e3114430add0947cd05b816
  | 21 => 0xac99482e3e092cc3de8380df8ec8f1e20d1741da0c8237d093924c5388273230b691141d11d0993d2d072a000000037c0d50001538e1e0e821e0d6c00000015e0ec400045407c19380000000000a900001a51b000000001430002428a7e000000000000000000013c000036c4b185200000002761c5c00000020a88ccc5c46b000205ce2606b3498584ef22153b98c2c0000633b880004784503400c0d3103b70130ca829e1b8135000011685d36106c0ce857704f1b482c64ef02425fcdf45a21ec215800000032b9af80002ad28a82ac4fa26b00016392c80002568b7cb9232f42b9468c1a6a3322979080c6e548602a8000665000023d0dc53c347048098a00000013ed03662846c9a840c206f148218c000865099a09800002d118a268d6048c0001bfcf265f30ad0b1531863711693885c86d706023d46d253b1dd200c83a27501389b4e529771489d703fa6733ab8000a740fd0000000da600037223c099c0001e8800088474831b1dac000272000072000066f38680008ee12100012448668002d08000fac56d00000000003c60001ecd1002082c69e045a400044c884c0005b9000031120a000000000115c0002c01aa0a384ae4c0800000039800016e84f60000001a30e9a8f61e99b742a8776387174474e0352ef8000ca4174357036c0aa73e3491eac5267e80001bf07225bd32f9620694137000111c0004e800006740007850d100881e6000000148cc7e3320cf800022000042225e05283b910d159891a20e1bd1101138244026140508663114420050568ec20b9968fb82d71c5177059866118b02b458001c1a7a2dd12e14e1861308da055c1d70e04ad08a42c090c059284c00017c40005ff02094bca722983f800000529661de0d4d1de0001210000efc6bf4c31f003680001b3132cfb60da4090aa00000003c691442bc5d635893cd2b281e04d9a3cd52925326985c1145ac38d80000ec2ae096889480e8321e0156c8ec7ca0e6963d052590446903444249032390986307e01a3875c0006940001e1c000000000000009a00007900011b010745681945a25bb12a00011025d025500009862c73762324e5c000000019883600049798541d61c52ea896800096a16325b80002bf0c5000070a00039ca108bf400018c8fd522a34100025ec63c0003a000006422450ee8fb0d9c0000000f2822c7f92bf811000039c3d0113ce3011d1f2204053e0002e41cc914c6f42a809c008695f0ed1d586b895101f236c00013143c00000f63da00012891d6000000185800000034d8b0401e0023241a54a3e452132083d2624da4881c80aaa77d08c8bfcc0e3a02548c4c0002f600016500009391b7167cafa00031e0d5ca7a6040000000b140000001374ca8000000196d2ce0d70000a48cac1b20db8d601e024b28f19542444f4067a1c008a05
  | 22 => 0xc60f31d444405ad2b6150c24628c4c1a3f4c848df053890506a5ef06e800000025c1ef000084666c008254c2fa8f80d89f90ae68ce07f000050e0d80001d24c945a843610900a29412bd840102224e2c61d2ca9a00031780006706bd4a581d46c46cd43b1e5923c00045f0e7c0006cf23e9dc00006230000ad47489573312104ade31b1420a5c094000000000042c000000204c28862230287480007240001a44c2856e39606b400081648880000264b92aa00001c879713e1f151ca30e3fd800034202a27a800032e93d09c1460db66d607b82e4f061e71ee82880505f5173831cbd60ae0121f546ac0003dc1db490c0000000000bf270c00000000007720001d30b220002378984000576205844800085100000009048f2000096400088e4189b245c21ea2089e384143c40001cf40003614a811789084bd0d484e877c3e903f08acc128cb04b0d4400073313d0be400054c000000050a0570e79450f502de3e78244cd62ac000000010000000000000002861751c8894826f3eb87d8000000352a438d0c0001ba80000000004808fc420c07802e043093852b48b175cd108a3319903000031400c03a4a046eb3738ecc18631d11ca08c8d274130880f4a646794b988106ba9430760e411740b81c020ecc3210b02589f80be00017ea240c364782dc19988ac87d43a176c2fc21b44993a8e4668546f17a92f24d848223cd1104703d114590507641c71b2ccc84443be1358af87580248e54cc080810f089ccfe3863df0cb012a80d2fb13c805e85a1e8226c1668d133c0fece040000371e5466e1141f5a190d38088351000000014d4918218cdc2f43d9085003429d08414ccd025713c4847c3546d501c1a7400617f02e9d8ccb2243433816c7c418b0001a282a42d525b8320a904791fb16f09be2cb49b09810306e043d00004ae91f3d711140008bb179a62c000000000112c5de6f50ab84b87b2610000071c000210180a5d026026e0000f4800017522e80007f200008c1d4cdf650a2bc8dc00000002f408dd1540002bd00000104f9392891c06c3e3000000000047324a828c0003c5207a4c031a186095219831e09714b0ae41183c149b9070124000169805129a6903e4a0804aa0002640a804ca72b44283b859a8ed48108185b01db2ee811cebe00020c1bf8a001a407c882528424600005b4bc2334126231831269900007c8e865c0000000112400003a1aec2ce00000014e057645a4b7a0545862663fa0000ad258606a01fc00085019324b487e5590d582c01086c316b1f183663bf12405b000004637c1ca0c1493b1511ae4efe59c41080006446f9000000016a0000a00604e107e60368000f768090002120d3c46539f9de800089449a9bc044c6b32a89d38e843e72da05302d443439e1294dfa95a3ff93d88583f328301780a84594508d
  | 23 => 0x1fd4750819000000000016600001f06660002a30000d54000000173400006900004d43a61b914783f08fc70b0c608d07fa3ea00000006720000608000e8e2ba0a288a80005ce0a307c507e52a0000ed41982dc1ff14b4aca75934c166865040419725601a230019e17801740993f702bc4b68fc09618a84441d531c90c85b600006f8160690171000000113c7a62479ba518686a2d90b10a505ed43ca4f87d000037688a084e13d00000012b89480001ee8b264380001ff8f5e72f07080012ac6300002624ebc4db0dd82606f00191010000ad67f72141f68698276313174c01279d405990104a64300000000003c728624e0b3c3502d3a0b40000a146a2028e021020000000a6c3ac0000becc9277416795600000000fc83d52ba8952530b28ed88f71a19134cf863220916541ca053000000013e5201f08e0c00069718206b00fa4cc2af239061e5ab25d962d2e47c224f170cf5491902800007b817a3f9231c22e67e0fa80004f292000d97f51d43761000000c1c00000021f07fe173000038d104534353000003e51700013dd25433e00007390b267526c8ed85544b02d20890fca2812298dcce0a1c20380de47865de31290140142fe2241ed51568043de07001f60a94b487a0d048b20a582f0b5c5b640110bc2ca4
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x157c4876e15324c120004e2653814c9304800134b984ca514c120197121d932945304800182f7460b43d971000607dd183d0b65c400d07691a1d5458f100341da468755162c400103d94a1f654cb1000613a1c32d9532c4001649900cb654cb100060de10815d1658400182d7460b4359610006075d183d09658400183b746004159610005852455450d6384001624915514258a100040f65087595328400184c870c9654ca1000592640325953284001a0d8360864d95100068660d801936544001a298260064d95100068c60580193654400182f7460b43d951000607dd183d0b654400141d939db75d91100050b64a76dd7644400182f75e0973d911000607dd7835cb644400781c875514358d10747031c95450d634400782c87551425891073f031cd5450962440014c9900ca764c91000532640321d9324416b83681193754c9100040f65287d953244001649900cb654c9100040fa6075d913244001689900cb644c9105af0c040649da514400193375610704c5100064cdd5841c1214416b4369499071541100041d660641c5504416b8369819071541100060d660641c55044001c169319071541100070564c641c55044001c2692190715411000709648641c550441cdc329019071541105af0c640641c5504400d4709650071541100064c611401c55044001350984c5504c11002d5425d31541304400b650964c5504c110004d826121541204400b56097485504811002d9825921541204400d07698e0574594106550d24574d0d650400182d7460b435941064d0d2457450d6504191434915d34259410006075d183d09650418f434915d142594100348da63815d564040016319020575590106550d24575dcd640400182d7560b735901064d0d245755cd6404191434915d77259010006075d583dc9640418f434915d5725901064e0d205745516304195614915534358c100068355182d0d6304193614915514358c100058364a745516304195a14819d15458c1064e8520574551630400d25698e055458c100059464081551630400121d942157258c100060761d54d096304191614915534258c1063d8524554509630418f834815d154588106458924554d096204001a0d5460f425881063d8924554509620400160d939d154588106468920674551620418fa24815d1545881003499a638155162040016619020554588100048b650855cd620400182d8755343588106558924554d0d62041936249155143588100053264032dd932040014c9900c9764c8100040f650875953204001649900c9654c8100040f660755913204001689900c9644c810005076507558d320400142d941d5624c8100351ca4485dd9100415fc3251ddb744401057e8c94687591100400d63291a1564440100358ca4585591100400d633955456444010
  | 1 => 0x10050da47845d3654c40181f7460f42d95310060e5d180107654c4016249155142d89310051a640655c8604c40d0749161d54d8e2164d852455450d638858f52691dd142d95210050764f42dd3654840143691e1174d95210060bdd182d0f65484018397460041d9521005852455450f63484014599019573181210060ddd0815936354001837742056458d50006191c8815916354001464915937258d500060ddd0815936254001649900cb63d89500060ddd08159162540018547320564589500051524564dcd6254001649900cb764c9500341da4784dd93254001549900ca764c95000643610321d93254001549900c8764c95000683610321d93254001649900c8764c9500040f662841d9325400182d84cc8764c95000607612321d9325400144e928c8764c95000607610321d93254001459900c8764c9500060b610321d93254001469900c8764c95000613a60321d9325400184d980c8764c95000703a50321d93254001c0d940c8764c95000613e10321d93254001c0e840c8764c95000613610321d93254001c0d840c8764c95000603610321d93254001c46910c8764c95000711644321d93254001c4a900c8764c95000513640321d93254001c49900c8764c95000512640321d9325400181d84cc0764c9500060b613201d9325400144c93c80764c9500068cd9180107615400d834815d16498550006139cc8258e615400184e7220d62985500060ddd0815916154001834742056458550006076117318c615400182d845c862185500060d61f641046154001a336460041185500068c19180104615400182d7460b43185500068910582d0c61541918344161f4218550006075d183d086154001a144160f42185500360d20574508615400184d874c83218550006924c9800c8615415f23698d0540185500050b64b435d1658c19583481d0d745963064e0d205435d1658c0018378420574596306450d24574d09658c00181d7460f425963063d0d24574509658c00183b7460041596300361c1c580105658c00141f9755143d8530005852455450f614c00d834815d1541853000447653874ca514c00184c62e1d329453000652dd5821c1314c00111d9421d325413000613188874c9504c00141d93d0974596206460d207425d1658818f8348150974596200060de10815d16588195434915d343596200060b5d182d0d6588193434915d143596200060edd180105658800d8707160041596200341e25d80145634800142f9755142d8520005892455450b614800d834815d154185200044b653874ca514800184c63e1d329452000652dd5831c1214800112d9421d32541200061318c874c95048001348984c9504c12002d5225d32541304800b648964c9504c12011f121d932541304815794887e15324c1205669221b854c93048
  | 2 => 0x50000b038240000030200204018000002020000a020000c0e000002804000002c0c05018000a020202c001802030000000040000b00028001d0402000020000402000182414190781804010701404190055264032dd3654c80194432a0774d953200552640325d3654c801c0c325d364d95320050da4774993654c80903e98dd164d9532007030cb74593654c80143691dd164d95320040fe6174193654c80114d980ca71d953200552640329c7654c801549900c970d95320050b64b43dd3654c99583681d0f74d953264e0da0543dd3654c80141d93d0b74d95326460da0742dd3654c98f8368150b74d95320050da47749d3654c80143691e1174d95320040fe61741d3654c8018397460041d95320361c9c580107654c80d07691a1f40d953200552640325d7614c80183674a0765d85320040fe5d84197614c801a0c3261065d85320040f66274197614c801c0c650c974d853200562640325d3614c801549900c97598532006075cd84196614c80182d7261065985320055264032dd5614c801a0c3261065585320340f26174550614c80903c985d154d813200552640325d6604c801a0c3261065981320055264032dd5604c80181f7361065581320060bdc984195604c801549900c975181320040fe5d84194604c80181d7361065181320060b5c984194604c801a0c3261065181320040f66274194604c801a4832600651813200703194325d0604c801589900c974181320050d650659c4604c8015c1900ca71181320050d650655c4604c80147190195711813200711194325c4604c8015c1900c97118132005836503258d629440d646910c96358a51005926403258d629440190d840cb764ca510055264032dd93294401a0d840cb764ca510059264032dd9329440182d84ccb764ca510060761232dd9329440181d840cb764ca510051664032dd9329440182d840cb764ca510051a64032dd9329440184e980cb764ca510061366032dd93294401c0e940cb764ca510070365032dd9329440184f840cb764ca5100703a1032dd9329440184d840cb764ca510070361032dd9329440180d840cb764ca5100711a4432dd93294401c45910cb764ca5100712a4032dd9329440144d900cb764ca510071264032dd93294401449900cb764ca510060761330dd9329440182d84c83764ca510051324f20dd93294401549900c9764ca510040f652871d9329440184e870c8764ca5100592640321d9329440d8388759140582510060bdd182d0d609440181f7460f42582510040f653874c96094401a493260032582510058664c745016094401629921d140582512558c64474501609440162992d0d40582510058664f42501609455f23a98d0540582510348e26141501609458f624915514258a3164d45a477450f654c40142d92d0f74d953
  | 3 => 0x2343013c638e86c862a314a4486e86000108be130008b0467f2a23106400014988ce7ba8e2011475970038009400000000000001f1c69600000000a10e65a0060016c0593a1ca8235a4c4ca80aa8004295488a4662800711601b2882f162000223e88a9b800001f0071e27724e4a15c841d4409da3c134641c00009e008002911e7d9de26834129bc000003708c8c000870f855800000009682a87a282410e839260b9109e8005400000088000d0380ea95a382a93e2b16a1a15248a26519240e04e6a174068a2998003d00081000a4800820000a00085800a803010148682906615a000206b88699000352247a8f2002780023e4005e1d8b63d866a18009ca060026a001aa260a80015e298d8000007807425978110000007a732020027c07a40708b42c1e8030004d9fe160eca703e208d218104040048825400000699b45d9407611600000749f400212a507e5faa446a7e2b83a00084152a83300066966021085312e14164910c8921f2608b273a9a00236971ba00000509b836a8a252423f88e000009c14e121b68029e3289c0000016800000e23919c0f1448502c1592a828b89b00000000981ca5e9ec000001a852001848a8a000232799c86c03263000000009a1066f996a58fc4b000000000d8004c0000023a248000000000158000004e00092988000000000074000000003b80000070a619409800170123091c6b00068986000000021a060ba0000067a3c64972792749d8005b9a48b8c64820c4325e460001e0249480a0017c0000037aa67e1fa60008000b80000000a0440a000400000010100012010001c0023010241601010080000008082c000a8202400018040201030
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa6400c05a0593d0b74d9532005413401930832ec29900340865640325d3614c801504d0064c20cab0a6400a8268032610659813200501b4e19308328c099002a09a00c984194604c801424d3864c00ca3026400d02195900c9741813200580b4832864b88c099002c41a0194325c4604c801a2032b20192e23026400c42611900cb764ca5100641308c8065bb265288030198464032dd93294401814c2320196ec994a200a03692980cb764ca5100501b514a065bb2652880240da9a1032dd93294401407d4b08196ec994a200a036a5840cb764ca5100700b0948865bb265288030459864432dd93294401a02ca322196ec994a200e01611910cb764ca510070130948065bb2652880300d8464032dd93294401824cc320196ec994a200d02a51900cb764ca5100681328c8065bb265288038098464032dd93294401a2148b20196ec994a200d10645900cb764ca5100609708c8065bb2652880340a8464032dd93294401824c2320196ec994a200d02611900cb764ca5100601308c8065bb2652880300d8424f20dd93294401406d250e190ec994a200c42611900c8764c95000641308c80643b264a800301984640321d93254001814c2320190ec992a000a03692980c8764c95000501b514a0643b264a800280da8a10321d93254001407d4b08190ec992a000a036a5840c8764c95000700b09488643b264a800304598644321d93254001a02ca322190ec992a000e01611910c8764c95000701309480643b264a800300d84640321d93254001824cc320190ec992a000d02a51900c8764c95000681328c80643b264a800380984640321d93254001a2148b20190ec992a000d10645900c8764c95000609708c80643b264a800340a84640321d93254001824c2320190ec992a000d02611900c8764c95000601308c80643b264a800300d8424f201d93254001510d0082c168630aa000a846804160f421855000604902c9686ba2cb18002814a15d183d09658c001806ca0c5c3a6528a6000c036506221d325413000602902c9e84ba2cb10002824a15d182d0d6588001806ca0c7c3a6528a4000c036506321d3254120006090ec4c264a826090002309a42613254130480018243b730994a298240008c2693984ca514c12000501b4943865b2a658800304a8764032d9532c4001406d210e192ca9942000c1221d900c9654ca105ae06320cc0c838aa0880030159864c641c55044001a08c8326320e2a822000c0966192190715411000680b26c90c838aa08800342190648641c5504400141250ae8c1686b282000a052857460f425941000504942bab05b9ac808002814a15d583dc9640400150250aa8c1686b182000c81205929d15458c1000602922c3aa9a12c608002a04a155183d09620400190240b273a2a8b102000c09245875534358810
  | 1 => 0x1088cc7cb20a80000000002e0002a60006c40060d42aa2960000caba6c924694006a00005aa84c00c8c0bc000008002c0000005648b000aace8e9c3882c29e3220003e5818004e8c6474145e3c00448462b60c001e009a905caec64224a43478b800006e0098000052860e2640368a300000bea07e727a5416d666b4284a1a001c221200d20068503a76000470acd00200000000010a001101090202050c0101030307100603000a040708060404000002000600428b5219503ba6ca99002941a00ca81dd3654c801604d0064ba6c9b2a6400a03aa032dd164d953200581340196e8b26ca9900340432a4774593654c80181340b25a1ee9b2
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x800002b069691002eaa002c10002630020049c18e7a2a00614085006002000004405ba0ca91dd164d9532005401b00ca91dd164d9532005401b4195900c97118132005005b9611910cb764ca51005009b8a51900cb764ca51005009b9611900cb764ca5100700184a45900cb764ca5100700184645900cb764ca51005005b9611910c8764c950005009b8a51900c8764c950005009b9611900c8764c95000700184a45900c8764c95000700184645900c8764c95000600876690984c9504c12000600876693984ca514c120005009b4a1d900cb654cb10005009b421d900c9654ca10004821b02857560b7359010004811b02857560f7259010004a01b02855460b4358c10005201b0205929d15458c10005011b0245875534258c10004a01b02855460f4258810005201b0205939d15458810005021b0245875534358810
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x2
  | 7 => 0x4b
  | 8 => 0x4c
  | 9 => 0x4d
  | 10 => 0x4e
  | 11 => 0x138d
  | 12 => 0x94b
  | 13 => 0x94c
  | 14 => 0x94d
  | 15 => 0x94e
  | 16 => 0x124d
  | 17 => 0x124b
  | 18 => 0x124c
  | 19 => 0x124e
  | 20 => 0x138b
  | 21 => 0x138c
  | 22 => 0x138e
  | 23 => 0x98c
  | 24 => 0x98d
  | 25 => 0x98e
  | 26 => 0x128c
  | 27 => 0x128d
  | 28 => 0x128e
  | 29 => 0x9cb
  | 30 => 0x9cd
  | 31 => 0x9ce
  | 32 => 0x12cb
  | 33 => 0x12cd
  | 34 => 0x12ce
  | 35 => 0xa4b
  | 36 => 0xa4c
  | 37 => 0xa4d
  | 38 => 0xb0c
  | 39 => 0xb0d
  | 40 => 0xb0e
  | 41 => 0x140c
  | 42 => 0x140d
  | 43 => 0x140e
  | 44 => 0xb4b
  | 45 => 0xb4d
  | 46 => 0xb4e
  | 47 => 0x144b
  | 48 => 0x144d
  | 49 => 0x144e
  | 50 => 0x14cb
  | 51 => 0x14cc
  | 52 => 0x14cd
  | 53 => 0xccd
  | 54 => 0xcce
  | 55 => 0x94055
  | 56 => 0x94056
  | 57 => 0x138955
  | 58 => 0x95395
  | 59 => 0x138956
  | 60 => 0xa4955
  | 61 => 0x94a55
  | 62 => 0xb0955
  | 63 => 0xb0956
  | 64 => 0x94b15
  | 65 => 0x140955
  | 66 => 0x140956
  | 67 => 0x95415
  | 68 => 0xb4955
  | 69 => 0xb4956
  | 70 => 0x94b55
  | 71 => 0x144955
  | 72 => 0x144956
  | 73 => 0x95455
  | 74 => 0x14c9
  | 75 => 0x14c955
  | 76 => 0x954d5
  | 77 => 0x1489
  | 78 => 0x139255
  | 79 => 0x125395
  | 80 => 0x14d255
  | 81 => 0x1254d5
  | 82 => 0xa5395
  | 83 => 0x138a55
  | 84 => 0xb1396
  | 85 => 0xb1395
  | 86 => 0x138b15
  | 87 => 0x141396
  | 88 => 0x141395
  | 89 => 0x139415
  | 90 => 0xb5396
  | 91 => 0xb5395
  | 92 => 0x138b55
  | 93 => 0x145396
  | 94 => 0x145395
  | 95 => 0x139455
  | 96 => 0x9c996
  | 97 => 0x9c995
  | 98 => 0x12c996
  | 99 => 0x12c995
  | 100 => 0xcb
  | 101 => 0xa4995
  | 102 => 0x98a55
  | 103 => 0xb0996
  | 104 => 0xb0995
  | 105 => 0x98b15
  | 106 => 0x2cb
  | 107 => 0x14c995
  | 108 => 0x994d5
  | 109 => 0xcc996
  | 110 => 0xcc995
  | 111 => 0x98cd5
  | 112 => 0x168b
  | 113 => 0x9d296
  | 114 => 0x9d295
  | 115 => 0x8c
  | 116 => 0x2c9
  | 117 => 0x14d295
  | 118 => 0x1294d5
  | 119 => 0xa49d5
  | 120 => 0x9ca55
  | 121 => 0xb49d6
  | 122 => 0xb49d5
  | 123 => 0x9cb55
  | 124 => 0x2cc
  | 125 => 0x14c9d5
  | 126 => 0x9d4d5
  | 127 => 0xcc9d6
  | 128 => 0xcc9d5
  | 129 => 0x9ccd5
  | 130 => 0x150c
  | 131 => 0x14d2d5
  | 132 => 0x12d4d5
  | 133 => 0x198b
  | 134 => 0xb0a55
  | 135 => 0xa4b15
  | 136 => 0x140a55
  | 137 => 0xa5415
  | 138 => 0x198c
  | 139 => 0xb4a55
  | 140 => 0xa4b55
  | 141 => 0x144a55
  | 142 => 0xa5455
  | 143 => 0xcca55
  | 144 => 0xa4cd5
  | 145 => 0x150e
  | 146 => 0x168e
  | 147 => 0x140b16
  | 148 => 0x140b15
  | 149 => 0xb1415
  | 150 => 0xb4b16
  | 151 => 0xb4b15
  | 152 => 0x144b16
  | 153 => 0x144b15
  | 154 => 0x154c
  | 155 => 0x24b
  | 156 => 0x14cb15
  | 157 => 0xb14d5
  | 158 => 0x16cb
  | 159 => 0xb5416
  | 160 => 0xb5415
  | 161 => 0x20c
  | 162 => 0x145416
  | 163 => 0x145415
  | 164 => 0x144b56
  | 165 => 0x144b55
  | 166 => 0xb5455
  | 167 => 0x14cb55
  | 168 => 0xb54d5
  | 169 => 0xcd4d5
  | 170 => 0x14ccd5
  | 171 => 0x17cb
  | 172 => 0x164c
  | 173 => 0x5cb
  | 174 => 0x4955
  | 175 => 0x130a
  | 176 => 0x1a89
  | 177 => 0x1049
  | 178 => 0x59d5
  | 179 => 0x5856
  | 180 => 0x289
  | 181 => 0x10a
  | 182 => 0x198d
  | 183 => 0x2cd
  | 184 => 0xd0c
  | 185 => 0x104c
  | 186 => 0x1a8c
  | 187 => 0xe8b
  | 188 => 0x104b
  | 189 => 0x1a8b
  | 190 => 0xa0956
  | 191 => 0x95416
  | 192 => 0x95456
  | 193 => 0x95496
  | 194 => 0x125396
  | 195 => 0x124296
  | 196 => 0x124a16
  | 197 => 0x8e
  | 198 => 0xce
  | 199 => 0xd0a
  | 200 => 0x188a
  | 201 => 0xe8a
  | 202 => 0x18ca
  | 203 => 0xcc9c99e
  | 204 => 0xcc9c99d
  | 205 => 0x9c98cdd
  | 206 => 0x1289d6
  | 207 => 0xa0e
  | 208 => 0x180e
  | 209 => 0x5396
  | 210 => 0x4956
  | 211 => 0x139256
  | 212 => 0x124956
  | 213 => 0x130956
  | 214 => 0x151296
  | 215 => 0x1692d6
  | 216 => 0xb1456
  | 217 => 0xb0296
  | 218 => 0xb4296
  | 219 => 0x5c0d3
  | 220 => 0x44c
  | 221 => 0x45294
  | 222 => 0x5d2d3
  | 223 => 0x5cb53
  | 224 => 0x44b14
  | 225 => 0x5d6d3
  | 226 => 0xe97d3
  | 227 => 0x164d14
  | 228 => 0x17ce93
  | 229 => 0x1797d3
  | 230 => 0x282d1
  | 231 => 0x104d14
  | 232 => 0x104e93
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 1416
  | 6 => 3962
  | 5 => 2445
  | 4 => 342
  | 3 => 108
  | 2 => 25
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
  | 8 => packedAt gbK8 (1870+((h/22+packedAt gbK8 (1716+(h % 22)*7) 7) % 80)*8) 8
  | 7 => packedAt gbK7 (57584+((h/472+packedAt gbK7 (52392+(h % 472)*11) 11) % 1870)*12) 12
  | 6 => packedAt gbK6 (207336+((h/1320+packedAt gbK6 (190176+(h % 1320)*13) 13) % 4755)*13) 13
  | 5 => packedAt gbK5 (154035+((h/815+packedAt gbK5 (144255+(h % 815)*12) 12) % 2935)*13) 13
  | 4 => packedAt gbK4 (24966+((h/114+packedAt gbK4 (23940+(h % 114)*9) 9) % 452)*10) 10
  | 3 => packedAt gbK3 (9036+((h/36+packedAt gbK3 (8748+(h % 36)*8) 8) % 143)*8) 8
  | 2 => packedAt gbK2 (2348+((h/8+packedAt gbK2 (2300+(h % 8)*6) 6) % 34)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1fe1fc3061f87f01fc701fffff14c18f0930ff
  | 1 => 0xe1fe1fc07e1f87fe0f801c1c1f2b0e7336cc93
  | 2 => 0x1ffe3ff801ff8000fffe01fe0cc307cc70f1c
  | 3 => 0xfe0003ffffe000000fffffe000f03f80f80fe0
  | 4 => 0x3fffffffffff000000000ffc000fff000
  | 5 => 0xfffffc00000000000000000000ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2402400002009008010050508004085001025
  | 1 => 0x20a208c02208824c0c80c84856010632124c92
  | 2 => 0x1354154801d501425254012c24c1058470518
  | 3 => 0x540002a9754000284a4a92c004b02b00b80ac0
  | 4 => 0x1011033e599664b16003008080fe8000eda000
  | 5 => 0x99d9900c110440c1800c030318fffdef000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36302
namespace PEqualNP.Outside.L_meta_36302
open PEqualNP.Outside.L_meta_36302.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 6 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 26 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_128 : Interval s4Atlas 3 128 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 144 := (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 (concat bs4_3_96 bs4_3_128)))
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
theorem bs4_4_768 : Interval s4Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_800 : Interval s4Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_832 : Interval s4Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 19 := block_range (n:=19) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 883 := (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat (concat bs4_4_96 bs4_4_128) (concat bs4_4_160 bs4_4_192))) (concat (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)) (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 bs4_4_416)))) (concat (concat (concat bs4_4_448 (concat bs4_4_480 bs4_4_512)) (concat (concat bs4_4_544 bs4_4_576) (concat bs4_4_608 bs4_4_640))) (concat (concat bs4_4_672 (concat bs4_4_704 bs4_4_736)) (concat (concat bs4_4_768 bs4_4_800) (concat bs4_4_832 bs4_4_864)))))
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
theorem bs4_5_736 : Interval s4Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_800 : Interval s4Atlas 5 800 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 802 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat bs4_5_96 (concat bs4_5_128 bs4_5_160))) (concat (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)) (concat (concat bs4_5_288 bs4_5_320) (concat bs4_5_352 bs4_5_384)))) (concat (concat (concat bs4_5_416 (concat bs4_5_448 bs4_5_480)) (concat bs4_5_512 (concat bs4_5_544 bs4_5_576))) (concat (concat bs4_5_608 (concat bs4_5_640 bs4_5_672)) (concat (concat bs4_5_704 bs4_5_736) (concat bs4_5_768 bs4_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 8 := bs5_2_0
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
theorem bs5_3_96 : Interval s5Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 102 := (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96))
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
theorem bs5_4_704 : Interval s5Atlas 4 704 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 725 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 (concat bs5_4_192 bs5_4_224)) (concat bs5_4_256 (concat bs5_4_288 bs5_4_320)))) (concat (concat (concat bs5_4_352 (concat bs5_4_384 bs5_4_416)) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512))) (concat (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)) (concat bs5_4_640 (concat bs5_4_672 bs5_4_704)))))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 682 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 bs5_5_384) (concat bs5_5_416 (concat bs5_5_448 bs5_5_480))) (concat (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)) (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)))))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 25 := bgb_2_0
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
theorem bgb_3_96 : Interval gbAtlas 3 96 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 108 := (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96))
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
theorem bgb_4_320 : Interval gbAtlas 4 320 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 342 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320))))
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
theorem bgb_5_2432 : Interval gbAtlas 5 2432 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2445 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)))) (concat (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)))))) (concat (concat (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))) (concat (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))))) (concat (concat (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952))) (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112)))) (concat (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272))) (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432)))))))
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
theorem bgb_6_3936 : Interval gbAtlas 6 3936 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3962 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960))))) (concat (concat (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184))) (concat (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440)))) (concat (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696))) (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 bgb_6_1952)))))) (concat (concat (concat (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 bgb_6_2176))) (concat (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304)) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432)))) (concat (concat (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560)) (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688))) (concat (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944))))) (concat (concat (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))) (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 bgb_6_3296)) (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 bgb_6_3424)))) (concat (concat (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552)) (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 bgb_6_3680))) (concat (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 bgb_6_3808)) (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 bgb_6_3936)))))))
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
theorem bgb_7_1408 : Interval gbAtlas 7 1408 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1416 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 (concat bgb_7_448 bgb_7_480))) (concat (concat bgb_7_512 (concat bgb_7_544 bgb_7_576)) (concat bgb_7_608 (concat bgb_7_640 bgb_7_672))))) (concat (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832))) (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)) (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216))) (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 66 := (concat bgb_8_0 (concat bgb_8_32 bgb_8_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
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
def fullWord : Sig := 0xfeeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8feeefee8feeefaa8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075688 * 2 ^ 32 + 4277074600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36302.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[1,6]⟩,⟨.or,[0,7]⟩,⟨.and,[2,3]⟩,⟨.and,[0,8]⟩,⟨.or,[8,9]⟩,⟨.and,[1,10]⟩,⟨.or,[2,4]⟩,⟨.or,[3,12]⟩,⟨.or,[13,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4277074600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4277074600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36302

open PEqualNP.Outside.L_meta_36302 in
theorem PEqualNP.Outside.L_meta_36302 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4277074600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4277074600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
