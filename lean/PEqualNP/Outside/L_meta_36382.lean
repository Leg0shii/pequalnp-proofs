import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36382.Model
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


end PEqualNP.Outside.L_meta_36382.Model

namespace PEqualNP.Outside.L_meta_36382
open PEqualNP.Outside.L_meta_36382.Model
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

def mirrorSteps : List Move := [swapRows 64]

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

end PEqualNP.Outside.L_meta_36382

namespace PEqualNP.Outside.L_meta_36382
open PEqualNP.Outside.L_meta_36382.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x500787297012a93d814643803c00d8980c80e001a01282f0215d00416000bac00068500026201d31c08d0000420000400421c244bff32fe32fd32fc32ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a621ff53c42fea7887f94f10bf29e21fd53c42faa7887f14f10be29e21ff43c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621ee52c42dca5887f54b10bea9621ed52c42daa5887f14b10be29621ff42c43fc85887f50b10fe21621ff32c43fc65887f4cb10fe19621fe41c43fe63887f8c710fe98e21fc31c43fe43887bc8710ff10e21fd21c43da43887f08710ffa0621fb40c43fc81887f50310fe20621f840c43fe61887f8c310fe98621fc30c43fe41887f88310fe90621fc20c43fea9087f95210bf2a421fd54842faa9087f15210be2a421ff53842fea7087f94e10bf29c21fd53842faa7087f14e10be29c21ff43843fc87087f50e10fe21c21ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff42843fc85087f50a10fe21421ff32843fc65087f4ca10fe194217d51843fe83087f90610ff98c21fe31843fa63087f0c610ff90c21ef21843fc43087f48610f690c21fc21842fca1087fd0210ff20421fa40843fa81087e50210fe20421ff30843fc61087e8c210fe98421f930843f861087fc8210ff10421fd20843f841087fc4210fb88421fb10843fea8885fd5110dfaa2213f54443fca8885f95110feaa2217d54443f8a8885f15110de2a2213c54443fea6885fd4d10ff29a217e53443faa6885f54d10fe29a217c53443fe86887f90d10fea1a21fc43443fea4885fd4910ff292217e52443faa4885f54910fe292217c52443fe84887f90910fea1221fc42443fe64887f8c910fe99221fc32443fe82887f90510fea0a21ff31443fc62887f4c510fe18a21ff21443de42887f88510fe90a21ed21443f842887fd0110ff20221fa40443fa80887e50110fe20221ff30443fc60887e8c110fe98221f930443f860887fc8110ff10221fd20443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8086f950109f2a021fd54042faa8086f550109eaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087794c10af29821fd53042faa6087754c10aea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087b94810b729021fd52042faa4087b54810b6a9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821ef21043fc42087f48410f690821fc21042fca0087fd0010fda0021fe40043fa80087f10010fc20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf524c2dea4987f94930fea9261fc524c2f8a4987b14930b629261ff324c3fc64987f4c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fcc530ef98a61fe314c3fa6298774c530fe18a61ff214c3de42987f88530fe90a61ed214c3f842987fd0130fda0261fe404c3fa80987f10130fc20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061fd540c2faa8187f15030be2a0617e530c3fe86187f90c30fea1861fc430c3fea4187f94830bf29061fd520c2faa4187f14830ff99061fe320c3fa64187f0c830ffa8861fe510c2fca2187f54430bea8861fc510c3fe62187f8c430fe98861fc310c3fe42187bc8430ff10861fd210c3da42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9907fd4f20bfa9e41fe53c82fca7907f54f20bea9e41fc53c82f8a7907fd0f20ff21e41fd43c83f887907f90b20ff99641fe32c83fa65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe63907f8c720fe98e41fc31c83fe43907bc8720ff10e41fd21c83da43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa441fe54882fca9107f55220beaa441fc54882f8a9107fd4e20bfa9c41fe53882fca7107f54e20bea9c41fc53882f8a7107fd0e20ff21c41fd43883f887105f54a20ffa1441fe42883fe65107bcca20ff19441fd32883f865107b0ca20ffa8c41fe51882fca3107f54620bea8c41fc51883fe63107f8c620fe98c41fc31883fe43107bc8620ff10c41fd21883da43107f08620bf28441ff40883fc81107f50220fe20441ff30883fc61107e8c220fe98441f930883f861107fc8220f790441fb20883fea8905fd5120ff2a2417e54483faa8905f55120fe2a2417c54483fea6905fd4d20ff29a417e53483faa6905f54d20fe29a417c53483fe86907f90d20fea1a41fc43483fe84907f90920fea1241ff32483fc64907f4c920fe19241ff51482fea2907f94520fea8a41fc51482f8a2907fcc520ff18a41fd31483f862907fc8520f790a41fe21483fa42907b48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907e8c120fe98241f930483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8107f55020beaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107f54c20bea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041fe42083fa84107f10820ff99041ef32083fc64107f4c820fe19041ec32083fea2107f94420bf28841fd51082faa2107f14420ff98841fe31083fa62107f0c420ff90841ef21083fc42107f48420f690841fc21082fca0107fd0020ff20
  | 2 => 0x87fa6310fd4c621fe18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe6490fbcc921ff19243ee32487fa6490fb4c921fe19243ec32487fe6290ff8c521fb18a43fd31487ea6290ff0c521ff90a43f721487fc4290fb88521ffa82437f50487fca090ff54121fe282437c50487dea690fb94d21f6a9a43ec53487dea290f9d4521f798a43ee31487cc6290fb4c521f298a43ec31487dea090fb94121f6a8243ec50487fea610dfd4c21ff298437e53087faa610df54c21fe298437c53086fca410db94821ff99043fe32087fa6410ff0c821bf28843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50086faa9207fd4e40ff29c817e53903faa7205f54e40fe29c81ff52903fca5205f94a40fea94817d52903f8a5207fcca40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff31903fc63207f4c640fe18c81ff21903de43207f88640fe90c81ed21903f843205f94240ffa0481fb40903fea6a05fd4d40ff29a81fd53503f8a6a05f14d40ffa92817f52503fca4a07f54940fe292817c52503fe64a07f8c940fe99281fc32503fea2a05fd4540ff28a81fd51503f8a2a05f14540ff98a81fe31503fa62a07f0c540ff90a81ef21503fc42a07f48540f690a81fc21503fc80a06f90140ffa9881fe53102fca6207f54c40bea9881fc53103fea4207f94840bf29081fd52102faa4207f14840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207f54440bea8881fc51103fe62207f8c440fe98881fc31103fe42207bc8440ff10881fd21103da42207f08440bf28081fe40103f480207f50040fca0081b940103fea9985fd5330ff2a6617e54cc37ca9984f95330feaa6617d54cc37aa9984f55330fe2a661fe43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ff99661fe32cc3fa65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe639877cc730ff18e61fd31cc3ba63987f0c730ff90e61ef21cc3fc43987f48730f690e61fc21cc3fe81987f90330fea0661fc40cc3fea9187f95230bf2a461fd548c2faa9187f15230be2a4617d538c3fe87187f90e30ffa9461fe528c2fca5187f54a30bea9461fc528c3fe65187f8ca30fe99461fc328c3fea3187f94630bf28c61fd518c2faa3187f14630ff98c61fe318c3fa63187f0c630ff90c61ef218c3fc43187f48630f690c61fc218c2fca1187fd0230fda0461fe408c3fa81187f10230fc20461ff308c3be61187ecc230ffaa2617f544c3fca8985f95130feaa2617d544c3f8a8985f15130ffa1a61fe434c3fa86987fd4930bfa9261e
  | 3 => 0x1c00003000c01002c01c05400001400400000000c02c00000400800401405c0100040c800401803c0280080000300a000400000801000401c02000000400800004800c0c402800400401802001c00000000000001c00c03c01800400802000008806800804007800800c00000006403802400003c01800800800c03000000408800400c03800001000000000002c00008800400000400002807c01000001001002800003c00000001400400002000000000402000800c01001402800c00000000c00400400000801000c00400400401400000c00000000404c00400401403404800003401400800003005000002403000005400000401c01400002c00003c0000200c80800040280040140c7fea3997f94732bf28e65fd51ccafaa3997f14732ffa8665fe50ccafca1997f54332bea8665fc50ccafaa7195f94a32ff99465df328cbde65197fd4632ff28c657e518cbfaa3195f54632fe28c65ff508cbfca1195f94232fea84657d508cbf8a1197fcc932f799265fe324cbbc64997fd4532bfa8a65fe514cbfaa2997f14532be28a65ff504cafea0997f94132fea8265fc504caf8a0995f94c32bf29065ff320cbbe64197f8c832f719065fd320cbba64197b4c832ffa8865fe510cafca2197d94432bb28865fd510cafaa2197d54432baa8865fc510cbfea0197f94032bf28065fa500caf4a0197f54032bea8065f9500caf2a0197f14032ffa9663fe52cc6fca598ff54b31bea9663fc52cc7fe6598ff8cb31fe99663fc32cc7fea198ff94331bf28663fd50cc6faa198ff14331bea9c63ff528c7fca518df94a31f7294636e528c7faa518df54a31f6a94636d528c7f8a518ffcca31ff19463fd328c7f86518df94631ff98c63df318c7ee6318ffd4231ff284637e508c7faa118df54231fe28463ff524c6fea498ff94931fea9263fc524c6f8a498ffcc931ff19263fd324c7f86498ffcc531fb98a63fe314c7bc6298ffd4131bfa8263fe504c7faa098ff14131be282637e530c7fea418ff94831bf29063ee520c6dca418ff54831bea9063ed520c6daa418ff14831ff99063fe320c7fa6418ff0c831bf28863ff310c7be6218ff8c431fb18863fd310c7ba6218fd4c431ffa8063fe500c6fca018fe94031bd28063fd500c6faa018fe54031bca8063fc500c7fea790dfd4f21ff29e437e53c87faa790df54f21fe29e437c53c87fe6590fbccb21ff19643ee32c87fa6590fb4cb21fe19643ec32c87fe6390ff8c721fe98e43fc31c87fea190ff94321bf28643fd50c86faa190ff14321f7a9e43ee53c87daa790fb14f21f798e43ee31c87da6390fb0c721f7a8643ee50c87daa190fb14321ffa9c437f53887fca710df94e21fea9c437d53887f8a710df14e21bea94436d52887fe6510ff8ca21fe99443fc32886fca310ffcc621ff18c43f6318
  | 4 => 0x18ade096c1bb0000d5c001d19721890d857d92a4b9a158a3c0000001b80000015013f00000000008d93497b9fb9f08774560c21c7a0d00002d8001e756013c9e0036cdf52783a84055b0000000000939f492b400000000181086d90d76db020c4d1d3ecb61e44000bacd88bf8eb0a7e1408320b0cb8ef8000000000000f21679319ed0000b013605dc151380b7d1a0f4150c32d53d4817d03b41396a1a300018b8090000e59314000d30b10cc1b20000000ba5ffd2e835879de6c625889f91c29710c78849dda068134f98ec0429e3c8940003ec0014d47c40000006212a1e29658000000450f5154000060a2401458b0e417621f8001fa00000000006a0000000d64698001e20578001d3080c0000012b12e075c000000000002199b88000000000000c683d00000013d00019c0000000000002329180001c480010200004a0000300000fa5bf1531a9589c000b898e8efcd244381dcf25b50000e78dcd1d09dd5f8000a100000000000000000010d0f0029c0013880019a4000be835cfa9d712657b1681788001515c92028f81430000000df80022aca4c002004c880000010f1345d6a32e0a5ee0696220ec4879444ec8d0a0502a0828f61ab9398e90b41199150000a68af8000d807a57e0d59a58c39a680014dd3a5b2d6416e05ae1095845d574960800071199c0000008f8000000472008730002270b18380c0400000400000406800401804001c0240040a401400403803000400000400000c0040000180280240000c800801400c00007000000000000000406000400001400802000c03800c04400000000000001c00404c04001808800001003000800401000c02405400000404800000400c00000000001001402000004000c01000400000800000800001405003800800001802001008401000001005800401802000800000408c00400000800000000000000801000002402c0000040000140080100000140140640180340b40000a400001400800001003403c02000400400c00000001800802802400800c01000000c0080080540400c800c02001001000000402401c0580f000000000402c02401800008403800407c00002000402400000001000800400001800800002000804400c02c05000c00c00c00000400400c09c01c00000401406007c00003800000000001800c0000000000040600380340000180b400400001002000401400c00001800000000000c00800002000001405002c00400007402003000c01001407803800400004801001402c00001c02403400000003000002000c00005000802002c03400801c00400000001001800801800c00401400000801400801800004800002c0080100380b000000002c00004000c03008c00400005c03401c00002400400c03400400000c00000c0000ac00000c00001800
  | 5 => 0xb0d6d821c50f10bb41f89b10a02b8dc10d92f19ad5e8a507da0d8630548080808e5d52d079915f3dfc08a13d9f99104f8c13c050289525065690ee0c3ce2dd04e885d05aa0e9b1d8c0c00761a180a41d92a8521eb89714f4e09660310000001320a190607b4f395611f1568000000f080011000000000003bc00151ceed924770784c1139ca616881a163c1108a9708558910001548720000000c98689b9093188000061c5e43cc000ce9b69778a9000000000000000067c838000b500000018f00007ac000000000001121e7c000000001ff54e9d22060000000f480000005e0000e48198000000000000000000000d480000d14b0000f144099e8000a1400059d97000044400212c00000015a1640013cd019048ee54893f5e78000000000001095a209a00023257a0001770000000001ec0dd4000000000000791c0808a360821090dec5b0fa0128f0c89da42318000000000008000fd08e8390002208000628596032225438098c0dc98340d713843984e0bd9f38a305c57992b9feddb82d0a407f8b74048be089a2e0d42314419918569e42300119ca99885f8a6d7c1cc9448f68000cb0bc20408cc001f656e800000185958c5642a8881700facd68f784b8a720bce1d038000270c718d40000009885bd159a921280005186b0fe06a899c0000000000000000005e800000153937159cb70a895083951dc0016f87e4af0751e38001740fc20a95700021a8001b600013d46d0001861b592158286c94d03dd9a0269a880000c00019d00019b8eb90012687f4ae1f4d42222dac8001450000000f6c0010bd0ba34a2c0241dc15d115e14db384987b88e1875980c609c538e091cf89c8421929435ce9728114181a8014c148000995b100005a07383e81cd245999cb800000081800088c951c38e20d9923c07d0309bc389d8d951de0db920e321fc81d02395a8db17fa210360d8c3098d8000414000f7e1d1ac000129000061a2d80bdd00000000000c80179510002180000000001ea8000001808001235211e980000013f82e00021f228c540dd0c29c8007a0196d09186804400021d99d8605be8000000318f9c0000006154d80000018cc0018a4b91580b493c469c0e53a00016b0bb9948f2a001551630000000de9241c41e91461f55fb0364ae89283a0e300016a954db2810068e3380e844d6d9330b2038cf59a00ed80012380b4001df9a9de34000ad8000001df0b59938060c41470002218d116552080008500014a00007cdd980dca483e5f5a079bd9ef0000539baa3511147e88022345c9230000e7011cff9d0c36831e0995c8fe8001074a28c348051115f1d114904e80000001c03e00007698480006f800070135a278979bc90fa239f101ec000a24000e24f2d0680000000000012d1d380019583f00000003281bd758000b843b1c1dee8
  | 6 => 0x11c8020da05880005900019b0000000001c891887bc66110c6584d00019bc00137c0011ecde111c000ad00007e0a5daa129d3bc001b30000bf0a204788845b8001a48000000001c3c001108001d400000009f8480000000000bc99a80a8000d016391ac000000001350e107f2111d28a3800000000185026000081c7494792c91180000020c9af0ddc0000d4001621ba2231229148a08cd0000000f1dc31f418e1ca00011640000000013e4000d340021b97a8001990f942f0c4db180014410520ce0acb941e0961bc0bbc0013400002589f13b5f8808c9a55c20392c012c000170001011390001be12980000011e80018a00018c9d48000000c240000000014f9a780014aa2a521e0c1ec93dcf70fc8a34000000d78ac0461594130b5c164b306706906685cced1a291f8c596f0da8000000000169f78000cf8000685ed8000c65bd16514ee160000000001141a71f500000018f8140001a39b79dc86004300000007ec0002c04c8000000191f28000870ac8000000000000d923082c961152927077c000000aa1de9fe61782e8000000611cc20595204f2201d61e619790cc9094c8b09e56290fb14f125c0712d9b71d58fd87c8c75739a98b9c028e298189d80c5dd0000188000000000000000c310c8350640c90ca9fd0639218001518edc000ab0fb8718f747798a88d0000981070920b28000000000000b66248330551ad89cd411170000e600004f8bfe1000003a5801e589e9e4dfe95d9750a761e03d4e6800164e29400000000000176843400000162800000190924c00189400143cb82268000001419ae21a0000000000378c2cdc4000000ab8001309b2400000060cdd8011f00000000349cf0d2944d8715e22f0860355ce000221c4d9c61d09d80000252088000000000584001339558001eb00f91386c1d7509c0183704012597311d98bc6b8a980004880016c9a10000e80cd9841d6c2b08685f0ba9d79f60001f2148625a2b80ed88c0422822c8811961f31aa40a0248000a58b78b8dbb9fddda874037c108e0c9021690c47986e1e517e916c221ef89a85da2a1e647c06d924834c709aac4c6311d8a33c1d50e09598b50c0ba16189d165e34158a139898001041099d50fdcf88580510374aa9c34bd0e01c20d4df184100008ca2e8001ff83240007294588b217105c940a2c219ad000096a0b4ea15983adbf8a78888759e489844b1cd9b413b8000000448841e5c000468e38e990591614c0ff00000022514692040000012ae124000afc0000000020716b80000000000007d0000000000ee87fc002144000d752f800000000000020149887c0000000014fc66c0016683b88580000001613fccf0000000d45f680021919b50a4001718756261c5a31e1503c82913e11ba359ea1648491839da00c9b35d15a08c4878c0687a19e00f13
  | 7 => 0x62c94942800010cce0000cb4000000001409b3c2980007648c00002fa0f1b1455ce187dc474d1908d911a61a51e811b1e31b0878a2d0c15e1a299369fe11fcd562b0f062f8999f801f0abc3f80fde1000108a369921b4900a134000a8c000000814e50001178531260c520498c53c1401b80bb213cde5f5c0000017909d5940000156081db2330c440000003200000021892015901e8000ecdfd8b38f650b43842812814e0df229c230ef0d60a841ca0b89c0f307b21480010849ac0016706f000150400043c5b58300022890b09906e80317f19317c91300387800010e800005902800000079620d2540010ae130679080a5522531e16c27a3340000021c87a823dd85ab1764dc865130119009cd209b90a896c4c1e7056cca0228648a003c1d7c5019c8f901205fdc000b850a1e8459378d3852a0108f21213a9aa80015b83d8465c71995d658680000011e4635c2d1a88b8000001e680000021b1c18000000000d7dae863d5a1ff0338001f44001544000ef4000001e89288001cd02120f9968598bc53e8e15cb2229578000cca0e09b62a816c1b1c69f714ba0a00cc4a9d1c1e40f4000000c198d00e05717800019fa2b4000000b6a1c19012211c191db99250c080b132a15400000000000015cf19534001d9112820a119c25879699c1400000000215c084ea922cd50a800001a83c48913106ce2149745c00da020001fa89e19f0a1dc10344001169af85a51e000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8400436d5210010bd98440042f56110010ee50040042f96510010de59440042796510010be99040043ba6410010ded5040043ba5410010de55040043b95410010ce550400437b5310010f694c40043795310010f654c40043595310010eed0c40043b94310010fa94840043e95210010fc98440042f96110010fc584400437a5110010ee90440043b84110010fac8440043e921100109f59730042be64cc010af593300433e54cc010cf553300435e53cc010d754f300436e52cc010db54b300427f658c0109f596300433e548c010cf552300435e538c010d754e300436e528c010db54a30042f6618c010bd586300437a508c0109fd95300433e544c010cf551300435e534c010d754d30042ef624c010bb189300436e524c010db549300437a504c0109fd94300427e650c0109f594300427c650c010cf950300433d540c010d794c300435d530c010db948300436d520c010bd98430042f5610c0109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f596200433e5488010cf552200435e5388010d754e200436e5288010db54a20042f66188010bd586200427f6548010cf951200433d5448010d794d200435d5348010db949200436d52480109fd94200427e65080109f594200427c6508010cf950200433d5408010d794c200435d5308010db948200436d5208010bd98420042f56108010cf953100433d54c4010d794f100435d53c4010bb98b10042ed62c4010db94b100436d52c4010f9c8710043e521c4010dd59710043b654c4010ed55310043d653c4010f554f10043e662c4010f958b10043e652c4010f954b10043f340c4010fc103100433e5484010cf552100435e5384010d754e100436e5284010db54a10042f56184010dd94610042f96584010de59610042796584010be99210042f86484010ded5210043ba5484010de55210043b95484010ce552100437b5384010f694e10043795384010f654e10043595384010fa94a10043e95284010be586100437a5184010fc94610043eb2184010fa486100427f6544010afd9110042bc6444010cf951100433d5444010d794d100435d5344010db949100436d5244010f9c8510043e52144010bdd95100437765440109dd9510043b76444010ed19110043b65444010ed55110043d65344010f554d10043e65244010f954910042f76044010dd94110043f22044010fc48110042fb6544010ded95100427b6544010eed9110042fa6444010be19110043b86444010ae191100437b5444010ee95110043795444010ee55110043395444010ded4d10043da5344010de54d10043d95344010d654d10043ea5244010fa54910042fb6144010fcd85100437a5144010fc94510043eb2144010fc88510043e92144010fc48510043e12144010
  | 1 => 0x427d6590410cf952410433d5490410d794e410435d5390410bb98a41042ed6290410db94a410436d5290410be98241042f960904109fd95410433e5450410cf551410435e5350410d754d410436e5250410db54941042fb60504109f594410435e5310410d754c410436e5210410db54841042fa6010410be580410427d65cc410cf953310433d54cc410d794f310435d53cc410db94b310436d52cc4109fd96310427d658c410cf952310433d548c410d794e310435d538c410bb98a31042ed628c410db94a310436d528c410be98231042f9608c4109fd95310433e544c410cf551310435e534c410d754d310436e524c410db549310427f650c4109f59431042be640c410af590310433e540c410cf550310435e530c410d754c31042ee620c410bb588310436e520c410db54831042fa600c410be580310427d65c8410cf953210433d54c8410d794f210435d53c8410dbd4b210436e52c8410db54b210436c52c8410bb597210436d65c84109b597210436f54c8410db95321043ae54c8410cb953210436d54c8410eb553210432d54c8410db153210436f53c8410db94f21043ce53c8410d394f210436d53c8410f354f210434d53c8410db14f210436e51c84109fd96210427d6588410cf952210433d5488410d794e210435d5388410bb58a210436e5288410db54a21042fa6088410be582210427f6548410cf951210433d5448410d794d210435d5348410dbd49210436e5248410db549210436c5248410bbd95210436f65484109bd95210436f5448410db95121043ae5448410cb951210436d5448410eb551210432d5448410db151210436f5348410db94d21043ce5348410d394d210436d5348410f354d210434d5348410db14d21043e76148410db94521043e74148410f910521043e63148410f94c5210427f65084109f594210433e5408410cf550210435e5308410d754c21042ee6208410db948210436d5208410be98021042f960084109f592500427e63940109f58e500427e62940109f58a500427d6194010dbc86500436d21940109f597400433e54d0010cf553400435e53d0010d754f400436e52d0010db54b40042f965d0010de597400427965d0010ded5340043ba54d0010de55340043b954d0010ce553400437b53d0010f694f400437953d0010f654f400435953d0010fa94b40043e952d0010be587400437a51d0010eed0740043b941d0010fac8740043e921d00109fd96400427d6590010cf952400433d5490010d794e400435d5390010db94a400436d5290010bd98640042f56190010be982400437a50900109fd95400433e5450010cf551400435e5350010d754d400436e5250010db549400437a50500109fd94400427e65100109f594400427c6510010cf950400433d5410010d794c400435d5310010db94
  | 2 => 0x5494810db152520436f5394810db94e52043ce5394810d394e520436d5394810f354e520434d5394810db14e520436f6494810db992520436d6494810db192520436f6394810db98e520436d6394810db18e520436f4394810db90e520436d4394810db10e520436e6194810db186520436e6094810db182520433e5454810cf551520435e5354810d754d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810dbd95520436f5454810db95152043ae5454810cb951520436d5454810eb551520432d5454810db151520436f5354810db94d52043ce5354810d394d520436d5354810f354d520434d5354810db14d520436f6454810db991520436d6454810db191520436f6354810db98d520436d6354810db18d520436f4354810db90d520436d4354810db10d520426f6154810db985520426d6154810db185520436e6054810db181520436c1054810af99052042bd6414810cf950520433d5414810b798c52042dd6314810d794c520435d5314810bb988520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109b988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420436e52d0810db54b420427f65908109f996420427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a42042f66190810bd58642042fa6090810be582420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db54942042fb6050810be181420427f65108109f994420427d65108109f194420433e5410810cf550420435e5310810d754c420436e5210810db548420427f65cc8109f997320427d65cc8109f197320433e54cc810cf553320435e53cc810d754f320436e52cc810db54b320427f658c8109f996320427d658c8109f196320433e548c810cf552320435e538c810d754e320436e528c810db54a320427f654c8109f995320427d654c8109f195320433e544c810cf551320435e534c810d754d320436e524c810db54932042fb604c810be181320427f650c8109f994320427d650c8109f19432042be640c810af590320433e540c810cf550320435e530c810d754c320436e520c810db54832042f6610c810bd58432042fa600c810be580320427e64944109f592510427e63944109f58e510427e6294410db98a510426e62944109f58a510436d62944109b58a510427d65d0410cf953410433d54d0410d794f410435d53d0410db94b410436d52d04109fd96410
  | 3 => 0x10cf55054042de6315010b758c54042ee6215010bb588540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de980540427a6015010af99353042bd64d4c10cf953530433d54d4c10bb98b53042ed62d4c109f993530433e64d4c108f993530427d64d4c10cf593530423d64d4c109f98b530436e62d4c109b98b530427d62d4c10db58b530426d62d4c109f987530437661d4c109f983530437a60d4c109f596530433e5494c10cf552530435f5394c109f992530427d6494c109f98a530427d6294c1097596530435f5494c10d7952530439e5494c10c7952530435d5494c10e7552530431d5494c10d7152530435f6494c10d7992530435d6494c10d7192530435f6294c10d798a530435d6294c10d718a530435e6194c10d7186530435e6094c10d7182530433e5454c10cf551530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10d7d95530435f5454c10d7951530439e5454c10c7951530435d5454c10e7551530431d5454c10d7151530435f6454c10d7991530435d6454c10d7191530435f6254c10d7989530435d6254c10d7189530435e6154c10d7185530435e6054c10d7181530435c1054c10af99053042bd6414c10cf950530433d5414c10b798c530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd984530427e6014c10de980530427a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c10d794f430435d53d0c109fd96430427e6590c109f596430427c6590c10cf952430433d5490c10d794e430435d5390c10be98243042f96090c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c10bbd8943042ec6250c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c10cf950430433d5410c10d794c430435d5310c10af99352042bd64d4810cf953520433d54d4810b798f52042dd63d4810d794f520435d53d48109f993520433e64d48108f993520427d64d4810cf593520423d64d48109f98f520435e63d48109798f520427d63d4810d758f520425d63d48109f987520437661d48109f983520437a60d48109f596520433e5494810cf552520435e5394810d754e520436f52948109f992520427d64948109f98e520427d63948109b596520436f5494810db95252043ae5494810cb952520436d5494810eb552520432d
  | 4 => 0xe50e40442fa6190110ee90640443eb2190110fa486404427d6550110cfd51404433c5450110bdd8540442f46150110eed9140443bb5450110de95140443785450110ee15140443385450110bed8d40443f36150110be18540443f06150110eed0540443b94150110fac8540443e921501109f994404433f5410110be98040443b940101109f99730442be64cc110af593304433f54cc110cf153304435f53cc110d714f30442f661cc110bd587304427e658c110cfd52304433c548c110be996304437a658c110bed9230442f9648c110eed52304437a548c110de15230443b8548c110ce15230442f9638c110de94e3044378538c110ded4a3044379528c110be98630443eb218c110fa486304427f654c1109f595304427c654c110cfd51304433c544c110d7d4d304435c534c110bbd8930442ec624c110bdd8530442f4614c110be1953044378654c1109e19530442fb644c110be59130443bb544c110de9513044378544c110ee1513044338544c110f6d8d30443db534c110de94d3044378534c110f614d30443eb624c110fa189304437b524c110de54930443f3614c110be18530443f0614c110f6cc530443d9314c110fac8530443e9214c1109f994304433f540c110cf15030442fa600c110f64c0304427e65c8110cfd53204433c54c8110dbd4b204436c52c8110bd98720442f561c81109f996204433f5488110cf152204436e5288110db54a204427f65481109f595204427c6548110cfd51204433c5448110dbd49204436c5248110bdd8520442f461481109f994204433f5408110cf150204436e5208110db548204433f54c4110cf15310442ee62c4110bb58b10442fb64c4110be59310443bb54c4110de953104437854c4110ee153104433854c4110bed8f10442f963c4110fa98b10443e962c4110fac8710443e921c4110cfd52104433c5484110f9c8610443e52184110edd5210443b45484110fcd4210443f24084110fc50210443f23084110fc4c210442de63d5010b758f54042ee62d5010bb58b540427e63d5010d798f540425e63d50109f58f540435d63d50109758f540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540437661d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540423d6595010ee182540433f6395010cf98e540433d6395010cf18e540433f6295010cf98a540433d6295010cf18a540433e6195010cf186540433e6095010cf182540433f64550109fd8d540427c63550109fd89540427c62550109fd81540427d6055010de181540433f6555010ee181540433f6355010cf98d540433d6355010cf18d540433f6255010cf989540433d6255010cf189540433e6155010cf185540433e6055010cf18154043386055010cf04154042be6415
  | 5 => 0x524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910cfd50524433c5414910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524427c60149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910be98342442f960d09109fd96424427e65909109f596424427c6590910cfd52424433c54909109fd95424427e65509109f595424427c6550910cfd51424433c54509109fd94424427e65109109f594424427c6510910cfd50424433c5410910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910cfd53324433c54cc910dbd4b324436c52cc910be98332442f960cc9109fd96324427e658c9109f596324427c658c910cfd52324433c548c910d7d4e324435c538c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c9109fd94324427e650c9109f594324427c650c910af99032442bd640c910cfd50324433c540c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442fa60d0510be583414433f5490510cf15241442ee6290510bb58a414427c6550510bed8141442f860505109f997314433f54cc510cf153314435f53cc510d714f31442fa60cc510be583314427e658c510cfd52314433c548c510bb98a31442ed628c5109f195314433f544c510cf151314435f534c510d714d31442fb604c510be181314427e650c510af99031442bd640c510cfd50314433c540c510bb98831442ed620c510be980314427e65c8510cfd53214433c54c8510dbd4b214436c52c8510be98321442f960c8510dbd97214436e65c8510db597214436c65c8510dbd5321443af54c8510cbd53214436e54c8510db553214436c54c8510eb153214432c54c8510dbd4f214436e53c8510db54f214436c53c8510fa98321443e960c85109f996214433f5488510cf15221442ed62885109f195214433f5448510cf151214436f5248510db14921442fb6048510be181214436f6548510db995214436d6548510db195214436f5448510ebd51214432f5448510db951214436d5448510db15121443ac5448510cb151214436f5348510db94d214436d5348510db14d21443e76148510f990521443e54148510f98c521443e53148510fad8121443e860485109f994214433f5408510cf15021442ee6208510cfd53404433c54d0110bd98740442f561d01109f996404433f5490110cf15240442fa6590110de996404427a6590110be59240443bb5490110de95240443785490110ee15240443385490110be58e40443bb4390110e
  | 6 => 0x36c52c8210db94a208436d5288210bd98620842f56188210dbd49208436c5248210db948208436d5208210bd98420842f56108210bb98b10842ed62c4210f9c8710843e521c4210bd597108437565c4210f998b10843e562c4210be597108437965c4210bed9310842f964c4210de953108437854c4210bed8f10842f963c4210fa98b10843e962c4210fac8710843e921c42109f98f544427d63d51109f98b544427d62d5110eed83544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f54951109f98e544427d63951109f98a544427d6295110dd586544437960951109fd8d544427c63551109fd89544427c62551109fd8554443776155110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f18054442be6515110cf994544423e6515110ee580544433f6315110cf98c544433d6315110cf18c544433f6215110cf988544433d6215110cf188544433f6115110cf584544433f6015110cf440544433f54d4d10cf153534427e64d4d109f593534427e62d4d109f58b53442be6494d10af592534433f5494d10cf152534435f5394d109f992534433e6494d108f992534427d6494d10cf592534423d6494d109f98e534427e6294d109f58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af191534433f5454d10cf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534433f5414d10cf150534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d10de580534427c6014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433c54d0d10be98343442f960d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10be98243442f96090d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10bbd8943442ec6250d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10bd98443442f56110d10be98043442f96010d10cfd53524433c54d49109f993524427d64d49109f98f524427d63d4910af99252442bd6494910cfd52524433c5494910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910cfd51524433c5454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191
  | 7 => 0x10e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10db548528427e6414a109f590528427e6314a109f58c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10be98342842f960d0a109fd96428427e6590a109f59642842f66190a10bd586428427f6550a109f595428427c6550a109fd94428427e6510a109f594428427c6510a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10dbd4b328436c52cca10be98332842f960cca109fd96328427e658ca109f596328427c658ca109fd95328427e654ca109f595328427c654ca109fd94328427e650ca109f594328427c650ca10af99032842bd640ca10dbd48328436c520ca10bd98432842f5610ca10be98032842f9600ca10be98341842f960d0610bb98a41842ed6290610d794f318435d53cc610be98331842f960cc610bb98a31842ed628c610d794d318435d534c610bed8131842f8604c610af99031842bd640c610bb98831842ed620c610be580318436e52c8610db54b21842fa60c8610be583218436e65c8610db597218436e54c8610db553218436c54c8610dbd4f218436e53c8610db54f218436c53c8610fa98321843e960c8610db949218436d5248610bed8121842f86048610dbd95218436c6548610db951218436d5448610db151218436f5348610db94d218436d5348610db14d21843e76148610f9d0521843e63148610f94c521843eb6048610fa181218433e5490210cf55240842f66190210bd586408437a5490210ee95240843b95490210de15240842f96390210eed0e40843b94390210be98640843f26190210fc58640843ba4190210fac8640843e92190210bed95408437b6550210eed9140843bb5450210de95140843785450210ee15140843385450210bed8d40842f86150210eed0540843eb2150210fa485408433e5410210cf55040842f66110210bd58440843b94010210af99330842bd64cc210d7d4f308435c53cc210d794e308435d538c210bd98630842f5618c210be5963084379658c210bed9230842f9648c210de9523084378548c210de94e30843da538c210f654e3084378538c210ded4a3084379528c210be98630843f2618c210fc58630843eb218c210fa486308435f534c210d714d30842ef624c210bb18930842fb654c210ded9530842fb644c210be591308437a544c210de15130843db634c210f6d4d308437a534c210de14d30843d8534c210fad8930843e8624c210ded493084379524c210be18530843db314c210f64c530843eb214c210fa485308435e530c210d754c30842f6610c210bd58430843d9300c210dbd4b2084
  | 8 => 0x10d754e31c42ee628c710bb58a31c436e528c710db54a31c42fa608c710be58231c435f534c710d714d31c436e524c710db54931c42be640c710af59031c435e530c710d754c31c42ee620c710bb58831c436e520c710db54831c42fa600c710be58031c436f52c8710db94b21c436d52c8710db14b21c42ed65c8710db59721c436f54c8710db95321c436d54c8710dbd4f21c436e53c8710db54f21c436c53c8710db94a21c436d5288710be98221c42f96088710dbd4921c436e5248710db54921c436c5248710bbd9521c436f6548710dbd5121c436e5448710db55121c436f5348710db94d21c436d5348710db14d21c43e76148710f990521c43e63148710f94c521c436e5208710db54821c42fa6008710be58021c433e54d0310cf55340c436e52d0310db54b40c42f661d0310bd58740c43ba54d0310de55340c43b954d0310ded4f40c437953d0310fa94b40c43e952d0310fc98740c42f961d0310fc58740c43eb21d0310fa48740c433f5490310db94a40c436d5290310cf95140c433d5450310db94940c436d5250310bdd8540c42f46150310db94840c436d5210310ee50040c42f96510310de59440c43ba6410310ded5040c43bb5410310ced5040c43795410310ee15040c437b5310310de54c40c43bb4310310ee50c40c43ea5210310fa54840c42f96110310ee90440c43eb2110310fa48440c42be64cc310af59330c435e53cc310d754f30c436e52cc310db54b30c42f661cc310bd58730c436e528c310db54a30c435e534c310d754d30c42ef624c310bb18930c436e524c310db54930c42f7614c310bd18530c436e520c310db54830c436e52c8310db54b20c42f661c8310bd58720c436e5288310db54a20c436e5248310db54920c42f76148310bd18520c436e5208310db54820c433f54952109f98e548427d63952109f98a548427d62952109fd8d548427c63552109fd89548427c6255210cf550548427e63152109f58c548427e62152109f58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de98353842be6494e10af592538435f5394e109f992538433e6494e108f992538427d6494e10cf592538423d6494e109f98a538427d6294e10de98253842ef6254e10bb189538427f6454e109f191538435f6354e109fd89538436f6254e109bd89538427c6254e10db189538426c6254e10d754c538427e6414e109f590538435e6314e109f988538427d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10be98343842f960d0e109fd96438427e6590e109f59643842fa6090e10be582438427f6550e109f595438427c6550e10bbd8943842ec6250e10bdd8543842f46150e109fd94438427e6510e109f594438427c6510e10be98043842f96
  | 9 => 0x98854c42ed6215310bb98b53c42ed62d4f109f99353c427d64d4f109f98b53c436e62d4f109b98b53c427d62d4f10db58b53c426d62d4f10dd98753c437960d4f10d7d4e53c427e6494f109f59253c427e6294f109f58a53c427f6454f109f19153c435f6354f109fd8953c427c6254f10af99053c42bd6414f10d754c53c42ee6214f10bb58853c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c435e6314f109f98853c436e6214f109b98853c427d6214f10db58853c426d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c433e54d0f10cf55343c427f6590f109f99643c427d6590f109f19643c435e5390f10d754e43c42fa6090f10be58243c427f6550f109f99543c427d6550f109f19543c433e5450f10cf55143c435e5350f10d754d43c42ef6250f10bb18943c42fb6050f10be18143c427f6510f109f99443c427d6510f10bd98443c42f56110f109f99352c427d64d4b109f98f52c427d63d4b10dd98752c437960d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c436f5494b10db95252c436d5494b10db15252c436f5394b10db94e52c436d5394b10db14e52c436f6494b10db99252c436d6494b10db19252c436f6394b10db98e52c436d6394b10db18e52c436f4394b10db90e52c436d4394b10db10e52c436e6194b10db18652c436f6094b10db58252c427f6454b109f19152c427f6354b109f18d52c436f6254b10dbd9552c436f5454b10db95152c436d5454b10db15152c436f5354b10db94d52c436d5354b10db14d52c436f6454b10db99152c436d6454b10db19152c436f6354b10db98d52c436d6354b10db18d52c436f4354b10db90d52c436d4354b10db10d52c436e6154b10db18552c436f6054b10db58152c436d5214b109f99052c427d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b10db94b42c436d52d0b109fd9642c427e6590b109f59642c427c6590b10db94a42c436d5290b10be98242c42f96090b109fd9542c427e6550b109f59542c427c6550b10db94942c436d5250b10bed8142c42f86050b109fd9442c427e6510b109f59442c436e5210b10db54842c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c436e52ccb10db54b32c427f658cb109f99632c427d658cb109f19632c436e528cb10db54a32c427f654cb109f99532c427d654cb109f19532c436e524cb10db54932c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c42be640cb10af59032c436e520cb10db54832c42f6610cb10bd58432c42fa600cb10be58032c436e5290710db54a41c42fa6090710be58241c435f53cc710d714f31c436e52cc710db54b31c435e538c7
  | 10 => 0x20834d530c820f998432082ed610c820f958432082e5610c820fa98032082ed600c820fa580320837751944209f992510827d64944209f98e510827d63944209fd91510827c64544209fd8d510827c6354420db989510836f3254420db0c951082be6414420af59051082de6314420b758c510837551144209fd97310827e65cc4209f597310835e53cc420d754f310827f658c4209f996310827d658c420bb98a31082ed628c420dd9463108375518c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420af99031082bd640c420bb98831082ed620c420be98031082f9600c420db94b210837651c8420dd54721082fa60c8420be583210836f54c8420db953210836d54c8420db15321082ee63c8420bb18f210836f53c8420db94f210836d53c8420db14f210836e51c8420f9947210836d51c8420f9547210836551c8420fa98321082ed60c8420fa583210827d6588420bb58a210827f6548420db94921082ef6548420dbd95210836f5448420db951210836d5448420db15121082ee6348420bb18d210836f5348420db94d210836d5348420db14d21083e76148420db94521083e63148420f94c521082ef6048420bb98821083765108420dd54421082fa6008420be580210827d64940209f98e500827d6394020dbcca500836c3294020dbc86500836d21940209f597400827f65900209f596400833e5490020cf55240082ee6290020bb58a400827f65500209fd94400827e65100209f594400827c6510020cf950400833d5410020bb98840082ed6210020ee500400827d65cc020af99330082bd64cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c020de942300827f654c020bbd8930082ec624c020de941300827f650c0209f994300827d650c0209f194300835e530c020d754c30082ee620c020bb58830083d9300c020bb98f20082ec63c8020bb587200836d51c8020bb58a200836e5288020ded4e20083795388020be58a200837a5288020fa94a20083eb3288020fa0ca20083eb2188020fa486200827f6548020bbd95200836f65480209bd9520082ee6348020bb18d20082ef6148020db54520082ef6048020db94120083ea4048020fa50120082fb6548020ded95200827b6548020ded4d20083795348020bed8920083eb6248020de94920083ea5248020fa90920083e94248020bb98b54c42ed62d53109f98f54c427d63d53109f98b54c436e62d53109b98b54c427d62d5310db58b54c426d62d5310dd98754c433f54953109f98e54c427d63953109f98a54c427d6295310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310b798c54c42dd6315310bb
  | 11 => 0xf9638c120de94e3048378538c120be98a304837b518c120fac8630483e9218c1209fd95304827d654c1209f195304835f534c120d714d30482ef624c120bb18930482f8654c120de1953048278654c120de9513048378544c120f6d8d30483db534c120de94d3048378534c120f614d3048358534c120fad8930482f8624c120fa189304837b514c120f6cc530483d9314c120fac8530483e9214c1209f99430482fa600c120bed8f20482f963c8120fac8720483e921c8120db94e204836c5388120bb586204836f5188120fad4220483ea3088120fa4c2204827e63d50209f58f540836e62d50209f987540827d61d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540833f64550209fd8d540827c63550209fd85540827c6155020cf55054082de6315020b758c54082f66115020bd584540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540827e6115020dd984540827661150209f584540837561150209d584540827e6015020de980540827e64d4c209f593530827e62d4c20db98b530827e61d4c209f587530827e60d4c20de983530827d6594c20d7d4e530827e6494c209f592530827e6194c209f586530827f6454c209f191530835f6354c209fd89530827d6254c20db189530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209e980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf55343082ee62d0c20bb58b43082fa60d0c20be583430827f6590c209f996430827d6590c209f196430835e5390c20d754e43082fa6090c20be582430827f6550c209f995430827d6550c209f195430833e5450c20cf551430835e5350c20d754d43082ef6250c20bb189430827f6510c209f994430827d6510c209f194430827e64948209f592520827e63948209f58e520827d65d08209fd96420827d6590820cf952420833d5490820be98242082f960908209fd95420827d6510820be98042082f960108209f59732082ed65cc820db597320836e54cc820db153320836f53cc820db54f32082ed61cc820bb583320827f658c8209f596320835e538c820d754e32082ee628c820be98232082f9608c8209fd95320827f650c8209f59432082be640c820af590320835e530c820d754c32082f6610c820bd58432082fa600c820be580320836d650c8209b59432083ae640c820eb590320836e540c820db15032082ee630c820f398c320836f530c820f394c320836d530c820f354c3
  | 12 => 0x551209f185544837b60551209f994544833d5415120cf990544827e63151209f58c544827e61151209f584544827e64d4d209f593534827e61d4d209f58753482be6494d20af592534835f5394d209f992534833e6494d208f992534827d6494d20cf592534823d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de582534827f6454d209f191534835f6354d209fd89534836f6254d209bd89534827f6154d209f185534827f6054d20ded81534827e6514d20d754c534827e6414d209f590534835e6314d209f988534827c6214d209f984534827d6114d20de580534827f65d0d209f997434827d65d0d209f197434833f54d0d20cf153434827f6590d209f996434827d6590d209f196434835f5390d20d714e43482fa6090d20be582434827f6550d209f995434827d6550d209f195434833f5450d20cf151434835f5350d20d714d43482ef6250d20bb189434827f6510d209f994434827d6510d209f19443482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920be98342482f960d09209f19542482fb6050920be181424827e65cc920d7d4f324835c53cc920be98332482f960cc9209f996324827c654c920d7d4d324835c534c920bed8132482f8604c9209f99432482be640c920af59032483cd320c920bd98432482f5610c920be980324827e64d45209f593514827e63d45209f58f514836f62d4520ddd4651482bf6454520af19151482df6354520b718d514837551145209f990514827d64145209f98c514827d63145209f997314827d65cc5209f19731482fa60cc520be583314827e658c5209f596314827c658c520d7d4e314835c538c520bb98a31482ed628c5209fd95314827e654c5209f195314827e650c5209f594314827c650c520af99031482bd640c520d7d4c314835c530c520bb98831482ed620c520be98031482f9600c5209f99721482ee65c8520db997214836f54c8520db953214836d54c8520db153214836f53c8520db94f214836d53c8520db14f214836c51c8520bb98321482ed6288520ddd4621483745188520be98221482f96088520ddd4521483745148520bed8121482f86048520dbd51214836e5448520db551214836c5448520dbd4d214836e5348520db54d214836c5348520f9d85214836f5148520f9d4521483675148520db14521483e45148520f98c521483e53148520fad8121482ec6048520fa181214827e6508520bb988214833f54d0120cf15340482ee62d0120bb58b404827e65901209f595404833f5450120cf15140482ef6250120bb189404827e6510120ee500404827e65cc120af99330482bd64cc120d7d4f304835c53cc120bb98b30482ed62cc1209f99630482fa658c120de996304837a548c120de15230482
  | 13 => 0xbe98342882f960d0a20d794f328835d53cca20be98332882f960cca20db597328836e54cca20db153328836f53cca20f394f328836d53cca20f354f32882ed61cca20fa98332882ed60cca20fa583328835e534ca20d754d32882fb604ca20be18132882be640ca20af59032882f6610ca20bd58432882f9600ca20bb594328836d650ca20eb99032883ad640ca20db950328836c540ca20f398c328836f530ca20db54c32883e6610ca20bb58432883e5610ca20b958432883ea600ca20bb58032883e9600ca20ba580328837751946209f992518827d64946209f98e518827d63946209fd91518827c64546209fd8d518827c6354620db589518836f3254620db0c951882be6414620af59051882de6314620b758c518837551146209fd97318827e65cc6209f597318835e53cc620d754f31882fa60cc620be583318827f658c6209f996318827d658c620bb98a31882ed628c6209fd95318827d654c6209f195318835e534c620d754d31882ef624c620bb189318827f650c6209f994318827d650c620af99031882bd640c620bb98831882ed620c620be98031882f9600c620bb597218836d65c8620db953218836d54c8620db15321882ee63c8620bb18f218836f53c8620db94f218836d53c8620db14f218836e51c8620bb58321883765188620dd54621882fa6088620be58221883765148620dd54521882fb6048620be181218836e5448620db551218836c5448620bb98d21882ec6348620dbd4d218836e5348620db54d218836c5348620f9d85218836e5148620f9945218836d5148620f954521883655148620f98c521883e53148620bbd8121883eb6048620fa181218833e5490220cf55240882ee6290220bb58a408833e5410220cf55040882ee6210220bb58840883b94010220af99330882bd64cc220d794e308835d538c220bb98a30882ed628c220be5963088379658c220de9523088378548c220de94e30883da538c220f654e3088378538c220be98a30883ea628c220fa58a30883eb328c220fa0ca3088379518c220fac8630883e9218c220bbd8930882ec624c220bed95308837b654c220de9513088378544c220f6d8d308837a534c220de14d30883eb624c220be18930883e8624c220ba18930883eb324c220fa0c93088379514c220f6cc530883d9314c220fac8530883e9214c220d794c308835d530c220bb98830882ed620c220bb597208836d65c8220bb98f20882ec63c8220bb587208836d51c8220be597208837965c8220bed8f20882f963c82209f98f544827d63d51209f987544827d61d5120cfd5254482de6395120b758e544827e6395120d798e544825e63951209f58e544835d63951209758e544836d62951209f986544827d6195120de582544827f63551209f18d544827f6255120dbd89544827f61
  | 14 => 0x9643c827e6590f209f59643c827c6590f20be98243c82f96090f209fd9543c827e6550f209f59543c827c6550f20cf95143c833d5450f20bbd8943c82ec6250f209fd9443c827e6510f209f59443c82ee6210f20bb58843c82fa6090b20be58242c835e538cb20d754e32c82fa608cb20be58232c82be640cb20af59032c835e530cb20d754c32c83cd320cb20bd98432c82f5610cb20be98032c82f9600cb20af99351c82bd64d4720ddd4651c827e64947209f59251c827e63947209f58e51c827f64547209f19151c827f63547209f18d51c836e6254720dd54451c827f65cc7209f99731c827d65cc7209fd9631c827e658c7209f59631c82ee628c720bb58a31c8376518c720dd54631c827f654c7209f59531c827c654c720dd94531c8375514c720bed8131c82f8604c7209fd9431c827e650c7209f59431c82be640c720af59031c82ee620c720bb58831c82fa600c720be58031c837651c8720dd54721c82fa60c8720be58321c836f54c8720db95321c836d54c8720dbd4f21c836e53c8720db54f21c836c53c8720db94721c83e651c8720db54721c83e551c8720d954721c82ee60c8720fa98321c83e960c8720bbd9521c836f6548720dbd5121c836e5448720db55121c836f5348720db94d21c836d5348720db14d21c83e76148720db94521c83e63148720f94c521c82ec6048720dd94421c83755108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320cf95140c833d5450320bbd8940c82ec6250320ee50040c82be64cc320af59330c835e53cc320d754f30c82ee62cc320bb58b30c835e534c320d754d30c82ef624c320bb18930c83d9300c320b798f54882dd63d5220cfd52548827e63952209f58e548827e61952209f586548827f63552209f18d548827f61552209f185548833d54152209f98c548827d6315220db588548827e61152209f584548837a6015220af99353882bd64d4e209f993538833e64d4e208f993538827d64d4e20cf593538823d64d4e20db58b538827e61d4e209f587538837a60d4e20af99253882bd6494e20d7d4e538827e6494e20cf992538823e6494e209f592538833d6494e208f592538827e6194e209f586538837a6094e209fd91538827c6454e20d7d8d538836f6254e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20d794f438835d53d0e20bb98b43882ed62d0e209fd96438827e6590e209f596438833e5490e20cf55243882fa6090e20be582438827f6550e209f595438827c6550e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20cf950438833d5410e20d794c438835d5310e20be98043882f96010e2
  | 15 => 0xc2fa60cc430be583310c27d658c430bb98a310c2ed628c4309fd95310c35e534c430af990310c2bd640c430bb988310c2ed620c430dd944310c375510c430be980310c2f9600c4309fd97210c27e65c84309f597210c36e52c8430db54b210c36f65c8430db997210c36d65c8430db197210c36f54c8430db953210c36d54c8430db153210c36e53c8430db947210c36d51c84309fd96210c27e65884309f596210c2ed6288430dd946210c37551884309fd95210c27d65484309f195210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c2fb6048430be181210c36f6548430db995210c36d6548430db195210c36f5448430db951210c36d5448430db151210c3cf6348430f318d210c36e5348430f9d85210c36e5148430f9945210c3665148430db545210c3e55148430d9545210c3e63148430f94c5210c3eb6048430fa181210c27f65084309f994210c27d6508430bb988210c27d6494030dbc86500c36d21940309f597400c37a50d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd63900309fd95400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c37a5010030ee500400c2be64cc030af593300c39e64cc030e7593300c35d51cc030f3c87300c3cd21cc030b758e300c35e538c030de952300c378548c030be58e300c37a538c030f694e300c379528c030de546300c3eb218c030fa486300c27f654c030bbd89300c2ec624c030b7d95300c35f654c03097d95300c3cf624c030f3189300c35d514c030f3c85300c3cd214c030b7d81300c35e504c030f6901300c3d9404c030bed95300c37b654c0309ed95300c37a544c030de151300c2fb634c030f6d8d300c37a534c030f694d300c3da434c030f650d300c3eb624c030fa189300c379524c030f68c9300c3d8324c030de545300c3db314c030f64c5300c3eb214c030fa485300c2f661d5320bd58754c827e63d53209f58f54c836e62d53209f98754c837661d53209d98754c827d61d5320dd58754c827561d5320cfd5254c827e63953209f58e54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c827e64d4f209f59353c836e62d4f209f98753c827d61d4f20de58353c835f5394f209f99253c827d6494f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c82be6414f20af59053c835d5314f20bd98453c82f56114f209f99053c833e6414f208f99053c827d6414f20cf59053c823d6414f20d798c53c836e6214f209f98453c83766114f209d98453c827d6114f20dd58453c82756114f20de58053c827f65d0f209f99743c827d65d0f20cf95343c833d54d0f20be98343c82f960d0f209fd
  | 16 => 0xf3148530f98c5214c3cd3148530f94c5214c3c53148530fa981214c3e960485309f994214c27d65085309f194214c2de6308530b758c214c2ee6208530dbd48214c36c5208530be980214c2f96008530cfd53404c33c54d0130b798f404c2dd63d0130dbd4b404c36c52d0130be997404c37a65d0130ded53404c3bb54d0130ee153404c2fa63d0130f698f404c2da63d0130f658f404c2f962d0130fad4b404c3e852d0130be587404c37851d0130f6cc7404c3d931d0130fac87404c3e921d01309f996404c33e5490130cf552404c36f5290130db14a404c2fa60901309f595404c33f5450130cf151404c2df6350130b718d404c36f5250130db149404c27e6510130cf950404c36f5210130db148404c3b94010130be994404c37a6510130be990404c3ba6410130ded50404c3ba5410130de550404c3b95410130ce550404c2fa6310130eed0c404c3b94310130be588404c3eb5210130fa148404c2f96110130de144404c3db3110130f64c4404c3eb2110130fa484404c2be64cc130af593304c36f52cc130db14b304c2fa64cc130ee993304c2ba64cc130ee593304c2f962cc130fad4b304c3e852cc130be587304c3db31cc130f64c7304c3eb21cc130fa487304c36f528c130db14a304c3cf528c130f314a304c2dd618c130f3c86304c3cd218c130f6d42304c3db408c130f6102304c35e63d50309f98b540c27d62d50309f987540c27d61d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c33f64550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6315030d798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c30cf992530c23e6494c309f592530c33d6494c308f592530c27d65d0c30cfd53430c27f6590c309f596430c33e5490c30cf552430c2fa6090c30be582430c27f6550c30cfd51430c2ef6250c30bb189430c27d6510c30be980430c2f96010c30dbd4a520c27e64948309f592520c27e61948309f586520c27f64548309f191520c27f61548309f185520c2be6414830af590520c36d5214830bd984520c2f56114830db94b320c36d52cc830be983320c2f960cc8309f596320c27f654c830af990320c2bd640c830db948320c36d520c830bd984320c2f5610c830be980320c2f9600c830bb98a510c2ed6294430ddd46510c27e64944309f592510c27e6294430db98a510c26e62944309f58a510c36d62944309b58a510c27f64544309f191510c27f62544309f189510c2be6414430af590510c2ee6214430bb588510c3755114430d794f310c37651cc430dd54731
  | 17 => 0x4930dbd53524c36e54d4930db553524c36c54d4930bb587524c3eb60d4930dbd93524c36e64d4930db593524c36c64d4930dbd8f524c36f43d4930db90f524c36d43d4930dbd87524c36e61d4930db587524c26d61d4930db187524c36f60d4930db583524c36f5294930db548524c27e64149309f590524c27e61149309f584524c3796014930bb994524c36e6514930dbd50524c36e5414930db550524c36c5414930bb584524c3e96014930dbd90524c36e6414930db590524c36c6414930dbd8c524c36f4314930db90c524c36d4314930dbd84524c36e6114930db584524c26d6114930db184524c36f6014930db580524c3696014930db4c0524c27e65cc930db14b324c36f528c930db14a324c2fa608c930be582324c36f524c930db149324c2fb604c930be181324c27e650c930af990324c2bd640c930dbd48324c3cd320c930bd984324c2f5610c930be980324c36f52d4530db14b514c27e64d45309f593514c36f62d45309f98b514c27d62d4530db18b514c2ee6294530bb58a514c36f5294530db14a514c3775194530afd91514c2bc6454530bbd89514c2ec6254530dbd49514c36c5254530af990514c2bd6414530bb988514c2ed6214530dbd48514c36c5214530dd544514c27e6414530cf990514c23e64145309f590514c33d64145308f590514c27e6214530db988514c26e62145309f588514c36d62145309b588514c37960145309f997314c36f52cc530db14b314c2de65cc530d7997314c35f54cc530d7553314c3cf52cc530f314b314c35c51cc530f6d83314c2de60cc530f6183314c2dd638c530bb98a314c2ed628c530dbd4a314c36c528c530ddd46314c374518c530be982314c2f9608c530dbd49314c36c524c530ddd45314c374514c530bed81314c2f8604c530d7d51314c35d544c530f3d49314c3cc524c530f5d85314c3d7514c530d7145314c3d4514c530f6d81314c2dc604c530f6181314c27e650c530af990314c2bd640c530b798c314c2ee620c530bb588314c36f520c530db148314c2fa600c5309f997214c27d65c85309f197214c36f52c8530db14b214c2fa60c8530be583214c36f65c8530bb997214c36e65c85309b997214c36d65c8530bb197214c36c65c85309b197214c36f54c8530db953214c36d54c8530db153214c36f51c8530db147214c3cf31c8530f34c7214c3ea60c8530fa583214c27e65885309f596214c27c6588530b798e214c2dd6388530bb58a214c36f5288530db14a214c3d53188530be982214c2f960885309fd95214c27e65485309f195214c36f5248530db149214c3d53148530dbd95214c2ee6548530db995214c26e6548530db595214c2ec6548530db195214c26c6548530dbd51214c36e5448530db551214c36c5448530f9d85214c36f5148530db145214c3c
  | 18 => 0xde982528c27f6454a309f191528c27f6154a309f185528c36d5214a30db94a328c36d528ca30be982328c2f9608ca30db949328c36d524ca30bed81328c2f8604ca30af990328c2bd640ca30bd984328c2f5610ca30be580328c2ee6294630bb58a518c37751946309f992518c27d64946309f98a518c36e62946309b98a518c27d6294630db58a518c26d6294630de982518c27f64546309f191518c27f62546309f189518c2be6414630af590518c2ee6214630bb588518c3755114630bb98a318c2ed628c630dd946318c375518c630be982318c2f9608c630dd945318c375514c630bed81318c2f8604c630af990318c2bd640c630bb988318c2ed620c630be580318c27f65c86309f997218c27d65c8630db94b218c36d52c8630be983218c2f960c8630dbd97218c36e65c8630db597218c36c65c8630db953218c36d54c8630db153218c36e51c8630db547218c3ea60c8630fa583218c27f65886309f996218c27d6588630be982218c2f960886309fd95218c27d65486309f195218c2df6348630b718d218c36e5248630db549218c36f6548630db995218c36d6548630db195218c36e5448630db551218c36c5448630f3d8d218c3cc6348630f9d85218c36e5148630db545218c3e63148630f94c5218c3ea6048630fa581218c27f65086309f994218c27d6508630be980218c2f96008630be597408c37965d0230de553408c2fa63d0230be58b408c2f961d0230de947408c3eb21d0230fa487408c33e5490230cf552408c2de6390230b758e408c33e5410230cf550408c2de6310230b758c408c3b94010230be594408c3796510230ee990408c3ba5410230de550408c3b95410230ce550408c2fa6310230f698c408c3d96310230eed0c408c2f96210230be584408c37a5110230fac84408c3e92110230af993308c2bd64cc230b7597308c35d65cc230e7993308c39d64cc230d7547308c3cf21cc230f3487308c2f965cc230de597308c2fa64cc230ee993308c2ba64cc230ee593308c2f962cc230be587308c3eb21cc230fa487308c27e62d51309f58b544c27e61d51309f587544c37960d5130cfd52544c2ee6295130bb58a544c35d63951309f98a544c36e62951309b98a544c27d6295130db58a544c26d62951309f986544c27d6195130de582544c2ef6255130bb189544c2f76155130bd185544c27f6355130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c37b60551309f994544c33d5415130cf990544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d30be982434c27c6550d30bed81434c2f86050d309f993524c27d64d49309f987524c27d61d
  | 19 => 0x52cc33e5414b30cf55052cc36d5214b30bd98452cc2f56114b30cf95332cc33d54ccb30db94b32cc36d52ccb30be98332cc2f960ccb30cf95232cc33d548cb30cf95132cc33d544cb30af99032cc2bd640cb30cf95032cc33d540cb30db94832cc36d520cb30f34c832cc2f6610cb30bd58432cc2fa600cb30be58032cc2be64d4730af59351cc33e54d4730cf55351cc33e5494730cf55251cc2ee6294730bb58a51cc37751947309f99251cc27d64947309f98a51cc36e62947309b98a51cc27d6294730db58a51cc26d6294730cf95151cc33d54547309fd9151cc27c64547309fd8951cc27c6254730af99051cc2bd6414730cf95051cc33d5414730bb98851cc2ed6214730dd54451cc33e54cc730cf55331cc37651cc730dd54731cc2fa60cc730be58331cc35f54cc730e795331cc35d54cc730e755331cc31d54cc730d794731cc3d651cc730f554731cc2de60cc730f698331cc3d960cc730cf95231cc33d548c730bb98a31cc2ed628c730cf95131cc33d544c730b7d9531cc35f654c730d7d5131cc39e544c730d755131cc39d544c730c755131cc3d7614c730d794531cc2dc604c730af99031cc2bd640c730cf95031cc33d540c730bb98831cc2ed620c730dd94431cc375510c730be98031cc2f9600c7309fd9721cc27e65c87309f59721cc33e54c8730cf55321cc36e52c8730db54b21cc36f65c8730db99721cc36d65c8730db19721cc36f54c8730db95321cc3ae54c8730cb95321cc36d54c8730eb55321cc32d54c8730db94721cc36d51c8730f3cc721cc3cd31c87309fd9621cc27e65887309f59621cc33e5488730cf55221cc2de6388730b758e21cc3765188730dd54621cc3d531887309fd9521cc27d65487309f19521cc33e5448730cf55121cc36e5248730db54921cc3765148730dd54521cc3d53148730bed8121cc2f86048730dbd9521cc36e6548730db59521cc36c6548730dbd5121cc36e5448730eb95121cc32e5448730db55121cc3ad5448730cb55121cc3e76148730db94521cc3e65148730d994521cc36d5148730f954521cc3655148730f3cc521cc3e63148730f34c521cc3e53148730f14c521cc3eb6048730fa18121cc27f65087309f99421cc27d6508730cf95021cc33d5408730b798c21cc2dd6308730cf95340cc33d54d0330b798f40cc2dd63d0330cf95240cc33e5450330cf55140cc2df6350330b718d40cc33d5410330ee50040cc2ee62d5230bb58b548c33f54952309f98a548c27d62952309f986548c27d61952309fd89548c27c62552309fd85548c27c6155230de181548c33d5415230d758c548c27e62152309f588548c27e61152309f584548c37a6015230be983438c2f960d0e30be582438c2be64d4a30af593528c36f5294a309f992528c27d6494a309f986528c27d6194a30
  | 20 => 0x27c6254440b798c51102dd6314440bb98851102ed6214440dd544511027f65cc4409f997311027d65cc440d794f311035d53cc440be98331102f960cc4409fd96311027e658c4409f59631102ee628c440bb58a3110376518c440dd546311027f654c4409f595311027c654c440d794d311035d534c440dd9453110375514c440bed8131102f8604c4409fd94311027e650c4409f59431102ee620c440bb58831102fa600c440be580311027f65c84409f997211027d65c8440db94b211036d52c8440be98321102f960c8440dbd97211036e65c8440db597211036c65c8440db94f211036d53c8440db947211036d51c8440fa98321103e960c84409fd96211027e65884409f59621102ed6288440dd946211037551884409fd95211027d65484409f195211036e5248440db54921103765148440dd54521102fb6048440be181211036f6548440db995211036d6548440db195211036e5348440db54d21103e76148440db94521103e65148440d9945211036d5148440f954521103655148440f98c521103e53148440fad8121103e860484409fd94211027e65084409f59421102ee6208440dbc86501036d2194040be59240102b96490040de95240103ba5490040be58e40102fa6190040de54640103eb2190040fa486401027f6550040bed95401037b65500409ed9540102fb6450040de95140103ba5450040bed8d40102f86150040de54540103eb2150040fa48540103bb6550040aed95401033b6550040eed8d40102bb6350040ee98d40103b96350040ee18d40103bb5350040ee94d40103b95350040ee14d40103bb6250040ee98940103b96250040ee18940103bb5250040ee94940103b95250040ee14940103bb3250040ee8c940103b93250040ee0c940103bb6150040ee98540103b96150040ee18540102b86150040eed4540103ba5150040ee54540103395150040ee14540103bb3150040ee8c540103b93150040ee0c540103bb2150040eac8540103ba2150040ee48540103a92150040ee085401035e63d53309f98b54cc27d62d53309f98754cc27d61d5330cfd5254cc27e62953309f58a54cc27e61953309f58654cc33e6395330cf18e54cc33f6295330cf98a54cc33d6295330cf18a54cc33f6195330cf98654cc33d6195330cf18654cc33f6095330cfd9154cc27f62553309f18954cc27f61553309f18554cc33f6555330cf98d54cc33c6355330cfd8954cc33e6255330cf58954cc33c6255330cfd8554cc33e6155330cf58554cc33c6155330cf58154cc33d5415330be98243cc2f96090f30af99352cc2bd64d4b30cf95352cc33d54d4b30cf95252cc33d5494b30dbd4a52cc27e6494b309f59252cc27e6194b309f58652cc33e5454b30cf55152cc27f6454b309f19152cc27f6154b309f18552cc2be6414b30af59
  | 21 => 0x5314d409f988535027d6214d409f984535027d6114d409f98f525027d63d49409f987525027d61d4940dbd4a52502f66194940bd586525036d52149409f98c525027d63149409f984525027d61149409f997325027d65cc9409f197325036f52cc940db14b325027e658c9409f596325027c658c9409fd95325027e654c9409f19532502fb604c940be181325027e650c9409f594325027c650c940dbd48325036c520c940bd98432502f5610c940be98032502f9600c9409f98f515027d63d45409f98b515027d62d4540bb98a51502ed6294540ddd4651502de6314540b758c51502ee6214540bb588515037551145409f98c515035e63145409798c515027d6314540d758c515025d63145409f988515036e62145409b988515027d6214540db588515026d62145409f997315027d65cc5409f197315037751cc540dd147315027e658c5409f596315027c658c540bb98a31502ed628c540be98231502f9608c5409fd95315027e654c5409f195315027e650c5409f594315027c650c540bb98831502ed620c540ddd443150374510c540be98031502f9600c5409f997215027d65c85409f197215036f52c8540db14b215036f65c8540db997215036d65c8540db197215036f53c8540db14f215036f51c8540db147215027e65885409f596215027c6588540bb58a21503775188540dd14621502fa6088540be582215027f65485409f995215027c6548540dbd49215036c5248540ddd4521503745148540dbd95215036e6548540db595215036c6548540dbd4d215036c5348540f9d85215036f5148540f9d4521503675148540db14521503e45148540d914521503e63148540f94c5215027e65085409f594215027c6508540bb98821502fa6008540be580215033f5390140af586405033c5190140ebc8640503ad2190140eed42405035f5394c409f98a531027d6294c409f986531027d6194c40bbd8953102ec6254c409fd89531036f6254c409bd89531027c6254c40db189531026c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531036f52948409f98e521027d63948409f986521027d61948409fd8d521027c63548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521027f65cc8409f997321027d65cc840d794f321035d53cc840be98332102f960cc8409fd96321027e658c8409f596321036e528c840db54a321027f654c8409f595321027c654c840d794d321035d534c840db949321036d524c8409fd94321027e650c8409f59432102f6610c840bd58432102fa600c840be58032102ee6294440bb58a511037751944409f98e511027d63944409f98a511036e62944409b98a511027d6294440db58a511026d62944409fd8d511027c63544409fd89511
  | 22 => 0x421ddd4e21087755388421bd58a21087765288421f994a210867f6548421db94921086ef6548421dbd95210866f6548421dbd4d210876e5348421db54d210876c5348421bbd85210876e5148421f98c521087e53148421bdd95210877765484219dd9521087775348421dd54d21086f76248421f9d8921087765248421f994921087665248421f98c921087e53248421ded42500867e64940219f592500867e63940219f58e500876f2194021db486500867f64540219f191500867f63540219f18d500876f2154021db48550086be6414021af59050086de6314021b758c50087795014021bb98b53902ed62d4e40d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40b798f52902dd63d4a40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529027f6154a409f185529036d5214a409fd97329027e65cca409f59732902be64cca40af593329036e52cca40db54b329027f658ca409f996329027d658ca40d794e329035d538ca409fd95329027d654ca409f19532902fb604ca40be181329027f650ca409f994329027d650ca40af99032902bd640ca40d794c329035d530ca40db948329036d520ca40bd98432902f5610ca40be98032902f9600ca40bb98a51902ed6294640ddd46519027e63946409f58e519027e6294640db98a519026e62946409f58a519036d62946409b58a519027f63546409f18d519027f62546409f18951902de6314640b758c51902ee6214640bb588519037551146409fd97319027e65cc6409f59731902be64cc640af593319035e53cc640d754f319027f658c6409f996319027d658c640bb98a31902ed628c640be98231902f9608c6409fd95319027d654c6409f19531902bf644c640af191319035e534c640d754d319027f650c6409f994319027d650c640af99031902bd640c640bb98831902ed620c640be98031902f9600c6409fd97219027e65c86409f59721902be64c8640af593219036e52c8640db54b219036f65c8640db997219036d65c8640db19721903ae64c8640eb593219036e53c8640db54f219036e51c8640db547219027f65886409f996219027d6588640be98221902f960886409fd95219027d65486409f19521902bf6448640af191219036e5248640db549219036f6548640db995219036d6548640db19521903af6448640eb191219036e5348640db54d21903e76148640db945219036d5148640f98c521903e531486409fd94219027e65086409f59421902fa6008640be58021902f965d0240de597409037953d0240be587409037a51d0240fac8740903e921d02409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ef6254d40bb18953502f76154d40bd185535035d
  | 23 => 0x314f31487e751cc521bb98331486ed60cc521bb996314876e658c5219b99631486ed638c521bb98631487e7518c521f3cc631487e7318c521bb98231486ed608c521f999631486e6658c521d999631486e5638c521f9d4e31487e6538c521f954e31487e4538c521f9d8231487e6608c521f958231487e4608c521bbd9531486ee654c521bb59531486ec654c521f3d4d31487cc534c521f9d4531487e7314c521f38c531486ef604c521bb18131487e6654c521b999531487e4654c521b919531487e7634c521f1d8d31487e7534c521f1d4d31487e6534c521f954d31487e4534c521f114d31487e7604c521f998131487e5604c521f918131486ee650c521db994314866e650c521bb98c31486ee610c521b998431487e7510c521f3cc431487e6310c521f34c431487e5310c521bb98031487ea600c521ba98031486ed600c521fa58031486e9600c521bb99350486ed64d4121bb98f50486ed63d4121dbd4750487e751d4121f98c750487e531d4121bb99250486ed6494121bb98e50486ed6394121db94e504876c5394121f958650487e75194121f98c650487e53194121bb982504876f5094121fad4250486ef6454121ebd9150486af6454121bb19150487ac6454121ab19150486ef6354121f3d8d50486cf6354121bb18d50487cc6354121b318d50487e76154121f9d4550487e63154121f94c550487eb5054121db94150486ee6514121bb99050486ed6414121bb98c50486ed6314121db94c504876c5314121dbd4450487e75114121f98c450487e53114121dbd4050487ea5014121db54050487e950141219f98b530876e62d4c219b98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6094c219f582530875f6354c219fd81530867c6054c21d754c53086fa6014c21be580530867e6314c21d798c530867e6214c21db988530866e6214c219f98453087766114c219d984530867e6014c21de980530867a6014c219f58053087796014c219e580530867e63948219f58e520876f6394821db98e520876d6394821db18e520876e6094821db582520867d65cc821db94b320867f658c8219f596320875e538c821d754e320876e528c821bd98632086f5618c8219fd95320876e524c8219fd94320867d650c821d794c320875d530c821db94832087cd320c821bd98432086f5610c821be98032086f9600c8219f98e510867d63944219f597310876e52cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c421db94a3108776518c4219fd95310876e524c421dd945310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb588310876e520c421be98031086f9600c421dbd4f210876e53c8421db54f210876c53c8421bb58a210876e5288
  | 24 => 0x534867e6014d21de980534867a6014d219f58053487796014d219e580534867e65cc921d7d4f324875c53cc921bd98732486f561cc921db997324866e65cc921dbd4f32487cf53cc921db54f32487cc53cc921bb98732487e661cc921b998732487e561cc921bb98332486ed60cc9219f99632486ee628c921bb996324876e658c921bb58e324876e538c921db14e32487e7618c921bb98632487e4618c921bb98232486ed608c9219f195324875f534c921d714d32486f7614c921bd185324876c654c9219b19532487cf634c921f3d4d324876e534c921db14d32487cc534c921d314d32487e7614c921bb18532487e4614c921bbd8132486ec604c9219f99432486ee620c921bd98432486fa600c921be58032486ee650c921db99432486ee630c921f398c324876f530c921db54c32486ee610c921f998432486e6610c921f958432486ee600c921fa98032486ea600c921bb58032487e9600c921ba580324867e65cc521d7d4f314875c53cc521bb98b31486ed62cc5219f99631486ee628c521bb58a31486f6658c521dd99631486f5638c521dd94e3148774538c521f9d8a31486f6628c521f998a31486e6628c521f958a31487e4628c521f9cca31487e6328c521f94ca31487e4328c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb18931486f4654c521dd1953148674654c521f5d8d31487d7534c521dd94d3148774534c521f514d31487e7624c521bd18931487e4624c521f9cc931487e6324c521f94c931487e4324c5219f99431486ee620c521bb58831486f6610c521be98031486f9600c521bdd8f21486f563c8521f9ccb21487e632c8521f94cb21487e432c8521bbd8e21486ee6388521bb58e21486ec6388521f9d4621487e63188521f94c621486ee6088521bb582214867e64d41219f593504867e63d41219f58f504877b5094121afd9150486bc6454121b7d8d50486dc6354121de540504867e64141219f590504867e63141219f58c504876f3214121db0c850487e761d4d21bb98353486ed60d4d21bb98e534876f5394d21f3d4e53486ed6194d21f958653486e56194d21bb98253486ed6094d21f3d4d534876e5354d21bbd8553487e76154d21b9d8553486ef6054d21fad8153486eb6054d21bb18153487e86054d21ba18153486ee6514d21dbd4c53487ce5314d21db54c53487cd5314d21d354c53487e56114d21bb98053487ea6014d21ba98053486ed6014d21fa58053486e96014d21bb98f51486ed63d4521dbd4f514876e53d4521db54f514876c53d4521bb98351486ed60d4521f9d8f51487e663d4521f958f51486e563d4521f918f51487e753d4521f994f51487e553d4521f914f51487e760d4521f998351487e560d4521f918351486ee65cc521bb19731487cf53cc521f
  | 25 => 0x67d6394321dbcca50c876c32943219fd9150c867c64543219fd8d50c867c6354321de54050c86ed61d4f21f958753c86e561d4f21bb98353c86ed60d4f21dbd4e53c87cf5394f21bb98253c86ed6094f21f3d4d53c876e5354f21bbd8153c86ec6054f21dbd4c53c87ce5314f21db54c53c87cd5314f21d354c53c86ed6114f21f958453c86e56114f21bb98053c87ea6014f21ba98053c86ed6014f21fa58053c86e96014f21bb59731c87ce53cc721f354f31c86ee60cc721bb58331c86ed658c721db59631c87cf318c721f9cc631c86ee608c721bb58231c86ef654c721f394d31c87cd534c721f9cc531c87ce314c721bbd8131c86ec604c721bb59431c876d650c721f3cc431c87e6310c721f34c431c87e5310c721bb98031c87ea600c721ba98031c86ed600c721fa58031c86e9600c721bb99350c87ae64d4321ab99350c86ed64d4321eb59350c86ad64d4321bb98f50c86ed63d4321f958750c86ee6494321bb59250c86ee6394321bb58e50c876e5394321db14e50c876f5094321fad4250c86ef6454321bb19150c86ef6354321bb18d50c87eb5054321db94150c86ee6414321bb59050c86ee6314321bb58c50c876e5314321db14c50c87e56114321dbd4050c87ea5014321db54050c87e95014321db58b538877661d4e219f983538867d60d4e21d7d4e53887766194e219f982538867d6094e21d7d8d538867f6054e219f181538875d5314e21be98053886f96014e21d798c538876d6214e21dd984538867e6014e21de980538867a6014e219f58053887796014e219e580538875e53cca21d754f32886f661cca21bd587328875e534ca21d754d32886f7614ca21bd18532887cd320ca21bd58432886fa600ca21be580328875e538c621d754e31886ee628c621bb58a31886f5658c621dd5963188776538c621f594e31887d5538c621dd14e31886f6628c621f998a31887e5628c621bdd953188777654c621f5d8d3188776534c621dd14d31886f4624c621d794c318875d530c621bb98831886ed620c621be98031886f9600c621bb597218876d65c8621dbd4f218876e53c8621db54f218876c53c8621bd597218877565c8621bdd8f21886f563c8621ded42508867e64942219f592508867e63942219f58e508876f21942219fd91508867c64542219fd8d508867c6354221dbc8550886be6414221af59050886de6314221b758c50887795014221db58b534867e60d4d219f583534875f5394d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f58253486fb6054d21be181534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534875d5314d21be98053486f96014d21d798c534876d6214d21dd584
  | 26 => 0x54c431f3949310c7cd524c431b7d85310c75e514c431bdd95310c777654c4319dd95310c6f7634c431f5d8d310c776534c431f594d310c7e6524c431dd549310c7e5524c431d9549310c6be64d4031af593500c6ee62d4031bb58b500c76e52d4031db54b500c76e5294031db54a500c77b50940319f992500c67d64940319f98a500c67d6294031ded52500c77a5494031ee952500c73a5494031ded4a500c77a5294031fa94a500c76a5294031de54a500c7e95294031da54a500c7785294031f6cc6500c7f23194031f64c6500c7f13194031ded92500c77a6494031de592500c7786494031de18e500c77b6294031de98a500c7796294031de18a500c77b3294031de8ca500c7793294031de0ca500c7786194031decc6500c77a3194031de4c6500c73e5454031db949500c76d52540319fd91500c67c64540319fd89500c67c6254031d7cc5500c75d3154031ded95500c77b5454031de951500c7ba5454031ce951500c7795454031ee551500c7395454031ded49500c77a5254031fa949500c76a5254031de549500c7e95254031da549500c7785254031f6cc5500c7f23154031f64c5500c7f13154031ded91500c77a6454031de591500c7786454031de98d500c77b6254031de989500c7796254031de189500c77b3254031de8c9500c7793254031de0c9500c77a6154031decc5500c75b3154031de8c5500c7793154031d64c5500c7783154031af990500c6bd6414031cf950500c73d5414031bb988500c6ed6214031db948500c76d5214031be980500c7795014031db98b53c877561d4f219f98353c867d60d4f21d7d4e53c876e6294f219f98253c867d6094f21d7d8d53c876c6254f219fd8153c867c6054f21d754c53c86fa6014f21be58053c875e6314f21db98853c87756114f219f98053c877a6014f219e98053c867d6014f21de58053c86796014f21bb59732c876d65ccb21dbd4f32c876d53ccb21bb98732c86ee60ccb21bb58332c875e538cb21d754e32c86f6618cb21bd58632c876d658cb21db94e32c87ce538cb21f354e32c876c538cb21bb98632c87e6618cb21f958632c86ee608cb21bb58232c86ef654cb21dbd9532c87cf634cb21db94d32c876c534cb21bb18532c86ef604cb21bb18132c875e530cb21d754c32c86f6610cb21bd58432c86fa600cb21be58032c876d650cb21f398c32c876f530cb21f394c32c876d530cb21f354c32c874d530cb21bb98432c87e6610cb21f958432c86ee600cb21fa98032c86ea600cb21bb58032c87e9600cb21ba58032c875e53cc721d754f31c86ee62cc721bb58b31c86ee628c721bb58a31c875e534c721d754d31c86ef624c721bb18931c86ee620c721bb58831c86fa600c721be58031c86be64d4321af59350c877b50943219f99250c867d64943219f98e50c8
  | 27 => 0x31db54832cc6f6610cb31bd58432cc6fa600cb31be58032cc6be64d4331af59350cc77b50943319f99250cc67d64943319f98a50cc67d6294331bbd8950cc6ec62543319fd9150cc67c64543319fd8950cc76f62543319bd8950cc67c6254331db18950cc66c6254331de54050cc76f5294a31dd986528c67e6094a319f582528c7e66194a31dbd8e528c76e6194a31d9986528c76c6194a31dbd82528c76e6094a31db582528c76c6094a319fd81528c67c6054a31dbd95528c7e66154a31db58d528c76e6154a31db185528c76f6054a31db981528c76d6054a31db181528c76d5214a31db94b328c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c76d520ca31f34c8328c6f5610ca31be980328c6f9600ca31db94b318c76d52cc631b7597318c75d65cc631f394b318c7cd52cc631bd597318c77565cc631bd58b318c7e652cc631f954b318c6ee62d4231bb58b508c76e52d4231db54b508c76e5294231db54a508c77b50942319f992508c67d64942319f98a508c67d6294231afd91508c6bc6454231db949508c76d52542319fd91508c73f64542318fd91508c67c6454231cf191508c63c64542319fd89508c67c6254231d7cc5508c6be6414231af590508c6ee6214231bb588508c76e5214231db548508c77950142319f983524c67d60d4931dbd4a524c6fb6054931be181524c76d5214931dd584524c67e60149319f580524c67e65cc931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c6f6610c931be980324c6f9600c931bd58b314c6ee628c531bb58a314c7ce628c531f358a314c7d7518c531b7582314c67e64d41319f593504c67e62d41319f58b504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c67e62141319f588504c6fa60d4831be583520c76f52948319f982520c67d6094831db18e520c76e6194831db186520c76f6094831db982520c76d6094831db182520c67f60548319f181520c76f6554831db98d520c76e6154831db185520c76c3154831dbd81520c76e6054831db581520c76c6054831bb988520c76d5214831be980520c6f96014831db94b320c76d52cc831bd987320c6f561cc8319f596320c76d528c8319fd95320c76e524c831db948320c76d520c831f34c8320c6f6610c831bd584320c6fa600c831be580320c76e6294431db58a510c76e52cc431db54b310c7ce52cc431f354b310c6dd638c431d794e310c6ee628c431bb58a310c76e528c431db54a310c6f5638c431dd94e310c7d6538c431f998a310c7e5628c431f994a310c775528c431f954a310c765528c4319fd95310c76e524c431db549310c6df654c431d7d95310c65f6
  | 28 => 0xd81518ca7c6054632dd544518cb7b50942329f992508ca7d6494232dbcca508ca7e61942329f586508ca7f64542329f191508ca7f61542329f185508cb795014232bb587324cbcf528c932dbd8b514cb6f32d45329f983514ca7d60d4532ddd46514cafb6054532be181514cb7551145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132af992504cabd6494132ded42504cb7950141329f990504ca7d6414132dbcc8504ca7e61141329f584504cadd638c832d794e320caed638c832db94e320cbce538c832bb586320caee608c8329fd95320cadf654c832d7d95320ca5f654c832b7d89320cb5e524c832bbd95320cb6f654c8329bd95320caef634c832f3d8d320cb6e534c832f394d320caef614c832bb181320cafa60d4432be583510cb7751944329f982510ca7d6094432f998a510cbd73294432f98ca510cbd53294432f94ca510cb746394432dd18a510cb773294432dd8ca510cb753294432ddd82510cb766094432dd582510cb746094432db989510cb6e3254432db4c9510ca7f60544329f181510cb776554432f9989510cbd73254432f98c9510cbd53254432f94c9510cb766354432dd989510cb666254432ddcc9510cb763254432d98c9510cb753254432d94c9510cb743254432ddd81510cb766054432dd581510cb746054432bd984510cb755114432be980510caf96014432af993500cabd64d4032bd987500caf561d4032dd947500cb7551d4032dd946500cb755194032ded42500ca7e64940329f592500ca7e61940329f586500cb7b5494032de952500cbba5494032ce952500cbe86294032f6cca500cbea3294032f64ca500cbe93294032ded46500cb7a5194032fc946500cb725194032de546500cbf15194032dc546500cb785194032ded92500cb7a6494032de592500cb786494032de18e500cb786294032decca500cb7a3294032de4ca500cb7b6194032de986500cb796194032de186500cb3e5454032dd945500cb7551540329fd91500ca7c64540329fd85500ca7c6154032ded95500cb7b5454032de951500cbba5454032ce951500cb795454032ee551500cb395454032fa189500cbdb3254032fa8c9500cbd93254032fa4c9500cb7b5154032de945500cbf25154032dc945500cb795154032fc545500cb715154032de145500cb7b6454032de991500cb796454032de191500cb7a6354032de989500cb7b3254032de8c9500cb793254032de0c9500cb7b6154032de985500cb796154032de185500cabe6414032af590500cb3e5414032cf550500caf66114032bd584500cb765114032dd544500cafa6014032de540500cb6f5294b319f98252cc67d6094b319fd8152cc67c6054b31db54852cc6fa6014b31be58052cc76e52ccb31db54b32cc6f661ccb31bd58732cc76e520cb
  | 29 => 0x10007000000300100000004005001400000000020000000000c000001c015009c00000040000024000000402f00000000014000000c0050000027001c00200040020020005000c009001000b000000c002c0070028006003c005002c00500000060030000000c001000c00a0000001000000000000000010000000c01400240070020006009c0010000001000000300180000050002000000000100000004000001c0020004003000000c00040000010001000c00a00040000024002002c00e00100060008006000400500040010000000000800200040020014000000000500000000000002002000100000060004003000c00000000110034006001000300100060010007001000000000060014000000000500080030010001000c005007000300140000058000000000f00000010000006000800d001800d00000030000000000800100080000020002002c004002801a00200030000004000400000000030008000000c0020000004001c00000200080010000000802f0004006005c0070014007000400b000000000500020004012000000100640000000008000000300140020000003005000500280100004012000000500000000004003001c001000c000000800d0030001002000000040090004001000000100100010000000000c005000400a00000060020000000000000140020000001001c0010020002000c006000000a0018005000c00100140200038003000400000100010000000001000300180000008002001000000000110000000000000500000000000000000000200000010000001001c002000401400140000000001001c000001c002000c0000000003000400000100010008001005c0010040000000c0030004010000c0050004000000000500240000024014000400a00080060018000000400000000010008006006c000002400a0004002000c003005c00e00000000000000001000000040060000001000c00400040060024003000000d0008001006c00200080010008001001401600100000010004001000300080010020000000c00000440020004008001000100280210004005000c00000040040050001000000000040010004000001800000080000004003000802b000c009000400000280000000000000000400180050000004000000200040010000001000800200000070000009000000300000000000001000800800037751947329f98251cca7d6094732db58951cca7f60547329f18151ccb755114732be98051ccaf96014732af99350ccabd64d4332ded4250cca7e64943329f59250cca7e61943329f58650cca7f64543329f19150cca7f61543329f18550ccb795014332b7597328cb5d65cca32bb597328cb6d65cca32bb587328cb7751946329f982518ca7d6094632db989518cb6f32546329f
  | 30 => 0x80000008000000000100000000030000001c00000080070000001000400100040010004010003001c002c000000400000040000004001003c006000c0060000003001c003000000500180180000005000c0010028010001c00200940000030000001400500000030000000000000000280000020002000c00000180020000008002c0010000000000000000140040000001000800200000020020000000400d0030001000400500000000008001000800600000000010000002002000000000000000001000900000140014000000000100000010008001002000000140040008010000000200040010008002000c0130000001000400300000000020004000000400140020004001000000400840000004004000000000000010064004000000200000180000004000000000040020034000000000000700000008000008000200040000008005000c00c003c0000034004000c00e00140000010001000000900200000014003000000b000000a0000002004c00200140010000008001000800480080008010000c00900000020004006002c00000000010000009000000700300010000000000000100000010000000000000a0024018000800900100020044008000c01a001c000000800000080080000002001000000040060010021000c00f000c000001c00a001400000500030004001001000900080000004002000800200000100014003000000a000c0010000001000c0050000000000000200080030004004005400000140010030003000c0010004000002c01d00080000048000000000e0040009001800000080000004000000000d001001800140000000004000000000040000008001000c0000014000000400a00080000008000000800000040030004000000400300080000014008000000500100010000005001c00000140050040003005000e0004000000000700000000020000001400900000010088001000800000180090008002000800a000400900000060000000000400100080030014006000000000000040004000000400c00280000000002003401d0008002004400500100000004001002c0010000003001c00f000000800040030074000000c0080000001001c007000000000040080008002000c0010064009002800000000000000001001800900040020024000000000100000010000001000400100140000004000003402100100010034000000000a00080000004002000800200100030004008000000400200000020000000000c00040000004002000000200000060004016004c01700340020010004001c002000000a0000000000000000040090010001002400000080000004008000400000080020004004000800c0004020001400000000040000002000c0080000000000400a000000800
  | 31 => 0xc0000000000800a000c00600000070018005001000200000030008000000000000140010038001000000b00040190010002000400000200000000002000c000003800a00280020000017000000000000090024001003002100080060010007000000c0008019001800a00400000004005003800300040010008007000000c00040050010001000000200000000008008000c000007800100040080008000005c000007c0040000002000c000004c00000040010000000000000100300030000002000800100f000600000010000005003c003001400f002000600000000004000000000800000020014008000400100040020000009008800f000c00400000000000001000400f0020000001c004000400000080000010000000000b000c000005800300040000010002004000000200010000000002800200040010008001003c00100240020000000001c002000c0000010005000000100280070018000000000100040050048017001800400100010000003000c00600340030020001000c00000140050000001002c001005800000040010014001001c0050040006000c001000c00100780030000000000800000040050020000002000c00140010018001000000100000010020000000400200040020000000005c00d000400400200110000020000000800000010008004000c00000080080000003001c0020008001001c00100280010000001000000000300020004000001001800080010004000000000000080000024001000000a0010000001001c000000b00000070048002000c0090000000000c00500080020000000000400000140060010000000400800280010000002001000b0020000000000100000090014000000000700000010004000000c000001400300000010000004000c00c001001a001000000040010000001000400800000060008001000000000000070008000000c002001c000000000200000170028000001000200300010008008008c002002800700080040010000000400500000000004002002c0080004000001800100580000000003002c00400000000000002001000000180090018001001000000040020008001003c00100000000004000001c0000004000000c00c0000000000000700040000004000001c005000c00100280040020001000400200780050014003000400400280020000001000c00900040030018002001c0160000026000000000080010000002000000d00040060030000002800100040010000008000400300000000000001000800400000020004000001000500100000000000000c001000c003000000000000000004002001400400400000000002000800200180000000000000400700000080000000001000000580050008004003000a0014006000000e00000
  | 32 => 0xc0070004002000c00000300040028001000400b000c0100010001003800000180000000001000800800240000074000000c006000000200080010014000000c0000038007000800100000010028001004401a0010000003c0090024000000000d00000090000006003000c000800e0000006000000b00040000000002001c0020010001006800000240050000000004400000000030004000002000000000010008005002c000001c00100100060010002000000000100010000000001400a000000100000010014000000000100640010000001002000000100020014000001400600140030000002002c0080000001000000000280010014001000400200180000000001002000200000010000000000400200180010000000000000000080000000000000c0010000000000400c000000200000030004001000400200000000000009000000a006c00200040040000011001c024007c00100000000010004001400000100030000002000000000000050000004000000100040000000001001000b001c003001000100240000048001000c0080000004001000b000000300000020000000000c003000c0040000034002001b0000000000000400040000000003000000200000020000013001c003000000000040020024001001400a00000040070001000400b000c006002800400140010008004000400000080010028005001000600580010040002000400100400060058000000c0000000004000000000040030000002001400800000020044009001800d0000001000c00100080140018001001400a00040000000003002000b0000000000800000040030018001000c00000180000020006003c004000000000080020000004001c002004c000000800000000010000005000001200140090000000000c03700080000014002004c00200000000014001001c00a000800200100040008002001400100180010000002000000000240000000007000000a002000900000010008003000001e00040100010004000800500000010000002000000300000000004002002000e00100000010009001000200000000004000002000000080080000000000c0010018004000400300540000004007000000400400050010003000000100080000000001000400a000400e0000000000400200f4008004c001000000100000080000000000c0010020001008800000440000010001000000c0000000000000a000802200000070018000000c00100440000000004000400200080040008000001c006003c00000000000004001001000a0034003001000000000000014000001c001002c000000c0000004000000400100040110004002000001c0018005000c000000c001004c001005000000000040014001004c0000004019000001300140010
  | 33 => 0x5e211f700000002088ef2a70a85606005ec32a645c00013186fa972c0001a78000244616f03a600000007bd4000000000000011880c00eb20cd00005e69eacb7b02a604e2da85a58ab469c8cf39af8e0e27f99b8b5e23470000533b3f400000028068aa5e443571a6c000000097216ce5e5166a5311f5e0000d4206698cd317145c3982a31a5400000002ccf000090c54625be22ac2626b28e5608e92d800000000002f4000028b60001baab861f3c0002cfe5019d2c000250c0ad079e0000c2800022fa34f41e4085803a3ee110c666a61cac0800000011c63c726ec0000000000198c18080006474ad0800a9943b4137e56426986e600000002dd500000009b927de29b800094e400000000000000000000000000000002b8800009725d883280000000000000000000003e05af1348b6d0a8c0e2a2180000c5002b98d766b990781a50622e5110e32a116399a15f03362da65340000210eb0f00008382d9aac20ac27bfc02ed9a53f086d80e9c7d4f200000200fcc1578000c030000000000053bafb3000000022f9cf2b0e9a8b736acbc0001eeb82713ae33e0b605a29c100002e1cb520000bfc00005349d8257b0e550000000250acb48fd47f7006c0010004004003c000003400d0028001000c000004001a000000200180020000022000400000080020010002001c00500000060018000000000a0018000000400000000000024004001400100080040008001000c000000000000040020008000000000e00300050014000001c0010014004003c0000000000002c000001000800100030044001000801f002800200280010004001000001000200000000000000000000040010008008000400000240090000005000802600100000000002000800b00000010004000000000e000c0000008003000c003002400000040010034007002800d00100010008001001c003000c0030000008000400100140010018000000000e0024003000400000080060000000003c0090000008000400000200020000001000000000080000004000001800c000c00100040160004001000400f000400000040040004001000000100100000004001000c00f000c009000000000180040008000000000000100050000002000400d001c0050018006002c00000080040020000000001600000090000002000000d000000f001000f00180130000000000c00100580020000001000000500000000000000003c0000000004000000400080000000000002c0000000002002000000000040000000000c0000000007001800100000000008000000000200080000054005001c0000008000000000a002000d0010002001c003000c00100000020010000000401600040050014001000000000000050000002000c00400000040000000003400d00000010004
  | 34 => 0x97c5e58dea00004640001ae0676c0000000b4f27200000000d0e00000000000000000000000000000000000484ebfeb3e40004b4179201726ccc0a800013317c262105e40a90a309461cfe9032d5000000007e62a700ae05c205a0000014252014200005d380002ff8dbcb5f8a7a0002ee400007e4b7e5f363f000004fda9483cb00005d1dda86d8dfe80d4834327a4000000000000000000cae4a862a20b20000bbe91d90b800000005570e6f41e000094200007aa12d28c26a410000000396207200000000000f350001d008338a7697b80001e8ad52c41098e83aab547fb0e4e00000007851d4600000009d99d570001a6d18f0000000000000029eabaf8000000058f000096c000000070b185c000025a6bea0ee00011c26504000b18a2060000e9c000231600000000000000638d6deb531b528b9292a7959ac78c665bf645000000017f87bb04dc75e01fc49f49aa0000ac2a1c800063602e800000001072882545ee76bb12566b53a7ba76182666800000000000015280e90000000000000040000007724a95be70000858064800006e39d9c0000000000737da631b18972a2e288c20300000000de0560400000000006f7122800006de3a9c0006cf000077b000093306062eaa36a75126dc95d22f85278bcc00019b400000000e649dc0000000000010b299800026b40000000000a211cd6480000000000009968000b4d00003dc228d04be24a4940ef405f486c000277c38627625e54bf06420e3a000000000000000000eda39d1982c199c788b20000219a48400008fa0000000000305404fafd7b52800068f97bd2168678be0e9bc00026240002d386dd90a00001c550001ff2000000000027345f064086302886aa693f00002b633a61ae400009b000019fe796af0452e8a2624880a85848000000160033c9c9a000000000000000000000a23696800000004e60b3626d000033fa622bd46bb10000e2a7520000000080200000007f4a98600000006f6a0de01b0000000294e00000001a200001b9000000000004dbaf7600000001878ece000000074789470000e3e0000716bb3465400021ee85dadae0002df4309a132256ecaf210800008e5c58b25177437c990fc3e2a332a188114992d2e62e8b2303b00000002fba4c8d4cf00000000000000bab400049880002b600001d8dc42201800000006acbc3800045e00008c39812000222600027eb6729340140a2b6000000034321fc348800018d821db3549f4609a7a63840272544c92fae2e28800008590001e2a93f9e6a2f00fce6d7000088e800074cabc021f0000220a61a57808480002f7953667be64492605db8c905552f6e143908a693000052a40005f8a19e0000ed80001f0e0000da6abfc0002d7c00000000000002204361c0007e38000b27800006f800000000000000000
  | 35 => 0x34c7096370c8402000000064a165e2c78c329184987b7c400000000000cc9c8400022e01a90000000157671d00008c4914000000008dea53624b408274845cc70cc000c1e00000001dae79928c49f7034a00006fa99800000000bec4529b660000000b258f89091c0005631b4a0001569413c00095d80003bf5d14520d201b1e8000c3598bc71aac02974aa9668a271e87ed06c407a24083c2c4a9d02c88a2cad92471e00e88415ce0000c6916f98b2aca03b33669d84525acae0000c8b09d0000b42e8dd00010449279cd941cd2512af953b4d6116590484c0720a1545b300005c98ce70e580008d080000b26d315ff000026b11b0a871d807c88256b3524c80001b865ed2af7aefa7245e8300e0001bfc56900001b998ce38185340001b02153abc6bc896a8b3780003080d0d65800000000a000000c680001ca739fc00000008dc45095196bf000000000005810000000000000000000001a9a000000000026321d5884e7070000099171e091400000000000c200005701ef400000008b185760002dcdaf400001ec80000000d450003003c162b888fa0000000000000000000000000ba1128d000136861e291844787f800002ea1eb1d4c12681d418129dc1078000074a7d6b91c8a30002c588200cc63848b5a12f2b2db792fd57ccddb6896000000000006761bd0bb9481e49a867cb4f2b00491b0981c93038b33af660af2666b1d9b7a43f079a322902e09800002d8a5678a80000b4ae0f6a1f8000756033051a00006fe993b000000079b80000002a166d38a6f0ce1aea00000004809cac00000000002e100001ee9000047400023800dc8d0a394c240651000000007694ae09d00001fee1881058087000092f800056180007ac00007eb8000b1a80000000000000000000014675b1233a8980a8a1cf000000007d66462052c04a7121a4c9190000000a14a98c4f9a0a20002c32c06aff5babc8261c280003a000008bf8000000000065b22de44084ecb9d1094965efc89b2956233112d7000158838c1f685231eea618288e79861ecb3ed30600011aeb960040b6c21d0675970b1e12b2e88ba57e2c699115135e467ccb0ae589a1175b5adf2b92a5268a708fb76f118e853818758e864c6058000a0993020002b8f8398412599ac1c781b03477c2ab0000000000030fc3f2a8c2a5d04fe3000a5cbf2db46000000000025580000000b6000000000000000000064886d40002f7e47000000000000000148a000193800007a80000fa2c1ea3f400000007698d840000000aa199de00000000000000a391020000000034f00000000000b7b8000a980400a19a66c143049600009eb0000f6a3bb0000b990000000000000000000000dd0467176622940006f4a1832c291616540c6e3e52d146380000b8380004518de800000000d2400091b8000a49
  | 36 => 0x5e10000615c000a51aff400001fe000237c00011a900000001a2800052a9a2a0d00000211c0000002332c37dd1a00017ba67f213a05e1758103305f0001e700001120c28a9125f989043b2aaa683686673df92db00029580002043bdc00000000000898839883080000000b089e5ece800000007ed234a02219c47749acc47f08f8b458c9cb945edc77dabc2000272a00000000000000b410000790ab9e5558000785800051a8000b5340002544000c15a2b50000000953000032e80000d1c5221de078d000000000000004e005c4a64ab9c31c1a4450547980001898000285a4ae54b86d7a3270000254000003e477c13415489e797300004bd0514698895400005aa64b8c4e7c98f0a09a24904dd80003030000a83c0000002c340001c65a999b1c000000031613f45a6d2b6732df4587600000b98000000041a000000024c124279f98869ce2c13000116e00022acbcd80003a204ce0000000771eede1a38000182000000000009d580000002084b1c1d550000b2650b000000026d000025986b503fc9fb096a074c0000001ae218c0d8e9cb187388f8000000239ea295500a2de593205cf78b52c00000000000391b726075de621780008681906000097174aac269dc8faf7e481bd0000e6400000009f01f9ac10800000000008e9800052b16b80892d7200000000000000516058e0ae9cca5f3400000021484704b9e6358bb20000000000305bbb080fe00000009019a8e00000eb0002f3f70a0b394ea000000000000000000723125c45caea400013fa29a90d491f8000af14b760001fb01cf8f60680800083880001fb273600000000000000000000083e400011605542a3c0000dfc0000000000ad39cb753826ac69e95d6c1730888b001b229408deb589de87da8c1e54a97c49b399808a164045dc000000012dd00000005a7858400017aa8a00000000000000001a2000159a96440006bac40e000000013ca8df0000000069df424e22efa91c07dc0001c86000024d00009b20001f474f8800082bc8c04ef0000000000085985fc514800094eaf683ce448c4baafae0000000000000075780009ed807064980000d3146348707449ad282589e9fc63e8064a86c1c76000225a628aa7a000144c77500000b830767ae4000000087a00018d413f00007198418909000000000004522f91bf4207900027698d600005b6800000005105da2ec0c0a24746552314be02796c0e67c16bb0000c42c0000000a3a00003c86ce2010212a09e83c80005270000353800000000000000f149f68000346add80002ef24ad16d91b4913e00000000a300000000293000000000f0000a025a68000000000016b23a14b2000000000000e1600000000002efc0000a8205107281a7000000022460001e8cabea62e6c48db0000000000018a
  | 37 => 0x6e4be97c366b00008f3007e23b80005ad03f21bd6d200000b10000000000021e40000000340a45a444ab8c41f40000f78000aab0000000031b35a00001fd00003640000722400000000000000884000005a851296c5b56b0c0000000812533306ba5570000d3540b020476e0d000e0066a0000ff8000217e20280000d0ac2a41a0e1a0219b200003008508cbd25d1aa307c755f8a9680008b3a134be380004852583000000050105703a4521e00018810000aa90000000000000000000000a89b0e1352c156738dc2a84c0bf7f693259c62a1a71ed21230b25b20000a870000000b8107403e5ac610000000709800000000000000000793000037d05120001ad20002f2800001e5000000000028aa0000000b68180a34b60aa7b28736b0f1fa27ef12ca0002c7882a552e17fa6383b6ca7290c28bb93a00843e613ca4fe218da250e42a7b17ee8a62998985ab4bb5eaa0e62f89db1561098000067e00000007ff0a12000236600023400000000b80000000006c100000000674000bd29f28000004865927ce91816a400013822598b8eaec057e24800007c94c454711436918c00036882be000000000000003578f560000000000089800000009e1125400000003ae15e625cc0000000279000160c00000000001888b01108c000032d20d80000003002b08a35e1e48eac00005c83a35a5d57b80006df661e8569e101171da40452646a92807a8958e000f02b118739ae132f1c790000000ab41e1e4f3e688000217059a18d2c03d7bc000291e0001c7e5cf2cb23b787b08d32d44c212d88bb2c00066f8000858800086f20907c8544faf294724c782f1314ac060000000000000030c053854c8000a2e6adf3a563862b10000000000000016749e40000000000000015f2525226a6c9a6c2000000090680000000bfcb39297a96500004c30360253a3623cd0c5633b1cb0b36c6f109b2f7d6f08a2e260a6143d095a800007c806d208d33680b2476956a193a8e8ae0a29267819ea7330a98c1b0d85bea2f58a1291d23d79ae84be119058201ea6b0e6700799fde8c90a5400000006dec0009f28891080460c000103869ec0000002abf9f4003693ba75b11e2c84b10a95a8c4128073460d79e1caac7471fac00022cc00000000001f05528532f7734000be5efb868403b80002a6c00007b610180009698000000000000000002d52fd226e000058b8f460db6612550432a000130e10f1a6000000004e1258a491cd5674440000000000000000006f21813ea15040ff8000266952600007da704dee81b327b264794e25a2057a8a7a95230119006428000768a228bd894d6bea8a100002a2e84560d20001fcc23065520000e480000000bdce75e00002ce000021e000147121c80001740796601b06e8dd22205c30ac82de8b0400022328481c4e4921eb835
  | 38 => 0x658000be1918f0000594a30284e8259972396807c0000d74000060058b308620393374715fcaa2894da000000000000000228000be5000077caf6500020952131a36706400073e8000ab670f40000000025c44100000000000000227400078c000012aad3772e0202b3680006c89c177c2a1d700027a009f800000000000000b0cb142f9500000000002c2800000000001bb29300414353000071840003b94000000097e6f19f7a145800000000007459c0a0001cdb5211670981000000000000000000bdd19290000ac60260f7b93b00000000000966c00034217b85d2c55000010b400000004ffaaec31d02e50002a405452efe00000000000000aa90b724270cb8232868285088a2737820082684d60001b2d822aa06b2da5409b52a2c1c9a0761b0eebc58ca2a3000307c000220065a181e863cc780002ee04730c981011a9c000105a9be00000a3a86e00009780000000000044260e9aae93e0000432a877b8c98b097880003a40000750800000017c6000000000000004826bb243e26303f580005e2800000000000002c444a0400000019b24deaa4581880c4618e8ecc380fea000000034a2758b90a66925b9a5ebc314cb0000000596817e7a5876aafd68c80000c344a90c10a0f4e2ebb4531f000000055f804a0002b7656700004e38000834058092d03590000000000258507da80abce9a5a532000049000003009012926942ea221b420cf22ec0b8da4aa69dfea95ed708741800073070b0bb711525f200000d75054000000000015a6b0421264b54000000304e4f7800020485e000020cc4fb30daa2600005e09e5fa88400004581b0bf3c000a370d460f0a2ee7c5185e63124ac1ed14fa6ae517a9c009de255938caa62a0c9e31b441bd8cf18fc857bb1c80004130d1e90d12f74db25f56039700000000000010da40124c6000148600000004bb25c135e426a32e54308ae1ac46b1832cab058547a000000000b780002196000000054f800000000000499f16279afe35bfc000149000000000000df0000812c000000247ca34800001a0f480bb2cad0018420bd18000182939c4ca1707000000000000000002d0e52ceba13ff851a86a8000055147a7650d051b7225c00027e6773c000294923c000000000021f84669b270000000411800a00022b00001c0da5980000001b0400009b69700540afb91285f8227e0002110000089e1c24e34bf158bd6ba4000b22800042fa43c0000c2a8889fc4a9d0000000281200021521e0a32e69204da0000000640a3d8b7bcc6f0b2857940d80000002fb40000e7e000169c7570f4b164800027a80005f0154c00000008c81894620006e00000009400000ae1c0000001f12bcc90a6490cf7a00000005d6867600000000000000000221400020d32820c48000000000018180000424000047eb2ac6
  | 39 => 0x8f87899b698cf91fd06d82069780c544faaca3c292fe0000000000000000000000b901e1c46a00000001c2d655871e00000000899af71cc0fee8e10f7c14780003f618ae000163009e8da84a96a7c0002760b2e80006e900004e480000001ac200000000000d100f7147e3df4da500014c3b559f72b2b24c2238c0005e780004906d093f4000000023c0278150244e931264fa31800000003cd84d2615800000000008948f9044aa28300000007c000002cf000004888b4000000000000000000000000000046e9a370250e0884d80d4bf180000000d787b19256000000051d031a28b16490001cd76701b640002101603000056b87c46cbea420542aca462edd60002f8900016af016000000000000000000000000096186ea99e00004d7800018e0c640002f3900008d656d8000265885870d15fc24b9c9853d169a0000b6a0d4d0567c6e9163a3c4c6690953d179a5f683f9cf49c8065aafee9366e2819c0118a3e27190aebf0a334000057c1db94c10cbc2524c02d07477a05425294550002caac1225b005fd2520000573a6b136013984905908c9eb1fa4fca28204c00024b86a916600000000a6a40000000242a0fef2caead46e0002402726edea06eaed4517b0b400005dc8ef008c6470d8000000006750000a7603be044a5349eb12bcaf495551182074166b0ee00098dc0000000037803878f22962b2a836422244c9f8c000651c854a9307c26660000ae40000c2f8000000303a62e701cb74943a87720bec35dd1f0002b1a61c9f3d0000b8c0002930697c0000000c4300012663af5722a2b1bf43a8000009b956600016388f696ed00001f200025770000000367800000021c4000000090a92fe000291400000000001c80af8a81000022e6a8800002fa80000001c8e76600000000844183acbea3c87c6398ade012f8d2374ceb4a5b4164c05ea1c86d96f1f49e1fd4b8a89d62cb1c161a41e8ab5809f01aba9b67e0a3444f19948a69123e20d64163e640004e90704397eb5141c999082c52ba000018c07200000000000068400075aab0a0002ee20000000c0c8f1e000000024621240000000554c0001c88000b32c0000001abe000121d944ae49039dd4a00009bc5ff8090000104e0002ddc04a099c4e298b7704aa63bcef00d616d4220000000000190c0001f3834cd4128670dd200016a79a8800069480449368e24000056200004e44b20d143bd89087420a2489e1b3a0000156000000064ac0007460000c44c0008799b785a490454f70b9c3ec0b1c0001f9c68c2e9807a129e93e94f695790470574786bf708d5a410000a31a5823a30000c4316d8a32800016662b74d880000441a8a13ea3f9b57221a72c9ee6297859d5185b40b765bb40ef2ace0000cb292294fe50099843561f8807e9dc4683975c963104b2fe9a410cf9eb69
  | 40 => 0x1e0a49a00003c948ce59d98b4b42a34ead8800039f400000000000000ed433857d6aab800000000008cdb0c80f6c0000000000988c2cfc338cf4112800012926f08aa8000a940990685999c2f5231a1cd0d7a9a08000b394833b4c2c5ea1e5614246986a0f1a59ab1ac7e2035a51c0fa2d276eba2f22e80c2e5c4af5e2e1143ec202cca8691810067e67a4362a80bf6d3c029f0c949dfc43a34f80c85448878ba5a1a83e380007d5800096700009ca4000a7e07fe00000000002e5007100000001c300002b618f391eeb1b000000014d80002dd43a51520a1b28e6a59000084f84f836196ec000000000015c80002299b830000598831c6cf8450295800077f800000006680000a426ae8000740800000000000000c768310000000000035a8000342400000000000001b736dbd61045e44e250aabaeb7f80009cb800093c29c475660bc0001f4c887920e17494b63b0d5df541ace15d9e354c2a8000000000095640000001d8eb4a800056e80000001584000000068cb09c0778b30c42951a3e98d172290000287a60f5c6651e8fe000072eb04058395ad0000fa500000002e62f99000020822362720001ab048c0000a1cf0e29dd88c22dc1ce80d129547c200001c000000000c8500000000002eba2bda75f000220a70bae2d0f1c0008a50387000000040a000024c80008dda3b46fe30c2000000000d0000984178c000095a8080000000012e00000007802a7e0001cf04aaca941728e8e0002c4cb31d2820001122c1d00008661aa678fa7a84766a3a80ec84982e2bccac8891b0920f2f1c080e0388af21912a9fc026a7bc0fc2a686ab0f040fd90329cfde20999d64aa626dac269c0000002c733e792260000000137800000003ce00000000000000000000000011105e88e8415681bb789017bb50800034ca0866dac00000000000000000c2c800069630068ee117e34714596c6115c22681243e08cb03f99f8055168ee79a00006f000008571750bb86d4021c17a5bd1c0009141c450002eb455480000000000000144600006341aa9efa00000916ac9c4c703015233f208225dea0427b800045d800069a81ec00023e60001ab18700000bd5aa6d9220000bb3d3366ffa3380001a7d00025f086d275c9712eb2072a29002f9781929066482980000000000975855c9f600007ce88fc00026ba00022f08248a84230e4561b387be41a96e20000012000012d0000ea24cc273d2bc700952f09d25d9571c974011c0001e887e914ca00012a04c500000001bce16400000002e8d387800000020440000b8800021300479fba9b7999400026d65c1515a1590bb85fa959900000006560746000308208a8000523400000a0d819a4800000022480000000beded469ef60653d7c00007e0850000212e3388d707aba962bf612df42d8d6645d24f25091
  | 41 => 0xa6fd00021c6b5f135a90b0000254d22e00000000c397e80bd80000d1800e00000008a9c00037e92b1188af843bdd36a000000048c4a40b78a5aaabc18447d0c720b3440000001de030f6e8b6c18000ac995d03b050cebd103500001a565ed4c6a98f854275011f25ce19dc04a97ec00029084378c608a1ee6035fb03c2391ea0bd381720001648000270c504d18200020b9354836ebdecebc34a8c729c416945ec01584734d6e0f32b847a712833fa26264fa23a86a8179305d24ce26101aaae9aa432a5e0c826ec0f20fa893e3e20913ab98ae673996e043b0d294c2c0002ee83a077e10aa5d29ad6484175e0000000b7785d60001f5c11d80001634f760002694417c00000000004f42e55318800000000000000c1a01d8ef8630800000018cc0001f3e69c107e30900000000a2222a531100026fa5ecafe569d80002e297690000000221601c1658000000216828198420001511b15aed07234000a961dde00002284bc4c46365000000000003c5c00000028de99891e2b8bea5e9d480000000c6b000000000008679deaef60001a3c2d49f2e000268c55f4dba9c1a028bb6a6423404348a13280579dc962063977cc3756d2b0300c289dad0107819c2c1aaca260c20fb4b783ac6aa252c03703359c72c2f6aa90ea293092c0000000aa700000002f5272b82ee83909882aba0d820ca2c4804491160aac0a13117bec281a338aca18c4ab4a44a63c000278800000025fe0000000000000046fb11100000008db00000001966000132e000000028140008e4957a0002046000000000007fc00027f60000c3e3dc80009a42aba268103a67684d8c13283e109932690faf260000e6c1ad2f54000000092b8a77551800021a000021d11a700000005062d68b7dabd40000000000000000000002c614201e5087749c0000c2480000001efea5c2a115a42c1f4e44db8a878000000241e7d7c00000018408020000a06a858071a10a5cc9c250001aadba7800081a99d259023220e4254b000000000000b80002a4400009ba000220e5c1800000000001761ea4883298400000002c080000001c41a2f400075a2b1cb6c800090289929d0458297c990501300007c406ca000000015100006bbade88420000a180000a1a8000885856000025ca2bd002c426867a3a5a31c91e000046ef0d200000000ed00007b8081000030b8000000000000003f798e89fa4b440001ae58bd5e5c10e05e25881a6b2a6a7e2bd827fcba456aa95a0a7597f28e3000000025403c45cc1e280460000b8f00005c61d235eb23d2000000000000004cb0430814000000000000002f2a95180007bdc0000001e62000000065395789209988bbcc0da63e9a8600000000000e6a345a5a43e2ce70000000070609f8a40c00029d163c0000f28b164000ade12760002b8e7ebc5b20000000
  | 42 => 0x375000024283ca4e40000000276e00022893cc98328eeafd62cd194a595a37eaa36e90bd400000000092ba3efcd3e6d55e1bd1ffe0002ba0000000005ce50a0578000be9edeb78ca34681290c43c3911c0f9800026a1f8f0000000b1e556700011b409429e6000139a4a392d600001cc7f7e0f373382c80002b5a7372be8707d8223c8eb063d0400011399249b8800000002c10002a9e54d1fadbbb9e9f6b72e7c46fdfb20e326404532800a9d88904e780b0b6f9a96bab184c76826b6823282463922d00000000000000000030f0c3b2ccd6a60000000226686c88f90002ffa48da61bc1c856609fdf9464f2acc918978e117800000000000000ffa00022a800000007bd8f9234117a643f800000020d468280000000000000000000000f46e9a1b82534000559075a00000006cc93e00003057000288f000029cbb9a90c30edaa1bde000064806d00001fe40001ae35029867900000007700006f800007fe28083676add0002bba0000000000276c00028230002e56000000092d9bf083c442c1cb80007e2944ac3a0824b8e800035400005dc8000928000023692c4863800011a800077325388a5c0006c58a4800000005d640001d7a714891037a5ea1a82079c1489da81a8627a07a96b087b1989e69ab81d6c018b04a00022701f7caf0a7798ca000142878da2d6a268598819b05da0ec19434854ec4d29b1eba52c2e20f80002510000000299a000084bb8f8000b4ea0f474e800064e43aea00d547a9200006821e6389b94dc2e923068c203e40000000000058c8fb1728938822f00000000000000ace000015ba82c7476de7c278000af5ca0cac48f5b65e0ebe543a1741a816e400000000000000000009e5bb9ca0be300006f7800097192ee711214a864a2424a5dd26c0c000000010f0000138100000000002c8e00000000000000977ac4087c0a342c1861aa3045f886ba73eb7e19f6000000062e000000028f60001caaa7b80007d887f61670000a8408eab3f00003b8193684a137c000000099faab268105ba0000548808a3044b2461cafc300156c2e5476200003465a2000014788af821000009586a79dfa96d0d8a907057721480000dc1e507a105dab6aa38c00010488978392875abaa000284202e8774722acd75bf8000298dd7c0001e7841c00005be40008ecacf27e65d1bb590000814c1da7d696a6272de08bec9b743c3ebecc0b00000930c9280600000002b7200000000000e6e00000000000e7a5600cd70000fac2572ecc000006a8629338b1748e65b3d8eab31ad54000211c690d46600008165be929000000007d39344b2316dc1e32d239cf2f086e38e920bc80000000deea41585a62d9e34759adc000000000002d3e49e80005d36b2033d99e22d216a0000191f241ac2c4bd9fe600028bf10ca82ea360eb000000007b4
  | 43 => 0x61ba2e8390048200000000000cef000297e20a8abaa150a36c0826b06b7c00000012c546c67160000bf38d6916a60a00960000a6c000158e00029d257a1f8cb150cd55aa400040500004b694a000008ac000000054280003dd2eb69a116b600000008940000a07ad6a78d4000000000000000000000000c1540005d0ad848ffce7280c000000003880ecaa18419898615b446261c000021905a285788cc000145f91a2eae03c15a200000000d5900a4e59b96b358000793ad3392480000c318c800000fc509c00000000000000ca607b685e2db98ee3b54dda0002f1c41bad5e0000000000288a0002f4c4ef80000000a4600014707cc000000000000000000454278693480000002feaab84000acc00000000000000000070e00002fe071c80c993222a85adbf281706b770e40000000000000077380000000b3a0000000000224e00011680002eb8417a9e21a7abb48a11760ad7800000013b200011ab24f1a120000427437207e1fd5af207014c69b692581bb9af46f91eda3418ad41ef1b756d8418ac23db144ac03b672710ba0000000000000000014f0a57975b69525ec0ea88768f418aaa29000000000001861208840800023c5e124abaddb0000000b3416f73b58c4ab4b540c23609619b981318da292e0002f338f20000acaafecaeda30200000008dc80000003052000047095900002a701927f86dfaab799a800016f44a640009f112e99202be41dc2f92bb295e2be40f6b73f51980dac686822201e95f129190e80641f6c74c4a29b7708d17e40001c364c21681bcd0000939b0ab1bc02c0a7a2ab85661364247b10d6888b2e3d1c2124b38b7c405922fbe4d6ac61840c0ae5000000000002b00b9f000303600026360001ce000004ae439212c67d2d51a75483040221f600019923c90e7c00012e55f2800000007420001bb603ba7817bc419093d80000bd038e6d7d2a84550d486db1d8c02d80000001b30797800000005780002548000000000000000001e5b3cdc000000000000000003326ee8000000095680004069d388ba87fa0000e540000e2892ca3e2083292c3d904a8810086e000000053e00000001294460c312adc4000ab105c0000230b0000000000000046949974a180000000000348000005dc0008c940000000000000000037d800063c0000668a9b1a0ea006b53d539c1f88189d851320b6ab2467b2c645c50d643ff1cb4b3002f04de095e1940ca45d908048c2ac3010babf30609a180389f6408b000023fcb38af1dec09bfda9f412800c16d1ade7ddaaebbf983a800019f04a994629f4e7c55c124d42e49c7c0000000000074a50f14cca8559400000000468af825a640002860bd800000004bc8000000000000000000001f960000a0232251e37f0161e2498000000000044d000000012169178974618844
  | 44 => 0xf4e000010600007ba00006e250e00009a000000000000000000007400007e180000001c401be2496102c7f9a8a01b80001f4823140000d985a80003062c29a987a7599e831250760000000b88088b0000000726567e0001006000000000000000e50f331d200bc64948344b91c689d0915e9539b942491b2481729002f5af770000000000220200000005cba1f2a274dde0002daf00000004c6a5880b61cbf6bc000095d400000000000000000000000000000001778d542342a007f72e82711ae8ec41c54c27c830a000165456f8fda00000003f71ce2b4181a40002a232a14000000256c000000000016f200005a4b75c000a3d2a6eb061c6e00001710000e68366035800000000002be6000000000000000002ba26f614e67590000000242823483f309e1cbc00012be00029785b50434b9e8f4f0001aa30002cb1465027124d1109000105214616720000000c2ea87c85fdf0700027f28a28ba223520a3410000062800000001e5841a5cbeaba4b6b11a0bdc7929e722f10d240cc53a6000018848e235c3f909fa3264fb61ad800000000003632a8faa32e4884184565bbc1967d823fdc3ea41035b25273ba0c236970060be7af960000000000246c0001bb800011ce2bb922a0002d8e709df0b344a39620809c49d426342fd8672b3d8efeb256fa933d4afe8d822dc3c4157118587a42be8892bf79868b73243700006922271b480fb21ccc0b8f6675893cc762802aadf95da62416860000dc05d4c00022300004450be2056eb505f480009b49fe375f8000aaf19f286e9f586306f309832f062a00680a938f49000216eb331b5b6a480000000000b4a4a4a3d700004f91eef665838200000000000000000187c0000e593ca921f000000000011a6679c00016b16fc783800000004f60000000000000000000000002023a428d2ea751c3c2e6921a5f5237832d95dc000000020f30b300000000000000000000000000000000000000000000030de7e1073826780006c2b00a6868ec0913800000000009928eeb000293c44e10744a3caa0575307dc29c0000002b4c62b2fa6129a48c00024bc64c4a3cbb8e74c0788000a48400000000001480dbe000000000000000000eee0000000ab5df7477140000002bf91b10b4c80f00007dac000000126e0000436afdcce690da3b080f92882dd047a12ca1c295cd77900000001f7834b696c000a864314513800016c4000b2a0a1c6fd800000004480002b8d577b06422c02a1a3c1e98963800071480003a6914e0002c98041190491aa96ea50b0183762cc9846abce744264e2a7c05e7cab0314860ad2162516032d2fd48541ac8b4d86ecb9eeff3000049c26980000002b5643b8e2c7492ba8c31000004dabd6b8e000034d2bd90001c7a00025300000000a89800019c00003588f6e0001b5600
  | 45 => 0x85a65477600007c3302600000009cc1930c17843e2000000696541a6070000a2fab3cb822bbcbf261786b0000040c024fb6c6ed2a2849aea2a00004212f7c8845d367140000aeb00000000000473c0000001352000299c00000000001d0e0002aa287556eb000000000014a4000000032585a0b9e61fe2a0d1e89fb96345709e790fe1a4e2da24149310368a481c620d5075cc2c69230002db89329b54aaf8cfd3cc5bcc3ec8bda56a8828000000000005c6b3bace7be680000000000a27044490826760002bea0001f3b00024b00000b149e9000000001a00000ebb0001ce90000f3a00000004ac8d5a000000091980000000d958532f7f7a1800057193216c946be80314002114000039ad58b321dca00000008479dd60002759b7b40000000000000121b0000000637ad25000250200002d20000000ada2a2a00000000000a32ab688620001b8318fa5b71614000bdc89400000000000122c31e800074d0d3f0000db4000000005b1c565ba68460002454000000000015c40000ae80000c510000072134000000006a62ac86140400000b1b8f12941951e7af80000002fe2482956588d8000321000023a00000000000bb580000cb802e8178000712d74000027d50a780009894000816c000000070c33dd40e00000008e827839218db2958243982e97ab00023ca0002eaa535e3820000e970000000afda9ce00000000000dca0610575000286200017201d600007c62c5a552664436b1cf372d9a4643488400000b0e73909364a71ba871ceef00000000943801a6f8a5920002e6c4412e6a48660c60e1000044c197400011d80001664000000000022ae000206c03d80005050000000000022dc0001cc80003fda572b7f04e80000a4ec32a0630000fe2685265622293ce9e289520d7834e9750a339d540009c2800000027f85f7a1e20000bce83b0000000059e865123a25a2bfd61492fdb20eab60000000000000052f8f26aad15828b69c3a52b8caf1cb0fbc61b2c123691cee5c0a960964165c128a696bfcaadb66955ea2f40e1497e831026897a9bce02707b30aec53a83f75648f408ef86c7066c0008b616c815c4000088c00000005b584328307cb0a140002c7c99d5d7ab7c00009e8a8bc000111a3f80000a06000066d8000305019857e8f220001ef9000000018404b06fa130a5de80008e603b000029f2057283989b075400000000de1e4042c2000bb180008b480000001ef20002ae49d100005be00000001cec27d8000000000040382387df0e61000260ab7180006740a5a11b10c60000000b679f23a7400008668e5280a87f000010c843d000071200000000dfea072ca73454000a14c9d94bec00000019217c45fa6b42092a00c974c5fd0e8233389ec00000004ea8bb460f99a600025230002a827ac4b7e7bc04ac31f85b800000
  | 46 => 0x328929a12a0001bc450943641faa5705522b0e6d9c51c5e01f7d00000000002a0260d28070000c3cbf385280002fa0ab1a3c60003102b4687600a488897290000b364b221fb8000000115f2f900000002c6d000028868e6c4ba94c1331ee11560000000320cf4c00009d880480000cd80000002ac0bf46cdc0002fb0a248e5e5c2800000028ba71505ce104092812e05e8948400000000003ea8a283831ef800000000000316000000080d908e0000000000000000011640000000a43a7700000000af80000ad8256a0ab8f3c9ae0000000000015ca73700000000000000000228e091800000006fc62280008eb2e92acc83045490790be047081c4b02fabe00000001144b94a8cf07ce158b8a278e4f084540000bae0002ba31a60f7393d2d000fe80000002e5d1fa2b9ab40e3d4ab214980001d3e57d6fc453900000000000b29a8d000000000000000332000000001ce23b06d8b34c000000000002b0000000269a0000000b002a3e3995b7c46a8f800000000934c000000000094eedc400002d495b925e53081a50001abc63da53e8618000ab607882cc9c058e529be000000004c813000000002ad80005d10000000232a5560000a6a8000000237b6e70000391a6bc000118000009e300016f6b119a5344f1184b9c20e068f6bfcbef2e785aba9760001a3558280000000000b2e000000006c2b7ec1795b0242646c8000000131600000000a816890d88000000160261f8000000000070900000000000579000061900009e480000002b7b0000fd40a8d9e631014500001ffa4910000a1a0666953deaa3665332ba700f8000000000016800001d740000764000000054d8ec600012377d4ce8a6f9871a54cc0000002c2100026c00000000b6311a132a9892042adbc00014c079f00001199ed000014541e9a0ac8dc000000000540000d7c2f1800000031050000000554400000000005e5e39a000000042782deb2c0dd65f72c14b436d7052a20267ea184e00027e8000041657f80001f384a00000000b2865b6000183c39100008ff920c00000000a5951c32f800012d0000000000082fee1422223b605b941c15580000002330516966e94d5c5a0000000000000000000008a2c00000000007c26ffe000000000000ce11c80005538000469000084380000000000ab4a87865180001bc806639dc000056b1125ed8000000147c54e00000000000b6e800081a23fc000000000008f4000000012123c410540005ac400000000000001b4c0001a2e1130000a72010291e92a2000113600000003ba848e00000007b90ec99f920b600000007bba5a7a46a3ee00025a57244ecc68e133c2eda84087ea57859b6a78a63623c7ed95efb3a554ab9192f0951c000000134cb4996982fc890e7d014a646d924e2c59d042ec0000000077aa62e2a20000000b
  | 47 => 0xb3810530df9e1a19600000fd09d400026641e70cc048883d4986154d99a869600029cc22e800000000000001c5c000000000000009272e441200000000184a0002f1e00000005240cdc00000003b222d79123114000255c3792ca010ecbc8264e00436a91852a890aca332cff052ac3800000008f918f4c040aaa6c6a73b699176c367172a194852a81466b2130c4b6b60afd3b9780000000000520000000000002af20d617c2b6ec142f3d41707140001800000082c12626ae591a8340000000ad09ff60000290a3954340001f5b18caaf600000000002d9600000006fba848000000000000304dc80009f5c0006a212e690889c000000000000000000001c9b24c8000002d000000006e0303d0319d1200016f38f580001f0000051d80002e010bc0001622b651a8c30e95430002607643a82aa970000845aa170000000a082f63a8a566c0422b580001d525d8de0200000008df50807948f308054e320002d3f13280000002d6c5f628e2a8e209800019aa467caea6bfa97c4819fbe0001ad10001b9a805a52e0001ca13fd00000000000724000000000003648000000000001e00001f2800000000000000000b4600000002bb800000003462f1014e8b4e5b9800038706a2bd90000be627b800000007c0c0000000000000000000000008b50e930a08000000000039c4000000000000000000000814658800000020c013b8772860800080900006fb1616000008e260c9484a8e5ae21aa584abbdb8c00020bd8bf177e3fc081a000175296885a66cd0000b3a9fd0b4f45862fb9bba0000fd2977035a6e8800000000000000fae1979eba7f0af6c104dd5022b80000002f245f38c5a8c79846722c00000000001e2800000024e05f41f5d00024ba9dfab2c000000000000000002a55111800000027bb0000000244a36eb690000baa06566d6091445f291c00000007e6e9f4a62800027328f82b0c000ae14f58321a3286568f1100000004ec164472b400000014609c6a4320000c397c100009bb8000aaaa754000000000018dd0001010b20579c81f30a8756874e0000f8a00020f8b13853eb489c9e108d3d414c02cc95400000000000000000000000000002b8a2b925f40000000000177640f800054b00002f98298a3f11861f5e77dadbcff24ce80000002bf400001eb000000000000000001a9400001a600000000e6800000000008a08000b9ba9910264de272a17784498c9152211b856c8cd62d1935071280d042411ec0edd31b0000000221a9a651080009f325e6810800000000007ac8b640002da2244022182d0ddc000000025540000fb800000013b83adab404e80ce0b17c0009ce442265c086b3d12cec86d956c02d0f1999cc000274c0000000eaaa3f970e00010a80002a34b136ff7c110e500000000000000037c1356000083a739c
  | 48 => 0x13a76f8f200002d320000000000052600000000000cd45b08000000260ebc82b04c090b4200000000002c360000bc2000000012e80008b8800011b9ae60001ed46f0de599e212c1556800000007f200017b3c0ec000572800000000005ba92c289f2b140f585ae0002b4600008f000030c02fa0c086010f180002cc2662800083a0ee6214c0000000000a7c00002a9883f83e9e3a8162b7abfa0706a7beb498d15c9dbc018d00001e9000002a88688c66bed400047e9ddc000029f26fc0002d40000951000064400009524000755938f0002f12514d5acb3e94a2092674600025da1ce8000adb1685a8b67b09112adc8bd17a463b2e67a7b40000000000b268afc0000000000000000020ae0000d384c3c000397000014da6f45a38000b4b00007d9a83294529e07e5dbc18d4a013b0c704635dae8000018a4b939c040000b6cc356ff6103c0000000022231961a78b03336ca000041ea5322d62b365cd23a477200003c26ec8a088900abf48e203941856899c704792e305ba253c09783a407d11bc015a078816aa6a88b00000000000000000034e9a900ce80000000000a532fb6b96cea4bf92e2647e000000000007b62b808e22d76461ed352eb21e8b3624de85b036a20225bca0390f217a8e762b7173a184976aa1e99760000000b172cf8000247b0000000000020a59480000002cf48e4000000000004772ce200008b2a9c9432538cf4aad9a29a0001b2c28100002a8e9964e50000363400000028020000f770000284a8acd8871c5b5a18e8ccb9509ec8083a1386a110d69dd06bcabf94ce0000b2a700d790a4e0000000193a5421fe09340000ae249ab7e55ac154400000000000614000013208fe000000055ba69c0000f071ba1cea4780dcc53a2f884632e5755c8000000275a4008322a640000000000000020a00001ea26165d2063c8894c442d2f8238000000102639300008181c940938b5d1da2d7478e02dc3328cc21db133e587029422384c14b8acd2094ebc45eb5a5079b0000a19709646593d84156ea28a06722627400053cb0f26e82b16b148f9a66f17da3038d720002bfa2ac1650717ab3eb73c0cc64681eea6cc0005190000a41a1049a82350a0e1dda08c9b9ea7280009ba800000027c8c2d9a344c80c8c00025ba03e8a20bc60e040002bde3aea2a4b21905070265b3af20b5600021d4439d7ae550146c45b0c16520878b0003014661ac630000000a6a087e00000000001a0600000002728000a20000089d0000c29400000000003c6a8e05a0c000000000000006b0000000050e40003280000c2b6f2e0000000000000081ac000a0f1d9a216e2309a38c887b880008820000bba80000022d980000000000163e1418000000168c00021da855800070807d206b1dfc9bcaa8429f800049f80009c11ea60001d96
  | 49 => 0xa4a680002ea00000001daa0002e1f2838ce525ea6488d900a489300e84e8967800003811f800006a01ece0001d22a3367c2bd226c6000045251cc0007580000a4c9158ad34c446270120255c0000000f0200000007c7000047f80003a98f9c00012cc0000000000031e17d800062300007d194260000000247222a000029a66c18089b8000474287cc0002d12848814e949000000025b8c360a389e00000a4d02b103aa0a42c027b47360000388291056d28749e700002119596bac00000c60acc4d1800031040d2b442b6a6d80d9f74c0ca245880182f2800056e27999c39b8496819a0511303f0000bf490e15d8bcf1fd6331c0000002e5c0000000aa380000000000906000046799fa00010d0000000000000000000000b0812aa0a28e027298000122800000000002828f000002facb1a23ae0000000000268a96a23de00000000e780000000000000000000827c640a9bd634c000000000000002580a14310e0000000a5a82e4b25cee4512000025161e0653eb082b8000064d000001496c67a39324b81ae8c6e221805819bb04032f353184000b3980005d240009e46f873ad0b3eb4a265c6cb8a613ce28b000002fc00000005fc9b62000028029c0000653000070f4ce80000c224418df88bded1c9fc18e200013075d5a89f7999e609251d059cca11400003d0bc512840f69fe23a1a4eaa949051874820b00780009306268331584861d5dee0002e240000000a3aa5c200000002d35c6c7d3d086ae495e19f451d6a1d531718986840db1b0c44b8000b79959492a9ec479200008bda73a1d4869132b000023c8a73ad48fc238f00000002172a1c1082b99982413c259ea339c078e8ddea1022fdaa8fd7fabdd53b49b2127f362c00086426f67791ebc0b880000001c229b2c000430000000000000000000000062e0002a460000000646d0c296567c713a80004968000000000055809fc81c238e000267416c000000002d6819c000000264c8e8490200024527ee18360051dc0000000000003a27c7800000003240001c728b2a38a000013c0109a6e0c080008a980001222d9000019a499615d2000000000005f40001a744462aa0000000000000007e0400000019526da1e540002aea0002ba99ff8b12b82800000000000d46bd80001ad88a1aad400010fa0e70574923979184f049e71800000041e0c0001ada3341a2c78629fab8b08561d880007fd085f0438000000000099b92c00ee9f060002686258000000016b086219ba00024720002afc36241b71ac8000b8080006081ede00009380002541a7db09a0001c1ab038dfc80b1192000000000000000000d9609f28d6068cf850002e4c000000000000000000000000000037b000000000003aa0000000000000000000002a56a145bbca620cee67b80008d2189a07a592a9e61a3a000
  | 50 => 0x7a63cc240000000000000000000002c5b000175400023c23ac46421ea80008fdd528b23c00000000007f22ef400022c2c32df3425ec00000024d800016f0347603f8c000000002b2b2b580001d98e9f070997e25da3dc2183106a679db09d29798207000006a694000015bc02996be7d49f785f31bbeb1800000002d240002f020000f866ae00004b1941e5509c53b6daff84490000072cccc00026c445ec7e6642409caa2800099f000061d86159801a81a988000aa4110000013c423812ac35100002650000ac4000000000001218000000120430d8d4a0059a5500029da0002af500000000000a8807c5a1e3c18dc4adf46a83f180240518000719c000000000000028900000000000012c4742e0165a80000000000000000022d84c231f1034000158a7c92a12b235cd46daa2388500ce33018ec4c332fd900021f400013d6000000020f4a2a9f85492771a86431b23265d8add0000000000000003d4b0c6096000097151ca5fd86df8ad0e389d22c487ea9d720001d545c41c699bf10f67dba5e8b878a1a44209af7811b827f6228c6722956515ac9da351a1d2258000bd68d600001c3e98040000000cea26000ca930d8fc00000008fc188e14b2ea6a059c4d9e78000ace800054880000706fa283f2ba40000074b202a2405930160000fc49109b812b398821a56f3e23dabdcbd09c02900400057d800000030dcad21c3ba75c2fe0002fc786b27fa0000000bde8000c252d66be96628ad3de65a1db0fe312c3396890d39c231e9e7d5289ebb9d5a000014b419b08a8a4f9cd23eeacc57f7400000013100000000716c0000fe66d873f00003cfeca520ba9c60c811c800029aeacd2c1e9aa2112718ded669f9a8f000124c5b2ad1e2d280005540000092a9b4bef80000000e36372000000030d498200004eb265000028963e3000076eac1ab2412ef0000000000030f0002254000000017c9a0c0000a581628000a0a00000139f445cd8a782be00009e140000001292000000041918963048cfaa01039f0b180000000000aa200009d902225679c0800012dcb8d04e00002bda6e4a4587df9dac00021de0002fee0001c646f288c46a2632c000000000000000000000b568d7b5aeb05ab9f800000000007288cf9000000006780006c20c1d2e6498c1e825164428000788ae2ea8d8225851870e707afc00001df457d23a29d381abbd722d918929b849298662e5982cb739d0c82a0000731a0e5000000077e5aa281b91669f485eea8f217a8ea99e41a6a27f198187b37cc5320002ea011f29a0a8c8000000173e9c0a972000000097df0224ff2b4414014ab00000000000000000077ec0faa14408a5f86c40fec00020341c41ff0220118a34da98e9ba16280000000000112c4b840003efa04100000003d52e360f4985d00005fa00025b1000294
  | 51 => 0x5458000a298000b5b982e2f82f4958d92d455c15444ca885c08faaee61e5cc40000326bbb000000026020dd93b66050c820002c24a82022ea6e8000b61a62054c31003499c887a0a52a086ab9888d0000000153a53b6ece2a780009101dd047980000000000521567c1aea98249d1efc2790000968c0000000efc0000000000000000007d8815aad60001a40ad70000b40800055d000030700000000f84000000029a000000013d20000e663131042000204e0000000253196e00018c60000230227cea9438a51a0002b860002fa4000000000026a6c1c04f46d6587a00000002591a510f7c2f53718a927f3adda1918c42a88800000000009f95684bd8400082c00000000000000218400001860001f1a502000070a8000b0f998e00006daafc817600000002661658a172528732128c6caa2bc7308cf00000000000000000024d53c31c922ca1d289c9c10c3bc200fbb7426100000000000ed20000000aecdd76302830653510679bf80000000e780000fa40000140c2280000002c9fa2b82fa000077c48d12967c341f000026031750000270907c6068a6000000002e080000dd0000b968dae0f60000bfc63ea00000001eb997a7a6aef5409229b000000067e00000001191a6cab53813ca16a991945955000087280000001d4e1e24ced54d40003da13f2b2093342a902ef00000000280000a82afcc000000079d12240000000bd7ecef6f5000032b80009e68a6580516d770194dbb4300000000a6700016246dc0efa00000002fdc1663b0800049b2e8a85a92e0b02011ab93c0000000aa80000000000000000025890002dc200010a26e420940e188c82d700009528000429200aadd239c299000000010b20000f6cc3a80000002af100000000000492000123200000006df800076c8000009800093585464ee8000190000000000009a780006ad00000002038488d3ee0002652abd2e225fc265e6ada93a185f0f600000001f422ab0000000b24a02e0002e687dc025114f171a5c5a8fa31782c254548e5bc691ff6b4262910282b200000aa7b0a5ea0434c8e000130422e1ace69fc6741d400009371cd03d6a7ea306000000001ef000195e8ae8a9655f221c57318da586141647d8000000000061628a3bbe000000000005a88f2e9ea8e9e00009161c5439b000000074b80d826c40000000000273a17c9e500000002c710b1257a4680000000216400002866fca6720000000ac602ac0003000000240e889195c4d3a5624dc03cb0be08a0884800000007180000000bc580000000edc0000000000000000016820002708aa4800000000000002f8a000000000000000002e62806ad9c000246484600004180ade00018d908f0fb400000000001092000000014b91f04bf20dc0000a903c21410a48aae28f8164e08613540002510000000033
  | 52 => 0xb9c9d70339000000020893cfadcabb7c717075800000025e415aa33c0000e26a700000364dd9e19100004c880003d8a5ce5d44a8e0000397adc0f91afe000025c00007d2800027a13868c31f5010aa7782c92c74a9506c04a615684331c51b3b4a6252c8d8200000000000000000135c00000000001e2e9a900000000000c01000005f12209ca000000000000000000000308e69f14c905a89daa408000000068c7e81e7622980000000000000000037380000002e8800000000002b64c1a11d4000062a39280000001c96000072a12529fe812065c0002f45a19cb909f50000000000008d800047aaf8500028da0588000000174840f035c70381423d41a66101ef6a0000000c4214b0085000049f0000939150c0002dc88fd9d6e0f8999e764af4f0001f9e0000000000050a74f1bacbc280008192c7b73000001b8191676713da000127291e6b7c00000004ba1366000000000000000000000000000010a30e6727d0e600000000001c003680d2c0000e0a0000000000000067180007a51c572f7a63a00000001169786a03294463f8f1654f262a1ae0aa52519af6407147f15a255b000000065f0000a4a000024eb0bc14107d46c00000000295c61d0b8600000000000ab8a8bc2761a5058826918a68c5dcf69289c14aaa2cf022f30d05acddb46d418e6bff06c826fa7e79f82ae830e252264b29a258aa980b1980008991f6cb058b5ebb60411b84949a7c08191a29c000981ab1eb7fd48e9ebb01e2bc81d81b59a1c26cd3429e6c0001e0000059e9d9000027685101cf8a111dc2ba190e87ad056cabc9f908402c9c46b094bb7a6e1aba6ac8b2d029b00530cd20e258bb86f80002ef0ba6b62877618b2356537800000000004060000000000036d80004dd00009558000000030d6008000673000000000000000f6700010e0a2d25046e146280001de27a480000aa80000000000425800047d07a55c9000065080000000000326800000000006db91d100000009aaa9e408823faa49aa943ab800000030604f35838262a42e0001b360582cc445c02441bf9f20379a7261e382b6b48678298b0000ae59af86f221ea00000000002ce3c2b2ca400027f43f205b692600008698ee2445800000000002b6a7530288000000281479e80
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x864d5398b10043172a2c5880218b55162c4010c9ca6b16200864d5358b1004236bb4a5880211bdd952c4010e4aa890e200874553487100438aaa2a7880219959662c4010ccacab1620087255454b10043a2a9aa5880211d5da51840108f2ea324200855973d52100431cb2ca9080211edd95484010c74c8aa4200863965552100431dbb2a9080218e1d954840108f2eda9c200853974d4e100432cb2ca708021c65525384010cb2caa9c200871a5454e100438caa2a708021969915384010cb0c8a9c20086696594a1004394aa4a508021d254e5284010cd2caa9420087295454a10043a4a9aa5080211e5da5184010ad2eb90c200866965c861004394aa64308021d254f2184010ad6ea90c2008669654861004394aa24308021d254d218401087ced2a2200843c76951100421f3b2a88802187d925344010c38c929a200861f6454d100430e322a6880218bd925244010c58c9292200862f645491004316322a48802199d972144010cceca90a20086a4644851004392aa24288021d154d2144010c6ee9b2a200863474d95100431bb2ec8880218dd946444010c6ecb2a2200863765551100432bb2ca68802195d955344010e2aa8a9a2008667659491004333b2aa488021c95515244010e8aa6a92200863b74d95100431c3a6ca880218ed9764440108f2eb32220084ba74991100431db28c8880218e5d464440108f4edaa2200863864d5110042acb9ea8880212e1da5444010a72eb2a2200863b65951100423c3b2a8880218e1915444010970ecaa2200863b65551100431dbb2a8880214e9d95444010a70ecaa2200863876551100421c3b2a8880211e9db5344010a72e9a9a200863864d4d10042acbaca68802196d965344010d30c929a20087195494d100431c322a68802196d955344010d30c8a9a200871a5454d100438caa2a688021c6d915344010cb4c8a9a20086586454d100438c322a688021861915344010cd6cb29220086a8649491004394aa4a488021d254e5244010cd6caa9220086a8645491004394aa2a488021d254d5244010c72a9b0a200865953d851004398aa6c288021d454f61440108f4ed28a2008638649451004358324a288021785ca5144010ad2eb90a200866b65c8510043543264288021ca5532144010e92a790a20086b0648851004398aa44288021d454e2144010bc2e510a200856b754851004335b2a4288021aa1912144010e52a890a20087495348510043583224288021cc5512144010ea2a690a20085e37548510043b1baa4288021b8d952144010ec6ca90a20087a36448510043713224288021b81912144010f40c890a20086a06448510043b1aa24288021e89512144010ec2a890a20087a1544851004390aa24288021d8d4d2144010f84a690a20087615348510043e0a9a4288021d054d2144010
  | 1 => 0x40042acb9ea9a00218e59654d00108f2eda9e800853974d4f400432cb2ca7a0021c655253d0010cb2caa9e800871a5454f400438caa2a7a00219a59652d0010e52a929680087495394b4004334b2aa5a0021ca55152d0010e92a6a96800863954587400432ca9ac3a00211e5da51d0010a72eba0e800863965d07400438ca9e83a00214edd541d0010c72caa0e80087195350740042b4bae43a00219a59721d0010e52a990e800874953c8740042b5baa43a00219a59521d0010e52a890e80087495348740043d1a0a43a00218d55161900108bce7328800845d739944004237394ca200211b5ca65100108bce6328800845d731944004237390ca200211b5c86510010a72e0aa08008655539844004332a94c2200218d9516110010caaa6b08800866552584400431db2a80200218e5954010010e34a6a0080087195350040043952928020021ca5494010010a72eb32080086396599040042acb9ea8200214e5d65410010c72cb2a0800847b76550400431d322a8200218e5955410010a76ecaa0800863b76550400429db9aa8200211e5db5310010a72e9a9880085597594c400432cb2ca620021c65525310010cb2caa98800871a5454c400438caa2a620021c69d15310010e32e8a98800865a6454c400438d322a6200214e5d74310010c72cba18800871953d0c400429cbaa86200218e5954310010e32a6a1880085b07150c4004334b2ca420021ca5525210010e92a72908008669655484004394aa2a420021d254d5210010ea2a7308800847b75584400431caa2c2200219654d6110010ea2a6b08800847976944400425cbb482200214edd64110010e32a7208800853975104400438ca9882200215a5d72110010cd2cb908800872954c8440043a4a9e42200215add52110010cd2ca90880087295448440043a4a9a4220021b85852110010f4082908800843f76953300421ebb4a9980210fdd954cc01087aecaa6600861e6494f300430eb24a7980218799153cc010c3ac8a9e600862e6494b3004316b24a5980218b99152cc010c5ac8a9660086555358630043172a6c4980218b553624c010c9ca7b12600864d53d8930043172a0c4980218b550624c010c9ca6312600864d531893004272b88c4980211b9da524c0108d8ed292600846e7654930042363b2a4980210f9d2650c01087ae9328600846e729943004236b94ca180210f9d0650c01087ae8328600846e721943004236b90ca180218d552610c010ccaa5308600863554584300432b29ac21802199549610c010ccaa4b0c400843e74994200421eba4ca10021179ce65080108bae7328400843e74194200421eba0ca10021179cc65080108bae6328400863554984200432aa9cc2100218d5516108010caaa6b0840086665258420043172a4c5880218b55262c4010c9ca731620
  | 2 => 0xc5188219354d628c4108deed294620846d7694a3104237bb2a5188211b5d9528c410acae2a94620863954982310432ca9cc1188211edd5608c410970e8b04620863954582310432ca9ac1188210f9d3650c41087ae9b28620846e72d943104236b96ca188211e5c1650c41087aeb320620843f75590310421fbb4a8188210f5da540c41087eecaa0620843d76550310430f324a61882187592530c410c3cc8a98620861d6454c3104236bacc4188218b952620c410c5aa9310620864e539883104326a9cc4188211bdd5620c410c5ca8b10620862d54588310432729ac4188219354d620c4108deed290620846d769483104317324a4188218b592520c4108deeca90620846d765483104317322a4188218b591520c410c74a9300620863954980310432ca9cc0188219a94a600c410cd2a5300620863a54580310431caa2c0188219694d600c410cb2a6b00620866a525803104334a92c0188214b9d352c8410a5ae9a96420854e73d4b21042a6b9ea5908214b9d052c8410a5ae8296420854e7314b21042a6b98a5908211b5db54c8410a9ce7aa6420854d73d532104316b2ca9908218b59554c8410e50e0aa6420846d7615321042a7398a990821535cc54c84108daeda9e420852e74d4f2104296ba6a7908219359653c8410e1ca929e420870d5494f2104326b2aa790821c395153c8410e1aa8a9e420846d7614f21042973a0a7908214b5d053c8410ad4e029e420863954982210432ca9cc1108218e5516088410cb2a6b0442086695258221042973a6a4908214b5d35248410a9ce7a92420854d73d4921042373b0a4908214b9d05248410a5ae8292420854e7314921042a6b98a49082159dc765484108dcedaa2420854e73d5121042a6b9ea8908214b5d65448410c5ecb2a2420862f65551210439238aa890821ca1c154484108dcec2a2420854e7315121042a6b98a890821599c45448410ad4e02a2420846e76d4d21042973a6a6908214b5d35348410a9aeb29a420864f6594d21043872a4a690821c35525348410e8ce329a42085657154d2104327b2aa690821c39515348410e1aa8a9a42087467154d21042373b0a6908214b9d05348410a5ae829a420854e7314d21042b3388a6908215a9c05348410e4ca9b0a420872554d8521043a329ec290821d154f6148410acaeba0a420872554d0521043a2a9e8290821595d44148410e8aa620a42085e17010521042b2bac6290821c99523148410e4aa918a4208745538c521042f0b846290821c99513148410e4aa898a4208746534c521043a2a9a62908218b9526208410c5aa9310420864e539882104326a9cc4108211bdd95208410c72a9300420865953980210431caa2c0108219654d6008410cd4a4b00420843e7498e500421eba4c7280211bdc963940108d8e4b1ca00863a74597
  | 3 => 0x926214810c9cc7310a40864d63988520431ab24c2290219558e6114810c72c9300a40865963980520422f39ccba1021175ce65d08108bce632e840845d73197420422f39ccb21021175ce65908108bce632c840845d73196420423abacc3210218d5526190810caaa730c840863554586420432aa9ac3210219994961908108f2eb304840863954982420432ca9cc1210218e5516090810cb2a6b04840866a52582420422f39ccaa1021175ce65508108bce632a840845d73195420431caa6c0a10219654f6050810cd2a5b02840847975181420431caa0c0a10219654c60508108bce7328840845d73994420422f398ca21021175cc65108108ece2328840843e74997320421eba4cb990210f9d065cc81087ae832e640847a70197320421f3a4cb190210f5d2658c81087ce832c640843d74196320421f3a4ca990210f5d2654c81087ce832a640843d74195320431caa6c0990219654f604c810cd2a5b02640847975181320431caa0c0990219654c604c81087ce9b28640843d74d94320421f3a4ca190210f5d2650c8108eae2b28640847970594320421f3a0ca190210f5d0650c8108ece2328640847a70194320421ebacc8190210fdd5640c81087eed2a0640843d76950320421fbb2a8190210f5d9540c810c3cc9298640861d6494c320430f322a61902187591530c810c5cc9290640862d649483204317322a4190218b591520c8108eaeb308640863654984320431aaa4c2190219554e610c810ccaa5308640863654584320431aaa2c2190219594d610c810caaa6b086408666525843204332a92c2190211e5d6600c810c74a9300640863954980320432ca9cc0190219a94a600c810cd2a5300640863a54580320431caa2c0190219694d600c810cb2a6b00640866a525803204334a92c0190211b9cb65904108dae5b2c820846d7598a41043172a4c5208218b5526290410c9ca7314820864d5398a4104237baac5208218b9516290410c5aa8b14820864e5358a4104326a9ac5208211bdda52904108daed294820846f7654a4104236bb2a5208218e5526090410cb2a7304820847b75582410431caa2c1208219654d6090410c74a9b02820863954d81410432d29ec0a08219654f6050410cd4a5b02820866952d81410422fbb4a620821175da53104108beeca98820845d7654c4104237bb4a4208211b5da5210410c9cc7290820864d639484104237bb2a4208211b5d95210410c9cc6a90820864d63548410432d29cc0208219654e6010410cd4a5300820866952980410431d2a2c0208218e5516010410cb4a6b008208659535804104335292c0208219a54960104108dce5b2c620846d72d963104236bacc5188218b952628c410c5aa9314620864e5398a3104326a9cc5188211bdd5628c410c5ca8b14620862d5458a310432729a
  | 4 => 0x3ac9318a60862e649885304316b24c4298219398e6214c10c5cc8b10a60862d64588530432731ac4298211b9ca6114c108dae5308a608635649845304332b14c2298218e9926014c10c72c9300a60866a629805304334b14c0298211b9ca65d0c108dae532e860846e721974304236b90cba18211b9ca6590c108dae532c8608479705964304237390cb218211b5c86590c108f2eb304860863a54982430431caa4c1218219654e6090c10c74a8b04860863954582430432d29ac1218219654d6090c108dce532a860846d729954304237b92caa18211b1c96550c108dce432a860846d721954304236baec4a18218b9536250c10c5aa9b12860864e53d894304326a9ec4a18211b5d46250c10c5ca8312860862d541894304327298c4a18219354c6250c10c6aa9b0a860865553d85430423aba8c2a18211e5d76050c10c72a9b02860865953d81430423cba8c0a18218e5506050c10cb2a6302860846e729944304236b94ca218211b9c86510c108dae4328860847671194430430f2a4c7a90218755263d4810c3ca8b1ea40861d5458f520430f324a7a90218759253d4810c3cc8a9ea40861d6454f520430f324c7a90218759263d4810c3cc8b1ea40861d6458f520431cb24c1a90219658e60d4810a5ce9a94a40852d74d4a52042a739ea529021535cf5294810a9ce7aa4a40854d73d525204394382a929021539cc5494810a9ae62a4a40852e74d4e5204296ba6a729021c39525394810e1aa929ca40870e5454e5204386aa2a7290214b9d05394810a5ae829ca40856671d9252042b5386c9290214b9d06394810a5ae831ca4085667118e52042b5380c7290215a9c24394810ad2e121ca40846f7650e52042363b287290210f9d0635481087ae831aa40847a7018d52042973a6c4a90214b5d36254810a9ce7b12a40854d73d8952042373b6a8a9021539cf5454810a9ae7aa2a4087287055152042373b0a8a9021539cc5454810a9ae62a2a40846e76d4d52042973a6a6a90214b5d35354810e1ca929aa40870d5494d52043872a2a6a9021c355153548108dcec29aa40852e7414d5204296ba0a6a90215a1c16454810ad0e0b1aa40852e7418d5204296ba0c6a9021599c46354810ad4e031aa40856a7090d52042b4b8486a90211bdd943548108d8eca1aa40852e740415204296ba020a9021539cc1054810a9ae6082a40843d76950520421fbb2a829021879526314810c3aa9318a40861e5458c520430eaa2c629021175da5314810c3cc9298a40861d6494c520422fbb2a629021879915314810c3ac8a98a40862e549885204316aa4c4290219394e6214810c9aa7310a40846f765485204317322a4290218b5915214810c9cc6a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c5204317324c4290218b5
  | 5 => 0x863454987204431a2a2c390221531cd528811087ae9b2a408843f74595204422fb9aca90221171cd65481108dcec292408846f7654820442a639aa4102218bd5262c4110c58a9316208862f5458b10443162a2c5882218e59054c4110c72ec2a6208863854d8f104431c2a2c788221ca15262c4110e50a8b16208872854c8710443942a24388221c91512184110c9cc7316a80864d6398b540432731ac5aa0219358d62d5010cb2c7306a80851e73d52540428eb9ea92a0214b9cb5495010a5ae5aa4a80846f7258e5404236392c72a0214e9c26395010a5ee4b1ca80852c7258e5404297394c32a0214b5ca6195010a3ce630ca80851d731865404297390c32a0214b5c86195010a3ce7b22a80851d73d915404297396c8aa0214b5cb6455010a74e131aa80852f7258d5404296392c6aa0214d1c56355010a70e0b1aa80853671989540429d384c4aa0214e1c16255010a5ce530aa80852d72985540428f398c2aa021475cc6155010a5ce430aa80852d72185540431db18c0aa0218e58c6055010c74c2302a80863861181540421fbb2a82a021875526315010c3aa8b18a80862d549885404316aa2c42a0219398e6215010c9ac7310a80864e635885404326b1ac42a0211b9ca61150108dae5308a808655639845404332b14c22a0219698e6015010cb2c7300a80866a629805404334b14c02a0218b95262d4c10c5aa9316a60862e5458b5304316aa2c5a98218e1c164d4c10c5cc9316a60862d6498b5304317322c5a98218b59162d4c108dce530ea60846d72987530431cb24c1a9821479d35394c10a3ae9a9ca60854e72d4e53042a6b96a7298211bdc96494c108d8e4b24a60854e72d5253042a6b96a929821c61c15494c10a9ce42a4a60854d7215253042ad386c92982153dc96494c10a98e4b24a60851e7418a530428eba0c529821559c46294c10ab4e0314a60854e7298653042a6b94c329821479d06194c10a3ae830ca60854e7218653042a6b90c329821479d36354c10a3ae9b1aa60854e72d8d53042a6b96c6a98210f9d06254c1087ae8312a60843e74d815304237b92c0a98211b1c96054c108bcedaa2a60854e72d5153042a6b96a8a9821c61c25454c10e30e0aa2a60845e7615153042a7390a8a9821535c85454c10ab4e1b22a60854f7259153042a6392c8a9821551c56454c10ab0e0b22a60855870589530428f3a0c4a9821475d06254c10aace2312a60855a7018953042a7394c2a9821535ca6154c10a3ce830aa60851d7418553042a7390c2a9821535c86154c10a3ce8082a60851d74041530421ebb4a8298210fdd95414c10c3ca9318a60861d5498c530422fbb2a629821879915314c10c3ac8a98a60862e549885304316aa4c4298219354e6214c10c5ca8b10a60862d545885304326a9ac429821879926314c10c
  | 6 => 0x14431c2a4c198a218e15160cc510c5ea9314628862c5498a3144317aa2c518a218b151628c510c70a9b02628863854181314421fbb6a818a210f5db540c51087eec2a0628843d761503144317aa4c418a218b152620c510c5ea8b10628862c54588314431daa4c018a218e152600c510c70a930642886385458321442973a6cb90a214b5d365c8510acae3b2e428852f7459721442963a2cb90a2153dcd65c8510a98e6b2e428852e7494f2144296ba4a790a211bdd953c85108d8eca9e428852f7454f21442963a2a790a21ca15260c8510e50a8b06428863854d81214431c2a0c090a214b9d36548510a5ae9b2a428852f7459521442963a2ca90a2153dcd6548510a98e6b2a42885677159521442b3b8aa890a214b9d45448510e4ae22a2428852e7494d2144296ba4a690a21595c653485108deeca9a428846c7654d2144297ba2a690a214b1d15348510accebb0a428866465d852144393aa6c290a21c91536148510bc4e1b0a42887245490521442b23aa8290a21781c14148510e4ea918a4288724548c521442b23aa6290a21c9d513148510e48a898a4288747534c521442f03826290a21ca1536048510e50a8302428862f54988214431a2a4c3a02218edd26590110c74cbaa480886385458e404431d32e87202214e1d54390110c74caa1c808863854986404431d32c83202219a9972190110e50a990c808866a6548640443942a24320221e89052190110c6ea830a808853a75d91404423d3b0a8a02214e9d85450110c74ec2a2808863854d8d404426cb98c2a02214e1d54150110e50a990a808872854485404437030a42a0221e8505215011087ceb326608843c75593304421fbb6a9982210f5db54cc11087aec2a6608847a75d92304431cb20a9182218e994548c110c74ec2a4608863976152304438d398a918221c65cc548c110a74e929c608847b7654a304429c3a2a518221561cd528c110c70a930c608872854c8630443942a243182210f5d3654c11087ee8b2a608846f725953044236392ca982218bd53624c110c58a9b12608862f5418930443162a0c49822193d4c624c110c98a6312608863454d85304431a2a0c2982211e9d7644c1109e0e2b22608863865d5130442ad39ca8982218ed90544c110c72c82a2608863865151304431d3b0a898221c6153634c110e30a9a9a608853a7494d304423d3b0a698221c6d50534c110cd0cbb12608872854d893044334328c498221ca150624c1108f0eca9260885387454930442ac39aa498221cc153614c110972e830a60886385418530443982a0c298221b8d88614c110cb0cb98a608871854cc5304432c32a6298221c6151314c1109d4ed90a608866865c8530443942a642982213a1d9214c110cd0ca90a608872854485304437030a4298221f04c5214c110e36a8980608
  | 7 => 0x5884219a59562c4210a5ce5b1ea88852d72d8f544430fb1cc7aa2214e5c063d5110a5ce5b06a88852d72d83544421fbb2a82a2211bdc963151108d8e4b18a88853970d8c544429cb84c62a2214bdc96315110a58e4b18a88861d6318c5444297390c62a2214b5c86315110a6ae2318a8885397018c544429cb86c42a221479cc6215110a3ae6310a88853571188544429cb80c42a221479cf6015110a3ae7b00a88852e72d805444296b96c02a2210f9d262d4d1087ae9316a68846f725825344236392c129a218e9916094d1087cedaa2a68843e761515344317aa6c4a9a218b1536254d10c5ea8312a68862c541895344317b26c4a9a218b1936254d10c5ec8312a68862c641895344327b18c4a9a218d1936154d10c70c9b02a68866862d81534422fbb2a629a21531c95314d108dce5308a68846d729845344237390c229a211b5c86114d108dce5b2e868846d72d97434431c2a4c1a1a218e15160d0d10c76a9304868863854982434431c2a2c121a211b9ca6550d108dae532a868846f725954344236392caa1a211ddc56550d10a3ce7aa2868862f54d8943443162a6c4a1a218bd506250d10c58a831286884e5711894344237390ca21a211b5c86510d10a3ae62a0868863454984434423a3aac221a218e1526010d10c70a8b00868843e7498f524421eba4c7a92218d9916194910c74c8b04a48843e76d51524421f3b0a8a922187d536354910c38a9b1aa48861f5418d524430e2a0c6a922187d936354910c38c9b1aa48861f6418d524430e320c6a9221965c06354910c98c7b12a48863864d81524432c31ec0a92211bdd95214910a98e6a90a48845e73d97424422eb9ecba12218e15260d0910c70a8b06848847571d96424422fb9acaa1221171cd65509108bce6328848845d73194424431a2a4c2212211d1d56110910c68a8b08848863854980424431c2a2c0212210f9d365cc91087ae9b2e648843f74597324421e3a2cb992218e15260cc9108f0eab06648863854583324421f3a6cb192210f5d3658c91087ee8b2c648843c74596324421f3a6ca992210f5d3654c91087ee8b2a648843c74595324423db82ca992210f9d3650c91087ae9b28648847571d94324423cb86ca192210fdd1650c910878e8b28648843e74194324421eba0ca192211d9c4650c9108f4e0328648843e75990324421e3aac8192210fddb540c91087aedaa0648843f76150324421ebb0a8192218dd52610c910c68a9308648847475584324431baa2c2192218d151610c910caea6b086488667525843244332292c2192218ed52600c910c70a9300648847875580324431daa2c0192218e151600c910cb6a6b00648866b52580324431c2a4c1a0a218e15160d0510c5ea9314828862c5498a4144317aa2c520a218b1516290510c76a83028288638541814
  | 8 => 0x5620c7108daed290638862e6494831c4316b24a418e211bdd9520c710c5cc8a90638862d6454831c4335294c018e219a54a600c710cb4a6b0063886595358031c4335292c018e219a549600c7108daedaa6438846d76d4f21c4236bb0a790e214b9d053c8710a5ae829e43886695298221c42373b0a490e211b9db54487108dceda9a438846e7614d21c42973a0a690e214b5d05348710e8aa718a4388747534c521c4237bb2a410e219a94a6008710ccaa5b0a81886655218540c43952928020621ca54940103108f2edaa081884b976d5040c42d938ea8206214e5db5410310c72edaa0818853973d5040c4395396a820621ca5cb5410310e64e3aa081885997315040c42d9388a8206211e5db5310310a76e8a98818853a75d0c40c429d3aa8620621c654d4310310cd2cb290818872b5494840c4334b2aa420621cad515210310c76a8b08818872b54c8440c4395aa24220621b85852110310f4482908818861d6494f30c430eb22a7986218b99252cc310c5ac9296618862e6454b30c4316b22a5986219954a61cc310ccaa4b0e618846d75d8930c4236ba8c4986211b9da524c3108d8eca9261886665258720c4332a96c2906210fdd954152108dee4b18a90846c7258c548431d324c129c218e5926094e10acae2312a708666711895384332b88c4a9c219a9c06254e10cd2e0312a70845f7654c5384237396cba1c211b5cb65d0e108dee4b2a870846c725954384278b80c2a1c211b9c86510e108dae4328870843e7498f528421eba4c7a94211bdd95214a10ce2c3300a50845e73d97428422eb9ecba1421179cc6510a108bae6328850843e74d97328421eba6cb994210f9d2654ca1087ae932a650843e74d94328421eba6ca194210f9d0650ca1087ae8328650854d731483284333a92c21942199149610ca10cd6a4b00650851d7494f318428eba4a698c214b9d253c8610a5ae929e430846f7654f21842973a4a690c214b5d253486108d8eca9a4308746534c521843a2a9a6290c216c1c54390210b62e3aa2810847a76151408425d3b0a8a04214e9d85450210c74ec2a2810873171151408431c2a6c6a04218e15061502109b2e630a810872854c8540843942a242a0421b81852150210f468290a81086b161500408423dbaac9184218e590548c210a74e929c610845e7614d3084272b88c4984212e5d3654c210a74e9b2a61084f07159130842ad39ca8984218e590544c210ba2e3a9a610853a7494d308423d3b0a698421369d8534c210cd6ca31261085e171189308423d3b6a498421561cd524c210972e830a61084ea76c8530842743b24298421f04c5214c2108beeca9861086d1614c030842373b0a4904211bdd95208210ccacb31621086656558b108425dba2cb884214e1d165c4210c72c92a6210863b641531084334b2cc
  | 9 => 0x4e029a42104e4764c521083a329a6290841d154d314842087ce931ca01043d7498e50082b2b8865280415a5c032940208bce7b2c801045d73d964008316aa4c520041179cc65100208bae6328801043e74d96300821eba6cb180419354e628c02087ce8328601043d741943008272b88c7900419958551c80208daed29440104797694a20082b4ba86510041785c432880208dae3b2a401046d7598d20082373b2a29004199d8551480208f4eda9a40106656298754c4237b92c72a6211b1c9639531087eecaa0a98861d5458c54c429c3a2c1a9e211bdc96494f108d8e4b24a78845f7654c53c430eb22a629e21875926314f10c5cc9310a78862d6498853c4317322c429e218b5916214f10ccac5308a78863a6458053c431cb22c029e219a9896014f10cd2c4b00a78846e7299743c4236b94cba1e211b9ca6590f108dae532c878846e7219643c4236b90cb21e219694d6090f10cb2a6b04878846e7299543c4236b94caa1e211bdc96550f108d8e4b2a878846e7219543c4236b90caa1e211b5d76250f108daea31287884e57118943c4237394ca21e211b5ca6510f10a9ce62a4a58854d7315252c42973a0a7296214b5d05394b10ad2e1b24a5885667119252c42973a0c7296214b5d06394b10c9ac631ca5885667118e52c42b4b80c7296215a9c24394b10ad2e121ca58846f7650e52c42363b287296214b9d06194b10a5ae830ca58854e7318652c42a6b98c3296214b9d36094b10a5ae9b04a58843e7418d52c421eba0c6a96211b9db5454b108dcec2a2a58854e7315152c42a6b98a8a96211b9db5354b108dcec29aa58852e7414d52c4296ba0a6a962153dcd6454b10a98e6b22a58856b7059152c4297ba2c6a96214b1d16354b10ad6e0b1aa58852e7418d52c4296ba0c6a96219358c6354b10acce231aa5885697018d52c42b538486a96215a5c24354b108deeca1aa58846c7650d52c42b338886a9621595c44354b10a5ce930aa58852d7498552c42a739cc2a9621535ce6154b10a5ee8b02a58852c7458152c42a7b9ac0a9621531cd6054b108deeca90a5886726158052c4335294c12162117dcd6550b108b8e6b2a85886695218142c4333292c2216210f9d065ccb1087ae832e658843f7459532c421e3a2ca99621531cd524cb10cd2a4302658843e74d9432c421eba6ca196210f9d0650cb1087ae8328658862e6494832c4316b24a419621535ce520cb10c5cc8a90658862d6454832c4332a94c21962199949610cb10ccaa4b08658866a5298032c4334a94c0196219a949600cb10cd2a4b00658846d7694a41c4237bb2a520e21475d053cc7108daeb314638846f7558a31c4236bb4a518e211bdd9528c710970e8b04638845e7614d31c428eba0a698e2187592530c7108beeca98638861d6454c31c4236bacc418e211bdd
  | 10 => 0x76351486304821eba6ca982419314f624c120ab4e72a2609055a75d8d304829d3a4a698241569ce534c1208f4ec29a609055a7614d304832d3b0a698241565c4534c120cd0cbb12609074853d8930483a4298c498241561d7314c120ab0ea98a609066865c8530483a429e42982413a1d9214c120cd0ca90a60907485348530483b1a8a4298241f04c5214c120ccac3a8c409045e73185540822eb98c2aa0410fdd95415020c3aa8b18a810635545845408326392c62a0419358e6215020cacc7308a810655639845408333394c22a0419598d6115020caac6b08a810666625845408333392c22a0419658e6015020ce2c3300a81043e74185530821eba0c2a984117dd95314c20c3ac8a98a61065553584530830eb24c6298418b5926214c20c6cc9308a610635649845308333394c2298418d9916114c20c6ac8b08a610656635845308333312c229841999c96114c20c74c9300a61063964980530833930cc0298419c5866014c208ece232e861047571197430823b388cb218411d5c46590c208f2eb3048610659539824308237394caa18411d9c46550c208eae232a861046d7518943083172a0c4a18418b5506250c20c9ca6312861064d531894308237390ca218411d9c46510c208eae23288610639549824208236bb0a999041535cc54cc820acae22a6641047b75582320821f3a6ca190410f5d3650c820c3ac9298641061d6454c320832b29ac2190419554d610c820cb2a7300641062d659903208316b2ac8190411b5d8540c820a9ae62a064105657115032082a6bacc619041535d6530c8208deeca98641054f7654c3208327bb2a619041c3991530c820e1ac8a9864106656598432083a2a9cc2190419354d610c820ccacab0864106a6645843208352b22c219041d154d610c820ccceab0864106657558432083332a2c21904199151610c820ccea6b0864106c6535843208332a9ac219041b154d610c820c8aa6b0864106696598032083a4a9cc019041b8586600c8208deeab006410669655803208354b22c019041d254d600c820dc2c2b00641045e73191510822eb98c8a88410f9d0635442087ae831aa21056571cc951082b2b8864a88411ddd95114420c6ac8a88a210655635445108333312a3188410fdd1654c420878e8b2a621043e74195310821eba0ca988419354c624c420ce2a2302621043e74d94310821eba6ca18841595c754c8420a9ce62a6421054d7315321082b2b88a990841595c753c8420c98c6a9e421052e7414f2108296ba0a790841595c453c8420ad4e029e42107615198321083b0a8ac19084159dc55448420a9ce62a2421054d7315121082b3388a890841595c45448420acce329a42105657194d21082363b2a6908419318d5348420a5ce829a421052d7414d21082b3388a690841595c45348420ad
  | 11 => 0xc828f39ea92a441179cc61552208bae630aa91043f765505488317322c5a9c418e59260d4e20a3ce9a9ca71062f725925388316392c929c418e9926094e20c72c9304a71051e74d8d538821f3a0c2a9c410f5d06154e208beeca98a71051d7494f438831d2a4c121c418e5526090e208ece232887104757119443882973a6a7994419654c604ca20c5acab20651054d739503288236bb0a8194411b5db530ca20a5ce9a986510665655843288353322c219441a9591610ca20ccaeab0865106665458432883322a2c21944199d4d610ca20ccaa6b086510669659803288370b0cc019441aa991600ca20d52c8b0065106e2615803288370b0ac019441531cd6254620c9ec6192a310565710c951882b4b8064a8c411ddd9511462087ce9b2e631043d74d97318821f3a4cb98c410f5d265cc620a3ae929e63104e872583318828eba4a698c410f9d3650c62087ae9b2863104e97018f21882973a6a790c414b5d353c8620a5ce929e431052d7494f2188237bb2a790c41599c45448620acae22a243104e97018d21882973a6a690c414b5d35348620c98c7a9a431056571d4d21882973a4a690c414b5d25348620acce329a43105657194d21882b3388a690c41595c45348620acee6a8a4310565758c521882b2baa6290c41d194d3148620e8aa698a431076151d8121883b0a88c090c418b9516210220a74e929c61105e1710ca30882e439a4318441d8545218c220ab4e72a2611047a76151308829d3a4a6984411e9d8534c220cd6cbb1261104ea76cc930882753b06498441785c4324c2209d0ec90a61107615148530883e098a42984419394d620c2209cae231e411066561547208830faa2c72a241965c26395120c9cc6b14a89065a63582544821fbb2a82a241475ce64151208dee4b18a89061d64d4e534831d322c129a4117dd95314d20a3ae9318a69065b53582434832c29ac121a411bdc96550d208eee2b2a86904747159543482373aec4a1a418b1536250d20c98a7b12869047671194434823ab88ca21a411b1d56210d20c70a8b06849065853583324822f39cc9a8a41175ce64d452087ce931ea29043d7498f514823bbb2a228a410fdd1658c520878e8b2c629064c5358a314821f3a0ca18a410f5d0650c520c3ac9a98629061d6414c3148327a9ac418a4196d4d600c520cb0a6b00629054e7395321482a6b9ca990a414b9d253c8520a5ae929e429046f7654f21482a739ca890a41535ce5448520acae32a242905677155121482b238aa890a414b9d25348520a5ae929a42905667194d21482b2b8ca690a4159dc55348520acce229a42905657114d21482b2b9ea290a41599d63148520e8ea718a4290566754c521483b1a8ec090a41d8d446048520c3ac9a9e609061d6414f304823cbb4a918241569ce548c120a74e929c6090
  | 12 => 0x2a061995ca6115030cacc6b08a81866662584540c332b12c22a061999c96115030ccae4b08a81866962980540c338b0cc02a0618e9526090c30c72a9304861847b75580430c237bb2a4290618b5915214830ccaa4b08a41862d64948320c316b22a41906199949610c830ccaa4b08641866952980320c237390c8a88611b5c864544308eeeca88a21863564544510c332b12a228861475d253cc430a3ae929a621863564944310c332b14a2188618d591510c430ccac4a88621867151980310c2b2b8ecb908614b9d065c8430a5ae832e421856a70197210c2373b0a9908611b5d854c8430acce22a6421856571153210c2973a4a7908614b5d253c843087ee8b2a421843c74595210c21f3a0ca908610f5d06548430c98c6a92421856672945210c297ba2ca908614b1d16548430acee2b2a421852e74195210c296ba0ca908615a9c06548430acce3aa2421856571d51210c2373b0a8908611b5d85448430acce22a2421856571151210c326b28c6908614b9d25348430a5ae929a421856575d85210c2b33b4a290861999da5148430acceca8a421874763545210c3a231aa290861595d63148430aceea98a4218746534c5210c2b4baec090861d85476048430ad2ea30242186c863181210c3b0a88c090861875526390030a72e9280801853b75500400c3a2a8a4398061175da538c030ad2e42a4601857171152300c23cbb4a7180614e9d2538c030ec2a290c601864f65d89300c327b28c49806193d97214c030998ec90a601864f65485300c3a2a8a429806156dd5404c0308f4ec2a2601856972151300c2b8b88a8980614e9d2534c030b32e929a60185597590d300c38c2a28698061721c9434c030cd6cbb12601866b65189300c2ccba06498061d2548324c030ba2e2192601875151cc5300c335b2e42980613a1d9214c030cd6ca90a601876151485300c3e098a4298061999ca61d5320cccc4b0ea9906667258754c829b38ea92a6414d9c7645532087eecaa0a99045f7654c53c831b324c229e418d5926114f20ccce5308a7906366458453c831ab22c229e41999896114f20ccce4b08a79063a6458053c831cb22c029e419c9856014f20ce2c2b00a7904767199743c823ab8ccba1e418e95160d0f208ece232c87904757119643c823b38ccaa1e411d5c66550f20a38e6aa2879062e5418943c832ca9ac0196414d9d3519472087ce831aa39043d7418d51c823bbb2a228e410f9d2658c72087ae932c63906666254631c821f3a6ca18e410f5d3650c720acae3aa6439056571d4f21c82973a0a790e414b5d053c8720acae229e43907615198321c83b0a8ac190e41599c75448720acae3aa243905657195121c82373b6a690e41599c65348720acae329a439052e7414d21c8296ba0a690e41599c45348720acae229a439064e5318930
  | 13 => 0x514c530b8ae428a629846f76d48314c317326a418a618b593520c5308deec290629862e64148314c316b20a418a619ad4a600c530cd0a5300629866852983214c26c39ac190a619a14960c8530a5ce9b2e429852d74d97214c2b2b88cb90a61995c465c8530cd2e032e429846e76953214c236bb4a990a611bdd954c85308d8ecaa6429856771553214c2b238aa990a614b9d051c8530a5ae828e429864e65cc7214c32732a6390a619a19660c8530ad0eab06429866865583214c2e439ac190a610f9d0658853087ae832c429864e63d4a214c335a94c110a611b9d66548530acae332a429866571995214c297ba2ca90a614b1d16548530ad6e0b2a429866970195214c2373b4a890a611b5da54485308deecaa2429846c76551214c2b3b8aa890a61591c55448530acce22a2429856571151214c2973a0a290a614b5d05148530c98cb98a4298666658c5214c33232c6290a61715ce3148530c98ca98a4298666654c5214c33232a6290a61d1d953148530d8cca98a42986c4654c5214c3a232a6290a61d1d513148530e8aa898a42987c3704c5214c3e03826290a615a9d66048530cd0cb30242987c131981214c2b43aac090a619a1956048530b50e8b0242985c873581214c3e098ac090a610f9d0650853087ae8328429846e75988214c327318a410a619a14a6008530c9cc6296809864d6314b404c26d3acc7a0261969d663d01309b2e331e809866a65d4b404c36531ea5a02619a99452d0130d94c6296809847976147404c29cba0a3a026136ddb31d01309b6ec98e809856a75c87404c36531e43a02615a1d521d0130d94c690e80987c131487404c29a38aa9202610f9d85450130e56a4a00809872852500404c2ccb9ca8202611edd95410130ae0e2aa080984bb76550404c2cdb9aa8202616c1c55410130a76ecaa0809863b76550404c29db9aa820261c6dcd5410130e56e4aa0809872872550404c399b8aa8202614e1c55410130e60e2aa0809853071550404c29cbaa8620261361cd6210130e52a9a90809866a65148404c394aa0a4202618e5516110130a72e8288809871954cc4404c38caa26220261b45853110130ad4eb908809872954c84404c2b43aa4220261ca5512110130dc2c290880987c131484404c317326a5982618b59352cc130c5cc8296609862d6414b304c355326a598261aa99052cc130d34c998e60986d161cc7304c34d3226398261aa99321cc130ad0ea90e60986aa64487304c370b0a4398261f04c521cc130a98ea90c609859a74d42304c237394c3aa0611b5ca61d50308dce530ca81846d72986540c237390c2aa0611b5c8615503087eecaa0a81862d54588540c31aaa2c22a0611b5c66215030c9cc6b10a81846f71588540c237394c22a0611b5ca6115030cccc5308a81866562984540c333394c2
  | 14 => 0xe5b22a31847776544518c2b2b94a318c612e1d1608c630acae528a631843e74d97218c21eba6cb90c610f9d265c863087ae932e431852e74d97218c296ba6cb90c61595c765c8630a5ce932e431852d74997218c26cb80c690c614b9d26548630a5ae932a431856771595218c2b3b8aa890c61591c55448630acce22a2431856571151218c327328c690c61725c06348630d90c730243185a874581218c2e439ac090c61879516310230a76ecaa0811863b76550408c29c38aa8204618e55161102308f2ed288811872954c84408c394aa24220461b85852110230c3acb326611861d65593308c31cb2cc9984618e59564cc230d54c990e61186aa64487308c370b0a43984611b9ca61d51308dae530ea89864d6398a544c236b8cc52a2611bdc562951308dce530ca89846d72986544c335312c12a2611b5c762551308dae2312a89866762d85544c332316c2aa26199dcb6155130cc8e5b0aa89846e72185544c236b90c2aa26199d886155130cc8c430aa89865573185544c333390c2aa261995c86155130ce0c3b02a89843f76550544c29a38aa82a2611b9ca61151308dae5308a89863854583434c2b3b8aa9a9261591c554d4930b54e9b06a49854d73d93524c2b4b86c9a92614b9d363d4930a5ae9b1ea49856a7090f524c237bb287a92614b9d061d4930a5ae830ea49854d73187524c2b4b80c3a92614b9d360d4930a5ae9b06a49846f76548524c236bb4a8292611bdd95414930acee2aa0a49856471550524c2b4b86c829261535cc6414930acce2320a49856571190524c2b4b80c8292615a9c34314930ad2e1a18a49856a7090c524c237bb286292615a5c36114930a5ce8308a49852d74184524c2a6b98c2292615a5c06114930a5ce9b00a49852d74d80524c2b338ec029261595c76014930cd6c2b00a49866961580524c334294c1192619ad48604c930c5cc9a90649862d64d48324c2e4382641926199d4a610c930ccea4b0864986c532584324c335a94c0192611b9ca64d45308dae5326a29846f72593514c236392c9a8a61595c762d4530acae2316a29846e76d49514c317b26a4a8a618b19352545308dcec292a29862f64149514c316320a4a8a618b9935214530c5ac9a90a29856571d48514c317320a428a618b5905214530acae2290a29847776544514c29a3a2a228a618d1c56414530c76e0b20a29863870590514c317324c428a618b5926214530c5cc8b10a29862d64588514c31d322c028a618e5916014530cd4c4b00a29866962580514c2aa38aa998a619399452cc530a3ae828e629859a74d83314c2ad3a8c198a611b9d6628c5308d8eab14629846d76d4a314c236bb0a518a61595c4528c530acae428c62984b874582314c2b2b88a498a61595c8514c530cd0a5b02629866852181314c2e2b88a498a61475d0
  | 15 => 0x2e7298654cc296b94c32a6614edc16195330a3ce630ca99852e7218654cc296b90c32a6614e5c06195330a5ce5b04a99852d72d8254cc237390c2aa6611b5c86155330a38e6b12a99851e7398554cc297394c2aa6614b5ca6155330a76e0b0aa99851e7318554cc297390c2aa6614b5c86155330a72e030aa99852f7258154cc296392c0aa6614ddc56055330a68e2b02a99843f7655054cc31d2a4c121e618e9516090f3087aed2a0a59843f7655052cc237bb2a4296618d9526114b30c6aa9308a5986365458452cc31aaa2c229661995496114b30c74a9306659863a5458332cc21ebacc8196610fdd5640cb3087aed2a0659843f7655032cc386aa264196618d952610cb30c6aa930865986365458432cc31aaa2c21966199949610cb30ccaa4b0865986c53258432cc31d2a4c0196618e552600cb30c74a8b0065986395458032cc334a92c0196618b9526294730c5aa9314a39862e5458a51cc316aa2c528e610f5da541473087eecaa0a39862e5498851cc316aa4c428e618b9516214730c5aa8b10a3984777654451cc332b12a228e618e95260cc730c74a8b0663987155454731cc3172a4c518e618b552628c730c5ca8b14639862d5458a31cc38aaa6c298e610f5d6640c73087eeab20639843d7695031cc21fbb2a818e618b952620c730c5aa9310639862e5458831cc316aa2c418e619958a510c730ccac4a88639863a5498031cc31caa4c018e618e951600c730c72a8b0063986715158031cc21f3a4cb90e610f5d265c8730acae3b2e439852e7499721cc296ba4cb90e614b9d065c8730a5ae832e439870d54cc721cc386aa26390e610f9d2658873087ae932c439861d5498e21cc30eaa2c710e61c5551318873087ce832a439843d7419521cc2b3394a290e61c55513148730c74a9b02439863a5418121cc2973a4ca90e614b5d26548730acee2b2a439852e7419521cc296ba0ca90e61599c75448730acae3aa2439856575d8521cc3932a6c290e61c95536148730e4ca928a43987255494521cc2b33b4a290e61999da5148730e4ca8a8a43987255454521cc2b33b2a290e61c35533148730e4ca918a4398725548c521cc386aa26290e61d19453148730e4ca898a4398725544c521cc2e3baa6290e61d1dd53148730e8eca98a4398744654c521cc3a3aa26290e61e19513148730e8aa898a4398785544c521cc382aa26290e61ca9536048730ec2a3b0243987c131d8121cc3952a0c090e61d85446048730f8262302439843e7499421cc21eba4ca10e61875526308730c3aa8b18439861e5458f40cc30eaa6c6a06614b9cb54952308dce530ca91846d72986548c237390c2aa4611b5c8615523087eecaa0a91846e72984548c236b94c22a4614b9d35294a308deeca90a51866a62982518c334b14c128c611b9cb64546308da
  | 16 => 0x2b33b2a29088159dcd5148440aceeb18a4220565758c521102b3baa6290881595d53148440e8ca698a4220745534c521103b0a8ec0908819a5946048440b52e8302422076151181211023cbb4a9200819c9855190040ec2a290c80204d973185401033830aa2a00819ad972150040cd6ca90a80206e06148540103b0a8a42a00818e5d76550040972e7b2a80204ba71d95401031d3b6caa00814e5c76550040974e3b1a80205397598d401029dbaac6a00816adc96350040b50e4b1a80205b37158d40102d838ac6a00812e9db5350040974ed29a802069b6394d401025d3b2a6a0081a6d8d5350040b56e4a9a80205a87254d401025d3b0a6a0081c654c5350040b54e429a80205a97214d40102d9388a6a00816c5c45350040a72eb31280205b27198940102d8b8cc4a00814edd56250040974eda9280204ba7614940102cd398a4a0081665cc5250040e52a429280205b27114940102d8b88a4a00812e9db3250040972ed992802053b754c9401029c3aa64a00812e9d83250040972ec192802053a750c9401029cba864a00816c9c43250040b62e219280205397598540102d5394c2a00816a5ca6150040a76eab0a802059a7318540102ccb98c2a00816a9c86150040b52e430a802063975185401034d398c2a00812e5cc6150040d32e630a8020499731854010355390c2a0081aa5c86150040974eda8a80204b87694540102d5394a2a00816a5ca5150040d60c328a80204b876545401035830aa2a00814e9d95150040a70eca8a802063876545401031db1aa2a0081ccd855150040c70c2a8a802073061545401025d3b0a2a0081669cc5150040b32e628a80205aa7214540102d4b90a2a00812e9db3150040972ed98a80206b061cc5401025c3b462a00814e9d63150040a72eb18a80205aa728c540102d4b9462a0081cc5463150040976ec98a80204b8764c54010398a8a62a00812e9d83150040972ec18a802053a750c5401029cba862a00816a9c83150040b52e418a80206b0610c5401025d3b642a00812e5db2150040d54ed90a80206a976c854010355b2e42a0081cad972150040d56c790a80206a861c854010394a8e42a00814e9d62150040a72eb10a80205a972885401035830c42a0081cc5462150040976ec90a80204b876485401035830a42a0081cc5452150040d56ec90a80206a8764854010355b2a42a0081cad952150040d56c690a80207a37148540103d1b0a42a0081aa1852150040f40c290a80206a06148540103d128a42a0081ca5452150040f42a290a80207215148540103d118a42a0081e84c52150040a74ea10a80205397508540102d539042a00811b9ca61d53308dae530ea99846e7298654cc236b94c32a6614b9c86395330a5ae431ca9985367118e54cc29ab88c72a6614e5c36295330a3ce6314a9985
  | 17 => 0xc81595c765c8640a9ce732e432054d739972190317b2ac990c81539ce6548640a9ae732a43205677159521902b338ca690c81595c65348640e8ca698a4320745534c52190338b0ca3a04811d9c662d4d408eae3316a6a046e729875350236b94c3a9a8117dd95314d408dce5308a6a046d729845350333a92c3292811bdd952149408eee2b2e64a047471597325025d3a6c0992811d9c4650c9408eae232864a054d731483250333a92c21928199149610c940970e8b0064a066b525803250237b92c7a8a811b1c963d4540ccac5a8ca2a047776544515032731cc428a819358e6214540c9cc6b10a2a064d635885150237b92cb98a811b1c965cc540aaae628e62a046e721963150236b90cb18a812e1d1608c5408dce432862a046d721943150332b16a218a8199588510c540970e8b0062a06735158031502b2b88cb90a81539cc51c8540a9ae628e42a045e73196215022eb98cb10a81555cc5188540970e8b0442a05557314521502b3390a290a81595c66548540a9ee6b2a42a054c7359521502b3388a690a81595c45348540accebb0a42a056476d4521502b2b9ea290a81539cc5148540a9ae628a42a05c57314521502b33b0a290a81999d85148540e8ce628a42a05657314521503a2b98a290a81515cc5148540acceb18a42a0564758c521502b33aa6290a81591d531485408bce632842a045d73194215025c3a2c010a81475cc5190140c6ac228c80a0724514864050237394c3298811b5ca6194c409cae2312a62046d71d89531023b388c4a98811d5c46254c40acae2312a620666711895310236b88c4a9881995c46254c408cae2312a62066a701895310334b80c4a98811b9c86154c408dae430aa62045f7654c5310326a9ac4298819554d6114c408ece231aa4204757118d5210237bb2a4290819358d5214840ccaa4b08a42054c7254f321025cba4c1990811d9c4654c8408eae232a642047671d94321023ab8eca190812e5d2600c8408dce431aa22046d7218d511023bbb2a2288819558d5114440ccac4a88a22046f725973110236392cb988812e5d260cc4408dce5b2c622046d72d9631102b2b94a3188819958a518c440ccac4a8c622046f725953110236392ca988811b9c8654c4408dae432a622056572945311025cba0c0988819654c604c4408dce5b28622046d72d94311025cba4c0188812e5d260c8440acae3b2e422054e7319721102a6b98cb908811bdd953c84408d8eca9e42205a974983211022fb9aca90881171cd65484408bce632a422045d7319521102b3394a2908812e5d06048440cd2a4302422054f7359521102a639aca9088159dc56548440a9ce632a422054d7319521102b338ca690881595c653484408deeca9a422046c7654d21102b2baec290881599da5148440ccced28a422056573945211
  | 18 => 0x34c521b8ae1a9a6290ce67694d31486e339ca698a43d1d4e534c521cc8caa9a6290de37054d31486f0382a698a43399d8534c521bc4e029a6290de17014d31486e33b0a698a43b19d8534c521b8cea29a6290f467514d31487e1380a698a43715c0534c521f82e029a6290dc17014d31486d3ba2c098a43691d1604c521dc2c03026290e66759843148672bb6a218a4393997310c52199eec9886290e4e654c4314876330a6218a4339dd9310c521cd4cb3006290eaa649803148771a8cc018a43b88c6600c521dc2633006290e6a655803148755322c018a43aa591600c521dc6a2b006290ecb31580314877118ac018a43b24c5600c521dc262b006290cae7498e5048656ba4c7282435a5c053941219caed18ca090ec6634c65048762b1a6328243a3d936354121d18c9b1aa090ec771d8d5048747b20c6a8243a31906354121d8ae231aa090ec97018d5048753b26c2a8243a91936154121d8ec7b0aa090ec463d855048753b26a2a8243a91935154121d8ec7a8aa090ec463d4550486733b462a8243a9d923154121d48c918aa090ec7638c5504876231c62a8243a9d913154121d48c898aa090ec7634c5504876231a62a8243aa1935054121d90c7a82a090e4c639415048726b18a628243591d53114121d8cc6988a090ec5634c45048637bb2a028243531cd50141219d6eca80a090da87454050486e439aa02824317dd95314c21cb2a6b00a610e6672984530871d324c0298439a98a6014c21ce4c3300a610e3a64580530871cb22c0298439698d6014c21cd4c4b00a610e72615805308726b18c7290431ddd5618c821ccca4b0c6410d4d7394832086a7baa64190439554e610c821ccca4b086410e5a53580320872ca9ac0190439394e628c4218deeab146210c6d7694a3108726a9cc4188431bdd5620c4218daed2906210e5a53580310872ca9ac0188435a9c053c8421ad2e029e4210c6d7694a210863abb4a5108431b9db53484218dcec29a4210d667114d21086b5380a6908435a5c05348421acaeb18a4210f45538c5210863b3b6a690843599cb5348421acae72924210d67758c921087a2a9c649084359dd5324842187ce931ca010c3d7498e500863dbb2a0280438e5915014021cb2c6a80a010d4e72d4e5390237394c329c811b5ca6194e408dce430aa72046d72185539022fbb2a629c81539cf5294a408deeca90a52047671d94329023ab8eca1948187592530ca40c3ac8a98652062d649483290316b22a4194819594d610ca40caaa6b086520666525843290332a92c2194819654e600ca40cd2a5300652046e72d8d5190236b96c6a8c811ddd951146408dce532e632046d72997319030eb24a798c811b9cb658c6408dae5b2c63204b8745823190237396ca18c811b5cb650c6408bce732e432045d739972190316b24a59
  | 19 => 0xc29a6310e4d53588318872d29ac018c439654d600c621ad4e029e4310d697014f218861f3a4c7284430f5d263942218f6eca80a110e3964540508872cb1aa0284430fdd160d4d21878e8b06a690e3b64d81534871db20c0a9a438e1906054d21cb6c6302a690e6b62181534862fbb2a629a43561c15314d21ccac4b08a690e3a649805348734b14c029a439c5866014d21c74c8b00a690e39645805348734b12c029a439c5856014d21cd6e4b00a690e687258053486b4382a799243399d661cc921ccceb30e6490d667518632486a73aec699243539ce534c9218dcec29a6490d4e7614d32487273b0a699243d15c4534c921e94e029a6490f497014d3248726298c0992431bdd9530c921ad0e0a986490e66655843248755324c019243b8986600c921dc2c33006490eaa645803248754b22c019243b8985600c921dc2c2b006490e687558032486acb80a798a439314d62cc521ccccab146290d667518a31486b23aa6518a43d114d328c521bc4e01946290de1700ca31486acb80a698a431d9d8534c521ba2e029a6290ce676cc9314873232c6498a43591d5324c521cc8ca9926290ce6760c931486f13806498a43785c0324c521d8ac71964290de2700cb21486f0b806590a433a9c063885219d2e031c4290ec5638c6214863dbb2a0282434e1d15014121ab0e6a80a090e4d630c85048672b8cc1a9a432bdd160d4d21958e8b06a690ce7715835348763a9ac329a43b1d4f6154d21d56c9b02a690ee361d815348755b20c0a9a43aa1906054d21dc6c2302a690ecb531815348735298c0a9a43715c65314d218deeca98a690d687054c5348667bb2a629a4371dc55314d21b90e0a98a690d4f7654c5348727bb2a629a4353dc55314d21e8ee2a98a690f4b7054c53486a6382a629a43d21c15314d21a90e0a98a690f45535845348755324c029a43d254e6014d21dc2c3300a690eaa645805348754b22c029a43d254d6014d21dc2c2b00a690d6b7054f51486b4382a7a8a439358c53d4521ad4e029ea290d697014f51486f1380c7a8a43785c063d4521d8ac7a9ea290de37054f51486f0382a7a8a43b158c53d4521bc4e029ea290de17014f51486d33a6c1a8a43695d360d4521dc6c1306a290cea701973148674b80cb98a43725c053cc5218d8eab066290e4e65cc63148657ba2c118a432b1d1608c521ccccba9c6290e666554e31486f1b82a718a43781c1538c521e8aa629c6290de27014e31486f0b80a718a43599d7608c521b4ee8b046290da47458231486b33a8c118a43699d0608c521b4ae83046290ee1601823148673b8aca98a4393594534c521b92e029a6290ce676d4531486a73ac6298a43715ce654c521d8ae732a6290e667519531486b33aec698a43719d7634c521e8cebb1a6290dc570d8d314873232ea698a43d11975
  | 20 => 0x964192500c63cbb065280634e9d03294031a72e8194a018d72710ca500c6b8b8865280634e9d06194031a72e830ca018d6a72186500c6b4b90c3280635a9ca3194031ad2e518ca018d6a72d51500c6b4b96a8a80631e9db5254031a74e9a92a018d3974d49500c7952a4a4a8063ca5525254031e54a8a92a018f2954549500c63d3b0a4a80634e9d05254031a72e8292a018f1a54cc5500c78caa662a8063d294b3154031e92a598aa018f31548c5500c7b0a9462a806356dd53154031e34a898aa018f19544c5500c7a529262a8063d25493154031ae6ea98aa018f31544c5500c7b0a9262a80635c1c56454031c72c8322a018d3a7498d500c69cba4c6a8063561cd62540318f4ec192a018d3a740c9500c69cba064a8063d24c83254031ae4e2192a018d71710c9500c6b5394c2a80635a5ca6154031ad4e518aa018d69728c5500c7a9b8a62a80634e5d03154031ad4e418aa018d69720c5500c61ebb4a8280630fdd95414031c5ca9310a018e2d54988500c7172a2c4280638b55162140318daed290a018e2e64948500c716b24a4280631bdd95214031c5cc8a90a018e2d64548500c71d2a4c0280638e5526014031cd4a5300a018e6952980500c63dbb2a0280638e9915014031c72c8a80a018e6a62540500c734b12a0280630f9d36054f2187ae9b02a790c5f7654c53c8733312c229e438e9926014f21ce2c3300a790e3a6458053c871cb22c029e439c5856014f21cd0e4b00a790c6e7614d32c872aa9ac2196431bdd9530cb21a9eeca986590e4f7654c32c87a2a9cc21964399595610cb21e8aa6b086590e696598032c8755324c019643d254e600cb21dc2c33006590e696558032c8755322c019643aa591600cb21e92a6b006590ee16158032c8735baac0196439354c624c721a74e9a84a190c3e7498e50c861eba4c7286435a5c032943218f6eca80a190dc571d4e53c86e2b8ea6a9e432b9d36054f2195ae9b02a790c6f7654c53c8667bb2a629e4353dd95314f21c9eeca98a790e4d5358453c87a2a9ac229e43b194d6114f21ccaa6b08a790ec55358453c8722a9ac229e43aa9926014f21e92a7300a790ee16198053c8755322c029e43aa5916014f21e92a6b00a790ee16158053c8637baac198e432bdd1608c721958e8b046390ccf764c431c8673bb26218e439a596600c721d54c93006390e696558031c8755322c018e43aa591600c721d9662b006390ec93158031c8753322c3a8643a959161d432195ce931ca190cad7498e50c86b2b88a7286435a5c05394321b54e9a84a190daa74d4150c8726b18a6286431bdd950143219d6eca80a190c5f7654c538872ca9ac029c439958a6114e21c74c9300a710e6962980538871d322c029c438e5916014e21cb4c6b00a710e6962580538872729ac518c4399595628c6218ece
  | 21 => 0xa9dba2c3280654e1d16194032a74e830ca01953974186500caad398c3280655a9c8619403287ce830aa01943d74185500cab938ea8a80655c5c75454032e54a8312a01972954189500cb8caa664a8065ca5523254032ab6ea992a019719544c9500cab5baa64a8065ca55132540328f4eda8aa01953a74d45500ca9cba6a2a8065cc9525154032e62a928aa01976272945500cbb0314a2a8065cc9515154032e62a8a8aa01976272545500cbb0312a2a8065d4cc95154032ec464a8aa01975132545500cbb0992a2a80651e9d85154032a74e828aa01953974145500caad39cc8a80655a9ca6454032ad0e4b22a01963964191500ca9d3a4c6a80654e5d26354032a72e8192a019572710c9500cab8b8864a80655a9ca6154032a76e8b0aa01953874585500caac39ac2a80655a1c96154032a74e830aa01953974185500caad398c2a80655a9c8615403287aed2a0a01943f76550500cb1b2a4c2280658d5526114032c6ca8b08a01963554584500ca3abb4a2280658d9925114032c6ac9288a01947776544500cb1b322a2280658d5915114032c74a9300a01963954980500cb3928cc0280659c54660140328f6eca80a01963a64540500cb1cb22a0280659c9855014032ce2c2a80a01946f7654852cc732a92c2196634e9d350943318f6eca80a198d6a70186528c6b4b80c3294634b9d36094a31a5ae9b04a518d6671d82528c6b3388c1294635adc16354a31ad0e0b1aa518d6a70985528c6b4b84c2a94634bdd16054a31a58e8b02a518d4f73581528c637bb2a42946399949618ca31ccaa5b0a6518e6552584328c762992c2194639a54a600ca31cd2a4b006518e4d6594b318c726b2aa598c639959652cc631ccacaa966318e2f64949508c716324a4a84638bd915254231c58c8a92a118e1f64cc5508c636bb4a4284638b9925214231c5ac9290a118c6f76548508c717322a4284638b59152142318f6eca80a118d3874540508c71cb22a0284631bdd95214931ad0e0a90a498c9f74582314c63dbb2a0282634e1d15014131ad0e4a80a098d6a70d4a520c6b4b86a5290635a9c06394831ad2e031ca418d4c73581520c637bb2a4290639a54a6014831cd2a4b00a418e6552587320c732a94c21906399949610c8318f2eb3006418e6a52980320c734a94c0190631edd5600c831cd4a4b006418e6952580320c62ebb4a7188631d5da538c431c9ecb2926218e4f65549310c733b2ca49886399d95524c431e8ec6a926218e2e6494b500c716b24a5a80638b99152d4031c5ac8a96a018d3a74d42500c69cba6a1280635a9cb5094031ad2e5a84a018d6a72d52500c6b4b96a9280634e9d35294031a72e9a94a018f2a5494a500c7952a2a5280634e9d05294031a72e8294a018f61528c6500c6adbaa63280635cdd53194031ec2a498ca018e3
  | 22 => 0x3006003c01a0030000034000002005800c000002002000400a006001000801a000000001800e00500000080000080060028002015000801000c000000000800e00c008800000000000100100220070058010002012003805c004013002800000200c00080b000000d000001002400001300040000080008088054000000800000800d002804800400d000001800400600f800800200600080000060000008008078009000000403601f00381c80100020020010006004001003800001a00600280000000038018006001000004000000800200380060010028078004011000802000c022000803c00401e0048008002007001000400001f005001801800c00c000401200f006800002c017000802c01600101a8008000002005800c000011027000000000a004000801c0110008008076005010802400e000000803c004002003800c016020000800c01e003008800802801d01900000240150338000000002000002003a0070020068004002007801401e00b00000000000020018000004006000002400e000000003c0000020018004008001000001c002002001004800e0000000000002017002802000000e004006400400d001008c00600a0040000006005000000401600b008002802000000000000150fdd16094732878e8b04a3995687058951cca3bbb2a228e654e9d3509433287ce830aa19943d7418550cca3dbb2a028665595c732546328eeeca88a31947b76540508cab2b8e65a8a650f9d260d453287ae9306a29947776544514cb1cb26a1282651edd9501413287ee8b08a09943c74584504ca2ebb4a7190651b5da538c8328dae3b2a641957270d46510cab8b86a3288650fdd16094432878e8b04a219557754ca510cab3baa65288655c9c06394432ae2e031ca21956672d82510ca9bba2c1288654d1d16094432a6ce8304a21953574182510caab398c128865599c86094432acae3192a21946f764c9510cab3b8a64a88650f9d0605443287ae8302a219557754c9510cab3baa64a8865d15ce6254432acce1312a219566708c9510cab3bb264a8865d1dcd3254432ac8e0992a21956672d81510ca9bba2c0a88654d1d16054432aa8e6b02a21956472581510ca9b3a0c0a88654d5d06054432aace6302a21956672181510ca3bbb2a2288659c5466014432ce2a2b00a21963664947500cb1ab24a3a80658d99151d4032c6ac8a8ea01953a74d42500ca9cba6a1280655c9c75094032ae2e3a84a01943f74586500ca1e3a2c3280655c9c75494032ae2e3aa4a01955b754ca500cab5baa65280654e9d35194032a72e9a8ca01973254946500cbb1394a328065cc9515194032ec4e4a8ca01976062546500cbb1192a328065d84c95194032a74e828ca01953974146500caad39ec9280655a9cb6494032c72c8324a01956a72986500c
  | 23 => 0x380000300058000000023003800000000a026007800c004002000c02c0000068008038000004017802e005008000000000300e00040060060030004004001000800009801b0000058004005003000000201a002001400000200c0000046020000001400c003002801001c02400000100000010000000000008008804c03001c001004c014000000800c00e0150028004000008008800c02400000200d400200901d000800e01e000000000000100600240000010120014004000000000002c01b018000c0000030010008000016002803001600f00d80b805600700280bc00400300200040120000020010000002000000002c00c004800400c03d00280340b0006002000c000001000800c0040040100008074000004801c002009002008001600f000001803e00000000700080020000004004002001001400a0000030000000007000003400000c0140000002000008001400001200f801400e00300200000020040000024004001001800401600000080ac06000300d000c00001401e806400e0060000004004003010005c0000090008010000000000800005800400a801400a005001000000c00100a005c04e00a001000803a01d00200080020050070000002001002000400c00300400040a20020050020002008001014002a00c017000c044000004800000e006000000000000400d0010004001000000002e013014800000401c00d001c02200200a804000a00200000100080060068000000002000803000e016006003c040001002800c02200f003000c002000000000004805700b800000c0030008038022006006801c002006007001000403f000002804800400000100000070078000002009001005c008019001009401e003009001403600300081ac0060010018000004006001804402c002000801000000200380a401800500b000c000000026000c00000300080900020000000000002012000800401200800280e000800e0008000012001000804404c00400000140000070048004000003000000c038001000001400a005016800c00c00100d000802400a0010024010001006800000a00d003805000400200580ac006001001002402c00400880280020010028000008004001800c000013001001000c002007000803200000380000000060008000004000012801c000004000003000e00300100000260010010000006051000002002401000680080120030018000000019004000002c000003800001000800280cc00000f014000005002500400000100010000000008002004800c000003000801404c0020018010008007000003000000f000800c01c001011001c00200e00000280040020000000010002005801801600400400040040100140004024017002000c09e003000001000401a004000801e000004002000200
  | 24 => 0x7e00003e80005c400000013840000000002449ca4e2500010bc0003c22329e1897cded2a927d8d24a58649462637e00004ea30f11e5720b87a618fc78a0e91c340000000cfec00b7f36041b1c2400089e12a958d2c60dde6e34608ccb676209a78dcf0002d706c118b0005e9800000062215c80000000000000c6400036e08a7920702000000000000000000029399a7bdd000000000017f57c8aad8030f4662000104a8d24950a10df4c91000150d9411be001402a001000000402a04200c003403e0090188028030003005800c012000001001000e004000003000400000300080020000000004002056007800000000400000780020060258030050000002800802e00000080400000090000064004009001806002a00100200480220010040004006027001800c000038003003001c002001002c012003000002403200100580040060000100000006001003805003203c0028004000004000003000000601e8000004000000800400400c0040000014000003802c016014000004000c006000800800a000005807401c000001000003200001180000020010058030000017001002000e01f00f803c0080250008014000000002800000000b00e80080080000020004002005002804004200700000580000000000008000017006000c00000b01a806400e00501800bc00200900000500320020098010026000001800000e0000060008014002008802400000403f800c01c0000038020004004004800003e00b001005c010000004001803c000000800400001200000a000a024002800000e00f00000d000202901c000400c038005800000c00100180140020050008010014005000801800c00700380300020010038018066001006001801000500300140000000030018028024002801401a000001000c00000500100000020000038020000012003000000001300600100000000000068072006005800000a00e002800801200f005800000e0010000180006000004800c006041001000c002001000801c02200200c004000200400f000001800400e00f80480150000004002003000001400e016002000c002007001803c00a0020028010010003007801402e000001804401c003002801000001300a00280080000020000010009002000000c00100000000020010010008020002001002c0060010000060000002001003400000f001800400c000000800c00400000000240220130018000008002000003800004d006009000a008001800000e01a00000140000090000088012002000001401200200c000000e001016801401c003000800401401e00200000000020008040030004027001000c001007809001a00000000c0000000013803402800200c004c000008000808c006009001000800e00c001001c000001000000000400000080
  | 25 => 0x943988e96bb75891a15910c95ec1469800031d00025c400016b0001fe50ed00059d0000de800036ad6a2be400000016e0bb40004858000000c095c200014d2cae0000001c5c0002faafebb06eb332e80006c40000002c5050f1c0582ceaa5420006f1676c00000073326988e0b7222a33980008d41153775b48eaa63584e349eca6a1a1e08440cc06ca083bcc61903371f3824483872a1bc8000dbfd08000055c75f0002e740000001e24af80000000b93649a4012700015a40000003efadb40007d374c8d5400000061f28cc6be0001f3703b0c05b20001280cecd56b9a06898a6e4c0cea77d4da55f72a8568b2a7e71278c68968227e1fc0008c9cd01f000014f8b6a00019b5d16e2065218547d2ad10620c614524e36b338f8000614000280c8ae5756dd6898eac3f717c800000013850336fd26acc24271b6163c2604a04000f98e9e51d00002cad1a0ab80016a83d85af8545b048cb3118184000c11319383000044a95e021196dc9f00014316580002aba21574a5e87269a046c29ea98520359b3ca66f7b15bb50a6a3638eec000b751e58a6904e38b27bb68976a43968b789b47c9d24b22265c75bbd5f30001d6e6dcf18ebb0000859102c00028046a0000e6b57e5d431f94d9516cb45fd20c0a26d593c9ab355a0c4d00033b025c28064dd4c16407fa21204c8225cb35d737f3615d21b2caa6c65432267a1b30a765b930e0038caa568f05927ceae8db6f29b058bedb16ad91e8448104619b6ab682cb5c03a90bce4e351ef80017a28fbcc8261c000dd3da6b37eff057e1648001c805f70001ccd5200000000548eaa6c6800306d0c2db2bf08ec7a1055361fb26b36eb2d6f88d8c65679f39e354eb905cf44f87a809b1f82952e3a8a2dec65b0000a8ade3404530e9c406745ee26c26a60a62a8904176d2c84ad2dd066182453089cdded6f3df270841e83d6cd09cd1240e00b6b17b5ca708dd7966d79c00012214e94aae100000000000e5b74e00005ca3100001b8c0000001070000000c4a29f0a7d93289446510c0ad6d2b34580019939ac56f0768b380006d3c000000000210adf8f120006b1ddd8a24d5d620c0014a04bf49f947543c1d7205ab0000069a6f82b601d281a5c6a5f52428fb0058f2509638c3b7996173600061013ca00000019facbc00000024f07317b85647374001c916350000b08f4c4146e9790ad7cc9a12d83b970017b10139dcceab9946040017abceb3d416f939680a000026ee5c0006b0a160914de09243978720b7c1aa05e40000ce00033d5166ae741407655ac0ac40e58c536607b00030b40005875a22d7b414b1a0c383bd07433e58885dc0f2b8c5c70cc1adc3cf8000e50000d70cd814140007613e589653c820120e1a2492e1c300009eaf5e566eaa59500001a333c9068ac02d6689ccd0f02cb200022fcf
  | 26 => 0x543b77f9492d743f000000000046f800111600000024e4000ccf3dd837236250a00037c80003d774215e572000035ac23723871415d24f194e0004bd0001be857f08eb25016bea29e2c0010febe40000a1c0000002ac822f6bc77724459f08a0a3f200b44c000a5a000202cf58d8918424012e40003db80000008f137ab550aaa32b80008117303278000000bac22b000163129448c0000000558b864862ecd84c799107f27b25818a325b8f75fa4e7258263c1a0d1c6a400006b0b068a519909bc5320000001cf285d029b1fae37c5d63a18e9392047441a6c275a6d607512660000003e41fdc3c983e7211dc1d1057b6b432bd967866306126c0003886e91c7a7ba4d040cb91b7f629d597044d29e82ac6eb6d319c0002ef2b699ec0002434d994ca00000000019ac1ca00000004ea17000008c568048b5638659d1a00013f2b64ece40964b27281256600cfb0d1b943052a4000124884d45e47050ca00036780006da3b8265a914edf88d6482e1557a1b96da162c47200011724d048e0a128f0000b78715227a4b4fc4cd3402173075cc2162c4298e9a00965e000153c010654a5516e00000c61481154833b35a0a55be000522000000000000003d400000000026458ea0001cd0000000000718118cc0ebef47e22c81c284164ce2a50927795b797042b686d04b08e178a83c0000c6d2de59f6dc76f344600050a00000000190001ff800000000000000002da6cc5c84dc2daf702a5ac1ca6f940a101cf460222c0322a59683f988a3412bcd95c0f407898eb0b8f23070000c0134daa4c4da9e61d08787a1bccb74b01c85e4cda0000000df07ab325216bca50005ebc3a15a66f0595a9fc836854a29973938a0003da00000c420c6d5367a61e2360171c1dac534c33fb7213ee00057b81e816201d1ffc140a660013819f6411000000023dd51a95354880000000006a3991c5b25ff1b6c001a4807000012be1f874e2cb8efc69407e3f2314598bc125d92754ab014735c211400081f00000b5754a9d6da96e942a0007558000a202de000000191c0164e7b2cbb070000ee200d20400a737e605274947753977069600014d8ba14d899218ba0c47304f15108015af23abe5c09a8b58db7d90abd0b349a021431244ec01f651b5800a8e394339fb8b9696904c2f0c78e1445511dba700d94a2f98d11de7ec069b1ec7a87633963660b3ce566e09ef000000002fa5ec0007d71ceb65418633c00001c4bbe029648cb9c6f8e49229080c1f50660cd040c68a3fc374c370f7014f61284adc148ad0118f30190bc73f185b8fd6d0d49c12448e60cf0bf36c021a00069bc000bca17c4a0377c3fa760e2789c940a3f7d8c399400026417e9b2556e0000000ea14b28a468816c0ec42ef2ca045d90c00003780011e027b27ec7b512a6a22720001a5c0003
  | 27 => 0xcd6aef83e8d452ed8cd46bae06000005c000000699e5e11d0da55b6520040cc67c1913eca7ae0465886f0c12aca19db6dc4ac59950dae28ba00253e31d1929c9f847fa96d7a0b7109e5470d06c28739b3500403a70512da127ac073dab65828494c70a9064239aad207b38cdfeb27662ad4cca2d3b1e99848251711750b11f860c818580b0035689142a0d188ac01b4e99fa907ec9486037cca0602607fd08085480c3e889e9bd6d4660fafd9cdbd213c21ad455e038394ab999f6045085b3c14ce44c62068909460555f6a6f1bb65c004a15e0756e2f6460c2d89c98a4a3193f7c625368eae7d2fc0c6132aaa02baa7b2568f157b22bb1af19406e2d26b3a31e447ae5a00000011fc7f553f02fd5f87404f417297724fd74e72000003e7800145d54c9999148be03dc42d2b083c98b27605ae10b959870c6912bc972cda30001a500001015f421c80008714c29d21c1b0005a89498f5a0004b2aa00f74000000000024c0bd62343c07740979f23849c6c997376c0016a44134f5b33000045c2613905aac772284a0e41fa0001c9b18c00062c64088b0000000721a739ca0a66000121dc0482154180008e20000003a0414e8c40001fc5cf0904008b70b9563644f1ab518af686e449b4c00000000000d490c68c1e3397dd1e4e0021a1033ae61e4cfa8881e6000423b768000c404c40000754e0ef560ec023c6c235406793d28ace34ade8664707e098000c1a0005b080350c400069aa8f41a83b7044a156658000000327f56a25d6b19c41b74bd836db28e624a610000ac58e7056d690272642497e2c20dd9a248f6932f844848f51069e49702c373100984a0200011401d100cdfc1fc3838d72df84cd000179a90700029dc16e16900024a521c2e94ca0215cd7086e74876cc8ce4b48bb7030543d14fe000189129904caddc2773b93ae8001844a0f5fe8001b4e6de0001a9910e7a5290a71c00000353c2b6c688a380e780018bf4425632c5475e00000004c55c8cdf5de0e3dbc0a7610923e911c00000016383b000015a8b480000006a99b28ab81490e6930c0544fe9868031c650002f884bc2c47ef00000000008c1b66b032c9a9113410d0d9892ad62239a188c91d2c98ea5c62eb5057a1a534ed0b8d22c9e5fc1333dcebe01d654006ea7d195d11a6942769bec120375a7e885229409d578800edb2246ba48aebd7064e0a9c9da35019025211623ed5409900442a8e34835839aadf749da44c76aba80bc1cb42eace0a5492390c76053f001cc00000000000018f4ad56649a7400064345728d0df8000211bac942433d17b2d2cb0621107634b0faa0f664c2d5d4e43de40a846558496172ace9104641137ba41961e17161eafa52b49754912eecc784f90b38914258dd340b110dabc8bd48c8871a46bcc00001098d5d335759345cdc68e0e9924e
  | 28 => 0x6a476a58507d4d6272500032a990102b35e0000000d8192ba0783cc8e16ce681d9c01631521d4cf80af10c40000000e678000000b4e54b60c078d04c00000000011609b5902b3fd8b6e261d9ac7c00000001e000000000073506bc0000000000001858000124aaa4000d74000062c5520d133d9b9d0358356000000000d85192023ed644358000001c380001721b141466063c6a0b80009be655ce8c000e320000000e6204d4e403ddd0a5e70000000f6000059980004e000066e8000066ca10223a86fd000027f062572800010f36264dc2db0000dddaa07f459d90d57f2e534de822c172cb95be81747e884339e838cfb4441b3e8b7d958166d8202d45981ef00039719ee1c26819d5043a7af9ee0e24a98495c67a834b4015e6cdd6d029a6422c10b513368571bf88c03687e504a74e032e0e736b94912a40874d4448d044e6cf4a23900008242a494580009fd00000000006570431c08cf3b7900038ff4988895881d3daf4c8a6ce000027a183bfe1c8c0007f02620eb2000a6f68786e821900000000000006bb00014b5c116e90ae10e7b02dee2ba76d99d028542d05a0d740573236f6c3a85ec70d183d142c7c18e36e68fc95633f61d606843614980c00008630000000bf2a940003888e5689758123b9d463820000001ace4f2442199800005b1688000000000521800179e00040c7ad8e260004fd800000000073e80008905d146cb81d030ac526c38ef848cef5e0b6edc3c06330bb4fc8dacd84396145180cbf6709d14820e9f426159994bd4d71e8231c126701bb0c92bb278c74e8d585a0b2a19d1894bd46532911a18b7e4162be99e8c5cd423a517a548edacd88d008758cad1f1b685aaa55aafe151cc022cd43a51d0d7a71b644dc7879c67e50b2ead50485b5f1366d82e62a5e20f94f84e0811d34058c50b2175a0dbb78de70eea47c5b5e46347a2dd09e0a8216ece5c358770ff00f4ab41f919c966000074c25500008d60006b5378774e907c4400003113f000024592100e40000000000db823e00013483be24d120555828f0000001a6e53930f9afe530d2507139b0a3e116d81aec035f4d36812ff183c8c855789e1d5ee7b00000012bac61027c00000092600015500004e619c18dc0000006668cc54640e600039d40001ce03bc483636d39550aae8e7420aad9b80cb9aaae180345455011b19559b04d200000028b9c4f95f64a85bc82a0edd74aa9c7d049ea579885076e2a758af00d3881b2c79c5c2fa09c0093189a9689c10c2a614a68bb6faac1c94c3ee1ce424dbb0449c6d21d8e40dabe83a8218161ec25e069c00065a5010cdd1fa00000300600b00000001afc332256a508ed16105ed571a0bc5663f109528bd2b278331eb741a2509165e9ce0cbc5c34fca7100425e480d1add2125c91c9109d48c4dc207c85dbd4b10
  | 29 => 0xd06067841631aa4cf37443f656c60a0e5205778f1a72e204f2c3a53a8a2c990d4169f33641fcb60000127424232833bf49d0e6dfb8ef0df956c4126738e800005443b287cc3960006444e6f64a6cb7161a9000000012a3448ade672672b028f0ad0e1a38458e5be6f5d600011a260b0000100a36dab00000004b847f15117d818e7b93601110296c56170336e520ce2040899800081fd582dac00000029a367edc0325651361b1aa00010d300b20675a70babfc000ce6bdb153979668473826e1a9d71f00021c006e4f4585b0d99360000001984a6e61a1e9368e6d60004748ca3affda610982b44a2eb6c072e98a0eead5ba249caa5afa2b102353da610466836c684013269190452e62b531161893204b2ec24b96bbb562a3381f0f256d53987d8da4115000332364c00044c0000dd86e20002d55bfe000409b9b591a00071c2b11b8a5882fd94a1a2e70b4ab8514e0857024e08b4000e2d579820f68acc39ed00017709d80000000000c4bc2f060d0c9a4043d31b4c3ac5e0000168000a48518b568000b5b00004f006c766d60ba2a148dad2d19a45a156c5bd99118000000727cd042b916162380000005e05eb0000000000637ad31426cf859ab79ed4e70a0a1a5fd6b2d00105a30b652c619b839fd36c7c5cd9077ba8008a224b1698b35383b682e924a2222830c31b0c4f35fb88292500e9dbb1d0cee2c4569d3570da08c3504a55bbf42b2175234c0ea61839db4da72ae60570a0d1bb2a9521f057c0003e61ae1c1513a1024ceaec5a9f2e639f1e8918a24345a8f11a98aea5b301459ae5195f833d37d4d8d6bf56a18cca540135a0735cc031ff26a0000cce393910134a000000389167111c04d9f70a4666225ccde9c31b0535835fc7646d40e426881e2e6289b800140287b7143407c02d34000000134664900005617d85110aa1eb98e041ccb834f16843b12db078825346148f2c3a0009c60f391a5c228905a196ddc8a0006e21e500003d038c9fb4ec8357467f91cf008ed3e38e95a524792513a80e84b6ac1691d4f826380000000ad4bc60609e7173c81c13105e8400a1c2063a6950cde940800003f400022a8001bad00006f032870ee7a095d7f42a64040000930fcc4884ef35c595010c226b7e59a5bff33bb072000b92000000000000000000012660000000c4d8e4cf97529d7ed5600031c88bd8fe8402e3b0102a5ce3c35b8d00006f32870000972e95688b1487385a6000082f17ccb1e3e93fc9b486e14490f1babe5742aa76638abf9f51091849445a0b50001afc0002e98268000c48000285d4f245b0001f344322bf2e3088c0000000922becee84cd4f10960e2c8f64752ae5bc87183a901dc08c81d97d22e037a2153eb1cd5a7a2f460303e92569d03ef027976c86831395d110080567aee4cc042880692e8ca5ca496d4c71
  | 30 => 0x2800000024a98ec5eab2870a33e79da40373e00006d041bc1466100001955b20a954825bd6b29615d049ba170aed18763830662505a882aa60846320000000000e6c7c294d0000000b7b36f000000131800009540000000002d236ce04800000039c4fb06ce000056eb42ccfcee0000d4200018100000005f8024203c0002a60c7945519800013bb04090a0006770000b2400011992b00005766e68a29ce181100037f52b66480e3099d6d29ec6edc0002ec4ef18480000000000000887b2000000012414dc1e17338000000d7c8002979baa9420000000000d760002e1cef6000532193d9a4848000179800023767bc0000000001718db19742dc47a27b8ce2e8704f9c040000006bd80007dea0400000000a43db00014c400000012d725d664494621e588bc257a2521dfbd06558de48dc93e02324ce0414e24a8f22e9f487e4b234ea24352a06682dab628dd4314301b773aea14843a9ec963810046eda1eccaa001ffa1e032634823918a15ea2d3455812913d5713912a5c166dcc3271374e6e773047a73064ce7e4e0957ecbed14334b46d9fcb3473274d792d34d59ba32436e2964299354906514285921131a7396ee3a0154037935180009ae0006820000c320f86e10000fe60000000000a1a850000387dcec697cb039a60dc36a68cdfcaed09d9499043d11400031690e000090a62a25b1ca9262eb9af5d748ea9049357c00079812f80013168e200030b969003b00000018278083641629372a3516209480008af08539640d62c6096a204000a6b359a0240002a317f94f1a644ba25c0ad830023b0480bb00000004e00504100bbf5ad367400055100001b0000b4f0000000b08d722c6800007223cb3986380000a94410000d073ea0000cb91403cd0d4b81a064059000251132cb6300037500006e409f0b153fe00026480000000005a706ccba40bf80000004fe00000015a188500017bb075144db9000124c0000006ef00018a04c51ad99ea63c2910000a1890472438d03c772a031647809d60c3d94f9035da4f00000028614840004d5ac05b526dc0001d600000000000171d122cf6eb9558e3a06d621959dbc20002b70850bfce3f32b2f7c0ec19b10800000d000066340015d00005d68001aa5000678832c000976000000049c0003e82d899ff46c00031a808243b1e00000000a840000001a0c0d5218f23bc7426360b17c144e40d3879e9001052b13589f12dc66f735800000047d74df84c8826440000a04000bd415a1f5026f1860002a640008bc0000001b58a3723565449d443a0000000f940000001b640000000b5c530d5468a317800096c6676d2c000000a8500006b56fe695000287dd2240816731810020001b48000a30e3c34cb8ec924bca0c090c5158b0e00002da0000003149de0f16e5828d1ca8a843656cbb108ed859
  | 31 => 0x494730001a60d696428159b1e68d0001624000bc26e380006eaca50000001d5c85f000369b9d447c80016440d219c103838fb63dbb85b0001a19000679b31830a63024480008ce62446324503d0ae2138854163200005c322cab996a22729c5b7ab476c4000009eb732d96d404369a139787a435852927a9bd87610e780011dc000000161889359c00016e800001ecfebac80011d600062b9e7847e43b9128df4cb600048080000000000000000000c3813e9bedd48d99800339e000d6f991a30497a00000025e5aa400000025cd2d0ac94524001c9332e9a880009b60002e287dd46c00011a2868dd04591de09409b26ddd6b80000000000000000000000000309c0c83f580005180009954ae11b847c70600034c4f1cc732b29cd931c6112dda48cf091d5436378874cc713d895f0d587dd4988001a6c000754244126e0000000a308c00006a480000008b93e182946529775520ebf230000377e9c00005eb3b4847d54aaf60c21914187e448840000dda00033b4000b620002c080005905c275c0c5479e38a58b0d000000000000000000b9a0003430e4c00000035baa008a74cc83608c7a89055adec0000820002e4571692f3eda8c14a238d4f9af699868de3f926bc2a365c0941ea52cc01503c0f059b9800186ce58a8281d0b01ef5cbadc05f3b7ed1e490f6c3cf0c09238614f3664d6812533c0c1d1507510c8b4281ac1c93c801f015c77f361b194e7ecfc47475898c85c400023b11ca0aa3baba4c000c4581fa9d19e3596589805036a36ee6dba987ea8443b874aa79084222c074190e79a61521f19f1a0e68b28eda9c9582f78fe4f71c0242b0adc5aa3016997397c884c61bc06946ce13b2e359a977435a03fa67b6127471609a589f0aa3658312dc00333668c0f8b52731d1280009f40000001260c7c4b14902e0c7334b5267af95a5328e260ad74121bf526f9cc96f0b463003a28506d091fd96a87ece4e1cf9f1000000016c00000980003e780002cf0000000fe8000b65000221895c6da08c0001990ba132928b080c0001789dad8d80c49db0000a940004a2a415b1c0d946b00011ce000000266000000070b00000000002ae8001878be000035f4000e18000276b4180001413035cf73596179a4cbe85af2f1abb9c9ed8700002f04dd3ef888953d66255e2650001940ba2e339b54cc69d1000041d7bc4627148001b0047d99693b086e7961378000d3ee2b0002935d600006e0f4795de81769504e8a58aed3cbab20000b3c23b303835ca5f06fafc80008ba0021d7986acf20f819317dc8d730b231fcf9750605c555a9edd653424d92364cc4ba2a48c26a886d983e4964c9c9a9aff912c89fc32386651abd54dda294e8216652b8ebaec36a50b22b805f862609b394488e5022529e1d534000515327470ad7dcf28fcaef4b8247cb5
  | 32 => 0xacf30d8000edccc70000000f691eb15eaaa993c00054b00011c0000449925800000000000000004eb14e00000001bb52c64698dc9cd28200000000002160e793fcc921c88000d05dcf451b02a000a7d00000019081c74c49015300e19000020c140d8a9258c0dd2098244604400c00002b98000ffe44566f5b45177a52598107c0003737069d110fad2f6c580707d86af6a8e971790d586e1889956898bf02e1d084408e0000c395ba00018218d84803a263bba2f3e29c363b30e4bba2b023790ace9268060c9d700000000769820a5ea11586305400002c21e4000272000000000104005e6a19ad80007f6707ae891f0c0f9f133f2896da0d7f1b99c66527000361019253508333e85da1f20001b94000a3c71393940002f35912af009c1ff59c2e5c9509d673a1c70dba6f137f38dd094c8259f115260c22ce24c7592aa0006b23798000000000025cd5ab6c0000650000eb460780008d032736327d52ce45e59200007e600065a87a3b9c0005d4800018a38e00000008f6000014364f4727953983379091c1a00020b00000b40000000000beb65b80000004780dc1ea8000d516ff3465906000165264c2d823c53028b592f6a900022e6f3aaf004a80000006c406d10980000000003a1863e00021e80007d626800015417e821a8000000000235000367971e00000000013c010e417f67c3ca5ab10ec000ef85d5614900029cdae2928cbd4f4e2121faa28b5a3362f98001004abe2dae7a98184182f7000000039746380e9c4654d55c00006e80004a5a2d930ca636343171cc86872c4f9965e0c315f871e09562ee7308745c949a9479b8fb53e4a734b9c20e00b1d0ef80093ba6333443681cd2852096f874732cfd3d3a3b2cffbf7b4c097949631670d86a155698310f8e1171234949f2864c1c2b868fb647c9b60435715dcbc85fa16383ed67ed770d913c04b418d3feb5e15b8c055b728a14566a05ce2c5cab640e14ab2f89a88c8df8e0af8641122602ac5b2675b4d5330420527400012d71348460001e205f60005101e81926b36287a6fc0003bd6e33724000bf880035b536a7662c83a1eefa110d251e44000abb00013b8000d6c52b079e8c8e8e5e90859846e971f3b130b4453f3e2afc49d08dc6c46360000000559105cf420000000db2b4a0003f480002280ff52e80001c14fc72051298564f669682f9cc786a37745597f00c248a8f282e8dbe0848f5483a469a12a6c4e1c8c259e800054086f0c93020f27a1d647f7a169497c00035ac0004b3559b55c83c13f2192d60ff66c39eb06850b81304b6b72da2b26c5868dec9d20b2ba1f65e4101b63cdab0db224d6505b4153de0000000d3c0000fcda487f08661344a1844681406a1fe8a48efc0656c613382521730f01b7d9c86ee2eba79d9940000003a6daf81a000012ed5969
  | 33 => 0x5460001168c7dc9820484126fd5d026d00007c972540bdd180cd0f8b2ec2b20004158935a168e35f99420000a9c0cc0
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd3148430c497518c6048430e40635446048430c4476545214c030b0982151434c030b1181151434c030d0974548324c030d41525c4324c030c6076545214c030a4583951610ca20a2684d4d610ca20c47635c43254620c0e7418f5348620b058494d3148620c487614d214c120b418114d214c120a45811c96315020e066454d610c820e056454d610c820a4583151610c820e4153586600c820e096454d600c820e4153585600c820c447654d3148420a0c8458c6354b10a4583949610cb10d21729c75410310b2281d51521031092987d53211031092a87d512110310e23545852110310c61719c06254e10a4583149610ca10b058494d31486108b1861c54390210c18545cc6150210e20541852150210ac1831852150210a3081590544c210c63655c4624c210865811c96315110925811c96315110c0d635c86315110c15635c46315110c24545c46250d10d20549c36148510d20541c14148510d20541c13148510e22659052190110ac1831852150110b2085505215011083987150614c110e2054d88614c110c2a76153214c110c2876151214c110aa184185214c110e2054185214c110cc0764c5214c110f00544c5214c110a308158c6055010a19831846055010c187454d608c410b05831c55448410d20711c154484109458754c4148410d21545c04148410d41535c041484109a0845c23148410d21545c23148410d41535c23148410b2185d0521d0010e2165d0521d0010f0153d0521d0010b10815d15310010931851c5431001083b855da4110010c197654e41100109198754c4110010e21545852110010e41535852110010b21851052110010f01531052110010c25545c4624c010c45535c4624c010e046454d2144010c18645cf544401083a869d95444010839871935344010a18865525344010a18869515344010a18865515344010a1a849915344010a28865525244010e086454e5244010a28865515244010e086454d5244010ca0645ca5144010c29751932144010a28865532144010e086454f2144010a30865522144010e106454e2144010c2b751912144010a28865512144010e086454d2144010a30865512144010e106454d2144010aa2849912144010e21851912144010ca3751912144010e23751912144010e2064d512144010b4183d512144010aa0869512144010b21859512144010a60865512144010aa0865512144010e23865512144010b22865512144010b20865512144010e20865512144010a20865512144010b2184d4d2144010e2064d4d2144010b418594d2144010e806494d2144010f015494d2144010e206454d2144010e436554d2144010e806454d2144010f025454d2144010f015454d2144010f036454d2144010e426454d2144010e406454d2144010f006454d2144010e006454d2144010
  | 1 => 0x80c00000301416110002c0002a30815906454031e4153586600cb21e096454d600cb21e4153585600cb21e41535866014f21e096454d6014f21e41535856014f21d09745c0534c921d41715c0534c921d0b741c15314d21d08741c15314d21a478654d6114d21b408054d6114d219488754e6014d21b088454e6014d219488754d6014d21b088454d6014d21e096454d6014d21e41535856014d21aa284d8260d4521b408054c538c521aa084580608c521ca174580608c521987845c3634c521987845c3534c521c60651c1534c521d82745c0534c521d81745c0534c521aa084580604c521a858498d3194121cc1715c06354121c447558d3114121a4583949610c821a4583149610c940b05831452190140c61719c06254c40c61715c06254c40a48835946048440d21745446048440a51831855150040ac18318521500409a1811c95350040d09535c85350040d11535c45350040d09735485250040d21525c452500408b0815db3250040931811d53250040c19759cc6150040c19755cc6150040c29759c86150040c89739c86150040c29755c86150040c89735c86150040899831da5150040a91831865150040ca1721865150040a91831855150040a19831855150040b11831855150040b21821855150040a91831873150040838865d63150040d21725463150040c31751843150040ca1721843150040a89831872150040e20615472150040c31751862150040a91831862150040a91831852150040c30765452150040aa286dc52150040a89831852150040b81831852150040aa2871852150040ca2871852150040e21851852150040e82831852150040aa1831852150040e81831852150040a81831852150040aa0869452150040aa0865452150040b22865452150040b20865452150040e20865452150040e23765452150040e20765452150040e23635452150040aa0868c52150040b21858c52150040aa0864c52150040e05544c9610cb30b05841953148730a0e849946348630b20815512110230e21545852110230c45735c86155130ac0804c9610c930c25645c45214530a6181148604c530a618119660c8530a44865513148530d42754c66048530c28651d16048530c48651cd6048530d40754c56048530e40654c56048530d80744c56048530c487598d21d0130ac18198d21d0130d23721c55410130d20721c55410130c31861c55410130d11831c55410130d22821c55410130d21821c554101308d1811cd6210130b20815535210130b20815505210130b10815533110130e1154585311013092b875532110130b20815532110130928875512110130b20815512110130e21545852110130f01544c52110130c287599121cc130c607558521cc130d40754c521cc130e82644c521cc130a0c845946348430b058494
  | 2 => 0x10c0340033800000c40005f20c001c40000000000cc04908c0600424b1000920007c3f0741f4ca35042800a33faf22f82539c1f15c00000a900000000000000032c001046f0006816c579e8bf000da200ea038090002c358ec000070000002c00001068006a1ac163aa42000003b8ba0000030894434318008726c003e00000000000320008b298440e8000000000000000000008c0646114c15860d3000ad000210000600050000e41c8f580000000fd0540000000000080004b4163d0008f000760001dc18000d8bc00000000ff1480000000000000000000097000000000c208002f4002dc00000003ec000004ac2c00070db35c00000cd0010abd800000430e4000a4ed18cd5394f03789e26826178a242ef9164b92cc63800eb05c840000129cd0126cf0007e0fc00000eb87441800773041431c00000c912000001028d4000008611ce000000000000000028107000c608c962d8ab361043b2551d44e068fa8004cad0a53d04d9e0000000000000374af00000000000c4001a4f5000ac436e92ec95000e82c00019aa40ea0000000000988000019000000000010e27e510100000016962ef3200000013000220008d1fc4f0e08111900968000001e00000000ae000a8000000a0d9000330005400000040650000003ce2000001886e000930ac888de700a8000004040c3719c88404d22843b0bc490283e228112c8f138c053dcaa40079314e6ba63c30c850b5024140021e000b8fcc2090344e61ccdc2e0fe00c000d0000c020300910008909c003e89f09098158f493060134021709d1eca3800450001b4285800000000003cc66000000009c0006d1b0b51280037c8e2645d000000000000000000e10180000000080210030100001060040e04010080200010040000050000e04000000601080000005000040402000080803000007402008140c000000000000880002030000406010e01816000181012000000402020080c000002004220800000180714004
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xd00000080000000001000000180000e7a0013000b9e3280b110000000000104b006c2402440e000026a00000c000123cd02140000000307150a4ce9f00120008000040840010160221d6454d6014d21a204baa6b0ac029a436009454d615805348710306b90c328a802058064c615472150040c08bab0630c42a0081a0185a0c61485401034030ac18c290a80204a064c8694521500409104b30b18a42a0081c00651d131581214c3080eac0cc690e8098604619831c55410130c10c330438aa8202619018360871550404c28412eaa2c2908809854025d544c52110130e003acc898a43982618407660453485304828452faa2c29088188680151831852150210910cc0a830a4298221c00761513148530442a0326388e0aa24208640211535c23148410980cc2a620a4220021a006460f54485100424452d432a890a200848866064d4d2144010b004b2a929a4288021600969515348510042c012caa2a690a2008580a526454d2144010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 29
  | 6 => 1134
  | 5 => 6283
  | 4 => 3769
  | 3 => 271
  | 2 => 33
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
  | 5 => packedAt gbK5 (274944+((h/2585+packedAt gbK5 (238754+(h % 2585)*14) 14) % 11260)*14) 14
  | 4 => packedAt gbK4 (203375+((h/1438+packedAt gbK4 (184681+(h % 1438)*13) 13) % 5180)*13) 13
  | 3 => packedAt gbK3 (17187+((h/103+packedAt gbK3 (16260+(h % 103)*9) 9) % 497)*10) 10
  | 2 => packedAt gbK2 (2427+((h/12+packedAt gbK2 (2343+(h % 12)*7) 7) % 69)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3f87fe3c1f1f1fc7c71fc7e0e381c3fc73c64f
  | 1 => 0xc7f87fffe01ffff807e3f8fffc01fffc8c787f
  | 2 => 0x7ff803fffe01e3ff803ff00fffe03830f8f8c
  | 3 => 0xf800003fffffe03ffffc0000fffffc03f00ff0
  | 4 => 0xffffffc00000003fffffffff00000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10b21444c42a2c01c3054124a09450e831c645
  | 1 => 0x8101080802440008002088424408891004181a
  | 2 => 0xb2112c914a06505a4802d20a692c0a190e8a8c
  | 3 => 0x465122901004a49548001092513022d00560
  | 4 => 0x246460031c9899372693249c00602043eb6000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeecfc88feecfc88feecfc88feecfc88feecfc88feecfc88feecfc88feecfc88feecfc88feecfc88feecfc88feecfc88feecfc88feecfc88feecfc88feecfc88, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_36382
namespace PEqualNP.Outside.L_meta_36382
open PEqualNP.Outside.L_meta_36382.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 33 := (concat bgb_2_0 bgb_2_32)
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
theorem bgb_3_256 : Interval gbAtlas 3 256 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 271 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96)) (concat (concat bgb_3_128 bgb_3_160) (concat bgb_3_192 (concat bgb_3_224 bgb_3_256))))
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
theorem bgb_4_3744 : Interval gbAtlas 4 3744 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3769 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416)))) (concat (concat (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)) (concat (concat bgb_4_544 bgb_4_576) (concat bgb_4_608 bgb_4_640))) (concat (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768)) (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 bgb_4_896))))) (concat (concat (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat (concat bgb_4_1024 bgb_4_1056) (concat bgb_4_1088 bgb_4_1120))) (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 bgb_4_1376)))) (concat (concat (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472)) (concat (concat bgb_4_1504 bgb_4_1536) (concat bgb_4_1568 bgb_4_1600))) (concat (concat (concat bgb_4_1632 bgb_4_1664) (concat bgb_4_1696 bgb_4_1728)) (concat (concat bgb_4_1760 bgb_4_1792) (concat bgb_4_1824 bgb_4_1856)))))) (concat (concat (concat (concat (concat bgb_4_1888 (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 bgb_4_2080))) (concat (concat bgb_4_2112 (concat bgb_4_2144 bgb_4_2176)) (concat (concat bgb_4_2208 bgb_4_2240) (concat bgb_4_2272 bgb_4_2304)))) (concat (concat (concat bgb_4_2336 (concat bgb_4_2368 bgb_4_2400)) (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528))) (concat (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656)) (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784))))) (concat (concat (concat (concat bgb_4_2816 (concat bgb_4_2848 bgb_4_2880)) (concat (concat bgb_4_2912 bgb_4_2944) (concat bgb_4_2976 bgb_4_3008))) (concat (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136)) (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)))) (concat (concat (concat bgb_4_3296 (concat bgb_4_3328 bgb_4_3360)) (concat (concat bgb_4_3392 bgb_4_3424) (concat bgb_4_3456 bgb_4_3488))) (concat (concat (concat bgb_4_3520 bgb_4_3552) (concat bgb_4_3584 bgb_4_3616)) (concat (concat bgb_4_3648 bgb_4_3680) (concat bgb_4_3712 bgb_4_3744)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeaafeecfc88fefefeaafeecfc88fefefeaafeecfc88fefefeaafeecfc88fefefeaafeecfc88fefefeaafeecfc88fefefeaafeecfc88fefefeaafeecfc88
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124202 * 2 ^ 32 + 4276944008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36382.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[1,5]⟩,⟨.and,[0,3]⟩,⟨.or,[6,8]⟩,⟨.and,[3,6]⟩,⟨.and,[0,7]⟩,⟨.or,[10,11]⟩,⟨.or,[0,7]⟩,⟨.and,[9,13]⟩,⟨.and,[4,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276944008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276944008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36382

open PEqualNP.Outside.L_meta_36382 in
theorem PEqualNP.Outside.L_meta_36382 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276944008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276944008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
