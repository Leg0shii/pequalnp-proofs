import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36286.Model
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


end PEqualNP.Outside.L_meta_36286.Model

namespace PEqualNP.Outside.L_meta_36286
open PEqualNP.Outside.L_meta_36286.Model
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

def SBf (j : Nat) : Nat := [6, 6, 6, 5, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36286

namespace PEqualNP.Outside.L_meta_36286
open PEqualNP.Outside.L_meta_36286.Model
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
end PEqualNP.Outside.L_meta_36286
namespace PEqualNP.Outside.L_meta_36286
open PEqualNP.Outside.L_meta_36286.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x40c092002b2984051c00203bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x100c0008008ea98852c525065ca5205554430
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (208+((h/4+packedAt s1K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s1K3 (112+((h/1+packedAt s1K3 (108+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 2 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 3 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8040888500808002904c02240229109408d131
  | 2 => 0x10891048252442502a11214921422528a22486
  | 3 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36286
namespace PEqualNP.Outside.L_meta_36286
open PEqualNP.Outside.L_meta_36286.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2010829b0bf43bd43be42bc42ee32ed32
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x823aa6216350d32
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => packedAt s2K4 (102+((h/2+packedAt s2K4 (96+(h % 2)*3) 3) % 8)*4) 4
  | 3 => packedAt s2K3 (56+((h/1+packedAt s2K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3ffc0fff83ffc1ff07ff07fc3fc0ffd9c739f
  | 1 => 0xfc0fff03ffc1ffe0ff83ff83fc3ff03ee78ce7
  | 3 => 0xfffffffc0001ffff0003ffffffc0003f07ff07
  | 4 => 0xffffffffe0ffffffc0003ffffffc3f80ff8
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x58244628925044053424b424c06425a48c318b
  | 1 => 0x9648a19221284a054a154a1442960a8a584a5
  | 3 => 0x30c9145074a5296b0842694baa80c31302df06
  | 4 => 0xa28a208244202a528948084233128a03500a50
  | 5 => 0xc30c38e38739cf9cee738e7022230c23ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800eeeeee00eeee8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36286
namespace PEqualNP.Outside.L_meta_36286
open PEqualNP.Outside.L_meta_36286.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3ffc1ffe0ffff83fc1ff83fc3fc0fffece333f
  | 1 => 0xc0ffe07ff07c1fc3fe0ffc1fc3ff078173cdcc
  | 2 => 0xffffff80007ffffc000ffffffc0007ff83fe0f
  | 4 => 0xffffffff801ffffff0001ffffff801fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8244451094110808d092a124064254a4461115
  | 1 => 0x9648c32484a129415285a50c4296150c52c54c
  | 2 => 0xc910a0d294a12d421094a5aa80c2259816e0a
  | 4 => 0x28a21049080a54a6252042133128a011a80aa0
  | 5 => 0x30c39c71ce739f3bb9ce73822230c461ffb000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0eeeee0e0eeeea0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36286
namespace PEqualNP.Outside.L_meta_36286
open PEqualNP.Outside.L_meta_36286.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xa437c53487ee8290fd10521fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410df94421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fda0281be40502fca8205f94c40bea98817e52102faa4205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7185f94a30bea94617e518c3eca3185d94630bea8c61f5518c2eaa3185f94230ef98461fb308c2fea8985f95130beaa2617c544c2fea4985f14930ef99261dd324c2fea2985f14530fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f661907e0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220fd18441f930883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20bfa8a417c51483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa88417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e50843f481087e50210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fb98a21f431443ec42887d48510fd20221f940443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f741043e882085f94010fb88021fa10043ea20087e44010
  | 1 => 0x2008000000000040500100401c0180101a00c00df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543fba8a87775150ef8a2a1fd14543ba28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642fb28c85765190afaa3217d54642baa8c857e5090afaa1215fd4d42be29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9995f94732bea8e657e50ccafaa1995fd5232bf2a4657d548caf8a9195f54e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997bcc932ef192657f514cbeea2995dd4532be28a65f4514cae8a2995fd4132fda82657b504caf8a0997e14132bc282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cafca41977cc832f719065dd320cbda64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e837e52d06faa5a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41be29a837f52506f8a4a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077c8620ef10c41bf290837d521077e8420ef50841bf28883bf41107ec8220ef50441faa0883b541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21fb98e43f431c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea94437e51887ee8310fd10621fb18c43f531887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9
  | 2 => 0x3946321b0004842b003106360892512a60000000000038c510ba000134d70670000340017200000013800000748df8901783fc548000000005a95649e294b4000130038cb800000104000004166580009c00400000000000000002290004d4000000007540000000012d2b96228481c000000e2718a21373d6000001b700037c000003d01b4000753c040d17000000545228af3660000000011e2800000039610c9385c4445847386a0000001f2551d4000000cd0ba000000003a000000000000550fa000000114210000003742b8ed0102e0d8a3e3fc048000000600000000000000000105000000e995943458c189b90de8980020426c2c4841f334843883000000000001f121a00096a274985e0780622de0300000028e000248003be0a4570610008c0679761b88751ca1c2e00005ba49370000d3000000000000601264c056800000680000001b22641c101000324002080000004b94c156520e715f2520bc4f8682468300d24e302058b200000000000000150000000440000000000000000000000000000910000007a4000350000000023a0fa1e8f10e139068c0580023a00000000000000002400006bc000002dc00000000000890000000008552a0002087bca50fe0004f4d500000031c4d20d00000000000000398000403b644c7d8000007604200002894835916000000001930cc0010c8854863f000000000000960002f60000302b41e000710001ec000000d72fe660930002b00000002c2202ec290002707d4000000004f8c580016000032000000000000000001c01ba4735a000001ee0000000000000018c8d000420278d5800000000af25325c6880000000045cf1a3d000534001be000000fe8c80008283a1e7000648001c300000000149000000ba000000194ce8d52403505524a0006081509b1e84e4450004665d40000028280c50990000460409c0000778000000000000000000029c838001d04f000000000000001b200000028800000000000000401b8be0002547b0489430000000e00004c6210f02237663400000000140118000001c83b9e500a7c8f80000090020040000b0000000380800a0000080000600401804000028028000080180000d0020000000400e00401000004004018000000380080100403001800000004028010000300280101000c000020000000000000c0140000a0080240000501c0180000000a01400002000000000020080080080000401c000040000140000100000c000000020000000c00200000000000028000010000000000300400405004000024000050020040000000e000000040000080000000800000800000000038010100180480000a0000080000001401806000004038050020100280201400000801016008020000060040080300600001800000004008030020080080500
  | 3 => 0x39e000fb800000724da0004563c8c2a280000b87c9ed2fa8a81c8000302f42d8170685cc001f9158000d08001c8960000000a800059000000078ad1e10483f400000336000000000008b4001fb00000000214000654141462128d0fc23100000000000000708f5000296000e38000007908500000000000000264000bc80033e1f11f88e2ba6280023b074000000001d60000009600069400194274714e881d000000001771460641d8000006e8c4a3610e000cc80000000000000180000000000009085f0001040000005e02a75000000360000000003f836c5980100061cb30000004000021724a000d40000007588d8002d800000000128254000d635847c2a800308000001cd1e2935100ce0000010f800000000000ec2a4000000001b4000c78000008d47a81342434081086000618a0073020084700000000003b000000200b68bf490169028cc168224460d2098808000002aa000a78d3148000000c1000630000b6000000000000008e085800000514000000002e4fd21809e3787d1bc0d24506198348c000d4800000000db21601e000000000129049f9b5000000000ef00080108a0e000000088002ca000000000004ac252130000000003f09c1e4ce04647802862124000000002091a2804b583c0fe010eb9673b4328628c2116644d396000007ccd0004880000000000000000088000000000000005e800007394000198000d8000298004ac000000000009400011e2b8464c7133458120de89d4425c40010c0007d8000f30000000000014c000aba2546e00000000000000a70f800092c0002d0001e0000e90006780011c00000000115000000000000000002c00045e2341910f000000e22060fc0000013b0b209400000268000238000000000d8cb000248ff98006c3dca803d0003b8bf1d9250774ee1cc0be4c4e0a322d288c8896a0004bc3d9e62b6
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x553d02746154f409d98652d02756194b40ae58041902ba6090d40ae18142503364314540cd10c51503374214540cd508515037160145408f997415033451d0540cd145415033451901408f59641103355190440cd54441102b96010440cd547401037151900408fd9540102b46150040cd545401027b6550040dc545401027661d53309d58754cc2d8604cb309d987548c27561d52309d984548c2756115230cd952518c3355494630cd951518c33554546309bd89544c26c62551309dd85544c27461551308f990524c23d64149309d984524c2756114930d3149324c27761550309d185540c26e62150309b588540c27661150309d584540c23f64544308f191510c23e64940308f592500c25f654c0309ed95300c27661d53209d58754c823f6454f208f19153c82776154f209d18553c823e6414f208f59053c82766114f209d58453c827761552209d185548827661152209d584548823e64d4e208f593538827661d4e209d587538823f64546208f191518825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534827b6054d209e9963048278654c1209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c755153083586054c208f990530823d6414c209798c53082766114c209d584530827a6014c20cd95251083355494420d594e51083555394420cd95151083355454420d594d510835553544209e597300835953cc0209e5943008359530c020d654e200826f65480209ed95200835953480208fd9153c423c6454f108f99252c423d6494b10cd15141c425e63d52109758f548423e64d4e108f593538423e6414a108f590528425e6314a109758c52843375410610bc58041843b04190210bc18540843b341502108f992544427761551108f99454443356115110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d52442766590510cd15241442746550510cd151414427665cc510cd15331442f260cc510cd150314433454885109d19521443345448510bc18121443385490110ec90640442786550110ec505404433454841108f596540433461550108f990540427661150109e980540423e64d4c108f593530427661d4c108f990530423d6414c109b988530426d6214c108f993520423d64d48108f990520423d64148109798c520425d63148109d984520427565d0410cd55341042756510410cd55041042f16010410cd55310042796584010ce55210042776544010ad191100433554440109ed9510043395444010
  | 1 => 0x822205402000020500401c0201404000010500600c00008020040702005008070082301c0d014000000101c01018000400203c0000800000050001a0200400c0101c080040b01c0200c000500105c0c01c0504c0100c0100818034010180e000000100002007034040080100404004000081f00c06004170040300035000020000b0000004c0700010000010000813400000060000200802000040000000014018020240207c039d98652d0e756194b439d9865090e756194243cd90c5150e3f6550c43ad1854310e5f6550c43ad18543d0b364394642cd10e5190b3742946428f9974350ab46150d42ad9864250a7661141429d5845050a776154c429d1855310a3d6590c428fd954210a6f65508429dd8554cca7461553328fd9151cca3c64547328f99250cca3d64943329d98650cca7561943329d987548ca7561d52328f992544ca7661951329d586544ca7a60951329e582544ca7761551329d185544ca7b60551329e181544ca3e6515132cdd53514cb3454d4532cdd50514cb345414532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb7051141329d987540ca7561d50329e983540ca7960d50328f596540ca3e64150329d984540ca7561150329e980540ca79601503297d95320ca6f654c832cd952510cb355494432cd951510cb355454432ce952500cb395494032dc946500cb715194032ce951500cb395454032dc945500cb715154032d6cc9500cb593254032ad58443106b561d0841ad592411063f65504419dd9541106b76550441cdd9541106b46350441add8941106b46050441ec50650107354154041ec505501073a4354041ce10d501073b4254041ce509501073b4154041dc90550107394154041dc505501073141540419e98354cc67960d5331cdd5041cc6f160107318f99250cc63d64943319e980548c67960152318f992528c63d6494a318f992544c67761551318f994544c73454cc5319b988540c66d62150319e980540c67960150319d594410c7355410431bc580410c65f654c4319dd95310c6b4644c4318f99353c863d64d4f218f99053c863d6414f219e98053c86796014f21cd95331c8736540c7219e980548867960152218f993538863d64d4e219e983538867960d4e21cd55041886f16010621ad19131886b664c862197d8d544865c63551219ed81544867860551218fd91534863c6454d219dd85534867b6054d219e181534867665d0521cd55041486f160105219d9963148674654c521ad19131486b664c85218f990504863d64141219d987540865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f59053086766114c219e98053086796014c218f992520863d64948219d5973108675650c4219bd95210867765484219dd8
  | 2 => 0x1ec64000901f6910006ea0a339883aaec571567aa7800122068ca11128ba9841f2a4b4adeac21c6182c0b89a002f83c8c83c0208c0007712ab580a04800059f0000781384c8dae09e802738480000000144ad9ee28a48c2a34749ae6a004000008b81852a12001d8342da58ab85407a260001d86000000128c23d8006f9e0932709a2f0a8b065eaa02b800968da0c218580e03700099800b12b2b00c6c30c4478006e10e001c876a962eaf40013e539c2169e460258bd80000000001c00d0bc5b3025f232c22084c014802e8710e4b50be192749b00000284bf924002ba938000018a11914b21a208800003120005400000b0800a6300bb8004489202000591468903c5d8403994c29800000a8b7238a209e63996409fe818000028aa3000a78004da1e219548e800732f2419386c8286788a00178000a00007209890a3a6a952cc66116000000008cb98003491018800672ce0000000038a1a9a00000000006c2d00013c0000e0000000310002ac001b481272560060a86c002e2000800700000000092fc2a8a41d06a80800aa0005a1348b24a9406600140001080e9523f0b64b1740001098ab46b1263b292c51421c0948f0f87429023a560030e352640000037800002a67981e859704700000000000009d8000031600000000e200000b90000019471800b1a105f9a67510c9725e000004296600000af096be850aa9720022075a14000ac00000000000000000118000007e1f25680086800a52ca6a800179fc271a4480c0c1000220b42ca2ab600000228a70006480c1f95e3f8006d8000c8d8001bc35982982469f252108fa000007ea6e3a18c788003b93a2e052830367d05c1a2be468562c19a9f92e3d20e520cc0f9005ba3e5a9e8909041ba2677aae20a800028272932210586
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1601c6955000174402400000d04cf38264018000c6c14841c560000034a2c80400008a38020f4c1c14154041a62e221aa020d3171d0950106983b282a80834c1cd4154041a66e4a0aa020d3270d5041cc719aa2c020e638c5516010431c62a8b008310d14735504148698382a820a438c5516010521962e330486a04b17118142502993848628a814c1c14214540a2ce7aa083086335458041842593b682a04218c5856015110962e93066288630549833144258ba0c090a218c1506048510a64eb20c8088630655054044318aa2c0208210d1d95444010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xc001100a10835516010521a1283d5160106108318715260cc510831871506048510
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 601
  | 4 => 396
  | 3 => 29
  | 2 => 4
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
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (18427+((h/200+packedAt s4K5 (16227+(h % 200)*11) 11) % 1056)*11) 11
  | 4 => packedAt s4K4 (16368+((h/132+packedAt s4K4 (15048+(h % 132)*10) 10) % 523)*10) 10
  | 3 => packedAt s4K3 (1475+((h/9+packedAt s4K3 (1421+(h % 9)*6) 6) % 41)*6) 6
  | 2 => packedAt s4K2 (244+((h/1+packedAt s4K2 (240+(h % 1)*4) 4) % 12)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xff07ff03f8ffff078fc3fe1fe381fff91e327f
  | 1 => 0xff81ffc00ffe1f80ffc3fe1fc01fe01e3cc7c
  | 2 => 0xfffffffff07fffff0003ffffffe1ffe03ff8f
  | 3 => 0xf0001ffffff801ffffffc001ffffe007fc0ff0
  | 5 => 0xffffe000000001fffffffffe00000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x215151189121510182e24b12a08932d10e1235
  | 1 => 0xe232d22872529338056617316415543162cc5c
  | 2 => 0x40084412014004a100024444924092201648a
  | 3 => 0x40a508924080c494a988800192588044b40b60
  | 5 => 0x88c610e384e719e74e33399800611187dbb000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee0fee0f8a0f8a0fee0fee0f8a0f8a0fee0fee0f8a0f8a0fee0fee0f8a0f8a0fee0fee0f8a0f8a0fee0fee0f8a0f8a0fee0fee0f8a0f8a0fee0fee0f8a0f8a0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36286
namespace PEqualNP.Outside.L_meta_36286
open PEqualNP.Outside.L_meta_36286.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a07dd4540bba8a817c51503e8a2a05d14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630fb28c6176518c2faa3187d54630baa8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930ef99261dd324c2fea2985f14530ef18a61dc314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa418778c830ee190617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef32883d865105f94620bea8c417e50883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc84907b50920bfa8a417c51483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bcc820f6190417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10ef29c215e53842faa7087754e10aea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e50843f481087e50210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fb98a21f431443ec42887d48510fd20221f940443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f741043e882085f94010fb88021fa10043ea20087e44010
  | 1 => 0x75150eeea2a1df14543fa28a87745150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e85de53d0abca7a15f54f42eea9e855d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3217d94642bb28c857d5190beaa3215d54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f721665ed42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7197790e32eea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6197790c32eea18657e520cbdc84197b50832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c837e52906faa520efd0a41dea14837e519077e8320fdd0641bf284837d50906fea6a0df14d41bfa92837c52507ee82a0ef90541bfa82837c50506fca820df94c41ef298835e53106faa620f754c41aea98837e52107dca420db94841bea9083ed52106daa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31fba0e63f441cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7bc8698f750d31bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea9063de320c7b86418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21f721643ed42c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea94437e51887ee8310fd10621fb18c43f531887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487dc8490fb50921fba0a43f441487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29
  | 2 => 0x9886226918c0e0f48370004640008a00021c3524b3b8000eaa644168292d0660661289608f48e1f8fc8ea44097c5b0ba4864c8e2a5726e0011a9120000009192517e69015219156604e5914248934000000600008017a3c88e4a79d42dc39c38a4f1aa6f8001173740004317433e4b8aa9673361cc590df1b86f06601d4125a0be8002cc910089033ca1f0290014382f4cb883294000249a81049bc311654546f4239dd2562e45510f1940001f18000099ca88542229ac9b130000000000670004a40027106a4f8cc2031503980f1344a6001108002800b53a1333403784a1b82be9a08418d2b6000fe9d71461391e8000007480521a08a080108263b23fcef22c4304c5148953ee0006280e2120011e25903e4e0001e60004604e0043346d8000422da38c000003200d01791a07840922a022a667139251000000000002f624cef83a2a02bc45a54254134b606f1c2320261e20000011ba10182631198e41108c07800014c30c4f8050b88acd99b01124d49300b1a09852e8004288902d95c1d09551b1f00e8694d516b0f62d42b9c80c00012f0002e015486800000258471930009a90e843290178e70d31c03ecd89e01ea05c1596041a58d2923a31e3e8ab8004985c88d9270005649f80040e0002300041e3c51323f0fe2dcfd24807a1587a1ef3b69ccf19131b268c570fd13c20442009168068ae9ab2424e4be191424344c494b1b40c50a8cb3b488c8e8be27a1d4c280809673c562494c6248fa93b2f23b0c214901e5a9251150d678472a4104e3f8ad11c3160fc7ca172ac5386a1cd0c66c8e99c3038144b49fe1222c4f59992861b0f40642887b83d0eb30c620f69a23762012c1820e4700611ff25a25c1924033a418e60dd0881611a23b34c548208060066fcc71734dc2e0039102ea1690f2112160d88f0001ac2410d84f20e658b10f21f800c0101c540341c16400004001641b100010084d00c00050010040300407020030000a00805000410001a0180900022048030040100c03010220141f040070804a0141b0100e02c04018060280002c01028280901b00c010800800c000000300004010020441e000030081001071008020200000c0203c0602c13000000841a000000001e00002018000586500402018000381400401004191544e000020041d00c01000350080005c3b000000a002040010007a0300d00000004080240b0200c07c0b004000b01d0c4070d00a16850000030000d000000101600420028360181701c0101400010030080100c00010080001803010018110040a0001802c04014020080201401bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a87f
  | 3 => 0xda1a132a7187c16f1809dc799280362745105f3826dd001a9000744090992180006c0003840640008530e8b400000000000000680005d8001ad00000034a014ea1b400000410100678f73ac3888b0004ca2ccbf00038e1e41620502a1400008d04a7c8dc8ad4cc438010000000010b05336a000f99451428b89d0ce1d21e13802449c291071d847c488460d21ae6bc329ec4ac000668004b8414d71713d4404000a72c2000000141348e0381781925fc080000000b8e8000000000000000005351100000000000000000000000002c8000000004624bc821460006784c20600026c0000d3f0940002420007ec5e0131521843b26d44a030001540003d86382307689cf3800072980c185d1603bc3e98a14a8113b000000650001f42bc96c9e0bb46447d060590001b8000ee000000c900000072400000000000000003947d8001c44265dc240180008bc3ba462409b0ac1fc450000d39470527c48514c050280a10ed0000000002235887c0b1411b6
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x524c23d64149309d984524c2756114930cb990524c32d6414930d390c524c34d4314930d9984524c3656114930da580524c25e65cc930d314b324c34c524c930d314a314c2da608c530d3148314c34c528c130b5986304c27761550309d185540c25e63150309b988540c26d62150309d984540c275611503097596320c2d9600c83097d95300c2cc624c0309ed95300c27661d53209d58754c825e63953209758e54c823e6414f208f59053c82766114f209d58453c825f63547209718d51c827761552209d185548825e63152209758c548827661152209d584548827661d4e209d58753882e9600ca208fd91518823c6454620f20ca30882e8624c220f2cc9308825e63951209758e544825f63551209718d544827761551209d185544825e6394d209bd89534825e6514d20d6580534834c53909209b195424834c5350920d614e3048278654c120d314e204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530834c6254c208f990530823d6414c209798c53082766114c209d584530827a6014c20cb553320834d53cc8209b594320832d540c820cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420cb553200835953880209bd95200832d5448020b318d200827b6548020d654d200825e63153109758c54c426e62153109b58854c426e62d4f109b58b53c425e63d4b109758f52c423e6494b108f59252c42d463487109798f548425d63d52109798c548425d63152109b988548426d62152109798f528425d63d4a108f990528423d6414a109798c528425d6314a10d594f41843565310610bc58041843b04190210bc185408435653c42108f992544427761551109798c544425d63151109b988544426d62151108f994544431e6315110c758c544432e6215110cb58854443356115110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d52442766590510cd15241442746550510cd151414427665cc510cd15331442f260cc510cd150314433454885109d19521443345448510b518d21442f06048510ce15240443b241901109e19540443345484110b598e104425e63150109758c540426e62150109b588540427661150109e980540427661d4c108f990530423d6414c109b988530426d6214c1097d8d520425c63548108f990520423d64148109798c520425d63148109d984520427565d04109d59441042f160104109798e500425d63940109e59610042776544010ad191100427b6544010
  | 1 => 0xcb1e6395032cb98a540ca3e64150329d984540ca7561150329e980540ca79601503297596430cb1e5450c32b5185430ca6d6590832cb951420cb8d435083297d95320ca6f654c832cd952510cb355494432cd951510cb355454432d590d510cb554354432d9909510cb654254432ce952500cb395494032dc946500cb715194032ce951500cb395454032dc945500cb715154032d690d500cb594354032da909500cb694254032d6cc9500cb59325403297d8d529065c6354a419798e509065d6394241d5185531074e5394841d354e52107666194841d394d521074d5354841c754f421071d5350841cb949421063f65504419dd95411075a5394041d654e501076a5294041da54a501075a5354041d654d501076a5254041da549501073b4254041ce50950107724154041dc505501067a60d53319e58354cc66e62953319b58a54cc6d46150f31b558c41cc6f160107319b988548c66d62152319e980548c67960152318f992528c63d6494a31b5584328c6d9600ca319b98a544c66d62951319dd85544c65c6550d319798c540c66e62150319b588540c67a60150319e580540c74d520c831b6580320c6756510431cd550410c6f1601043197d95310c677654c4319798e54c865d6395321c798e54c871d6395321cb98a54c863e64d4f218f59353c863e6414f218f59053c867a6014f219e58053c872e5450b219798c548865d63152219e980548867960152219e983538867960d4e21b558c41886f16010621ad993218865e63942219758e508865e63951219758e544865f63551219718d544867b60551219e181544865e6394d219799453487556114d21d314e42486e661909219b195424874c53509219d997414875453d0521b558c41487545310521b998841487a54210521bc5804148754538c5219d19531486b664c85219d987540865e63150219758c540866e62150219e980540867960150218f990530863d6414c219d984530867a6014c219e580530863e64948218f592520866f65484219dd9521086776154f409d18553d02766194b409d58652d026f6254e409b189539025f6354a409718d52902b96010640cdd0851503354214540dc58051503345190140d394e521034d5394840d394d521034d5354840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cb54a41103355190440cb548411032d52d0040dc546401023f6550040cb54940102b461500409ed95401037151500409d98754cc27561d53309b98a54cc26d6295330b518543cc27661d52309d587548c26e62152309b588548c27661152309d584548c2d9600ca30d58ca518c3543294630d5947308c26e62951309b58a544c26f62551309b189544c27761551309d185544c25c6550d30b5185434c2d86050d308f99
  | 2 => 0xcfb9470a6400000d6956da8000027a000001c0008a8004da720ba860000e6c000000fcb10009a9e400000c980000000000009b9c6218a4ca8002725420a0e8601a28a88b90ea851dc000948e0001211033090cf39c3f80012800ab9fea00002e29e79800de800b08002132e7e8a0908c20000000000de00059800d90007d138c900000000bd800003aa002b20036e000000012ed4000d3824b73867b012aeace29972e7afe00058818000025860114c5992918009f000e8a44af926000000024ccb000000000000000356001a81b8009f800000000000000000018000031c0000057182030000034ca51680b3449d296000caac336671bc1e07ca49ca0e80094000001463980097ad87b800aa8000011c7e26c88800e680000000000000200053354e20dc7618a6207a000005600086800739da7a08c00000e429834b626e8b468a36000000000000000002a2810005780000312cc0d68e80000000ae000338002b00040b82a0aa0b2000d0800000008b880001b6003b0d2b60782ea72010008006f800382d6000923e0da8997a0025a1a000e637c00194228007c000e00360c922000f40016a0000000000a300000332002e6000000016c1c800d0118c10000025c00000be228568660000039000841425d2a86b00026800000b20019052176000b02d80000000b180000000001f2000000800000000e30be759a4b31f6480000000000000adaca00000003a0d9b0000000928001a800e3aa6000a8000000021ebb1448f06c468260e1308c07607000dd00053a1600100b02248f80099a0a000002f000002e8d70003e80010b0a003a40fa62b406459004002320000058b209db4800000000000033a0016031a90002520100400004004040080001015000070100200000010000040100801000000100200402000000280900000004000040201800000060100000c09000020140003003008000040100c0100005004000080100000000020100100002004030000b0000100400000010280500000004050040400c010100200c000200b00808008010000200000008040001500c01000000040601800008020040502002000000000d0080100400000000000001002000020000000c04000040000104004008020000100002002766194b439d58652d0f666194b43d958652d0ece62d0e439d9865090e756194243b398b4350e3f6550c4397d954310f1e5350f42ad18543d0ace63d0a42cdd0a5190aae62d0d42ad1854350ace63d0942ad9864250a5e63141429758c5050a7661141429d5845050a3f65508429bd954210a7761553329d18554cca7661943329d58650cca7661d52329d587548cad46150e329758e544ca6d62951329dd85544ca7461551329ed81544ca7860551329d987540ca7561d50329e983540ca7960d50328f596540
  | 3 => 0x29c6b97ee1000000000000000000000000000017124788d000000152b400152d60220036c00000ca1a65f1aaea1d0b8800dd8000a8004c99ac18000000000000110ee002d2000000013ece000c099e47b1e00000001843b0000004642000b80000000000000c39066e12a0035e0003c000ba002020020800000000004f000138007f00000000000000013441000000005500000030bf0c4da2d4003aeeb3700000000334c5000731b216800438000001426000c6000bc8002222095800a2b46a6800000009a0f64e9960017037a4e001d47aabc000601d00007912662de001c0c2000900d43c1865e00000000002ee0008e00234389a0000560000013310001b4d4a1202a8e528000020c3c80000392c6800000000000000200278000580000000e980000000710964a018100000005e000004598e9c0007790c000000022c36278500004280000000000aae596e14000002a400000ab0000000000000bd0ae00000c30c8be80000000000000003400000000000a0c00000014950b6862002484b0e8dfa60bc2840000000000870000007ee2b22dc9d263
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1900000a1c815744071800000409200025618068000004c54f38d6d44cb0d00e484000280105611c54350832e0a86a12a2195507150d500cb84a1a84a806592549600c831c62a8b008218c557614c4148742b1a8420a43c114d4210521ca0a6b008290ea1425804148712a90c2a0081545c03294630a88e2a18a4985487050c524c312b22c2292618a5916014930c90a5304629864452986304c2653b66498441835506348020ca4a6b00830860d635885444314b12c02a2218c15260cc510c28a831a42886305418121442993ac8320221851526384110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1400b008150d4254032a058614d4210521e00535096010521
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => packedAt s5K5 (19164+((h/210+packedAt s5K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s5K4 (19544+((h/157+packedAt s5K4 (17974+(h % 157)*10) 10) % 829)*10) 10
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 41)*6) 6
  | 2 => packedAt s5K2 (182+((h/1+packedAt s5K2 (180+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1ffc7f07e3ff0e3c7e3f03fe381ffc33327f
  | 1 => 0x1fe0ff8ff803f8f03f8fc7fc1fc01f80cdcc7c
  | 2 => 0x1fff000ffffc7fffc00ff8001fffe3ff0e0f8f
  | 3 => 0xe000000fffff80fffff000001ffffc03f00ff0
  | 4 => 0xfffffff0000000ffffffffffe0000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x424a1081304410020c120908ca0884a8111235
  | 1 => 0xc4c6281211c921301486423856414918454c5c
  | 2 => 0x804492442814054400c9051049242510e048a
  | 3 => 0x8198b248a50232aab92000a299259022f00b60
  | 4 => 0x1110c000c61244cd224924c300060043aaa000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeef8a0feeef8a0feeef8a0feeef8a0feeef8a0feeef8a0feeef8a0feeef8a0feeef8a0feeef8a0feeef8a0feeef8a0feeef8a0feeef8a0feeef8a0feeef8a0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36286
namespace PEqualNP.Outside.L_meta_36286
open PEqualNP.Outside.L_meta_36286.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c18000ffd50037f5400ff95003fd5400df55003fc54017fd4c05fe53017f54c05fc5300ffd0c03fe4300ff50c03fc43017fd4805fe52017f54805fc5200ffd0803fe4200ff50803fc42007fcc801fe32007f4c801fc32017fd4405fe51017f54405fc5100ffd0403fe4100ff50403fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc5000ffd0003fe4000ff50003fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42004ff08210027fe2108013f71084007fd8842009ffd951004dfeca880037f65440013fb2a2009ff99510015fcca88027fd65440137eb2a2009ff19510015f8ca880277c65440053e32a2008ffd9110045fec888003bf64440015fb222008ff9911000dfcc888023fd64440117eb222008ff1911000df8c888023bc64440035e3222008ffd5110046fea888023fe5444011feaa22008df55110047f8a888003ff63440017fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c688027ff5344013ff29a2009ff54d1004ff8a688023ff4344011ff21a2008ff50d10047f88688003ff62440017fb122000ff9891003dfcc488003fd62440017eb122000ff1891003df8c488027ff5244013ff2922009ff5491004ff8a488023ff4244011ff2122008ff50910047f88488003ff3244001ff1922000ff4c910007f86488027ff5144007ff28a2009fd9451004ffaa288027f55144007fe28a2008ffd051001ffc8288023f64144011fea0a2008fd5051001ff88288003ff3144001fb98a2003ff8c510007fa628800ffc3144001fa18a2000ffc851001ffc4288003f62144001fe90a2000fd4851001ff84288027ff5044009ff2822009fe9411004ffaa088027f95044009fe2822008ffd0110027fc8088023fa4044011fea022008fe50110027f88088003ff3044009ff1822000ff4c110027f86088003ff2044009ff1022000ff48110027f8408800fff1044007fd8822004ff84110027ec2088013ff65040097fb282004ff99410015fcca080137e65040053f3282004ff59410035faca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff9901000dfcc808013fd640400b7eb202004ff19010025f8c808017ff540400bbfaa02005ff9501002ffaa8080177d540400bfe2a02004ffd8c10025fec608013fe63040017f3182004ff58c10005fac608013fc63040097e3182006ffd4c10037fca60801bfd530400dfe2982005ffd0c1002ffc8608017fd430400bfe2182004ffd8810025fec408013fe620400f7f3102004ff58810005fac408013fc62040097e3102006ffd4810037fca40801bfd520400dfe2902005ffd081002ffc8408017fd420400bfe2102000ffcc810007fc6408003fd3204001fe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802003fe44010
  | 1 => 0xbfc4108001ff9884000ff8c420007fa6210003fc310800fff9084007ff8842003ffa421001ffc21080097f3004004ffd4020027fca010013fd5008009fe2804004ffd0020027fc8010013fd4008009fe2004004ffcc020027fc6010013fd3008009fe1804004ffc8020027de4010013fe2008009fd1004004ff48020027da401001ff92008007ffb2e2003bfd971001ffccb8800afe65c4007feb2e200dbf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc988006fe64c4007feb26200cbf5931001ff8c98800efc64c4019ffaa6200cdfd5310067fca988033fd54c4019beaa6200cff1531001ffec78800eff63c4007ff31e2000bf98f1001ffac788002fd63c4007fe31e2003bf18f1006ffea788037fe53c401bfea9e200dff14f10067fe8788033fe43c4019fea1e200cff10f1001ffec58800eff62c4007ff3162007bf98b1001ffac588002fd62c4007fe3162003bf18b1006ffea588037fe52c401bfea96200dff14b10067fe8588033fe42c4019fea16200cff10b10007fe6588003fe32c4001fe9962000ff0cb1001ffea38800ffe51c4007fb28e2003ff5471006feaa38800ffc51c4007ffa0e2003ff9071001fec838800ffd41c4019faa0e2003ff1071001ffe6388003f731c4007ff18e2003ff4c71001ff8638800ff431c4007ff90e2003ff8871001fec438800ffd21c4001fa90e2003ff0871006ffea188013fe50c401bfea862004ff14310067fe8188013fe40c4019fea062004ff10310007fe6188013fe30c4001fe9862004ff0c310007fe4188013fe20c4001fe9062004ff08310027fecb08012ff6584009ff32c2002bf99610027facb0802efd6584009fe32c2004bf19610027fec908012ff6484009ff3242001bf99210027fac90802afd6484009fe3242004bf19210057fea90802b7f5484015ff2a4200aff55210056faa90802bfc5484009ffb1c2004bfd8e10027fcc708002fe6384009feb1c2000bf58e10027f8c708012fc6384017ffa9c200bff94e1005ffaa70802ffc5384015ffa1c200aff90e10057fa870802bfc4384009ffb142004bfd8a10027fcc50801efe6284009feb142000bf58a10027f8c508012fc6284017ffa94200bff94a1005ffaa50802ffc5284015ffa14200aff90a10057fa850802bfc4284001ff9942000ff8ca10007fa6508003fc32840117eb0c200bffd461001ffca30802ffd5184007fe28c200affd061001ffc830802bfd4184007fe20c2000ffcc61001ffc6308003fd3184007fe18c2000ffc861001ffc4308003fd2184007fe10c2004bf98210027fea108013fe5084009fd2842004ff5421005ff2a108013fc5084009ffa042004ff90210027f48108013fd4084015fca042004ff10210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fe9
  | 2 => 0x2003ff8a51004bff428800fff2144012ff50a2003ff88510003ff328800fff1944000ff4ca2003ff86510013ff6188009ff30c4003bf98620027fac310002fd6188009fe30c4013ffd462009ffca31004ffd5188027fe28c4012ffd0620097fc831004bfd4188025fe20c4000ffcc620007fc6310003fd3188001fe18c4007ffc8620007fc4310003fd218800ffe10c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fd1844004ff4c220007f26110013fc3088009ff9044004fbc822003ff64110047ff65480237fb2a4011ff99520015fcca90047fd65480237eb2a4011ff19520015f8ca90043ff64480217fb224010ff9912000dfcc890043fd64480217eb224010ff1912000df8c890043ff5448021bfaa24010ff95120087faa8900437d5448021fe2a24000ffd8d20005fec690003fe63480017f31a4000ff58d20005fac690003fc63480017e31a4011ffd4d2008ffca690047fd5348023fe29a4010ffd0d20087fc8690043fd4348021fe21a4011ffd492003ffca490047fd524800ffe2924010ffd092003ffc8490043ee4248021fea124010fb5092003ff88490003ff324800fff1924000ff4c92003ff86490003ff61480017fb0a4000ff98520007fac290003fc61480077e30a4011ffd452008ffca290047fd5148023fe28a4010ffd0520087fc8290043fd4148021fe20a4000ffcc520007fc6290003fd3148001fe18a4007ffc8520007fc4290003fd214800ffe10a4011ffd4120027fca090047fd5048009fe2824010ffd0120027fc8090043fd4048009fe2024000ffcc120027fc6090003fa3048001fe9824000fe4c120027f8609001fff204800ffd9024004ff88120027dc4090013ff65080097fb284004ff99420015fcca100137e65080053f3284004ff5942007dfaca100137d65080013eb284004ff19420025f8ca10013ff64080097fb204004ff9902000dfcc810013be64080035f3204004ff59020075fac810013bd64080015eb204004ff19020025f8c81003bff540801dbfaa0400eff95020077faa81003b7d540801dfe2a04004ffd8c20025fec610013fe63080017f3184004f798c20005bcc610013fd63080017eb184004f758c20005bac610013fc63080097e318400fffd4c2007ffca61003ffd530801ffe298400effd0c20077fc861003bfd430801dfe2184007bf9882003ffea41001ffe520800ffea904007ff1482003ffe841001ffe420800ffea104007ff1082003ffe641001ffe320800ffe9904007ff0c820027fec210013fe61080077f3084004fd98420005ecc210013fd61080017eb084004fd58420005eac210013fc610801fffa88400fff9442007ffaa21003ffc510801dffa08400eff90420077fa821003
  | 3 => 0xf202601aff50130027f88098003ff304c001fd9826004ff8c130027bc6098013ff650c0097fb286004ff99430015fcca18013fd650c0317eb286004ff19430025f8ca18013ff640c0097fb206004ff9903000dfcc818013fd640c02f7eb206004ff19030025f8c81805fff540c02fbfaa06017ff950300bffaa81805f7d540c02ffe2a06019bf98c300c7fea61805bfe530c031fea986016ff14c300bffe861805bfe430c02ffea186016ff10c30027fec418013fe620c00f7f3106004ff58830005fac418013fc620c031ffa906018ff948300c7faa418063fc520c02fffa106017ff908300bffa841805ffc420c02dff9906000ff8c830007fa641805bfc320c009ffb086004ff9843001dfcc218013fd610c0017eb086004ff184300c7fea218063fe510c031fea886018ff144300bffe821805ffe410c02ffea086017ff104300b7fe6218003fe310c001fe9886016ff0c430007fe4218003fe210c001fe9086000ff08430025fcc018013ff500c009ff2806004ff54030027f8a018013ff400c009ff2006004ff50030027f88018013ff300c009ef9806004ff8c030027f46018013fd300c009ee9806000fe4c03003ffecb9001eff65c800fff32e4002bf9972003ffacb90056fd65c800ffe32e4007bf1972003ffec99001eff64c800fff3264001bf9932003ffac990052fd64c800ffe3264007bf193200a7fea9900537f54c8029ff2a64014ff553200a6faa990053fc54c800fffb1e4007bfd8f2003ffcc790002fe63c800ffeb1e4000bf58f2003ff8c79001efc63c802bffa9e4015ff94f200affaa790057fc53c8029ffa1e4014ff90f200a7fa8790053fc43c800fffa964007ff94b2003ffaa59001ffc52c800fffa164007ff90b2003fdc859001ffd42c8029f6a164007ff10b2003ffe659001ffe32c800ffe9964007ff0cb2003ffec39001ffe61c80077f30e4007ff58720005fac39001ffc61c802bffa8e4015ff947200affaa390057fc51c8029ffa0e4014ff907200a7fa8390053fc41c8001ff98e4000ff8c720007fa6390003fc31c800fff90e4007ff8872003ffa439001ffc21c802bffa864004ff943200affaa190013fc50c8029ffa064004ff903200a7fa8190013fc40c8001ff9864004ff8c320007fa6190013fc30c8009ffb2c4004bfd9620027fccb1000afe6588009feb2c4013bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc910006fe6488009feb244012bf59220027f8c910012fc6488025ffaa44012dfd5220097fca91004bfd5488025beaa44012ff15220027fec710012ff6388009ff31c4000bf98e20027fac710002fd6388009fe31c4004bf18e2009ffea71004ffe5388027fea9c4013ff14e20097fe871004bfe4388025fea1c4012ff10e20085fac51004fff528800fff2944013ff54a
  | 4 => 0x5bfc43cc02dffb166000ff98b3003dfcc598003fd62cc0017eb166016ff18b300f7fea59807bfe52cc03dfea96601eff14b300cffe8598067fe42cc033fea166019ff10b300b7fe6598003df32cc001ff1966000ff4cb30007ba659805bfc32cc02dffb0e6000ff9873001dfcc398003fd61cc0017eb0e6016ff187300f7fea39807bfe51cc03dfea8e601eff147300cffe8398067fe41cc033fea0e6019ff107300b7fe6398003fe31cc001fe98e6016ff0c730007fe4398003fe21cc001fe90e6000ff087300f7fea198013fe50cc03dfea866004ff143300cffe8198013fe40cc033fea066004ff10330027fecb18012ff658c009ff32c6002bf99630026fccb1800a7e658c009feb2c601dbf59630026facb180027d658c009fe32c6004bf19630027fec918012ff648c009ff3246001bf99230027fac918072fd648c009fe3246004bf192300e7fea9180737f548c039ff2a4601cff552300e6faa918073fc548c0357eb1c601dffd4e300effca718077fd538c03bfe29c601cffd0e300e7fc8718073fd438c039fe21c6004ffd8a30027fcc51801efe628c009feb146000bf58a30027f8c518077ff528c03bff294601dff54a300eff8a518073ff428c039ff214601cff50a300e7f88518003ff328c001ff1946000ff4ca30007f86518013ff618c009ff30c6003bf98630027ecc318002f6618c009feb0c6000bf58630027eac318002f5618c009fe30c601dffd46300effca318077fd518c03bfe28c601cffd06300e7fc8318073fd418c039fe20c6000ffcc630007fc6318003fd318c001fe18c6000ffc8630007fc4318003fd218c001fe10c6004bf98230027fea118013fe508c009fea846004ff14230027fe8118013fe408c009fea046004ff10230027fe6118013df308c001fd984601bffd95300ddfeca9806ffe654c0057f32a601bff595300ddfaca9806ffc654c0057e32a601affd91300d5fec89806bfe644c0037f322601aff591300d5fac89806bfc644c0037e322601affd51300d6fea89806bfe544c035feaa2601adf551300d7f8a89806fff534c037ff29a601bff54d300dff8a69806bff434c035ff21a601af790d300d7fa869806bdd434c035fe21a6000ffd8930005fec498003fe624c001feb126000ff1893003df8c49806fff524c037ff292601bff549300dff8a49806bff424c035ff212601aff509300d7f88498003ff324c001ef9926000ff8c930007fa6498003dd324c001fe1926000ffd8530005fec298003fe614c001feb0a6000ff1853001df8c29806fff514c037ff28a601bff545300dff8a29806bff414c035ff20a601aff505300d7f88298003ff314c001ff18a6000ff4c530007f86298003ff214c001ff10a6000ff48530007f8429806fff504c009ff282601bff54130027f8a09806bff404c009f
  | 5 => 0xc62101fec631080ffd3188401fa98c4203ff0c62101ffe431080fef218840ffb90c4203ffd822101ffcc110812fe6088407feb044200bf5822101ff8c110893ff5088449ff2844224ff54221127f8a11088fff4088447ff2044223ff5022111ff8811088bff65484457fb2a4222ff99521015fcca9088bfd65484457eb2a4222ff19521015f8ca90887ff64484437fb224221ff9912100dfcc890887fd64484437eb224221ff1912100df8c890887ff5448443bfaa24221ff9512110ffaa8908877d5448443fe2a24200ffd8d21005fec690803fe63484017f31a4200ff58d21005fac690803fc63484017e31a4222ffd4d21117fca69088bfd5348445fe29a4221ffd0d2110ffc8690887fd4348443fe21a4222ffd492103ffca49088bfd524840ffe2924221ffd092103ffc8490887ee4248443fea124221fb5092103ff88490803ff324840fff1924200ff4c92103ff8649088bff5148407ff28a4222ff5452101ff8a290887ff4148407ff20a4221ff5052101ff88290803ff3148407ff18a4200fd8c521007fa6290803f53148407fe18a4207ffc852103fee429080ffe2148407f710a4200ffd8121005fec090803fe6048401feb024200ff18121025f8c09088bff5048445ff2824222ff54121117f8a090887ff4048443ff2024221ff5012110ff8809080fff65084077fb284203ff99421015fcca1080ffd65084417eb284203ff1942101df8ca1080fff64084077fb204203ff9902100dfcc81080ffd640843f7eb204203ff1902101df8c81087fff540843fbfaa0421fff950210fffaa81087f7d540843ffe2a04203ffd8c2101dfec61080ffe63084017f3184203ff58c21005fac61080ffc63084077e3184220ffd4c21107fca610883fd5308441fe298421fffd0c210fffc861087ffd430843ffe2184207bf9882103ffea41081ffe520840ffea904207ff1482103ffe841081ffe420840ffea104207ff1082103ffe641081ffe320840ffe9904207ff0c82101dfcc21080fff5108407ff2884203ff5442101ff8a21080fff4108407ff2084203ff5042101ff8821080fff3108407ff1884203ff4c42101ff8621080fff2108407f79084203ff8842101fec421080ffd2108407f69084207fd4842101ffec01080ffe60084097f3004203ff58021005fac01080ffc6008441ffa804220ff94021107faa010883fc500843fffa00421fff900210fffa801087ffc400842dffb2e601ebfd97300f7fccb9800afe65cc03dfeb2e601ebf597300b7f8cb9800afc65cc02dffb266019bfd93300cffcc998006fe64cc033feb266019bf593300b7f8c998006fc64cc033ffaa66019dfd53300cffca998067fd54cc033beaa66019ff153300f7fea79805bfe53cc03dfea9e6016ff14f300cffe879805bfe43cc033ef21e6019ff50f300cfba8798
  | 6 => 0x17eb286203ff1943101df8ca1880fff640c4077fb206203ff9903100dfcc81880ffd640c44f7eb206203ff1903101df8c81889fff540c44fbfaa06227ff9503113ffaa81889f7d540c44ffe2a06229bf98c31147fea61885bfe530c451fea986216ff14c3113ffe861885bfe430c44ffea186216ff10c3101ffec41880ffe620c40f7f3106203ff58831005fac41880ffc620c451ffa906228ff94831147faa4188a3fc520c44fffa106227ff9083113ffa841889ffc420c42dff9906200ff8c831007fa641885bfc320c4077f3086203ffd443101ffca21880ffd510c407fe2886203ffd043101ffc821880ffd410c407fe2086203ffcc43101fbe621880ffe310c407fb1886203ff4c43101fba6218803f5310c407ffb006203ff98031025fcc01880ffd600c4017eb006203ff18031147fea0188a3fe500c451fea806228ff1403113ffe801889ffe400c44ffea006227ff1003103ffecb9081eff65c840fff32e4202bf9972103efccb9080a7e65c840ffeb2e4226bf5972103efacb908027d65c840ffe32e4207bf1972103ffec99081eff64c840fff3264201bf9932103f7cc990806be64c840ffeb264225bf5932103f7ac990802bd64c840ffe3264207bf1932112ffea9908977f54c844bff2a64225ff5532112efaa990897fc54c840fffb1e4207bfd8f2103ffcc790802fe63c840ffeb1e4200bf58f2103ff8c79081efc63c844dffa9e4226ff94f21137faa79089bfc53c844bffa1e4225ff90f2112ffa8790897fc43c840fffa964207ff94b2103ffaa59081ffc52c840fffa164207ff90b2103fdc859081ffd42c844bf6a164207ff10b2103ffe659081ffe32c840ffe9964207ff0cb21137fea39080ffe51c844dfea8e4203ff1472112ffe839080ffe41c844bfea0e4203ff10721007fe639080ffe31c8401fe98e4203ff0c72103ffec19081ffe60c84097f3064207ff58321005fac19081ffc60c844dffa864226ff94321137faa19089bfc50c844bffa064225ff9032112ffa8190897fc40c8407ffb2c4203bfd962101ffccb1080afe6588407feb2c4224bf5962101ff8cb1080efc6588407ffb244203bfd922101ffcc910806fe6488407feb244223bf5922101ff8c91080efc6488447ffaa44223dfd522111ffca91088ffd5488447beaa44223ff1522101ffec71080eff6388407ff31c4200bf98e2101ffac710802fd6388407fe31c4203bf18e21127fea710893fe5388449fea9c4224ff14e2111ffe871088ffe4388447fea1c4223ff10e2110dfac510893ff528840fff2944224ff54a2103ff8a51088fff428840fff2144223ff50a2103ff88510803ff328840fff1944200ff4ca2103ff8651080efe6188407ffa8c4203ff9462101ffaa31080ffc5188407ffa0c4203ff9062101ffa831080ffc4188407ff98c4203ff8
  | 7 => 0x98806fe64cc453feb266229bf593310b7f8c998806fc64cc453ffaa66229dfd533114ffca9988a7fd54cc453beaa66229ff15331177fea79885bfe53cc45dfea9e6216ff14f3114ffe879885bfe43cc453ef21e6229ff50f3114fba879885bfc43cc42dffb166200ff98b3103dfcc598803fd62cc4017eb166216ff18b31177fea5988bbfe52cc45dfea96622eff14b3114ffe85988a7fe42cc453fea166229ff10b310b7fe6598803fe32cc401fe9966216ff0cb31177fea39880ffe51cc45dfea8e6203ff1473114ffe839880ffe41cc453fea0e6203ff107310b7fec198803fe60cc4097f3066200ff58331005fac19885bfc60cc45dffa86622eff94331177faa1988bbfc50cc453ffa066229ff9033114ffa81988a7fc40cc407ffb2c6203bfd963101ffccb1880afe658c407feb2c622dbf5963101ff8cb1880efc658c407ffb246203bfd923101ffcc918806fe648c407feb24622cbf5923101ff8c91880efc648c459ffaa4622cdfd5231167fca9188b3fd548c459beaa4622cff15231155fac7188b7ff538c45bff29c622dff54e3116ff8a7188b3ff438c459ff21c622cff50e31167f8871880fff628c407ff3146207bf98a3101ffac518802fd628c407fe314622dffd4a3116ffca5188b7fd528c45bfe294622cffd0a31167fc85188b3fd428c459fe2146200ffcca31007fc6518803fd328c401fe1946203bf9863101ffea31880ffe518c407fea8c6203ff1463101ffe831880ffe418c407fea0c6203ff1063101ffe631880fdf318c401fb98c6203ffd823101ffcc118812fe608c407feb046200bf5823101ff8c1188b7ff508c45bff284622dff5423116ff8a1188b3ff408c459ff204622cff50231167f881188afff654c4577fb2a6200dfd9531004feca988affe654c4057f32a622bff5953115dfaca988affc654c4057e32a622bdf19531014f8ca988abff644c4557fb22622aff9913100dfcc8988abfd644c4557eb22622aff1913100df8c8988abff544c455bfaa2622aff95131157faa8988ab7d544c455fe2a2622bffd4d3115ffca6988affd534c457fe29a622affd0d31157fc86988abde434c455fea1a622af750d31157f88698803ff624c4017fb126200ff98931007fac498803fc624c40f7e312622bffd493115ffca4988affd524c457fe292622affd0931157fc84988abfd424c455fe2126200ffcc931007fc6498803fd324c401fe192622bffd453101ffca2988affd514c407fe28a622affd053101ffc82988abfd414c407fe20a6200ffcc531007ee629880ffe314c407ef18a6200ffd8131005fec098803fe604c401feb026200ff18131025f8c0988afff504c457ff282622bff5413115ff8a0988abff404c455ff202622aff50131157f8809880fff650c4077fb286203ff99431015fcca1880ffd650c45
  | 8 => 0x750e321a7f8871901efe628c80fffa946407ff94a3203ffaa51901ffc528c80fffa146407ff90a3203ffa851901ffc428c80fff9946407f7cca32007de651901fff618c80fff30c6403bf9863203ffac319002fd618c80ffe30c6435ffd46321affca3190d7fd518c86bfe28c6434ffd06321a7fc83190d3fd418c869fe20c6407ffd823203ffcc119012fe608c80ffeb046400bf5823203ff8c1190d7ff508c86bff2846435ff542321aff8a1190d3ff408c869ff2046434ff502321a7f881190cfff654c8677fb2a6400dfd9532004feca990cffe654c8057f32a6433ff5953219dfaca990cffc654c8057e32a6433df19532014f8ca990cbff644c8657fb226432ff9913200dfcc8990cbfd644c8657eb226432ff1913200df8c8990cbff544c865bfaa26432ff95132197faa8990cb7d544c865fe2a26433ffd4d3219ffca6990cffd534c867fe29a6432ffd0d32197fc86990cbfd434c865fe21a6433ffd493203ffca4990cffd524c80ffe2926432ffd093203ffc84990cbfd424c80ffe2126400ffcc932007de649901ffe324c80fef1926400ffd8532005fec299003fe614c801feb0a6400ff1853201df8c2990cfff514c867ff28a6433ff5453219ff8a2990cbff414c865ff20a6432ff50532197f88299003ff604c8017fb026400ff98132007fac099003fc604c8097e3026433ffd413219ffca0990cffd504c867fe2826432ffd0132197fc80990cbfd404c865fe2026407ffd943203dfeca1901ffe650c8057f3286407df99432014fcca1901ffd650c8617eb286407df59432004faca1901ffc650c80f7e3286407ffd903203dfec81901ffe640c8037f3206407ef9903200d7cc81901ffd640c85f7eb206407ef590320057ac81901ffc640c80f7e320642fffd503217efea8190bffe540c85ffeaa0642fdf5503217ff8a8190c6fe630c861ffa986416ff94c32187faa61905bfc530c85fffa186416ff90c3217fbc86190bffd430c85feea186416ff10c3203dfcc41901fff520c80fff2906407ff5483203ff8a41901fff420c80fff2106407fb9083203ffa84190bfed420c80ffe2106407ffcc83203fbe641901ffe320c80ff71906407ff4c83203fba6419003ed320c80fffb086407ff9843201dfcc21901ff6610c8017b3086407ff58432005fac21901ff5610c8017ab086407ff18432187fea2190c3fe510c861fea886430ff1443217ffe82190bffe410c85ffea08642fff1043203ffec01901ffe600c8097f3006407fe98032005f4c01901ffd600c8017eb006407fe58032005f2c01901ffc600c861ffa806430ff94032187faa0190c3fc500c85fffa00642fff9003217ffa80190bffc400c82dffb2e622ebfd9731177fccb9880afe65cc45dfeb2e622ebf597310b7f8cb9880afc65cc42dffb266229bfd933114ffcc9
  | 9 => 0x300100000000100000a00400000200100100000100200100300300200000200000000900101200000000000100600200400300000000c00200000100500100000400500300500100000200100000000100400600100200b00300000100400100300000800000100000400000200200000000100a00300300100100000000000200300400100000000000000000100000100200000400200500100000700400000000200300100000500000200000000400000100000000100100000500000200200000000400000100300200300b00000000000000000000000300100000200401100200000000200701000000500100300000100000300600500000900000200100200000800000700400000200500000100000000000000000300000000100000000200000100100000100000200100000400000200000000600100100100200000200200200000100000300300200300000600100000000000000100400100100000100000400000600600100200000400100800000000000c00100000000000000600101d00100100100300300200100300200100400300000600200400500100100700a00000000100000300000000000000100400000400500100000200200100100500300000a00300400d00000400000300100400400300000500000000300000900000300200000200000100001000700000300000300000000a00300200100100400500200300100400200500000d00000300000200100900200000000200200100e0010050000000000000000000010b7fecb990daff65cc86dff32e6402bf997321b7facb990dafd65cc82dfe32e6402bf197320b7fec9990c6ff64cc863ff3266401bf9933218ffac9990c6fd64cc82dfe3266401bf1933218ffea9990c77f54cc863ff2a66431ff5533218efaa9990c7fc54cc86dffa9e6416ff94f321b7faa79905bfc53cc863ffa1e6416ff90f3218ffa879905bfc43cc86dffa966407ff94b321b7faa59901ffc52cc863ffa166407ff90b3218fdc85990c7fd42cc863f6a166407ff10b320b7fec399003fe61cc8077f30e6400ff58732005fac39905bfc61cc86dffa8e6436ff947321b7faa3990dbfc51cc863ffa0e6431ff9073218ffa83990c7fc41cc82dffb066400ff98332025fcc199003fd60cc8017eb066416ff183321b7fea1990dbfe50cc86dfea866436ff1433218ffe81990c7fe40cc863fea066431ff1033203ffecb1901eff658c80fff32c6402bf9963203ffacb190d6fd658c80ffe32c6407bf1963203ffec91901eff648c80fff3246401bf9923203ffac9190d2fd648c80ffe3246407bf192321a7fea9190d37f548c869ff2a46434ff552321a6faa9190d3fc548c8657eb1c6435ffd4e321affca7190d7fd538c86bfe29c6434ffd0e321a7fc87190d3de438c869fea1c6434f
  | 10 => 0x9084f473e26018ac7160003578aa44c00000000000000000000151000021300000000000000469b2c00034f00004100000000001554000000000000000000000015c04e8000032800009e32a00006780000000001520cda0000a5800015e0001808000640000000000023238413e1e14f7404839a0834000000000000000075f000000000076e0001020b5c46812c0d149f667614b815c00038e0001e4ceb62501c8041c0000f03800eac0000001f296b40005c209700b10327b8208104cbb27b43e7000038653b034000000049e000000000075412f80000000000001f801fa0c9234a03c64e4d60001bdc8be1ce1f700380000000001ab8a0413a16003f000000028880000004742ce1c985cc0e100000000000000001320f904542ec00000000003e80afc00051f00007700004f0000000078e23b13c9ffce8862f0ad181409c00000000005ea24040000000002fd2f59e58a567de3eb87184ae0b004b074463e56a3b2893c43065d0bb9a6c30e31811585f020c01e17d991080e32c03583085d456f000135c0005f40001dac0001100000000a86000000000037c59121f8eb071469000001b800000000018c8000000000000000000035e06f41643d73a000005b43160d300000000000000ab00004a7000021c0000000000b64dec3bd06d800000000000018a40002c300000000000c0000000098e0001340e980005e213b0eb800000000000010100003140dbc00000000000000003801700d9c90800100100100400000000100200400d00300100000500000200400200000000000100300100100200000000000300a00a00200000600900300000100000000200000100000400000000500800000100200600200300000200000400200000300100900900000000000100000300200b00200000200200100000400400100000700100000000000000300200000300c00100000500200200200600000000700100700000000500000200200300200100d00000f00400000300000000800300100100500000400100200100000200000000500300000000900100100300100000100200300000000000000100900300100300400300000000000300200000000000a00000300000800300600000000300000500300000000100300000200100200000800600000000200100000100100600100000900100100000100400000100001000000000400300200500000000000d00500000001200000900600100100000000400000000200200300000200f00000400100000501c01400000000000100000001400000000000600100000100000600700000200100400000000600200000000000000500200100100100100100800000400700800000300100900300500b00000300000800400401200600100000000300100000000000100100400200100
  | 11 => 0x6a118988cc0000003b7800000000023f12d899806a000195400022d00000000000000000f3c0000000000878000000405857885e0002aa00000005aa000131000034c00005d03da0a80b98000f6a15d1e80c280003022a285040002de0000000eaa21933a0d0501c1a300011245441af0001ce40aa000000000000057307d800000000037080003c600000014740007cb1661924bc6220283800000031e0000a948a46ef35d8000000000000000000000000000000000000000000ce66190b414544f60000000e7c0420003e3000000000011e80000000003900000b6e00000000000005a81388000c7c35a2a380000000000001a18000792000000052c2a81ed099808200000013a896a43b00000000006a4000023009643e2b3816c08c5bd00006509a600019700000000ad1b30000d1e000000000000061c2009d8c0001bc21480000007b223b9fb01b0724000000032200021e1280a9c705000080c5b021d2691ce000012900200001721801d49738b1612f27701d8c1831900000000004240000000c12000000189c0006c528317b022e000000000000000000000007c600033e800000042b071145cee080a1dd980c00006732a0adc87018509d80000001822e31ea496626526e9de800046600009c000000000014700004482d116ccb1e09313e82cc95226b00019ac08451009815088284b7352969c67e251013800033e0002d09df457c667126143463600015a96ec00000027f16c000046700014e80003880f8086c00e159000000092e0001f015f800000025e10081ac03c00505e8388305294800000062100000003b41113680000000000000000008871410080006242f3000069cd0a000000032cc9801d06410a000071c00012b00000000000000fb0000162000105419d0001b38c8205200017e8000000053101000028127400000007dc3d320ac000000226800000000000001d07ac71d0b800000000002590420a360000001d181b46b00000edc00024b205843400081629615580007523ac8000000000000000000000000000006901601138a001fe44e07480009126d90001fb80000000000310b124832e29170000000000000000063d00000007f80d1000000000000025e913cbd272214c0c8400000032f0000da2719000000084c00003f0e8cef274200000000000000000000000000276000000026a000000062e3ea000000000000014e186c0007290001140dbc00000007480a205400003ac77403933600006f40002991eb80000000001d283ae5192799bd4d300000000bb00000000000000f2a000178800069a6f80e01a380001ac00a1fe083c6e92c6967d0483c23349028f9a6f124a98cc7ce8252648db45b82c93a80a3c4a800800018e0a6272f1b4994c0000000001b540004420000000b88356000185879a594219
  | 12 => 0x300000004900000e9cdfa00035e8f70000000000000000000000000007f60000000000fcc3700001678000000000000100a4ce2e699f80000003a09058bf20000000c24bc06dc305934005a1a93e000000000f9000000000000032d00004c4000000000058c2ae09b06d8be080c06c9f14000331000000000000000000000000001691d24af00003f18000fc83ef1c90000c727b32ae1e88c26575123800103c5fb3f5000051835422510741f05d50c5a07c000006066975000040c00000000000001b60000e9e1b100000000003380000000a40000000180800000014905e443e000085800084457a0000000e1273d000000028409d0000000000000000000000000008b000077c216000028837400007000004de4e000016b0acc4553d60fdc3ce1fa39900004c209516b00004780781599a1c3f60000000e64d6c6dd1470000d8600000000000000003db0e7800000027c80000000002ad1d846ec625156897800000023c9e400001b932c0000de881433284480003890000000abe6ff33896040006ed00001805aa00037400002042a436f89fcdae00020d92042646f00ea9fc067a3370000d5400045a2809e64c4807a09c124c1e459a00000005de0003a9800000000000014f800003f3008694dca7f140187ccf2e00000007640b200031b1fc80003a232b0000fd20000c703a86162c20000bc800042a40498fc0001e410a80000003573bd9f3090a5c90b50ffc420063000000000016f11083d04ba32d01b1ccce1e0002108000e8600000000000004470001038ab26952630d78f7e04a0a3858839875727d12306784e60000000000000000000000010a0000000000000000026400000000012b8b4a2e400000005200000d996e40000003d89cb40bc02539a89b494a038298000000000000017fc0002cf000000061062d3d800000000ae1ca137000000032c93f026200039f999035a59b2c39cf000000000000007bc2b626d800044a0923720000d0800011900001382ca0000000fd0000000142836a0f1000000075400010219f0000000000000000076215a1c10bca7aa1688000c2e0000000184f066b31e20e60fb44203df0000b3a00000002443a80002b188900000001b88000afa00035000000000001ae90b00000900000bb800000000001c000000000016ac0007120001e44000608117000000023e0000000a7879a1c3800000000000000005326352da8000aec3240000e18000000253059824c0b62491e60bfc7563a3883c0000001da9b8800024100000000000003bc09c8cae6633fb08c4f4e1f904d8a3436473b25d00000000ee0000000aca17b0000000000000069975859c0001c6800000000000014248606ba0000000950000000080802c15f1ad80000005fc0000000df63970b480000004880cd9b1caa6000000000000
  | 13 => 0xa866100009dc740391271800043460e00006e0bec00000000000000000b680009c40003250b506f810302c1aa40f258e3889e34000050000049000000000000000000000001a58000000000028c00062223202100000000000000000175000000028026405d16102f003e0001880e4252d1bb800000000d2049970d3a00009a000000000024b0000b06001000014c00041104f98484a64eb1bf119400000000000000007160000f987fc00040d0000000000000000000015b2521e0800076a0000000be45de0900000000000000140061a2fe0000a0800039b00005901680000001f640004600e68000fda2051de0a6ca4478c32fa0049320001048000fba2bb0000538b18236172a0080000000000000db400000000000000000001e1000010c03f9094fa400015004dc9aa000131800032a00031707fc00048f000085061e0003a7052000000000000000005b60001e94f14000000000091c00007400000000001bd800019881800000002a200034e08e86a40002de094818a412000011c30255e00000007c800006f0000000000000000005e00029500000005d22bd800000a34b0001178ec06b90b600d00002e1334000000000032900001760001748000e6c2230000098d8200025d860c9305271f8804800053300000000000003c7075800000000000007ec00003e80000003620001cc000000000000000005281ac0bc075e3cb06912ac77054c00006acc0e3a11ef910c1520943de13dcf5e2a108e0a20d340000000ac8c6e5cb000045066a3790001e2422614c2d9000059074c00000000001a2000072500e0002e80ce80000000000000a1800000004ccc740000000a240002692d0205cc2a0002dd19b81e62a337704e416e0000000000eb40002610e9000059800000000000000000000bc200000009f86ca0000f4039846864222e9a00c4661f0001c3400021228a00005620000fe023ca1e000084800000065b00010f40000000b8800000000000006210444e421700009fa000000000000000000000003be00000000000008230000000000000000000072a3853ea8aac05654d0a50be0a720002581e1cd703602ed00000000003dc80002440000001ab00000002351ad4c8e6992b118400005f83e48c302c21b42c280000000000200000cde38c20c0fb4fc25231fc1c4c9460001680efc8f82380fa000000000000006a800034a2e60000fa20002a780008d6000000000000052f3ba00b83a600016394b880000000000000000e4000000064c0be268800047e00017692fc00030e00115741ea00015811e800000030a1dc49b44402b20090fbe7451f81eece303e8067800078a78f00018d015815c0000000ea2000000085c000023000032876407137f003000000013a8000ca25520000000000000000000000000035680007ba20c3c
  | 14 => 0xea000026c00016088f005640e1ea000000029e8d44bbe5c73ce07981be00040e800000031c06388700000001fe800000011d0000000fe60003d0000000000000012f81ec0000001fd0f820002a580000008280529ce80000b10000000000000000000005200009599e42dc29300020a40000000000d7c00000000000000000000000000a801de00c843ca1077f397070400063c3ae800000000000000000003ad0000fac00000038b85181060000260bdc5ba05c0e413d83ec0000fb8000ac26460618000a6c1e11e9000002648d03a8000aee08000004f83486ca2d798b06fa00029a8558a241e035b80007726cf04f006c7c25a9188000024a00000000007980002e19c6c0001b73f780000006c217c8898b9e6b11ba0000f3e6f32cb800099e00016980003e40000000d1000000011804d406239a3200f5084e0003240ae4af276818a8c1c0005e41e0872c0002450000da069200029f9eac25400000000000000000000000a4a0001f98000fb60000bf193841000019b000064400000000000000002fb8484000000000000000000012d000000000041300001d800000000000000000000000000000000209c00000006e80000005e70001c9496801800001cc2a00000000000cd40002629498cc472a0000a7800000000000000004ef15d105410c7ad2510d9029a1453fb9c380000000001be431e4f430792b4c9e5dd30f0f442d637300000002ec186000154400038f2820000bb81f121893949940000940dac0000004090dfc00000000000000000000000114000000183000045875e36303b400024600000000000002c800000001ae000000000004d12c8000b2a45816587f40000003268f8840c0000000bfc340000000000041400000b9f0cdb60000458000b0c57100a8414bcc000107000000000003480000001e5203000049075c06a0a18c306752d200000003400000000e340003649f1c000000111080076c0003301c081c60001c18f382885b80000000000000000152800025600007bc11400000019c06a60000001704d2600008a8000000304000054c3300003600a9c000000000000000011e000000000000009392680740a035f80000000000000d0c7048133fe800000071e325927c0001c700007d40000c100009e00de5ef25c8658be64913c5800039e03b27480881560f717111d48b26a80ec0e7086e00037380000003340001cc40000003760b9c00033300000000000000000000d908150000000d2e7640d41c1c9f000018d1e8ca6e3db0000e94c605693918cec2b008e0c90b1400000018a000083e00000011f4000453000175d03600022d95b4b145b43c0825c9da1ee0e5000021c2551e3000010242d26180005d61232cc8198b7e70c34a1c0ccf600023080002ae6eb000000c40e3031a11f080000001551c2cd
  | 15 => 0x48719f13c800000000000000004173591cac0003783960000000000000000000022823800000000003de88440220000000000afe3291fa882cb7c00000000009ea0003bb8a280000000000000000000000000000000005e83f83b60001578024000534220800000077c4088000b264710630c8c79400036601f078600034f80005e81c522b8be85f829d3ac0ec43347693e9903446e000273a01825a32b2fe80004dc48b0c61658a2c2c121c990c0001010f500000001c2000000000009a000000000000000000000000000001114b9400022600000001a13fd0000ac034600000000000000b90524cfe000000000000068c37d10140862670000fe80e47f909e800091443a26a000072c00005500000000000df9c18868588000132c000000000000000000016f8000d246a607280000004330000b6c16a49d2018000dcc4d81b90000ab600005e006800000000000000000000000000e4e000000000000062a341000000018a4020ca017052400800000004a12a48000f3a41c00011b80b44f10000000ae408800014604b83d30180ec09fe71500002080005db3700000cf00000001c40888000032000000000014a80001de46f1e491880003813b91ba8cee00000000a00003f234680005346b43698000000000000059c000000000000000000000000009280000c8164850e0000f589cca1c00000000000000a73539208f0046c000118c6b200000000000004c120795ac2865501218000ffc68a00000000006d200000000000000000ae00006810001dd8e9a325000000000000000000000001f800000000002bd23687888ec000000061000025b000168c130000000003c3126aa0001068b620000001e6c0004860000000ece1b0410000000060039b9f9c0380003b320840000001e00000d7c4af1e40b340c431107d00002aa00002f8e4ca825050000000a8c0002fa853cdf80d000012700000003e2000000000000018687aa0000000000000000115000010a000000046849c4cd0000000a7051e23d800000000030680000000004080d38d160000000000f420d70000cc80000002551f940000000001dd400000025c000000036e2d3000000050b0000000c0c2910101e786d47ca0001d2c8ac00000007a433800001a8c74eda00000000000006ab00015d0000000000000000000000000001420491b099c85161bb00000000000000000a7cc220001ec800000068900000002ca0000001c7c5ae70a371807ca2600028d07740005f100008bc00000000000dc0ee05d1ce8a500007fb0001edc49a5682708000db00ce31300000000000000bd8d220323fa80000003390368f60f9e00000015b023e000080194011247f08d84b050a5e81ba80008a21fe25890d42a400b1ae191400000000000001aa5ed01e8a987e828400000000000dc0
  | 16 => 0x74000080d26c8cc0fc40000000000a063b400000004940000001bc88e67eb2231e20d9a0003ca0000fac7fc174000090002a000000000000030e8664896419000000000049b2e41a8800077e00015b82fa0000b180000003f900018c4000000197908c0004360001e90dac00000015f07d80002e00af01480002e884f0e102353a4174c00000000000000000000cb8000c1430000018ec68e13f0000d8cab000000000003d800014180009be5572f500002fe00034180000000001220550a42604000000017e0003440fa400069e1a80b8c000118000000000018d3621f500002490c980000007013b999e8ccc000000000000000000008e40005ee000000000000026f01ec0000001d980000000000001ca00005802390000ed80000360000d460e70000000066000000000000000000008a4
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc72594100067f42594100067e42594100067d42594100067c425941001e7f715941001e7e715941001e7d715941001e7c715941001e7f415941001e7e415941001e7d415941001e7c415941001e7f315941001e7e315941001e7d315941001e7c315941001e7f215941001e7e215941001e7d215941001e7c21594100267f70594100267e70594100267d70594100267c70594100267f40594100267e40594100267d40594100267c40594100267f30594100267e30594100267d30594100267c30594100267f20594100267e20594100267d20594100267c20594100267f10594100267710594100267e10594100267a10594100267d105941002675105941001e7910594100267c10594100b4ff7598c10014fe7598c10004fd7598c100b4fc7598c100b4ff7498c1000cfe7498c10004fd7498c100b4fc7498c100067f5498c100067d5498c10024fe7398c10026de7398c100b6de4398c10006dd4398c1003cfe7298c10004fd7298c1001cfe7198c1001cfc7198c1001ede3198c1001edc3198c10024fe7098c10024fc7098c10026de3098c10026dc3098c10026f71098c10026f51098c10004ff7558c10014fe7558c10004fd7558c10014fc7558c10004ff7458c1000cfe7458c10004fd7458c1000cfc7458c100067f5458c100067d5458c10024ff7358c10026df7358c10006de4358c10006dd4358c10004ff7258c1003cfc7258c1001cff7158c1001cfe7158c1001cfd7158c1001cfc7158c1001ede3158c1001edc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10004ff7558810014fe7558810004fd7558810014fc7558810004ff745881000cfe7458810004fd745881000cfc74588100067f54588100067d5458810004ff73588100b4fc7358810024ff7258810026ef7258810006ee4258810006ed425881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026f510588100b4ff76cc810024fe76cc810004fd76cc810024fc76cc8101b67e65cc8100067d65cc8100b6de63cc810006dd63cc81003cff768c810024fe768c810004fd768c810024fc768c8101ae7e658c8100067d658c81003eee628c810006ed628c810004ff764c810024fe764c810004fd764c810024fc764c8100057f754c8100357c754c81019e7e654c8100067d654c810006de634c810006dd634c81003eee624c810006ed624c81003cff760c810024fe760c810004fd760c810024fc760c8100357e750c8100057d750c8101867e650c8100067d650c81002dbe740c810005bd740c81001df6710c810005f5710c810025fa700c810005f9700c810
  | 1 => 0xc51021df5750c51000777650c51020774650c51001df7740c510215f5740c510007b7640c5101ffb4640c5101ff77540c5101ff75540c51020df6730c51001fd6730c510006f7630c510006f5630c510005f5720c510025f6700c510025f4700c51001ef7600c51001ff3600c510207f2500c510207f1500c5101fff2400c5101fff1400c510024fe76c8510024fc76c851004d7e75c85100057d75c85100067f65c85101367c65c8510045be74c8510005bd74c8510006bf64c851012ebc64c8510006ef62c851003eec62c8510025fa70c8510005f970c851001ff010c8510005f6768851001ef6768851001df775885101f5f575885100077765885101e774658851001df774885101edf57488510007b764885101dfb464885101df7754885101df755488510005f6738851001df47388510006f76388510006f563885101cdf5728851003ef6628851003ef46288510025f67088510025f4708851001ef7608851001ff360885101e7f250885101e7f150885101dff240885101dff14088510024fc76485100067f65485101167c6548510006bf644851010ebc6448510006ef624851003eec6248510005fb7048510025f87048510025f4764851003ef47648510024f476485101d5f775485101d5f575485100077765485101c77465485101cdf774485101cdf57448510007b764485101bfb464485101bf7754485101bf755448510005f67348510005f47348510006f76348510006f5634851001df7724851001fe77248510007e7624851003ef6624851003ef46248510007e462485101bfe642485101bfe54248510007f37048510025f67048510025f47048510007f07048510025f0704851001ef7604851001ff360485101c7f250485101c7f150485101bff240485101bff1404851001cfe76cc1100067f65cc1100f67c65cc110006bf64cc1100cebc64cc110006df63cc1100b6dc63cc11001df671cc110005f571cc1100b4ff764c110004fd764c11001cfc764c1100067f654c1100de7c654c110006bf644c1100d6bc644c110006df634c110006dc634c110005f7714c11001df4714c110027d8304c110027f0104c11001cfe76c811001cfc76c81100067f65c81100ae7c65c8110006bf64c81100a6bc64c8110006ef62c811003eec62c811001df671c8110005f571c8110027f010c811003cff7648110004fd764811001cfc76481100067f654811008e7c6548110006bf6448110086bc6448110006ef624811003eec6248110005f7714811001df471481100067f74594100047f74594100067e74594100067d74594100047d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067
  | 2 => 0x24fc70d891004d7e75989100057d75989100067f65989100067c6598910045be7498910005bd7498910006bf6498910006bc6498910006ef62989100057f755891004d7c75589100067f65589100067c6558910005bf7458910045bc7458910006bf6458910006bc6458910005df7358910005dc7358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891000cfe7458910004fd745891000cfc7458910006bc745891000cbc74589100067f54589100067d5458910004ff7358910006df7358910004df73589100b4fc7358910006dc7358910004dc7358910006ef7258910006ee4258910006ed4258910004ff7158910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc641891003eee6218910006ed62189100b4ff76cc910004fe76cc910004fd76cc9100b4fc76cc9100067f65cc9101b67c65cc910006bf64cc91018ebc64cc910006ef62cc91003eec62cc91003cff768c910004fe768c910004fd768c91003cfc768c9100067f658c9101ae7c658c910006bf648c9101a6bc648c910006df638c910006dc638c91001df6718c910005f5718c910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c91004d7c754c9100067f654c91019e7c654c910006bf644c910196bc644c910005f7714c91001df4714c910005fb704c910025f8704c91003cff760c910004fe760c910004fd760c91003cfc760c91004d7e750c9100057d750c9100067f650c9101867c650c910045be740c910005bd740c910006bf640c91017ebc640c910006df630c9100b6dc630c910006ef620c91003eec620c91001df6710c910005f5710c910025fa700c910005f9700c910024fe76cc5100067f65cc5101767c65cc510006bf64cc51014ebc64cc510006df63cc5100b6dc63cc510025fa70cc510005f970cc510025f676cc510006f676cc510024f676cc510235f775cc510235f575cc5100077765cc51022f7465cc51020df774cc51020df574cc510007b764cc510227b464cc5102277754cc5102277554cc51001df673cc510006f763cc510007d763cc510006f563cc510007d463cc510227d643cc510227d543cc510005f572cc510025f670cc510007f270cc510025f270cc510007f170cc510025f470cc51001ef760cc51001ff360cc51022ff250cc51022ff150cc510227f240cc510227f140cc510024fc764c5100057f754c51004d7c754c5100067f654c51015e7c654c510006bf644c510156bc644c510006df634c510006dc634c51001fd4314c510005fb704c510025f8704c51001ff0104c510005f6760c51001ef6760c51001df7750
  | 3 => 0xd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d911023ebf71d9110246be71d9110046bd71d9110246bc71d9110006bf51d9110246be51d9110006bd51d9110246bc51d9110246be31d9110246bc31d9110246be21d9110246bc21d9110246bf70d911023ebe70d9110046bd70d911023ebc70d9110006bf50d911023ebe50d9110006bd50d911023ebc50d911023ebe30d911023ebc30d911023ebe20d911023ebc20d9110246bf10d911023ebe10d9110046bd10d911023ebc10d91100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d10004ff74d8d1000cfe74d8d10004fd74d8d1000cfc74d8d100067f54d8d100067d54d8d1003cfe72d8d10004fd72d8d10006f571d8d1004d7e7598d100057d7598d100067f6598d100067c6598d10045be7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d100b4ff7598d10014fe7598d100b67e7598d100147e7598d10004fd7598d100b67d7598d100047d7598d100b4fc7598d100b4ff7498d1000cfe7498d100b6be7498d1000cbe7498d10004fd7498d100b6bd7498d10004bd7498d100b4fc7498d100067f5498d100067d5498d100b4fe7398d100b6de4398d10006dd4398d1003cfe7298d10004fd7298d10004fd7198d100b6f57198d10004fd7098d100b6f97098d100057f7558d1004d7c7558d100067f6558d100067c6558d10005bf7458d10045bc7458d10006bf6458d10006bc6458d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1000cfe7458d10004fd7458d1000cfc7458d10006bc7458d1000cbc7458d100067f5458d100067d5458d10006df7358d10006de4358d10006dd4358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10006dd6318d100b4ff7518d10014fe7518d10004fd7518d100b4fc7518d100b4ff7418d1000cfe7418d10004fd7418d100b4fc7418d100067f5418d100067d5418d100b6de7318d1003cfe7218d10004fd7218d1001cfe7118d1001cfc7118d10024fe7018d10024fc7018d1003cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910004ff75d8910014fe75d8910004fd75d8910014fc75d8910004ff74d891000cfe74d8910004fd74d891000cfc74d89100067f54d89100067d54d89100b4fe73d8910004fd73d891001cfe71d891001cfc71d8910024fe70d8910
  | 4 => 0x8a10026f51058a100b4ff76cca10024fe76cca10004fd76cca10024fc76cca100b6de63cca10006dd63cca1003cff768ca10024fe768ca10004fd768ca10024fc768ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca100057f754ca1005d7c754ca10006de634ca10006dd634ca10005fb704ca10025f8704ca1003cff760ca10024fe760ca10004fd760ca10024fc760ca1005d7e750ca100057d750ca10055be740ca10005bd740ca1001df6710ca10005f5710ca10025fa700ca10005f9700ca100b6de63cc610006dd63cc610025fa70cc610005f970cc6100057f754c61005d7c754c610006de634c610006dd634c610005fb704c610025f8704c61005d7e75c86100057d75c8610055be74c8610005bd74c861003eee62c8610006ed62c8610025fa70c8610005f970c861003cff764861003eee6248610006ed6248610005fb7048610025f8704861004d7e76d951004e7e76d95100147e76d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d951024f7771d951004f7471d95100077641d95100077541d95102577b70d951004f7870d95100077a40d95100077940d95102577b10d951024f7610d951024f7410d95102577810d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d951024e7f71d95102567e71d951004e7d71d95102567c71d95100067f41d95102567e41d95100067d41d95102567c41d95102567e31d95102567c31d95102567e21d95102567c21d95102567f70d951024e7e70d951004e7d70d951024e7c70d95100067f40d951024e7e40d95100067d40d951024e7c40d951024e7e30d951024e7c30d951024e7e20d951024e7c20d95102567f10d951024e7e10d951004e7d10d951024e7c10d9510045be76d9110046be76d911000cbe76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d911023fb771d9110047b471d9110007b651d9110007b551d9110247bb70d9110047b870d9110007ba50d9110007b950d9110247bb10d911023fb610d911023fb410d9110247b810d9110006bf75d91100063f75d9110006be75d9110006bd75d9110006bc75d91100063c75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006b
  | 5 => 0x4ff7258f1003cfc7258f10024fc7158f1001ef47158f10024f47158f1001ede3158f1001edc3158f1001ef43158f1001ef62158f10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b1000cfe7458b10004fd7458b1000cfc7458b100067f5458b100067d5458b10004ff7358b100b4fc7358b1001eef7258b10006ee4258b10006ed4258b10024fc7158b1001eee2158b1001eec2158b100b4ff76ccb1001cfe76ccb10004fd76ccb1001cfc76ccb1001df471ccb1003cff768cb1001cfe768cb10004fd768cb1001cfc768cb1001df6718cb10005f5718cb10004ff764cb1001cfe764cb10004fd764cb1001cfc764cb100057f754cb1006d7c754cb10005f7714cb1001df4714cb1003cff760cb1001cfe760cb10004fd760cb1001cfc760cb1006d7e750cb100057d750cb10065be740cb10005bd740cb1001df6710cb10005f5710cb10025fa700cb10005f9700cb1001df576cc710006f576cc710285f775cc710285f575cc71027df774cc71027df574cc7102777754cc7102777554cc71001fd673cc71001ef763cc710006f563cc710277d643cc710277d543cc710005f572cc710025f670cc710025f470cc71001df77648710006f7764871026df7754871026df57548710265f77448710265f5744871025f77544871025f755448710005f67348710005f4734871001ef76348710006f5634871001fe7724871003ef6624871001ef4624871025fe6424871025fe54248710025f67048710025f470487100b6de63cc310006dd63cc31001df671cc310005f571cc310006de634c310006dd634c310005f7714c31001df4714c31003eee62c8310006ed62c831001df671c8310005f571c831003cff764831003eee6248310006ed6248310005f7714831001df471483100b4ff7598e10014fe7598e10004fd7598e100b4fc7598e100b4ff7498e1000cfe7498e10004fd7498e100b4fc7498e100067f5498e100067d5498e10026de7398e10006df5398e100b6dc5398e100b6de4398e10006dd4398e1003cfe7298e10004fd7298e10024fe7098e10026de3098e10026dc3098e10026f71098e10026f51098e10004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e1000cfe7458e10004fd7458e1000cfc7458e100067f5458e100067d5458e10026df7358e10006df5358e10006dc5358e10006de4358e10006dd4358e10004ff7258e1003cfc7258e10024fc7058e10026de3058e10026dc3058e10004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7458a1000cfe7458a10004fd7458a1000cfc7458a100067f5458a100067d5458a10004ff7358a100b4fc7358a10026ef7258a10006ee4258a10006ed4258a10024fc7058a10026ee2058a10026ec2058a10026f7105
  | 6 => 0xe7558420004fd7558420014fc7558420004ff745842000cfe7458420004fd745842000cfc74584200067f54584200067d5458420004ff73584200b4fc7358420026f77158420006f75158420006f65158420006f55158420006f45158420006f74158420006f64158420006f54158420006f4415842003ef7215842003ef42158420024ff7058420024fd7058420026f61058420026f41058420006f77558420006f67558420006f57558420006f47558420006f77458420006f67458420006f57458420006f47458420006f75458420006775458420006f65458420006f55458420006755458420006f45458420006f77358420006f67358420006f57358420006f47358420006f75358420006f65358420006f55358420006f45358420006f74358420006f64358420006f54358420006f4435842003ef7725842003ef6725842003ef4725842003ef7525842003ef6525842003ef5525842003ef4525842003ef7425842003ef6425842003ef5425842003ef4425842003ef7325842003ef6325842003ef5325842003ef43258420026f77058420026f67058420026f47058420026f75058420026f65058420026f55058420026f45058420026f74058420026f64058420026f54058420026f44058420026f73058420026f63058420026f53058420026f43058420026f72058420026f62058420026f52058420026f420584200b4ff76cc420024fe76cc420004fd76cc4201767e65cc4200067d65cc42014ebe64cc420006bd64cc4200b6de63cc420006dd63cc42001ef661cc420006f561cc42001cff768c420024fe768c420004fd768c42016e7e658c4200067d658c420166be648c420006bd648c420006de638c420006dd638c42001ef6618c420006f5618c420025fa708c420005f9708c420004ff764c420004fd764c420024fc764c4200057f754c42007d7c754c42015e7e654c4200067d654c420156be644c420006bd644c420006de634c420006dd634c420005ef724c42003dec724c42001ef6614c420006f5614c42001cff760c420024fe760c420004fd760c4201467e650c4200067d650c42013ebe640c420006bd640c4200b6de630c420006dd630c42001ef6610c420006f5610c4200b4ff7598f10014fe7598f10004fd7598f100b4fc7598f100b4ff7498f1000cfe7498f10004fd7498f100b4fc7498f100067f5498f100067d5498f1001ede7398f100b6de4398f10006dd4398f1003cfe7298f10004fd7298f10024fe7198f1001ede3198f1001edc3198f10004ff7558f100067f7558f100047f7558f10014fe7558f10004fd7558f10014fc7558f100067c7558f100147c7558f10004ff7458f1000cfe7458f10004fd7458f1000cfc7458f100067f5458f100067d5458f1001edf7358f10006de4358f10006dd4358f10
  | 7 => 0x8c20026dc4098c20026df2098c20026de2098c20026dd2098c20026dc2098c20026df1098c20026de1098c20026dd1098c20026dc1098c20004ff7558c20014fe7558c20004fd7558c20014fc7558c20004ff7458c2000cfe7458c20004fd7458c2000cfc7458c200067f5458c200067d5458c20024ff7358c20026df7358c20006df5358c20006de5358c20006dd5358c20006dc5358c20006df4358c20006de4358c20006dd4358c20006dc4358c2003cff7258c2003cfe7258c2003cfd7258c2003cfc7258c2003ede3258c2003edc3258c20004ff7158c2001cfc7158c20024fe7058c20024fc7058c20026de3058c20026dc3058c20026fa2058c2003ef92058c20006df7558c20006de7558c20006dd7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c200065f5458c20006de5458c20006dd5458c200065d5458c20006dc5458c2003edf7258c2003ede7258c2003edd7258c2003edc7258c2003edf5258c2003ede5258c2003edd5258c2003edc5258c2003edf4258c2003ede4258c2003edd4258c2003edc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df5158c20006de5158c20006dd5158c20006dc5158c20006df4158c20006de4158c20006dd4158c20006dc4158c2003edf2158c2003ede2158c2003edd2158c2003edc2158c20026df7058c20026de7058c20026dd7058c20026dc7058c20026df5058c20026de5058c20026dd5058c20026dc5058c20026df4058c20026de4058c20026dd4058c20026dc4058c20026df2058c20026de2058c20026da2058c20026dd2058c2003ed92058c20026dc2058c20026df1058c20026de1058c20026dd1058c20026dc1058c2001ef7759842001ef6759842001ef5759842001ef4759842001ef7749842001ef6749842001ef5749842001ef47498420006f75498420006775498420006f65498420006f55498420006755498420006f4549842001ef7739842001ef6739842001ef5739842001ef47398420006f75398420006f65398420006f55398420006f45398420006f74398420006f64398420006f54398420006f4439842001ef7729842001ef6729842001ef5729842001ef4729842003ef7529842003ef6529842003ef5529842003ef4529842003ef7429842003ef6429842003ef5429842003ef4429842003ef7329842003ef6329842003ef5329842003ef43298420026f77098420026f67098420026f57098420026f47098420026f75098420026f65098420026f55098420026f45098420026f74098420026f64098420026f54098420026f44098420026f73098420026f63098420026f53098420026f43098420026f72098420026f62098420026f52098420026f42098420004ff7558420014f
  | 8 => 0x67f41594200067e41594200067d41594200067c415942003e7f215942003e7e215942003e7d215942003e7c21594200267f70594200267e70594200267d70594200267c70594200267f40594200267e40594200267d40594200267c40594200267f30594200267e30594200267d30594200267c30594200267f20594200267e20594200267d20594200267c20594200267f10594200267e10594200267d10594200267c1059420006bf7559020006be75590200063e7559020006bd75590200063d7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006be5359020006bd5359020006bc535902003ebf725902003ebe725902003ebd725902003ebc725902003ebf525902003ebe525902003ebd525902003ebc525902003ebf325902003ebe325902003ebd325902003ebc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf5159020006be5159020006bd5159020006bc515902003ebf215902003ebe215902003ebd215902003ebc2159020026bf7059020026be7059020026bd7059020026bc7059020026bf5059020026be5059020026bd5059020026bc5059020026bf3059020026be3059020026bd3059020026bc3059020026bf2059020026af2059020026be2059020026bd2059020026ad2059020026bc2059020026bf1059020026be1059020026bd1059020026bc10590200b4ff7598c20014fe7598c20004fd7598c200b4fc7598c200b4ff7498c2000cfe7498c20004fd7498c200b4fc7498c200067f5498c200067d5498c20024fe7398c20026de7398c20006df5398c200b6de5398c20006dd5398c200b6dc5398c20006df4398c200b6de4398c20006dd4398c200b6dc4398c2003cfe7298c2003cfc7298c2003ede3298c2003edc3298c2001cfe7198c20004fd7198c20024fe7098c20024fc7098c20026de3098c20026dc3098c200b6df7598c20006de7598c20006dd7598c200b6dc7598c200b6df7498c20006de7498c20006dd7498c200b6dc7498c20006df5498c200065f5498c20006de5498c20006dd5498c200065d5498c20006dc5498c2003edf7298c2003ede7298c2003edd7298c2003edc7298c2003edf5298c2003ede5298c2003edd5298c2003edc5298c2003edf4298c2003ede4298c2003edd4298c2003edc4298c200b6df7198c20006de7198c20006dd7198c200b6dc7198c20006df5198c20006de5198c20006dd5198c20006dc5198c20006df4198c20006de4198c20006dd4198c20006dc4198c2003edf2198c2003ede2198c2003edd2198c2003edc2198c20026df7098c20026de7098c20026dd7098c20026dc7098c20026df5098c20026de5098c20026dd5098c20026dc5098c20026df4098c20026de4098c20026dd409
  | 9 => 0xe7418d20004fd7418d200b4fc7418d200067f5418d200067d5418d200b6de7318d20006df5318d200b6dc5318d200b6de4318d20006dd4318d2003cfe7218d2003cfc7218d20006ee4218d20006ed4218d2001cfe7118d20004fd7118d200b6f97018d20024fe76cc920006df63cc9200b6dc63cc920025fa70cc920005f970cc920024fc764c9200057f754c92008d7c754c920006df634c920006dc634c920005fb704c920025f8704c920004ff75d8520014fe75d8520004fd75d8520014fc75d8520004ff74d852000cfe74d8520004fd74d852000cfc74d85200067f54d85200067d54d85200b4fe73d8520004fd73d8520006ee42d8520006ed42d8520024fe70d8520024fc70d8520006f761985200057f755852008d7c7558520005bf7458520085bc7458520005df7358520005dc735852001ef66118520006f56118520004fe76cc520004fd76cc5200b4fc76cc520025fa70cc520005f970cc520004fe768c520004fd768c52001cfc768c520006df638c520006dc638c520004ff764c520004fe764c520004fc764c5200057f754c52008d7c754c520004fe760c520004fd760c52001cfc760c520006df630c5200b6dc630c52003dee720c520005ed720c520025fa700c520005f9700c520024fe7688520006f7618852001ef46188520025fa7088520005f97088520024fc7648520006f7614852001ef46148520005fb7048520025f8704852003cfe76cc120006df63cc1200b6dc63cc12003dee72cc120005ed72cc120005fa768c120026fa768c1200277a758c12002779758c1202977b548c12029779548c12029df9738c1200b6fa638c1200b6f8638c12003dfa728c120025f8728c120026fb628c120027eb628c120297ea428c120297e9428c120027f2718c120027f1718c1200b4ff764c120004fd764c12003cfc764c120006df634c120006dc634c120005ef724c12003dec724c120027d8304c12003df8764c120006f8764c12003cf8764c12028f7b544c12028f79544c120025fb734c120027db734c120007db634c1200b6fa634c1200b6f8634c120007d8634c12028fda434c12028fd9434c120007eb724c12003dfa724c12003df8724c120007e8724c120026fb624c120027eb624c12028fea424c12028fe9424c120007db324c120007d9324c1200067f74594200047f74594200067e74594200067d74594200047d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067d43594200067c435942003e7f725942003e7e725942003e7d725942003e7c725942003e7f425942003e7e425942003e7d425942003e7c425942003e7f325942003e7e325942003e7d325942003e7c32594200067f71594200067e71594200067d71594200067c7159420
  | 10 => 0x8e20014fe7558e20004fd7558e20014fc7558e20004ff7458e2000cfe7458e20004fd7458e2000cfc7458e200067f5458e200067d5458e20026df7358e20006de4358e20006dd4358e20004ff7158e2001cfc7158e20024fc7058e20026de3058e20026dc3058e200b6de63cca20006dd63cca20025fa70cca20005f970cca200057f754ca2009d7c754ca20006de634ca20006dd634ca2003fcc324ca20005fb704ca20025f8704ca20004ff75586200067f75586200047f7558620014fe7558620004fd7558620014fc75586200067c75586200147c7558620004ff7458620006bf7458620004bf745862000cfe7458620004fd745862000cfc7458620006bc745862000cbc74586200067f54586200067d5458620004ff73586200b4fc7358620026f77158620006f65158620006f55158620006f64158620006f54158620024fc7058620026f61058620026f410586200b4ff76cc620024fe76cc620004fd76cc62001ef661cc620006f561cc620025fa70cc620005f970cc62001cff768c620024fe768c620004fd768c620004ff764c620004fd764c620024fc764c6200057f754c62009d7c754c620005ef724c62003dec724c62001cff760c620024fe760c620004fd760c62001ef6610c620006f5610c620025fa700c620005f9700c62001ef66188620006f56188620025fa7088620005f9708862001cff764862001ef66148620006f56148620005fb7048620025f87048620025fb764c220006fb764c2202a77b544c2202a779544c220027db734c220027db634c2200b6fa634c220026f8634c220027d8634c2202a7da434c2202a7d9434c22003dfa724c22003df8724c220007db324c220007d9324c220004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d20004ff74d8d2000cfe74d8d20004fd74d8d2000cfc74d8d200067f54d8d200067d54d8d20006df53d8d20006dc53d8d20006de43d8d20006dd43d8d2001cfe71d8d20004fd71d8d20006df6398d200b4ff7598d20014fe7598d20004fd7598d200b4fc7598d200b4ff7498d2000cfe7498d20004fd7498d200b4fc7498d200067f5498d200067d5498d200b4fe7398d20004fd7298d200b6ed7298d20006ee4298d20006ed4298d2001cfe7198d20004fd7198d20004fd7098d200b6f97098d200057f7558d2008d7c7558d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d2000cfe7458d20004fd7458d2000cfc7458d200067f5458d200067d5458d20006df7358d20004ff7258d20006ef7258d20004ff7158d2001cfc7158d20004ff7058d20006fb7058d20004fe7618d20006dd6318d200b4ff7518d20014fe7518d20004fd7518d200b4fc7518d200b4ff7418d2000cf
  | 11 => 0x4ff725843003cfc7258430026f77158430006f65158430006f55158430006f64158430006f541584300b6f731584300b6f43158430026f61058430026f41058430004fd768c430004ff764c4300057f754c4300c57c754c43003cff76c8430024fe76c8430004fd76c84300c57e75c84300057d75c84300bdbe74c8430005bd74c843003eee62c8430006ed62c843001cff7688430024fe7688430004fd768843001ef66188430006f56188430025fa7088430005f97088430004ff7648430004fd7648430024fc7648430005df73484300b5dc734843003eee6248430006ed624843001ef66148430006f5614843001cff7608430024fe7608430004fd7608430025fb764c030006fb764c030004fb764c0302af7b544c0302af79544c030025fb734c030027db734c0300b6fa634c030027da634c0300b7da534c0302b7d9534c0302afdb434c0300b7d8434c030006f9624c0300b7db324c030007d9324c0300b7db314c030007d9314c0300b4ff7598f20014fe7598f20004fd7598f200b4fc7598f200b4ff7498f2000cfe7498f20004fd7498f200b4fc7498f200067f5498f200067d5498f2003ede7398f20024fe7298f2003eee4298f20006ed4298f2003ede3298f2003edc3298f2001cfe7198f20004fd7198f20004ff7558f200067f7558f200047f7558f20014fe7558f20004fd7558f20014fc7558f200067c7558f200147c7558f20004ff7458f2000cfe7458f20004fd7458f2000cfc7458f200067f5458f200067d5458f2003edf7358f20024fc7258f2003ede3258f2003edc3258f20004ff7158f2001cfc7158f2003efa2058f2003ef92058f20004ff7558720014fe7558720004fd7558720014fc7558720004ff745872000cfe7458720004fd745872000cfc74587200067f54587200067d5458720004ff73587200b4fc7358720024fc725872003eee4258720006ed425872003ef7715872003ef7215872003ef421587200b4ff76cc72003cfe76cc720004fd76cc72001cff768c72003cfe768c720004fd768c72001ef6618c720006f5618c720025fa708c720005f9708c720004ff764c720004fd764c72003cfc764c7200057f754c7200ad7c754c72001ef6614c720006f5614c72001cff760c72003cfe760c720004fd760c72003dee720c720005ed720c7200b6de63cc320006dd63cc32003dee72cc320005ed72cc320006de634c320006dd634c320005ef724c32003dec724c3200b4ff7598e20014fe7598e20004fd7598e200b4fc7598e200b4ff7498e2000cfe7498e20004fd7498e200b4fc7498e200067f5498e200067d5498e20026de7398e200b6de4398e20006dd4398e2001cfe7198e20004fd7198e20024fe7098e20026fa7098e20024fa7098e20026de3098e20026fa3098e20026dc3098e20004ff755
  | 12 => 0xe42cc9302efcd42cc9300b7db70cc930025de70cc930025dc70cc9300b7d870cc9300b6df60cc930024fe768c9302dddd738c930006ef628c93003eec628c930025fa708c930005f9708c930024fc764c9300057f754c9300dd7c754c930006ef624c93003eec624c930005fb704c930025f8704c930024dc764c9300075f754c9302e75c754c9302dddf744c9302dddd744c9302d75f544c9302d75d544c930007cf724c930007cf624c93003ede624c93003edc624c930007cc624c93003ecc624c930007db704c930025de704c930025dc704c930007d8704c930004fe760c9300dd7e750c9300057d750c9300d5be740c930005bd740c9302cdde730c930005f6710c930005f5710c930025fa700c930004ff75d8530014fe75d8530004fd75d8530014fc75d8530004ff74d853000cfe74d8530004fd74d853000cfc74d85300067f54d85300067d54d8530006de43d8530006dd43d853003cfe72d8530004fd72d8530006f761985300057f75585300dd7c7558530005bf74585300d5bc7458530005ef7258530005ec725853001ef66118530006f56118530004fe76cc530024fe768c530006f7618c53001ef4618c530025fa708c530005f9708c530024fc764c5300057f754c5300dd7c754c530006f7614c53001ef4614c530005fb704c530025f8704c530004fe760c53001ef6610c530007d5310c530004fe76c8530004fd76c853003cfc76c85300dd7e75c85300057d75c85300d5be74c8530005bd74c8530005de73c8530005dd73c8530025fa70c8530005f970c8530004fe7688530004fd768853001cfc7688530006ef628853003eec628853001ef66188530004ff7648530004fe7648530004fc7648530004fe7608530004fd760853001cfc7608530005de7308530005dd7308530006ef620853003eec6208530025fa7008530005f97008530025de73cc130026df63cc130024fa76cc1302c77b54cc1302c77954cc130025fa73cc130026fb63cc130027db63cc1300b7da43cc1302c7d943cc130005f972cc1300b7db32cc130007d932cc130004ff7558830014fe7558830004fd7558830014fc7558830004ff745883000cfe7458830004fd745883000cfc74588300067f54588300067d5458830026ef7258830006ee5258830006ed5258830006ee4258830006ed42588300b6ef32588300b6ec3258830004ff715883001cfc7158830026df3058830026fa3058830026dd3058830026ee2058830026ec2058830004fd768c830004ff764c8300057f754c8300c57c754c8302bede634c8300b7cc324c830004ff75584300067f75584300047f7558430014fe7558430004fd7558430014fc75584300067c75584300147c7558430004ff745843000cfe7458430004fd745843000cfc74584300067f54584300067d5458430
  | 13 => 0x8630006f54158630006f44158630026f61058630026f41058630006f77558630006f67558630006f57558630006f47558630006f77458630006f67458630006f57458630006f47458630006f75458630006775458630006f65458630006f55458630006755458630006f45458630006f57358630006f75358630006f65358630006f55358630006f45358630006f74358630006f64358630006f54358630006f44358630006f77258630006f67258630006f57258630006f47258630006f75258630006f65258630006f55258630006f45258630006f74258630006f64258630006f54258630006f44258630006f73258630006f63258630006f53258630006f43258630026f77058630026f67058630026f47058630026f75058630026f65058630026f55058630026f45058630026f74058630026f64058630026f54058630026f44058630026f73058630026f63058630026f53058630026f43058630026f72058630026f62058630026f52058630026f420586301767e65cc6300067d65cc63001ef661cc63016e7e658c6300067d658c63001ef6618c630006f5618c630025fa708c630005f9708c63001cff764c6300057f754c6300ed7c754c63015e7e654c6300067d654c63001ef6614c630006f5614c630005fb704c630025f8704c6301467e650c6300067d650c63001ef6610c630006f5610c63003cff76c8630024fe76c8630004fd76c86300ed7e75c86300057d75c86301367e65c86300067d65c86300e5be74c8630005bd74c863001ef661c8630006f561c8630025fa70c8630005f970c863001cff7688630024fe7688630004fd76886301267e65886300067d658863001ef66188630006f56188630004ff7648630004fd7648630024fc76486301167e65486300067d6548630005df7348630005dc734863001ef66148630006f5614863001cff7608630024fe7608630004fd76086301067e65086300067d650863001ef66108630006f56108630025fa7008630005f97008630025f976cc2300b6f976cc2300277a65cc2300277965cc2302ff7b54cc2302ff7954cc230027da73cc2300b7da53cc2302f7d953cc230005f972cc230027f261cc230027f161cc230004ff75d8930014fe75d8930004fd75d8930014fc75d8930004ff74d893000cfe74d8930004fd74d893000cfc74d89300067f54d89300067d54d8930006ef52d8930006ec52d8930006ee42d8930006ed42d893001cfe71d8930004fd71d8930006ef62989300057f75589300dd7c75589300dd7e75189300057d75189300d5be7418930005bd741893003eee6218930006ed6218930005f67118930005f57118930004fe76cc930005de76cc930006de76cc9302cddf74cc9302cddd74cc9302ef5f54cc9302ef5d54cc93003ede62cc93003edc62cc9302efc
  | 14 => 0x67c74596300ee7f73596300ee7e73596300067d73596300ee7c73596300067f43596300067e43596300067d43596300067c43596300067f72596300067e72596300067d72596300067c72596300067f42596300067e42596300067d42596300067c42596300067f71596300067e71596300067d71596300067c71596300067f41596300067e41596300067d41596300067c41596300267f70596300267e70596300267d70596300267c70596300267f40596300267e40596300267d40596300267c40596300267f30596300267e30596300267d30596300267c30596300267f20596300267e20596300267d20596300267c20596300267f10596300267e10596300267d10596300267c1059630004ff7558a30014fe7558a30004fd7558a30014fc7558a30004ff7458a3000cfe7458a30004fd7458a3000cfc7458a300067f5458a300067d5458a30026ef7258a30006ee4258a30006ed4258a30004ff7158a3001cfc7158a30026df3058a30026dd3058a30026ee2058a30026ec2058a301b67e65cca300067d65cca30025f870cca301ae7e658ca300067d658ca3003eee628ca30006ed628ca30025fa708ca30005f9708ca3003cff764ca300057f754ca300ed7c754ca3019e7e654ca300067d654ca3003eee624ca30006ed624ca30005fb704ca30025f8704ca300ed7e750ca300057d750ca301867e650ca300067d650ca300e5be740ca30005bd740ca30007cd320ca30005f6710ca30005f5710ca30025fa700ca30005f9700ca3001ef7759863001ef6759863001ef5759863001ef4759863001ef7749863001ef6749863001ef5749863001ef47498630006f75498630006775498630006f65498630006f55498630006755498630006f4549863001ef77398630006f75398630006f65398630006f55398630006f45398630006f74398630006f64398630006f54398630006f4439863001ef7729863001ef6729863001ef5729863001ef47298630006f75298630006f65298630006f55298630006f45298630006f74298630006f64298630006f54298630006f44298630006f73298630006f63298630006f53298630006f43298630026f77098630026f67098630026f57098630026f47098630026f75098630026f65098630026f55098630026f45098630026f74098630026f64098630026f54098630026f44098630026f73098630026f63098630026f53098630026f43098630026f72098630026f62098630026f52098630026f42098630004ff7558630014fe7558630004fd7558630014fc7558630004ff745863000cfe7458630004fd745863000cfc74586300067f54586300067d5458630004ff725863003cfc7258630026f77158630006f75158630006f65158630006f55158630006f45158630006f74158630006f6415
  | 15 => 0xe5398c21006dd5398c210b6de4398c21006dd4398c2103cfe7298c2103cfc7298c2103ede3298c2103edc3298c2101cfe7198c2101cfc7198c2101ede3198c2101edc3198c21024fe7098c21004fd7098c21004ff7558c210067f7558c210047f7558c21014fe7558c21004fd7558c21014fc7558c210067c7558c210147c7558c21004ff7458c2100cfe7458c21004fd7458c2100cfc7458c210067f5458c210067d5458c2101cff7358c2101edf7358c21006de5358c21006dd5358c21006de4358c21006dd4358c2103cfe7258c2103cfc7258c2103ede3258c2103edc3258c2101cfe7158c2101cfc7158c2101ede3158c2101edc3158c2101ef62158c2103ef52158c21004ff7058c21024fc7058c21004ff7558021014fe7558021004fd7558021014fc7558021004ff745802100cfe7458021004fd745802100cfc74580210067f54580210067d5458021004ff73580210b4fc735802101ef6215802103ef5215802101efb7058021006fa5058021006f95058021006fa4058021006f9405802103efb205802103ef8205802101efb105802101ef810580210b6ef6298b3003eec6298b300b6ec6258b30004ff7558b30014fe7558b30004fd7558b30014fc7558b30004ff7458b3000cfe7458b30004fd7458b3000cfc7458b300067f5458b300067d5458b30024fc7358b300b6ef3258b300b6ec3258b30004ff7158b3001cfc7158b30024dd76ccb300b5df74ccb3031ddd74ccb303175f54ccb303175d54ccb3003ede62ccb300b7ce62ccb300b7cd62ccb3003edc62ccb30317ce42ccb30317cd42ccb30025de70ccb300b7da70ccb300b7d970ccb30025dc70ccb300057f754cb300f57c754cb30005df764cb30006df764cb300075f754cb3030f5c754cb30305df744cb30305dd744cb302bf5f544cb302bf5d544cb300b7cf724cb3003ede624cb3003edc624cb30025de704cb30025dc704cb300b6f7619873001ef461987300b6f46158730004ff7558730014fe7558730004fd7558730014fc7558730004ff745873000cfe7458730004fd745873000cfc74587300067f54587300067d5458730024fc7358730006de4358730006dd4358730004ff725873003cfc72587300b6f731587300b6f431587300057f754c7300f57c754c7300b7d4314c73003cff76c87300b4fe76c8730004fd76c87300f57e75c87300057d75c87300cdbe74c8730005bd74c87300b5de73c8730005dd73c873001cff76887300b4fe7688730004fd768873001ef66188730006f56188730025fa7088730005f97088730004ff7648730004fd76487300b4fc764873001ef66148730006f5614873001cff76087300b4fe7608730004fd76087300b5de7308730005dd73087300067f74596300047f74596300067e74596300067d74596300047d7459630
  | 16 => 0x8d21006dd43d8d21024fe70d8d21004fd70d8d21006df6398d210b4ff7598d21014fe7598d21004fd7598d210b4fc7598d210b4ff7498d2100cfe7498d21004fd7498d210b4fc7498d210067f5498d210067d5498d210b4fe7398d21004fd7298d210b6ed7298d21006ee4298d21006ed4298d21004fd7198d210b6f57198d21024fe7098d21004fd7098d210057f7558d211157c7558d21004ff7558d210067f7558d210047f7558d21014fe7558d21004fd7558d21014fc7558d210067c7558d210147c7558d21004ff7458d2100cfe7458d21004fd7458d2100cfc7458d210067f5458d210067d5458d21006df7358d21004ff7258d21006ef7258d21004ff7158d21006f77158d21004ff7058d21024fc7058d21004fe7618d21006dd6318d210b4ff7518d21014fe7518d21004fd7518d210b4fc7518d210b4ff7418d2100cfe7418d21004fd7418d210b4fc7418d210067f5418d210067d5418d210b6de7318d21006df5318d210b6dc5318d210b6de4318d21006dd4318d21006ee4218d21006ed4218d210b6f57118d21024fe7018d21004fd7018d2101cfe76cc921006df63cc9210b6dc63cc92101df671cc921005f571cc92101cfc764c9210057f754c9211157c754c921006df634c921006dc634c92103fcc324c921005f7714c92101df4714c92103cfe76cc521006df63cc5210b6dc63cc52103dee72cc521005ed72cc521005f6768c52101ef6768c52133777548c52133775548c52133df5738c5210b6f6638c5210b6f4638c52103df6728c52101df4728c52101ef7628c52101fe7628c521337e6428c521337e5428c521005f5708c5210b4ff764c521004fd764c52103cfc764c5210057f754c5211157c754c521006df634c521006dc634c521005ef724c52103dec724c52103df4764c521006f4764c52103cf4764c52100777754c52132f74754c52132777544c52132775544c52101df7734c52101fd7734c521007d7634c5210b6f6634c5210b6f4634c521007d4634c521327d6434c521327d5434c521007e7724c52103df6724c52103df4724c521007e4724c52101ef7624c52101fe7624c521327e6424c521327e5424c521005f7704c521004ff75d8121014fe75d8121004fd75d8121014fc75d8121004ff74d812100cfe74d8121004fd74d812100cfc74d81210067f54d81210067d54d81210b4fe73d8121004fd73d8121006ee42d8121006ed42d8121006fb60981210057f75581211157c7558121005bf745812110dbc7458121005df7358121005dc73581211157e75181210057d7518121026fa6018121006f960181210b4ff7598c21014fe7598c21004fd7598c210b4fc7598c210b4ff7498c2100cfe7498c21004fd7498c210b4fc7498c210067f5498c210067d5498c2101cfe7398c2101ede7398c210b6d
  | 17 => 0xb4ff7598f21014fe7598f21004fd7598f210b4fc7598f210b4ff7498f2100cfe7498f21004fd7498f210b4fc7498f210067f5498f210067d5498f2103ede7398f2101cfe7298f2103eee4298f21006ed4298f2103ede3298f2103edc3298f21024fe7098f21004fd7098f21004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f2100cfe7458f21004fd7458f2100cfc7458f210067f5458f210067d5458f2103edf7358f2101cfc7258f2103ede3258f2103edc3258f2103ef62158f2103ef52158f21004ff7058f21024fc7058f211767e65cc7210067d65cc72114ebe64cc721006bd64cc7210b6de63cc721006dd63cc72103dee72cc721005ed72cc7210057f754c7211357c754c72115e7e654c7210067d654c721156be644c721006bd644c721006de634c721006dd634c721005ef724c72103dec724c721004ff7558321014fe7558321004fd7558321014fc7558321004ff745832100cfe7458321004fd745832100cfc74583210067f54583210067d5458321004ff73583210b4fc735832101cfc725832103eee4258321006ed425832103ef6215832103ef5215832103efb705832103efb205832103ef820583210b4ff7598e21014fe7598e21004fd7598e210b4fc7598e210b4ff7498e2100cfe7498e21004fd7498e210b4fc7498e210067f5498e210067d5498e2101ede7398e210b6de4398e21006dd4398e2101cfe7198e2101ef67198e2101cf67198e2101ede3198e2101ef63198e2101edc3198e21024fe7098e21004fd7098e2101ef71098e21004ff7558e21014fe7558e21004fd7558e21014fc7558e21004ff7458e2100cfe7458e21004fd7458e2100cfc7458e210067f5458e210067d5458e2101edf7358e21006de4358e21006dd4358e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e21024fc7058e210b6de63cca21006dd63cca2101df671cca21005f571cca210057f754ca211257c754ca21006de634ca21006dd634ca21005f7714ca2101df4714ca2101df7764c621006f7764c62100777754c62134f74754c62134777544c62134775544c62101fd7734c6210b6f6634c62101ef4634c621347d6434c621347d5434c62103df6724c62103df4724c621005f7704c621004ff7558221014fe7558221004fd7558221014fc7558221004ff745822100cfe7458221004fd745822100cfc74582210067f54582210067d5458221004ff73582210b4fc735822101cfc715822101efb7058221006fa5058221006f95058221006fa4058221006f9405822101efb105822101ef81058221004ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d21004ff74d8d2100cfe74d8d21004fd74d8d2100cfc74d8d210067f54d8d210067d54d8d21006df53d8d21006dc53d8d21006de43d
  | 18 => 0xf7558831014fe7558831004fd7558831014fc7558831004ff745883100cfe7458831004fd745883100cfc74588310067f54588310067d545883101eef7258831006ee5258831006ed5258831006ee4258831006ed42588310b6ef32588310b6ec325883101ef6315883101eee215883101eec2158831004ff7058831024fc705883101ef71058831004fd768c831004ff764c8310057f754c8311457c754c83101df7764c431006f7764c431004f7764c43100777754c43136774754c43136f77544c43136f75544c43101df7734c43101fd7734c4310b6f6634c43101fd6634c4310b7d6534c431367d5534c431006f5624c431005f7704c431004ff7558031014fe7558031004fd7558031014fc7558031004ff745803100cfe7458031004fd745803100cfc74580310067f54580310067d5458031004ff725803103cfc725803101efb7058031006fa5058031006f95058031006fa4058031006f940580310b6fb30580310b6f8305803101efb105803101ef810580310067f74597210047f74597210067e74597210067d74597210047d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067f43597210067e43597210067d43597210067c435972103e7f725972103e7e725972103e7d725972103e7c725972103e7f425972103e7e425972103e7d425972103e7c425972103e7f325972103e7e325972103e7d325972103e7c32597211367f715972135e7e71597210067d715972135e7c71597210067f415972135e7e41597210067d415972135e7c415972135e7e315972135e7c315972103e7f215972103e7e215972103e7d215972103e7c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067e40597210067d40597210067c405972103e7f205972103e7e205972103e7d205972103e7c205972135e7f105972135e7c1059721006bf7559321006be75593210063e7559321006bd75593210063d7559321006bc7559321006bf7359321006be7359321006bd7359321006bc7359321006bf5359321006be5359321006bd5359321006bc535932103ebf725932103ebe725932103ebd725932103ebc725932103ebf525932103ebe525932103ebd525932103ebc525932103ebf325932103ebe325932103ebd325932103ebc325932112ebf7159321356be7159321006bd7159321356bc7159321006bf5159321356be5159321006bd5159321356bc5159321356be3159321356bc315932103ebf215932103ebe215932103ebd215932103ebc2159321006bf7059321006be7059321006bd7059321006bc7059321006bf5059321006be5059321006bd5059321006bc505932103ebf205932103ebe205932103ebd205932103ebc2059321356bf1059321356bc1059321
  | 19 => 0x8231006f9405823101efb105823101ef8105823115d7e76d953115e7e76d95310147e76d95310057f74d95310057d74d95310067f64d95310067e64d95310067d64d95310067c64d95310075e43d95310075d43d95313875e31d95313875c31d95310067f74d95310047f74d95310067e74d95310067d74d95310047d74d95310067c74d95313867f73d953115e7e73d953115e7d73d953115e7c73d95310067f43d95310067e43d95310067d43d95310067c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067d42d95310067c42d95310067f71d95313867e71d953115e7d71d95313867c71d95310067f41d95313867e41d95310067d41d95313867c41d95313867e31d953115e7d31d95313867c31d95313867e21d95313867c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d95313867f10d95313867c10d95310067f65d89310067c65d8931004ff75d8931014fe75d8931004fd75d8931014fc75d8931004ff74d893100cfe74d8931004fd74d893100cfc74d89310067f54d89310067d54d8931006ee42d8931006ed42d8931024fe70d8931004fd70d893115d7e75989310057d75989310067f65989310067c6598931155be7498931005bd7498931006ef62989310057f755893115d7c75589310067f65589310067c65589310067f65189310067c651893103eee6218931006ed6218931004fe76cc9310067f65cc9311b67c65cc93101cfe768c9310067f658c9311ae7c658c931006ef628c93103eec628c93101df6718c931005f5718c93101cfc764c9310057f754c93115d7c754c9310067f654c93119e7c654c931006ef624c93103eec624c931005f7714c93101df4714c931004fe760c93115d7e750c9310057d750c9310067f650c9311867c650c931155be740c931005bd740c931007cd320c93101df6710c931005fa700c931005f9700c9310067f65cc5311767c65cc53101dde73cc53101edf63cc5310077765cc53137f7465cc5313777754cc5313777554cc53101df673cc53101ef763cc53101fd763cc5310b7d643cc531377d543cc531005f572cc5310067f65d81310067c65d8131004ff75d8131014fe75d8131004fd75d8131014fc75d8131004ff74d813100cfe74d8131004fd74d813100cfc74d81310067f54d81310067d54d8131006de43d8131006dd43d813103cfe72d8131004fd72d8131006f731d813115d7e75981310057d75981310067f65981310067c6598131006fb60981310057f755813115d7c75581310067f65581310067c6558131005bf7458131155bc7458131005ef7258131005ec72581310067f65181310067c6518131026fa6018131006f96018131004f
  | 20 => 0x3efb205803203ef82058032006fb7558032006fa7558032006f97558032006f87558032006fb7458032006fa7458032006f97458032006f87458032006fb54580320067b5458032006fa5458032006f95458032006795458032006f854580320b6fa7358032006fb53580320b6fa5358032006f953580320b6f85358032006fb43580320b6fa4358032006da4358032006f94358032006d943580320b6f8435803203efb725803203efa725803203ef8725803203efb525803203efa525803203ef9525803203ef8525803203efb425803203efa425803203eea425803203ef94258032006e9425803203ef8425803203efb325803203edb325803203efa325803203ef9325803203ed9325803203ef83258032006fb7158032006fa7158032006f97158032006f87158032006fb5158032006fa5158032006f95158032006f85158032006fb4158032006fa4158032006f94158032006f841580320b6fb31580320b6f8315803203efb215803203efa215803203ef9215803203ef821580320b6ef6298b3103eec6298b310b6ec6258b31004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b3100cfe7458b31004fd7458b3100cfc7458b310067f5458b310067d5458b3101cfc7358b310b6ef3258b310b6ec3258b31004ff7058b31024fc7058b310057f754cb311757c754cb310b7cc324cb311757e75983310057d75983310b6fb6098331026f860983310b6f86058331004ff7558331014fe7558331004fd7558331014fc7558331004ff745833100cfe7458331004fd745833100cfc74583310067f54583310067d545833101cfc7358331006de4358331006dd4358331004ff725833103cfc72583310b6fb30583310b6f83058331004ff7558a31014fe7558a31004fd7558a31014fc7558a31004ff7458a3100cfe7458a31004fd7458a3100cfc7458a310067f5458a310067d5458a3101eef7258a31006ee4258a31006ed4258a3101eee2158a3101eec2158a31004ff7058a31024fc7058a3101df471cca3103eee628ca31006ed628ca3101df6718ca31005f5718ca3103cff764ca310057f754ca3116d7c754ca3103eee624ca31006ed624ca31005f7714ca3101df4714ca3116d7e750ca310057d750ca31165be740ca31005bd740ca3101df6710ca31005f5710ca31005fa700ca31005f9700ca3101df576cc6310b6f576cc6313977754cc6313977554cc63101fd673cc6310b7d653cc63138fd553cc631005f572cc631004ff7558231014fe7558231004fd7558231014fc7558231004ff745823100cfe7458231004fd745823100cfc74582310067f54582310067d5458231004ff725823103cfc7258231006f7315823101ef4315823101ef6215823101efb7058231006fa5058231006f95058231006fa405
  | 21 => 0xf745843200cfe7458432004fd745843200cfc74584320067f54584320067d5458432006de4358432006dd435843203eee4258432006ed425843203ef77158432006f75158432006f65158432006f55158432006f45158432006f74158432006f64158432006f54158432006f441584320b6f731584320b6f4315843203ef7215843203ef42158432004ff7058432024fc7058432006f77558432006f67558432006f57558432006f47558432006f77458432006f67458432006f57458432006f47458432006f75458432006775458432006f65458432006f55458432006755458432006f454584320b6f67358432006f753584320b6f65358432006f553584320b6f45358432006f743584320b6f64358432006d64358432006f54358432006d543584320b6f4435843203ef7725843203ef6725843203ef4725843203ef7525843203ef6525843203ef5525843203ef4525843203ef7425843203ef6425843203ee6425843203ef54258432006e5425843203ef4425843203ef7325843203ef6325843203ef5325843203ef43258432006f77058432006f67058432006f57058432006f47058432006f75058432006f65058432006f55058432006f45058432006f74058432006f64058432006f54058432006f440584320b6f730584320b6f4305843203ef7205843203ef6205843203ef5205843203ef42058432026fb7598032026fa7598032026f97598032026f87598032026fb7498032026fa7498032026f97498032026f87498032006fb54980320067b5498032006fa5498032006f95498032006795498032006f85498032026f87398032006fb53980320b6fa5398032006f953980320b6f85398032006fb43980320b6fa4398032006f943980320b6f84398032026fb7298032026fa7298032026f97298032026f8729803203efb529803203efa529803203ef9529803203ef8529803203efb429803203efa429803203ef9429803203ef8429803203efb329803203efa329803203ef9329803203ef83298032026fb7198032026fa7198032026f97198032026f87198032006fb5198032006fa5198032006f95198032006f85198032006fb4198032006fa4198032006f94198032006f841980320b6fb31980320b6f8319803203efb219803203efa219803203ef9219803203ef82198032004ff7558032014fe7558032004fd7558032014fc7558032004ff745803200cfe7458032004fd745803200cfc74580320067f54580320067d5458032006de4358032006dd435803203eee4258032006ed425803203edf325803203edd3258032004ff715803201cfc715803203efb7058032006fb5058032006fa5058032006f95058032006f85058032006fb4058032006fa4058032006f94058032006f840580320b6fb30580320b6f83058032
  | 22 => 0x943203e7d325943203e7c32594320067f71594320067e71594320067d71594320067c71594320067f41594320067e41594320067d41594320067c41594320b67f31594320b67c315943203e7f215943203e7e215943203e7d215943203e7c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067e40594320067d40594320067c40594320b67f30594320b67c305943203e7f205943203e7e205943203e7d205943203e7c2059432006bf7559032006be75590320063e7559032006bd75590320063d7559032006bc755903217ebf73590320b6be735903217ebd73590320b6bc7359032006bf53590320b6be5359032006bd53590320b6bc535903203ebf725903203ebe725903203ebd725903203ebc725903203ebf525903203ebe525903203ebd525903203ebc525903203ebf325903203ebe325903203ebd325903203ebc3259032006bf7159032006be7159032006bd7159032006bc7159032006bf5159032006be5159032006bd5159032006bc51590320b6bf31590320b6bc315903203ebf215903203ebe215903203ebd215903203ebc2159032006bf7059032006be7059032006bd7059032006bc7059032006bf5059032006be5059032006bd5059032006bc50590320b6bf30590320b6bc305903203ebf205903203ebe205903203ebd205903203ebc205903203def764c832006ef764c832004ef764c8320076f754c8323a76c754c83203f6e654c83203f6d654c8323adef744c8323aded744c83203fae644c83203fad644c83239f6f544c83239f6d544c83203def734c83203fcf734c8320b6ee634c83203fce634c8320b7ce534c8323a7cd534c8320b7ce434c83239fcd434c83203fe6614c83203fe5614c83203fea604c83203fe9604c83201ef7759843201ef6759843201ef5759843201ef4759843201ef7749843201ef6749843201ef5749843201ef47498432006f75498432006775498432006f65498432006f55498432006755498432006f4549843201ef47398432006f753984320b6f65398432006f553984320b6f45398432006f743984320b6f64398432006f543984320b6f4439843201ef7729843201ef6729843201ef5729843201ef4729843203ef7529843203ef6529843203ef5529843203ef4529843203ef7429843203ef6429843203ef5429843203ef4429843203ef7329843203ef6329843203ef5329843203ef4329843201ef7709843201ef6709843201ef5709843201ef47098432006f75098432006f65098432006f55098432006f45098432006f74098432006f64098432006f54098432006f440984320b6f730984320b6f4309843203ef7209843203ef6209843203ef5209843203ef42098432004ff7558432014fe7558432004fd7558432014fc7558432004f
  | 23 => 0x14fc7558232004ff745823200cfe7458232004fd745823200cfc74582320067f54582320067d5458232006de4358232006dd435823203edf325823203edd3258232004ff715823201cfc715823203efb705823203efb205823203ef8205823219d7e76d953219e7e76d95320147e76d95320057f74d95320057d74d95320067f64d95320067e64d95320067d64d95320067c64d95323c75e32d95323c75c32d95320067f74d95320047f74d95320067e74d95320067d74d95320047d74d95320067c74d95323c67f73d953219e7e73d953219e7d73d953219e7c73d95320067f43d95320067e43d95320067d43d95320067c43d95320067f72d95323c67e72d953219e7d72d95323c67c72d95320067f42d95323c67e42d95320067d42d95323c67c42d95323c67e32d953219e7d32d95323c67c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067e41d95320067d41d95320067c41d95323c67f21d95323c67c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d95323c67f20d95323c67c20d95320067f65cc9321b67c65cc93203dde73cc93203edf63cc9320076f65cc9323bf6c65cc9323b6ef64cc9323b6ed64cc9323b76f54cc9323b76d54cc93203dee73cc93203eef63cc93203fcf63cc9320067f65d85320067c65d8532004ff75d8532014fe75d8532004fd75d8532014fc75d8532004ff74d853200cfe74d8532004fd74d853200cfc74d85320067f54d85320067d54d8532006f741d8532006f441d8532024fe70d8532004fd70d853219d7e75985320057d75985320067f65985320067c6598532006f76198532005fa7098532005f970985320057f755853219d7c75585320067f65585320067c65585320067f65185320067c651853201ef66118532006f561185320067f65d81320067c65d8132004ff75d8132014fe75d8132004fd75d8132014fc75d8132004ff74d813200cfe74d8132004fd74d813200cfc74d81320067f54d81320067d54d813201cfe71d8132004fd71d8132006fb40d8132006f840d813219d7e75981320057d75981320067f65981320067c6598132005f67198132005f57198132006fb60981320057f755813219d7c75581320067f65581320067c65581320067f65181320067c6518132026fa6018132006f960181320067f74594320047f74594320067e74594320067d74594320047d74594320067c74594321867f73594320b67e73594321867d73594320b67c73594320067f43594320b67e43594320067d43594320b67c435943203e7f725943203e7e725943203e7d725943203e7c725943203e7f425943203e7e425943203e7d425943203e7c425943203e7f325943203e7e325
  | 24 => 0x18006003000000000e0080040010000005000000000000400000040060020010004004033002800c00800700080100000010010008008000003800000c00000a8018002004001001400a0010000000002002001800400c001001000c00600500480000580050030000008002000801000a00600000000260110000000004012000800800a000001800400000a000000000c000000800000000500b8000004000001800000200400400040140030008004000005000000c002000000001001e0060000020000004000000400800d000000000200100a000c024001001000000e00f005002c00800500180080040000028044002006000001405800700c800000c0030010004000006000004001c01f0038000000002000800c0080070040048006014003002c00a000003003000402d001000801e00c0000014016005003801801c00d007800800000500c80080000030000010004005000000c004001000000c00400100300080020210010000000004001800c0200020058024004000000801401400a00d0000006007005001c0000000000018000004004800800e00e00280040000000028004000000000002400201400200000020000000000006003013803800c0000068004000000003000c000000000800001804f00380b801a0000010000002006001801c00a00b0000010000001001800000200d000000001c01300000000000000040024000001004000000600700080000040020018064008001000002c0060020b6f7619873201ef461987320057f75587321b57c75587320b6f46158732004ff75587320067f75587320047f7558732014fe7558732004fd7558732014fc75587320067c75587320147c7558732004ff745873200cfe7458732004fd745873200cfc74587320067f54587320067d545873203cfc7358732006ee4258732006ed42587320b6f731587320b6f43158732004ff7058732024fc70587321b57e75983320057d7598332005f67198332005f571983320b6fb6098332026f860983320b6f86058332004ff7558332014fe7558332004fd7558332014fc7558332004ff745833200cfe7458332004fd745833200cfc74583320067f54583320067d545833203cfc7358332006ee4258332006ed4258332004ff715833201cfc71583320b6fb30583320b6f8305833203ded76cca320b6ed76cca3203eef64cca323d6ed64cca323d76f54cca323d76d54cca3203fce73cca320b7ce53cca323cfcd53cca32004ff7558632014fe7558632004fd7558632014fc7558632004ff745863200cfe7458632004fd745863200cfc74586320067f54586320067d5458632006de4358632006dd435863203ef7715863203ef7215863203ef42158632004ff7058632024fc7058632004ff7558232014fe7558232004fd7558232
  | 25 => 0x10048038004002000000c0320060010004000000007800000000100480140040000020000002003001000c000003000800000800200100040040010000000002000003003000800200200080020000010008000000000801800000200300200000020000000000004001800800000c001001000a000003006400c00500600000020020010000002001000000c01c000000800001e001000800800000300a0004018007004000c00400100080040020080000000002006000001802e00a00100000000000008000006000000001000000100080000040020078000008000004802c036003000800c0160000000010000004000806000200500200040100000000038006002000001c0000030020058000000003000800c00200d80000020070020000000001000001400a0020000004000007002000c0020000008000016000007000003c000001800003e009003800000000000300040080030008018000000002800401001f0000000000003000000000000000000000160010010008006000000805c002003000800c0000060088020008005000000400000100180000000020000018002004000000800000000080100040060008018002006001000000001b006800000000300280000000000060004008003000000401200700080000040010000000000001001000400000000d8004026001006800c006000003002800e0030058018004009000000400200b000800400400000f80540100000010010004001000800c018006000000000c0000008008008000002000000402600500200000020028024004001000802001e0000008004010000001801801a0000008008000001002800000c00000500040020000018010020001011800c00400000000180000150000080002000002000c0060000000000000000008000000200100000200100030000014000004003000000000300d000400c0020010000000000000800c0140030048000000001000802000c003003001c0000000030000004000014800800800a000000c0020030000008000001001000c00200300100180080040000004004005009000003400c001002c010000000800c00a00b000000c00200001e8000000000002800402a003002000801800700000380120040000004000002000003800c000001000000601a0008000002009000002c0000000000000012008000005c000001000003800200000000040020050008028000005001002000600000500600060010000018000001008000c006002000000c0000010008018000002000800401e00b0000008008001000000c00800d000800000a006003003000600c013000800c001007000c004000004000400400a0010044000008000800001201e001001000000100000000060070030010000011002003800001600000
  | 26 => 0x2b835bc03b22f88f119650123ba80720000a8a00000000000e651d2cbe21e980000550cc3000035311d008d2d500000000000000095721c4000000000000005bd33644b106b00833408fc8140c5ac00ac5b80ed47fa2f80cad210c000181040201e8caf00000001bec77c0444000300c7df37c400033c46170e0c6a20000a6a36fc220160800000000000000000000000000007bb291c00000000002b3c8800318bd1000000017580001f7085d293c0000000b3700006281cac83d11e8aed051ce523b24000174894330d422e32640121714b2622944e413f0dd0000084a207c46f30dc5c4239c27e0000f631994f5b27d000025ec0000000b243c180000628c8f0f4c00000003623aa063800004440000803396858a257c0002c740000000be90ce081d28a075d04744780658a60000000004e8c6c34e45b722c037f162072924e00000240ff60000d953f5070428b864700000120000008004000004004001c000001006000c0000040040000008006003000400a000000800001800000000080020040010068012000000800c01c001002800c000000000000401600500000000020000008024016001000000c000000003801000c003003804800000000b802c0040080000000000000000003000a004000800402a01e005004c012010001800400a002008002c00600000080140020040010004006000003003c00c00000000200020020020008004004005001800a000003800800a00a000000400800b0000004010000001004800a00000080140020010000008000000002000000c0030018010002001000000c008021000800402000000400440020010070000012003000001400401b000000c00c000001801000a00300580b800a0100008018002008001000000000200000300080010000000000000007800000201c0028000000000003800000a00500000380400000010004004000003002002000800000000300000000000000000000808c006004005800400400200f0044016001000000000000c0030000002006005000000400000100bc006000005803800000300100000020000010008000003000001c00e002001000000a000001000c00e000003000000a000000801c006000000801000000200e801c018006000000c00200100080000160020038014032005006800001c014008002003a00700300300100000008028000000000800801c008000004000a000000002c002001000000000200100000040060000068030000000001000400000e00300780080000000000010002000000400a00500000000160010010000000000000000001000b00500000040030040000000019000001800200a001004800e000000803c0060000080014008000000000000000100080040000080000000000018001000000200b000000400c0
  | 27 => 0x3a50152000000026e88660000000000000000002671740000000080e1120d34000000026d4fe63114b053834f3b09fc000000023400005b11ad08e5094401f00010470000f9f00008010000ec732d81df14bc07800007d32c641b700009b30000000247800000000fb25489a135488851124238343099f1ee4d810ae45b0400826608c8f1d1a64d5800009cd3bf8b3b00849e51b9c2ab000098e3180b090f98000243450d0e5800000000240000dcb0a1c000000070600000330a843cb0000000300400038c4f0e11c0cb12450bda0000db6126856c0000b0d00000002ed86f321446e2166c0000000e8227dc94d39100000708a13211c52c0d400002c287860000000000000024acb60000000f00000c2152000000001740000000000000036b067800000000000210125cef42428bf334a496d05f00b5088800000001f12dc80470000e03000041e0000000000021c28f0b7b000005820e80003e34fd91bd83af2778ee92b300000000bc5134c00017a81f236989d500003e80c381d122181d800009210e000004090dad3c8021a00e00c83b7089b131c7813cf8a2517f4000292069f00002bb004019d0000d770d7c0000000000209ca991ce04d1142400000000000d48b7407240000d288a600007a22304b441430b513fb818020183483a44d630000beb3998000241c7d22c4464c0efc401395cb430b6889c1544fa406bc9b20000e880100000000000000005801508000000042c1c407ef00000000dac40c224c6ea0e640002a24670000000000000000000f2f2220fae000000000000f800007e8000000000009fe2eb42501a280000000000000000000000002e101a31ba4a17354cd0a24c09c213d41a435e0c0e1a844b81a084b222bc1b61db0bfd27845f31d5839d38302ef1ed44df2d34d6509f40000000000000000017a00000000d030e7c000393cfa5000000000005372fe5027242c0000000eda36607b80fec00004c03050000ded00000000000cee327435c2970b7f285069c1facfa70000d3a000000000000002424c3600000f50c4000000000000000e4e10384be000045200000002b34eef265000000002561b5400000006fd000000034c8a1b1264d381b440000ed80003fb400000000000000329370c82b0000e280000000382820700005af29c000013344150f0c82200007fe00508b13530770054000c0e88c2b00000000b740000000c5d17d4e6427c400039a89871644f48000000015e800000000001cd000b0000000241829018bc0000000e8016642911d845dd0000315000076936d502102b80150af89452bb059c2ad03dd134800032290000000b3f00006ee00000000000075000000000000001b9475a21b03ea15b80000dcc0001ab80003c6844b0000bcd31ec1b914f81ce2be40fe17c0b360000a060a100002430
  | 28 => 0x816a400c3740000c0f0f6c0000000a53383894813301931760ae53dd00000000000000000000000002e18000000000020943f223540000000a6734b454c3b3c00236790132de4d8d26fc000000096332680000000000000000000006f00000db2403446e0000ee51b14bb30af0e8a005cb3114889df1a185c127acffb1f20d843130c6b0c483ef2130000350c00000001f51074cfa00000003e8c0002f60e75000071d000053f000068800000000000ab21aec0002edc9aa00010432a1c5773e2019226dc12b00005e5000078f3db0b1218d01e641380881c24445259409f17e8df424382e42b500001eb000000000000000b99000000024b48820000187213c12433f400036187cc1c6800000000000000ba80000f3800000000000b700000a9a192c1bd3f2800000000000b2460800000703e545361834677294036d31dc17031f4ad500002230000e1d0bf40bb222cf8235a0000177cfc60ee8c9b132000000006d823b00000000e7c00000d60000000087500500005f70000000000026b00000000000000000000021640000000fc1000037900880360754000190c00000003513c0c4851f145a400000002e0c2d32ea8609364c00009d0d5d00000000000bbf000063d21d479506f000002447b400007530000000054ced13188a2926f8086219030a2fc00a213c0a0a1df44290000adf019ccd2000052005b46cb152800019e436900000001b08000000014c000000021acbb220d000000008d32db4b1c0000cfe000039a123c49b000000037541eb03a00a50f200ee2b140002de8e463cb454f0000b52000000001b4eb43c7000038400002a38ee8263cc6107740002b2000000005eb0cdc0000000dec04346e61aa00000000ef20a209833164cd01b90f550bf8a2322782a5236859f00007c32180b9b2a842812634f6931a80003bb8c5f1b5c88c00000002e6027b024c5c03d90f0903f00050000c00283c38d00005a9110cf01148c48319281650000d8c07fc12d000000009500003f9c88a2870000030c0000a8c69621a400034a8a4d0000000373cec22fa012a0000f730000f29173c2260000f180d0029807d8d442cb40002b404a31e9c0000000cc12df0fda3be8f170684000000018d09040710ffc00007cc0000db80cc0000e2e0238c2316e4e4c00006cc40a4fd21c4c78a1c44e3c1b0038e349c5333f6000005d81d025b88fc25d00000fb4332143ceb7178803e344000007689980000bcb0000aa314f4c852370fab0ed000000005d3408000000004513c200000000000000075129907881e340003644bee08fcf4f0018000347cb41000104b00001c7000000032f08c5109c00000009b40000ffc00000000000b65000058c0000000337485608003d13db400000000000000e0030b8000000093a0000560000040019d4794281026c
  | 29 => 0x50e5089631d8a8012d80e423989ec00000d100002650500367231832b00001dc2d1828b37a04ea28840982e30b6b1990000000000000000813250bc202700002654ed500003f321400002f903783fe400000006900000a311044c1a18dc7444114b671e84ca8041c6cf3578bde287800014b80a600001e72bc442f36e400000008390000000098c000009c67a0cbc0001ac440528bc0000000000162c1120000f11024838b3e806b0145c9a5069c0002af047502540001884000156057f39800002b5c0003a1c0000000000411061917c4d3f2c40d5108e4eba1b38a01403c0002100d0d1ee80000000000000000033ac1e20c0400000000000000000131813d2dc421824640a7401ca9f01748672328d5b35d01980f182e13db802600002d425501140a5400016c81c50000a840268000193c18b32800000d6c000000000000000000000b6600000003f88000000011b00000000d34d4734383cc3e50eb53c88ae100000000b340004128bc41d640000eac7260000ea52b9cd2c1d3031f0f40b171f18000259cd1c1584c423bd42c2057ce53000401a0368d3c00008ce3c28b29022468f00000001c9000000005852c04000234810200000000000ec12a9400000000001c9c00018900003c98f9016588a11b800000cc40001b2411e1bf8ca32048d252c7c47701f49e839f40000000925129c92200005c31378edf00010250000cd321948632c20000087831d00009d90f789173a5c20118743bc38e8f131134000000000024f84ed03540000000000124c0000d0c5c8085c95a299800000007990000164221cc273c1017b10247a33134f911ef89840000ae8405817d1208f9e117087e18603e4180c79e2b4cf2318e437c0544543344849234c501e1574b53303471800007ad187806c10188ab33c800000006d916ec0002564faf0810000000000000005fb00000001ad487c0000000080c4e623d400031280000000000000000000000000000dc02fa84e800000000000f9d0000ec400000001bb00001f900002bac924000000036b80000e6c0002b700000d3046933140000000000000000027880000000fc70000efb0000e8f0b388093018f4507d08f8275ceab09906253f542160b5c3a426a4f6a3e380f40c68af326ac00004c48d40cb4829075c77e00000000000000000000035209fb0aa80003fac0000000000203c4dc0ee400000008990000d09000000003b4f8f04d445f39e8fc42b4491f0000da109d43a8000025c29c4ea10000ebd0000ba11ec400039dc000082400000003c700000000b200002ea4f7b03bc25d1fd80aa22d839800c4000335cdee0f68000208c90500000001efc45400000000000000197000000000000a7400000f43921af400010b8adb00002370f7c92a14009e40000000000022106cc31423fc7620210f6605b
  | 30 => 0xd000012ac14e0e54e981b282b71680bbc157808f16f8d3e41180f6000000000006ff09790363590fd71b04a2d10dc0003d1102e08d8a4300000003ddc71510ec00000005e9000069700001ea3c9c0001fe4f160d1047b37040b90000a4540a000000008ed061000000002140000000113cd9c0924c5325f4910227449e2bf42fb29f8c0b0000a722e9ca032c18a563d1800012741bf227ccba196c52d004ceed02f50192910ef1147c28524b84f8235893310882f31b7800030d034536c0de900000001698abb1c644bc2410c9828f83c02d080000be4c30341c76e3de8c2428dc4623fbc7d700000d2000000000009720000dc530f80002498b8a00005d933dce423d848c000000c00000000000000000009c3000000014a4dab000004f3278a5110e800038d8f7132945a20e5c3a100007760000f4a00003cd24bc0002c6850129f000007b8fcd390033d2aa8d8f267066818cc2833f782f608448ef2420c8d2f4012c049475e3f009d40000390117480d29743c224489010000ce700000000000530000000002b02db0000bb42af4f72295c000220c0002f84b4a00000002e78e8332702e21850d610c24c78000000027bc00017d80001ff0f500000fbc2da860636c4cec1a503f719509342690bc6000091a177853a345458e36f04682608e9a3e28c5815980992798b0f3aa8bba2c7848803b04e92e74793072902b11304a62960a240f950373a303d20b14d7b2fd41cd20105ae00004a00138e4b032c032000075830800000000ced0000b680000c6f327c0001c8400027c0de60000d850d3c0001d20cca28a80002d840001dccda93e2cab104205ad0ac4000352c83c000011300000000930f2b240c4fd3b34f8620d469e05344d000008f9187c1b4000083807e03610000c1805a494c0000000000088f000000000000000d740000000000000000000000000000fd1000000000008db000000000000000000e903b64a5f1be00000be8fa122500ca1ba00003c480000f1464022484b30518fb54028e1e331c24a18a8789176c6322ae49da11ac3f8000000000000000000eb1238800006300000458000265c39100000001a9400025380000000ebe09f0000000000000000003e1026f13c413c19540002254000000000000000000000000390400000000000da8ac322900000020c7100001d402dca20000000000005ec0000a05204c75f1c040db0000000000032e1048733000043e38880000000ac40000000330800000000002c585cc37845971e803ad0bd44c12f1c7391490ca900001de3138e7e00008bf00000000000dbb00005d70000a962058fcb19401d936a80002a800002028b8f1654e711b7c4182c88a5237385730fb8f5e0c4487d08f81db2f640280d24cea02d0eaf19f403f00dce7b1648eb834dc1043aec00000008aa0000cb
  | 31 => 0xbe15100002f704811ea00000000774000000000000e138ec2760000000000000000000003f3000000000000000a770d180000000000000000029b832a020800023450151daca30323097f30742570000920000000016a0b730000c5c0000a7d2ce40001e44bff31549af3a1811715f8f020c588cc21d902c10b41770094d410bac7cd0000bdd32200002a505e712dcae90000dfd343c4ba016814227d8c6812b000020c40001fdc00000003e12e40dc831c8ffa000028e00000000000da500005d10bf00002f9430301a0c4f2a5cfb60000000357c2802a907ab2ac072c135000000003b832fcc262a442e83d345682950e263a70c2d0cfc0000000aa938dc00000000d3007000010e0775000000000002ca2cf08b90d50e0f21549f51c3c12e09c8a9d08a86c63380fb72f38d2804bc0000000000000000000004db404400018f89e0238400000000002cf80453360b0400005f400000000000e230000edb00000002334000000000012a0eae000000012e433e050422c1d70853215000000bc3d923ec8842e1c8490fd0a0715f00003a1072500007ed0000000057000d289c1032e90736048c27009a86a330bc293000000000000000000000000028d00000000000ec000000002b8800025008b714180003d4400020c00001c00ea600000002cc00c5000074d3c7d00e0000000195cbf63ca8f330e04000000000000002ad12d00000000000000014a2ddcd6b000000000000003474baf0000bec2b2800000002a020b8000106c27a10e423523d81e31adc00029bca732260aba0a7ced016aceff32c8728000000017e00001cdc20c3648db80130173287c19104d07172c94cc435cc88d335054534f478c130000035545ba26c0000138400037a8a150000b473bd867b3b1400000000000a488280ff4d01000000006208ea34acb2a329c08a3b28ddd3b840b22624df81e901e11bf03c40000de70000c67399c6810000a0c3d880000ba89603f589fd08b420b26e0ce1094c7a533002460a90a850794e2c3af00dd1064f5a00590312cb10333bb10231e681a2049800000004573a486a0236400032c0f600780133164c0112cc8000035c29740e80000d084983b1806414c468d23108fa000019e08487400000000389400000000090000bfe16740940000aa201a4000000078000000002d58c140000000171c5830000ad82ab424e317820526300003b2c58f149465e1e1c3d60d800a335b85672510c7e1f68a12130cd1a268c02e065c1ae2eb8f050000ca126200e0381853b3eb4df3144c57437f03063a6c38514ace7200000000b0419f244c00000009a71bacb5d1b688f02cd000014e400000000000c64eb226b0a1a25bc1d62d241cb0cb0cf9360ccf600009c711541220000fa619f095001bc80c17507e00ca00003388564118c5da1180bf228
  | 32 => 0x8d4a790a689c83a2ccef1de45270bc87453fe023b374c28a132829c28082b62110db3039449631fce500558612091065f2c80d890b00c1f1a2c71b14782a629ac7bc1fcc00022ec13e22d0d8e000017f35b0c3a18b4aac074cbd614601cf2584bcf30c800037c036f11401102a04d2332180761ddca4105e06dc1f404af1ec0cf0058c0be25a8d26382c714256d032312c9bc0a500000000000000030000000000790b6e000000000000000000000000059439e40000f28000000084d19849b60000d2f16d0000276089017b4eb30000d9d28e00001de85b60000000000050806a000000000001cf8000010c00000000004134b752fec0000afc000000000001041c636f4cbb000030228d8ac13be429b00002c7180400025080f93c00000396c6511e0c55f2bd0000000000000001892b6854e1f849491cfcea4127c2a70cd874a3e1492c006c00000000000000d3000000002be097625a0fc53d0cd963fccb07249c93f089c00025702bd096848430fcd660cc051c03f4b8d25ccd241d9c62b2800f9b31442a2000064130e0000000009603600cd00000003fd00002f24fe416fccc900000001c78000058000000000003d9cb3d000069139a40b31770e4a06189cc0e70bd5333c9900bb85791250bbd00000002f8c0000ff800000000002ed400000000004130000041400007a4cfb000077b00000002b24d4003cc0002bc810c0f04000000037d0000c501ae06460000b800000fb10a580000000a6100008580000000000000026ec0000a0901b0378aea1138f761230fbd3ad800000000001558e5e01cce270000000000000000000000ff000022b0fb8000047601ec975000010b35a8f783e8830737250173c3c7cb10fcdde0000a980000000000000005f8000000000035805e4103c76f00006ad211800016ccfdd36bc83200000002d9000021c0b95018c5401db446c11c4ae610ccfea0000f4e000058900000000000ce837ec4a5087c3a63de4c3c000000000000000000000359c00037187051800e48246c0001190c9625c0fe30000000000000000003f600000230000f0b2ff09ed3d0834e2d3c0000000000189860f02e8e133c6c0001aa4c8b3d2cd4e00005e12d68cfc1be4000206435a0b440002e04e7015c8bf1284046d0000323000000025e8000000031b000000002ac0003954c52402c000188800025f0f2c0000c0c0000000000080205b00dc161c423096c0fa39bcaf50e9c202001c6db1af099a3d4800036507e3012050723cc118021ca8d14504ae318c2300000a261a6c00036f86fa10200000ce4a181f549ad2560fba2e440610fc40000c940003b5c000000032611c82b200000000000f35000000031cc00040d472d18b0ab520bc00036dc9db116000000000000000000000000013885040000b2e00001fa0b8c0001c38a
  | 33 => 0x323830f3158dd6000008b2b18c5b0cd0929129000008c498034d8a762e681202614d7c3cf02c606e876517f837e0e4c49036685540854e5c06a8b881ef4a3900008d80000c043fc80000ce807908bcd1b2bdcee30e3c4e32cbc4d60000e1b0000000000000025dc635000000000000002d6c9bd0000ed8120059007f0b8b2f200000000e681bc48080000f141f0016f348461b14e03e335f400000000503750b890000000315d042152c00006ac98121090080000000000071f00008ad0d606ac3a240f71e4800000c0a8c07005813208f54000000003c08b311640002d403ce2ec49023120fcf1724000233cb582204f5d000101d00009ee21cc05b04a079d292c0003d04000275800005604352574f7e13fc0352f48e0400007ee306cc93238070a2078000000000013b06230000148000000000005a328e89862c3869d0fe838823d000040c0f3f1bdcc083240ba20000000083cb692c0cc022eac0004004c3b25ac000000040700000290abc019274800028fc6300000fd0336ca3d000000000000000000000000000000d000000000000be000033946d230a000004d8c91000049c1a6004a014ccde3b78e6b1464eb0295457b18fc0001aacb920000d421040e3f1364ce32374c17365c07e1f646c729000003058c0a0000d3b017c00013bc00000001c42aac00000003b3184c40d2cac000235cd693f4c04b07204dd22e07ca230cddc08349d109b80e62afc2f71ec8ff719108c90188ac221dc60b1960d33325c2d601b8c072930fb913d88051f5800018440000000bd30fe400011786f4122c0000000ddb3d6475000000001a389fc2fdc47f12a481826c43170000000000030d000025200000000000000000000000000000000b3500000000dd8000000000027046f20b3c432000033500000000000a6231d00003ab0a4a3e30a7437d881a001000006a40000000941402400007ec00000000000000d7a194800000008b200008df00008a90000fdf35f8000000000000000e7133ca9b1feca630b3000037e48eb19b8ff000010480000a190000a7512f4d5700005ee0000c1c000084b11000000c9c000000043d24a051208280001b5800037c8bd400000002d20e300b7873d2a20b960000ec3055c9c41ae49a01d24ad93c9054613104c919ccf9c3a8cde237dced61068000000000000000000000000000016200000000000000000085b0000278000023d0000ac02a0800000000000000000092000000004bb000062023f8b15000000020d89c007f43b105841940000a4600000002104000000000000006cd00000003ff8a421e14000000047d19141060818aaf3bacafb24604c519ac67f372894733387e51fa45f932880852738afa21b879c1e5cd56296405240505d52ab8aee2d38cdc03fc8a30568b9c3e00e5102fcea710903b23
  | 34 => 0x27fc0000e180002938ab600002f42588cb317805c605104f409a4d163ed0000000000020ec0002d7889a33ccd3532dc10e01fce4709b4f8130242ec2a18a5a0564247000033b374491c267400002b48e808f03870400760369cafc2a2c05740ecb623420000000000000000003c64532390c6b600000001938fbb3b3000040e0db43094c33375c1e80fb00000000000000000021e424f000000038a49c932e40001cbce2a148447e3444c6e03109f93049040105835508ac4da1618ef00ea8000100c15509347683d5800029b4bc00000000000000008e886f0000a682ee491506d475433a4341000037b05e47d135b40541a680001e603f02e942ae0000c22170800000000000f700000000000000000000003b0000000000002dc364026119c40000000af024dcb8e0000891202ccb430143e923f430426480b1345c000000000027701d22e8000000e4e1c33d0fe500000002a9c0000000d9b01180000000f920eec0a92c84653000000000004b00000000000000000000001a000af2308000139cfbf229c000066c0422df40df2844c410000c801da8778146c24b23dcc473e2448d0ef4ea9121c2d02e7c30b29b0000339082c00000e211586b21548ab700000001fc40000d5c7de28b011528241cc10280003960c1900001821594e991b5069517fd0391980bd70000a330000000018000000000e900003c92e8c00038bc88e0000b0b1c589513f6c000000016b000000029780003664c700000f30000063600008c80000e4d0000000000000002300003ab47fd00283750000000060400000000001c80f28000084e1ed8d0b00005fc33fc98a0484f6531f0fc314a8c923cb80002d8c00035240000000219252834b00000001394ce610f006b00002130a3c000000000029e016600008ba3dbc93528201c10000c87056c0002c60a222f6c000000000000003e70e304171dfc00000009c611183f521a082a00000653fc4e562dd8ab31568557397d018398813f1c306c8368035615404b5310cbbb00002551570000000099638b47f20000a8f31e841c3dc0f96000000000009d329fc000214904939fc3663f24d4a198ce323e5c0001b84689025c5472ce8ee21660743201c9a83c1c61c0000fbe057439e1e103a015ac731000012919bc46a1a9867200a80003a7caa8348029e00002ba1d54def000000000000003a7856a11f000028ac000190902222240000f80000000000000001490000e1401a80b00b1000000007720000de500000000000a3520980000000d6222806482b2c752398400000000000154bfa0000f98156493621ec09d0000e1710a800038ac5ce0668000409872300004653d7c00000000000000000320400023b8c4619b470204ec45310c07dd1cc883e25e4000312491135e4f102e142ff23c8dfa0000e0105d4add0694
  | 35 => 0xc70b12440000000b403a142592f7c000192427100006be1814d593100d193f800000ef851a33200001f1c0001d901a001dc9d0000057d2a4c0e3000000000000000000000000031c07e49c505c800000009cb00000000000b7800001ed000000000000001bd49a600004aa000000000000000000ac73ae40002eb0edd1f104733b80a5b3534dc70bb400040a80000b485f2000000000000002a540000000fec22d40a43790b4c000000025f89e90000a692050c540ea400000000001ea4f310000000000000000007463ea4ea038443202084bcc007473b2644fac3ce41a60000cbe22a052801980000000000000054d3d305e30da0436102c6c43dacb7e01f0b280000ad618588ae2dbc9ae28c83ac0c78c2a347873c1fd4e7832546dd028403a2114562097d03e3568195283466c2a98faa35c81903550ece135c44216d400000000000000b59000000013600000000771049c0000000ccd16a89a229e8874304400006146830a640001a1c7e615d4fce39cc57024f4e6c1f500001828bc318e8000240065d2fe0bb0000070309a0da800002283b4c09e0e94f8738143133820931218438920b40000000000000000037f8efc24ec55b398cf323be04f21ea800005782452d2c505033864d2e0800000000000000c6634880d000006311fd0f40172c101000000000001ad0000deb0000f371a900740dc83590e286d3000000039b85713e4c4672a78f210000e6d000101f32242620000efd00000003734f36000066237300003a38000000087f109885721e88c70000e9640d0676000054100000003a4c0001fb000018682b025b08bc36084ad0e08000367c00000004e001589662bbc14f0000000000000027e8af6282c615183000000003d805e81b82474e74381c9f8111c78b27c892315d881b0980946199827723a4d461c1cfff000086d10840f213e881010d0000332c5531c704f739640000b642b4225c6273ec87413ec00000ba400013b80000000000000056f0c845a13848f680000000000000000000000000000000085f0000000340000000000000000e0221207b31228ebf000011a0db053c1e3828600000000000279245800000000000000fb320440000000e3e012400027cc00013f89e3090c363142ce24344c000000000021a8d2e1428132257901a3cf48e400000000000018000000024e503f000000014380003fa00c12bf800040b497100000000acc68408909dd02807300000dd2386800032e0000401010f0000c7900000001958b971634fdc1ae80000b7c4f91e40d4537d4f990514c1019a8b5720701370664d750b80a83299400024f0c130000f53199cc3d40bc2d8000049500001ef130800030b0ba633300001afc18339d903c0b2c0002c9ca9c107c00e1f9cb0c3dfcc8434184d500000031cb8c2114987472c8c75b
  | 36 => 0x8000062e000083f32b800018f0d701c480000000000000051d1d8c0000edc0b80000000000000000000000f5c5842ee0413377caff35d8f1e3d1cdd830c503d026c824388019c1eb8b1b36883d5232c4890000d04000000021781bb0000cac2db0000401800023403a32fbc1ec15a48203a7472a238c45b0000000273c46100004863078f5c3824f573b9000000005bc0000a921cd40002ae042800002c3000059e36906e3253cc2900005ca3a3404d38f487220dcb553864dc40838e540cf0dda02a079f0dc01be00000001c8867e0894d4f1284dd900007c2000056d140800000000002c08cab2d7c70d2fb42ac06c8e5d00007082e4c000362c46600b0059266c3842b8c000410474227280003d604eb1554ef70000441132c0c70000c441b0cf0d337c4040ccc1fe1f6cd1436280001d38bc11f3c000262c1f023784a218a40000000208259010a1440cbd3d245350f3cdba0000414335400014547af37800000000c6500f07f02558000341437a0d90a4924c8000090000000780000000674000000037fc63b392473a000000009cc1190000000000100c33d400013ec4790000347329000000007e200802891e5800000000000000c6d000005e4040f8332a80003ce8000000000000005cd11283220000953000005c000000000000000000ffd000000003500000110511218800000000003f0843100000000000da30b9400004e4be7000011c0c6000000002d51f242e703c4c6434607ea10949930000f2500000002b90d87000000000002a8217030c387c0000000000014445a0000000169c6d000008171d9800008cc0002c50171000011f00002f03fa46aa27a80001acc6ed2b80800000000000000000000ee7331894b145901c3df40eb1f6059a1808000063c00002d8e812d144bf31d4d711238c5a00007571e6c4f31e080c9050c3710000a1d070c4ce06c0d7f3e687c100001f726e40000000cd600000000000000000065a38ccca6000000038e00000ddc9e7000000002f0ace3f8414b0bc4f0c3a543240f881381840b0030545632e50b33020083333445781694de300000000000c69362099e3dd4cf806c4d801d3c1683b982e62b780001fe00001f386ef00000002ef800000003eb2c4cad2000025830e4a0e25a4ea200008a2108000000000000000999000000000000ea0000a903c54d5038d00000000e153b508bd2858a7b21e02290c20000000000000005ef1edc000000060e28ec0000000e180000c833b2000000003ae38845e600000003cd0000033c00000009550d9421b1a480000000ed21a9cd5c000028c0000000152400000000002fd0fa8000000000007ff00008150000000243c0000000be63bcc35e00000000aa410900001670000e390000bca000068c0000e163df00003fd400010acb3814d0b5c00000001a4
  | 37 => 0x1a146af0f50e452168000000066909080d900b42b53368dc20638607000097
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc78655c03244001976c8b8064880032e191700c9100066db1ae01922016cd8635c032440019d6c4b8064881271d9db65cc51024eb9386cb98a2047cb676d93314408fb64e1b26628800395d9763cc510005b8c2ce198a20049f3875c331441030fd0dbaa62880030f193754c510386b8086ea98a200087e87d9531440930f90fb2a628812b950c7654c5100061fbaec898a2000c3c75d9131440091eb0fb1862880023de1d630c510024f8402e418a208187c865d72144001878c8bae42881af5c04175c851024c3fc3ecb90a200087d87d97214400187ce9b2e42882022f21974c85100061fb2ae990a2000c3c655d321440d5b6020ba6428811e2fe1f64c85100045ec3ec990a2000c3e75d93214400187aebb2642880127ca0273885100047ac3ec710a2007ae48258e21440938e8edb2a42881275c1c3654851023e5a3b6c890a2047db070d9121440091ed0d39a42880127ca0273485100066a39ec690a20078f48758d2144001cceca31242880127ca1f7048510005b8c28e090a200087f855d930440050f90abb260880022fe11764c11000c5e422ec98220008ef825d9304400f1d904bb26088127960c3654c1100043fc2aec902200287c855d9204400117f08bb240880062f21176481100046fc1aec90220168dc835d920440091ed0db8a40881ef1dc4374594103de3d086e8b28207bc7510dd165040ff8f221ba2ca081f61f61e74594100061fba4e8b28207ea77815d165040074e902ba2ca080030fe1174594100063bc0ae8b28207cc74815d165040fb8ee20ba2ca081f71e84174594103ee3a882e8b28207cc79105d165040f70fd0e3a2ca0800317dce73594100051f420e6b282000a3d841cd65040010fd0fa1aca080021f61f43594100061eba686b282000a6e82d0d65040014db05a1aca080030f5d143594100043f43886b28200087d8710d65040014bf06b92ca080029720d72594100051f420e4b282000a3d841c965040010fd0fa12ca080021f61f42594100061eba684b282000a5e83d0965040014bb07a12ca080030f5d142594100043f43884b28200087d87109650400387ce8aa4c6080030f5d15498c100070eaa287318200087f855ca63040050f90ab94c6080123721d4358c100070eaa286b1820008df835d5620402d1b906baac4080123b21d425881000716aa284b10200287c85dd932040010ff0abb2640800a1f215764c8100043ec36ea990200087e8759532040010f90eb2a64080123721d634c8100247643ac4990200287e855d8320400f1eb02bb0640801e3e601760c8100043fc32ea190200087f8759432040010fb0eb2864080030f9d1650c81001e3b38aca1902004c7a70594320400187ccaba064080030f595740c8100063b32ae21902000c75655c432040018f4cab8064080031e595700c810
  | 1 => 0xecaba4c4880030f19574989100061f3aec93122000c3d75d92624400187cea324c4880030f5d464989100143f436eab12204987c86dd562440010fd0fb2ac4880030f1d365589100043f438cab122000c3c74195624400317d0dba2c48811e2f21b74589100061fb2ee8b122000c3c65dd1624400117d0fb22c4880030fdd764589100061e3aec8b1220008be87191624400187eea322c4880030f1d464589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100062fb28e6b122000c5c651cd624400193ec839ac4880032719073589100043ec26eab1220008bf845d5624400317908baac48800237e0d75589100b46e41aeab122000c3f75dd16244001878ebba2c4880030fe1774589100061e42ee8b12200087f855d162440050f90aba2c48800237e0d74589100b46e41ae8b122000c3f751d16244001878ea3a2c4880021fa1f54589100143e43ea8b122000c3f74d516244003878e9aa2c4880021fa1d54589100043e43aa8b122000c3f745516244003878e8aa2c48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317d5373589100062eaa6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c5f541cd62440018baa839ac488003331cf725891000e563a484b122000ccc7390962440031d90ea12c4880038b55142589100066639a84b122081c7571194624410196ae2320c4880023be1d62189100056641ac4312200087f855db32440050f90abb664880022fe1176cc91000c5e422ed992200087f855da32440050f90abb464880022fe11768c91000c5e422ed19220048f4865c632440093e100b8c648800a1fa17764c9100043ec2eec99220018be84dd9324400117b09bb2648800a1fa16764c9100043ec2cec992200087f855d932440050f90abb264880022fe11764c91000c5e422ec992200287c851d932440010fd0dbaa64880030f193754c9100043f43eca992200087c87d95324400187eebb2264880030f1d7644c9100247b436e29922000cb464dc532440071f50db8264880032e193704c9100143e42cec19220018bc849d832440071e9033b064880123e202760c9100043fc2aec192200287c855d8324400117f08bb064880062f211760c9100043e432ea1922000c3c645d432440010ff0fb2864880021f61f650c9100061f3a6ca192204ac7671d9432440938f4e1b2864880022f219740c9100061fb2ae81922000c3c655d0324400117f0fb2064880022f61f640c9100061f3aec81922000c3d75d90324409196ce3b20648811f2e9c3640c9100247a432e21922000c77655c432440018e8cab8864880032dd91710c9100065a322e21922000cd7635c432440019cec4b88648800e3e219700c9100063db2ae01922000
  | 2 => 0x550d91100051f42cebb222000c3d751d7644409156d023aec88811ead60475d911023d5d400ebb222048ab9801d7644400147d0e3aec8880030fa1c75d91100071b408ebb222000e35811d76444001c75003aec8880038e60075d91100061fbaee7b222048ab681dcf644408f56b03b9ec8880028fa1673d91100051ec2ce7b222000a3f855cf64440014790ab9ec8880030fdd573d911000557c12e7b222000aac825cf6444001c3ea729ec8880022fa1c53d91100045ec38a7b222000c3f75dcb644400147d0b396c8880028f61672d91100051fc2ae5b222000a3c855cb644400187eeab96c888002a7e0d72d91100054e41ae5b222048ab6811cb644408f56b02396c8880022fa1c52d91100045ec38a5b222048e3651d4764441038eae232ec6882032d5c464d8d100247ac0eebb1a20048f581dd363440f78eae3aa6c6880030fdd154d8d1000e1e3a2a9b1a207dc7571553634400187ce9b2cc6880030f9d06598d100061fb2ae931a2000c3c655d2634400187cebb24c6880030f5d76498d100061f3a8c931a2000c3d7519263440010ff08bacc6880030fa157498d100061ec2ae931a200287f87d5263440010fb0faa4c6880070f9d35498d100061eba6a931a200087f8755263440010fb0eaa4c6880070f9d15498d100061eba2a931a2001c9e7450e6344001c3aa8a1cc6880021fa1f6558d100061e3a6cab1a200087e871956344001878e832ac6880030fd977458d100061e32ee8b1a20008be87d91634400187eebb22c6880030f1d76458d100045f438c8b1a2000c3f751916344001878ea322c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880031bd947258d1000636328e4b1a2000caf641c96344001958c8392c6880021f6137558d100045fc22eab1a20018bc845d563440011df04baac68801e3b2097558d100061fbaee8b1a2000c3c75dd1634400187f0bba2c6880030f2177458d100043fc2ae8b1a200287c855d163440011df04ba2c68801e3b2097458d100061fba8e8b1a2000c3c751d163440010fd0faa2c68800a1f21f5458d100061fba6a8b1a2001c3c74d51634410b8d8e5aa2c6880021fa1d5458d100043e43aa8b1a2000c3f745516344003878e8aa2c6882131b1c95458d1000e4e3a486b1a2083ccc7290d63440031b90ea1ac688003875514358d104166639286b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000c6f54dc963440018daa9b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100046fc3ac631a2000acc8258c634400387ce8aa0c6880030f5d15418d100043fc2ae431a200287c855c8634400187ee8aa6c4880070f1d154d89100061f3a6cb3122000c3e74196624400187
  | 3 => 0x298840048dd835d831080091eb02bb062100070f9d15498f100061eba2a931e2000e1d5450e63c40050fd0fbaac7881c31d1c77558f100043ec26eab1e20048f4815d563c40e10fd0e3aac78821b1d1c47558f100043fc2ae8b1e200287c855d163c40091e902ba2c7880021fa1f5458f100143e43ea8b1e207bc7471d5163c40010fd0eaa2c7880021f21d5458f103ee3a38aa8b1e20038dc8750d63c4001c3aa8a1ac78800e3b21d4258b1000716aa284b16200087f855db32c40050f90abb665880123d20576ccb100043fc2aec996200287c855d932c40091e902bb2658801e3ee19700cb100247bc3ac798e20008f48758d21c40091b906bacc7080070f9d15498e100061eba2a931c2000e1d5450e63840091bd0fa9ac70800317dd75358e100256d406a6b1c2000a9d8414d63840091b90ea1ac708003875514358e100247643a84b142000e2d5450962840010ff0abb2650800a1f215764ca100247c402ec9942000c5c7598d32840091b90eb1a6508003171d5634ca1003d66412c699420078f7865c432840018b8eb31a6308003171d5634c61003e57312e990c2000cad7458b21840010fd0dba6ca8800a1fe1f64d95100061eba6c9b2a200087d8799365440010ff0eb26ca880261f61c64d95100061eba0c9b2a2000a5e8319365440014bb06326ca880029ba0864d951000536c10c9b2a2000c3d871936544001c3d06326ca880038760c64d951000717410c9b2a2000e2d821936544001c6b02326ca880038e60064d95100071a32483b2a2049a74865076544001c70c9206ca88003cc90640d95102553c43281b2a200087d879d3654400187f08ba6ca880021fa1c74d95100061eba0e9b2a2000a5e831d365440014bb063a6ca880029ba0874d951000536c10e9b2a204aa76811d365440934eb023a6ca881269ea0074d95102553cc00e9b2a204aa7681dcf65440934eb03b9eca880028fa1273d95100051ec24e7b2a2000c5d731cf65440010fd0fa1eca880021f61f43d95100061fba687b2a2000a6e82d0f65440014db05a1eca880030fdd143d95100043f43887b2a200087d8710f654400147d09396ca880028f61272d95102553b408e5b2a2049a75811cb65440010fd0fa16ca880021f61f42d95100061fba685b2a2000a5e83d0b65440014bb07a16ca880030fdd142d95100043f43885b2a200087d8710b65440930fd0fa0eca880021f61f41d95102543f43e81b2a200087d87d03654400147d0dbaec8880030f9db75d91100051f430ebb222000c3e761d7644400187cedb2ec8880022f61e65d91100051f42ccbb2220008bf87597644400147d0c32ec8880030f9d865d91100071ac08cbb222000e39801976444001c68cb28ec88811ead21951d91100071c32ca1b222000f325194364440915710ca86c888003cc54
  | 4 => 0x308001c3aa9a1ac61001eb3a0b4358c200246e43a86b184000e1d5450d63080095b100a1ac61000297a144358c200052ec2886b184000c5f759d5630800159f04baac61001eb32097558c200054f420eab184000a9d841d563080014bd0b3a2c610002976167458c2003d67414e8b184000acd829d163080015b700ba2c610012b62017458c200052f428e8b184000a5d851d163080f7cb441aa2c610217964835458c203ed2ec2ca8b184000e1f549516308001c3f08aa2c610003879d15458c200070eba2a8b184084e1f425516308109c3a84aa2c6101f7968815458c204272c902a8b18407ba5e8515163080095b50138ac61000297e157158c200052e42ae2b184007acc825c563080095b50028ac610002b66005158c200052f42e82b184000a5d85d0563080011bd0e20ac6100023761c4158c200052f42882b184000a5d85105630800f59d0420ac610002b36084158c200256d40082b184000ad98010563080fb4eb0b2a4c2100038dd5254984200071bc22a93084084e37425526108109c6a84aa4c2101ee9da1454984200072ba9ca73084000ab68414e610800156b0829cc2100029da1743984200053ac2e873084000e3554d0e610800f5cd05a1cc210002b960b43984200071aaa2873084000a768510e61080014eb0a21cc2100123da1f51584200247a43aa2b084004af28014561080091ed0fa0ac2100029da1741584200053ac2e82b0840048f48750561080014ed0a20ac2100029d61441584200056b41882b084000ad583105610800f5cd0420ac210012bca00415842002579400eab084000af1801d561080014ed0b3a2c2100029d61674584200053b428e8b084000a75851d161080015ad063a2c210002b560c745842003d73410e8b084000ae5821d161080095e5003a2c210002bc60074584203ed3ac2ca8b084000e37549516108001c6f08aa2c2102138dd0954584204271aa12a8b08407ba768515161080014ef0ab9ac2100029d215735842003d72412e6b084000e575394d610800156d0829ac210002ad61053584200053b42e86b084000a7585d0d6108001c6aa9a1ac21001eb9a0b435842000572c1686b084000e355450d61080014ed0a21ac2100029d61443584200263d382cb1884004cba7059231080099b4e0b1c62100031e595708c4200065cb22e11884000cd9635c231080079e4c2b84621000a1f217764c4200246e41eec98840048f481dd931080010ff0abb2621000a1f215764c4200043ec36ea9884000c3e64dd531080e18ecc3baa62100021fa1d654c4200043e43aca9884000c3f755913108001878eab22621001f2b1c9644c4200062fbacc69884000c5c7598d31080018beeab1a6210003171d5634c42000656b26e49884000ccd63dc931080018eeeab0a62100031d1d5614c42000673b92c
  | 5 => 0x3171d7634c9200062e3a8c69924001cae7450b6148001c5aa8a16c2900023de1d61185200143f42cec98a400087d859d931480010ff0abb0629000a1f215760c5200b66631ae418a4016cd8635c031480079e0c2b84429005b3318d72cc1200043fc2aec982400287c855d9304800175308392609001f361db324c120024ec43a649824007cd8764c9304800fb90e499260901f61f61e74594200061fba4e8b284000c3f845d165080f70fd0e3a2ca1000317dce735942044537c12e6b284007a6c825cd650800147d0839aca100028f61073594200043f43e86b28400087d87d0d650800187ae9a1aca1001e9ba0b435942000536c1686b284000c3d7450d65080010fd0e21aca100021f61c43594200253d400e2b28400fa79801c565080010fd0fa0aca100021f61f41594200043f43882b28400087d8710565080014bd0620aca100029760c415942003d3741082b284000a6d8210565080094f50020aca100029e60041594200061fbaceab20407da3d879d564080f7c5e413aac8101ef8b48275590200061fc3aeab204084c3f725d5640810987ae4baac8101f78bc8175590203ef16902eab20407ba3e851d5640800147d0bb9ac8100028f61773590200061ebaee6b204007aae82dcd640801d55b05b9ac8100030f5d5735902043d5dc02e6b204004ab8805cd640800147d0a39ac8100028f61473590200070fa9ca6b204000aaf8254d640800f55904a9ac8100022fa1c53590200045ec38a6b204000a3e85dc5640800147b0bb8ac8100028fa1471590200051ec28e2b204000a9e831c5640800153b0638ac81001eaba08715902007556c10e2b204004aba801c5640801d5730038ac810012aea0051590200055cc00a2b2040048dc835d663080091b906ba4c6100070f9d15498c200061eba2a93184016c5f75d4e63080014bd0ba1cc610002976174398c200070eaa6873184007ace82d0e6308001c3aa8a1cc6100021fe157198c200143e42ae331840048dc835c6630802d8beeb3acc61000297a167498c200052ec2ce93184007ace829d2630800159b053a4c6101f6976165498c200070faa4a93184000e1f845526308001c3ce8aa4c610003875d15498c204270fa12a93184084e1d4255263080f74bd0a2a4c61000297e157198c200052e42ae33184004ada8014663080015b30028cc61000297a174198c200052ec2e8331840168de8710663080011bb0e20cc61000297a144198c200052ec28833184007ace82106630800159b0420cc610012b6a004198c200056cc008331840078ec825d563080091f100ba2c6100070f9d15458c200061eba2a8b1840048de87d4d63080018beeba9ac61000b179d65358c200246e43aa6b184000a9e8414d630800153b0829ac61001237a1f4358c200052f42e86b184000a5d85d0d6
  | 6 => 0x47bc3ac230a60038f6819da214c0010ff0abb0429800a1f215760853003e66312e610a6016dcb325cb304c00387ce8aa2c4180030f5d154588300247643aa4b1060048ec87509620c001c5aa8a12c41800a1fa1f75584300043ec26eab08600087f855d1610c0050f90aba2c2180021fa1f54584300143e43ea8b08600087e87551610c0010f90eaa2c21800b1d1d651584300247a43aa2b0860048f487505610c00f8dcc4bae421801f2b98974c843000636baac59086000cad7458b210c0010ff0abb2421800a1f21576484300b66a39ac29086000c7b54dd9300c0018f2a9bb2601805b3694f764c0300066ca9eec9806016ecb32589300c0016b70a9926018002d6e15314c03000e1f3a2a931e4000c3d7455263c8001c5aa8a14c7900021fe157198f200143e42ae331e400287e87dd563c80010fb09baac7901e21fa1c7558f200051ec20eab1e400087f855d163c80050f90aba2c7900023de057458f2001c7a40ae8b1e400087e87d5163c80050f90faa2c7900021fa1d5458f200043e43aa8b1e4001c3e7455163c800187ae8aa2c79000237e0d75587200b46e41aeab0e4000e2d5450961c80010ff0abb2639000a1f215764c72003e66392c6986407bc7a70d52638800387ce8aa4c7100030f5d15498e203ee3d382a931c4000e1d5450e63880091b90ea1ac710003875514358e200143f43eeab0c400087d84dd5618800117f08baac3100062f211755862000c5f43ee8b0c4000c3f75dd16188001878ebba2c3100030fe1774586200061e42ee8b0c400087f855d161880050f90aba2c3100030fdd474586200061e3a8e8b0c400087e87d5161880050f90faa2c3100030fdd3545862000e1e3a6a8b0c400087e8755161880010f90eaa2c3100030fdd1545862000e1e3a2a8b0c4002c747594561880091e90ea8ac3100072d1d241586200247a43a82b0c4004cf27058731880010ff0abb2631000a1f215764c6200045fc22ec98c40018bc845d931880099e0e0b0a43100127621d324c22003ee4392649844000c5d75d4f634800153b0829ec69000637e1d43d8d200070eaa287b1a4001c3e74552634800187ae8aa4c6900063be1d4298d2000716aa28531a400087d84dd563480011bf06baac6900023be097558d200043fc2ae8b1a400287c855d163480011ef02ba2c69000e3d2057458d200047dc02e8b1a400087e87d5163480050f90faa2c6900021fa1d5458d200043e43aa8b1a4000c5c75dcd63480018d8ebb92c69000237e1d6318d200052e42ac631a40168dc835d4634810b8f2e1aa0c6900070f9d15418d200061eba2a831a4084c79705506348001c3aa8a18c69020b365c14318d2003e74b848431a4001cae745086348001c5aa8a10c690003a350d4218d2003e74b828431a400087f855c463480050f90ab88c69
  | 7 => 0x74854ca618c0014ed0a194c3180029d61432986300055b4206530c6000ab5840ca618c0095e500194c318002bc60032986300061fba2a8b0c6001c3c74551618c0091e90ea8ac318012bca0051586300053b42e82b0c6000a7585d05618c0091e90ea0ac3180029da1441586300053ac2882b0c6000ad583105618c0015cd0420ac318002b960841586300257940082b0c6000ab6849d5618c00156b093aac318012bca00755863000578c00eab0c6000a76859d1618c0014eb0b3a2c3180029da1474586300053ac28e8b0c6000ad6831d1618c0015ab063a2c318002b9a08745863000572c10e8b0c6004af2801d1618c0015e3003a2c3180038dd5254586300071bc22a8b0c6000e3774551618c001c68e8aa2c3180029de1573586300053a42ae6b0c6000ab7845cd618c00156908b9ac318002b9e09735863000572412e6b0c6004af280d4d618c0015e301a9ac31800395d4e53586300055b420a6b0c6000ab58414d618c0014ed0ba1ac3180029d61743586300071aaa686b0c6000ae682d0d618c0015cb05a1ac318012bca03435863000578c0686b0c6000e355450d618c0014ed0a21ac3180029d61443586300053b42ce4b0c6000a75859c9618c00156d09392c318002ad612725863002579404e4b0c6000ad7835c9618c00156d08292c318002ad610525863002579400a4b0c6000af180149618c0014ed0ba12c3180029d61742586300071aaa684b0c6000ad683d09618c0015ab07a12c3180038d55142586300053b42884b0c6000a7585109618c0095e500212c318002bc60042586300053bc2a64b0c6000a74854c9618c0015e700992c318012bc20132586300053b42864b0c6000a75850c9618c00156d08192c318002ad61032586300076299064b0c6004af2800c9618c0015e300192c3180131e9c1658c6300063cb2ae118c6003cf2615c2318c0010fb0dbaa63181c31d987754c6304343e43aca98c6000c7775585318c0018e8eab0a63180033c587704c6300143f42aed90c600087f865d7218c0d78ecc2bae43180021fe1d65c86300043ec3acb90c6000c3e74597218c00187ccaba643180030f59574c86303565b30ae990c6000c7675587218c0018eaeab0e43180032d9d161c86300065aba2c390c6000cf1615c3218c0018bccbb9a43180031799473486300066a39ac290c6004c7a70594218c0018f2cab80431800f3c985700863000556c20a5b1260018ef8750b624c001c5aa8a16c4980021fe1571d89300143e42ae3b1260008bf845c7624c00317908b8ec4980023be1d62189300053642ac4312600287e859db324c0010fb0b3b6649800e3da0676cc9300047ac0ced9926000c6c75d89324c0f18b8edbaa64981e39318b754c93000567436e49926007ace86d89324c001ab6ea38264980038755143d85300
  | 8 => 0xe8aa0c690a131d5c55418d210070eaa28631a4282cd57150c634840f9cae3210c6908072b9d14218d2100716aa28431a4200e8d43508634840f9cae2a10c69085b360c17018d210062e3aec69924200c5c7518d32484010ff0abb2629080a1f215764c5210062e3aec698a4200c5c7518d31484018e8ea3b262908031d1db754c5210043fc2ae7b02420287c855cf6048401c5aa8a16c0908023ee1d601812100e1f3a2a93184200c3d745526308401c3aa8a1cc61080a1fa1f7558c210043ec26eab18427087e871d5630840147b083aac6108021fe157458c210143e42ae8b1842038f4815d163084010fd0faa2c61080a1f21f5458c210043f43aa8b18420087c87551630840387ce8aa2c6108030f5d15458c210162e3aca6b1842038dc8754d63084071b90ea1ac610803875514358c2101c7c43aa0b0042038f887501600840387ce8aa2c5980030f5d15458b300143f42ee2b16600087d85dc562cc00317d09b8ac5980022f6137158b300062e3aeec9966000e1d5450d61cc0079e4c2b8443981f61f61e74596300061fba4e8b2c6000c3f845d1658c0f70fd0e3a2cb180029be09735963000536412e6b2c608ca7b805cd658c0010fd0fa1acb180021f61f43596300061eba686b2c6000a6e82d0d658c0014db05a1acb180030f5d143596300ec3f43886b2c600087d8710d658c0094f501392cb1822e9e60272596300052fc1ae4b2c608aa5c835c9658c00147d08392cb180028f61072596300043f43e84b2c600087d87d09658c00187ae9a12cb1800297a0f42596300052ec1e84b2c6000c3d74509658c0010fd0e212cb180021f61c42596300253d400e2b2c601da79801c5658c0010fd0fa0acb180021f61f41596300043f43882b2c600087d87105658c0014bd0620acb180029760c41596300053741082b2c6000a6d82105658c0094f50020acb180029e60041596300247643a84b146000e2d54509628c0050fd0bb8ac5180021f6177158a300043ec36ea994608987c87595328c0610ff0cba865180761fe1d650ca300061f3a2ca1946004c7a70594328c00187ccaba065180030f595740ca3000726b2a641946000c76659c4328c0018eacb38865180031d995710ca300063ab2ae21946000c7a655c0328c0018f2cab8065180038dd5254986300071bc22a930c6000e575394e618c00156d0829cc318002ad61053986300053b42e8730c6000a7585d0e618c001c6aa9a1cc318002b9a0b439863000572c168730c6000e355450e618c0014ed0a21cc3180029d61443986300056bc1aa530c6000ad48354a618c00156d08294c318002ad61052986300053b42e8530c6000a7585d0a618c001c6aa9a14c318002b5a0f42986300056ac1e8530c6000e355450a618c0014ed0a214c3180029d61442986300053bc2a6530c6000a
  | 9 => 0x54588310061eba2a8b1062038ec87549620c42d59906a92c41880e3b21d425883100716aa284b106200c7475dd9310c4018eea9bb262188031d553764c4310b66b29eec9886200cd553dd9310c4018eeedbaa621880e3e21d505803101c7c43a80b00628487d879d165c840187ee93a2cb9080297a0e74597210052ec1ce8b2e4207a6e829d165c851f4db053a2cb908030fe11745972142c3f438e8b2e4200c5f739cd65c840147d0839acb908028f61073597210043f43e86b2e420087d87d0d65c840187ae9a1acb9081e9ba0b435972100536c1686b2e4200c3d7450d65c84010fd0e21acb908021f61c43597210052fc1ae2b2e4200a5c835c565c851d4df04b8acb908021fa1f41597210043ec3e82b2e426ba76811c165c84014eb02382cb908021fa1f40597210043ec3e80b2e420087e8710165c84010fb0e202cb9080297a0c40597210052ec1880b2e4207a6e8210165c84014db04202cb909ae9da0440597210053ac0880b2e4200c3f759d564c850947b0f3aac9908030fe1d75593214261fb92eab264284c3d725d564c850b47d0a3aac9908028fa1773593210051ec2ee6b264200c3d75dcd64c840f55d05b9ac990896ab60b73593210061ebaae6b264200ab7815cd64c84d556902b9ac9908028fa1473593210051ec28e6b264200e1f5394d64c840117d0e29ac9908022f61c535932146d57c12e2b26426ae3651d4564c840147d0bb82c9908028f61770593210051f428e0b264200a3d851c164c840153d06382c990802a760c705932103d57410e0b264225aad821c164c84d556d02382c990802ad60470593213555b408a0b264200ab58114164c840387ce8aa4c7908030f5d15498f2100716aa28531e4201c3e7455163c840187ae8aa2c7908021f61b754c7210061f326ea98e420087c8759531c840187eeab2263908030f1d5644c72103e56392c898e4200cad64dc931c84050fd0bb9ac1908021f617735832100e573a284b064200e2d5450960c84ff8ece3aa4c7108070f9d15498e210061eba2a931c427cc76715526388401c3aa8a1cc71080e3721d4358e210070eaa286b1c4200c3f745516088403878e8aa2c11080a1fa1773582210043ec2ee6b0442038f88754160884071f10ea02c110803175d753d8d210054ec20a7b1a42018df8750f6348401c3aa8a1ec6908070f9d15498d210061eba2a931a42018ef8750a6348401c5aa8a14c6908021fe157198d210143e42ae331a420087d84dd563484011bf06baac6908021fe157458d210143e42ae8b1a42008f7815d163484011f700ba2c6908123e2017458d210043f43ea8b1a420287c87d5163484010fd0eaa2c6908021f21d5458d210062e3aee6b1a42008df8758c63484014b90ab18c69085a3720d7518d2142e3ab8ea831a4201c3e74550634840187a
  | 10 => 0xb006400eca83509600c801d9306a12c019003aad0d42580320076521a84b006400ea943509600c801d9286a12c019003a250d42580320053dc2ae2b006400a78855c5600c80157708b8ac019002ae21171580320b56c41ae2b006407ae8825c5600c8014f50a38ac0190029e61471580320056dc1aa2b006416ad883545600c8011f50e28ac0190023e61c51580320053d42e82b006400a7985d05600c82d5b507a0ac019002b660f415803203d7541682b006400ae982d05600c801d528520ac0190023ea1c41580320047cc3882b006400a7a85105600c8014f30a20ac01905ab6a0c41580320056cc1882b006407aea82105600c8015d30420ac019003aa508415803200e1f3a2a8b166200c3d7455162cc401c3aa8a1ac19880e3b21d4258a3100716aa284b146200c3f74551608c403878e8aa2c11880e3e21d505823101c7c43a80b04620087e86dd3654c4050ff0fb26ca988030f5d364d95310043ec3cc9b2a6200a6e82993654c4014db05326ca988021fe1d64d953115c3ec38c9b2a6200c3d74193654c4e14b90ca1eca9880347dd143d95310070e32287b2a620087d879d3654c40187f08ba6ca988021fa1c74d95310061eba0e9b2a6290a5e831d3654c4e14bb063a6ca989c21fa1f43d95310043ec3e87b2a6200c3f74d0f654c4014dd05a1eca988029b60b43d95310061fba287b2a620087e8710f654c4570fb0e21eca988028fa1272d95310051ec24e5b2a6270a76811cb654c4014eb02396ca988021fa1f42d95310043ec3e85b2a6200c3f74d0b654c4014bd07a16ca988029760f42d95310061fba285b2a620087e8710b654c4010fb0e216ca989b297a0f71d95310043f43e83b2a620087d87d07654c4e14ed03386ca988029d60670d95310043f43e81b2a620087d87d03654c4010fd0e206ca988021f61c40d95310052f41881b2a6200a5d83103654c4014dd04206ca988029b60840d95313853b40881b2a6200a7581103654c4031df0ea16c4988038b55142d89310061f3a6cb3126200c3e74196624c40187ecaba4c4988030f195749893103e56312e93126200cad74d8a624c4010fd0fb2ac4988021fa1c655893100477c3ac4312628687e86dd5324c5130fd0fb2a649880a1f216760c9311843e432ea192620087f87d94324c4570fb0fb2864988030f9d3650c9313863b38eca1926200c3f655d0324c401878caba0649880393d95320c9310063db2ce01926200c78659c0324c4018f6cab8064988031e195700c9313872bb1ecb98a6200e1d5450f604c4050fd0dbaac0989c21f21b75581310043f43ecab026200c3c74d95604c4010fd0e32ac0988030f1d065581310061fb2ee8b026200c3c65dd1604c4018decbb92c0988031b197725813100637b28e4b026200c6c651c9604c4011f70eb00c0988070f9d1
  | 11 => 0xc80156908b82c21905ab520d705843203d72412e0b086400a76851c1610c8014eb0a382c2190023da1c50584320047ac38a0b086400a7685d01610c8014eb0ba02c21905ab5a0f40584320056ac1e80b086407ae682d01610c8015cb05a02c219003a950b405843200752a1280b0864008f687101610c8011eb0e202c2190029da1440584320053ac2880b086416ad683101610c8015ab06202c21901eb9a08405843200572c1080b086400e3b54952600c801c7708aa4c0192138ed0954980324271ca12a93006416e5a53d4e600c8014f50ba1cc0190029e61743980320071caa6873006407aea82d0e600c8015d305a1cc0190038e55143980320247d438a330064008f987146600c8014f50ba0cc0190029e61741980320247d4388330064008f987106600c8014f50a20cc0190029e61441980320b56d418833006400ad983106600c80f5d50420cc019002ba60841980320070eaa286b006401cae74509600c801c5aa8a12c019003a350d425803203c7d43ea0b0064078f887541600c82d5b106a82c019002bca04505803200578c08a0b0064078fa87d01600c8014f50ba02c0190029e61740580320b56d41e80b006407aea82d01600c801d5285a02c01901e3e21d405803200754a1280b006400a7a85101600c8014f30a202c01905ab6a0c405803203d7541080b006400af281101600c8015e302202c019002b6e0d75580320b56c41aeab006400aeb825d5600c80f5d104baac019002bca04755803200578c08eab006400a7a859d1600c8014f30b3a2c01905ab6a0e74580320056cc1ce8b006407aea829d1600c8015d3053a2c0190029ea1474580320053cc28e8b006416ada831d1600c8015b3063a2c01901ebaa08745803200574c10e8b006400af2811d1600c8015e3023a2c0192179a90b545803242f2d996a8b006485e5932d51600c801c76a92a2c01905ab6a0e54580320056cc1ca8b006407aea82951600c8015d3052a2c0190038ee1154580324271da12a8b006484e6a42551600c909c7284aa2c01921396cc954580324272c992a8b006416ada83151600c8015b3062a2c01901ebaa08545803200574c10a8b006416e5a53d4d600c8014f50ba1ac0190029e61743580320071caa686b006407aea82d0d600c8015d305a1ac01900396d5243580320072caa486b006416adb8290d600c9075b30521ac01920fb290a43580320071caa286b006416adb8450d600c82dd3708a1ac01900396d5143580320074d2a286b006400e595450d600c801d32a8a1ac0190038655143580324156dc1286b006482ad98250d600c905d3684a1ac01920bb290943580324174ca1286b006407eab84509600c801d54e8a12c019003aa5d1425803200735aa284b006400eaa54509600c801cd2a8a12c019003aa551425803200714aa284
  | 12 => 0xbea760c715903203d57410e2b20642faad821c5640c8015750038ac819002ae60071590320055d400a2b206400ab980145640c80147d0bb82c8190028f61770590320051f428e0b206400a3d851c1640c82d53d06382c8190bea760c705903203d57410e0b20642faad821c1640c80156d02382c819002ad60470590320055b408a0b206400ab581141640c8018d8ebbb264190031be17764c8320063642eec9906400c6f54dd9320c8018daa9bb2641905b3394f764c83200666a9eec9906400c6f76dd5320c801c6ea92a4c2190038de1154984324271ba12a93086484e3542552610c82dcaca7a9cc2190029da1743984320053ac2e873086400e3554d0e610c80f5cd05a1cc219002b960b43984320071aaa28730864038f687142610c8011eb0e284c2190029da1740984320053ac2e8130864038f687102610c8011eb0e204c2190029da1440984320053ac28813086416ad683102610c8015ab06204c21901eb9a08409843200572c10813086400e1d5450d610c801c5aa8a12c219003a350d425843203c7b43ea2b0864078f487545610c8015e50028ac219002bc600515843203c7b43e82b086400a7685d05610c8014eb0ba0ac21905ab5a0f415843203d7341682b086400ea542905610c80f1e90ea0ac2190029da1441584320053ac2882b086416ad683105610c80f5cd0420ac219003a950841584320057940082b086400af180105610c8015af06baac21905ab520d755843200579400eab086400af1801d5610c8014ed0b3a2c2190029d61674584320b56b41ce8b086400ad5839d1610c80f5cd053a2c219002b960a74584320053b428e8b086400a75851d1610c82d5ad063a2c219002b560c745843203d73410e8b086400ae5821d1610c8015e5003a2c219002bc600745843242f33216a8b086400e3754951610c82d5ad072a2c219002b560e545843203d73414a8b086400ae582951610c801c6f08aa2c2192138dd09545843242733212a8b086484e3542551610c82d5ad062a2c219002b560c545843203d73410a8b086400ae582151610c82dcaca7a9ac2190029da1743584320053ac2e86b086400e3554d0d610c80f5cd05a1ac219002b960b43584320072baa486b086400e555490d610c907d8c8521ac2190038d55143584320b56bc2286b086416e978450d610c801caea8a1ac219003a595143584320072aaa286b086400e955450d610c801c2aa8a1ac21920ba5d0943584324176321286b086482e954250d610c80fd4f08a12c219003a9dd14258432007523a284b086400e6754509610c801d4ca8a12c21900399551425843200752aa284b086400e2554509610c801d4e86a12c219003b190d425843200752a1a84b086400ec543509610c801d0a86a12c2190029de1570584320053a42ae0b086400ab7845c161
  | 13 => 0x43f438e9b2a6400c3d741d3654c8f10fd0fa1eca990021f61f43d95320061fba687b2a6478a6e82d0f654c8014db05a1eca990030fdd143d95320043f43887b2a643387d8710f654c8e94bd07b96ca990021fa1f42d95320043ec3e85b2a6400c3f74d0b654c8014bd07a16ca990029760f42d95320061fba285b2a6400a7a809c7654c8014f30138eca990021fa1f41d95320043ec3e83b2a640087e87107654c8010fb0e20eca9900297a0c41d95320052ec1883b2a6478a6e82107654c8014db0420eca990029ea0041d95320053cc0083b2a6400a76819c3654c8014eb03386ca9918697a0c70d95323c52ec18e1b2a640087e87d03654c8010fb0fa06ca990021fa1c40d95320043ec3881b2a6400a5e83103654c8014bb06206ca991e29ba0840d953200536c1081b2a6400a7681103654c8014eb02206ca991e393d8f65cc9320051ec20cbb0a6401c3e74553614c80187ae8aa6c299002b560c41d853200572c1083b0a6400af180107614c80147b0832cc2990031ed9670985320063c32ce130a6400c7b655c2614c8018f0cab84c2990033cd85709853201e7830ae130a640087e87d95614c8010fd0e32ac2990028f61065585320051ec20ca30a64008f787584614c80147b0832ec0990070f9d154d81320061eba2a9b026400ad983103604c8015d304206c099002bc60440d81320051ec20cb3026400c77659c6604c8018e8cb38cc0990031dd9571981320063a32ae33026404cf0605c6604c8019e2e3b04c09900a1fa1b75581323c43e436eab02640087e87d95604c8010fd0e32ac0990028f61065581320051ec20ca3026489c5d73194604c8011f70eb00c0992121f61e74594320061fba4e8b286416a5e839d1650c92b4bb073a2ca1901e9ba0a74594324a536c14e8b286400c3f845d1650c90b0fd0e3a2ca190c21fa1f43594320043ec3e86b286407a6e82d0d650c8014db05a1aca1924e97e0d71594320b52e41ae2b286400a7a801c5650c8014f30038aca190021fa1f41594320043ec3e82b28640087e87105650c8010fb0e20aca1905a97a0c41594320052ec1882b286407a6e82105650c8014db0420aca190029ea0041594320053cc0082b286492a5f835c1650c82d4b906b82ca192469be09705943203d36412e0b286400a76811c1650c8014eb02382ca190021fa1f40594320043ec3e80b28640087e87101650c8010fb0e202ca1905a97a0c40594320052ec1880b286407a6e82101650c8014db04202ca190029da0440594320053ac0880b286400c3f759d5640c90947b0f3aac8190030fe1d75590320061fb9aeab206400c3d735d5640c90987ee4baac8192130f5c9755903242d1f428eab206416e1e53d4d640c80147d0bb8ac8190028f61771590320051f428e2b206400a3d851c5640c82d53d0638ac819
  | 14 => 0x300100000201a00103601300100200000200200900000300000500500500000000300000100a00300202500900500500000901900200100000e00e00001300001300600700700001300300000200800300300600500100100300300000100300500000000200300000000300101e00300b00900600000200101000200100000600000000500000100000300b00100a00501100500600401600200700000000000501300100000100200000001400500100c00100001100b02100100000500400200c00100100000400100600500000400200300000100100600300400000300400001000000500600000700600000000300100100100901400000000300900100c00600000100300000200000900000300400900000300000200000e00500400000200100600100100900300200b00000000500e00100200000000100900100200a00000000700500000100000300000000001000000200600d00000500d00500000800100200900400101d00000000000400300100b00300c00100200100300000000000600400000900a00201000200100900101400100000a00000d00000700101900300300101200000200d00000000000000000501601b00300500900f00e00000400000600500600300e00100600000600500100800000a00500000100a00100000100200000c00000200000b00200700000000500701200000000000701100c00000000300c00100100500300000100b00a00800300200000f00100300b00000c00400000300200101f00500100100400c00700100200800200400100f00200002501500200000600400700000700000000100000b00000600900000000501d00000a00500000200300d00b00001200800000400400600700200200100700d00000000300000a00000000500200300000000400501100f00200000a00d00100201b00400200e00100200000000500301400101c01b00400600200100600800400000300100600000200100300001200200200000400000a00400100700600000000400400001500300300000700200100000000300000800c01902600200100303a00800100001000001000000000000100100300400a00200b0020020040000000080000030020040080100010043ec26eab0e640087f855d161cc8050f90aba2c3990021fa1f54587320143e43ea8b0e640087e8755161cc8010f90eaa2c3990072b1d1425873200716aa284b0e6400e2d5450960cc801c3aa8a1ac3190038755143582320043f436e9b2a640287f87d93654c80187ae9b26ca990021f61e64d95320061fba4c9b2a640087f87593654c80187ee8b26ca990029de0564d95320053a40ac9b2a6400a7b80593654c8014f100b26ca990ce1f61c64d95320061eba0c9b2a640087d879d3654c80187ee93a6ca990030fe1174d953200
  | 15 => 0xcd2000df4000000000386cb0f6420e000000000000000000a2e000cd4000398000000000000000000e7e000116c1420826ec78ae6a6633ea34ca840000000400000000084a23c0000001d42768441f84a2f5c000000000000000b9ea5ebce1e66d8d4a000c7601a0105968185d200e3d635e68e2c26bccaa170a9611837a4baa7e81c000944a287767123447ecdda0002ea094922000a80000000000000b7a15212e7ba5fe42800086ed40000ca2000c322ec71a3fc84c9287b85747d45e0e6cd5a9e25d6d64d16e3e4bef54cc6d96000000dd0878000200eeee92d86e401a200000030a00040a000d1a29a6f08c2de0db2000000000d6c000000166be8c9c81aaa00000007b40000005fadcc128de27000006e200023a6fa00000014a1426ee0644ec000dfc0000009266660006e4000000000000d9227000074a4c00000000002260000000000009eae74000704e1e04c1c4b26000000a3c5f2000000000000d84d3e740000000e8028ebd2000d8e00000041472c69449e22ad10af04980008a47a03246f80002d8c6e954d44644b80f662ee54ef58ee6f2e16a2f0b5cc7c4ae45e9f6a440e87d6ec048ea248646ecafcc289ee140ea0302598d66dd4c9878245ab689b000087604ad14c5ea724ac1200003ec7aa000000c90320000000ea82f80006d2000000f08000000ebce9e56e0de0004e26c607cdc25684a01f20faad6000628c12000aa612a8360002ac65c0000f6000000322000a90ce20001ae00000000082aedcc72000bf6cd85901be8324625a86607e0cbc00023e42a532c86cb852c0000b600005a0000000000e20000009be72eb6e000000936000d4e5400000009de916572db8e8e10c2ca034d9a01c9a2000d7e000000000000000000e76000272000000446358000000000ed000051aa881442126380000003c650a00087200000000000089ec2e968d18130000ba09007387c8980c3e370c04892800642e68a5816cb964f636aa70dfea5600065219a000000000000632684000bcac88f400007ce62c0480eef14f3293882c8f0ca63c4698d2cf2a46eda2b3eb8acac7e402c0000007a8000000e325d45d80002f4a0ae343f86ae1ca6badb400011cd300ccb2228c0003e47d8bd8000000ba2a52394250000000f60da6122e1cd20d24bdcd90562a7a38421aa500685782fac6cf1ab32c1600300100500400200000100a00000000d00000100000000600000000f00200200100000000000000000100200100200000400001900000800000000900b00300d00000000100300500000001c00200700a00300000200000900102000e00500b00900100c00700001101100100500200100000901500200000900400000000d00400a00300000000100800400700500300000200100e00000100100500100400000300900b00400f00
  | 16 => 0x9ea12b343a6242eb6b1079cf04506a465a0268536664610392ac6000f3672615e0005080002e68f265a00000000099a914d3ccf8b36ac094e9f82226ac086940998a78000d9e75ed7a0000000006720000003a200093aa8c9e88987da456000000000432e86c7e2cc16200a7b00000005865f094a7908b23424b6352e38cec1c0d565ba0002d4c300000000007f4000f02000e9000081e000b6a218084af80000004207bc000862608702b880000001600ac00000000000000000000000000000049c000b4805200000011e6302c6ee0e20000b52eec0004f445c8200006f60000000000001a680a000abee7a000e9c2a8bf23be7a60001f0e4e9346128aa5840000fe00017e00053e000000e6400052e000000000000000bc4ad046a000164986d809cc000c0a00040e00000096600000083cce03e2f6200020c00056c000000000000070620cf696c3f0c0e73e10ee1070eb509dc7c2f42b8c00000066c0009b80009762d28a211461c736c4cde4ba879aec4000000bfe000b727189ca000000c060000000004765923b034adc0e62cde000000000c4e4e4a4e354412d7889cdf2554bd4050d0e558a10f48636eb4088816a62eaeec21865447586d4f0a8b0000000b1c7d04b0000d1ea3ef3acd6a9447edbe566ecc3048c0e8474478e8daa5a1c25fc57ad5e7dc0000f8eb8bae000b7600060a48c0007f60000000004ea2aa18c148522182316ed418edb6874d829c86929bce6e22ea8e5b225c990000298000000e449f25340000dcbea3345acc008062047deaa2ce865058ec08000cbe00010a912748e420005ae00000000077a2e2000000e009e6efe0004948a6a9a58a00077c00070c14c6fc000000000000000ab4000000000000b0a000bc67fc17800027e318f4a0009529d8c7a0002469d60f0000c62b987cac52deac484c80007e82e836258c25e752b580742b65e4228000c6a000000956000aaa3a400009e0000003760000007889aa5880a00005643e01b20420000008f4acc410d52000000000e82bc8332cf004e63ed76378edab6ce60b3086c6d0bde5c63bcbb4906de6bf81c88148d63dcea4786d8c0006a08283d8b040008d06807ac00000022484e000b60992274000000000c0cb0ea220000007140004d617c3080000547beba4ed2ea26247548b834c67c9d07f01b8d2800cf1c0004345aa258bd08b43880009182da260a4ccb400062631c2660e40004389acca4484d9c39007805800000097e000546ace0608d831e8e60002c032e00000042cf5a1da000802000eba92403232a150ccc06a000000106000000000000e4c6c8000dae6227b2e2e0000000368b600000024899eece5bc8f6000c920009488eacc2ab24643a89623caae200032630e6a49e4000280b1ef5624c02e9b6732eca26200000044400096ea846680006f4
  | 17 => 0x4c56dde00000000000085a0000000000009c4000000000c440000004363404600001bc000000ac29da000d021540005828feaca0004421ecc360004de21e0006900e6000000000000d8820a000c1c000000016000000896b14c380008a000055e000d38aeeeacc8aede82600019017a000696a1a3d20000a2e0619c00000076a000caea6c964000000cb61360009e0396a2ad0a796dce7c60000c63b800003a000d06e0c0008ae1e2000e5e0004a60008ca00051c000000c58b9c000e8a8306b40000000000000d61fe8e83465480005c4000000e30890e484800000000ecaa86dea400005ca0006be000000c8eda01dcc74000000a8661478c3da6b2c704d48acb200a6b4e8ecc342a443a230f52b90994a76e260c048a006d605240004c26ea31462ea2cef2a424660001b40005a291a1e85a4930000d9400017605c5cca92d7c0c4e0a00000061ae4a0000009a89ce4c66cca16300000eb2000a4800000095c000000000e362a03b2000000c0200000000039c41a4ced32eea000000000710d0cdac1d64e00823e876e55247a000000406ef60007c463c7fa0003b6000aeab5e000000038000356656bba00000000000098a5da98800061ef5e0002a62b075c4aa000000000214000640a8a5b67708e20000000000005ce28a14e00029400025200000018a4daa1c00083a478000360e2800000000000079880e000b620fc00000051e000b926da6c044e87e0001081b600000000000001e40c000000f38cee42edf69d4ab8000000000a26000000ec84a8284ef064600080c000220000bb80005280008d4a3a54200000091cd5c2ba000158a36e7ca04a181d874edcaee86e00002d67fe7a409a9580000003aa516000000000ec63ee000000adc0009fc000000000f3e9d2e78000402c2ce9485e080000018000b3800000060c0008ee000c9a72400052624a184e9600070ab1a000b84000000c40000cca902000282cc48129fa000000000b16000d22d00a3800008c000000000c22000000000a0e000450a1400063acfaf346065ee278a5c55cafee0ebf0264bb2adaae8022338e541a021ccda6b071ccce254c4a5769ae5f6194b5acdcbaa67ebf467022cf22492ce41de24091e202810dba5be950e70238d3a67ae5235c88099637e69c6a200057c8ba41c1467ae234e980006020c2d74296dbc38a2864cceaad0499c2e478457eb44a02174bac000d48102df800064e0003c20000002e01003cc6780005f88c4000982d42056192000efa0aa0008483ba0005608fc9a46d6000c20be6c26dd8ad26c297c5de92a8bc15c37c7a24fe44c92e2b26e847c8600c89a009054add21eed54b86aae5209b20242ce7940009c600068ae16efcb8e84069e0001326e6f26000e660000007c0000c50b081ac74c000e8ca1e4f06b81388ccb06ddc112ef8bee1
  | 18 => 0x77894ce562c8d98f4e89a77e000972000d08d6e0a8000b82026000f2c0000006ce0000007d20000005c8000000000330000000482000d2ec94f1826c0004b800071e82207207e760b64604c660000000007228d2000870000aecb9a000000b4000000039e0008500ea07a3fe8046fef3000000095e000000000750000000a6e13a884c42d7230c0001fa000000aa40000000000003f600075a946b2c0003500000000000008666761ba8426183de000b7450c040000a68474180e880000000000d00006ca1b07560009420002fc0000000d829288e746cf45e6c1a0000008683c80009840bcf44000000000bd6000000bfc030aac7069c200059cb0200088827c000000000cfca200000143f25dca9c000ed66f2b4cad4206dc83ae00000000029c530960a825ea5a6b54c5a000c64e049040ae80890cef41d288a00008ac80000d3600012452a368000000000da800061682e766518c182fe5948fa000a9e000000000000092000000d8a13e0003d00ba1f690e886290000f168c864c00013c426062bda7f2000000eb04304528469ba4fc0e0000000ee244aee4380d6ae724a4c2a00031a02000021690ac24f060000000000001340000006745c21a4b66310ae07081cc3ced50000716000000bcc000b7e6aa104000418e2ae5a1ea49634e96a580afa1fca30780570b12448cc8728c3aa6469ae224b206c0d4000686000a060000000000009fe4d8d124e808ef0e000454b4a0003c0f244b493cae405e00033a38c336256e5c0281963821ce000000c5406e65e4bc0003ac000b94424000000374e1887a00000000054cf12000000772ed82bc5140b2c1e366000b3ce582de00000000073a46c0000004d2e1200053a39abbe0007ea5b88540007682b853c742000000dfa0000ca0000009c04d0e2c53829e000000682000000c8c000000b709701aa838510000c3c4c449a72a000000000b2a5128f8b009f0188f10a744f2d464f8a0c00000000060021031232812c0009b4000c68000372c960000000000000000005d0cf22ae0004ca95aa7c000098000110472000dd600089400000000083ed34cd00be00000000000050200050e0f2000500000852000000000dc600066a000198244000de86c4000734f503f4af4a4a4fae3c56ad1c4882b41c6b242f20f41d0000000ce600016e0003e628843e00000024e000af60000000000009200000000001680009a6e08000ca0550af235a00068c85603e01260ec840000006a679eb2800000062aad8cc0720c609f4e6a36e00097a000000236daa7f8000ab06dca002be000000000000458db00009ec0001720000002d0658306bbc38ed58000c8288cbe4b2e98c5e25f400000000000000000000015ad4ce46ebe044066b18882b0c5b4490f3c000b422a2000730662000aba910f0cc5c98e97
  | 19 => 0x126688ba6a326547b6978b3a0001f40000008340000466a800000059adf0b56f20cfe00092c03c33c8c641ebe0648dc4858c9e59e2c4cba00893e7e23d40ce000000000e3a55a25a78a0000000000007740000000008e4000e2400087c1e4000000ab6000ac800043cd700000004dc3fa000000000000000a088be404364ea600086a3a0ac45048a8a5485cbc23480b866e09600046800000073c000416000abc8dc1e0d2a76276ccb22f6c463b4000d2664a0027eedec9085e8b7c23247000000000000000011a0007640000004e6000f463eaa60000440bb0bc0000000f4cda427a0000000008ce000e140b0000000d681a80760006340002dc5568def1e6b602a000156000000bb6486cea8e08245ecc100b4e1a5c000000009cbe24eed620daf280d2000000000000bec0000000a47cc000000792000408ade932000000e9aa98a6a00042226abfa00036cf00000000000dee000b467e6e0200032cb780000000000000000000005b0000e50000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x88ea47c00a800001226009c0458307aba56705e0000000000d00064a09e82006c989442b288cec8400601000a00004b00030414220002004a000600010105030f070f1104050001120000082d310050b25d5450961cc80503e98dd164d95320040fe6174193654c80103f985d074d95320060bdd182d0f654c80181f7460f42d95320050e650659c2614c8014399419570985320050d650659c6604c801435941957198132006075cd84194604c80142d92dcd75590320050b65075dd9320c80142d94217764c8320068955182d0e610c801a25855084158432006a850980105610c801a255460b4358432005a164a5450d610c92de064255143584320058965474509610c801685931d14258432005a864074509610c8016859395142584320058965743509610c801e055490d425843200781d5143509610c801e055450d42584320068961542d01610c801a858350b40584320068a55182d0e600c801a298550b40580320068a55182d0d600c8016899295143580324b7829095450d600c92da1b8255143580324b6866095450d600c801629959d14258032005a264e74509600c801689939514258032415a265283509600c801e0954a0d425803241da2e5183509600c801e095460d42580320058a65743509600c801e095490d425803200782d5143509600c801e095450d42580320062a61d42105600c801a29855084158032006a260d42105600c80182f7460b43d953100607dd183d0b654c40182d825d7735932100e0be1d5450a634852dc15715514318d21427095c5545086348505c857150d4218d210050765075d8d324840141d941d4634c9210140f26174551630840141d941d7764cb300060b5d182d0d658c00181d7460f42596300068955182d0e618c001a155460f42986300048d650854ca618c001615931d154586300058964874551618c001a255460b43586300068555183d09618c0012359421532586300050b65075d89324c00503c985d15458f2000e0be1d5450a634812dc19705514318d204270a5c1545086348105c897050d4218d200050765075d8d324800141d941d4634c9200060b60975dcd640800160d929d15498c200058364a745516308001a255460b43984200068955182d0d610800141d941d6634ca10005076507558d3284001a0d8360864d95100068a60980193654400182f7460b43d951000607dd183d0b654400141d939db75d91100050b64a76dd76444001a318160065d91104be8ca06801d76444001a318160075d91100060bdd7825cf644400181f75e0d72d911000507e5d5450e634400381c875514358d104b7031c95450d634400382c8755142589100070355073509624400103d94a1f654c9100040fa6075d91324400182d7460b4359410006075d183d09650400103d9421d654c810
  | 1 => 0xe108c5284341650227ea600ac92b000726a8654000c2c022e286e4c004e3a4438c6005c00d674aa3c48769014d4cc00b6bcb85aae1a606846009a78188a0a3e2062d21c32b400a2c42ac2800000ca366696c01ebe244a
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4d
  | 6 => 0x4e
  | 7 => 0x3
  | 8 => 0x94d
  | 9 => 0x94e
  | 10 => 0x124d
  | 11 => 0x124e
  | 12 => 0x138d
  | 13 => 0x138e
  | 14 => 0x8d
  | 15 => 0x8e
  | 16 => 0x98d
  | 17 => 0x98e
  | 18 => 0x128d
  | 19 => 0x128e
  | 20 => 0x150d
  | 21 => 0x150e
  | 22 => 0x4
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x168d
  | 26 => 0x9cd
  | 27 => 0x9ce
  | 28 => 0x12cd
  | 29 => 0x12ce
  | 30 => 0x168e
  | 31 => 0x20d
  | 32 => 0x20e
  | 33 => 0xb0d
  | 34 => 0xb0e
  | 35 => 0x140d
  | 36 => 0x140e
  | 37 => 0x154d
  | 38 => 0x154e
  | 39 => 0x24d
  | 40 => 0x24e
  | 41 => 0x16cd
  | 42 => 0xb4d
  | 43 => 0xb4e
  | 44 => 0x144d
  | 45 => 0x144e
  | 46 => 0x16ce
  | 47 => 0x3cd
  | 48 => 0x3ce
  | 49 => 0x170d
  | 50 => 0xccd
  | 51 => 0xcce
  | 52 => 0x15cd
  | 53 => 0x15ce
  | 54 => 0x170e
  | 55 => 0xb0955
  | 56 => 0xb0956
  | 57 => 0x94b15
  | 58 => 0x94b16
  | 59 => 0x140955
  | 60 => 0x140956
  | 61 => 0x95415
  | 62 => 0x95416
  | 63 => 0x24955
  | 64 => 0x24956
  | 65 => 0x956d5
  | 66 => 0x94255
  | 67 => 0x94256
  | 68 => 0x16c955
  | 69 => 0x16c956
  | 70 => 0x956d6
  | 71 => 0x1489
  | 72 => 0x130a
  | 73 => 0x14c9
  | 74 => 0x134a
  | 75 => 0xb1395
  | 76 => 0x138b15
  | 77 => 0x138b16
  | 78 => 0x16d395
  | 79 => 0x1396d5
  | 80 => 0x1396d6
  | 81 => 0x9c995
  | 82 => 0x12c995
  | 83 => 0x989d5
  | 84 => 0x9d295
  | 85 => 0x9c0d5
  | 86 => 0x9c0d6
  | 87 => 0xcd695
  | 88 => 0x1689d5
  | 89 => 0x9d715
  | 90 => 0xcc9d5
  | 91 => 0x9ccd5
  | 92 => 0xcc9d6
  | 93 => 0x1709d5
  | 94 => 0x1692d6
  | 95 => 0x1692d5
  | 96 => 0x168cd5
  | 97 => 0xcd696
  | 98 => 0x171695
  | 99 => 0x169715
  | 100 => 0xb4b15
  | 101 => 0xb4b16
  | 102 => 0x144b15
  | 103 => 0xb0b55
  | 104 => 0xb5415
  | 105 => 0xb5416
  | 106 => 0xd0a
  | 107 => 0xd4a
  | 108 => 0xb4256
  | 109 => 0xb4255
  | 110 => 0x16cb55
  | 111 => 0x16cb56
  | 112 => 0x17ca
  | 113 => 0x16d456
  | 114 => 0x16d455
  | 115 => 0xcc3d5
  | 116 => 0xcc3d6
  | 117 => 0x3ccd5
  | 118 => 0x170cd5
  | 119 => 0x170cd6
  | 120 => 0x17cb
  | 121 => 0x1715d6
  | 122 => 0x1715d5
  | 123 => 0x1a89
  | 124 => 0x104a
  | 125 => 0x1049
  | 126 => 0x5856
  | 127 => 0x1a8a
  | 128 => 0x289
  | 129 => 0x2c9
  | 130 => 0xe8b
  | 131 => 0x178b
  | 132 => 0x104b
  | 133 => 0x1a8b
  | 134 => 0x5ca
  | 135 => 0x9695
  | 136 => 0x9716
  | 137 => 0x5cb
  | 138 => 0x12c3d6
  | 139 => 0x12c996
  | 140 => 0x12d696
  | 141 => 0x155415
  | 142 => 0x155416
  | 143 => 0x154d16
  | 144 => 0xb5796
  | 145 => 0x3d296
  | 146 => 0x3d2d6
  | 147 => 0x3d456
  | 148 => 0x3cd16
  | 149 => 0x3ce96
  | 150 => 0x104e93
  | 151 => 0x134954dd
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2092
  | 6 => 4175
  | 5 => 1972
  | 4 => 108
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (85768+((h/697+packedAt gbK7 (77404+(h % 697)*12) 12) % 3675)*13) 13
  | 6 => packedAt gbK6 (218483+((h/1391+packedAt gbK6 (200400+(h % 1391)*13) 13) % 6063)*14) 14
  | 5 => packedAt gbK5 (124232+((h/657+packedAt gbK5 (116348+(h % 657)*12) 12) % 2863)*12) 12
  | 4 => packedAt gbK4 (7848+((h/36+packedAt gbK4 (7560+(h % 36)*8) 8) % 130)*8) 8
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0f870787f0ff00ffe3807fff166478c33327f
  | 1 => 0xff07807f87f0fff01fc007f802b878f0cdcc7c
  | 2 => 0xffffff8007ff00001ffff87ffcc180ff0e0f8f
  | 3 => 0x7fffff80000001fffff800f01ff03f00ff0
  | 4 => 0x7ffffffffffffe00000000ffe0003fff000
  | 5 => 0xfff8000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa848101809019024ca0824caa0224384111235
  | 1 => 0x694180288310a4e056405550602858b0454c5c
  | 2 => 0x5292a48006aa01410492902544c080590e048a
  | 3 => 0x5597550000282992562008b012d02f00b60
  | 4 => 0x10866e4664cc4b0b000180010fd40003aaa000
  | 5 => 0x9ce00c0440888c0c000604460ffff6ec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36286
namespace PEqualNP.Outside.L_meta_36286
open PEqualNP.Outside.L_meta_36286.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 4 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 2 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 6 := bs2_4_0
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
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 29 := bs4_3_0
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
theorem bs4_4_384 : Interval s4Atlas 4 384 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 396 := (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384))))
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
theorem bs4_5_576 : Interval s4Atlas 5 576 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 601 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)))) (concat (concat (concat bs4_5_288 bs4_5_320) (concat bs4_5_352 (concat bs4_5_384 bs4_5_416))) (concat (concat bs4_5_448 bs4_5_480) (concat bs4_5_512 (concat bs4_5_544 bs4_5_576)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_448 : Interval s5Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 108 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_1952 : Interval gbAtlas 5 1952 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1972 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 bgb_5_576)) (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704))) (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832)) (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960))))) (concat (concat (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184))) (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696))) (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952))))))
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
theorem bgb_6_4160 : Interval gbAtlas 6 4160 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4175 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992))))) (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248))) (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))) (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))))))) (concat (concat (concat (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304))) (concat (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560)))) (concat (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816))) (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)))))) (concat (concat (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360))) (concat (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)) (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)))) (concat (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872))) (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)) (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))))))))
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
theorem bgb_7_1696 : Interval gbAtlas 7 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1760 : Interval gbAtlas 7 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1792 : Interval gbAtlas 7 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1856 : Interval gbAtlas 7 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1888 : Interval gbAtlas 7 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1952 : Interval gbAtlas 7 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1984 : Interval gbAtlas 7 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2092 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)))) (concat (concat (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664)) (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792))) (concat (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 bgb_7_1920)) (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 (concat bgb_7_2048 bgb_7_2080)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0feeefee0feeef8a0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075680 * 2 ^ 32 + 4277074080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36286.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.or,[4,5]⟩,⟨.or,[2,7]⟩,⟨.and,[1,7]⟩,⟨.or,[0,9]⟩,⟨.or,[1,8]⟩,⟨.or,[2,3]⟩,⟨.or,[6,10]⟩,⟨.or,[4,12]⟩,⟨.and,[11,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4277074080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4277074080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36286

open PEqualNP.Outside.L_meta_36286 in
theorem PEqualNP.Outside.L_meta_36286 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4277074080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4277074080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
