import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36717.Model
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


end PEqualNP.Outside.L_meta_36717.Model

namespace PEqualNP.Outside.L_meta_36717
open PEqualNP.Outside.L_meta_36717.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 8, 7, 6].getD j 0

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

end PEqualNP.Outside.L_meta_36717

namespace PEqualNP.Outside.L_meta_36717
open PEqualNP.Outside.L_meta_36717.Model
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
end PEqualNP.Outside.L_meta_36717
namespace PEqualNP.Outside.L_meta_36717
open PEqualNP.Outside.L_meta_36717.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x7f01fff80fffe07fe07e0f83ff07fe07f44e73
  | 3 => 0x7ffe03fff01fff81ff800ffc1ff83ff818739c
  | 4 => 0x800003ffffe00001fffff0001fffc0001f83e0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x108100881024000028a1104220842a28194a5
  | 2 => 0x2aa529946a548ae8f0548aa35546b415544a52
  | 3 => 0x4c954aa528d91a2b75410ce919d23950586318
  | 4 => 0x68d9b3464c91d34db9e7a8421ee710619e83e0
  | 5 => 0x70e1c3878f1e1c71de79cf73908421861f7c00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36717
namespace PEqualNP.Outside.L_meta_36717
open PEqualNP.Outside.L_meta_36717.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa80000000052380803074000004d00c3600f8f005801c0e9d52300340020c4110b425c00422000121465425009001a5600f1410981890a0880010c00011000094c3ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xe801624000c040d80000083081faaa311099c86052d80270f03ab049b9e001d8b0d1f212d16a2890025a8269a998f80278028801897292a00072210028ba52b8c9a0a92a4909c0891811421a982261eac8000019b000000138e1d15951920a3a007800580068014932c18178a001201860c4c00302243070800500266c20c280000004080160210203bba8a87745150e7ca1a14f55242afa9a855c5350aeea2a15d14542bda8285785050b3ea6a16714d42d7a9285b75150b68a2a16ed41429e28285b85050a70a0a14f95042bb28e657551cca7ca9194f55232bb28c6575518ca7ca8194f55032afa9a835c535067ea898cf15131ea988633e54c867aa990d794f21aea9e435e53886baa710cf950219eaa0435e53902baa7205d94640baa8c819e539033aa7204f54a40db28c81b5519027ca1204f548409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2eca2185d544309f2a6413d54c837081904fd52209e2a4413f5448278a89057d4d20ae29a417751482e8a2904f950209eaa0415e53082baa6105d94420baa8841b8400827ca9884f553109faa2213c54442bea6885714d10b7a92216c52442bca6085754c10
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xa0e2000c60004810c514c5150b1b5314142c614c5050b335114142cc1445050a94644c431c594e51902396510020
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 5 => packedAt s2K5 (788+((h/14+packedAt s2K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s2K4 (2694+((h/30+packedAt s2K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s2K3 (312+((h/2+packedAt s2K3 (304+(h % 2)*4) 4) % 14)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 1 => 0x3f80ffffe03f81ff83f03e0ffffc1f01d89fcc
  | 3 => 0x3fff03fffffffffffc003ff03fffffffe0e3ff
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x848a1008c489082014b14a114a2129540b2e15
  | 1 => 0x9526299143922ae58155168d96e51a0cd896cc
  | 3 => 0x22144aa20924614aa80825a4254a54a960c16a
  | 4 => 0x3458b34492074db34e6d810939b38831bd03b0
  | 5 => 0x3860c3871c3871dc738e39ce01c210c1f6f800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36717
namespace PEqualNP.Outside.L_meta_36717
open PEqualNP.Outside.L_meta_36717.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51903eca3205d94640bea8c81f551902eaa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a05f14540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f681907e10320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2107b88420f6108417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fba0e21f441c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fba0a21f441443ec62887d4c510fb10a21f521443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5090afea6a177d4d42afa9a857c5350bb8a6a15714d42dfa1a85bd4350bde84a16f90942bfa8a85f75150aeea2a15f14542fa28a85745150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3997d94732bb28e657d51ccbeaa3995d54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c53506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f7cca31ee994637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c7bc8698f750d31bfa92637c524c7bc6498f70c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863df430c7b88618df94831bea9063df320c7ba6418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21fba0e43f441c87ec6390fd4c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087ee8210fd10421fb18843f531087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa
  | 2 => 0xe03d2c01c35e4889f88b0007a0000000004140000000000000000326000eb01100000000174000000ada110000000000100000000000516000968ee34e02c0025c00020107800000000000000008ec2580000093454800000340d10b80009640009c33e0c0000000004ac2200028200000244000900ec800000000002160000000000040a000000f40009a80014a0005e800000000678cd8004ae000000002b84b8f60003fa9290fa14306a04dd1e10000013227804e000690000004c80017d000494001df404000b40002e40000000017819921a1b372584000564ca7780025311c0011584f226000000000005dc0003300020c00098000001390df3f0288aa0000005a4000122a60003221221e0003c8002140014627945e474fe07b1e2000df0001cc000000000ea000000000004840026c28e0c4000e4126000641ea09a32c87000474a504d0701fe70c00000000a20000502a2940a200041c7d94000010c030000000da89c5d8002f600000000452000208b245c4d04f9a63e80007687a0e6010001b314a860938003e44f86a800000088ae9b5000184c88fe1b4224068005047e40013c4c02200003c000000cb800000000001601e49847113a0006c40027b0745c0579372164f400000000000000001d8001398000006a4002470001f0121670000000000036c6dc00000000000000060ba0004c90d00000000000146690339f3114020f58400640bc9495200700000800000002004028000020000000801205c018000000000000600a0100080b0000100000400e0180000400801c00008002038000000020000100900e00c000000020000000600000000003000004048010020240c0080020000000d006000010000000000000400202c0080401e0040000b00000407001002000010000000000280b0000040080100602404802012010000000040000000000c004010060020180000700400007802014010000000180000000000a0200001000800c00800000000000000000000000f00202c0600100a00400801004000000080140180000101c004000020000040080c0020000280600c01c0000300001c0300000800000004000010000040100000100000600000800000000010010000680080c000000028090060000180402600406003bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857
  | 3 => 0x370000000006580020700088c000db3ae9d8d6a8a4c60001a12603600086000220624000000765e149000200000000003a00000018547e0000012c1b200000142000350e398b000588c78001400007587652a0010d17f3da0001f9662be000002410004e0889da276014f78250001c4001240006500006845a00000019000780002130000008d8000005d4002450000007199c17a1b8f818812a00000010000380002353c8000001e738448c8a85f03e5b4e5043000568df8c21946843b8000000014280016200000000000a350304e0003240003e058154001f10000007a8003928f0539dd29e40800000300704000000000006880051c2105b8d33ee2a0b280003a009018c71c21294180019a0a8ee00000000000000000a18001e33ea00000000000718000000006a00001404c854001cc188000d5a0a3cc8cc9000719e0000017e0400006300010a68cab000000000dea6d00000000000000000000000005f00000034a378000d62668e42d11f0005ac7b26b1ba72d3480009011c3f05b0008c47c0004e05a8d9035000a10ca8b602a000cd00008c7391b0004448950e98705a0000000016a518001ac0d2448000ac0720000025d52c000ea800432130940534f42cc00000120394002091d46d000000000000000000fe0000019200057800000232000a80ab0000008c2283809bca6800000958d5003000000c70ba4b4954002932aa4e4cc1364bc3cc9880018004cd8054000760b2021000944000be10e000ea1b80fa8d0839a01822047c9991fa7e80000033a5251305c000000000fc314124ed8002b23bcf10e700045c0b823000871438002102a8a01583ca458b989d4960d8a423e000000e22460a4000848004480009aa770003dc170094d0948228000001b0b78381048c853230000938c100012e1452109b4026308f00052e7353f22c41a58ce8a670c6078d72481b0530bc94b2dc884140003fe000000a42600388220043c000a70000c05c4002174400006724c0002840000025e30cc81450002303501a2ae000fd8004a8250819bb4ea278c20004dc97d278000000000005e0000000000039e000b60004540010408f0000001ea7c1ae000bb1c84cc3ec5f8c515a451482490b09d07d23d2347b8f48ae06e2c14882b30c000050650e423448a04000000000000003c066000286000001c5378830740000c4a3d3e8594700000006b3a42e4379060000012da6212c0583c0e9000000001fe00000105a10302000001d3000000000000520613884231a47080a7f0e800144a370002485a12a0a
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xc54c82766194f209d58653c823e6414f208f59053c825e63947209758e51c825e63d52209758f548827661d52209d587548825e63952209758e548823e6494e208f59253882766114e209d584538823f64546208f191518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551209ed81544823e6515120c7d53534831c54d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520ce153204836451881209798f540825d63d50209d987540827561d50208f596540833860550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083655188420ce553400827965100209bd9520082e461480209ed9520082b8644802097d8d54c425c63553109798c54c425d63153108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798e52c425d6394b10b558c41c42b4644c710b558e21c425e63d52109758f548425e63952109758e548423e64d4e108f593538425f6354a109718d528423e6414a108f590528425e6314a109758c528433561d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d9584524427665d0510d514f414436452d0510cdd5041442d56310510d514c41443645210510d514e3144364528c5109d19531442b4644c510d914931442766588510b558e214436452885109d19521443645248510d914a104425e63d50109758f540427661d50109798c540425d63150109b988540426d621501097596530425e6314c109d984530425e63d48109758f520423e64148108f590520425e63148109758c520427661148109d597210435553c84109d59421043555308410d554f100427965840109dd9510043555344010b9189100427b6544010
  | 1 => 0x69c63504419dd9541106d463504419b98854cc66d6215331b518543cc69d640cb31b558c41cc79643107318f992528c63d6494a31b5587328c63f64542318f191508c63e649513197d8d544c67761551318f994544c71d631513197996434c71c5490d3197195434c71c5450d31b5185434c71c548c93197994324c69d640c931c7150324c73454cc531c7152314c67a60d50319e583540c65e631503197597430c65d6510c31b5587320c65f654c8319d594410c794431043197d95310c69c644c4319dd95310c6b4644c4319798f54c865d63d5321cdd8554c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c87556194f21c795153c871d5454f218f99053c863d6414f21d594f41c87355410721b558c41c87565310721d594e31c86b4644c7219798f548865d63d52219e983548867960d52219798c548865d6315221d554f218865f63551219718d544867761551219ed81544867860551219798c544865d63151219d586534863f6454d218f191534867b6054d219e181534865e63141219758c504865f63550219718d540865e63150219758c540867a60150219e580540863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520865e63944219758e51086756510421b558c41086e562104219d59631086b4644c421b558e210866f65484219dd95210863f64540218f191500865f63540219718d500871d53d0b40c754d42d02b86050b40c794f43902b46150e40a758c42903565394640d554e51903565354640d554d519031e5390640a758c419031e5310640cd544419029d63d02409798c525025d63149408f99742502b860509409798c515025d6314540ad185431025f63548409718d521027761548409d185521023d6590840a758c421025f63544409718d511029d6310440ae580411029d63d00408fd95401027b65500409dd8554cc2746155330c718d54cc3376155330cd18554cc31d54d0f30c755043cc31d54ccb30b558732cc31d544cb30c755331cc29c644c730c755131cc27661d52309d587548c2d46150e309dd85528c2746154a30a7590328c29d64cc2309758e544c26f62551309b189544c27761551309d185544c25e65d0d3097994434c23e64149308f590524c25e65cc930b5587324c25e65cc530a7191314c25e63d50309d987540c27561d50309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c25f6550c30b5185430c25d658c830a7590320c23f64544308f191510c3376454430cd191510c3564354430d550d510c3563254430d50c9510c25d658c430d5546310c355510c430a7593300c35551cc03097d95300c355514c0309ed95300c25f63553209718d54c827761553209d18554c825e63153209758
  | 2 => 0x135605c0a90a0005ac00000262000000000f65f8688ce3ee4dc338430006d80014138a4e81d1aa1d02a4a51de0ec868160000e804ce81be0323345b1e1000000000003a412400000000000000090000000017a24c1702793540a360498ab220000699e2054480922183b0581059ff3680004a8000106808980032268c319b104a5740008f3f45882c0c0090104b08f32082b8a180027a000000002b683830040194000b803419e4f0b305f250864e688906c6dc7c8a212e850089cb3ec0801d8883aa130b50bf264548b69642f0364691380fa140380561dc018000d510a76ca006f2603188c1b50d60004e0fa0000000281405a3f0001fe000000000002ee000a20000560cc958001c0494b88001407b486939252268a319e0207c87a0a430a04c09000050340201807000050600a0000301c06000020a40908401000010240005800028000182c000040340c01004090000040101c010002f00406004010100105006018060200d0040604801018010c403048270201404c0000018000080700b0000c004030040b00c0913c070380f0101907c020000200401000080e419004340700f000040000200000068310000004c00088000300101003000270040000c0e064090000a0c814018140000e0000001c02000060100302c03048060000402c0202c000000300802000030100b04c030040801c0507c0a168180680a006776154b439d18552d0e7661943439d58650d0f574314543cd90c5150e3f6550c43ad1854310e5f6550c43b51854310eb46150f4297d8d51d0a5c63547429798e50d0a5d63943429d98650d0a7561943429798e5190a5d639464297d8d5090a5c6354242c714f4350ab46150d42d5d4f5150b5453d4542d5d4c5150b545314542d6d4f5050b5853d4142dcd475050b7051d4142d6d4c5050b585314142dcd445050b705114142ced0c5050b394314142ce9085050b1d53d08428fd954210b1d5350842ae1814210a6f65508429d98754cca7561d53329e98354cca7960d53329d98454cca756115332b518543cca3f64547328f19151ccb376454732cd19151ccb564354732d550d51cca7661d52329d587548cad561cca328fd91508ca3c645423297d8d544ca7761551329d185544ca7b60551329e181544ca5e6590d3297195434cad46150d329d984504ca7561141328f596540ca7761550329d185540cb1c6355032cdd85540cb3461550328f990540ca5e631503297597430cb1d54d0c3297594430cb1d5410c32c7553320cad561cc83297d95320cb1d544c8329bd95320ca5f6354b419718d52d065e63943419758e50d065e6394a419758e529069c6350a41ae181429065f63542419718d509075453d0541c714e41507546154c41c754e431071d53d0841a718d421071d5350841add8542106b860508418fd95411
  | 3 => 0x6d883002568148000b42dc07068000000599ec23e3f4cc85d31c0b8001dc1d807c758001863ec5800035077c9b14c0006e0000000003700013f234190001570ee2f4b38002d808c0021015e74c719ba3ba260a69530725cc4301b12c000800003008340000005e648610813285d4000fe146028000002166282a1d41e0820001d10ca000000451764bce405b2bc6c0909580bc1fc888c9000000769ee38e1ccde9790603581b8c701a854c987c24e0010080025a000060121e4000000003ce2b0e799c0007acd994908c718829e81a8660ed206202478e186907085c8a90f27c294e6000000008e4989352658f18000ae000460000004244118621c304788e10000002a9f80f20008a1ea3c0608951953165201320a31e0886620903a0009a0f81720006d0bc1bc688a11f332e108e22030d80680017d00646c0780039469cb78873d2299001c01700008e2110003d40017b38432cd90003cc48c778840001c8000003e2278628a10967bc4d9e407a7e4389fc03c630330472a22c8e088d1243104e9083341389107a29e7d0b70a8266690fa83535c6bc001120007f448800276394bb1a122c0f828800336694ab0902322e8bf81c1d2794750e6404110ac98829c01c8386115439c138283723dc860d0296634970310dc1340595514e474369693205d0eb05911467c7100009458c9609920c2b41903c0008584583f1c8594641032e40580c0802d06ec000df34c149079ac00061c001ad4267c0c18531ec0000006a2be1e0e70941fe010312120001f8be09f3027ec3a9d71ae7650619d40845c5a08e1625148102417c5505a947378570a81bf40e374c202
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xa34901404009200540f3151c81114d70c000601858e2c0000260000826874c1c54314142c32a6302842161463185540ca8a38aa8218658555161cc832c32a63028420e1454185434c60ebb0a819263251d161cc831a28e8b0ca790c557694c41c870ca98c0a16818518c6155330a28e2aa087986155458732cc20e3b2a898e61455d03254430a28e8a88621861564547300c28a3a2c229a21155d85310510c8ac62908288624641493144322b18a510a219154c6244010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x81608148755161cc8328148755161ccb30814865d032544308148759151cc030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | 2 => packedAt s3K2 (i*60) 60
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (20359+((h/221+packedAt s3K5 (17928+(h % 221)*11) 11) % 1059)*11) 11
  | 4 => packedAt s3K4 (22272+((h/179+packedAt s3K4 (20482+(h % 179)*10) 10) % 647)*11) 11
  | 3 => packedAt s3K3 (1273+((h/8+packedAt s3K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s3K2 (244+((h/1+packedAt s3K2 (240+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf03ffff81fffff81fffff83fff03fffcfc7e3f
  | 1 => 0xffc07fffe03f83fe0fc0ffc3fffc1e03639fcc
  | 2 => 0xffff81fffffffffff000fffc1fffffff83e3ff
  | 4 => 0x1ffffc003ffffff00001fffe003fc03f0
  | 5 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x94850808c489108052c52804a52132a82c2e15
  | 1 => 0xa19314914392159605545a42cb6514196196cc
  | 2 => 0x420a25220924422aa02094a8128a495282c16a
  | 4 => 0x8b2c59c492075bcd39b606229cf39063f403b0
  | 5 => 0xc3061871c386371ce38e73300c20183db7800
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36717
namespace PEqualNP.Outside.L_meta_36717
open PEqualNP.Outside.L_meta_36717.Model
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
end PEqualNP.Outside.L_meta_36717
namespace PEqualNP.Outside.L_meta_36717
open PEqualNP.Outside.L_meta_36717.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x80000a624010be41bc41bf40bd40f710f510
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4272a020ec50110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (104+((h/2+packedAt s5K4 (96+(h % 2)*4) 4) % 10)*4) 4
  | 3 => packedAt s5K3 (57+((h/1+packedAt s5K3 (54+(h % 1)*3) 3) % 5)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3ffc1fffffffc0ff83ff07fc3fffffd8e31ff
  | 1 => 0xfc0ffe03f07e0ff0ffc1ff83fc3c0f02f3cecc
  | 2 => 0xfffffffc007fffff0001ffffffc00fff03ff0f
  | 3 => 0xfffffff800ffffffe0003fffff003fc0ff0
  | 4 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x48244448841084022a12542440652948861055
  | 1 => 0x19648c3924a494b05a50b4a1c4286a18b2c6cc
  | 2 => 0x20c91090694909550421294aaa8084b3016b0a
  | 3 => 0xb28a2122480d2a6994a408433312c023580da0
  | 4 => 0xc30c39c38e71cf8ee739ce70222308c3efb000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0eee0eaa0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36717
namespace PEqualNP.Outside.L_meta_36717
open PEqualNP.Outside.L_meta_36717.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10050f029a7a316910001b8000cc01e00e17a012855001e0400a58d5ca600183ae6c219343689499487c5bb06000302a0022b289493a62400164660e0d2638b9d4e061868100040000e0c4800c08700263c180007fd5007fe54007f55007fc54017fd4c057f53017f94c05fd53015f54c05fc53017fd0c05fe43017f50c05fc43007fd4803fe52007f54803fc5201ffd0803fe42007f50803fc42017fcc803fe32017f4c803fc32007fd4401fe51007f54401fc5101ffd0401fe41007f50407fc41017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc21007fd4001fe50007f54001fc5001ffd0001fe40007f50007fc40017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842000ffd9510005feca880037f65440013fb2a2000ff9951004dfcca88003fd65440017eb2a2000ff1951004df8ca880037c65440013e32a2000ffd9110005fec888003bf64440015fb22200cff9911001dfcc888003fd64440017eb22200cff1911001df8c888003bc64440075e3222000ffd5110067fca888003fd5444019fe2a2200bffd8d1005dfec688003df63440016fb1a200bff98d10015fcc68802ffd63440177eb1a200bff18d10015f8c68802fdc63440056e31a200bffd4d1005efea68802ffe5344017fea9a200bdf54d1005ff8a68802fff4344017ff21a200bff50d1005ff88688003ff62440017fb122000fbd8910005dec48802bfe62440037f3122000ff58910005fac48802bfc62440037e3122000fb1891000dd8c488003ff5244015ff2922000ff54910057f8a488033ff4244015ff2122000ff50910057f8848802fff3244015ff192200bff4c910057f86488003ff5144001fba8a2000ff94510007faa288003fc5144001fa28a200cffd0510007fc8288003f64144001fea0a2000fd50510067f8828802fff3144017ff18a200bfd8c51005ffa628802ff53144017fe18a200affc8510007fc4288003f62144001fe90a2000fd48510057f84288003ff5044009ff2822000ff54110027f8a088033ff4044009ff2022000ff50110027f8808802fff3044009ff182200bff4c110027f8608802bff2044009ff1022000ff48110027f84088003ff1044001fd8822004ff84110027ec2088013ff65040097fb282004ff9941004dfcca08013fd65040017eb282004ff19410025f8ca08013ff64040097fb202004ff9901001dfcc808013be64040075f3202004ff59010005fac808013bd64040015eb202004ff19010025f8c808003ff540400fff2a02000ff5501003ff8a808013ff63040097fb182004ff98c10015fcc608013fd630400d7eb182004ff18c10025f8c60801bff530400dbfa982006ff94c10037faa60801b7d530400dfe2982006ffd0c10037fc860801bfd430400dfe2182004ffd8810025fec408013fe62040037f3102004ff58810005fac408013fc62040097e3102000ffd481002ffca408003fd520400bfe2902007ffd081002ffc8408003fd420400bfe2102006ffcc81002ffc640801bfd320400bfe1902008bf98410007fea208003fe5104001fea882000ff1441003ffe8208003fe4104001fea082007ff10410037fe620801bfe310400dfe9882006ff0c41002ffe4208003fe2104001fe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0xffc4148025ff98a4012ff8c520097fa629004bfc3148003ff90a4001ff8852000ffa4290007fc21480037fb024000ffd4120027fca090003fd5048009fe2824013ffd0120027fc8090003fd4048009fe2024012ffcc120027fc609004bfd3048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048001ffb2e2000bfd9710007fccb88026fe65c4001feb2e2000bf59710007f8cb88026fc65c4001ffb262000bfd931008ffcc98800efe64c4001feb262000bf5931008ff8c98800efc64c4001ffaa62011ff95310007faa988047fc54c4011ffb1e2008bfd8f10047fcc78800afe63c4011feb1e2008bf58f10047f8c78800afc63c4011ffa9e2008dfd4f10047fca788023fd53c4011bea9e2008ff14f10047fe8788023fe43c4011fea1e2008ff10f10007fec588002ff62c4021ff3162001bf98b10007fac588002fd62c4021fe3162001bf18b10007fea588043fe52c4001fea962010ff14b1008ffe8588043fe42c4001fea162010ff10b10047fe6588043fe32c4011fe9962010ff0cb10007fea388003f751c4001ff28e2000ff54710007f8a388003f451c4023ffa0e2000ff90710007ec8388003fd41c4001faa0e2011ff10710047fe6388023fe31c4011fb18e2008ff4c710047ea6388023fc31c4021ff90e2000ff88710007ec4388003fd21c4001fa90e2010ff08710007fea188013fe50c4001fea862004ff1431008ffe8188013fe40c4001fea062004ff10310047fe6188013fe30c4011fe9862004ff0c310087fe4188013fe20c4001fe9062004ff08310027fecb08012ff6584009ff32c2009bf99610027facb08002fd6584009fe32c2004bf19610027fec908012ff6484009ff3242003bf99210027fac908002fd6484009fe3242004bf19210007fea90803ffe5484001feaa4200fff15210027fec708012ff6384009ff31c2002bf98e10027fac70803afd6384009fe31c2004bf18e10077fea70803b7f538401dff29c200eff54e10076faa70803bfc538401dffa1c200eff90e10077fa870803bfc4384009ffb142004bfd8a10027fcc508006fe6284009feb142000bf58a10027f8c508012fc6284001ffa94200dff94a10007faa508037fc528401fffa14200dff90a10007fa8508037fc428401dff994200dff8ca10077fa6508037fc32840177eb0c2000ffd4610007fca308003fd5184001fe28c200fffd0610007fc8308003fd418401ffe20c200effcc610077fc630803bfd318401dfe18c200dffc8610007fc4308003fd218401bfe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fea042004ff10210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fe9042004ff08210027fe2108013f71084001fd8
  | 2 => 0x400b7f8c4a0006fc6250001ffa928016ff94940007faa4a005bfc5250007ffa128003efd094001ffc84a000ffd4250001dea128003ff109400bffe64a005bfe325002ffe9928016ff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc6150001ffa8a8000ff94540007faa2a0003fc5150007ffa0a8003efd054001ffc82a000ffd4150001dea0a8003ff105400bffe62a005ffe315002ffe98a8017ff0c5400b7fe42a0003fe2150001fe90a8016ff0854001dfec0a0003ff5050009ff2828000ff54140027f8a0a000fff4050007fda028004ff901400277c80a0013fc4050009de2028003fe101400bffe60a0013fe305002ffe9828004ff0c1400b7fe40a0013fc2050009ffb2c4004bfd9620027fccb10026fe6588009feb2c4000bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc91000efe6488009feb244000bf59220027f8c910012fc6488001ffaa44015ff95220007faa910057fc5488009ffb1c4004bfd8e20027fcc71000afe6388009feb1c4014bf58e20027f8c710012fc6388029ffa9c4014dfd4e200a7fca710053fd5388029bea9c4014ff14e200a7fe8710053fe4388029fea1c4014ff10e2000dfac510007ff5288003ff2944001ff54a2000ff8a510007ff4288003ff2144001ff50a2000ff88510007ff3288003ff1944001ff4ca2000ff86510013ff6188009ff30c4000bf98620027fac310002fd6188009fe30c4000ffd4620007fca310003fd5188001fe28c4015ffd0620007fc8310003fd418802bfe20c4014ffcc6200a7fc6310053fd3188029fe18c4001ffc862000ffc4310003ee2188003fe90c4001ff0862000fd84310012fe6088009ffa844004ff94220027faa110013fc5088009ffa044004ff90220027fa8110013fc4088009ff9844004ff8c220027fa6110013fc3088009ff9044004fbc822000ff64110013fc2088009fc1044000ffd9520005feca900037f65480013fb2a4000ff9952004dfcca90003fd65480017eb2a4000ff1952004df8ca900037c65480013e32a4000ffd9120005fec89004ffe64480077f3224000ff59120005fac89004ffc64480077e3224000ffd512009ffca890003fd5448027fe2a24012ffd8d20095fec69004bfe63480057f31a4012ff58d20095fac69004bfc63480057e31a4012ffd4d20096fea69004bfe5348025fea9a4012df54d20097f8a69004bff4348025ff21a4012ff50d20097f88690012ff6248003ffa924001ff9492000ffaa490007fc5248003ffa124001ff9092000ffa8490007fc4248003ff9924001ff8c92000fdc6490007fd3248025f69924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148001ffa8a4000ff94520007faa290003fc5148027ffa0a4000ff90520007fa829004
  | 3 => 0xfb20a004ff9905001dfcc828013fd64140017eb20a004ff19050025f8c828027ff5414013bfaa0a009ff9505004ffaa8280037d5414013fe2a0a004ffd8c50025fec628013fe63140057f318a004ff58c500ddfac628013fc63140097e318a009ffd4c5004efea628027fe5314013fea98a01bdf54c5004ff8a62806fff4314037ff218a01bff50c500dff88628013ff6214009ff310a001bf98850027fac428002fd6214009fe310a004bf1885004ffea428027fe5214035bf290a009ff5485004ff8a4280277c5214039ffa10a01aff90850007fa842806bfc4214037ff990a01aff8c8500dffa642806bfc3214009ffb08a004ff98450005fcc228013fd61140017eb08a004ff1845004ffea228027fe5114001bf288a009ff5445004ff8a2280277c5114039ffa08a000ff90450007fa8228073fc4114037ff988a01bff8c4500dffa622806ffc3114035ff908a000ff88450007fa422806bfc21140097f300a004ffd4050026fea028013fe5014009fd280a004ff54050026faa028027f95014009ffa00a004ff10050027fe6028013fe3014009fe980a004ff0c050027fe4028013fc2014009ffb2c8004bfd9640027fccb20026fe6590009feb2c8000bf59640027f8cb20012fc65900077eb248003ffd524001ffca92000ffd5490007fe2a48004ffd8e40025fec720013fe63900057f31c8004ff58e400cdfac720013fc63900097e31c8019ffd4e400cefea720067fe5390033fea9c8019df54e400cff8a72000fff4390007ff21c8003ff50e4001ff88720013ff6290009ff3148001bf98a40027fac520002fd6290009fe3148004bf18a40007fea520063fe5290001fea948018ff14a4001ffe852000ffe4290007fea148003ff10a400cffe6520063fe3290033fe9948018ff0ca40027fec320013fe61900017f30c8004ff58640005fac320013fc6190001ffa8c8000ff94640007faa320003fc5190007ffa0c8003ff906400077c832000ffd4190007fe20c8003ef106400cffe6320067fe3190033fe98c8019ff0c6400c7fe4320003fe2190001fe90c8018ff08640025fcc120013ff5090009ff2848004ff54240027f8a120013ff4090009dfa048003fed0240027f88120013f84090009ff9848004ff8c240027fa6120013fc3090009ff9048004ff08240007fecaa0002ff6550001ff32a8009bf99540007facaa0002fd6550001fe32a8009bf19540025fec8a000fff5450001dfaa28003ff9514001ffaa8a000ffc5450007de2a28017ffd8d400bdfec6a005ffe63500057f31a8017ff58d400bdfac6a005ffc63500057e31a8017ffd4d400befea6a005ffe535002ffea9a8017df54d400bff8a6a000fff4350007dfa1a8003ff90d4001ffa86a005fbd4350007fe21a8000ffd8940005fec4a005bfe62500037f3128000ff589
  | 4 => 0x27fc52d404bffa16a023ff90b50007fa85a808ffc42d4049ff996a023ff8cb50127fa65a808ffc32d4013ffb0ea009ff98750005fcc3a8027fd61d40017eb0ea009ff1875004ffea3a8027fe51d4013fea8ea009ff1475012ffe83a8003fe41d4001fea0ea025ff10750127fe63a8093fe31d4049fe98ea024ff0c75011ffe43a8003fe21d4001fe90ea023ff0875012ffe81a8013fc40d4049ff986a004ff8c350127fa61a8013fc30d4047ff906a004ff083500f5facb28013ff6494009ff324a003bf992500277cc92800ebe6494009feb24a000bf592500277ac928002bd6494009fe324a004bf1925004ffea9280037f5494045ff2a4a000ff55250006faa928027fc5494009ffb1ca004bfd8e50027fcc72800afe6394009feb1ca021bf58e50027f8c728012fc6394013ffa9ca021dfd4e5010ffca728087fd5394043bea9ca009ff14e5010ffe8728087fe4394043fea1ca021ff10e50027fec528013fe62940037f314a004ff58a50005fac528013fc62940097e314a009ffd4a50107fca5280837e5294001fea94a009ff14a50106f8a52808bff4294041ff214a000ff50a50107f88528087ff3294041ff194a021ff4ca50107f86528013ff6194009ff30ca000bf98650027ecc328002f66194009feb0ca000bf58650027eac328002f56194009fe30ca009ffd4650007fca3280037e5194001fea8ca009ff14650006f8a32808bff4194001ff20ca000ff50650117f88328087ff3194043ff18ca021ff4c65010ff86328083ff2194001ff10ca000ff48650107f84328012fe6094009ffa84a004dfd425004ff6a128013ff4094009fe204a004ffcc250027fc6128013fd3094009fe184a004ffc8250027f84128003ff64540017fb22a01fff9915001dfcc8a8003fd645403ffe322a003bf1915004ffea8a807ffe5454001feaa2a009ff151500f7fec6a807aff635403dff31aa002bf98d500f7fac6a807afd635403dfe31aa002bf18d5004ffea6a807b7f535403dff29aa01eff54d500f6faa6a8027fc535403dffa1aa01eff90d500f7fa86a807bfc4354001ffb12a000bfd89500effcc4a8006fe6254001feb12a01dff1895000df8c4a8027ff5254001bfa92a01dff94950007faa4a80037d5254013fe292a01fffd09500effc84a8003fd425403bfe212a01effcc9500effc64a807bfd325403bfe192a000ffd8550005fec2a8003fe6154001feb0aa000ff18550005f8c2a8027ff5154001ff28aa000ff5455004ff8a2a807fff4154001ff20aa000ff505500fff882a807bff315403dff18aa01eff4c5500f7f862a8077ff2154001ff10aa000ff485500eff842a8027ff5054013fda82a004ff94150026fca0a807fff4054009fe202a01effcc150027fc60a807bfd3054009fe182a01dffc8150027f840a8026fe6514009f
  | 5 => 0x814101ffe80a080fbf4050407fe202822bffcc14115ffc60a08affd3050457fe182822affc8141157f840a0803ff65884017fb2c4200ff9962104dfccb10803fd65884017eb2c4200ff1962104df8cb10803ff64884017fb244229ff9922101dfcc910803fd64884017eb244229ff1922101df8c910803ff5488453ff2a44200ff5522114ff8a9108a3ff63884517fb1c4228ff98e21015fcc7108a3fd63884517eb1c4228ff18e21015f8c7108a3ff5388451bfa9c4228ff94e21147faa7108a37d5388451fe29c4228ffd0e21147fc87108a3fd4388451fe21c4201bf58a2100ffea510807fe5288403fea944201ff14a2100ffe8510807fe4288403fea144201ff10a2100ffe6510807fe3288403f71944201ff4ca21147da6510807fc32884037f30c4200ffd4621007fca310803fd5188401fe28c4229ffd0621007fc8310803fd4188453fe20c4228ffcc621147fc63108a3fd3188451fe18c4201ffc862100fde4310807f72188403fe10c4201fd08621007fec110803fe60884097f3044200ff58221005fac110803fc6088453ffa044229ff10221147fe61108a3fe3088451fe9844228ff0c22100ffe4110807fc2088403f61044200ffd9521005feca90803fe65484137f32a4200ff59521005faca90803fc65484137e32a4200ffd9121005fec89089ffe64484077f3224200ff59121005fac89089ffc64484077e3224200ffd512113ffca890803fd544844ffe2a24226ffd8d21135fec69089bfe63484057f31a4226ff58d21135fac69089bfc63484057e31a4226ffd4d21136fea69089bfe534844dfea9a4226df54d21137f8a69089bff434844dff21a4226ff50d21137f88690806ff6248403ffa924201ff9492100ffaa490807fc5248403ffa124201ff9092100ffa8490807fc4248403ff9924201ff8c92100ffa6490807fc32484037fb0a4200ffd4521007fca290803fd5148401fe28a4227ffd0521007fc8290803fd414844ffe20a4226ffcc521137fc629089bfd314844dfe18a4201ffc852100fee4290807fe2148401f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024204bf1812113ffe809089ffc404844dff9824226ff8c121137fa609089bfc3048403ff9024201ff0812104ffec9a8027fe64d40077f326a009ff59350005fac9a8027fc64d40077e326a009ffd535004ffca9a8027fd54d4013fe2a6a009ffd8f5004dfec7a8027fe63d40057f31ea009ff58f50125fac7a8027fc63d40057e31ea009ffd4f5004efea7a8027fe53d4013fea9ea024df54f5004ff8a7a8093ff43d4049ff21ea024ff50f50127f887a8027ff62d4013ff316a001bf98b5004ffac5a8002fd62d4013fe316a001bf18b5004ffea5a80277f52d4013ff296a009ff54b50006faa5a8
  | 6 => 0xfbea98a209ff14c5117ffe86288bffe431445ffea18a22fff10c5104ffec428827fe62144037f310a209ff58851005fac428827fc62144037e310a209ffd485104efea428827fe5214413fea90a200df5485104ff8a4288c3ff421445dff210a200ff50851177f884288bfff321445dff190a22fff4c851177f864288c6fe6114413ffa88a209dfd445104ffca228827f65114413fea88a200df5445104feaa2288c3ff4114461fe208a22fffcc45117ffc62288bffd311445ffe188a22effc8451177f84228827ff6014413ff300a204bf9805104ffac028802fd6014413fe300a230ffd0051187f880288bfff301445fff180a22fff4c05117ff860288bbff201445dfe100a200ffd9641005fecb20803fe65904137f32c8200ff59641005facb20803fc65904137e32c8203bf5924101ffea920803bf5490407ff2a48203ff5524101ff8a92080fbc549045bffb1c822dbfd8e4116ffcc72080afe639045bfeb1c822dbf58e4116ff8c72080afc639045bffa9c822ddfd4e4116ffca7208b7fd539045bbea9c822dff14e4101ffe872080fbf4390407ff21c8203ff50e4116f7a872080ffc4390401ffb14822cff98a4100dfcc520803fd62904017eb14822cff18a4100df8c520803ff5290459ff2948200ff54a41167f8a52080fff4290407dfa148203ff90a4101ffa8520803bd4290407fe214822dffcca41167fc65208b7fd3290459fe1948203bf98641007fea320803fe5190401fea8c8200ff1464101ffe832080fbf4190407fba0c8203ff1064101fe883208b7ff319045bff18c822dff4c64116ff863208b3ff2190459fe10c8200ffd8241007fcc120812fe6090401feb048200bf58241007f8c12080fff4090407fe2048203ef1024116ffe61208b7fe309045bfe984822dff0c241167fe41208b3fc2090401ffb2a8200bfd9541006fecaa08027f6550401ff32a8209bf99541007facaa0802fd6550401fe32a8209bf19541006f8caa08027c65504077fb228203ffd514101ffca8a080ffd5450407fe2a2822bffd8d4115dfec6a08affe63504057f31a822bff58d4115dfac6a08affc63504057e31a822bffd4d4115efea6a08affe5350457fea9a822bdf54d4115ff8a6a080fff4350407ff21a8203ff50d4101ff886a0803ff62504017fb12822aff9894100dfcc4a0803fd6250455fe3128201bf18941007fea4a08abfe5250401fea92822aff1494101ffe84a080ffe4250407fea128203ff1094115ffe64a08abfe3250457fe992822aff0c94101dfec2a0803ff5150401ff28a8200ff54541007f8a2a080fff4150407fba0a8203ff905410077c82a080ffc4150407de20a8203fd1054115ffe62a08affe3150457fe98a822bff0c541157fe42a08abfc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028204bf1
  | 7 => 0xa8827fd62d44017eb16a209ff18b5100df8c5a8827ff52d4413ff296a209ff54b5104ff8a5a88e7ff42d446fff216a200ff50b511bff885a88e3ff32d446fff196a238ff4cb511bff865a88e7ff41d4473fe20ea238ffcc7511c7fc63a88e3fd31d4471fe18ea237ffc87511bff843a8827ff60d4413ff306a204bf9835104ffac1a8802fd60d4413fe306a239ffd03511cff881a88e3ff30d4471ff186a238ff4c3511c7f861a88dfff20d446ffe106a233bf59651007fec9288dbfe64944077f324a200ff59251005fac9288dbfc64944077e324a209ffd52511b7fca9288db7e5494401feaa4a209ff152511b6f8a9288c7ff63944637fb1ca231ff98e51015fcc7288c7fd63944637eb1ca231ff18e51015f8c728827ff5394463bfa9ca231ff94e5118ffaa7288c77d5394413fe29ca231ffd0e5118ffc87288c7fd4394463fe21ca200ffd8a511affcc528806fe6294401feb14a200bf58a511aff8c528806fc6294413ffa94a200dfd4a511affca528803fd5294401bea94a209ff14a511b7fe85288d7fe4294401fea14a235ff10a5118ffe65288d7fe3294463fe994a235ff0ca5104dfcc328827ff5194401bfa8ca209fdd46511b7fe83288dbfc4194463ff98ca231ff8c65118ffa63288c7fc319446bff90ca235ff08651007fec128803fe60944097f304a200ff58251005fac128803fc609446dffa04a236ff1025118ffe61288c7fe3094463fe984a231ff0c2511affe41288d7fc2094401ffb22a200bfd91510077ec8a8802bf6454469ff322a203bf99151007fac8a88d3fc64544077e322a200ef1915101d78c8a8827ff5454469ff2a2a200ff5515104ff8a8a88cfff63544677fb1aa233ff98d51015fcc6a88cffd63544677eb1aa233ff18d51015f8c6a8827ff5354467bfa9aa233ff94d5119ffaa6a88cf7d5354413fe29aa233ffd0d5119ffc86a88cffd4354467fe21aa200ffd8951005fec4a88cbfe62544037f312a200ff58951197f8c4a8806fc6254413ffa92a232ff94951007faa4a8827fc5254469ffa12a232ff90951007fa84a88cbfc4254467ff992a232ff8c95119ffa64a88cbfc3254413ffa8aa209fdd4551007fca2a88037e5154469ffa0aa234ff1055119ffe62a88cffe3154467fe98aa233ff0c551197fe42a88cbfc2154401ffb02a200bfd8151007fcc0a8803fd6054401fe302a204bf181511a7fe80a88d3fc4054467ff982a233ff8c15119ffa60a88cffc3054465ff902a232ff0815104dfcca28827ff6414413ff320a203bf9905104ffac828802fd6414413fe320a203bf1905104ffea828827fe5414461bf2a0a209ff5505104ff8a8288277c5414413ffb18a209bfd8c5104ffcc62880afe6314413feb18a22fbf58c5104ff8c62880afc6314413ffa98a209dfd4c5104ffca628827fd531445
  | 8 => 0xfccb5200ffc65a9007fd32d4803fe196a409ffd875204ffcc3a9002fe61d4813feb0ea400bf5875204ff8c3a90fbff41d487dfe20ea43dffcc7521effc63a90f7fd31d487bfe18ea401ffc875200ff843a9027ff60d4813ff306a404bf9835204ffac1a9002fd60d4813fe306a43effd03521f7f881a90f7ff30d487bff186a43dff4c3521eff861a9007ff20d4803fe106a401bfd9552007fec8a9002ff6454879ff322a403bf99152007fac8a90f3fc64548077e322a409ffd5152006fea8a90f3fe5454801feaa2a400df5515204ff8a8a90efff63548777fb1aa43bff98d52015fcc6a90effd63548777eb1aa43bff18d52015f8c6a9027ff5354877bfa9aa43bff94d521dffaa6a90ef7d5354813fe29aa43bffd0d521dffc86a90effd4354877fe21aa401bfd895200ffea4a9027ef5254803ff292a401df9495200ff8a4a90077c5254803f6292a401ffd095200ffc84a9007fc4254803ff992a401ff8c95200ffa64a9007fc3254801ffb0aa400bfd8552007fcc2a9003fd6154801fe30aa400bf185521e7fe82a90f3fc4154877ff98aa43bff8c5521dffa62a90effc3154803ff90aa401ff08552007fec0a9002ff6054801ff302a400ff58152007f8c0a9012fc6054879ffa02a43cff101521dffe60a90effe3054877fe982a43bff0c15200ffe40a9007fc2054801ffb2a8400bfd9542007fccaa1026fe6550801feb2a8400bf59542007f8caa1026fc65508037fb228403ffd514201ffca8a100fbe5450807feaa28400ef5514201ff8a8a10ebff63508757fb1a843aff98d42015fcc6a10ebfd63508757eb1a843aff18d42015f8c6a10ebff5350875bfa9a843aff94d421d7faa6a10eb7d5350875fe29a8403ffd0d4201f7e86a100ffe4350807fea1a843aef50d4201ff886a1006ff6250803ffa928401ff9494200ffaa4a1007fc5250803ffa128403fbd094200ffc84a1007be4250803fe2128401ef1094200fd884a1007ff3250803ff1928401fb8c94200ffa64a10ebed3250803fe1928400ffd8542005fec2a1003fe6150801feb0a8400ff18542005f8c2a100fff4150807fe20a8403ef105421d7fe62a10ebfe3150875fe98a843aff0c54200ffe42a1007fc2150801ffb028400bfd8142007fcc0a1003fd6050801fe3028404bf1814201ffe80a100fbf4050807fe202843affcc1421d7fc60a10ebfd3050875fe1828401ffc814200ff840a1027ff64d4413ff326a203bf9935104ffac9a8802fd64d4413fe326a203bf1935104ffea9a8827fe54d4413feaa6a209ff1535104ffec7a8826ff63d4413ff31ea202bf98f5104ffac7a88e2fd63d4413fe31ea202bf18f5104ffea7a88277f53d4413ff29ea209ff54f511c6faa7a8827fc53d4471ffa1ea238ff90f511c7fa87a88e3fc43d4413ffb16a209ff98b5100dfcc5
  | 9 => 0x400400409801c00003002c02806000002005c03400000000000800c0ac04002400c01000801c0100040140ac00000000800400400000007000004400800000401402401c01801006800400400000000c01801800c00000000003000000001008800000002c02001c00400000000001c01400406400400c03404801800004000800c0140380fc01000802402401402405c00800801003000402c00401000800408400400000000c077f32ea803bf5935401ffca9aa00f7e54d5007df2a6a803cf9535401ff8a9aa00f7c54d5013ffb1ea809bfd8f5404ffcc7aa00afe63d5013feb1ea842bf58f5404ff8c7aa00afc63d5013ffa9ea809dfd4f5404ffca7aa027fd53d5085bea9ea809ff14f5401ffe87aa00ffe43d5007fea1ea803ff10f5404ffec5aa027fe62d50037f316a809ff58b54005fac5aa027fc62d50037e316a809ff94b5404ff8a5aa00fff42d5007ff216a803ff10b54217fe65aa107fe32d5085fe996a841ff0cb5404ffec3aa027fe61d50017f30ea809ff58754005fac3aa027fc61d5007ffa0ea803ff1075401f7883aa10bff31d5085ff18ea842ff4c754217f863aa107ff21d5083fe10ea809ffd835404ffcc1aa012fe60d5013feb06a800bf5835404ff8c1aa00fff40d5007dfa06a803ff10354217fe61aa10bfe30d5085fe986a842ff0c35420ffe41aa107fc20d50077fb2aa803bfd915401ffea8aa027bf5455007ff2a2a803df9515401ff8a8aa00f7c5455007de2a2a840ffd8d54205fec6aa103fe63550057f31aa840ff58d54205fac6aa103fc63550057e31aa809ffd4d54206fea6aa103fe5355081fea9aa840df54d5404ff8a6aa00fff4355007ff21aa803ff50d5401ff886aa003ff62550017fb12a83fff9895400dfcc4aa003fd625507ffe312a801bf189541fffca4aa027fc5255007ffa12a803efd095401ffc84aa00ffc4255081ff992a83fff8c954207fa64aa0fffc3255001ffb0aa800bfd8554007fcc2aa003fd6155001fe30aa800bf1855401ffe82aa00ffc4155081ff98aa840ff8c554207fa62aa103fc315507fff90aa83fff08554007fec0aa002ff6055001ff302a800ff58154007f8c0aa012fc6055007ffa02a803ff10154207fe60aa103fe3055081fe982a840ff0c1541fffe40aa0fffc20550037f32ea409ffd935204ffcc9a900efe64d4813feb26a400bf5935204ff8c9a900efc64d4813ffaa6a409dfd535204ffca9a9027fd54d4801beaa6a409ff1535204ffec7a9026ff63d4813ff31ea402bf98f5204ffac7a90f6fd63d4813fe31ea402bf18f5204ffea7a90277f53d4813ff29ea409ff54f521eefaa7a9027fc53d487bffa1ea43dff90f521effa87a90f7fc43d48037eb16a401ff94b5200efca5a9007ee52d4803fe296a401df14b5200ffe85a9007fe42d4803fe216a401f
  | 10 => 0x5c77418911e098802d38b8d483ac10e079119505a8610801ae807c133237936829670d2e51804a684d12d517b004c0361de80000000003420850e6442d31aa16cc7e81f069853cc8c38a2521b84d9e3e60f01ba08664f8031800039a5b13490b3c0f6009426807000400000c00c02002402c0040000040080ac00801c00800002001000000c0000000940900d403401c09400005000001c0140f006008400c06800000000800400000000800403000000800401000009c0040bc01001405400c00000401006806c00401003c01404802006004800c0140000bc00000c03403c01401800004c00400402000c0040240140f003803400800005402804400000000000401400400803c03c00c0640a402009400804c13400400400000800c00002004407002404004803c01800000008400000c00003800003000004c05400c03402404400003803006814401c03800000006c07806400003809c01000400405000002800002c01001c01800002401c00000009c08c00000800000c03401003400002001404805000001800400002411400400407002c03800400000002c00804c00c06402800000400001800807000000000803c00800000801c00006c06801400000000000c06000400000405001800001400800001801000401401c0080040b408c0440840140700000300000080c40500a408400006002002800400400802403400004000400003000801000401800000400001402000002003400000000800400400801c01800400008800001c04c0ac0000080000180000a018000400000004000400400c02800000400400005c01806008c00007c0800080740c807801402c01000800002c03805802401806800000000400c00c00800400c0000000000180000240c000800000802802800c02800001802c00001800805004c00009001802802404801401800803001c00c00400000000001000400400000400c00400c0740100080a800004400000c01801c0a803018800005003400c05000404c00c0040040b400000003c04401001803002c01800407803804000c02003401002401800800000804401801800000002403000802c00001c0040400000c405c0000600640000440080180000000240140200b803c00001c02000000800000011804c00000000c01003401801000800003804800803420002c00006000401800806c00000407400400403c0000f000001002c04402c01c00001000000801c00400c04002800000401005400802805000014009800000804400c00002804400401004000000000400001002802000403400800000000400c00005c00005003005c00c02c0b800c01000803000c03c00400401001002403000c06400000000400c00000000801c0180140280280000000780000040000440d000401002800002c03409000
  | 11 => 0x1ba84d200005196008f27803598ce4e1e24a30a01081827382b08000c240000ad1f60d4e8791099bec55868000000008be16f0000b6cf5448800003dc0005283e6212815a12a1b301384747fb2079780f445cf0001d742d249e3940000e987431821b6c7861a929799986dc0ee000032d08265a3d806d4abc6fc00020708927b542b0794a0c13b21d9f5416c000000000042c83f1b48f00f0e53d175911035a6070d71c30000420406143c93e49541b8bd0edc0001dd0dbce2629d000119c7f22d63029544b6005522d8efcdb81a82ef80006461340001d0000052a18798640000fd0f50dd89c60e43d60d64726056000000082a72008a9658c1e8331d811f024c7c30000000a640000001b6507c29c26488f459a19d36295b0d5473700000000002ab000000000070e1b500000008603d1869c0006232dd8618fc65f9410800086857400b09dcd680b000000001f63d42a41faced641243717480007c517d00000000000ea00000a63dc270029000004b1539098f3400014f11300003eb2d211045840391f106343ba0000f681646ce5c116f0800a920000000d3486c0001888000fc20001fe144027a7293fe8000eee83b2031f185b800042786286443c525a01506b8699000210814a3633d496400985ea06614f8dee03a3d30fc50d63ab2f30690f264a13a39138fbc0b936f149c76605a1a0124c3585651381cac0204603a90fa417a7bd000000077817a2b500008d82980000768f404bf1e98a288842e508e84400d22652fd80040005a54121b5c14e0003811c2c00029b15800f41ae83d00009fc32c07a2c480003c6000390815c7b01952cb880c4e41d3108918ca020003cd800000000000011c07d00000d300000005c32d3800021000000000008b407e32a80000000002b2000000087200005f403e8450000e8800000025a8c14000000184816006e0000960fe8f168581461c289981360001bb000000029f8000fb6432181121c1d470829d20348fc05b14f811493263b21b952cb563bb3ce11b8aee6c72140a00f901c81b817c49e25a243e83c09d03412711eec0001ef0b88e08e8c20b1ca0ca0304038352a164fce2ee00019740e856f0000a8d0c85fa32f959c92e0f60000f6c55e5090001118e5c00000010c414c6c4239166d07400007e07289542043a704903100ab02e0f800305793f408e02140ba20000000008503c2063800071e000105c0000000001cd000075313300010904e105f1a2434040401da020c685a612c00ac4e65f80dd0cc44d846b31b00943ee81d21180683f45e501a8fb415021c1fc131ca5278e218150410c2011359ab41b254006c11545aa2dd33013340004841b41eacc880001d6150c62c37128898005425f227992c80780002c789709ec2b305989000002630028d909dc6f51780d5cef087126284047
  | 12 => 0xb0479e14a9a0400060e384a0601e86270a0057c0000662ea0d40d645c51e40000110227000000041807517f80007fa6873ef9e7c76a0ed2ad8d780000ec3d0800051c7d20000660bac0001898f389182b10ae0064e74000000182c0000003bb1770b746d30001a2c0000e710d009c2521e6318a0989e04a006a8e7c170348041a1948e808c29d9a60f782c72b31b74c9e73b24d17f46ac57f1101d20ce63f33b01e185a63550c9123806081311996185925cc32080000005b704d85d480400006800003462cc09c0000ac600000017605967da0d812b00000000a6800000073c0001cc01cc0002868000e3e00000011c477210c1551e20c9267e1628c50eb02e300017c094416236f9058b5038827d93200000001870fd01423271c71d14c646c02c09338000000242891465e46143e0f2c9367b700e00d0a6c4b92111bb4dde4030108f7cbe611c19a9a0856c81433a05fc98c6a106f9a387d81e7000089074234b25781f40005444018854de482931c038ca3a0003b500001242c403094c100e54a2729c18f8e2f207595a04b41aa3269674be88680b5161cd2e00000013fd02c02e38d1e649d41190faa11856400000012e0fb80000001c58000482154949400023208589401340000311ca80001d736a05643dc3813c80670c8e72d2f48c0417e14628712408225ff1501754ff459e365a1381ac17733a9734a9855c40d866c9f20001571f10c407c90728000ce045d1c20b28e622c11958344efe30c3a81a188c851e14286e46ca8703e98e482a854538087906763f60001a74afc1132aa1204b284c217f000107047a04f020497c2190efa1cc43c7af3eb0b6060e15d3650224abe3a00c889910fc81911b0ae40002f70cf0d445e273d1a485b07ba535081107446e29743b14982e669505118f80000000001fb00002c30000e54000881338998c84800038c2124b5a0523089d047e46a41df205400048012d82604602f820f1d687c269e37c114ca5a4a83b7840cbec2a43dc0cb8d926160d914dc3985160040e990b467f0f81ecc70e66a328955cdca79640107c4e222ad3b996f409e000091179c16a38c29706fc3c261e2d00ccc3921941710ba0f060001a783800004b13418538adc85c07c800000058a1e699907c81b438d96fca586f43f300fc2c61303338300f5c5c93ab1b449a000000020d8b2219f23e8944a267980000e78cae2b83890c60dfc4831748d1cafa71000000003b06c620c98682d629639f80003f019943492b8af40000001b3039c0002819d9cca46bc41894f07de86c0e007f4de252b4311d4478800016c9f048fe0001268b009ea5d73d6848025c81a1d500001a40c40b80cfc0004a722e1549054665000064cfa06c80000000b306e4000210c0001c2082847cd700001371a7c0d8595026a1002a43960d1076c0006240
  | 13 => 0xa10000000759000000000085e3b19e9400031d04686148bc16e0000000e4c286245916400000002320e4c1000004a037482022c0001ad8f3a00013d92b4d146a20000744fea67600000006c400034e00b06526f923305f8de013500000004ce0ef32f000000013a045000010e5e8000091c00020233796c891a34210e80780d60001cc8144a141270001fa418e6452351555096570000000000013f1eb95e10cc0003b117889ee4290db03188a000015f18400007850a3932ccd200012a139c02a63a00020380000000ea85ec5ea00000009f0b241bb000142c7340000000e9468668f28a8000d5c11404f80007b20002de0f8cada3f53f21bac59c7540000f941b678f1531bfcfca57131996ccc3a16d3ff8b205062291bb8554f0480f20c1d7c1d284705a0c68eca1411c58cc839e00b2581574d263a92f19fb47dc2413f81f5004874f000019c8125580f41bccbea68800000000004392239fc8c5428f3c6194012c6bb08b08b890c1f64030590e583f721f800000024c0001d6ce325ac3f717b42e81fb1cc16348a44d42860088e7c5af10d82140000c32769224d4600000000007ce0000000000000111000161000051f1e30cf90e885213400001f00001e51160ec259f2ef00000f20cd304800000040c2cc88400004eb0af0000af67570001ff0dfa4071db9f3c0003452fb8d802ca11e12a8000d6e29030c0bec0000001931b3419024e26189d4b8048a1ce0a0878e5ef2b01abc2b60171ed19e0c1827d1030db10503891e11b38e5e1ec0969de8ba28303eb8cc027846909b8b981043d121aa1dcb4215822181bcdce292110a0444ac2d72da023901487b3aa82804540000000000b700000000f400006022cd19003d204407894800083801aa2010ef636d3a1188906a00013c8c0c00000020a000000086a433837000021f0000000000451045800000075e00005d8e2810415b9810a100fe20e197044c02f0001c106f25db0000ee03340001850764e925e40799dc860c1f22650b400001250001ac400052300000000001cb14d1e04638768146878800054727d19210a62711c7a0c830200005b8cdc0000000089fc487068c06f0fa8b0a58803e0000502106000059cfe858e2ed0a4497679521e8f3cc38190048845c0002ea2e11774b6c4ab1ff915c19e4050001bb82e40001c6800000033407f8b7c2ac0000001ac0d585722c1833831800000000745a40002e40000000000000137cbb22fc27301a00000230e321b4a483f012780c447e0b22071a581c411a3cb913c9287920a51f389d83fb2ac9b4891e1fe2ba98e421e5fe205819448800036c0000efa4b30f9877000000017618f47980000d080003866bf04c88c4ecc0001e91bd80005933b804c853264a25b07104e82573181c8cc9c31727e14005c02b513d03a0b526a0339054c
  | 14 => 0xd00a3d6236800045a09500010ac44465916882ec5ce08f0f59efc83e2e1000000054a4c1000003cd287b610b94140fe8550001f64f48000032000104e000217851400000007a89a892462609c911435e01b00005e0ca687a31090691002252b10e0c1f4517177817caac70500a004c4be8572129a984b210d11792f105649819518b90686d6000025cd8400041e0dfc9c800031b8e6cc3e5ce36d13605440da2530d101580501119028f942390071538f8032c2250240dc67441c82000d5241b3928e1434a338368018074e107000186c37c0003d886f0af87a80c218b42ae5d31c88a4c00006d3ae092015e5cb11e0b6902060a16a0eb45e625d130865c66c518334112c3fe37326b945006620a3999710ca83150c01e249b67a71ce91dcf2802806a19f0c2e2e410c000001a62c2150d18e96685393971c0062521378a206163af2d7000009237210720810ea0731ff10b08ac4fe142133c6b051921e14e45da7ba0d8820064a33a3b8950829849c4090d6cc9880938a9ef80865b52c60ec89ac40d00302a46a647b40f1540a420781079ed0cf624205e01dc9b87cd000000000051b0239ae4f2204a3a500003068232b992940001fc0958824e3a37500001c80140000610a250de1663711f44cb62f6391092cb160000b00000024000335854105c0002838000c5e31002009e10ba6e91901cd8dcc0000241568cf425e1be87783126bd31480001c27c20c78e188ec32d000000000011222691a0c1a4d337d1f88d361281b08c7c92c56b3be1960d864d93b612440646ab15e8c900e24dd4009fe04108440b40324a085330e81b540184a932582740ba2352911518fd451c3098460a342493308df02f24012dc90e884262530a858461047300000007820001b580002464ba0001b80c564d500013f467867700019b0cf22bb2f082c4fee3d50d588f89461c50001f80a9e06a09f05f0d507cb0002150cfa000186800000002942601782628632fe00005508513ff081505806e00000009bc31e17c87e44861b72790d385fa6b53bf0dec51669a3bc81d841a60615e0ea0ba03a439aa17c15c2531090510c8423b2ce15a4f142b40de9988826440123074805442e11a1c900000003c68314a702760a89fd82923740001dd424235d1da154cbd67b904e02a8000817000000050e80b04219b4e0e427097800000e64308d9da40001481039a340006be00001c000026d00000809e83781a5071c72e0001630000000319000000087c40818d850d04a00038e0000d2018b0000df857400019e8ec4a9a00039c8c840001f400000004500003141300c780001ad0000ec80003f980008900ca15f93480003c92748000eda703000024ca620003800f7905e22b00015d8ff22600d999b8bdc37a23a80004fc7dd1801a450440001d1800000034c2df070497a74d
  | 15 => 0x2623018008cac8780208424b8c4623609fbcb4687f25b800093a7b200014485285020000d7c0003b622a000030e1b800013b
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc2159010026bf7059010026be7059010026bd7059010026bc7059010026bf5059010026be5059010026bd5059010026bc5059010026bf3059010026be3059010026bd3059010026bc3059010026bf2059010026be2059010026bd2059010026bc2059010026bf1059010026b71059010026be1059010026bd1059010026b51059010026bc105901004cff76d5010024fe76d5010004fd76d5010024fc76d501001ebe64d5010006bd64d501003f3e54d5010004ff7655010024fe7655010004fd7655010024fc765501001ebe6455010006bd6455010004ff755881004cfc7558810004ff745881001cfe745881001cfc7458810004ff7358810014fe7358810004fd7358810014fc73588100067f53588100067d5358810026ef725881002eee525881002eee3258810006ed325881000cff715881000cfd715881002cfc715881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026f5105881004cff76d4810024fe76d4810004fd76d4810024fc76d481004e7e65d48100067d65d48101f6be64d4810006bd64d4810004ff7654810024fe7654810004fd7654810024fc765481004e7e65548100067d65548101e6be6454810006bd645481000eee6254810006ed6254810004ff7650810024fe7650810004fd7650810024fc765081001ebe6450810006bd6450810005f77150810005f47150810004fd76d44101cebe64d4410006bd64d441022ef661d4410004ff769441004cfd769441004e7e65944100067d65944101b6be6494410006bd6494410007775194410025fa7094410005f97094410004ff7654410005bf745441003dbc74544101a6be6454410006bd645441004cff7614410024fe7614410004fd7614410024fc761441004e7e65144100067d6514410186be6414410006bd641441022ef66114410025fa7014410005f9701441008cff7690410024fe769041001cfd7690410024fc769041001ebe6490410006bd649041008ef66190410025fa7090410005f9709041008cff76504100057f75504100057c755041001ebe6450410006bd645041008ef66150410084ff7688410024fe768841000cfd7688410024fc768841014ebe6488410006bd648841000eee6288410006ed6288410086f66188410025fa7088410005f97088410084ff764841013ebe6448410006bd6448410086f66148410025fb7644010006fb7644010004fb76440100077b7544010007787544010007bb7444010007b87444010027ba6444010027b96444010007db7344010227d873440102277b5344010227795344010007eb7244010007e87244010025fb7144010027f3714401021efa6144010027f26144010007f25144010007f15144010007f24144010007f14144010
  | 1 => 0x4110006df63d4110126dc63d4110006ef62d411011eec62d4110005f671d4110005f571d411004cff7654110004fd765411004cfc76541100067f655411004e7c6554110006bf64541100febc6454110006df63541100f6dc6354110006ef62541100eeec6254110005f77154110005f47154110027f0105411001cff7650110064fd765011001cfc76501100067f65501100067c6550110006bf645011001ebc6450110006df63501100bedc6350110006ef62501100b6ec6250110005f77150110005f47150110007b54150110027f0105011000cff7648110054fd764811000cfc76481100057f75481100057c75481100067f65481100067c6548110006bf644811009ebc6448110006df6348110096dc6348110006ef624811000eec6248110005f77148110005f471481100067f65c41100067c65c4110006bf64c411008ebc64c4110006df63c4110046dc63c4110006ef62c4110086ec62c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c41100077865c4110007bb64c4110007b864c4110007db63c4110237d863c41102377b53c41102377953c4110007eb62c4110007e862c4110025fa71c4110026fb61c4110027f361c4110007f351c4110007f051c4110007f241c4110007f141c4110237f231c4110237f131c4110007f221c4110007f121c41100267f7559410004ff745941001cfe745941001cfc7459410004ff7359410014fe7359410004fd7359410014fc73594100067f53594100067d5359410004ff725941000cfe725941000cfc725941004cff715941004cfd7159410024ff7059410024fe7059410024fd7059410024fc70594100267e50594100267c5059410004ff755901004cfc7559010026bf745901003ebe545901003ebc5459010004ff7359010014fe7359010004fd7359010014fc73590100067f53590100067d535901003ebf4359010006be4359010006bd435901003ebc4359010004ff725901000cfe725901000cfc725901003ebf4259010006be425901003ebc425901001cff715901001cfd715901003cfc715901003ebc4159010024ff7059010024fe7059010024fd7059010024fc7059010026be4059010026bc4059010026f71059010026f51059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd53590100063d5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006be5259010006bc5259010006bf3259010006be3259010006bd3259010006bc325901003ebf7159010006be7159010006bc7159010006bf3159010006be3159010006bd3159010006bc3159010006bf2159010006b
  | 2 => 0x24f775214510007755214510025f67014510025f4701451029776501451029774501451007cfe76905100067f65905100067c6590510006bf649051001ebc6490510006df639051016edc6390510006ef6290510166ec6290510067b74190510005f6769051007ef6769051024df6759051024df47590510007776590510007746590510065f57490510007b7649051001ef6649051001ef46490510067b4649051001eb46490510007b75490510067b4549051028df7739051028df57390510007d76390510287d46390510287775390510287755390510067b74390510287b54390510005f57290510007e76290510007e46290510067b74290510007b54290510025f67090510025f4709051027fb6409051027fb44090510024fc76505100057f75505100057c75505100067f65505100067c6550510006bf645051001ebc6450510006df635051015edc6350510006ef6250510156ec6250510067b44150510005fb7050510025f87050510025f4765051001ef47650510024f4765051000777755051024df6755051024df47550510007747550510005747550510007776550510007746550510065f77450510007b77450510007b7645051001ef6645051001ef46450510067b46450510275f77350510275f57350510007d7635051026fd4635051026f77535051026f755350510005f77250510007e76250510007e46250510007f37050510025f67050510025f47050510007f07050510067b7405051006cfe76885100067f65885100067c6588510006bf648851014ebc6488510006df6388510146dc6388510006ef628851000eec6288510005f6768851006ef6768851024df6758851024df47588510007776588510007746588510005f77488510005f57488510007b76488510007b46488510265f77388510265f57388510007d7638851025fd4638851025f77538851025f755388510055f57288510007e7628851000ef6628851000ef46288510057e4628851000ee46288510057e6328851025fe53288510025f67088510025f47088510257e62088510257e42088510024fc76485100067f65485100067c6548510006bf644851013ebc6448510006df6348510136dc6348510006ef624851000eec6248510005fb7048510025f87048510025f4764851000ef47648510024f4764851024df6754851024df47548510007776548510007746548510005f77448510005f57448510007b76448510007b46448510245f77348510245f57348510007d7634851023fd4634851023f77534851023f755348510055f77248510007e77248510007e7624851000ef6624851000ef46248510057e46248510007f37048510025f67048510025f47048510007f07048510004fe76d41100067f65d411004e7c65d4110006bf64d411012ebc64d
  | 3 => 0xf725891006cff7158910006f77158910084ff7058910006fb7058910005ee7618910056ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d5318910057e571189102c6ef6118910007e63118910007e531189102c7e610189102c7e4101891004cff76d4910004fe76d4910004fd76d491004cfc76d49100067f65d491004e7c65d4910006bf64d49101f6bc64d4910006df63d49101eedc63d4910006ef62d491000eec62d4910004ff7654910004fe7654910004fd7654910004fc76549100067f655491004e7c6554910006bf64549101e6bc6454910006df63549101dedc6354910006ef625491000eec6254910005f77154910005f47154910004ff7650910004fe7650910004fd7650910004fc76509100067f65509100067c6550910006bf645091001ebc6450910006df63509101d6dc6350910006ef625091000eec6250910024fe76d4510024fc76d45100067f65d451004e7c65d4510006bf64d45101cebc64d4510006df63d45101c6dc63d4510006ef62d45101beec62d4510025fa70d4510005f970d4510025f676d451024ef676d4510024f676d451024ef765d45100077765d45100067765d451024ef565d451024f7465d4510005f574d4510007b764d4510007b464d451024df773d45102bdf573d4510007d763d45102b7d463d451024f7753d45102b77553d4510005f572d4510007e762d4510007e462d4510025f670d451024ff270d4510025f270d451024ff170d4510025f470d4510004fe76945100067f659451004e7c6594510006bf64945101b6bc6494510006df639451018edc6394510006ef62945101aeec629451024df67194510024fc76545100067f655451004e7c6554510005bf7454510065bc7454510006bf64545101a6bc6454510006df635451019edc6354510006ef6254510196ec6254510005fb7054510025f87054510004fe76145100067f651451004e7c6514510006bf6414510186bc6414510006df631451017edc6314510006ef6214510176ec6214510007755114510005f6761451024ef6761451024df6751451024f76751451024ef7651451000777651451000677651451024ef5651451024f746514510005f57414510007b76414510007b464145102af76541451024f74541451024df773145102a5f57314510007d7631451029fd4631451024f77531451029f755314510005f57214510007e76214510007e46214510
  | 4 => 0x8d102cede70d8d1005edd70d8d102cedc70d8d102cede50d8d102cedc50d8d10006df40d8d102cede40d8d102cedc40d8d10006df20d8d102cede20d8d102cedc20d8d102cede10d8d1005edd10d8d102cedc10d8d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910056ee62d891004cfe75d8910004fd75d891001cfe74d8910004fd74d891001cfc74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d89100067f53d89100067d53d8910056ee52d8910056ec52d8910006ef42d8910056ee42d8910056ec42d8910006ef32d8910056ee32d8910006ed32d8910056ec32d891000cfe71d8910024fd71d891000cfc71d8910056ef21d8910024fe70d8910054fd70d8910024fc70d8910056ef20d8910055ee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d8910257e771d8910007e631d8910007e531d8910257e610d8910257e410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910256ef71d8910056ee71d8910006ed71d8910006ef41d8910006ec41d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d8910256ee70d8910006ed70d8910256ec70d8910256ee50d8910256ec50d8910006ef40d8910256ee40d8910256ec40d8910006ef30d8910256ee30d8910006ed30d8910256ec30d8910256ee10d8910256ec10d89100057f75589100057c75589100067f65589100067c6558910005bf7458910065bc7458910006bf6458910006bc6458910005df735891005ddc7358910006df6358910006dc6358910056ec6258910004ff75589100067f75589100047f755891004cfc75589100067c755891004c7c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc73589100067f53589100067d5358910054ff7258910006e
  | 5 => 0x66be71d9110006bd71d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d911027ebe70d9110006bd70d911027ebc70d911027ebe50d911027ebc50d9110006bf30d911027ebe30d9110006bd30d911027ebc30d9110006bf20d911027ebe20d911027ebc20d911027ebe10d911027ebc10d91100057f75591100057c75591100067f65591100067c6559110066bc6459110005df735911005ddc7359110006dc6359110005ef7259110055ec7259110004ff75591100067f75591100047f755911004cfc75591100067c755911004c7c7559110064ff7459110006bf7459110004ff7359110006df7359110004df7359110014fe7359110004fd7359110014fc7359110006dc7359110014dc73591100067f53591100067d5359110004ff7259110006ef7259110004ef725911000cfe725911000cfc7259110006ec725911000cec725911007cff7159110006f7715911008cff7059110006fb7059110005be7619110066be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100079c63191100069c63191100073f53191100073d5319110006be6219110006bc6219110067b571191102d6bf6119110007b63119110007b531191102d7b610191102d7b4101911004cff76d5110004fe76d5110004fd76d511004cfc76d51100067f65d511004e7c65d5110006bf64d511001ebc64d51100673e54d5110216dc63d511020eec62d5110004ff7655110004fe7655110004fd7655110004fc76551100067f655511004e7c6555110006bf645511001ebc6455110206dc63551101feec6255110005f77155110005f4715511005dde76d8d1005ede76d8d10014de76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d102cfd771d8d1005fd471d8d102cfd610d8d102cfd410d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006de52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d102cedf71d8d1005ede71d8d1005edd71d8d1005edc71d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d
  | 6 => 0xd5359510004ff7259510006ef7259510004ef725951000cfe725951000cfc7259510006ec725951000cec7259510004ff7159510006f77159510004ff7059510006fb7059510004fe761951004e7e65195100067d6519510006dc63195100057e76195100067e76195100047e76195100067e64195100067c64195100057f73195100057d73195100067f63195100067e63195100067d63195100067c63195100075c63195100065c63195100067e62195100067c621951029777711951000776311951000775311951029776101951029774101951004e7f741951004e7e741951004e7d741951004e7c741951004e7f731951004c7f731951004e7e731951004e7d73195100047d731951004e7c73195100067f43195100067e43195100067d43195100067c431951004e7f721951004e7e721951004e7d721951004e7c72195100067f42195100067e42195100067c42195100067f32195100067e32195100067d32195100067c321951004e7f711951004e7d71195100067f41195100067c41195100067f31195100067e31195100067d31195100067c31195100067f21195100067c211951004e7f701951004e7e701951004e7d701951004e7c70195100067f40195102967e40195102967c40195100067f30195102967e30195100067d30195102967c30195100067f20195102967e20195102967c20195102967e10195100067d10195102967c101951001cfe76d91100067f65d91100067c65d9110066be64d9110006dc63d911004cfe75d9110004fd75d9110066be54d9110066bc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d91100067f53d91100067d53d9110066bf43d9110006be43d9110006bd43d9110066bc43d911000cfe72d9110004fd72d911000cfc72d9110066bf42d9110006be42d9110066bc42d911001cfe71d9110024fd71d911001cfc71d9110066bf41d9110024fe70d9110064fd70d9110024fc70d9110066bf40d9110065be76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d91100073f53d91100073d53d9110006be62d9110006bc62d911027fb771d9110007b631d9110007b531d911027fb610d911027fb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006be52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d911027ebf71d9110
  | 7 => 0xa10005f77150a10005f47150a1004e7e65d46100067d65d4610025fa70d4610005f970d46102de7f659461004e7c659461000777519461004cff765461004e7e65546100067d6554610005bf745461007dbc7454610005fb7054610025f870546102967f651461004e7c6514610064fd769061027ebf649061001ebc649061001cff7650610024fc76506100057f75506100057c755061001ebe6450610006bd6450610005fb7050610025f87050610054fd7688610256ef628861000eec628861000cff7648610024fc764861000eee6248610006ed6248610005fb7048610025f87048610025f976c4210006f976c42102e77b53c42102e77953c4210027f271c421004cfe76d9510006dc63d951001cfe74d9510004fd74d951001cfc74d95100067e54d95100067c54d9510004ff73d9510014fe73d9510004fd73d9510014fc73d95100067f53d95100067e53d95100067d53d95100067c53d951000cfe72d9510004fd72d951000cfc72d95100067e52d95100067c52d951004cfe71d9510006f571d951004cfc71d9510024fe70d9510024fc70d951004c7e76d95100067e64d95100067c64d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100067e62d95100067c62d95100077571d95100077631d95100077531d95102df7610d95102df7410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95102de7f71d95100067d71d95100067571d95100067f41d95100067c41d95100067f31d95100067e31d95100067d31d95100067c31d95100067f21d95100067c21d95100067f70d95102de7e70d95100067d70d95102de7c70d95100067f40d95102de7e40d95102de7c40d95100067f30d95102de7e30d95100067d30d95102de7c30d95100067f20d95102de7e20d95102de7c20d95102de7e10d95102de7c10d95100067f6599510065be7499510005bd749951005dde7399510005dd7399510006dc6399510055ee7299510005ed7299510005bf7459510065bc7459510005df735951005ddc7359510006dc6359510005ef7259510055ec72595100067f7559510004ff7459510006bf7459510004bf745951001cfe745951001cfc7459510006bc745951001cbc7459510004ff7359510006df7359510004df7359510014fe7359510004fd7359510014fc7359510006dc7359510014dc73595100067f53595100067
  | 8 => 0x7b77450710007b7645071001ef6645071001ef4645071008fb46450710315f77350710315f5735071030f77535071030f755350710005f77250710025f67050710025f4705071008fb74050710024fd768871000eee6288710006ed6288710025fa7088710005f97088710025f5768871000ef57688710024f5768871022df6758871022df47588710005f77488710005f57488710305f77388710305f573887102ff7753887102ff75538871000ef66288710087e66288710007e5628871000ef46288710087e632887102ffe53288710025f67088710007f27088710007f17088710025f47088710257e62088710257e4208871002cff7648710005f7764871002ef7764871022df6754871022df47548710005f77448710005f574487102f5f773487102f5f573487102ef7753487102ef755348710007e7724871000ef6624871000ef46248710025f67048710025f4704871004e7e65d43100067d65d4310005f671d4310005f571d43100277a50d431004cff765431004e7e65543100067d6554310005f77154310005f4715431001cff765031001cfc765031001ebe6450310006bd6450310005f77150310005f47150310007b5415031000cff764831000cfc76483100057f75483100057c754831000eee6248310006ed6248310005f77148310005f471483100267f7559610004ff745961001cfe745961001cfc74596100067e54596100067c5459610004ff7359610014fe7359610004fd7359610014fc73596100067f53596100067d5359610004ff725961000cfe725961000cfc7259610024fc70596100267e50596100267c5059610004ff755921004cfc7559210026bf745921007ebc5459210004ff7359210014fe7359210004fd7359210014fc73592100067f53592100067d535921007ebf4359210006bd4359210004ff725921000cfe725921000cfc725921007ebf425921007ebf4159210024fc7059210026be4059210026bc4059210026f71059210026f5105921004cff76d5210024fe76d5210004fd76d5210024fc76d521001ebe64d5210006bd64d521007f3e54d5210004ff7655210024fe7655210004fd7655210024fc7655210004ff7558a1004cfc7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a10014fe7358a10004fd7358a10014fc7358a100067f5358a100067d5358a10026ef7258a1006eee3258a10006ed3258a1006eef2158a10024fc7058a10026ee2058a10026ec2058a10026f71058a10026f51058a1004cff76d4a10024fe76d4a10004fd76d4a10024fc76d4a1004e7e65d4a100067d65d4a10004ff7654a10024fe7654a10004fd7654a10024fc7654a1004e7e6554a100067d6554a10004ff7650a10024fe7650a10004fd7650a10024fc7650a1001ebe6450a10006bd645
  | 9 => 0xd76d531004cfc76d531004e7e65d53100067d65d5310006bf64d531001ebc64d531008f3e54d5310004ff7655310004fe7655310004fd7655310004fc765531004e7e65553100067d6555310005f77155310005f471553100057e75d8b100057d75d8b10086ee62d8b1004cfe75d8b100067e75d8b1004c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfe74d8b10004fd74d8b1001cfc74d8b10004ff73d8b10014fe73d8b10004fd73d8b10014fc73d8b100067f53d8b100067d53d8b10084fd72d8b10086ee32d8b10006ed32d8b10006f671d8b10006f970d8b10256ee20d8b10256ec20d8b1000cff7658b10086ec6258b10004ff7558b1004cfc7558b10004ff7458b1001cfe7458b1001cfc7458b10004ff7358b10014fe7358b10004fd7358b10014fc7358b100067f5358b100067d5358b10006ef7258b10024fc7158b10086ec2158b10086ef2058b1004cff76d4b10004fe76d4b10004fd76d4b1004cfc76d4b100067f65d4b1004e7c65d4b10004ff7654b10004fe7654b10004fd7654b10004fc7654b100067f6554b1004e7c6554b10005f77154b10005f47154b10004ff7650b10004fe7650b10004fd7650b10004fc7650b10006bf6450b1001ebc6450b10005f576d471022ef576d471022ef765d471022ef565d4710005f574d471022df773d471034df573d471022f7753d47103477553d4710005f572d4710025f670d4710025f470d4710024fd769471004e7e65947100067d6594710025fa7094710005f97094710005bf745471008dbc7454710024fd761471004e7e65147100067d6514710007755114710025fa7014710005f97014710025f5761471022ef57614710024f5761471022f76751471022ef7651471022f76651471022ef56514710007756514710005f5741471033f76541471022f74541471022df77314710335f5731471022f77531471032f755314710005f5721471022f775214710007755214710025f6701471022ff2701471022ff17014710025f47014710297765014710297745014710024fd769071001ebe6490710006bd649071008fb74190710025fa7090710005f97090710025f5769071001ef57690710024f5769071022df6759071022df4759071001ef6649071008fb66490710007b5649071001ef46490710007b7549071008fb45490710325f77390710325f5739071031f77539071031f75539071008fb7439071031fb54390710005f5729071008fb74290710007b54290710025f67090710007f27090710007f17090710025f4709071027fb6409071027fb4409071003cff76507100057f75507100057c7550710006bf645071001ebc645071008fb44150710005f7765071003ef7765071000777755071022df6755071022df47550710007747550710005747550710
  | 10 => 0x852001cfc7418520004ff7318520014fe7318520004fd7318520014fc73185200067f53185200067d5318520024fd721852002eee3218520006ed3218520006f74118520006f44118520006f73118520006f4311852002ef6211852002ef52118520024fe7018520024fc70185202c6ee20185202c6ec2018520004fe76d4520004fd76d452004cfc76d45200067f65d452004e7c65d4520004fe7694520004fd7694520004fc76945200067f659452004e7c6594520004ff7654520004fe7654520004fc76545200067f655452004e7c6554520005bf745452009dbc7454520004fe7614520004fd761452004cfc76145200067f651452004e7c651452000dee7214520005ed7214520025fa7014520005f97014520004fe7690520004fd7690520004fc76905200067f65905200067c6590520006bf649052001ebc6490520004ff7650520004fe7650520004fc76505200057f75505200057c75505200067f65505200067c655052000cfe76d412000cfc76d41200067f65d412004e7c65d412000dee72d4120005ed72d41200277a50d412004cff765412000cfe76541200ecfd765412000cfc76541200067f655412004e7c6554120005ef725412000dec7254120027e8205412001cff765012000cfe76501200b4fd765012000cfc76501200067f65501200067c6550120006bf645012001ebc6450120005ef725012000dec725012001cfe74d9710004fd74d971001cfc74d9710004ff73d9710014fe73d9710004fd73d9710014fc73d97100067f53d97100067d53d971000cfe72d9710004fd72d971000cfc72d9710006f671d9710006f970d97102de7e50d97102de7c50d9710004fd76997100067f659971004cff7659710005bf745971008dbc74597100067f7559710004ff7459710006bf7459710004bf745971001cfe745971001cfc7459710006bc745971001cbc7459710004ff7359710014fe7359710004fd7359710014fc73597100067f53597100067d5359710004ff725971000cfe725971000cfc72597100067e52597100067c5259710006f4715971004e7e65197100067d651971008ebe64d931004cfe75d9310004fd75d931008cfd74d931008ebc54d9310004ff73d9310014fe73d9310004fd73d9310014fc73d93100067f53d93100067d53d931008ebf43d9310006bd43d931000cfe72d9310004fd72d931000cfc72d931008ebf42d9310006f671d931008ebf41d9310006f970d931027ebe40d931027ebc40d931001cff765931008ebc6459310004ff755931004cfc7559310006bf7459310004ff7359310014fe7359310004fd7359310014fc73593100067f53593100067d5359310004ff725931000cfe725931000cfc7259310024fc715931008ebc415931008ebf405931004cff76d5310004fe76d5310004f
  | 11 => 0x67f43195200067e43195200067d43195200067c431952004e7f721952004e7e721952004e7d721952004e7c72195200d67f42195200d67e42195200d67d42195200d67c42195200d67f32195200d67e32195200d67d32195200d67c321952004e7f711952004e7e711952004e7d711952004e7c71195200067f41195200067c41195200067f31195200067e31195200067d31195200067c31195200d67f21195200d67e21195200d67d21195200d67c211952004e7f701952004e7e701952004e7d701952004e7c70195200067f401952035e7e401952035e7c40195200067f301952035e7e30195200067d301952035e7c30195200d67f201952035e7e20195200d67d201952035e7c201952035e7e101952035e7c101952001cfe76d91200067f65d91200067c65d912009ebe64d912004cfe75d9120004fd75d9120004ff73d9120014fe73d9120004fd73d9120014fc73d91200067f53d91200067d53d9120006be43d912009ebc43d9120024ff72d912000cfe72d9120024fd72d912000cfc72d91200c6bf42d91200c6bd42d91200c6ee32d9120006ed32d9120004fe71d9120004fd71d912009ebc41d912000cfd70d912009ebf40d91200057f75591200057c75591200067f65591200067c655912009ebc6459120005df7359120095dc7359120005f77159120005f47159120355fb7059120004ff75591200067f75591200047f755912004cfc75591200067c755912004c7c75591200c4ff7459120006bf7459120004ff7359120006df7359120004df7359120014fe7359120004fd7359120014fc7359120006dc7359120014dc73591200067f53591200067d535912009ebf4359120006bd43591200b4ff7259120006ef72591200b6ee3259120006ed3259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f47159120354ff7059120006fb705912004cff76d5120004fe76d5120004fd76d512004cfc76d51200067f65d512004e7c65d512009f3e54d5120004ff7655120004fe7655120004fd7655120004fc76551200067f655512004e7c65551200067f65d85200067c65d852004cfe75d8520004fd75d852001cfe74d8520004fd74d852001cfc74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d8520024fd72d8520006f741d8520006f441d8520006f731d8520006f431d852006ef621d852006ef521d85200057e75985200057d75985200067f65985200067c6598520006f76198520055f970985200057f75585200057c75585200067f65585200067c6558520005bf745852009dbc7458520005df7358520095dc7358520085fb70585200067f65185200067c6518520006f5611852004cfe7518520004fd751852001cfe7418520004fd741
  | 12 => 0xf649062001ebc6490620006f66190620006f56190620004ff7650620004fd7650620024fc76506200057f75506200057c755062001ebe6450620006bd6450620005ef725062000dec7250620006f66150620006f56150620256ef638862036eed638862036f6f538862036f6d538862000dee718862000fe67188620257e66188620006ed6188620257e56188620257ea7088620255ed7088620007e9708862000eee608862000fea608862004cfe76d952001cfe74d9520004fd74d952001cfc74d95200067e54d95200067c54d9520004ff73d9520014fe73d9520004fd73d9520014fc73d95200067f53d95200067e53d95200067d53d95200067c53d9520024ff72d952000cfe72d9520024fd72d952000cfc72d95201067f52d95201067d52d9520004fe71d9520004fd71d952004c7e76d95200067e64d95200067c64d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95201076e32d95200076d32d95201077b20d95203676e20d95203676c20d95201077820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95203667f72d95201067e72d95201067d72d95201067c72d95201067f42d95201067e42d95201067d42d95201067c42d95201067f32d95201067e32d95201067d32d95201067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95201067f21d95201067e21d95201067d21d95201067c21d95201067f70d95203667e70d95201067d70d95203667c70d95200067f40d95203667e40d95203667c40d95200067f30d95203667e30d95200067d30d95203667c30d95201067f20d95203667e20d95203667c20d95203667e10d95203667c10d95200067f65995200edf9709952011dfb70595200067f7559520004ff745952001cfe745952001cfc7459520004ff7359520014fe7359520004fd7359520014fc73595200067f53595200067d53595200ecff7259520006ef7259520004ff7159520004fc715952011cff7059520006fb7059520104fe761952004e7e65195200067d65195201057e76195200067e76195201047e76195200067e64195200067c64195200057f73195200057d73195200067f63195200067e63195200067d63195200067c63195200d76e32195200076d32195200d77b201952035f6e201952035f6c20195200d778201952004e7f741952004e7e741952004e7d741952004e7c741952004e7f731952004c7f731952004e7e731952004e7d73195200047d731952004e7c7319520
  | 13 => 0x540007b46150540007bb7050540025be7050540025bc7050540007b8705054001ebf605054001fbb6050540004fe7688540004fd7688540004fc768854001dbe7488540005bd7488540006ef628854000eec6288540004ff7648540004fe7648540004fc764854001dbe7448540005bd744854001cfe76d414001cfc76d41400067f65d414004e7c65d414001dbe74d4140005bd74d41400277a50d414004cff765414001cfe76541400fcfd765414001cfc76541400067f655414004e7c6554140005bf745414001dbc74541400267f7559620004ff745962001cfe745962001cfc7459620004ff7359620014fe7359620004fd7359620014fc73596200067f53596200067d53596200ee7f52596200ee7d5259620004ff7159620004fc7159620024fe7059620024fc70596200267e50596200267c5059620004ff755922004cfc7559220026bf74592200aebc5459220004ff7359220014fe7359220004fd7359220014fc73592200067f53592200067d53592200aebf4359220006bd43592200b6bf42592200b6bd4259220004ff7159220004fc71592200aebf4159220024fe7059220024fc7059220026be4059220026bc405922004cff76d5220024fe76d5220004fd76d5220024fc76d522037e7f65d522004e7c65d522001ebe64d5220006bd64d52200af3e54d5220004ff7655220024fe7655220004fd7655220024fc76552203767f655522004e7c655522004cfe7598620004fd759862001cfe7498620004fd749862001cfc7498620004ff7398620014fe7398620004fd7398620014fc73986200067f53986200067d5398620026f67198620006f63198620006f53198620086f62198620086f52198620024fe7098620026f61098620026f41098620004ff75586200067f75586200047f755862004cfc75586200067c755862004c7c7558620004ff7458620006bf7458620004bf745862001cfe745862001cfc7458620006bc745862001cbc7458620004ff7358620006df7358620004df7358620014fe7358620004fd7358620014fc7358620006dc7358620014dc73586200067f53586200067d5358620026f77158620006f63158620006f53158620056f62158620056f52158620056ec2158620024fc7058620026f61058620026f4105862004cff76d4620024fe76d4620004fd76d462000dee72d4620005ed72d4620006f661d4620006f561d4620004ff7694620024fe7694620004fd76946202de7f659462004e7c6594620004ff7654620004fd7654620024fc7654620005bf74546200adbc7454620005ef725462000dec725462004cff7614620024fe7614620004fd76146202967f651462004e7c6514620006f66114620006f56114620025fa7014620005f97014620004ff7690620024fe7690620004fd769062027eb
  | 14 => 0x25bc70d514001ebf60d514001fbb60d514037f3e50d514037f3c50d514000cfe76d89400b6ee62d894004cfe75d8940004fd75d8940024fd74d894000cfc74d8940004ff73d8940014fe73d8940004fd73d8940014fc73d89400067f53d89400067d53d89400aebf43d8940006bd43d89400b6ee42d89400aeed42d8940004fe71d8940004fd71d89400b6ec21d894001cfd70d89400b6ef20d89400057f75589400057c7558940005df73589400bddc73589400b6ec6258940005f77158940005f471589403adfb7058940004fe76d4940004fd76d494004cfc76d494004e7e65d49400067d65d494001dbc74d49403973f54d4940004ff7654940004fe7654940004fc765494004e7e65549400067d6554940005bf745494001dbc74549400073f5454940025bc765094000ebc7650940024bc7650940395be7550940395bc7550940006bf6550940006bd65509403a5bf73509403a5bd735094039ebf635094039ebd635094039f3f535094039f3d535094001dbf725094001faf7250940007af625094000ebe625094000ebc62509400b7ac625094000eac62509400b7ae325094039fad3250940005bf7150940007bb7050940025be7050940025bc7050940007b8705094001ebf605094001fbb605094004cfe75d8540004fd75d8540024fd74d8540004ff73d8540014fe73d8540004fd73d8540014fc73d85400067f53d85400067d53d854000cfe72d8540004fd72d854000cfc72d854007ef641d854007ef541d8540006f721d8540006f421d8540006f76198540065f970985400057f75585400057c7558540005df73585400bddc7358540005ef72585400b5ec725854008dfb7058540006f5611854004cfe7518540004fd7518540024fd7418540006bf541854003ebc5418540004ff7318540014fe7318540004fd7318540014fc73185400067f53185400067d531854003ebf4318540006bd431854000cfe7218540004fd721854000cfc721854003ebf4218540006bd421854003ebf411854003ef6411854003ef54118540006f72118540006f421185402d6be40185402d6bc4018540004fe76d4540004fd76d454004cfc76d454001dbc74d4540004fe7694540004fd7694540004fc76945400067f659454004e7c659454001dbe7494540005bd74945401b73c5494540025fa7094540005f97094540004ff7654540004fe7654540004fc7654540005bf745454001dbc7454540004fe7614540004fd761454004cfc76145400067f651454004e7c651454001dbe7414540005bd74145401873c5414540024bc76505400073f7550540395be7550540395bc75505400073c75505400053c755054038dbf735054038dbd73505403873f53505403873d5350540005bf725054001dbf715054001fb77150540007b76150540006bc615
  | 15 => 0xd7654a40024fc7654a4004e7e6554a400067d6554a4004cfe7598640004fd7598640004ff7398640014fe7398640004fd7398640014fc73986400067f53986400067d539864000cfe7298640004fd729864000cfc7298640026f6719864008ef6419864008ef54198640006f63198640006f53198640024fe7098640026f61098640026f41098640004ff755864004cfc7558640004ff7358640014fe7358640004fd7358640014fc73586400067f53586400067d5358640004ff725864000cfe725864000cfc7258640026f77158640066f64158640066f54158640066bc4158640006f63158640006f53158640024fc7058640026bf4058640026bd4058640026f61058640026f4105864004cff76d4640024fe76d4640004fd76d464001dbe74d4640005bd74d4640006f661d4640006f561d4640004ff7694640024fe7694640004fd769464004e7e65946400067d6594640025fa7094640005f97094640004ff7654640004fd7654640024fc7654640005bf745464001dbc745464004cff7614640024fe7614640004fd761464004e7e65146400067d6514640006f66114640006f561146403cebe659064027ebc659064027ebf63906403c6bd63906403c73f53906403c73d5390640006bd629064001dbe719064001fb6719064027fb66190640006bd619064027fb56190640006b5619064027fba709064027dbd7090640007b9709064001ebe609064001fba6090640004ff7688640024fe7688640004fd7688640006f66188640006f56188640004ff7648640004fd7648640024fc7648640005bf744864001dbc7448640006f66148640006f5614864004cfe76d9540024ff74d954001cfe74d9540024fd74d9540006bd74d954001cfc74d95401167f54d95401167d54d9540116bc54d9540004ff73d9540014fe73d9540004fd73d9540014fc73d95400067f53d95400067d53d954000cfe72d9540004fd72d954000cfc72d95400067e52d95400067c52d9540116bf42d9540004fe71d9540004fd71d95400067f65995400bdde7399540005dd73995400fdf9709954012dfb70595400067f75595400fcff7459540006bf74595400febc5459540004ff7359540014fe7359540004fd7359540014fc73595400067f53595400067d5359540004ff725954000cfe725954000cfc72595400febf4259540004ff7159540004fc715954012cff7059540006fb70595403767e50595403767c5059540114fe761954004e7e65195400067d6519540025be76d5140396be76d5140024be76d514001dbe75d514001f3e75d5140396bf65d51400073f65d51400063f65d5140396bd65d51403973c65d5140395bf73d51403bdbd73d51403973f53d51403b73d53d5140005bd72d5140005bd71d5140025be70d5140397ba70d5140397b970d5140
  | 16 => 0x8850024ff7258850026ef725885004eef52588500d67e525885004e7c525885004eec52588500d6ee42588500d6ee3258850006ed3258850004ff7158850004fc715885004e7c51588500d6ef2158850024fc70588500267f50588500267d5058850026ee2058850026ec2058850004ff7650850004fd7650850024fc76508500057f755085004d7c755085001ebe6450850006bd64508500073d545085000eee6250850006ed625085001cfe7498450004fd749845001cfc7498450004ff7398450014fe7398450004fd7398450014fc739845004e7f53984500067d539845000cfe7298450004fd729845000cfc7298450026f6719845004ef7519845004ef45198450006f63198450006f53198450026f61098450026f41098450004ff7458450006bf7458450004bf745845001cfe745845001cfc7458450006bc745845001cbc7458450004ff7358450014fe7358450004fd7358450014fc735845004e7f53584500067d5358450004ff725845000cfe725845000cfc7258450026f7715845004ef7515845004e7c515845004ef4515845004e745158450006f63158450006f53158450026f61058450026f4105845004d7d76944500067d76944500057d74944501b67e649445004e7c64944503dd7f73944503dd7d739445004e7f63944503d67d63944500d57e72944500d57c72944500067d629445004d7e719445004f7671944500067d61944502dd7d70944502de7e609445004f7a6094450004ff7690450024fe7690450004fd76904500057f759045004d7c759045001ebc64904503cf3f5490450006f66190450006f56190450004ff7650450004fd7650450024fc76504500057f755045004d7c755045001ebe6450450006bd6450450006f66150450006f56150450004ff7688450024fe7688450004fd768845004d7e75884500057d7588450006f66188450006f56188450004ff7648450004fd7648450024fc76484500057f754845004d7c754845000eee6248450006ed6248450006f66148450006f561484500267f75596400fe7f54596400fe7d5459640004ff7359640014fe7359640004fd7359640014fc73596400067f53596400067d5359640004ff725964000cfe725964000cfc7259640004ff7159640004fc7159640024fe7059640024fc70596400267e50596400267c5059640004ff7558a4004cfc7558a40004ff7358a40014fe7358a40004fd7358a40014fc7358a400067f5358a400067d5358a40026ef7258a400c6ee4258a4009eed4258a400c6ee3258a40006ed3258a40004ff7158a40004fc7158a4009ebc4158a40024fe7058a40024fc7058a40026bf4058a40026bd4058a40026ee2058a40026ec2058a4004cff76d4a40024fe76d4a40004fd76d4a4004e7e65d4a400067d65d4a40004ff7654a40004f
  | 17 => 0x67d53d89500eeee52d8950004fe71d8950004fd71d89500eeec21d895004cfd70d89500eeef20d89500eeec62589500057e76d495004e7e76d49501047e76d49500067f64d495004d7f73d495040d7d73d49504067f63d49504067d63d49500ed7d72d495000e7e62d495000e7c62d49500257e70d49500257c70d495004e7f60d495004f7b60d4950024fc7654950006ef625495000eec6254950005fb7054950025f870549500257c765495000e7c76549500247c76549500067f64549503fd7f73549503fd7d73549503f67f63549503f67d635495004d7f725495004f6f72549500076f625495000e7e625495000e7c62549500ef6c62549500077b70549500257e70549500257c705495000778705495004e7f605495004f7b6054950004ff7650950004fe7650950004fc765095001ebe645095001cfe74d8550004fd74d855001cfc74d8550004ff73d8550014fe73d8550004fd73d8550014fc73d85500067f53d85500067d53d855000cfe72d8550004fd72d855000cfc72d8550006f76198550005bf74585500fdbc7458550005df73585500f5dc7358550005ef72585500edec7258550006f5611855001cfe7418550004fd741855001cfc7418550004ff7318550014fe7318550004fd7318550014fc73185500067f53185500067d531855000cfe7218550004fd721855000cfc72185500067f52185500067d52185502967e50185502967c5018550024fe7694550006f76194550006f46194550025fa7094550005f97094550024fc7654550005bf74545500fdbc7454550006f76154550006f4615455004f745154550005fb7054550025f87054550004fe7690550004fd7690550004fc7690550006bf649055001ebc6490550004ff7650550004fe7650550004fc76505500057f755055004d7c7550550004fe7688550004fd7688550004fc7688550006ef628855000eec6288550004ff7648550004fe7648550004fc764855001cfd7559050024ff7459050026bf745905004ebf545905004ebc5459050004ff7359050014fe7359050004fd7359050014fc735905004e7f53590500067d53590500e6bf4359050006bd4359050004ff725905000cfe725905000cfc72590500e6bf4259050004ff7159050004fc71590500e6bf4159050024fc7059050026be4059050026bc405905004d7f765505012e7f765505004d7f745505004f3f745505001e7e645505001e7c64550503ed7f73550503ed7d735505004e7f63550503e67d63550500d57e72550500d57c72550500e73f42550500057c71550503757f70550503767e605505004f7a605505000cfd7558850004ff745885001cfe745885001cfc745885004e7f54588500067d5458850004ff7358850014fe7358850004fd7358850014fc735885004e7f53588500067d535
  | 18 => 0x77258650006f67258650006f57258650006f4725865024ef75258650006f65258650006f5525865024ef45258650006f74258650006f64258650006f54258650006f44258650006f73258650006f63258650006f53258650006f43258650026f77058650026f67058650026f47058650026f75058650026f65058650026f55058650026f45058650026f74058650026f64058650026f54058650026f44058650026f73058650026f63058650026f53058650026f43058650026f72058650026f62058650026f52058650026f420586501b6be6494650006bd6494650006f66194650006f5619465004f775194650025fa7094650005f9709465004f7b50946500057d74946501b67e64946502df3e64946501b63e64946502df3d64946502de7c649465042d7f739465042d7d73946502de7f63946504267d63946501057e72946501057c72946500067d629465004d7e71946502df7661946500067d61946502df7561946502df7a70946502dd7d709465000779709465004e7e6094650005bf7454650115bc74546501a6be6454650006bd6454650006f66154650006f56154650005fb7054650025f870546502957d761465004e7d76146500057d74146501867e64146502973e64146501863e64146502973d64146502967c641465004d7f731465041d7d73146502967f63146504167d63146501057e721465004d7c72146500067d621465004f7671146502977661146500067d611465029775611465000675611465004d7f70146502957d701465004f7a6014650004ff7690650024fe7690650004fd76906500057f759065004d7c759065001ebe6490650006bd64906500073f5490650006f66190650006f56190650004ff7650650004fd7650650024fc76506500057f755065004d7c755065001ebe6450650006bd6450650006f66150650006f56150650004ff7688650024fe7688650004fd768865004d7e75886500057d758865014ebe6488650006bd6488650006f66188650006f56188650004ff7648650004fd7648650024fc76486500057f754865004d7c754865013ebe6448650006bd6448650006f66148650006f5614865001cfe76d91500febe64d9150024fd75d915001cfc75d91500febe54d9150004ff73d9150014fe73d9150004fd73d9150014fc73d91500067f53d91500067d53d915000cfe72d9150004fd72d915000cfc72d9150004fe71d9150004fd71d91500febc41d915004cfd70d915037e7e50d915037e7c50d91500febf40d91500febc6459150024fc7655150006bf645515001ebc6455150005fb7055150025f8705515000cfe76d89500eeee62d8950024fd75d895000cfc75d895001cfe74d8950004fd74d895001cfc74d8950004ff73d8950014fe73d8950004fd73d8950014fc73d89500067f53d8950
  | 19 => 0x8a5001cfc7458a500067f5458a500067d5458a50004ff7358a50014fe7358a50004fd7358a50014fc7358a500067f5358a500067d5358a50026ef7258a501067e5258a50106ee5258a501067c5258a50106ee3258a50006ed3258a50004ff7158a50004fc7158a50024fc7058a500267f5058a500267d5058a50026ee2058a50026ec2058a5000cff7654a503657f7554a501e6be6454a50006bd6454a5000eee6254a50006ed6254a50005fb7054a50025f87054a5004f7b5054a50004ff7650a50004fd7650a50024fc7650a500057f7550a5004d7c7550a5001ebe6450a50006bd6450a500073d5450a5001cfe7498650004fd749865001cfc7498650004ff7398650014fe7398650004fd7398650014fc73986500067f53986500067d539865000cfe7298650004fd729865000cfc7298650026f67198650006f74198650006f44198650006f73198650006f63198650006f53198650006f43198650006f72198650006f42198650024fe7098650026f61098650026f41098650006f7759865022ef67598650006f77498650006f67498650006f57498650006f4749865022ef75498650006f65498650006f5549865022ef45498650006f77398650006f67398650006f57398650006f4739865022ef75398650006775398650006f65398650006f5539865000675539865022ef45398650006f74398650006f64398650006f54398650006f44398650006f77298650006f67298650006f57298650006f4729865022ef75298650006f65298650006f5529865022ef45298650006f74298650006f64298650006f54298650006f44298650006f73298650006f63298650006f53298650006f43298650026f67098650026f57098650026f47098650026f75098650026f65098650026f55098650026f45098650026f74098650026f64098650026f54098650026f44098650026f73098650026f63098650026f53098650026f43098650026f72098650026f62098650026f52098650026f42098650004ff745865001cfe745865001cfc7458650004ff7358650014fe7358650004fd7358650014fc73586500067f53586500067d5358650004ff725865000cfe725865000cfc7258650026f77158650006f74158650006f44158650006f73158650006f63158650006f53158650006f43158650006f72158650006f42158650024fc7058650026f61058650026f41058650006f5755865024ef47558650006f77458650006f67458650006f57458650006f4745865024ef75458650006f65458650006f5545865024ef45458650006f77358650006f67358650006f57358650006f4735865024ef75358650006775358650006f65358650006f5535865000675535865024ef45358650006f74358650006f64358650006f54358650006f44358650006f
  | 20 => 0x67d529875004ef6719875004ef7519875004ef451987502de7e509875004e7c5098750024fc7558750004ff745875001cfe745875001cfc7458750004ff7358750014fe7358750004fd7358750014fc735875004e7f53587500067d5358750004ff725875000cfe725875000cfc725875004ef7715875004ef7515875004ef45158750004ff769075004cfe7690750004fd769075001ebe6490750006bd6490750004ff7650750004fd765075004cfc76507500057f755075004d7c7550750004ff768875004cfe7688750004fd768875000eee6288750006ed6288750004ff7648750004fd764875004cfc7648750026bf7459250116be5459250004ff7359250014fe7359250004fd7359250014fc73592500067f53592500067d5359250116bf4359250006be4359250006bd4359250116bc4359250004ff725925000cfe725925000cfc7259250116bf4259250006be4259250116bc4259250004ff7159250004fc7159250116bf4159250116bc4159250024fc7059250026be4059250026bc4059250006bd7559250116bc7559250006bf7359250006be7359250006bd7359250006bc7359250396bf53592500063f5359250006be5359250006bd53592500063d5359250396bc5359250006bf7259250006be7259250006bd7259250006bc7259250396bf5259250006be5259250396bc5259250006bf3259250006be3259250006bd3259250006bc3259250006bf7159250006be7159250006bd7159250006bc7159250396bf5159250396bc5159250006bf3159250006be3159250006bd3159250006bc3159250006bf2159250006bc2159250026bf7059250026be7059250026bc7059250026bf5059250026be5059250026bd5059250026bc5059250026bf3059250026be3059250026bd3059250026bc3059250026bf2059250026be2059250026bd2059250026bc2059250026bf1059250026be1059250026bd1059250026bc105925037d7d76d525004e7d76d525001e7e64d525037f3e64d525001e3e64d525037f3d64d525001e7c64d525004d7f73d525044d7d73d525037e7f63d52504467d63d52501057e72d525004d7c72d52500057e71d525037f7661d525037f7561d52501173c41d525004d7f70d525037d7d70d525004f7a60d525037f3f40d525001cff765525001ebe6455250006bd6455250005fb7055250025f8705525004f7b50552503757f765525001e7f765525001c7f765525004d7f745525004f3f745525001e7e64552503773e64552503773d645525001e7c645525043d7f735525043d7d73552503767f63552504367d63552501057e72552501057c72552501173f42552500057c71552503777661552503777561552503757f70552500077b705525037778705525004e7e6055250004ff7458a5001cfe745
  | 21 => 0xc755912104c7c7559121164ff7459121006bf7459121004ff7359121014fe7359121004fd7359121014fc73591210067f53591210067d5359121154ff7259121006ef7259121474ff7159121006f7715912113ebc4159121004ff7059121024fc705912113ebf405912104cff76d5121004fe76d5121004fd76d512104cfc76d5121006bf64d512101ebc64d512113f3e54d5121004ff7655121004fe7655121004fd7655121004fc765512100cfe76d452100cfc76d45210067f65d452104e7c65d452100dee72d4521005ed72d4521174fe769452104e7e65945210067d65945210077751945211afe4219452104cff765452100cfe7654521194fd765452100cfc76545210067f655452104e7c6554521005bf745452113dbc7454521005ef725452100dec7254521197e421545211acfe761452104e7e65145210067d651452146cfe769052101ebe6490521006bd649052101cff765052100cfe7650521154fd765052100cfc76505210057f75505210057c7550521006bf645052101ebc6450521005ef725052100dec7250521466ef6388521466ed63885214676f53885214676d538852100dee718852100fe6718852100eef618852100fe7618852104cfe75d8121004fd75d812101cfe74d8121004fd74d812101cfc74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d81210067f53d81210067d53d8121086fa20d8121006fb60981210057f75581210057c7558121005bf745812113dbc7458121005df7358121135dc735812113dbe7418121005bd7418121256ef6218121026fa6018121006f96018121024fc755935004ebf745935004ebf545935004ebc5459350004ff7359350014fe7359350004fd7359350014fc735935004e7f53593500067d5359350006be435935012ebc4359350004ff725935000cfe725935000cfc725935004e7f525935012ebf4259350004ff7159350004fc715935012ebc41593503767e505935004e7c505935012ebf4059350024fc7558b50004ff7458b5001cfe7458b5001cfc7458b50004ff7358b50014fe7358b50004fd7358b50014fc7358b5004e7f5358b500067d5358b5004eef7258b5004eef5258b5004eec5258b50004ff7158b50004fc7158b5011eec2158b5011eef2058b5004d7f7654b500d67f7654b500d47f7654b500067d6454b5045d7f7354b5045d7d7354b5004e7f6354b504567d6354b5004f6f7254b5000e7e6254b5000e7c6254b500257e7054b500257c7054b50004ff7650b50004fd7650b5004cfc7650b5001ebe6450b50006bd6450b50024fe759875001cfe7498750004fd749875001cfc7498750004ff7398750014fe7398750004fd7398750014fc739875004e7f53987500067d539875000cfe7298750004fd729875000cfc729875004e7f5298750
  | 22 => 0x92210067f53d92210067d53d922114ebf43d9221006bd43d9221006ed72d9221166ee32d9221006ed32d922146cfe71d9221006f671d9221024fe70d9221004fd70d922101cff765922114ebc6459221004ff755922104cfc7559221006bf7459221004ff7359221014fe7359221004fd7359221014fc73592210067f53592210067d5359221006be435922114ebc4359221156bf4259221156bd4259221156ee3259221006ed325922100cfc715922114ebc4159221004ff7059221024fc705922114ebf405922104cff76d5221004fe76d5221004fd76d522104cfc76d522114f3e54d5221004ff7655221004fe7655221004fd7655221004fc7655221194fd76d462100cff769462100cfd769462104e7e65946210067d659462100dee7294621005ed72946210077751946211afe721946211bcff7654621005bf745462114dbc7454621197e7215462100cff761462100cfd761462104cfc761462104e7e65146210067d651462100dee7214621005ed721462100cff769062101cfe769062100cfd769062101ebe6490621006bd649062100dee7290621005ed7290621474ff76506210057f75506210057c75506210057e75d82210057d75d8221006fb6098221004ff755822104cfc7558221004ff745822101cfe745822101cfc7458221004ff7358221014fe7358221004fd7358221014fc73582210067f53582210067d5358221056ee3258221006ed3258221056fa2058221256ec205822114dbe7418221005bd7418221026fa6018221006f9601822104cfe76d952101cfe74d9521004fd74d952101cfc74d95210067e54d95210067c54d9521004ff73d9521014fe73d9521004fd73d9521014fc73d95210067f53d95210067d53d95211acff72d95211acfd72d95211ae7f52d95211ae7d52d9521024fe70d9521004fd70d95210067f6599521195f57199521005bf745952113dbc74595211bdf771595210067f7559521004ff7459521006bf7459521004bf745952101cfe745952101cfc7459521006bc745952101cbc7459521004ff7359521014fe7359521004fd7359521014fc73595210067f53595210067d5359521194ff7259521006ef72595211bcff7159521006f77159521004ff7059521024fc70595211acfe761952104e7e65195210067d651952101cfe76d912113ebe64d912104cfe75d9121004fd75d912113ebc54d9121004ff73d9121014fe73d9121004fd73d9121014fc73d91210067f53d91210067d53d912113ebf43d9121006bd43d9121164ff72d9121164fd72d9121166bf42d9121166bd42d912100cfd71d912113ebf41d9121024fe70d9121004fd70d912113ebc40d91210057f75591210057c755912113ebc6459121475f77159121004ff75591210067f75591210047f755912104cfc75591210067
  | 23 => 0x67c31195410067f21195410067c211954104e7f701954104e7e701954104e7d701954104e7c70195411867f40195411863f40195411867e40195411867d40195411867c40195410067f30195410067e30195410067d30195410067c30195410067f20195410067c201954100cfe76d89410067f65d89410067c65d8941156ee62d894104cfe75d8941004fd75d8941004ff73d8941014fe73d8941004fd73d8941014fc73d89410067f53d89410067d53d8941156ee42d894114eed42d8941156ee32d8941006ed32d894101cfd71d894114ebc41d8941156ef21d8941024fe70d8941004fd70d894114ebf40d8941156ec20d89410057f75589410057c75589410067f65589410067c6558941156ec6258941485f77158941004fe76d4941004fd76d494104cfc76d49410067f65d494104e7c65d4941004ff7654941004fe7654941004fc76549410067f655494104e7c655494101cfe76d454101cfc76d45410067f65d454104e7c65d454101dbe74d4541005bd74d4541184fe76945411b67f659454104e7c65945410077751945411b7b4419454104cff765454101cfe76545411a4fd765454101cfc76545410067f655454104e7c6554541005bf745454101dbc74545411a7b441545411b4fe76145410067f651454104e7c65145410073f65905413cebe65905413cebc65905410073c65905410063c659054147ebf639054147ebd639054147f3f539054147f3d5390541006bf629054101dbe719054101fb6719054101ebf619054101fb76190541005bd70905410067f65d81410067c65d814104cfe75d8141004fd75d8141004ff73d8141014fe73d8141004fd73d8141014fc73d81410067f53d81410067d53d814100cfe72d8141004fd72d814100cfc72d814108efa40d81410057e75981410057d75981410067f65981410067c6598141006fb60981410057f75581410057c75581410067f65581410067c6558141005df735814115ddc7358141005ef7258141155ec72581410067f65181410067c651814127ebf6418141026fa6018141006f96018141175f671d962101cfe74d9621004fd74d962101cfc74d9621004ff73d9621014fe73d9621004fd73d9621014fc73d96210067f53d96210067d53d9621006ed72d9621174fe71d9621006f671d9621024fe70d9621004fd70d9621194fd76996210067f659962104cff76596210067f7559621004ff745962101cfe745962101cfc7459621004ff7359621014fe7359621004fd7359621014fc73596210067f53596210067d53596211967f52596211967d5259621004ff7059621024fc705962104e7e65196210067d65196211adf6711962114ebe64d922146df671d922104cfe75d9221004fd75d9221154fd74d9221004ff73d9221014fe73d9221004fd73d9221014fc73d
  | 24 => 0xd5358241066bf4358241006bd4358241004ff725824100cfe725824100cfc7258241066bf4258241006bd4258241066bf4158241066fa405824127ebc4058241026fa6018241006f9601824104cfe76d95411b4ff74d95411b4fd74d95411b67f54d95411b67d54d9541004ff73d9541014fe73d9541004fd73d9541014fc73d95410067f53d95410067e53d95410067d53d95410067c53d954100cfe72d9541004fd72d954100cfc72d95410067e52d95410067c52d9541024fe70d9541004fd70d954104c7e76d95410057f73d95410057d73d95410067f63d95410067e63d95410067d63d95410067c63d95410067e62d95410067c62d95411b77741d95411b73c41d95411b77441d95411b73f40d95411b67f74d95411b67e74d95411b67d74d95411b67c74d95410067f73d95410047f73d95410067e73d95410067d73d95410047d73d95410067c73d95411b67f43d95411b67e43d95411b67d43d95411b67c43d95410067f72d95410067e72d95410067d72d95410067c72d95411b67f42d95411b67e42d95411b67d42d95411b67c42d95410067f32d95410067e32d95410067d32d95410067c32d95411b67f71d95411b67d71d95411b67f41d95411b67e41d95411b67c41d95410067f31d95410067e31d95410067d31d95410067c31d95410067f21d95410067c21d95410067f70d95410067e70d95410067d70d95410067c70d95411b67f40d95411b67e40d95411b67d40d95411b67c40d95410067f30d95410067e30d95410067d30d95410067c30d95410067f20d95410067c20d95410067f65995411a5f571995411cdf771595410067f75595411a4ff7459541006bf7459541004bf7459541004ff7359541014fe7359541004fd7359541014fc73595410067f53595410067d5359541004ff725954100cfe725954100cfc72595411ccff7159541006f77159541004ff7059541024fc70595411b4fe761954104e7e65195410067d65195411b57e76195410067e76195411b47e76195410057f73195410057d73195410067f63195410067e63195410067d63195410067c63195410067e62195410067c62195411877741195411873c41195411877441195411873f401954104e7f741954104e7e741954104e7d741954104e7c741954104e7f731954104c7f731954104e7e731954104e7d73195410047d731954104e7c73195411867f43195411867e43195411867d43195411867c431954104e7f721954104e7e721954104e7d721954104e7c72195411867f42195411867e42195411867d42195411867c42195410067f32195410067e32195410067d32195410067c321954104e7f711954104e7d71195411867f41195411867e41195411867d41195411867c41195411863c41195410067f31195410067e31195410067d3119541
  | 25 => 0x805104efb505805104e7c505805104ef850580511b73c54d9641185f671d9641006bd74d96411b67e54d96411b67c54d96411b6bc54d9641004ff73d9641014fe73d9641004fd73d9641014fc73d96410067f53d96410067d53d964100cfe72d9641004fd72d964100cfc72d96411b6bf42d9641184fe71d9641006f671d9641024fe70d9641004fd70d96411a4fd76996410067f659964104cff76596410067f7559641006bf74596411a67f54596411a67d54596411a6bc5459641004ff7359641014fe7359641004fd7359641014fc73596410067f53596410067d5359641004ff725964100cfe725964100cfc72596411a6bf4259641004ff7059641024fc705964104e7e65196410067d65196411873c541964116dde7319641005dd73196411b5f671196413cebd76d524101dbe75d524101f3e75d52413cebf65d52413cf3e65d52413cebd65d52410073d65d52410063d65d52413cdbf73d52414adbd73d52413cf3f53d52414a73d53d5241005bd72d52413cfb671d5241005bd71d52413cfb571d5241005b571d524101ebe61d524101fb661d524127dbe70d5241166ee62d8a4149df671d8a4100cff7658a41166ec6258a41004ff7558a4104cfc7558a41004ff7358a41014fe7358a41004fd7358a41014fc7358a410067f5358a410067d5358a4113ebf4358a41006bd4358a41166ee4258a4113eed4258a4101cfc7158a41166ec2158a41004ff7058a41024fc7058a4104cff76d4a41004fe76d4a41004fd76d4a410067f65d4a4104e7c65d4a4101dbc74d4a413cf3f54d4a41004ff7654a41004fd7654a41004fc7654a410067f6554a4104e7c6554a41005bf7454a4101dbc7454a410073f5454a41165bf7650a4100ebf7650a4100cbf7650a413cdbe7550a413cdbc7550a41006bf6550a41006bd6550a41495bf7350a41495bd7350a4148ebf6350a4148ebd6350a4148f3f5350a4148f3d5350a4101dbf7250a4101faf7250a4100ebe6250a41167ae6250a41007ad6250a4100ebc6250a41167ae3250a4148fad3250a41005bf7150a41007b77150a41007b47150a4101ebe6150a4101fb66150a4127dbc7050a411a4fd76d464101dbc74d464101cff769464101cfd769464104e7e65946410067d659464101dbe7494641005bd74946411b73c54946410077751946411b7b741946411ccff7654641005bf745464101dbc74546411a7b7415464101cff761464101cfd761464104cfc761464104e7e65146410067d651464101dbe7414641005bd74146411873c5414641006fb60982410057f75582410057c7558241004ff75582410067f75582410047f755824104cfc75582410067c755824104c7c7558241006bf5458241066bc5458241004ff7358241014fe7358241004fd7358241014fc73582410067f53582410067
  | 26 => 0x196ef21d8951024fe70d8951004fd70d8951196ec20d8951005bf74589511a5bc7458951006bf6458951006bc6458951196ec625895100cfc7654951006bf64549511e6bc6454951006ef625495100eec6254951005f77154951005f47154951004ff7650951004fe7650951004fc7650951006bf645095101ebc6450951006bf64945511b6bc649455104df6719455104ef761945510073f64945511b67e64945511b67c64945510073c64945511b63c64945514b57f73945514b57d73945514de7f63945514de7d63945510067f629455104d7e719455104e7f619455104f776194551006bf64d8151006bc64d815101cfe74d8151004fd74d815101cfc74d8151004ff73d8151014fe73d8151004fd73d8151014fc73d81510067f53d81510067d53d815100cfe72d8151004fd72d815100cfc72d815122ef751d815122ef451d81511a5be7498151005bd7498151006bf6498151006bc6498151006fb6098151005bf74581511a5bc7458151006bf6458151006bc6458151005df735815119ddc7358151005ef7258151195ec72581512de7f6518151006bf6418151006bc6418151026fa6018151006f9601815104ebf745905104ebf54590511867e545905104e7c545905104ebc5459051004ff7359051014fe7359051004fd7359051014fc735905104e7f53590510067d5359051006be4359051186bc4359051004ff725905100cfe725905100cfc725905104e7f5259051186bf4259051186bc4159051004ff7059051024fc705905104e7c5059051186bf4059051004ff745885101cfe745885101cfc7458851004ff7358851014fe7358851004fd7358851014fc735885104e7f53588510067d535885104eef725885104eef525885104eec5258851176ec2158851004ff7058851024fc7058851176ef205885104d7f76548511be7f76548511857e74548511857c74548510067d64548514d57f73548514d57d735485104e7f63548514ce7d635485104d7f725485104f6f725485100e7e625485100e7c62548510057f71548511ae7e615485104f7661548512957c7054851004ff7650851004fd765085104cfc76508510057f755085104d7c755085101ebe6450851006bd64508511873e5450851005f77150851005f4715085104d7f76544510067f76544510047f76544510073f74544511857e74544511857c74544510073c74544511853c74544514c57f73544514c57d735445104e7f63544514be7d63544510057f725445104d7f715445104f7771544514b67e615445104f7661544512957c7054451004ff745805101cfe745805101cfc7458051004ff7358051014fe7358051004fd7358051014fc735805104e7f53580510067d5358051004ff725805100cfe725805100cfc725805104e7f52580510067d525805104efb705
  | 27 => 0xf7254a5104f6f7254a5100e7e6254a511af6e6254a510076d6254a5100e7c6254a510057f7154a51007777154a51007747154a5104e7e6154a512dd7c7054a51004ff7650a51004fd7650a51004fc7650a510057f7550a5104d7c7550a5101ebc6450a511b73e5450a510057d76d465104e7d76d46511b57e74d465104d7c74d465104d7f73d46514f57d73d46514ee7f63d46514ee7d63d46510057d72d465104f7661d46514ef7631d46514ef7531d46512dd7e70d4651006fb6098251004ff745825101cfe745825101cfc7458251004ff7358251014fe7358251004fd7358251014fc73582510067f53582510067d5358251004ff725825100cfe725825100cfc72582510067f52582510067d525825124ef7515825124ef451582511b5be7418251005bd7418251026fa6018251006f9601825101cfe76d91511a6be64d91511a6be54d9151004ff73d9151014fe73d9151004fd73d9151014fc73d91510067f53d91510067d53d91511a6bf43d9151006be43d9151006bd43d91511a6bc43d915100cfe72d9151004fd72d915100cfc72d91511a6bf42d9151006be42d91511a6bc42d915104cfd71d91511a6bf41d9151024fe70d9151004fd70d91511a6bf40d91511a6bc40d91511a5be76d915101cbe76d9151006bf63d9151006be63d9151006bd63d9151006bc63d91510073f53d91510073d53d9151006be62d9151006bc62d91513cfb751d91513cfb451d9151006bf75d91511a6be75d9151006bf73d9151006be73d9151006bd73d9151006bc73d91513cebf53d91510063f53d9151006be53d9151006bd53d91510063d53d91513cebc53d9151006bf72d9151006be72d9151006bd72d9151006bc72d91513cebf52d9151006be52d91513cebc52d9151006bf32d9151006be32d9151006bd32d9151006bc32d91513cebf71d91511a6be71d9151006bd71d91513cebf51d91513cebc51d9151006bf31d9151006be31d9151006bd31d9151006bc31d9151006bf21d9151006bc21d9151006bf70d9151006be70d9151006bd70d9151006bc70d91513cebf50d91513cebc50d9151006bf30d9151006be30d9151006bd30d9151006bc30d9151006bf20d9151006bc20d91511a6bc6459151005be76191511a6be7619151006bf6319151006be6319151006bd6319151006bc63191510073f53191510073d5319151006be6219151006bc62191511cebf61191514e7b751191514e7b4511915101cfc7655151006bf645515101ebc6455151005f77155151005f4715515100cfe76d8951006bf64d8951006bc64d8951196ee62d895101cfe74d8951004fd74d895101cfc74d8951004ff73d8951014fe73d8951004fd73d8951014fc73d89510067f53d89510067d53d8951196ee52d8951196ee32d8951006ed32d895104cfd71d8951
  | 28 => 0x8142004fd75d814200cfd74d8142004ff73d8142014fe73d8142004fd73d8142014fc73d81420067f53d81420067d53d81423aebf43d8142006bd43d814201cfd72d8142356ee32d8142006ed32d8142004fe71d8142004fd71d81423aefa40d8142356fa20d8142006fb60981420057f75581420057c7558142005df73581421d5dc7358142005f77158142005f47158142005f67118142005f57118142026fa6018142006f9601814204ebf745935104ebf545935104ebc5459351004ff7359351014fe7359351004fd7359351014fc735935104e7f53593510067d53593511cebf4359351006bd4359351004ff725935100cfe725935100cfc72593511cebf42593511cebf4159351004ff7059351024fc70593511cebc4059351004ff7458b5101cfe7458b5101cfc7458b51004ff7358b51014fe7358b51004fd7358b51014fc7358b5104e7f5358b510067d5358b5104eef7258b5104eef5258b5104eec5258b511beee4258b511beee3258b51006ed3258b5104e7c5158b511beef2158b51004ff7058b51024fc7058b511beec2058b51004ff7650b51004fd7650b5104cfc7650b5101ebe6450b51006bd6450b5100eee6250b51006ed6250b51005f77150b51005f47150b51004ff745835101cfe745835101cfc7458351004ff7358351014fe7358351004fd7358351014fc735835104e7f53583510067d5358351004ff725835100cfe725835100cfc725835104efb705835104efb505835104ef850583511b6be64d92511b73c54d925101cff765925104d7c75592511b6bc64592511b73e54592511b67e54592511b6be54592511b63e54592511b67c5459251004ff7359251014fe7359251004fd7359251014fc73592510067f53592510067d5359251004ff725925100cfe725925100cfc725925104cfc71592511b6bc4159251004ff7059251024fc70592511b6bf405925101cff76552511b57f755525101ebe6455251006bd645525104f3c5455251005f77155251005f4715525104f7751552511aeee62d8a5100cff7658a511aeec6258a51004ff7458a5101cfe7458a5101cfc7458a51004ff7358a51014fe7358a51004fd7358a51014fc7358a510067f5358a510067d5358a511aeee5258a5104cfc7158a511aeec2158a51004ff7058a51024fc7058a510057d76d4a5104e7d76d4a511b57e74d4a5104d7c74d4a510067d64d4a5104d7f73d4a515157d73d4a5150e7f63d4a5150e7d63d4a5100e7e62d4a5100e7c62d4a510057d71d4a5104f7661d4a512dd7e70d4a5100cff7654a5100eee6254a51006ed6254a51005f77154a51005f47154a5104f775154a511ad7f7654a5100e7f7654a5100c7f7654a511b57e7454a511b57c7454a510067d6454a515057f7354a515057d7354a514fe7f6354a514fe7d6354a5104d7
  | 29 => 0x6f441d8552006f731d8552006f431d85521bef621d8552024fe70d8552004fd70d8552006f76198552005bf74585521e5bc7458552006f5611855201cfe7418552004fd741855201cfc7418552004ff7318552014fe7318552004fd7318552014fc73185520067f53185520067d531855204cfd7218552006f74118552006f44118552006f73118552006f43118552176f52118552024fe7018552004fd701855201cfe74d8152004fd74d815201cfc74d8152004ff73d8152014fe73d8152004fd73d8152014fc73d81520067f53d81520067d53d815204cfd72d8152004fe71d8152004fd71d8152006fb30d8152006f830d815211efa20d81523667f65981521e5be7498152005bd7498152005f67198152005f57198152006fb60981523667f6518152026fa6018152006f9601815204cfe76d954200cff74d954200cfd74d95425367f54d95425367d54d9542004ff73d9542014fe73d9542004fd73d9542014fc73d95420067f53d95420067d53d954201cff72d954201cfd72d954252e7f52d954252e7d52d9542004fe71d9542004fd71d9542024fe70d9542004fd70d95421fcfd76995420067f65995421fdbd74995421e5ed729954204cff765954220dbf74595421f5ef7259542005f77159542005f471595420067f755954220cff7459542006bf7459542004ff7359542014fe7359542004fd7359542014fc73595420067f53595420067d53595421fcff7259542006ef7259542004ff7159542006f77159542004f77159542004fc7159542006f47159542004f47159542004ff7059542024fc705954252cfe761954204e7e65195420067d651954200dbc765514204ebc765514200cbc765514201dbf755514201f3f75551420073f655514204ebe655514204ebc65551420073c6555142525bf7355142525bd735514251f3f535514251f3d5355142007af725514200dbe725514200dbc72551421ffac725514201ebf625514201faf62551421ff3f52551421ff3d52551421ffae325514251fad3255142005bc7155142005bf705514204cfe75d8542004fd75d854200cfd74d8542476bd74d8542004ff73d8542014fe73d8542004fd73d8542014fc73d85420067f53d85420067d53d854201cfd72d8542486f641d8542486bc41d8542006f631d8542006f531d8542476f621d8542024fe70d8542004fd70d8542486bf40d8542006f761985420057f75585420057c7558542006f5611854204cfe7518542004fd751854200cfd7418542004ff7318542014fe7318542004fd7318542014fc73185420067f53185420067d531854249ebf4318542006bd431854201cfd721854246eee3218542006ed321854249ef54118542006f63118542006f5311854246ef52118542024fe7018542004fd7018542024fe76d814204cfe75d
  | 30 => 0x9601815400cfe755935200cfc755935204ebf745935204ebf545935204ebc5459352004ff7359352014fe7359352004fd7359352014fc735935204e7f53593520067d53593521febf4259352004ff7159352004fc7159352004ff7059352024fc705935204d7f76553525767f765535204f3f745535204f3f645535201e7e645535201e7c645535204f3c645535256d7f735535256d7d735535204e7f63553525667d635535200d7e725535200d7c72553521ff3f42553520057c71553520057f70553523767e605535200cfe759875201cfe7498752004fd749875201cfc7498752004ff7398752014fe7398752004fd7398752014fc739875204e7f53987520067d539875204ef6719875204ef7519875204ef451987521aef52198752024fe7098752004fd709875200cfc755875204e7c755875200c7c7558752004ff7458752006bf7458752004bf745875201cfe745875201cfc7458752006bc745875201cbc7458752004ff7358752014fe7358752004fd7358752014fc735875204e7f53587520067d535875204ef7715875204ef7515875204e7c515875204ef45158752196f62158752004ff7058752024fc705875200cfc7558352004ff745835201cfe745835201cfc7458352004ff7358352014fe7358352004fd7358352014fc735835204e7f53583520067d5358352004ff7158352004fc715835204efb705835204efb505835204ef850583520eefa205835201cfe76d91521e6be64d915200cfd75d91521e6be54d9152004ff73d9152014fe73d9152004fd73d9152014fc73d91520067f53d91520067d53d9152006be43d91521e6bc43d915204cfd72d915220ebf42d9152004fe71d9152004fd71d91521e6bc41d9152024fe70d9152004fd70d91521e6bf40d91521e6bc6459152005f77159152005f4715915255d7e76d515204e7e76d51521fd7d74d515201e7e64d515201e7c64d515204d7f73d51525557d73d515254e7f63d515254e7d63d515200d7e72d515200d7c72d515204e7f62d515204f6f62d51520057e71d51521e73c41d51520057d70d515237e7c60d51521e73f40d515200cfc7655152006bf645515201ebc645515204f3c5455152005ef725515200dec725515200d7c765515201e7c765515200c7c765515204d7f745515204f3f74551520073f645515201e7e645515201e7c64551521e73c64551525457f73551525457d735515253e7f635515253e7d63551520076f725515200d7e725515200d7c72551521ff6c725515204e7f625515204f6f62551521ff3f42551520057c71551520057f70551523767c60551521be7d75d855201cfe74d8552004fd74d855201cfc74d8552004ff73d8552014fe73d8552004fd73d8552014fc73d85520067f53d85520067d53d855204cfd72d8552006f741d8552
  | 31 => 0x4a00000500d400c0040020034000001003000408600902880000020020030000004006001805c016006004002800000300200380a4000000800c02800e00d000800000101cfe7558b5401cfc7558b5404ebe5458b5404ebd5458b54004ff7358b54014fe7358b54004fd7358b54014fc7358b5404e7f5358b540067d5358b5404eef7258b5404eef5258b5404eec5258b5420eee4258b54004ff7158b54004fc7158b541e6bc4158b54004ff7058b54024fc7058b541e6bf4058b5401cfe75987541b67e549875404e7c5498754004ff7398754014fe7398754004fd7398754014fc739875404e7f53987540067d539875400cfe7298754004fd729875400cfc729875404e7f529875404ef6719875404ef7519875404ef451987541b6f54198754024fe7098754004fd709875404e7c509875401cfc7558754004ff7358754014fe7358754004fd7358754014fc735875404e7f53587540067d5358754004ff725875400cfe725875400cfc725875404ef7715875404ef7515875404ef451587541a6f641587541a6bc4158754004ff7058754024fc70587541a6bf405875401cfc755835404e7c755835401c7c7558354004ff7358354014fe7358354004fd7358354014fc735835404e7f53583540067d5358354004ff725835400cfe725835400cfc725835404e7f5258354004ff7158354004fc715835404efb705835404efb505835404e7c505835404ef850583540fefa405835400cfe76d89541feee62d895401cfd75d895404cfd74d8954004ff73d8954014fe73d8954004fd73d8954014fc73d89540067f53d89540067d53d89541feee52d89541feee42d8954004fe71d8954004fd71d8954024fe70d8954004fd70d89541feec6258954005f77158954005f4715895404cfd74d8554004ff73d8554014fe73d8554004fd73d8554014fc73d85540067f53d85540067d53d855400cfe72d8554004fd72d855400cfc72d85541cef641d8554006f731d8554006f431d8554006f721d8554006f421d8554024fe70d8554004fd70d8554006f76198554006f5611855404cfd74185544e6bf54185541867e54185541867c5418554186bc5418554004ff7318554014fe7318554004fd7318554014fc73185540067f53185540067d531855400cfe7218554004fd721855400cfc7218554186bf4218554186f54118554006f73118554006f43118554006f72118554006f42118554024fe7018554004fd701855412e7d75d815404cfd74d815457ebf54d815412ebc54d8154004ff73d8154014fe73d8154004fd73d8154014fc73d81540067f53d81540067d53d815400cfe72d8154004fd72d815400cfc72d815412ebf42d8154004fe71d8154004fd71d815412efa40d8154005f67198154005f57198154006fb6098154026fa6018154006f
  | 32 => 0x2400000000b808801800d0050000000005006808000a000001804002801401b801000400f01b000c008000031000400000b00000040000000000028006006002802c074006011001400400501b000007e008000000000a0000018004074000000800001401000e0020006000003000002c00c00000200040000048000008007013801000600d009000800c00900080000040020020050008008000803400000200f00000280200020000000002007000000a0000010000002001007000800600e00000d000c003001803c000005000009c016000000800000001c0008000016000000001800400200000500000000010150024000001000000000c000001000000000d00000020010048028016000000802804c033001003c0380090020018000002000001c00000f0008000010003001001800c000001800c00603e000009400000500300a803400a0008000014002004001c000039002000002200000a800000000b00d80040020010060000012007001001402005b002805c00c001000003007400300800a0000000004000c010003007000004002f001001c01000f012001801800100a000002000a00100200020220068008000001006003c00a00600e000c01003f00a8004006019006000000600d0020020002018003000000400b007000800a00500000040020010020000024003003000001202d00f0004000001002803800001d000000004600400180100ac0000000004000001001800c00a00d00181c80080000000008002003004001400c000001801405600500e00080020080020028016016001800001400d01e800000200f0008060000001001800c0920000128000002000000800800c0020088024000003001005c00200800c0000002000000800000200d00680540000120038004062019001800801c01500c8000062002000003400800c002000806e005008000000001800000100040000070034040001021001c00a00700a00000020060120030002001000005c0020000050004016000001803804a011005800800e001003001c000007001000005200401c801000600c008801c00200000a800c0020180270004002012002800408c0030018008000000001000804c01c00d0000008004006005400000500000000000110000010016001000005400000600800d0004002002000000000b006000c0020000028008000008000800003a0020068038006000002805c002004000002c0020250070014000020000002c004004005000000e00100600000840030068000036015008800000001b000800002c00900000600000010080004036007006000c004002004000c03200100080000040130000068000011008801802e000007000000a00501b000c0000000010014014000001000000e01f005000000e0030018028
  | 33 => 0x4004005000000800000600080c800000600b00ac00000100b803c00200a0010000002007017800001000000280040340070028000004002002800800a006000802c00800f00780b400a002032800c00000b00e8078000000001800c0280030028010014000000000000000100180080020040050034002000003000c00a002002003002c0190000008000004005000000200300f80000080050028020000014000800400c005000806402000c001000402a0030200034008000006000c016006001801400c01f00b800000e008001805c004002002000800200d00b005002a000001000002200100000300000010008010014031000005000801000b00140060010048038014000004014c000004000803800000300500100140930000020000002001005405402b004004800000000500000020030000008006055000000000000200c8080000000000004800000c008000401e0010008008012000005800001000100600100020030000060048001000800c006000002800400c00601d0034004000004003c0040060018054006000001000000800100100040000060030020008001001001c03c00800380ec02e00000900240020060000000014003010800803602700e000c01200000100c0000000001800c05e02a0000144014024000000000000c00180100160000108050030000029000c008001017003c0000020010008020005000000002a00400000000020030008014000000001001800a00500d00000020000048004006054002001400400800680f40880010010004004006006001400000300080280020020058000000064000000000801600100380240a3004800c0440060000028000000003801405c009000000800e01b000007803602000000240200010018000018004000800402400101a000403c0150070078024004003001003203e0048010002013002004c00e000002802002c00400080180000030000014012001008000000000000200280040060000000008003003804005200000001cc01a0000010024002019000000001400000d0000000000000801400c00900480000000000000000014003006003400e000001800c000005000000800e0030000034004035005800400800100e800400001b000000002e03700b006c00a0080000004042013004801000000801a800007a001000805802c01600e8000040004000000404400100200180000030040000002001008800802a00b007001000c0020010000004015004001001a00400080000800050000030004019000000003000e001807800a000006000800003f008800000000000100040040040000088072003000800005c00f00000080280130018000006000000800000c02100000580000040018000006033019802802e00400f801c000008008805c000018
  | 34 => 0x4c1033a090a2a85cc8a48000161c94285ba4f300000000c9072a04146601e46916202294b9c9c00015da45c89908d893ce286800059a00002651cc2053a358529059a000285e494150c97c25ac0db875a71b27547aa898690913e00d91ec6a8d924289c96de000277e7388000636278e0001bd4000086a18a28b08f0138a86911120001dd25ab0000073993280c8efa330800022e96ec886000000b9c5819092a62a323a62518c2c5f0936629f250c2c223268e023943b122e4476167e001000000000300b807401200700d005800e00500080000000000020000014000000002805c01000280140000000048000004009000000000200600280040820000018040004006000006c038000005809802e0020050004006003016003800c003001000c01c003001001403400000a000c0540150038000006000009001003a002003000c02602800500b000601000d000401a00702d803c000005001802801e006000001000e0060048000000031002805c002005005002000800000d804000a005001001c05c02a000000402600400200000000060008000000008001001400804f00000200000090168000000004002802002002f004000000802700780580000000018004024007000000c00800e00c0000000032016802c002000008807c00400e00000100460030000074008022000800000000700e801c02800201f002c0000100000048000000006800804a0030000028016004001801800a00401280480320050008004000001000000406000000e80040000020000174000015000000802c005001802c00c00100200e80100070188014010035003801c00000e000801400a009002806c008009001002000200600401f0008000000000804600100000040060010000000020000001001c01800d007800000a0090010040000005000004400001f003808400e00e005800801402000000e801e001000000c00e01a0008000080035003000c03000300500e800000f001802000e007002805800200200000d0000016002800400000700300bc01e00100400480a0006005004000a0440040008000008001805400000d004800800000f007001c00c002002005400c000000000000c0000230000024000028006000e007001000c002000006800000e0020018028008003004804000a015002800c048004008000000000000a0004012000008000c01404a0050004008003000000401c000001800c01000000200000000090010000042006020001000200701500100000030038000000005018800010801c000003c05c0030010004006001001800006400a00a802808000000c8004008000007002c0060440038000000003000001800000400b0010004001002008000000101800200020020090000006000001000803400d0000038000000000000
  | 35 => 0x211410c25146f487da00000002e89c5a0000f524a601964a51aea08797d02508a848a282fc44326847ab909071a1b1290ba7902cc00009df1b823ee95d6a49001e66c00003188ee40e3883219715125b42622a44166c32f16d68748b40a791ce8a41a1f692808242c38bac4c0853a1ae9dbe9c900be39092ae0c5a3167dea65a67e8d880ed1f7e7540d1083615a621baa8a4212a0a0b712da0d004685468ebe2a59a820948eb40f790de0fb87322612a343dd9bda4aa8e722970352234168c5ac094063c1d069ef860a16a1bd035805866761a160000b4e60da51607b0a0214f9baa69697a601185e24ef048a0e2a4767af05ce961818c0000000a8c00007bb8ca29dc800099e1a0c8e703b0a1f25362ea13624d79e1c1f21536a5e9e5438e078606190d8953901e564962e3ab91ba7a4952e334000082516a66a92470a0294fa88883421038000511025479d000061687d663e96345288bb80001d904cba81819ea8ae00000002778e1c000000000018867c798d4a379f160f7098256d276e6591b18a95274888e0e3e000017e0002902746886263f21603ba266436985f4180298c868000c68e882c0e0a08a96825881698cea46985941eb92685109cc45f500006ff0eea000152c7cd00001dc1ffc77c21c000000009c49d36a759f4810b00005850716000123c94009c680e9d9c0d88eec9b123642b58edaa27a07868911cc27b041a000000061b19b26df85e600020ec93520686d0a8be457a90c660aa8413a80000000df200000000002046a8b158c83691c665a93c802aaa06000039e82a91981e0a70c252a58c2278de42d6a5080ea1ba09238cf052a29fc3f7a2d602e9c5e21480000b528dc000000043483ea1a30e9890da5ba04427bc4ce1438514086840e1cb69ba85c60a61a9046b09187780272224000000d081e3a1a6320000a3a2bf88c222980000001d0c000228e0001dd07b013f477f00009380fcc00006460000f04972aa083d206ce84715bc6ef02ea897848282f985278a81769059f062b780000000e0c0001caaa452702000267208481be8e680004b4a99000000000001e10441066a1b902d665d860404516c64d4260682e1ce45d495900fb23ca000140298a0000a0c1fc4a2593ae37802be1fe00002bb8dda75380008cf000000000004fd800081600005ae17369100fe250f128642d102223a843e1181da60002a8800006a2000000078e054c98c02a0a7a94ea05e9ef800012008c100008cd800040180106f227b60ad0df057f00006648000000093c8a58df87d00c428cc15e0a5994fe29280008a10b4c3eb81ee1172a9068b0e5847a020aa28275657d893224f849000003c600023bc964041c333000000017623b21e1e6452a5c758201008b8c7a0930ef669f08fe46e1bca79d903a7e61db88401a9297a000098f9d6e
  | 36 => 0x7d400d2000177400023925a3860c33719e2000000096900000001a4e78499861d5800044d80000002000995000000025fe619244ca4a065aa3a00001568e9c96f867c77fa2741cf997e00019c20000b0c323067402200005be0b9c9d89b1a4b11e4a425800075627cc81e8000493000069e91543598ab217483268af200e054856a000000022d00001de98c801ca41e1e4121438ea876a0022e6818a65e000031000029d200024225cf93d829e9d528f11c0c5c49a0e4c580843ef25faa31866ea8987d4636947058d933e3020feea2482ee85e8dd44eda1343e3966a2532a3e53da55e7b6243a5798394965169c1d023aa9b6a0524450f70347a16a07f2a1488f1c18953252c278000000027d043180000000792107a2503fd1c2400016522ec217400008720a90306000263a9ea0ffe5611a1021717ac2dc20cc3ac000400029502978000235261e20397a2000117e1ae0a0832d95ca77080009cb13407729b140001dc855594f41e620642cb9f029b618822658b9e4af139020200e628a14e629019c09c5039680f05ea51883ca77e193455f01d622c1b0a1429ff65a686126db92d63af28883258a8895f1e44a159f3813c9f9e000000072287545d1a1b04138dc64171b3235d946007802340000ecc000088e9240aba1e2aa2e9b9a342487172000026862439b0c418932495d8a269491604827000000027309ae8c0084a1c2a906003a00007e097c91b071a8e8e11a89022fe838600018a25c70f66a41188a00021b62082718a43aa6c48d8ac000000001aa1788a660adc7739b408cb91ec0001ea200014f2a4e0000000192089303d03ab211e7779a3e000000012e0000359000001f9ba4905115220e00008efa83a72c25c06de0000015a81a2319f809cd09f61088d7c3e6800000000005d919bc197975c3b380009300638844973a7fe9c920001e3217e800016393c03840d2603d92d462d06504e7800053280000388000873a6fa19328d009103449b40e78000001600002567d3209a91708ac9cc8fb870b00002bd964c36487de341000030e00007b899967ef030c1e30aac5f69e285c880004710d2405608987e58000a63800000000000310000501201e000184e1f2a98064287b4000027e00025269361e8c78097d67e39a720c50b66000000000017f0000000081d80004bba1767fe011688a800026a1f7800000007a3800040d80f2409000000021207191cf65d61186882170a058963a47d91fa52c29d86b4975e87a05a237b0b4671c0a9a7ba090056807ce2a613868911e3a05a05403828b946fc98702ea87fe1e5114a17c8280897261290220bc1d380c640b248c57a8230493907474e005c6189a54a0f93c624b9d8866e04aa7519d4a66d88a8000047684b936455f80008259706062813c18f8abe70089c011980004ca0b86815
  | 37 => 0xf19e0615a4ae979a24a6249e662bc82bc67f81a8498a38c432a93e0d989c236c89580f8a43e9f20d12a03a04219c95483bf94aa43020560b405da4f912a07db81c4a72956e3a58b1c11d1d5e38b85d03589d564bd071a77e891c2679e4827b8220443845081c0b964e4a4d085b8a429a70e5c57c8a7023b0a3246217767bc93f06930d8061d80004560e601e2106a6ee9860827909207c99106449b560001ab80db028c6bba768a3a87e221d837e73c0c4827f80008a692102f4214c09929c46b0000000000004dd0d1c92f9d962e389ca9210eb8541123000009c84029e3ea21232c0000bc4000000054a0000000046c69b04be00000c86751adc6a5800009a800040a284e0c085740000ff075d800094112c06c981b2051262e49f943203e000000010d66680a4ca1f87a451182e43c51b7082200001c99de414a18909528f821368b6c58faa5619f829a00021dc00002d225480007a4117839c04ac133a0ca5d680002390170000235c24e069c4a683460380f622018c040700000838099a76ba3240000000483800000c926408c86268721c0400000000000258128000083a80000001eb6a4000003c709047bd92283a21ab222080000000d460aa958a14ca102035a9fe8f42a823432a6696a037660900006a8934aa329f600001bb032a82ec11480000cb000000000005ffa13a0b194dc65980b61c712349a619e4621122c4219b24871a2fca1e80001f310340000d2a43b000041998ba99c0c9e65e800062380003f722fa00002ac896a70600011641d88a9225c800018c29ce0000000000165e00020f40000d1449223cc9c588aa89b9bc299e804c417a6026bd9a8a6119d8c604a4a80000ce600000008169418788a34c36a17ae70896408be0742a6e16a86650a1e3f28ea07d60000204204429602ba00005640000000000125e5762808000000047e0c6e24d000094e80006ab069e3c21b84862000013986065e40076346a73a000087a47910f000000000000928a031a7800000000000844000246468b83c435783981cd8d0254908e2000172c05ca49a79f9a808ec01aa55125282e41f1825a809e7028484706904801b00cc6981b2000015c6097186e11213c270e2038637000006719a22ba98ac6b917140000000151000000001d81dd1400100127a9b8000036586809f680009b4a7265c780007b080008ed00000b7800088c9144998a3763d585aa00000009bd03f000000000000660687823600029605ca00aea9d1c860d589be43114ba8bb9fb822d948e63d2300157147e4c79c20253891403920e890086f0643274004918a8000000000014e20f3921a3fca0ce9de157473e9b1c9608d220dc283232e9874a870e4621d16f60c9244280a010a0a788560f524785db88147149b720b692dc0001332771205c43e908e000160e899000
  | 38 => 0xde23e800027e00002251fd2a57289c6818faa8d519888099c7625d8000a6921be25b128867f27522750a06831a26c200a49ea51137632680a80988a6085096322e8143a2469d725d202c42290a8e2ff05700002a0275913483b800006910700599a6c024b047251a80000cb898a162082e353265200004861d823a2043944002e034c6a79b549378a18a93a0fa603187c48fa5801f985ca603800042980003f3a64a89e80000678b1849e000000002b6583217c0ca87b065500001a09aba0001c8875e9b9a7589ae047012266b61c106af935c647193c9fb223a35718720182a7079400008649cde0001818323800000002c0536a54636280f069986ae2d295aa3f597928d48b222280cd20000c1233e9312000149c266181602c1acc1e99f3c00008427da057609980b29bb80009ce000000005d49ec0000920837a1d126f800028c0000000088796305458c14a7699688ae0d34141a4cc4daa15677c8eaa83f245433298066cc12727fba406570887e11080003c40cfc22000a6a5691b6691906440f8748837a3b846809102061e3c9d61a6205ba2f23070bb286e9d4866aa32a11785d860e93b06e5a962a3324803c380003d50480936a97c729a28c3cda488000230600000002d599f478b00002d400007fa000000020ee9ad01e4000039a274800000022280002a2a0000668000000000000009000456000295400000000001e5a7ab000000000000000000767a9e27b49098a3b9c401d71fb68b1a55c3402a8c0001da45ac81f43df836a45ea148343803600003d222e00009fd88e69f80044092991a0ce170838d10a471406e6620037249827b287519f68e21c7826913f275a01504dc2a5a55614929ab2a162cea256a180d4e9041fa828f261c8012886771913c5278ab4102000077d00bc20fa1520001240a0aa7fc9aa826e00021d654c052c79c9cd80f580005639010593a52248e24e42d2000069205ec2810cde78907800001dc094d2a920558f324ba10702c4a4f83900f3872582b87180b806e3285254d11065b60992777128e67a04f485917566330dfe5d41f9c52416aa4929f662380cda55306568ad10b0006000084b19984741c283940dde25e1f2c3bc1f0a5ab861c61725f423d0df46f3901c993a04c67113268ce21bc3f106c04f7875043b9c7426893d214b97bc6459bb6487a46e1a8261a8fb064438995d470f94d89679e949561fda35b85b400005387c90b6e2e681d40000bdc79600006fba67e34f8dba00016c430f800017e00005b6800000000000001b0499d8b4200019068e1800074f07a81b127f48bc0e18416000069b80009a280009e2106e000055e113800093b983e834a36e60a942e6c5999c67e26a075717cca5e0de8a0b272e52b81e284d990831523d218416967f30fea1408ae050894ec8ba88120ab883421
  | 39 => 0x48bec1b708f649712c87f700002be80000b625388d81e1aa320f9495580003b48e360000614630000045080000000000000217200027f80000000000262a9f0000000000000000c749ac83cc6b09bf0280009604e10560bc956c0001e0654c80009f1941e4709a743a5283688524ea0001578000054e56c1f1431aa8bc00002fe00023d88f980005e30000006a656a9424fc750152a906935424a9b6800000007b3a3ee44c800000015fa7331b98116212a639a99a252000010ba42800016088faa9ac000128264e821000000005e180009d9916c8490bc89f6053c3e489a695024aa5018f2089e0a681e3951c69c00745099be8000000027599502068e66000000068012de65601d29829ca092c815a6008c804e58374a54a9962c19d344c8839ca4200004052a8e31f97443170d8ea1202e64480e0400000006ad9ac44cf0af000019a613521fa8909d1e762a14600001a000005be00013fc000213000014ee00000000000be6059107250a0278000192e00014860e91fd40c110aa6810f6a0c38f4c1ef98882a0800057880000001bf651d283800000008af919a410962c7b31c820001ef40000bb4000000000007961d287061e7a348a6b801489480fc607962888106e89649cd0143a6e427406ac32498e4237079c00018ea27913882eb9044196022251d889a1ce137a73397f48031356800800000024c600012209a48000000247e3bd0eca2c68bc24a78b3253100003d280006020e5637600001508618288828e1f026827d720e28d7a9b6000276a8c505a48a92a78428a16c2310118577a5d219e1aaa55700000070000000000098d800085a28660249cee36d29f48d00000860975467212f647c911e33d1f3e000088474a985442e0cce93f84c056b0000000000055380000e324a2000000067713846860b1e51385507a18000000256400000004cc000000000002d10bd45da8be255512801370b6230c80640ac06d08138000000111a8ac800000023fe0001da0a620dcc0000ac60001f266d92122000000002299840001702629013071c94b80000816000245e3be0e5a3e1a31e0000a9c0870000010946c58601fa3359e34918959e9d10a0c8b5195223ca3f2515916064f9fd883999d272ca42a38b1e6471e89f04fb8d7009d23ae8dc9c16820276027712ac8e0897491d260ca4b826800000000b296980eb92584609ede5b71ed4000151e1431e145579f8a633a6a23b0a8a86f89e6e9bb232800022ec3d01efc00000004b1815410d256675f8c288e82956000034872691346c09fc000016444a8a48aa6f8000000000000018e00000bd66ca0000442a6e817715181bda0a26e3800000000009ed1b4a63119784a11e5246aa0f079302764c21662432297290b0b266b58c2e2b681464eb0b8a59d09365dfa0f65151f3001486c22fa23
  | 40 => 0x74c88649eb80006c2000054281dc86a0000483182829d942c6daa58a2331cbe96c8000000140c4c609569d70000000027a9e0a89a2a897e4458a2e02b997d251c80000001a8863480007aa1e603ce9f36a68040445c15665b38c2a4fea01a291a00a9e4917482321f405e0b7a104800001a1546000235a55923fa65585347e328fe7b413b493b23f69c8291c7d1a6dc38223fc00009cc4bf00001c40764186800074894b43e8800000016a4613000075b19602379f0c00011100411e6a00012b653315100c680002fd8000a5923a40000d4aa479c620002a805a11fe400000009a218441aa81ca0000f50944a63800009ae61222d22488f6475d0000142129c69a08b200000000fd800010d909e0000a942c5807a4010b5e16f00003ae9a3600021f00000000000009a000000094ca37a2fc125400000006ee0c104db1da27251cbc38a15ee00026000d288462aa0000465107a00004a8000232056196e6000000000005ae00024661c29216111800015c80004aa278600000002958f800000c6c7c39b9c2c29fc87a9261694c12cc6a9932c3e78d9c3dc954a30d285496b80a467780000000000a3f13008a50aec5660f160cd24c400000000001540702035462321d01b4830097e00007f895ec15480001c39180000000016300009e510d4000264c000274e9d6978a7450616278a1ee2d9294c162a3f40731d840002a28991000066f9b665ed000006000007e8a312000000000026400001f1c40c80000000e6c573a574071a79a6fb000000029ee319000025e8000000000013a2a5299d1a2a000000000026603b7111688c0f223e10d187b11d6aa9faa4473703128f9000000001f800010b600001080000000000000000000004808ed685120b44dc90e84c1a4f03ed83323c48000a08000077507f4477a6de00006960000eb26bc03ba9b39ff4802040a865a5da0000a50000011e000213e3098768000296a2e1000000005b000027fe00000700cd812a0001a9a68c00f4000283c0001f4e7f7a5c40000f2a000000099f1424000116883080001fba72a52d8a4e08ea874132a9b48b2a3700000000000000043080008320f42000000000000004151b7a282855800000006d408040000a1c3f4800098d2a049a98000000010c0000d2060800006b996a20001d4c8260fc619485b80000050313018887f00003c7957200018b89180000258a7d62128a6c408196c0a894b27df256e00003ac1f701d062ca36800006b20001d704db8e0e0000000682000036695145eca4c26c01e9a1291e8a00012b241317fc49a977848280003e20d2e632a6808b783b613328906cb8a8aa4998f851ba71e45f01b617d913e52588a28a411f40d39a7e9d09da876a9742821901a14596d22aa991e00024ba0001c3652119420800000676997c3161e1646722009
  | 41 => 0x161e7d489b4000000000001e6869884061a13a65280866a0a28820000e6e7bb00000000f5e5c9987812c9fb263883b2806106c1c5202e3aa0cc822f028285e040c85527baa93277480a8284658a2b68670ce85120cb418b222c34b1f9a0000000688895e1f90000824229e47c11ce08f00003100000846a91613e095c5770fa6000112600020d43879838000199e88b9eb211f1c7e21e16ba4ee01f65b226a46940fa861fa4a63cd1e4ea4691ca8788fc86aa0718a77a258315a8d49bdaa4040b8d747a596cc2482050397a52a20327e66d3812862a934c5c61c568c3026c7ba8b72640280683900004488fa0374a70a385064e0000e8466b00e80000886000035c1a6800047682483118000a881c303e413d48370efc0001dbc4a2846252f99ca5c31a28000000079e9c4e0001c5423b80002d71bc000014780001b3c00000006be876a00000005742a3c0f0000000018144e701907ae052053486a685fa51028e0f6c843915c00027d2467969e71b8406797220c0002a1287801a488fa7ce00024ce89f000000000005058dd60000e2422f93da59f0000000008c368000043325a287600ea1eaa27618780002131a1243994c6764aa5e656a648a16824e00029b02ba00a25fd833c4628000000168aa8e9dee4409bdc09682f400000002ef0000000000027e97dc9b2000002d00007dc84ae1928000000228000000000000000505213c00013a0000000032a00000fea9f815e9fac00000002a800005889bb25340ac2a5c0766a380af46d48082145116e04c9c122ce135800007c25e5a1701f196b6657a01c62ba8fa2f69faa2e62212967262c8e6138c783a1985bfa49290380007bf8e9080f9b6012c19cc5da003e0000db8373a6f24b397ce5a40ec08c29f886c880005928ea67d51db43a2a98619da0a40ea800093d80000000e440000000000000025f80001fa09e6a0091b27e48fd033925d644200000da00000000bd25ed8000066948a000246ca5791ea8c6a73c1839a4a000131c1c797840001670000091e1b624ac88380d03030c9c7ad14c082a0e3c734980433ba618820a5482f90000a39145e7cc8b2c86e0ad80000848a841a848b304f047ba92c0709c5c9081c26707a8a26488f5a6af1ed656e18a642e914e4000bc01b8a240179257a6439b8a81792be28d96f0372121872e05b2a0899725ce00003ef96be19891a2857815e2c09e365be9aae999a1de516a4e84b610e40b31832000233e29e0596000003000000006281fce9389e6c367a21c36626b662c193612596a099a9dd80f992665f89bfa6a80666048a23644002e839f122e9638c029a68e2231285d600024b603f93b28b2130e306052a859825e000184200020a62f81cca5499bde064a96856e97a461983583149e0a6268b6029ba31ca5b96bc15824fa64b14f81ee0
  | 42 => 0x84e05f9aa1a2cd9b9ea0700008d1168807c0d728df130a1db04d291180007e0800043aa8644f29a6400019a4602a826128895a81f9fba9dc17040001c4c1f111ae0000fa45cb86d600000908f7274c8e594941bf915097309ac25f21066dd80001a411e08e408301c2051c75519ae80b0f0c7caaa005e61e989e01568000020e7ce96568d29fae3fd80006881c1ca4800123ca1b887768e7e5a480002b5000000021b4213a1580002a38000000049580007b28f4400000006b3aa6800000000001edc7050dbc0000f2e41e15be8048b7600000006bd000000028b268d14302b400004e0831c0f68c681e691969840e52316a4e678b9d106b4048c3cfa11882118f6000204a27c80400b38fe69718e3204d81340002810a5283e8091800050680003e3159c2f62722000000000000005320eb600022e8021880a2a980001ad0000a9c9b460000c1a90ca65807a80008f180007001b5e6fa800092617aa00000000001f125e0955a1a1000074b0d3a1ce8da204197b07a79bf492c228673c80000000ee273f1f7000000000000f264b98fb244e048e241857ea4aa7aa5c028143299eb08c3920699a0c30a8895e86e01624a7c00de02b20f887a8a0e3c6119095f8ab61b196001601f20370030aa5393421518cc0173066c29993ea739847e18c821a581999020025aa529aa186040eee0001d8e1be00003df284a00026b823a13e286380da72310dc13ea4d21a1839042f8a247599fa62631f082a0012c8d41e7c00008c02f3198a00000003b7800057d262015f028a69720b2000237461002c846f8048000000035117de1fc91a482b277a000000000020724228b1089c11d443e16786f82092a6ea2c2060979c75f193812f25e23ec0d403c180004520c98000000000000949f788f8765005a5f228e2342174a8e7a27e97b00000cc1f9400000004020000a51a9a83a6937e00002b2000166026e931417b80006ea25d00000000646000013617169e902065840000a3991b4a1c0b24000165a0ef1f2e320805e4c325bc78107020570f6ea9b800000022ba96d0000000256a67a800092f19f2a20068e6cd80000002750000000041806f24d6aa626b180000002a0c00013d012699ce0000d5400a0f4e00016c25ee80008f880003cf000000003800001f6c1ef000031824dc000104657e0e4c90728243f52984a2a9612027206c6961204463268e9778ca039aa0202492544a36075e2739a025a099f09faa936188162a7f98fac4a49cf43b61506703989c00007304e925029a422d05e813d6519837826818c67ec268c58f1d9a284944aa9921406e4a46a50d846e40f210a1889d446a7095036a8bce0f8088a89aa1ca000090873e124613d96724061a8e956804aa7e90a08988c504380e0206d270413400009c0223474e9380000000031c8d6a1eb0664
  | 43 => 0x227259a5ea18962e992246098cf69fc8000a60a53e1a926467d58bee00029940000d86494936864c28f400000c03fb15007d918ec000194a000000014680008f51dcc9b528c473b1b580000000657000000015808b105de0001fb489200000ef974e00029c80000000000159a95817ec7a206ee1ec800036425ee00022163d815a482d8a441950c6604ba7848e3822c002a4b4047265ca3b1d0400008c818f25e09b88a201fd8ee679c28d654f9bc460b11fc08a02949bf13ba9f9172a8df8ace7881b0613f0000a7991762d4a1da11283fe30f22e221b20c0414220655418fe59ea5ea67401de6ff9c3c884165c26ca79c27617d83f91d240fd27460001562973a7d410c8a2e63ba45a2cfa7286cd25503569a267a10b683dea3f84ea883a0e89f744d825420808b8c008087005b06b63988dfa589804e80c12083fea51e43d85846378ba451308280d789e813180007bc1e406ce83b8912237880d916a000107e87f90ac1c89c3400e16c025c210426c1fa418d97108b60000000226662629127c11d028f38478958872c77892e244a80003e604e277980009d91ebe68c8f5832129d480926b05df28a642b95968881052a1e01406bb1a9800885f042f2a48160856297910d0260045a2b2817445012225dc0b921ac23c887ca9c21cd29ec38a88d803600585ad049e56a01848ce863a5231dec15521c20c899241a62846000141c54e290a04086da000006a00007a28db1fd646a1ca20000f74a9f1d12000000049b29bc0000d7e90c185849c00000001cfe9030c0a6d20000a56190228519e624980004a914d66e500007898000000082a15b09686538000218229895b00001ba845453900001461c4400026c600021ac36c15b24771ab48ea1d820890bde00000008ee9b0e67b876e6868ae43a4923260d1ee6a9a85b64ff927400024945de80003f084641b7a71c4fe279651f10fc7fa8bea4272976000013e000000000000000a400006e880008100000000000090e0000000196e81818d080d0000a1a92c200000000000000a771fa012d00000a9a0c40000f687d1042682c1f0026a800069a80007ca000039e933400011841fc04c244a077e0000000000000080520ae08988500001b2a57c0ed0862953c3bc992646f2626124833e10a2a2491a21381441a561a51cac5148c063138e302f2a56809407283fa0c8a7471724068a99c13793522ca985e17010767600c448eca04861e829260c16ea1559fc68c881fe7e11cea2841b5c44c25a68341b9074026c24cd81a6946a1107fc868854e981a7568b581e8032853792e06f5a29c5cc05c89e89db613108ca3540ac8a308da46b5124403b9f761bf1f9067b013a1ff1d0e2f185e899b970e873145c845841041690e284c8c227958194a2d14644748d3039d0f248d39e428601b5a1ca8e8c8cc
  | 44 => 0x6a1800049d8c7c52f07b67c880001321ec86250000889800038693a297da8122ca22da6828fc029480007b6808029f915a97f064059b929657200005fe1e78139072e93d04021b20b000002a4251e9a524a3148051a0f9c00024a400000a06e982709eb03fc05081c808e1522a7a0d785041afc0aa207c06c10a8868802c608a108455800032b827c651829c0830000a2e9d265d9800035a059c735934e9a51fbe4058260000112461a82082a40000780093a7f40e9e3c0286c16610f43218f2c961208e2232006000000027f0000125000000008ae1b300008610ce23a900004b4000033c80002ed9c981b2800029d00008919cb435621c45b90b7e00000000001e085f800003f605ac28585120000e12000000014000004d18ff87f28ac4a98000000000006eb92b00b8150e7351508000000037287848eda75e701816a00009601de00009bc276c50a86484c40ca449698c22cf18e8a2604443788c1e34f16fc5cd29a268521267ff998e97522f44f992fe28b1ca491f234613b81bc6bf8e8289a1542242a7fa98f143e6d319b468726be20722b06bc898e7da8ea26f321629b284386a30a865fe85c486193be5ba00004c6a696000018e6ce0a30a160000000000000015e477d842a6f1838830d8a5aa3e22aa0bc1620a1b9c461af10f24460cec1c32a0e72e800012da3f02168d38a2300001ee939480591d62df16ee39390b2018a3ac8f680000481d0848a8772a7008da00014580000d6c91407d0000011a126142015e06e000027c405280009259f6200008ce65c28403509fe0853964298214f0990a7086f90f7810ea7760f20590585973c7d099ba00000d41a292f806b01609941dd681a8c5e40325dc7129cc897210402359b2c331a55226203a00c7907c1dd86709890b6a15b8350000273e4df21e626e094400221f82a786083311dac37d926e8a0918ea7d9a5e215000000015ae5bc80000000dae5bd000044e889255c0692000000000000006ac2a7aa46296c6b88e805549bbe843089656da3106ed051e7381f5e42220f28b023c255818bc1b511fe5a51a386b283d8866a98a9139a769e9940a17f163825500007a9a572a69807894f16ca719837c34da5787210cfe570085855aa6cc0c82868164a89477aa29257fa2f61c49e6835598be0858aa47a08d94000082230814fca960420000000015980000001c3aa8c802400000000000f466fe2932a1092ea8cd28446531f10a64a31869012f200000009e62a4635222fe000278a44ba5b852204a6a8795820e481ae000283439d8000000247240483184ad16e24519ac83ed0000902800072422ae9438bbaa5fa71a2bf09664be9b7c5828f5c9b5a2a6882961a39907d86510dee298874656893a86758d8ca9d976036119284bc12ec388090c5fa0a3e6d8a9745f28cb8912a52
  | 45 => 0xdd00661d303e28166a508ae23771d169cda74a40a80009c425b6086099c14d94985d300ce00027f0403a5d857496547200a72322177266697c68809cc0392862a87b059e8c21c2e32c07ea20f137854080544b90fda2349e0c15294e05e6923a040048830380ec05207d22098d8200024440a2063450d13986db0aaea3c872400011924e3a2240000ab85ee10685a0129000009da380132a91482fa6f605e08d99d205039780835976c6b697c476c1686591957aa1895cc12e86f40fc80069329d78a502074000077c0000c7010593dc00019c60000ab004994c21be9e30a291c327b909bc0e98e5400000000000c943711d0a5ef8a544ae12caa67a93a86b9ee039a04d624582c28b3a8ac9e7979e11c05c268f03e408f89c42c80b787109f4aa7819045481de8a71909a2d517942b481b836b13ec5620de69f894089011be69f08f1a55d98b634a2190927017c0001b44865139a91e8abc6b7911caa181ba94710ce42328ce31e09127e18bf2612885e94180fa00007047fb183ca0b800000004180000000000000074b80006a5132056500000000db661400000000a6a9fb80003059344a4f00004250000309000e00a80000f085240e10240000112c93580007c6800013f80000000ed40000e4823c22a228d000007a0b7449f02861c81b1013b04403e5800078611c80308ffc9c3850417f964837a91e25fc9b7414986ec535259893ca604a140b346eb29aa627a06e886a60e00023e09aa00000000026484a5968950000828284c0000cf852b0cac0001676000288a032862458080009f2a1501fb180000000006be03f800000003c2a1aaa078b14000000066322dc12727a0797800011302f6000003c76e9c9e91580dca2d80008da8000000102637081da00000008199d42a6c9650000000022200000000cd4533a88e8a81ff014c285c89824b88c09cc674fa66c345896ea3d8dfc5d006020810f301af992a8d5847a01f03602e0aa4a7a710027661ae810910822e220baa5209ea3549b1e5208af818b9c484f129227460bf81fe8d7a9708cbe526821489385a0736814c45997ea6502570152006e5b50c3a0be293083fa4865b81ea06358e160449efa98529cca1c978ea4d11e69550cb28f589b61d49c7c8ab23e863c99749ee171a2c10bbe000a6ae420141229910fe7a0194845312ba59921b272b8cd88678e06023904a27d093002629f22590bf41cf17ee342822aa0587589bf8acc72393e860ba18c5f00c769af16587ae85683b18308000242623f27e89461f5a00000009f7133a1d328b86cf9b868e28a2a338214a6070d0690d28d24369db20a5a9d09e30fe0879215c79895c496c14e8a010bfe00028f034c835a690883640c043c66a28da856a4c80b885229a78dbe7f0a3848a20f02761a43c00000660001d2800
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc6c62dd520440010fd0c3aa40880030f19075481100062e318ea902201ac6c621d520440350fd0fb2a40880821f21f65481101043f438ca902200987c87195204400187eebb2240880030f1d764481100062fbaec69022000c5c75d8d20440018deebb1240880031b1d762481100065a326e29022000cd463dc52044001968c838a40880033518c714811000673b10e2902205bc7a76d9710440138f4ec32e208813f2e9db64c411001e5d3b0c98822059cda76d8f10440959d4edb1620880073a9d862c4110005b842a83882200287c85dcd65040090f90ea9aca0800317dcd53594100245f43c86b202000a3e8590d640400147b0b21ac8080122f21d43590100245f43c84b202000c3f759d5640400147d0b39ac8080028f61673590100051f428e6b202000a3d851cd640400155d0439ac808002ab60873590105871b886a6b2020b0e3510d4d640416347b0b29ac80800387d4e53590100070fc1aa6b2020b1e371054d6404163c6a20a9ac8082c28fa1453590100051fc2ae4b202000a3c855c9640400156902b92c8080028fa1472590100051ec28e4b202000a9e831c9640400153b06392c8080022fa1c52590100045ec38a4b202000a9e83149640400153b06292c8080028fa1732590100051ec2e64b202000e1d53cc96404001c3aa6992c808002ade0532590100055a40a64b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202000e8d320c9640400f17d0f98ac8080022f61f31590100051f42e62b202000a3d85cc5640400155d0598ac808002ab60b31590100051f42862b202000a3d850c564040095750018ac808002ae600315901003c5f43e42b2020008bd87c85640400147d0b90ac8080028f61721590100054f41e42b202000a9d83c8564040095750010ac808002ae60021590100245fc3ac9aa02000a3f8559354040091790eb22a8080023d20573588100162f39aa6b102000c5d7354d62040091d90e992c40800b331cd325881000726a9a64b10200487c8759552040091d90eb12a4080122f21376508100043fc2aeca10200987c855d942040091790eb2284080023d61b71508100065ab26e2a1020008f5861c5420400196ac838a84080132e9c164944100071ab26a32882000cb9645c2510400717909bb2a2080d22f61b74544100045f43ac8a8820078bc875915104001972c8b8482080db0f99375504101861f320eaa082045c76611d5410400187eeab2282080030f1d5645041002477c3ac51082000cd873dd9100400197709bb220080032e21376440100063da9eec8802000c7953dd910040018f6edbaa20080031edd875440100065dbb6e88802000cbb761d110040019b6edb9a20080033addb724401000675bb0e48802000af386545100400176708a8a2008002dce154144010
  | 1 => 0x8c8316a288003b118c62d45102c6f1380c5a8a2049c7671d965144001878e9b2aa2881271ddc765545102de3c386caa8a205a8be86dd1514400187ecbba2a2881e70f19774545100064e31ee8a8a2000cac62dd1514413917d0fb22a28813e2f21f64545100064fba6c6a8a2000c9c74d8d514400195ee9b12a2880032b1d362545100063db2ee0a8a2049c77519d851440134e90ca88a288156cd211511451024e3a32cec28a2000e5463d9451440a54eb0fb28a28816f1d61f65145100071bb2ec828a2000e37651905144001d28c6320a28800395d97631451000733b2ec428a2000e67651885144001d48c8310a288003b118c62145100071ba0ecb20a204fab581d924144001c68c9b2c82880038d190659051001d5b436c920a2000cb676d92414400156d0daa48288003a5193639051000752326c520a2000ce67618a4144001d48c83148288003b118c62905100055a4328520a205287e86dd5414406d878c9baa82880031718f755051000636316eaa0a205b87e861d54144061878c83aa82880031718c755051000636310eaa0a2055d34411d541440610fd0fb2a828816e1f21f65505100071a20ecaa0a203687e8719541440130f90e32a82880030fdd764505100061e3aec8a0a204fcb870d9141440018beebb1a8288003171d7635051000637baec4a0a2000c6c75d8941440932ed0fbaa82880db1d1db75505101863a3b0eaa0a205b976861d541440aba68c83aa82881265de0c7550510004bac18eaa0a2000d54631d541440aba6e803aa82882ca5da1f65505102de3a3b6caa0a2000e3464d9541440a52e90e32a828814b1d1d8655051001e5a3b6e8a0a2000d3475dd1414409f968edb2282880034d1d764505102ce6a3b6c6a0a2000d5475d8d41440959c8edb128288003591d762505102c6723b0c4a0a2000d64751894144001d48c83128288003b118c6250510006b83aee0a0a2000d73751c1414409fb66e838282880033518e768851000732316cb10a2000e646219621440011ed0dba44288003a918b64885100065b3b0c910a2000ea4621922144001d88c5b1c4288006b9a1b6288510006733b6c510a204ace870d8921440b78e8edb2a42880039918b65485102963a3b0ca90a20048f4865d121440932e90aba2428813f2d1db64485102d65a3b0c890a2000ea46219121440b39a8edb1a4288007391db7248510256723b6c490a204ade3721c121440138e8cb38ea0880022fe11765411001c5e422eca8220008df835d950440051b906bb2a0880023be09765411000c76412eca822000c7765dc550440018eeca38aa0880033918b71501100065bb20e2a022000ce4621c540440093690ea0a8088012ad21941501100059a42a82a022004bb08050540440010fd0dbaa40880030f19375481100062e31eea9022020
  | 2 => 0x8651891000536c18ca3122000e6571194624400195cedb20c4880038bd9764189100071632ec83122000ea571d9062440011db0f320c4880029ba16641891000536c2cc83122000aae84990624400159d07320c488002b360e641891000477c3ac83122000a6f8559062440014d90ab20c488002b3e0d64189100056641ac83122000aae86190624400195cec320c4880038bd94641891000716328c83122000ea5811906244001d4ae2320c4882d3a984064189105a752080c83122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000e8c64d8c6244001c9f0bb18c48800393217631891000762b8ec631220008ed8798c62440014dd0b318c4880029b616631891000557424c63122000aad8498c624400159d07318c4880023be1d631891000537c2ac63122000a6c8558c624400155f08b18c488002ab211631891000573c0ac63122000a6e8518c62440014db0a318c488002b3a186318910006673b0c63122000e4f6518c6244001c98ca318c488003a3d90631891000746320c63122000e4e8518c6244001c9b0a318c488003b1604631891000763388c63122000ec57118c6244167d8c20318c4882cfb1040631891000537436a63122000a6c86d4c62440018dceda98c4880038bd93531891000716326a63122000e4f63d4c6244001c98c7a98c4880029ba19531891000536432a63122000c6e7654c6244001c5ec8a98c4880038b191531891000727b1aa63122000e4c6354c62440015cd0d188c488003a919231189100076231c623122058ae4864c46244001d48c8988c488003b118d31189100247ac0ceda922049c74519db52440030f90abb6a4880022fe1176d491001c5e422eda9220008df835db52440051b906bb6a48800e2fa1376549100045ec26eca9220028de83dd952440011bb07bb2a4880021fe1576549100045fc22eca9220038bc845d952440011bf06bb2a48800a3720d765491000c3f43ecaa9220098ee87d8952440091ed0db8aa4880031dd9771549100065a326e2a922000cd463dc552440018eeca38aa4880032d19071549100066a318e2a922000ce7621c552440130fd0bbb284880021f61776509100146f41eeca1220008dd83dd942440010ff0abb284880261f21576509100045fc22eca1220008df835d942440051b906bb284880023be0976509100047bc0aeca1220018be87d9142440071dd0fb1284880039518f65d45102deb9386cba8a2049a7587d9751440018eb0fb2ea28813f2d9db64d45100071bb2ec9a8a204fdb270d9351440b596cec326a2880038dd9464d45100074a318c9a8a205adb27019351440b39acedb1ea28800395d9763d45102cee9386c7a8a204ace676d8b5144001ccecbb16a28812b789c362d45102c6733b0c5a8a2000e676518b5144001d4
  | 3 => 0x9b122000ae6811d362440955cb023a6c4880038bd5254d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000667b9ce7b122000a6e851cf62440014db0a39ec488002b9a0473d891025572c08e7b122000e4f5394f6244001c9f06a9ec48800393dcd53d89100072639aa7b122000a6e8590f62440014db0b21ec4880023ba1c43d891000476c3887b122000a6e8510f62440014db0a21ec4880029be1571d89100053642ae3b122000aaf845c7624400155908b8ec488002b3e0d71d89100056641ae3b12204a8ee87cc762440011db0f98ec4880029ba1731d891000536c2e63b122000aae84cc7624400155b0998ec4880029ba1431d891000536c2863b122000a6e85dc362440014db0bb86c4880029ba1740d891000536c2e81b122000a6e85cc362440014db0b986c4880031b18b755891000636310eab12200087e87d956244001878e9b2ac488003171cf65589100043f438cab122000c3c7419562440018b8e632ac4880030fd9774589100061e32ee8b122000cac62dd1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c7319162440051bd0db9ac48800317d9773589100062e32ee6b122000c9f64dcd6244001938c9b9ac4880033318b73589100046f43ec6b122000c5f75d8d62440018b8ebb1ac48800327dd363589100064e3a6c6b1220008de8718d62440018beea31ac488003171d463589100064fba0c6b122000c9c7418d62440130fd0fbaac4880021f60f755891001c5f43ee8b122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b1220028de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bf0bb9ac4880031721773589100043fc2ae6b12200987c855cd624400117f08b9ac48800e2f211735891000477c12e6b1220008f7815cd62440011bd0e39ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880021fa1f535891004c3e43ea6b122000c3f74d4d624416d878e9a9ac48800317dcf53589100162e39ea6b12200087e8754d62440010f90ea9ac4880030fdd153589105ae1e3a2a6b122000c5f7354d62440058b8e6a9ac4880031bdd77258910006363aee4b122000caf74dc96244001958e9b92c48800333dcf72589100066639ee4b122000cb474dc562440019a8e7b8ac4880031b9db651891000536c1eca3122000e6581d946244001ccae3b28c4880023b61e65189100053742cca3122000aae84994624400155b09328c488002b3a0e651891000566c1cca31220008ef87594624400155f08b28c488002ab211651891000567c1aca3122000acc8359462440014dd0c328c4880031b9d
  | 4 => 0x34400159f04b26c688002b320964d8d100054f430c9b1a2000c9e761936344001c3eca326c6880038719464d8d100070fba8c9b1a2000e1c751936344001d2b02326c68800297a1662d8d100052ec2cc5b1a2000a9e8498b634400153b09316c688152b5a0775d8d102cd6ac0eebb1a2000e5681dd76344001cab03baec68800297a1675d8d100062eba8ebb1a2000a5e871d763440018bd0e3aec68800297a1674d8d100052ec2ce9b1a2000ace829d3634400159b053a6c68800297e1574d8d100052e42ae9b1a2051ad6811d363440b35ab023a6c68800387d5254d8d100062fbaee5b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a2000ccf729cb63440014bf0ab96c6880029721572d8d100062fbaae5b1a204cad6811cb63440b35ab02396c68800237a1c52d8d100046ec38a5b1a2000a9e8414b634400153b08296c68800237a1c42d8d100046ec3885b1a2000a5e8510b63440014bb0a216c68816637a1f21d8d100046ec3e43b1a2000a5e85c8763440014bb0b90ec688002a7a1321d8d100054ec2643b1a2044ad681dc363440014bd0ba06c6880029761740d8d1000666196e7b122000c5f7354f62440058b8e6a9ec4880029ba1732d891000536c2e65b122000e4d53ccb62440051df0e996c48800b339cd32d891000726a9a65b122000a6d83d976244001ccb03b2ec488002aba1265d891000556c24cbb122000ace83997624400159b0732ec488002abe1165d891000556422cbb122000acf83597624400159906b2ec4880029b60c65d891000717b2ec9b122000e2c65d9362440014dd0b326c4880029b61664d89100056741cc9b122000acd8399362440014df0ab26c4880029b21564d891000567c1ac9b122000acc835936244001c5eca326c4880038b19464d891000752c08c9b122000e4f65d8f6244001c98cbb1ec488003a3d9363d891000746326c7b122000e4f85d8f6244001c990bb1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec4880029ba1463d891000536c28c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000e4e8518f6244001c9b0a31ec488003b160463d891000537436a7b122000a6c86d4f62441718dceda9ec4880038bd9353d891000716326a7b122000e4f63d4f6244001c98c7a9ec4880029ba1953d891000536432a7b1220b7c6e7654f6244001c5ec8a9ec4880038b19153d891000727b1aa7b122000e4c6354f6244001d88c718ec48812ab921931d891025572c0eebb122000aae849d7624400155b093aec488002b3a0e75d891000566c1cebb122000a6e859d362440014db0b3a6c488002b3a0e74d891000566c1ce
  | 5 => 0x800317dcf53591100162e39ea6b2220b8c6c72d4d64440010fd0ea9ac8880021f21d53591100062fb9aa6b222002c5c7354d644416f8d8e4a9ac8880063ba1f725911000637baee4b222000c6c75dc9644400195ee9b92c88800333dcf72591100066639ee4b222000c6f53dc964440018daa7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc725911000672396e2b222000c3e76d94644400147b07b28c8880038d60765191100071ab8eca32220008bd87994644400147d0b328c888002a7a0e65191100054ec1cca3222000aae82994644400155b05328c8880022fe1d65191100054fc1aca3222000a9c83594644400155f04b28c888002ab20965191100051f430ca3222000c3e76194644400147b06328c8880038d5c465191100045ec3cc63222000a3e8598c644400147b0b318c888002aba0a631911000556c14c632220008bf8758c644400147f0ab18c8880028f215631911000557c12c63222000aac8258c644400147d0a318c8880028f61463191100070fb28c63222000e1c6518c6444001c3d0a318c8880038761463191100074ac08c63222000e967118c6444001d2ae2318c8880028fa1b53191100051e436a63222000c3e76d4c6444001c3ec7a98c8880038718f53191100051f432a63222000a3c8654c644400187ceca98c88800387d8d53191100070e31aa63222000a3e85988644400147b0b310c888002a7a0e62191100054ec1cc43222000e94638c464440b55690c988c888003a518d31191100061f2a4edaa220048f5819db54440070f90abb6a88800237e0d76d51100146e41aedaa220008ef825db54440031d904bb6a88800e8f21365d51100051ec2ec9aa220028de83dd954440011bb07bb2a8880063ba0b765511000476c16ecaa2200087f855d954440011bf06bb2a88800a3720d765511000477c12ecaa220018ec825d954440070fd0fb2aa8880262fa1f64551100247b436e2aa22000c7765dc554440019a8c7b8aa8880033918b7155110024f9406e2aa22000c77651c5544400196ec838aa8880033518c715511000672310e2aa22000a5e86dd763440018bcedbaec68800297a1875d8d100062f3b0ebb1a2000c5e76d976344001cab03b2ec6880023761e65d8d100052f42ccbb1a2000a9e84997634400153b0932ec688002b3a0a65d8d1000566c14cbb1a20008df87597634400153f08b2ec688002a721165d8d1000567c12cbb1a2000acc8259763440014bd0c32ec688003179d865d8d100064f3b6c9b1a2000e1f65d936344001c38cbb26c68800387dd764d8d100070e3aec9b1a20008dd8799363440014bd0b326c6880029761664d8d100054f424c9b1a2000ace82993634400159b05326c68800237e1d64d8d100052fc2ac9b1a2000a5c855936
  | 6 => 0x52f41e4232a2000a5d83c8465440130fd0fa00ca880021f61f401951004c3f43e6032a200087d87cc0654400147d0b21ec8880028f61643d91100145fc3a87b222000a3d83d976444001c6b03b2ec888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec888002a7e0d65d91100054e41acbb222000aaf82597644400155904b2ec8880028f60c65d91100051f42cc7b222000a3d8598f644400155d0531ec888002ab60a63d91100051fc2ac7b222000a3c8558f644400155f04b1ec888002ab20963d91100051f428c7b222000a3d8518f6444001c3eca31ec8880038719463d91100070f428c7b222000e1d8518f6444001d2b0231ec8880028fa1b53d91100051e436a7b2220b6c3e76d4f6444001c3ec7a9ec8880038718f53d91100051f432a7b222000a3c8654f644416b87ceca9ec88800387d8d53d91100070e31aa7b222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b222000e94638c7644409f5690c98ec88813ead60775d91100061eba8ebb222000a3e859cf644400147b0b39ec888002aba0a73d911000556c14e7b222000a3e851cf644400147b0a39ec888002ada0473d911027d5ac08e7b222000e1f5394f6444001c3f06a9ec8880028fa1672d91100051ec2ce5b222000a9e839cb644400153b07396c888002ada0472d911027d5ac08e5b2220008be8714b644400117b0e296c888002a7a0c52d91100054ec18a5b222000a3e85ccb644400147b0b996c8880038754f32d91100070ea9a65b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000e8d320cb644409f17d0f98ec8880022f61f31d91100051f42e63b222000a3d85cc7644400155d0598ec888002ab60b31d91100051f42863b222000a3d850c7644409f17d0f90ec8880022f61f21d91100051f42e43b222000a3d85c87644400153d0790ec888002a760f21d91100051fc2ae1b222000a3c855c3644400147d0b986c8880028f61730d91100061e326eab222000c3c641d564440010fd0fb2ac888003171cf655911000636396cab22200087e8719564440018b8e632ac8880031b1c865591100062fb2ee6b222000c5c65dcd6444001938c9b9ac88800317dd463591100062e3a8c6b222000ccc7218d64440018decbb92c8880031b197725911000656326e4b222000ccc63dc964440130fd0fbaac8880021f60f75591100061fbaee8b222000c3c75dd164440051bd0fb9ac88800317dd773591100062e3aee6b222000c9f74dcd64440018bf0bb9ac8880031721773591100043fc2ae6b22200987c855cd644400117f08b9ac8880023be09735911000c76412e6b2220008de871cd64440018beea39ac888003171d473591100064fba0e6b22200087e87d4d64440130f90fa9ac88
  | 7 => 0x6e82cc765440014db0598eca880021fa1c31d95100043ec3863b2a205b87e87c8765440010fb0f90eca880028fa1321d95100051ec2643b2a2000a5e83c8765440014bb0790eca880021fa1f40d95100043ec3e81b2a200087e87cc365440010fb0f986ca880030f9d365995100062f39ecb32a2000c6e72d96654400187ecaba4ca880270f19574995100062fb2ae732a2009c5c655ce654400193ce831cca88003275d0639951000667390c732a2000c6f655ca65440138d8cab94ca880033318d72995100064fba0c6b2a2000c9c7418d6544001998e431aca880033318f72595100061fbaee8b2a2000c3f751d165440018beebb9aca8800327dd373595100064e3a6e6b2a2000c5f85dcd65440010ff0ab9aca880022fe11735951001c5e422e6b2a20008ef825cd65440031d904b9aca8800317dd473595100064fba0e6b2a2000c9c741cd65440010fd0fa9aca880030fdd353595105b61e3a6a6b2a2000c5f73d4d65440058b8e7a9aca882e31b1cb53595100143e43aa6b2a2000c3f7454d654416b878e8a9aca8800317dcd53595100162e39aa6b2a20b7c6c7254d65440018deebb92ca880032bdd37259510006563a6e4b2a2000ccf73dc96544001998e7b92ca880031bd4f725951000636a9ee4b2a2000c6f751c9654400195ee8392ca880032b1d0725951000667b98e4b2a2000ccc731c965440091eb033b0ca880021fe1d65195100051fc22ca32a2000a3c8459465440014bf06b28ca880029720d651951000537c12ca32a2000a6c8259465440a54eb033b0ca880021f60e76195100052f41cc832a2000a5d8399065440014dd05320ca880029b60a64195100043f436e632a200087f87d8c65440018bae7b18ca880021f61e63195100051f424c632a2000a3d8498c65440014dd05318ca880029b60a63195100043fc3ac632a2000a3f8458c654400147908b18ca880029be09631951000536412c632a200087d8718c65440018bae6318ca880031761c63195100072ac08c632a2000a3e84988654400147b09310ca8800297a0e62195100052ec1cc432a2000e54638c465440a54e90c988ca880261fe0d731951004e2fc1ae632a200987e8790c65440010fb0f218ca880261fa1c43195100043ec388632a2000a6e8210c65440014db04218ca880261fa1c42195100043ec388432a2000a5e8310865440014bb06210ca880261fa1f32195100043ec3e6432a2000c5d73cc865440018bae6990ca880261fa1c32195100043ec386432a2000a3e840c8654400147b08190ca88003934c8321951004c3f43e6232a200087d87cc4654400147d09988ca880028f6133119510005374166232a2000a6d82cc465440130fd0e188ca880021f61c311951004c3f43e4232a200087d87c84654400147d09908ca880028f61321195100
  | 8 => 0xb3b2858800a37a0e7650b100046ec1ceca1620018be87d9142c400355d05b2285880026de1176d47101b51e422cb28e2030a3c8459451c40cf66908a88a38819ecd21165147100055ac36a920e2030c3c641d541c40cfa68823aa83880122fa1f64507100061e3aec8a0e2067d34641d541c408b2ef063aa83880025d60c755071033e9ba00eaa0e2000d3475dd141c4001a68ebb228388002ec60364507100247ac36e910e20009b584dd921c408b2e90aba2438816e1fe1d65d431004e3b32ce3a8620049b48750540c40016690aa0a81880121fa1e54596100061fba4a8b2c200487c8754d65840018bee6a9acb0800317dcd53592100162e39aa6b2420048bc8750d648400917f0eb26a9080028fe1564d52100045fc22e6b1420038bc845cd62840091d90e992c50800b331cd3258a1000726a9a64b14200487c8759552840091790eb2285080032d5937150a102943fc3acba8c2000c3c74595518406187cc83aa83080030f1d564506105ce6ab88c7b2a2000c3d7495365440014eb032a6ca880029e60254d95100247ac0ee7b2a2000c5f73d4f65440058b8e7a9eca882c31d5c753d95100062eb9ca7b2a2000a758194f65440050ff0ea9eca88003175cd53d95100053bc0aa7b2a20b1c757154f65440014eb03296ca880028fa1052d95100051ec20a5b2a2000a5e8314b65440014bb06296ca8800297a0e64d95100052ec1cc9b2a2000a6e8299365440014db05326ca88003175cf63d95100051f424c7b2a2000a3d8498f65440014dd0531eca880029b60a63d95100051fc22c7b2a2000a3c8458f65440014df04b1eca880029b20963d95100062eb98c7b2a2000c5d8718f6544001cab0231eca880028fa1262d95100051ec24c5b2a2000a5e8398b65440014bb07316ca880039518d71d95100072a31c63b2a205ba74864c76544001ca8c698eca8816e9d60774d95100061eba0e9b2a2000a76811d365440b74eb023a6ca8816e9ea0074d95100053cc00e9b2a2000a7681dcf65440b74eb03b9eca880031da0773d95100063ac0ee7b2a2000c5f835cf65440018bae639eca880029da0473d95102dd3ac08e7b2a200087e8790f65440010fb0f21eca880021fa1c43d95100043ec3887b2a2000a6e8210f65440014db0421eca8816e9d60772d95100051f424e5b2a2000a3d849cb65440014bd07396ca880029760e72d95100053b408e5b2a205ba75811cb65440010fd0e216ca880021f61c42d95100052f41885b2a2000a5d8310b65440010fd0f996ca880021f61f32d95100062fb9e65b2a2000c5f734cb65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb6544001c9a64196ca880031ddcd71d95100063ab9ae3b2a205b87e87cc765440010fb0f98eca880028fa1331d95100051ec2663b2a2000a
  | 9 => 0x53591200062fb9ea6b224002c5c73d4d64480010fd0ea9ac8900021f21d53591200062fb9aa6b224002c5c7354d64480051790ea1ac89000b271cd43591200147643a64b224002ccc734c96448001c9aa6992c890003a350d32591200063bbaee2b224000c7475dc564480019aee7b8ac890003351cf71591200063ba9ee2b224000c7553dc564480018eeea38ac8900031d1d471591200065bba0e2b224000cd7731c564480019a8e638ac89000339dc871591200063ba98e2b224000c75531c5644800196e8638ac8900032d50c715912000673190e2b224000ce5321c564480070f90abb6a8900021fe1576551200046fc1aecaa240028dc835d954480011ef02bb2a8900023d205765512001c3f43ecaaa24000ab684cc761480010fd0fb2ac2900030f1d365585200062e39ecab0a400087e871956148001878e832ac290003171cc65585200061fb2ee8b0a4000c3c65dd161480018becbb9ac2900031719773585200047bc3ac230a4000ab48458461480015a906b08c2900021fe15741852004c3e42ae830a4002c5e7354c61480018bae6a98c29000b331cd321852000726a9a6430a4000af180104614800156d09988c290002b960b3118520007629906230a40038be849d9514800117b093b2a2900261f21476545200061e3a6caa8a4000c3f65dd151480f3878cbba2a2901b21fe15761452000c7c432e028a400087f855da41480130f90abb482900261fa1776505200043ec2eeca0a400987e859d941480010fb0b3b282900021fa1b75505200043f430eaa0a400087e87d9541480010f90fb2a82900021fa1c655052004c3e438caa0a4020c6c72d9550480018decbb92a09000a1fe1d53d97100062eb9aa7b2e20048f4815da65c400717d0fba2cb880022fe11735971001c5e422e6b2e20048f4815cd65c400187ee9a9acb882db0f1d353597105863a38ea6b2e200287c8754d65c400187ee8a9acb882d70f1d153597100062fb9aa6b2e20b1c747154d65c400147b08292cb880029760c52597100065bba0e2b2e2000cb4741c565c40010ff0eb28cb8800b179cd53d93100062eb9aa7b2620028bf8750f64c400593ce6a1ec98800e1fa1676d53100247a40aedaa62003a3c8459754c400147b0bb26a9880022fe11765531001c3e43acaaa620048f5861c554c40130ff0ebaec5880021fe0d75d8b1004c3f42ee7b16200087d85dcf62c400717d09b9ec5880022f61373d8b1004c3fc3ea7b16200087d87d4f62c40010ff0ea9ec5880021f61d53d8b1001477c3a65b162002cce734cb62c4001c9aa6996c5880061f21576d4b100045fc22eda9620038bc845db52c40091e902bb6a5880021f61f65d4b100043ec2ceca9620008bf845d952c400717908bb2a5880061fa1f6554b100247ac30e2a96200987e859d942c40010fb
  | 10 => 0xa0c40048f48758541880018e8eab0a83101623be1d618862000567c1ac310c4000c3d7495365480018bae729eca900029b60a53d95200143fc3aa7b2a4000c5d7354f65480018bae7b1eca900028fe1163d95200051e422c7b2a4000a778158f65480014e902b1eca900028fa1063d95200051ec20c7b2a4000c5d7318f65480d94d90c996ca9000353dcd32d95200072631a65b2a4000c3d741d365480018be65b9eca90003174cb73d95200043ec3ce7b2a4000c5f835cf654800147d0839eca900028f61073d95200062eb98e7b2a4020a6e821cf65480d94db0439eca900021fa1e43d95200043ec3c87b2a400087e8710f65480010fb0e21eca900829ba0843d952000536c1087b2a4000a3e84dc7654800147b09b8eca900021fa1f31d95200043ec3e63b2a4000a3e84cc7654800147b0998eca900829ba0b31d952000536c1663b2a400087e870c765480010fb0e18eca900821fa1f40d95200043ec3e81b2a402087e87cc365480010fb0f986ca900021fe1573595200045fc22e6b2a40038bc845cd65480011ef02b9aca900023d20573595200047dc02e6b2a400087e87d4d65480050f90ea9aca9000317dcd53595200043fc3aca32a400087e86dcc65480010ff0fb18ca90003175cf63195200043ec3cc632a400087f8758c654800147f08b18ca900028f21163195200053bc0ac632a4000a748158c65481754f700b18ca900021f61c63195200051f420c632a4000a3d8418c65480018bae6318ca901ae9b2193219520006a6b9a6432a4000e4c634c865480130ff06b98ca9002717e0d73195200062f992e632a4000c5d325cc65480018bc60b98ca90003170c1731952004c3f43c8632a400087d8790c65480018bae7218ca90003175cd431952004c3f4388632a400087d8710c65480354dd04218ca900029b608431952035d3d4008232a4000a798010465480130fd0f988ca900021f61f31195200051f4266232a4000a3d84cc465480018bae7988ca9006a9ba0b311952000536c166232a4000c5d734c465480130fd0e188ca900021f61c311952004c3f43e8032a400087d87d0065480130fd0f980ca900021f61f30195200166639a65b224000e4d534cb6448001d1c86996c8900021fa1f65591200062e39ecab22400087e8719564480018b8e632ac89000317d9773591200062e32ee6b224000c7765dc564480018e8cbb8ac8900031dd9471591200063a328e2b224000cb4641c564480130fd0fbaac8900021f60f75591200146f43ee6b224000c5f75dcd64480018b8ebb9ac89000317e1773591200062e42ee6b22400087f855cd64480130f90ab9ac8900022fe1173591200047bc0ae6b2240008f4815cd64480011bd0e39ac89000317dd473591200062e3a8e6b224000c9f741cd64480010fd0fa9ac8900261f21f
  | 11 => 0x900b596f0eb0c83200038dd4d61906400071aa9ac320c80048f58798621900091e90eb0a43200032ddd161486401151f42ae9b2a80048bd84dcf655016187ae9a9ecaa000a1fe1d53d95400051fc22a7b2a80b1c3d7454f65500018bae6a9ecaa00028f61252d95400051ec20a5b2a8000a5d8314b65500018becab9ccaa002717195739954000477c12e6b2a80018ec825cd65500011ef02b9acaa00023d20573595400143e43aa6b2a8000c5f7354d65500058b8e6a9acaa00021fe1d65195400fd1ec3ecbaa28000c3d87d9754500b51790cb8ea8a000317dcd53d89400162e39aa7b128002c9c7350f62500010ff0ab8ec4a00261f21571d894000c5e422e3b1280008df835c762500051b906b8ec4a000339188715894000c3f42ceda9280048bd849db52500e587ea93b6a4a00021fe1d65d494000c3e43acaa928072c3c75d9542500031790eb2a84a0006ab209655094000d57436c4a12805a8be86dc542500011ef0eb08c2a0002b920961185400055bc0a8430a8000ab584c84615000917b093b6a2a000237e0d76945400146e41aed28a8000c3f655d251500071f10cb84a2a000e2f21076545401849f43eeaa0a807293f831d5415000127b063aa82a00c30fd8075505401869db00eaa0a80118be871854150001878ea30a82a00034e1d770505400069dba8e0a0a80048bc865d121500e52790aba242a01ba1f61f65d41400061fb2ee8a82800487c8754d65880018bee6a9acb1000317dcd53592200162e39aa6b2440048bc8750d6488005938e6a1ac91000e1f21576d52200245fc3ac9aa44000a3f8559354880070fb0bbb2a9100022fe11759862001c5e422eb30c40048f5878c661880010fb07baac31016f1d607755862001c5f43ee8b0c4000c3f75dd16188001878ebba2c3100030fdd474586200061e3a8e8b0c40028de87dcd61880018beebb9ac310003171d773586200064fba6e6b0c4000c9c74dcd61880018bf0bb9ac3100031721773586200066610ee6b0c400087f855cd61880130f90ab9ac3100022fe11735862001c5e422e6b0c4000c5f751cd61880018b8ea39ac31000327dd073586200064e3a0e6b0c400087e87d4d61880130f90fa9ac3100030fdd353586205b61e3a6a6b0c4000c5f73d4d61880058b8e7a9ac3100021fa1d53586200043e43aa6b0c4000c3f7454d618816b878e8a9ac31000317dcd53586200162e39aa6b0c4002cd4738c561880091e90e98ac3100029de1561d462000672b92c3a8c40008bf845d9518800717908bb2a31000237e0d76546200146e41aeca8c4000a778558451880010ff0abb483100261f21576906200247ac3cc320c4003ab48458641880010ff0abb283100261f21576506200046fc1aeca0c40028dc835d9418806187cc83aa83100030f1d564506200063a3acc2
  | 12 => 0x29d61442586500056b41884b0ca000ad58310961940934ed0b992c3280029d61732586500072aa9e64b0ca000e55534c961940934ed0a192c3280029d61432586500055b42064b0ca000ab5840c96194001d8a64192c3281cb8dd4564946500265d382c928ca000cb9645c251940019e4c2b84a3280db0f991749465024eb938ae128ca0008bd86dd151940011790eb22a3280032ddd261546500065a3a4c2a8ca000cb7745855194001968e8b0aa3280033c58770546501843fc32e828ca02087f8758851940418dce4b10a3281271ddcd61146500063ab9ac228ca000c3d76d5241940091eb0f30c83280122f21376506501b61f326eaa0ca000c3f7559141940e5878eab2283280031ddd6615065022e3a3acc2a0ca0048f48758541940938e8eab0a83280025ee0175886500247ac3cc310ca045c767598621940018eaeb30c43280030f99375486500247a43ac290ca049c747558521940018bee6a9ec4a80061f21571d89500045fc22e3b12a0038bc845c762540011bf06b8ec4a800a3720d71d89500047bc3ac230aa0038be84dcc615400117b09b98c2a81263d61f619455022c7b438c2a8aa000ab581d9241540130f90a3b282a800317dcd53590500245e43a86b20a01a87c8755162140130f90ab9ac4280022fe11735885001c5e422e6b10a0008f7815cd62140011e902b9ac4280123e20173588500d43e43aa6b10a0048ec874c96214005998e6992c4280039354d32588500257440264b10a00187d85dc562140011ef02bb284280023d20576508500245e43ac8a10a00993c8755142140091d90eb1284280038b55162508500247ac3c63308a0038be87dd161140f3878ebba2c2281e78d14774584503ce1fa9ee8b08a09cc3c751d16114139c68a23a2c2280261f21573584500045fc22e6b08a0038bc845cd611400187ee8a9ac2282d70f1d153584500062fb9aa6b08a000a748154d61140134e90b18ac2280123d21d315845004d3a42a62b08a009c76715da511406d0ff0cba4a2280db0f99174944500d43fc3ac5288a01ac6e7258a511406d47908b0ca2281e70fd5176904500247ac3cc3208a003ab484586411406d0ff0abb282280270f1d5645045004e3a3acc2a08a0048f48758541140138e8eab0a82280123d61e61884500045fc22ec908a0038bc845d921140091e90eb0a42280271d1d561484500243e43aa6b2c8000c5f7354d65900011ef02b9ac5200023d2057358a400247643a64b148002ccc734c96290001c9aa6992c5200261fa177158a400043ec2ee2b148000cb441dc562900090f90eb2aa5200123d61e31986400062fb9aa6b0c8002c5c7354d61900091e90e98ac320002ade1131586400053bc2ac3a8c8000cb57458751900091f501bb4a3200029de0565946402d45fc3ac320c800fab78758641
  | 13 => 0x55cc0042b24a036c3e649c75494001972c9b82a9282bf4edd370552501043f43ea8b14a02087e87d4d62940018bae6a9ac5280123b21d3258a500166639a64b14a000e4d534c9629400717d09b8ac5280022f6137158a50004bcc06eaa14a0048bc87591429400187eeab2285281cb0f1d56450a5000d56412c8a14a00993c87551429400747f0caa285280029d61441986500053ac2e6330ca000ab684cc6619400156b0998cc328002b9a0b319865000572c166330ca0048f5878c661940014eb0a18cc3280029d61721986500055b4264330ca000ab584c8661940015ad0790cc328002b560f21986500053bc2ae930ca045a76851d261940014eb0a3a4c3281178dd52549865022d3b42ce730ca000a75859ce619400156d0939cc328002ad612739865000573414e730ca000ae5829ce619408b4ed0a39cc3280029d614739865022f2ba9ca730ca045e578354e619408b4ed0b21cc3280029d616439865022d3b4288730ca000a758510e61940015cd0421cc328002b960843986500053ac2ee530ca045a76859ca61940014eb0b394c328002ada1272986500055ac24e530ca000ad6839ca61940015ab07394c328012bca00729865000578c00e530ca000a778550a619408b4e90aa14c3281169da1442986500053ac288530ca000ad68310a61940015ab06214c3281169da1732986500053ac2e6530ca000e5553cca6194001caaa6994c3281169da1432986500053ac286530ca000ab6840ca619400156b08194c328003b14c832986500062fb9ea6b0ca002c5c73d4d61940014e902a9ac3280029d61741586500053ac2e62b0ca000ab684cc5619400156b0998ac328002b9a0b315865000572c1662b0ca0048f4874c561940014eb0a18ac3280029d61721586500055b42642b0ca000ab584c8561940015ad0790ac328002b560f21586500055bc22eab0ca000ab4845d561940015af06baac328002b520d755865000573c12eab0ca000ae4825d561940934ed0b3a2c3280029d61674586500056b41ce8b0ca000ad5839d161940015cd053a2c328002b960a74586500053bc2ae8b0ca049e375495161940095e5012a2c328002bc602545865024d3b42ce6b0ca000a75859cd619400156d0939ac328002ad612735865000573414e6b0ca000ae5829cd61940014ef0ab9ac3281269d215735865024d3b428e6b0ca000a75851cd61940014ed0fa9ac32800395dcf53586500072a39ea6b0ca049e575394d61940014e90ea9ac32812795e0d535865024d3b42c86b0ca000a758590d61940934ed0a21ac3280029d61443586500057341086b0ca000ae58210d61940934ed0b392c3280029d61672586500055b424e4b0ca000ab5849c961940015ad07392c328002b560e72586500053bc2ae4b0ca049e675294961940934ed0a212c328
  | 14 => 0xc65dcd60504018decbb92c0a08031b19772581410047dc3ac030282038be84dcf658840117b09b9ecb108023da0773d96210247d406e7b2c42008f980dcf65884050ff0ea9ecb10803175cd53d96210143e43aa6b2c4200c5f7354d65884010ff0eb28cb1080b179cd53d92210062eb9aa7b2442028bf8750f64884051df0e996c91080b339cd32d922100726a9a65b244200e8d434cb648857756d03ba2c9108022fa1e43592210166739a64b244200e4d534c96488401d1c86992c9108261fa1770592210043ec2ee0b2442008f6819d954884018dacab94a31080317dcd53582210162e39aa6b044202cce734c96088401c9aa6992c1108023ee1d60182210061eba4a9b2a420287f8754f65484018bae6a9eca9080e2fa1f74595210061fba8e8b2a42008bf845cd654840717908b9aca908023de0573595210047dc02e6b2a42048f8805cd654840187ee9a9aca90adb0f1d353595210143e43aa6b2a4200c3f7454d654856b878e8a9aca9080317dcd53595210065a3a6e2b2a420087f87594654840147908b28ca9080b179cd53d91210062eb9aa7b2242028bf8750f64484010ff0ab86c8908261f21570d91210061e320eab22420987e87dd564484010fb07baac8908030f1d774591210043fc2ae6b22420987c855cd64484011f700b9ac8908123e20173591210043f43ea6b22420987c87d4d64484010fd0ea9ac8908021f21d53591210063a3aee2b224200a3d85d9354484010ff0abb2a8908022fe1176551210047bc0aecaa24236a3c845965148401878e9b2aa2908021fe1d65145211851e422ca28a42018bf8759241484f34790ab2482908c30f19075505210061e3aec8a0a42008bf845d7604840717908baec0908023ee1d601812104c5f43c86b26a0038be84dc562d400117b09b8ac5a800a37a0f7158b500046ec1ee2b16a0018bc8759142d40018bae6a9cc3a80121f21576507500051ec2c86b24a0048bc8750d6494005938e6a1ac9281ca8fa1673592500051ec2ce6b24a022a3e851cd649400147b0a39ac928003275cc735925000557410e6b24a000aad821cd64940e5c3ea729ac9281cb87e0d53592500051fc2ae4b24a022a3e851c9649400147b0a392c928002a7a0c72592500054ec18e4b24a000cad721c964940e5c5ea5292c9281ca8fa1732592500051ec2e64b24a000e1d53cc96494001c3aa6992c9280022fa1c32592500045ec3864b24a072a3e850c9649400147b0a192c928003a34c832592500051fc2ae2b24a0008be87cc5649400117b0f98ac9281ca8fa1731592500051ec2e62b24a000aae82cc5649400155b0598ac9281ca8fa1431592500051ec2862b24a0008be87c85649400117b0f90ac9281ca8fa1721592500051ec2e42b24a000a9e83c85649400153b0790ac928012aea00215925000
  | 15 => 0x2386caa08021fa1f30d95410043ec3e61b2a820087e870c365504010fb0e186caa08da8fa1030d95410051ec2061b2a8200a6e820c365504014db04186caa08029da0430d95410053ac0861b2a820087e8708365504010fb0e106caa08da8fa1020d95410051ec2041b2a8200a5e8308365504014bb06106caa08029da0420d95410053ac0841b2a820087f855cd655040117f08b9acaa08023de0573595410043f43ea6b2a8279c3f74d4d65504050f90ea9acaa08030fdd153595410062fb9aa6b2a820087f8759465504010fd0db98caa08021fe1f63195410062eb9ec632a820087d8798c65504014dd05318caa08029b60a63195410043fc3ac632a82c1a778158c65504010fb0e318caa0803175cc63195410052f41cc432a8200a5d8398865504130ff06b98caa082717e0d73195410062fa1ae632a8200c5c435cc655040187882b98caa08030fd01731954104c3f43e6432a820087d87cc865504018bae7990caa08028fe1132195411851e4226432a8200c5d734c865504014ef02990caa08029d205321954104c3f4386432a820087d870c8655046147d08190caa08028f6103219541007269906432a820987e87cc465504010fb0f988caa08c28fa1331195410051ec266232a8200a6e82cc465504014db05988caa0b038d10731195410062eb9c6232a8200a3f844c4655046147908988caa08261fa1c31195410043ec386232a8200c5d730c4655057fc6882188caa08261fa1f21195410043ec3e4232a8230a3e84c84655040147b09908caa080297a0f21195410052ec1e4232a82bee3441c84655057bc6882108caa08261fa1f30195410043ec3e6032a8200c5d73cc0655046147d09180caa08028f61230195410053b40c6032a8200a75818c065504018bae6980caa08261fa1c30195410043ec386032a8230a3e840c0655040147b08180caa08029ba08301954100536c106032a8200a76810c065504014eb02180caa08261fa1c20195410043ec384032a8230a3e84080655040147b08100caa080297a0c20195410052ec184032a8200a768108065504014eb02100caa080e3d60773d894101477c3a65b128202cce734cb6250401c9aa6996c4a08021fa1f65589410043f438cab1282bcc777119562504030f90abb6a4a09e62fe1176d494100c3f43ecaa928209c3c655d3515046d4ed0da8ca2a08dacda1351945411b61e3a6caa8a8200c3f65dd151504f3878cbba2a2a08c28fa1b65905411b71bb0ecb20a8279a3f83196415040147b0632c82a08c30f9c465905411871b388cb20a82038bc865c24150401878cab8482a093f2e181709054127e1fb24eb3028255c757119660504010fd0fb2ac0a0803171cf655814100636396cab02820087e8719560504018b8e632ac0a08031b1c865581410062fb2ee6b028200c5
  | 16 => 0x3191510051f436a6322a200a3e8654c64544014790ca98c8a880387d8d53191510051ec2cc4322a200a9e83988645440153b07310c8a88032dd9071551510062fb9aa7b12a2028ef874cb625440599ce6996c4a88039354d32d89510045f43ec8b12a2008be871916254401968c9b8aa4a88032d190715495100c5f43ec8a12a236a3e86d9251544f3c6ec3b24a2a88d22f21b74581510045f43ec8b02a200c9c73d916054401958e5b22c0a88022fa1c64581510064e398c8b02a200cac72191605440193ec9b9ac0a880327193735815100657b26e4b02a200cac64dc960544011f70eb00c0a88261f21573590511843e43aa6b20a2098be8790d64144070fb0bb82c8288c21f21d645485100c5e43ac8a10a200cb5641c542144010ff07bb2a2288021f60f76544511849f43ee8a88a200c3f76dd1511440187eec3a2a22894a1f21d53580510062fb9aa6b00a252a788054d60144a50f90ea92c0288023da0773d96410143fc3aa7b2c8202c5e7354f65904018bae6a9ecb208d28f21774596410143e43aa6b2c8200a3f8454d65904018bee6a9acb208021fe1d651964104e2f32ae632c8200c5d655cc65904f3a38a8b98cb208da4fe1d65d52411b51fc3acbaa48200c3f87597549047317f0cb8ea9208e66de1971d52414e65bc32e3aa48279d37535c75490401a6aa6b8ea92080e3d2057358a410162f39aa6b148200c5d7354d62904030f90abb6a5209e70fd5176d4a4100c3f43ecaa9482018be87d95429044f17b0db8a85208030f59574946411b59a426a328c82349b581dd1519040187d09baac1208030f61375582410043ec1eeab048200c3f42dd560904018ed03baac1208031d60775582410061fbaea8b04820087f855cd60904130f90ab9ac1208021fa1f535824104c3e43ea6b04820087e8754d60904010f90ea9ac1208030fdd542582410047dc3ac03048200c5d7394f65504050ff0ea9ecaa0803175cd53d954100636b94a5b2a8200a3d8414b65504014bd06296caa08029760c52d95410062eb9ec7b2a8200a6e8298f65504014db0531ecaa0803175cc63d95410052f41cc5b2a8200a5d8398b65504010fb0f39ecaa080317e0d73d95410062eb98e7b2a8236a3e849cb655040147b09396caa080297a0e72d95410052ec1ce5b2a8200c6d721cb65504010fd0f996caa08021f61f32d95410062fb9e65b2a8200c5f734cb65504010fd0e196caa08021f61c32d95411b51f42065b2a8200a3d840cb6550401c9a64196caa08da1fa1f31d95410043ec3e63b2a8236a3e84cc7655040147b0998ecaa08029ba0b31d954100536c1663b2a820087e870c765504010fb0e18ecaa08da1fa1f21d95410043ec3e43b2a8236a3e84c87655040147b0990ecaa080297a0f21d95410052ec1e43b2a8200a3d841c3655046d4eb0
  | 17 => 0x2a8400cb7741c565508018eea638acaa10031d54c71595420043fc3aca32a8400a7481594655080317b09b9ec2a12e30f5d353d85425be1eba2a7b0a8402c5e7354f61508018bae6a9ec2a100a3de1d31d85420055bc2263b0a84008f78758461508014e90ab08c2a100b331cd321854200726a9a6430a8400e8d434c861508051eb0f188c2a1003b14ca31185420043fc2ae030a840987c855c061508011bf06b80c2a100a3720d70185420047bc0aebb0284008f4815d76050805998e6996c0a10039354d32d814200746a1a65b0284008fb8758060508018bee6a9ac9a880a2f21d43593510055bc0a86b26a2008bf845cd62d440717908b9ac5a880a3b21d3258b510166639a64b16a200e4d534c962d44015cf02992c5a88062f21d6450b5101c7643ac4a16a20097585dc542d440196ac9b8a85a88033958b7150b511b43f43ea6b24a236a3e84d4d649446d87eeab22a928a734d15071552510062eb9aa6b14a23693c845db529446d0ff0eb26a5288db0f9d164d4a511b49e422e3a94a20097581dd5429440117f08b9ac12880e2f21173582512dc3f43ea6b04a200c5f73d4d60944058b8e7a9ac12896e1fa1f525825100e36396a4b04a21a87c875496094409974c0ba0c1288023ee1d60182510065cba2c0304a200a3d8590f645440517f0ea1ec8a880e1f21570d915100557414c7b22a200aad8298f645456b87ceca9ec8a880387d8d53d91510070e31aa7b22a200a9e8398b645440153b07316c8a88d28fa1673d91510051ec2ce7b22a200aae829cf645440155b0539ec8a89e68fa1473d91510051ec28e7b22a279e1f5394f64544f3c3f06a9ec8a88d28fa1672d91510051ec2ce5b22a200a9e839cb645440153b07396c8a89e78bd4a52d91513cd1f42e65b22a200a3d85ccb6454401c3aa7996c8a88038754d32d91510045f43865b22a2008bd870cb64544f347d0a196c8a88028f61432d91510074699065b22a2798be87cc7645440117b0f98ec8a89e68fa1731d91510051ec2e63b22a200aae82cc7645440155b0598ec8a89e68fa1431d91510051ec2863b22a2008bd87c8764544f347d0b90ec8a88028f61721d91510054f41e43b22a200a9d83c87645446956d03386c8a8802ad60670d91510051fc2ae1b22a234a3c855c364544f347d0b986c8a88028f61730d91510045f43861b22a2008bd870c364544f347d0a186c8a88028f61430d91510055741061b22a200aad820c3645440156d02186c8a8802ad60430d91510045f43841b22a2008bd8708364544f347d0a106c8a88028f61420d91510054f41841b22a200a9d83083645440156d02106c8a8802ad60420d91510045ec3cc6322a200a3d8598c645440155d05318c8a8802ab60a63191510045fc3ac6322a200a3f8558c645440156f02b18c8a8ada8fa146
  | 18 => 0x200301500000400000000200c00100100200300500b00600000500400300000000000100100300100200000000f00100000000b00100100003000600c01b00000300000100000100000500000100e00000000400100500900000900300000000000c00100400100000900000000000000000000100400000000000300c00800200900100300200000000000701500000000000100000100001500300000000000400200100100000400f00001f00500000000000500200200200300100000000700200200100700300200300100000100000700100500000000600100000300000100c00d00200b00700500000100000400000000100100000000300200000300100000c00800c00000500400000200000000100000000300000000000000500200300100000500200700000200400400100300000001300200600100100200700300401a00000a00400900000600f00500000200101000200500400000000300400400600100400100100200000200000000000100500900700000000100300300000301600800000000300100000000000200700100d00400000500000000b0000050150100000010000020047bc0ae6b16a8008f4815cd62d500196883b8ac5aa00237e0d70987540146e41ae130ea800c5f7354d61d50130f90bb9ac1aa00e1f215735835437c3e43aa6b06a800c5f7354f62550014eb0b98ec2aa002b9a0b31d85540053ac2863b0aa800a7585c8761550015ad0790ec2aa0023de1d611855461d3bc2ac230aa800a7585cc4615500156b09988c2aa002b9a0b31185540053ac2e4230aa800ab584c8461550015ad07908c2aa00e1f61773d81543743ec3ea7b02a8b587d8754f60550011f70eb00c0aa00317dcd53593523743ec36e0aa6a400c5d7354e61d480717d0fba2c3a91e70f1d774587523ce1fa9ee8b0ea49cc3c751d161d48130f90bb9ac3a90061f21573587520045fc22e6b0ea4038bc845cd61d48010f90ea9ac3a90030fdd153587525ae1e3a2a6b0ea400c5f7354d61d48014e902a9ac3a900317dcd53583520051ec2c87b22a400cb4641c564548df0f90cb86a8a906a1fa1b705515200c3ec2ee7b0aa40087d87d4f61548058bce7a9ec2a9003175cf53d85525bc3ec3aa7b0aa400a748154f61548014eb0ba0ec2a90029d61731d85520055b42663b0aa400a75850c761548011ef0eb08c2a9002ad21161185520053ac2e6230aa400ab684cc461548015cb05988c2a90029e61730d81520053cc2861b02a400ae9820c360548011f70eb00c0a91b29ee1560181520143fc3aa7b2a8400c5d7354f655098587eebba2caa10022fe1173595420047bc0ae6b2a84008f4815cd65508011f700b9acaa10123e20173595420143e43aa6b2a8400c5f7354d65508018eea7b8acaa10031d54f71595420063bba8e2b
  | 19 => 0xc847aa10095416a0a09dfc8e06df2739398ffa7142b5a00c8ae2d00f7a040a9003f40580000002361501ae81980000001480bca00035e83bc2644d600020a8ca45d417d0eb89a40e54588dacab05fb000249000097a0000850d7672f1df82f000005b45f93bc86e000352800032023c0000000000000000000000043e00000012063631cb093400000000000000000000e38000000764000056d41c0004c1125d40e00300000000300c01100800600001600000500100300300100900100200000301700700800300000000000000300201700600700000900600a00000a00100100000000a00000100100100100700000200200400500100000300101200000000100500000400900100100300000900001900000200800200100000200101600000100000000600101300300100300101800000500400800400600100600100100500c00501200400200000000000100400000300501201c00a00000000100b00500300202900600100a00400700b00000100300600000f00200a00200000100200400c00800200000000200000000100400100300300000000100700100300000000000500600300900300800800500300000a00000000100601700d00b00e00000400200000000300000300700001a00700300a00500000000700801f02400200002100000000200e00300000000000000400600100000400100002600200300100000e00600200101000200000000000900500000200100000000200100600e00a00100b00400100000100000000000300e00100001d00200600300100000700000700700000002400100000600200000100200400300000700000a00000000100400100700400000000300700700200100400500501600800100200a00400500300000202400400100200001200000100100000000c00e00000d00100500100800200400000000200500000100100000101000100000b00400000600000100100500001000400200600900200400000000300000100000600701b00200300000a00d00200400000000600300300400103b00600000300d00700200400300100301300000000100000200600000800200000000000000100200500800200a00600200600000000e00400100100900100000000000200b00300100700000000100100100d00200400500300000000600100000100000000100200000200200000500101900400400100000d00f00200000000000400000000400100700400000100300300001100900c00600400200600000000100100400000000500500000000401400000400000000400000200400200300500900200000d00100000001400001800000f00000200100001a00300100800000200000000200100200300500000000200000400000a0080040010020000140010000000010000080060
  | 20 => 0xce07963e5800001e1242dc249d0de77822127543e445e46080009ae00000000005ca4c707616a00000000839c0c0001c000001ec60400046a12f92cc0003821fa071200012b23f8b9000039f00009bc55936b000052e4cb25a00000007c50000000d3a1ee35582a4ede86700004840008242b792b13788a42d9920c6fc43643400001548473ca28040000c12a7966074c09036da33c0000000000000000000000000139a0000001e00a2698a47b8000c6229348da4844a28491059a240001b135f80000008ea132000000071d000100000000035aa7d0ce400015209bc4ce3f40f8912800000002580000003b62d5174000016f000000000000000015b03c850e0e780000000003e300003360ff42f95741924a80899accd2c1bf3bd83a052090f26c8979146678365a0e000003712e800130c3bd36308480000002dca674d9000019725b00003150000a280000000000a0c0000000002550d0c00000000000001c40000000000000000062c4540002c98cec0000002ab896512a00015a80002d200044300000b20003cc92f4000321297981c00072d45f00000000001010000000000000000049c0004a281b00889d00b90fd42326e205921747a42ba0ad1d1400027133582f836a6f20000b78e5400000013cc9982a200000001ec000000226ca385f100021b853613c2ce00010600003981e789aa6e80de800136e0001b600000000000001cec84048d4be0fbc00000000000002e00000000b6941089142592d40000824b510a00ac63947116f80000004460cd8f449ad1f28fed0c400047606bc0003c34360cf8ee48090000538c1e0004d2a50c37008b170969042232a5001ae05c000013a87b122055f322947400e000000247c8fa8720a588147387f000000003da00037c9414d280000000b880008fc0000000000000195800029287c11617e40003a4000266855007e2e880006a288b1798dd40009eb075800020a5474b38dc400044f0c88c6c00c00029680007504100a3268823e2f849b00007629654918af800073c22f8a08ad27ac00000000005150000000d840003d39350000771509000060000048e888059e00000000000000000000dc103a0000988000f300002631da53865441daa60460839d1a4809541e4db18786a800000000022640000b10880000efa000000000000094407e0d203f81db0cd24811ba8023949f6060a1fb03497680006c40611f84dd400b1210d4c000878171a6640000004da207085e4f02298be4b0e2f431b8c512321b65019a0000040b3a2102891657b1fb80000006cc0001bdc0009d213a10fc00018900000000000000000750cd20000f9800050c06f000000000000032e831ccda36719a169800052a0000000c560003dba3a090000030e8e782880001c20f741b068514a8744e7e136000127130e
  | 21 => 0x22e00021d117a3bb0000000c660001d2a7903f04080000f904385f60bd9a691406952b085cc40c5730001fbd2560001a580010f60003738000b2c0c44f3154d3bc00000000002d85d73a912e80005fe27e0400fb22773082114c4430118f101c94039949d891927c0983d2825d18066f0cc04e4d4e2aa3869db800000000000005427c900000000000000001a887a87c80000d640005bb1aa99b0ae00003231db4c0c7060000a242d6101000097c00010e15681a8ebc9d138f1b411248a517aa6a106c4b633097249345382be80000000502079ccc0740b900008ec0003600002530a3600039c26e0d3e43d3cb81a142093700016380008fb0000000598000227268c2fc492212859c0000001ef80005e40001ff800014890a00018793c20004999fe12a60034f606842b245800013b81bc00000a8450534000135000127a2a3000000116a000000086000000040c000000000000000000003ac05a800121215d0eca5f4fce6cd1279d3cde000000011a41464fb31b20153c086519023e400016324d985511015800000000008e53bd00000000000000000adc33711b962400000018509e80385493a4800007870200009a0e9c7f427c91bc0023ca00018441123862eaa5f821e7ae23f0edc0000003938000000000325000000000000023280002b837480000005a000000012e8000000054000059400010ac9d0866407800132c00000000012b600000000010420003f216400007203ae0000e587a039d00207e01fe15e00a462c0000320e003a00fe0c9143cab651943ea65068c42705b800000059f3ac800059a2c2000000028000003e8244c8e92a00018946c404c06b9e4846a3d31fb1f990324bc30d800098a5d2264960c0e23f82e507fd0d252e1b9a1591600004a327888d851f2479ab519a5324e0000000067a2db1b780002b100000008f000043089000a40e300022e8000000000000079a49d375a4b01c263e04d0000d6801f4a380004324b73570b64d3c0004f7257450200043a81e47525351fe986521a7a93c090e000000021c800000000000000000007cd000000047e8e907a80010e213b0b8867800000000000006b60000000000aac1a7000008885c11c09a1c1c1dc0000f51a28be09fe1838b441b20530f184d535856d3728d108585bd45522a4d0672427597bc8ee25536712ed08899f35300000007f312d8bb93ea37b0001aa4a7250d0000000fa82e7391800000000026e9a8041809d1f480003d21990001104c000004c792189c296b494223ca9694148125841246160d400013160000b700013944170000000000000000000000070020f00012ec6790679a600005233c41fa83cc21d0a6000000000000022d111442900002792006881c39010da65284c6a540b24000020000102838c435a348aa09aa000000003a5513fb
  | 22 => 0x246101421a0000bb40001c10001fd40007670b692b87da7210001c04000649000130800044621e22848760004b200010b87d300000000000d6000018440e64d0000d6809e2c74d0877416c0000000000bee2c60001a840005b534600008ce0000000000cc63d92b500013e27b400005f456c9911960534d948200e41c3c37c0001420000000298000000138e0002c0800118800000004111c26133149954aee000000000000000000000000000001d398d4000000000000025200000000010ae0000001d880000000e9a534d0242300000000007eb4628a147c60a748e1bd88985182110b392da40e000000052276638ba180df65e62a612e431000000019a100e0002ef225830a303000000000033900011ad24a83f4f3837d40a8704659bb800000013d80000005dd4d01e690d40004d2000000000024b1f54000531111a3587249cf2e7800066a00022297f45b867c36a09980000002369c4467800024a04613b600040f00000002d22f51b3d3fa0001cf80380000002eb1ef839499245300006947b50000cf429e2d72820a3c00000009c030125c1682a68000eb008f1b200c8eb48c80528e8d1768f00e30d5c4b83420000f586da47b00000000006274bc89e048a000356000038475100012385f69dd45600000008163b58da80001e826203a907818e4e425884980cd26090b4bc65e44b7260c00000029580000004930000bfc0006484ad138cdcc0003ed8ba4ce600029090a93260000002368eba94204280e0b5e00010083dd2a464f3dd24c80002df00022f000000000000000142873ce07f45ac19600000000008f118900f4cfe186199266076668b0b30000d6e82f446981524c000304000018a00000012840000002e580000000001ae000000057822e88a47e627201214f08b808027b80001580000001668a8c00000008c0e7a187000244516c34500016dd07485e000000000096f0f00c440000001b7976400062d4e480011e4046000045c0007461a7a4bcb865674ab0388e9a1eb0000000634000281822094c6532e99c6448284e000106938a0e4000000110e7e23c8275045046a113043464a0004ce27e0bdc5f313023b8fba8123c4a0a08026773db00005d0031000009839c3cc316104c86000023096d0a167ed078988c0007bb3929d2127e0943d682ec0000f94af0000b4280617200000009b50170f680007b94d980008e43e73f011b8cdc1953478114bb080422895009626d933880007060001380000b8a04e0738044eb680d00011cc0000fd426875c0000000001c5400000000000000000000be000000000008900000000003a500010f46990fc81fc6fe6c130611d48120000001ecc71c00038c000034a65a27500000000000001ef0000000000011c0000af0391f4400056400000007e24e4000000072a39127a996400
  | 23 => 0x5a00030c00000007d20001b69150073000270841c000000080d14e156232000000026c00000000001e536c000000053e2f5800000000027480001408c22bb15e471e43a30220b4f480001560354cea4df109800017491618b881104c7bf1ed894800015c4b80000e1467d28d10d029083100000009461742a19fc40003412d700003ee2483629f6857e0000001ee12d09493058ae400090100018ec14441100007580000004b9141800000034d800103e0000000ddc4ca77c4098000bc46ed00001b859400000000000006ef0000000000000224a48800000000000000000001aa188455c3be0950000e345dc000000003047c2ad1b1c00060328506506b0454000091c71a00000009e48424ed0000a30f7a6b903180002ee0000180000c78000000203000028800000000000001af985c53e9481910000b9a00000004f4ffe4594a7800080a0862cb8000dfc8790001d3078c3930000000d1a000000277032655c11c83814123cb1fca104360004252a420464a0c2d2918cc748f64fe0b00b807a303c11800007c100020940003d5000000054a8ff4d806ad2082dd0000000e5691546f83d000013a2a108f540400004e000000043542a99600003eb2c404f8bea9803b1860c4703382a2a76479e406121800110600d14911d809452716c0abcf2278c38e1e4c0009f047c000020c94035180006ec2eb0081880e6470b46e1be00ca00000000011448e00799fb000000006700000000004cba8180000000c11fe80003b40000770eca5f4161800000003b0000000f363503bb163c0003883c38bc535c0000000000790000389000000098c00023d0a740ed0000d0c0009ff000019937e130000000000087313082b51dea1300000000001450000c4c0da00025919d913c66628f0000c7091a15924790944740000000fbc80040415fc000000348a3180008290000db814c71041199000009d81120f5c5821a20dba7a11860002d800008cc09608d98bc2bc7a83a393e80000000000da54148ed021949890e6be03d17e0de2634069999442073428b93410b02fd09181d83741d20000000f943c14c497300006af00000000004c0115a5a495e00046b8ac01e489700000002a498817820d4b6261a0000000a9c00000000000009cb006000109e508000000000000000000006f49bb466092c00021709006b122426d2c60e84000000194100c67e0000002570cfc5b2000072c000000000192cb1a8432c20000c288f344482a00003dc27c000000000041992c0f3a74024603e03aa5711c807d0d0465f0000001336815253932000069c4980000a201540d904fc818000000000000034d24f80000005a90000160b8c7790f824d14085ab02f8fa08f29391938928ffc01b25109b837283914e9fb89301a40e280bd3d481a4e99e089fc0004e700005cc00000
  | 24 => 0xeb8a711a29c100000000008b200023f424c0001bc258c6521090fa80000003ba014000077200004fa2380006fc1d800004d60002e21424f62137000060400071f0928c604920004f79fed12635200000000007501ab22b80004470000000ce8000000000106850200013fc000000000133800031d18e000023a3332f48000a764a93e122088666d2187000010657a00002640009b21cb94000001bc00003288b62a937a000020402c1b30b5520c94e0bd12e0e848e311281800005e10000000d9263f0cb800053225400013f47c47a606d86a454c5a331525283384a400000e4cac3ce4b9800011a3ea0bca3540000004d782fce6e3d142427b50ee29424080001ba0002888000e6c51235e00000009840000cc50447c43d7844431e00020c221490800035880003b442411699ece504d10001cb938c18c41d84b4ff86d513b158121c16427b000000025a2f61898e620844fd00ccca28d914722101a4000000190400021f3eb2190bfe0004d58834b7e0622619d5430853303b800102e5821648e04e180b32ba09f0b5a534387115532a08710400004fa3ab49d05d48ca2cb2be04acc642b41ff0f4000098e3ef84580000003ca88e84886874e2069835c90c0a50000a2c4443a5826c9120000000000000000000049c7f87aa0000000fa00000000b10000905000000069c00000025ecebe3e04d3a39c0000004fd8000c506303b4000000030923880010fc7f917512fc6c23a220e036882a00031e800057a000000215036888026d000019619d26c0000000000000199c0008e632100000040000001804a6c35d321a82c45e9e50000df000020000000d40000000000000f8e32f0000bf8a8200000000a92ea66a2598ef0e100003f48000dae0003b022b530a00000000001680000c6a42c0000c34ab85546fa8371fd015c764000000000000000000000006981cd41e83a4ed89f93e7800000010a0fd19780000000e196140009b10001dcc00060900000000aa2c518f851cf0a0051d025e0c040004fb9ddcf143b800a0150da23262de1e18f1c3101a012080245991ec04b88c42274bba4b4d801032a90178c5c8b70d984689d876a3e7166c09a2311c2879c1cc000426000101c756145800000000000016545f81612259c14bd02d400009f8f080002910000b140000001dc063265b0001ce4ac449043f90740920000000000a52000361a360b5841646485880001f602e1554d2600010d8a590360b8140109800047a2ce99800007c335b02f411c95929e80001020004db0aac0000001cd000000089800000000000f0000000000010c00000000001c935224f113826303a16182fe8b300012ac05600000008cc00066420f80007cc6fd000245000000015b88240008500000000000935000094c00008c0000bd93ac3c400000000004484aa9e0c6
  | 25 => 0x2768f8038b2ed9c4c61820a20c80008d00000001a3886475419180000004122aa0000f3e000000000000000010b152800000000000012529a63ee18701264404210f010c60001d680000000000d1a14cd2453f16d9e2d1d6000309171c0003ec000098800000000000009e20000000bb00008d0000000078a00000000004a012f00005d800001a177800000001339113c861678d3270dc91c80004ef8c910da07c2268888bce02d4b000011b6697068252ccc40a132e055cdc051406300f86bc5301640000000365000067d3d25653f1a31c02e2212b9000000076129280849b80001980058b846fa0001aa00001e23708680dfe9714e61e84d2000045c812000012c0001930730000013800042a000000002421091700023e800012824500000000000001aa84b09bd24400003bc507000000113429e4161f308a456326797f00006e420d9910b9c4020689034cae4ca19d11580008462f0105006888138d80002a68273071e3c16000000000001140191ba2274c480000001d04fee00001b12440000000001ec07922573ba162c00038a00013800005a728601c000055e2281f5cbbe0ab000214507c6ec4f9949073685202ea27c95a50140087850569b909105800b40ae4afa0c851a00048389cc0d69f224a9d5d3c621e242987cdea60a2baa6407bc0202fd04541a800042c850c00082e34206ec0001ad00000008620002c89fc92700420000ea80000004578e0933c5f217b8000e4c11e2e081449c415f183073008210b1348000000000000000000023e5088000fca6540000000a58743272a83475e6dd40891fceea73500013d0ca056604a80007c200006e0000dc63ee455850830039400000011bc6dc00006280008ce00000000000000000000d6487618426e8c1a23407d81d51a636824f00000000000ec0000bda00000022412fe00000000012b015100015a0f560000118c352266b0000019d2622b31bc9d4d3525800b28f092a22a7099a7d89327161698000de600000022e10b4000000000041e00044a14dc1f45ba00000790b6000000000000057e221877c0005a20000000efc4d30bc1c24000347000116800000013f93345760001e3800000059e00026f8f643f24
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8804801a80000032f00004ab00c04155c88214000002700000000000b000000f0050000131a6002c4c0001c0e00031045c0801c00019000169266000290a819211e7460a006c023000d28b20d001a3ea80010e041c0000400206000040604141800060d1d08154d61d480188e874c832d915100683611320cb655040144d9210d731954100607211734c865504018557320532195410048d245840c86550401a0d844c832195410068910682cc465504018344161c311954100705105730c46550401a1441a0f211954101613e1d534cb648840548f9750d32d9221006235cd821cd649400188d835c872592500062361d320c96494001a85844c83298650006a1611320c9619403544c9754d32588500060d1d08154d61140014c593188715894000583650634cb654800181d845cc63195200051365c634c8654800160d9418d321952000507650305cc654800144d920c1731952000515644305cc654800181d845cf3119520006135cd82cc4654800144c9754d32591200161321d534c9644800548c9750d32591200162321d434c96448001c45534c871591200072150d321c5644800144f9754d32d8b100064c1d580d9141c4001a0d844c832d951000683611320c8654400188e874c832d9110005852557118c644400188d84dca72d8d100052365032dcf624400188d84dce73d891000589255811906244001c144118c755051000709104621d5414400143697107655051000705190631d54144001c24751906250510007111d463189414400188d874c83259010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa81285844c83219541
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4d
  | 8 => 0x138c
  | 9 => 0x6
  | 10 => 0x94b
  | 11 => 0x94c
  | 12 => 0x94d
  | 13 => 0x124b
  | 14 => 0x124c
  | 15 => 0x124d
  | 16 => 0x138b
  | 17 => 0x138d
  | 18 => 0x98c
  | 19 => 0x98d
  | 20 => 0x128c
  | 21 => 0x128d
  | 22 => 0xa0b
  | 23 => 0xa0c
  | 24 => 0x130b
  | 25 => 0x130c
  | 26 => 0x14b
  | 27 => 0x14c
  | 28 => 0x14d
  | 29 => 0xa4b
  | 30 => 0xa4c
  | 31 => 0xa4d
  | 32 => 0x134b
  | 33 => 0x134c
  | 34 => 0x134d
  | 35 => 0x198b
  | 36 => 0x198c
  | 37 => 0x198d
  | 38 => 0xb0c
  | 39 => 0xb0d
  | 40 => 0x140c
  | 41 => 0x140d
  | 42 => 0xb8b
  | 43 => 0xb8c
  | 44 => 0x148b
  | 45 => 0x148c
  | 46 => 0x2cb
  | 47 => 0x2cc
  | 48 => 0x2cd
  | 49 => 0x14cc
  | 50 => 0xbcb
  | 51 => 0xbcc
  | 52 => 0xbcd
  | 53 => 0x14cb
  | 54 => 0x14cd
  | 55 => 0x19cb
  | 56 => 0x19cc
  | 57 => 0x19cd
  | 58 => 0xd0c
  | 59 => 0xd4c
  | 60 => 0xd4d
  | 61 => 0x1a0c
  | 62 => 0x1a0d
  | 63 => 0x104b
  | 64 => 0x104c
  | 65 => 0x1a8b
  | 66 => 0x1a8c
  | 67 => 0x95394
  | 68 => 0x94054
  | 69 => 0x138e
  | 70 => 0x138954
  | 71 => 0xb0954
  | 72 => 0x94b14
  | 73 => 0x94e
  | 74 => 0x1409
  | 75 => 0x140954
  | 76 => 0x95414
  | 77 => 0xb8954
  | 78 => 0x94b94
  | 79 => 0x1489
  | 80 => 0x148954
  | 81 => 0x95494
  | 82 => 0x2c9
  | 83 => 0x2c954
  | 84 => 0x942d4
  | 85 => 0x2c955
  | 86 => 0x19c954
  | 87 => 0x959d4
  | 88 => 0x209
  | 89 => 0x1449
  | 90 => 0x289
  | 91 => 0x14c9
  | 92 => 0x139254
  | 93 => 0xb1394
  | 94 => 0x138b14
  | 95 => 0x141394
  | 96 => 0x139414
  | 97 => 0xb9394
  | 98 => 0x138b94
  | 99 => 0x149394
  | 100 => 0x139494
  | 101 => 0x2d394
  | 102 => 0x1382d4
  | 103 => 0x2d395
  | 104 => 0x19d394
  | 105 => 0x1399d4
  | 106 => 0x180b
  | 107 => 0x449
  | 108 => 0x1649
  | 109 => 0x141294
  | 110 => 0x1049
  | 111 => 0x1a89
  | 112 => 0xb8a14
  | 113 => 0xa0b94
  | 114 => 0xa0e
  | 115 => 0xd0a14
  | 116 => 0xa0d14
  | 117 => 0x150d
  | 118 => 0x1a8a14
  | 119 => 0xa1a94
  | 120 => 0x149314
  | 121 => 0x148e
  | 122 => 0x14c154
  | 123 => 0x154d4
  | 124 => 0x104154
  | 125 => 0x15054
  | 126 => 0xd4a54
  | 127 => 0xa4d54
  | 128 => 0x1a0a54
  | 129 => 0xa5a14
  | 130 => 0x2d354
  | 131 => 0x1342d4
  | 132 => 0x14d354
  | 133 => 0x1354d4
  | 134 => 0x105354
  | 135 => 0x135054
  | 136 => 0x1a9354
  | 137 => 0x135a94
  | 138 => 0xd5994
  | 139 => 0x198d54
  | 140 => 0x140b14
  | 141 => 0x28b
  | 142 => 0x184b
  | 143 => 0x148b94
  | 144 => 0x154d
  | 145 => 0xd1494
  | 146 => 0x148d14
  | 147 => 0x20d
  | 148 => 0x1a9494
  | 149 => 0x149a94
  | 150 => 0xbd4d4
  | 151 => 0xbc2d4
  | 152 => 0x2cbd4
  | 153 => 0xd42d4
  | 154 => 0x2cd54
  | 155 => 0x14cbd4
  | 156 => 0x28e
  | 157 => 0x19d4d4
  | 158 => 0x14d9d4
  | 159 => 0xd54d4
  | 160 => 0x14cd54
  | 161 => 0x1a14d4
  | 162 => 0x14da14
  | 163 => 0x104d14
  | 164 => 0xd1054
  | 165 => 0x194b
  | 166 => 0x164d
  | 167 => 0x104d54
  | 168 => 0xd5054
  | 169 => 0x1a8d54
  | 170 => 0xd5a94
  | 171 => 0x74b
  | 172 => 0x105a14
  | 173 => 0x1a1054
  | 174 => 0x44d
  | 175 => 0x180e
  | 176 => 0x1a49
  | 177 => 0xec9
  | 178 => 0x942d5
  | 179 => 0x24211
  | 180 => 0x28211
  | 181 => 0xecd
  | 182 => 0x1a4d
  | 183 => 0xecb
  | 184 => 0x1a4b
  | 185 => 0x249
  | 186 => 0x15693
  | 187 => 0xb8293
  | 188 => 0x2d555
  | 189 => 0x202d5
  | 190 => 0x1542d5
  | 191 => 0x242d5
  | 192 => 0x16c2d5
  | 193 => 0x2d6d5
  | 194 => 0x1a9953
  | 195 => 0x2d4d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2178
  | 6 => 5450
  | 5 => 2580
  | 4 => 54
  | 3 => 1
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (89298+((h/726+packedAt gbK7 (80586+(h % 726)*12) 12) % 2614)*13) 13
  | 6 => packedAt gbK6 (285208+((h/1816+packedAt gbK6 (261600+(h % 1816)*13) 13) % 6541)*14) 14
  | 5 => packedAt gbK5 (162540+((h/860+packedAt gbK5 (152220+(h % 860)*12) 12) % 3746)*13) 13
  | 4 => packedAt gbK4 (3906+((h/18+packedAt gbK4 (3780+(h % 18)*7) 7) % 93)*7) 7
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff80ffc03ff80ffc0fffffffd13f3c7d8e31ff
  | 1 => 0x7fff07ffc0fff03ff07c03c02ed8d39ef3cecc
  | 2 => 0x81fff80000ffffffff8003fff0e0e3e303ff0f
  | 3 => 0x1ffffffff00003ffffffc003f00fc03fc0ff0
  | 4 => 0x1ffffffffffffc0000000003fff0003fff000
  | 5 => 0xfe00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8a8011420928824400a54a54800b042c861055
  | 1 => 0x6c8b02da485a921d10681a8186585194b2c6cc
  | 2 => 0x155a80410952caaad00212b30a0a2c3016b0a
  | 3 => 0x2166ccacb2010433ce52b0023b00f803580da0
  | 4 => 0x49f8f7373ce7cf008420c20c3dfd0003efb000
  | 5 => 0x7040803820060803084300303ff6ff78000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36717
namespace PEqualNP.Outside.L_meta_36717
open PEqualNP.Outside.L_meta_36717.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 92 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
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
theorem bs3_4_64 : Interval s3Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_128 : Interval s3Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 539 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 bs3_4_224))) (concat (concat (concat bs3_4_256 bs3_4_288) (concat bs3_4_320 bs3_4_352)) (concat (concat bs3_4_384 bs3_4_416) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 664 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_7_0 : Interval s3Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_7 : Interval s3Atlas 7 0 1 := bs3_7_0
theorem alls3 : ∀ k ≤ 7, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
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
theorem bs5_3_0 : Interval s5Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 2 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 54 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_2560 : Interval gbAtlas 5 2560 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2580 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)))))) (concat (concat (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)))))))
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
theorem bgb_6_5440 : Interval gbAtlas 6 5440 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5450 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)))) (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)))))) (concat (concat (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)))) (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))) (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))))) (concat (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)) (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)))) (concat (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496))) (concat (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))))))) (concat (concat (concat (concat (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008)))) (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168))) (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))))) (concat (concat (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520))) (concat (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616)) (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712)))) (concat (concat (concat bgb_6_3744 bgb_6_3776) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872))) (concat (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)))))) (concat (concat (concat (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224))) (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384)))) (concat (concat (concat bgb_6_4416 bgb_6_4448) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544))) (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736))))) (concat (concat (concat (concat bgb_6_4768 bgb_6_4800) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896))) (concat (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)))) (concat (concat (concat bgb_6_5120 bgb_6_5152) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248))) (concat (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344)) (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440))))))))
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
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2176 : Interval gbAtlas 7 2176 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2178 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 (concat bgb_7_1856 bgb_7_1888)))) (concat (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 bgb_7_2016)) (concat (concat bgb_7_2048 bgb_7_2080) (concat bgb_7_2112 (concat bgb_7_2144 bgb_7_2176)))))))
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0eeeaeae8eee0eaa0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 4007717536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36717.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,4]⟩,⟨.or,[0,6]⟩,⟨.or,[1,4]⟩,⟨.and,[0,8]⟩,⟨.or,[2,3]⟩,⟨.and,[1,2]⟩,⟨.or,[9,11]⟩,⟨.and,[7,10]⟩,⟨.or,[3,5]⟩,⟨.and,[12,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4007717536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4007717536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36717

open PEqualNP.Outside.L_meta_36717 in
theorem PEqualNP.Outside.L_meta_36717 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4007717536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4007717536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
