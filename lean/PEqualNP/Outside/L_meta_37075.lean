import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37075.Model
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


end PEqualNP.Outside.L_meta_37075.Model

namespace PEqualNP.Outside.L_meta_37075
open PEqualNP.Outside.L_meta_37075.Model
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

def SBf (j : Nat) : Nat := [7, 5, 5, 5, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37075

namespace PEqualNP.Outside.L_meta_37075
open PEqualNP.Outside.L_meta_37075.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x110008b0f8c4e4c003362831e4c0189140208175e70a15484800f2c018000000000008400200000005a1c4a80ab8e9a322c00030946aa56a51811c1e1c101060428114003042a24200ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4a0c800008d00000d80010001060000000ae000380128433500000491d800cc5a1f2604496000000006000b42852311801e1b00000aa0051010e8364b80132794a9fcbc7348054003a188d48e4b00070009b1a058422316000002a0000000002d800007d3400000420700000512c9bd0c000f8744e0d422144c9f000011c0020800782f120011800001311232048c010002e8e45013240000018280008017001d4f44f051ecec12000152601478fc8c9238270209d3ba2d027c3915822a0521e0c287270f418a1228a4340332a780491269b8b8820599cc65451990d6331717d3437400acda53129107088001a4b07e451c43c000000010002890e00000006800001000f038c028b810506010080010004029608008886000101000a80000000800002850609828c8380804f94b439ea8e873e50d0e7aa921dbd4943b6292879f5350f5ea4a1cf14943d6292872c5250e7ea2a1cf141439f2a0875e53d0abaa7a14f54e429f294853d5190a7ca12157d4d42ae29a853d5310a7ca4216b948429ea88853e5010a7ca9994f55332d6216653f548ca78a91967d0e32cea1c659f548cb38a9195794a32cf214659c428ca7ea8994f151329f2a0653d540cb3e86196750c32d6210659e540cb3aa8195794832e729065cf420cb3c84196710832e6210658c420cabca7a0d754f41cf29e833d53d073aa7a0c754f419f296839e32d073865a0cf943419eaa4833f5350678a4a0e78c941ce19283b75150678a0a0cf950419f2a6633d54cc67ca918cf55231cea1c636e528c6daa518cf951319eaa2633e540c67aa818e750c319faa6433c54c87986590cf952219eaa4435e53886baa710cfd51219e2a2435f53486b8a690f30c921bda824378504867ca810cf550219ea9c813e529033c6520670ca409ea8c813e50902bca6205754c40cf298813d531033aa6204754c409f290819e321033864204f544409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f550309f2a6413d54c827ca9104f55220af29c415d538839865104fd51209e2a2415f53482b8a6905dd4520ba28a413f5408278a810730c8209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x76440222abd5363e2800f0c000ac00d002d2c9c025407149800d4b8270411b12478693166930e48e590308dd5801201d004274407666540536018000031700281e000080c20584060010d0c0408f0004000c3d4c5250f0f631494387d8d5190a1d63942428d584548ca8e62d5232a3988548ca9561152328b594420ca8e6290832a3d94420ca8d6510832a3584420ca8e60108329318953d062c6254f41a318953d070f6254f418718953d070c6254f418318953d061f658cb418759432d070c520c9418758c505068c6250e31c350e528c61d63951318b189544c6386055131a3189430c61d6315321c315032c870c540c921d20c8504861d6395021c3948329021f635464093189531022c6254c40a3189531030f6254c4087189531030c6254c4083189531021f658c84087594321028c6250f308b98b548c21c6550d30a3189434c30d4314930c550c514c21d6395320c3950328821d63150208d584540830c540c8208758e54c421d6315210
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x4004800820cc0000a2380428338ec629287215c76510832818e4b18a0a0c0c7258e5408607396c6a8c81411c9431453081aec2a06410505711503208206392c72a621031c96315210
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (912+((h/16+packedAt s0K5 (800+(h % 16)*7) 7) % 67)*7) 7
  | 4 => packedAt s0K4 (4895+((h/55+packedAt s0K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s0K3 (2420+((h/20+packedAt s0K3 (2280+(h % 20)*7) 7) % 73)*7) 7
  | 2 => packedAt s0K2 (502+((h/3+packedAt s0K2 (490+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf03ffffe07ffffffe07fe07fffc1ffffce3e3f
  | 3 => 0xffc07ffff80fe07fff83ff81fffe0f01f3cfcc
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1105108c412248100594a8a25012915414d0d5
  | 2 => 0x248a29103244942960294454a6412aa8ca262a
  | 3 => 0x42934a2490e904caaa8275113aa40c0d634b4c
  | 4 => 0xb2c74492481d974d34c1861cd39c031bc0db0
  | 5 => 0x8c307871c70e1e7f1c739e780e3188c1ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37075
namespace PEqualNP.Outside.L_meta_37075
open PEqualNP.Outside.L_meta_37075.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe421
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | 3 => packedAt s1K3 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s1K3 (17+((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffe03ff81fffffffffffc03f1fffc7
  | 2 => 0x3fc07f00fffffffe0f80f81f80fffffe64cff
  | 3 => 0x3fff8000fffffffff000ffe000ffffff870ff
  | 4 => 0xfc0000000fffc0fffffff000000fffc0ff80f8
  | 5 => 0xfffffffff00000fffffffffffff00000ffff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x186450a1802382180318d18a28e2c6190a95c3
  | 2 => 0xa929314696449469606a46a1b1255a6a664c5d
  | 3 => 0x5250a26b2a8928b2ad048b6c8249acb4b870ae
  | 4 => 0x6362c58dcd120edcd6b6e049248e3718df80f0
  | 5 => 0x8383060e0e1c30e718c70c71c7003820f56a00
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37075
namespace PEqualNP.Outside.L_meta_37075
open PEqualNP.Outside.L_meta_37075.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfe07ffffff01ff81fffff03fffffc07e7e3fc7
  | 1 => 0xfff80fe03ffffffe0f81ffc0f80fffff93ccff
  | 3 => 0xfffff0003ffe07fff001ffff000fff81e3f0f8
  | 4 => 0x3ffffffffffe0000000ffffffc00ff
  | 5 => 0xffffffffc00007fffffffffffff00001ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1230a145011c1180318a310d28e2ca2a2615c3
  | 1 => 0x445262895224a29606a0d544b12552cc92cc5d
  | 3 => 0x98a144d5a44875aad04969ae2249ab296370e8
  | 4 => 0xd1c58b1e3891474d6b6c0c28848e3c71fc00b6
  | 5 => 0xe1060c1830e186718c718e30c7003041d9aa00
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaacc880000eeaaeeaacc880000eeaaeeaacc880000eeaaeeaacc880000eeaaeeaacc880000eeaaeeaacc880000eeaaeeaacc880000eeaaeeaacc880000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37075
namespace PEqualNP.Outside.L_meta_37075
open PEqualNP.Outside.L_meta_37075.Model
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
  | 0 => 0x1fffffe03ff81c1ffffe0fffff81ff007cfe7c
  | 1 => 0xe07e07ffffffffe0f81ff0780fffffff9333ff
  | 2 => 0xff8007ffc1ffffff001fff800ffe0fffe3c38f
  | 4 => 0x7fffe001fffffe000000ffff001fc03f0
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc30c40238410a40318a60288e390990c24563c
  | 1 => 0x49108a4490a208a06a0a905124a322549130d5
  | 2 => 0x842554890d44954d04952b0249548ca962c30a
  | 4 => 0x1659e7122876de76b6c18a448e79c831fc03e0
  | 5 => 0x1861861c31871b98c719cc67006100c1dba800
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0eaeaeaeac8c8c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37075
namespace PEqualNP.Outside.L_meta_37075
open PEqualNP.Outside.L_meta_37075.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x5e9800060000233a3800602e00345c84931000128900e56ba2000d181a6c98f000000000d5eab405c50000000320e0d43f223003c5864a003cf82aa768803700104000490b1c66554806c0059f009c0000600081001200102040838004181841408381bda8287785050edca421db54843afa9a855c5350aeea2a15d14542bda8285785050abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d06dca5a0db54b41af29c835d53906f4a120de54241b7a92636c524c6f4a018de54031afa9a435c534867ca810cf55021af298435d53086f4a010de54021afa9a815c53502bca6205754c40b7290816d52102eca2205d544409faa2613c544c2eca2185d544309f2a6413d54c82bca7905754f20af29c415d53882eca3105d546209faa2213c54442bea6885714d10b7a92216c52442bca6085754c10
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (731+((h/13+packedAt s4K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s4K4 (1875+((h/21+packedAt s4K4 (1728+(h % 21)*7) 7) % 92)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ffffe03ff8307fe0ff87ffff83fe018cfe7c
  | 1 => 0xf81f83ffc1ffff83ff07f8780ffc1ffef3338f
  | 2 => 0xffe003fffffffffc0007ff800fffffff03c3ff
  | 3 => 0x3fffe003ffffff800000fffe003fc03f0
  | 5 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x30c320238411500c642980a8e3a1321884563c
  | 1 => 0x524424448ca11281a522883124a514a8b13285
  | 2 => 0xa1094a891144253410855502494a495302c15a
  | 3 => 0xc59673122875b9dad6b044248e739063dc03e0
  | 5 => 0x618421c31862e6318c66647004201836ba800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0eeeaeeeae0c0e0c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37075
namespace PEqualNP.Outside.L_meta_37075
open PEqualNP.Outside.L_meta_37075.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x43ef32087d86410df94421fba0843f441087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740df20e81bc41d02faa9205f94e40bea9c81be439037887205f94a40bea94817e51902faa3205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c525037e84a06f50940bfa8a817c515037c82a06f10540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea90817e51102faa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc3bc6598770cb30bf28e617d51cc3be6398774c730fda0661f840cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5185f94630bea8c617e508c3f481187e50230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f480987e50130fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ee218617e520c2faa4185f94430bea88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f681907e10320fd18641f930c82fea9105f95220beaa4417c54882fea7105f94e20ef29c415e53882faa7107754e20aea9c417c53882faa5105f94620bea8c417e50883f481107e50220fd98441f830883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20bfa8a417c51483f480907e50120fd98241f830483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020fda0041f840083f460107e4c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd20621f940c43f661887e0c310fd90621f820c42fea9085f95210df2a4213e54842faa9086f552109eaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fda0221f840443f460887e4c110fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f480087e50010fd98021f830043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xf4290afca3215f54642bf284857d5090afea6a177d4d42afa9a857c5350bb8a6a15714d42df21a85bc4350bde84a16f90942bfa8a85f75150aeea2a15f14542fa28a85745150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0217e94042bd280857d5010bf2a0215e54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1997e94332bd286657d50ccbf2a1995e54332bfaa4657e548cb7ca9194f95232beaa465bd548ca7aa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf28465fa508caf4a1195f54232fca846579508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cafaa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41dfa1683bd42d06fca1a0fe94341bd286837d50d07f2a1a0de54341beaa4837e53907bca720d794e41bea9c83dd53906baa720ef90e41de21c837e52906faa520ef90a41de214837e519077e8320fdd0641bf28483fa50906f4a120df54241fca84837950906fea6a0df14d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331efa1e63dc43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c7be8698f710d31bfa9263ef524c6dea498df14931f6292636c524c7be6498f74c931fb98a63de314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c6faa818df15031bf298637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fba0e43f441c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef32887d86510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29
  | 2 => 0x20800000000a08000000f80c0b6a36198001121df00020476a5b364000000003c400000000000000000943f84906700021c37c000000f00011d8fd26c960700000007cc610ae296000658000206e0d0a70500848000000000007ca31000000c180002a4a80006c0001fc1aa2714c80d0f00006e760001403e0000000143440003324c2ac3b800000242000001921688889820a4542bd218d300000000000000000e7858000000c5210000000cd08411c578fc16413e21400106000254000004a800000000192000000000004a4a3800000000138f300000085a85000000de800170000f5800000000150c547200009800204975480ec23820cd414c000001418000ea3c4000002a8001168000b2000d980027e4cc001e0000000000003b400000000000000d600000000000000000000c98c800000000000000000fc8d400015030000000464000003e87500019b2f41f80004f418000201380000102d00047c8fd038001881ed26a213d236c52911030001398000185c93f046000000000c0000000002791de4043780000065c6b9aa348000001b65248000e0000000000000024c000328003ca0001581b00045c68a77000138691c846a494850001180004e0000007d8000002fe5693780000000000000000000f500012000000000000000380f43782dc0003e000000cc8000000010b1f5000000000f8000000001411fc00000000000000001070010000080000100600001801004008008000020040100500000002805002004000060000080000000200400000014000018040000000100000000000000000014008000000000000000000001000000000000010020040000000000000001000000010000000040080a0020040080400001000005000000000060020140000000a0000000100a0040080600c00c01002000000008030020000100300400c028020000000180200201402800016004010040000000000000200000801002008000010000040000000a0000180c00603404800000000020000000000000100201001005000018020010020000000000000000002000000008000000000000900800c0000000600c018050000000000000e004008020020000080200000000001000000000030080140080200001000000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021fe94043bd280877d5010ff2a021de54043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485e
  | 3 => 0xbd4d0000000000fa0000f0a70004d408800000000000001f800000000012000000000000000008a34c140d80001580012c8003224c4000000006b8ce26352811c000000000000012d1b84f400000000000002650008a51900000000000000000000fd9393d857c0000000000000000000000000bc4e2000000c30007dc0000000091d3f8002a200000000380020609742889d4000000000000000015200029000000000b18dd00051901000000000001d9000001020001d4000cc19d160000000000000007403b0445f4c322c00000c0022f5185640000000000145800130000000000d428c00178000000001324f4000e229549e2d400223460000f40440989a80000021e1211e8003520006d13a4c4000000000000000021100000000000000000b88000000000028a0bc000801bb000914d380a2d867c000000000000009a00000000000508861048570000000000028a62d0d00000a000be00f0002b4550b62583980000041c83c00000000000390000ba1e90ba4a0b8000210000000006511200000000000000458fe80002e33d438d600058470a8803a0004028f000000cf00029a8800000039a72c1e800000000791ef0006e800000000001430000007300000008a000000000000000020843805800234290000ba9a04780000c8c74905e4b702f000158c1000000000001ad31e000c6087078084c00be09208d4b0000000000026b4a06fc000000d2000002560005740015218c0008f800000918321be38e00000000000000000f6000000000000c475819a780000003b8b1000000738000007e80000000022c9b8000000008a1e40008a00000000000000000000000000000009b4469880000000006d0000000000000090800000000754781b93fe0c800000048798000000004200000000024c000000009ec1488f0002908d1130007b8001690000000000046e4f80000007e00000000522000170004740002fa6050292400000456000000000005d872a4b0000000000000000000000000000000004ae0000012e00076c5591500086532000000774f38eb0000006a8de000098aa80000012800201312000001dc0a600000000000000c2800000588e80010000011717e0000008614e000361468a20007b400000000948db8004f8000540360000c40000044a0000000032a708340550000000014900c144001b50000008486100096831a060e8000002740003e800000246000000002f622509a1f2d00009d8004cc000b5000000000e90963a60000000031aa4c0028900025c002692060000000000000000000000460710004b8000002510003a4000670dc000000000000000000034a001200790000000004d000000000000000809006b000000000000003dc0026c0004140000000022000276000658f880005a2640580000
  | 4 => 0x2ec000000005ac0020b244104001872ae0000026e00e3d52a8fb1a000000000000610001ce38c5c0000431b20010d800000000000000727f8000003c6000b9834000000000380004bc001662ca000000000004740025f000008e080000000000127000000000000006380010d000280000000000000014f000000da11001c0010a000096390002382a0714ad800000000001283ae50c7fa67000000001ca0000000014a2de5082d8863bc5800000023c0000000000000119a9741a0010ea4e42a650c80ba4a6000000000002fc000000009c800000124000959c916654c4d8254824d04e89e0000000000040a46c000000000003b00000000000000000000000b20000000027d35600000000000000000000344f0001a3000000ae000000000bb8000e2000f083a000000002260009780000000000000000000284000000000000001f00059c5c800000000c0800362034000001c60b147073208334140000009852200000000000000000744f9091000000091c32b0000000000006bc00000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x151cc23c6454730b318931cc2d8604c7309b988548c26d6215230b6580438c3984390230b618d408c23e649513097d8d544c27b60551308f994544c3396015130c7152324c31c540c930c7153314c31c544c530b3189314c27a6590130ce152404c2786550130ce151404c2d86350130ce153304c31c548c1309d987540c27561d50309e980540c25d6510c309e597400c2796510030e610c400c25f654c030a7191300c27b654c030ae191300c25e63d53209758f54c823e64d4f208f59353c823f64547208f19151c82b8644c3209798f548825d63d52209d987548827561d52209798c548825d63152208fd91538823c6454e20c7d91538831c6454e20d618153883595390220b618d40883595350220d654f3088359530c220d654f208825f63551209718d544827761551209d185544827b60551209e582534823f6454d208f19153482776154d209d185534825e63145209758c514827a65901209e19540482d863501209e997304827a650c1208f596540825f63550209718d540831f6355020c718d540833860550208f990540827a60150208f993530823d64d4c209e983530823e6414c208f59053082766114c209d584530825e63940209758e500827965d0020ce55340082796510020ce5504008279658c020ce552300827b654c020ae1913008339544c020ce55220082d963880209bd95200827b6548020ce551200825e63d53109758f54c423e64d4f108f59353c425f6354b109718d52c423e6414b108f59052c425e6314b109758c52c42d86350310ae59020c425f63552109718d548431f6355210c718d548433860552108f993538423d64d4e109b98b538426d62d4e108f990538423d6414e108f993528423d64d4a109798f528425d63d4a108f990528423d6414a10ce55340843395410210ce55230842b8644c210ce55130843395488210b658e20843395448210ce5531084279609511097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d109ed81534423f64549108f191524425f63549109718d524427b60549108f990524423d64149109e997404427a65101109e9963044278654c110ae191304427a6588110b658e204427865481109798f540425d63d50109e983540425e63150109758c540426e62150109b588540425d6594c108fd91530423c6454c10c7d91530431c6454c10d6181530425e6314c109e980530425e63d48109758f520423e64148108f590520425e63148109758c520427a60148108f992500423d64940109e596400435953900109ed9540042d86350010d654d400427965cc010d654f3004279650c010d654c300427965c8010d654f20042796508010ae590200435953080109e59610042b96484010d654e100427765440109ed9510043595344010
  | 1 => 0x75953542419e98053506796014d419e980525067960149418f99742506b461509419ed8153106786054c41ad58443106b96010c4197d8d521065c63548419ed81521067860548418f59642106b96010841ae583411063f65504419dd95411067b60553319e18154cc67a60153319e58054cc6d96010f318f99252cc63d6494b319e98252cc6796094b31b658332cc67a60d52319e583548c67a60952319e582548c67b6054a319e181528c71d63d51318f992544c66e62951319b58a544c67a60951319e582544c66f62551319b189544c67b60551319e181544c63e651513197997434c71f5410d31b6580434c72f54d4931cb153524c72f5414931cb150524c74f4314931d310c524c65e65cc931d314b324c6d960cc931d3149324c74c528c531ced53504c73854d4131dad4b504c76852d4131ced50504c7385414131dad48504c7685214131d6d0c504c75843141319798f540c67a60d50319e583540c66e62150319b588540c67a60150319e580540c65d658c83197d95310c6cc624c4319dd95310c75a3254031d60c9500c75b3154031d64c5500c65f63553219718d54c867b60553219e18154c867a60153219e58054c863e64d4f218f59353c867a60d4f219e58353c867a6094f219e58253c865e63943219758e50c865e63d52219758f548867a60d52219e583548867a60952219e582548863f6454e218f191538867b6054e219e181538867a6014e219e580538863e64942218f592508863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219dd85544867b60551219e181544863e6515121c7d53534871c54d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534866f6254d219ed8153486786054d2197994534871f5414d21c7150534873454c8521d314e214873b54d4121ce153504875b53d4121d614f504873b5414121ce150504875b5314121d614c504865e63d50219758f540867a60d50219e583540863d6595021cd185540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530874c6254c218f990530863d6414c219798c530867a6014c219e580530874d53cc8219b594320873554d04219d594410866f6548421b318d21086776548421ad191210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500865f6354b409718d52d02b46150b40ae18142d025e63947409758e51d02ba6090740ae58043903596014d40c714f425031c5350940ad185425031c5390540c714c415035853d0140c714e405023f6550040a718d401027b6550040b618d401023e6494b308f59252cc2da608cb308fd9
  | 2 => 0xc3125a4a387328845c670003846646215908e000cb8002a40f8000003fa000000001be81400000408438c41ba0744b05292616e3b0bc0951f639000194112000001a10008380000020c7ec8e0000003b800210000000509d7000000000000de81c0c924350324070002c2680530723443d4a49c60001dc199d41186905c8970c635c001dc2227c89b186000000380003aa19cff00001a00000000434000a5000410000ce1ff15019802a0f1d48342184500068ce490d3a46686b0000004d40003c1bc090259b30000bc001f10006347985e0f805c000842962ac809d82a6698410f60ea0005a8001a82c0000e62e04bc860b20000405612e1c261c789a92d85c8290c32b60504d21502271cde03609200051894064370f706d0366b89d1f33d20200600002000000280b004010000403c030041b00003000080041e0d018040000280a0340000c000240a02800040020000215c24018020001a0080101c110180101c16000020cc0101c0b024080240b01c120a000044010203601003000000240f0080b008000003103c48008210580000c00040070900001c1f0081603c070040003c0b2d001000000040000005080010cc00048011400b01c010080003402000070541a010000040f0001a0202a0a80c0040e0f001004000080c0040e020000480001c0200c020840a03006000030004702c0700c000500400004014140027b6054b439e18152d0e7a60947439e58251d0e7a6094a439e5825290e7b60546439e1815190f5b4314143ce90c5050e3f6550c43ae1814310e5f6550c43b61814310e7b6054f429e18153d0ab96010f429798e51d0a5d63947429e98251d0a7960947429e9825390a796094e429ed815190a786054642c7d4c4350ab96010d42d5d4f5150b5453d4542d5d4c5150b545314542cd90c5150b344314542cd9085150b5b53d4142d614f5050b7351d4142dc1475050b5b5314142d614c5050b735114142dc1445050b3a4314142ce10c5050a3f6550842ad1854210a6f6550842ced095010b3942540429d98754cca7561d53329e98354cca7960d53329e98054cca7960153329e983548ca7960d5232c7d8d548ca7a60152329e580548cb1d5410e32b6580438cad960cca32ce952508cb395494232d6d0e508cb584394232ce951508cb39545423297d8d544ca7761551329d185544ca7b60551329e181544ca7a60151329e580544ca7a60145329e580514ca7b60550329e181540ca7661150329d584540ca7a60150329e580540ca5d6510c32b3588430cad96010c328f992520ca3d6494832b6583320ca5f654c8329bd95320ca3f64544328f191510ca7b60544329e181510cab46150b41ced0950d07394254341c754c43906b96010e41ae58042906b960d0641d694e50907595394241ce90e50907384394241d694d509
  | 3 => 0xe29653b66d06a8cd3bc38ce205c3e80542400a11a5e4269400501106098e2820006304f1323ac880d22cc1acdc92b0001d89f0ef0541ecbd9f0424700749fa2265d0928f21b46b44e83f0002c4bb1a50003e02e9d136a158998382fe46000180252160a8892130614060ca2c429caf1e20720ec598001481e4001aa03e20c0000028c218a68003d043cf6a01326000f58000c4764e705b098478658000004a8c102718a000f21cb228568250120e2758cc0fd27801ce78d10122bc6606901e2a90b9f9126658741564066b10c0001f41a0000ed250001048002b0540440fe20e000af99b27658c149ab2aa70c0015437002000214000000000781a660cc792d2245e89f8370467a8c51b108c858b21cd29e514131483027d49e90900202c3d18b23e308401733087683a12236e138f382d2e267c8b18c32a364ab96d210108108c80604c8db13943222c8e8bb37a168201bb144340a182e0a27bce40601022f0ef85900c84c569023ee184e09002fc360b71a70625a0fc1340ca26d051dd2b8808b5013260010e81af006581059e52f81f467891270154501cc0003dc0011a0a66740d12002c5bc4b0640002e84509e2d659c0014e0ae78c7f80003c000bb9b217a000001ec3ec3885b08f0006f84f8f43c021498990000074e519e3cc0ac1a0251c01042a2062982f8000001ce1b093800214001088fc1703004707e13800063800242394001920002a4a10000003e4baa001ba6fc001b0120644818503a642c1a87f07a2b85a1190000080010417e0b00006a0004540006e000830000000004dc829e10be0008d97d000088100f010e0000e15d1b6060919f
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x58000001018000000000f0000ca00008000000038101800054050000000000000024700000b0003110121480000000044c000000000d5c000000810004000014c5c04314542a60e2a12a0215307150950d06a4b8086292639214960cc931a90e498aa018e145318542503062a0c498a61861506350130c30c8302a7104587654d408828c3a2a6184418618c6055020a30e6aa0801043876551300830caa2c7100418618c6055210a30e6aa0810843876551308430caa2c710421861906054c108b0eca9a80085187454c300430cb22a610021865915384010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x20300040000818875516388020818875516388210818875915308010818875915384010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1408)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 647)*11) 11
  | 3 => packedAt s5K3 (1281+((h/8+packedAt s5K3 (1225+(h % 8)*7) 7) % 81)*6) 6
  | 2 => packedAt s5K2 (244+((h/1+packedAt s5K2 (240+(h % 1)*4) 4) % 13)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfc07ff80fff8383f07e0f87ff0ffe03189e7c
  | 1 => 0xfffffffff03ffffc007ffffffff03ffc1fff8f
  | 2 => 0xfff81ffffffffffff800ff81fffffffe0e3ff
  | 3 => 0xf00001ffffc003fffffff0001fffc003ff03f0
  | 4 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x6a530d88e2895780bc1743c6a78e721b188e3c
  | 1 => 0x2285101121921094002a5488c99214a80b3685
  | 2 => 0x810a24a244244129548009521224a95160c15a
  | 3 => 0xca2c594489071ace694d60049ccb1062bd03e0
  | 4 => 0xc3061870e3863738e718e67000c2183d6f800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0fcc8e0c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37075
namespace PEqualNP.Outside.L_meta_37075
open PEqualNP.Outside.L_meta_37075.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5005fe5401ff55005fc5401ffd4c07fe5301ff54c07fc53017fd0c01fe43007f50c05fc4301ffd4807fe5201ff54807fc52017fd0801fe42007f50805fc42007fcc801fe32007f4c801fc3201ffd4407fe5101ff54407fc51017fd0401fe41007f50405fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc2101ffd4003fe5001ff54003fc50017fd0003fe40007f50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24001ff9012000ffa8090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9024000fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007fe1048003fd0824001ff04120037fecb88022ff65c4011ff32e2003bf99710047facb88022fd65c400dfe32e2003bf19710037fec988002ff64c400fff3262002bf99310007fac988002fd64c400dfe3262002bf19310047fea98801ffe54c4011feaa62007ff15310037fec788002ff63c4001ff31e2000bf98f10007fac788002fd63c400dfe31e2000bf18f10047fea788023fe53c4011fea9e2008ff14f1003ffe8788003fe43c4001fea1e2007ff10f10037fec588002ff62c4001ff3162000bf98b10007fac588002fd62c400dfe3162000bf18b10047fea588023fe52c4011fea962008ff14b1003ffe8588003fe42c4001fea162007ff10b10007fe6588003fe32c4001fe9962000ff0cb1000dfcc388023ff51c400dff28e2008fd94710047faa388023f551c400dfe28e2007ffd0710037fc8388003fd41c400dfe20e2000ffcc710037fc6388003fd31c400dfe18e2000ffc8710037fc4388003fd21c400dfe10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe82188017ff654400b7fb2a2000dfd9510004feca88017fe65440077f32a2005ff5951002dfaca88017fc65440077e32a2005df1951001cf8ca88003ff64440017fb222004ff99110015fcc888003fd64440017eb222004ff19110015f8c888017ff5444009ff2a22005ff55110027f8a888003ff63440017fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c688017ff534400bff29a2005ff54d1002ff8a688013ff4344001ff21a2000ff50d10027f88688003ff62440017fb122000ff98910005fcc488003fd62440017eb122000ff18910005f8c488017ff524400bff2922005ff5491002ff8a488013ff4244001ff2122000ff50910027f88488003ff3244001ff1922000ff4c910007f86488006ff614400bffa8a2005ff9451002feca288017fd514400bfaa8a2005ff14510027fe8288003fe4144001fea0a2004ff10510007fe6288003fe3144001fe98a2000ff0c510007fe4288003fe2144001fe90a2000ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044001fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3dc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6000bf1853007ffea29803ffe514c01ffea8a600fff14530077fe8298003fe414c001fea0a600eff10530007fe6298003df314c001ff18a6000ff4c530007ba6298003fc314c001ff90a6000ff88530007fa4298003fc214c0037fb026001ffd413000ffca098007fd504c003fe2826001ffd013000ffc8098007fd404c003fe2026001ffcc130007f66098007fe304c003ef1826001ff0c13000fb86098007f8304c003ff1026001ff0813000ffc2098007fa104c003fe082600bffd972006dfecb90037fe65c80077f32e400ddf9972001cfccb90037fd65c801b7eb2e4000df59720004facb9002ffc65c80077e32e400bffd9320005fec990033fe64c80057f3264000ff59320005fac99002ffc64c80057e326400dffd5320067fca990037fd54c8019fe2a6400bffd8f20005fec790003fe63c80017f31e4000ff58f20005fac79002ffc63c80017e31e400dffd4f2006ffca790037fd53c801bfe29e400cffd0f20007fc8790003fd43c8019fe21e4001bf98b2006ffea59002ffe52c801bf7296400dff54b2006fdaa59002ffc52c8019ffa16400bff90b20007fa859002ffc42c8001ff996400bff8cb20007fa659002ffc32c8017ffb0e4000ff98720005fcc390003fd61c80017eb0e400bff1872006ffea390037fe51c801bfea8e400dff14720067fe8390003fe41c8001fea0e400cff10720007fe6390003fe31c8001fe98e4000ff0c72005ffe4390003fe21c8001fe90e400bff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff4c32000ff86190007fe20c8003f71064001fe8832000ff84190007ec20c8003ff0864001ff04320057feca9002aff6548015ff32a4003bf99520057faca9002afd6548015fe32a4003bf19520007fec890002ff6448013ff3224002bf99120007fac890002fd6448013fe3224002bf19120057fea890027fe5448015feaa24009ff15120007fec690002ff6348001ff31a4000bf98d20007fac690002fd6348001fe31a4000bf18d20057fea69002bfe5348015fea9a400aff14d2004ffe8690003fe4348001fea1a4009ff10d2000dfec49002bff5248015ff292400afb94920057faa49002bed5248015fe2924009ffd0920007fc8490003fd4248013fe2124000ffcc920007fc6490003fd3248001fe1924000ffd8520005fec290003fe6148001feb0a4000ff18520005f8c29002bff5148015ff28a400aff54520057f8a290027ff4148001ff20a4000ff5052004ff88290003ff3148001ff18a4000ff4c520007f86290003ff2148001ff10a4000ff48520007f84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa
  | 2 => 0x4009ffea6a004ffe5350027fea9a8013ff14d40017fe86a000bfe4350005fea1a8002ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0002fc6250027ffa928013ff9494009ffaa4a004ffc5250005ffa128002efd0940017fc84a000bfd4250001dea128002ff10940007fe64a0003fe3250001fe9928000ff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc6150027ffa8a8013ff9454009ffaa2a004ffc5150005ffa0a8002ff905400077c82a000bfd4150005fe20a8002ef10540007fe62a0003fe3150001fe98a8000ff0c540007fe42a0003fe2150001fe90a8000ff0854000dfec0a0007ff5050003ff2828001ff5414000ff8a0a0007ff4050005fda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffc60a0007fc3050003ff1028001ff0814000ffc20a0007fc1050021ffb2e6012bfd9730097fccb9800efe65cc025feb2e6012bf59730087f8cb9800efc65cc021ffb266000bfd933008ffcc99800afe64cc001feb266000bf59330087f8c99800afc64cc025ffaa66011ff95330097faa998047fc54cc0037f31e6012ffd4f30087fca79804bde53cc025fea9e6012f754f30087f8a798047ff43cc021ff21e6000ff50f30087f88798043ff62cc001ff3166000bf98b30007fac598002fd62cc021fe3166012ffd4b30097fca59804bfd52cc025fe2966011ffd0b30007fc8598003fd42cc023fe2166010ffccb30007fc6598003de32cc001fe9966010ff0cb30007b86598043ff61cc001ff30e6000bf98730007fac398002fd61cc021fe30e6012ffd4730097fca39804bfd51cc025fe28e6011ffd0730007fc8398003fd41cc023fe20e6010ffcc730007be6398003fe31cc001fe98e6000f74c730087f86398003ff21cc001ff10e6000ff48730007f84398006fd60cc003ffa866001ff9433000ffaa198007fc50cc003ffa066001ff9033000ffa8198007fc40cc003ff1866001f78c33000ff46198007fc30cc003ee1866001ff8833000ff84198007fe10cc003fe086600fffd953007dfeca980037f654c0013fb2a600fff9953001dfcca9803ffd654c01f7eb2a600fff1953001df8ca9803f7c654c0073e32a6000ffd9130005fec898003bf644c0015fb22600eff99130015fcc898003fd644c0017eb22600eff19130015f8c898003bc644c0055e322600fffd5130077fca89803ffd544c01dfe2a26001bfd8d3007ffea69803ffe534c01fef29a600fff54d3007fbaa69803ffc534c01dffa1a6000ff90d30007fa869803bfc434c001ffb126000bfd8930007fcc498003fd624c001fe3126000bf1893007ffea49803ffe524c01ffea92600fff14930077fe8498003fe424c001fea12600eff10930007fe6498003fe324c001ef1926000ff4c930007f8649800
  | 3 => 0xf0844206ff042210dffeca9086eff6548437ff32a4203bf995210dffaca9086efd6548437fe32a4203bf19521007fec890802ff6448401dfb224200afd91210d7fcc89080afe6448401feb224200bf591210d7f8c89080afc6448401de3224202af191210dffea89086bfe5448437feaa2421aff15121007fec690802ff6348401efb1a4200b7d8d21007fcc690802fe6348401feb1a4200bf58d21007f8c690802fc6348401ee31a4200b718d210dffea69086ffe5348437fea9a421bff14d210d7fe8690803fe4348401fea1a421aff10d210dffea49086ffe5248437fea92421bff149210d7fe8490803fe4248401fea12421aff10921007fe6490803fe3248401fe9924200ff0c9210dffea29086ffe5148437fea8a421bff145210d7fe8290803fe4148401fea0a421aff10521007fe6290803fe3148401fe98a4200ff0c521007fe4290803f72148401ff10a4200fb88521007fec090802ff6048433ff3024201bf98121007fac090867fc60484037e302421bffd41210cffca09086ffd5048433fe282421affd01210cffc8090867fc4048433ff1824219ff0c1210cffc4090867fc2048433ff0824219ff04121037feca1085aff650842dff3284203bf994210b6fcca1080e7e650842dfeb284216bf59421006faca108027d650840dfe3284203bf19421037fec810802ff640842bff3204202bf990210077cc81080abe6408401feb204200bf590210077ac810802bd640840dfe3204202bf190210b7fea810857fe540842dfeaa04215ff15021037fec610802ff6308401ff3184200bf98c21007bcc610802de6308401feb184200bf58c21007bac610802dd630840dfe3184200bf18c210b7fea61085bfe530842dfea984216ff14c210affe8610803fe4308401fea184215ff10c210c5fcc41085bff5208417ff2904216ff5482105ff8a410857ff4208417ff2104200ff5082105ff88410803ff3208401f7990420bff8c821007fa641082ffc3208401f61904217bf984210b7fea21081bfe510842dfea884206ff144210affe821081bfe4108401fea084206ff10421007fe621081bfe3108401fe9884206ff0c42105ffe4210803ef210840dff1084200fd88421007fa4210803ed2108401fa9084206ffd80210a7fcc010806fe6008401fd3004201be98021007fac010802fd6008401fcb004200be58021037f8c010806fc600842dffa804214ff940210b7faa010853fc500842bffa004214ff900210a7f88010853fe3008429fe1804214ff8802105ff84010853fe100840dfe0804213ffd954009dfecaa004ffe65500077f32a8013ff5954009dfacaa004ffc65500077e32a8001bfd9140017fea8a000bfe5450005df2a28002ff5514009f7aa8a000bfc5450001ffb1a8000bfd8d40007fcc6a0003fd6350001fe31a8000bf18d
  | 4 => 0x802fd620c40dfe3106222ffd4831117fca41888bfd520c445fe2906221ffd0831007fc8418803fd420c443fe2106210ffcc831007fc6418803de320c401fe9906210ff0c831007b8641888efe610c445ffa886206ff94431117faa21881bfc510c443ffa086206ff90431007fa821881bfc410c421ff9886200f7cc431037fc6218803f6310c401fe9886200f74c431007ea621881bff600c441ff3006201bf98031007f4c018806fa600c401feb006200bf58031007f2c018802f9600c40dfe3006201bf18031117fea018883fe500c445fea806220ff1403110ffe8018883fe400c441fe2006220ff8c031087f86018883fe200c441fe1006220ff84031037f8201882fff65c84317fb2e4218ff9972101dfccb90863fd65c84317eb2e420bff1972101df8cb9082fff64c84017fb26421fff99321015fcc990803fd64c84017eb26420bff19321015f8c990863ff54c843fff2a64218ff553210fff8a99082fff63c84017fb1e4200ff98f21005fcc790803fd63c84017eb1e420bff18f21005f8c790863ff53c8431ff29e4218ff54f210c7f8a79087fff43c8401ff21e4200ff50f210fff88790863ff52c8417ff2964218ff54b2105ff8a59087fff42c8417ff2164200ff50b2105ff88590803ff32c8417ff1964200ff4cb2105ff86590863ff51c8431ff28e4218ff547210c7f8a39087fff41c8401ff20e4200ff507210fff88390803ff31c8401ff18e4200ff4c721007f8639082fff60c843dff3064201bf98321007fac190802fd60c8417fe3064201bf183210c7fea19087bfe50c8431fea86421eff143210fffe819087bfe40c843dfe206421eff8c3210f7f8619087bfe20c8417fe106421eff843210f7f8219081bff658842f7fb2c4217ff9962101dfccb1085ffd658842f7eb2c4206ff1962101df8cb1081bff64884017fb24421dff99221015fcc910803fd64884017eb244206ff19221015f8c91085fff548843bff2a44217ff552210eff8a91081bff63884017fb1c4200ff98e21005fcc710803fd63884017eb1c4206ff18e21005f8c71085fff538842fff29c4217ff54e210bff8a710877ff4388401ff21c4200ff50e210eff8871086efd628842fffa944217ff94a210bffaa51085ffc528843bffa144200ff90a21007fa8510877fc4288401ff9944200fbcca21007fc6510803fd3288401fe1944200fb0ca210b5fcc31085fff518840dff28c4217ff54621037f8a310877ff418840dff20c4200ff50621037f88310803ff318840dff18c4200ff4c621037f86310803ff2188401f790c4200fdc8621037fec110873fe60884037f3044200ff58221005fac11081bfc60884037e3044217ffd42210e7fca11085ffd5088439fe284421dffd02210e7fc8110873fc4088439ff184421cff0c2210e7fc4110873fc2088439f
  | 5 => 0x8331157fcc198806fe60cc401feb066200bf58331087f8c198806fc60cc449ffa86622aff94331127faa1988abfc50cc457ffa06622aff90331157f881988abfe30cc421fe186622aff88331157f841988abfe10cc455fe0866206ffd963111dfecb1888ffe658c4077f32c6223ff5963111dfacb1881bfc658c4077e32c6206ffd9231005fec9188a7fe648c4057f3246200ff59231005fac91881bfc648c4057e3246223ffd523114ffca91888ffd548c453fe2a46227bf58e3111ffea71888ffe538c447fea9c6223ff14e3114ffe8718803fe438c401fea1c6229ff10e31037fec518803fe628c4017f3146200ff58a31005fac51881bfc628c447ffa946223ff94a3111ffaa51888ffc528c453ffa146200ff90a31007fa85188a7fc428c401ff9946200ff8ca31007bc6518803fd328c401fe1946200f70ca31115fcc31888fff518c40dff28c6223ff54631037f8a3188a7ff418c40dff20c6200ff50631037f88318803ff318c401ef98c6200fdcc631037fec1188a3fe608c4037f3046200ff58231005fac11881bfc608c4037e3046223ffd4231147fca11888ffd508c451fe2846229ffd0231147fc81188a3fc408c451ff1846228ff0c231147fc41188a3fc208c451ff0846206ff0423113ffeca9889eff654c44fff32a6203bf9953113ffaca9889efd654c44ffe32a6203bf19531007fec898802ff644c401dfb226200afd9131137fcc89880afe644c401feb226200bf59131137f8c89880afc644c401de3226202af1913113ffea89889bfe544c44ffeaa26226ff1513113ffea69889ffe534c44ffea9a6227ff14d31137fe8698803fe434c401fea1a6226ff10d31007fec498802ff624c401f7b126200bbd8931007fcc498803fd624c401fe3126200bf18931007d8c498802ec624c44fffa926227ff9493113ffaa49889ffc524c44dffa126200ff90931007fa849889bfc424c401ff9926200f7cc931007fc6498803fd324c401ee9926200ff0c93113ffea29889ffe514c44ffea8a6227ff14531137fe8298803fe414c401fea0a6226ff10531007fe6298803f7314c401ff18a6200f78c531007fec098802ff604c44bff3026201bf98131007fac098897fc604c4037e3026227ffd413112ffca09889ffd504c44bfe2826226ffd013112ffc8098897fc404c44bff1826225ff0c13112ffc4098897fc204c44bff0826225ff04131037feca1888aff650c445ff3286203bf99431117faca1888afd650c40dfe3286203bf19431037fec818802ff640c443ff3206202bf99031007fac818802fd640c40dfe3206202bf19031117fea818887fe540c445feaa06221ff15031125fcc61888bff530c421ff2986222ff54c31087f8a618887ff430c421ff2186200ff50c31087f8861881bff620c401ff3106200bf98831007fac418
  | 6 => 0x1ff100640bff08032187fc20190c3fc100c80dffb2c822fbfd964117ffccb2080efe659045ffeb2c822fbf59641037f8cb2080efc65904057eb248202ffd5241017fca92080bfd5490405fe2a48206ffd8e41007fcc720802fe6390401feb1c8200bf58e41037f8c7208bfff539045fff29c822fff54e4117ff8a72080bff4390405ff21c8200ef90e41017fa872080bfc4390405de21c8206ffd8a41007fcc520802fe6290401feb148200bf58a41037f8c5208bfff529045fff294822fff54a4117ff8a52080bff4290405ff2148200ef90a41017fa852080bfc4290405de2148200ffcca41007fc6520803fd3290401fe1948202bf9864117ffea32081bfe519045ffea8c8206ff14641017fe832080bbf4190405fba0c8206ff10641017e8832081bff609045dff3048201bf98241007fac120802fd609040dfe3048201bf1824117ffea1208bbfe509045ffea84822eff14241017fe812080bbf4090405ff2048202ff10241177fc61208bbfc309045dff104822eff08241177fc212081bfc109045bffb2a822dbfd954116ffccaa080efe655045bfeb2a822dbf5954116ff8caa080efc65504057fb228202ffd5141017fca8a080bbe5450405feaa2822def55141017f8a8a0803ff63504017fb1a8200ff98d41007fac6a0803fc63504017e31a822dffd4d4116ffca6a08b7fd535045bfe29a8202ffd0d41017fc86a080bfd4350405fe21a8200ffd8941005fec4a0803fe6250401feb128200ff18941005f8c4a08b7ff525045bff292822dff5494116ff8a4a080bff4250405dfa128202ff90941017fa84a0803bd4250405fe2128200ffcc941007fc64a0803fd3250401fe1928202bfd854116ffea2a08b7fe515045bfea8a822dff14541017fe82a080bf74150405ff20a8200ef90541017f882a080bbc4150405fa20a8200ffd8141005fec0a08b3fe60504037f3028200ff58141167f8c0a0806fc605045bffa82822cff9414116ffaa0a08b3fc5050405ffa028202ff90141017f880a08b3fe3050459fe182822cff88141167f840a08b3fe1050459fe0828210ffd9731125fecb98893fe65cc4077f32e6224ff59731125facb98843fc65cc4077e32e6210ffd9331005fec9988affe64cc4057f3266200ff59331005fac998843fc64cc4057e3266224ffd533115ffca998893fd54cc457fe2a66224ffd4f31087fca798893fd53cc421fe29e622bffd0f31087fc8798803fd43cc421fe21e6210ffd8b31007fcc598802fe62cc401feb166200bf58b31087f8c598893ff52cc449ff2966224ff54b31127f8a5988afff42cc401ff2166200ff50b3115ff88598843ff32cc401ef9966200ff8cb31007fa6598803dd32cc421fe1966224ffd4731127fca398893fd51cc449fe28e622bffd0731007fc8398803fd41cc457fe20e6210ffd
  | 7 => 0x190cefd658c817fe32c6403bf1963205ffec919002ff648c873ff3246402bf992320077cc91900abe648c801feb246400bf592320077ac919002bd648c817fe3246402bf1923219ffea9190e7fe548c867feaa46439ff152321bdfac7190cfff538c867ff29c6433ff54e3219ff8a7190e7ff438c801ff21c6400ff50e321cff887190cafe628c867ffa94640bff94a3219ffaa51902ffc528c873ffa14640bff90a32007fa851902ffc428c801ff9946400f7cca32007de651902fff618c801ff30c6400bf98632007fac319002fd618c817fe30c6433ffd463219ffca3190cffd518c867fe28c6439ffd06321cff8831902fff608c871ff3046401bf98232007fac119002fd608c817fe3046401bf1823219ffea1190e3fe508c867fea846438ff142321cffe81190e3fe408c871fe2046438ff8c2321c7f861190e3fe208c817fe1046438ff842321c7f821190dfff654c86f7fb2a6437ff9953201dfcca990dffd654c86f7eb2a6437ff1953201df8ca99003ff644c8017fb226436ff99132015fcc899003fd644c8017eb226436ff19132015f8c8990dfff544c86dff2a26437ff551321b7f8a8990dfff534c86fff29a6437ff54d321bff8a6990dbff434c801ff21a6400ff50d321b7f886990dfff524c86fff2926437ff549321bff8a4990dbff424c801ff2126400ff509321b7f88499003ff324c801f79926400ff8c932007bc6499003ff614c8017fb0a6400ff98532007fac299003fc614c8017e30a6437ffd45321bffca2990dffd514c86ffe28a6436ffd05321b7f88299003ff604c8017fb026435ff9813200dfcc099003fd604c86bfe3026401bf181321bffea0990d7fe504c86ffea826435ff141321b7fe80990d7fe404c86bfe2026435ff8c1321aff860990d7fe204c86bfe1026435ff841321aff8209902fff650c8657fb286432ff9943201dfcca190cb7e650c8073f3286432ff59432195faca190037d650c8013eb28640bff1943201df8ca1902fff640c8017fb206431ff99032015fcc819003fd640c8017eb20640bff19032015f8c8190cbff540c863ff2a06432ff5503218ff8a8190d2fe630c865ffa986410ff94c32197faa619043fc530c863ffa186410ff90c32007fa8619043fc430c8677f3106432ffd483205ffca4190cbfd520c817fe2906431ffd083205ffc8419003fd420c817fe2106410ffcc832007be641902ffe320c801f71906400ff4c832007ba6419003ed320c817ffb086400ff98432005fcc219003fd610c8017eb08640bff18432197fea2190cbfe510c865fea886432ff1443218ffe82190c7fc410c817ffb006430ff9803200dfcc019003fd600c8017eb00640bff1803200df8c0190cbff500c861ff2806432ff54032187f8a0190c7ff400c861ff2006430ff10032187fc6019043fc300c86
  | 8 => 0xf84143207f820a182fff659087f7fb2c843fff9964201dfccb210fffd659087f7eb2c840bff1964201df8cb2100afd6490805ffaa48402ff952420177ca92100bfd549087fdeaa48402ff1524205ffec721003fe63908017f31c8400ff58e42005fac72102ffc639087fffa9c843fff94e421fffaa7210fffc5390805ffa1c8402ff90e42017fa872100bfc43908057f314843fffd4a4205ffca5210fffd5290817fe2948402ffd0a420177e852100bef4290817fe2148402fb10a4205ffec321003fe61908017f30c8400ff58642005fac32102ffc619087fffa8c843fff946421fffaa3210fffc5190805ffa0c8402ff1064201778832102fff609087dff3048401bf98242007fac121002fd6090817fe3048401bf182421fffea1210fbfe509087ffea84843eff14242017fe812100bfe4090805fe204843eff8c2421f7f861210fbfe2090817fe104843eff842421f7f821210f7ff655087b7fb2a843dff9954201dfccaa10f7fd655087b7eb2a843dff1954201df8caa100aff6450805ffaa28402ff95142017faa8a100bfc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8400bf18d421effea6a10f7fe535087bfea9a843dff14d42017fe86a100bfe4350801df21a8402ff50d42017f886a100bbc43508057fb12843dffd49421effca4a10f7fd525087bfe2928402ffd0942017de84a100bfe4250801df2128402ff109420177884a100bec4250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8400bf185421effea2a10f7fe515087bfea8a843dff14542017fe82a100bbf4150805fe20a8400ffd8142005fec0a10f3fe60508037f3028400ff581421e7f8c0a1006fc605087bffa82843cff941421effaa0a10f3fc5050805ffa028402efd0142017fc80a100bfc4050879ff182843cff0c1421e7fc40a10f3fc2050879ff082843cff04142087fecb990d2ff65cc869ff32e6403bf997321a7facb990d2fd65cc821fe32e6403bf19732087fec999002ff64cc877ff3266402bf99332007fac999002fd64cc821fe3266402bf193321a7fea9990effe54cc869feaa6643bff153321a7fea799043fe53cc869fea9e6410ff14f321dffe8799043fe43cc801fea1e6410ff10f321a7fea5990d3fe52cc869fea966434ff14b321dffe8599003fe42cc801fea16643bff10b32087fec399003fe61cc8017f30e6400ff58732005fac399043fc61cc869ffa8e6434ff947321a7faa3990d3fc51cc877ffa0e643bff10732087fec1990ebfe60cc8037f3066400ff58332005fac199043fc60cc8037e3066434ffd43321d7fca1990d3fd50cc875fe286643bffd03321d7fc81990ebfc40cc875ff1866410ff0c3321d7fc41990ebfc20cc875ff086643aff0433205ffecb190ceff658c867ff32c6403bf9963219ffacb
  | 9 => 0x400000c00000200000800000000800200200002000601400000000000600200600001000200401000400600200400002000e00601400200a00200200600400c00200200000400001a00400400200000202800000400000e00000e00200200000400000200000000000001800002400a00000000400200000000200200000000600401400000400a00000000200200000200000000200000000400000000400200000001401000000000a00e00c00000202600400400001200000401000000801601000000000400000000a00000600400000000200200802800000200800200000e01600201e00400000000200000600c00000000800c00000000000400c00800600000000400c00600404200400200800200400000000000600000001200800800200200000000200400600200200600000000001a00200a00c02400200000400200000200000600400000400200000000200200200400001200001000400000000000001c00600000000000400a00200201200200610ffd964321dfecb2190ffe6590c077f32c8643ff5964321dfacb21843fc6590c077e32c8602bf59243017fea92180bfe5490c05df2a48602ff5524321f7aa92180bfc5490c057f31c8643ffd4e43087fca72190ffd5390c21fe29c8602ffd0e430177e872180bdf4390c21fe21c8602f710e43087fec521803fe6290c017f3148600ff58a43005fac521843fc6290c87ffa948643ff94a4321ffaa52190ffc5290c05ffa148602efd0a43017f88521843ff6190c01ff30c8600bf98643007fac321802fd6190c21fe30c8643ffd464321ffca32190ffd5190c87fe28c8602ffd0643017f8832180bbc4190c21ffb048642ff9824300dfcc121803fd6090c017eb048610ff1824300df8c12190fff5090c85ff2848643ff54243217f8a12180bff4090c05ff2048642ef90243017f8812180bbc4090c85ff1848610ff0c243217fc412190bfc2090c85ff0848642ff0424320ffecaa1906ff6550c83ff32a8603bf9954320ffacaa1906fd6550c83fe32a8603bf19543015fec8a180bff5450c05ff2a28602ff55143017f8a8a180aff6350c83ffa9a8641ff94d4320ffaa6a1907fc5350c05ffa1a8602f7d0d43017fc86a1803be4350c05fe21a8602ef10d43017b886a1803ff6250c017fb128600ff98943007fac4a1803fc6250c017e3128641ffd494320ffca4a1907fd5250c83fe2928602ffd0943017f884a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c017e30a8641ffd454320ffca2a1907fd5150c83fe28a8602ffd0543017f882a1803ff6050c017fb028640ff9814300dfcc0a1803fd6050c81fe3028601bf1814320ffea0a1903fe5050c83fea828640ff14143017fe80a180bfe4050c05fe2028640ff8c143207f860a1903fe2050c81fe1028640f
  | 10 => 0x3a46040c8000db226125f9fdc0000001578000db819f00017d452200022b20944e41cf111800036038c37283204307810001134da41443e583d0000000000000000000000000000000002d280005800000f480000002490000b6845c3df30388110007523f984880005fd12c18ccc0400000000000007f911a10b4b4e4be36e8000ea22ec181809400000000002bc42a6553c7829c93200016c178c00014a0bc1eb817800000011500000000000000894000000000000014b0000f9400000023810280000002670b1c00050e00021440000000000000b5000000000007cc1500818ddc6840003948000bf800000000005ee7f1000000000000010d000000013c00005dc15c00041b99087360000000e589da00021c972ceea5df3740a6400000000000000000001ea9840000409344800094c74b1c2941104c27d06302e0a562d12d509cc37837f000164000000000000000e02200800800000400200600800000000600800200000000200400c00000200400000000600a00000402800800400000800600000800000000000600000400000400000000a00000000000000000200600000400400000000400000000000000000000400600000000000200200000000800000000a00e00800000800000200200001e00000600c00400000200400000000400001000c00000200a00401000000400000400c00600400800801200200200000801e00000a00200800400000400200000000400800000200600200200000000600c00400a00800a00000000200800201801a00201000a02200400c00000e00400000200000a00a00000000800600801400200000400000000c01800c00001400600801800000401600400200000000a00000000600001000400200200000200200000000001000000000800200200601000200001400800a00200a00400400a01800000000000400a00201200600000000000a00400200800200800601a00000600600000000000000000400200200800400000000200000400e00000600400002a00000200000600800000000400200000600a00000000200000000600000000400000800200400a00000000600400800400001001000000400200200000400200e00001400200200600001a00a00400000000200000000000000a02800200000000000000200400000200200000400000200000400000400000600003a00c00600000200400000000000000200000000000000e00000400000000000401200c00800600201400000600000000000000000000000400000400000200000400000400400203600000200001001000001c01200200000400000000600001401400600200000000200000600000800400000200000200400000202200001e02200000200200000000001a008000002012002000018006002008004
  | 11 => 0x1d000000000000024aa1140000c700000001e000040200001f40002c7800000000000000000001cb0bc811400000000000000280000000000000000000003ce9420f000033096270e000000088800d1bc8000d9a3be000000000000000000010520002668000b787081bd800014436502a116cd5e654000000105c6cf2991f04000000000000000037d000000000000000000001ba36f000000002400000000001ea00002300002b4000000000000000032317646600002f58000bd0000000000000000037a9294c3e7ec0000fbc0000000b10000fea00000017cc0003634029bdc1e60001a81f4ccf600010c80005d40002cc89180000001320fd47106f90001cb03941a20000000f5800000018505067583140ac46be06e2ae991466c7d70e10000da849f2d919b800070b19b9e0c8762f900000000004a40000ca40e02fd00015900000003dd1efcebe0003ea000073000012782d8000000000000040e0eb00000000b200033600005d6244000089c4d82a622898d0ef035e1910078ff682220014fc1280003d68c50e54000000000000000000014f400047500000000000002c09408b6081c0d489a8a8a00005600000006480000cb058458330205b0000000000204cba44d0000000000000012d0ca8000000000000030e3430cc85547fc000000000023e00000000001047d8343142806400034380000002c100000000006cb1ef15cccce5af0fd80b8c4400000008380007d500000000000000258000a0600000014b800000000000000005470b587f82be2c93269dacb98000000000000044900000000000000000000000000000000000000000000000003fd1d00000fd41752c901082a644f30780000000000000000c320000450ce8d4800000000006d46111ac00000000000000000000000000101cc2615e2aa000000005b00007c800068c00000000005de0001da800000000000000002de000000063a0000ca8fcc000577000050c0000002f292b80007120001f2000000000000004d200e0d400000007720b90490000000000000063e000000000071a4780000000b0c56600000000000002a60c84aa6000000000000075d3f68de800015b00007f000000000012d4000000000000c0000000000f080000003aa00000003c71f80000000000401955436c20d2180000e604af003841876664922f0420adc000103000000000000000000000e111e80009e200000000000005702a182600001470000a9c00068417c0cb80000000000000dec000000203d050572000000005e2550001df400011c1f10278322000000000000000005286143426093721b440000471d897d84fc0003ff11744ea00000006f800000032606cc0000000000000eb20003539fb816a0002dc0000000000410800083265c2218a6ca800000fc000000000008680
  | 12 => 0x1e20359e880000003571068ee677e000000000054f1359b4090a00019a9f800000b73ab9ae475a71f11300000001ab0000000b9a6eb0001d9c00000000014842f60002be0000f2200000000000005cf00015580007b924b00009226591db890c0000003e902740004e324214440000000000000cb048800000006e43c50001f7400006123a03a47445800000840ca470f0a114580005500000ec000071e14c000070800006d1a4c4a000000000000000003f10000cf200017911f0c6238a03206e40000000001c80dae00040918bc2da1c800000000de25922c80004d000021880e849863725d810c34c00030b80000000930000000b3601a000041049600020f9c50f3e70a32f1bb02b24013c60e7cd385ae000000000000000011c800000000020e8f6a34023097c400000000000000003ee0000d48cf80000002020d74674151a12c000263000082c68c27027780f400045a25d104c35c1dc00000010480002df18a4d462710000000b220000000e3835e0000000000dda00000000000001e03331c440004cb0000da00000002461c94bfc6883388120fbc58d0ed884c01084a40c0c583142e613017746242e82f90a881d02410cf1aac7b07b33d51f1c5727a800000000002140000f6cc820002ca8000000000000000000078b29f1a540000000000000eda00000000000000c200000000524ca0f980000000000000000f9e831000000050a80923415e4bb0079000880c3860aa000090000000000004fc00005d1e481d4f8438b0000d3c00000000000000e800028a990000045500000000b40000000000000000000000055862639700008e200000013e477e00005c8bb4a005fa097800000000030180004500d300000009b003835b8000f5e6430000000f2000003b800051a4151e69a50e860ab0ea8e441f63ba0791d1904e11e33d1120fde35713a06c80006350ab0d380003921c1000000046438019c8b480000000000dc40000000000000000000000000061b1ad1f6c2d23eb000000000065b39b00006b80e00000f740080002b40424bb83b911d0df809881100005041de3fb12b85c068819610b9314e467f60e60324a0a7c040aa0b000000012e10a400000013b1b8c33670531919b400000018a998d02e5a32db80004be2e4197800033a51f1b68000a924110000000ed000000000000000001d08000f4c2c31b3800000053937f00003fa0833911be8b560002620dc419400003699ac17a00002e000085e1e800008000003411dd928495800000000000000000000000b2639c00005240002020c080009002ae26f80000000000000000aa200000000000004671f200000004180000000d2c78038980000000000000000ee0000000018c0001aa04b860c00000000000000000000000e540004f70000ccc43c18c3d919bc0004
  | 13 => 0x6e70000594c5a0000058b340cc5d02af84f86ba0b041f19cc0f63f7000000023612901885e8d3a3f635b03b400017d0fc927041000026100b40000000000d2c7ae00007710cc00059f33a89b8ee25f025480008ca000137800000069a0d68dd8fe04b800000009b25fb2b6800000000000004489b644612716a4ec00193b19980fc6116014037c72e28b2d6811000011a1550778e8200032b0f10cc4000000000000077600000009040001cca1240003092448848cc86b40b50a840be1b52d0000018651b254035000000000000000002b01d58000de40000000000a8c1ec2a68ff011210040f1e08b7200000011e8a520713ec80000002dc00015640002d700000000002a5000000000000017a20c065a00036412045080003cc800000000000018c00000000001ad400077b0000000e3876935080000004420000000b4c00040d937457082b00020bc00053a1650ba450000000000000000000000b500001c03c500000000003d58c290a800014e80000003c103120d0a300000001e58c5428826783c467e000000000038c0000000580aa442700000000004501c80000000457000000000000027813a806000000000000540000a89f68b680001fa08940001ee000000000000000000000006a90c4000000000000000000040d80000000000000000000000022b00000000000002af00000004d739383700000000001dbcbcc00028097b825a05700000009ce75e2c600000000002e380001bc35534f20503e20003e6800000025b00b00000003cc0000000f3603e00019d800000000000000000cb00000000000000000000000000000117000048300000000000000000bcd0881541db0b6ca8800014b942000000000019a80001d70000b54e6a60c00000000000000001c080005c80001a041a01e6000000000079700000000000001568e79014000000000016400a0000000a9400023b9ca0efe5e92fa0000000000000000000000000001347480002891e3447800004f8c69086497054000000000014b147800049303f875856a0003db18f8000024000000000000000014bc0006e04230000d4405e28b9a6cf0e0091840000e20000000000000029e00006e800047f03287649dc58e227041c00033c27400000000000000a1895a64f41904e0e2c490051859c3e066111d800038863918b90340004cc00004d0698313000000047c0003da00002660002b59cc87f280b000099cdc2000000087c79e403000069504024800000008dc00005680002ec0001929a980005e40000000000000000135083800000000010982d02c4902000022900004d830c3ae2cc000070e6053b316842d075535e1ba85040000989ce000011308b87041c67940000000fe820a000000000000000002387f436100003fcc487ca2fc00000007e12dd80005340000000
  | 14 => 0x9c5433443504380000000001822040e800003a618e0c742560001d90a7800030b0c4432853807e8aa00000001b209280f000000000000008480be0ac854075000016680000000dc00000001da0000000fac2b41b708d4f0810541e1a3400000015b07fc91c840000000096e2930cc14a000078637893ac8a41d11a40d1cf101fa315953857c48f2e49a3cdfe00000013a419e53500000006480002950d88ca6000000000000000011f800000000034180000000f800000000002ba000107800000000020e429a15723f12d8f3a63f15e85b800000011b000000000000016c488e3ec296000025044100000002584d100000000003e81941620702000000077c00000000016583d400026996740005ed0001f14a3200023791b00000a01e595d40001d324e96f47524d52010c3400a6fd2130d3479043e0d2189c5b213a04311604cc6800480ed021e74d00003d8bb66db0348000bae18e0000000f6e35100000006f000035c00000380001e988bce680b3000000000000000000000006da11c105077000001a8000000852000000000053b3569718ec25ef34c031100483838d01809c201b1631cf4c6c53610484382041271d90ea8b445d439889fc8541bf0001f7026049200015840000000000000a3a0000000000de8000000000000040f1558000c8e0001ec95d80000000000000bf200000004600000723648c1800000039080000007d127f1b7900221b0a402582023450081c342fe525011182c44800000011e4000092000035400000038d96cc0000000000f8c00000000011ec000000009800065600032700005c200000013801cc6b03b700008fa0002538000d864452bc1fa000012b21f9b7c0fc699000000000023200002a44f6310000000000061a0000c6411a749000000000041b14780003b03bd0001650462000000000000000007f1aec00076500000000002a400011cc0002f50001d6cd240000f2137032400026d1768d6200020b000080a5d5140800000000002c0000000793000108cce02ce0000000000531000000000039d00000000005ba2b500003ce7df1b593d0d5035907501445662543bca03832e30b0c81f9486c74428e1aa800000002780000007850000af0cca00005f1a44f3400000003000000001c30000d846ac00000000000002e192f4e8e0000000084f400000000000afa40b31e00ac4f87cc0000000c9400000021040000000dd90480000000000000ddc0003e70a503ee60e0000000000682000000091400026480000001d20000c30fa06e600002549bc08f00010e830464410e81388d24fd4270000ab600021a05cc0004bc2690d28440080073800098606c00000004ca70300018f4000193000068ccfa00042800003087e6000000000000018e1bbc46e0002e712e400064b000058cf3846a0000000990
  | 15 => 0xe3c0001dd0000c980fa2f01a4888817432317700002fc28a1e503949542a900000008405d62b6062c0007b001a0334000338000000000000000000000004220da000000000017e0c3cb160001e00000e025072c380000000000f5909090c0c524d19680000003dc026c0007f8088000000000040e8000e0800017180000001402df800093055c0000000ac665d18009741f87a5000008cae84a032b857000059e41aa0f4b823b51658a240000000000a40b080000e39cbc0001ce40d1cf0ca22621f89418b8800000000000000000d018b0000000000000000082a3d48000c4261d08a8000ac0000000000000003b00010e09d837314e00005c05094298000d1609130c1828a202fa000000046600000008b0eb466800000000000000520000000000000000000020527b0000000000000000028c777000000067a000000000058a1ed05a0ce40006c600000000000000000080c24137167a1080003e103b1b100002950ea1b3000000003d00006304c707b80000ce3d12a09af40f80001de00009f8514259800000000000000008d63ff0000000000000000000000077c000128c00000021900002a47e70b093cc6a60000000c1400000000000980ac0001900000d4058a2ad08e4f883270000000b0a73a0001fac04e000000000000059c00000000000003a99820bee0000689d5817e5691d293189640a61d3800000024700000001823690db89e000038025113883ca018166000000003f000000000061e02a800107600000001a800000007c92d057e523419912c000000000000050e000000000000057100007140005c2000000000049e0000aec0003562b2800024c10c00005140006d60001c5ce3062501b16d80000000000000d6424500000000002d217f9bf000033400000000000061f01e78cf06c01699784c0c0000720c38f7a000000000045480d129943c75800000000000000000000000f2a7fd0c780000000002608b100002b741b10dccfe1ef0001f180003af07100005fc6d530e02c49361210000000d660001c18000d0a00021080000000000001b045ce7890001ef0cd281f1b6000000057f00000006cc00036c15e805817109507d800042c0990000e3a0000760000a2600000013ec6e05d128613940007fc000130029e0002458b88d9408100000002b03ce2e513986b67be000000000000000017000007a439200000005e704d1cb40007ff28d0fb4bd8011000000081c3ea3b1152c00000000009080001e10000e8c00000000a9c30e6e2dd26b04f4a1600000016b0fd2000202059800000000b9a5c298000000000000000022f800060e11100000007ac0000001b1c0000001fc1d3c00000000000000000000000f9c0002d63c900000000000291a380000000000000fc872b14900003a04f52901e606ea0503e1
  | 16 => 0xd880000007741c9997c3920ce3799c2400015d4060e2475011439f89486645e004e00000e618d4030fc8a665583b614b40002513629a405e204111810a00666e900000000003da18f14d010803c0001ccc42c0001aa0000442000000000031222d01c9a2902c000000000000025e3f9093400000000000003384102298000eb86fb00007d400027a38c9eec0001802ab949c00057e000000085c28e3830264000000000000000000023b000000014e00000000000002721608602000000000000000000000003c60002b3800000074203408047d256f00000000004663a280000007a3000000000043c0928000a844631e3201c0004940000000000000000000000008800010f45be00009a8000d7c00000000000002792581434ac40000b21e843e81392a40bece9c000000208c4da2e50000f40b6a0001640e6800013b1ca06b000000010e042834e4251e91e9c0940db0001188c003c3000035c0000002368dd06620000001b38ba63d42030358e720002f5165c7b84ff020000000000035f9e380005370000000000000352800000000018118340001190000000e76211000000023a0000b793c841867e22617fcb8a8471be1c1c1b229f4268214e7c000097042c518000328034809200000000008563a6000213cc5c0000001bc0c464f824693e8a447c900020fc000000000000000000017b00000005242bd800081877a369814c0000000000000000000000000037a1202f10c6c00000c1778000a4c0001b0185417608b39312ad05a6f80ba18ec06e7483d88cf80000000000230c401cd00019dc0004400000cec000000000000003e4170001804ff427734f8000000000000000090e000000048c0000002980000142000000000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101be7c654c91000dfa704c91005cff760c910004fe760c910004fd760c91005cfc760c91002d7e750c9100057d750c9100067f650c9101967c650c910006df630c910086dc630c910006ef620c91005eec620c910005f6710c910005f5710c91000dfa700c910005f9700c91023cfe76905100067f659051017e7c6590510016be6490510006bd6490510014ff765051000cfe7650510164fd765051000cfc76505100067f655051016e7c6550510006bf6450510016bc6450510005fb705051000df8705051000cfe76cc51000cfc76cc5100067f65cc5101267c65cc510006df63cc510086dc63cc51000dfa70cc510005f970cc510104fe768c5100067f658c51011e7c658c51000df8708c510084ff764c51000cfe764c51012cfd764c51000cfc764c5100067f654c51013e7c654c510005bf744c510025bc744c510006df634c510006dc634c510005ef724c510005ec724c510005fb704c51000df8704c510144fe760c5100067f650c5101167c650c51000dfa700c51000cfe76c851000cfc76c85100067f65c85100c67c65c8510006ef62c851005eec62c851000dfa70c8510005f970c85100a4fe76885100067f65885100be7c658851000df8708851005cff764851000cfe76485100ccfd764851000cfc76485100067f65485100de7c6548510005bf7448510025bc7448510005df7348510005dc7348510006ef6248510006ec6248510005fb704851000df870485100e4fe760851002d7e75085100057d75085100067f65085100b67c6508510025be7408510005bd7408510005de7308510005dd730851000dfa7008510005f8764c110006f8764c110004f8764c1100077b754c11023778754c1100077b654c11023778654c110007bb744c110007b8744c11000dfb734c11000fdb734c110007db634c110086fa634c110086f8634c110007d8634c110237da534c110237d9534c110005fb724c110007da324c110007d8324c110007f3714c110035f8714c110007f0714c11000efb614c11000ff3614c110237f2514c110237f1514c110007db314c110007d9314c110005f87648110006f87648110004f876481100077b654811022f786548110005fb7348110005f9734811000dfb724811000feb7248110007eb624811005efa624811005ef86248110007e8624811022fea524811022fe95248110007f37148110035f87148110007f0714811000efb614811000ff3614811022ff2514811022ff1514811000dfa76c411000efa76c411000cfa76c41100077b65c41102277865c4110035fb73c4110005f973c4110035fb72c4110005f972c411000dfa71c411000ff271c411000efb61c411000ff361c4110037f251c4110227f151c4110
  | 1 => 0x8d10086fa3018d10106dd3018d10084ff7690d10004fe7690d10004fd7690d10084fc7690d100067f6590d1021e7c6590d10006bf6490d10016bc6490d10005f67190d10005f57190d1000dfa7090d10005f97090d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1020e7c6550d100067f65d89100067c65d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910014fe74d8910004fd74d8910014fc74d8910084fe73d8910004fd73d8910006ef42d8910006ec42d8910034ff70d89100e4fd70d89100e6ef20d89100e6ed20d891002d7e75989100057d75989100067f65989100067c6598910006ef62989100cdf5719891005cff759891001cfe759891005e7e759891001c7e7598910004fd759891005e7d75989100047d759891005cfc7598910014fe7498910004fd749891005cfc7498910084fe7398910004fd739891005cfe72989100ccfd719891005ef571989100f4fd709891005ef9709891005efa20989100057f755891002d7c75589100067f65589100067c6558910005bf7458910025bc7458910005df7358910005dc73589100f5f77158910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df7358910084fc7358910006dc7358910004dc7358910006ef72589100f4ff7158910006f771589100ccff7058910006fb70589100e4fe76189100067f65189100067c6518910025be7418910005bd7418910006ed621891005cff751891001cfe7518910004fd751891005cfc7518910014fe741891005ebe7418910014be7418910004fd741891005ebd7418910004bd741891005cfc7418910084fe7318910004fd731891005eee7218910006ef421891005eec4218910034fe7118910034fc7118910034ff701891000cfe70189100a4fd701891005ef9701891000cfc701891005eef201891005efa20189100a6ed201891005cff7690910004fe7690910004fd769091005cfc76909100067f65909101fe7c6590910006bf6490910016bc649091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101ee7c6550910016be6450910006bd6450910005f77150910005f47150910084ff76cc910004fe76cc910004fd76cc910084fc76cc9100067f65cc9101a67c65cc910006ef62cc910006ec62cc91000dfa70cc910005f970cc91005cff768c910004fe768c910004fd768c91005cfc768c9100067f658c91019e7c658c910025be748c910005bd748c910006df638c910006dc638c91000dfa708c910005f
  | 2 => 0x24e7d20d951024e7c20d951024e7f10d951024e7e10d951024e7d10d951024e7c10d9510014fe76d91100067f65d91100067c65d9110026be64d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110084fe73d9110004fd73d9110026bc43d911005cfe72d9110004fd72d9110026bc42d9110034fe71d911000cfd71d9110034fc71d9110026bf41d9110034ff70d911000cfe70d9110174fd70d911000cfc70d9110176bf40d9110176bd40d91100057f755911002d7c75591100067f65591100067c6559110026bc6459110005df7359110005dc7359110005ef7259110005ec7259110245f77159110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110174ff7459110006bf7459110026be5459110006bd5459110004ff7359110006df7359110004df7359110084fc7359110006dc7359110004dc7359110004ff7259110006ef7259110004ef725911005cfc7259110006ec7259110004ec7259110026bf4259110244ff7159110006f77159110026bc4159110164ff7059110006fb70591100067f65d8d100067c65d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df43d8d10006dc43d8d1005cfe72d8d10004fd72d8d10034ff70d8d10144fd70d8d10146df30d8d10146dd30d8d1002d7e7598d100057d7598d100067f6598d100067c6598d10006df6398d1012df57198d10084ff7598d1001cfe7598d100867e7598d1001c7e7598d10004fd7598d100867d7598d100047d7598d10084fc7598d10014fe7498d10004fd7498d10084fc7498d10084fe7398d1005cfe7298d10004fd7298d1012cfd7198d10086f57198d10154fd7098d10086f97098d10086fa3098d100057f7558d1002d7c7558d100067f6558d100067c6558d10005bf7458d10025bc7458d10005ef7258d10005ec7258d10155f77158d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1005cfc7258d10006ec7258d10004ec7258d10154ff7158d10006f77158d1012cff7058d10006fb7058d10144fe7618d100067f6518d100067c6518d10006dd6318d10084ff7518d1001cfe7518d10004fd7518d10084fc7518d10014fe7418d10004fd7418d10084fc7418d10086de7318d10006df4318d10086dc4318d1005cfe7218d10004fd7218d10034fe7118d10034fc7118d10034ff7018d1000cfe7018d10104fd7018d10086f97018d1000cfc7018d10086df301
  | 3 => 0xc7598b10014fe7498b10004fd7498b1005cfc7498b10084fe7398b10004fd7398b1000cfe7198b1000cfc7198b10036ee2198b10036ec2198b1005eef2098b100f6ed2098b10005df7358b10005dc7358b10036ec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10014fc7458b10004ff7358b10006df7358b10004df7358b10084fc7358b10006dc7358b10004dc7358b10036ef7258b1005cff7158b1000cfe7158b100ccfd7158b1000cfc7158b10036ee2158b10036ec2158b100ceef2058b100ceed2058b100cefa1058b10034ff7518b1001cfe7518b100367e7518b1001c7e7518b10004fd7518b100367d7518b100047d7518b10034fc7518b10014fe7418b10036be7418b10014be7418b10004fd7418b10036bd7418b10004bd7418b10034fc7418b10084fe7318b10036de7318b10004de7318b10004fd7318b10036dd7318b10004dd7318b1005cfe7218b10036ee7218b10034fe7118b10036f67118b10036f97018b1005cff7690b10034fe7690b10004fd7690b10034fc7690b10004ff7650b10034fe7650b10004fd7650b10034fc7650b10016be6450b10006bd6450b10005f77150b10035f47150b10084ff76ccb10034fe76ccb10004fd76ccb10034fc76ccb10086de63ccb10006dd63ccb1005cff768cb10034fe768cb10004fd768cb10034fc768cb1003dbe748cb10005bd748cb10006df638cb10006dc638cb10004ff764cb10034fe764cb10004fd764cb10034fc764cb10006de634cb10006dd634cb1005cff760cb10034fe760cb10004fd760cb10034fc760cb100457e750cb100057d750cb10006df630cb10086dc630cb10035f6710cb10005f5710cb10244ff765071012cfd76cc710036df63cc710036dc63cc710154ff764c710005bf744c71003dbc744c710036df634c710036dc634c710005ef724c710005ec724c7100ccfd76c87100f4ff7648710005bf744871003dbc7448710005df7348710005dc73487102557e76d951002e7e76d951001c7e76d95100067e64d95100067c64d951024f7771d951024f7471d951024f7a30d951024f7a20d951024f7610d951024f7410d951024f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d951024e7f71d951002e7e71d951024e7d71d951024e7c71d95100067f41d95100067c41d951024e7f70d951024e7e70d951024e7d70d951024e7c70d951024e7f40d951024e7e40d951024e7d40d951024e7c40d951024e7f30d951024e7e30d951024e7d30d951024e7c30d951024e7f20d951024e7e20d9510
  | 4 => 0x852000cfe7688520006f76188520036f4618852000dfa7088520005f9708852000cfc7648520005bf744852004dbc7448520005df7348520005dc7348520006f76148520006f46148520005fb704852000df870485200f4fe76085200557e75085200057d750852004dbe7408520005bd7408520005de7308520005dd730852000dfa700852000dfa76c812000efa76c812005f7a75c812005f7975c812000dfa72c812000fea72c812000efb62c812000feb62c812005fea52c812025fe952c8120005f971c8120034ff75d931001cfe75d9310004fd75d9310034fc75d9310164fd74d9310084fe73d9310004fd73d931005cfe72d9310004fd72d9310034fe71d9310036f671d9310036f970d9310014ff7659310036bc6459310004ff755931001cfe7559310004fd755931001cfc7559310036bf745931003ebe5459310006bd5459310004ff7359310084fc735931003ebc4359310004ff725931005cfc725931003ebf4259310014ff715931000cfe7159310014fd715931000cfc7159310036be4159310036bc4159310166bf4059310166bd4059310034ff75d8f1001cfe75d8f100367e75d8f1001c7e75d8f10004fd75d8f100367d75d8f100047d75d8f10034fc75d8f10014fe74d8f10036be74d8f10014be74d8f10004fd74d8f10036bd74d8f10004bd74d8f10034fc74d8f1005cfe72d8f10004fd72d8f10034fe71d8f10036f671d8f10036f970d8f10036fa10d8f1012cfd7698f10036df6398f10084ff7598f1001cfe7598f10004fd7598f10084fc7598f10014fe7498f10004fd7498f10084fc7498f1005cfe7298f10004fd7298f1000cfe7198f1000cfc7198f10036de3198f10036dc3198f10086df3098f10156dd3098f10036dc6358f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10014fe7458f10014fc7458f10036df7358f10004ff7258f1005cfc7258f10084ff7158f1000cfe7158f1012cfd7158f1000cfc7158f10036de3158f10036dc3158f1012edf3058f1012edd3058f1012efa1058f10034ff7518f1001cfe7518f10004fd7518f10034fc7518f10014fe7418f10004fd7418f10034fc7418f10084fe7318f10036de7318f1005cfe7218f10004fd7218f10034fe7118f10036f67118f10036f97018f10084ff7690f10034fe7690f10004fd7690f10034fc7690f10016be6490f10006bd6490f10035f67190f10005f57190f10004ff7650f10034fe7650f10004fd7650f10034fc7650f10034ff75d8b1001cfe75d8b10004fd75d8b10034fc75d8b10014fe74d8b10004fd74d8b10034fc74d8b10084fe73d8b10004fd73d8b10034fe71d8b10036f671d8b10036f970d8b10036fa10d8b100ccfd7698b10036ef6298b1005cff7598b1001cfe7598b10004fd7598b1005cf
  | 5 => 0x4ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20014fc7458d20006bc7458d20014bc7458d20006df7358d201d4ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20034fc7158d20006f47158d20004f47158d201acff7058d20006fb7058d201aefa1058d201c4fe7618d20006dd6318d20084ff7518d2001cfe7518d20004fd7518d20084fc7518d20014fe7418d20004fd7418d20084fc7418d20086de7318d2005cfe7218d2005cfc7218d20034fe7118d20004fd7118d2005cff7018d20184fd7018d20086df3018d20186dd3018d20084ff7690d20004fe7690d20004fd7690d20084fc7690d20006bf6490d20016bc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20264fe7690920014ff765092000cfe76509201e4fd765092000cfc7650920006bf6450920016bc6450920005fb705092000df8705092000cfe76cc92000cfc76cc920006df63cc920086dc63cc92000dfa70cc920005f970cc920184fe768c92004dbe748c920005bd748c920006de638c920006dd638c920084ff764c92000cfe764c9201acfd764c92000cfc764c920006df634c920006dc634c920005fb704c92000df8704c9201c4fe760c9200557e750c9200057d750c920086de630c920006dd630c920004ff75d852001cfe75d8520004fd75d852001cfc75d8520014fe74d8520004fd74d8520014fc74d8520084fe73d8520004fd73d85200f6f710d8520006f761985200057f75585200557c7558520005bf745852004dbc7458520005df7358520005dc7358520005de7318520005dd7318520006f56118520034ff751852001cfe7518520004fd7518520034fc7518520014fe7418520004fd7418520034fc7418520084fe7318520036de7318520004de7318520004fd7318520036dd7318520004dd731852000cfe7018520036f9701852000cfc7018520036f71018520036fa10185200a6f51018520004fe7690520004fd7690520034fc7690520006bf6490520016bc649052000dfa7090520005f97090520004ff7650520004fe7650520004fc7650520004fe76cc520004fd76cc520084fc76cc520086de63cc520006dd63cc520006f761cc520006f461cc520004fe768c520004fd768c520034fc768c520006df638c520006dc638c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520005bf744c52004dbc744c520006de634c520006dd634c520005ef724c520005ec724c520004fe760c520004fd760c520034fc760c520006df630c520086dc630c520006f7610c520036f4610c52000dfa700c520005f9700c5200a4fe76c852000df870c
  | 6 => 0xe654cb200067d654cb200067e65987200067d659872005ef76198720034ff759872001cfe7598720004fd7598720034fc7598720014fe7498720004fd7498720034fc7498720084fe7398720004fd739872000cfe729872005ef72198720036f42198720036f710987200e6f510987200067e65587200067d6558720005bf7458720065bc745872005ef46158720004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720006bf7458720004bf7458720014fe7458720014fc7458720006bc7458720014bc7458720004ff7358720084fc735872000cfc725872005ef7215872005ef421587200cefa20587200cef71058720034ff769072005cfe7690720004fd769072017e7e65907200067d6590720006bf6490720016bc6490720004ff7650720004fd765072005cfc765072016e7e65507200067d6550720016be6450720006bd6450720084ff76cc72005cfe76cc720004fd76cc7201267e65cc7200067d65cc720086de63cc720006dd63cc720034ff768c72005cfe768c720004fd768c72011e7e658c7200067d658c720004ff764c720004fd764c72005cfc764c72013e7e654c7200067d654c720005bf744c720065bc744c720006de634c720006dd634c720005ef724c72005dec724c720034ff760c72005cfe760c720004fd760c7201167e650c7200067d650c72000dfa700c720005f9700c7200ccfd76887200be7e65887200067d65887200e4ff76487200de7e65487200067d6548720005bf7448720065bc7448720005df7348720005dc7348720014fe76d912004ebe64d9120004ff75d912001cfe75d9120004fd75d912001cfc75d912004ebe54d9120006bd54d9120084fe73d9120004fd73d912004ebc43d912005cfe72d912000cfd72d912005cfc72d912004ebf42d9120034fe71d9120004fd71d912004ebc41d912005cff70d91201f4fd70d91201f6bf40d91201f6bd40d912004ebc645912026def7259120004ff755912001cfe7559120004fd755912001cfc75591201f4ff7459120006bf7459120004ff7359120084fc735912026cff7259120006ef7259120004ff7159120034fc71591201e4ff7059120006fb7059120004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20014fe74d8d20004fd74d8d20014fc74d8d20034fe71d8d20004fd71d8d2005cff70d8d201c4fd70d8d201c6df30d8d201c6dd30d8d201c6fa10d8d20006df6398d201aded7298d20084ff7598d2001cfe7598d20004fd7598d20084fc7598d20014fe7498d20004fd7498d20084fc7498d20084fe7398d201acfd7298d20086ed7298d20034fe7198d20004fd7198d201d4fd7098d20086f97098d200057f7558d200557c7558d20005bf7458d2004dbc7458d201d5ef7258d20005f77158d20005f47158d20
  | 7 => 0x97202767d70597202767c70597202767f40597202767e40597202767d40597202767c40597202767f30597202767e30597202767d30597202767c305972005e7f20597202767e20597202767d205972005e7c20597202767f10597202767e10597202767d10597202767c105972005cff75d932001cfe75d932005e7e75d932001c7e75d9320004fd75d932005e7d75d93200047d75d932005cfc75d93201e4fd74d9320066be54d9320006bd54d9320084fe73d932005ede73d9320004de73d9320004fd73d932005edd73d9320004dd73d932005cfe72d932005eee72d932005ebf42d9320034fe71d9320004fd71d9320066bc41d932005ef970d9320014ff76593200067e65593200067d655932005ebc6459320004ff755932001cfe7559320004fd755932001cfc755932005ebf7459320004ff7359320084fc7359320066bc4359320014ff725932000cfe7259320014fd725932000cfc725932005ebe425932005ebc4259320004ff7159320034fc7159320066bf41593201e6bf40593201e6bd405932005cff75d8f2001cfe75d8f2005e7e75d8f2001c7e75d8f20004fd75d8f2005e7d75d8f200047d75d8f2005cfc75d8f20014fe74d8f2005ebe74d8f20014be74d8f20004fd74d8f2005ebd74d8f20004bd74d8f2005cfc74d8f2005cfe72d8f2005eee72d8f20034fe71d8f20004fd71d8f2005ef970d8f201acfd7698f200067e6598f200067d6598f2005edf6398f20084ff7598f2001cfe7598f20004fd7598f20084fc7598f20014fe7498f20004fd7498f20084fc7498f20006df4398f20086dc4398f2000cfe7298f2000cfc7298f2005ede3298f2005edc3298f20034fe7198f20004fd7198f20086df3098f201d6dd3098f200067e6558f200067d6558f2005edc6358f20004ff7558f2001cfe7558f20004fd7558f2001cfc7558f20004ff7458f20014fe7458f20014fc7458f2005edf7358f20006df4358f20006dc4358f20084ff7258f2000cfe7258f201acfd7258f2000cfc7258f2005ede3258f2005edc3258f20004ff7158f20034fc7158f201aedf3058f201aedd3058f2005cff7518f2001cfe7518f2005e7e7518f2001c7e7518f20004fd7518f2005e7d7518f200047d7518f2005cfc7518f20014fe7418f20004fd7418f2005cfc7418f20084fe7318f2005ede7318f2005cfe7218f2005eee7218f20034fe7118f20004fd7118f2005ef97018f20084ff7690f2005cfe7690f20004fd7690f2005cfc7690f2021e7e6590f200067d6590f20016be6490f20006bd6490f20004ff7650f2005cfe7650f20004fd7650f2005cfc7650f2020e7e6550f200067d6550f2026cff7650b201ee7e6550b200067d6550b2005ebf6450b2005ebc6450b201acfd76ccb201a67e65ccb200067d65ccb201d4ff764cb201be7
  | 8 => 0x6bf648c53014ebc648c53012ddd738c530006f7618c530036f4618c53000dfa708c530005f9708c53000cfc764c5300067f654c53013e7c654c530005bf744c530075bc744c530006bf644c530136bc644c530005ef724c530005ec724c530006f7614c530006f4614c530005fb704c53000df8704c53012fd8304c53000ddc764c53012edc764c53000cdc764c53028ddf754c53028ddd754c5300075f654c5302875c654c5300079f744c5300079c744c5300079f644c5300079c644c530007cf724c530005dc724c530007cc724c530005cc724c530006df624c530007d7714c530007d7614c530036dc614c530007d4614c530007db704c53000dde704c53000ddc704c53012fd8704c53012edf604c53012fda104c530154fe760c5300067f650c5301167c650c530006bf640c53010ebc640c530155de730c53000dfa700c530004fe76c8530004fd76c853005cfc76c85300067f65c85300c67c65c8530006bf64c85300febc64c8530005df73c8530005dc73c8530006f761c8530006f461c8530004fe7688530004fd7688530034fc76885300067f65885300be7c6588530006bf64885300eebc6488530005de7388530005dd7388530006ef6288530006ec6288530007cc328853000dfa7088530005f97088530004ff7648530004fe7648530004fc76485300067f65485300de7c6548530005bf7448530075bc7448530006bf64485300d6bc6448530005df7348530005dc7348530004fe7608530004fd7608530034fc760853007d7e75085300057d75085300067f65085300b67c6508530075be7408530005bd7408530006bf64085300aebc6408530005de7308530005dd7308530006ef620853005eec6208530007cc3208530006f76108530036f4610853000dfa7008530005f9700853000dfa76cc13000efa76cc1300077b65cc13027f7865cc130007bb64cc130007b864cc13000dfa73cc13000fda73cc13000efb63cc13000fdb63cc130087da53cc13027fd953cc130007da32cc130087d832cc130005f971cc130087db31cc130007d931cc13005d7f765972006e7f765972001c7f765972005e7f64597200067e645972005e7c645972005e7f635972005e7c635972005f6e72597202776d725972005e7f615972005e7c61597202776e205972005f7a205972005f6c20597200067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200067f43597200067c435972006e7f725972005e7e72597202767d725972005e7c72597200067f425972005e7e425972005e7c425972005e7e325972005e7c32597200067f71597200067e71597200067d71597200067c71597200067f41597200067c415972005e7f215972005e7c21597202767f70597202767e705
  | 9 => 0xf65cc9301a67c65cc930006bf64cc9301debc64cc93000cfe768c9300067f658c93019e7c658c930075be748c930005bd748c930006bf648c9301cebc648c930006ef628c93005eec628c93000dfa708c930005f9708c93000dde768c9301c6de768c93000cde768c9302bddf758c9302bddd758c9300075f658c9302b75c658c9300079e748c9300079d748c9300079f648c9300079c648c930185de728c930006df628c930007cf628c930007cc628c930005dd718c93000dde708c9301c7da708c930007d9708c93000ddc708c9301c6df608c9301c7da108c93000cfc764c9300067f654c9301be7c654c930006bf644c9301b6bc644c930006ef624c930006ec624c930005fb704c93000df8704c9301d4fe760c93007d7e750c9300057d750c9300067f650c9301967c650c930006bf640c93018ebc640c9301d5de760c930006de760c9302addf750c9302a75e750c9302addd750c9300075d750c9300055d750c9300075f650c9302a75c650c9300079f640c9300079c640c9301c5de720c930007ce720c930006df620c930005dd710c93000dde700c93000ddc700c930086df600c930187da100c9300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d853001cfe75d8530004fd75d853001cfc75d8530014fe74d8530004fd74d8530014fc74d853005cfe72d8530004fd72d8530156f710d853007d7e75985300057d75985300067f65985300067c6598530075be7498530005bd7498530006bf6498530006bc6498530006f761985300057f755853007d7c75585300067f65585300067c6558530005bf7458530075bc7458530006bf6458530006bc6458530005ef7258530005ec72585300067f65185300067c6518530006bf6418530006bc6418530006f56118530034ff751853001cfe7518530004fd7518530034fc7518530014fe7418530004fd7418530034fc7418530036dd731853005cfe7218530004fd7218530006de3218530006dc3218530036f97018530036f71018530036fa1018530106f51018530004fe7690530004fd7690530034fc76905300067f659053017e7c6590530006bf6490530016bc6490530005de7390530005dd739053000dfa7090530005f97090530004ff7650530004fe7650530004fc76505300067f655053016e7c6550530006bf6450530016bc6450530104fe76cc5300067f65cc5301267c65cc530006bf64cc53015ebc64cc53000df870cc530087d830cc530105de76cc530006de76cc53029ddf75cc53029ddd75cc5300075f65cc5302975c65cc5300079f64cc5300079c64cc530005de72cc530006df62cc530036dc61cc530087db70cc53000dde70cc53000ddc70cc530087d870cc530086df60cc530157da10cc53000cfe768c5300067f658c53011e7c658c530
  | 10 => 0x9130006bd75d9130006bc75d9130216bf73d9130076be73d9130216bd73d9130006bf53d9130006be53d9130006bd53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d9130216bf70d9130216be70d9130216bd70d9130216bc70d9130216bf50d9130216be50d9130216bd50d9130216bc50d9130216bf30d9130216be30d9130216bc30d9130216bf20d9130216be20d9130216bd20d9130216bc20d9130216bf10d9130216be10d9130216bd10d9130216bc10d91300057f755913007d7c75591300067f65591300067c6559130076bc64591302cddf7359130004ff75591300067f75591300047f755913001cfe7559130004fd755913001cfc75591300067c755913001c7c7559130214ff7459130006bf74591302ccff7359130006df7359130004ff725913005cfc7259130004ff7159130034fc7159130204ff7059130006fb7059130215be7619130076be7619130214be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c65191302c6bf63191300079e53191300079d53191302c6bf60191302c79e30191302c79c30191302c7b830191302c7ba10191302c4fe7690d300067f6590d3021e7c6590d30216bf6490d30016bc6490d30014ff7650d3000cfe7650d30204fd7650d3000cfc7650d300067f6550d3020e7c6550d30006bf6450d30016bc6450d30005fb7050d3000df87050d300067f65d89300067c65d8930006bf64d8930006bc64d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930014fe74d8930004fd74d8930014fc74d89301d6dd73d8930034fe71d8930004fd71d89301d6ef20d89301d6fa10d893007d7e75989300057d75989300067f65989300067c6598930075be7498930005bd7498930006bf6498930006bc6498930006ef62989300057f755893007d7c75589300067f65589300067c6558930005bf7458930075bc7458930006bf6458930006bc6458930005f77158930005f471589300067f65189300067c6518930006bf6418930006bc6418930006ed621893005cff751893001cfe7518930004fd751893005cfc7518930014fe7418930004fd741893005cfc7418930034fe7118930004fd711893005eef2018930186ed2018930004fe7690930004fd769093005cfc76909300067f65909301fe7c6590930006bf6490930016bc6490930004ff7650930004fe7650930004fc76509300067f65509301ee7c6550930006bf6450930016bc6450930005df7350930005dc7350930184fe76cc9300067
  | 11 => 0x6bf6490730016bc6490730085de7390730005dd7390730004ff7650730004fd7650730084fc765073000ddd76cc730086dd76cc73000cdd76cc730085df75cc7302eddd75cc730005de72cc730006dd62cc730036de61cc730087d661cc730087d561cc73000dde70cc730087da70cc730087d970cc73000ddc70cc73012cfd768c730144ff764c730005bf744c73008dbc744c730005ef724c730005ec724c730145df764c730006df764c7302e5df754c7302e5dd754c7300079f744c7300079c744c730007cf724c730005dc724c730007cc724c730005cc724c730006dd624c730087d7714c730036de614c73000dde704c73000ddc704c73005cff76c8730084fe76c8730004fd76c8730005df73c8730085dc73c8730034ff7688730084fe7688730004fd7688730085de7388730005dd7388730007cc3288730004ff7648730004fd7648730084fc7648730005bf744873008dbc7448730005df7348730085dc7348730034ff7608730084fe7608730004fd76087300957e75087300057d750873008dbe7408730005bd7408730085de7308730005dd7308730007cc320873000dfa7008730005f970087302dd7e76d953007e7e76d953001c7e76d95300067e64d95300067c64d95302d75f73d95302d75c73d95302d75e30d95302d75c30d95302d77830d95302d77a10d95300067f74d95300067e74d95300067d74d95300067c74d95302d67f73d953007e7e73d95302d67d73d95302d67c73d95300067f43d95300067c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067c42d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067c41d95302d67f70d95302d67e70d95302d67d70d95302d67c70d95302d67f40d95302d67e40d95302d67d40d95302d67c40d95302d67f30d95302d67e30d95302d67d30d95302d67c30d95302d67f20d95302d67e20d95302d67d20d95302d67c20d95302d67f10d95302d67e10d95302d67d10d95302d67c10d9530014fe76d91300067f65d91300067c65d9130076be64d9130004ff75d913001cfe75d9130004fd75d913001cfc75d9130006bf54d9130076be54d9130006bd54d9130076bc54d9130084fe73d913000cfd73d9130084fc73d9130076bf43d913005cfe72d9130004fd72d9130076bf42d9130076bc42d9130034fe71d9130004fd71d9130076bf41d9130076bc41d9130084ff70d9130214fd70d9130216bf40d9130216bd40d91302c5be76d9130014be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91300079e53d91300079d53d91302179e30d91302179c30d9130217b830d9130217ba10d9130006bf75d9130006be75d
  | 12 => 0xc7348540004fe7608540004fd7608540034fc760854009d7e75085400057d7508540015be7408540005bd7408540005de7308540005dd7308540006ef620854005eec620854000dfa7008540005f97008540084ff75d933001cfe75d9330004fd75d9330084fc75d9330204fd74d933008ebe54d9330006bd54d9330084fe73d9330086de73d933005cfe72d9330004fd72d933008ebf42d9330034fe71d9330004fd71d933008ebc41d9330086f970d9330216be40d9330216bc40d9330014ff7659330086bc6459330004ff755933001cfe7559330004fd755933001cfc7559330086bf7459330014ff735933000cfe7359330014fd735933000cfc7359330086be4359330086bc4359330004ff725933005cfc7259330004ff7159330034fc7159330206bf4059330206bd40593302ccff7650f3008dbe7498b30005bd7498b30086ef6298b3005cff7598b3001cfe7598b30004fd7598b3005cfc7598b30014fe7498b3005ebe7498b30014be7498b30004fd7498b3005ebd7498b30004bd7498b3005cfc7498b3000cfe7398b30086ef3298b3005eec3298b30034fe7198b30004fd7198b3005eef2098b301c6ed2098b30086ec6258b30004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b30014fe7458b30014fc7458b3000cfc7358b301aedc7358b30086ef3258b30086ec3258b30004ff7158b30034fc7158b301aeef2058b3005cff7690b30084fe7690b30004fd7690b30004ff7650b30004fd7650b30084fc7650b30006bf6450b30016bc6450b30005df7350b30085dc7350b301acfd768cb3008dbe748cb30005bd748cb301addd768cb30006dd768cb302fddf758cb302fddd758cb300079e748cb300079d748cb30006dd628cb30005dd718cb3000dde708cb3000ddc708cb301c4ff764cb3000ddd760cb30086dd760cb3000cdd760cb30085df750cb300875e750cb302f5dd750cb300875d750cb300055d750cb30087ce720cb30087ce620cb30006dd620cb30087cd620cb30005dd710cb3000dde700cb30087da700cb30087d9700cb3000ddc700cb30086f76198730034ff759873001cfe7598730004fd7598730034fc7598730014fe7498730004fd7498730034fc749873000cfe7398730036de739873005cfe7298730004fd7298730006de3298730006dc3298730086f73198730036f43198730036f71098730146f51098730005bf745873008dbc7458730086f46158730004ff755873001cfe7558730004fd755873001cfc7558730004ff7458730006bf7458730004bf7458730014fe7458730014fc7458730006bc7458730014bc745873000cfc7358730004ff725873005cfc7258730086f73158730086f4315873012efa305873012ef71058730034ff7690730084fe7690730004fd7690730
  | 13 => 0x894004df97098940065fb7058940006ed621894005cff751894001cfe7518940004fd751894005cfc751894000cfd741894005ebd7418940326be5418940006bd5418940084fe7318940004fd731894005ebf421894005eee4218940326ed4218940034fe7118940004fd7118940326bc411894005cff7018940014fd701894005eef2018940266ed201894000dbc76509401e6bc765094000cbc765094031dbf755094031dbd7550940006bc6350940015bf7250940017af7250940007af625094005ebc6250940007ac6250940005bc7150940007bb705094000dbe705094000dbc70509401e7b87050940016bf6050940017bb6050940004fe76cc940004fd76cc940084fc76cc940006df63cc940086dc63cc940004fe768c940004fd768c94005cfc768c940015be748c940005bd748c940004ff764c940004fe764c940004fc764c940006df634c940006dc634c940004fe760c940004fd760c94005cfc760c94009d7e750c9400057d750c940015be740c940005bd740c94000dfa700c940005f9700c940004ff75d854001cfe75d8540004fd75d854001cfc75d854000cfd74d8540246bd74d8540316be54d8540006bd54d8540084fe73d8540004fd73d854005cfe72d8540004fd72d8540316bf42d8540006bd42d8540316f641d8540316f541d8540316bc41d8540014fd70d8540246f710d8540006f76198540025f970985400057f755854009d7c7558540005df7358540005dc7358540005ef7258540005ec725854003dfb7058540006f56118540034ff751854001cfe7518540004fd7518540034fc751854000cfd7418540084fe7318540004fd731854005cfe7218540004fd7218540036f6411854030ef54118540034ff7018540014fd7018540036f7101854023ef5101854000dbe7690540176be769054000cbe7690540305bf7590540305bd7590540006bc6390540005bd7290540006bc6290540015be7190540017b67190540006bf6190540007b76190540007b4619054000dbe7090540177ba7090540007b9709054000dbc7090540016bf6090540017bb6090540004fe76cc540004fd76cc540084fc76cc540015be74cc540005bd74cc540004fe768c540004fd768c540034fc768c540006df638c540006dc638c540004ff764c540004fe764c540004fc764c540005bf744c540015bc744c540005ef724c540005ec724c540004fe760c540004fd760c540034fc760c540006df630c540086dc630c54000dfa700c540005f9700c540004fe76c8540004fd76c854005cfc76c8540015be74c8540005bd74c8540004fe7688540004fd7688540034fc7688540005bf7488540015bc7488540006ef6288540006ec6288540004ff7648540004fe7648540004fc7648540005bf7448540015bc7448540005df7348540005d
  | 14 => 0x4fd755802101cfc7558021004ff7458021014fe7458021014fc7458021004ff7358021084fc7358021006fb50580210a6fa5058021006f950580210a6f85058021006fb40580210a6fa40580210a6f840580210a6fa30580210a6f8305802105efb205802105ef82058021036fb1058021036f81058021035fb76580210a6fb765802100cfb7658021036fb6558021006fa65580210377a65580210067a6558021006f96558021037796558021006796558021036f86558021036fb6458021006fa6458021037ba6458021006ba6458021006f96458021037b96458021006b96458021036f86458021036fb6358021006fa6358021037da6358021006da6358021006f96358021037d96358021006d96358021036f86358021007eb325802105fe83258021037eb2158021037f22158021037e9215802105ff12158021006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f843580210a6fb725802105efa7258021006fb525802105efa5258021006f9525802105ef85258021006fb425802105efa4258021006f9425802105ef84258021006fb325802105efa3258021006f9325802105ef832580210a6fb7158021036fa7158021006fb5158021036fa5158021006f95158021036f85158021006fb4158021036fa4158021006f94158021036f84158021006fb3158021036fa3158021006f93158021036f8315802105efb2158021036fa2158021006f92158021036f82158021004ff75d8d4001cfe75d8d40004fd75d8d4001cfc75d8d4000cfd74d8d40006df53d8d40006dc53d8d4033ede43d8d4033edd43d8d4005cfe72d8d40004fd72d8d40034fe71d8d40004fd71d8d40014fd70d8d402cedf30d8d40006df6398d40075f97098d400057f7558d4009d7c7558d4008dfb7058d40006dd6318d40084ff7518d4001cfe7518d40004fd7518d40084fc7518d4000cfd7418d40336be5418d40006bd5418d40006df5318d40086dc5318d40086de4318d40336dd4318d4005cfe7218d40004fd7218d40336bf4218d40034fe7118d40004fd7118d40336bc4118d40084ff7018d40014fd7018d402c6be4018d402c6bc4018d40086df3018d402c6dd3018d40004ff75d894001cfe75d8940004fd75d894001cfc75d894000cfd74d8940084fe73d8940004fd73d894032eee42d894032eed42d8940034fe71d8940004fd71d8940014fd70d894026eef20d894009d7e75989400057d7598940005de7398940005dd7398940006ef629
  | 15 => 0xc324c8211aefa604c82105eed760c821004ed760c82105f6e750c82105f6d750c82105f6e650c82105f6d650c82105fae640c82105fad640c821365ee730c82105fce730c82105eef630c82105fce630c821006ed630c82105fcd630c82105fe6710c821005ed710c82105fe5710c82135eee610c821357ce310c821357cc310c8210ecff765042116e7e65504210067d6550421016be6450421006bd6450421006de6350421006dd6350421037b44150421166fa6050421004fd76cc4211267e65cc4210067d65cc42115ebe64cc421006bd64cc421086de63cc421006dd63cc421007cf32cc421156fa60cc421004ff764c42113e7e654c4210067d654c421005bf744c4210adbc744c421136be644c421006bd644c421006de634c421006dd634c421005ef724c42105dec724c421007cf324c42112efa604c4210376e65c84210376d65c8421037ae64c8421037ad64c8421005ee73c842105dec73c8421037ce63c8421037cd63c8421035ed71c8421036ee61c8421037766588421037756588421037b66488421037b56488421037d66388421037d5638842105df5728842105ef66288421037e66288421007e7328842105fe43288421004ff76484210de7e65484210067d6548421005bf74484210adbc74484210d6be6448421006bd6448421005df7348421005dc7348421006de6348421006dd63484210cefa6048421035ef7648421006ef7648421004ef76484210376e65484210376d6548421007af7448421007ac7448421037ae6448421037ad6448421007cf7348421005ee7348421005ec7348421007cc7348421005cc7348421037ce6348421037cd6348421035ef7148421036ee6148421037e6514842134fe55148421347e61048421037e4104842105df77648421006f77648421004f7764842105f76654842105f756548421007b77448421007b4744842105fb6644842105fb56448421007d77348421007d4734842105fd6634842105fd56348421035f77248421037e7724842105ef6624842105fe6624842105fe6524842134fe55248421347e6204842105fe42048421036fb6598021006fa65980210377a65980210067a6598021006f96598021037796598021006796598021036f86598021036fb6498021006fa6498021037ba6498021006ba6498021006f96498021037b96498021006b96498021036f86498021036fb6398021006fa6398021037da6398021006da6398021006f96398021037d96398021006d96398021036f8639802105efa6298021007eb329802105fe83298021036fa6198021037eb2198021037f22198021037e9219802105ff1219802100cff76580210067e65580210067d6558021006be6458021006bd6458021006de6358021006dd6358021036f86058021004ff755802101cfe7558021
  | 16 => 0x8c21004ff7058c2100cfe7058c2100cfc7058c21006de3058c21006dc3058c21035df7658c21006df7658c21036df6558c21006de6558c210375e6558c210065e6558c21006dd6558c210375d6558c210065d6558c21036dc6558c21036df6458c21006de6458c210379e6458c210069e6458c21006dd6458c210379d6458c210069d6458c21036dc6458c2105fcc7258c21036df6058c21006de6058c21036dc6058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c2105ede7258c2105edc7258c21006cc7258c21006df5258c2105ede5258c21006dd5258c2105edc5258c21006df4258c2105ede4258c2105edc4258c21036de7158c21036dc7158c21006df5158c21036de5158c21006dd5158c21036dc5158c21006df4158c21036de4158c21036dc4158c2105edf2158c21036de2158c21036dc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21006df4058c21006de4058c21006dc4058c2105edf2058c21006de2058c2105edc2058c21036df1058c21006de1058c21036dc1058c21034ff7518c2101cfe7518c210367e7518c2101c7e7518c21004fd7518c210367d7518c210047d7518c21034fc7518c21014fe7418c21036be7418c21014be7418c21004fd7418c21036bd7418c21004bd7418c21034fc7418c21084fe7318c21036de7318c21004de7318c2105cfe7218c21036ee7218c21034fe7118c21036f67118c2100cfe7018c21036fa7018c2100cfa7018c21004fd7018c21036f97018c21004f97018c2100cfc7018c21084ff7690c21034fe7690c21004fd7690c21034fc7690c2121e7e6590c210067d6590c21016be6490c21006bd6490c21086de6390c21006dd6390c21216fa6090c21004ff7650c21034fe7650c21004fd7650c21034fc7650c2120e7e6550c210067d6550c21016be6450c21006bd6450c21006de6350c21006dd6350c21005ef7250c2105dec7250c21005f77150c21035f47150c21206fa6050c210fcff76508211ee7e65508210067d6550821016be6450821006bd6450821006de6350821006dd63508211e6fa6050821004fd76cc8211a67e65cc8210067d65cc8211debe64cc821006bd64cc821086de63cc821006dd63cc8211d6fa60cc821005ed76cc821006ed76cc8213776e65cc8210076d65cc821007ae64cc821007ad64cc82105dee73cc821006ef63cc821007ce63cc821006ed63cc821007cd63cc821006cd63cc821005ed71cc82136eee61cc821004ff764c8211be7e654c8210067d654c8211b6be644c821006bd644c821006de634c821006dd634c82105fc
  | 17 => 0x6bc7059021006bf5059021006be5059021006bd5059021006bc5059021006be3059021006bc305902105ebf2059021006be205902105ebc2059021036bf1059021006be1059021036bc1059021034ff75d8c2101cfe75d8c210367e75d8c2101c7e75d8c21004fd75d8c210367d75d8c210047d75d8c21034fc75d8c21014fe74d8c21036be74d8c21014be74d8c21004fd74d8c21036bd74d8c21004bd74d8c21034fc74d8c2105cfe72d8c21036ee72d8c21034fe71d8c21036f671d8c2100cfe70d8c21036fa70d8c2100cfa70d8c21004fd70d8c21036f970d8c21004f970d8c2100cfc70d8c21004fd7698c210067e6598c210067d6598c21006be6498c21006bd6498c21036df6398c21084ff7598c2101cfe7598c21004fd7598c21084fc7598c21014fe7498c21004fd7498c21084fc7498c21034fe7398c21006df5398c21086de5398c21006dd5398c21086dc5398c21006df4398c21086dc4398c2105cfe7298c2105cfc7298c2105ede3298c2105edc3298c21034fe7198c21034fc7198c21036de3198c21036dc3198c2100cfe7098c21004fd7098c2100cfc7098c21006de3098c21086dc3098c21004dd7698c21036df6598c21006de6598c210375e6598c210065e6598c21006dd6598c210375d6598c210065d6598c21036dc6598c21036df6498c21006de6498c210379e6498c210069e6498c21006dd6498c210379d6498c210069d6498c21036dc6498c2105fcc7298c21036df6098c21006de6098c21036dc6098c21086df7598c21006de7598c21006dd7598c21086dc7598c21086df7498c21006de7498c21006dd7498c21086dc7498c21006df5498c21006de5498c21006dd5498c21006dc5498c2105ede7298c2105edc7298c21006df5298c2105ede5298c21006dd5298c2105edc5298c21006df4298c2105ede4298c2105edc4298c21036de7198c21036dc7198c21006df5198c21036de5198c21006dd5198c21036dc5198c21006df4198c21036de4198c21036dc4198c2105edf2198c21036de2198c21086df7098c21006de7098c21006dd7098c21086dc7098c21006df5098c21006de5098c21006dd5098c21006dc5098c21006df4098c21006de4098c21006dc4098c2105edf2098c21006de2098c2105edc2098c21036df1098c21006de1098c21036dc1098c210067e6558c210067d6558c21006be6458c21006bd6458c21036dc6358c21004ff7558c2101cfe7558c21004fd7558c2101cfc7558c21004ff7458c21014fe7458c21014fc7458c21034ff7358c21036df7358c21006df5358c21006de5358c21006dd5358c21006dc5358c21006df4358c21006dc4358c2105cfe7258c2105cfc7258c21006ec7258c2105ede3258c2105edc3258c21034fe7158c21034fc7158c21036de3158c21036dc315
  | 18 => 0xe74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067f43594210067c43594210b67f725942105e7e72594210b67d725942105e7c72594210067f425942105e7e425942105e7c425942105e7e325942105e7c32594210b67f71594210367e71594210b67d71594210367c71594210067f41594210367e41594210367c41594210367e31594210367c315942105e7f21594210367e21594210367c21594210067f70594210067e70594210067d70594210067c70594210067f40594210067e40594210067c40594210067e30594210067c305942105e7f20594210067e205942105e7c20594210367f10594210067e10594210367c1059421034ff75d902101cfe75d90210367e75d902101c7e75d9021004fd75d90210367d75d90210047d75d9021034fc75d90210acfd74d9021084fe73d9021036de73d9021004de73d9021004fd73d9021036dd73d9021004dd73d902105cfe72d9021036ee72d9021034fe71d9021036f671d902100cfe70d9021036fa70d902100cfa70d9021004fd70d9021036f970d9021004f970d902100cfc70d9021004bd7699021036bf6599021006be65990210373e65990210063e6599021006bd65990210373d65990210063d6599021036bc6599021036bf6399021036bc639902105ebe6299021036be6199021036bf6099021006be6099021036bc6099021014ff76590210067e65590210067d6559021036bc6459021004ff755902101cfe7559021004fd755902101cfc7559021034ff7459021036bf7459021006bf54590210aebe5459021006bd54590210aebc5459021004ff7359021084fc73590210aebf43590210aebc435902105cfe725902105cfc725902105ebe425902105ebc4259021034fe7159021034fc7159021036be4159021036bc4159021004ff705902100cfe705902100cfc70590210aebf4059021006be40590210aebc4059021035bf76590210aebf7659021014bf7659021036bf6559021006be65590210373e65590210063e6559021006bd65590210373d65590210063d6559021036bc6559021036bf6359021036bc6359021036bf6059021006be6059021036bc6059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bd5359021006bc53590210aebf725902105ebe725902105ebc7259021006bf525902105ebe5259021006bd525902105ebc525902105ebe325902105ebc32590210aebf7159021036be7159021036bc7159021006bf5159021036be5159021006bd5159021036bc5159021036be3159021036bc315902105ebf2159021036be2159021036bc2159021006bf7059021006be7059021006bd7059021
  | 19 => 0x8d21006dc5018d21006df4018d21006de4018d21006dc4018d21006de2018d21006dc2018d21006de1018d21006dc1018d21084ff7690d21004fe7690d21004fd7690d21084fc7690d21006bf6490d21016bc6490d21006df6390d21086dc6390d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d21016bc6450d21006df6350d21006dc6350d210ecfe7690921006bf6490921016bc6490921006df6390921006dc6390921014fc7650921006bf6450921016bc6450921006df6350921006dc6350921005f77150921005f47150921004fe76cc921006bf64cc9211debc64cc921006df63cc921086dc63cc921005f671cc921005f571cc921004fe768c9210d5be748c921005bd748c921006bf648c9211cebc648c921006df638c921006dc638c921004fc764c921006bf644c9211b6bc644c921006df634c921006dc634c921005f7714c921005f4714c921004fe760c9210dd7e750c9210057d750c921006bf640c92118ebc640c921006df630c921086dc630c9210fcfe7690521006bf6490521016bc6490521006df6390521006dc6390521014ff76505210d4fd7650521014fc7650521006bf6450521016bc6450521006df6350521006dc6350521005ef7250521005ec7250521004fe76cc521006bf64cc52115ebc64cc521006df63cc521086dc63cc521005ee72cc521005ed72cc521004fe768c521006bf648c52114ebc648c521006df638c521006dc638c521084ff764c521004fd764c521004fc764c521005bf744c5210d5bc744c521006bf644c521136bc644c521006df634c521006dc634c521005ef724c521005ec724c521004fe760c521006bf640c52110ebc640c521006df630c521086dc630c5210cdfa700c521005f9700c521006bf64c85210febc64c8521006df63c8521006dc63c8521007b764c8521007b464c8521007d763c8521007d463c8521006bf64885210eebc6488521006df6388521006dc6388521007af6488521007ac6488521007cf6388521006ee6388521006ec6388521007cc6388521006cc6388521007e7618852100cfe76d8121006bf64d8121006bc64d8121006df63d8121006dc63d81210cefa60d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121014fe74d8121004fd74d8121014fc74d8121084fe73d8121004fd73d8121006fb50d81210cef850d81210cefa20d81210cefa10d81210057f75581210dd7c7558121005bf74581210d5bc7458121006bf6458121006bc6458121005df7358121005dc7358121006df6358121006dc63581210cef860581210357f76594210b67f765942101c7f76594210367f64594210067e64594210367c64594210367f63594210367c63594210367f60594210067e60594210367c60594210067f74594210067
  | 20 => 0x69c64d8d21006de60d8d21006dc60d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21006df72d8d21006dd72d8d21006df52d8d21006de52d8d21006dd52d8d21006dc52d8d21006df42d8d21006dc42d8d21006df71d8d21006dd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21006df41d8d21006dc41d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dc40d8d21006de20d8d21006dc20d8d21006de10d8d21006dc10d8d210d5be7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d21084ff7598d2101cfe7598d21004fd7598d21084fc7598d21014fe7498d21086be7498d21014be7498d21004fd7498d21086bd7498d21004bd7498d21084fc7498d21084fe7398d21004de7398d21004fd7298d21086ed7298d21004fd7198d21086f57198d2100cfe7098d21004fd7098d2100cfc7098d21005bf7458d210d5bc7458d21006bf6458d21006bc6458d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21006bf7458d21004bf7458d21014fe7458d21014fc7458d21006bc7458d21014bc7458d21006df7358d21004ff7258d21006ef7258d21004ef7258d21004ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21004fe7618d21006bf6418d21006bc6418d21006dd6318d21084ff7518d2101cfe7518d21004fd7518d21084fc7518d21014fe7418d21004fd7418d21084fc7418d21086de7318d21006df5318d21086de5318d21006dd5318d21086dc5318d21006df4318d21086dc4318d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d21086dc3018d21005de7618d21006de7618d21004de7618d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d210079f6418d210069f6418d21006de6418d21006dd6418d21006dc6418d210079c6418d210069c6418d21006de6018d21006dc6018d21086df7518d21006de7518d21006dd7518d21086dc7518d21086df7418d21006de7418d21006dd7418d21086dc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d21086df7218d21006dd7218d21006df5218d21006de5218d21006dd5218d21006dc5218d21006df4218d21006dc4218d21086df7118d21006dd7118d21006df5118d21006de5118d21006dd5118d21006dc5118d21006df4118d21006dc4118d21006dd2118d21086df7018d21006de7018d21006dd7018d21086dc7018d21006df5018d21006de5018d21006dd501
  | 21 => 0xc744c621036df634c621036dc634c621005ef724c621005ec724c621007cf324c621035ed76c8621006ed76c8621005ee73c8621005ec73c8621037e651c862137fe551c8621005f576c862105ef576c862105fe652c862137fe552c862100cff76582210057f75582210bd7c7558221036f86058221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7458221014fe7458221014fc7458221004ff7358221084fc73582210e6fa30582210e6fa2058221036fb1058221036f81058221014fe76d91210d6be64d9121004ff75d912101cfe75d9121004fd75d912101cfc75d9121006bf54d91210d6be54d9121006bd54d91210d6bc54d9121084fe73d9121004fd73d91210d6bf43d91210d6bc43d91210d4fd72d91210d6bf42d91210d4fd71d91210d6bf41d912100cfe70d9121004fd70d912100cfc70d91210d6bf40d9121006be40d91210d6bc40d91210d5be76d9121014be76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121006be60d9121006bc60d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d9121006bf72d91210d6be72d9121006bd72d9121006bf52d9121006be52d9121006bd52d9121006bc52d9121006bf71d91210d6be71d9121006bd71d9121006bf51d9121006be51d9121006bd51d9121006bc51d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d9121006be30d9121006bc30d9121006be20d9121006bc20d9121006be10d9121006bc10d91210d6bc6459121005df7359121005dc7359121004ff755912101cfe7559121004fd755912101cfc75591210d4ff7459121006bf7459121004ff7359121006df7359121004df7359121084fc7359121006dc7359121004dc73591210ecff7259121006ef72591210fcff7159121006f77159121004ff705912100cfe705912100cfc7059121005be76191210d6be7619121004be7619121006bf6519121006be6519121006bd6519121006bc6519121006be6019121006bc6019121006bf64d8d21006bc64d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21014fe74d8d21004fd74d8d21014fc74d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21006df43d8d21006dc43d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d210079f64d8d210069f64d8d21006de64d8d21006dd64d8d21006dc64d8d210079c64d8d21
  | 22 => 0x8321014fe7458321014fc7458321004ff7358321084fc735832105efb205832105ef820583210f6fa1058321034ff75d922101cfe75d9221004fd75d9221034fc75d92210ecfd74d9221084fe73d9221004fd73d92210eebc43d9221036ed72d92210eebc42d9221036f671d9221036bf41d922100cfe70d9221004fd70d922100cfc70d92210eebf40d9221014ff7659221036bc6459221004ff755922101cfe7559221004fd755922101cfc7559221036bf74592210eebe5459221006bd5459221004ff7359221084fc73592210eebf4259221036be4159221036bc4159221004ff705922100cfe705922100cfc7059221034ff75d8e2101cfe75d8e21004fd75d8e21034fc75d8e21014fe74d8e21004fd74d8e21034fc74d8e21036ed72d8e21036f671d8e2100cfe70d8e21004fd70d8e2100cfc70d8e21004fd7698e21036df6398e21084ff7598e2101cfe7598e21004fd7598e21084fc7598e21014fe7498e21004fd7498e21084fc7498e21036de3198e21036dc3198e2100cfe7098e21004fd7098e2100cfc7098e21005bf7458e210edbc7458e21036dc6358e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21006bf7458e21004bf7458e21014fe7458e21014fc7458e21006bc7458e21014bc7458e21036df7358e21006ef7258e21036de3158e21036dc3158e21004ff7058e2100cfe7058e2100cfc7058e21034ff7518e2101cfe7518e21004fd7518e21034fc7518e21014fe7418e21004fd7418e21034fc7418e21084fe7318e21036de7318e21036ed7218e21036f67118e2100cfe7018e21036fa7018e2100cfa7018e21004fd7018e21036f97018e21004f97018e2100cfc7018e21084ff7690e21034fe7690e21004fd7690e21034fc7690e21006bf6490e21016bc6490e21004ff7650e21034fe7650e21004fd7650e21034fc7650e21005ef7250e21005ec7250e210d4fd7690a21006bf6490a21016bc6490a21014ff7650a21034fc7650a21016be6450a21006bd6450a21005f77150a21035f47150a21086de63cca21006dd63cca21035f671cca21005f571cca21006ed76cca21006ef63cca21007ce63cca21006ed63cca21007cd63cca21007e671cca21005ed71cca21007e571cca210edbe748ca21005bd748ca21006df638ca21006dc638ca21006de634ca21006dd634ca21005f7714ca21035f4714ca210bd7e750ca210057d750ca21006df630ca21086dc630ca21007cd320ca21005ed760ca21006ed760ca2135f6e750ca210076d750ca21007ce730ca21006ef630ca21357cf630ca21006ed630ca21357cc630ca21005ed710ca21357ce310ca21357cc310ca210acff7650621036bf6450621036bc6450621036df63cc621036dc63cc621007cf32cc621005bf744c6210edb
  | 23 => 0x86fb3258031006fa3258031006da3258031006f93258031086f83258031006d83258031106fb7158031036fa7158031006fb5158031036fa5158031006f95158031036f85158031006fb4158031036fa4158031006f94158031036f84158031086fb3158031006db3158031036fa3158031006f93158031006d93158031036f83158031036fa2158031036f8215803105cff75d932101cfe75d9321004fd75d932105cfc75d93210fcfd74d93210febe54d9321006bd54d9321084fe73d9321004fd73d932105eee72d932105ebf42d932105ef571d93210febc41d932100cfe70d9321004fd70d932100cfc70d9321014ff765932105ebc6459321004ff755932101cfe7559321004fd755932101cfc755932105ebf7459321004ff7359321084fc73593210febc435932105ebe425932105ebc42593210febf4159321004ff705932100cfe705932100cfc70593210febf405932105cff75d8f2101cfe75d8f21004fd75d8f2105cfc75d8f21014fe74d8f2105ebe74d8f21014be74d8f21004fd74d8f2105ebd74d8f21004bd74d8f2105cfc74d8f2105eee72d8f2105ef571d8f2100cfe70d8f21004fd70d8f2100cfc70d8f21004fd7698f2105edf6398f21084ff7598f2101cfe7598f21004fd7598f21084fc7598f21014fe7498f21004fd7498f21084fc7498f2105ede3298f2105edc3298f2100cfe7098f21004fd7098f2100cfc7098f2105edc6358f21004ff7558f2101cfe7558f21004fd7558f2101cfc7558f21004ff7458f21014fe7458f21014fc7458f2105edf7358f2105ede3258f2105edc3258f21004ff7058f2100cfe7058f2100cfc7058f2105cff7518f2101cfe7518f2105e7e7518f2101c7e7518f21004fd7518f2105e7d7518f210047d7518f2105cfc7518f21014fe7418f21004fd7418f2105cfc7418f21084fe7318f2105ede7318f2105eee7218f2105ef57118f2100cfe7018f21004fd7018f2100cfc7018f21084ff7690f2105cfe7690f21004fd7690f2105cfc7690f21016be6490f21006bd6490f21004ff7650f2105cfe7650f21004fd7650f2105cfc7650f21005f77150f21005f47150f210acff7650b2105ebf6450b2105ebc6450b2105edf63ccb2105edc63ccb2105edf634cb2105edc634cb210d4fd7690721006bf6490721016bc6490721014ff765072105cfc7650721016be6450721006bd6450721005ef725072105dec72507210ffb44150721086de63cc721006dd63cc72105dee72cc721005ed72cc721006df638c721006dc638c721005bf744c7210fdbc744c721006de634c721006dd634c721005ef724c72105dec724c721006df630c721086dc630c7210f5fa700c721005f9700c72100cff765832105ef86058321004ff755832101cfe7558321004fd755832101cfc7558321004ff745
  | 24 => 0xe634c831087cc324c8311aefa604c8310875e750c8310875d750c831395de720c831087ce720c831087ce620c831006dd620c831087cd620c831087d6710c831005dd710c831087d5710c83138ede610c83114cff7650431166fa6050431005de72cc431006dd62cc431035dd71cc431036de61cc431085f5738c431086f6638c431037d6638c431007d6328c431087d4328c431004ff764c431005bf744c43110dbc744c431005ef724c431005ec724c43112efa604c431035df764c431006df764c431004df764c4310079f744c4310079c744c431007cf724c431005dc724c431007cc724c431005cc724c431006dd624c431035df714c431036de614c431037d6514c431387d5514c431085f7764c431006f7764c431004f7764c431007b7744c431007b4744c431035f7734c431037d7734c431086f6634c431087d6634c431087d6534c431387d5534c431007e7724c431007e4724c431036fb6598031006fa6598031006f96598031036f86598031036fb6498031006fa6498031006f96498031036f86498031086fa6398031036fb6298031006fa6298031006f96298031036f86298031007da3298031087d83298031036fa6198031037db3198031037f23198031037d93198031087f1319803100cff76580310057f75580311157c7558031036f86058031004ff75580310067f75580310047f755803101cfe7558031004fd755803101cfc75580310067c755803101c7c7558031004ff7458031014fe7458031014fc7458031004ff725803105cfc7258031006de3258031006dc3258031006df3158031006dd3158031006fb5058031106fa5058031006f95058031106f85058031006fb4058031106fa4058031106f84058031086fb3058031086f83058031106fa2058031106f82058031036fb1058031036f81058031035fb7658031106fb765803100cfb76580310077b7558031007787558031036fb6558031006fa6558031006f96558031036f86558031036fb6458031006fa6458031006f96458031036f86458031036fb6258031006fa6258031006f96258031036f86258031007da3258031087d83258031037db3158031037f23158031037d93158031087f13158031006fb75580310067b7558031006fa7558031006f97558031006f87558031006787558031006fb7458031006fa7458031006f97458031006f87458031006fb5458031006fa5458031006f95458031006f85458031106fb7358031086fa7358031006fb5358031086fa5358031006f95358031086f85358031006fb4358031086fa4358031006f94358031086f84358031006fb7258031006fa7258031006f97258031006f87258031006fb5258031006fa5258031006f95258031006f85258031006fb4258031006fa4258031006f94258031006f84258031
  | 25 => 0x531006bf6450531016bc6450531005df7350531005dc7350531006ef6250531006ec6250531137b44150531006bf64cc53115ebc64cc531006ef62cc531006ec62cc531007b764cc531007b464cc531007e762cc531007e462cc531087d732cc531007d532cc531006bf648c53114ebc648c531006ef628c531006ec628c5310079f648c5310079c648c531005dd728c531007cf628c531006dc628c531007cc628c531006cc628c531007d7618c531005dd708c53100cfe76d8131006bf64d8131006bc64d8131006ef62d8131006ec62d813112efa60d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131014fe74d8131004fd74d8131014fc74d813105cfe72d8131004fd72d8131006fb50d813112ef850d813112efa30d813112efa10d81310057f755813113d7c7558131005bf7458131135bc7458131006bf6458131006bc6458131005ef7258131005ec7258131006ef6258131006ec625813112ef86058131034ff75d903101cfe75d9031004fd75d9031034fc75d903110cfd74d9031084fe73d9031036de73d903105cfe72d9031004fd72d9031034fe71d9031036f671d903100cfe70d9031036fa70d903100cfa70d9031004fd70d9031036f970d9031004f970d903100cfc70d9031014ff7659031036bc6459031004ff755903101cfe7559031004fd755903101cfc7559031034ff7459031036bf745903110ebe5459031006bd5459031084fe7359031084fc7359031086be4359031086bc4359031004ff725903105cfc725903110ebf4259031034fe7159031034fc7159031036be4159031036bc4159031004ff705903100cfe705903100cfc705903115cff7650c31206fa6050c31036ef629883105cff759883101cfe7598831004fd759883105cfc7598831014fe7498831004fd749883105cfc749883105eee5298831006ed5298831086ef329883105eec3298831036ee2198831036ec219883100cfe7098831004fd709883100cfc7098831036ec6258831004ff755883101cfe7558831004fd755883101cfc7558831004ff7458831014fe7458831014fc7458831006ee5258831006ed5258831086ef3258831086ec3258831036ee2158831036ec2158831004ff705883100cfe705883100cfc705883105cff7690831034fe7690831004fd769083105eee6290831006ed62908311f6fa6090831004ff7650831004fd7650831034fc7650831016be6450831006bd6450831005df7350831085dc7350831006ee6250831006ed6250831005f77150831035f471508311e6fa6050831004fd768c83110dbe748c831005bd748c8311c6fa608c831005dd768c831006dd768c831004dd768c8310079e748c8310079d748c831085de728c831006dd628c831005dd718c8313a6de618c831004ff764c83139ed
  | 26 => 0x6ef6298931005bf7458931135bc7458931006bf6458931006bc645893113d7e75189310057d7518931006bf6418931006bc6418931006ed621893105cff751893101cfe751893105e7e751893101c7e7518931004fd751893105e7d75189310047d751893105cfc7518931014fe7418931004fd741893105cfc7418931006ef521893105eee5218931006ed521893105eec5218931006ef421893105eec421893100cfe7018931004fd701893100cfc7018931006ee201893105eec2018931005ee7618931006ee76189310076e75189310076d7518931006ef6518931006ee6518931006ed6518931006ec6518931006ef6418931007af6418931006af6418931006ee6418931006ed6418931006ec6418931007ac6418931006ac6418931007cd7318931006ee6018931006ec601893105eef7518931006ee75189310066e7518931006ed75189310066d751893105eec751893105eef7418931006ee7418931006ed741893105eec7418931006ef5418931006ee5418931006ed5418931006ec541893105eef7318931006ef5318931006ee5318931006ed5318931006ec5318931006ef4318931006ee4318931006ed4318931006ec431893105eef7118931006ed7118931006ef5118931006ee5118931006ed5118931006ec5118931006ef4118931006ec4118931006ed311893105eef7018931006ee7018931006ed701893105eec7018931006ef5018931006ee5018931006ed5018931006ec5018931006ef4018931006ee4018931006ec4018931006ee3018931006ec3018931006ee1018931006ec1018931004fe7690931004fd769093105cfc7690931006bf6490931016bc6490931005de7390931005dd7390931006ef629093105eec6290931004ff7650931004fe7650931004fc7650931006bf6450931016bc6450931006ef6250931006ec6250931004fe76cc931006bf64cc9311debc64cc931006ec62cc931005de76cc931006de76cc931004de76cc9310079f64cc9310079c64cc931007cf62cc93105edc62cc931007cc62cc931006cc62cc931035de71cc931086df61cc931005dd70cc931135be748c931005bd748c931006bf648c9311cebc648c9313b5dd738c931006ef628c93105eec628c931005f6718c931005f5718c931006bf644c9311b6bc644c931006ef624c931006ec624c931005f7714c931005f4714c9310079f644c9310079c644c931007cf724c931007cf624c93105edc624c931007cc624c931006cc624c931007d7714c931035dc714c931007d4714c931005df704c931004fe760c93113d7e750c9310057d750c931006bf640c93118ebc640c9313adde730c931006ef620c93115cfe7690531006bf6490531016bc6490531006ef6290531006ec6290531014ff7650531134fd7650531014fc765
  | 27 => 0xc40d9131135be76d9131014be76d9131006bf65d9131006be65d9131006bd65d9131006bc65d9131006be60d9131006bc60d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131006bf73d9131136be73d9131006bd73d9131006bf53d9131006be53d9131006bd53d9131006bc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bd52d9131006bc52d9131006bf71d9131136be71d9131006bd71d9131006bf51d9131006be51d9131006bd51d9131006bc51d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d9131006be30d9131006bc30d9131006be20d9131006bc20d9131006be10d9131006bc10d9131136bc6459131005ef7259131005ec7259131004ff755913101cfe7559131004fd755913101cfc7559131134ff7459131006bf745913114cff7359131006df7359131004ff7259131006ef7259131004ef725913105cfc7259131006ec7259131004ec725913115cff7159131006f77159131004ff705913100cfe705913100cfc7059131005be7619131136be7619131004be7619131006bf6519131006be6519131006bd6519131006bc6519131006be6019131006bc601913114cfe7690d31006bf6490d31016bc6490d31014fc7650d31006bf6450d31016bc6450d31005f77150d31005f47150d31006bf64d8931006bc64d8931004ff75d893101cfe75d8931004fd75d893101cfc75d8931014fe74d8931004fd74d8931014fc74d8931006ef52d8931006ee52d8931006ed52d8931006ec52d8931006ef42d8931006ec42d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931007af64d8931006af64d8931006ee64d8931006ed64d8931006ec64d8931007ac64d8931006ac64d8931007cf73d8931006ee60d8931006ec60d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d8931006ef73d8931006ef53d8931006ee53d8931006ed53d8931006ec53d8931006ef43d8931006ee43d8931006ed43d8931006ec43d8931006ef71d8931006ed71d8931006ef51d8931006ee51d8931006ed51d8931006ec51d8931006ef41d8931006ec41d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931006ef40d8931006ee40d8931006ec40d8931006ee30d8931006ec30d8931006ee10d8931006ec10d8931135be7498931005bd7498931006bf6498931006bc6498931
  | 28 => 0x833101cfc7558331004ff7458331014fe7458331014fc7458331004ff725833105cfc7258331086fb3058331086f83058331156fa1058331034ff75d923101cfe75d9231004fd75d9231034fc75d923114cfd74d9231036dd73d923114ebc43d923105cfe72d9231004fd72d9231036f671d923100cfe70d9231004fd70d923100cfc70d9231014ff7659231036bc6459231004ff755923101cfe7559231004fd755923101cfc7559231036bf745923114ebe5459231006bd545923114ebf4359231004ff725923105cfc725923114ebf4259231036be4159231036bc4159231004ff705923100cfe705923100cfc7059231006be405923114ebc4059231134fd7690e31006bf6490e31016bc6490e31014ff7650e31034fc7650e31016be6450e31006bd6450e31005f77150e31035f47150e31036ef6298a3105cff7598a3101cfe7598a31004fd7598a3105cfc7598a31014fe7498a31004fd7498a3105cfc7498a31036ee2198a31036ec2198a3100cfe7098a31004fd7098a3100cfc7098a31036ec6258a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31014fc7458a31036ee2158a31036ec2158a31004ff7058a3100cfe7058a3100cfc7058a3105cff7690a31034fe7690a31004fd7690a31004ff7650a31004fd7650a31034fc7650a31016be6450a31006bd6450a31005df7350a31005dc7350a3114dbe748ca31005bd748ca3105eee628ca31006ed628ca31035f6718ca31005f5718ca310079e748ca310079d748ca31007ce628ca31006dd628ca31007cd628ca31007d6718ca31005dd718ca31007d5718ca31006ee624ca31006ed624ca31005f7714ca31035f4714ca3111d7e750ca310057d750ca31007cd320ca31005dd760ca31006dd760ca3138f5e750ca310075d750ca31007ce720ca31357cf620ca31006dd620ca31357cc620ca31005dd710ca3110cff7650631037b44150631035dd76cc631006dd76cc631005de72cc631006dd62cc631037d651cc6313bfd551cc631005f576cc631086f576cc631087d653cc6313bfd553cc63100cff7658231036f86058231004ff755823101cfe7558231004fd755823101cfc7558231004ff7458231014fe7458231014fc7458231004ff725823105cfc7258231006de3258231006dc3258231006df3158231146fa3058231146fa2058231036fb1058231036f81058231014fe76d9131136be64d9131004ff75d913101cfe75d9131004fd75d913101cfc75d9131006bf54d9131136be54d9131006bd54d9131136bc54d9131134fd73d9131136bf43d913105cfe72d9131004fd72d9131136bf42d9131136bc42d9131134fd71d9131136bf41d913100cfe70d9131004fd70d913100cfc70d9131136bf40d9131006be40d9131136b
  | 29 => 0x84fc76cc941006ef62cc941006ec62cc941004fe768c941004fd768c94105cfc768c941015be748c941005bd748c941006df638c941006dc638c941004ff764c941004fe764c941004fc764c941004fe760c941004fd760c94105cfc760c94116d7e750c9410057d750c941015be740c941005bd740c941006df630c941086dc630c941006ef620c94105eec620c941005f6710c941005f5710c941035bf75905413c5bd7590541006bc6390541005bd7290541006bc6290541035be7190541037b67190541036bf6190541017b7619054100cfe76d8141166fa60d8141004ff75d814101cfe75d8141004fd75d814101cfc75d814100cfc74d814103ebe54d8141006bd54d8141084fe73d8141004fd73d814105cfe72d8141004fd72d814103ebf42d8141006bd42d8141014fd71d8141006be41d814103ebc41d8141166fa40d8141166fa10d81410057f755814116d7c7558141005df7358141005dc7358141005ef7258141005ec7258141166f86058141084ff75d933101cfe75d9331004fd75d9331084fc75d933115cfd74d933115ebe54d9331006bd54d9331086de73d933105cfe72d9331004fd72d933115ebf42d9331086f571d933115ebc41d933100cfe70d9331004fd70d933100cfc70d9331014ff7659331086bc6459331004ff755933101cfe7559331004fd755933101cfc7559331086bf7459331086be4359331086bc4359331004ff725933105cfc725933115ebc425933115ebf4159331004ff705933100cfe705933100cfc705933115ebf405933110cff7650f3115dbe7498b31005bd7498b31086ef6298b3105cff7598b3101cfe7598b31004fd7598b3105cfc7598b31014fe7498b3105ebe7498b31014be7498b31004fd7498b3105ebd7498b31004bd7498b3105cfc7498b31086ef3298b3105eec3298b3100cfe7098b31004fd7098b3100cfc7098b31086ec6258b31004ff7558b3101cfe7558b31004fd7558b3101cfc7558b31004ff7458b31014fe7458b31014fc7458b31086ef3258b31086ec3258b31004ff7058b3100cfe7058b3100cfc7058b3105cff7690b31084fe7690b31004fd7690b31016be6490b31006bd6490b31085de7390b31005dd7390b31004ff7650b31004fd7650b31084fc7650b31006bf6450b31016bc6450b31005f77150b31005f47150b3105ede62ccb31087ce62ccb31087cd62ccb31035de71ccb31087d671ccb31087d571ccb31005dd70ccb3115dbe748cb31005bd748cb31005df764cb31006df764cb31087cf724cb3105ede624cb31035dc714cb31005df704cb31134fd7690731006bf6490731016bc6490731014ff7650731084fc7650731016be6450731006bd6450731005df7350731085dc735073100cff7658331086f86058331004ff755833101cfe7558331004fd755
  | 30 => 0xc4258a41034fc7158a410d6bf4158a41036ee2158a41036ec2158a41004ff7058a4100cfe7058a4100cfc7058a410d6bf4058a413d6bf6590a413d6bd6590a41005be7390a41015be7290a41017ae7290a41007ae6290a41006bd6290a41007ad6290a41007b67190a41005bd7190a41007b57190a41016be6190a41017b66190a41005bd7090a41084ff76cca41034fe76cca41004fd76cca41015be74cca41005bd74cca41086de63cca41006dd63cca4105cff768ca41034fe768ca41004fd768ca41015be748ca41005bd748ca41004ff764ca41004fd764ca41034fc764ca41005bf744ca41015bc744ca41006de634ca41006dd634ca4105cff760ca41034fe760ca41004fd760ca4117d7e750ca410057d750ca41005bf740ca41015bc740ca41035f6710ca41005f5710ca4100cff76582410057f755824117d7c7558241036f86058241004ff75582410067f75582410047f755824101cfe7558241004fd755824101cfc75582410067c755824101c7c7558241004ff7358241084fc7358241004ff725824105cfc7258241034fc7158241006fb5058241176f85058241176fa4058241176fa3058241176fa2058241036fb1058241036f81058241004ff75d8d4101cfe75d8d41004fd75d8d4101cfc75d8d41006de53d8d41006dd53d8d4114ede43d8d4114edd43d8d4105cfe72d8d41004fd72d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d41006df6398d41135f57198d41005ef7258d41005ec7258d4115df77158d41006dd6318d41084ff7518d4101cfe7518d41004fd7518d41084fc7518d4110ebe5418d41006bd5418d41086de5318d41006dd5318d41086de4318d4110edd4318d4105cfe7218d41004fd7218d4110ebf4218d4110ebc4118d4100cfe7018d41004fd7018d4100cfc7018d41006de3018d41086dc3018d41004ff75d894101cfe75d8941004fd75d894101cfc75d8941084fe73d8941004fd73d8941006ee52d8941006ed52d89410eeee42d89410eeed42d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d8941006ef62989410d5f57198941005df7358941005dc73589410fdf77158941006ed621894105cff751894101cfe7518941004fd751894105cfc75189410aebe5418941006bd5418941084fe7318941004fd731894105eee5218941006ed521894105ebf421894105eee42189410aeed42189410aebc411894100cfe7018941004fd701894100cfc7018941006ee201894105eec20189413cdbf75509413cdbd7550941006bc6350941015bf7250941017af7250941007af625094105ebc6250941007ac6250941007b77150941035bc7150941007b47150941005b47150941016bf6150941017b76150941004fe76cc941004fd76cc941
  | 31 => 0xc832004ff764c8321be7e654c8320067d654c83205ddf764c832006df764c832004df764c83205f5e654c83205f5d654c83205ddf724c83205ede624c83205fce524c8323e7cd524c83205fce424c832007cd424c832005dc714c832005df704c832085ef764c832006ef764c832004ef764c8320876e654c8320876d654c83205def734c83205fcf734c832086ee634c832087ce634c832087ce534c8323e7cd534c832087ce434c832007cd434c832005ec714c8320067e65984320067d659843205ef76198432034ff759843201cfe7598432004fd7598432034fc7598432014fe7498432004fd7498432034fc7498432086f73198432036f4319843205ef72198432036f4219843200cfe7098432004fd709843200cfc70984320067e65584320067d6558432005bf745843218dbc745843205ef46158432004ff755843201cfe7558432004fd755843201cfc7558432004ff7458432006bf7458432004bf7458432014fe7458432014fc7458432006bc7458432014bc7458432006df3258432006dd3258432086f73158432086f4315843205ef7215843205ef42158432004ff705843200cfe705843200cfc705843200cff76580320067e65580320067d655803205ef86058032004ff755803201cfe7558032004fd755803201cfc7558032004ff7458032014fe7458032014fc7458032004ff7158032034fc7158032186fa4058032086fb3058032086f8305803205efb205803205ef82058032186fa1058032036df6398e41084ff7598e4101cfe7598e41004fd7598e41084fc7598e41006df5398e41086dc5398e41086de4398e4115edd4398e4105cfe7298e41004fd7298e41034fe7198e41034fc7198e41036de3198e41036dc3198e4100cfe7098e41004fd7098e4100cfc7098e41036dc6358e41004ff7558e4101cfe7558e41004fd7558e4101cfc7558e41006df5358e41006dc5358e41136de4358e41136dd4358e41136bc4358e41004ff7258e4105cfc7258e41034fc7158e41036de3158e41036dc3158e41004ff7058e4100cfe7058e4100cfc7058e413debf6590e413debd6590e41015be7390e410179e7390e410079e6390e41006bd6390e410079d6390e41005be7290e41007b67190e41005bd7190e41007b57190e41016be6190e41017b66190e41005bd7090e41216be6090e41216bc6090e41036ef6298a4105cff7598a4101cfe7598a41004fd7598a4105cfc7598a41084fe7398a41004fd7398a4105eee4298a410feed4298a41034fe7198a41034fc7198a41036ee2198a41036ec2198a4100cfe7098a41004fd7098a4100cfc7098a41036ec6258a41004ff7558a4101cfe7558a41004fd7558a4101cfc7558a41004ff7358a41084fc7358a41006be4358a410d6bc4358a410d6ee4258a410d6ed4258a410d6b
  | 32 => 0x1adfa7018532005f97018532034ff751853201cfe7518532004fd7518532034fc7518532014fe7418532004fd7418532034fc7418532006ef3218532006de3218532036f65118532006f55118532006f74118532036f4411853200cfe7018532036fa701853200cfa7018532004fd7018532036f97018532004f9701853200cfc7018532006f61018532036f4101853200cfe76d81321aefa60d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132014fe74d8132004fd74d8132014fc74d8132006de32d8132034fe71d8132004fd71d81321aefa30d81321aefa20d81320057f75581321bd7c7558132005bf74581321b5bc7458132005f77158132005f471581321aef8605813205d7f76594321967f765943201c7f765943205e7f64594320067e645943205e7c645943205e7f615943205e7c615943205e7f60594320067e605943205e7c60594320067f74594320067e74594320067d74594320067c74594321967f73594320867e73594321967d73594320867c73594320067f43594320867e43594320867c43594321967f725943205e7e72594321967d725943205e7c72594320067f425943205e7e425943205e7c42594320867f325943205e7e325943205e7c32594320067f71594320067e71594320067d71594320067c71594320067f41594320067c41594320867f31594320867c315943205e7f215943205e7c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067e40594320067c40594320867f30594320067e30594320867c305943205e7f20594320067e205943205e7c20594320067e10594320067c105943205cff75d903201cfe75d903205e7e75d903201c7e75d9032004fd75d903205e7d75d90320047d75d903205cfc75d903218cfd74d903218ebe54d9032006bd54d9032084fe73d903205ede73d903205cfe72d903205eee72d903205ebf42d9032034fe71d9032004fd71d903218ebc41d903200cfe70d9032004fd70d903200cfc70d9032014ff76590320067e65590320067d655903205ebc6459032004ff755903201cfe7559032004fd755903201cfc755903205cff745903205ebf7459032084fe7359032084fc7359032086be4359032086bc435903205cfe725903205cfc725903205ebe425903205ebc4259032004ff7159032034fc715903218ebf4159032004ff705903200cfe705903200cfc705903218ebf40590321dcff7650c3220e7e6550c320067d6550c321ccff76508321ee7e65508320067d655083205ebf645083205ebc645083205f5e65cc83205f5d65cc83205ddd72cc83205ede62cc832005de71cc832005dd70cc83205f6e658c83205f6d658c83205fae748c83205fad748c832085ed738c832086ee638c83205fce638c832005ee718
  | 33 => 0xe3059232006bc305923205ebf2059232006be205923205ebc2059232006be1059232006bc10592321b4fd7690e32016be6490e32006bd6490e32014ff7650e3205cfc7650e32016be6450e32006bd6450e32005ef7250e3205dec7250e3218cff7650a32016be6450a32006bd6450a321debe64cca32006bd64cca3205ddd76cca32006dd76cca3205f9e64cca3205f9d64cca3205fce52cca323efcd52cca32005de71cca32005dd70cca32005ed76cca32086ed76cca32007ae64cca32007ad64cca32087ce53cca323efcd53cca32006be6498632006bd649863205ef76198632034ff759863201cfe7598632004fd7598632034fc7598632014fe7498632004fd7498632034fc7498632006ef329863205ef72198632036f4219863200cfe7098632004fd709863200cfc7098632006be6458632006bd645863205ef46158632004ff755863201cfe7558632004fd755863201cfc7558632004ff7458632014fe7458632014fc7458632006df325863205ef7215863205ef42158632004ff705863200cfe705863200cfc705863200cff7658232006be6458232006bd645823205ef86058232004ff755823201cfe7558232004fd755823201cfc7558232004ff7458232014fe7458232014fc7458232004ff7158232034fc7158232006fb50582321c6f850582321c6fa305823205efb205823205ef820582321c6fa1058232014fe76d91321b6be64d9132004ff75d913201cfe75d9132004fd75d913201cfc75d91321b6be54d9132006bd54d91321b4fd73d91321b6bf43d91321b4fd72d91321b6bf42d9132034fe71d9132004fd71d91321b6bc41d913200cfe70d9132004fd70d913200cfc70d9132006be40d91321b6bc40d91321b6bc6459132005f77159132005f47159132004ff755913201cfe7559132004fd755913201cfc75591321b4ff7459132006bf74591321ccff7359132006df73591321b6bc43591321dcff7259132006ef7259132004ff7159132006f77159132004f77159132034fc7159132006f47159132004f47159132004ff705913200cfe705913200cfc70591321ccfe7690d32016be6490d32006bd6490d32014fc7650d32006bf6450d32016bc6450d32005ef7250d32005ec7250d321dcfe7690932014ff76509321b4fd7650932014fc7650932006bf6450932016bc6450932005df7350932005dc73509321b5be748c932005bd748c93205f9e748c93205f9d748c932007cf628c932005dd718c932004ff75d853201cfe75d8532004fd75d853201cfc75d8532014fe74d8532004fd74d8532014fc74d8532006f651d8532006f551d8532006f741d8532006f441d853200cfe70d8532004fd70d853200cfc70d8532006f610d8532006f410d8532006f76198532005bf74585321b5bc7458532006f56118532
  | 34 => 0x9332004ff755933201cfe7559332004fd755933201cfc7559332086bf74593321debe5459332006bd5459332086be4359332086bc43593321debf4259332004ff7159332034fc71593321debc4159332004ff705933200cfe705933200cfc705933218cff7650f321b4fd7690b32014ff7650b32084fc7650b32016be6450b32006bd6450b32005df7350b32085dc7350b32086f76198732034ff759873201cfe7598732004fd7598732034fc7598732014fe7498732004fd7498732034fc7498732086f73198732036f4319873200cfe7098732004fd709873200cfc7098732086f46158732004ff755873201cfe7558732004fd755873201cfc7558732004ff7458732014fe7458732014fc7458732086f73158732086f43158732004ff705873200cfe705873200cfc705873200cff76583320057f75583321a57c7558332086f86058332004ff75583320067f75583320047f755833201cfe7558332004fd755833201cfc75583320067c755833201c7c7558332004ff7458332014fe7458332014fc7458332004ff7158332034fc7158332006fb50583321d6f85058332086fb3058332086f830583321d6fa20583321d6fa105833205cff75d923201cfe75d9232004fd75d923205cfc75d92321ccfd74d923205edd73d923205eee72d9232034fe71d9232004fd71d923200cfe70d9232004fd70d923200cfc70d9232004bd769923205ebf6599232006be6599232006bd659923205ebc659923205ebe629923205ebf619923205ebc619923205ebf6099232006be609923205ebc6099232014ff765923205ebc6459232004ff755923201cfe7559232004fd755923201cfc755923205ebf7459232006bf54592321cebe5459232006bd54592321cebc54592321cebf435923205ebe425923205ebc4259232004ff7159232034fc71592321cebf41592321cebc4159232004ff705923200cfe705923200cfc70592321cebf4059232006be40592321cebc405923205dbf76592321cebf7659232014bf765923205ebf6559232006be6559232006bd655923205ebc655923205ebf615923205ebc615923205ebf6059232006be605923205ebc6059232006bf7559232006be7559232006bd7559232006bc7559232006bf7359232006bd73592321cebc7359232006bf5359232006be5359232006bd5359232006bc53592321cebf725923205ebe725923205ebc7259232006bf525923205ebe5259232006bd525923205ebc525923205ebe325923205ebc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006be5159232006bd5159232006bc515923205ebf215923205ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232006bc5059232006b
  | 35 => 0x4ff755864201cfe7558642004fd755864201cfc75586420d6be5458642006bd5458642004ff7358642084fc735864205cfc72586420d6bf42586420d6f641586420d6bc415864205ef7215864205ef42158642004ff705864200cfe705864200cfc705864200cff765824205ef86058242004ff755824201cfe7558242004fd755824201cfc755824204ebe5458242006bd5458242004ff7358242084fc735824205cfc725824204ebf4258242004ff7158242034fc715824204ebc41582421f6fa405824205efb205824205ef820582421f6fa1058242004ff75d8d4201cfe75d8d42004fd75d8d4201cfc75d8d42006df53d8d42006dc53d8d421cede43d8d421cedd43d8d421cebc43d8d42034fe71d8d42004fd71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006df6398d421b5ed7298d421ddef7258d42005f77158d42005f47158d42006dd6318d42084ff7518d4201cfe7518d42004fd7518d42084fc7518d42006df5318d42086dc5318d42086de4318d4218edd4318d42034fe7118d42004fd7118d4200cfe7018d42004fd7018d4200cfc7018d423febf6590d423febd6590d42015be7390d420179e7390d42006bf6390d420079f6390d420079c6390d4205dbe7290d42007ae7290d42007ad7290d42016bf6290d42017af6290d42005bd7190d42005bd7090d42216be6090d42216bc6090d423f6bf65909423f6bd6590942005be739094205dbe729094205fae729094205ebf6290942017af6290942005bd7190942005bd7090942004ff75d854201cfe75d8542004fd75d854201cfc75d8542084fe73d8542004fd73d8542006f751d8542006f451d85420fef641d854200cfe70d8542004fd70d854200cfc70d8542006f76198542005df7358542005dc73585421ed7e75185420057d7518542006f56118542034ff751854201cfe75185420367e751854201c7e7518542004fd75185420367d75185420047d7518542034fc7518542084fe7318542004fd7318542006be43185420aebc4318542006be42185420aebc4218542006f75118542036f45118542036bf4118542036f641185420aef5411854200cfe7018542004fd701854200cfc70185420aebf401854200cfe76d81421ed7e75d81420057d75d81421e6fa60d8142004ff75d814201cfe75d81420067e75d814201c7e75d8142004fd75d81420067d75d81420047d75d814201cfc75d8142084fe73d8142004fd73d8142014fd72d8142034fe71d8142004fd71d8142006fb50d81421e6f850d81421e6fa40d81421e6fa20d81421e6f86058142084ff75d933201cfe75d9332004fd75d9332084fc75d93321dcfd74d9332086de73d9332086ed72d9332034fe71d9332004fd71d933200cfe70d9332004fd70d933200cfc70d9332014ff7659332086bc645
  | 36 => 0xf705864300cfe705864300cfc705864300cff76582430057f755824321d7c7558243015bc7458243086f86058243217ba4058243004ff75582430067f75582430047f755824301cfe7558243004fd755824301cfc75582430067c755824301c7c7558243076be5458243006bd5458243084fc7358243004ff725824305cfc7258243076bf4258243004ff7158243034fc7158243076bc4158243216be4058243216fa4058243216bc4058243086fb3058243086f83058243216fa1058243406bf6590d43406bd6590d43085be7390d430879e7390d43086bf6390d430179f6390d43216be6090d43216bc6090d43004ff75d894301cfe75d8943004fd75d894301cfc75d8943006be43d89431debc43d89431deee42d8943034fe71d8943004fd71d894300cfe70d8943004fd70d894300cfc70d8943006ef6298943005f77158943005f47158943006ed621894305cff751894301cfe7518943004fd751894305cfc751894305eee421894318eed4218943034fe7118943004fd711894300cfe7018943004fd701894300cfc7018943004ff75d854301cfe75d8543004fd75d854301cfc75d854305cfe72d8543004fd72d854315ef641d854300cfe70d8543004fd70d854300cfc70d8543006f76198543005ef7258543005ec7258543006f56118543034ff751854301cfe7518543004fd7518543034fc7518543006be431854310ebc431854305cfe7218543004fd7218543036f6411854310ef5411854300cfe7018543004fd701854300cfc701854300cfe76d8143206fa60d8143004ff75d814301cfe75d8143004fd75d814301cfc75d8143014fd73d814305cfe72d8143004fd72d8143034fe71d8143004fd71d8143006fb50d8143206f850d8143206fa40d8143206fa30d81430057f755814320d7c7558143206f8605814305edf6398e42084ff7598e4201cfe7598e42004fd7598e42084fc7598e421debe5498e42006bd5498e42086de5398e42006dd5398e42086de4398e421dedd4398e4205cfe7298e4205cfc7298e421debf4298e4205ede3298e4205edc3298e42034fe7198e42004fd7198e421debc4198e4200cfe7098e42004fd7098e4200cfc7098e42006de3098e42086dc3098e4205edc6358e42004ff7558e4201cfe7558e42004fd7558e4201cfc7558e42006de5358e42006dd5358e421b6de4358e421b6dd4358e4205cfc7258e4205ede3258e4205edc3258e42004ff7158e42034fc7158e42004ff7058e4200cfe7058e4200cfc7058e42006de3058e42006dc3058e4205ef76198642034ff759864201cfe7598642004fd7598642034fc7598642084fe7398642004fd739864205cfe7298642036f641986420eef5419864205ef72198642036f4219864200cfe7098642004fd709864200cfc709864205ef46158642
  | 37 => 0x2000800000000030000000000000200040020000001000c0020004007000400400040020000000001800700000030004000000c0010008000000400000000010000002000400600000050004000000c0020000000001800300000000000001000000a000c0010000000000400e00000000008001000c00700000000008000001400100000000004000000000000080010000000000c000000000000000020004000000800000000000004001000c000000000100140050000000000400000040000000000000000300000010000000000400700000010000000000c0000000005000000100000010000001000c0030000000000000000240000000005000800400000000004000000400100000020000005000c001000400000000020004006000400000040000000003000000000040000004002000000000040010004000000400400100000000006000400100040000008000000800000100010010000000000100040070008001000000300040020010000000000000000000000000000400200240030018001000c00000140000000001000000000000010008001000400000000000004003000000000000010008001000000100040000000002000000100040040000005000000000080070000000000400000000030004003000400600080040024002000400000000010000002000c0020000000000000000040070000000000800900000020000000000400000340000000000000400100040040004003000000100000010000000000000000000000018001000c0010000001000400100040010000001001400300080080008000000400000000000000000002c017000400000000010004002086ef6298a4305cff7598a4301cfe7598a43004fd7598a4305cfc7598a431cebe5498a43006bd5498a43084fe7398a4305eee5298a43006ed5298a4305ebf4298a4305eee4298a431ceed4298a43086ef3298a4305eec3298a43034fe7198a43004fd7198a431cebc4198a4300cfe7098a43004fd7098a4300cfc7098a43086ec6258a43004ff7558a4301cfe7558a43004fd7558a4301cfc7558a43084fc7358a43006ee5258a43006ed5258a431b6ee4258a43086ef3258a43086ec3258a43004ff7158a43034fc7158a43004ff7058a4300cfe7058a4300cfc7058a43086f76198643034ff759864301cfe7598643004fd7598643034fc7598643084fe739864305cfe7298643004fd7298643036f6419864314ef54198643086f73198643036f4319864300cfe7098643004fd709864300cfc7098643086f46158643004ff755864301cfe7558643004fd755864301cfc7558643136be5458643006bd5458643084fc7358643004ff725864305cfc7258643136bf4258643136f64158643136bc4158643086f73158643086f43158643004f
  | 38 => 0x40000004000000000300000020000000000000100000060004000000c000000c0000010000000800000000000054000000400000000000008003002000200040010008000000800200040000004005000c002001000000000000000000000000200080010000000000c000000800000200050008000000400000000010004007000000000000020000001000c000000000300040060000000000000000140010028001000c002003000000140010014001000000100000000010007000c00000000000008000000c00000100040004001001800100040000000000001800200000050000000000000000000010000000000000200000060008000000800000000070000001000400100000000000001000000000200000000001000000e00000030018009000000000000000010000000000000200020000000000000000000040010000001c0000004004000c0010000001000400600000010000002000800000040070018008000000100000010000001000800c00000000000000001800400040000000001002800100080010000003000000000000040004002001c00200100030010000000000000000000000000000400000000000018000000400000040010000000000000100080000010000000000500000020004000000c0000000000000c0040000000000000000040010018002000c00500080000000001000400100000090000000000400600040030010000000c00000000010000000001c0000010000000000d003c000000c0020000008000400100000000000007000000300000020004000000000300040010000001000c0000008000000000500000000018000000000000200040004007000800000040060008000000000100000020004008000000200000060000002000000a000c00000000000000007001000200000020008000000000600040000004000000000300000020000003000800100000000000000000c0040004002000800000000030018001000400200000000000004000000000000000008001000c0000000001000000100100000008000000000100040000000004001000300040000010001000000100000000008000000c000000800600140050018004000000b00080000000000000c004000000000000020024001000400000140000000000000000400040000004001001c00000000060000000000c000000000000040030008000000c005001000f0004002000c004000000100000000004003000c000000c00000000060008000000000100000020010000000000000140010000000000400000080000000003002c000000c00000000000000000001000000080000000002000000000000020020002000000000040010000007000000c0008000000000300100000010003000400
  | 39 => 0x1c000000400100000020010000000000100040050008002000000b000c0000000001000c003001000100200000000003001000200000000004001000800100000000008001000c001000c0000008001002c0000004002001400300080000000000000000000080000034003000000000000070008000000400000000020004000000400000040000004000001c0000004001000000200140010010006000000000080000008001000c0020014002000000000040000000008000c0000004001000c0110028000000000100380010000001001000200000000000001000800000080010000004000c004000c002000000000000000020004000000000000050004000000000000000050000004000000100100000000000000000400000030014000001c00000000010000000000000100040040004001002800400000000000005000400200040000000002001000000040080000001000000000140000000002000400a000c0000000002000400200000030008000000000100080010000003000000d000000100000000004001000000200000000008000001400100000000014002000000900040020008000000400200000000000001000000000180040000000000c000000c000000000200100000000000001800000000000004001000800000000060000000001c000000400000100050010000000c002000800000000000004000001000000040070008002000c001000000a0000001000c00200000010000013000000000000000000000000000200000020004005000000100000040004003000400800000030004004000400200040010000000000c001000000300000020014006000000100000050004000000c000000000000000000000000003c00300080000004002000400000000000000001000400100000000004002000000a000800200040000000001002000700080000008000000400000000010000003000800200000020000000001c006000800000040010000001000000000080010004000000800000100040000002000000000000050000002000400000000000000001000000000080010008002000c002000c004000800a000000100000000000000000c002000000200000010000001000400100040030000000002000300040010004002000000000000000000009000000400040010000001000000600000020004000000400400040030008002000000000080030004000001400900080000000000000c0000000000003000000080000000000000000000000030010001001000300000000000001000000500000000008000001c002000c0000000005000c002000800300000010000001000400000000020000000000c002000000100040010000000000000000000020000002001c002000000100
  | 40 => 0x10014001000800100080000000000000000a000800000040000000000000000000000000008000000400000080040000007000800300000020004001000000000000000000004000400b0000001000000000180010000001000c004000c0000000004001400200040010000000001c00100080020000002000000000000000000001001000000000010000001000000200000020004000002800000000000000000000000000180010000002000c000000c00000000000000001000800000080000004000000000000000010014000000000200000010004000001400100000080004001000800000080070000001000000000240030014006000000900000030008002000400000040040000001001c00300140050008000000c00100100040000000000400400040020014000001400000080000008000002c0010004000001000100000040000006000c00100080000014004000400100000000000000000000000000010004002000000500100000000000000800000040000000000000000200340000000000000c0000000001001800100000000004001000000100100020008000000c00200000000018002000000000040010000001000000200100000024000000400a000000300000020000007000400200100020010003000c00100040000014000000400000000050008003000c00200000000000000000400e0000002000000a000000200080030000001000000300040010010000000c002000000100000000000000000800300000040008006000c004000400000140020004000000400000000000000000000800400000060000000000000000000010000000000400200000000000004000400200000000000003000000000000000000000001000000040020000001002400000000050000000000000900280000018008002400000000000000006001c003000000c0000003000400100040000004003001000000000010004000001c000001000300440010008002000800800040070010000000000000000000020000000c006000000000000000000001001c000001800000040000008000000000100000030014003001000100000010020000000c00100000010008001000c001000000300040000000001000800000100040010003000c00400000010000003003c00100000000014001000800000040010000002000000000040000010000000000200080020010000000800000000000004000000000000000000004000000000000040020000001000000200040000014001000000000000040000000000400800180000004000001000100000030000002000000000000010004000000000100240010000000000000300000000000000000400a000000000040000000001000000400040000000007000000000080
  | 41 => 0x740800000000001ec8000000000001b998815a8ba2000171ac2712763ea8d8277800000000000000000079810fa000000e024237c1398000000000000025720000000000000000000000001b16ae8241e00000000000000442000086586d03531d322df105c05099d086e00781d2aa5883e155e37eaa20949913873131c09a8a1f2be1000063f80000002ac4b36102674480000000000c6613c43e901ae0000000b3dad8caa900009d69be47890000770286c000188a7be001a0002b36000000030988e200000000001356000000000000006600dac00000009c807748d1afb89fb92465f1193498e12f64b31d8a88c138a0000000b598000a0f00000000000000000052d00008540000000000077b2c0848aa3647d200002192b68a9780000002a005782b6255a80000ad800000017b24ad1a0a16a80000000d1478f000000025e0a78800078d00c60001d5e37f800075011c0c5c069200000000000000000124a000000000000002b58aec8e8a8a8000216a6c105641e09cf85910e0c00000000002520a888000000000000000000002dea0000000c1310a0000000069128be000000000000000000000613b0284401ef0498100400024e68952cf848980001ea000000028128330e8e44ea6a8650000095b0000ba09ca4a5300008c38340884974600000003aa1454975a2086f6000050e098814280000002dee000000025e2fdc000049ab5a0102000000000000006d400c091117400001dda2028000b938000000000086c000017aa0b000015de9ae00008a900000000d68a609c22000150000000000000000a89848600000007d600000000000c2c0000632ae980c593e0000000000000002d09ed4205a5e400011ac8b0800000000006a480000000000000000058130f0000000000000000002abc0001b2864c000094a000033d00000000000b3c10ae00007b000000009ee1c4c0001c6297b000016f000000000008db220430826d2000000046604e20001b18000075a00021180000000000000000000002db000000023921d02a0800023dc0000000a360000000000000000002e500000000ca808e8390000000061d84dab75000000006f4a988000000000000001e667ba02a16d0000000000000000005ff8000000219ac3d800000000000000000b1e80000001970159800000015721bc8c983a500002fd1ee40000000000000000000000000000000000000000000000000974000000000000000000000000056f0000000000031600000002cdc7fd1b1200000000000000b9e00009fa0000a3000000000000000000000000000000000c0a8000000063000000000000000234897cc0400005f312c819b0000000310c0000000a6c94680000d92000000007c000300040000008000000c000000c0080000001000c000000000100000050
  | 42 => 0x5a31ade0000000000000000000005d2800000000007fc80000fc19020001cba000006667a31b6b6218c8000000009380009c28000113317cb08868a6aa800065d80000001900000163c0000000000000000000000000b54390a31eace1d90000000000000004a500007f10000000148400000001229ffcb0900002e59b380002b100000000000296aa0a2fbaa5a1e1827680000000000000000000300000002bd266c0000000274c00000000000000a4780002b19920000000081628ee000271800000003bb2d0829b83862a0000069980002398ffc21d927a65e8000000245800000000000000000000030e2b56000000000000008f89c1a0000422000037a000000056800000001232000174400009283f1140470ca2b000000000000000000000000000009d021120001f862810b1c9dc185a0001e020001ef6000207400014d800000002ea00005d4af200000aa41d200000000c3cc4531a02ef23200000000c3e00000000000000000000014720002d02aed2bbc4a9026eb1e2a46472808ea5200000000000898230224315eebe18000b260000a112cca2938000a180000b122ed273380009a28228000000025c03e414909c6754ad9215c007603f06e4a0c8000a6f02383cb00008328e660001fd82f18000c2e000000017220000000000000000000000000000000000000000000000000020033e5609d340000aa600012f80f880000000000000000000004c46cb0000245ae0c34a9a6ab67800000000006238000000000000000000a59fee0001e429150f1c3b50000000000000000000000000000000000000008fe177600008ce000000027f800000022de0000000000000000000000002602000203c000017c54980000001e6e0000000672000007700000000000000000003100002390000a948000000310a0000000000000008b1cee00000003911c2e48500000000e5e000264e00000008ab8d0c00000000002a90000000042c9b5296e800000000000000000000000000015468b220306e1000000000007530000aa7800043f0000000000056d9b9000000000000af200000006b90c3676680000001cb455290e0822800000000000000a463c48000000000000000009e912d41e72c6000019283ac2ff400006380ab80004e987f48381a10000000087e0cb819c00007e38000000000093b8100683adfc3e00bf252eac843ae9e32000182439eabf440e000041f2cd62f20000ad7000000000000000000788800000012986350000000000000002500000000c2b812402b053898caaba3d7001c000000023faa540002f7400000006df200200018860000000000000007c8000000000034b800000000009039b3e0000000000000085e80000000000bc2000000016843810000000308e00000007050000804800000000000000
  | 43 => 0x2d300000000b9d0000000000000000000000000000068678f80001b600008808000000000000021109070000abd00008e0000094f00000001efa0002f24aa28c1625a800000014dab25a81c65423fc7f52fd20eb22241aa15ac13c1fcca369944000000000030348e300004ed80000001d18000000088707da82300002b100000002b7a0000000af20000000000000018c00000000000000000000000000000000000000000002449aae00022e4bb180007598000000000000007727040000ac2a056000240a000000000000000000000000000033683e800000000001fc0000000000000000001e56a55965a00000000000000000060e06e80004d6800062a8000000000000000003d584422adb12000000000000cca4841c00000064200017ac00022f000012b6a159a3c00004ec000000000000006a7258600000008c60000000000000000000000000000000000010ba0000000000000058a00007732046017885e000000000003eeb7a28ca00023d0bcd930a1e90cc6000075c2a80000ba1800055f000018a000047d00000000000207979849a8000000000069188cc00002c669698e000029b886c883e8b9800000028403619d360000000000306200000000002372000000000000000000000000000000010820001c8671b800000007ba000087886d00000000000000000000000000002542000062a9708438a79890abe780000000000000000000000002a5a2f433a97382648000000297c45d000060e000082b00000000000000000000000000000000000078c00000005b2a06a18311ce5180bd0000275488180009bc1c967a00016580152215e0870000141a55d082e5e4a4524868db46901e84c0e80007948000000000021b00008ef909407f9f9a0002fa400000000000000855000000029980000af40002bfc00000001a38be2b3a1114b06ae8026b0bdc3970a241020c809520000000000000000003b8804a00000000001a4a00028a08e405227f980000000000879800090c0904354939400000000000000000000000000000f2000083ea8b400019e400000000000000000000000002260000000b07000067811400000000143863a00000002818f102d30000000000000000000000000ae0809200000003948f7c000000073d920c0000000969254a00000000001ac431713fa4de013a66a800047113f4bf1a99c2d8a650b1b2be48b504f200000000000edc0000000b55000016a208e95491700000000000000093682d800000009130000c3783a600001949f5800000029083c1993200000002fa00000000000000000000000000000dc4c149f7e000000000000000000000906000000000cc00030b400000000002b660000000000000000022dc7fe000000000000000000000000085e1f24b16a6c01929c78a5b00000000000
  | 44 => 0x60002f102360000000000000002d4000000000000009c500000000000a3b1982b0d005c5051ece000242400024020000000000000007080000000000000000000026fe0000000000000000000004442c3000000000001a2a000250c0002e2c0000cc40002d4a7cfa47e00000000380da20000000000000000000000000000000317664710e811b99ea000000006200002b800003c012900001bd095a0000176000000022ea094800018f819800017022d590cec02000000000007608c5e41600000002d7c00029fc000000000000005161a9e0000e307e91c9e00022be1cd000004c23de47f8510c66914e25d1d265988000000196a7bd211ca718000118000037d00006e800000000000000003e0001002988800000000000001562145aeba906ab2098b80ca029000061496880000000000000000000000002ace00021380000266743a9900001d480d686d600027fc00000000002ac6000000000000e6c3200004a68000000000000000000000df800019d67b818100001208101a31a11d27fa00013720000000000000038c8f3800000000001cfc0001a2e9d080006ab0000000000000000000000000c5994de00007ec1b716fe00000002eeb0ec000222c0001ec44891956c0297960001c8a658316a8bb1dee00025980000000c3f00007de0000000000000021fa00000006b59216847b110680b042ab20e4c87c005800000000002cd20000544000077c32f800000013d600000000000d580002f548be000040500000000000000000000031260000000748800000000001e20000000046400000003eb8d4461028e88fb0a569b286580000000b21800000000000000000771800000000000001a6c00000000000000b012826c7380004bbad70000190e000000000000005729f44bcea02210f0a0a39000006e5000000000004470000bc8aab0000000021a972667683ce7678000ad1ac9a00000006ba000000002d6b14a782020800000000000000000000000019a1ce6376a102928904eb3080000002fbeb6900000000000a8b8000000000000000000000000000000039d000015321d29f2800000000000001d80c3ca9e849d313a6ac1422a9f95a23f80df21fc1586c0789dc27603d2c6504d6b7621d42c52e207fd800000025da00000008e5818a9cc8000414800061b8a32000000084c80000a400000000dbe0000ede12e033400021c20002d580000f1e00002700000b009ab0000c0500000000000428a4280930000000000000000005bb80000002510c290000ac0170a0000000005000000000009da919e3922f6e31d16e203e80006e48000000210a3610000000207a000004e0002e9c0000000bb32eb0a260f3a00000002151a82000000081e000000000000000000000150600000000000000000000000000006af14184c39bc6000
  | 45 => 0x6ad4c1052a249e1249400004ce0000000bdb0000bd89fd28421e7000000000000000000000012988b63cf0000000257679b1f920000f3e0000e3a00004f428a80000001cbc00000001bb221a870000000015343b419f25310ff0221313000027c20002ca4000122238f0000000000000002420002f7285f28de288800088802f2000036c8a2a73800000000000cae326800085b00003700d1690d9be8bed0000a4891de0001d8621ba54e0001d2ab7e14bc0000000000106c51080000000000b568f240001af000026f64e70000b58000062f2790052212282e104a000000068c80004598000aee854a4411a360000000000000000000000002dde000000039a0000000000076c8000000000000000005e380dc63e9b1e1b10d94493800000000000000000008800000000008c507e403f8000000000096988680a98c8a0002044bec19686752ed8000000000001600000bfe14a23e86578000000000008500000002a705a79c0a000000038600003ca94a600017d00000000000000000000000002b969fe2464a2f2bbe73a0000b038000000000000000000000af0000000079314480000c9200016d22b71da20000000000055ebea80000000000000000000000000000c02468135e58230460a000000f40000000220a00000003b28000000000000000000000fa20000000000000083200005750a6400000001c5acbe000000000000000000000000000000001828210000000000000000004af00000000000018025c000262059529d40002e8e0000000000153072395fa5f9000000010c800000007fb00000003174000265600000000000000157000011484e80000000aa031ae1079ae200000005c20000571b0400002bae000233600018a4b8180008399b060000000000246e0002aa8b4f000000000000002bfe84d0ce62882a4000000004f780008ec00e464980005f71e8e00000004cd9a420000a58c1f0b120f51c7e000121e106b05a3f196ce00000009c6abe80000000aad9d0600013040000000000000000028f8a2000000000000000000044804b0978800000020c000009ee000092e000000000000000000000000000000000000000000237800002f8a021302dc8b8c8000000000064a9a4cc0900008ec950c00024400002e1c000000000012a69bc88003fa8ce8b5d14ce00000004c0a9620000000322000000001f6b79000000000008681e540001bceabe00da0000bfcc461368a9d8000018800071c972e49f1e8c00000005b7800011a8000052800000021760001bde000141000000003169b240fe00000002bf000024dca8f800000000000000000000000071086e80002e720002d5c0000000714a2d2000110600004ea00000008ae8000ac900003e125c000000000280000528000080600006a58000330000000001625f59fc
  | 46 => 0x3c59f816e00001365d724f01151cd09c88b2a000000000000007dd800000000000002f880000000000000042e0000000136e000000000000009918000b65034492799d20000000000005a0002c4e218219e00024a600027363fc800000000000000000079314e981aec228a00007a500002cb000000000003b39cae3cd31924c98000aa5800000029c800000000001fb8000000000000000000000000000000000005243044000000000000000001a2404b30aa00000000000000000000000000009ac9d4e0df85680000d740001a38afc8dca000000000000000000000000094000000007960000046a0543c8000000028061aa97620000a7c00000000000000a971f620000000000000000000000000e6200015d878a00ce564077e4b195e62e00000000000000000006188000bf604b29d2279a72d8000a21180266e80000d5800000018f800000005470000000048e00000000000000000000000025ee000000000000006522524000151a00200009b50000000000000000a60000f169c300000002a3200000007c22e16bc98000378132cc3a8d6a19c8db000000000000000000290444900000000000000000000000002d280000000000b0e31380000fb6755000000000001210000000000000005c60001cc66f700008bc80000000bf0527291a0e51a30000000000000000000000aeb204e0000e38a4d00004ae00000000af8000000036e25fe7e7914c43b000000000003a4189200000000001d1e0000f7600017941668000a76aebe7d300000fc8000000188883f99b4a95823400018640000dd088c9fe400000000fd8000c690000a6d93343a9000000000000000000000000000027ea000139a7201ed850b15400000000327000033519be000009600000001f0800009b0000119812a0000000000000000000004df800000030c000000007e080000000000000078000000004ab000000024125ab81389c700000002ad20000000000307000000007759b440000000b63800000000002ba833678e0ca4b080000c548000000242e0000000000000000030fe00020da5cb19dc00000000bc0000a6a8000000161664f815c000027e000000000027607cf0000a029efe000239400008b40001c8c21731960002ade6a90000000000000000000000000add000000024680ff00003b1800060f0000000000000000000fe800000018d665180006fc00000001ac20000000000236000994665032e3c5732d7aaca861000031860002b30997012eb821f0200000006fb806cadf80004c500003128f50000048226b800000000006652612056082a36b9e763b82ee60000e1c1daaa9408089240000000000163e0000000000000000000002fe80d0000000000003a2a689dbac3600005d08da00002e4c9870000000224ab3180000000000454a594a6
  | 47 => 0xd340002fc2b000000ac700004f180000001b208e12cb200025aac64000030f80000000e3676305dc000000000000005fb9eb6b3a8acc0002cccb6c000000000000002aec0000000000224ec5b896400017c8000131800000009e380009859d92000000000015941f41f6a0000c560000000000029400026eaa0e00000000000000000000022a800000000000024179a3b600000000c8000000030740000000000000031b000044780007e880000000000a77000000018b800000000001cde7d800000000000053214a00000000002db6ab8800000027126e6800089200006cc8fd600000009dc99e20001c9c604880c2611a14c268000000000000000000001566bc380000002b80bf000007300000000000000015a800000000002a8686d800000000003778000000000000000003481532000292085723e4370937409905949e492580003012a538000989000000027b00000a0e76d800080b905a00015525f01ab83f400000000000000000000000000001c580000000000000000009c80000d3600030860001ea8bcc85843a82d1a0000000000041086e80000000000000000098b0ba000000000002da800000000000000000000000001e21538000000304e36e856200011ba00000001080000000000000025460000f8a000000098d0000000114800019eca758206027800000000008190000c5e8000000102e000000055e00000000d64000000000000000002fe400000000000000000000000007c884c25e60000b6e30e800000025780dc874600000000000000000000000000009a9800000000009de800093ea0d2a6280002a530e80002dbc62600000000ab20000b0e1e78000af68b3004c8000000075055500000000000000000000000000000000000000000000000002d6e4e5800000000005f6260473c2164736a1048028230000000057d0000a1a0000000000054b800000000006ea800032980009d780000000bda00000006d9a1c600000000000000000000035e80002d700000f781d4c52827c0002e340000000807a2b2000000000007680000000000000000024e8000000094481d8999068000005fe00000000003082000108a0000000b8b8968bf98000000000067f800000020de0000000a2994ec00009ba0002608000000084a800000028360000000000182800000000000000000000076c264c2c99018263800028d00008559a2000000006d5283a00000000001bc810d0d6c283169600002ce0000000aee0000bcb00007928000000160e000045e8770000000000041a80003a9800098680000002ff200000000000000000000000b83ae00000000000384b918000000000044d800000000007ba000000002b0b920330000177235c0000c08aff08da257e00022b4000000000000000000000576967600015
  | 48 => 0x698000a7eaafc0000000000000000030e6927000000000001cd8000579000054200000001b4e0000084a2a80002ab8000a3c86741a1000000016fc000000000031b097302f40002cc8aa2179c0002a164a300002b200006fe1e440000000897000000029249b21d1a0001f1400011d4af60000639000000018cc00000000379e2c00028f60000000693999e00000000000afe000009c000314800027fe2f11b3a25504a0000035261700000000b2e7a18a00a909c9407d155800030005f98000000000000000006cc000000000005b98000000000000005984ea800002d8a7807412180002f8a4c00a740eda0c60ba30669c08ce0c319172c1e9a26000000038d1a0c5830fde0000000000000000000000000d66000000000000000001a601b3a3f66128000000000000000005e118a863d303025221847a990780c9a87017d0ab0a06162e0000000000205c0000f3600000000001b3600023d4223032a57001aa0000000000121c00000004c680007b300000000000000000013e0000000000000022ca0000000000000000000000000000a508a680000000a438000000000000028d0c4d0000000000000000000000000000269400000000002244000000000029720001b0c2aa2c68000270e6de8122b2527e60001322000000000000000001b6a2518c94000092c0000000000000000019f0000000026c800000000000000000c6e88dc912af700001656a3c00000000000000000000000001ff800000000000000000000000052797c25ae88fc0002068000000000005ec0000000a69000000020bc000000005920141b28000a1f0000000255e00008f200000009e300000000000246000000028540001d7423195200baaab2bbd0000211800096e0a366b70000000000000014f600011c8a440000a08a32e5a90000997912e968a26a0000000000167c0000000000000000000002cd00005f500006dc071e0000698000152a5628000078000067000000000000000269873d24f4869000000000007f080000001716000138e00000000002214bfe0000adaaf5200010e44f8b10627e000000000002661c48430800000000000000000000000000000000000f040000000000000000000004f02710b1d82be1f780000000000467000000eaac0000177e76a80006e90000000000092380200000f7a20688bc586973e0001c745a18000b8e00000000980ac980008738000acb1098000000000000000dc000026a000000000000001a640b10000000000000000000002b4e21c9732000000090f000000000b80002ee200000009de2cde0000000769800000000006b4000000016483e08000000000000000000000000000000050796f80000000b108000b1580005f88aba000000000001c800000000000000000000049c910e000000081c80000
  | 49 => 0x43688b200023169170a4005c9cfab1baf300000eac0000000be6164c00000005db8000be5800000000001418000000000000000000000e9c3348000494800000000002328de24d3800000000000002c06000268ea6c06f6000000000000007eb2d9a13191fc7010000000229e000000000000007d496ea636866a91daa6ec1418683d600d2000000000000005ba000000012de00000000000c2a0000f4a92c91785001d2400006e60649fe85879cca1ca8c1200009b00000fb20001a5c28400006d622faa4cac70b970000000000000030ba00000b400000000000000000000000000008bf800061f0d4622c00006a194780000ee447400006d080000e29f7222487dc000177a91e00000001f0e02a2e446a33032ac1000000000006ef1c30000000041c80000000000000000000000005be80003308bde00026700000000084000089c80005a0a04a00000004b4187072a23aaa13069e000000058800003f28032c33800000000000000000000065c00000000000a08000000000024ba00000f8824aa8e0002dec0000000000079a000000078e8e2800012b01a8ae0200000004cc307e00022d673cadd6000000000000005ab000000026e00002a480001d6e8c188e000000008e72a7a00006e24310b240d880000000000000000000000000000000000000013500004e1800000000006d780000000000000000000031780fa893e9b91344068800000024bc045943047487000000000000261000000000000000c0180000002a0c00000000000c6000010bc00000008c300001790df60002aae8f080000000000000000000000001e28fec0000000215b1587ff857613d8000000000000000007d71406629abe000000000000000666800000011640000436000000000000008a70b8e871000000018f200018dc000166e0000000955000000000008b6ad329fd000000000004e08a7200000001d30000000058a0000000b680000000000000000000000950392800028980000000000578800000000000000742c180000000258c4fb0000b60000000000008d89c4e0002950aa6910c389a5640000d760001bac704908600000000000000000240400000009e0012000000000000e7254e815a000000000000000001254000000022a2dd22c11d3e0000000b049f3400000000e92e560001e2000000000000000000000000000000000000a8d872483395d2000006a00023546f48000292042648a00000000000000170e0358efa8579ee65738960301135441987f6204a9160000000000000000000002ef80000ea8000000000000000003a2000000000000c300009e7a09c0000000000000a5a4aa3c00001e8bde245002a93900000bae7a880000001a545ed12aa0000000000000000028f400005d000000000428000c328000000000000000008510
  | 50 => 0x123c000000000005d2000023e0000000000000000000000001c5aa5681780000882000132e3af0000000000097d00000001bea0000000000284600000003e480004fb85f81cf8000000000006d29060000938b0f80000000000144800086600006ec00000001c50000000098f198cb1180001672bde0000e8c00000000000000498800000000000000000000000000000000000000000000000000009d900002b92c54940178a9b88000000103687a0000545800000000003ab800000000000000000c28899000000004780a84a5e9f9000000002c584563052d38450a23e00000005059d2c0001d5a616228600000008b1028800000000000000000000000000003da800000000006ec8000bdf000053a80000002bf833d83b2000030a0000000000000000000000001aea073000000000003d680009f6800000000000000000000131c00000000000000000000000000000000000bae242abd80e6000008280000ed600005b267e16a08da800000009bc248800000000008f18000000141c00001ec0000000000000000000005149fae00000002400000000280c00014562af0000000000000014940002f940000000000101000000000000000000000000026f40000f143400000000000014e800000000006af8f2ea1e013400000000000d26000000000000005142b4c0000000000210c0000000391b0cc65900000000000253000000007fa0000000000000019880000000ff80002f76275000000000005c0000000000000000de46db000000002c0599800000028661c28d3e1b00e0e85c2a7c4e7800000002e20002e300002a2c15b94820bd8000000000000031c40000000816a0b40003018000000000000000000000000231257100003241c7000000008990e868689b5abb81f560001b0800000008760de83001f4a00012780000000c5c8000000133c000031c2a68000000000000000000000000000000048f8000000233c00014320000000000000000000000000000ab32cfc000000037f000000000000000000b0c8b466be0758a84210e00003e63d0ac4c00000000000000000290c8f81da400030840000000000000000000000002d120000000000000000000003e800000000000000263a000020a00000000000000000279477e0000a8780005e43038000214c000000043d98ac0000000c4f1cd648493f00000000000000000000000002db80000000000000000007300000200000000069600880000000c151312ad80000a0580003be0000798800000000000002a64b3880000000000ac780005b70000831000000000000000000000000000015b4000000000000007c597de1b302e4521800062800000001c440000000b9a134c00000000d38000a9a8000000221e000178200020524d22ef80000000c0b91b600031804348000
  | 51 => 0x6520000000000003633f8000bc11cd2ace8502000118e155a86a00018e8000027800016740000000ba680003d300006340000523000085804240000000000000019f0b880001f1a3ea11803803182a9d2b4a000000000000007e580000002b8e00006540002e5400007860000000a22000000000000002a5a00012e84768d3c00013ae2ae11560000000000000000023707ac192c00000000000000000000000002dc00000001470b8c000266093f21e20002e12229800035b81b0a00196c3d90000000000071986f017780005c1870800000004b48000611976c000000000000000000000000000053980000001a520000000b9b0c2eb5a80000000000c4d837600000004bf01dab209a5ebf41ae600020f0304000000000006628000705898a14d000000000000830000000000000003920000000504982e5da91920000000000000063185a280c80002cd9a783bb8000000000023100000000000000000000000001ba8000000173629b2f3c0000000000000030c80009920a9800000000000000000000000000725530000000043200005e8000000090c800052a8000bc78000c6c9aee0000000a5e00005ad8000661015e200aaa07c72e2800000000000000000000000021141329118577000000000000002f4461b0574000312c000012844c8176a1680000002c7e00028248ffa8ce98300000000862000000000000000001b4600000000000000000000000028c6000215200000005e99c760002df451f9d168c1030e0002d2a00000000000000167800000018006361ac60000000000263e0000000000142420f1b88bfb0000c03800000029700000b8667d00004dc00000000000000000000000000000378be48000000000063b800000000000002e7a85223445fd862cb6b0000b8e9514000004877a00000d78000c00800000000008140000b4b1e6a5358000000000005c14e00000000000000000018ec000000071504a85bc8000000000000025b4bea0db600013f20002146000180e000000000029e015f20349000000bda82a28f297bcb4f9942000303e5c515f01bf83eca35134a0000678000274e000000069b80000000000000000000000000000000aa98c2c0002b780001ed0000000000003a00000000210096232aa16e9ce800000000000000d8e9a7800000000004a0800000000004a1a566b4890a800024c2000000000000000003104bb90b203890000000267e00000006b6000000027bca6300000000000000000087d93dc000140a11615b000000000000308000000000000000000000000091c59c968e32893da00000001918000249a5dc00000000000000000000000000006f500000001b0e0000b100000000000000003b164a0000000000000000007c04070d88b0b3108000083a9562f3400000000000000000
  | 52 => 0x299ae00000005938754a258bb0000000000025180002e640000fd400000000001f740000a4c000000099c9fea00022bc00000000000000719000089c00000000000000065a0002292a932116000000000029f8b7c053c43b800042113ce026800000018fc3850000bb680003cc821ab3b2cae00006b026f8000000000000000001f801f800000000000000000000000000008d2919aa348000acd03cca69986600000000000cfa0001cbe65b8000000260a0002be643f80009a080000001ba247880000002b8427da234000195a74a06d4824126e465985496208a0000259000022800000000aa894ae0000c440000000000000000000000000000000087e000000000021bc000187e78480000000000000000016190be000261ebb110ea8e28000000301600000001331f2c417afde2c287f282f800000013b04379f40c1c8000000000066dad0a47929c00879040000000000000000001306000000014f820400029ea00028fe04faea20002bfa0000000000000035f800000017be00000000000000000206c00000004038000000000000000000000000b6a8000b43000000015ec3d100000000000000000000018b0bc2af0225391ec00000000000000000070ebd300001c68e2a36280000000000513000004f00004f980007e02ba64c785185590c0e1139c3850b9e5a4699042000000047e244e00000000000000b97857200011463ff800000000000000000599000000000000001342549000040900000000186a6580000000000a4ba38649f80000000eb2191226e000000070180000000c0a000138c00000004df27dc87d2ba458a8bcc0002c880460ab4afa8000c12288200000000001ae07978000000276691f15109da199cbb70000000000023a0000c1e0000534a00e2c080000002ffe0c923ae00000005fc800000000000000f5e0000000000000000012c4000000084da4ce000000000004ba0000000b1f00000000000000000000000000000000000000051d9b7e000000000021423a60bd200017ca23e80007ef8000000000032800000003098c51048c0000f7e000170c00487902f5265a00010160000000000000000026c200000000002334415b150ac6800000013240001570ad081747ca8b3840a80000001b02000000018480000000000000000000028021ce00000000f4e00000003fa0000000000000000000001c98000286e000183a01d0f9853ba3b8930000076e26cc5e1800000000000000000000128e254aae000000000001a720000000c6700002222cb8bd78a8a00010462d00000000000000000000000000000000000000008b3000000000000000000000000000013660000000000306e46a80007c825ce1c82e5a47e807c641245a66880000000a82000000000000000002aaac400000000000000000002b0000
  | 53 => 0x73fa8ea000113e1128222000118843c9a16000132800024800be000062ea0fc2ed839c12b0000000190c00031568f59b34813302c7540fceb888000000134600000000000000000116c00000000000000ad10000000000035731a6265a8041d131d20000624000000000000000001d980002bb61e98000c590000c1a8000af400007708000b028000000000064d9aa085016c4896a4ca23c0000228a34092e1d68c24a4e40002fae000000000004460000000ac303be1fe000042400004e89fc8adb0000b860000c578000000000054fa42cbb39e361b49d100000000c37000000000002618000000000016d800000000003e3000000000000000000a7bb116274aef28cc0000241a1ecaad2a8cbab8e828838c08000000044b000098a2f64000000000000005d98000000000000000004080000000291282d8000c629d60acca6b479c800003b984800000006b007600001bfebd402760000000961000000000000f6a7968e6000000000000000000000000000023f27e700005828000000000000000000001818b76861e225253a4b802e0c71a9b494da1ca0be80003bf83600002d1400031887f89fca3990000000143cbf3000000000001f18000000074e00000002e4000000000000000000b2492042da9e7800000003eb0000000000075f29380002bb00109a1c0001d9c0000ae63e40fba0002324000000000000000001ce22728000000000056908f602c86de0000f685cc0a5c242133a3c68000000000000000000002776000000000000000000000000000000022e0000000059e0000000000049080002a200000001182a77800000000000ed0ec21e4a7e0000000000010a600008da3f00448a39a13ca330e800000000000000030a05c20000000b418000000000000016a800020800000000000146e000000000000003ba00001db049c21100007072fe200c301a319000000000002afaa04c470000000000032f0000b2d80004b2800000004680000000000000000000000002abe000104c0002dfa0002e96000000000000009f000000000cb6000142046b80000002d769ef9a28739000076500000000000000000000000000000000000000000000000001efc1808dec28e8000000162c00000000002492a268000ae605ae2a381c40000000a17800020c00008f3000000030ee55380004e60e5000017240000000a0b8a8c1b6800000023e600010a4000207c0000000000105000020965a00000000000000000000d4000099480007a82fac00000004c32a300001990000000000000006b5000000029a000000005e30000000000000005b8000170400000002eb17b0000000000000000000e0a22ba33a00000000000000bd280002d98688a42a34809ca50e00026d0a5d932a7828da800006c6a47000000013d03a7a87a2aa892aba
  | 54 => 0x103e00000000000000000209ab92800000000000d606c200015600000b68b192000793a25e00017ce1520000b0a2f0626080000000000000228c43c0000000000000000004f29c2800000000000000ab7000000013ac00000002f9821699a000000000009850000af30000aa4a26600000000002d6c0000000000000000000000000e20000000000000004acaffc18887cc1a5aa12000000000000000000d0290208801ebae5200000000000000000000046c00000000e7e777800000008d42fb922e000000097a00000000a62799800077d16520e58fe61a800000000000aa080006278000000057a00000000000f182678000a1225a800018ce00000002be80005d580007c0000025baa280978d4082a13206a686c87ca0260b16043a00000007ab00004990000000194e72b000000018224e000000001b72a5d0a7000000006e1800024e80000000000000000000000000000000aae1eee28f07520061d0c31885003630ef2a3ea268000309e000000000000000000000000000059e80000000000c4a800000000000000e6a00000002a8aa9800006b800019b800000000002e660000000bf510540000000000000043700000002186586000000016360000d9e70b14440002de00000000000000000000001a6881c000000000000000000000540801019da8140000000000000000027ac00000000000000000000000000000ef22580000000a040444c6385c40000b44000021ca749236bd20000000227aa2c80003460000000000075900005722094369a4340000000000018035780000002194000276c00000000002bee55b800045422a0000000000000000da80000000000adf209e0002f40000055a00000000410be4000135c0000000ad905e21d78000000000056a98ea00012663b31dac000097600000009a58000000000000000009d282920000000358800000000006caa864b2e8000000191884a0000000000073087d64db052086b28c20001a12b610d1e000137a7639dbe00000ea000000000002080000000000000000000000002a1800002b8000000000000000000000000000000000000000000000232a164000000000000000cce49b2fda0000000000073c9422fd679724703f3004069423da000000076100000000000b3d00000002c142c3251e00012e25b800002e100008a98000000000000004bec72800036f000000000000000ad000006ae0001b400001962b4600000000000b66000000008220001f5e0000aee000000024680000000000000258e73a86b40000000bad07ac9b624623e2000006c80000002fea0000cb45600000160b0580001bd6c6a0000567000000012209860cac85d063229f89f027b00005b5000000000003672960000000000000000000b0800000000001b9c81da0b20000000c4b800000000
  | 55 => 0x30800000000000000000318c000000000000006a38d7c8fea5228e8000016200004ee81fc000000014c9f04baf2f9a000000000000000000000000061c6e78db2b52000000000000002d0000012d8000166a96580007760000000000081b9a18000000051f241021f000080a002c000292800000008568000000000000000000000000a2b800034a1bda0000cba0000000000000000009c2000000000007be9c1810e58d00002de09c496c80000001d140000000000000099bacb096b800000000006fe9dfe0000000922000000000000000000000000000000000001b0a0001aa200001d6b1d2c5e64e80005b60b9840c221600000008ca230a23091eaa320000206251aa5785f000000000002ea48290000a869bc0adc084821e975eb2f29ba3f682ec6de0000783aeb200000000000d5a044801e00000000002592a602e0a3e380006b28ef6273866e28b05584fe00003b630d64e82ac27738eb8b9897106f0afc8581871254288986442c2a84f81ea74ea7cc00014cc000000000010d00001e1e172207095026001868cd000000002f627b27af9f220002e8875f800070200000af00000000000000000059714a4000125cad227e400000000002cf260d00008070f6253ea4ac3cc08f8c19026857e0656000000000029f0000000000000000000dc60000000a1c8b3c00000000000000baa00009fc000000000000000508000000040c847e00005e039bab2836000006289912102ab2e7118000c4080000000000720929c0000000000000000000000002756ad79a7c31c05048948000bb79658446800000000001630000000000000000003ee1e162eca8e200000000001d2e0002ffa00011122732de64b5839a059b05640d000000000000000608000000000015486488000b078d04395800000011cc000000077a8000403000000000000db80009d60000000000000000000ab1d78424ab9246425d44ae80000000000000164677922d81ad997426e2a3400000000000000726908c0000000000000000005c00000000000000000000000000000ba9895a3420d42100000000000007c29e04c68a9947ba800000000003c280005612992255800000020c20002ca27e1000000000009c9800000030e40000000000000000000000000836503a8920001b1c00000000000184000000033f03a800003063fd800000000000000000c4a1a34652ab943798000000184c3528000382000000015b805b00008fa862e7ec04d80000000942800075626a45410000000000000022400000feebe408a4000000000000000001598afb0000000028e35c9e88323000082086acb53ad962509ac8bad800000023ba1818bce0000000214ab120000000000253214a80005372e360000000000000000029180000000000055000000000000dee000000000000000
  | 56 => 0x6400000002dba00000000000000000000000000000000000000000000028e00002a785ce80000000000b8526803fea040000000000000004f08000a18acd40001dca00030e230616c60000000b0f12a0673293a124283448d26be7621c56add800000009e02e92dce77400002cfa4746bb0ad406f014ec0110c680199fa01f933e4302a68be8895e64e03148a8824800026ae000142617ea52caab212e5759d968a6a72c44d297e79f0a52c6a877601e9e147ce811e000113000000001941f6e000304a5eb8000000000000000000002bc2000281a0000000000099a5238000adb8000000000000000000000e4ea10a570c341c3a0001f384a020860000baa000000000000005392c500000000000000066c8e9a1978000681af1c000000000000009bf26aa000107ab7d80004a10d98bde80000000000175000060680987ad2d2e86284fcac1adccac58000395052600000000000000000000000002fc6f8a4c40000000000054676a26ce951000000000000002276ba529ae8fc000054e01ee65f17a02e280000000000967a0380000000000000040200000000000000000051900000000000000114a0000000000187812520880000cee3c2000000008be12da1660000000bbf00000aa8bd602e800000023f400000000001bf600012300001194202000027580000000000000000089fa8ba000000000000000001826000104800027d80002562bb52c8e93492a87f68000000271e0000000580818e1a70000bbb8acac570cf200000000001afc4d400009a328a26adab0845f19080001e7e3968000b00800030c20ec0002228000000000002ba0dd0e580000a185512e0090e9f1800028fca239be0acf800000012c01f492402b4aed004414e20000f52afd80000001f5027aa8300001288bba8000b0b80009761c020002486639800000002ccaf280000c11c7cb06000000000003c3800000000000002dc000000000000000000000000000003c30e3e120000002507982e6912a9d1ab185fc0256000000000000006a28000000000061d00000001440000072cc4780000ff80001be8e6c8aa849e0002700a4501a000010d4000128a000306cb1c9718000099c0000000000097283d8000000000041b8eea4b080005b029cc92a116eb0da3ce00000002e782ca00010620000000000000063da7a225b000078000000e380003472eca0000c66000000092c06a63c980009af24e20000dc80001c7a00025c417b80000fd0fc80002a0a000000056b90220001b9658c1670ba127ce76b893ca87000000000000000000000000000000000000000000000010b00001db80000000000a8ea75260a81a822780000001a1e00000000000cec000000071a00000000000000000000000006ef8000000000094f8000000155c9530000092b124bfa00000002
  | 57 => 0x9e984839edc386a3d2000000000007b8a8e000000005fc1c72d0400000007b6b1d6b7cafb200000000000000c2800000000f860000902b12916a0001f8c8012d0e00000000000000000000074e15280001e7a0000814000277c1658000000000096d80000000e929ae98302c196a69ca907686380006a40000ab9000000000000000000000000000017a420400000000000ba400000000e7000000002e0800000017aa00002c800000000001a3a60180008498000000025a0a60b7000000000000ed2000000065c80000001c9239f09347e8116800000007a7000000000000000000000000000008b80000000284800000011a865600008d71d76000000000000003dd00003c88000000060a00009a6ae70e84000000028c0000c708000c178000922acb4000084c9569b4c0000000000000000000000000000000117a0001fa6000000074100000000000000029c000146a0000000000000000000002018498000056c0002c809ea8000000000000021aea14000012a909a7868000af50000000292caba81c0bbd80006ff223a00028b87ef220ca7d1a565f4a92a6b31b804398d1a31080004b98000000000000000000002caa85a047c321a36e90512f400000000000000abf8000000180a000000081f8866000000000000000002bc0b8f893600000000000000be082740000c22c5090e200000000000000000079600000007ee96a257f97349d120f483bad42000000000008860000000000000000000007508000306968a954026aa5b800000000009e700006a98a6600015f200000000000000b49175a000000000000000002f0c0000000671000003512500000000000000028f800083524169ed1cd4737000000000000000ea200011beaf382e6000252e0001b8a00000000000000610950e7df000000011bc307b08c5341b4a0000000000000088da39e000000000002a80002484000000002300000000000c67a28200031b400003ca00009b400000e872c14fe6231cd800006ee000216231e80001b80f466aa011400000007090000000000000005f62fd8052279252a000231013e800056780000000000c610d0eaf580000f60000216157e0002cfa00000009f21690aea00009df8adab8aaad8500a01660b1ff09fb1dc467d973c0ad1f1e10314b2000029e00030fab71000000000005b300001758000000000000011ee0000000c5f80000000000000000000000000000000000000000000000002f160000000000217e5e000000002fce87a9e5078306944001d7a000000034e00007ea00002d2000088f256e0000428000000000000000001b1000000001ce800000022840001a6200000008de00000002e6e461800000029ec0000000000000000000000000e767b280000000000000000000015d00002d1000000000000000000288c
  | 58 => 0x42a00003c662b80001ff08d600009aa1c51afe6310e2c65300000000994000000000000005bb00000000c40000000047700000000000a928000000000077d81260002250615800000000004362e24b45800000014be7d90154000035c000290000005cc0001c88ab52cc000008eebdf8bb8630a18c7a78000000000041d000000009fc00024e00000000000000056984dca6b18f000022940000412000000000000000000000000000000000000000000000308853d10b60002d8a0000000313800067f0000c22adfe000237e8cb01be19f836400105a45c491b82cc8d3a4078b5097c00000000e02000000031a02a4041b14600000000000a2e74c0000c250000bc6156845780007900000590800000000000000000000000000013849dd000000000001e50000000000093f8000b671de200029f64be8c520d2a5ea09ea88670f2e049a7144e10621928e6adbebf12e588e918b49a8294ab2b13be000000069c26fa00000009571ca0000205e60d806807786606dd8626be9aa9c6da1fb200000005e680000c680000000000000000000000000000000000000000000f40001ea400005da00009f4000000068000003bf19a0c031c18000143633200008358000b0996600000000000000000000000000000000000025600000ec0000000227400023ac462a3320000ec800000009f500000000000000082600000000001622096000000000000002d56000000097c800016000000000000abb800008385ac00000001c9800000000000000000110000009025fcbd3858e7ea9f660000000000000000000000000000c380000c31000000000004550152bd5800097e31da0000000000000000000000000000a6f823cc5680009032f38000000000000000000000000000000000007ab80001ca00005648dce0a6a9840000a5400000002dc9a740001eec00000003f90000990800000021e4000000099d0f9a000000000000000000a14995000051b000087b800000000000000000000260e75280000001c0c463263631300000000000000120214d80006c519a46d700009ee95180000000000000000000009d400002ddacee29695fc0000000277b14c7749dd40950000000000000000000000000000000000000000001f68000000000031b85ca00004b680007770000000000000000000000000000000000000000002926000000000023a6000316037a80000000000bf800000000ce400000000892c8ca1281b60e080004049ab4be80000000000000012e400014a2000253400022100000000456000000031bc0000000000000000000000000000000000000000000000000898a8e4000000071a800000000000000000000000076f1c90000278aa2723b45638246a4f80000000000000000029100000000f720d31256000000047a2d2870a
  | 59 => 0xb6c96b015026760002d20000000000000000000ccc0000000000064e2faa6621a080007428f9c5de00007dc0fbcbc014b60f1224675c80000000d485f1942a000000000000000000000000000000000000000ae89459088c2b0000b390c960000a1e802100a679800050d000000000000000000000267c00000007212dd0524894a0000dd20000b4e00000005da24ea772000000000005b931be0000000000000000000000000000000000064b8000000000000000000002cfe00000000002060000040e6f330d20002bb20002f460000000298000062c991619200000000000000047a0001ed600000000000000000000000000000001e2a00000000000000a819f109a1a5740000000000000000010285d230be9b7148800017745d4005050fb1223a280001f3800000000003ef83c21ef1da000003540b480000000000940800000000000000000aba0000000153610f845a186187a000040400028b600000000001be620922ceab59c1e2e4a9588ab18443b981fa0002ca6a54a3580000000000106849100009bb0000000000000000000000bec0002afa00000000000000000000008b8000000000058e80006ed1f88000000000000002de8000a6180003db8000853ac6a0000000000000000000009f10000047313e000232200000003888ae23d200000002730000000000000000000000000000000000000000000c35257a00020e20001b8e0000000b54a28e000000000024ec00000000000000c2a00000001fdc000000000000000002da200001c60001e3001c000000000000000000000000054788ec0001a68634800066a2f8e601059233893604baaa6c01515ba00000009089626000000000000000002374373000000000008b4000000003120000000000000000000005d3000082a80000000168000000000000009eda0982d82da60000000000000000006366d88000000000000012485f68000ac514f042b0daa3ad0b521e1000063780000c60000a93800000000000000000000000088e155630d000000000f20001ebc19e800000007ea0002dc2c1a16103690000000090e0f594c60000c84000000065722904e92bdc000098c00000000000000000000000000000000000000000073b00007128b5a5fd000000000003d80c6a40f0f7800029a80000000000000000000005168000000000000000005ad000000029e462500000000000bc4a124000149a0000000000263095f00000000d6000000bc0000000000000000000000001bf4000000000001ca0001392000000000000000b0800000007ca00000000000000143000000000000000000717000000000004409ce00000000000000000000000001ec000000006200000000000027991d80001b4882ba658000000000026900000000000000000000000000000257000
  | 60 => 0x17b600000009c1269284b155a2e71a9878200008ce000000017e800000f60000d240000000134800000000006d813d4a0a800033e000000013b4a71000075a8006475800000029540002a4400000008281df0000000010b8000000000000018be0000000000000000000001e3b0b65bc00005d6273c00000000000000000030260808380738000411152c0000d2c0002ae699100009fca38800007b60001f9400000000000000000000000014e88d58000b5e0000bab000000003887cc106400010d60000000000266a06e000000007785b5971c00000000000000000256a00000004800a760000000000039865fa0240002ec0bbb22b893788200002560000000000000000002c4000004720000000923019c00000000000000000000000000000000a7ac070000000000000022564a580000000000000234200000006a500006e0837c00000000000000c2000000000b180002894bc680000002b8a000120a1f51bc40000000000000000000005b080000000000423b0760000bc200013380000000000000051296d000001a46b38000a73922c7420000000000000000340632506000000005580860cf157a000000000000000000000000028c00000007d380000002fca7990140000137600000000000ec449794f80000000c752c10000051a31c80000000bca87400007400000919800000000000000000000285c3f88000493000049a0b3a0000000a240ade5ac80003d01bb800001460000000a0b0000989ad5e0000000a03a2e80000a16928000000026d6af18000348981693d80000000000b6180001ae80000000000000003c000000000000000000000b9a88423dc00000000000000000000000001f8800000000000000000000000000012dc908190608dae8c6db800064900008c9989a8562ada169a2f668fa1fec44961424787e80001ba616f8000000000000000007b4ab3c19300005189612000000000003e08418000ad68000000000000019921c12e10203800000000000000346624000086a00000002fbc69d80004bc8000718000000000000000000000087400000000000000000000069200004a8999600000000000000000000022b000000000004969af656f97f8a70800051700005aa9b1a0002b8c06680000000000000000066980004d900000001f42620a8b05ca80000000a4256c8000000000058900000002188000000070da26c960882c13f92ec458800000000000000000000000057d8000000237a5ae2ad000029feb380a502f00c0c00024d000000000002a020000000000077a00000000000000c30800000029d800000000000000067a5c6000000056594c8c0f259c34180000002f42b72884e00000000001f1200000000002a0eb310ef00002100456a1dac6b0e16931aff64018b5e0002786124934000
  | 61 => 0x4c8000a63a5807db0c549321a7a2f80d32a0faf661171270000000000000000000000000000000027289998000000000000001961fbb1d882e870600009d0abc1b6400023660000e065b22c3a28683669ac000000000006030000b4d8000646800000000006fb10f800025ac6dd1184c2c80000001c6c0000000226800000000000002e9ea9417fa000000030924aa9472b521680232000000000000000002c8a41f800000026e8a1d956c1ac80003fd2fb694c0000b5f8c7e000039e0f000000000000000000000000009f7a79800012fe1e81e0600000005d92f2e0001e7435403ba42d0108038a0e803c2ddc0002ca05870cd68e080000000000000000000000000000000000198600000000000000000000000000000000000259800070994a812f000032080000c7964020100008d300000000038000200c0000e120000000000061400000000000d54be71a7e84e80008b002181ea80000288000000000000000000002e7eb1880008720000000191e000000020d0000000000000a033a0000000000000055d90961af8000000000000000009a22c9027caa84000264a9108000ad50c780000000000204200aa010000000000000000001e9a0000d3000029406d580000001a2c00000008c700001c88430000000000000000000c764f4a95c150a4f8019000000012380000000000000000000000002de23ed00000001eba11d80000002e0ea620ace00000000000000000000000008aa6c98000a5900009350c462169fe000026b600000001059952751a87454480000000000000222e3378cb000014d478b800000001507179ba802b8666000097a00000001dc000000000000000000ad6178800010805630462901a12057095424c200007aaa24c0002190c0dacdab519e822e980000000000000000032c8000941000087584c84af8000000028a00031cc829b096000038caf88a4ab592f287cc901a471a4d80000910834000037502da000000031f0000adc94ca5af0000000109e000000027a000060719d8000201a000000088000003f600000000d4e0000cf00000000000800000000000001bb6000143a00007a28778000a13800000000b023d000000000000000322000000000021cc000109c0000000000266c2788b1a000000074700000000046000000000000000cb0000000000000000005e88212000000000027c677f24a40000b64b03000000000000000000000000000000004458000a8a8000000000000027246638000000000023200005ff09a4000169c00030da000000000000000000b1e00000007bc8000000000012904ae4f30000779af14000174e000000000000009c2000000013d87a400000c4000000026ee000000067780000002c660000000000000000028081381b983440000517817a0001a84000000000000
  | 62 => 0xc72000016c00000001428000000000006bc0001ffa4ff800086fa38e00024b69559a08968112200000007b184700000d0ab900000000000000019ac000000062da9f200000008fb8000000267a000000000029ca000249a6be8a6a3e500000bfa51400000000000000000000000000008c00000000000000000009a68000000000005a80000001f460cc80000000000000000000000000001bae03200000bb80000002d44000227c000224214b222a00000005ea000079a00003878000312293c1f600000000dd886a8c8e4330e106f2800000000000000000b4980004690000000235eae2000000000000001b8c0000000bfb93621a41eb82140000000000000000009728fd2a59a99e0002a140000afc0000000c58800070d0000c50172058e08ea6662e503d9800000015ea9e2294491b2f8cb64276e3771d2000000002228000000000000020dcae1a6da00000000000000000000000000000001e96c2f000000021a68a214460002b501901fd69f4af5800000000000000000189c00000000002e7c00002a04da87c40ce27d08d401447c9800000000000000000481a6c4000000075724980000000000000091e800000009a2000000000016f47f78000000000000000000000000000000000000000001d4492414c0000030000028ac000273e4c4072e0000af693300008b886000000000a149b2e000052e48e800080b000025f80002a700008d4a5380002b225eea7e20000000a08000028700003ada75c8cfac5c0000000000000000024f200000000000000000000000000000ca28dc5622ce6130800000028580001ad2bbc000052297541548000c2411f0122107051d18726388000c5a00005bd97b8a22a218000000018f0000708000000000008bb8756000000014c02d06bc98320000000000000044f23d8ba804de6eea1fc686a3c83b688d04ea022ab9da4be000084a00000000ee08ba75b00009099bf29b1977c00025de02280000000cd84ec8000000000024c112631ba1e0000000011e00000000a920000dd61c4000058cab907b880009be00000000000000000000000005a68000836000000003487320000000000072980001c080003b000000000000b98273439e1ede00013fc4bc0df02258000607b1d0bd71aba97d8cdc0ac8000000000000000000000000000000000000000000bb4c1705ce000169827e8c1c47d80000001e468b1b16c6c02640625ac9c00000000000000502000000013e4860000090e13bc0002ee80000000000000000000000000000000057e1c605ca79200007ed83dc000129e0000000000000023011600000000000026200017ec74f2482000000070f8000000000000000008d6983e00017eab1124b4b9c287e000000000000004d49c0e5f80c0618592ceabd91a22
  | 63 => 0x85c800000009141d88b580000000a518000000000000000000000000b8698087ac89b69e99ccc8670aac8f12d1c000000000018604d60000670800059780001c3000000000000000000000243e81980000110000972000029780000000000c3d0000bb594700002936ac3a2b63e58000000000000000001a9276253080000910000b9080000000000327800000000006178000b05800078980001ed1c4053c800000023760002a66000000000000001cc80000002026000000000000000002ec80001b2200017600000000000089c59a05600000b2800020f272880d80001a2200000004fa045098a95e8000000000000000000000000171e00000000000000000000097e80000000000000000000000569b9800052c00000002af2000259a000000000031322481f54bbea6844ab80003aa800000000000000d90155193c00008900000fb0000138855400000002c9e00000000d086f80432dae000000000002de7840000470800000000009b78bf867198500000000000000000004eea2793b8b60965000022fc0001480000000076d2baa00000004fa800053f1a80000000000027a01009f98000017e7a29ec29eb841c00022269cb800000020ea4c59f7a0000000000000075c01d23e7800080f800000023c000016be0000368925ab0243d1fce2df8000000068c4cc894400011b211b000045105ba0a1af5a91780000002bc40002efe42c0514432a0623140220000149600000003ca0000000186a0000b22000049600019ca3e9800000000000000000000000000000000001d5600013f600024d60000e2e00000000000000000117e605000084694b8915a8c4b4d00000002d50b588000000267806b051e0a12dc68a580003f7000000000000000000000000000000005dc234e828a8d696c0000c080000c550000000000000000000002eaa7cb8000000000066f1ec800024480308000000004c3a58ebe9c5acce0002e920000000000179e6cf25bc7c30380a40a81ea29190a19904a27d6a182c4380000000000888800068100000000000b340a900001e1c3d50fc20000000000000000005f200000007a499661bf2b40be0000000000000000f020001292ae6915cb47af6852b000091a8f6c0000000b4e9ada81224603448000000000018d000000007660000000b89800000023bc000000000000000000000418032e00000006739fb41d90000134000035e1f368a62f3e80e80000000a866ac800000009a00000000000000036680000002a720002d4000000000000000000000072e0000a74202000000000001df2000000000007e66a20000000088e000227800011e60000000bcaa4720002b9e00000005b68000655244600000002700b7428e0000000000000027a8000000000000000000000000147a7f4000000013c800000006210
  | 64 => 0x27f60001cb27e280000000000000000000030a6b5c80002a78000b8786040001f060000000000000000000005a50000000000044a1af40000000a4c00000000000000159a42aadb42b6102cae8b11a00000000000d5646d0000000000013911f2526203645d8d9600000000001d6200000000000000ab280000000ac20000000000000059b110a645000077e84b4000000000000000a080000000000a9800000002ca80000ef41880000962800092b883265e000083925d200000000000000000000072a8000000000040ea3a896f80000000000c098000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9f74dcd6244001938e9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880032b1d372589100066639ee4b122000cd473dc562440018f0ebb82c4880030f9d365189100061f3a0ca3122000c3f655d06244001878caba0c4880023be1d621891000556422c43122000acc8358862440171d904ba0c48802f2b209741891000656ba684312200087f855da42440070f90abb4848801a3e219709091001c3f42eeca12200087d85dd942440010ff0abb2848800e1f21576509100045fc22eca1220008df835d942440211b906bb284880023be09765091005c5e43ac8a122000a9c83591424401755904b2284880063da1b71509100063a32ee2a122000975851c542440018e8ca38a84880032d59071509100043fc2aed992200387c855db324400d1f10cb8664880031e19570cc9100043fc2aed192200387c855da324400187ce9b2c64880030fd95748c9100061e32ae91922000c9e74d8e324400193ce831c648801a3e219708c9100063c32ae1192200387e85dd932440010fb0bbb264880021fe15764c91001c3e42aec99220008bf845d9324400517908bb2648800237e0d764c91000477c12ec99220008f7815d932440070f90b3b064880021fe15760c91001c3e42aec19220008bf845d8324400517908bb064880423720d760c91005c76412ec192200087c865d432440010ff0fb2864880021f61f650c91000c7a432e2192200bce4625c4324400d1f10cb8064880062fe1d64905100054e41ac920a2000aac825924144001878e9b2a62880030fd97744c5100061e32ee898a2000c9c74d8d3144001938e831a62880031bd97724c5100063632ee498a2000c6f651c931440018d8ca392628800333d8c724c51000666318e498a2000c7865dc131440938f4e1b2862880030f1d365485100061fb2ee890a2000c3c65dd121440018becbb9a42880031719773485100062fb28e690a2000c5c651cd2144001958e9b124288003331cf6248510006563a0c490a2000ccc7318921440031f50db8242880031e19770485100b43e432ea10a200087f87d94214400b0fb0fb2842880030f9d3650851024e3d386ca10a2000c3f655d02144001878caba0428800317d9673085100062e32ce610a2000c5f655cc21440018b8cab9842880031e194764c1100063c3a8ec9822000c7b851d930440018f10a3b260880031e1db754c1100063c3b6ca9822000cb876dd13044001970ec3a260880034e1d4744c11000ced43c649822000cd8768c930440219b0ec1926088002d6614324c110005e8c08649822006cd876cc530440033b10e98a608801b361d9314c110005e4412629822006dd0714c530440018f0ca3b240880031e1db65481100347c432e69022049c7a76d971044093ce6c3b2e208800276e0d72c4110
  | 1 => 0xb0fb1865881ab33d8c724c71035666318e498e2049a7a80dd365440014f301ba6ca880030f5d074d95100051fc22e7b2a2000a3c845cf65440018bae639eca881269ea0073d95100053cc00e7b2a2000a3f845cb654400147908b96ca880028fa1072d95100051ec20e5b2a2000c6d721cb65440934f500396ca880029e60072d95100043f43883b2a200587d87107654400d1f301baec8880021fa1f65591100043f438cab222000c5f65dcd64440018b8cbb9ac88800317d9473591100062e328e6b222000c9c641cd64440018decbb92c8880031b197725911000637b28e4b222000c6c651c96444001958c8392c88800e1fa1f75591100046fc1aeab2220108dc835d564440011df04baac88802e3b20975591100043f438eab2220038bc8755164440018beebb9ac888003171d773591100062fba8e6b222000c5c751cd644400193ee839ac8880032795073591100064eaa0e6b222000c9f421cd64440019388239ac8880031bdd77259110006363aee4b222000ccf73dc96444001998e7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc725911005e57420e4b222000cae541c9644400195aa8392c8880032b10472591100043f43ecab1a2000c3c74d9563440010fd0e32ac6880030f1d06558d100061fb2ee8b1a2000c3c65dd163440018decbb92c6880031b1977258d1000637b28e4b1a2000c6c651c963440070fd0fbaac6880022fe117558d100145e422eab1a20008ef825d563440171d904baac6880023ee017558d100043f438eab1a20028be87dd1634400187eebba2c6880030f1d77458d100061fba8e8b1a2000c3c751d16344001938e9b9ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d1000672396e2b1a2000c7875dc163440011bf0eb18c688002a72116318d1000566412c631a20108dc835d063440010ff0abb4868800e1f2157690d1000c7a432e321a20068f8865c243440070fd0bbb286880021f6177650d100043fc2aeca1a200387c855d9434400117f08bb2868800237e0d7650d1000477c12eca1a200b8ec825d9434400117f08b9ec48800a2f21173d891001c3f436eab12200087e87d956244001878e9b2ac4880021fa1c65589100061e3a0cab122000c3f65dd16244001878cbba2c48800317d9773589100062e32ee6b122000c5f651cd62440018b8ca39ac48800e1fa1f75589100045fc22eab1220028bc845d562440011bf06baac4880423720d75589100047dc02eab12200087e871d5624400517d0fba2c4880030fdd774589100061e3aee8b122000c3f751d16244001878ea3a2c48800317dd773589100062e3aee6b122000
  | 2 => 0x173987200061e3a4cab0e4000c3c7459561c800187ccbba2c3900030f59774587200045fc22eab0e40028bc845d561c800517d0fba2c390002a7a0f64907200045fc22eca0e40008bf845d931c800517908bb263900023be09764c72000c76412ec98e4000c3c7459531c80178d8e4b2a63900030f997744c7200061eb2ee898e4000c9c7498d31c8017998e531a6390003271d1634c72005e66392c698e4000c6e65dc931c80018dacbb92639013b1e9c1650c7200063d32ae018e4000c79655c031c8001878e8b2a43900030f99774487200061eb2ee890e4000c5e65dcd21c80018bacbb9a43900031799473487200062eb28e690e40038bf8755364480011bf06baac8900423720d75591200047bc0aeab2240068f4815d564480011f700baac89002e3e60375d8d2001c3f43eeab1a40008bf845d5634800517908baac6900023de057558d200347a40aeab1a400087e871d5634800517d0fba2c6900030fdd77458d200061e3aee8b1a4000c3f751d16348001878ea3a2c6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4006cf2801c5634800d9e30038ac69000237e1d6318d200056a40ac631a40008bf845c4634800517908b88c6900021fe157690d2001c3e42aed21a400087f855d943480070f90abb286900022fe117650d200047bc0aeca1a40068f4815d943480031bf0eb1c6490002b5205638c9200046f438c699240008df8758c32480015a902b1864900023de1d61185200056a41ac230a40008bf845cc614800517908b98c29000327e1173185200064e422e630a4000ccf825cc614800199904b98c29001b3520573185200366d082e630a4006cd9105cc61480010ff0abb4829000e1f21576905200346f41ced98a4006ad48158f31480015ab0630e629000a2fa12764c5200045ec24ec98a400b8ec821d931480011bd0f31a629001a3721d634c5200356a40ac698a40018ee86dc931480012db0a39262900033398c724c52000666b18e498a40018f8809d831480010ff0abb0629000e1f215760c5200045fc22ec18a40028bc845d8314800d1e902bb062900023761f630c5200066db1ae018a4010cd8635c031480019e6c2b806290003351cf61485200066a398c290a40068bc8755164c400d17f0eb24878801b2d9c56490f100046fc1aeab1620108dc835d562c400517d09b9ac5880022f6137358b100064f426e6b162000c9d84dcd62c40019b421b9ac5881ab338847358b1035666108e6b1620008df835d942c40211b906bb285880063d2057650b100345e43ac8a162006cb47159142c40011bf06bb2658800237a1e634cb100346e43ac699620108dc835d832c40011b
  | 3 => 0x898a6058c9c76191314c001c38ca3226298003331db724c530004aec28e498a6000ccc761c9314c001b1ee83926298003631d0724c53000667430e498a6000ccd861c9314c001a9d0a392629800353614724c530006a7b28e498a6000d4c651c9314c001b1ec8392629800363190724c53035666308e498a6000ccf601c9314c001b9420392629800237a1f624c53000666396c498a6000dc472d85314c001caeca30a6298003a5d90614c530006e2390c298a6000dc872dc1314c0b58f4e1b28629810b2e9c3640c5300043fc2aed90a600387c855db214c00117f08bb6429800a2f21176c853000c6f436e790a600095d851cf214c0010ff0abb4429800e1f21576885300045fc22ed10a60028bc845da214c0031b90cb9c429800e1fa1776485300043ec2eec90a60028be84dd9214c00117b09bb2429800a2fa1276485300045ec24ec90a60028bc841d9214c0211b9063b242980030f1d365485300045f436e890a6000c3f65dd1214c001878cbba242980022fa1f64485300045e43ec890a60018de86dcd214c0018becbb9a42980031719773485300064fb26e690a6000c9c64dcd214c0018beca39a42980031719473485300064fb20e690a6000c9c641cd214c0070f90b3b0429800a2f21276085300346e41cec10a60018f8809d8214c0010ff0abb0429800e1f21576085300045fc22ec10a60028bc845d8214c0010f90cba842980030f19175085300043fc3eca10a600087d87d94214c00187ce9b28429816b1e9c365085300045e432e810a6000c3f655d0214c001878caba042980022fe1f64085300045ec3ec810a6000c3e75d90214c00187aebb20429810b2e9c364085300062fb2ce610a6000c5c659cc214c00193ec9398429800327192730853000c6e432e610a6000c5f655cc214c0018b8cab98429800327d9173085300064e322e610a6000ccd73d88214c00139b0e19042981abb118432085300066ab9ec210a6000c7b655c0214c0018f0cab8042980032ed9170085300065c322e010a6000ceb625c0214c0019e6c2b80429816b1e9db65cc1302d72db1ecb9826042cba76d93304c005974ec32660980038e19464cc130086e998ae39826000bc8824c7304c00187ee93a2cb900029ee0174597202753c402e8b2e4000a3e84dcd65c800147b09b9acb9000317dce73597202753d404e6b2e4000a79809cd65c800147f08b8acb900028f21171597200053dc02e2b2e404ea78805c565c800147d0838acb900028f61071597200043f43882b2e400087d8710565c800717f0eaa6c9900032795273d93200064eaa4e7b26400bc9f429cf64c801793a8539ec9900032710673d932005c6e41ae931e400b8de87d0d63c801759d05a1ac7900022fe117118f200145e422e231e400b8bf8759243c800117f08b9cc39000a2f21
  | 4 => 0x24c00187aebb24c4980030f9d464989300061eba8c93126084c9d73192624c0010fd0fb2ac4980030f1d365589300043f438cab126000c3c74195624c00187ecbba2c4980030f19774589300045f43ec8b126000c3f75d91624c001878ebb22c4980022fa1c64589300061fba8c8b126000c3c75191624c0018eecbb8ac4980031d19771589300065bb26e2b126000cb464dc5624c0018eeca38ac4980031d19471589300065bb20e2b126000cb4641c5624c0011df0eb10c498002b920562189300045fc22e231260028bc845c4624c0010ff0abb4849800e1f215769093001c3f42eeca12600087d85dd9424c0031bd0db9a84980031719773509300062e328e6a126000c9f641cd424c00187ce9b2c64981622f219748c9300061fb2ae91926000c3c655d2324c08517f0fb2464980022f61f648c9300063c32ae1192605ac5e76d96324c00193ced3a46498003669c2748c9300064f3b2e91926042c9e76d92324c0b193cec324649800387194648c93000727b2ec5192603287c865d4324c001878c8ba864980021fe1f650c93007c3ec3eca1926000c3e75d90324c00187aebb20649815657219750c930006adc02ea1926000d58805d4324c0218bec0ba8649804356d81750c930006ad082ea192600095f87d94324c001a3aebb20649820f279d8640c9300068eba8c81926000e1c65190324c00187ce9b2cc2980030f9d065985300061fb2ae930a6000c3c655d2614c00187cebb24c2980030f5d764985300061f3a8c930a6000c3d75192614c0070fd0dbaac2980021fa1f65585300061e3a6cab0a600087e87195614c001878e832ac2980030fd9774585300061e32ee8b0a60008be87d91614c00187eebb22c2980030f1d764585300045f438c8b0a6000c3f75191614c001878ea322c29820b27dcc645853000637b2ee4b0a6000c6c65dc9614c00195ec9b92c2980032b193725853000637b28e4b0a6000c6c651c9614c00195ec8392c2980032b19072585302de2eb98ca30a60008f787584614c0015c904b08c2980022fe1172185300145e422e430a60008dd878c8614c0011bb0e190c2980021fe15769053001c3e42aed20a6042cba70d92414c0018b8cb39c829800327d92739053000c6e432e720a6000c5c655ce414c0018f0cab84829800e1fa1776505300043ec2eeca0a6081c9e76193314c001c38ca32662980023761f62cc5300061e3a6ca98a60588be86dd1314c00187ecbba262980030f197744c5300045f43ec898a60428bc87d91314c0018decbb9262980031b197724c53000657b26e498a6000cac64dc9314c0018deca39262980031b194724c53000657b20e498a6000cac641c9314c0019c8e5b0a6298003391c8614c5300063c32ee098a605ac5c76d95314c001938edba26298003271d8744c5302164e3b6c
  | 5 => 0xe1f215760c5400347c432e018a8000cdb635c031500219b0c6b8062a00062f21974c85400043fc2aed10a800387c855da21500011bf06bb442a00423720d768854000c5f436e910a80108de839d921500011bb073b242a000a2f210764854000c5f436e890a80068bc849d821500031790cba042a00032b5d362085400347c432e010a8000ceb625c0215000717f0eaa6c9980063720d7558b3000c6e41aeca1660008f7815d942cc00d1e902bb2859802e2fa1f6450b3005d57416c8a166000c9d769d232cc0031bf0eb14659815317581750cb300046ec3c6530e60008dd870ca61cc00117f08baac39800a2f21175587300145f43ee8b0e60008bf845d941cc0011bf0eb16639800327dd8744c730004aec28e498e6000ccf761c931cc001b1ee83926398003631d0724c73000666c30e498e6000d4e851c931cc001a9b0a39263981ab33984724c730006e5400e498e6000dc9801c931cc0011b90eb126398003331c9624c73000c6e41aed90e60008bf845da21cc00517908bb443980022fe1176487300145e422ec90e60008df835d921cc0031b906bb2439801a3760d76087300061eba0e9b2a605aa7a801d3654c0014f3003a6ca9815697a0f72d95302d52ec1ee5b2a605aa7a80dcb654c0014f301b96ca980028fe1172d95300051e422e5b2a6000c6d721cb654c00147d0938eca980028f61271d953029d2f418e3b2a605aa5d831c7654c0b54f50038eca980029e60071d95300043f43883b2a600087d87107654c00187aebaa6c898002a760f54d913001c5fc3aa9b226087e1d83197644c001c38cb29ec89810aa721953d91300061eba8ebb226000a9e831d7644c08553b063aec898002aba0875d913000556c10ebb2260428be87d4f644c00117b0fa9ec89800387d4e53d91302154ec1ee5b2260008be87d4b644c00117b0fa96c8980038bd4a52d91300051f42ce3b226000a3d859c7644c08553b0638ec898002ae60071d91300045f438a3b2260008bd87147644c001878c9baac8980021fa1f65591300043f438cab22608bc5f73195644c0070fd0fbaac8980022fe1175591300046fc1aeab2260008fb805d5644c0010fd0e3aac8980030fdd774591300061e3aee8b226000c5c75dcd644c0018f0ebb82c89822b0f9db65191300045ec3cca3226085a3e85994644c00117f0eb28c898226a7e0d65191300055dc02ca3226088a3e86194644c10f87cec328c89821b8760c65191304370f180ca3226086e1c30194644c10dc7060328c89821b8e840651913042d4f434a63226000e1c6594c644c0b15390ca98c8980038719553191302165c386c8a1a6000c7865dc1434c0b78bae632ec4980063760f75d89300847cc06ebb126000c3e74d96624c00187ce832cc4980030fd9574989300061e32ae93126000c3e75d926
  | 6 => 0x846e43cc69084200c9f7498d2108401938e931a421080237a1d63484210046e43ac69084200c9f7458d2108401938e8b1a42108032be13764842100656426ec9084200ccf83dd9210840199907bb2421081b39947764842100672a8eec9084200caf76dd1210840195eec3a2421080333ddb734842100476c34e6908426a9ce839cd210840199eec39a421080363dd07348421006c63a0e6908426a9cf861cd21084d539b0c39a42109ab539947348421356a6b28e6908426ad8e641cd21084d5b1ac839a42109ab339847348421356e3288e69084200dc5511cd21084d5b94c039a42109ab725807348421006e3080e6908426adc4101cd210840196f09bb242108032d21376484210066bc1eec9084200cd483dd921084179cca5bb242108033954b76484210065bbb6e89084200cb7761d121084019aeedb9a421080335dd87348421006ca3a0e6908426adc7721cd21084175d104b1cc01082fb2209639802100764b1e6530042068fa87d41600840d1f10ea82c0108029ea1740580210053cc2e80b00420be6832595600840dcd642b2ac01081b9c88565580210373490acab00420be71215956008417d5064b22c01081baac8564580210375490ac8b00420bec88258d600840dda442b1ac01082fb4485635802100734b2e64b004200ea964cc96008401d92c7992c010802aea1075580210055cc20eab004200ada831d560084015b3063aac01082ebaa0875580210a574c10eab004206af2811d560084295e3023aac0108029ea1674580210053cc2ce8b00420bae8825d160084175d505aa2c010802ba60b54580210071daa4a8b004200a7b855cd60084014f10ab9ac010802aee1173580210055c422e6b00420bae8825cd600840d5e102b9ac010802aea1353580210055cc26a6b00420baea82d4d60084015d305a9ac01081abca07535802100578c0ea6b004200e5b5394d60084175d505a1ac010802ba60b43580210055d426a4b004200ab984d496008417cd4a5a92c010802aee1131580210055c42262b004200aeb824c560084175d10498ac010802aee1121580210055c42242b004200adb8348560084015b10690ac010803175d753d8d400054ec26a7b1a80008df8758c63500014b90ab18c6a0232a7e116318d400846e41aea31a8000a9d84d4c63500011df04b88c6a002e3b2097118d400065a20ae231a80008ef8758862500011bf06b88c4a00423720d71189400049ec28e2a12800087f855db32500070f90abb664a002e2f212768c94000c5e432e919280018bc865d032500171f10cb8064a00062f61375d85400147cc06ebb0a80008bf8750b61500011ef0eb08c2a00022f61c62905400245ec3ec320a80018bc865d331500171dd053b262a00023b60a764c5400145e420ec98a80018be86dd131500010ff0abb062a
  | 7 => 0xce82d4d630840d5ad03a9ac61080f179d65358c210346e43aa6b1842068de87d0d630841759d05a1ac61082f931ca6558c2105f26392cab184206e4f21595630840dc9a42b2ac61082fa31ca6458c2105f46392c8b184206e8f21591630840dd2c42b22c61081ba34856458c2105f4a90ac8b184200c5f759d5630840153d093aac610802a76127558c2105d67414eab184200acd829d5630840d5ad033aac610802b56067558c2100567c12eab18420bacc825d5630841759d053a2c610802b360a7458c2105d66412e8b184206ad4815d1630841759d05aa2c610802b360b5458c210070faa4a8b18420be4e851c96308417c9b0a392c6109ab339c47258c2135666388e4b184200a9e84d49630840153b09a92c61082f9394b5258c2100666396e0b18420bace829c1630840159b05382c61080297e157058c210052e42ae0b184200a9f845c1630840153908b82c61082eb32097058c210356a40ae0b1842008de8714163084011bb0e282c610802a7a105058c210054ec20a0b18420bace82141630840159b04282c61081ab5a045058c210056ac08a0b184200a5e85d0163084014bb0ba02c61081ab5a064058c210056ac0c80b1842008dd87881630840153d09082c610802a76121058c210345fc3ac9218420b8ec825d9430840d1e902bb2861081a2f21d6450c210346e43ac6a184200cad64dc9430840199ac7b9286108032d5937150c210066ab1ee2a184200c6d76597320840195aecb266410803335da63cc8210072732ac79904200e4d6558f3208401d1cc8b1e6410803a359163cc82105f26192ca990420be8c32591320841759904b1a641082f1ba15760c82105e36c2aec190420bcce835d832084d599c62bb064109ab330c5760c82100477c3ac61904200cce7358c32084011df0cb8864109ab710c5710c8210371a20acaa084206ab481591410840dd2882b1a8210803335db32cc4210145e426ec9884200c3c7459531084178d8e4b2a621089a2f61b744c4210061f32ee89884200c3d65dd13108401974c1ba262108022fa1d644c4210ac5e43ac8988420bcac72591310840193ee931a6210803271d2634c42105e66394c69884200c9f7458d3108401938e8b1a621082f331c9634c4210063732ee49884200c6d65dc9310840195cc9b9262108032b593724c4210066731ee49884200ccd63dc931084019d4c1b9262109aa73a1f324c42100667bb66498842028bc84dd92108401878e8b2a421086a2f61b74484210061f32ee89084200c3d65dd12108401974c1ba242108022fa1d64484210ac5e43ac89084200c5e65dcd21084018bacbb9a42108032799373484210064eb26e69084200cda60dcd21084018bcca39a42108031759473484210064f320e69084200c9d641cd21084019b4c039a421080237a1e63484210
  | 8 => 0xc639262908032e9c3640c5210066d386c618a4200cbb645c03148401970c8b80629080336d8d700c5210866c31ae018a4200e946418f2148401d1ec831c4290803a319063885210d45e436e8b0242008be87d91604840187eebb22c0908030f1d764581210045f438c8b024200c3f751916048401878ea322c09080327d9373581210064e326e6b024200c9f641cd6048401938c839ac09080237a1f63581210062fbaec6b024200c5c75d8d604840193ee9b1ac090803271d363581210046f438c6b024200c5f7518d60484018b8ea31ac09080327dd063581210064e3a0c6b024200c3f749d1650851b4ef02ba2ca1081a9d20574594210051f426e6b284200a3d84dcd65084018bee739aca109b29be09735942105d36412e6b284200a3e841c1650840147b08382ca1080297a0c70594210052ec18e0b28420ba6e821c1650842d4db04382ca1081a9da0470594210b53ac08e0b28420087e87d0165084010fb0fa02ca1081a9da0640594210053ac0c80b28420ba6e828c165084014db05182ca1080297a0e20594210052ec1c40b284200a3e84841650840147b09082ca1081a3d20575590210345f43ea8b204200c3f75d51640841755d05aa2c81081a2f21d545902101c3f42ee0b20420087d85dc1640840187eeb3aac81082eaba0a755902100556c14eab204200ab7815d5640840d56902baac81082eab20973590210355a40ae6b2042008be87d4d640840117b0fa9ac81080387d4e53590210ac5f43ea4b2042008bd87d496408417c5ca5a92c8108028fa1770590210051ec2ee0b204206ab6819c1640840156b03382c81082eab20970590210045f438a0b2042008bd87141640840153d06282c810802a760c505902105d57410a0b204200aad82141640840d56d02282c810802ad604505902105d5741460b204200aad828c1640840153d07102c810802a760e20590210ac5f43c20b2042008bd87841640840d1b906bacc61081a3720d7498c210862fbaea73184200a9e84d4e630840153b09a9cc6108021fe157098c2101c3e42ae131842008bf845c2630840517908b84c61081a3720d7098c210862fbaceb3184200a9e849d6630840153b093acc61080387d525498c210054f426a53184200a9d84d4a6308417c9ca5a94c61080297e157098c210052e42ae13184200a9f845c2630840153908b84c61084237a1c5098c210046ec38a13184200a9e84142630840153b08284c61082eb3a085098c2100566c10a13184206ad68114263084015ab02284c61080297a174098c210052ec2e8131842108de87882630840153d09084c610802a76121098c2105e36394cab18420be4c325956308417958e5322c61082fa30c96458c2105c76412eab1842068de87d4d63084018beeba9ac610802a7a135358c210054ec26a6b18420ba
  | 9 => 0x10d8d210054ec2421b1a42008de870436348421938c6ba4c690803279d36398d210064eba6c731a42008be87d91634840117d0e322c6908022fe117558d210145e422eab1a42008df835d563484011df04baac6908023ee017558d2100c7c402eab1a4200c9f74dcd6348401938e9b9ac6908032bdd37258d21006563a6e4b1a4200cb474dc563484011bf0eb18c690802a7e116318d210054e422c631a42108dc835d463484211b906ba0c690802a7a135318d210054ec26a631a420087f855c063484070f90ab80c6908022fe117018d210145e422e031a42008dd87994634840153d09328c690802a76126518d210046fc3aca31a4200a9f84594634840153908b28c690802b6e016518d210056c402ca31a4200c9e76d9063484011bb0f320c69080237e1d6418d210064f3b0c831a4200a9e84980634840153b09300c69084317dd67518d210054f424ea31a4200a9d849d46348401c3ea92a0c690802a7a135218d210054ec26a431a4200ad681d4863484015ab03a90c69080393d4a5218d210054fc22e231a4200a9c845c4634840159d05a88c690802b360b5118d2100567c12a231a4200acc82544634840153d08288c690802a76105118d21005674168231a4200acd82d0463484014bd0a208c690802976144118d210054fc224231a4200a9c8448463484014bf0ab80c690802972157018d210054fc22e031a4200a9c845c063484211bd0e280c6908023761c5018d210054f420a031a4200a9d84140634840159d04280c690802b36085018d210056b408a031a4200ad58114063484014bd0ba00c690802976174018d21005674108031a4200acd8210063484011bb0f100c690802a7a102018d210054ec204031a4200a9e84840634840153b09080c690802b3a0a1018d2100566c142031a42108de8704063484211b906bb4869080237e0d7650d2100477c12eca1a42008f7815d9434842117d0fb22869080a37a1f6350d210066a31ee2a124200cb7641c542484019a8c638a84908433518e71cc9210145e424ed19242398bc865d2324840117f0fb24649086a2f61f648c9210064f3a6c71924200c9d74d8e324840193ce831c6490803275d0638c9210065a326e29924200cb4641c532484019aec638a64908030f191750c9210862e31aea1924200c3e75d90324840187aebb206490803179d7630c9210062ebaec61924200ccc63dc9414840195ec839282908033318c72505210866631ce598a4210ccc635cb314840117f08bb2629080a2f211764c5210145e420ec98a42008be86dd1314840117d0fb2262908022f21f644c5210064fba6c698a4200c9c74d8d314840193ee831a6290803271d0634c52100657b26e498a4200cac64dc93148401998c7b9262908032bd90724c52100656320e498a4200ccf631c93148401998
  | 10 => 0x18e420087f855c364884070f90ab86c91081a2f21d54592210045fc22eab1c42028bc845d563884011f700baac7108063e2017558e210145f43ee8b1c4200caf74dc96388401958e9b92c7108021fe157018e2101c3e42ae031c4200c7b855c063884018f10ab80c710843360c97018e210366d98ae031c4206cd9315c0638840117f08bb2871081b2d1c56450a21354e7c3ac79944200ad98018e32884011bd0f31a65108023761f630ca21355e240a641944200c6d765d432884d578d0339865108023b61f630ca2135666318e498c426a9ce87cc931884070fd0fbaac1108021fa1c75582210061ebaea9b2242038bf8755364484010ff0ab86c89080e1f21570d91210054f41ccbb224200a9d83997644840153f06b2ec890802a720d65d91210055dc02cbb224200ab880597644840153d07306c890802a760e60d91210061eba8ebb2242008be87d4f644840117b0fa9ec89080387d4e53d91210045f43ea5b2242008bd87d4b6448401c5ea5296c8908038dd4651d91210045f438a3b22421a8bd87147644840147f0ab86c8908028f21570d91210045f438a1b2242008bd87143644840153d06286c890802a760c50d912100557410a1b224200aad82143644840156d02286c890802ad60450d91210054f41c41b224200a9d83883644840117d0e106c89086a2f61c20d91210045ec3c21b224200a9e83043644840153b06086c8908032719373591210064e320e6b2242008bf845d564484011bf06baac8908423720d75591210047bc0aeab2242008fb805d564484031f100baac89080327dd373591210064fba0e6b224200ccc73dc964484019a8e7b8ac8908022f61e65191210054f41cca3224200a9d83994644840155b05328c8908022fe1d65191210054fc1aca3224200a9c83594644840156f02b28c890802aee0165191210055c402ca3224200a9e83980644840153b07300c890802ad60660191210062ebaea7b1a4200a9e84d4f634840153b09a9ec69080e37e1d53d8d210054f424cbb1a4200a9d84997634840153f08b2ec690802a721165d8d210056dc02cbb1a4200ad880597634840153d09306c690802a761260d8d210062eba8ebb1a4200a9e841d7634840153b083aec69080387d5254d8d210054f426a5b1a4200a9d84d4b6348401c9ea5296c690802a7a1371d8d210054ec26e3b1a4200e5751947634840153d0828ec690802a761051d8d210052f42883b1a4200a5d8510763484014bd0bb86c6908029761770d8d210054f426e1b1a4200a9d84dc363484011bd0e286c6908023761c50d8d210054f420a1b1a4200a9d84143634840159d04286c690802b360850d8d210056b408a1b1a4200ad58114363484014bd0ba06c6908029761740d8d210046ec3c41b1a4200a9e84083634840153b08106c690802a7a12
  | 11 => 0xc401b18e8392621880333618724c431006a7428e49886200d4d851c9310c4d5b8ca2392621880371544724c431356e5300e4988626adc9601c9310c401998e4b1262188433594f764c4310066aa9eec9886200cb776dd1310c40196eec3a2621880339ddb724c43100673bb0e49886200da4741c9310c4d5b8ee63926218842b620d62980310056cc3465300620387e87dd5600c4018f501baac0188031e60375580310043f438eab006200acc824c5600c40d1f50fa82c01881a3e21d50580310053d42e80b006200a7985d01600c4018f6edbaac0188031edd8755803108764194c4b006200ad9868c9600c401575083aac018802ae61075580310856d418eab006220ad9831d5600c4015d5043aac018802ba608755803103579408eab006220af1811d5600c4018f50e3aac0188038ea1075580310071cc20eab006200e5a831d5600c401cb3063aac0188039aa08755803100734c10eab006200e72811d5600c401ce3023aac0188029ea1674580310053cc2ce8b006200a7b855d1600c4014f10aba2c018842b620d74580310856d41ea8b006200ad983d51600c401c76a92a2c018802aea1353580310055cc26a6b006210e5a53d4d600c4215b507b92c018882b660f72580310053d42ce4b006200a79859c9600c4014f70ab92c0188029e21572580310055dc22e4b006200ab8845c9600c4215b106b92c01881abc20572580310055d420e4b006200ab9841c9600c40157509a92c018802ae61352580310856d41ea4b006200ad983d49600c40d5e503a92c018802bc607525803100735a94a4b006200adb83549600c4215b106a92c018842b6a0f42580310056cc1e84b006200adb83509600c4215b106a12c018802bce0542580310357840a84b006200aba848c9600c40157309192c01880396dd632580310072c3ac64b006200e9a848c9600c401d3309192c018802b660632580310872d42864b006210e59850c9600c401cb6ea192c018803961d432580310876541064b006210ed2810c9600c4015b302192c018843b460432580313576510864b00626aec8210c9600c401cb6eb98ac018803961d731580310056d41662b006200abb844c5600c4015710898ac018802bae0931580310057441262b006200e5b754c5600c401cb0ea98ac018803a6e1131580310074c42262b006200ecb824c5600c4015b10498ac018803b220931580310056441262b006210ed3814c5600c40dda4a298ac018803b4545315803101c5fc3aa9b2642008df835d564c84211b906baac9908023ee01755932100c7c402eab26420387e85dc164c84010fb0bb82c9908021fe157098f2101c3e42ae131e4210c5f305d463c841717f0eb24879080237a1e634c72105e66394c698e420bccc7258d31c84011bb0fb18639080336d8d700c7210866c31ae0
  | 12 => 0x80393d4e531893100573c0a863126200ae48150c624c40155f08b88c498802ab21171189310056741ea23126200acd83d44624c40159f06a88c498802b320d511893100557420a23126200aad84144624c40159d07a08c498802b360f411893100537428823126200a6d85104624c40155f08988c498802ab21131189310056741ce03126200acd839c0624c4018daeab80c498802b3a0e501893100566c1ca0312620b8ee87140624c4011db0e280c498802aba10501893100556c20a03126200ace83140624c40159b06280c498802b9a04501893100572c08a03126200a6e85d00624c4014db0ba00c498802b3a0e401893100566c1c803126200ae681900624c4015cb03200c498802b3a0c401893100566c18803126200aae84840624c40155b09080c498802b3a0e101893100566c1c203126200ace83040624c4171d904bb4849880327d92739093105e66314e7212620bccc625ce424c4051dd0fb1284989ab33e0a76cc9310064f3b6c99926200c9e76193324c40199cedb166498803a3d9062cc93100746320c5992620be4e8518b324c417c9b0a31664989ab339c462cc93100666312e199262008bc865d2324c417958c4ba464988022f61f648c931006573a6c51926200cad74d8a324c4179c8c538c64988032d193714c9310065a320e29926200ce7621c5324c40159d0db926498803a3d90624c93100746320c49926200ace87189324c41799d0e312649882f93a14624c93105f26c28c49926200dc7721c5324c401998c5b8264988030f191750c93105e36312ea1926200c3e75d90324c40187aebb2064988031b9d7620c93100636baec41926200c9f641cd414c40199ee63128298803331cc625053100752208c4a0a6200ea46418b314c4011bb0e3146298803335c8628c53100747b20c518a6200e8c6418a314c40199b0e314629880393a14628c53100726c28c518a6200ccc625c2314c44d1790dba2c0988022fa1f64581310061fbaec8b026200c3c75d91604c40117d0e322c0988030fdd464581310061e3a8c8b026200caf64dc9604c401958c9b92c0988032bd90725813100656320e4b0262008ee87d89604c4018deebb12c0988031b1d7625813100657ba6c4b026200cac74d89604c4011dd0e312c0988031bdd46258131006363a8c4b026200caf74189604c401958e8312c0988021fe1570d903101c3e42ae1b206200c7b855c3640c4018f10ab86c81881a2f21d54590310347643aa4b106206cb471591420c40d1d90eb1284188032e981748c8310064ebb4e91906200c9d765d2320c4011bf0eb166218803339c962cc4310065d306e89886200cea60dc9310c4019d4c0392621881b35947764c4310066aa8eec9886200c9f76dd1310c40193eec3a2621880333ddb724c43100667bb0e49886200d8f741c931
  | 13 => 0x54f418a1b226200a9d83143644c40155d04286c898802ab60850d91310055b408a1b226200ab581143644c40153d07106c898802a760e20d91310045f43841b2262008bd87083644c40117b0f086c898802a7a0c10d913100656326e4b226200cac641c9644c40117f08baac8988023be09755913105c76412eab2262008fb805d5644c4031f100baac8988032bdd3725913100657ba0e4b226200ccf731c9644c4019c8e5b8ac8988022f61e65191310054ec1cca3226200aae82994644c40155b05328c8988022fe1d651913100557c12ca3226200aac82594644c40157700b28c898802ae201651913100557414c03226200aad82980644c40196ec838a86988031b5d752d893100557426a5b126200aad84d4b624c4071df0ea96c4988021fe1570d893101c3e42ae1b126200aae84083624c40155b08106c498802aba1265d893100556c24cbb126200aaf84597624c40155908b2ec498802bae0165d893100574402cbb126200aae84983624c40155b09306c4988031b5d475d893100557420ebb126200aad841d7624c401c5ea92a6c498802aba1353d893100556c26a7b126200e4f5394f624c40155d09b8ec498802ab61371d893100733a8ca3b126200aae84147624c40155b0828ec4988029ba1441d893100536c2883b126200aae849c3624c40155b09386c4988029be1570d89310053642ae1b126200ace831c3624c40159b06386c4988023ba1c50d893100476c38a1b126200aae84143624c40155b08286c498802b3a0c50d893100566c18a1b126200ae681143624c4015cb02286c4988029ba1740d893100536c2e81b126200aae84843624c40155b09086c498802b3a0c10d893105e56312e93126200cae74d8a624c40195ae9b14c4988022fa1f64589310045f438c8b126200c3e75d90624c40187aebb20c4988030f9d464189310061eba8c831262008ef87588624c40155f08b10c498802ab211621893105e36412ea312620bc6f205d4624c4018daeba90c498802aba13521893100556c26a43126203c6e75548624c40159b07100c4988031b9da7518931006373b2ea31262008ed87994624c40155d09328c498802ab612651893100477c3aca3126200aaf84594624c40155908b28c498802bae01651893100574402ca3126200cae76d90624c401c5cebb20c4988038b5d7641893100476c3cc831262008ef87590624c40195cec320c4988038b9d4641893100716ba8c83126200e8f645cc624c401d18c8b98c498802aba12601893100556c24c0312620bc6f759d4624c40155d093a8c498802ab612751893100717424ea3126200e2d849d4624c4018df0eba8c49882f1bdc1751893100717aa4a83126200acf83550624c40159906aa0c498802aba13531893100556c26a63126200ae681d4c624c4015cb03a98c498
  | 14 => 0xd83841650c8174dd05082ca190029b60a10594320852f41820b286400a5d83041650c80717f0eaa6c8190423720d75590320047dc02eab2064018f8805d5640c8070fd0bb82c8190021f617705903205e67296ec9906400ccd52dd9320c8013b30038a64190433394f764c83200666a9eec990640087f855c2610c8070f90ab84c2190030f1d265584320862e39ccab08640bc6c72995610c801878e8b2ac219043950c5655843205f3210acab086400c3e65dd1610c80187acbba2c2190022fe1175584320145e422eab0864008fb805d5610c8031f100baac219002b5a07325843205f6210e64b086400ad4814c9610c821cb660b2ac019002a76135398e410062fbaea6b1c8200a9d84d4d639045317f0eb1c87208022f61a7290e4115c5fc32e321c8242cba605c2439043b17f0eb14852087e2fe197190a4105d66412c699482029b4845c432904070fd0fbaac1208031ea0375582410063cc06eab04820087e871d560904071bf0ea9ec6a080237e1d6318d4100566412c631a820087f855c063504070f90ab80c6a080e3be1d52d89410043fc2ae1b12820387c855c3625040159d07106c4a0802ab61020d894100477c3ac43128200acc83588625040159d07100c4a08766da1871509410365b430e2a128206d36851c5425040da6b0a38a84a08032d18c7150941034da40ae91928200c9d7418e32504218b8c6ba864a082f1b189750c9410062ebaec61928200c6d75d8832504171e90cb8864a080a2f61c629054100656b90c520a8203c3e7555360504011bf06b96c0a08423720d72d81410055a40a85b0282038bf8755364cc40d1b906baac9988023ee01755933100c7c402eab26620387e85dc164cc4010fb0bb82c99880e1fa177058b310043ec2ee0b16620b8be87d9142cc40196ec838a859881a2f21d545923101c3f42ee0b24620087d85dc1648c4011f700baac5188063e2017558a3101c3f42ee0b14620087d85dc1628c4d539f0eb1465189aaf1205320ca310062f3aaec1946200c5d765d4328c4d578d033906518803339c962cc6310346ec1eebb226200c3d75d53644c40717f0eaa6c8988021fe1570d913101c3e42ae1b226200aae82997644c40155b0532ec898802abe0965d913100556412cbb226200abb80597644c40157100b2ec898802aba0a60d913100556c14c1b226200a9e83dd7644c40153b07baec8988030f5d475d91310045f43ea7b2262008bd87d4f644c401c3ea729ec8988028fa1472d91310051ec28e5b226200a9d831cb644c40117d0fa96c8988022f61f52d913100717a94a5b226200e3751947644c40117d0e28ec89889a2f61c51d91310051fc2ae1b226200a3c855c3644c40153d06386c898802a760c70d91310055b408e1b226200ab5811c3644c40117d0e286c8988022f61c50d913100
  | 15 => 0xab86c9990422f21d545933201c3f43eeab066400c7a80dd560cc8018f301baac1990021fa1c75583320145f426e2b0664008bd84dc560cc81717d0faa2c9190030fdd7545923205d57416a8b24640b8bc87551648c8070fd0bb82c9190021f61770592320061fbaceab24640baae829d5648c80155b053aac919002a7e0d75592320054e41aeab246400ab7815cd648c80156902b9ac9190022fa1f53592320045ec3ea6b246400e1f5394d648c87317d0fa92c9190022f61f525923205f17296a4b246400a9f835c5648c80147d0a38ac9190028f61471592320065ab88e2b2464008be87145648c80117b0e28ac9190028fa1770592320051ec2ee0b246400a9e839c1648c80153b07382c919002ada0670592320055ac0ce0b2464008be87141648c80117b0e282c919002a7a0c50592320054ec18a0b24640baae82141648c80155b04282c919002ada0450592320055ac08a0b24640baae828c1648c80155b05182c919002a7a0e20592320045f43c20b2464008bd87841648c80153d06082c919002a760c105923200656b26e4a1c6400cad76993328c80195aecb2665190021fe15709863201c3e42ae130c6400ad681cc9618c80517d09b8ac1190022f613715823201c5fc3aa9b22640087f855c3644c8070f90ab86c8990032d19071591320046fc1aeab2264008f7815d5644c80d1e902baac8990023ee01755913200c7c402eab226400cb7741c5644c8019aee638ac89900339dc871591320065a218e2b22640b8bf87592434c80156902b24869902f630c9748c93201c7bc3aa3b0a6400a7585107614c80156d09086c299002b560c10d85320047bc3ac230a6400ab484584614c8015ab03190c2990021fe15701853201c3e42ae030a6400c7b855c0614c8018f10ab80c299003368c970185320367928ae030a6400cf1515c0614c80d9b662b80c29901b364c570185320055b4242030a6400cf170840614c80117f08b8ec09900a2f21171d81320872d984c0b286400c3f749d1650c91d4bf06ba2ca190429720d74594320053dc02e8b286400a78805d1650c80147f08b8aca190028f211715943238d2fc1ae2b286410a5c835c5650c8d74df04b8aca1902e9b20971594320053dc02e2b286400a78805c5650c80147d0838aca190028f61071594320043f43882b28640087d87105650c8214bd07382ca191529760e70594320051f420e0b286400a3d841c1650c8214bd06382ca190ca9760c705943205d37410e0b286432a6d821c1650c8014ed02382ca190029d60470594320043f43e80b28640087d87d01650c8214bd07202ca190029760e40594320852f41880b286400a5d83101650c8174dd04202ca190029b60840594320852f41c40b286400a5d83881650c80147d09082ca190028f61210594320852f41c20b286400a5
  | 16 => 0x880500080000000900380000180080000500200000100000400200300b80300100080100100300400000200f00380000200980580000380c01780000300180200180180980080600300900000000200180000000200100480a00180000180200100000200000200f00000000280680000280000080980000380100100400680100000a80400280000000480080080300180000180000680680000000080100080080080380700280380000200180100000100000080b80280000000080180100380000100080080000300200a00300080980180200480000001880000400080780100100100800580300500280080000280000580100080b00000600300d00800000080700b00000401680000000700100180100000000000880100200080200280180100700183000480a00180080080181f00100200a80000d80400481280480180080100980680080500400000200480180000980580500400200900102100180000580000080080780000280880400080301180000a00401100000080000180100080000380900180680100080000080000a00200000100000280400000000000000600080080080100400e00500a00100880080080600180000000000080400000080000900100180180280000400080080000500100000200380001600280180500000000000000000080280000000a80900d00580380000100180180300000e00100700880080000180080200000600000500000000000500100000300100900400000003000080080300100003280780000000180100100080300300280d00581301900680000000000180000080080500d00000280080580200000000000100a00a0423b21d5258a430047dc02eab0c86018f8805d56190c070fd0fbaac1218030fdd375582430043f438eab048600c3f741d56090c07878eaaa2c1218021fe1570d894301c3e42ae1b1286008ef875886250c015c902b10c4a18023de1d611854300572412c230a860087f855c06150c070f90ab80c2a18031e5d750d81430043fc2ae131c840387c855c263908171b90ea9ac7210021fe15709864201c3e42ae130c84008fb805d561908031f100baac32100f0f1d554582420062ebaea7b1a8400a9d84d4f63508011bf0eb18c6a1002b52056318d420054ec26a631a84368bd87d8e43508011790cb8c86a10031d5d751d85420055ac20a3b0a84008f78758461508015a906b08c2a10030f10d75185420061e212ea30a8406c74815d4615080d87e82ba8c2a101b0f50575185420061fa02ea30a8406c77105d4615080187aeb218c2a100a2f61e42185420061ebac8430a8400ab58190861508018eaeba88c2a10021f61e75d814201c3fc3aebb028400c7b805d760508018f100baec0a10062f21171d81420063cbaea1b02840087f855c364cc8070f90
  | 17 => 0xc868a44f01009bcef200000000005103740000fbcd400000001e10ae87d915d15442d02a41818660a5a78e275960504c1f721298f400006d000000000054726499c000051a2231b7c94e36e05f000075c108012000000000000b80000006f93ba93c8d4800000003004ec0550c796407a4219000000079800010f942c9843df35e97682045712908ba04b67ba06a8f3803400022113204fc0b5155938814c00039215b040652225f0dcc0008320bd80000000000001760e14000223903d02a7d62b70c6d1aa26636a97fcfd47b226881e00a28080c686442784493fc8758000041000000000041232f800028200024620a834427339500000007cf07e21a0000000015000081000026680006406d31b9000000075835f8cc0a8400042097d88984c71b810800003820d50d509a8825251a2148a80fa09d9a28a2a0003940000446000000000099c4870000000b6a00030906e4ec83963a19de0b4c86e4030084eba0da0fc99d41a20ed1768a702c40bb35b92887c841b15084c807434214b1dc4be81b41d81cac51c0e73d017080000003cb9270f540003ee0534e9a8033d48000000000000059c00058b1ca8000000000000000009c44500003c90043e030891c0b1e6be02fa27400067a1239eac000000000000000000034a0000da82a30851c40efa0a52920000350427170a22400085400000080880180000280000480100280080280080200b00280380080180200200000280300000580480500400100280900400000000680000000080100e80100580800200300000200480000080d80000000300100000180300000380100a81b00080000200280380200880a00000a80001400000200a00280000000000f00b00a80300280300000a80300000b00400380a80000000500080000000000000600580080000500080000000080000500100480a80000000180480200000080180080880200280000180000080000000100000380680380a00000080000980780580080100000f80000100180100600d00980000900000480180000001680700980080100300000280000080580081080000302000000000200000280200300300d80180281180100c80000080000180000300480080900000000000400280280400080400680080580000280000500700f00300000b00080200580000000080180600000100280200080000200180700100300080000200280400680000000800300080500080081700581580400900000000580500300700080280080000a80001080100100700280400080300e00000000100080200300980200200200180400280600600300480100700100100080180100380180c01180100780180000580200000080000700100300280480000e80080100080000081280080000280a002804001004809800803000809
  | 18 => 0xc35a0353e315740003872931ad455c00000018c8b3c2f20001f6c2f28c42d2800034275400018fc0000000000e9c0004da13d80001d23dd3b30bd80006e51cd04250e634031c0cf84101a700000000003191dc0a5d1a07a62b3822d0e824a0042264b1000022b000024800003b9740766650000000000052f4501fcc0001a315918283fe2a51a500002406cb22f00004706da1ed1f8ceac4551ff8000b266332f8893000001400000000007f800002b400033f00000002d6000000000000000000000006280944530c080004b0000183c00000007c000000047241c206400047a0000000000000161948c0008970002128df05e207980000006662270fd0398000038800000000000004a00004a01b080004565c600000003fa87000001984824ca302a1340000000001a648e21d70002074a084d30000e3000000000000003de00000000000c449239a0b30b28836000071c45830f0000e34db600000000009160003c3800000000009280000f81c100004883e800b0fe0de88c64d2000193016e4e80610e240002f00000ec83d26c62411a5465c0001071b10c2017100000e47fc193009800080a2e60001e88e9c5c70338000b5a2dd2030b18f588933588000cfc51e14780003f400000ea170d5884f40000000001482e280000004c008f84b081a0fe0228ee478a25600012c8e608db39b000000066020b00006cc4d51221f5c42e60c2749294eee0000ca000109c6c71aa8bacbf42c214282d82367d3116a2b487401c10a22a90f406a11b8d341607521c78f18e848cd028043020c520000010cc5673b0001c840005f310480011c84ef0df0c384145312e500001c600000000010f686124180002460300ed0af898845144d9770cd241c000000000000000000000000000d012f4000000261800000078a0001888cca19d1131e90a3202906e1ec10781050629e5905a85e2a49474d908b80fc11986767492bb8d405d856315d80bc9c27511e698002220f702e0990c802fa000057806653328b00006620001b1000000050f23d90cc5fa00000004e01443fc2ed8a40be066431e0c280a400028c0fe904e2a823107cc3c223219584d4e7a0f52530000c4c2042c2000000000f0000bd0de27ca33416c000078634b9c98b3420706593d073627045491048626fa1bb1fa4c9215a2e19c4910075a3c49e2c6445b942b0350f063f72b92220bc86fe06c93a88b225d4388adca144ba03d0a24a1c0002f285f4dec047000100c68874800002287e63410e9064015668731195a9046255403863886019c32d884cb500c80c909f51243060001b8000041d3478f84710000000232c8e804a3a3000077800015984bc5681b537413ccbfa3fd38f82241a64af3e117348787050001a8c0000000002048d802d105883fca9070800001fcc7400022f9db8000000
  | 19 => 0xd317947114825e29822ac7465a31b296fcfc46e42b001f50122af1ae84581001b709f0244f981ea0000b28e1a00011980011604971ae1a481c86fb0c29510c621d82f19c5000000029708485604092a500000007920dea1ad0222272e48a9918a3d53970774f203002e984e50cc5463901e7c8ec3900b6940819a496130105cc8c00032400009828d82bc1dc835e4b70d59bf0af669f1561ad839e000398800000000027e1660fca49f350860ce0066304c9e503600003d6800082220d00022d82263e52aa85641406ef216043c33485d3e1a2c829623b10a88e51340002170ad400071500000ad0846a72d48000dc260d293a388f9675900001b028800015b13e50420000a901800007b71ac0b348fc0002860b6cc8e000439202800000000009a0050747416023111a6c942d0000000529000000000035617c0000000000000000000072500015607f600000022601263e213d1bf40007fa0000fc45ac0000a19c0c00043b36b0c30b0c11400014244a2402380813000051f1d303b8a9804418099ecdce0541af11205223d4000087117a000000000000047d43603c400063e12c00003ec00000004d8ff873a3770160b188be3551fd800000010802540001f500000e0b0a8843730e7400037745b9600b7a83908e1b5cb90608001a2584ca0001888000dbc00030d879908c4cb04e00000000ba30b88800004bf0000000cb200027d238c00048525e0378c3832405e15c000000000020c4f028bb3e71a6c0008b10ac16444ea5452d0904cab80002ab800021602739900004ae00040e000000a8c2450800000000000000000000001a8800091c000086828cf3c000000054400035334989344e80000001a88e946072441d4c00005d00015a51b251145c800000053d242188453c0003b482051bc0073378df45961ac22d88bc7f0040000136086a00036c20585307c10b2800005a7820000c10850000000152c00089500019a800054d00000000000000001f980000000001a2c00000000000000000003bf0000b2e00016c00000000000cc98802e62cf26c8000b6448a00021d40444dd44a14c800020135a0868ef40570000c591c23521fc85e8dfe7de3f721e40004860001448ab655e0679e54caa12b0b611dc8a0847000000116a35f00000000004c52291a24d1057300018d8c34000428800000000026f0000eb800031496482f80003de8c600005aa2b109c40002531cf00003e00003d09160cd63c91ca1d842981b80000c5c0000001c903286d60cc0631bcc7dc00000000ec00000004e89b42a85890a383746f26af0001ed8b3a5e81d4920057046b000000062407200000003d02ce00000008f200000018a0c4e66e1e518781e86241c5a160f667df04f8d8087e3a53de17dcdba06944f0edc27e2991c00ebcf8e83e21a111117e45713606e
  | 20 => 0xed0860000000bbcd000003ea9e4c10800009b8000ed03c82f712a400082b00001d514630721e940c00085500a8ca4bbe10700020a4b96000406800072606b25d800000000040b9ac000000043480004223c42009ce4aa655a00017f0fea0ec239a06036c64d3a08000fc271e0e284c038061d32296802be0002be9bc0d7234729a0000000000039800030200000021400000003b80000e520bf0001ac8b3e46d05708001c249d24a80981300002fc18d01f27eb0cb07786f03bf4619d805c079900000000007850001ba4ca23c20f3834800074c13b8bf80900db0a109fc0c20000e49d789ee000156920449625c2e880000a600029a80004d200030f8000c320001ce00000006bc000000000000000005bce340001be00005920002148000fb48c100000000001a92110000e700f0300a0809fc7c500000000000003af8c9c0006542119a6000000040800000005830ba8000bc2000000000000021837b837c51a29519180c400000026d8000c306b325b00000e82e72a79690c125e906b9d9d0880003e2180ca9c6740001c4c000000151145c01a000000006400083004100008dc5961458af403c357339004466c44346a14dc1b014600000000000000b480001de0004660c840004390a28cf05c647c32f10608207ed000000096834f00000010b2000000094865043e445874cb880fb000093c9f008f02b00000000000000000fe08b3000000027418c2be1f50eca03f00000000000002d10168478489061950068c7622f388a46905950ea02180007ef1ee1c70e8811d149975446252a4110234ca67d000000006b200008a899d14e82e12f8b6400000033f80000001fb4339c5cc2814a39a96c49328ae43c100060a7193bb02143b836f3b6a2400001c243b1750bda0251a60720f800001c28b4cf3a8a529588d01a032533b9450a001872489dac0003d040580005880000001a10506000032800063c0001310c9908a5d20000e04ade000225a004fe83432eba1905aa6811b3803854e42b1f180008640000001cf032e31c1f80b511ba7af2fd80001700002de07910ee7ff301220c0000000a0000000016e409839910e000315091800000000017aced800000017742a019b0b0840040a40a31a93987323b60b31c583161551d41ee05dc32d38c20fc0008a806b1bb04164dc000133c50c00002f00005e207043f000115864119500002ac7e700015b400000000019289ce4ae0001a340000002c500010a46dc0001fa0fba0000c31fc45040ea2681eec70611939f1b38a0e53b0000ed00000001b4207cd040001170f9847c3a223788e85d43130729bd4e7e7a5356869800024314a02f499883732c1b311ac3cf1ed861000079135705e0c6e06f0001318a824041031bd0b7c29232707c40005381cc12e40003b518d0001178391082150d19e4e
  | 21 => 0x7e45d218885453903c923c55469e1b696dcc5a678005078c00072200012b00006c10002288ee67ec000000109033735c07643a27401cf800069c8df18f999cdc40ce32b8000c9e8e017c99b014872c3430cd469262543694f8af43c01fb08883743bd33c9e60f925ea00000004040000740000c2619e23390e09fe3aa46500005bc8573650cf47da8240d713b824c0af383800000072343f9b64b7009a42009b850800010b2050b6c4b3341923450e0001728ae4e120ac04180009303be0081e3495600000000004547e43c4000000032c443000023c00000000006d400023214fc5a432f0001970c1c45a1ad9a387d681a31804cceb66d000007b82c6000053800096a0000548460b0e15c064918418e00019c000119021e00000011025ba0001f6061a36900000000021ca457896829c06800012a066433300009851b8160250938cf004a4396a1f47e41c419d00000000000000900d182c10ba0bf0a5836c2569e6c5802e416812501d63ad05c99c472e8d104905dc4503cb0000f645344240b206549fa6a807113947ea00014d8000b5c2a90319e68c5c00016b939012e28a3688000f907d104b00005c46420de2010ca423f28d80000006ea464a27c0004931841bac0004403be22709547040ab8f440120643059b0c3a05af0371608a6c34b0001584000180000000046c04d00000005be4b100000002a67be0000924bd80000000000e963a027aa0e84f80000000a8000000041795640000001c3044103600031608c07d20000020dc416460400004a40000002a8169c0005f51e09f8021c0003bd848400472f00005a800000035594045781a43bf816436220f20f902ceae0003fe9fdcb383c72178dfc5f653a00008f50967330aea3188ea38a3d40108d347a333096b000000028291745624b834e14184f04f12a908750ca221048234c63a525000045c03003d0e694208d05660bf93ec36451327b078009e2592cd9a94b325cf0001dbd19c0002ec87c829e3e72d9856c31442123487b506623502317590b67bf00320791a48051f503f400013d140008ceaa0000000bfc10e0c41c2000109800038110b40007b406097301662240471380b9c863288214d07a0003d71a40afc00000000000363d732b00000006ed1d880000006cf45a1a4493640c20f20ec71c83510d96ecc0c2541880b146127a743790d800000014092407d0049441118106888e0df95e4c8641922e103800003c2fc9a588f000000000002680000000000000375424800026271126b13c02e01df04f0f607566d217a9c183128d70bb114c49c5fe0bf17807ac2480c1012cf9a71d294005911829f08d21808942450f600b86f61c614ea23c03e55440783d8a1a76a2ef101c44a05b33e02848341e201b16ac0006390001a9807c00000000000001fe38580000000001d09a
  | 22 => 0x370d98030de46e316380484840000001cdcafe3de3b1800000070c000026d18e4ec4071594ac858e26f9ee50d40a846d109839c46a0891d145e688a0ed97bcf6243733b02d0c2a28c29e1b140008c000019b4ad080c09380000003a42f900003d61a50000f4c3100e016d0000aea1d51ad11fcc966c238789acc7614918a9a745b855f32d16d04f249e0001798aec6cd19a094025a2630001910f1e67d0001fec0006851b18eec5ee2e93399c9c4e40000000000774828000000093444d3da81ec20630b01a170425c0000cf8eb000007635d198867226a0001ff87d80003e900b0d5212a43e072cee82c80550220f1858d3a79054b8065d4489fc88d870e1b2185857e5561e191946fc71b0f29e702e41c342f9d4020220c2b5935c8280
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x32e34980806014b36a92b8289a7baa0c00a608016100c003a47000100010011c03c008b0040f66074995610c8012d190205325843235531a5b721c5324c40184d86614724c4310069260d821d5600c401a3184604755803100698609811d5600c401259981d43258031006a2e10824c5600c401a8884209315803100692a54824c5600c401a4995209315803100692dd4824c5600c401a48752093158031356b0944824c5600c401ac082545315803100652615801c931cc00155191201750c9300050765c65190324c001c0c65190724c53000711d9472185314c001c87641c8614c53000507654419cf64c800103d981d2655872035531245631c9314800141d9510473591100050b654411c964440010759819471509100052524d641c542440d58c876209314c110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x8926a4752093158031
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x94d
  | 5 => 0x94e
  | 6 => 0x2
  | 7 => 0x138d
  | 8 => 0x138e
  | 9 => 0x98d
  | 10 => 0x98e
  | 11 => 0x3
  | 12 => 0x150d
  | 13 => 0x150e
  | 14 => 0x9cd
  | 15 => 0x9ce
  | 16 => 0x4
  | 17 => 0x168d
  | 18 => 0x168e
  | 19 => 0xa0e
  | 20 => 0x209
  | 21 => 0x20d
  | 22 => 0x20e
  | 23 => 0x140e
  | 24 => 0x154e
  | 25 => 0xb09
  | 26 => 0xb0d
  | 27 => 0xb0e
  | 28 => 0x1409
  | 29 => 0x140d
  | 30 => 0x1549
  | 31 => 0x154d
  | 32 => 0x249
  | 33 => 0x24d
  | 34 => 0x24e
  | 35 => 0x144e
  | 36 => 0x16ce
  | 37 => 0xb49
  | 38 => 0xb4d
  | 39 => 0xb4e
  | 40 => 0x1449
  | 41 => 0x144d
  | 42 => 0x16c9
  | 43 => 0x16cd
  | 44 => 0xb89
  | 45 => 0xb8e
  | 46 => 0x1489
  | 47 => 0x148e
  | 48 => 0x3c9
  | 49 => 0x3cd
  | 50 => 0x3ce
  | 51 => 0x15ce
  | 52 => 0x170e
  | 53 => 0xcc9
  | 54 => 0xccd
  | 55 => 0xcce
  | 56 => 0x15c9
  | 57 => 0x15cd
  | 58 => 0x1709
  | 59 => 0x170d
  | 60 => 0xd09
  | 61 => 0xd0e
  | 62 => 0x1609
  | 63 => 0x160e
  | 64 => 0xe89
  | 65 => 0xe8e
  | 66 => 0x1789
  | 67 => 0x178e
  | 68 => 0x138956
  | 69 => 0x98956
  | 70 => 0x9c956
  | 71 => 0x289
  | 72 => 0x1849
  | 73 => 0x14c9
  | 74 => 0x2c9
  | 75 => 0x150996
  | 76 => 0x409
  | 77 => 0x1889
  | 78 => 0xd49
  | 79 => 0x1689d6
  | 80 => 0xb49d6
  | 81 => 0x9cb56
  | 82 => 0x16c9d6
  | 83 => 0x9d6d6
  | 84 => 0x3c9d6
  | 85 => 0x9c3d6
  | 86 => 0x15c9d6
  | 87 => 0x9d5d6
  | 88 => 0x589
  | 89 => 0x18c9
  | 90 => 0x17c9
  | 91 => 0x5c9
  | 92 => 0x168b56
  | 93 => 0x1696d6
  | 94 => 0x1683d6
  | 95 => 0x1695d6
  | 96 => 0xa1496
  | 97 => 0x4d
  | 98 => 0x124d
  | 99 => 0xa0d16
  | 100 => 0x8d
  | 101 => 0x128d
  | 102 => 0xcd
  | 103 => 0x12cd
  | 104 => 0xb0211
  | 105 => 0xb0216
  | 106 => 0x3ca
  | 107 => 0x3d416
  | 108 => 0x21716
  | 109 => 0x171416
  | 110 => 0x170216
  | 111 => 0x155416
  | 112 => 0xb4256
  | 113 => 0x3d456
  | 114 => 0x255d6
  | 115 => 0xcd6d6
  | 116 => 0x15d456
  | 117 => 0xb5716
  | 118 => 0xb4cd6
  | 119 => 0x16d456
  | 120 => 0xb9496
  | 121 => 0xb8d16
  | 122 => 0x161496
  | 123 => 0x179496
  | 124 => 0xcc3d6
  | 125 => 0x1715d6
  | 126 => 0x160d16
  | 127 => 0x178d16
  | 128 => 0x178e96
  | 129 => 0x58251
  | 130 => 0x59451
  | 131 => 0x59711
  | 132 => 0x58cd1
  | 133 => 0x585d1
  | 134 => 0x5c591
  | 135 => 0x5d791
  | 136 => 0x597d1
  | 137 => 0x59a51
  | 138 => 0x17d791
  | 139 => 0x5d8d1
  | 140 => 0x59791
  | 141 => 0x21856
  | 142 => 0x3d8d6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2133
  | 6 => 6382
  | 5 => 2277
  | 4 => 30
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (87453+((h/711+packedAt gbK7 (78921+(h % 711)*12) 12) % 3746)*13) 13
  | 6 => packedAt gbK6 (336114+((h/2127+packedAt gbK6 (306336+(h % 2127)*14) 14) % 13565)*14) 14
  | 5 => packedAt gbK5 (143451+((h/759+packedAt gbK5 (134343+(h % 759)*12) 12) % 3006)*13) 13
  | 4 => packedAt gbK4 (2160+((h/10+packedAt gbK4 (2100+(h % 10)*6) 6) % 37)*6) 6
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe0fc03f01f03ffc1ffe00067d8cff189e7c
  | 1 => 0xe00ff0003fffffffffe03fff1992f3301fff8f
  | 2 => 0xfffffc001ffc07fffffffe1e303c3e0e3ff
  | 3 => 0xffffffffe00007fffc000fe03fc03ff03f0
  | 4 => 0xfffffffffffff80000000fffc0003fffc00
  | 5 => 0xfff000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa1ee02c60b28721a9d0e720602248457188e3c
  | 1 => 0xc2225000154a9463252214aa0890b1300b3685
  | 2 => 0x444a55a40012a884a54a954616302c160c15a
  | 3 => 0x888b39aca6ac0012739b1018b603dc02bd03e0
  | 4 => 0x110dce3738f1cf3c000c2060dffc0003d6f800
  | 5 => 0x1e00003800c00c2002100180fddb6ba8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37075
namespace PEqualNP.Outside.L_meta_37075
open PEqualNP.Outside.L_meta_37075.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := (concat bs0_3_0 bs0_3_32)
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
theorem bs0_4_160 : Interval s0Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat (concat bs0_4_0 (concat bs0_4_32 bs0_4_64)) (concat bs0_4_96 (concat bs0_4_128 bs0_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
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
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 64 := (concat bs4_4_0 bs4_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 40 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_512 : Interval s5Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 bs5_4_224))) (concat (concat (concat bs5_4_256 bs5_4_288) (concat bs5_4_320 bs5_4_352)) (concat (concat bs5_4_384 bs5_4_416) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 30 := bgb_4_0
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
theorem bgb_5_2272 : Interval gbAtlas 5 2272 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2277 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))))) (concat (concat (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))))) (concat (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112)) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)))))))
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
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6382 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)))))) (concat (concat (concat (concat (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)))) (concat (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368))))) (concat (concat (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)))) (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))))))) (concat (concat (concat (concat (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))) (concat (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)))) (concat (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744))) (concat (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)) (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 bgb_6_3968))))) (concat (concat (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))) (concat (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)))) (concat (concat (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448)) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544))) (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 bgb_6_4768)))))) (concat (concat (concat (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960))) (concat (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056)) (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)))) (concat (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344))) (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568))))) (concat (concat (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat bgb_6_5696 (concat bgb_6_5728 bgb_6_5760))) (concat (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856)) (concat bgb_6_5888 (concat bgb_6_5920 bgb_6_5952)))) (concat (concat (concat bgb_6_5984 (concat bgb_6_6016 bgb_6_6048)) (concat bgb_6_6080 (concat bgb_6_6112 bgb_6_6144))) (concat (concat bgb_6_6176 (concat bgb_6_6208 bgb_6_6240)) (concat (concat bgb_6_6272 bgb_6_6304) (concat bgb_6_6336 bgb_6_6368))))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2133 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568))))) (concat (concat (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696)) (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824))) (concat (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 bgb_7_1952)) (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0feeaeeeafcc8e0c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4241023168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37075.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.or,[5,6]⟩,⟨.and,[1,3]⟩,⟨.and,[1,4]⟩,⟨.and,[1,2]⟩,⟨.or,[7,9]⟩,⟨.and,[4,6]⟩,⟨.or,[0,8]⟩,⟨.and,[11,13]⟩,⟨.or,[12,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4241023168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4241023168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37075

open PEqualNP.Outside.L_meta_37075 in
theorem PEqualNP.Outside.L_meta_37075 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4241023168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4241023168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
