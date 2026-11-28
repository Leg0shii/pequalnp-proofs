import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36276.Model
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


end PEqualNP.Outside.L_meta_36276.Model

namespace PEqualNP.Outside.L_meta_36276
open PEqualNP.Outside.L_meta_36276.Model
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

def SBf (j : Nat) : Nat := [8, 6, 6, 7, 7, 6].getD j 0

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

end PEqualNP.Outside.L_meta_36276

namespace PEqualNP.Outside.L_meta_36276
open PEqualNP.Outside.L_meta_36276.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x53ebd118243c2270000d80000128032800ad4ca482c3400991108ce030cb8f0a16a0b8e4200a2b4800eaa04003801a30b092a00134008b000100047040100ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x617e510c2faa2186fd0430dea0861df310c3bc6218774c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030efaa061de540c3baa8187715030efa9061de520c3baa4187714830efa1061de420c3ba84187710830efa8861de510c3baa2185754430ee28861df410c33e82187790430eea08619d410c3b8821877c8430ef10861dd210c3b842187794030af28061da500c3be80187790030cf20061dd400c3b880186710030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20bf28e417d51c837e83906f50720ef98e41dd31c83de43907b48720df20641bc40c83bc6190770c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106fd0620dea0c41df31883ba63107b88620f610c417e508837c81106f10220ef18441dc30883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a4174514837e82906f50520ef98a41dd31483de42907b48520df20241bc40483bc6090770c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841bf410837a821077cc420ee98841ee21083d842105f94020df20041bc40083bc6010770c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c43be6388774c710df20621bc40c43bc6188770c310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c21df53842bea7085f94e10bea9c217c53843b8a7085714e10bfa94217e52842faa5085f14a10bea8c21bf418437a830877cc610ee98c21f721843e843085f94210df20421bc40843bc6108770c210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd41443be6288774c510df20221bc40443bc6088770c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821bf410437a820877cc410ee98821f721043e842085f94010df20021bc40043bc6008770c010fb88021fa10043ea20087e44010
  | 1 => 0x721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa0a43bd41487be6290f74c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421ef98843dd31087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40bf28e817d51d037e83a06f50740ef98e81dd31d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c81df31903ba63205f94240dfa0481fb409037ea7206f94e40dea9c81bc539037ea5206f94a40dea9481bc529037e65206f8ca40de99481bc329037ea3206f94640dea8c813d5190378a3206fcc640cf98c81be319037a6320674c640de18c81bf219037c43206f48640de10c813e50902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c52502fea2a05f14540dfa0a81bd41503be62a0774c540fda0281be40502fca8205f94c40bea9881bf431037c86206f50c40de218817e52102faa4206fd0840df21081bd421037884205f94440bea8881bf411037c82206f50440de20881df31103ba62205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28881bf311033e62206f8c440de988819d311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc2fca5985f54b30bf28e617d51cc37e83986f50730ef98e61dd31cc37c81986f10330bfaa4617e548c2faa9185f15230bea9c61df438c3bc87187750e30ee21c617e528c2faa51877cca30ef19461dd328c3b865185f94630bea8c61bf418c37a831877cc630ef18c61dd318c3b863185f94230df20461bc408c3be61187ecc230efaa461de548c3baa9187715230efa9461de528c3baa5187714a30efa1461de428c3ba85187710a30efa8c61de518c3baa3185754630ee28c61df418c33e83187790630eea0c619d418c3b8831877c8630ef10c61dd218c3b843185794230efa0461de408c33c81187750230ee204619c408c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930bfa8a617c514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ef21861dd430c3b886185f94830bea9061df320c3bc6418774c830ee19
  | 2 => 0xcbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53907bca720d794e41bea9c83dd53906baa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83be435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41ef298835e53106faa620f754c41aea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc7be8798f790f31eea1e63dc43cc6fca598df54b31ef99663de32cc7ba6598f70cb31dfa0e63bd41cc6fca198df54331efaa663de54cc7baa998f715331efa9663de52cc7baa598f714b31efa1663de42cc7ba8598f710b31efa0e639f41cc7bc8398f750731cea0e63dc41cc7bea198f794331af28663dd50cc7b8a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31aea9c637e528c6faa518df94631dfa0c63bd418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f790d31eea1a63dc434c6fea498df14931ef99263de324c7ba6498f70c931dfa0a63bd414c7ee6298f78c531bfa82637c504c7bea898f795131eeaa263dc544c7bea498f794931eea9263dc524c7be8498f790931eea1263dc424c7bea298f5d4531efa0a639f414c7bc8298f750531cea0a63dc414c7bea098f794131eea8263dc504c6b8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31af298637e520c6faa418df94431dfa0863bd410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21dfa0e43bd41c87be6390f74c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621dfa0c43bd41887be6310f74c621f790c43f
  | 3 => 0xc42f2415320000012d5500018d9ae000e10438cd54cbf0000d71ac1340021f6f4595280000006d8000ac0007d40000071c2791f029366ad9429d80f033c0023c142bb80033f0000000000000010c0030c0009b80028c034004a200000064400000000609e1a816e87f8e580426825c0000000000011155000235d58005600000000000092ced80000c79512bbe63a08c30800210841a5b16000049a117a55e8202d9bf7628480039633a001e20005221b42f9a870e79c9f3890000013f000770984000000000020100300000200c0000001a0000200300202000000006038018040000000c80100400001800000004058000040240080c0160000080000000800000002010020060000a8000000160040300001400000001000004008010000000180700202c048000000080500500205c0180100000c000050040140000100a0300500400400400016002004000000060000180f00000809001002010020040000441580200a02c000050000000b80500e000000040000180080002402c0a0010000040000100000001000002040000000060100000000005c1180801000c0000000406408007000008028060120000000000002400801002000010000080000080000800c0000700202000002008008010000080000600002a0080200000a0000300201c01005800004000008010000080000300c02c0080000e0100780300400c000020000080280000c00c0000d006000000070060100000800200800006000020010070000000180a004018008010000200100500200400000000008000000020000280200c024008000460000580000402c0300300402805800000000018010080040181300c0100100101200c000000000140180100e0000600101001802014008000008020040040180f00800400800006000015f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528
  | 4 => 0x2772f8ec9afb6f62a7ac410830009b5698000000000005d01aa88003d85da60c000d82e200153800000001212f3000001a2000164d04c33e63849a82994f0fea59110884f4d3000000000b08002c668a3b16f0e637699cee0f3000001d1800000dd51fa2b7b405c00130000001b721a0000015f2aa6e60007f80566800000000000001ce2870c46d400000012001bfb08000001c31701be0009439500093000000098038ae0f542648434a116b87b1891227106ac58016414edd01ac056400113800000878000006f69eca000064c215758007a69918d3c91d60017d800278000000000000011989f0000009daca2929cc1ca985260012f8562640007d093000000000004ec000001b7000fb00c0bd148954bb808236001b90000002a5cdaf621600064ac7000118001b065e0640000012a190c0bad7c0560e6000000084000322d8720fbb2d16200162800000000000000005ede7800000431809ea000600003646947a527a6002266c63b1e0001d00eb8578cea006113506995d30d341630d65a1b45400000000054000003e20000010200000054d88000000998002ac000724b582d4f2000000005f20000038c21ce61030000000000000000000000000744a1923905000650768ce0663c0e511e5d0d6d568815880018c00067858c658003345795c9a50000000020f0000008ea8d18c000140d4714001d9800000498280c25869f435b566ba43da994d4301f8000000002701dbee000bfcf81e815ecac4da002ea148cf138000e75472a45a27d0ca98e7a8114fe0d05e8da0158a3000000d91d6616f35e8b541d0ce8ef3ef00088c7e000438b2400000660dc0a103407e7488a16400065c001161f6001938b820c58559800000000249694e473c0028a6124acd33b039a001e2ba7000a094e00002629d2216d000001e0359774d494a9c65760c5928385ce53924007000384aa3c1048cc8002db330880608157244cc48000000000e204830ed44a62e92f2a812b9ee7e43a5fb1df4ac000000921a43d0003d744c0016faae7a40016780000000082382000e790b35e03c000002904e20001b8007da0011a800516000bb0000003e400000312db0963472ae700c686c000001dc86a000000001930000000003d49200150b990ca5cc5baec00042400360000885cf800000e943c9e0100a69f48ab6ce000e38c84b2ed8052a3524001310000ec8d80033708e000001fa7bc000002e23740002a240000ddc001f25cab541f08a2a278c1b3f4000e5c003480fa630000005909705b000000000000002328ed148b4200001eda3d7ac39de38573baea40000034889155bf026c000000002b69f00000066c1c4301f85f40011a34e05e0010a2c159ae2c00000000a24ea08b166ac531b8f7a0799df8420ee3dc8106625490de40dd404ea8511aa5a44
  | 5 => 0x27aadc3aaf80000000030261c5bca436265ce84a280012807ced3431c659d3600017c000d100053c000003650000000036d00009c00217308a6db1a584d2444dc0da000f70928005b02a194800000c88f7800000001f08006500809c800230d34afa9d6e24bc550bb2dc000003a05b429400010340fac002f543240c001b46fc4a41d000632210df20700446904800000000003e7000000cb000000354d63145fc8e16e00040a001889e1000000001f357e0000006e796f38d8999626001d2338000001be0fd2c0000000000580008b9d10b81f02c985000a944e8e44b4eb13a8bc0c63e09f91f43ace4173833a0b74b1143096ae93a34f666001908007caced1880017e001f8959194af06cbb4734428003ae49a06c220cc598da812800000a5d2e8000005e11724a7c61ccf684e6488e4d082611ebdcf132a6fa000000003b2c807b000658144003df01648d9aa5200000062b8d0000000005500067000000000001700004e07fcc505a000640d798f000b380000028c0713c07a172c000028f7e60000000015ad8400000000000a9000000000b30ea00043400357132000b51150003c8000ef2d0b65443e448a480000002b475c00003000000fdb694640003d800000738beae16b00014a0006b496d91bcc500310700fe0008e92f25378438935835000230dc9f600013dfbb045c6224571357d47051b80012203d342b50009396b9f1094e049393a00074d5c03c45e0000000025cc3c00000180c15ee800000000001413520004d2b44fe52c0030d42a491230006aa0000019f75ec5df41370b040400000000000bf0ba12cdadec97260c3b86f0dc4585fcfe9d56a0d195e8001e27e4e18005fa000f230a5e0de1fabb50007140003079428154ad410c575c839400000000000778001de80035a440000005de83118379000b9978800000529c8800662b904730700068c0000028e00068a517f02980000053ec0c000000286f56b000000f55790000828a00000067ab4000000000e017522d63810000000000000002542a09bcc5b762ac41d06a840e0001008b57260008e3660006484c000000000001881b6000d38000e41a08900067ceeda00e50ce6f00000041c000ba3490dec7c0000000
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xc40842b56110210c7d52308431c548c210b5586308431f540c210c715030842d5610c210f808620842f06148210f8c85208423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425e6014d1097180534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414425e65cc510c7d53314431c54cc510d3d4b314434c52cc510b6983314425c654c510c7d51314431c544c510d3d49314434c524c510e550531442d8604c5108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c521011097996304431f548c110c7152304434f528c110d314a304425e650c110c7d50304431c540c110d3d48304434c520c110da14a20442786548110d914a104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c1097d85530425d6154c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810d9185520423e64148108f590520425e63148109758c520426e62148109e980520423e64944108f592510425e63944109758e510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410425d65cc410c7953310431d54cc410d394b310434d52cc41097d95310431e544c410c7551310434e524c410d3549310436552c84109d594210423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400425f658c01097596300431e548c010c7552300434e528c010d354a30042d5618c01097d94300425d650c010c7950300431d540c010d3948300434d520c010b55843004398400c0109e596100436952840109dd9510042e462440109ed9510043695244010
  | 1 => 0x8398400c2208f587544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6115120c7d53534831c54d4d2097587534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534825d6114d20cdd53514833454d4520d5d4f514835453d4520cdd93514833464d4520d5d8f514835463d45208f990514823d64145209798c514825d6314520cdd5051483345414520d5d4c51483545314520cd99051483356414520d598c51483556314520dc580514823e65d05208f197414831f53d0520c714f414833751d0520cd147414823e65505208f195414831f5350520c714d41483375150520cd145414825e65cc52097197314831f54cc520c7153314835751cc520d5147314825e654c52097195314831f544c520c71513148357514c520d5145314826e65c8520d9147214836451485208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4c404831c5310120cdd444048334511012097996304831f548c120c71523048357518c120d5146304825e650c120c7d50304831c540c120d5d443048354510c120e61003048364518812097d8d540825c63550209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948208f992510823d64944209798e510825d6394420cd94541083355150420ae1814108356514c420d554531082d8604c4209b59621082e960084209bd9520082e46148020ea10120083c830480209ed95200825e63d53109758f54c425e63153109758c54c423e64d4f108f59353c431e5494f10c755253c431e5454f10c755153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c431e53d0710c754f41c431e5350710c754d41c431e54cc710c755331c431e544c710c755131c4395414c710c794e40c431d5390310c794c40c431d5310310c795230c431d548c310c795030c431d540c310e610030c433561d5210ce983548425e63952109758e548425f63552109718d54843356115210ce980548431f54d4e10c7153538435561d4e10d6983538423e6494e108f592538423f6454e108f191538431f5414e10c715053843556114e10d6980538423e6494a108f592528425e6394a109758e528423f6454a108f191528425f6354a109718d528431f53d0610c714f41842ba60d0610c7d4d418431c5350610ae181418431f54cc610c715331842da60cc610c7d51318431c544c610b618131842f16008610c7d4e408431c5390210ad586408431f5310210c714
  | 2 => 0x605063097994418c25d651063097996218c25d6588630a7992218c29d648863097994218c25d6508630a7990218c29d6408630b6980218c2d96008630a7586408c31d5190230a7584408c31d5110230e6980408c23d61d51308f992544c25d639513097d8d544c23e65151308f584544c23e64145308f590514c23e65d05308f197414c23e65505308f195414c25e65cc530c7d53314c31c54cc530c7d51314c31c544c530d5d45314c23e65901308f994404c31f548c130c7152304c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30c7151430c25d6510c30c7550430c23f64548308f191520c29f644c830a7191320c29e640c830a7590320c34d520c8308f992510c23d6494430cd945410c3355150430ae181410c35551cc43097596310c29e648c430a7592310c29e640c430a7590310c29e64cc030a7593300c25f654c030a7d91300c29c644c0309ed95300c2da60d5030c7550540c2ce6215030b3588540c2d66115030b5584540c2da6015030b6983520c29f6454830a7191520c29e6414830a7590520c34d5214830b5984520c2d56114830b6980520c2da6090830b6582420c25f655083097195420c25e651083097594420c2da60d4430a7992510c29d6494430a7990510c29d6414430b3988510c2cd6214430b6980510c31d51d0430a7983410c25e659043097596410c29d6490430d5546410c3555150430b6d81410c2d86050430e5d85410c3965150430c7545410c3955150430c5545410c39b6050430a7181410c3986050430a6181410c25e651043097594410c29e641043097996210c25d6588430a7992210c29d6488430d5546210c3555148430b6d81210c2d8604843097994210c25d6508430a7990210c29d6408430b6980210c2d96008430c7d06500c31d4194030d6982500c39b4194030e6506500c25d65d0030a7586400c31d5190030a7982400c31e5090030e6942400c25f6550030a7584400c31d5110030a7980400c39a6010030c7940400c39a50100309798f54c825d63d53208f58654c823f61553209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f209758653c831e5454f20c755153c825f6154f208f99053c823d6414f208f99251c823d64947209798e51c825d63947208fd9741c823d65d0720c794f41c831d53d07208fd9541c823d6550720c794d41c831d5350720ae18141c825f65cc7209759731c831e54cc720c755331c825f654c7209759531c831e544c720c755131c82d8604c720c794e40c831d5390320c794c40c831d5310320c795230c831d548c320c795030c831d540c3209798f548825d63d52209798e548825d63952208f993538823d64d4e208f992538823d6494e208f992518823d64946209798e518825d6394620ba580218
  | 3 => 0xe40c7d4e53902ba6014e40a798f529029d63d4a40ae983529029e6394a40a758e529032f5294a40ae980529023f654ca408f195329023e650ca408f59432902ba60d4640a798e519029d6394640a798c519029d6314640ab98851902ad6214640ae980519031d51cc640a7983319023e658c6408f5963190397614c640c7545319029c604c6408f994319023d650c6408f996219023d6588640a798e219029d63886408f994219023d6508640a798c219029d6308640ae98021902b9600864097587535025d6114d409798c515025d63145408f997415031f53d0540c714f415031f5350540c714d4150337515054097997315025c65cc54097995315025c654c540c7d4e405031c5390140c754c431025f63548409718d521029f6350840a718d421029e6310840a758c421032d52108409798e511025d6394440cd547411023d6590440a798e411029d6390440a798c411029d6310440d59453110355514c440b6181311029e63d0040a758f401023f6550040a7d8d401029c63500409ed9540102ba60d4c40c754c53102ae6214c40ab58853102b66114c40ad58453102ba6014c40ae983521029f6354840a718d521029e6314840a758c521032d5214840ad98452102b56114840ae98052102ba608c840ae582321023f654c8408f195321023e650c8408f59432102ba60d4440a798e511029d6394440a798c511029d6314440ab98851102ad6214440ae980511031d51cc440a7983311023e658c4408f596311029d638c440cd5463110335514c440aed8131102b8604c440e5d853110396514c440c75453110395514c440c5545311039b604c440a71813110398604c440a6181311023e650c4408f594311029e630c4408f996211023d6588440a798e211029d6388440cd54621103355148440aed8121102b860484408f994211023d6508440a798c211029d6308440ae98021102b96008440c7cc6501031d3194040ce982501039b3194040e64c6501023d61953308fd8554cc23e64947308f59251cc23f65d07308f59741cc23f65507308f59541cc2b86050730c795331cc31d54cc730d554731cc31e544c730c755131cc26e62d52309b58b548c31e5450e30c7d50438c23e6494a308f592528c29f644ca30a7191328c34e524ca30a7990328c29d640ca308f992518c23d6494630a7992318c29d648c630d5545318c29e640c630a7590318c29e64cc230a7593308c2ce62d5230b358b548c2da60d5230c7d52548c2da6015230a7993528c29d64d4a30b6983528c29e6494a30a7592528c34f5294a30b6980528c25f6550a3097195428c25e6510a3097594428c2da60d4630a7992518c29d6494630a7990518c29d6414630b3988518c2cd6214630b6980518c31d51d0630a7983418c25e659063097596418c3976150630c7545418c29c
  | 4 => 0x7590524c74d5214931b5987424c6d561d093197d95424c65c655093197994424c65d6510931e5d47414c69e60d053197996414c69d6490531e5d85414c7975150531a7181414c65e6510531a7990414c69e64d4131a7593504c69f6454131a7191504c6cf6254131b3189504c71f4114131c7504504c65e63d50318f596540c63e60950318f181540c63e64150319798c540c63e64944318f592510c63d65d0431c794f410c63f6550431c794d410c71e54cc431c7553310c65f654c431c7951310c71d544c4319dd95310c756534c4318fd91500c63c645403197d8d54c865c63553219798c54c865d63153218fd9153c863c6454f218f99053c863d6414f21e550531c863f64543218f19150c865f63543219718d50c865e63d52219758f548863e60952218f181548865e63152219758c548863e64d4e218f593538871e5494e21c7552538865e6094e21c7951538871d5454e2197181538863e6414e218f590538871e53d0621c754f418871e5350621c754d418871e54cc621c7553318871e544c621c7551318863f64542218f191508865f63542219718d508865f63551219718d544867b60551219e181544865e63151219758c544863f6454d218f191534867b6054d219e181534863e6414d218f590534863e64d41218f593504865e63d41219758f504865e63d50219758f540867a60d50219e583540863d65950218f982540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c2197982530871e5454c21c7551530865c6054c218f990530863d6414c219798c530867a6014c219e580530863e64944218f592510865e63944219758e510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410865d65cc421c7953310871d54cc42197d95310871e544c421c75513108795414c4219bd9521087a54148421f14c521086776548421ce95250087395494021d694e50087595394021ced9250087386494021d6d8e50087586394021ced0650087394194021d6cc6500875931940218fd91500863c645402197d8d500865c6354021ce95150087395454021d694d50087595354021ced9150087386454021d6d8d50087586354021ced0550087394154021d6cc550087593154021dac85500876921540219758653d025f6154f409798e51d025d6394740c794f41d031d53d0740cd54741d031e5350740c754d41d025f65cc7409759731d025f654c7409759531d02d8604c740c794d439025e6394a409758e529029f6350a40a718d429032e5250a40a798c429029d6310a409798e519025d6394640a798e419029d6390640cd545419029e6310640a758c419029e63d0240a758f40902ae62d4e40ab58b53902ba60d4
  | 5 => 0x51cca3f64543328f19150cca7a60d52329e583548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f587544ca3e60d51328f992544ca5f63551328f994544cb1d63151328f584544ca3e601513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3e64145328f590514ca3e64d41328f593504ca3d65950328f586540ca3e6095032c718d540ca3f61550328f181540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c8328f992510ca3d64944328fd91500ca3c6454032c754c43d065f6354b419718d52d069f6350b41a718d42d069e6310b41a758c42d072d5210b4197d8d50d065c6354341ad58753d071d5314f41ab98853d06ad6214f41ad58453d06b561d4b41a7d8d52d069c6354b41a798c52d069d6314b41cb54852d06b56114b418fd9532d063c654cb418f99432d063d650cb41a798f50d069d63d4341ab98b50d06ad62d4341a7d8d50d069c635434197982539065c6054e41c794f419071d53d064197d8d509065c6354241c714d435065e63149419758c525069f6350941a718d425072c5250941a798c425069d6310941a798e415069d63905419798f505065d63d4141ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506b56194941a7d8d525069c6354941add8552506bb6054941ae181525069e6314941a758c525072d5214941ad98732506b561cc9418fd95325063c654c9418f994325063d650c941a798f505069d63d4141a7d8d505069c6354141abd8950506ac625414197982531065c6054c41c794f411071d53d04418fd95411071e5350441c754d41106776550441cd951411065f63540419718d501066e62153319b58854cc71c5450f31c755043cc63f6454b318f19152cc69f644cb31a719132cc69e640cb31a759032cc74d520cb318fd9150cc63c6454331b558754cc71d5415331b398854cc6cd6215331b558454cc6d561d4b31a7d9152cc69c6454b31a799052cc69d6414b31d354852cc6d56114b3197d9542cc65c6550b319799442cc65d6510b31a798341cc7976150731a718141cc69e64d4331a759350cc6ce62d4331b358b50cc71f4194331c750650cc69f6454331a719150cc63e60952318f181548c71e54cc631c7553318c63f64542318f191508c66f62551319b189544c67b60551319e181544c65e65d0d3197195434c71c5450d31c7550434c63e64149318f590524c69f644c931a7191324c74c524c931a7990324c69d640c931a7992314c69d648c5318f993504c63d64d4131b5586544c6cf6255131b3189544c6d76155131b6d81544c6d86055131c7550544c6d56194931a7d91524c69c6454931b5d85524c6db6054931b6181524c69e6414931a
  | 6 => 0xf8800000264858a6c84ca7906c11f8002238b2a8f8a315988480005c11801ea8414116198e26592c14500020ea9895c0000000db0002839358d41f29a90000598a70000000628fc24e17d800000288a921150002189cc03f8b6a910000ee00880000004580012300018e85d9539c180006f8000970000bd9950f19d90568f00668811e41c31d209788a1088cd8ce9b893b9370178dfa8922308e24121c20a06913e19e8020000260680080b02a040000020000040000e00003403800000004010160000080000100a008000000000200a00900c0140d801000034070020000000300901a0000081001800404807004020000060000000500b0180000d00002c0280000a000024030640000000000000c00c0080400a00000000000060010010000c40c0000000040000700200c09000000060010000080080180100800001004012004008030000000a8080100440c83b00a028000010020000200800600c01801000010138050100040600401e0040000500c068028060040080100400004c0101b000000030070260000280600202800003022004018000040040100502e06c008000140000300a00a010000070180480380d00c000028000000000200c00a088000060080080000001a00c0300c00e0000100000e01005809014008028000100100080501e044048030000040100801c000020030080000a00001c0080c80600a0200180200e09400001008000000090040300000000e0040e008024020008000060180000a0320300100500e000098240000040401700800800017002000008110040000180600001401801008004100060000080080c0060200b8070060100100000200c010000000080000b01e00000001004004010000000100000000e00c0000700e0040400000c008018000080100580c00204c068390000300100801c000020000080040100100600403005000018000080040801e80200c054178010040480580301c00001001006008050020000500000600001c00000004020000000060101501200207c09000068004000010060300100500802c0200001a0040202c03c000000000000029d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a71814310f1d4354843c750d5110f1d43940439798e51d0a5d639474297d8d50d0a5c63543429798e5190a5d639464297d8d5090a5c6354242975875350a5e60d4d42975845350a5e6014d428f9974350b1c53d0d42c714d4350b1c53909429798c5150a5d63145429798f5050a5d63d4142975865310a5e6094c4297d855310a5c6054c428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429798e5110a5d639444297d8d5010a5c63540429d98454cca756115332c715143cca3e64947328f592
  | 7 => 0x983027120c93f80011d1b4035259a1a95f0f39902321a4a6309a9470531319a500028e1c72260c22508000639bd00027c0002530c51aaa11a6514e01698b22a96c05380024ca0b8fb9069e69f610f85b83a0000000128e61290b02899c58001ec80026104d9ba0001eb8000001338000000001679ea00022f29c91400400c0f923695d23c00000019c0d928027e00691c8578ae0f1205a9d1c384903702f10b82b84500000000000000c8000001210000000000a50bd06080006180000011381ca470000000000b58001b58000bea3d24c25c2308fd8a1a859060000001f423a1d99561d60ea1621948ac07b00007a8002609f114b9b1a5b80a80002e9828f40000000c78cc94e9c097899aa8b22d07280007a2149af8000000000000000aa00000f80000010288d0710f811aa6c19c9c695a05028aa2e2430001d38d898d90a80008400022c8000000000001fd2462242980001e580028300e2109c90000000a2800124810000074830a9180027e8fe92786123f8001a7800000279a0e0e007d8e381b1d6a6208189d8920000d200002a20387c8eba0516e8ae8781d7a498b48001c81d40482190df08b95e262a9c0d11d0a6601ba5b2378001be8ba85b1ad82303380014c8001f2240a000fb0672450940000000002548000000002110000000000d29608000000d50000000002338000000001038000bb9590000000000001e02680a000007200000000000025a0000078001be00022b1c21080ce2088519d29099e89e325f14f83681589d19208985e0cc00081da878e100000b8a09258b20000a4a2529a9879531cc8cf9548c10880809ee00000000028e80000000009380000023e80000014a8002329ad00028c92702921f8000000839499159af00000000000001389f00029f8e91311d01c00e0a7812f0da95a92387ea4011c00000018f90c2559988b0a8201f847023a278061d187997198c27d8870050709e7114892a0607b8e31870900f78002269732221dda6916422027f8000a900024f16294407c0221421120de9908469218731330a6a282619ab9f8992a1400f0ef9938ff03d8581701ce1e49f98a59a182292e91b245a3e0261199f3a3495701d20694d9fe8b721d89693d88013494393091608e92d0a38db80000018a8001521e09cd1090000000000f502180000020d0d78fa94f01aa5ea57a6f9749b518a0e1a699569981221798ee878a0116987195b0421b31e9a0191a1601bf25e17917c03d0140640000b904e8d5a550461818099d729600009c0b98cd0eb1a6a0499314086e18385084a2440681e90002318058002811cf2180e980026ba938bb0401b6a43800000042800000185a5d0f30998c5a501cd8002031df80013a29280000000000027a80016b82b0000f49ba99780000013280000013f00018800000009315da8d0
  | 8 => 0x15502e11f0379fa8001281fa17400001c003a1ba529bb8000002818b617ca6d8960b400008c8000a20000000888ad23c8000298ac8001820028000630001c791190e05a03e0ec2538a8800138090a8815284a98100019e1b4a1a1a200000022c04300025d93c00024180025c8170001bc81185d02518f02788218687f80015111d96880000000003111b8dd8268280000001de9b38382730ba0e4a3899594585480000027d1019850e581120b25408f1ef9e826a0e81a2a1691316f8001f491889c8000000000fd1e394600000017e00018d1d58988b18081d48af067a0705f9db80017580023f28d8af8000002998000001f1a0a8000409eb00025100000000014309e0000200000f08000000000150001588b38000000570002950272a00002588000000d800700b00008597f8000000000001848bc9fd9720cf1a015e8bc000263a4490327480012c80000027714d00000004d2391f903ba3980000000014a000025a009d50a817106a00000000026f2101a106593a8001d11ff800290a8f1b29cb8dd136222a20a170189b90241c103b01094c0001768c724b29692f958082a8286e824a1d0c315789b1990d083301907687f03f24910028727b8eaa8c0c496104f9da0560f223301f2569e210400020f0000002159389b7a5a8001e600e9e28c08868b50fe10d91e0b8a8a0ab0001750448bf10480017600000012b92680000023d80000d03ca7b148280a9e8ab80216e1c9a8b8000000f9a9a27a00006b21e88b03985217f09e83a966a7ca47a5602887928481a00017a0002291190000980000cb0002979890d30660da1cf84b80d87d1a0924101231094800077a729ef19a10b08c0b10001a380003600022712b164a679ed8be0e700027406c9f09509998001341f31008000510d9800000163000000000070139800297095800000202a6017a891800000165000000000235a760000000f2a2980000001480000000009ba302700000489aa0fc80000023aa090001ea8000000000f68d182a80000000014000023b0d000019b8000000eda0f97780002f8001b01a88001110aa8001b1000032000212a718000000319488890001e10c294b00023600000000018896d92d9919bfa4d8910540dc16a0001e18000000761051ca9368000d49351bd80024a8e20a601829f0600000160ec82083ea211941970c692005e8000001840a10b30000000e413d117a4e8878000e51801d80000b80758001f02079fb1419c613790a2751f797726729319f0a7a2b9d30ad91715000a1c49f597e9b608321e1808750211aea4a0e7a73a581898cb9479a61830c39ff2570000f583c2352519c51b08000000000000001e780000024f8002709968000e29670018de0c61d89a41109070000bfa6e1ac0000411f816f07e208149268a9da94a7f25f8d61a317d04
  | 9 => 0x5c84c09506da76a9e1020ff9dc8698ca1ab0000b799d8000001ce8000990ed0c892298b80000000016c8620000002958e8916a4224d22d80029b00025204195c80010580009a00029b93c8000000001f500017b0001fb996047a2ea6a99115413906b8011dc0e683588f98616607401e12096d04f0f70c920222f82c00000021222a2130001a58558000851b99f71b821600025905a97080000005506502d0001518000002941de00903423b92e00026b1a70000000000000000002150d710e800052a6680000016901300010d17b88d99b2219261b220d91e90c84b0001ca0c189f8a42991c88ca8d69449e50000c4012000004834a4295fa138002860000000001bc1ed129a868592259ae142a6ea199129f6a380199300c01b724886d24b9df1fc0649eea179738c99659db2640c80fa125246a721078001288d380004e0a99780000862371fe20404421c9ec06f20c29007727880002c9c29c4172955a0996a91005f2759bb12a073a6d16b1680001639a983912a8002850000439ac80013b0001a802da2890f0dca34000068a1b19d0328f61321fc80000006a80008a80000000015ba4818c8ef00013e800277a2480019fa1f1468388001da8000031dd1cb
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xca00bec25ad89c003e42a800003a0000007486c48c5496cc00dac000000e0000de2ad2188414d6d410201e282cac9800b00056ce12003002ae0ac8ba3cb280886048aa445c8ed07a9ab638b49070042e62001c00c60c5e00bc246adc00004a9200a400468200b87c943458a09e78081aa64c1664367626004e228a686c7e0672526e4032a26650000b000101030101020008050a0402170501140101007e04021a0718000c0e0c08010e0602a2ee2a1aa221d187050e5010e8ab88a8a1e65469c35410e32838ecaa2641960d6354842d0706a9ac429e838358d5214b41c18c629284a0d0c7254c535068c382a629a83255c66314941a18e6a90a4a0d2870548525061c382ca19283435c85450f31c1ac8a906598e0d5458854cc706b22a429663431c95410d31a30e0aa08698e0c64149324c686392a82a263461c1541513192ae3320a498d0c74548524c6a4382a429263161c16510931a30e0a08a098f11414c55008790a0a42a8043d04c52154021a2ae329a83a060c639494290287396a729c81439cf5294a40c1ac6a908420651511813110306a9ac4298818554d6114c40934e1b1aa42060d635485210312a92c2290810d5c4654c840930e0b1ca220631511813110388a8ec09888185544604c440e22a2302622069251181311030ca88c098881a4544604c440c22a230262204987058e211030ab1aa310881455c6544c730a1ce5aa0871860c64949328c287396a92a461439d35294a30a1ae42a2861851571151430c306b22a4190618c5446050430c1aa8b10a81861554584540c24d386c8a9061835915214830c8aa4b08a41845571195420c24c382c928861945446050430e22a3b02821861551181410c388a88c0a0861a49446050430c32a2302821869151181410c308a88c0a0861261c16488430c2ac8a8c421861561544400c28ab8ca6a0e418694c6050720a2ae32a2639061a5418131c83882888018241a81844048020d80c2182401061853181418430c2a0c098c2185d4d6110210c2ea8b0861084e276c85208430c298c0a0a218a1486050510a28eaa0a62886146550531443822928298a21641c1414c510c30a83026288648521813144348a08c098a218554d6110010c4aa4b088008615545843004322a92c218021465d4400c010c32ca20060087095210030042c8b888018021a4584400c010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xe000c000140030004124281c00a108058d5188440a10805915188430a118194c6050720a1181950604c720d00521c1414c510e0052504604c510c11655c4400c010d01525c4400c010c1175584400c010e0152584400c010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 6 => packedAt s0K6 (864+((h/16+packedAt s0K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s0K5 (31188+((h/339+packedAt s0K5 (27459+(h % 339)*11) 11) % 1477)*11) 11
  | 4 => packedAt s0K4 (56038+((h/448+packedAt s0K4 (51110+(h % 448)*11) 11) % 1776)*12) 12
  | 3 => packedAt s0K3 (5784+((h/37+packedAt s0K3 (5488+(h % 37)*8) 8) % 135)*8) 8
  | 2 => packedAt s0K2 (615+((h/3+packedAt s0K2 (600+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 2 => 0xf07fffe0fffffff81f07fc3ffe1fffff463c7f
  | 3 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x210c08c42890400165098044c022425818d1b1
  | 2 => 0x44109102412221280a422429121494a1422446
  | 3 => 0xa22522481a440652a084ca8265412a0a854a98
  | 4 => 0xcb59c4929076ab9cd3d06223b9980c33e80f60
  | 5 => 0xc61871ce38733e71ce77330311030c3f7b000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36276
namespace PEqualNP.Outside.L_meta_36276
open PEqualNP.Outside.L_meta_36276.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x80046002a000bf43bd43be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x40270a0a1e610030
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => packedAt s1K4 (104+((h/2+packedAt s1K4 (96+(h % 2)*4) 4) % 11)*4) 4
  | 3 => packedAt s1K3 (57+((h/1+packedAt s1K3 (54+(h % 1)*3) 3) % 5)*2) 2
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3fffc0fffffe0c1ffffe0fff07fffe00f3f3fc
  | 2 => 0xc1ffff03f07fffe0f83ff0fff8780fff4c7ccf
  | 3 => 0xfe0ffffc007fffff003fff0fff800fff8f8f0f
  | 4 => 0xfffffff800fffffc0000ffffff003f00ff0
  | 5 => 0xfff0000000000ffffffffff000000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x84204628a0101005284e0113008a621811b15c
  | 2 => 0x94448a1904a484a05a1290a54850a4a94454c5
  | 3 => 0x8a914406949094b04252a0a950149528a8b0a
  | 4 => 0x294e20924c0dae729681888ce6658063e00ea0
  | 5 => 0x318c38e38e71cf9ce739ccc0c4460183ff6000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaaf000faaafaa0faaaf000faaafaa0faaaf000faaafaa0faaaf000faaafaa0faaaf000faaafaa0faaaf000faaafaa0faaaf000faaafaa0faaaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36276
namespace PEqualNP.Outside.L_meta_36276
open PEqualNP.Outside.L_meta_36276.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x20f710f510
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (34+((h/1+packedAt s2K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfe03ffc0fffffe07fe0ffe07ff07fffd8f1e3f
  | 1 => 0x3ffc0fff01fc0ff83ff07ff81ff83e02f3e3cc
  | 3 => 0x3ffffffffe000fffc0007fffffffc00303fff0
  | 4 => 0xc0000fffffffffffffff80001ffffffffc03ff
  | 5 => 0xfffff00000000fffffffffffe0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x82982446244946014a8496a2a3216a98870e15
  | 1 => 0x8429648a1c91565816942aaa8d292c28b362cc
  | 3 => 0x2850c914483a6aaac1084d34d6b5885301b770
  | 4 => 0x21628a2091220934a529010418c611635801aa
  | 5 => 0x31830c38e1c38dc739ce71c700842183eed800
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee00eeaa0000eeeeee00eeaa0000eeeeee00eeaa0000eeeeee00eeaa0000eeeeee00eeaa0000eeeeee00eeaa0000eeeeee00eeaa0000eeeeee00eeaa0000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36276
namespace PEqualNP.Outside.L_meta_36276
open PEqualNP.Outside.L_meta_36276.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x962e401616c02252089aad3a00a876c09e8d3085bac00bc000706c7ae00015994cc841e3e9c033180000000008a33419e3b144922a7e0da3e2680a28745d4801c1409c29221420000001033a84a805c002030608101bda8287785050edca421db54843bba8a85745150abca6215754c429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032b7a92836c52506f4a020de540419f2a6633d54cc6dca598db54b319f2a4633d548c6f4a118de542319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502eca2205d544409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f209f2a4413d54882eca3105d546209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (718+((h/13+packedAt s3K5 (640+(h % 13)*6) 6) % 53)*7) 7
  | 4 => packedAt s3K4 (1875+((h/21+packedAt s3K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 1 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 2 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 4 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x309118a290425014a849d0930194d21886315c
  | 1 => 0x52922864129212816942528510a154a8b284c5
  | 2 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 4 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36276
namespace PEqualNP.Outside.L_meta_36276
open PEqualNP.Outside.L_meta_36276.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x114000000024200192c7c00000000244eac01e003c684004540c3a945000c040132ea40180001507006c29a4c704a2400118b1c8419520100083004040000240000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fb40fe40fd40fc40f840ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fa10fd10f910fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x86503288961800001a9400b2000080003a4e6630004204447664200000007e6a000000003e1c000e6200487224a4268c68000c78228a005e60aa2e560000929828a88e00009c58a29e0006000000001000ac907a40385c12081e52142c3616827c5a00000a4a3c6c6eb04c02ae2a34709a7454a0a68446080401246000850004683121c40012440830008086160019d0616eca321dd54643bd28487795090ef6a0a1de14143bd28485795090abea6a15714d42bba8a85745150af6a0a15e141429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032bb2886575510caf4a0195e54032af29c835d53906f4a120de54241bda82837850506f4a020de540419f2a4633d548c6f4a118de54231bd2806379500c6f4a110de542219f2a0433d54086bca610d754c21bd280437950086f2a3a05e94240bb288817551102f4a8206e95040dd21881b8431037684206e50840f9288817951103e2a2205c54440dd20881b8411027ea8984f15130bb2886175510c27ca9904f55320bb28c417551882f4a9085e15210bca8c213f5444278a8886ed5110bd2a221785444370a8884e15110f9a8a21f241443e282887c8c510f898a21f321443e042885e94010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1801e0000a852e72c18a00041202212a6a6808380900300580c0608318a002127161141439c5865090a3864540318e19150886b26190c40a618d42102b06150840cc90d51103304354440ccd0951103314254440a698e411033151904408e99254443316115110cc15241442d163905109c19541442b1648c510cc1523144330544c510cc15321442b16408510cc15021442d16308510
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x9828010020068839a84a88818498d5190440c20a8b1c8288431761523144218bb0a810a21841516308510
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
  | 4 => packedAt s4K4 (2640+((h/30+packedAt s4K4 (2430+(h % 30)*7) 7) % 119)*8) 8
  | 3 => packedAt s4K3 (998+((h/8+packedAt s4K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s4K2 (302+((h/2+packedAt s4K2 (294+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffc0ffc07e1f830f8fc1ff87f8781f00c79ecc
  | 1 => 0x7ff07ff801ffff00ffe0ff87f801ffcf8e30f
  | 2 => 0x7fffffffffffffff0000fffffffffff00ffff
  | 3 => 0xf80007ffffe003fffffff0007fffe003ff03f0
  | 5 => 0xfffff800000003ffffffffff80000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x3256344714a5570382e953c4bc48d918c38ecc
  | 1 => 0xd28a54890cca5330056b44cc4cc11a68d8a305
  | 2 => 0x2104011220100044900009111112449100545a
  | 3 => 0x4228a22448831999298c6000666588226d03a0
  | 5 => 0x8430c438711c62ee4e318e66000610c3b6f800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfee0fee0f0c0f0c0fee0fee0f0c0f0c0fee0fee0f0c0f0c0fee0fee0f0c0f0c0fee0fee0f0c0f0c0fee0fee0f0c0f0c0fee0fee0f0c0f0c0fee0fee0f0c0f0c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36276
namespace PEqualNP.Outside.L_meta_36276
open PEqualNP.Outside.L_meta_36276.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x8fb40f840
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (34+((h/1+packedAt s5K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe0ffffe03e1f0878f87f8ffffc3c0f008cfecc
  | 1 => 0xff07e1ffc01fff80ff87f1e03fc00ffcf3330f
  | 2 => 0xfff801ffffffffff0007fe003fffffff03c3ff
  | 3 => 0x1ffffe00ffffff800003ffff003fc03f0
  | 4 => 0xfffffe0000000fffffffffffc0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2630d02384a258181a2982a39e2469188456cc
  | 1 => 0x4a5112448ccc49806aa290c4a6608a68b13305
  | 2 => 0x8402448910100229000524090889249102c05a
  | 3 => 0x18a5991228866cd2b33000923332c822dc03a0
  | 4 => 0x10c6001c31188764c446491c000300c36ba800
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfeeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0feeaf0c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36276
namespace PEqualNP.Outside.L_meta_36276
open PEqualNP.Outside.L_meta_36276.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001007fd5007fe54007f55007fc54007fd4c05fe53007f54c05fc5301ffd0c05fe43007f50c05fc43007fd4801fe52007f54801fc5201ffd0801fe42007f50807fc42017fcc801fe32007f4c805fc32007fd4401fe51007f54401fc5101ffd0401fe41007f50407fc41017fcc401fe31007f4c405fc31007fc8401fe21007f48401fc2100ffd4003fe5000ff54003fc5000ffd0003fe4000ff50003fc4000ffcc003fe3000ff4c003fc3000ffc8003fe2000ff48003fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x4420dffcc22106ffc6110837fd308841bfe1844206ffc822106ffc4110837fd208840dfe1044204ffc4221027fc2110813fd1088409fe0844200ffd9521005feca90803fe65484137f32a4200ff59521005faca90803fc65484137e32a4200ffd9121005fec890833fe64484077f3224200ff59121005fac890833fc64484077e3224200ffd5121067fca890803fd5448419fe2a24200ffd8d21005fec69082ffe63484057f31a4200ff58d21005fac69082ffc63484057e31a4200ffd4d2105ffca690803fd5348417fe29a420cffd0d2105ffc8690803fd4348417fe21a4200ffd4921037fca490803fd524840dfe292420cffd0921037fc8490803fd424840dfe212420bffcc921037fc6490803fd324840dfe1924200ffd4521027fca290803fd5148409fe28a420cffd0521027fc8290803fd4148409fe20a420bffcc521027fc6290803f63148401fe98a4200fd4c521027f8629081bff214840dfb90a4204ff88521027dc429082bff60484157fb02420aff9812100dfcc09082bfd60484157eb02420aff1812100df8c09082bff5048415ff282420aff54121057f8a09082bff4048415ff202420aff50121057f8809082bff3048415ff182420aff4c121057f8609081bff2048415ff102420aff48121037f84090813ff1048415ff082420aff44121027f82090813ff65084097fb284204ff9942104dfcca108137e65084013f3284204ff59421005faca108137d65084013eb284204ff19421025f8ca10813ff64084097fb204204ff9902101dfcc810813be64084075f3204204ff59021005fac810813bd64084015eb204204ff19021025f8c810803ff5408411ff2a04200ff55021047f8a810813ff63084097fb184204ff98c21015fcc610813de63084056f3184204ff58c21005fac610813dd63084016eb184204ff18c21025f8c610803ff530840fff2984200ff54c2103ff8a610823ff430840fff2184200ff50c2103ff8861081afe620840dffa904206ff94821037faa41081bfc520840dffa104206ff90821037fa841081bfc420840dff9904206ff8c821037fa641081bfc32084097f3084204ffd4421027fca210813fd5108409fe2884204ffd0421027fc8210813fd4108409fe2084204ffcc421027fc6210813fd3108409fe1884204ffc8421027de4210813fe2108409fb1084204ff48421027da421081bf52108409ffb004204bfd8021027fcc010806fe6008409fd3004201be98021027fac010816fd6008409fcb004200be58021027f8c010806fc600840bffa804205ff9402102ffaa010817fc500840bffa004205ff9002102ffa8010817fc400840bff9804205ff8c02102ffa6010817fc300840dff9004206ff88021037fa401081bfc2008409ff8804204fdc4021027fc2010813fd100840bfa8804204ff04021
  | 1 => 0x3dd324c405fe1926202bfd8531007fea298813fe514c401fea8a6204ff145310a7fe8298813fe414c401fea0a6204ff10531017fe629880bf7314c409ff18a6204f78c531027f86298813dc314c405fa18a6202f50c53109ffec09884eff604c427ff3026201bf9813109ffac09884efd604c427fe3026201bf1813109ffea09884ffe504c427fea826213ff1413109ffe809884ffe404c427fea026213ff10131017fe609880bfe304c405fe9826202ff0c13109ffe409884ffe204c427fe9026213ff08131027fe209884ff7104c427ff0826213ff4413109fea2098813fc104c40dffb2e4206bfd9721037fccb90826fe65c840dfeb2e4200bf59721037f8cb9081afc65c840dffb264206bfd9321037fcc99080efe64c840dfeb264200bf59321037f8c99081afc64c8401ffaa64212ff95321007faa99084bfc54c840dffb1e4206bfd8f21037fcc79080afe63c840dfeb1e4200bf58f21037f8c79081afc63c8401ffa9e4211ff94f21007faa790847fc53c8425ffa1e4211ff90f21007fa8790847fc43c840dffa964206ff94b21037faa59081bfc52c840dffa164206ff90b21037fa859081bfc42c840dff9964206ff8cb21037fa659081bfc32c8401ffa8e4204ff94721007faa390813fc51c8425ffa0e4204ff90721007fa8390813fc41c8423ff98e4204ff8c721007fa6390813fc31c840dffb064206bfd8321037fcc190806fe60c840dfeb064210bf58321037f8c190806fc60c8421ffa864210ff94321087faa190843fc50c8421ffa064210ff90321087fa8190843fc40c8421ff9864210ff8c321087fa6190843fc30c840dff9064206ff88321037fa419081bfc20c8409ff8864210fdc4321087fc2190843fd10c8421fa8864204ff04321027fecb10812ff6588409ff32c4209bf99621027facb10802fd6588409fe32c4204bf19621027fec910812ff6488409ff3244203bf99221027fac910802fd6488409fe3244204bf19221007fea91083ffe5488401feaa4420fff15221027fec710812ff6388409ff31c4202bf98e21027fac710802fd6388409fe31c4204bf18e21007fea71083bfe5388401fea9c420eff14e2107ffe871083bfe4388401fea1c420eff10e21055fac510803ff528840dff2944200ff54a21037f8a51083fff428840dff2144200ff50a21037f8851083bff328840dff1944200ff4ca21037f86510812fe6188409ffa8c4204ff94621027faa310813fc5188409ffa0c4204ff90621027fa8310813fc4188409ff98c4204ff8c621027ec6310813fd3188401fa98c4204ff0c621027fe4310813ef218840dfb90c4204ffd8221025fec110813fe60884037f3044204ff5822106dfac110813fc60884037e304420dffd422106ffca110837fd508841bfe284420dffd022106ffc8110837fd408841bfe2
  | 2 => 0x4101ffea8a080ffe5450407feaa28203ff15141007fec6a0802ff6350431ff31a8202bf98d41007fac6a0863fc63504057e31a8200ffd4d410c7fca6a0803fd5350431fe29a8203ffd0d4101ffc86a080ffd4350407fe21a8200ffd8941005fec4a0803fe6250401feb128200ff18941035f8c4a0803ff5250401ff2928200ff54941007f8a4a080fff4250407dfa128203ff9094101ffa84a0803bd4250407fe2128218ffcc941007fc64a0803fd3250431fe1928203bfd8541007fea2a0813fe5150401fea8a8204ff1454101ffe82a080ff74150409ff20a8204ef90541027f882a0813bc4150407fa20a8218ffcc541027f862a085fff605042f7fb028217ff9814100dfcc0a085ffd605042f7eb028217ff1814100df8c0a085fff505042fff2828217ff541410bff8a0a080fff4050407ff2028203ff5014101ff880a085fff305042fff1828217ff4c1410bff860a085fff205042fff1028217ff481410bff840a0813ff105042ffb8828217ff841410bffa20a085ff51050409fe0828204ffd9631025fecb18813fe658c4137f32c6204ff59631005facb18813fc658c4097e32c6204ffd9231025fec918813fe648c4077f3246204ff59231005fac918813fc648c4097e3246200ffd52310b7fca918803fd548c42dfe2a46202bf58e31017fea71880bfe538c405fea9c6202ff14e31017fe871880bfe438c405fea1c6202ff10e31027fec518813fe628c40d7f3146204ff58a31005fac518813fc628c401ffa946200ff94a31007faa518803fc528c42dffa146200ff90a31007fa851885bfc428c405ff9946202ff8ca31017fa651880bfc328c4097f30c6204ffd4631027fca318813fd518c409fe28c6204ffd0631027fc8318813fd418c409fe20c6204ffcc631027be631880bf7318c409fe18c6204fd0c631027fec118812ff608c409ff3046201bf98231027fac118856fd608c409fe3046201bf182310affea118857fe508c42bfea846215ff142310affe8118857fe408c42bfea046215ff10231017fe611880bfe308c405fe9846202ff0c2310affe4118857fe208c42bfe9046215ff08231027fe2118813f7108c409ff0846204ff442310afea2118813fc108c401ffb2a6200bfd9531007fcca98826fe654c401feb2a6200bf59531007f8ca98826fc654c401ffb226200bfd91310a7fcc89880efe644c401feb226200bf591310a7f8c89880efc644c401ffaa26214ff95131007faa898853fc544c4097fb1a6202ffd4d31017fca69880bfd534c405fe29a6202ffd0d31017fc869880bfd434c405fe21a6200ffd8931005fec498803fe624c401feb126200ff18931035f8c498803ff524c401ff2926200ff54931007f8a498853ff424c401ff2126200ff509310a7f8849880bff324c405ef9926202ff8c931017fa649880
  | 3 => 0xeb02a21ebf581510f7f8c0a8806fc6054413ffa82a21eff941510f7faa0a8827fc505443dffa02a21eff901510f7fa80a887bfc405443dff982a21eff8c1510f7fa60a887bfc305443dff902a21eff881510f7fa40a887bfc2054409ff882a21efdc41510f7fc20a887bfd105443dfa882a204ff0415104dfcca28813ff6414409ff320a203bf99051027fac828802fd6414409fe320a204bf1905104ffea8288277f5414413ff2a0a209ff55051006faa828827fc5414409ffb18a204ff98c51015fcc628813fd63144017eb18a204ff18c51025f8c628827ff5314413ff298a209ff54c5104ff8a628877ff4314439ff218a200ff50c510e7f88628813ff6214409ff310a206bf98851027fac428802fd6214409fe310a209ffd485104ffca428827fd5214413fe290a21dffd0851007fc8428803fd421443bfe210a21cffcc851007fc6428803fd3214439fe190a204bf98451027fea2288137f5114409ff288a204fd94451027faa2288137d5114413faa88a204ffd0451027f88228813ff3114409fe188a204ffd8051025fec028813fe60144037f300a204fe9805100df4c028813fd60144377eb00a204fe58051005f2c028813fc60144037e300a209ffd405104ffca02886f7e5014413fea80a209ff1405104ef8a02886fff4014437ff200a21bff500510dff8802886fff3014437ff180a21bff4c0510dff8602886fff2014437ff100a21bff480510dff84028813ff1014409ff080a204ff44051027f82028813ff65904097fb2c8204ff9964104dfccb20813fd65904017eb2c8204ff19641025f8cb2080efd6490407ffaa48203ff9524101ffaa92080ffc5490409ffb1c8204ff98e41015fcc720813fd63904017eb1c8204ff18e41025f8c720803ff5390435ff29c8200ff54e410d7f8a72080fff4390407ff21c8203ff50e4101ff88720813ff6290409ff3148206bf98a41027fac520802fd6290409fe3148200ffd4a41007fca520803fd5290401fe2948203ffd0a4101ffc852080ffd4290407fe214821affcca41007fc6520803fd3290435fe1948204bf98641027fea320813fe5190409fea8c8204ff14641027fe8320813bf4190407fba0c8204ff10641027e88320813ff3190409fe18c8204ffd8241025fec120813fe60904037f3048204fe9824100df4c120813fd60904337eb048204fe58241005f2c120813fc60904037e3048219ffd42410cffca120867fd5090433fe2848203ffd024101ffc8120867be4090407fea048203ff1024101f788120867ff3090433ff1848219ff4c2410cff86120867ff2090433ff1048219ff482410cff84120813ff1090409fb8848204ff84241027fa2120867f51090409fe0848200ffd9541005fecaa0803fe65504137f32a8200ff59541005facaa0803fc65504137e32a8204bfd91
  | 4 => 0x80efe64d4413feb26a200bf5935104ff8c9a880efc64d4413ffaa6a209ff9535104ffaa9a8827fc54d4413ffb1ea209ff98f51015fcc7a8827fd63d44017eb1ea209ff18f51015f8c7a8827ff53d4413ff29ea209ff54f5104ff8a7a889bff43d444bff21ea200ff50f5112ff887a8827ff62d4413ff316a206bf98b5104ffac5a8802fd62d4413fe316a209ffd4b5104efea5a8827fe52d4413fea96a200df54b5104ff8a5a889bff42d4401ff216a200ff50b51137f885a8897ff32d4401ff196a200ff4cb5112ff865a889bff41d4409fe20ea225ffcc751027f863a8827ff60d44137fb06a209ff9835100dfcc1a8827fd60d44497eb06a209ff1835100df8c1a8827ff50d4413ff286a209ff5435104ff8a1a8893ff40d4449ff206a224ff50351127f881a8893ff30d4449ff186a224ff4c351127f861a8893ff20d4449ff106a224ff48351127f841a8813ff10d4449ff086a224ff44351027f821a887afd6594409ffb24a204ff9925101dfcc928813fd64944017eb24a204ff19251025f8c928827ff5494401bfaa4a223ff95251007faa9288037d5494413fe2a4a204ffd8e51027fcc72880afe6394409feb1ca200bf58e51027f8c728812fc6394413ffa9ca222ff94e51007faa728827fc5394447ffa1ca222ff90e51007fa872888bfc4394409ffb14a204ff98a51035fcc528813fd62944017eb14a204ff18a5104ffea528803fe5294401fea94a209ff14a5111ffe8528803fe4294401fea14a223ff10a51117fe6528803fe3294401fe994a222ff0ca51025fcc328813ff5194409bfa8ca209fdd4651027fe8328813fc4194409ff98ca204ff0c651027fec128812ff6094409ff304a201bf98251027fac128886fd6094409fe304a201bf1825104ffea128887fe5094443bf284a221ff5425104ff8a1288877c5094443ffa04a221ff9025110ffa8128887fc4094443ff984a221ff8c25110ffa6128887fc3094443ff904a221ff8825110ffa4128887fc2094409ff884a204fdc4251027fc2128813fd1094443fa884a204ff04251007fec8a8802ff6454441ff322a203bf99151007fac8a8883fc64544077e322a209ffd5151107fca8a8803fd5454413fe2a2a200ffd8d51005fec6a887ffe63544057f31aa200ff58d510fff8c6a880afc6354413ffa9aa21fff94d51007faa6a8827fc5354441ffa1aa21fff90d51007fa86a887ffc4354401ffb12a200bfd8951007fcc4a8803fd6254401fe312a206bf1895104ffea4a88037f5254401ff292a200ff54951006faa4a8827fc5254441ffa12a200ff90951007fa84a8883fc425443fff992a200ff8c951007fa64a887ffc3254413ffa8aa209fdd4551027fca2a88137e5154441ffa0aa204ff105510fffe62a8813fc315443dffb02a21ebfd81510f7fcc0a8806fe605443df
  | 5 => 0x4942007faa4a101bfc5250807ffa128403fbd0942037fc84a101bbe425080dfe2128406ef1094201fd884a10b3ff325080dfe1928400ffd8542005fec2a1003fe6150801feb0a8400ff18542025f8c2a100fff4150807dfa0a8403ff10542167fe62a10b3fc3150857ffb02842bbfd814215ffcc0a1006fe6050857feb02842bbf5814215ff8c0a1006fc6050857ffa82842bff9414215ffaa0a10affc5050807ffa028403ff9014215f7c80a100ffd4050807fe2028403ef1014215ffe60a10affe3050857fe982842bff0c142037fe40a10afef2050857ff102842bff4814215fda40a101bfc2050857ff882842bff8414215ffa20a10affc105080dffb2c6406bfd9632037fccb19026fe658c80dfeb2c6400bf59632037f8cb1901afc658c80dffb246406bfd9232037fcc91900efe648c80dfeb246400bf59232037f8c91901afc648c801ffaa4642aff95232007faa9190abfc548c8057eb1c6402ffd4e32017fca71900bfd538c805fe29c6402ffd0e32017fc871900bfd438c805fe21c6406bf98a32037fea51901bfe528c80dfea946406ff14a32037fe851901bfe428c80dfea146406ff10a32037fe651901bdf328c805f79946406ff0ca32037d8651901bff618c80dff30c6404bf98632037fac319002fd618c80dfe30c642affd0632157f8831900bff318c805fe18c6406ffd8232035fec11901bfe608c8037f3046406ff5823214dfac11901bfc608c8037e3046429ffd423214ffca1190a7fd508c853fe2846429ffd023214ffc81190a7fd408c853fe2046402ffcc232017fc611900bfd308c805fe1846406ffc8232037fc411901bfd208c80dfe1046429ffc423214ffc21190a7fd108c853fe0846400ffd9532005feca99003fe654c8137f32a6400ff59532005faca99003fc654c8137e32a6400ffd9132005fec8990a3fe644c8077f3226400ff59132005fac8990a3fc644c8077e3226400ffd5132147fca899003fd544c851fe2a26406bfd8d32017fea69900bfe534c805fea9a6402ff14d32017fe869900bfe434c805fea1a6402ff10d32015fec499003ff524c80dff2926400ff54932037f8a4990a3ff424c80dff2126400ff50932037f8849900bff324c805f79926406ff8c932037bc649901bfc324c80dee1926402fb0c932007fec299002ff614c801ff30a6400ff58532007f8c299012fc614c851ffa0a6428ff10532017fe629900bdf314c805fe18a6427ffd813213dfec09909ffe604c8037f3026427ff5813213dfac09909ffc604c8037e3026427ffd413213ffca09909ffd504c84ffe2826427ffd013213ffc809909ffd404c84ffe2026402ffcc132017fc609900bfd304c805fe1826406ffc813213ffc409909ffd204c80dfe1026427ffc413213ffc209909ffd104c84ffe0826409ffd935104ffcc9a8
  | 6 => 0x5feb02a432bf58152197f8c0a9006fc6054813ffa82a432ff94152196fca0a90cbfd5054813fe282a432df14152197fe80a90cbfe4054865fea02a432ff10152197fe60a90cbfe3054865fe982a432ff0c152037fe40a90cbfe2054865fe902a406ff08152197fe20a90cbfe1054865fe882a432ff0415204dfcca2901bff641480dff320a403bf990520377cc82900ebe641480dfeb20a400bf590520377ac829002bd641480dfe320a406bf1905204ffea829027fe5414813feaa0a409ff15052037fec62901bfe63148057f318a406ff58c52005fac62901bfc631480d7e318a409ffd4c5204ffca629027fd5314813fe298a431ffd0c52187fc8629003fd4314861fe218a406bf98852037fea42901b7f521480dff290a406fb94852037faa42901b7d5214813f6a90a406ffd0852037f8842901bff321480dfe190a406ffd8452037fcc229012fe611480dfeb08a400bf58452037f8c2290c7ff4114863fe208a430ffcc452187f8622901bff601480d7fb00a406ff9805200dfcc02901bfd601485f7eb00a406ff1805200df8c029027ff5014813ff280a409ff5405204ff8a0290bfff401485fff200a42fff5005217ff880290bfff301485fff180a42fff4c05217ff8602901bff201480dff100a406ff48052037f840290bfff101485fff080a42fff4405217ff8202901bff659080d7fb2c8406ff9964204dfccb2101bfd65908017eb2c8406ff19642035f8cb2100efd6490807ffaa48403ff9524201ffaa92100ffc549080dffb1c8406ff98e42015fcc72101bfd63908017eb1c8406ff18e42035f8c721003ff539085dff29c8400ff54e42177f8a72100fff4390807ff21c8403ff50e4201ff8872101afe629080dffa948406ff94a42037faa52101bfc529080dffa148406efd0a4201fde852101bfc429080df62148406ffcca42037f8652101bff619080dff30c8404bf98642037fac321002fd619080dfe30c8403ffd064201ff883210bbff319085dfe18c8406ffd8242035fec12101bfe60908037f3048406ff5824216dfac12101bfc60908037e304842dffd424216ffca1210b7fd509085bfe2848403ffd024201ffc812100ffd4090807fe204842dffcc24216ffc61210b7fd309085bfe1848406ffc8242037de412101bfe209080dfe904842dfb48242037f841210b7ff109085bff084842dff4424216ff82121003ff65508017fb2a8400ff9954204dfccaa1003fd65508017eb2a8400ff1954204df8caa101aff6450807ffaa28403ff9514201f7ca8a100ffd5450801deaa28403ff15142007fec6a1002ff6350859ff31a8402bf98d42007fac6a10b3fc63508057e31a8400ffd4d42167fca6a1003fd5350859fe29a8403ffd0d4201f7e86a100ffe4350807fea1a8400ef50d4201ff886a100eff6250801ffa928406ff9
  | 7 => 0xa18efff5050c77ff282863bff541431dff8a0a180fff4050c07ff2028603ff5014301ff880a180bff3050c05ef9828602ff8c143017fa60a18efdd3050c05fe182863bffc81431dffc40a18effd2050c77fe102863bffc41431dffc20a18effd1050c77fe0828609ffd935204ffcc9a900efe64d4813feb26a400bf5935204ff8c9a900efc64d4813ffaa6a409dfd535204ffca9a9027fd54d4801beaa6a409ff1535204ffec7a9027fe63d48057f31ea409ff58f52005fac7a9027fc63d48057e31ea409ffd4f5204efea7a9027fe53d4813fea9ea400df54f5204ff8a7a90ebff43d4873ff21ea400ff50f521cff887a90ebff42d480dfe216a439ffccb52037f865a9027ff61d4813ff30ea404bf9875204ffac3a9002fd61d4813fe30ea43affd07521d7f883a90e7ff31d4873fe18ea409ffd835204dfec1a9027fe60d48037f306a409ff583521c5fac1a9027fc60d48037e306a409ffd435204ffca1a90e37e50d4813fea86a409ff1435204ef8a1a90e3ff40d4871ff206a438ff503521c7f881a90e3ff30d4871ff186a438ff4c3521c7f861a901bff20d4871ff106a438ff48352037f841a90e3ff10d4871ff086a438ff443521c7f821a90cafd659480dffb24a406ff9925201dfcc92901bfd64948017eb24a406ff19252035f8c929027ff549486fff2a4a400ff5525204ff8a92901bff639480dff31ca402bf98e52037fac729002fd639480dfe31ca406bf18e5204ffea7290dbfe5394801fea9ca409ff14e521bffe87290dbfe4394801fea1ca436ff10e52035fcc52901bff529480dbfa94a409fbd4a52037fe852901bfc429480dff994a406ff0ca52037fec32901bfe61948097f30ca406ff58652005fac32901bfc619486fffa0ca437ff106521b7fe63290dbfc319480dffb04a406bfd8252037fcc129006fe609480dfeb04a435bf58252037f8c129006fc6094813ffa84a435ff942521affaa129027fc509486bffa04a435ff902521affa81290d7fc409486bff984a435ff8c2521affa61290d7fc309480dff904a406ff88252037fa412901bfc209486bff884a435ff842521affa21290d7fc1094801ffb22a400bfd91521a7fcc8a900efe6454801feb22a434ff1915201df8c8a9027ff5454801bfaa2a434ff95152007faa8a90037d5454813fe2a2a400ffd8d52005fec6a90cffe63548057f31aa400ff58d5219ff8c6a900afc6354813ffa9aa400dfd4d5219ffca6a9003fd5354801bea9aa409ff14d521a7fe86a90cffe4354801fea1aa433ff10d5204ffea4a9027ef525480dff292a406df949521a7fe84a901bfc4254867ff992a406ff0c952007fec2a9002ff6154801ff30aa400ff58552007f8c2a9012fc6154869ffa0aa434ff1055219ffe62a90cffc3154865ffb02a432bfd8152197fcc0a9006fe605486
  | 8 => 0xfd4154207fca0aa103fd5055081bea82a809ff1415401ffe80aa00ffe4055007fea02a803ff10154207fe60aa103fe3055081fe982a840ff0c154207fe40aa103fe2055081fe902a840ff08154207fe20aa103fe1055081fe882a840ff04154015fccba9827ff64d4c13ff326a603bf9935304ffac9a9802fd64d4c13fe326a603bf1935304ffea9a98277f54d4c13ff2a6a609ff55353006faa9a9827fc54d4c057eb1ea602ff94f53016fca7a980bde53d4c05af29ea602ff14f53016f8a7a980bff43d4c05ff21ea602ff10f5304ffec5a9827fe62d4c0d7f316a609ff58b53005fac5a9827fc62d4c7fffa16a63fff10b53017fe65a980bfc32d4c13ffb0ea609ff98753025fcc3a9827fd61d4c017eb0ea609ff187531fffe83a98fffc41d4c05ff98ea602ff0c75304ffec1a9826ff60d4c13ff306a601bf9835304ffac1a98fafd60d4c13fe306a601bf1835304ffea1a9827fe50d4c13fea86a609ff143531f7fe81a98fbfe40d4c7dfea06a63eff10353017fe61a980bfe30d4c05fe986a602ff0c3531f7fe41a98fbfe20d4c7dfe906a63eff083531f7fe21a98fbfe10d4c7dfe886a63eff04353015fecaa9803ff6454c017fb22a63dff9915301dfcc8a9803fd6454c7bfe322a603bf1915304ffea8a98037f5454c7bff2a2a600ff55153006faa8a9827fc5454c057fb1aa602ffd4d5304fbea6a980bfe5354c05bf29aa602ff14d53016f8a6a980bdc5354c05ffa1aa602ff90d53017f886a9803ff6254c017fb12a600ff98953007fac4a9803fc6254c0d7e312a63dffd09531eff884a980bff3254c05fe192a600ffd8553005fec2a9803fe6154c01feb0aa600ff18553025f8c2a98f7ff4154c7bfe20aa602ffcc553017f862a98f3ff6054c797fb02a63cff9815300dfcc0a98f3fd6054c797eb02a63cff1815300df8c0a9827ff5054c79ff282a63cff5415304ff8a0a98f3ff4054c79ff202a63cff501531e7f880a980bff3054c05ff182a602ff4c153017f860a98f3ff2054c79ff102a63cff481531e7f840a98f3ff1054c79ff082a63cff441531e7f820a9803ff6550c017fb2a8600ff9954304dfccaa1803fd6550c017eb2a8600ff1954304df8caa180aff6450c07ffaa28603ff9514301f7ca8a180ffd5450c01deaa28603ff15143015fec6a180bff5350c05ff29a8602ff54d43017f8a6a180bff4350c07efa1a8602ff90d430177c86a180bfc4350c05de21a8602f710d43007fec4a1802ff6250c01ff3128600ff58943007f8c4a181afc6250c07ffa128603efd094301ff884a180bff3250c05fe1928600ffd8543005fec2a1803fe6150c01feb0a8600ff18543025f8c2a180fff4150c07fe20a8602ffcc543017f862a18efff6050c777fb02863bff9814300dfcc0a18effd6050c777eb02863bff1814300df8c0
  | 9 => 0x2002001000400100000100020000018004000005006000800000000000040000010000000000001001000000c00600000040000030008000000001000000000200600080200020000010000000000001800c00200100000100100030010000002001007800000200000a000400000100000080080050000000000004001000400c001000803c000000003800400a0010000000000000000801800800a0018000000000000800c0020010000000004000001000000800200000000000030038004002002004000800200000000040060060000004006001000001000000000080000060000018004008001000000c002002000800800000000080000040000008000002000001000000000000000000080010018008000001000001c000003000000800c001000800000200000300040000000000004004000000000000000000000100160000008000004000000001800000000000380060000000000002001000800c0000000000000000006000803400000200100080040060020010000000002000400000200280080000060010008000007000000000000800000040040020000004006002000001400a001000001000400200000efe65d50077eb26a803ff9535401efca9aa00fbe54d50079f2a6a803ff1535401ef8a9aa027ff63d5013ff31ea802bf98f5404ffac7aa002fd63d5013fe31ea802bf18f5404ffca7aa027fc53d5007ffa1ea803ff90f5401ff887aa027ff62d5013ff316a806bf98b5404ffac5aa002fd62d5013fe316a803ffd0b5401ff885aa10fff32d5087fe196a809ffd875404ffcc3aa012fe61d5013feb0ea800bf5875404ff8c3aa00fff41d5007fe20ea843ffcc75421ff863aa027ff60d50137fb06a809ff9835400dfcc1aa027fd60d50857eb06a809ff1835400df8c1aa027ff50d5013bfa86a809ff9435404ffaa1aa10b7d50d5013fe286a803ffd035401ffc81aa00ffd40d5007fe206a842ffcc354217fc61aa10bfd30d5085fe186a842ffc8354217fc41aa10bfd20d5085fe106a842ffc4354217fc21aa10bfd10d5085fe086a803bfd955401dfec8aa00fff5455013dfaa2a803ff9515401efca8aa00ffc5455007be2a2a803ef15154007fec6aa002ff6355083ff31aa802bf98d54007fac6aa107fc63550057e31aa841ff94d5404ff8a6aa00fff4355007dfa1aa803ff90d5401ff886aa003ff62550017fb12a800ff98954007fac4aa003fc625500d7e312a803ffd095401f7e84aa00ffc4255083ff992a841ff0c954007fec2aa002ff6155001ff30aa800ff58554007f8c2aa012fc6155007ffa0aa803ff1055420ffe62aa107fc3155081ffb02a840bfd8154007f6c0aa002fb6055081ff302a801bf98154207fac0aa102fd6055081fe302a801bf18154207f0c0aa006f86055013ffa82a840d
  | 10 => 0x26e000000000000000009c40000000b280005f90000c1c25c00013f9a74000705000000062c0140000e5800000000000002060000811f180002532450000e900000000424c8c5d626000006382664210000000227000000092c6b22d00b7cace2ea08a80d80007012dd0bbd01200000000008681353c70000c0a5f30000000f203902258000000839000000076057b1f200002187b14229ca400075500000000000000000e74cc800000000000000c40a88000d06000000000000000003d800000000000000007726411e8000000017f38100000005ad0001b3800000000000000000000000cd408200000007d44880001a6000000000010000000b000000000000007f8000189466800008992d400077039420700006ed00006d80006f215e85e0000585000000000039f0001ce804400013a00000005970000000003002001c000000001000000400c000000000200300680040000000040000006001000000c0000000000000000000000001800600400000000140000010000000000000000c0040000008000000000002000400000000000000060080000004004000000000000a00000000000000000018000008000000000400000000000300160000018000004000001001000000300200040000000010004000000000000000000000000100000030008000006003001000400200000000140000000008000002001000000c010001000001000e0020008008000000000001400e004001800400000100180040060000010004002005000001c006002001001400000100280040040000000000000000000000000a000000800400a0030000004004000000000400800300000000080020020000000003000000000a0010010008000000000000000000a0028000000000000000000200a0008008000002000801400200000000000000010008004002000000800000200100100040000000000004000001000001800200000180000000010000004002005000000000400100080000080000000000000001000800401a000000800000200000080000020000010000000000001000000c0030000000000005001000000a000001000000000000180100000010000000000000000800000000000000100000040000000004000000000800200000000000040080010000002000000000c0060000000004000005002800000400200000000000010008008012001000000000e006000000c00600000000040000000008018002000001000000600300080040000040020030000000000800000000c0008000002002000000c00000200100180020000000008000001000800000400100180000020020000004006000000000c00000000080000020010000000000000003800000e00000080000020010018000000000001800400600000080100
  | 11 => 0xe2879c41100005cc00000000000004ca0004098cac2940250ba9fb4a5e5883fe02647ae38905880004300000000000000000000000000000000011fc9307233c99d9c0a06772898000dec62c3ca000000000000000000000000000000000000000000000000000012dc89a1072d3821000072a0001a780187ff00000003d02da39f80006f000019c80c4000000051041800083a0d295bc0000001409b84f380ce000093c41000030800003e43be2658000a4455f0000e844560003e6828000031a28f800066638c0e9042c0000000000000000000000078c00000002d000000000000003080000000000c900000000000b0000000000000000000000001af8c606a100004ec6400000000000fe000000009780000000000b88b3200000014e80000000000000da60003ad80002101f101217e00005700000000000000000208800000000000000000003648000d840000b900000000000001f68000000000000000068c00005d014e6e400000000000000001e009620003da89ec4d400023c8ba00000000001c54000000000000000000004e00002d000013d00000001fc00000000000000000f6c00000000000000005a5000000000000008d00000003e200005d87363dc09380000008150cc000083c0000000000000000000000000041d37e0bc400000038e000011000000000000000000001a180003f200016c80000000001d3c00030c00000000003ea00000008bc39500013440000000001538a124f13f288a4000000000000000000000004440005a12f11c9c00027c000140800041000000000002430000000c844d8000000000000007980000004a6331000101c0003cb8000000000224135cdca00000000000005f6000111c0007fd0a20bec0000000000ac00000001f89924b6e33e0000060cbc5500000464000000252800000000000012380000000000d2000000004007d8016796095980c2b404d1ad0da8bbc69610886f8cf84953df9a80a4800021e9abcb520002d1000038a5d83e48000e3440400006fc00055e00000000000000000000032515000107000044a0000000000000000000061a41b42313640000004118000ed80001950a804680000000000a4c00000000000007fb40907341ba5300270000000529000059451460f0000000000000022800000000031785dc0000002d40000ee600038ba03c0006310001e2000000016e8000b7c00004b815c57252a0001b740007250000000a660002c4919c1220160000b5000000000000005b60002fd00000006273ef00005aa00000008080008260000750b2c51d1bb000000008110210650480002cf8000e640002d991f80006c4319800000038500000000000000000000d5638b1c68000d760001c300000002e3000000002e7d80000000fde427000000000000000014f00000
  | 12 => 0x3de899c6fa3c03318a24b8e7af013000000c000189000000000000000000000002c00d740001991ea80000000000650000c7e00035380000006c70ae0158ccc000000000000000023c0414aae0bf38f80000002c412c07a839872f30e8000e0800036b11a800000000018840000f90000000c3c5dc139000000050a0d3031c0006b905b80000005453f6000000000000007cc0000001049e5468a0b527709bc8d255237c8000d906ef0000000000000000115c5ec00020000000007fa312000000000009c000000000000005a480a000270800000000026380803420000c310245620000d6800069e000000000106e00000000000001ba2320000000000000000000000018000000000000000000000000000000077400001700009d80001ea000097436b20b1b3000019a0000000000023000000043600031680000001371a680840000b3000120025800000000000007df00189e0bd68020000000d4a74a00002f0d3e1df000000000078731499d40007c70001d2c85250c1359ce00000000001250bc200006f0000000000000155400000017c0000000011123083cd66000000000000012500000000000740001d1cc1c62e3f005080000000001d4c0006e2000000000000037500000002bc159916c000564000123ccf63a30000000000000109039c07073e1f00000000000000000000000000005bc00000000000006e840d00000007be43e00000000005e30948f34000000389977400000000000000000000000db09ac00000000000000000000000000194365059ceb80000000000000000000000000014726403d00001f022d00000000000000b1c0000000000c2800000000000006280ed327151c00000000400000006cf1110118b4652120615ac7ce0000f0800034650406f996c000000000000000000012a0000ad2000000000000054117f00007c25aa39c95682785bd2df9629018000000000107800040b00000004650001fa40000001d780000000000a580002ac00037a8000e1e000000000000000000000000000000000aac82e0070000000000000000000000000000000000fc2fa000070c0000000000218000843000000011a000000000038456c000000102e6e800015a80001792ac8d980000002938000be87781c005b8000000246800000000000000000004f900019000000001070000a5c68e0000000c244372a6000002440100012d8c400921a190d8cd27b721e17ec64652d0001d0c00000000003303da66a0000000000000000000028c00000000000002550000364d5456500000000005b90000fbc0000000000000fae00000020840002d90e220d800047c00019706222c90d6117cce07f93858fd0fe61fb0000b6000000002780000000000000cb808800000000000003cb00000000000001758000dee0003658
  | 13 => 0x40300020640003b40000000000000000000009400000000000000000000d046bc11200000000003930000000d2000000001f0000000000000052c0001cf1ee4000000000000000034e000000000000000016380000003a71c1858400037480009580000001c84f1606f098000000000000007e10687ea1e900007dc19719d00000000ea23d93dc33e0d22f5182c00000000000000005cf000000108000034e1bf498c00009c99f80000003e2000029c000000187c000000000000000000023d000015e3c43958d480e064f14100000005070000000000000000144400000041700000003d900000000000ec000000017a000000000029e0000001e144c0000000000062600000000009d012100000000000001eb000000000000000000006b819600000000000c70000516000000000000000038b0ab800000015c209c00032d000000104a4f20001b402be0cf000000000000034280010280003fa000000000000000000001ae00000000004550001460e0600000000004320001b488807540000000dc400003300011443b621a0d81de448e450414976851c0000e88000000407000000000045c34a8214e987ad0aa0dcc5da6ee3fb1f401ca4711ef01c40007be19c13d0000000328000081c35012018f045028f1491b7800000025f067454a0a128e03700003d321194e44480e40ab80000002150000e48bde01a27180000000000dd80000003b114d80000000000001b340000000001e7c0000003ff00000e40001b01e843ca000000000000050f00006dc000000000000039000000000004600003e908bc00000016400005ce009077954c00048431500a426c6d8000000003668800012a80000ac0000000000000000000000000000002f869242c00000000000000000df00000001cd15700000002cd16bcae277a3510ad80006f40000000054000000000000000000000000000000000b4800035438f1308000000000000000000000000000000002a1800000000032500000000000000dbc0000000e0800000000000000006042cf129000000000012d000007629800003d82200001c186cc0003bf38c1f6c0000003c68000000000000000000060d1e41e3c0003a01fb9cf000000041415603160000000e0400052b00000006444a400010180004460000000f60000000038800000000000000008042229478c0000000000bc00063d0000d5c00015300004008b2000046000000000025194b000006d000000000000036280000000002e5000030e0352e88f9504040b12483f45ae77401904cc0003ac03b1738f9c351000172c00083f34d97c80000001308c789680000000b2c426000000000000066b25e00000000552759f980000001c4178054400000001b800000004c00002820003f41a5000000000000000000003889755088
  | 14 => 0x47d31da80000007862670ddc00000000000000000000001e689422d11280d606e000000020180007090001d040007a43ac000012800029880fc0002bf00000006203d10000000a8c000000000000063b00020f400000000016480007591c100000006bf0000000dd61260000000000000000160c0f00000001cd0f4e00024f00000000001780c940000e300004f80005cd39d9be0eda81124898540001a416e000000000000005c47f800000e0a7c0002f31439b8000027640c000000049d3a28d0000000000001748800ff000000000078c0000000f4a0000000a500003910000e3c3e812f000020c000000000000074c1e225916c0000000000000000000004700000000000000000bda000000000097e39400e800078a3ca38c89a000081d000063cd8c64d2bc000000000032a9f8c00005e11d80002fa00002417b857c00008c19e80000003580000f7010a3478000000309000000000000009506bc23a7cf2e40000000000057114c00000027e800000000000016308a41e700000009be000000000000000000002e4000000000057400060c00009648c20003a10fc02c80003869da82bc0004058000000000273146c43c00000018046a600000000000004130000000af20000ec000000051700008744e2000000153454c00000000000000000001aa02cc0001fd00000007770b8000050065a2d89dfc0fa00000000000000002ce83147640000000274000000000000088800016314dc0003612a4000000000041d910c00061700000000000000000000000660000000001c0000000000ce833c0000000000000000000000054f29f00006f627e0000000eca00000003001dc00025d800052a16d0000000000000000158443e00000000000000000be0000a462f42f4835000065300000008ee68d000156c00059e3a812081127b600000000006a3268000091251431f0000906000032874c000730301048c00000000000000003a700003d4854476000000000069a219122c0004300000a6400000021580000000002ea0000f8600036f9618b36000000000091873700000000000000000450d4c5ab3c500000000003d014ec00000000000000005df0330000f44756000000000018c26d90ec0000000000478cb20003d188fc0005c527380e40000003ab80000005c60000100074593000000053c30f0001df4000575000000044673d1de80000000000ee8f1c00053f08b8ba445a7f127d924caf800018b8000b0870c2618000a68000000000061057e2ce09280000000000000000043000000000000000011080007140001d74cc25d016f1a4400039c35d000000073100000000007ee3dd0a44bf825b00000004c800000000004782e12c38a102b0000151800000000040500000000000000000000000000000071c5942e61334000000000
  | 15 => 0x19a00004701208000ecc14917613e041400000000000000000000614e0054920a02540002ad000000000000016600000000001f9800045820d2f60490db246f3d61a9089e10d3158fd83505511e11d840007aa22700004980000000000000000113072c0005200000da000000000000000006b4000000014c3270001f847f066e35a90d43fa2f52100eec00017b3bf003cc6c616340107c3040000001f880000002fa9bec2980000001c6c2502172578000d084e00000000000000000072800000000000004ae3470000000ac479235b8ea01b600000000006f221404d9fac5ee1a000003e8e403030ea800000000023184e8000000000000000000000000000000000000000ea4422000000074400000000000000002108aec0000001f6027882a7f2000000000000000012b80000000000000000000000000023e00040280000006f03ad0fe4b5c28625400000566c00a416d800000000000000000000000000f5000033c80000001840000778000000000132800000000000000000000001af00006d703b800094e21c04801840000003af8040000000000000000000025c8000000000000000032a0000000840be27240001f5000000000000002c46451fe9d344705e834380000000000bd158cdcc0000f580000002511ffa0f80d20001d700002c2000000000000000003109b05fa45d0000000000000000141478c65f2ff8000000000000000000000000000000006090000000000000000000000000026f103c0000000000c04000000061800000000000000000001cf00000007b006a0000a5c0000002a0000000000002580005f23e918a80010700001561a0461c0c82e097643ac32832b8000170000000171063611b000000000000005b00010060000b198603c00000d11dbc5f8536000000000009a2408000e1c0000001b6c01425d2678d9c4847ae00016d0000000259800009854400000000000002370cbc7c600000020400000003c487e400048703a8fec000000000206caba0000000000f220002780000da20000000000c364862368b94000000000000000042f0000000c1400021c9f28cde54b3fa9cb885c0da1a590e0e6c4e9041000033c2f230a00000008302991b68c5000000000007980000000000f520001cc000000000000000000000000000c14684000000000000068b000000000000033b00003720003da0e940005c30519fdcfa2000303144007c00000000000000000000000b2a0000001a4857416b0001e0c00057d193000091003d35499b40006e7332a0d40007bb40384380000003eb14940005820000000b2200000000000000003ee0000000431321999c6080002c0800023868a0fd0adc0005c20e312880000000000000de200000000000000000000000000000000075c0f20000580000a2
  | 16 => 0x7d8eb44180001b100000000000000000c980000d880006600002390078000000000000000033702a00000003312e4800000000000000000000000001d18e5800000000003540003190634e244601dc00000003ed23405489520000b5000000000000000004ee00000013d49a482a000000067e0d51198000824639341017c03e08a415906905a0003360ea40000000cd80006fc4b035700009d44c500000000004fc000081828600000000000005d30000000c100000000c601485e531a0fa0f96833134856c0000001db8dc815600035b1d5014a000000000000006000017c0eec0003f206f0a1a000000000001a00030e0d182b200000a9c1cebc0000659280000042000186454826d3910000000000000000000000000000000000ad00000000000000000000ac000000015a0000000000000000000026a800000049f0000f0c0000000000d7cf560000000ad04f200000000003520000000000000000248000000047401408b80000000000648c3462300000003a00f73b100004960000000000000637000000084a262361800000036d047801016843f40d07682c02d30000b400007b3201119800000000000001a60000001cd400000000000000000002808fac676538000055400022500007b00000002840000708000000000000000020c000000000000000003221312d31d2400000000000000000e00000000000428000000000002d00008f808e4e509680007ea43a00000000000000000000000000066800000000015497000002e60000000a001e40000e90ae66891578d6c79e781000000038e58b25684040262363258ef00006d500000000000000ce00006ea32900000001820000000d900000001cc80dd05e6bd00000000004c900000000000002a10000ec00000000000acc6dc0000000cb05e6379800000000000000005500340000000bee0fe24283a00ce00002894380000000000ff80000001240000000000384000000067d000000000006b00011d40000d7000043c0006b1216800039c6721b184fc6320002a5184ca500000000bfc000000000082c00000000010980002b512b000013e67f00000001e227003400000007690291dd400000000014d446e5760000000f301f718f8c8460c1ff0360340000000000000000000006b00009de207000200400000000000000780000c180004e663800000006dc000000000000014d000021c00079b00006580000000181a5c0000000da000000000000000010100003e0207cbb600000012acfce0003c200000e62e400080000000001618540b780000001c9800079d2ba000000000000000000000002768d28ba457732a1418c0e0e10f70000afe4b83b201e83b23321cb9e980001e9000093412600000000005101400000000e800000001b50b4846200000006aa00000
  | 17 => 0x2f38000000000000000000000035620c44fa0000000a6800027500013310587d9000000000000000019e000000000000007ba0000000000000000000000000000022c000000022a32215b48a87330000000152000000022c53a0002ff1bb00000001428000000000000000031433611880008140a80000604f6400000014644720000de80008e600000000000000002858b38ca200000000000000000318000000000000000000000027b064c9340001481f203564241ac800079212231d13e80000270dc00000006223a21c4089200014180003cc4d30b605f86fe516146136800000038e80149a835600015b8c2249724c89700002b20000000a0600000000000c851a10180000b6000064800000000000000001540003b70000000556150913000069810280b03fc80037d19587cc0000001374f820000000bb800031d099000031200007e000076c000000000038000000000000000000000000e5a2aa3bd95c822c64810b14f458a05c1ae0d100004c4339800000000023e80000000000000000f0400000000000000000001da0000059000000000000027f80000000000000000000365000000000037a00013903006ad0d9000000000000000000000000000000ec63ab0001b8c00059800000000000d13e616b00000000000000ea20e600012480000000000884c8e00000000004be000000000036a232000000097a81e000000000000016b1e64b700003e2836088200005900000000f0000000000076b4208000000000000000000000034c800000000004b16ec8d877200002ecf3c7c200012708ac6d221989b870e00000000000000003021948616000000080400057a0790640bae00000000000006c10000000000000235800081000000000005c049b02483a47660000000a3400018800017900005fd09e800000000000000000001450000000000000000163c0000000820b3400077100013f8faa0002c6a03400023d00000000000000ee02e80003c137f000000000000000000004c112299c40006ff19e80001d600000100000000000000000000000000000000000000008d4fba00014980005820000f7800000012003f80004c623a127014c1f02a73130f68cba0003851550ef800000000000000000d3800000029c0001a4c0001c941904d018c6350000000b6a7bc2798000b2000000000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7058c2103edf3058c21006de3058c21006dd3058c2103edc3058c21026f71058c21006f51058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c21036df7258c21036de7258c21036dd7258c21036dc7258c21036df5258c21036de5258c21036dd5258c21036dc5258c21036df4258c21036de4258c21036dd4258c21036dc4258c21026df7158c21026de7158c21026dd7158c21026dc7158c21026df5158c21026de5158c21026dd5158c21026dc5158c21026df4158c21026de4158c21026dd4158c21026dc4158c21026df2158c21026de2158c21026d62158c21026dd2158c21036d52158c21026dc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21006df4058c21006de4058c21006dd4058c21006dc4058c21036df2058c21036de2058c21036dd2058c21036dc2058c21026df1058c21026d71058c21026de1058c21026dd1058c21006d51058c21026dc1058c2104cff76d4c21024fe76d4c21004fd76d4c21024fc76d4c2104e7e65d4c210067d65d4c211febe64d4c21006bd64d4c21016de63d4c21006dd63d4c2103f5e53d4c211f6fa60d4c21004ff7654c21024fe7654c21004fd7654c21024fc7654c2104e7e6554c210067d6554c211eebe6454c21006bd6454c21016de6354c21006dd6354c21005ef7254c21035ec7254c21005f77154c21025f47154c211e6fa6054c21004ff7650c21024fe7650c21004fd7650c21024fc7650c210067e6550c210067d6550c2101ebe6450c21006bd6450c21016de6350c21006dd6350c21005f77150c21025f47150c211defa6050c21006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f84358021036fb7258021036fa7258021036f97258021036f87258021036fb5258021036fa5258021036f95258021036f85258021036fb4258021036fa4258021036f94258021036f84258021036fb3258021036fa3258021036f93258021036f83258021026fb7158021026fa7158021026f97158021026f87158021026fb5158021026fa5158021026f95158021026f85158021026fb4158021026fa4158021026f94158021026f84158021026fb3158021026fa3158021026f93158021026f83158021026fb2158021026fa2158021026f92158021026f82158021
  | 1 => 0x94210067f70594210067e70594210067d70594210067c70594210067f40594210067e40594210067d40594210067c40594210067f30594210067e30594210067d30594210067c30594210367f20594210367e20594210367d20594210367c20594210267f10594210267710594210267e10594210267d10594210067510594210267c1059421004ff755902104cfc7559021024ff7459021026bf7459021046be5459021046bc5459021004ff7359021014fe7359021014fc7359021046bf4359021006be4359021046bc4359021034ff7259021034fe7259021034fd7259021034fc7259021036be4259021036bc4259021024ff7159021024fe7159021024fd7159021024fc7159021026be4159021026bc4159021004ff705902100cfe7059021004fd705902100cfc7059021046bf4059021006be4059021006bd4059021046bc4059021026f71059021006f51059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006be5359021006bc5359021036bf7259021036be7259021036bd7259021036bc7259021036bf5259021036be5259021036bd5259021036bc5259021036bf3259021036be3259021036bd3259021036bc3259021026bf7159021026be7159021026bd7159021026bc7159021026bf5159021026be5159021026bd5159021026bc5159021026bf3159021026be3159021026bd3159021026bc3159021026bf2159021026be2159021026bd2159021026bc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bd5059021006bc5059021006bf3059021006be3059021006bd3059021006bc3059021036bf2059021036be2059021036bd2059021036bc2059021026bf1059021026b71059021026be1059021026bd1059021006b51059021026bc105902104cff76d5021024fe76d5021004fd76d5021024fc76d502104e7e65d50210067d65d502101ebe64d5021006bd64d50210473e54d502121ede63d5021216fa60d5021004ff7655021024fe7655021004fd7655021024fc765502104e7e65550210067d655502101ebe6455021006bd645502120ede6355021005f77155021025f47155021005fb705502102df87055021206fa6055021004ff7558c2104cfc7558c21004ff7458c2101cfe7458c2101cfc7458c21024ff7358c21026df7358c2103ede5358c2103edc5358c21006df4358c2103ede4358c2103edc4358c21034ff7258c21034fe7258c21034fd7258c21034fc7258c21036de3258c21036dc3258c21024ff7158c21024fe7158c21024fd7158c21024fc7158c21026de3158c21026dc3158c21026f62158c21036f52158c21004ff7058c2100cfe7058c21004fd7058c2100cf
  | 2 => 0x5f6768c521026f6768c52105df5738c521016f6638c521016f4638c521035f6728c521025f4728c521026f7628c521027e7628c52122ef7608c52122ef5608c521014ff764c52105cfd764c521034fc764c521006df634c521016dc634c521005ef724c521035ec724c521027d4314c521035f4764c521016f4764c521034f4764c521025f7734c521027d7734c521007d7634c521016f6634c521016f4634c52105fd4634c521016d4634c521007e7724c521035f6724c521035f4724c521007e4724c521026f7624c521027e7624c52105fd7324c521007d5324c521226f7604c521226f5604c52104e7f749942104e7e749942104e7d749942104e7c749942104e7f739942104e7e739942104e7d739942104e7c73994210067f43994210067e43994210067c43994210367f72994210367e72994210367d72994210367c72994210367f42994210367e42994210367d42994210367c42994210367f32994210367e32994210367d32994210367c32994210267f71994210267e71994210267d71994210267c71994210267f41994210267e41994210267d41994210267c41994210267f31994210267e31994210267d31994210267c31994210267f21994210267e21994210267d21994210267c219942104e7f709942104e7e709942104e7d709942104e7c70994210067f40994210067e40994210067d40994210067c40994210067f30994210067e30994210067d30994210067c30994210367f20994210367e20994210367d20994210367c20994210267f10994210267e10994210267d10994210267c1099421024ff75594210267f7559421004ff745942101cfe745942101cfc74594210067e54594210067c5459421004ff7359421014fe7359421014fc73594210067e53594210067c5359421034ff7259421034fe7259421034fd7259421034fc72594210367e52594210367c5259421024ff7159421024fe7159421024fd7159421024fc71594210267e51594210267c5159421004ff705942100cfe7059421004fd705942100cfc70594210067f50594210067e50594210067d50594210067c5059421026f71059421006f510594210067f74594210067e74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067f43594210067e43594210067c43594210367f72594210367e72594210367d72594210367c72594210367f42594210367e42594210367d42594210367c42594210367f32594210367e32594210367d32594210367c32594210267f71594210267e71594210267d71594210267c71594210267f41594210267e41594210267d41594210267c41594210267f31594210267e31594210267d31594210267c31594210267f21594210267e21594210267d21594210267c215
  | 3 => 0xc7359521006dc7359521014dc7359521004ff7259521006ef7259521004ff7159521006f77159521004ff705952100cfe7059521004fd705952100cfc7059521004fe761952104e7e65195210067d651952101cfe76d9121066be64d912104cfe75d9121004fd75d9121014fe73d9121004fd73d9121014fc73d9121034fe72d9121024fd72d9121034fc72d9121066bf42d9121024fe71d9121034fd71d9121024fc71d9121066bf41d9121004ff70d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121066bc40d9121066bc6459121004ff755912104cfc7559121064ff7459121006bf7459121004ff7359121014fe7359121014fc735912107cff7259121006ef7259121094ff7159121006f77159121004ff705912100cfe7059121004fd705912100cfc705912104cff76d5121004fe76d5121004fd76d512104cfc76d51210067f65d512104e7c65d51210673e54d5121004ff7655121004fe7655121004fd7655121004fc76551210067f655512104e7c6555121005fb7055121055f87055121014fe76d8d2105ede63d8d2104cfe75d8d21004fd75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2105edc53d8d2105ede43d8d21034fe72d8d21024fd72d8d21034fc72d8d2105edf32d8d21024fe71d8d21034fd71d8d21024fc71d8d2105edf31d8d21004ff70d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d2105edc30d8d210057f7558d210057c7558d2105edc6358d21004ff7558d210067f7558d210047f7558d2104cfc7558d210067c7558d2104c7c7558d21004ff7458d2101cfe7458d2101cfc7458d2105cff7358d21006df7358d21074ff7258d21006ef7258d2108cff7158d21006f77158d21004ff7058d2100cfe7058d21004fd7058d2100cfc7058d2104cff76d4d21004fe76d4d21004fd76d4d2104cfc76d4d21006df63d4d21016dc63d4d2105f5e53d4d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d21016dc6350d21024fe76d4921024fc76d49210067f65d492104e7c65d4921025f671d4921005f571d4921024fc76549210067f655492104e7c6554921005f77154921025f47154921024fc7650921006bf645092101ebc6450921005f77150921025f47150921037e42150921024fc764c921006df634c921016dc634c921005f7714c921025f4714c921034fe76d4521034fc76d45210067f65d452104e7c65d4521035ee72d4521005ed72d452104cff7654521004fd7654521034fc76545210067f655452104e7c6554521005ef7254521035ec725452101cff7650521064fd7650521034fc7650521006bf645052101ebc6450521005ef7250521035ec7250521027e42150521
  | 4 => 0x4f21025f47154f21004ff7650f21034fe7650f21004fd7650f21034fc7650f2101ebe6450f21006bd6450f21005f77150f21025f47150f2104e7e65d47210067d65d4721035ee72d4721005ed72d47210277651d472104cff765472104e7e65547210067d6554721005ef7254721035ec725472101cff7650721034fc765072101ebe6450721006bd6450721005ef7250721035ec7250721014ff764c721034fc764c721016de634c721006dd634c721005ef724c721035ec724c721027d4314c7210267f7559621004ff745962101cfe745962101cfc7459621004ff7359621014fe7359621014fc7359621024fc71596210267e51596210267c5159621004ff705962100cfe7059621004fd705962100cfc7059621004ff755922104cfc7559221026bf7459221004ff7359221014fe7359221014fc735922107ebf4259221024fc7159221026be4159221026bc4159221004ff705922100cfe7059221004fd705922100cfc705922104cff76d5221024fe76d5221004fd76d5221024fc76d52212467f65d522104e7c65d522107f3e54d5221004ff7655221024fe7655221004fd7655221024fc765522123e7f655522104e7c6555221005fb705522106df87055221004ff7558e2104cfc7558e21004ff7458e2101cfe7458e2101cfc7458e21026df7358e21076df3258e21024fc7158e21026de3158e21026dc3158e21004ff7058e2100cfe7058e21004fd7058e2100cfc7058e2104cff76d4e21024fe76d4e21004fd76d4e21024fc76d4e210775e53d4e21004ff7654e21024fe7654e21004fd7654e21024fc7654e21005ef7254e21035ec7254e21004ff7650e21024fe7650e21004fd7650e21024fc7650e2104e7e65d4a210067d65d4a21025f671d4a21005f571d4a2104cff7654a2104e7e6554a210067d6554a21005f77154a21025f47154a2101cff7650a21024fc7650a2101ebe6450a21006bd6450a21005f77150a21025f47150a21014ff764ca21024fc764ca21016de634ca21006dd634ca21037cc324ca21005f7714ca21025f4714ca21025f7764c62103ef7764c621027d7734c621027d7634c621016f6634c621026f4634c621027d4634c621026d4634c621035f6724c621035f4724c621077d7324c621007d5324c621026f7604c621236f5604c62104cfe76d952101cfe74d9521004fd74d952101cfc74d9521014fe73d9521004fd73d9521014fc73d95210067e53d95210067c53d9521034fe72d9521034fc72d9521024fe71d9521024fc71d9521004ff70d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210067c50d95210067f6599521005df735952105ddc73595210067f7559521004ff745952101cfe745952101cfc7459521004ff7359521006df7359521004df7359521014fe7359521014f
  | 5 => 0x1b7d43194931004ff7654931004fe7654931004fc765493104e7e65549310067d655493119fd43154931004fe7614931004fd7614931034fc76149310067f651493104e7c65149310a5be7414931005bd7414931015de7314931005dd7314931006ef6214931036ec6214931025f67114931005f57114931187d43114931004fe7690931004fd7690931034fc7690931015de7390931005dd7390931006ef6290931036ec6290931025f67190931005f57190931177d43190931004ff7650931004fe7650931004fc765093101ebe6450931006bd6450931006ef6250931036ec6250931167d43150931024dc764c931015df724c931017cf724c931007cf624c931036de624c931036dc624c931007cc624c931036cc624c931007d7714c931025de714c931025dc714c931007d4714c931025d4714c931016df614c931017d7614c93124fd7104c93124fd5104c931014fe76d4531014fc76d45310067f65d453104e7c65d4531015de73d4531005dd73d45310277651d4531027d431d453104cff7654531014fe76545310fcfd7654531014fc76545310067f655453104e7c6554531005df7354531015dc7354531027d4315453101cff7650531014fe76505310c4fd7650531014fc7650531006bf645053101ebc6450531005df7350531015dc7350531027d431505310367f7559721004ff745972101cfe745972101cfc7459721004ff7359721014fe7359721014fc7359721024fc72597210367e52597210367c5259721004ff705972100cfe7059721004fd705972100cfc70597210067e50597210067c5059721006f71059721006f51059721004ff755932104cfc7559321036bf7459321096be5459321004ff7359321014fe7359321014fc7359321096bf4359321024fc7259321036be4259321036bc4259321096bf4159321004ff705932100cfe7059321004fd705932100cfc7059321006be4059321096bc4059321006f71059321006f5105932104cff76d5321034fe76d5321004fd76d5321034fc76d532104e7e65d53210067d65d53210973e54d5321004ff7655321034fe7655321004fd7655321034fc765532104e7e65553210067d655532101ebe6455321006bd6455321005f77155321025f47155321005fb7055321085f87055321004ff7558f2104cfc7558f21004ff7458f2101cfe7458f2101cfc7458f21036df7358f21024fc7258f21036de3258f21036dc3258f2108edf3158f21036f62158f21036f52158f21004ff7058f2100cfe7058f21004fd7058f2100cfc7058f21006f71058f21006f51058f2104cff76d4f21034fe76d4f21004fd76d4f21034fc76d4f2104e7e65d4f210067d65d4f2108f5e53d4f21004ff7654f21034fe7654f21004fd7654f21034fc7654f2104e7e6554f210067d6554f21005f7715
  | 6 => 0xf7650a31004fd7650a31024fc7650a3101ebe6450a31006bd6450a3104cfe76d9531117d431d953101cfe74d9531004fd74d953101cfc74d9531024ff73d9531014fe73d9531024fd73d9531014fc73d95311167f53d95311167d53d9531034fe72d9531004fd72d9531004ff70d953100cfe70d9531004fd70d953100cfc70d95310067e50d95310067c50d9531006f710d9531006f510d95310067f65995310fdf5719953112fd43199531005ef7259531005ec725953112df771595310ffd431595310067f7559531004ff745953101cfe745953101cfc74595310fcff7359531006df7359531004ff7259531006ef7259531004ef7259531034fc7259531006ec7259531034ec725953112cff7159531006f77159531004ff705953100cfe7059531004fd705953100cfc7059531006f71059531006f51059531114fe761953104e7e65195310067d65195310e7d4311953101cfe76d91310a6be64d91310d7d431d913104cfe75d9131004fd75d9131024ff73d9131014fe73d9131024fd73d9131014fc73d91310d6bf43d91310d6bd43d9131034fe72d9131004fd72d9131014fd71d91310a6bf41d9131004ff70d913100cfe70d9131004fd70d913100cfc70d9131006be40d91310a6bc40d9131006f710d9131006f510d91310a6bc6459131255f771591310c7d43159131004ff755913104cfc75591310d4ff7459131006bf74591310c4ff7359131006df7359131004ff7259131034fc72591310a6bf4259131254ff7159131006f77159131004ff705913100cfe7059131004fd705913100cfc7059131006f71059131006f5105913104cff76d5131004fe76d5131004fd76d513104cfc76d51310067f65d513104e7c65d51310a73e54d513121fd431d5131004ff7655131004fe7655131004fd7655131004fc76551310067f655513104e7c6555131005df7355131015dc7355131005f77155131025f4715513120fd43155131005fb705513109df87055131077d431d893104cfe75d8931004fd75d893101cfe74d8931004fd74d893101cfc74d8931024fd73d8931076ee32d8931076ed32d8931024fe71d8931024fc71d8931004ff70d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d8931006ef629893105df5719893108fd431989310057f75589310057c755893108df7715893105fd431589310057e75189310057d75189310a5be7418931005bd7418931036ee6218931006ed621893103fd4311893109dfa7018931005f97018931004fe76d4931004fd76d493104cfc76d493104e7e65d49310067d65d4931006ef62d4931036ec62d49311cfd431d4931004fe7694931004fd7694931034fc76949310067f659493104e7c6594931015de7394931005dd7394931025f67194931005f57194931
  | 7 => 0x8941004fe76d4941004fd76d494104cfc76d494104e7e65d49410067d65d4941004fe7694941004fd7694941034fc769494101dbe7494941005bd7494941004ff7654941004fe7654941004fc765494104e7e65549410067d6554941004fe7614941004fd7614941034fc761494101dbe7414941005bd7414941024bc7650941006bf6550941006bd6550941006bf635094101dbf725094101faf7250941007af6250941036be6250941036bc6250941007ac6250941007b77150941025be7150941025bc7150941007b4715094101ebf615094101fb7615094115ebe605094115ebc605094125faf205094125fad205094125fb7105094125fb51050941004fe768c941004fd768c941034fc768c94101dbe748c941005bd748c941004ff764c941004fe764c941004fc764c94101cfe76d454101cfc76d45410067f65d454104e7c65d454101dbe74d4541005bd74d45410277651d454104cff765454101cfe7654541104fd765454101cfc76545410067f655454104e7c6554541005bf745454101dbc74545410267f7559631004ff745963101cfe745963101cfc74596310067e54596310067c54596310fe7f53596310fe7d5359631004ff7259631034fc7259631024fe7159631024fc71596310267e51596310267c5159631004ff705963100cfe7059631004fd705963100cfc70596310067f50596310067d5059631026f71059631006f51059631004ff755923104cfc7559231026bf74592310c6bf43592310c6bd4359231004ff7259231034fc72592310b6bf4259231024fe7159231024fc7159231026be4159231026bc4159231004ff705923100cfe7059231004fd705923100cfc7059231026f71059231006f5105923104cff76d5231024fe76d5231004fd76d5231024fc76d52312467f65d523104e7c65d52310b73e54d5231004ff7655231024fe7655231004fd7655231024fc765523123e7f655523104e7c6555231005f77155231025f47155231005fb70552310adf87055231004ff7558a3104cfc7558a31004ff7458a3101cfe7458a3101cfc7458a31026ef7258a3105eee3258a3105eed3258a31024ff7158a31024fd7158a31024fc7158a31026df3158a31026dd3158a31026ee2158a31026ec2158a31004ff7058a3100cfe7058a31004fd7058a3100cfc7058a3104cff76d4a31024fe76d4a31004fd76d4a3104e7e65d4a310067d65d4a31034ff7694a31024fe7694a31004fd7694a31025f67194a31005f57194a31004ff7654a31004fd7654a31024fc7654a3104e7e6554a310067d6554a31005df7354a31015dc7354a31034ff7614a31024fe7614a31004fd7614a310b5be7414a31005bd7414a31025f67114a31005f57114a31034ff7690a31024fe7690a31004fd7690a31025f67190a31005f57190a31004f
  | 8 => 0x34ff768ca41024fe768ca41004fd768ca4114efa608ca41004ff764ca41004fd764ca41024fc764ca41016de634ca41006dd634ca4113efa604ca41006fb7558241006fa7558241006f97558241006f875582410cefb74582410cebb74582410cefa745824126ef974582410cef874582410ceb8745824126efb545824126efa545824126ef9545824126ef85458241006fb7358241006fa7358241006f97358241006f87358241006fb5358241006fa5358241006f95358241006f8535824126efb435824126efa435824126ef9435824126ef84358241006fb7258241006fa7258241006f97258241006f87258241006fb5258241006fa5258241006f95258241006f8525824126efb425824126efa425824126ef9425824126ef84258241006fb3258241006fa3258241006f93258241006f83258241026fb7158241026fa7158241026f97158241026f87158241026fb5158241026fa5158241026f95158241026f85158241026fb4158241026fa4158241026f94158241026f84158241026fb3158241026fa3158241026f93158241026f83158241026fb2158241026fa2158241026f92158241026f8215824104cfe76d9541024ff74d954101cfe74d9541024fd74d954101cfc74d954111e7f54d954111e7d54d9541014fe73d9541004fd73d9541014fc73d9541034fe72d9541004fd72d954111ebf42d9541004ff70d954100cfe70d9541004fd70d954100cfc70d95410067e50d95410067c50d9541006f710d9541006f510d95410067f6599541105f57199541135f77159541005fb70595410bdf870595410067f7559541104ff7459541006bf7459541004ff7359541014fe7359541014fc7359541004ff7259541034fc7259541106bf4259541134ff7159541006f7715954123e7e515954123e7c5159541004ff7059541006fb7059541004fb705954100cfe7059541004fd705954100cfc7059541006f8705954100cf87059541006f71059541006f5105954111cfe761954104e7e65195410067d6519541014fe76d8d410c6de63d8d4104cfe75d8d41004fd75d8d41024fd74d8d41014fc74d8d410c6de43d8d410b6dd43d8d41034fe72d8d41004fd72d8d410b6bf42d8d4101cfd71d8d410c6df31d8d41004ff70d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006f710d8d41006f510d8d410c6dc6358d41265f77158d41004fe76d4d41004fd76d4d4104cfc76d4d410c75e53d4d41004ff7654d41004fe7654d41004fc7654d4104cfe75d8941004fd75d8941024fd74d8941014fe73d8941004fd73d8941014fc73d894107eee42d894107eed42d8941004ff70d894100cfe70d8941004fd70d894100cfc70d8941006ef6298941065f57198941095f771589410057e75189410057d7518941036ee6218941006ed621
  | 9 => 0xd628c85114efa608c851004ff764c851004fd764c851024fc764c8510057f754c85104d7c754c851016de634c851006dd634c851036ee624c851006ed624c851005f7714c851025f4714c85113efa604c85104efb75580510de7b755805104efa755805104ef9755805104ef8755805104e787558051006fb7458051006fa7458051006f97458051006f8745805104efb545805104e7b545805104efa545805104ef9545805100679545805104ef85458051006fb7358051006fa7358051006f97358051006f8735805104efb535805104efa535805104ef9535805104ef85358051006fb4358051006fa4358051006f94358051006f84358051006fb7258051006fa7258051006f97258051006f8725805104efb525805104efa525805104ef9525805104ef85258051006fb4258051006fa4258051006f94258051006f84258051006fb3258051006fa3258051006f93258051006f83258051026fb7158051026fa7158051026f97158051026f87158051026fb5158051026fa5158051026f25158051026f9515805104ef15158051026f85158051026fb4158051026fa4158051026f94158051026f84158051026fb3158051026fa3158051026f93158051026f83158051026fb2158051026fa2158051026f92158051026f821580510267f75596411067f54596411067d5459641004ff7359641014fe7359641014fc73596410067e53596410067c5359641004ff7259641034fc7259641024fe7159641024fc71596410267e51596410267c5159641004ff705964100cfe7059641004fd705964100cfc7059641026f71059641006f51059641004ff7558e4104cfc7558e41026df7358e410d6dc5358e410d6de4358e410a6dd4358e41004ff7258e41034fc7258e410d6df3258e41024fe7158e41024fc7158e41026de3158e41026dc3158e41004ff7058e4100cfe7058e41004fd7058e4100cfc7058e41026f71058e41006f51058e4104cff76d4e41024fe76d4e41004fd76d4e41016de63d4e41006dd63d4e410d75e53d4e411f6fa60d4e41004ff7654e41004fd7654e41024fc7654e411e6fa6054e41004ff7558a4104cfc7558a41004ff7358a41014fe7358a41014fc7358a41026ef7258a41066ee4258a41066ed4258a41024fc7158a41026bf4158a41026bd4158a41026ee2158a41026ec2158a41004ff7058a4100cfe7058a41004fd7058a4100cfc7058a41006be4058a41066bc4058a4104cff76d4a41024fe76d4a41004fd76d4a4104e7e65d4a410067d65d4a411c6fa60d4a41034ff7694a41024fe7694a41004fd7694a411aefa6094a41004ff7654a41004fd7654a41024fc7654a4104e7e6554a410067d6554a41196fa6054a41034ff7614a41024fe7614a41004fd7614a4101dbe7414a41005bd7414a4117efa6014a41
  | 10 => 0x49510367e62d49510367c62d49510257e71d49510257c71d495104e7f61d495104f7761d49511c67e60d49511c67c60d495128f7710d495128f7510d4951024fe76949512857d7594951006ef6294951036ec6294951025f67194951005f57194951024fc7654951006ef6254951036ec6254951005f77154951025f471549510247c76549510067f64549510067f635495104d7f725495104f6f72549510076f62549510367e62549510367c62549510076c62549510077771549510257e71549510257c715495100774715495104e7f615495104f7761549511967e60549511967c605495127f77105495127f751054951004fe7690951004fd7690951034fc769095104d7e75909510057d7590951004ff7650951004fe7650951004fc765095101ebe6450951004fe768c951004fd768c951034fc768c95104d7e758c9510057d758c951006df638c951016dc638c951004ff764c951004fe764c951004fc764c95101cfd7559051024ff7459051026bf745905104ebf545905104ebc5459051004ff7359051014fe7359051014fc73590510eebf4359051004ff7259051034fc72590510eebf4259051024fc7159051026be4159051026bc4159051004ff705905100cfe7059051004fd705905100cfc705905104d7f76550511367f765505104d7f745505104f3f745505101e7e645505101e7c64550510ef3f43550510ef3f425505123d7f715505123e7e615505104f7661550510077b70550510dd7e70550510dd7c70550512777870550510dd78705505104e7f605505104f7a60550512767d605505104f796055051014fd7558c51004ff7458c5101cfe7458c5101cfc7458c5104e7f5458c510067d5458c51024ff7358c51026df7358c5104edf5358c5104edc5358c510e6de4358c51004ff7258c51034fc7258c510e6df3258c51024fc7158c51026de3158c51026dc3158c51004ff7058c5100cfe7058c51004fd7058c5100cfc7058c51004ff7650c51004fd7650c51024fc7650c5101ebe6450c51006bd6450c510073d5450c51016de6350c51006dd6350c511defa6050c51004ff745885101cfe745885101cfc745885104e7f54588510067d5458851004ff7358851014fe7358851014fc7358851026ef725885104eef525885104eec52588510267f51588510267d5158851026ee2158851026ec2158851004ff705885100cfe7058851004fd705885100cfc70588510067e505885104e7c5058851034ff7690851024fe7690851004fd7690851036ee6290851006ed629085116efa6090851004ff7650851004fd7650851024fc765085101ebe6450851006bd64508510073d5450851036ee6250851006ed6250851005f77150851025f4715085115efa6050851034ff768c851024fe768c851004fd768c851036ee628c851006e
  | 11 => 0x297751055251004ff7458e5101cfe7458e5101cfc7458e510067f5458e510067d5458e51026df7358e51116de5358e51006df4358e51116dc4358e51004ff7258e51034fc7258e51116df3258e51024fc7158e51026de3158e51026dc3158e51004ff7058e5100cfe7058e51004fd7058e5100cfc7058e51116df3058e51006dd3058e51026f71058e51006f51058e51014ff7654e51016de6354e51006dd6354e51005f77154e51025f47154e5104f775154e51004ff7650e51004fd7650e51024fc7650e510073d5450e51004ff7458a5101cfe7458a5101cfc7458a510067f5458a510067d5458a51004ff7358a51014fe7358a51014fc7358a51026ef7258a51024fc7158a510267f5158a510267d5158a51026ee2158a51026ec2158a51004ff7058a5100cfe7058a51004fd7058a5100cfc7058a510067e5058a510067c5058a51036ee6294a51006ed6294a51025f67194a51005f57194a5104f775194a51034ff7654a51036ee6254a51006ed6254a51005f77154a51025f47154a51034ff7690a51024fe7690a51004fd7690a51004ff7650a51004fd7650a51024fc7650a5101ebe6450a51006bd6450a510073d5450a51034ff768ca51024fe768ca51004fd768ca51004ff764ca51004fd764ca51024fc764ca510057f754ca5104d7c754ca51016de634ca51006dd634ca5101cfe76d9151106be64d9151024fd75d915101cfc75d9151106be54d9151014fe73d9151004fd73d9151014fc73d9151034fe72d9151004fd72d915104cfd71d91512467e51d91512467c51d9151106bf41d9151004ff70d915100cfe70d9151004fd70d915100cfc70d9151006be40d9151106bc40d9151006f710d9151006f510d9151106bc6459151005fb70591510f5f87059151024fc7655151006bf645515101ebc6455151005f77155151025f47155151005fb70551510f5f87055151014fe76d8d510fede63d8d51024fd75d8d51014fc75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d510fede53d8d51034fe72d8d51004fd72d8d510fedc32d8d5104cfd71d8d510fedf31d8d51004ff70d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51006f710d8d51006f510d8d510fedc6358d51005ef7258d51005ec7258d51024fc7654d51006df6354d51016dc6354d5104f5c5354d51005f77154d51025f47154d51004ff7650d51004fe7650d51004fc7650d510057f7550d5104d7c7550d5101cfe74d8951004fd74d895101cfc74d8951014fe73d8951004fd73d8951014fc73d8951006ef32d8951006ec32d8951004ff70d895100cfe70d8951004fd70d895100cfc70d8951006ef6298951005df73589510fddc7358951105be7418951005bd7418951036ee6218951006ed62189510057e76d495104e7e76d49510067f64d49510067f63d
  | 12 => 0x741d8532006f441d853208ef631d8532004ff70d853200cfe70d8532004fd70d853200cfc70d8532006f710d8532006f510d8532006f761985320057f75585320057c7558532026f66118532006f5611853213dfa7018532005f97018532024fc755935104ebf745935104ebf545935104ebc5459351004ff7359351014fe7359351014fc7359351136bf4359351004ff7259351034fc725935104e7f5259351136bf425935123e7e515935104e7c5159351136bf4159351004ff7059351006fb7059351004fb705935100cfe7059351004fd705935100cfc7059351006f8705935100cf87059351006be4059351136bc4059351024fc7558f51004ff7458f5101cfe7458f5101cfc7458f5104edf7358f5104edf5358f5104edc5358f51004ff7258f51034fc7258f5104e7f5258f5112edf3158f51004ff7058f5100cfe7058f51004fd7058f5100cfc7058f51004ff7650f51004fd7650f5104cfc7650f510057f7550f5104d7c7550f5101ebe6450f51006bd6450f51024fc7558b51004ff7458b5101cfe7458b5101cfc7458b51004ff7358b51014fe7358b51014fc7358b5104eef7258b5104eef5258b5104eec5258b51004ff7058b5100cfe7058b51004fd7058b5100cfc7058b5104d7f7654b510067f7654b510067d6454b510067d6354b5104f6f7254b510367e6254b510367c6254b510257e7154b510257c7154b511967e6054b5104e7c6054b51034ff7690b5104cfe7690b51004fd7690b5104d7e7590b510057d7590b51004ff7650b51004fd7650b5104cfc7650b5101ebe6450b51006bd6450b51005f77150b51025f47150b51034ff768cb5104cfe768cb51004fd768cb5104d7e758cb510057d758cb51004ff764cb51004fd764cb5104cfc764cb51005f7714cb51025f4714cb51026bf745925111ebe5459251004ff7359251014fe7359251014fc7359251004ff7259251034fc725925111ebf4259251024fc7159251026be4159251026bc4159251004ff705925100cfe7059251004fd705925100cfc7059251026f71059251006f510592512457d76d525104e7d76d525101e7e64d525101e7c64d525104d7f71d52512457d71d525104f7661d525110d7e70d525104d7c70d52512467f60d525129e7d60d52512477710d525129f7510d525101cff765525101ebe6455251006bd6455251005f77155251025f4715525104f775155251005fb705525110df8705525123d7f765525101e7f765525101c7f765525104d7f745525104f3f745525101e7e645525123f3e645525123f3d645525101e7c645525111f3f435525111f3f425525123d7f715525100777715525123f74715525104e7e61552510077b705525110d7e705525110d7c705525129778705525110d78705525123e7f60552512967d605525123f771055251
  | 13 => 0x5232034fc765523204e7e65552320067d655523201ebe6455232006bd6455232005df7355232015dc7355232005fb705523214df87055232004ff755863204cfc7558632004ff745863201cfe745863201cfc7458632034fc7258632036df3258632036dd3258632036f7715863205ef63158632036f72158632036f42158632004ff705863200cfe7058632004fd705863200cfc705863204cfe76d953201cfe74d9532004fd74d953201cfc74d95320067e54d95320067c54d9532034ff73d9532034fd73d95321b67f53d95321b67d53d9532024fe71d9532004fd71d9532004ff70d953200cfe70d9532004fd70d953200cfc70d95320067f50d95320067d50d95320067f659953219ded72995321cdef7259532005f77159532005f471595320067f7559532004ff745953201cfe745953201cfc745953219cff7359532006df73595321ccff7259532006ef7259532004ff7159532006f77159532004f77159532024fc7159532006f47159532024f47159532004ff705953200cfe7059532004fd705953200cfc70595321b4fe761953204e7e65195320067d6519532145be7419532005bd741953201cfe76d9132146be64d913204cfe75d9132004fd75d9132034ff73d9132034fd73d9132176bf43d9132176bd43d9132014fd72d9132146bf42d9132024fe71d9132004fd71d9132004ff70d913200cfe70d9132004fd70d913200cfc70d91320057f75591320057c7559132146bc64591322a5ef7259132005f77159132005f47159132005fb705913213df87059132004ff75591320067f75591320047f755913204cfc75591320067c755913204c7c7559132174ff7459132006bf7459132146be5459132164ff7359132006df73591322a4ff7259132006ef7259132004ff7159132006f77159132004f77159132024fc7159132006f47159132024f47159132004ff7059132006fb7059132004fb705913200cfe7059132004fd705913200cfc7059132006f8705913200cf8705913204cff76d5132004fe76d5132004fd76d513204cfc76d513204e7e65d51320067d65d51321473e54d5132004ff7655132004fe7655132004fd7655132004fc765513204e7e65551320067d655513201ebe6455132006bd6455132005fb705513213df87055132014fe76d4932014fc76d49320067f65d493204e7c65d4932015de73d4932005dd73d49320376e52d493204cff7654932014fe765493219cfd7654932014fc76549320067f655493204e7c6554932005df7354932015dc7354932037cc325493201cff7650932014fe7650932164fd7650932014fc7650932006bf645093201ebc6450932005df7350932015dc7350932037cc325093204cfe75d8532004fd75d853201cfe74d8532004fd74d853201cfc74d8532034fd73d8532006f
  | 14 => 0x35bc7255142007ac725514201ebf625514201faf6255142005bf7155142007bb705514215dbe705514215dbc70551422bfb8705514215db870551422bf3f50551422bf3d50551422bfaf20551422bfad2055142014fe76d8d42166de63d8d4204cfe75d8d42004fd75d8d42034fd74d8d42156be54d8d42006bd54d8d42166dc53d8d42166de43d8d42156dd43d8d4201cfd72d8d42166df32d8d42024fe71d8d42004fd71d8d42004ff70d8d4200cfe70d8d42004fd70d8d4200cfc70d8d420057f7558d420057c7558d42166dc6358d422b5ef7258d42005f77158d42005f47158d42005fb7058d4215df87058d42004fe76d4d42004fd76d4d4204cfc76d4d4204e7e65d4d420067d65d4d4201dbe74d4d42005bd74d4d420073d54d4d42006df63d4d42016dc63d4d421675e53d4d42035ee72d4d42005ed72d4d42004ff7654d42004fe7654d42004fc7654d4204e7e6554d420067d6554d4201dbe7454d420073d5454d42035bc7650d42016bc7650d42034bc7650d42005bf7550d42005bd7550d42006bf6550d42006bd6550d4201dbf7350d4201f9f7350d420079f6350d42016be6350d42016bc6350d421679c6350d42007af7250d42035be7250d42035bc7250d42007ac7250d4201ebf6250d4201faf6250d42005bf7150d4215dbe7050d4215dbc7050d421679f3050d422af9d3050d422afaf2050d422afad2050d4201cfe76d494201cfc76d49420067f65d494204e7c65d494201dbe74d4942005bd74d49420073d54d49420376e52d494204cff765494201cfe76549421a4fd765494201cfc76549420067f655494204e7c6554942005bf745494201dbc74549420073d5454942037ac425494204cfe75d8542004fd75d8542034fd74d8542014fe73d8542004fd73d8542014fc73d8542096f641d8542006f731d8542006f431d8542004ff70d854200cfe70d8542004fd70d854200cfc70d8542006f710d8542006f510d8542006f7619854215dfa7098542005f97098542026f66118542006f561185420367f7559632004ff745963201cfe745963201cfc745963219e7f535963219e7d5359632034fe7259632034fc72596320367e52596320367c5259632004ff7159632024fc7159632004ff705963200cfe7059632004fd705963200cfc70596320067e50596320067c5059632004ff755923204cfc7559232036bf7459232156be5459232166bf4359232166bd4359232034fe7259232034fc7259232036be4259232036bc4259232004ff7159232024fc7159232156bf4159232004ff705923200cfe7059232004fd705923200cfc7059232006be4059232156bc405923204cff76d5232034fe76d5232004fd76d5232034fc76d523204e7e65d52320067d65d52321573e54d5232004ff7655232034fe7655232004fd765
  | 15 => 0xc3258c52004ff7158c52024fc7158c52186df3158c52004ff7058c5200cfe7058c52004fd7058c5200cfc7058c52186df3058c52006dd3058c52004ff7650c52004fd7650c52034fc7650c520057f7550c5204d7c7550c5201ebe6450c52006bd6450c52004ff745845201cfe745845201cfc7458452004ff7358452014fe7358452014fc73584520367f52584520367d5258452036f7715845204ef7515845204ef45158452036f72158452036f42158452004ff705845200cfe7058452004fd705845200cfc7058452006f71058452006f510584520367f75596421a67f54596421a67d5459642004ff7359642014fe7359642014fc7359642034fe7259642034fc72596420367e52596420367c5259642036bf4259642036bd4259642004ff7159642024fc7159642004ff705964200cfe7059642004fd705964200cfc70596420067e50596420067c5059642004ff7558e4204cfc7558e42036df7358e42176de4358e42146dd4358e42034fe7258e42034fc7258e42036bf4258e42036bd4258e42036de3258e42036dc3258e42004ff7158e42024fc7158e42176df3158e42004ff7058e4200cfe7058e42004fd7058e4200cfc7058e4204cff76d4e42034fe76d4e42004fd76d4e4204e7e65d4e420067d65d4e421775e53d4e42035ee72d4e42005ed72d4e42004ff7654e42004fd7654e42034fc7654e4204e7e6554e420067d6554e42004ff755864204cfc7558642004ff7358642014fe7358642014fc7358642034fc7258642036bf4258642036bd4258642036f77158642066f64158642036f72158642036f42158642004ff705864200cfe7058642004fd705864200cfc705864204cfe76d9542034ff74d9542034fd74d95421be7f54d95421be7d54d9542014fe73d9542004fd73d9542014fc73d95420067e53d95420067c53d95421bebf43d9542024fe71d9542004fd71d9542004ff70d954200cfe70d9542004fd70d954200cfc70d95420067f65995421a5ed7299542005df7359542165dc73595421d5ef7259542005f77159542005f47159542005fb705954215df870595420067f75595421a4ff7459542006bf7459542004ff7359542006df7359542004df7359542014fe7359542014fc7359542006dc7359542014dc73595421a6bf43595421d4ff7259542006ef7259542004ff7159542006f77159542004f77159542024fc7159542006f47159542024f47159542004ff7059542006fb7059542004fb705954200cfe7059542004fd705954200cfc7059542006f8705954200cf870595421bcfe761954204e7e65195420067d6519542035bc765514204ebc7655142034bc765514201dbf755514201f3f75551420073f655514204ebe655514204ebc65551420073c6555142005bf7355142007af7255142035be7255142
  | 16 => 0x8d52006dd30d8d5219edc6358d52005f77158d52005f47158d520057e76d4d5204e7e76d4d520057d74d4d520067f64d4d5219d7d73d4d520167e63d4d520167c63d4d520357e72d4d520357c72d4d5204e7f62d4d5204f6f62d4d520057d71d4d521957e70d4d5204d7c70d4d52034fc7654d52006df6354d52016dc6354d52005ef7254d52035ec7254d520357c7654d520167c7654d520347c7654d520057f7454d520067f6454d5204d7f7354d5204f5f7354d520075f6354d520167e6354d520167c6354d5219f5c6354d520165c6354d520076f7254d520357e7254d520357c7254d520076c7254d5204e7f6254d5204f6f6254d520057f7154d521957e7054d521957c7054d52004ff7650d52004fe7650d52004fc7650d5204d7e7550d520057d7550d5201ebe6450d520073d5450d5201cfe74d8552004fd74d855201cfc74d8552014fe73d8552004fd73d8552014fc73d8552006f741d8552006f441d8552006f731d8552006f431d8552004ff70d855200cfe70d8552004fd70d855200cfc70d8552006f710d8552006f510d8552006f76198552005df735855219ddc7358552026f66118552006f56118552195fa7018552005f97018552034ff7459052036bf745905204ebf545905204ebc5459052004ff7359052014fe7359052014fc735905218ebf4359052006be435905218ebc4359052034fc72590520367f52590520367d5259052036be4259052036bc4259052004ff7159052024fc715905218ebf415905218ebc4159052004ff705905200cfe7059052004fd705905200cfc705905218ebf4059052006be4059052006bd405905218ebc405905204ebf755905204ebe755905204ebc7559052006bf7359052006be7359052006bd7359052006bc735905204ebf535905204ebe535905204ebd535905204ebc5359052036bf7259052036be7259052036bc7259052036bf52590520363f5259052036be5259052036bd52590520363d5259052036bc5259052036bf3259052036be3259052036bd3259052036bc3259052006bf7159052006be7159052006bd7159052006bc715905204ebf515905204ebe515905204ebd515905204ebc5159052006bf3159052006bc3159052036bf2159052036be2159052036bd2159052036bc2159052006bf7059052006be7059052006bd7059052006bc705905204ebf505905204ebe505905204ebd505905204ebc5059052006bf3059052006be3059052006bd3059052006bc3059052036bf2059052036be2059052036bd2059052036bc2059052006bf1059052006be1059052006bd1059052006bc1059052004ff7458c5201cfe7458c5201cfc7458c52034ff7358c52036df7358c5204edf5358c5204edc5358c52034fc7258c520367f5258c520367d5258c52036de3258c52036d
  | 17 => 0x6f71058752006f51058752036bf74592521bebe5459252004ff7359252014fe7359252014fc73592521bebf4359252034fc72592520367f52592520367d5259252036be4259252036bc4259252004ff7159252024fc71592521bebf4159252004ff705925200cfe7059252004fd705925200cfc7059252006be40592521bebc405925201cff765525201ebe6455252006bd6455252005ef7255252035ec725525204f6f5255252005fb70552521adf87055252004ff7458e5201cfe7458e5201cfc7458e52036df7358e521b6de5358e52034fc7258e520367f5258e520367d5258e52036de3258e52036dc3258e52004ff7158e52024fc7158e521b6df3158e52004ff7058e5200cfe7058e52004fd7058e5200cfc7058e52014ff7654e52016de6354e52006dd6354e5204f5c5354e52005ef7254e52035ec7254e5204f6f5254e52004ff7650e52004fd7650e52034fc7650e520057f7550e5204d7c7550e5201ebe6450e52006bd6450e52004ff745865201cfe745865201cfc7458652004ff7358652014fe7358652014fc7358652034fc72586520367f52586520367d5258652036f77158652036f72158652036f42158652004ff705865200cfe7058652004fd705865200cfc705865201cfe76d91521a6be64d9152034fd75d91521a6be54d9152014fe73d9152004fd73d9152014fc73d915204cfd72d91521a6bf42d9152024fe71d9152004fd71d9152004ff70d915200cfe70d9152004fd70d915200cfc70d91521a6bc6459152005df735915219ddc7359152005f77159152005f47159152005fb7059152195f870591520057e76d515204e7e76d51521a57d74d515201e7e64d515201e7c64d51520057d73d51520357e72d51520357c72d515204e7f62d515204f6f62d51520057d71d51522467c61d51521957e70d515204d7c70d51522ce7f60d51522ce7d60d5152034fc7655152006bf645515201ebc645515204f3c5455152005ef7255152035ec7255152005fb7055152195f870551520357c765515201e7c76551520347c765515204d7f745515204f3f74551520073f645515201e7e645515201e7c64551521a73c64551520057f73551521a73f43551520076f72551520357e72551520357c72551520076c725515204e7f625515204f6f62551521a73f42551520057f715515223e7c61551520077b70551521957e70551521957c70551522c77870551521957870551522c67f60551522c67d6055152014fe76d8d5219ede63d8d52034fd75d8d5201cfe74d8d52004fd74d8d5201cfc74d8d520067f54d8d520067d54d8d5219ede53d8d52006df43d8d5219edc43d8d5204cfd72d8d5219edf32d8d52024fe71d8d52004fd71d8d5219edc31d8d52004ff70d8d5200cfe70d8d52004fd70d8d5200cfc70d8d5219edf30d
  | 18 => 0xb7059543004fb705954300cfe7059543004fd705954300cfc7059543006f8705954300cf870595432e4fe761954304e7e65195430067d6519543015bc765514304ebc7655143014bc765514301dbf755514301f3f75551430073f655514304ebe655514304ebc65551430073c65551430079f7355143015be7355143015bc735514320f9c735514301ebf635514301f9f635514320f3f535514320f3d5355143005bf7255143007bb70551432dfb870551432df3f50551432df3d505514320f9f30551432df9d3055143034fe76d894304cfe75d8943004fd75d8943014fd74d89432b6be54d8943006bd54d894301cfd73d89432b6ee42d89432a6ee32d8943024fe71d8943004fd71d8943004ff70d894300cfe70d8943004fd70d894300cfc70d8943006ef62989430057f75589430057c7558943005f77158943005f47158943005fb70589431ddf870589430057e75189430057d7518943036ee6218943006ed6218943024fe76d854304cfe75d8543004fd75d8543014fd74d854301cfd73d8543034fe72d8543004fd72d8543266bf42d8543266f641d8543256f631d8543004ff70d854300cfe70d8543004fd70d854300cfc70d85430057e75985430057d7598543006f761985431ddfa7098543005f97098543026f66118543006f56118543034fc755935204ebf745935204ebf545935204ebc5459352004ff7359352014fe7359352014fc735935204e7f53593521d6bf43593521d6bf4259352004ff7159352024fc7159352004ff705935200cfe7059352004fd705935200cfc705935204d7f765535218e7f765535204f3f745535204f3f645535201e7e645535201e7c645535204f3c64553520057f73553521d73f43553520357e72553520357c72553521d73f42553520057f715535223e7e61553520077b70553521c57e70553521c57c70553522d77870553521c578705535204e7f60553522d67d6055352034fc7558f52004ff7458f5201cfe7458f5201cfc7458f5204e7f5458f520067d5458f5204edf7358f5204edf5358f5204edc5358f521cede4358f521cedf3258f52004ff7158f52024fc7158f52004ff7058f5200cfe7058f52004fd7058f5200cfc7058f5204d7f7654f521867f7654f520057f7454f520067d6454f5204f5f7354f520167e6354f520167c6354f520357e7254f520357c7254f520057f7154f521c57e7054f521c57c7054f52004ff7650f52004fd7650f5204cfc7650f5204d7e7550f520057d7550f5201ebe6450f52006bd6450f520073d5450f52016de6350f52006dd6350f52034fc7558752004ff745875201cfe745875201cfc7458752004ff7358752014fe7358752014fc735875204ef7715875204ef7515875204ef45158752004ff705875200cfe7058752004fd705875200cfc7058752
  | 19 => 0x8b5304e7f5458b530067d5458b5304eef7258b5304eef5258b5304eec5258b5319eee3258b53004ff7158b53024fc7158b53004ff7058b5300cfe7058b53004fd7058b5300cfc7058b53014fc7558753004ff745875301cfe745875301cfc7458753004ff7258753034fc725875304e7f525875304ef7715875304ef7515875304ef451587530fef63158753004ff705875300cfe7058753004fd705875300cfc7058753006f71058753006f5105875301cfe76d91531eebe64d9153014fd75d91531eebe54d915304cfd73d915321ebf43d9153034fe72d9153004fd72d9153024fe71d9153004fd71d9153004ff70d915300cfe70d9153004fd70d915300cfc70d9153006be40d91531eebc40d91531eebc6459153005fb70591531e5f870591533057e76d515304e7e76d515320d7d74d515301e7e64d515301e7c64d51530157e73d51530157c73d515304e7f63d515304f5f63d51530057d72d51532467c61d51532fe7f60d51532fe7d60d5153014fc7655153006bf645515301ebc645515304f3c5455153005df7355153015dc7355153005fb70551531e5f870551530157c765515301e7c76551530147c765515304d7f745515304f3f74551530073f645515301e7e645515301e7c64551531ef3c64551530075f73551530157e73551530157c735515320f5c735515304e7f635515304f5f635515320f3f43551530057f72551531ef3f425515323e7c61551530077b70551532f77870551532f67f60551532f67d605515301cfe74d8953004fd74d895301cfc74d89530067f54d89530067d54d895304cfd73d89531ceee32d8953024fe71d8953004fd71d8953004ff70d895300cfe70d8953004fd70d895300cfc70d8953006ef6298953005f77158953005f471589531edbe7418953005bd7418953036ee6218953006ed621895301cfe74d8553004fd74d855301cfc74d855304cfd73d8553034fe72d8553004fd72d855312ef631d8553004ff70d855300cfe70d8553004fd70d855300cfc70d8553006f76198553005ef7258553005ec7258553026f66118553006f561185531e5fa7018553005f9701855304cfe76d9543014ff74d9543014fd74d95432ee7f54d95432ee7d54d954301cff73d954301cfd73d95432e67f53d95432e67d53d9543034fe72d9543004fd72d95432eebf42d9543024fe71d9543004fd71d9543004ff70d954300cfe70d9543004fd70d954300cfc70d95430067e50d95430067c50d954320cfd76995430067f659954320dbd74995431eddd739954304cff765954321dbf74595431fddf7359543005fb70595431ddf870595430067f755954321cff7459543006bf745954320cff7359543006df7359543004ff7259543034fc72595431eebf4259543004ff7159543024fc7159543004ff7059543006f
  | 20 => 0x24fe71d8d54004fd71d8d5420edf31d8d54004ff70d8d5400cfe70d8d54004fd70d8d5400cfc70d8d5420edc6358d54005fb7058d54205f87058d54006f86058d54006f860d895404cfd74d8954014fe73d8954004fd73d8954014fc73d89541d6bf43d89541d6ee42d8954024fe71d8954004fd71d8954004ff70d895400cfe70d8954004fd70d895400cfc70d8954006ef6298954205fa7098954005f97098954006f86098954005df735895420ddc7358954005f77158954005f47158954005fb7058954205f87058954006f86058954036ee6218954006ed6218954006f86018954006f860d85541367d75d855404cfd74d8554014fe73d8554004fd73d8554014fc73d8554034fe72d8554004fd72d8554136bf42d8554136f641d8554004ff70d855400cfe70d8554004fd70d855400cfc70d855420dde7398554005dd7398554006f76198554205fa7098554005f97098554006f86098554005fb7058554205f87058554006f86058554026f66118554006f56118554006f86018554205fa76d8154206fa76d815400cfa76d815431f7b75d81542077875d8154327bb54d815431f7a54d815431f7854d815431fb854d8154006fb63d8154006fa63d8154006f963d8154006f863d815431fbb43d8154006fb62d8154006fa62d8154006f962d8154006f862d815431fbb42d8154006fb61d8154006fa61d8154006f961d8154006f861d815431efb75d8154206fa75d8154206f975d8154206f875d815431efb74d8154206fa74d8154206f974d8154206f874d815431efb54d815431efa54d8154206f954d815431ef854d8154006fb73d8154006fa73d8154006f973d8154006f873d8154326fb53d8154006fa53d8154326f853d815431efb43d815431efa43d815431ef943d815431ef843d8154006fb72d8154006fa72d8154006f972d8154006f872d8154326fb52d8154326f852d815431efb42d815431efa42d815431ef942d815431ef842d8154006fb32d8154006f832d8154006fb71d8154006fa71d8154006f971d8154006f871d8154326fb51d8154326f851d815431efb41d815431efa41d815431ef941d815431ef841d8154006fb31d8154006f831d8154014fe7559353014fc755935304ebf745935304ebf545935304ebc545935320ebf4359353004ff7259353034fc725935304e7f52593531febf4259353004ff7159353024fc7159353004ff705935300cfe7059353004fd705935300cfc705935304d7f76553533167f765535304f3f745535304f3f645535301e7e645535301e7c645535304f3c64553530157e73553530157c735535320f3f43553530057f72553531ff3f425535323e7e61553530077b705535330f78705535304e7f605535330e7d6055353014fc7558b53004ff7458b5301cfe7458b5301cfc745
  | 21 => 0x800a0050040024008005000800c00400300000000020000008004016000002000000000200000100000020008020014001000000400000000180440020000028010002000000800800200100100000000010008004000000005800c00200300480080000000008004002002000000c010002000000000000100000080020030010008002001000000c00200200080080020000020008004000002000000200200080000000010000000002000000800000200300000000160010030018004000000000800800900000140080010000004006005000000000200100000000060010000000004001002000000400200380000000000000004000007000800800600100280dc004000000800000400000000000020080000000000000000800401a00000000100000010030004002003000801c00000400080000020000000014002005003000c0000010000004000001000001000000700180000000020038004000000000802000000300080000020000010008002002000000c006002000800400400000080040040030000014000004000800c0140010028010006003000000800e000000800400e0050018000006002000800c00e00d0000000002008003805800600000080000060000038004000008000800000800000200040000000008000006003000001000a002000800000c006000000c01400400000000000020000018000001000000800000800080080040000000014016000000800001000000980040000010000000008000000000c002001000000c0140000000000008003000000c0020000018004004005000800400000000000080020010000000002004000000000400100280000000000000004000014000000801000a01cfe7558f5401cfc7558f5404ebe5458f5404ebd5458f5404edf7358f5404edf5358f5404edc5358f5421ede4358f54004ff7258f54034fc7258f5404e7f5258f54004ff7158f54024fc7158f54004ff7058f5400cfe7058f54004fd7058f5400cfc7058f5401cfc7558b5404ebe5458b5404ebd5458b54004ff7358b54014fe7358b54014fc7358b5404e7f5358b5404eef7258b5404eef5258b5404eec5258b541a6ee4258b54004ff7158b54024fc7158b54004ff7058b5400cfe7058b54004fd7058b5400cfc7058b5401cfc755875404e7c755875401c7c7558754004ff7358754014fe7358754014fc7358754004ff7258754034fc725875404e7f525875404ef7715875404ef7515875404e7c515875404ef45158754106f64158754004ff705875400cfe7058754004fd705875400cfc7058754006f71058754006f51058754014fe76d8d5420ede63d8d54006f860d8d5401cfd75d8d5404cfd74d8d5420ede53d8d5420ede43d8d54034fe72d8d54004fd72d8d541febf42d8d5420edc32d8d54
  | 22 => 0x800400200000080000000030018010000000000000000600e00180000020000008004004000000000000200300000000020000000018000004003802c00e00000000040060000050004000008000001800000100100080040040000008000001002000400600000100000000020048008000000000801001400000080440000000000000008003000000000a0010008014002000000000c00c0010000024006000002000c0000000000008006001003001c00000000000040000000000008000001004801c0100000010000000000000000c00400e000800400000d000000400a0000000000004000000000801e004002800001e0010000008000000003001c0000030000008000000000000000000100000000020030000000004001001000400400100100000000000000018000003000000000600000080080000020000000004000000001000200300100000000050010024000000000000000400100100000000000008004006005001800000600200080040000000018004004005006800403a00000300140020010000008016002000000c0040000038000000000005001400a0030018004000000000000000200100000080000020000000000000001800401200100000000000000008008000000000800c00000000400080040000038000006000000000003000000000000100010000000000000000800400400000000200040030000000042001000000000000000080000040060000000000000002001000e0000030008000001000001c01000000080040040000000000010000000800000e0000020004000006001000c002000000800000400000100000020040000000002001000800000000200080000000000010000004000001000c00600000000040040040000000002000000000000000500000000000010018008000002000002c00000000000000040010000000000000000001400000600000080000000010014002001001000000200100000040040010000004004002000001800c0070060018000005000000400000300080000000000008004002002000000c00200000080000100010000000008000002000000600200080040020020000008000000004000000200100680080040000000000014007000801000000000080000000000008000002002000001c0020030008010002003000001000e00b0000004000001001000801200000200000000020008004000007000800000200c000000000400000000000000000010000002002000800000c0010000024002000000000400400300000000060060068000000007002000000e0010028020002010000000400000100300000040000008008000000002000800800000100080000080008000008000000000000000b000801c0040000008000002000001000
  | 23 => 0x2b7584600052a8001a12000000115800000014399a40009d40000000df82c5000000000000000019900008bb1b600c4eb400000030c0000c25653800000018207880ec26c000003800031abd208ab7ccaca3bc0001b100dc0000080bb45683140002b5800000052700009e60780001e2c0006960000000000d5300000000000005d900000000e761925d80000000000000000b19462800000000000000000000000000338b6000000000016b48b238c800000000000000000000002bd80000004431c483f800000005a88680000000000001c6e000000000000052400000012d6507000137800000000000000000953ed08480000002cab378e4e86300000000000002858f9800004f0ed8a7c00000052bb4542a000062b87f8000d8300000007c00350b200000006a604e0000af20000000154e8809100032e800000000000002b67b76000001564b922ed31f5b127280002a05b3e00000000009d20000000000000c6c000000000022b1fc000000000000c0000de60001c2b5ad882c023450000000000173a0b8e422b10a1000000000000032883e400000019f81e80000000000128124000000000000000000000000003698000000000000000000002c000000045e26d00001d80009bb0000001b92c1b00000006dad4c4ee3058000b2300000000000000001c8066012d0000000000a6f14a9bf400000000000015f000027e80000000000dd0dd851c0000000f413c6d3c63a8b00ffc4222192d015a08a600b9accb16b5f40daaa9c4e00046dadc40002155fd1388e763bb0000000ec20000001f90324bff49625ec0009841aa0000000000000000000000029e2be8632c2e60c385c0003a80000a14000000000000000000045d00000008b3497000030e000008aff1b800002af800000076d0001c5000000000038300000000000428dc20000000000176d8a00026e40005460001e6996c8140b080007480000010000000001000400a002000800000e0010020004000001001000000c000000000400e002000000800000f000800400000000000000000040000018000003000000000200400180040040000028014002005000002c002002003000000a0050010000002000000800c006000001801800000a00080000000000008010002000001800400200200180040040000010004006002000000c00e0010038004004004003800c00000100000300060010008008000001000000000000000100080000000000008002001000000400000200000080040000000000000001000000800000200200000020000010018000000000800401000c0018008000000004000400400000080000180060048000002000001800000800100080180020000000000000000001000000400000180240040030000000006005000800400800
  | 24 => 0x1601c000000000000038b000000000000000000000000002d2c6ea1be000000129c0000000000000b650002a689a000000005880000446432f3822e00034200002bc1370000001a7a0004c82a340280000002c30000c9200000013cc28869c0d292440000000001704000000000154a0000000000000000000042c52c0000000afc0007c400021a09e20003ae892000000000000000000001ed9110bb883d0000001b740000000000000aaf19615545fc0006a1800000000000018880000006778000482107364b04c000000000097d61c00000017787889a84e11d7d5385c3000000044800000000000000003da1294000e0e2698000c1c0000002f9c000c780260000000864367a8f400000005a2b08000bba000201c000ca60000001b1047c00000000004071af8000000000000121c000b83000000115600068280007b4c0a0000000f7e000414a2f0abc5fd19b8c7d23256024080004b00000001c3c0000000000000000000000000183e0000000000000abe487000034c00000000000000005400000e720001bb800000000000007e8b2e276508000000000000000000000000000000edcd4200000000000001f12b5c00000014e8001ad49f84008000974e2d137a864a8a1b42d12b30bba603549361c000cc54c92884a9c0004622c4c0006e727d000085e0005708cd80000d700b07358843e55f200013f200000032348b03ff51323298d6cb90002f6867ac6000000000000005fd80001cc00041b80000000004830000000000000000000071f564800117e00000032cc00000032c00017e602b4d2800000000001d14fd27c08d5c2800000000000000000006b93eb0ab813400038d356c21200020100004ba0006d32b000007f800000000001a86648000000000000000000000000000011180004b0a55d312d2500000007c8a12000237c44e84113a00004920000000000ac290c000000150451c00000000b82013c483c8000bb1332a11d3604d60fa9cb0d2e9270000f009dac8f000000000053522d1480efcdf200000000000000000000000d0600000014d65860000001c6284a3a0127800000000000000fe0ec00000000000000002a209d00000000001616b3f00000000007c80000001914000000072800000012e0001682429704800000098e1a880000000005338001abe00000000000000005ea0000000000000000000000000000000005f7181800064c0001c5800089c1f02dd30f92f000048280000000000000a2c00038464aa1b116200000000017660000000000bae0002fa80016c60001ef9e28ab69a4170000000008e0000b44d128580002ea40000004028001ba837a04d800084a97700000000005281ca1ef800000000000013340002a00001226c6200000000000000002019b982254458001ac2000688000000000000
  | 25 => 0x14c000ae642b80007b05d500000000003500000000000000000000000022e00038f110c00000014280000000000000000702000000000089c000116c6988983528000000000000000000000000000000001731610000000000000000000046100000000000002f9a9fd6cc0000002cb4000000000273c00075c03a00000000002b6ac855e27590002d883564bd2a1800000082a27907ed01200000016740000005639f74000497000000027ecb100032e00000000fc947c0d402a0000a6911c35b08c958cb6e329206a5e573a13d3aa96248c01d44410264a4e0003ea80000000000000000000abb0001e7434600068a0758116000508965845a74e000000000000055e0000000473000000088c00071280018920000d200003a40003bba07974200000000000005333b037b00000004f90c7000056b08a1274d98a4b00000000009ee0000000c7c000617800000000000027680000007190284000000000000000000000000000000000000c343c20000001940000000000000036c68d0002b3858670412aa30000000038c0000000cfe4a1a535c2a0004c50001b7c0006e231dc000abd5a51f2cbcc0002f0869400041a000000040c0006ff31c80000004dc2e58fae64452300000000004d00c10c6200000027880000003dc0000000d98000000076eda528b80013e66ce00000014da83b0002fa00003ae11a0000c6e7d9000058d77cb7a000000000000000018b0000000000000000000033c0231844c8000000000007ee000000000095c4c6000000000057580000003f200000017e21b7000000000047f0002cbc8a800000038a843c0006028000000cf04ab2e2800003400011c14e48166b2a9e4000000675a40c0000003558000000df900000000000003efa791ba05931282b0c0000d52da1ad4000aa3000000000000045c38500000000cd38fc53c6d80000fdd26c0000cb0001406000313800000000000000000000002f38000000000000240412e000000000076200000015119848a9594857c2787242121f3caba13b0690771bac11a34fa344d8e8da0e72c041a661014229800000000001b2c000231228b4b09140000002c24830c9a0000000000ae24c38000ec60004fd0530b7800058100015f20000e7800000091a03306f4000ce55a103dc00018e2d6800000200000008dc85021700000000000000000000c420000002fb97f2c743a5219d3fc00005000003ae00055200018ec0002f70000a067f10001630a34c3f5db80000000000000e940002210001f840000000002f0800000065600000000000000000000d000003755a62000000000000000000003e18c600067600016924f62b1134400000000034b40007900000000000d9e000000094600000016f4000772000168000000047c09698d2cbc6bd800080800070180004
  | 26 => 0x102000000000022a80008c74e1a975af02bb000124c00000000006d4de00000000cd000097c0002b34000000000000000000000000000009df0000000000000000290800000000027c00001d52933545960655000000143e0007088001b2ed1c00000010383e80001ebc0009f665f80019e400062db7a80000000000000000d1300000006220006fb000000031033e8c4981637266180000005946320001c020901ee0000000d765eb00000000001a70000000a9623e92fc7ba000000000000000057eb52439065a0001c147e601e48d8000ab865321521c0000a650002bb0000d3a19cac20000a18000037016c9c500000018a83c342024c5294000000000000024b6e78000000000000000000005b28d98a40006182e899383b0dbd000000000000000029e124608a34c17a84f80001530001648d6e00000013ee00047b90f0000b9400004351b881f5da0d8457c3b426d23e5b8e0001f3a2d4c5ed7269a1fac0000000000ed8000000708000000000041880000008720002bc00000000000000354000000000040a6dc5510000c9619730789c80009c666691280000001e68c89c76bc50b7803d01e00000023888b200000028f14ccd6400000014468af1b896840000060001d79274bde0001b687423b32ddacdcde875800028a901627b37b0000000dbf2c823400000000000001a900002fd00019680003e380007340000000000000000000004ca768ef5a2ab64000122143000038600000008f16bc1021508000000967000062c83a4aa517b8d000016c27301a47645f407e922000024512c8000000a8c00000015bc82731fb8e10227b600000000004cb5bd8b6c4c88031fb2440396000000000000000006526598200002e90000000000545000000086e25f02dc1c842b3098bd4bd642d0000000000d3b00000019a40001ea0b6139c0000000000982000000000000000044490e1c380000250000000a1e6a71d88000a9b68d21e1092000014000000000032a000038000000000000008fd0000168f3e0c4000198c00026a00000000ea00000000000000000001548842bcb066800001c21f384199c6d40004aa888800000000000000008920000000aee0005aeaa40bda7bb000000000080400000000000002db029c9600001a4000000021c000044c00000024fae242803173e080000000000000001a500000002e3800000000034e54700000000a084ee344000139c3b46056ebb829bb000044e93600001013bd000130000015e00bc0c07b100000014920005d6a5180009a10001615758d8c30a880c000e040000000db685535f28c400000061500000008742e680000007c60000c54310d1800000000006c800000003d6b791c718b80003ba0002dcd1a600000000000000000a7a66054ed8600000000000000000000e966520
  | 27 => 0x4b9000194077467180005c4000000000000068300038f83ba4530fc199800000007700000000001a09415754d8517eb6e0000b9f2f6348c000000000121800000020913bc000c7b00014a5a94000438a08083c98519f9be556e96d4571fd57d8c99000067c8d432f6ef02c96d60000001cb400000058faf8c0000000001870bfc0002700324d8a00037d0001920d1f00000000000000000000d64bfd000374c0000004950001b4400000000000000006998034000be5494b7880000004441ac0000e2467400258d049513f32599b2000586afd8592cf900000000000000002d313bca680000eb4ba0b5300000014863af6a9000000074100021748809ea1348000000000000000000000000007ccf9200000000018b00000001a0800000000000000009a700000016d210026a96480003fb3891e8431200039e8411b4212a1f6b58800000011b00000007990fe3604000000026800000056600000019d27cd06000000000006569ff51485d83981370ad274550280000006c230580000000000000000a0c0003f780000000003b600000005cf1b80b9077223e0000000000000000212000000000000000009f100000000000000ce267800000000000000000000000000000af400000000000000000000000000000000160800000000000fa2c76d88001c046b422f228183a74206580000008d60001aec000cda530800000089a0000000b9200000007f4000000000155cc3c00000000018384b5528000106cba536a0000000cc611916a800041f0f78000770a1d0000000000000000000141a0006f480008d0bd50000000a0400000003502860006d59bac0000001dea3b400035700000dc00000000000000000002c236593aa00000000002a8c0c0000001a5677b4d729a592eb4326a1dd82067f736facb90100000948000000db300027658da00036a8000000000000000103000032ea76d4f4734361800000000000000017184f9000000000000000000000004e300019f00000000f700000000001f7908d3d8ba84c100000000000000000404e1900000000007e348b0000e98000000153483696a0aea2dc602000000000191684d47180000005f600000000001864e8800000000049db13400000000029cc0000004ca000000000008e8000d4000000025f48b8000000000000000000026c80004b669217c80000000000000e06000151a3b0e4400041198196aea0b65700000f46403488c4cc641c700000007c68fc0002d51638000577800108c0000000fb8000d0f59c80000003aa00014dd566a004608001298000000000000000000012440003903402870000000000000194851665ab0980000000001ea80004ca58e88cc71a261198b0b4000af60000000000449703000000000000000000f80005caa7ec664b77000000000050e0000000
  | 28 => 0x18fccc71cc017c9fcac55240becc3253654f86c4000d1e000000000020f0b90001282c3934d800000000000000013c000000000002c00000000000f380000000000000000071333cf5c2686ab144580878e0000000000c3a55fa38114e000616069c0003435a38b79b8c7b36bea39800000000034bc6180004941c1d17c0000001a38d3abb5000000000077100000005740003959638000995000000000003d2048000000e1200026f0a600000003465a968171bfa3ac0000000000000000000000156400073700022b4798aad670000004e7a44310484a94bbc66ea3316508d4000000122a63b00013740004c6343000000000000000000006e210380000000000000001c1a00000013399880000000000000e1e35b000000000000000019ea00000000014c60000001660000a095350000000043000000094400002b0000000a2c6a20cac0006261c9000026a0004f5930c000c852bf00000005ce1a937140000000000000000ce40003404af0c9b5c4000000009231400000006ef000000000000000000000000000000910a960006af252400043e00000000004805620f05ac60e10be10b8fa24b730a0e1800000030b978d34687d5b09bec0000000001720000b8100033540002b2643a1f80789c125d92d1574dc2141800056c8fe484068800093d000000000064326380000000005051c5c0008f371800001a238a000247c000000713000000017e000000156800000014a959e000000000037200049900000000001a32951034000000000000000071d3304fcc28149035ddbca11e5ec01c400088a00000007329385df821c0007dc00000000000001548000000b753ffa8a400065f00000000000b100000000000000a4800060e0000001e887180000f40000000000000000182e000177879c00000034f1d0cef01e006e9a4c00022600000000006e8000264c4d62d600021acbb68e90338000000000114124871e86644200000002f30abac44000a580000000e4c0006798001c4400000000000000000000000000b2200030510ac17000031f000000023d80000000000000000a100000c50c8400009e00000000009395e9926c000000596000077c66000031fc000000000000188e00000000000000000000000a7cafc42d1728f580000001ec80000000e3137c0007860000e0d3a400000000000004e13d40000000d0c34c9dd492000a6a0144d9944cc29ea4952160bf3e98000000db00a58000000cd300030cc00000048e80000000001e134f80000000001194f0622a000283d5a8a942f48000cd474643b000010c34d6aab580dac34200037700000005a896fc0000000002099b58000241275cff8d1656d89286fa84c06fa51d9fa000147a8802506816271924a32bd96e580000005f1222967038a00000025800000000000000000656
  | 29 => 0x2000000000029104100b482836743494e15aac203b283fd0bccee5b40af400048c000154c000a400002c780005e2000000129eb172890001a8e0000000001666000000000000000000000000000a900000000000000000000cec37c00024019504f554c800101a000000000065a00034807880000000003489056d950000000e20000000000000000004402ac00000000000015941b219d800018a00000000000007570bc0ac0d501e30be8000000000000000000010f668b434bf81d900004bc000000312000000000041c000000058a38980000007b555030d5a0e6aa1ce312868000000017fcbf200000017c0bca8615ee1d4ceb6000000000000065e0000001720acb0290c9436635a0efaa3cf222eb67c08e0596000316b1207ae00000038a04988c90002fb4000000000342c0008a200000017d60004de8000a920005fa800000000022f8000cd00001cf223400000045a021400000000000000000000000c78000800040b0900c400000014b547c00000005ed1bc26239d31bdbc84c96870538000c3b000278400000035117ec0003270001f397f0bf24cea74c6c6d45157812400093755a80000006c015280000000002cc9410cee47a00000005a000043f9e4895aadc0000000d24a226ec93653960f52370494a0000000000000006af23c9e1028c000000372000000039a8000000000000291000085051c800094c90d000000000000000000000000000a3ab613ca51e07b07080600000000000f2812600000000000001da8000000cf60001678000d8e10a0000b700005f08b5c000000000000196e00000000000009f400000009d4cc8000000000000000000000000000bb00000000006299dbc6c4caa00000000000002a614b89500000000565660a2e3e900017c4e3d00000000000006fe84e400000047800000005b500037f00001480c80fa88a0c032bf8000b72bdd00000000002a200d800000000000012e14f82b50f500014080000000000896000000000000000021b388c7520000000000e3663d4eeaee5078881000286c0000000000e04dae20c2458000ce400013aa5f80000006bf233db54a851b78b54fce74f0000000000000497800000028a00000000005a923688ec00000039500002249810ad2965c801323dc81092687f935d000000067a000000081c00000000000000005e6000132200000000000000002d18000fd0ab91ac868574c0002ea0000000000000000109e72e26d8000fc40000000000000c0100005fc00062562ab1640004106f58000000000000129c00000022900012b40000000000000000604000038801256d1489a365cc5e482bd6fe36e2d28bdc000000716000149a00000000007a6dee00000000000000001bb840000000034818bc000000000000017100023fd7263f12211495be8c9c24caba
  | 30 => 0x35c000000000000000000013f007c0000000000230c56345aa10270675108b0183607db36680016a00000002bddaba0000000000000000000228c5905d64b280006ac8340a9800000070c000242400000047a800000000000028058865f800015cc0000000b5000000000000000000ca0ed00000000000002a780000004623beb1cd8e20c700006603c8b6e6e732455ca0006460e5995620800000000003643d5ad5484c00000012500ae9830000c198a0a344a98c80000c5c3f80001a6c0002ac0000000b6f0000000000ad221880006f000021e8000ce86a359c2bb80406ec00000000000000001f8000035500000000006ed61487d1a1000066009440000380001a916e843a03817bc8e8ded1fc80013fa43b0000a80b8e7336e1a8d8cae00000022400000000ac084d73076700000015165be6ff80000000004b600000006a73370000000e1d48e2ab000000059b0744000cce209ae90c78a25373081000037460c9b904fa00000000000007800000000c6c26600002f99040002e58bc400000002380000000000000000000466000000000000000000000000001f800000000001b000000003d5000000000039b44cb674c9a27336300005c2c5f25ca0759f4921000000000000000001902d62796ce19300000005098c14000000000000197a0db000000000000000008f4000cd700000010be00000000000002dd32280011a431800000000000000000000000000250349931aa3525e289da0699900009599e8ba0231aa45736d4d3fb239107ed574528000f0e3a24d49780f840003b80000000000406000000079300000007a4000000000110a2470001e35b160001af00000005a40002b9cfd202e302000000000037f17180003790a6b80185072948bb5bc1acdc10000000000e2000027240000000000000000000000000110e00000000018b400000000006d00000f60001b220ad0ce9944000000000000000000000000010a89ac0000000000b9a6288000ed2600000000000027800000000000005988000000d5a0612fdcd94000000000000082c4d893ed020a170001bdc956051678800035e00000000000004ff00000002cc0002470000000caf319800000000000000000003fc000324c8ce223000000000000000000000000000000000000c3c0002854000000072800000083a00015a12de0005198000000b250b7000000000000014311360000003330930aae34a80017a22425a400000000000c28be400000000000200000000000000a200000000000000b4d5c0000055a0ba0000000018b9c1a38000000a6c0000414722000000000000012b0002c3c00053a0000000000de037c14bd38846f58d1e3c000959298b7e8000116000000000000035c211408c0007108000f3600000000000000000000ba4000309000272824e15
  | 31 => 0x2745700002060000000df80000000000c5d0000000b8ae350000be8000000522a4600000806a8000000000007e000160a5c16d682cc0008910b48000c8e000000000010800000000000000001a9b84c0004f8000000000000063d000000000000000000000000002f013fe00014e00000484ee2c110008ba0005be00000000f02992500000a060000000c56000386800000067346125cd74400038e29280000002d3895c00002600001dc000000000000000000b187800013e00063532100000001d380000004cf0fb00000000004630fd40000000000000000000531000000000000032790a295209980002d06884a5ac291e466f66811ad62000058d9ee84a6d69000000000000000023d000028909a225062c29b131ab20000b00000000133e4691c12a7400000000004180003240000fb147e12c00000000002090000d3c00000039180000007ad1a495902e85ac604a1f18c24af644800028200039c2cf4f04000487b4fd39a8ea3d300010322ce000000074ccd600000005cce1a2aa099c63a6113688001ae2a532208ff505eae3000000193a00000000000005760000d60000000000000137e0003928bf000002557fb27c88e00038880000000000001190b227a00000000000b6000025d00006f10000000000000000000000021600014740000005930000000b7000000010ca38062020b4ab400066fb66c00061f0000000000000000000000000000008a5b040000000001a9e00000024cc0000003548d707b223952e000008292b0002dd8000000477000009000000000000000003b22c5587a0000000da4000000262b6c8000000000000197c000000000000000000030680000001c38000000000000000059400000038ac000958000000000069c5cf00000001e517a00000000000000a5d5bec4c000000182a00020311e142c98600000009e8dbc000148c0004c046c800061c0000003284130a5b2a8b5b008a8b96938a919a8c373f68000000000000000000068f00028092c69af0000cd52040000002d70a1e0004cb8000598d684580000cc40000778000000000000381441a2ab00000000000000002cf000071e000127168cd7c45080007960000000001390000425920c0000000002620000000000000061000048528b4fca7816c000009485b2207800940e00000000000005ab00006b4dcabbd047a1dd9b69702cd2bcd5a60eb0e0b47599674d00f8f3d842000172a0885fe3e101b10c0964d8f39895206465746590ccc49e0000dc00019f893f61c20cc00043f358800136a00000000000007fb19c000000047157d9c74000000000000000026e00029d00000f90000000000000000000084e00000000018ce7500002ae1b6a00000006800007660870eb0000000000036873ad350000644000000000000000000000000
  | 32 => 0xa69a520005b68000000df700004204860935388000172b3a6c931482380006440001278df009f3858000000000188102600038300010ea30041f1e9d74e5a66d736bcbbeaa60001858e6458718daed9b288603cb800018610c6bf85105d8ce13e522a031e0000003260e160005c88000000000208b4c99ce000681000047e5716ed80e5004000000241c0003930002f5cb1e96e000000000000046682a000000053b800014643400000013985b10003115ab016716e1fe800083000000008900000f8a5e8c9400031a00001700003a89f514ec0000000000000220000000000027f256000000062300024901540000000000b5c88000028692c80004f794ac0000cf29a060c0bc419000000000068c0000604000000000000000000003d80000000000002394c022d94f68cf1c0e1bc54f00000c200000026d971a0000000001ace31a6f7800000041700000019b82d30000000fbc14a6c98000000000000000000000000000000000000002321790ac132d93900001a90002445b68bf0250800000002900015411060003d28000000a5e25480010b600000033eceac00002c000000048d169000033200051829440008f11d58980000000000000000000067bb7840440006e500000000000000d2d6545835a219180008794b48e80f2a0000001e1400000044990dd81a4d7000294800065c2cf8000000c4b44a814000000000000018626f252d108000000000020e489ab3e000000000042c41435cdb4e7470000000966000000000000073f46a8000000aed00022580000000002df528800000000000008d700038600009710000000148000000338800000071b1824000baf47b0add3363bf010800090a00000015b0000000568ae643361205e186fdb3400067f80012be2a80a895044e000001186ed34c0000000600000299000000000067914c3690000af528480008024156db00000000000000918000000116000000026c00011d89d60002ab018c28a5c246e9cf00f200000026f800000000000001d000030d214d06adb96ac80006160006fd99c4746000068107000061b5990010e2a00063283052fe0e93c628a0000ac60ae0001a2ed8d3b52ba48aa0006230000b0060a105000000000000000000000000000000000000000341000000000000005be000000000163000000000000a800013d000000000006c0a480009c70ca80000000000000000000000000000000000003423841f63d60000938000175000096c0006ea000239c00000035e8000000a2b6db8320000518000387c1d470e6c81830000000000000000061243d00000000000000000000005000262dc5200004b00000006ac593800000000010e800000095b22603784e200000000000000000002029c1e00053e80000000000000cb800020e00000004a4c7943500000000
  | 33 => 0x34b800052c37480014ac00000038e4c100000002514dbaa320001f0cd420000000000000000000000000000000035c1bc6b3b5c79308000da81ae9f3000079600000012d0000000000000000000002240000003360000ea87880000000000a703e82f405542540002a5c00037e0001985b9a3fa2780facf3cae432c87240804f72be0000d5c00020b000000000000000000004c40000000f8000010c0001526de76332c800000730000000000000000000000084453f000153067070400000000000000001ba49fc000190400000033f80000002da0000d15410b8400011c880617a0002cd16b0b8b5edb7a00321770000e20b3600030eb7454f6366000000061470000000c9b08000000000197600005e2a2400000000000013ce2cf0000000a840000002521a22975496b7c400069452f8330650b5900005e40000002c68f4517a1840002ba80960bd356a85183c57067502941068c300017907940000000000588ce600026dc2201f700000000000000980000d0aaa709d123c00000000017a0b6616d1ff0554000000000000109c00000035180000000000000000be64891014a280005d8000000000322796047bc66b000000000000064a0001550a3b3f90f1c0003e90002d3c8ee0000000bc800000000007fc00039f12f000000000043db79800000000000000000000000001adabc6303800169c280558b03d7be00032795bc000a4c0ab07780006b70000bc000000058a0001506ddf0002d90ba60fa71787300004d2000210cc6037b4b12f055e400000006b0d82afe4e00934000d2160930d00000f30000000a2a01a20580fc2464e54129c29ae87f422b80000001d31598000066bb848200012a8b78000000000000042900010b23c5000000179a00069bb110a42bfe0000000aea00025891d4da00000002c0c0000000e810e5af4000264236000000000026a800000014800000000005b918340007bd00031c0318d543a404b93d286f5d18000000293000227d656ae0000000160ce0b06c80017deca30001ea4f602940002ad8000000000000033c98f2ec800000040a000301c00000000021b4000165000046c0ba2ee00011f8efe00007014e4000000000000000076b3f9aa38000e1b00001c99525474dd225c000c835b60798c9000061b291c000000719af28000c6e36f000046000000007a40004331e315e80000001952cd4d0e50d280800043200066c26acda411f5e2000000000000000013680004a1000000095100000000000000000298158015000000000000000000000000001e400000000000000000000000608a760000d1241900013a091e6d484c4222000000000000088f54aad6c000a0c25700005c60004fa8074e5e9666138a3400000000027a00000005d700000fc000000313c00000000000000005670001
  | 34 => 0x4090001b4073e3e280005d000000000017c00000000000c7400024b1fb0cdab1210801391f6000000245194a0000000000000c2b37a8bd800000000000000000005b529b8ef8a371630001bb462a000038c000ddd0ca00000000000000000000a4142111b0d7e3971fa000000000045b000000077300032051d000000000016ce05915c8ec05a80c6000000000049a0000dcc0006d91668000000da30378ba9c5c0000000d94792bcf00012240009a20000a30000302000000113c00050700000000000001af172e00000018e086a815000293c79cd66000000000000000000000009d60000000e120a237f8be0b8000000002b80004843ec254046a0002e21b8c00033e035800133800027624c0e6cbf455580000007bc000000101c95d12008e8dc085c2b70e5591c0000362fa4000000000232c0008ce5d5800000000000030394c879869822b0e922c12c40000000000676800150e92600028910e60004af16bc0000005580000000000000000000057d33da090000b7e000064d70c36b2b92aa40000002b50000fd4df50003429af27796ae086cc72d750581e8db32dbb6a08ce926a0000002d480000003a92a8550cbea47d07b4c045a85c380004ca64215601b400000051d34a8c6a000000000162ca750002c1ced0701000000177600000026b578e4cd00000000008210002d580000004d98000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe3485441640840956f00882c810813ace01105902100759b8220b204200eb0704416408401d64a0882c810803ac54110590210075918220b204200eb13044164084cdd6440882c81099bac48110590210061f2a2edaa04203a3e84597540840917f0eb26a8108028fe1564d502100c7c406ecaa042048f4815d954084011f700bb2a8108063e20176550210243e43acaaa04200c787059554084091790eb22a8108032e1c164550210063ab2ee2aa04200cb564dc554084011f30db82a8109931e99770550210063cb2ee0aa04263cba64dc15408401972c9b82a8108033698f70550210246f43e86b184206ace82d0d630840d1d904b82c61081237a1e3058c210256b40c60b1842018dc874c163084039e4e0882c610803b48c11058c210076898220b184200c5f759d5630840d59904baac610812b52057558c210054f420eab184200a9d841d5630840d59d053a2c610802b360a7458c210256a40ae8b184200a5e851d163084014bb0a3a2c61080387d525458c210056bc0aa8b184204ad48155163084015b700aa2c610802b62015458c210256b40ce0b184200ad5819c1630840159f04b82c61081ab32097058c210256b408e0b184207ad5811c163084095ad03282c610802b56065058c210256b408a0b184200ad58114163084095ad03202c610802b56064058c210046f43880b1842008dd8710163084014bd0a202c610802976144058c210356741080b184200acd8210163084095ad02202c610802b56044058c210072bc2a20b184200e54854416308401d2f08882c610803a52111058c213356bc1220b184266ad58244163084095af00882c610813b4e011058c210076938220b184200ed1704416308401da4a0882c610803b45411058c2100769a0220b184200ed04044163084cdda440882c61099bb44811058c210243ec2aeda984200c5e535db53084054bd06b2ea6108038794d64d4c210246fc3ac7a984200a5f8558f53084090f90bbb2a61081a3b2097654c210247a40aeca98420487c8759553084091b90eb1aa610813351c56354c2100636b2ee4a984200ccd63dc953084018eacbb8aa6108033558f7154c210245e426eca1842048dc83dd943084091e902bb286108122f21d6450c210246e43ac6a184204cd47158d430840196ac9b8a86108033558f7150c2102579408eab004205af1811d560084014f50a3a2c0108029e61474580210056d418e8b004200ad9831d1600840d5d5043a2c010816ba608745802102579408e8b004205af1811d16008401c76a92a2c0108023ee1d54580210047c43aa8b004265aeb825cd600840d5d104b9ac010812bca04735802102d78c08e6b004200e5b5394d60084015750829ac010802ae61053580210357541686b004200ae982d0d60084014f50a21ac0108029e6144358021
  | 1 => 0xd0fb2aa8908031e1c365551210062e318eab1a420987e87dd563484018b8ebb9ac6908031b1d77258d210063a3aee2b1a420087f855c163484130f90ab82c6908022fe117058d2101c5e422e0b1a42008df835c163484011df04b82c6908029761763d4d210043fc2aeca9a42008ef825d953484011ef02bb2a6908021fe157650d2104c3e42aeca1a42008f7815d943484011f700bb286908063e2017650d2101c6f43ec6a1a4200c7765dc552484011bf06bb2a29080a3720d76545210256b40ec698a42018ee86dc931484055ad0db1a62908127521d324c5210256a4326498a4206cd4764c9314840db88e499262908261fa1c43994210043ec3887328420987e8710265084010fb0e204ca1080297a0c40994210052ec18813284206a6e8210265084014db04204ca108129da0440994210053ac08813284204a76810c265084014eb02184ca108121fa1e54594210061fba4a8b28420487e8794d65084018bee729aca108028fa1053594210051ec20a6b28420487e8794165084094ed03282ca108061f21d50594210253b408a0b284201cf2704416508401ce4a0882ca108039c54110594210061fba4e8b284204a74815d165084014f700ba2ca108029e20174594210062fb9ce6b284206a6c825cd65084094e902b9aca108028fa1073594210051ec20e6b284206a6e82d0d65084014db05a1aca108021fa1c43594210043ec3886b284204a76819c165084014eb03382ca108129da0470594210053ac08e0b284204a768190165084014eb03202ca108021fa1c40594210043ec3880b284200a5e8310165084014bb06202ca1081a9ba08405942100536c1080b284204a768110165084014eb02202ca108129da0630594210053ac0c60b284204a76810c165084014eb02182ca108031de1d10594210063a43a20b284200e37844416508401c6908882ca108129de01105942102739c0220b284200e72704416508401ce2e0882ca108039cd0110594210073820220b284200e72304416508401ce260882ca1099b9c88110594213373890220b2842048be8790d640840917d0f202c810812ada06405902100c5e43a80b204267eb34044164084cfd6080882c8108030fdd675590210255a40aeab204200abb805d5640840157100baac810812ad20573590210051f428e6b204200a3d851cd640840117d0e29ac8108022f61c53590210255b40ce0b204200ab5819c1640840147d0a382c8108028f61470590210054f418e0b204200a9d831c1640840d55d04382c810822ab60870590210255b408e0b204208ab5811c1640840956d03282c810802ad60650590210255b408a0b204200ab581141640840956d03182c810802ad60630590210255b40860b204200ab5810c1640840196f0e882c8108032d21d10590210071bc2a20b204200
  | 2 => 0x5705913104c3e42ae0b2262008bf845c1644c4011df04b82c89881a3b209705913100c7a43a20b22620387c855db544c4011df04bb6a89881a3b20976d513100c7d404ecaa262008f9809d9544c4011df04bb2a89881a3b20976551310047dc02ecaa262018f8805d9544c4070fd0fb2aa8988031e1c365551310246f436e6aa26200c5f65dcd544c4093ad03b9aa89880a3da1b7155131014eb41ee2aa26200dd031dc1544c4010ff0ab86c4988261f21570d89310045fc22e1b1262038bc845c3624c401aa863baac498803550c47558931006aa18cea3126200d54315d4624c401b2862ba0c4988023be1d62189310053642ac43126200dd0315c0624c40d0fd0b3b6a49881a9b20965d49310062fb2ae729262049d4815ce524c40d1e90cb8ca49880a7520d71949310066a18eeca926200cd4311d9524c40d0f90eb2aa49881a9b20965549310043ec3eca2926200c3f655d0524c413878caba0a49881b2b1897414931006ca18ae82926206ccc625cc524c4093a902b98a4988032b5d362149310347a432e229262029d4835c4524c4010ff0abb484988261f215769093103476412ed2126206ccc625ce424c4093a902b9c849881a3d2197190931014ea41ae321262068bc87591424c4071dd0fb12849881ab3a1b624c931024eb43ee29926200bd1801c5324c4018becbb9aa29881a1fa1e50597210053ac0ca0b2e4200c7b7094165c84014eb02282cb908039c94110597210345f43c80b264201cf07044164c84d5d6080882c99080237e0d76553210146e41aecaa642008fb805d954c84031f100bb2a99081a1f21d65553210063c382caaa642068bc8759154c8401970e0b22a99081a1f21d6554f210152e41acaa9e420087f855d943c84130f90abb287908023ee017650f2100c7c402eca1e42068bc8759143c840d998e4b1a63909a61fe1570596210045fc22e0b2c42038bc845c165884010ff0ab82c9108261f21570592213445fc22e0b24420387c855db54884070fb0bbb2a9108023ee01765522100c7c402ecaa4420087f855c163884130f90ab82c7108022fe117058e2101c5e422e0b1c4204cd47158d32884093a90e9926310812b5219324c621036e23926498c4200c5d7394f65484014eb0329eca908028f61053d95210053ac08a1b2a4200c5f751cd6548401998e7b92ca90803351cf71595210043fc2ae0b2a42008bf845c1654840717908b82ca9080237e0d70595210146e41ae0b2a420087f8759465484014b906b28ca908021fe15705912104c3e42ae0b2242008bf845c164484011bf06b82c89080a3720d705912101c3e42aedaa242008df835db54484051b906bb6a8908063ea0276551210047cc04ecaa242008df835d954484051b906bb2a8908023de0576551210047dc02ecaa242018f8805d954484070f
  | 3 => 0x6b00a209a7a85d0d60144014f30ba1ac0288038e55343580510257940c86b00a200af18190d6014401c72a8a1ac0288269ea1443580510053cc2886b00a204af281dc960144375e303b92c0288269ea1672580513753cc2ce4b00a200aba849c9601440157309392c0289b69ee15725805104d3c42ae4b00a209a7a85d0960144014f30ba12c0288038e55342580510071caa284b00a200af38150960144095e102a12c0288269ea1442580510053cc2884b00a200a7b854c960144134f10a992c028802bce0532580510257840a64b00a2008fa870c960144011f30e192c0288269ea1432580510053cc2864b00a200aba840c9601440157308192c028812bca04325805100578c0864b00a200c5f7394d659040147b0829acb208073c9c1105964100e7938220b1c8200a5f8558f5390401974c0ba0a52081ab3209634ca4126d5d424eab048200ab9849d5609040157708baac120936ae211755824102579408eab048219af1811d560904014f50b39ac1208029e616735824126d5d424e6b048200ab9849cd609040157708b9ac120936ae211735824102579408e6b048219af1811cd6090401cb6a729ac120936aea1053582410055cc20a6b048204af281dc960904335e303b92c1208029ea1672582410053cc2ce4b04824daba849c9609040157309392c120802aee11725824126d5c422e4b04824daba84149609040157308292c1208023ea1c32582410047cc3864b048200a7a850c960904014f30a192c120936aea1032582410055cc2064b048204af2810c960904015e302192c1208029d60650d95410063cb84a1b2a8200a75811436550401ce4a0886caa08063ea1f70595410043fc2ae0b2a82008bf845c165504011f50e382caa08031edd470595410065dba0e0b2a8201cf070c4165504031e90e882caa08021fe1d65195410053c402ca32a820087f855c362504130f90ab86c4a081a2f21170d894100477c3ac4312820687e859db52504714f100b2ea4a081a1f21d65549411953c402caa9282068bc849d8525040d1790eb2a84a08aeae201655094123c3ec3ecba8a8200c3f65dd151504090fd0f2a2cb188030fdd254596312443f438a8b2c620187c87541658c401ce2a0882cb1880e1f21576d523101c3ec2eecaa462048f4815d9548c4011f700bb2a9188063e20176552310062eb2ee6a946200a5d83943654c4014eb03286ca988031e5c250d95310053ac08a1b2a6200e7250443654c401b8863b92ca98803710c4725953100637ba8e4b2a6200ccf731c9654c4019c8e5b8aca988021fe1570595310045fc22e0b2a62038bc845c1654c4011df04b82ca9881a3b20970595313667239620b2a62018f487441654c4cd9c8e4882ca988021fe1d651953100536412ca32a6201cf270443644c4d7d6080886c8988021fe1
  | 4 => 0x44c8031f50fb82c8990031edd770591320063c3aee0b226400cf371dc1644c8019e0e3b82c8990021fe15705913204c3e42ae0b2264008f7815c1644c8091e902b82c8990023ea1c70591320063dba8e0b226400c78751c1644c8019e6e2382c8990033c1c4705913201c3f42cedaa2640087f87597544c8914e902b2ea8990063ea0276551320047cc04ecaa2640087f855d9544c8011bf06bb2a8990023de0576551320247a40aecaa264008fb805d9544c8031f100bb2a89900e1f21d655513223d3a40acaaa264098bc87591544c8138b8cab9ea49900317d9773549320047dc02e9b0a64018f8805d3614c8014ed0ba0ec2990261fa1770d85320043ec2ee1b0a64038be84dc3614c80117b09b86c2990063de1d10d85320053a42a21b0a6400ab484443614c8011ef0eb08c2990029d215611853200c7d43ee0b26a200cba84dc164d44c997309b82c9a89923ea1c705935104c5f43c80b26a20487c855d943d44011f700bb287a88063e2017650f510145e43ac8a1ea20987e85dc162d440717d09b82c5a88022f6137058b511953c402c8a96a2008fb805d942d44031f100bb285a88aeae2016450b510065ab26e2a16a264d7351dc154944432f50fb82a92898f1eddb7055251006b9b8ee0aa4a200a5d85d0d6394401c3aa9a1ac7288063721d3058e510052fc2a60b1ca200ed13044163944099a8e2b1aa7288029e2015458a510053ac08a0b14a203a3f8655142944ed67100aa2852880317dd5634ca5103566412c6994a201cf27044364544ebd6080886c8a88032e1c3645515100666318e4b1aa200a6d850cb62544015cb02196c4a881a1f21570d89510045fc22e1b12a2038bc845c362544011df0eb10c4a8802b320d621895104e3bb0ceda92a200b71801c552544018baebb1c64a88261f21570590510dcbd43ee0aa0a20987c855c1631440117f08b82c62880e2f2117058c510245e43ac8a18a2048dc8758d4314401c3aa8b1a86288029e20154588510343ec2ee0b10a20987c855c16214409968e2b2284289d2ce20154508510247643ac4a10a200e2d5458942144138b8eab1a6428813351c5634c8510247643ac4990a209a7885dd160144134f50b3a2c0289ce9e61674580513263c3ace8b00a272a7b855d160144134f10aba2c0288269ea1474580510dd3cc28e8b00a271c78751d160144015b5063a2c028802b660c745805100575410e8b00a200ae9821d160144095e5023a2c02886ebc60474580510063dc3aa8b00a21ba7a8755160144374f10eaa2c02893b1e21d54580510dc3c43aa8b00a209a7b845516014413c7708aa2c0288038edd154580510071c3a2a8b00a209a7a859cd60144e14f30b39ac0289be9ee15735805104d3c42ae6b00a200abb845cd601440157108b9ac028812bca0473580510dd78c08e
  | 5 => 0x90c68f614735905204d1f42ee2b20a431a3d85dc564148015750138ac829002ae60271590520055d40062b20a400ab9800c5641481347d0a382c8290c68f61470590520054f418e0b20a400a9d831c1641480d55d04382c8290c6ab60870590520055b408e0b20a400ab5811c1641481347d0b182c8290028f61630590520055b40860b20a400ab5810c1641480117f0e882c8290022f21d10590520051fc2a20b20a409a3c8544164148031b90e982c6290023ee017650c5200c7c402eca18a40087d86dd5431480d1790eb2286290030fdd56450c5204e1e3aac8a18a42187f855c1611480117f08b82c22900e2f211705845200c7a43a20b08a40687e8794165908018f6e1282cb210029d60450596420343e43acaa9c840087f855c161908130f90ab82c3210028f61253d95420062eb9ca7b2a8400a3d8414f655080d17b09b86caa100a37a1f73595420062fba8e6b2a8400cd773dc565508019a8e7b8acaa100335dcc71595420066a398e2b2a84018fa87dc165508019b6e7b82caa1003361cf705954200679b8ee0b2a8400cf071dc165508011bf06b82caa100a3720d70595420047bc0ae0b2a84048f4815c165508011f50e382caa100336dcc70595420066c398e0b2a8400cf3711c165508019e0e2382caa10021fe1d65195420052e41aca32a8400da870dc954508573750fb82a8a11932e1db70551420062e318eab1a840287e859db53508010ff0eb2ea6a100a9720d65d4d420052ec2ec7a9a8400c9d74d8f5350801c3aa9b1ea6a100e3b21972d4d4200696aa2e5a9a8400ccf635cb53508050f90eb2aa6a100a9720d6554d420345e432eaa1a842b9b8805d543508051790eb2a86a101a8f21954d49423c59c402a9a928400c3f65dd1525080d2790eaa2a4a101a8f219545494203596412a8a928477b388055152508015e30018ec2a10261fa1770d85420043ec2ee1b0a84038be84dc361508031ef0e886c2a10029d21510d854200679b0ae130a8404cf0615c261508011ef0eb08c2a101a1fa1e50596320052ec1ca0b2c6400c7b70941658c8014eb02282cb1901a2fa1e40592320047bc0aecaa464048f4815d9548c8011f700bb2a9190063e20176552320343e43acaaa46400c7870595548c80d1790eb22a9190032e1c164552320062eb2ee6aa4640087f855c1618c8130f90ab82c3190022fe11705863201c5e422e0b0c6400c3d74953654c8030ff0ea86ca990031ddd471595320066bb98e2b2a6400ce7721c5654c80117f08b82ca9900e2f21170595320047bc0ae0b2a64048f4815c1654c8010ff0eb28ca990029d205651953204e1f32ae832a6400c3d655d0654c8010ff0ab8ec8990261f21571d913204c3f43eeab226400c5c75dcd644c8018eeebb8ac8990031d1d771591320063bba8e2b226400c74751c56
  | 6 => 0x47dc3ac7b02a8008f98798b60550011f70eb16c0aa002b6e0d62d81540056c41ac5b02a800af38158b60550015e102b16c0aa0023e61e61d81540056d41cc3b02a800ad98398760550011f70eb0ec0aa002bca0673d815400578c0ce7b02a864a7a851cf60550c74f30a39ec0aa18eaea1073d81543255cc20e7b02a864e5b5394f60550015e702b96c0aa002bc20572d81543253d428e5b02a863a79851cb60550c757508396c0aa192ae61072d81540047d43865b02a8008f9870cb60550c94f50a196c0aa0029e61432d815431d5d42065b02a800ab9840cb60550015e502196c0aa002bc60432d81543253d42ee3b02a863a7985dc760550c757509b8ec0aa192ae61371d81540047d43863b02a8008f9870c760550050f90ab82c3a98022fe11705875301c5e422e0b0ea6018f48744161d4c052b906b96a8a98032e1c3645515331e3c3b6e0aa2a600d5873dc15454c0117f08b86c4a980e2f21170d895300477c3ac4312a600ae4815886254c011f700ba6c2a98063e20174d85530143ec2ee1b0aa6038be84dc36154c0117b09b86c2a98023de1d611855300572412c230aa604cf2615c06154c019e2c2b80c2a98029760e50d95430063cb84a1b2a8600a75811436550cf587eebba2caa19e717dd7735954300c7d43ee0b2a860087f855c16550c0117f08b82caa18023ea1c70595430063dba8e0b2a8600cbb741c16550c010ff0eb28caa18029e20165195433265c3b6e0aa2860087f855c36250c130f90ab86c4a18023be1d621894304c3f42ee1b0a860087d85dc36150c0517b09b86c2a18023de1d61185430343e42ae0b26a44787d86dc554d488f8ecc3b8aa9a90e25ea1f70553520343e42ae0b1ea4008bf845c163d480717908b82c7a901a1fa177650f521c4bc402eaa1ea4028bc8759143d48071b90eb1a87a9003875516350f520343e42ae0b0ea4008bf845c161d480717908b82c3a90063d21d10587520065c382c8aa4a40096d82dd5439480d1790eb2287290030fdd56450e5200c7d406e8b0ca4008f980dd1619480117f08b82c32900e2f211705865201c3e42ae3b22a44887c865c754548918e8c2b8ea8a90035a1c3725515223e3a30ee2aa2a43297a87dc154548c78f0edb82a8a90029761743d8d520070eaa687b1aa4018df874c363548014bf0a986c6a90033518c7158d520152f436c6a9aa40687c865d543548652f100baa86a90023ee0174d855200c7c402e9b0aa400a7585d0761548014eb0b98ec2a9002bc60031d855204c3f42ee1b0aa4038be84dc3615480117b09b86c2a90063de1d10d85520053bc2a21b0aa400ab48444361548011ef0eb08c2a9002b520d611855201c3ec2ee2b20a4068be8790164148031790ea02c8290268f21573590520055dc02e6b20a400ab8805cd641481347d0a39ac82
  | 7 => 0x132000d3c00000000010000000000000000000031000000000a3ccc1a10ce3ad0a02b000a50002b4000000278bc5c6e54bba92000c7400000000000000001ea000000007b63d800000480000000fa0005b0003c7462f887180000085400000000000000ef116000001f020c760cbb56000dfcae8b204c7dc003d953c1a4002aa11c000a3800358b349503f0000005b00065a001a70890007a8000005faa944023d0001392d21d5440000000072e7f8a2000000000f080023800000039000370002522580c0d7000000000dca5c25c675a51542fca9984174356ef4000006fa7f0000003fe765450004426240000022aea4bc0127545c0001e92c6000000000000000000002200000000000b60002c703200033000000000000004b67880023c0008780011f000ad456bab000001680000008a916018000000d48003e2000ea000000000a330327ae1000000438f9400000000a14c990d670ee493000226000a9bad0e8410613e3000c7c2eb110000000100000000c0140000100601800000008004000000080000100001e01c0000101c01000802006010020000000000000000601805802002000010000020000200400600803001000000000090000040000100000c0000000401001801000028010020020000000000000c0200100000801807002000008010020080180201200400800002004050000000140000900000c008000060100080700200c00001000000008000000000300700a004000000000100000000000c020010000000000000400004800006000000000000040200500800002806000004000000040000000000001c0080000002802800000008010000000080000000001000005002000030000000300080000004c01002002000000010040200180201000000002002018008050100140000202400400000002000000040000000200000c000048020180040100200a000000000020040080000000c0600b00c00801803000004020000020040000c000034008000000140080000000003801004004000010060000300800a00000805000010000000000040200100401400005000014010070000000200a002004000010000000080200001400801006000000010000000180000200402001016000008000040387c855c161d50031e90e882c3aa002ade1110587543fe3dba8c0b1aa87ec797518262550019b6e6302c4aa003361cc605895400679b88c0b12a800cf07118162550011df0eb10c4aa1f31e5d460189543ee5d3a0c0312a871cb97418062550f98f2ea306c2aa00e1f61770d85540266a30ae730aa800cd573d8661550019b4e6304c2aa003365cc609855400c7d436e0b0aa8408f886dc161550f78f6ea302c2aa0023de1d611855400739288c030aa8008f98798f60550015e50331ec0aa002bc60663d81540
  | 8 => 0x1ce0e2214b080027800000000332000000000000b59db48636001b08311b00000003511e8180013f000decb71763c80000039f000000542ed39a4948525e180bbc00000400561e80000000015b17942c00116a504e0e8c0039c000000000004140007f800000f7400283000545a914200001c0030676600158800792ba11c1cc7360000003c0000013c0004d8f0514b0c23a001d28006565410f94c114a1c281054ccc3c00000380d900016555e094000650000000000007c0000011b5dc9cc0aa4f17a000aab27592a84c3ac2000491e2000000a9c99921170f45c61b2000274000af2ae000001955ba00000379202620762c53400740011400038800000000000000002b4000000005bc1f9018d4000000000002569eceab92000000000000000014f80000000000000000448000005ac000000000007940d800176000872d900081560b4000043d4d80104eadcaf15c65cdbcf68000003a975000486000000007ac001a6127000000baa710000000006d2120a1cea68000dac0028610e720a48006a8001c3b892c400014a49000d40003bc000001250000000418f2740aa0010d00067c1ac500000eced40298e00000182800000000000000004899cb180f400000000000ea1542e00fe93855bb0000000a036800000000000000001621c91e4e792b80012600074000000000002bf00030de400000600000000000694d30001c8001738ac000badaea3f09699d8b1354b077d69a356586509b80003e0000000066200000000000ec4c9049000000001735100008cbda0a2000003657aaf7c8f00052c34815204000ee81e80059600070000000bfd391a808a98929a6b6aeeec002541ae001df0000009b40000016e9a98d1dd03c820fc360000ec937806000cd0003a73ac610000003b800189b2476c1892b1c1720000588000000000009062e0011d814000840f9800000000001bd68c80438000744ce94e982000000000c60a466c00171360dc8001454880000000000000000000000000000de000604002286088bdb9896000a600009a0f8f14ce0000a6000000d50000010d8401988e5ac1da6842d400075000534002454bec489f29762898c97b593cc338fa8f91ac084549c366cacd3f2473e44ec000000000000000000066800000000254c31d0734be00006e19aebc000323c6f982e000000000001112c8d78003000e4000118000005c800143252dc4068007a839426a373dc6d8000da6da2980000000015c0b0000000000000000000000000000000000005f6000000b4000001458000d80009c00057600199abd3e84c09b07b72c000001ec39672894000000f6096afe2949d9411d15eab887e0c92d4001c1800558e18658003160004b80014a001da3010bca38000007040000000031a00167aa00000017600077ec2d400914dc3f40
  | 9 => 0x31c00374000000003d255617d2300034400164380716ba4000001f0b442a02400086400000000c8000000000000001bb1600007dadb4660eca7a091a0f3cd38981d2cc1288dd1a6990001485aeab8000005469e8d8800272ae1a6800282109c0acc67a7a05f370012e604d800000001a2000522f84002363a6000000000000003b800564e1434000206021ee0f11cc0bc0000000003d8480005c0000020717200000275000bd800000000000678006b800000000000000000000000003500b00078000222110000fd000000001eb800000640b5b2a06e00000000000a1000000000ca13b800000208000380002907f323246cbd1a131000c38bd225652b7cdd2552049f4000005180000036a63818c9000059c000000000000002d80000057c2cb932300001600079c000fe800000c840b9b83685ed7cb9441a908000001e6001119c2580af0002a40000012ea2b5727bc003260000010920e0005a4a9000000ae8c508d000860003de6f0001db91a000920300000000000011655a3b49a0000000000000c5f428c0029a4600000027f62a0013000000000000061000000000200000006d80000025000000118001ad39100068ca70005e41bd4980000085c000004f2000260a7000000000000000002d000000088002a9000e9178a260002b8000003182a8000002b6a70000000000000029900004c0000032c02800000000de8000000000cc000007321e40000045c0000023e000001c789e5a873da98f4300598491f91bee3986b6c0748909d3cd0b0000000006200018398f6fc121e304a1e0329d01c55caf297e1af36e995e1800000d8ddc00020e5b45d26164471c0017d00056400388000001078786cc0016e295000000b7800000000001db00011d2628936a844000006780000000049ab983e84350200000000000000d6800560001c68001ce905633cb142a400037700021800000000000000000000004e00000000085883464b2884000000001f00000000013e33f01cb84ef00003879de00bf0005f00000022082c323a1000000000000008e82b0000006cc000006b66f8003cc5aa678001c66ec289ba9eb75c008422d20006fc0021322e0017b89f00092da180006c6f06099158600185000692bcdb48002c00d134800000d9c00000418c08000443a475c00000000d88000005b4db98c99f3540000000000000000345166691a3b55696000000d118a3dc8600000052c0038a000000003c251acc8ab35f3ec001d62f0000001100e164a0000000000006800000000000bf8000e600000000200000e20001dc5a000000000000000000006140000066e118000d900000000335306000003e4000af9a08000000000025900059c20ae400032000227000e98000815e8d440037c000001010003f600000099000001e980000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc19099a0b082c2ae214aa2000000784016000612a32d0e72460f00028100258014e092585701855300703553635cb535080143491595741953200594e553044163944016289055162508510dc1ea63875516014401619931d154580510058a6487455160145014389755342580513a50e25d5450960144016519394110d953100551648315d4624c401585920c5741893100531648311d9524c4018348721110594210051c65c404416508401651931011059421005986484044165084018348721510590210058c654704416408401691931c1105902133da8648704416408401a14852111058c21005b0e497044163084014d1971011058c21005946544044163084016c1921011058c21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x2
  | 5 => 0x209
  | 6 => 0x3
  | 7 => 0x20c
  | 8 => 0x20d
  | 9 => 0x6
  | 10 => 0xb09
  | 11 => 0xb0c
  | 12 => 0xb0d
  | 13 => 0x1409
  | 14 => 0x140c
  | 15 => 0x140d
  | 16 => 0x1549
  | 17 => 0x154c
  | 18 => 0x154d
  | 19 => 0xb49
  | 20 => 0xb4d
  | 21 => 0x1449
  | 22 => 0x144d
  | 23 => 0xb89
  | 24 => 0xb8c
  | 25 => 0x1489
  | 26 => 0x148c
  | 27 => 0x2c9
  | 28 => 0x2cc
  | 29 => 0x2cd
  | 30 => 0xbc9
  | 31 => 0xbcc
  | 32 => 0xbcd
  | 33 => 0x14c9
  | 34 => 0x14cc
  | 35 => 0x14cd
  | 36 => 0x19c9
  | 37 => 0x19cc
  | 38 => 0x19cd
  | 39 => 0xcc9
  | 40 => 0xccd
  | 41 => 0x15c9
  | 42 => 0x15cd
  | 43 => 0xd09
  | 44 => 0xd0c
  | 45 => 0x1609
  | 46 => 0x160c
  | 47 => 0x449
  | 48 => 0x44c
  | 49 => 0x44d
  | 50 => 0xd49
  | 51 => 0xd4c
  | 52 => 0xd4d
  | 53 => 0x1649
  | 54 => 0x164c
  | 55 => 0x164d
  | 56 => 0x1a09
  | 57 => 0x1a0c
  | 58 => 0x1a0d
  | 59 => 0xe89
  | 60 => 0xec9
  | 61 => 0xecd
  | 62 => 0x1a49
  | 63 => 0x1a4d
  | 64 => 0x1049
  | 65 => 0x104c
  | 66 => 0x1a89
  | 67 => 0x1a8c
  | 68 => 0xb4b11
  | 69 => 0x144b11
  | 70 => 0xb5411
  | 71 => 0x104a
  | 72 => 0x1a8a
  | 73 => 0xccb51
  | 74 => 0x184c
  | 75 => 0xd0b91
  | 76 => 0x16cd
  | 77 => 0x94d
  | 78 => 0x1042d1
  | 79 => 0xd4bd1
  | 80 => 0xbcd51
  | 81 => 0x1a0bd1
  | 82 => 0x1054d1
  | 83 => 0x1a94d1
  | 84 => 0x188c
  | 85 => 0xe8d11
  | 86 => 0x170d
  | 87 => 0x104d11
  | 88 => 0x104d51
  | 89 => 0x1a8d51
  | 90 => 0x105a11
  | 91 => 0x104e91
  | 92 => 0x194c
  | 93 => 0x17cd
  | 94 => 0x104ed1
  | 95 => 0x1a8ed1
  | 96 => 0x74c
  | 97 => 0x105a51
  | 98 => 0x5cd
  | 99 => 0x198d
  | 100 => 0x180e
  | 101 => 0x21711
  | 102 => 0x94b
  | 103 => 0x94215
  | 104 => 0x130a
  | 105 => 0x134a
  | 106 => 0x95555
  | 107 => 0x94b55
  | 108 => 0x138b
  | 109 => 0x2d651
  | 110 => 0x2cd51
  | 111 => 0x2d7d1
  | 112 => 0x2ced1
  | 113 => 0x10e
  | 114 => 0x2d951
  | 115 => 0x2d051
  | 116 => 0xd02d1
  | 117 => 0x94bd5
  | 118 => 0xd14d1
  | 119 => 0xd4d11
  | 120 => 0x1a0d11
  | 121 => 0x1a57d5
  | 122 => 0x1a9954
  | 123 => 0x154d5
  | 124 => 0x14d
  | 125 => 0x1889
  | 126 => 0x14d55
  | 127 => 0x157d5
  | 128 => 0x1882d1
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2119
  | 6 => 3649
  | 5 => 999
  | 4 => 27
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (87581+((h/706+packedAt gbK7 (78403+(h % 706)*13) 13) % 4502)*13) 13
  | 6 => packedAt gbK6 (190960+((h/1216+packedAt gbK6 (175152+(h % 1216)*13) 13) % 7048)*13) 13
  | 5 => packedAt gbK5 (62604+((h/333+packedAt gbK5 (58941+(h % 333)*11) 11) % 1752)*11) 11
  | 4 => packedAt gbK4 (1944+((h/9+packedAt gbK4 (1890+(h % 9)*6) 6) % 33)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7e1e0f83fe1fffff87807c0058cc79c8cfecc
  | 1 => 0xf83e00ffc1fe1f007f8007ffcaf0f8e0f3330f
  | 2 => 0xffffff0001ffe0007ffffffff30300ff03c3ff
  | 3 => 0x3ffffffe0000007ffff8003c03ff03fc03f0
  | 4 => 0x3fffffffffffff800000003ffc0003fffc00
  | 5 => 0xffc0000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x426060190a6035473c4836418084c38c8456cc
  | 1 => 0x4a26006948a216094cc0469680b0d8a0b13305
  | 2 => 0x9488a90001554012111291291301005502c05a
  | 3 => 0x3352b5ac000424666562022c026d02dc03a0
  | 4 => 0x841d9cc6319988b80001800c3f5800036ba800
  | 5 => 0xe7001804201110c0000604303fefb6f8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36276
namespace PEqualNP.Outside.L_meta_36276
open PEqualNP.Outside.L_meta_36276.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
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
theorem bs0_3_96 : Interval s0Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 112 := (concat (concat bs0_3_0 bs0_3_32) (concat bs0_3_64 bs0_3_96))
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
theorem bs0_4_1312 : Interval s0Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1344 : Interval s0Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128))) (concat (concat bs0_4_160 bs0_4_192) (concat bs0_4_224 (concat bs0_4_256 bs0_4_288)))) (concat (concat (concat bs0_4_320 bs0_4_352) (concat bs0_4_384 (concat bs0_4_416 bs0_4_448))) (concat (concat bs0_4_480 (concat bs0_4_512 bs0_4_544)) (concat bs0_4_576 (concat bs0_4_608 bs0_4_640))))) (concat (concat (concat (concat bs0_4_672 bs0_4_704) (concat bs0_4_736 (concat bs0_4_768 bs0_4_800))) (concat (concat bs0_4_832 (concat bs0_4_864 bs0_4_896)) (concat bs0_4_928 (concat bs0_4_960 bs0_4_992)))) (concat (concat (concat bs0_4_1024 bs0_4_1056) (concat bs0_4_1088 (concat bs0_4_1120 bs0_4_1152))) (concat (concat bs0_4_1184 (concat bs0_4_1216 bs0_4_1248)) (concat bs0_4_1280 (concat bs0_4_1312 bs0_4_1344))))))
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
theorem bs0_5_864 : Interval s0Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_896 : Interval s0Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_928 : Interval s0Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_960 : Interval s0Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_992 : Interval s0Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs0_5_0 bs0_5_32) (concat bs0_5_64 bs0_5_96)) (concat (concat bs0_5_128 bs0_5_160) (concat bs0_5_192 bs0_5_224))) (concat (concat (concat bs0_5_256 bs0_5_288) (concat bs0_5_320 bs0_5_352)) (concat (concat bs0_5_384 bs0_5_416) (concat bs0_5_448 bs0_5_480)))) (concat (concat (concat (concat bs0_5_512 bs0_5_544) (concat bs0_5_576 bs0_5_608)) (concat (concat bs0_5_640 bs0_5_672) (concat bs0_5_704 bs0_5_736))) (concat (concat (concat bs0_5_768 bs0_5_800) (concat bs0_5_832 bs0_5_864)) (concat (concat bs0_5_896 bs0_5_928) (concat bs0_5_960 bs0_5_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_32 : Interval s0Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 48 := (concat bs0_6_0 bs0_6_32)
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
theorem bs1_3_0 : Interval s1Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 2 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 6 := bs1_4_0
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
theorem bs2_4_0 : Interval s2Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 2 := bs2_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 64 := (concat bs3_4_0 bs3_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 40 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs5_4_0 : Interval s5Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 2 := bs5_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 27 := bgb_4_0
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
theorem bgb_5_992 : Interval gbAtlas 5 992 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 999 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 bgb_5_992)))))
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
theorem bgb_6_3648 : Interval gbAtlas 6 3648 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3649 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)))))) (concat (concat (concat (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240)))) (concat (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))) (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720))))) (concat (concat (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)))) (concat (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392))) (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)) (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648)))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2119 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568))))) (concat (concat (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696)) (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824))) (concat (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 bgb_7_1952)) (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 36, 37),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0feeefee0feeaf0c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075680 * 2 ^ 32 + 4276809920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36276.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[5,6]⟩,⟨.or,[1,3]⟩,⟨.or,[3,5]⟩,⟨.and,[1,9]⟩,⟨.or,[0,10]⟩,⟨.and,[4,11]⟩,⟨.and,[2,8]⟩,⟨.and,[7,11]⟩,⟨.or,[12,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276809920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276809920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36276

open PEqualNP.Outside.L_meta_36276 in
theorem PEqualNP.Outside.L_meta_36276 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276809920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276809920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
