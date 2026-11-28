import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36769.Model
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


end PEqualNP.Outside.L_meta_36769.Model

namespace PEqualNP.Outside.L_meta_36769
open PEqualNP.Outside.L_meta_36769.Model
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

def mirrorSteps : List Move := [swapRows 67]

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

end PEqualNP.Outside.L_meta_36769

namespace PEqualNP.Outside.L_meta_36769
open PEqualNP.Outside.L_meta_36769.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x256a92b800093650ed1ec27c52011000b00c8042f1221aa239b80816980a000184eb000b5c0173150b30000450000432c20c21cbfe43fd43fc43ff32fe32fd32fc32ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc41fd21883f843107b08620fa10c41e421882fca1107fcc220ff18441fd30883f861107fc8220f790441fb20883fea6905fd4d20efa9a415f53483fca6905f94d20fea9a417d53483f8a6905f14d20ee29a415c53483fc86907f50d20fe21a41ff32483fc64907f4c920fe19241ff51482fea2907dd4520bba8a41fe51483faa2907f14520be28a41f451482e8a2907fcc520ff18a41fd31483f862907fc8520fb90a41fe21483fa42907f08520fa10a41ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841fe43083fa86107f10c20bf29041ff32083fc64107f4c820fe19041ff51083fca2105f94420fea88417d51083f8a2107fcc420ff18841fd31083f862107fc8420fb90841fe21083dc42107f48420fe10841ec21083e842107908420bf28041ff30083f660107f8c020fe98041fc30083f060107fc8020f790041fe20083f440107f48020f690041f920083fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff32c43fc65887f4cb10fe19621ff31c43fc63887d8c710fe98e21f531c43f863887fc8710fb90e21fe21c43fa43887f08710fa10e21ff30c43fc61887f4c310fe18621ff20c43fc41887f48310fe10621ff53842fea7087f94e10bf29c21fd53842faa7087f14e10be29c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ff99421fe32843fa65087f0ca10bea8c21ff31843fc63087f4c610fe18c21ff21843ee43087f88610fe90c21fc21843e843085f94210ff98421fe30843fa61087f0c210ff90421fe20843fa41087f08210ff88421f710843f621087fd4d10bfa9a21df53442bea6887f94d10bf29a21fd53442faa6887f14d10be29a21dc53442b8a6887f90d10fea1a21fc43443fea4885fd4910f7a92216f52443fca4885f94910fea92217d52443f8a4885f14910f6292216c52443fe64887f8c910fe99221fc32443fe62887f8c510fb18a21fd31443ea62887f0c510ff90a21f721443fc42887f48510fe10a21f421443fe60887f8c110fe98221fc30443fe40887f88110fe90221fc20443fe20887ec4110ff08221f610443fea6085fd4c10ff298217e53043faa6085f54c10fe298217c53043fc86087f50c10fe21821ff52042fea4087f94810bf29021fd52042faa4087f14810be29021ff32043fc64087f4c810fe190217e51043fe62087f8c410fe98821fc31043fe42087dc8410ff10821fd21043f842087d08410bf28021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0x650087eaa010fd14021ffaa661fe54cc2fca9986f953309f2a661fd54cc2faa9986f553309eaa661fc54cc2f8a9987fd0f30ff21e61fd43cc3f887987fd4b30ff296617e52cc3faa5985f54b30fe29661ff42cc3fc85987f50b30fe21661ff32cc3fc65987f4cb30fe19661ff51cc3fca3985f94730fea8e617d51cc3f8a3987fd0730ff20e61fd41cc3f883987fcc730ff18e61fd31cc3f863987fc8730fb90e61fe21cc3fa43987f08730fa10e61ff40cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617d538c3fe87187f90e30ef21c61fd438c3ba87187f10e30ffa9461fe528c2fca5187f54a30bea9461fc528c3fe85187f90a30fea1461fc428c3fe65187f8ca30ef19461fd328c3f86518770ca30ffa8c61fe518c2fca3187f54630bea8c61fc518c3fe83187f90630fea0c61fc418c3fe63187f8c630ef18c61fd318c3f86318770c630ff90c61f7218c3fc43187f48630fe10c61f4218c2fca1187fd0230ff20461ff308c3be61187ecc230ffaa2617f544c3fca8985f95130feaa2617d544c3f8a8985f15130ffa1a61fe434c3fa86987f10d30ffa92617f524c3fca4987f54930fe292617c524c3fe84987f90930fea1261fc424c3fe64987f8c930fe99261fc324c3fea2985fd4530ff28a61fd514c3f8a2985f14530ffa0a61fe414c3fa82987f10530ff98a61fe314c3fa62987f0c530ff90a61f7214c3fc42987f48530fe10a61f4214c3fe80987f90130fea0261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061fd540c2faa8187f15030be2a0617e530c3fe86187f90c30ef21861fd430c3ba86187f10c30ffa9061fe520c2fca4187f54830bea9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830ef19061fd320c3f86418770c830ffa8861fe510c2fca2187d94430bb28861fd510c2faa2187d54430baa8861fc510c3fe82187f90430fea0861fc410c3fe62187f8c430ef18861fd310c3f86218770c430ff90861f7210c3fc42187f48430fe10861f4210c2fca0187fd0030ff20061fd400c3f880187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea7905fd4f20ff29e417e53c83faa7905f54f20fe29e417c53c83fc87907f50f20fe21e41ff32c83fc65907f4cb20fe19641ff51c83fca3905f94720fea8e417d51c83f8a3907fcc720ff18e41fd31c83f863907fc8720fb90e41fe21c83fa43907f08720fa10e41ff30c83f661907f8c320fe98641fc30c83f061907fd4e20bfa9c41fe53882fca7107f54e20bea9c41fc53882f8a7107f90e20fea1c41fc43882faa5107fcca20ff19441fd32883f865107fd4620ff28c417e51883eca3105d94620fea8c417d51883eaa3105d54620fe28c41ff31883fc63107f4c620fe18c41ff21883ee43107f88620f710
  | 2 => 0xc7fc8798ff50f31fe21e63ff52cc7fca598df94b31fea96637d52cc7f8a598ffd0b31ff21663fd42cc7f88598ffccb31ff19663fd32cc7f86598ffd0731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fea918dfd5231ff2a4637e548c7faa918df55231fe2a4637d538c7fe8718ff90e31fea1c63fc438c7fea518ff94a31bf29463fd528c6faa518ff14a31ffa1463fe428c7fa8518ff10a31ff99463fe328c7fa6518ff0ca31bf28c63ff418c7fc8318ffcc631ef98c63f7318c7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c7fca898df95131feaa2637d544c7f8a898df15131ffa1a63fe434c7fa8698ff10d31ffa92637f524c7fca498ff54931fe292637c524c7fe8498ff90931fea1263fc424c7fe6498ff8c931fe99263fc324c7fe8298ff90531fea0a63ff314c7ee6298ff8c531ef18a63ff504c6fea098ff94131fea8263fc504c6f8a098ffd5031bfaa063fe540c6fca818ff55031beaa063fc540c6f8a818df94c31ffa1863fe430c7fa8618ff10c31ffa9063fe520c6fca418ff54831bea9063fc520c7fe8418ff90831fea1063fc420c7fe6418ff8c831fe99063fc320c6fca218ffd0431ff20863fd410c7f88218ffcc431ef98863fe310c7ec6218ff4c431ee98863f5310c7fea018ff94031bf28063fd500c6faa018ff14031ffa9e437f53c87fca790df94f21fea9e437d53c87f8a790df14f21ff21e43fd43c87f88790ffccb21ff19643fd32c87f86590ffcc721fb98e43fe31c87ec6390ff4c721fa98e43fc31c87e86390ffd4321ff286437e50c87faa190df54321fe28643f753c87eca790fd54f21fa29e43f643c87ea8790fd10f21fb99643f632c87ea6590fd0cb21fba8643f650c87eaa190fd14321ffa9c437f53887fca710df94e21fea9c437d53887f8a710df14e21ff21c43fd43887f88710df54a21ff99443fe32887fa6510ff0ca21bf28c437651887fe6310ff8c621fe98c43fc31887fe4310fbc8621fb90c43ff50887fca110df94221fea84437d50887f8a110ffd4d21bfa9a43fe53486fca690ff54d21bea9a43fc53486f8a690ff90d21fea1a43fc43487fe6490ff8c921fe99243fc32487fe6290ff8c521fe98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffa98437f53087fca610df94c21fea98437d53087f8a610df14c21ff21843fd43087f88610df94821ff99043fe32087fa6410ff0c821bf28843ff31087ee6210ff8c421fb18843fd31087ea6210ff0c421fa18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087eea610fd94c21faa9843f453087ec8610fd50c21fa21843f652086eca410f994821fb99043f632087ea6410fd0c821fba8043f
  | 3 => 0x400800001000c00800400000402800c00000c01002c00001401803000401c00400001c02400401c00000001000800000000000800002402400000001800c00001002400401800002800000800001000400400002800000400400402800800400005000400000000003c00400000400001800406800001000400800800000800000801000400400000000400400400c00c01c00800400000000400000001400400000000009000c00001c00400400000c00401001000c00400800000800400002401000400c00403c00800400c004000004004000000014000008000018004004000000000008000008000034028000000018008014008030000004020000000018010014004010016faa921df94e43ffa1c87df4390ffea521ff94a43bf29487fd5290efaa521ff14a43ffa8c87fe5190efca321ff54643bea8c87fc5190ffea121ff94243bf28487fd5090efaa121ff14243ff21a87be4350ffea4a1dfd4943ff29287fd5250ff8a4a1df14943ffa8a877f5150ffca2a1ff54543fe28a877c5150ffea0a1dfd4143ff28287fd5050ff8a0a1df14143bf29887fe4310fbc8621ff50c43eea18879d4310ffea421ff94843bf29087fd5210efaa421ff14843ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffaa665fe54ccafca9997f55332beaa665fc54ccaf8a9997fd0f32ff21e65de43ccbfa87997750f32fe21e65ff42ccbfea3997f94732bf28e65f651ccaeca3997f54732bea8e65f551ccaeaa3997f14732ffa8665fe50ccafca1997f54332bea8665fc50ccbfea9195fd5232ff2a4657e548cbfaa9195f55232fe2a4657d538cbfe871977d0e32ff21c65fd438cbf887197710e32bf29465ff428cbfc85197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132dfaa2653f544cbfca8995f95132feaa2657d544cbf8a8995f15132de2a2653c544cbfe86997f90d32ef21a65fd434cbba86997f10d32ffa1265fe424cbfa84997fcc932f799265fe324cbbc64997fd4532bfa8a65f7514caeea2997f94532fea8a65fc514caf8a2997d14532ba28a65ff504cafea0997ed4132bda8265fe504cbfaa0997f14132be28265f8504caf0a0997fd5032bfaa065fe540cafca8196f950329f2a065fd540cafaa8196f550329eaa065fc540caf8a8195f94c32ffa1865df430cbfc86197f50c32fe21865dc430cafca4197fd0832ff21065fd420cbf884197fcc832ef99065fe320cbdc64197f4c832ee99065ed320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea998ff95331bf2a663fd54cc6faa998ff15331be2a663ff43c
  | 4 => 0xdd0000030001898000001d40000001b500015e4000001ab0520000000000bb8000ed1920000001c90220001be8298000c74001fb80000000011e0001b6a025a99db8000001b5d5143191acb70ae91d8a74000000002214d28000000001ab833949c7d082930032dd548589680000022289a11b00000000000019600000000000014c8000001880000000cd1a400000000004c80000607cd4c05dc0007c50e93f00007987f82a81815c000000000000000000173ce38000b300000000000000012d9020000000001288501df00000005396d80000000917c40000018b13984940e02f52591721715754e83a0001bc0001d10000000001830bb00010b977156c8904418e14400019ec000000000000580000380d80b757f00012e9270930000fcce2c1709788200010d8161c0d5b8f2d6440019ac0000000018f8a01895c41f61498001f680008fc000651c280000000010f40000000000007d80000000018393ece496c8000e18638000d189709c85d40000005d8000a106794960d15a80000012b01923105356186f04a88bd6544e0001d600001d0000a6d3b0f90be80000014294fa005d195ea1061a15f99b81500004880c4b18c01b700005b0002108000000a91708001754000508000e05a58f9a1c9e000000011e93ba250561c600d0fd00000012380011f0000d004b4000001ba1dca02c00000000041457800000000000000001001001801801000000000000001400801401400000c00400400402000000802000400402000000000802000400800800400402400c02000000400000801400c00000000802000002c00800000c01801001800000400400001800400000004000002000001000000800802400001001000000401c01c01001800000401401400000002401800800803800800400401800000401000400000401400400000800000400000803400400000400002400800401002800801400001c00400001c00400401000000800001400000400400403000402400001c01c00802400400800000000000c00400c00000c00400400c00400800400400401004402c00400800000000402000001000807000000003400000000000000400402003000000400c01001000000000001401001000004400001c01000000000000400802001c00000000400001800001000401400400000000001001003801800400400001c00801400000000403800c02000002001800000000c00001400001002c00000c01000000805000001402c00000000000c00000000402400400001002400000000400000000000401801000800c00001004400c00000401800000803c00800000400001400000801801000400800000004400001001000000001c00800800001402000c00000400000000000400000000005400001400000402800400001000400
  | 5 => 0x18001630f25bf90e4ab9a796c15980017680017b8000a1c000000314001c740007080000000003f40000000000018fc000000fe0bc03dc0000013100016d400000048c0017b61614362f22c10499e1af8000000b100000006e40008300000000013580013548f02b86ccc2087e0f9cf8861ac02f164056ccf0fa8000000000fc8605b893606280000005f0a09c59352120f1800000000000000000000012800024c00212400000000041d3f8d49ef83480002250f1189c722308380000014222a19b0001338000001bd0868734b04002322060000541cb8f11474558aecba8000794910cd901404197934ce66272178001604000001dd00bd728000000000001c1c8000015562d18a4002308ee1f98001744000000001a70000d6954c00000000000026c000001d840017a81a0000000000000000002354000001ca8000000000000000000c815240004ac0018c800031d888b54000000001ed0000001a8800047185c000000f79571699f19f12339ad0099381840000118000000eb1569ff07a02fc00015c0015c8185c5c9a5ea800193d24a0707500010903618e53d9f31f38000b21b30142159581810000000000f707e081000151000023d790f49f0d3f557800199840c9d8001c89ff8000165d20a7164c0000000001004c10317b02e0112280d8c19800053c38581a0e00000001b0001b18000000724000001f78b69284981fc839c654000f420fe1b000037879000000165c001930000000000068be0000000000000fd80000000016e40012980004110c025d3c0676018a395d8640000d40000000000000000000000000000000000000bf8bf0000000000000000000000c305100001d4000b454518600018b9a280000007298487c0e68000bc8a640001ec000da9378001bb81c8000da0a940dc5c2258001940001ed5b04d088c8851b6220c0003e8ab537226976c6809387e9f720a14fd0584616791302622111d0a28880000d240000020481880000019dc0022380017a027800000122dea0000c68fba358b486d9e98ff17f9a018aa1108d5060474000608000000741229f49db0e29f41fd00016609d076cc11b097cc0004e9de0001f28000754f64000a69f215b0c9a1b8240a0c0a9ee4000000000f28002038c854d80000000011bd4196b40000012500016081782d1674d641690d0770af914a0c8000b900014259d00000011fa31926c1555386680000000002e4000000b5935c000000000001ef0002369a48000000e9855df59591af081c000001551f50b8a260001ff4b6d0ed094db8002009548f000498f0760ed4de00003d8000f5a0e80000016a00f80009916e1c18001fd8108a5c002028000000c892a0000aaa2e00880000022f8159c500b80006006c92a8fc0c713d1315560000f51e280023497400015590708d1e78c08000
  | 6 => 0x213000000121000092deda1a965800142c00078d2d06184b80019d8000000000c1c944001320000000000db09221891a00000001f9df8fe82300c10ac000564c7ccc8eec001c397500000000000000016b9d591641388f91b5e604dc1a8ac0a1a2c814d158af102ce7d788000000a84904345758dcc000f309007b80016803884f56e84584d0c7948430179d6dca617d1430fb4001e599c0000e14000950000000b080008c40006a8000000000659540c41cca2198903b8842150f68870568001f00001ca1478408000484078001c009a800146c000ca0000001488000ed80000000000020a94686a0a30000000000001648c287200004a0bf41d822d400948175318000001980000000a454480019f8000f6151e331d71ba9408eaa1f0e085fda21989ec9c78a991c0c24d70549a382019180b1fa15891a945e1d1ce84805b8788d1c2580000003f82c8000001d91730dc116e04214000088cec16f4ac8000000001224000ea000000000175c5ccb4000078000073800172d0500000000000022a9b49eb80000022992600009e9b6d5203ec000000000000000001eb0000000001b22279d68000001230000000000bd0000000000000270a7dc25dfe0806dd720000e50000000611fb1470998000878b9ca580018ad614f205900000019d40000000010f8001951465be14816bd864000000b8dae9500001d094613e0001820a500017e0000000000000000f39ee05f424553076601586800000000140c000002240002098d119f00005293dc0017ea361544000001e40afc001b987a9e388e40000000000000000020f0000de8001f0800000000160000221e290000000b80001e11278398001e09b15c21bc80000000000000000016f00000000000000000000000017bc000769d800000000000010a000067000000110c058000000f3d31c39438d6d219000180a2880003c8000bac000000c3a1e0000000001220001078000588e415840000003300000000008141309e21f866465c001a6557dac87580000006b84a40000001e9f90000000c062b6118000001b548dc0000021694f19491514b18780010680004196ac000690291ad8ab00080000003113640001e40001dc0020b0001c680000002103f0001208000c34428ff80009287300000022d8000000000000a9c7f0aa5dc117c000000000918ad9a2d5dd3483a9cd8a4a1c06e0c90710c18c51eddf449b8000001d48000efa058ce08a10a5c80ee4ca9c100000ed910268000000d2d6b16503502a177d6686884d800060c0001200000000005f8439234b5028818c249198000c8e0d800000000000219800001930cef00000012680000000021e91c40002ed47c00000000167cb007840001f0e75858000c14228001fe0000000000cb9b4102513816d2417480d88d92807c915c0000010
  | 7 => 0xd643051808c08947185a8000d895ec54e209bd89c15d5518000000a816200000000000000000016ec00112806c065eee031d502c000047c001c080a166dc65fe823a350fdc000e3da51cf00018ec000000d6c64c250b29b90001fa8d1400000130449800218000000000090c00066c00000208800121c0013c8000000908000000b38000000000000000000940000000d3161c0f2328000b9400000000000000190847a1d88cce71b10779780001a91d31d9516093c0c8b8610d2b90291918da00c0009348a8a8c5ec369010c49761ee8989a3d6f97c9b780003e5a18aad7ad5045a1958081701e71f804f1b0de686d4961ce0fbce1d38901ce6e001968621330000000000dd9738000001c48000000000001ae0d580000280000000022ea2204ec4e6020000000884a20000518000cb00000000021fc000000001d7963a0b80010a87747bc9b01b875c2340000017103c0000000001d98a55e31438001d399c91c8a79da9e51a687d4000000000001e480007b1dd8000af536c6b14122b8958469990ba5f88570df0000000000000000000000001e200018d0001e18000550cc0000000e9088960d1180cd8a00000013e85e59e40003297dc749168e000b4df9202128002301764000598e30208000000000d90c2c0017340000000004f8001c31ef4531cb09f8000fc5a11174d392f8390ad0e246e8b9910127400000109d4e02d8308ede050d758280000016a8000000000819871328001b38ec80000000016100019a5d753a8000000000000b608980006600f4000000000001a240000000008ec9b4d985e8e588ad78400049c00201099d4a9368000001529098d500000012c10381e0d79c994a15a1ec1415d9dda00010b04059a9a612c8e115080013e4000000bfc000000001854001bf15e19021485540011b8fa1564280421b817c0a4d7a4aa071c0000000000013a209155c00052c0016280000008f40000015f13080018c0000000a243200000000017d9b58000001688001080e8a24963c00174c340000002200000334f8814825400000002143d1200000000021008b4b780019e9799bb04484303d00000022bc77c30dfc0808d2000084a138574b3c0000018505e0000e80039de9b1c0000009f017daa96900000000000018006c1928000e78000e60000000000cf8001000f09d5c0e4000700001ad40000002b00000000002e80000010e17740000000000000117d437150d48c05c001d01a08a420c14f46492f2078ce8219c15108c3c0000753fc4b1aa00015d0ba189c000050000000000000e0c000fa5184dc96651783b0b7d458ae1938490c59a30630545b003e0ee9b286f80018e80000000000000e8f81779d7c000000000001d280000000005c8000000a14000358fd5cc08e0698e35a800006d152c8b0a880000000001c000000
  | 8 => 0x2340bd80002f800000000121800134000000000000033d0c8825719140000000000000001e8000072c80c0000016700000010880000000000000000000010420680000000009adcd00000012e16a40000014d00014910080003245d22b14b8c60e21d88001290000400264000eb93900000004508e9404d611119a0000001e90000070fb1971e88b4c8b8000000000001
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427e6014810de980520427f65cc8109f997320427d65cc8109f197320435e53cc810d754f32042f661cc810bd587320427f658c8109f996320427d658c8109f196320427f654c8109f995320427d654c8109f19532042bf644c810af191320435e534c810d754d32042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f19432042be640c810af590320427e63944109f58e510427e62944109f58a510427d65cc4109fd96310427d658c410d794e310435d538c410dd94631042fa608c410be582310427f654c410dd945310427f650c4109f594310435e530c410d754c31042fa600c410be580310427d65c8410dd94721042f565c8410dd597210437753c8410dd94f210437553c8410dd14f210437752c8410dd94b210437552c8410dd14b21042f560c84109fd96210427d6588410db94a210436d5288410bd98621042fa6088410be582210427f65484109fd94210427d6508410db948210436d5208410dd94421043e52108410be98021042f96008410ddd94210437565084109d59421043775308410dd94c21043755308410dd14c21042f66208410f998821043775208410dd94821043e65208410d994821043755208410f954821043745208410fc98021042f56008410fc58021042f160084109f98e500427d63940109f98a500427d62940109f58650043772194010dd086500427d65cc010af99330042bd64cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c0109fd95300427f650c0109f994300427d650c0109f194300435e530c010d754c30042f6610c010bd584300427d65c80109fd96200427d6588010db94a200436d5288010bd98620042f56188010f9086200427f6548010b7d8d20042dc6348010bdd8520042f461480109fd94200427e65080109f594200427c6508010db948200436d5208010bd98420042f56108010f9084200437565c4010ddd4f100437553c4010bd98b10042f462c4010dd94b100437452c4010bd58610043765184010be596100437965840109e59610042f96184010de94610043f25184010fcc8610043f021840109fd9510042df6344010b718d10042ef6244010bb18910042f76544010ddd9510042776544010f5d8d10043d46344010ddd4d10043755344010f9d8910042f66244010bd18910043e46244010b918910043765244010dd14910042f76044010dd94110043f33044010fc0c110043f22044010fc48110042fb6544010ded95100427b6544010f6d8d10043d86344010fad8910043e86244010bed8510043f36144010de94510043f25144010fccc510043f03144010fc88510043f12144010
  | 1 => 0x42f860485109f994214435f5308510d714c214436f5208510db14821442f66508510dd99421442f76308510bd58c21443775308510f5d4c21443575308510dd94c21443755308510dd14c21443d45308510d514c21442f66208510f998821443775208510f9d4821443675208510dd94821443755208510dd14821443e45208510d914821442f660085109f99730442be64cc110af593304433f54cc110cf153304435f53cc110d714f304436f52cc110db14b30442f661cc110bd587304427e658c110cfd52304433c548c110d7d4e304435c538c110dbd4a304436c528c110f58c6304427f654c1109f595304427c654c110cfd51304433c544c110d7d4d304435c534c110dbd49304436c524c110bdd8530442f4614c1109f994304433f540c110cf150304435f530c110d714c304436f520c110db14830442f6610c110bd58430443d6310c110f64c0304427e65c8110d7d4f204435c53c8110dbd4b204436c52c8110bd98720442f561c81109f996204435f5388110d714e204436f5288110db14a20442f66188110bd58620443e421881109fd95204427d65481109f19520442df6348110b718d204435f5348110d714d204436f5248110db14920442f76148110bd185204427e6508110d7d4c204435c5308110dbd48204436c5208110f9084204435f53c4110d714f104436f52c4110db14b10443db53c4110f614f10443eb52c4110fa14b10443f231c4110fc4c710443f321c4110fc087104435f5384110d714e104436f5284110db14a10442f76384110bd58e10443d75384110f514e10442f66284110bd18a10443e75284110dd94a10443745284110f914a10443645284110fcd4210442be64d4c10af593530427e64d4c10cf993530423e64d4c109f593530433d64d4c108f593530427e62d4c109f58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10d754c530427e6414c109f590530427e6314c10d798c530427e6214c109f588530427e6114c10dd98453042766114c109f980530437a6014c109fd96430427e6590c109f596430427c6590c10cf952430433d5490c109fd95430427e6550c109f595430427c6550c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c10d794c430435d5310c10e750c430427e63d48109f58f520427e61d4810dd987520427661d48109f983520437a60d48109f596520436f52948109f98e520427d6394810dd186520427f63548109f18d520436f62548109fd85520427761548109f585520437461548109fd81520427d6054810b798c52042dd6314810db54
  | 2 => 0x63549109718d524436f62549109fd85524437761549109dd85524427f6054910ded81524427e6514910d7d4c524435c5314910db548524427e63149109f58c524436e6214910ddd84524427e61149109f184524427461149109f980524427c6014910bb994524436e65149109b994524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c52443e76114910dbd8c524436e6314910db58c524436c6314910db90c524436d4314910db10c524436f6114910d9d84524436d6114910dbd80524436d6014910db440524427f65cc9109f997324427d65cc9109f197324433f54cc910cf153324435f53cc910d714f324436f52cc910db14b32442f661cc910bd587324427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436f528c910db14a324427f654c9109f995324427d654c9109f19532442bf644c910af191324433f544c910cf151324435f534c910d714d324436f524c910db14932442f7614c910bd18532442fb604c910be181324427f650c9109f994324427d650c9109f19432442be640c910af590324433f540c910cf150324435f530c910d714c324436f520c910db14832442f6610c910bd58432442fa600c910be580324427e65cc510cfd53314433c54cc510d7d4f314435c53cc510dbd4b314436c52cc510be98331442f960cc5109f996314433f548c510cf152314435f538c510d714e314436f528c510db14a31442f6658c510dd99631442f7648c510bd59231443b7548c510ed15231442f5638c510f5d4e3144376538c510dd14e31443d4538c510d514e31442f6628c510f9d4a3144376528c510dd14a31443e4528c510d914a31442f6608c5109f195314433f544c510cf151314435f534c510d714d314436f524c510db14931442fb604c510be1813144374654c5109d19531442f7644c510bd59131443b7544c510ed15131443d7634c510f5d4d3144376534c510dd14d31443d4534c510bd18931443e7524c510dd9493144374524c510f91493144364524c510fcd8131442f4604c510fc18131442f0604c5109f994314433f540c510cf150314435f530c510d714c314436f520c510db14831442f6610c5109f997214435f53c8510d714f214436f52c8510db14b21442fa60c8510be583214437665c85109d997214437465c8510bdd8f21442f563c8510ddd4f21443d753c8510d5d4f214437653c8510dd54f214437453c8510f514f214435453c8510ddd4b21443e752c8510dd94b214437552c8510dd14b21443e452c8510d914b21442f660c8510fc98321442f260c8510fc583214427e6588510d7d4e214435c5388510dbd4a214436c5288510bd986214427c6548510d7d4d214435c5348510dbd49214436c5248510bed81214
  | 3 => 0x210d754e30842f6618c210bd586308435e530c210d754c30842f6610c210bd58430843d9300c210db94a208436d5288210bd98620842f56188210f908620842df6348210b718d20842f76148210bd185208436e5208210db54820842f66108210bd58420843e42108210bd597108437565c4210ddd4f108437553c4210bd98b10842f462c4210dd94b108437452c4210be597108437965c42109f993534427d64d4d109f98b534427d62d4d10d7d53534439f54d4d10c7d5353443d761d4d10d7d93534435e64d4d10d7593534435c64d4d10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534435f5394d10bb98a53442ed6294d109f992534433e6494d108f992534427d6494d10cf592534423d6494d109f98e534425e6394d109f98a534436e6294d109b98a534427d6294d10db58a534426d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10cfd5153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534433f5414d10d754c534427e6414d109f590534435e6314d109f988534427d6214d109f98453443756114d109f184534427e6014d109f18053442de6514d10d7994534425e6514d10d7d50534439f5414d10c7d50534435e5414d10d7550534435c5414d10e7150534431c5414d10f5584534435f6414d10d7990534435d6414d10d7190534435f6214d10d7988534435d6214d10d7188534435f6114d10d758453443556114d10d7d80534435d6014d10d7440534427f6590d109f996434427d6590d109f196434433f5490d10cf152434435f5390d10d714e43442f66190d10bd58643442fa6090d10be582434427f6550d109f995434427d6550d109f195434435f5350d10d714d434427f6510d109f994434427d6510d109f194434435f5310d10d714c434439d4310d10bd98443442f56110d10d7d4f524435c53d49109f98f524427d63d4910dd587524436f53d4910f3d4f524434f53d4910db94f524436d53d4910db14f52443cc53d4910d314f52443e561d4910dbd8f524436e63d4910db58f524436c63d4910db90f524436d43d4910db10f524436f61d4910db587524436561d4910dbd83524436d60d4910b798e52442dd6394910d7d4e524435c5394910dbd4a524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442df6354910b718d524435f5354910d714d524427f6354910d7d8d524425f63549109f18d524435c
  | 4 => 0xd58f21c437753c8710dd94f21c437553c8710dd14f21c437752c8710dd94b21c437552c8710dd14b21c42f660c8710db94a21c436d5288710be98221c42f96088710db94821c436d5208710be98021c42f96008710dd59421c42f76308710bd58c21c43775308710dd94c21c43755308710dd14c21c43e66208710ddd4821c43765208710f994821c43665208710dd54821c43e55208710d954821c42f66008710fc98021c43f16008710af99330c42bd64cc310d794f30c435d53cc310bd98730c42f561cc310d7d4e30c435c538c310f58c630c435e534c310d754d30c42f7614c310bd18530c435f530c310d714c30c42f6610c310bd58430c43d6310c310db94b20c436d52c8310bd98720c42f561c8310dbd4a20c436c5288310bd98620c42f56188310f908620c42df6348310b718d20c436e5248310db54920c42f76148310bd18520c436f5208310db14820c43e421083109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538427f6454e109f191538435f6354e109fd89538427c6254e10d754c538427e6414e109f590538435e6314e109f988538427d6214e10dd584538437a6014e109fd96438427e6590e109f596438427c6590e10be98243842f96090e109fd95438427e6550e109f595438427c6550e10bdd8543842f46150e109fd94438427e6510e109f594438427c6510e10e750c438427e63d4a109f58f528437561d4a10de983528436f5294a109f98e528427d6394a10ddd86528427f6354a109f18d528436f6254a10ddd85528436d5214a109f98c528427d6314a10db98852843756114a10de980528427f65cca109f997328427d65cca109f19732842f661cca10bd587328427f658ca109f996328427d658ca109f196328427f654ca109f995328427d654ca109f19532842bf644ca10af19132842f7614ca10bd18532842fb604ca10be181328427f650ca109f994328427d650ca109f19432842be640ca10af59032842fa600ca10be580328435e53cc610d754f31842fa60cc610be583318435f538c610d714e318435e534c610d754d31842fb604c610be181318435f530c610d714c318436e52c8610db54b21842fa60c8610be583218437565c8610ddd4f218437653c8610dd54f218437453c8610ddd4b218437652c8610f994b218436652c8610dd54b21843e552c8610fc98321842f560c8610fc583218436f5288610db14a218436e5248610db54921842fb6048610be181218436f5208610db14821843e52108610bd59421843756508610ddd4c21843765308610dd54c21843745308610f998821843775208610f9d4821843765208610dd54821843745208610f914821843645208610bd58021842be64cc210af593308435e538c
  | 5 => 0x30082f9620c020fa588300837a520c020f68c830083d8320c020fc98430083f1610c020f68c430083d8310c020fcc8430083ea210c020fa08430083f0210c020f808430083e721c8020f908720082ee61c8020facc320083e830c8020bb58a200836e5288020bd98620082f56188020f908620082fa6388020be18e20082f96288020de94a20083ea5288020fc98620083f16188020fcc8620083ea2188020fa08620083f02188020f8086200827f6548020b7d8d20082dc6348020bdd8520082f46148020f9c8520083e42148020bbd95200836f65480209bd9520083cf6348020f318d20083e76148020bb18520083e46148020b918520082ef6048020db94120082fb6548020ded95200827b6548020f6d8d20082fa6348020be18d20083d86348020b618d20082fb6248020fad89200837a5248020fa94920083f36148020fc18520083f32148020fc085200827e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10af99053c42bd6414f10d754c53c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9643c427e6590f109f59643c427c6590f10d794e43c435d5390f10bd98643c42f56190f109fd9543c427e6550f109f59543c427c6550f10d794d43c435d5350f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10e750c43c42f66110f10bd58443c42de63d4b10b758f52c427e63d4b10d798f52c425e63d4b109f58f52c435d63d4b109758f52c437661d4b10de58352c436f5294b109f98e52c427d6394b10dd18652c427f6354b109f18d52c436f6254b10dd18552c436d5214b109f98c52c427d6314b10db98852c43766114b10de58052c427f65ccb109f99732c427d65ccb109f19732c42f661ccb10bd58732c427f658cb109f99632c427d658cb109f19632c435e538cb10d754e32c427f654cb109f99532c427d654cb109f19532c42bf644cb10af19132c42f7614cb10bd18532c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c42be640cb10af59032c435e530cb10d754c32c42f6610cb10bd58432c435e538c710d754e31c42fa608c710be58231c4375658c710bdd9231c42f5648c710dd94e31c43d6538c710f554e31c4374538c710bd98a31c4376528c710dd14a31c42f6608c710fc98231c43f1608c710bdd9531c4377654c710bdd9131c42f5644c710f5d8d31c4376534c710dd14d31c42f4624c710dd94931c4374524c710bd18131c435e530c710d754c31c42fa600c710be58031c42f565c8710dd59721c42f763c8710b
  | 6 => 0x27d6590c209f196430835e5390c20d754e43082fa6090c20be582430827f6550c209f995430827d6550c209f195430835e5350c20d754d43082ef6250c20bb18943082fb6050c20be181430827f6510c209f994430827d6510c209f194430839d4310c209f98e520827d63948209f59732082f661cc820bd587320827f658c8209f596320835e538c820d754e32082fa608c820be582320827f654c820afd9132082bc644c820bdd8532082f4614c820bed81320827f650c8209f59432082be640c820af590320835e530c820d754c32082fa600c820be580320837751944209f98e510827d63944209fd8d510827c6354420b798c51082dd6314420dd544510827f65cc4209f997310827d65cc420d794f310835d53cc420bb98b31082ed62cc4209fd96310827e658c4209f5963108376518c420dd54631082fa608c420be582310827f654c4209f595310827c654c420d794d310835d534c420bbd8931082ec624c420dd9453108375514c420bed8131082f8604c4209fd94310827e650c4209f594310837651c8420dd54721082fa60c8420be583210837753c8420dd94f210837553c8420dd14f210837652c8420fc98321083f160c84209f59621082f66188420bb596210836d6588420bb98621082e66188420db54621082ed60884209fd9521083765108420dd54421083e52108420be98021082f96008420bb98421083e66108420f9944210836d5108420f954421083e73108420f98c421083e53108420f90c421083ea6008420bb58021083e96008420ddd4c21083765308420dd54c21083745308420bd98821083e66208420dd94821083e73208420f98c821083e53208420f90c821083f26008420fc58021083e66508420f959421083e76308420f998c21083e56308420f918c21083e75308420f994c21083e55308420f914c21083e64308420f950c21083e44308420f9d8021083e66008420f898021083e56008420f858021083e460084209f98e500827d6394020dd98650083756194020ddc86500836e2194020db08650083742194020d9086500827d65cc020af99330082bd64cc020f908730082f965cc020de59730082fa64cc020ee99330082ba64cc020ee59330082f864cc020ded4f300837953cc020be58b300837a52cc020fcc8730083ea21cc020fa08730083f021cc020f8087300827f658c0209f596300835e538c020d754e30082ee628c020bb58a30083e4218c020be982300827f654c020f9085300827f650c0209f994300827d650c0209f194300835e530c020d754c30082ee620c020bb58830082f6610c020bd58430083e4210c020f64c030082f9650c020de5943008279650c020be99030082f8640c020be98c30083da630c020ded4c30083da530c020de54c30083d9530c020f690c30083d9430c020fa988
  | 7 => 0x314520f514c51483545314520ddd8c51483766314520dd58c51483746314520dd90c51483754314520dd10c51483776214520ddcc851483763214520dd4c851483743214520ddd8051483756014520dd480514827e65cc5209f597314827c65cc520cfd53314833c54cc520d7d4f314835c53cc520ddd47314837451cc5209f996314827d658c5209f196314833f548c520cf152314835f538c520d714e3148377518c520dd146314827f654c5209f995314827c654c520cfd51314833c544c520d7d4d314835c534c520ddd453148374514c5209f994314827d650c5209f194314833f540c520cf150314835f530c520d714c3148377510c520dd14431482fa600c520be580314827e65c8520d7d4f214835c53c8520dd14721482f665c8520dd997214827665c8520ddd4f21483d753c8520d5d4f214837653c8520dd54f214837453c8520f514f214835453c8520d7d4e214835c5388520bd98621483775188520dd14621482fa6088520be582214835f5348520d714d21483775148520dd14521482fb6048520be181214827e6508520d7d4c214835c5308520ddd4421482f66508520dd99421482766508520ddd4c21483d75308520d5d4c21483765308520dd54c21483745308520f514c21483545308520bd98821483e662085209f99730482be64cc120af593304833f54cc120cf153304835f53cc120d714f30482ee62cc120bb58b304837751cc120dd147304827e658c120cfd52304833c548c120d7d4e304835c538c120ddd463048374518c1209fd95304827d654c1209f195304833f544c120cf151304835f534c120d714d30482ef624c120bb1893048377514c120dd145304827e650c120cfd50304833c540c120d7d4c304835c530c120bd98430482f5610c120ddd443048374510c120d7d4f204835c53c8120ddd47204837451c8120f6d4f204837a53c8120de14f20483d853c8120d614f20483f351c8120fc14720483f321c8120fc087204835f5388120d714e20482f66188120bd58620483775188120dd14620483e72188120f908620483cf5388120f314e20483e66188120f958620483e75188120db14620483e45188120d914620483eb50881209f993530827d64d4c209f98b530836e62d4c209f987530827d61d4c209f983530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553083786054c20af99053082bd6414c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6314c20d798c530827e6214c20db988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827f6590c209f9964308
  | 8 => 0x20bb597208836d65c8220bb98720883e651c8220f954720882f965c8220de597208837a53c8220de14f20883f251c8220fc54720883f321c8220fc087208827e64d4d209f593534827e61d4d209f587534835f54d4d20e7d53534831f54d4d20d7d93534835e64d4d20d7593534835c64d4d20d7d8b534835d62d4d20d7d87534835e61d4d20d7587534835c61d4d20d7d83534835d60d4d20af99253482bd6494d20cfd52534835f5394d20bd98653482f56194d209f992534833e6494d208f992534827d6494d20cf592534823d6494d209f98e534825e6394d209f58a534836d6294d209f98653483766194d209d986534827d6194d20dd58653482756194d209f58253483796094d20afd9153482bc6454d20cfd5153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209ed81534827e6514d20cfd50534835d5314d209f990534827d6414d20d798c534827e6214d209f188534827e6114d209f58453482de6514d20d7994534825e6514d20d7d50534839f5414d20c7d50534835e5414d20d7550534835c5414d20e7150534831c5414d20d7d90534835e6414d20d7590534835c6414d20d7d88534835d6214d20d7d84534835e6114d20d7584534835c6114d20d7d80534835d6014d20d7480534827f6590d209f996434827d6590d209f196434833f5490d20cf152434835f5390d20d714e434827f6550d209f995434827d6550d209f195434835f5350d20d714d434827f6510d209f994434827d6510d209f194434835f5310d20d714c434839d4310d20bb98843482ed6210d209f997324833f54cc920cf153324835f53cc920d714f32482f661cc920bd58732482fa60cc920be583324827e658c920cfd52324833c548c920d7d4e324835c538c9209f19532482bf644c920af191324833f544c920cf151324835f534c920d714d32482f7614c920bd18532482fb604c920be181324827e650c920af99032482bd640c920cfd50324833c540c920d7d4c324835c530c920d7d4f514835c53d45209f98f514827d63d4520ddd4f51483d753d4520d5d4f514837653d4520dd54f514837453d4520f514f514835453d4520ddd8f514837663d4520dd58f514837463d4520dd90f514837543d4520dd10f514837762d4520ddccb514837632d4520dd4cb514837432d4520ddd83514837560d4520b798e51482dd6394520d7d4e514835c5394520ddd4651482df6354520b718d514835f5354520d714d514835f5314520d714c514837551145209f98c514827d6314520bd99451483766514520ddd4c51483d75314520d5d4c51483765314520dd54c51483745
  | 9 => 0x588538827e6114e20dd98453882766114e209f58453883756114e209d584538837a6014e209fd96438827e6590e209f596438827c6590e20cf952438833d5490e20d7d4e438835c5390e209fd95438827e6550e209f595438827c6550e20d7d4d438835c5350e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20d794c438835d5310e20e750c438835e53cca20d754f32882f661cca20bd58732882fa60cca20be583328835f538ca20d714e32882bf644ca20af191328835e534ca20d754d32882f7614ca20bd18532882fb604ca20be18132882be640ca20af590328835f530ca20d714c328837751946209f98e518827d6394620ddd4e51883765394620dd54e51883745394620f9d8a51883776394620dd98e51883756394620dd18e51883764394620dd50e51883744394620ddd8a51883773294620dd8ca51883753294620dd0ca51883766094620dd182518827f63546209f18d51883776554620ddd4d51883765354620dd54d51883745354620f9d8951883776354620dd98d51883756354620dd18d51883764354620dd50d51883744354620dd58951883773254620dd8c951883753254620dd0c951883766054620dd181518837551146209fd97318827e65cc6209f59731882ee62cc620bb58b318837651cc620dd547318827f658c6209f996318827d658c620dd9463188375518c6209fd95318827d654c6209f19531882ef624c620bb1893188376514c620dd545318827f650c6209f994318827d650c620dd9443188375510c620be98031882f9600c620dd94721882f565c8620dd597218837753c8620dd94f218837553c8620dd14f21883765188620dd54621882fa6088620be58221883e65188620db54621883e55188620fa98221882ed6088620fa58221883765148620dd54521882fb6048620be18121883755108620f948421882ed6508620db59421883e66108620f9d4421883e65108620db54421883e55108620d954421883e45108620f9cc421883e63108620f94c421883e43108620bb58021882f56508620dd59421883775308620dd94c21883755308620dd14c21883e66208620f9cc821883e63208620f94c821883e43208620f959421882e56508620d959421883e76308620f998c21883e56308620f918c21883e75308620f994c21883e55308620f914c21883e64308620f950c21883e44308620f9d8021883e66008620f958021883e46008620af99330882bd64cc220dd947308837551cc220f9087308835e538c220d754e30882ee628c220bb58a3088376518c220dd54630883e4218c220dd9453088375514c220f9085308835e530c220d754c30882ee620c220bb58830882f6610c220bd5843088376510c220dd54430883e4210c220dd947208837551c8220f9c8720883e421c82
  | 10 => 0x3c827d61d4f20de58353c835f5394f20bd98653c82f56194f209f99253c827d6494f209f98653c83766194f209d98653c827d6194f20dd58653c82756194f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c837b6054f20af99053c82bd6414f20d754c53c827e6414f20cf99053c823e6414f209f59053c833d6414f208f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9643c827e6590f209f59643c827c6590f20d794e43c835d5390f20be98243c82f96090f209fd9543c827e6550f209f59543c827c6550f20d794d43c835d5350f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20e750c43c82ee6210f20bb58843c82f661ccb20bd58732c835e538cb20d754e32c82fa608cb20be58232c82bf644cb20af19132c82f7614cb20bd18532c82f8604cb20af99032c82bd640cb20d794c32c835d530cb20be98032c82f9600cb20b798f51c82dd63d4720ddd4651c827e63947209f58e51c827f63547209f18d51c837551147209fd9731c827e65cc7209f59731c827f658c7209f99631c827d658c720d794e31c835d538c720be98231c82f9608c7209fd9531c827d654c7209f19531c82fb604c720be18131c827f650c7209f99431c827d650c720d794c31c835d530c720dd94721c837551c8720be98321c82f960c8720ddd4f21c837653c8720dd54f21c837453c8720fc98321c83f160c8720dd94421c83755108720be98021c82f96008720ddd4c21c83765308720dd54c21c83745308720f998821c83f26008720fc58021c82be64cc320af59330c835e53cc320d754f30c82ee62cc320bb58b30c82f965cc320de59730c82fa64cc320ee99330c82ba64cc320ee59330c82f864cc320ded4f30c83da53cc320de54f30c83d953cc320fa98b30c82f962cc320fa58b30c83f321cc320fc08730c835f538c320d714e30c835e534c320d754d30c82ef624c320bb18930c835f530c320d714c30c82f6610c320bd58430c83d9300c320be59430c8379650c320be99030c82f8640c320f698c30c837b530c320f6d4c30c8379530c320f614c30c83da430c320f650c30c82f9620c320f68c830c83d8320c320fc98430c83f1610c320f68c430c83d8310c320fcc8430c83f0210c320af99353882bd64d4e20bd98753882f561d4e209f993538833e64d4e208f993538827d64d4e20cf593538823d64d4e20db58b538827e61d4e20dd987538827661d4e209f587538837561d4e209d587538837a60d4e20af99253882bd6494e20d7d4e538827e6494e20cf992538823e6494e209f592538833d6494e208f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20d754c53882f66114e20bd584538827e6414e209f590538835e6314e20db
  | 11 => 0xdf648c430b7592310c2de628c430b7986310c3d6518c430d7546310c3d5518c430d5546310c2dd608c4309fd95310c376514c430dd944310c375510c430be980310c2f9600c430b7d90310c2dd640c430b7988310c2de610c430f5984310c3d6510c430d7544310c3d5510c430f6980310c2dd600c430f6580310c2d9600c4309fd97210c27e65c84309f597210c2de63c8430b758f210c37651c8430dd547210c3d631c8430f50c7210c2f765c8430ddd97210c27765c8430dd997210c2f565c8430dd597210c27565c8430dd197210c37754c8430dd953210c37554c8430dd153210c3d663c8430f558f210c37653c8430f590f210c3d543c8430dd94b210c37552c8430f58cb210c3d432c84309fd96210c27e65884309f596210c2de6388430b758e210c2f66188430dd946210c3755188430be982210c2f960884309fd95210c27d65484309f195210c2df6348430b718d210c3765148430dd545210c2fb6048430be181210c27f65084309f994210c27d6508430b7d8c210c2dc6308430dd944210c3755108430f58c4210c3d43108430bdd94210c37765084309dd94210c3766508430bd594210c37565084309d594210c3746508430ddd50210c3765408430dd550210c3745408430f5d8c210c3d46308430dd94c210c3d64308430f550c210c2f66208430f9988210c3765208430dd548210c3d63208430f50c8210c27e64940309f592500c35e4394030d750e500c35e3294030d70ca500c35e3194030d70c6500c3772194030dd086500c27d65d0030b798f400c2dd63d0030dd947400c37551d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030e750e400c3765190030dd546400c27f6550030dd945400c37551500309f994400c27d65100309f194400c2de6310030b758c400c39d4310030dd944400c3755110030af993300c2bd64cc030dd947300c37551cc030b7d93300c39e64cc030b7593300c39d64cc030a7593300c2de62cc030b7987300c3d651cc030f5547300c3d721cc030f5087300c2dd638c030d794e300c376518c030dd546300c2f9638c030de94e300c3da538c030f690e300c3d9438c030be98a300c3da328c030f60ca300c3f2518c030fc546300c3da318c030f60c6300c3f3218c030fc086300c27f654c030dd945300c375514c030b7d95300c35f654c03097d95300c2df644c030b7591300c2dc624c030b7185300c3d6514c030f5545300c3d7214c030f5085300c2df604c030d7941300c3db404c030f6101300c2fb654c030ded95300c27b654c030bed8d300c3db634c030de94d300c3da534c030f6d0d300c3d8434c030be189300c3da324c030f60c9300c3f2514c030fc545300c3db314c030f64c5300c3f3214c030fc085300c27e64d4f209f59353c836e62d4f209f9875
  | 12 => 0x14830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830b798f420c2dd63d0830e750f420c2f661d0830bd587420c2fa60d0830be583420c27f65908309f996420c27d6590830cfd52420c39e4390830db94a420c36d52908309fd95420c27d65508309f195420c33e5450830cf551420c2df6350830b718d420c39d4350830db949420c36d5250830bdd85420c2f46150830bed81420c2f860508309fd94420c27e65108309f594420c33f5410830b798c420c2dd6310830e790c420c36e52cc830db54b320c2f661cc830bd587320c2fa60cc830be583320c27d658c830b7596320c35d658c830b7d92320c2dd648c830d7952320c35c548c830b798a320c35d528c830b7986320c3db608c830b7582320c3d8608c8309fd95320c2bf644c830af191320c2f7614c830bd185320c2fb604c830af990320c2bd640c830db948320c36d520c830be980320c2f9600c830b7d90320c39e640c830b7590320c39d640c830a7590320c35e540c830d7150320c2de620c830f3988320c3ce520c830d7548320c3cd520c830b7984320c3da600c830b7580320c3d9600c830ddd46510c27e64944309f592510c27e62944309f58a510c3775494430dd952510c3755494430dd152510c3d46394430f590e510c3d54394430bd98a510c3775294430dd94a510c3755294430dd14a510c3d63294430f50ca510c3776494430dd992510c3756494430dd192510c3746394430ddd0e510c3764394430dd50e510c3744394430ddd8a510c37662944309d98a510c3756294430dd18a510c3774294430dd90a510c3754294430dd10a510c3773294430dd8ca510c3753294430dd0ca510c3766094430dd182510c27f64544309f191510c27f62544309f189510c3776554430ddd51510c3765454430dd551510c3745454430f518d510c3d64354430f550d510c2f46254430ddd49510c3765254430dd549510c3745254430f58c9510c3d43254430ddd91510c3766454430dd591510c3746454430dd98d510c3774354430dd90d510c3754354430dd10d510c3776254430dd989510c3756254430dd189510c2746254430ddd09510c3764254430dd509510c3744254430ddcc9510c3763254430dd4c9510c3743254430dd981510c3746054430dd0c1510c2f66114430dd544510c27f65d04309f997410c27d65d0430b798f410c2dd63d0430dd947410c37551d04309fd96410c27e65904309f596410c3765190430dd546410c27f65504309f595410c27c6550430b7d8d410c2dc6350430dd945410c3755150430bed81410c2f860504309fd94410c27e65104309f594410c2de6310430b758c410c3765110430dd544410c2fa6010430be580410c37651cc430dd547310c2fa60cc430be583310c27d658c430dd546310c2dd658c430d7596310c2
  | 13 => 0xddd44414c37451105309f997314c377518c530dd146314c2fa608c530be582314c377514c530dd145314c2fb604c530be181314c27e650c5309f997214c27d65c85309f197214c37751c8530dd147214c37765c8530dd997214c37565c8530dd197214c37754c8530dd953214c37554c8530dd153214c37752c8530dd14b214c27e65885309f596214c27c6588530dbd4a214c36c5288530bd986214c27f65485309f995214c27c65485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c2fa6008530be580214c3776508530dd994214c3756508530dd194214c3775408530dd950214c3755408530dd150214c3d66308530f558c214c2f66208530f9988214c3775208530f9d48214c3675208530dd148214c3e45208530d9148214c3f26008530fc580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130cf952404c27d65501309f195404c2df6350130b718d404c2be64cc130af593304c3ba64cc130ee593304c37852cc130fcc87304c3f021cc130d7d52304c35d548c130d714a304c35c518c130f5c86304c3d4218c130f6d42304c2f661d5030bd587540c35e63d50309f98b540c27d62d50309f987540c37661d50309d987540c27d61d5030dd587540c27561d5030de983540c27d6595030cfd52540c35e63950309f98a540c27d62950309f986540c27d6195030cfd91540c27f63550309f58d540c27f62550309f189540c27f61550309f185540c33d5415030bb988540c2ed6215030bd984540c2f561150309f98c540c35e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a6015030cf992530c27d6494c30cf592530c23d6494c309f597430c33f54d0c309fd96430c27d6590c30cf952430c33d5490c30be982430c2f96090c30d7596430c25d6590c30b7592430c35e5490c30e7952430c39d5490c30d7152430c2de6290c30b7986430c3da6090c30b7582430c3d96090c30b6582430c27f6550c30cfd51430c2df6550c30d7d95430c39f6450c30e7d51430c35e5450c30d7151430c39c5450c30c7151430c2dc6250c30b7185430c2df6050c309fd94430c27d6510c30cf950430c33d5410c30b798c430c39d4310c30be980430c2f96010c30bd987520c2f561d4830dbd4a520c27e64948309f592520c37761948309f986520c27d6194830dd186520c2bf6454830af191520c2f76154830bd185520c27f6454830cfd91520c23f64548309f191520c33c64548308f191520c35e4354830d750d520c27f6154830ddd85520c27761548309f185520c37461548309d185520c3786054830af990520c2bd6414830db548520c2f661
  | 14 => 0x96218c27e65886309f596218c2de6388630b758e218c27f65486309f595218c27c6548630b7d8d218c2dc63486309fd94218c27e65086309f594218c2df6308630b718c218c3765108630dd544218c3d63108630f50c4218c2fa6008630be580218c3776508630dd994218c3756508630dd194218c3775408630dd950218c3755408630f5d8c218c3d46308630f590c218c3d54308630f9988218c3765208630dd548218c3d63208630f50c8218c3f26008630fc580218c2de63d0230b758f408c2de6390230b758e408c39d4390230af993308c2bd64cc230b7597308c35d65cc230e7993308c2dd64cc230e7593308c29d64cc230b798b308c2de61cc230f5c87308c3d421cc230be597308c37965cc230ee993308c3b964cc230de94b308c3f321cc230fc087308c27e62d51309f58b544c27e61d51309f587544c33f5495130d758e544c27e62951309f58a544c27e61951309f586544c3796095130bbd89544c2ec6255130bdd85544c2f46155130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f18c544c27e62151309f588544c27e61151309f584544c33f54d0d30cf153434c2fa60d0d30be583434c27e6590d30cfd51434c33c5450d30bed81434c2f86050d309f994434c39d4310d30bd987524c2f561d49309f993524c27d64d49309f987524c37661d49309d987524c27d61d4930dd587524c27561d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c36f52d0930db14b424c2f661d0930bd587424c27e65909309f596424c27c6590930cfd52424c33c54909309fd95424c27e65509309f195424c2df6350930b718d424c2f76150930bd185424c2fb6050930be181424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930dbd48424c36c52109309f997324c2f661cc930bd587324c36f528c930db14a324c2fa608c930be582324c2bf644c930af191324c36f524c930db149324c2f7614c930bd185324c2fb604c930be181324c27e650c930af990324c2bd640c9309f993514c27d64d45309f98b514c27d62d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c5490530b798e414c2dd6390530be982414c2f960905309fd95414c27e65505309f195414c27e65105309f594414c27c6510530cfd50414c33c541053
  | 15 => 0x8c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c2f66115230bd584548c33e54d0e30cf553438c2fa60d0e30be583438c2dd6590e30d7596438c35e5490e30b798a438c2de6190e30b7582438c33e5450e30cf551438c2fb6050e30be181438c35f6550e30e7d91438c35e5450e30e7951438c31e5450e30e7551438c2dc6250e30b7185438c2df6050e30f6d81438c3d86050e30e750c438c2be64d4a30af593528c2f661d4a30bd587528c36f5294a309f992528c27d6494a309f986528c27d6194a30bdd85528c2f46154a309fd91528c27c6454a30d790d528c35d4354a309fd85528c3776154a309dd85528c27c6154a30dd185528c2746154a30db548528c27f65d0a309f997428c27d65d0a30b798f428c2dd63d0a30e750f428c2f661d0a30bd587428c27f6590a309f996428c27d6590a30cf952428c33d5490a30e790e428c27f6550a309f595428c27c6550a30b7d8d428c2dc6350a30e750d428c2f76150a30bd185428c2fb6050a30be181428c27f6510a309f994428c27d6510a30cf950428c33d5410a30b798c428c2dd6310a30e790c428c2f661cca30bd587328c36e528ca30db54a328c2fa608ca30be582328c2df648ca30b7592328c35e548ca30f394a328c35d528ca30f354a328c2de618ca30f6982328c2dd608ca30f6582328c2bf644ca30af191328c36e524ca30db549328c2f7614ca30bd185328c2fb604ca30be181328c2be640ca30af590328c2dd650ca30d7594328c2df640ca30e7990328c2dd640ca30e7590328c29d640ca30d7950328c3ce620ca30d7548328c2de610ca30b7580328c37751946309f992518c27d64946309f98a518c27d62946309fd91518c27c64546309fd89518c27c6254630af990518c2bd6414630dd544518c27f65d06309f997418c27d65d0630cf953418c33d54d0630b798f418c2dd63d06309fd96418c27e65906309f596418c3765190630dd546418c2fa6090630be582418c27f65506309f595418c27c6550630cf951418c33d5450630b7d8d418c2dc6350630dd945418c37551506309fd94418c27e65106309f594418c2de6310630b758c418c376518c630dd546318c2fa608c630be582318c2df648c630b7592318c2de628c630f5946318c35d518c630f5546318c3da608c630b7582318c3d9608c630dd945318c375514c630bed81318c2f8604c630b7594318c35d650c630b7d90318c2dd640c630b7988318c3d6610c630d7544318c2dd600c6309fd97218c27e65c86309f597218c2de63c8630b758f218c37651c8630dd547218c3d631c8630f50c7218c37765c8630dd997218c37565c8630dd197218c37754c8630dd953218c37554c8630f598f218c3d563c8630f590f218c3d543c8630dd94b218c37552c8630f58cb218c3d432c86309fd
  | 16 => 0xc6454b309fd8552cc3776154b309dd8552cc27c6154b30dd18552cc2746154b30ded8152cc2be6414b30af59052cc33e5414b30cf55052cc36d5214b309fd9742cc27e65d0b309f59742cc33e54d0b30cf55342cc2f661d0b30bd58742cc2fa60d0b30be58342cc27f6590b309f99642cc27d6590b30cf95242cc33d5490b309fd9542cc27d6550b309f19542cc33e5450b30cf55142cc2df6350b30b718d42cc2f76150b30bd18542cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30cf95042cc33d5410b30b798c42cc2dd6310b30cf95332cc33d54ccb30db94b32cc36d52ccb30bd98732cc2f561ccb30be98332cc2f960ccb30cf95232cc33d548cb30afd9132cc2bc644cb30cf95132cc33d544cb30bdd8532cc2f4614cb30be18132cc2be640cb30af59032cc33e540cb30cf55032cc36e520cb30db54832cc2fa600cb30be58032cc2be64d4730af59351cc33e54d4730cf55351cc2ee62d4730bb58b51cc33e5494730cf55251cc37751947309f99251cc27d64947309f98a51cc27d6294730cf95151cc33d54547309fd9151cc27c64547309fd8951cc27c6254730af99051cc2bd6414730cf95051cc33d5414730dd54451cc27f65d07309f99741cc27d65d0730cf95341cc33d54d07309fd9641cc27e65907309f59641cc33e5490730cf55241cc2de6390730b758e41cc27f65507309f59541cc27c6550730cf95141cc33d5450730bed8141cc2f860507309fd9441cc27e65107309f59441cc33e5410730cf55041cc2fa6010730be58041cc33e54cc730cf55331cc37651cc730dd54731cc2fa60cc730be58331cc33e548c730cf55231cc33e544c730cf55131cc33e540c730cf55031cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730cf95321cc33d54c8730dd94721cc37551c8730ddd9721cc37665c8730dd59721cc37465c8730dd95321cc3b654c8730cd95321cc37554c8730ed55321cc33554c8730dd15321cc37652c8730dd54b21cc27f65887309f99621cc27d6588730cf95221cc33d5488730db94a21cc36d5288730be98221cc2f960887309fd9521cc27d65487309f19521cc33e5448730cf55121cc2fb6048730be18121cc27f65087309f99421cc27d6508730cf95021cc33d5408730b798c21cc2dd6308730db94821cc36d5208730dd94421cc3755108730ddd9421cc3766508730dd59421cc3746508730dd95021cc3b65408730cd95021cc3755408730ed55021cc3355408730dd15021cc3d66308730f558c21cc3e66208730dd94821cc3e65208730d994821cc3755208730f954821cc3655208730b798f40cc2dd63d03309f98b548c27d62d52309f987548c27d61d5230de983548c33f5495230d758e548c27e62952309f58a548c27e61952309f58654
  | 17 => 0x4821dd10e52087666294821dd98252087756094821f959652087e76394821f998e52087e56394821f918e52087e75394821f994e52087e55394821f914e52087e64394821f950e52087e44394821f9d8252087e66094821b998252087e56094821f918252086f565cc821dd597320867565cc821bd99332086f564cc821bd19332087d643cc821f550f320877652cc821f994b32087e742cc821bd98332086f560cc821bdd9632086f5658c821bdd9232086f6648c821bd59232086f5638c821f594e32087d5538c821f5d0e32087d4438c821bd98a3208776528c821f994a32087e6428c821f5cca32087e7328c821bd98232086f5608c821bdd953208777654c8219dd9532086f7644c821edd9132086b7644c821bd99132086f5644c821bd19132087b4644c821ad19132087d6434c821f550d3208776524c821f994932087e6424c821f950932087e7324c821f58c932086f7604c821fcd8132086f3604c821bd18132087f0604c821bc18132086f7650c821bd99432086f5650c821bd19432086f7640c821bd99032087b6640c821ad99032086f5640c821ed59032086b5640c821bd19032086f6630c821f594c32087d5530c821f5d0c32087d4430c821bd9883208776520c821f994832087e7420c821f910832087d7320c821f98c832087d5320c821f94c832087c5320c821bd98032086f5600c821bd98f50086f563d4021ddd4f500877553d4021f998b50087e652d4021bd59650086f66394021bd58e50087e46294021dd94a50087e65294021ddd4250087f35094021bdd8d50087d76354021b5d8d50086f46354021f518d50086d46354021ddd4d50087755354021f918950087765254021f994950087f35054021dd94150086f66314021f598c50086d66314021bd58c50087d56314021b558c50087e66214021f994850086f66014021ddd4050087f25014021dd54050087f15014021dc540500873f54953309f98a54cc27d62953309f98654cc27d6195330cf18e54cc33f6295330cf98a54cc33d6295330cf18a54cc33f6195330cf98654cc33d6195330cf18654cc33f6095330cf58254cc27f62553309f18954cc27f61553309f18554cc33f6555330cf98d54cc33f6255330cf98954cc33d6255330cf18954cc33f6155330cf98554cc33d6155330cf18554cc33f6055330cf58154cc33d5415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cf55343cc33e5490f30cf55243cc2fa6090f30be58243cc33e5450f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc2be64d4b30af59352cc33e54d4b30cf55352cc2f661d4b30bd58752cc33e5494b30cf55252cc36f5294b309f99252cc27d6494b309f98652cc27d6194b30cf95152cc33d5454b30bdd8552cc2f46154b309fd9152cc27
  | 18 => 0x9fd96310867d658c421d794e310875d538c421bb98a31086ed628c421bd98631086f5658c421dd5963108675658c421bdd9231086f6648c421bd59231086f5638c421dd94e31087d6538c421f554e3108774538c421f998a31086f5628c421f958a3108776528c421bd98231086f5608c4219fd9531086f7654c421ddd9531086f7644c421bd99131086f5644c421bd19131087d7634c421dd94d3108774534c421bdd893108776524c421bdd8131086f4604c4219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421bd98431086f5650c421dd5943108675650c421bdd9031086f6640c421bd59031086f4640c421bd98c31087d6630c421ddd4c31087d6530c421dd54c31087d5530c421f998831086f5620c421f95883108776520c421bd98031086f5600c421f9cc721087e631c8421f94c721087e431c8421bb98321086ed6288421db94a21086f76388421bd98e21086f56388421bd18e21086f56288421dd94a21087e65288421bd98221086f560884219fd9521086ef6548421dbd95210866f6548421bbd85210876e5148421bb18121086f76548421ddd9521086776548421bdd8d21086f66348421bd58d21086f46348421bdd8921087e76248421dd94921087e65248421bdd8121086f46048421ded42500867e63940219f58e50086df6354021b718d500867f6354021d7d8d500865f63540219f18d500875c63540219718d50087763154021dd4c550086de6314021b758c50087795014021bd99353086f564d4c21bd98b53087e662d4c21b998b53086f660d4c21bd58353086f56594c21bd99253086f56494c21ddd4e53087d75394c21bd98253086f56094c21bdd9153086f46454c21f5d4d53087765354c21bdd8153086f46054c21bd99053087b66414c21ad99053086f56414c21ed59053086b56414c21bd98c53087775314c21f594c53087755314c21f554c53086f66214c21f998853086e66214c21bd98053087f26014c21bc98053086f56014c21fc58053086f16014c21bdd9643086f66590c21bd59643086f46590c21bd59243086f66390c21f594e43087d55390c21f5d0e43086f66290c21bd58a43086f66090c21bd58243086f76550c21bd99543086f56550c21bd19543087d65350c21f554d43087b64350c21bdd8943087e76250c21b9d8943086f46250c21f918943086e46250c21bdd8143086f46050c21bdd9443086f66510c21bd59443086f46510c21bd98c43087d64310c21f550c43087954310c21bd98843087e66210c21b998843086f56210c21f958843086e56210c21bd98043086f56010c21bd98e52086f56394821ddd4e52087765394821dd54e52087745394821bd98252086f56094821ddd8e52087766394821dd58e52087746394821dd90e5208775439
  | 19 => 0x3534875f5394d219f992534867d6494d219f98e534867d6294d21db58a534867d6194d21dd58653486756194d219f982534867d6094d21afd9153486bc6454d21bed8153486f86054d219fd91534873f6454d218fd91534867c6454d21cf191534863c6454d21d7d8d534867f6254d21dbd89534867f6154d21ddd8553486776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f6590d219f996434867d6590d219f196434873f5490d21cf152434867f6550d219f995434867d6550d219f195434867f6510d219f994434867d6510d219f194434875f5310d21d714c434879d4310d219f997324875f53cc921d714f32486f661cc921bd587324867e658c9219f19532486bf644c921af191324875f534c921d714d32486f7614c921bd18532486fb604c921be181324867e650c921af99032486bd640c9219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521ddd4f214877653c8521dd54f214877453c8521f9d46214867e63d41219f58f504877721d4121ded4250486df6354121b718d504877950141219f98c504867d6314121ddc84504876e21141219f993530867d64d4c219f98b530876e62d4c219f987530877661d4c219f983530867d60d4c219f596530875f5394c219f992530867d6494c21dd986530867e6094c219f582530867f6454c219f191530875f6354c21dd185530867f6054c219f18153086be6414c21af590530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f98c530875e6314c219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c21bd98643086f56190c219fd95430867e6550c219f595430867c6550c21d794d430875d5350c21bbd8943086ec6250c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21e750c43086ee6210c21bb58843086f66110c21bd584430867e63948219f58e520867d65cc821bd587320867f658c8219f596320875e538c821d754e32086f6618c821bd586320867f654c821afd9132086bc644c821bdd8532086fb604c821be181320867f650c8219f59432086be640c821af590320875e530c821d754c32087cd320c821bd98432086f5610c8219f98e510867d63944219f59731086f565cc421dd59731086f664cc421bd59331086f464cc421ddd4f310877553cc421bd58b310877652cc421bd98331086f560cc421
  | 20 => 0x86f66290f21bd58a43c86f66090f21bd58243c86f76550f21bd99543c86f56550f21bd19543c87d65350f21f554d43c87b64350f21bdd8943c86f46250f21bdd8143c86f46050f21bdd9443c86f66510f21bd59443c86f46510f21f590c43c87d54310f21e550c43c86f66210f21bd58843c86f66010f21bd58043c86f565ccb21dd59732c86f664ccb21bd59332c86f464ccb21f590f32c87d543ccb21bd98332c86f560ccb21bd59632c86f7648cb21bd99232c86f5648cb21f594e32c87d5538cb21f5d0e32c87d4438cb21f5cca32c87e7328cb21bd98232c86f5608cb21bdd9532c8777654cb21bdd9132c87b7644cb21add9132c86f6644cb21bd59132c86f4644cb21ed19132c86b4644cb21f590d32c87d5434cb21f9cc932c87d6324cb21bdd8132c87f3604cb21bcd8132c86f4604cb21fc18132c86f0604cb21bd59432c86f7640cb21bd99032c87b6640cb21ad99032c86f5640cb21ed59032c86b5640cb21bd19032c87d6530cb21f554c32c87d7430cb21f510c32c87d7320cb21f98c832c87d5320cb21f94c832c86f6600cb21bd58032c86f663d4321f598f50c86d663d4321bd58f50c87d563d4321b558f50c877753d4321dd54f50c87e662d4321bd98e50c86f56394321ddd4250c87f35094321dcd4250c86f76354321bd18d50c87775354321dd54d50c87f35054321dd94150c86f66314321bd58c50c87e66214321ddd4050c87f25014321dd54050c87f15014321af99353886bd64d4e21be98353886f960d4e219f993538873e64d4e218f993538867d64d4e21cf593538863d64d4e21db58b538877661d4e219f983538877a60d4e219e983538867d60d4e21de583538867960d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21d754c538867e6414e219f590538875e6314e21db58853887766114e219f980538867d6014e219fd96438867e6590e219f596438867c6590e21cf952438873d5490e219fd95438867e6550e219f595438867c6550e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21d794c438875d5310e21e750c43886ee6210e21bb588438875e53cca21d754f32886f661cca21bd58732886bf644ca21af191328875e534ca21d754d32886f7614ca21bd18532886fb604ca21be18132886be640ca21af59032887cd320ca21d794e318875d538c621bb98a31886ed628c621d794c318875d530c621bb98831886ed620c621bb597218876d65c8621bb98321886f565c8621dd597218877753c8621dd94f218877553c8621dd14f21886de63d4221b758f508877b50942219f98e508867d6394221ddc86508867f63542219f18d50887772154221de540508867e64d4d219f593534867e60d4d219f58
  | 21 => 0x654c431b7d95310c75f654c43197d95310c6df614c431d7945310c7d7414c431f5105310c6dc604c431bdd95310c777654c4319dd95310c6f7634c431f5d8d310c776534c431f594d310c7d7434c431f510d310c6f4624c431dd949310c6be64d4031af593500c77b50940319f992500c67d64940319f98a500c67d62940319fd91500c67c64540319fd89500c67c6254031dd8c5500c7753154031de540500c67e64d4f219f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f21dd58653c867e6094f219f58253c867f6454f219f19153c875f6354f21ddd8553c867f6054f219f18153c86be6414f21af59053c875d5314f219f99053c873e6414f218f99053c867d6414f21cf59053c863d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f6590f219f99643c867d6590f219f19643c875e5390f21d754e43c86f66190f21bd58643c867f6550f219f99543c867d6550f219f19543c875e5350f21d754d43c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c879d4310f21bd98443c86f56110f21bd98732c875e538cb21d754e32c86f6618cb21bd58632c86bf644cb21af19132c86f4614cb21bed8132c86f8604cb21af99032c86bd640cb21d794c32c875d530cb21bd98432c86f5610cb21d794f31c875d53cc721bb98b31c86ed62cc721bd59731c877565cc721bd99331c86f564cc721bd19331c877753cc721f594f31c877553cc721f554f31c87e662cc721bd58b31c87e562cc721bd98331c86f560cc721bd59631c8775658c721bdd9231c86f6648c721bd59231c8776538c721dd14e31c86f5628c721bd98231c86f5608c721d794d31c875d534c721bbd8931c86ec624c721bdd9531c8777654c721bdd9131c86f6644c721bd59131c86f4644c721f5d8d31c8776534c721f594d31c87d5534c721dd14d31c86f7624c721f9d8931c87e4624c721bdd8131c86f4604c721bd59431c8775650c721bdd9031c86f6640c721bd59031c86f4640c721f598c31c8777530c721dd54c31c86f5620c721bd98031c86f5600c721b798f50c86dd63d4321ded4250c867e63943219f58e50c867f63543219f18d50c87763154321dd4c550c87795014321bd99353c86f564d4f21bd98b53c87e662d4f21b998b53c86f660d4f21bd58353c86f66494f21bd59253c87775394f21f5d4e53c86f66094f21bd58253c86f76454f21bd19153c87d75354f21dd94d53c86f76054f21bd18153c86f66414f21ed99053c86b66414f21bd59053c87b56414f21ad59053c87775314f21f594c53c87755314f21f554c53c86f66214f21f998853c86e66214f21bd98053c86f56014f21bdd9643c86f66590f21bd59643c86f46590f21f594e43c87d55390f21f5d0e43c
  | 22 => 0x931af191524c6fb6054931be181524c76d52149319f990524c67d6414931ddd84524c67e60149319f580524c67e65d09319f597424c67c65d0931dbd4b424c76c52d0931bd987424c6f561d09319f996424c67d65909319f196424c73f5490931cf152424c67f65509319f995424c67c6550931b7d8d424c6dc6350931bdd85424c6f46150931bed81424c6f860509319f994424c67d65109319f194424c73f5410931cf150424c6de6310931b758c424c76f5210931db148424c67e65cc931bd987324c76f528c931db14a324c6f6618c931bd586324c6bf644c931af191324c76f524c931db149324c6f7614c931bd185324c6fb604c931be181324c67e650c931af990324c6bd640c9319f997414c73f54d0531cf153414c6de63d0531b758f414c67d65505319f195414c6df6350531b718d414c6f662cc531dd14b314c6f560cc531f5d46314c67e64d41319f593504c67e62d41319f58b504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c67e62141319f588504c75e3114131be983540c6f960d5031d798f540c67e62d50319f58b540c77661d50319f983540c77a60d50319e983540c67d60d5031de583540c67960d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c67f60550319f181540c73d54150319f98c540c75e63150319f988540c67d62150319f984540c77661150319f980540c67d60150319f592530c67d65d0c319fd96430c67d6590c31cf952430c73d5490c31bd986430c6f56190c319fd95430c67f6510c319f594430c73e5410c31cf550430c79d4310c31bd984430c6f56110c31dbd4a520c67e64948319f592520c77461948319f982520c67d60948319fd91520c67c6454831dd185520c67f60548319f181520c6be6414831af590520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c6f661d0831bd587420c67f65908319f996420c67d65908319fd95420c67d65508319f195420c73e5450831cf551420c6df6350831b718d420c6f76150831bd185420c6fb6050831be181420c67f65108319f994420c67d6510831b798c420c6dd6310831db94b320c76d52cc831bd987320c6f561cc8319f596320c67f654c831afd91320c6bc644c831bdd85320c6fb604c831be181320c6be640c831af590320c76e520c831db548320c7cd320c831bd984320c6f5610c8319f992510c67d64944319f597410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c67f65504319f994410c67d65104319f194410c6de6310431b758c410c6de60cc431b758e310c75e538c431bd58e310c776538c431f594e310c6f6628c431dd94a310c67f
  | 23 => 0xf59542cc67c6550b31cf95142cc73d5450b31b7d8d42cc6dc6350b31db94942cc76d5250b31bdd8542cc6f46150b31bed8142cc6f86050b319fd9442cc67e6510b319f59442cc6de6310b31b758c42cc76e52ccb31db54b32cc6f661ccb31bd58732cc6bf644cb31af19132cc6f4614cb31bed8132cc6f8604cb31af99032cc6bd640cb31db94832cc76d520cb31bd98432cc6f5610cb31b798f41cc6dd63d0731af99350cc6bd64d4331bb98b50cc6ed62d4331ded4250cc67e64943319f59250cc67e62943319f58a50cc67f64543319f19150cc67f62543319f18950cc77950143319f98b548c67d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231be980548c6f96015231cf953438c73d54d0e31bd987438c6f561d0e31cf951438c73d5450e31bdd85438c6f46150e31e750c438c6be64d4a31af593528c6fa60d4a31be583528c76f5294a319f992528c67d6494a31dd186528c67e6094a319f582528c67f6454a319f191528c7746154a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a31bd987428c6f561d0a319fd96428c67e6590a319f596428c73e5490a31cf552428c67f6550a319f595428c67c6550a31b7d8d428c6dc6350a31bdd85428c6f46150a31bed81428c6f86050a319fd94428c67e6510a319f594428c73e5410a31cf550428c6de6310a31b758c428c6f561cca31db94a328c76d528ca31bd986328c6f5618ca31afd91328c6bc644ca31db949328c76d524ca31bdd85328c6f4614ca31bed81328c6f8604ca31af990328c6bd640ca31f34c8328c6de6390631b758e418c6dd65cc631d7597318c6de60cc631bd597318c77565cc631bd98b318c77652cc631bd583318c77b50942319f992508c67d64942319f98a508c67d6294231afd91508c6bc64542319fd91508c73f64542318fd91508c67c6454231cf191508c63c64542319fd89508c67c6254231af990508c6bd6414231de540508c67e62d51319f58b544c67e60d51319f583544c73f5495131d758e544c67e62951319f58a544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d6015131cfd53434c73c54d0d31bd987434c6f561d0d319f996434c73f5450d31cf151434c6f76150d31bd185434c67e6510d31e750c434c67e64d49319f593524c77561d49319f983524c67d60d4931dbd4a524c6bf6454
  | 24 => 0x430cb9d5410c32c7550430cbce6210c32b7588430cbcd6210c32b7980430ca7e64948329f592520cb5f4394832d710e520ca7d65d0832cf953420cb3d54d0832e7d0f420caf661d0832bd587420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420cb9c43908329fd95420cb3e5450832cf551420cadf6350832b718d420cb9f4350832bdd85420caf46150832bed81420caf860508329f994420ca7d65108329f194420cade6310832b758c420cb9c4310832cf953320cb3d54cc832bd987320caf561cc832b7993320cadc64cc832d7d53320cb9e54cc832d7553320cb9d54cc832c7553320cbd661cc832f5587320cade60cc832cf952320cb3d548c832b758e320cb5e538c832eb952320cbad548c832bb58e320cb6e538c832f394e320cbcf438c832f310e320ca7f654c832afd91320cabc644c832cf951320cb3d544c832bdd85320caf4614c832bed81320caf8604c832b7d95320cb5f654c83297d95320cb9f644c832b7991320cadc644c832e7191320ca9c644c832d7d51320cb9e544c832d7551320cb9d544c832c7551320cadf624c832d7949320cbd7614c832f5185320cbdb604c832b7181320cbd8604c832b6181320caef654c832dbd95320ca6f654c832ebd91320cbac644c832eb951320cbad544c832bbd8d320cbcf634c832db94d320cbce534c832f9d85320cbe4614c832fad81320cbe8604c832af993510cabd64d4432cf953510cb3d54d4432cf952510cb3d5494432ddd46510ca7e64944329f592510ca7e60944329f582510cb3e5454432cf551510ca7f64544329f191510ca7f60544329f181510cabe6414432af590510cb3e5414432cf550510cb755114432be980510caf96014432af993500cabd64d4032cf953500cb3d54d4032cf952500cb3d5494032ded42500ca7e64940329f592500ca7e61940329f586500cb3e5454032cf551500ca7f64540329f191500ca7f61540329f185500cabe6414032af590500cb3e5414032cf550500caf66114032bd584500cb795014032cfd5254cc67e62953319f58a54cc67e60953319f58254cc67f62553319f18954cc67f60553319f18154cc73d5415331bb98854cc6ed6215331d798c54cc67e6215331db98854cc66e62153319f58854cc76d62153319b58854cc77561153319f98054cc67d6015331cf95243cc73d5490f31bd98643cc6f56190f31cf95043cc73d5410f31e750c43cc6f66110f31bd58443cc76f5294b319f99252cc67d6494b31ddd8652cc67e6094b319f58252cc67f6454b319f19152cc7776154b319fd8152cc67c6054b31af99052cc6bd6414b31db54852cc67f65d0b319f99742cc67d65d0b31cf95342cc73d54d0b31bd98742cc6f561d0b319fd9642cc67e6590b319f59642cc76e5290b31db54a42cc67f6550b319
  | 25 => 0xa7e61d41329f587504cb7b54d4132eed53504cb3b54d4132de953504cb7954d4132de153504cbb854d4132ce153504cbda43d4132f650f504cbeb32d4132f68cb504cb7b51d4132fcd47504cb7351d4132de947504cb7951d4132de147504cbf051d4132dc147504cb7b64d4132de993504cb7964d4132de193504cb7b63d4132ded0f504cb7a43d4132de50f504cb7843d4132ded8b504cb7b42d4132de90b504cb7942d4132deccb504cb7a32d4132ded87504cb7a61d4132de587504cb7861d4132af992504cabd6494132cfd52504cb3c5494132bd986504caf56194132ddd46504cb745194132ded42504cabf6454132af191504cb3f5454132cf151504caf76154132bd185504cb775154132dd145504cb3f5414132cf150504cb775114132dd144504cb7950141329f990504ca7d6414132d790c504cb5d4314132d78c8504ca7e61141329f584504cafa6514132de994504cb7b5414132eed50504cb3b5414132de950504cb795414132de150504cbb85414132ce150504cbda4314132f650c504cbeb3214132f68c8504cb7b5114132fcd44504cb735114132de944504cb795114132de144504cbf05114132dc144504cb7b6414132de990504cb796414132de190504cb7b6314132ded0c504cb7a4314132d690c504cb794314132d650c504cb784314132ded88504cb7b4214132de908504cb794214132decc8504cb7a3214132d68c8504cb793214132ded84504cb7a6114132de584504cb786114132d798f540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d60950328f596540cb9c6395032cf98e540cb3c6395032cf98a540cb3c6295032cfd86540cb3e6195032cf586540cb3c6195032cfd82540cb3e6095032cf582540cb3c6095032cfd91540cb5c63550329fd85540ca7c61550329fd81540ca7c6055032cfd95540cb9c6355032cf98d540cb3c6355032c718d540cb3e6255032cf189540cb3c3255032cfd85540cb3e6155032cf585540cb3c6155032cfd81540cb3e6055032cf581540cb3c6055032af990540cb3d54150329f98c540cb5e63150329798c540ca7e6215032db988540ca7e61150329f584540ca7e60150329f580540ca7d6494c32dd986530cb756194c329f597430cb3e54d0c32cf553430cadd65d0c32d7597430ca5d65d0c32d7d53430cb9e54d0c32d7553430cb9d54d0c32c7553430cadd62d0c32b7983430ca7f6590c329f596430cb3e5490c32cf552430cade6390c32d794e430caee6290c32bb58a430ca7f6550c32cf951430cb3d5450c32d794d430ca7f6510c329f594430cb3e5410c32cf550430cb9d4310c32bb988430caed6210c32d7594430ca5d6510c32b7990430cb9e6410c32d7d50430cb9e5410c32d7550
  | 26 => 0x1951329f982544cb7a60951329e982544ca7d6095132de582544ca796095132bdd85544caf46155132bed81544caf86055132d7d8d544ca7f6255132dbd89544ca7f6155132ddd85544ca7761551329f185544cb7461551329d185544ca7f6055132ded81544ca7b60551329f181544cb7860551329e181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d6015132af994544cb3e65151328f994544cb9d6315132cfd8c544cb3f6215132cf588544cb3d3215132cfd84544cb3e6115132cf584544cb3c6115132cfd80544cb3e6015132cf580544cb3c6015132cfd53434cb3c54d0d32bb98b434caed62d0d329f996434cb3f5490d32cf152434cade6590d32d7996434ca5e6590d32b7592434cb9f5490d32d7952434cb5c5490d32e7152434cb1c5490d32b798a434cb3f5450d32cf151434caef6250d32bb189434cb9f6450d32e7d51434cb5e5450d32d7151434cb9c5450d32c7151434cbcf6250d32b7189434cbcc6250d329f994434cb3f5410d32b798c434cb9d4310d329f997424cb3f54d0932cf153424cade63d0932b758f424cb9d43d0932bd987424caf561d0932cfd52424cb3c5490932e790e424ca7d65509329f195424cadf6350932b718d424cb9d4350932cfd53324cb3c54cc932bd987324caf561cc932ebd53324cbac54cc932f390f324cbcd43cc932f9987324cbe561cc932cfd52324cb3c548c932b7d92324cadd648c932e7d52324cb5e548c932d7152324cb9c548c932c7152324cbcf528c932cfd53514cb3c54d45329f993514ca7d64d45329f983514ca7d60d4532ddd53514cbb754d4532cdd53514cb7654d4532dd553514cb7454d4532ed153514cb3454d4532f590f514cbd543d4532f9ccb514cbd632d4532ddd93514cb7664d4532dd593514cb7464d4532ddd8f514cb7743d4532dd90f514cb7543d4532dd10f514cb7762d4532ddd0b514cb7642d4532dd50b514cb7732d4532dd8cb514cb7760d4532dd983514cb7560d4532dd183514cabe6494532af592514cb3f5494532cf152514cb775194532be982514caf96094532afd91514cabc6454532cfd51514cb3c5454532bed81514caf86054532cfd50514cb3c5414532dd544514ca7e64145329f590514ca7e60145329f580514caf66514532dd994514cb775414532edd50514cb375414532dd950514cb755414532dd150514cbb45414532cd150514cbd64314532f550c514cbe73214532f58c8514cb776414532dd990514cb756414532dd190514cb776314532ddd0c514cb764314532dd50c514cb744314532ddd88514cb774214532dd908514cb754214532ddcc8514cb763214532dd4c8514cb776014532dd980514cb756014532dd180514cb3f54d4132cf153504cb7751d4132dd147504ca7e64d41329f593504c
  | 27 => 0x32e715143ccb1c5450f32b718943ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32b798f42ccadd63d0b32e750f42ccb7751947329f99251cca7d64947329f98251cca7d6094732ddd5251ccb765494732dd55251ccb745494732f590e51ccbd54394732ddd9251ccb766494732dd59251ccb746494732dd18e51ccb774394732dd90e51ccb754394732dd10e51ccb776294732ddd0a51ccb776094732dd98251ccb756094732dd18251cca7f64547329f19151cca7f60547329f18151ccb776554732ddd5151ccb765454732dd55151ccb745454732f590d51ccbd54354732ddd9151ccb766454732dd59151ccb746454732dd98d51ccb774354732dd90d51ccb754354732dd10d51ccb756254732ddd0951ccb776054732dd98151ccb756054732dd18151ccb755114732af99350ccabd64d4332bd98750ccaf561d4332dd94750ccb7551d4332dd94650ccb755194332ded4250cca7e64943329f59250ccb5e4394332d750e50cca7e61943329f58650ccb765154332dd54550cca7f64543329f19150cca7f61543329f18550ccaf66114332bd58450ccb765114332dd54450ccb795014332db98b548ca7e61d52329f587548ca7e60d52329f583548cb3f54952329f986548ca7d61952329f982548ca7d6095232cfd91548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf953438cb3d54d0e32bb98b438caed62d0e32e7953438cb5d54d0e32e7553438cbce62d0e32b758b438cbcd62d0e32b7983438cb3f5490e32cf951438cb3d5450e32bbd89438caec6250e32e750c438cadd6510e32d7594438cb9e6410e32d7d50438cb9f5410e32c7d50438cb5d5410e32e7150438cadd6210e32b7980438cb9f43d0a32bd987428caf561d0a32b798e428cadd6390a32e710e428caf661cca32bd587328cadd65cca32d7597328cade64cca32b7193328cb5f54cca32d7553328cbd661cca32f5587328cade60cca32bb597328cb6d65cca32f9987328cbe561cca32ddd46518ca7e64946329f592518ca7e60946329f582518ca7f64546329f191518ca7f60546329f181518cb755114632bd986508caf56194232ded42508ca7e64942329f592508ca7e6194232dd986508ca7661942329f586508cb7561942329d586508cabf6454232af191508ca7f6454232cfd91508ca3f64542329f191508cb3c64542328f191508ca7f61542329f185508cb7950142329f987544ca7d61d51329f983544ca7d60d5132e7d8f544cb3f63d5132cf58f544cb3f62d5132cf58b544cb3f61d5132cf987544cb3d61d5132cf187544cb3f60d5132cf983544cb3d60d5132cf183544cb3f5495132bd986544caf56195132be982544caf96095132d758e544cb6d62951329f986544cb7661951329d986544ca7d6195132dd586544ca756
  | 28 => 0xd815190e7c6054643dd5445190efa6014643be5805190f7b5094243cfd0e5090e7e62942439f58a5090e7e61942439f5865090e7f62542439f1895090e7f61542439f1855090ef66114243bd5845090f795014243e7d4e4350ebd6290d43af9824350ef661d4943bd5875250e7e61d4943dd9875250e7661d49439f5875250f7561d49439d5875250e7e60d49439f5835250f6f5294943bdd855250ef46154943bed815250ef86054943db5485250f3e43149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f7551145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050ef66114143bd5845050f7950141439f9885050e7d62141439f9845050f7661141439d9845050e7d6114143dd5845050e756114143b75924310e9d6490c43d79524310f9e5490c43b798a4310e7f6550c43b7d954310f5f6550c4397d954310edf6450c43d79514310f9e5450c43b71894310f9f6550c43a7d954310f1f6550c43e7d894310f9e6250c43e75894310f9c6250c43a71894310f9f6150c43e79854310f9d6150c43e71854310f9f6050c43e79814310f9d6050c43e71814310f9d43d4843bd9875210ef561d4843e750e5210f6f52948439f9865210e7d61948439f9825210e7d6094843e750d5210ef76154843bd1855210efb6054843be1815210f5e4354843d750d5210f1d43548439fd855210f7761548439dd855210e7c6154843dd1855210e7461548439fd815210f7b60548439ed815210e7c6054843de1815210e786054843e750c5210f6d5214843e750f5110eee62d4443bb58b5110f9d4394443ddd465110e7e62944439f58a5110e7e60944439f5825110f9d43544439fd895110e7c62544439fd815110e7c6054443e750c5110f755114443e750f5010f9d4394043ded425010f5e4394043d750e5010f1d43940439f98a5010e7d62940439f9865010e7d6194043e750d5010e7f62540439f1895010e7f61540439f1855010f9d4314043bb9885010eed6214043bd9845010ef56114043de5405010ef661d5332bd58754ccafa60d5332be58354ccb3f54953329f98654cca7d61953329f98254cca7d60953329fd8554cca7c61553329fd8154cca7c6055332cf55054ccaf66115332bd58454ccb5e6315332db58854cca7e6115332dd98454cca7661153329f58454ccb7561153329d58454cca7e60153329f58054ccb3e5490f32cf55243ccaee6290f32bb58a43ccb5e5490f32e795243ccb9d5490f32d715243ccade6290f32f398a43ccbcd6290f32b7d9543ccb5f6550f32e7d9143ccb9f5450f32d795143ccb5c5450f
  | 29 => 0x10004000000000000840010018018000000b00000000004009000c0010008009000000c00200040028001000000d00000050008002000000000040020004001004c0060000002001000000100040000000000800200080010000000000c001000c000000400200000030000001000000e0000001001400100000000000000000000a00100000010000000801200300030000000000000000100030004001001400400100000000003000000300000020008000000c001000c0000010000000c0000018001000400000180020000001000c00100000050014001000800700000000004000000c000000000300140020004002000400100140000004000000c00000000000000004000800000000000008006000c00c000400200000040000000000000000600010018003000800300100000008003001801e000c001001800300180000000001000000200300000050005000400f0000004000c00100080020000000001800200000080000002000000900000000004000000c00300080020000001000000400180000000000000c00d0000008004400100040040004000000c0020000003000800000100050004001000c000000000100080000000001000000b0000001000000500000150000000000c00200000020004000000000100080070000002001400800000020008000000000100000040000003000000200280080004002000000200000010000003000c001002c0000000000003400000040000014001000000500080040008000000000200000010014005000800800000000018004000000800080030000002000400000200010004006000c00300040010024002000000200080020018000000000000000040010007000800000040040000008000000400000000008013001000000040010000009000400000180000018000000c000000c000001000000100000000001000000000080010000003000000100040010000003001000a001000200040010000000001c00300140000008002000000300000000000002001000e004000000100030004009003c000002c000000800400000020024002000c0000000004001400a000400200000010004001000800b0000000001800100000060040004000800400000010000005000000400200050000004001400000000050014000000000000100000000002000c0030008000003c00100080010002dd65d0e43d75974390ef661d4a43bd5875290efa60d4a43be5835290f6f5294a43d7d0e5290e7e6194a439f5865290e7e6094a439f5825290ef76154a43bd1855290f3f4354a439fd855290f776154a439dd855290e7c6154a43dd1855290e746154a439fd815290e7c6054a43db5485290f7751946439f98a5190e7d62946439f9825190e7d60946439fd895190e7c62546439f
  | 30 => 0x30014000000000000000010008003002000100040020000001000000c0004007000800b0000000000c000001800000080020018000000400f00000040014000000000100140030024001000c0010014025001c001003c002000000700180050000001001800100000010078003000000b00100000004000000000200140030000001002400000100000000000000000500000080000004000000100040000008001001800200000000000001000c00200040000000002000800300000000034001000400000000000000005000000200000040014000000c0080004001000c0000008000000000100000000000002000c007002000100000000018001000000000140020060000000c002002c001000000300000020000000002400200000020044000000400000080000000001000000700000000000000000c000000000200140000000007000c0020004001000c0020008001000800100000000004000000400000380020000003000000300080020008002000c008000000300340090000001000c000000c000004c003000400000040030000000000c0000000000000000e00000020024001000c006004400700000080000000000c002000c00000000050000002003000000000020000000002c00c0004006001400000180030000000000c001000000100080020024000000800000000050000008000400400080010000000000c00400000000010000001800400000040000006000000400100010000001001000500080010000002000c0000004002000c013001c0040000001002c0000008002000c0060000001000000d000000200000030000001000400200040000008000000000300000020004004001400d00040030000001001000200000000010000000400200180010000006000000100000080000000000c001000c0000000002000c001001c00000040020004001000000500040000008000000000a0018000000c0010004000000c0000004000001800300000000030007000000100000010018002000000100000000018001000000000000070038000003800100080000004000002800000000000008000000800500000000018000000c00200040000008005000000b001000d0014000000000000140020014001000400000040070008000001000100040030000000000800300100010008000000400d0008000000800500100000024000002800000000070004012000000200200020004003000000000000030010001000800100000000008000001c003000c003004000200040000000004000c00600000000008003001c000000c005003400000000040024003000000200080010000002000000b0004004001800100040000004004000400800000050000000000001d0000000000000100080000004000001800000
  | 31 => 0x1400200000000010001000c005000800300780080004004000800e0000003000c006000800000140000028000000000d0008001000c000000000000000000004005000000500000000008000000c00000000000020000001c0010000000000000200000020044000000000100000000000000000000a000c00000140040000008000400300080000008008000800f000800200040000000002000800100000010000000000400000000040010003000c00d0000000000c00100080010000001000400100100000004001000000100080040020002000000000080050018003001c000000c000000800000000000004005000000000000040014007001c00500000020008000000c00000300010008002001c0000000004000000100040020000001000000200100000000003001400000000000000002000400100040000000009000c002000400000040010000003000800000040020014007000c0010000003000400d0018000000000100080000000001000c000000000000080000004000001000000140020000001001c00000000000014001001c001000000100040010000003000400000040140000001000000000000000004004001c0000000000000000100040010074001001000300100040004006002c00300100000000001000000100000010008001004c00200000000000000000000300440010000000000c00600080020000001003c000000401000000010000001001000100000010000000000400000000030000000000000500000020008003000800100040010000001001400000000010000007003800100000070018012000800d00100000004004000400100040000004000000000700000020004000003800500140040014002000c00000000010000005003c0010014006000c00500000080000002000400000040070008000000000700000000000000000000100000050000001003400200000060018007000400000040000018001000001300040000000000001c0020000001000c00400100080008000000800e000000000180000020004000400300040010000002000000e00100010008000001800000000000000002000400000180000008002000400100000000000001000000300040000000004000000200080000004002000800700100010000001000c0050004001001c00000040020008004001000400080040000000001c002001400400180000078004000000000100060010001000c000000000300040000004001001800000000000004001000c0000000010001000000000020008003000c000000000300000010008007000400200180000010004000c000000000200000140004003000c002001c003000000100000000008000000000000000000018006000400100180060000000000000100000
  | 32 => 0xe00040040008000000000200080000024014000000000040010028000000000000000010004000001c002000000600040010000009000800700040000004004001800300000040000001000400000000000010004004001100040050000003001000000000030000002000c00d00000000000000002800500080020000003000000c000400f000000000000000000000000c00b0008000000c00000080010010000000400900000010010001003c0000004007000800100000000000001000c0020008003000000b00040000008000000000a0000001000c0010004002000400400000000000002002000a0000001001400100000040008004002400b001000200000050000015009c001000000100000000000000003c0000018001000000000100040000012000c0030000000000000200000010004000000c003000800e001c018000000300040020004000000000000000010014000000400400000010000006000c0070000000000000500040020024003000000500100010000000000400000080150000000002000a00040040000008000c00000000070000003000000200040000000000000000300240000008001000c0000000000000000200080020000001000400400180040000005001400e00000000000000002000300040010000002002000200040000020000000000300000000000000000000f0004000000000000000060010000001000400000000004000000000a0010003001400000000010004002000400300040070000000002000c0004005000800400040010034001000400000000020004000002c00000000000014000000400000100000000003000000000000040004000001000100000030000000000800600000030000001001c000001800100000010008005002400000380000028001000000100000040000002000000d00000000008008002800400000000004004001c002001c0000004002000000b000000200000010010001000c00000040000008000000800b0000000000800200040040008000000000000040000000000001c000000400300040030000005004000100040020018001000000b0004004000000200000000004000002000100000000048006000000a0004000003c00000140030004001000000100000000004001000000000040000004000000400000040000000001000c0000010001000c0000000000000000400280010000000001800900040010004000001400100000020000000000000200000030004000000800b00000070024001000c00000080060024006000400000040070014001000000000000000000001000c002000000000880050004004000000000300000020001000c00d0004001000400300040000004001000c001000000100000030000000000000000100000
  | 33 => 0xb2500000002180000000019a00000001f1e1f600001d300005c1840719cc00083a000045d9a79000000000018245e601ac2108310a890000bffa4ea0000b5d000000071800007db0000bb600000adafd28f4a606219c000a1d80000001e80000308d22c929a00000009671aa00001b440000000144c00059a92c61d981305a8a5c800009943b600000000000000075c000000012aa0425ba080a00000001cc8000000053b94bdafb4218000849877000000008a30000616115c3a0800000000000000ccc4d080008e20000a03ab585d7173e0002f222c588651a7c00057e09f7af501023e1000000000004550000afc000000024e2b1d1dafaa0a3b340e476d071400000006443fd80000000000000000000000000000154aba80008370000000000021e0000000171600000009f1000000000e26e00000a0500002a185b65cb000000000000001cdc0001ea223882cfbfa800000024e000000000000000000170826f8000000000046a206a00020c65688000aac80007cbcad500001525169abc31d000035fc000ae4800082680007b0df329ba8c30657d9be6211a54c1700004cd95644d1c0000002c7200009ec00000000000000406021800040020010001000000500040040008000000c0000000004000800600000000000006000400000180090000000001c0010000000002c00600040020004003002000500000060000003000000500040000004003001c00000000010008001000c0000000014000400f000000000000000000004000c00800040010000002000000000100130028002002800000080010000000000000000e000500040020000000000c00300040000000002000400300000000008000000000100000070000000000000100080010000004000000300080040000001000000000000000008000002c000000000000180010028005001000500180000008002000c004000000000200040080000000800000000000008001000400b004c006000c0000008007000000200000000020000000800b00000010004002002400a0004002000000300000080008002000000100100060000000000800200240040000006003400000000000000001000400d000000000000000010001000000800240130004003000400c00000000000003000400100040010000001002400000000000000004000c001000000200040310014004000c00e001c000000000300040010004003001400200040040004001000400200040000018000003c00200000000000000009000b000800c0014000000400100000010014004000c0000010001000000400000000000002000c000000000300180000020006000000000040000000002000c0090000000000c006000000200080050004000003c00200000000028000000c
  | 34 => 0x33a00000000001f58292b0a816c2567000000000000002b18000000000081d80000000000596c7be89a00000000f715628e6c2cd1398629c00000000009370000825800056bc0003b2800000022b258000000eb9a3e00000000001f4c3db40000000000000221c000000000014fe000169ca99000000000000000fd00000000000246a0ef80000aa80005508000000000000000007dd000000000007a9309c00000002ba800072304de6ca800000019fc1fb40000000000080a2ab08b800000000004c84000ad0931c1609cf89f5c9b8343c0000001518162684e13e467a9cd8f8a10dabc4aed14180002883000133325f000033ac00000029ca00000007390bfa1c59c615e6d067000002c000000076580000002e40000000061b25fa00000008788000000188e000095c48201596414000000105929f00000002c84200000036f84c60002ae000000000001b7d000226a000274825605f01a52d110000000a9c000000008120091578789ac1a00004be00000000d1c0004ce05bc81f00002c74000000051e00013c4000000076220aa632924e1100000000249eaf09f7a291a7609850000bc02002055efaa000198265100000000000414000095ad9c000000000000000000169e2b8cf7650d1b1400000000000000000000000000002fa29185918c1c000000000028e0000000000009cc66700009560000000240a4a38abb6e388228529f319751b1a4a5964c2cc00ea19aa13062d807ab0080009b914820000000073102e000016a00000009de000046d1e447420cb77589ce76d896bc439abde000000000028c6142c0000000000110ed7265c40000002b2a31c481a3f28fb680158cc000161600000005e1accb8a4c00084687f000016a85afae620000000000282200000000002a5ea79400000000000ab4000000000002329e16a480000001c8000000000000000bf3a9c19a3ada880d0fd2000000000000000001bf2268451600000000000e7c33cdac71c2ded017221cd656d51000000006c3259200010e0a4e1bca0000d2f0000988088000080e02c240f17e0a9f8000ade108aa10909e00000004b0222813a2942c1d2f3200009660000000000000000000000b51b32a7f96044094dfe83bd68600003ea00780002c7000000000003f000003202ba800002fe2f3400000019800000000000000054e80000000000000000000012eca941db02eb80002f48000c05ac988c59cde61a41be50819f832f80000000bcc00000009709b6a4881cea4438d740000000000000000014eebf80000678800000000000000000000035a000248800000005cac0000001282b4ab0d0000017ea540000000056417400000000000a73800075d4d0600004270000000000000019d83fc30dd03d00007400c81fc703af0be0000000273c00000000000000000
  | 35 => 0x2af380004ecd08231e02622b304411d891e3000164e6a90dbf0002f544bc8000000000090e0000000000000014dc5ad4000779182344f800000006ec0000000b878000547843aab8d5e2000177e248032228b8a1c066800000000000000000000000042e000000021048ba0d1a0132f293a521c872891741c305242948b4ca2f13d26db092c233a0c211d197038e128803a14ec4290cd68fba5205ab801a9b7acf42c6c98c00024ac6540000136800077300000002cec000109a83e93e00001ef89c18380000000000000000000000000000077a80006ace1fe2c38000000000030900000000000000000000019f400000000000ab60000000000000000000000000000072e65c56b8000a4e80000000000000191a3218000000229569700003c480000001bf46c100000000000b15a6e65ecc0000000000820a2a20000fe6364c00094900d02e307d600008800000000707ad86b339b3e9ce000039280007e1ad6316023b2000000059980000002cfe312ab228478000000000060ac60614bc55a0000000237a6a826180007630af8b8500000000000000209cb990000aab80000000000af2297c0000000000012c9a800007fc80006df982000003528d2df6750700000000000000079200000000000000576acc900010c25748000000000043c85f400000007810000a548000000076069d80007b10000000000000000000001e67904000003800007a98000a7600000000000b64032a000046567999189c7c00000000007b39548000240c0001cc400005c200006ac000044878800000001ca401ab046a5c86e2292e3240001fbc4cc000055d80000002d332ce297a61c97fead2a6858368fee7568000000132c46f80000002f486af9f434d4864e11e80000001e8600000008d7000030d000000000000001534498000000006c800000000000000000000000000002c61386000000000006a289d07ea00000000b89f920000000000000095c82891cd136651080006d9c950bec03089dc800000003cc9e770940000000640a62400000003df19c833a04b00000504159c140a4b058e4ca8000aec000075f975400009fe6ed800000009bb000011230a0000185800000008ee357000000000008f6ac2c01983d600010b2089ed5c0000000a1d4000705000000023b7000276c330d5220001e0a167184600013bc908939b4432c9a000000000000007948000384eba200000000001258773c00000006545971b5460c8000901193c5a986a680f2797b49a6b469dc0003224d4fb5500002dc000000020195bec0bb1228000000075300015b246e0a06b28800000000000002660a77143e0ae995e7b0000000002f000000000002cc2000261c000000069312a2b2f8b84a18000000000000000000677a3901352e0746280003ace8020000ee6362c000a62
  | 36 => 0xb8000a6680003ce8000716c000000000075b071ca9480008ce1c94000000004f701400000001eea89e2d10fb4966a40e48080004532ed25c34ed61ad8000304ad828c413962591aa858a43c4351c0000000000092000000000004c488522fd049f0002468000000000007791bb800000000005d6d7ba39a9928b5a89f600010a25270f981a0000000024261ad187a00000000000000000000000029b600000007de5ce2ae82489000236e0000000371c00000000001af000000003fda39831c1cf508c000153e0001cda0002cb918894ca7ee4d1c51245120000000000014200000008150000000000095d069a000294064900000000552a01000000014162fa96948afa72474b2540131400016680000002f660002d1e134c0009d3239a000197e2f22830ac72b8000021020000000000000071100429ecc86cb718000b8317e497ec90380cad0279e979a4fd8b9266f506ea201bf600005060000f1e940805e3f746425d300002f963dc65a926c0b721880001dbc83d0c028f997c6a33a16a784159db1104b2000233a000000000000000000302a77400010b000000030600002d2e998800006380007450000bb0a6fe3d800000000dd67f50000000008a5e417a800005ea1b780000000000000073e66b4df020eae10912ad22b38421a1a423b9a6b01f471430c21c1d83e5ff187031f0592a1889420000b4ea1a000029400002d01aba00017dc00015ca000000000000002af27ad14f27b4000000000000000000e007a28c6a0698000ab1a1da749ab46000000000000000001da0b0c000000000000000c8200009960000000000000000000000000000b7f305a000000000002660000000000000000018ce000000091bc4c90001a5f756ccb521fc3ca87500009169b8ca4f10467cf02a991100000000d6b00028d4000000000000007b880000000000000000000000007128000c1b800081580000000b6a7aa800019f00009c280003415fb1596ab545b1653a6d38000514270bbca818f9b0800000000009d4a5320000000000214c0000294be84000000000066a290200000007af40000000000267c00000000000001f5e0e7a740a92ccba358800000000000000000698800006ac928000164219017925b0939460740000ee1dd6b720000000000000000000002e2cc2480000000bb200002dba7dcbbe649aa9a00004b4218d1420001aec41b000022600001cb00000000000ac18c16000000000000000000000000108043c00002ab4000000000000013c01808000000000000000008cf84e00000000000000009ad166000000000001d04300000000203e5e587784da9378bfc86fe5318000000000000014d075e81a500000004ee00007f88ffe8dadb12000000036b161064117421662ac467a26c67750000000210c521ad4e4d2aaf2a9b6f8
  | 37 => 0xdea6b9d9197f0f2683d40000670555adf2f6404a5fa4433286a47c63f0b148594000061f8c52f084f793fca3d97de28a0000a88c0000e4c00085480228ac00000000000000000000020ba000000000000000000000b8f2e6c1ff1eda093a67076980007c863b84b9ac0c00000007b61f8400000000000000000000000000001266a260000f2200011bc9f2837a0afdc323e329140000000000041da854000249a7d4bfb30386bda1e88c2d1b369b853200002d0911a95c173c00065200008f8aa7a75e4000042104e00006e80002fa6000000000000000000a9c1b5a462274a20e7ab2b2422b2dfe67aa6c00000f466ac400000002564460000000282600026f4520000094e0000a828000000000000010432431e2c60f18b8a11ad70b03973021d0000a5a20785705a9618680009c880000000000000000000000000002b16bc74db611b000000000000000000000098005f214190e800047c800072080000001c200000000620000049d8000553000061e248c3f889000000000169301e2f013e4000017827697a0000000000000006808000000285700002250003058000305285c25e08fb22c6be82b744b313d40000000000000000000000001d418e006e600000000000000000101ea2113647e8da84a911952049d46a0002b5a92f000053000000002642b6e00000001092000066e00000000000d2bc3f800085e81a8c45039707f80042c4800000000000000000004125e0000000000000000000001b2b0b4c13a53b0968fb2298400088f250e000057b02a20e0427e1a6012a84ba1ec2644f9d4be11cae665a11e30bb92c6037e246437453623811994581800000022e2000191c1341d3b07c00000002874000021600000000001e43000000015e05e63e580009cc8e2800020b0000000050b000000000000000000000000000000008438b820001f8816e80008aa40000001c920334fe400000007e500007cac0009958f7a0002be686b2b38000000085d899288480000002b2800001c4000275c34e22a3000000000000000000a18000000089c8000c38000000000000002ea86a700000002f86000000000009706ee1144569c00600006be000000088e8000000000056c0000a3c8000000000000000000000000000000000000000000b24000000000000000001a5e00000007ff00004f980001a30000000075975e00000000d3fa31c0008b06c10991800038d1ab20000000000138a1456b3600000003cf0fe90001d9a23f80008a580000002a74000000000000007f4a2940002da6000000000011cd87eac406282eb60a2a18c3ada08800000006b200005dc400000000000000f1cab50000a7f000000000001aa00009b5800000000000001f7e86e00000000ba030b22aeb7680000db00000000000000000000000000000000c2812da21
  | 38 => 0x850000000000000000001d3c000000074e000097e9e91f290001dfa0000ecf0002000000000030a80000001367000000026880000001d4a00000005b1a38c00000000002efa3f780000290000000000000000000000000000300aa130fa3000192d15c47ce0000188b7989ff2a7a052a13400000000b6056994650c00003a1eeb47c000004f1acae000011686e956c884c000000123ea6407d40000000666000077b8000000026e40480000000000b7e0dd58f0d2bc0224000000161a7ca800079d000000019ce41bce7b0000000b5496670000fd837ca1a75b8800082c800019e1e9202ad13464e0000367854a00029f896fc73656e000000009680beda82a0b80000000000000053440ec000000155200028ec8384a0700003f8669c00000027e200000000001bf82e58ddf7ee04916f468864036dc4682102d0428d8caf327fc77d66165ed1f7c4a6195caae14c408388c57c19c4600000000001a905b6161200000002a3974aa8240000e680000ea05d50000b9500000003376d8e7bf0894695c00038580008d215cf000038f00007870000000000000000003b5000000095cc0000000000000000000000000000000000000000000002a300009ec90246188f36b620000000295e66b8000a87c0008bd800000000000000000b4ac53aad3a3923bd03400001f720000aba14383867eaa62e0000000bf528c0000000000000000000dd8000000000000004cd00001c0a72ca1c000000001380002f040000000830000042e8000000000094c0000000000063b9817b87000079794f6076000064d400000000009591447b0a02e626700001a125bd000263874c000000029de000031d000000008300000000000b90a9d200013d102183fb00000004fe2496ae411700d5c00075d82ce000145600000009b3c00036a996c2c517a6ae7022c0864000000066c6c88a4000c140000017665db000024e00000001f66000000000000000002b7200000001764b204699b5000029f300000009e20000000116c21f950c000000000028e800001647f189ac00000006012650c03069600000001f6a2cc0001704974e718b6493fd00009b4000000000022e09784000883000000000000000a7600000000002a1228f9bda000000000000009f6ce8ebbb87ac0001e7e00000003efaa460000000000000024dc00010a442a7ef8cf100000000001f1d10000007ae00004e108cc5c38000428129cb0a888eaf194a614b65ec0000000575800038e846000000009f6000054aafdc0002f1b0000000000000000000004be9a7a0001a7087e1e6b858800000000004bfa246afb948a1b6ae9068e8d17bb9c860000000000018d4501af0e8520000000093500000000000000000000000000000000f88000000011640000002e30776c0003d0800019987fea7ea046a248d
  | 39 => 0x65c80581a700025b409f2dea0000000a84400007eaf5e5bb856e0c6c728000000021610aab3a000047885660002e4500000000001f42000000000006080e200000b300000002b083e3e2dc62696700002a4d4c80cf4000000070d00002ad3002000000000000000000768000028f87303749ef96f64400000a280d40119083873c1c02b0d800059202f700000002c1a7e807f4000afe800040c17216c826489a7c1b1888ac92000037100029f099cc0000edf08400016b80001710279d3ea2301f6002504961feaea430e400082d800034f9b822e9aa18000110a2b6276a9f78b0c0000000000000000000e400013d628e800050780000000000000163500024a800027866e2000000029ef0000cd00000000062a8a200000008188000000000013f80762fc957a7d140000000eec67fae5e8b4ad4c5008f6c784c0000d5000074c9ab7604a0f04ee4dea4c62d069d79d6eb219544000105cb2403c0120c000000119b000000084aaa485e000004be13540000e3b0000d5005e400000000000000000000159600012b37fba7640cd0000a32800000028a81a28a9800012b60000000115c000691800000000001f2258400000000000840000000000004fb183922e83f8000c3b000098ee23e43880001a869cc000000034e85ce294c000000000000008e62bd11220001bd0000000000000000890aae93980000000e0e39f4000511037c83906580000588b9480000000000000196ec02220200019667cb9e503581c001558000000105845caf9420c800017d80000000000000000000021dc00014b07c8302b31da508bb28214380c5aba3e0d260000000859227c3f5800000000000cdaf7a000044238c871444a2266000041b0000000bdda73044c1e550002b140002a0412505510000c3220b2610bacaf2400030f2b4c82c692ba73a21c8184b9f834633eaf8ab379af4348c2b2000000000026ba03b00000001a981c000000000688000222400029126da0d028bc8000000000002680000f3dc84000000000011d00000000000000060580000000000000000000011e900000003e680000000efe616aaf0000000000016a07ba800000000000000aca0000a4e0000000461800000006c043a9d105f889c25b380000002dbe1ce8223000000075642bc000064a2dd271900024d400000009588000000000000004340000000000000076d800095d81b633685602538dbb121248e71ce44859cdff80000270000000093f977800000008bd0000000000032e155032a46a4aec8d34000000017497c2237d5b76ac08e447d0190c3128fa051c9f80a65390681a8be6df25bc05a0c626b184048910ad01269a8eb0f18520002be40000000ab580000001337898ab3c1e255c4a610000000253e000270818a0ea8a650000bacc00000017c400000003
  | 40 => 0x30010bf07026088c200000000000000000000000000000000964000000023180001188168c000000000041ac00033e12c700000000000000216a0de4e30000670cef07c1400046600004a016c842bd40823ec000000000032740000cf17f2ac101600000bac647890e8a4000000005c695c610a317a8e40d800004008aac09b417fb7280000bf00004261df9b482f1e000055fa878000000000001b00006f066ae75726da253c00000017460000000000000000000000000000b93e9bf471800000005e100000006f70000000295428224348e10000000000a7448b5400004923b2000000012a600000000002b445e962da99d8000000000000000005410000ba82d87000000000004e2000089e079afb49712c706d4ca48325d24c000241e6830e40000255232da2261fa0c8a5d380008ac60189fd177464a8dc56fe84ba000282b000238a93b221857b80000001a5bbb02ccd000000000000000000000000000000000002ccdef06bba3f60000000000022193fc7309681c900000ee07ac9d6458fa9e7aa984c79f407e6aa0000000013fe00008f6000000000014a46e40709366800003f8d1b51465b92008000000222000000004c889a08668746000023e8e7800000000000000aa2000000040d0c856c7ab680002b7a00000000349ca85da9f3e36a4000c2593b400000004f3911e00011c449008fc00000000000d2c0000000a9fc0000001e1800000000080000a10000000023a2653800000000000000e9ca2b2e7c11e6aa43e48ade8199f47000000082ba4a24a12e1500000007734b485f58b699e88869235c00000000000000000000000000000007674000b678000686949a0001bbc29d00000a5ae8c00000007f38000000000000000000001e9a9a64038023ad5a00023deb7b0b19add8d456ef800088280000000ab50572b0e00014543e180002121b28146c000617ad080000000a648000c2b000027a1f560000100aac2ef81e214120fd9e246438c360b76398000000062c16b200000150001d4200006d518f8d7b123c444000146e9b38522547197a2cf2f1918c3006bc8444e549951a4a19f4a8081a7b3e4e85e7e405da0cfde39a7b0000154d0ac00000000370cc18ec2d1c0e400002248000521000026c85ca4cd40004e22ee027d0e2c8660a7a80b466429325d600028f0000105e3fc52f4000009235c400094301ad7612d149a4000000000000001d9500030123a20d96a15504c5eac1046f3c000000036a0000ae92a4000047282d603282e42ed44b814e1c28000208c1932cbc00020f827a40000000000000141400000000002e5f0e509a7000030a000000073f000000000000000000000000000008d41a7800065f30f99ec0764b10800000000000002dd00c2ecb00000f7d00001a200010f836401b34d366830a221d60000
  | 41 => 0x6cff36d00006c280b0832ad94a2080004ea050006003d37aba370b672c8249180001d60d920002c68000000000000008418fdc000212464c906d0000000714dd464fc0000000000000009de3c38dd3327a8fc980ad80887a654be780000001c3600000000002b866590000857aad81a388b80000000bcb0000000000000000000000000000013a00016f8373a87c5a0800049f81b48df2d6e10680000000d847e60000000000000001f80001d5d9a31ca000019db02124c20001b26c0c000000022a78ca8000c1902726402ca808010223e98000357aa06b9c11b100000000002c8a7e3b03443d0eba3d1040839d2a312e68110401a66a04197b84025749af020d801f916900030ca000264c51b1b8abea00000000000b86d5160000000098000000029f2000000000007a05279c1287b00000002c2400000000000000000000023a800000013ab0000000000093229e0d28000000000000005ec1910000131e17b1b866fc042484f1f6b0002db43099435af940006dd1eee7e703a4490e30000000004ce57a40001e7f9ff8000ac98166a7d80120c261d194791ed008edd25451c590a19751b8e649a01c90ca73597a900000000002aec5eb00007914ab381c800088b00001ef118464d80009340ac8adf80008c698281872a0b754562c00016588f2855c00021960002252000031886904dd6b493d08ab0a7280289ba14d501700005fe290a4a6000000090bacfc0948000000000000000009d28000adb0000296800000000000000d950002a2a00026ec000000022da8b29a4800000000000000000000000000000000bd5c7d00000006d900007124000498800000000006431f280000000000000000000cf00030d6130d21400011fc00000003d400006b72782a76966077f800092e2b602362f8036e000000000000000000000000000015d4000000074d1dad69e17242bcad34935a6b6899258c4940dd058aa98e3e7d7763186cfa81fa3378340000b86a15a0002758000000099d6d2c4d6142400014e092f80008940000845227860c0000000019e7c22424127800000000000000c03663800083baf5000000000000d229f72a1c053c0000000000c319b592af4000b7a0dad0a329db0002e38b4e0000000000000000000000af60000000798823200003ce000000000020ec000000000000000000f75305cbb017e8000000000037d48a00db956800006e00000948000000090f003d46780000000000000000051e400035a80006a79a2000000000001894c1000000002cb43fd6b9a000000092d000000015363e800004de82422ff255698b1afc35b227e8cb27660aa1772bed94d2a8b2d852ac157416199f60788cb20002e4e369800058da9fd00d067ea73c4a10000d9d3aa90269ae29203c2063a36c2a9800009bd5b71ab601e1e8eba88000
  | 42 => 0xe0000a1d2df504f1be1ba2000115025c81bc8a19e8c00000000000000000000036ac0000001cae000000000000000001f9e0000000ba79b5600000000000000000000066c29d400028b6693800000000008ea8aee000000000000000000000000000000001e13d5c902a0a1fea0000cf6000040300000000000000712d83100000003ca0e69601474400006ea000082800000000000000aa28000000000000000005d9e0a447f8baa0000000663000000000000000000000239c2450000000000000000000000c8b00000006f7aaee74f23f500013a69e4107000028a40000000048d0aebfa4000630000068d4000000305e00019b534840003ab800064c11403ce000000000000002a6e2980dfc50400006a316da00017f68a7c000aa88ee327800000000000668800057f27e100018900000c7e4d421d0402e9c44790f5ba0f2a84ae39a610000000a22a79b00000000000000aaa8000000254224740003bd80000b04f2e32d00009cd23360000a70000000000000000a997125c6a99800015f40378000bf1981800016fe7dd40001878000000301014ac00000000002e7c00000000002962e820000000bb3a80c00024aa9d5a9780000d0425ba7dd1e295471948b32a040000b44c0000000a6d00026819bc000078eda7c34c8c8f0000ae5000000094e5cb40001caabbb0ba400000003e140000000008807899e0000000aef0000a8e18c600029d1798483e0000000000160a00002288da0000000169200000025d78000bc680360530843b172e20047980fb73000000003b25da0e3ebf10dc84ea8e2b32b80000001bee000167c0000000b9e00002354000a5b800022fdfff00010b40000000575400000011c20c900002c5e00e0002e8e414a7940002e349550c7993f215094b000000000000001f18000000099f0000000000000000000002c4c2978ee80000c5700014fc1512bbe000000035cdee48e08000000155a412e76800025cd088905f39bc5300000ae6000000072d9e900001e0b000000000000009910000000130000027a8961c0bc363ed4a2ca000000000000000000120263db8600003808e5c00000007059c2c15f40000000000000000000026d200000000000ca460b9728000000003580000000c840e5a85100000000001c7000011ad00015580000d990000000000000000000000000000405000000016c142767cc32fcfac3f0b028000000000000000000000000000000000005ed9af000023440000000000125400000000000765c0b400000010e8000000069f80000000d890000b47000000000000000000000844b08c0002a7d000050a341c000b7e8000000000000000000002c20a47083c000144e000162fabd40004c1000012b000081a12ae000047794600000002f1c00000da000000066980000d2c84a00018da33d
  | 43 => 0x2c160002b9e5e30000000000000003e23da800000000000000000ab7800000000006998d5d0002a3a28f11c58921f9b89c03b9be327c000023a0108000068c1e5a33eed0e0000e6dbf8a48345200007c3000000000002580000000000000022e988200000000f6e000000000000000000e3c0f4800033780000000000785d5f0915000078dafb84c68000000029b18419eca83c00000026be0002f520000000000071047cd7f4c290b10baf0000000000027d4000000000000000000001cf288c886d00000000002fc04df98605762cda0002d3e0f0805aa7b5b48000076c8eb0000000000077d90560000000000038c8762e4c2f98000000306800000000002e28a672583a76548c91f2ec8bff0b2b0000000000000000025102b1e02a00004f6000000072180007bd8be28a704cfa9a0e702bb1088941911641900000d9457300000009570ca051ca1d29c4905b0001f3800016726dea15da388000c0d8dbd24c1e1cae104cb000289a630987e000000000000000000d4d00000000000000b31ac7e8b09bc82be8fcca67a5ceb1b8bce5e794780002b56000218486f0000029d9dc00000000000000a8a00000000d86b028b5c00019d0000000000011320001cd81132ada00011fa3c280004b515d30000000c1e8f161b50e660000000000000000023bd000000000007ae000000000000000000000000000099c80000001f6a7ff8514813966400022c0245cdccb31ef347b2a598a788000000194d00029e60000068135e7500000efa104ac7c000027f000102cc0b2678bcc0000000000000000000000b90000000019c00000001266000000068a80000000000000047e0f5595a0e66a660000000558800000000005882c0803c0000000000000000001e98000b4480006858000000181000022bc0000000000000090680000001292000039f00000000001ff39c680000000000000159084c800051280000001592000306c3dc0ffd000000010517406e58000000188a7eb400000030047b7eed69690000921acd869080006220b7a55e4000b2712908ed4a670680bee9849be2048939249a00003c1a06cbec823453530c00a026dd33bcf9ea4c1a559ee97ee5ef971cb7922af496af3cb26dbc49938e4576180003e240005638000000000018f0a4700000006128a65a7d040a00025a67748000999800000007a21e70000b758eee820e67a0d640000002df4ab8a8d2b69136b5c080000002b3a0000000bc40000bc540008d95432926000000018baae29de275dedee419ad6455f0786bda2bf8bdf294691384c499140004760316000077e6669a320000000000131f9080b620002a72000000000025b660544560001a7536e980c00030ba44a5a4576391364649baa47806f67ad92b4000000000006b800000000000ff4c2f0a8897323fc1760fa
  | 44 => 0x24000000033c80000000000175000000003a60002c4fb5f1f246e9000040fc0003cf9726bb31fca8bc137ca7900003e1c8eb35ca10900000003e4605a00000007a7400000029e8571a6d59e54f529a019d8020a13e00026d4b428000000006e2e1800000026edaa49e8300000000928000000000052b00000899848ad200009aa8ec60001f164002b320000000000000065c916800000000000000000158048c1988000000000000004f680004f32db200000000002dbc00000000000bd08bb800000002e078595b14da0d4a9790a266c2594c976275a0c19e5c59b96441c91b81000080476700004732c6660e400000014925d5918e000134c0001ac2000000041364ba8110e894450000b3700006bf80000000000000000000024f800000006f64a694edad03a938000246d18200000007a12cee00011940000e90000000063de500bafaec60a460d244f2a86b7c0d200001d028938000000090400000000001834b6d8d6100000003c125f25f400002c780009c500002ecc000820000000000007b480003b00e7609dcc0c0dcc0001df000000020e70000dd753c1bce0002f18022c6d200024c6000000000000000002e9a0002cc418e000000000001e0230237d1bc330600007428000000000076bae1f00025333725c3e15d1e3c0000000566b08670891c80000f49000170f000000000026847fd1a6c00023ba0000000691c4860000000000077a0002ccf00000000001f5a00000000002e127dc07b261516b6000000032980000bb00000002af60002b02994800000e95387f8000059c4000c1e160c2b90acb946a92a7f6000081b9f6400008a69101c4c21f43263544c4c0001dc27a7c0005538b88a56800038d80000000000000045000013a2000000068100009eb87b400003bc53c80004408726326e1cb3d0c000000000000013767e00000be680006d610d4393180700003aa0002dc20000000b34c0001b10c5c3d34000533978a00002d800000007902f12a8899168c4b10ea092b34897135737a0000000000072e000024244faa8e710a6b814366f9a26e02f838200000000001ac470ba5211d6800000000000000000000000081d2ad700000000000000000000077b0000000167d17747520002696392000080db048000000000023c000009162259e3500003760000000000263ca4980004670000a5b228a1d7e8610241614000290c00000b8000000083dcf476bc400000026945420d790001c5755f81ea000102014443a00001d583052ace8500a830002fe868d043e05e8000b1a8000000120038300008010000000175a0000de00002e1600009fa4bc1e1231604a678a00006cf1960029800074680007acd9412ef2d58000222b6c0963f22d00000002b0a2440c9cba225b000019ee39e00008ad0e4714cc00000018a6000000057
  | 45 => 0xb8a5f800026fa7888000709000000000007688000015800000000000000c8d879000000020e200007966b59f25000107e4102c623b3465e4378a22a5230f860983ba242df50aaa027400fc0000000000277000082780001b08000000267e0002182ae9800000000000000000777a1bb2264000c3a970caaf80007905ac5000000000027ce35f0e6b9018000000017b754af5a00000009c780000001d3600000000000000000098e23b000013e00007b1800000015f681f520a34dace62ee0f8000023c60748c886508da03d68c77000000000000004b59e98b5f80000000000000000000000004b780002f7142a5f50000a8cc0000000d6d0002aa013d1db4370c000694c94000000009e580003a99c7915b0a55bba2e5345a88d0b5b121c80e80000000000000000000000003a80f7800000000000000236969003b6bea667a5280000bb697a2dc000016400000000000000010f00008802e6016a0a6c2038000000000000024b60000000000056938c26ac96e969f598a928aad970a7521e76b39263023e8000639017200000004e080004d5a1e08dd91ce00003da00000001779ad485b1813b4a1b8f2d8000009b1d0b9e718bc000000060500000002c4a30e8a4f000000017815e83a697cab340000ad8800048c8de200015543b519687608000140af6e5fa2bec0000915542854f76600000002f9000000000000c6e0000000000000099680000000000b28000012c60ea2fc00000000000000105d00000005678c9266dc0003d9800000006208cc0000000000000000000f710daa88400000029c00000d68000000000028d82668dca855c0000000bda0000000000000000000000000000000043900024328b7800012824de00020be00000000001b4d67342064a280006b7a00c6138c1a09f8000479c00031100000001fc40000000000000000000000000000c0b80000002f9f5b014a09eb00000000afe34f08620f500c28b106ae85c80001f1800036080000000000ab0ac1e08a816ea6000004d18000c140b65165ae3293930a2968800076c9cc911f15280015061000000063d00001e0800000011da60280000000000081c0000000000b89000000022c8619000040bc04e0000000ac00998000000000000006f186d800000000000aaa000197600000004b880000001c77000000079f1bcc00000000000b0200000009c5aa961cf05e233b400000017880002b660001b4b00000007ece91a83c80004058000316ac34366140c6e7aafa00000000000ff3bef137d0000dd40002a0c71b208402200007e6800091800008d5ac2e6288bc400000000000000005c000000000000004ae37b80009428d1414a0000000000081c192e74917ea000000059d208eacc1e3e4a3000094b80000001e680d2400000000002488362bf40000577c00086f8a
  | 46 => 0x1aa2408c0000000000000000037eae560000000000000000000000d0c1a300000000000000bf600008cd2a5c00000007f5a1a83421a80a2500443141ab9b83857caf580000000000000056f6b92a973601e4e0000000c0a4ab80000d5a0001fa800017fa000000000005ae948800000000000000000000000000000000000d1000008880002f164bf000000024f2000065a0001e590119c6200000000000bde1c2ae721dbc00000000600000000635800011b80000000000b23a8cc00001da000000067c00000000d9f9fe80000001b340001b0b8bd4de698e8000000078421100002da23fa271000000ca1c0000079a000000000000000001190a8f80000002260000309000e4000000000074328667a848f8432000085a1e6a19d00000002024579800061b8000000000064fa6f23a4800098680000001ada000000000010363ae0f5900022ce0000aa604309760900000678000000000008f200000002d8c0000000000119a3320f2c10716800000000000071ec038000000000000000000002632000020a000000038fcd469d840009b10000000000079a400013300000000000000000049b800000000000001e3a000000000000000362d48727a6897cc070600000000002eb00001c9c0000000814086a771235800000000000000ac48000bd80517a86aa5400000003be00000001aaa0000000444a69e0000000000000049c800000000000000000000168e0000000373c000703800000000000000000000285b0001782000000000002123dd111c00000000001fa0000000052c959996500000000000421000063cd6d9b6c24a0357d0c7b6b1c4e00000007150000a6d03e6000000000000001eae9b85bc9b31000000000000009fe02de5f6000029980000000000009800063e4000000000000000000000000000000000027740000304000024410c6142000000000028164f29cbe97a96fa000087c7c51fd50d30f7e1c480000002a787b599d3000101f0001c48688959c08e8a64000000000000006c216d666a80000000000000062e00000000000000b8a800043e80000001705000000066f106a1d409620000000621800000000003a286fa00000008f600007b9800000028b4000000000000000002af45c4617c00000fcc3a0000c220d8ab6e8150a6093c801401f6000000000000002b25e8831640000000fa80002233b9d28a775544c236e40006cb0cfea1b86044a9000000008dc0000000b8b400000000001e30000000244204f00000000000000000000016de0002d0d44b88108f42d102ac5520000001c0000000000000000000000e700005e100007781dd000016d0000000048ac0004ee80001f311f80000d2900001480002289786800081780000001fec64e9b3000000000002aca0000f56731c0000001e4288440006
  | 47 => 0x75461debb8000149041141962742a5814680000000b6c5d4b11000025b235f4e6774388ca6851de60000d244b427049a614e2000000000000000000000000000000000007418000ae16c6c38062d87d4800059e816c00000006271d046a2842f87da58a2468000a172a0500000000001fb2b0600000000000000000000000000001cd000026867918cf09f669bc8c3035800024780450000142030e1160000973e7443818a68156e879000158c000000055700004fc93020fceab40000000afa18d8484130a06b8cd2ab2c94607fd56e69016ca0a7102a683af560d3ae17ad02146460167934784f2bd0898a68919124580000a78f03e0000c700000000000256896d58e079c00008c2891200000008d4a41800000000f440006208c944e695325cd9c56368e7003548000000266e7629c0a015103800000000000000606800000011eb44122ad5500dc181362920001d540631fba4ae267d519000072c039d5a680000000000a0a9d44000218e02e8ca700012f6ac413b000006623880000000000000a963a07786368c19b2e3f20000a96800093d0000a93000000005760000000158ecd444223ae3181758000232e53780008f821a00000426000115ab8d40000000000000254c9778000000000054f1e0800021a2000014400000000000000a598dc600000000000000000144c6b9800000025be0000a8a446aa7b0de084e000046a5a92ea60002d0453e040604d29be000116e82621580000c9ab0c8000000000084b80000000caa76a00009a70000000252aa3b8d2a17a23c41434000000000000000000000000000000000000000000000bb108342131ccf0002e9200000000000e64000179c00000000002582bdfa55a0000e8023e4000000000078aa546315400000029d0b37c000000179403302c00001a502510000000133d00000007a800002a480007c0800075ac82e8de8000b088c6694530ee000060c7fd848e4ef8d16367000071680000e49ede5d201d47580000a0e800077c8c8e2550000000000000000000002b5c000000000000ee0bd000035bee969a9c00000000003fe171e0cec00070992c2377400c08d800049e80000cb0a8235519846002c5a7c3a15c7929ae101b41e400000009b6c00000000005b9000000000000000000000000018600002d695dc74b800000000002e0000000000000000000000144f0002bd22ea026a00019dabc801a900000000ebc0000000be09de9aea00010100002844000000050f05e700000006e82834b6892ca6dc800000021ca000103a318e9f171b800042730f400000005bf400038888c4bc2800076b17c000000000000000000051000015a5b9a235446e893e8fd0d4ca41137b0000000a0680000320d3d89795fa0000000000000000000007bcaf743558000000040e3ddcff20000
  | 48 => 0xc7050e4514a44e800000024f6000011c0000cf900000005c0c0002840000000000040cc0000002e3e215a28828500f242f859e53a04d500000000002a1478d00000000000000000000002be00018764b3a2b800022bf00005dc97d93c160b00000001f930002f9c0ce310851d0000000023ca65a84a00026f617ca1c4b502ed097f98e6000268700008544e14f9c70e80000000d7e0d4000012a0498719000034d65485db473800000000001256000000000000000000000000000000001dd000000000030208298cbb0001d7400006db10140007da400000000000000000000000022b80000f919a40001f23abfa852acfa1e61d370d81dc800000000000000000bd8800000000002268b640001021a78000000000004a51fa628c00004830000000000076360f60000b048a81b3838a800000000003f5c000000000048f40002b68000000000000015d700000009e4895e00028180000ece0000000000245600000004e00b3a3fa8000c20a76e3b89ed413a84884b12c80441a17ec1983fe6c411debab92c80000000992ce56000000000002540000000aeb00003e896e60001b703312eba0bb80000000000000283639c829a4e916ea00022a8000000000000009b2ee3a22700000000b1a2f58ccea820ad23fb00003638dd20cc0120189800000000000000000000000014f64769e80000a418000000278c368552415e8000682a896c1884d90001b4cb3e00000b9646c83e453129b80000d9d8a88ed9c10000265e95d40000000b360962cc00eb000000000008311369c35000000000000001d4c0002b1a0000000a6a0000b762fe60001f9646bd5c812098f520feff4000000000000003820000000000000005729321c044030000b2e800057780005bd1cc80e2800000000000002a03000000051e800000000000000000000224200000006749ebc00000002d4800019580009f580000000000000000012ac86800000003d2c81873000000000000690c0000000000000000058e0000b658ad40002fac20f61b01031c3800014bc0000000000000047761b4675800000000006ae17076d2800000000000be00001bf000015600000000000000000000020cc00005b80000e8c0000ab700000000000e2d14f800000000000001d6d7e0a0c800000002f500002e880008841f7b0002bba47d8000c239d1e154000000000000002a8c00000000001c5f44ab09a000307c286a5f04eb84e6bd70f450000000000000021ac0000000b6758dc00000020f14818aaf00024920e60000000000000002fa000000095f894c01901240001856000000000000003c1400000000000001c0639489249d7c00002c800000000000000bc731217703022d180000cd400000003645992000000000000000000000000156058080980000c1e00020902859d928a468ba
  | 49 => 0x2f3b0001fe800010a6c298c05000000000010d818280004b80abe00000000000000000304c15c0000bba800000000000000000a8bad7ab58000080480000000000787800000020a83029d43000308a00000000001b526b02f2638553705958d8346c967eb2c800000000000000000753aa8e989a8589ac0e1f0001908c108c400001eb08121ad04d70692000000096bb04a06aacc800000002b5800009c53dc0000ac000000000000000000045f00028382a6ddfcbc180000002a9e0001f2cac32ed473980ad2ba063b000250400000003d6147f39d41ce9ba00005bc2a7600028b88d0801669740000000000aa756fc74f6a2d1dbaad098780004e7000000006ce0000000000000000000007f6800000000005c8b01ca6aa2169459bc0798ea4500000006ec800084fd3ee00003f23c091ac031ab52b5da7c2000000000000006a684870e3ae2bb818df34392850280996200000007a0a11c4ce8000a308000012c4dc000000003994aa52d9779671133200000000000000246444663b000011d83d00001fd01346f844690000772911016302ac64d181b8c24000000000000000000000a0056500000000000b4c000086a80004d110d20000000283000000000008c3800000000000002c96691000079e0000000043b000000063c80000000000000000084b279354b800029fa10813c0a4d00000008d816d4977000000000001ac000000022aa0002f3e9e780000000cee00000002d0ae4600021fc36ca5f448ea78d00004f54fa2bd093c0cac000000000000000000000b8d80000000ed24f898f600012e475f0356a1a400000005b200000000002f178d7969d0c4dec2610163c4aa0bb4000027959e1b1c00017ccb6117381bcad157dba0600a4052c00019d48a1000000027af000000004b80002f900001392a4f00002c80000c429e0efca02000000000ffa71f210b1f429c286181865cd0f306db83722fe2cef24e9c74314cc957a5a2821e7980e7b81f628dfaee29828000431a6fc2db955e78f70320000f489ee2bda6ab09ce2472cac999231e078e59100018bb2dc8000177c982684000048d02ae000000023c00003f6acf20000b9da07800083ec000401000000011f00002cc30001b5b6089a2622c04a9bf5a72ea4c800015b462c00000000002f728551e15a1b000013f0d77a530000000000060700000000000000000031cc0000000000000000039fa5608d18000624800086c95c72b6c0004d7a2a405d8000731aac8053800000014b856b413244926a27c4989600028c86de0f34000065000000001611d8063e8000540a8de48f0000320c00000000009470000655a2fe3d3000061a8000b5097a22414000000000000000000000000000000000019b200005ac0000000000130e00005f55368000000000000023ce0000fdb113
  | 50 => 0x135a00000000a080000120c6713297640001a52000274e00000000000d7a035000000000000000470000028e0000000000204000000000001986000000038900000002c64000019833de70200029d71e3945966297446b6c0000002fee54c1252000000000000000000da20dc000047580007fc00003978000000000000020260000000855400000000000000000000000000007b862b82edb4f0000399400083380073e84000c388864947e78568f30ae53e8000333668237da5b70001f2d000000094d80009e60000988000040c4000000265800000007b215845e8c0000000eb4129c94a00000000001b9a319187322300007b70000b14235a8a6000000030c8bebab4c328a28e90721380001465143c000323000094dc000ab7000095bc000acb92362e5000000027b60000f100000000000000000015c322080009338000000000000000006ea083b3e087c400019baa558000000025c7171326b8000000b10ec4000000000000000000000000003e00000004dc900300023d4a4b800000000000000eeac32ec7ac2a80000001d53000000056900006dd85cc000190a3b900007ddd88c000000000011aa9729c88652a27a695a56a016000000000000002c060000000486107c0000000000000028c80000002d8a0000000acb000000020cb000000050b8a380001a12000160817b80000000b7c000000000000000001bae0000a54a2ac0001e6266c16a80004d3800000026cac09800013000000001b3a000000000000002421c5db8cd22c1d228f4244c000491000000000000000000656126a00000004812a0732621cf7c9a70cb121468c4180000001aa600000000000000bd60dc40000ebe0002335773aa1310b90946c5a458313907688a8cca000000000000000439f78a0a5fc078024fa2b666bc0279138000000000000000000000000068b0001f4652380008d340000000328389a47e00000003438c470000000483a8540000000aea8e4625a88aa14baf38a080b0a153800073b800000000001204c7a0000dbc00000000002d46457800071e94621c8b0d232a104200013fa9a7503e619800049200000000000000000067c8000000000087a99b60000000000096c0002cb74888000a8acbbac0ea1de00000000001b5cb2314d82d24fce655070e1daabca01c0432b46800074f9bba000000000000009aca56e000165e0001ccb00000000000000000000000002980000fc688e2b8c0000000000000058c80000001d6603e04ec486a2d592500000000000000254a0002754a77ef14000147e000000056d1c08000000056b07ec2b8aa4263401c6c398000a96d6aa0002cb600000000000d44072a16b000097855c8a9a69682e3b4591d2b8fc51d0000000000000076cdd009e00cea68a1bb56ff0000a83400
  | 51 => 0x45000000000000007c65cba5d82b5000022540002e4800022ba00031020001a8800025d2000000000000000002e05a5c30dc48e26d18bb280011684b629ac3f5672a0080002fc212700000ec5b5e57b0f4eae900000002de04f36fc8000000000018190001f1b9839dc0a35800000007e4a0b000000a0000a1ea0a00000886000000000000000aada4a5d42fe733820450000000bfe23a65a21126b8080000000000b9500000002ca695e800041e0ce471ec0000001f1743d80009f4800044ac0000000000000000000026a40000000000000048480004e82bfe3b780009c99d8f5c019b800000fa000000084880000001aaf8d000000002ce02df947000015be0002ff60000000000000006480000000000000000085800006fa0e719f6800067e8dafb3c291e2bf0956adc2378000000010a2a9000000000001af800019c500000000000000854de727c700000001626b2a9d970000c1024d21c1a4380009048000568c0006ecc00000000000000a9600000000001ef43ca8b3e3c00000235800005595bc0000000755c00000000000000000000000000000000000000619400025240000000b980000000000130fb0980000f94b76000236c5618000601800000012a08efa2fcbf6a95884d81c3b34939e4ab0000077000000005a6b2e2c583b72f887d708457199a7f00017a700000000000dcd273400009180000000c20bbd09e210255d1000135d000000000000000000000000000000015952018000000000000000001dd0000a7ec000b072f7800000007f98000a8f01ee780846f3da0814ba2800000014b46292e2e7ad25e359402a033b233c0000062a8c187c00003e075a1f2700025e60000000000000000016650000000000154a0000000bcd800086d91b630880000000000000000000000000002c7610583ee0000d707260f1a0050000680000070600000001c960002f3a0000000000000074700000001fe51464000bb6a16e00000000000000072400017014d6000145c00013b100003a20002b6e90f8000be598c870c0000000117a4fb000059488660000000000000074a226c7650000000000000028da39a00001348000000133e00000004150000806dace8d8800055fc00000013140001d4082d00000001461a2200000000000000303f0002d000000000b1e0000bdb18e8c1c8d88000000090b000000000003e540007ed222d0810000000000000000007d000005222b200000000a6300000000a042d7a471000293e00000000000d75a2c0fc41fe000063e000000000008869fa20000000000000000000004ba800000009ca00001c8b0faa1050eae21135a5aa49c0000b3a4000796c34d9f8301a000000080c1c6747a80001bd1cc22c2000071486d761a0000451830185d000060798be07c95a02cb00000000000000000000
  | 52 => 0xafdacbf91e86d000000008c1000044821ae0a040001f4800069210ad229245000000aa3cc451c00023a473800008440f620000000191940e000000000015973f800009a2000000011b0178c000000040baf700000000000104294465e19c2bae000000000000000000000136f6f8c00000000000000d6600000000001340b81259e518165454b000000000000000f175ac28c427b8ace0002fbe8d381d64549fde5ca89fca1e0d4e66d209b693efa404feb1e24602109332e768d7cd1900023a80000000387000000000000000e9e5cd40006f580005860000b38afdeb37694eb9aa60400000009a980ae6132890000000000000006e72d243cd6643a896e1d9b20a2bba00000c090000769290876faae8490adae1ac88906f48b6348a63d70001663087800000000003a88000ba100000002f4e00027c6485a7ea00000001d080001ae800051f087a3430cb9757dcb28e380006e6000000000008932afc6170fe88c74000000159874600002aa1df0b69c0000000000afd000000000000000000159400040c80000000a150519917a3400009a6932481e8422468000000000005740000000000000000000002b98000000097b88c8000000020da1660001a6a1c61a740001a6750886899740000115000000010fe00000000000b61000278a268c31276418b45e380003b4000071a8000b139df77d061f40fe92dc1078000c3680000001f7652500006ec1eec94d272050e00f12f2834171a151277cc0007818eb02fb00000002aac7f08000be619c6b0e8e623940000175c0009e3961e000000027c00000002ccc000101cb788000390a322000162400000006eb000023a288e000229a94b5cd21e908baa3fb104ae20000000100a2c880000000000bd181a4000248a000000000000006b74000000041965000005cca83263f9dfbb6822048a3c000467d6754020000a8a602887b80001fac000492a3862c01b5a14e50d6bbf800000007040001e2e0000000000000000000000000000afc800000022583c90d339e6800058c021c873800096a000033a40006f900009170000000000000020e67e3276247b97f872f17bc944800000028989fbaee69198ecc00000000000000a80000000009d68d400000f20000b355f8a68d803c21408f161d4000539800000000000001bb400000000001efa6c66c5400012d204a253cb9ea6475c6292421187f69622be20b345408fe158800000000000000a5911960ed00002752e1900000000f0568c000000000000000000a63000046824d9f81124000000000000000000767800062c800009be092000000000027919e99a5900012ee0000000a7fc158000074a00002f6000000003bc2a20002ad22b9c00000000000000000000072a00000003159e6500013f4b9ba4800000dc200000009d1a25a00003
  | 53 => 0x56aadaadaa00021bd2f18c906311264149a96abb78000c3c05577aea06960da7e6000070800001ba52a0000000000024a94405698dc0000000000000000002332000122693a0000225c0007298000000000000000000002c00000000069600000000000000000088b80005b114631fb984216d14c2c06192c3e3912c0001db5b3158f17350cdc90023d6c2605d194acd009b41d4522f0d7814aa83e0001afa0000cc2c09d500b5e10bd1225903b5d03f4a5880008d286cc24b85a99600b2a3ec1f1ab77affa19c81367760d3003d29a0992830c87c23940e6c2877b316ac79580006ba122a2fda194453800015a0d4200024c02798a0e0000000000000000030f63d718b10000f7216800000001c721574eb25d88b9e3b0800000000000001d3a6fa8fd900000000002349ab9909680500000000f8b13cc000000081c74fc3bf00005a100000007c8a88c1fca636a8098ac2761e5342f15464879a688c9b0b21a1aa3291c800026c000031501b2000053600000000000000000095218d00005b486245c7dddac0ec0000000000931000050105480000fd4000000071600006f0800093680001b713df000231c3449990b82202e000000065d0000be480000001c2a12917ae57387aa9fc1e4800000000001e14a9450685029cf60002ac700ec2d231caf2e867a5270000f730001cf400023720c5400069ca4162308000a8595aa95c00007bfaf0c3258000835000041440000f780002e38000ab0d1780b285f83af0000000000000011c00001a73a8deb96aae8dcb9df00000000000c33ac1433180000002c0457800000000000000000000001ec7d52544a5d000000000009fd82b4058934870687761aa80001688f1800000000000c2e1170000000000098600005a615a84d81874000000006091d400007e000014ba00012b089d8000ba718500000f9063f12ba5709f486b3284839e9ccc9b312bea28c1953520a0379818d216410695438adc5f39c780000c3e000090a5b8000000000000001d934c228ea000107260bea5698020bc0000000161dcca78cac12000117e6378000a994000000285a386925cb89a7aab55ac463768a013b6a56605c0f6f2b082b8284aa6c1509fe44770018ab31319aab68aa4c5858a52628060fb04d8c392408934836869826d828d837e0d990d0000000039ba2e43c6400075a9f3a000000078fc00063a80000d203e30000c5b0001a1c0000000a6e80000002c9e00000000cf5e9c00000001144dec6e517f0755a49c295800002b2b9498d0ff06790000961a8124ac8f329caa9ea4f60d18000147641e929ec40201a000000015846e4840182a00009ea00023e83e90e4e59b263e3d280007771be0870c0002de22a6a5d80009be208a000032e21c2e3d00011ec511a97e98a247400000005160000983d065bf300000
  | 54 => 0x57f80000001cac0002d62000000063bd62264189c05154ae0b541e38ba6000074e1dc82d60a840bbea0e00001b80001e018f321c25258d81014800000025c0abe08410001c3c88a680a00000008ef000000026404eb000024180005ef4acdb5a00740000000000000000000002b11cfa0000000000133c01700000a78000748020828795b60000ad709a1fb600018aa00000000001345000000000002a70000000000000000022fa7ec25ac32c0000000000000000001cba2ea00000258c800001f0a3660000000000000030380008818000b43000040386a00000000000000000007c028163eab6600ce133a29dc3f17aa0002b5e6e4930645f27f7b0e22ca97180009cf0364000303c0000000000147b04f8b2e000000075c18dc2911bd40cf8ea400000006a5000000000000000000179000000024280000000000000000010909bb80009498a5c000015f00000009e12eacb770000000296023d05fc00022f800000000000000a9030b891b8000bda955600029ee8628d11119a6223d91d7b0a4945b5098bd8ab02910bd2900100006980000990000054c00017b292c09b68129f4417dc0006ad40000000000b8dc00055c00000001c850d0991300014ae5fb00004b6057e73b400000015660000000028000058c400000000001bc172e05780000000000b4e8000795302a2721a1e5390a994d2c00000000004cb80000000d6400008a2a2b827a5dba452b7c8e0a20210ee00016ec00000002dad6b40003056000000000027ec04940000002b1800003320134000b751aca2058000000000000000000001dba000268a3561bc903001fc957800011e0cbc319504871000001cdce9677244dbba1800000000007da2596645053f3980000a8d81db0000e3d000000000024ee23800001d58000000000066b05205c24000000000000000005d4ef703ef0c0400000000000c3c0001328000000075c80000000000000249083f000000029340000d0a00022b68538000528a0e91550ab2000000028d280800015ea0001374000205838411a200009a400004180000000646d89e533000002880006d0000000000004c6c0003a100000001a64b90c0000000000772c00002d0f790000000611000000000000000000978800038b800076a80000002094a428000568400000000001710a39000000000000002a800006fb06140000c060000000000000000000000000000000000000021440000000000242a423a3f2207845228b309e479891e592a29eb669fac9540000c3780005cdc00009e19960000000c200fba7f300000000000000000000000c4000000000000400002ae408e0000000024c42c21c6c1a80000000000000000026a8720000000047a08246488000a18de6631b00000000000000213a745800000029221735ffa24f0b56000006f0529
  | 55 => 0xb5000009a80e102016ef4b8a4c422d60000000000038d68b07b0000000000000006d1c00000019d100000000000000000000000004c80001634872400000000003c80000000000064740005f680000f180008f0aeaa000000000012246ad00001188b3f00000000002e940000000b88800082b0000000035e0002a9c00000003c30b66455a4820000000000000028a800000001852a9000095e06122cc40004182cf6a2990748b50000070916200000000000000000000039693dd00007b60001e810002d6600000005734000000118c33f223600000005ba42da82880000000efc9dc0000be3a93661bc82086400005ce4d97193c3005ae80009f2000073a000e00000000002abc0e54f5ebbda05ca6280007a79889717abd86731f1f0000000a61800022f80000001b60209a39600b800000000000001f0400016680000cd800000007cdaa7c5f49bd800000000000276000307e00030700000000256af443885a86418af288072cca00000000d70b262a52d44000273e00028723ff0b461e52cd6000215600000009210000a272a3400000004ec800000000000001ac90001c7e00002506d1aa940594c529fc973aa71a3bb00004719c4075e9009e6e00000006b60ce60001b84000000034ec9c6000000000000000000c680003044626000000000008d31f4e0000000000000000000000000000406800000026e03962cea1ea0ddc77e10ec40d5e5805d145e0000000000000086494480000000a1f9e0c7cd0000bc097313302d3600000000001f1003d92e835d8f40a6c0000000000000013a1a070000000186b2ae400000011ae00019a93951c9a065000027927e4bf92e501e4208688d000000000000002be0000000000000001b18000386000017580000001639795c0004aa800089000003d52e4100016cc000000000029005f985be0ed811a5a2868215787e20000000000162780b00009179cce0002edc26980003ab256d8b9800000021160c7831ab73961c00000005de80000000000b9100006c60000000127c838c00008f530c76e1ea80000ce200008a8000059f00000000000000bd00000000000000000000000000000000063895cb00030cc0000a621df400040a244c00020060002a2092900005cf139f23c80000000000b578562c1500000000000000257b000000000000000001d2ab3d4000aed8000bee84307f20000b2200000001c1c358c9ae96265610000000bd31a38ad903032f08000b51409c128800000000000a104bc80888d21b65d5e000000000029a2231800057c800088c06488d90000703050c1f7000010e0000aa206000fc00000000000000000000000000000a2036a0a6a6e983d830e217800007a59ca21f200017c800007f413baf5d00000002bc30b04db0000a6900006d980007af80003c514c8c3e8000
  | 56 => 0x104ab9280000000000247c00098a800068618f00002674000160e00000000ac0000a6c80008ed048c8359676000269118e40000000000000000077d0f330001e4c8850000bfc00000001593ae082f2151a1c79c3a414b82834a2d28000514aa9b5c818028ca04939f8c0000000000000080c00008e57718d948190000963aef00d128dc00000001128000a988000000000099a119953a80000000000a89c000000088a15a80000000000a75800000007ca0000000000164b000000000000000f340000ba1e9400000000003000221000000003140ec00000000000bbf0f9d00013271a70000391105a00000003a1a0b80001696958c000333d5cc0000000000000058a2a6a311871a4d269c800000002a00000000000009780007f7180858b9ee818c800002582fd0000f7b21d80008daa4d80000000000000000000009ea40001980e128ff9aae0002a609328cbd2d3c00092c8000000224a00000000000000000097a0000000000000000000000001c7600029a6000199d0001d2200000009b6538e3e5256c49e1acb9f9d0c1668077f49d10b6000268b8f90000000260c50a15e4867257c9b7040208c0e985068000000254e3fac0006481c8e4d6db0090da864000000000017141ddc00000001e0aebb0b6a29400000015ba84809a50002bfc000062a27c80000002256bbc800020c3076a45b10c4112280b3c4d6e000012a91c0000000204c000000000000000001e6c8dd0000000000000000000000000467606b43f0a0a7542128000271c000000025d0000000285978dc00000009bc6ff8000000000020a92289b89a6f73f82ea5419167c089b060001b428a947de9dfa7bc34b90c46bc800000000008f0674242a0b9c3eaa2d04f090dc8a1e7760fa2856000213436dc000217ae4d00000000002118be89cec0a90000812c00000000000000de4117800006c1f0a6cd9c420000fb8b290e1e01f2430b970ef268b9582000183a0001de8000000000000000000cdb0000000b969b2d7229b24976af23a529f6d0000000000000096e000000000000000000217000060e1e640000da46c38118312679944ec000589400036b9158000147100000005df000000000002610000a929e0e00000000000000459000004980002ffa010b7d9466b961fae4db851807a31120000000b1790ce24845d353d
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x845f7654c530423b394c2298211d9c46590c108f4e032c860846f725954304236392caa18211d9c46550c108eaebb0a860847575185430423cba8c0a18211b9c86510c108dae4328860847671194430428eba4a62182147dd54310c10a3aeaa1886084767198e520421fba2c7290210f1d163948108bee6b02a40845c735815204237bb2a429021879926314810c3cc8b18a40861d6458c520432ab1cc2290219658e601481087ce932e640843d74997320423ab8acb990211d9c465cc8108eaeb30e6408655539873204278b84c3990211d9c6658c81087ce832c640843d74196320421f3a4ca990210f5d2654c8108ece332a640847a70995320421fba2ca990210f1d1654c8108eee2b2a640847b70595320430e324a69902187191534c8108eaea30a640865653185320423cba8c0990219694c604c810cb2a6302640843e74d94320421eba6ca190210f9d0650c81087ae8328640847671194320423d380ca190219654e608c41087ce9b28620843d74d94310429b3a6a7908214d5d353c84108eaec29e42085567314b21042aab98a590821179cf65884108bae7b2c42085657294421042b3baa4210821599cb65084108eaeda98420853674d4c210429aba6a610821599cb53084108ecec29842084757614c21042b3390a61082159dda52084108eeeca9042085567314821042aab98a410821599c85208410ec4a530042084777558021043b1292c0108213cdd56008410ce6eab0042086d373580210436839ac0108219cd4d6008410ce2a6b004208672525802104338292c01082117dcd61940108b8e6b0ca00846f725865004236392c3280219998b21940108eeeab0c600843e74994300421eba4ca180211d5c5650c010caaa73086008475715962004333294c310021595d42188010ccaca10c40085e170086200423bb8eca90021179cc65080108bae632840084777558420042b2ba8421002199d9421080108eaeda9e200853574d4f100423aba8c5880219998a52c40108eaec29620085557314b100423abb4a3080211e5da5184010ce2cb90c200867165086100423b396ca8802195d976344010caeca31a20086946418d100423b3b6a6880214d5d35344010ccecbb122008475759891004273394c48802199d946244010d8ec631220086c4631891004333ba8c48802199d4c6244010ccaa631220086e170189100423a3b4a4880219918a52440108ecec2922008555731491004332310a4880219918a5044010b64e998220086e062cc110042b8ba86088021d454c3044010dc0c4182200857175881100437031440880213c1d92044010ba0e6902200865b65d8d100432db28c688021a61906344010cd6cbb12200866b651891004364318c488021b818b61440108f4ed28a200857175cc510042793b442880215cdd52144010
  | 1 => 0x2144333b18a590a219958c52c8510cc8a530642887605298321442793acc190a219c9d660c8510da6a730642886d0539832144371a94c190a219c94a60c8510ce0a530642886e0529832144330294c190a21d814960c8510cb0a7b024288658531812144335a90c090a213c1c16308510e2ea9a9842885367494c214429aba4a610a21559ce5308510acce529842885657294c214429bba2a610a214d1d15308510acee4a9842885647254c214423abb0a610a21559d45308510e2ea829842887145414c214432b3b0a610a21955d85308510caea731042886545398821443a3a9cc410a21d114e6208510e8ea7a90428874453d4821442b2bb6a410a21559ce5208510aaae729042884777654821442abb9aa410a21551cd5208510cccc42904288566751482144333328a410a21d1d4c5208510e88a62904288667631482144332b18a410a219914a600851087ceb326608843c75593304421fbb6a9982210f5db54cc11087eec2a6608843d76153304430f326a7982218759353cc110c3cc829e608861d6414f3044317326a5982218b59352cc110c5cc8296608862d6414b304432a29cc3982219914a61cc110cc8a4b0e6088656658c630443a229463182210f9d3654c11087ae9b2a608846e72d953044236b96ca982210fdd1654c110878e8b2a608846f725953044236392ca982218d153614c110cc8a5b0a608863454185304432ba98c29822199148614c110c6ea9308608863454984304432ba9cc2182219514e610c110ccea5308608866452984304431baa2c2182218d151610c110caea6b086088654535843044333a92c21822199149610c110caccb1886088744528c430442ac3aa6018221c6151300c110e90a498060885d0714c03044332294c3902219914961c8110ac8e2294408865753986204432a29cc31022199d4a6188110cc8a530c408865753586204432a29ac31022199d496188110cc8a4b0c40886666508620443a3a984310221d114c21881108bce7b2a408845d73d95204422fb9aca90221171cd65481108bcebb1a408845e7518d204422f3b6a690221171db5348110c3ec9a9a408861c64d4d204422f3b0a690221171d85348110c3ec829a408861c6414d2044327b1ea4902219318f5248110c9ec6292408864c63149204432ba9ec2902219514f6148110cc8a5b0a408865753185204432a298c29022199d486148110cc8a430a40885647114820443333284210221d1d4c2108110e88a610840887185414f10443a4298a588221c51505384110cccc429420887475314a10443a2298a50822199dd85284110cc8ec29420886676314a1044332b18a5082218d59261d4c10c72c9306a60851e74d4e530423a38ac529821479d36354c108ece3b12a60843e74189530421eba0c4a98210f9d36054c1087ae9b02a6
  | 2 => 0xc3992219914961cc9109e0e0b0e648843e74d96324421eba6cb192210fdd1658c910878e8b2c648843e74d95324421eba6ca992210f9d2654c91087ae932a648843f74595324421e3a2ca992211ddc5654c9108f6e0b2a648847471195324423c380ca992210f9d7644c91087cea322648843e76d51324421e3b6a8992210f9d8544c910878ec2a2648861f64d4d324430e326a69922187d90534c910c38c829a648862f64d493244316326a4992218bd90524c910c58c8292648847675d85324431baa6c2992218d153614c910caea7b0a648865453d853244332296c2992218dd50614c910c68a830a648865753185324432a298c29922199d48614c910cc8a430a648847a75d81324431daa6c0992218e153604c910cb0a7b02648866852d81324431daa0c0992218e150604c910cb6a63026488658531813244335a90c0992219a148604c91087ce9b28648843d74d94324421fba2ca192210f1d1650c91087ce8328648843d74194324421f3acc8192210f1d5640c91087eedaa0648843d76d50324421fbb0a8192210f5d8540c910c3cc9a98648861d64d4c324430f320a61922187590530c910c5cc9a90648862d64d483244317320a4192218b590520c910ca8a7308648866452984324423a3aac21922199149610c910cb0a7300648866852980324423c3aac0192219614e60cc5108ecebb2462884f070592314431b328a918a2195997538c510acce529c62887175414e314438a2a0a718a219514e628c5109e4e1314628874453d4a31442ab39ca518a2199988528c510cccca29462887275414a31443922a0a518a21d1d4c528c510e88a629462886677614a3144333b20a518a2199590528c510cc8a5304628863854d813144334296c098a218e150604c510cb6a6302628866852181314423a3aac898a21391c9644c5109e0e0b22628865465d8d31442b3394a698a211d9d8534c510e28a829a62884767694931442b3394a498a211d1d8524c510cc8c429262887275414931443922a0a498a21d1d4c524c510e88a629262886677614931443323b0a498a2199d90524c510ccac829262887476314931443b0296c098a2199148604c510ec0a430262884f27518131443393a8c098a21acd50604c510d60a830262886d3531813144368298c098a21b8d48604c510ce4a43026288670521813144370290c098a2198148604c510ca8a73086288664529843144334294c190a211d9d763c85109e4e1b1e428871754d4f214423abb4a790a214d9d253c8510a6ae929e42885667294f214423bbb2a790a214ddd153c8510a68e8a9e42885647254f214423b3b0a790a219558c53c8510e2ea829e42887145414f214432b3b0a790a21955d853c8510aace729642885557394b21442abb9aa590a21551cd52c8510e8ea629642887445314b
  | 3 => 0xd16214d10878e8b10a68847771588534430f32ea829a21175da5414d10a9ce52a0a68854d72950534422fbb2a829a2153dc95414d10a98e4aa0a68871754584534438a2a2c229a21555c76414d10ab2e1b20a68861d6419053442aab88c829a21555c76214d10a3ee8b10a68851c7458853442abb8ac429a2156dc16214d10a3ce8310a68851d7418853442aab88c429a21565c06214d10aa8e4b08a68851e74d80534428eba6c029a2147dd11014d10a38e8880a68846e72d964344236b96cb21a211bdc96590d108d8e4b2c868863754986434432a29cc321a211d1d56190d10ca8a6b0c868863b54982434432c29cc121a211e1d56090d10cb0a6b04868846e72d954344236b96caa1a211bdc96550d108d8e4b2a868847771595434423db82caa1a21479d35350d108dce5b28868846d72d944344237b92ca21a211b1c96510d10a3ae8298868851e7550c434428e3aa8621a21879954310d10c38caa18868865453984434423a3aac221a213c1c16110d1087ce931ea48843d7498f5244387aa6a7a92214b9d253d4910a5ae929ea48852f7454f52442963a2a7a9221c3d5053d4910e18a829ea4887457114f52443a3a9ac3a9221d114d61d4910a5ce9b1ea48852d74d8f52442b2b8ec7a92215a5c363d4910a5ce931ea48852d7498f52442b2b88c7a9221c350c43d4910a9ce7b06a48854d73d83524430f326a729221875935394910c3cc829ca48861d6414e524432731ea5292219358f5294910c3cc931ca4886557198e524430f322c7292218759163949108bceda9aa48861f64d4d524430e326a6a9221179d85354910c3ec829aa48861c6414d524430fb26c6a922187d906354910c38c831aa48864f63d89524432631ec4a922195d8f6154910ca8c7b0aa48865863d815244237bb2a42922153dcd5214910a98e6a90a48843f7458c524421e3a2c629221539ce6214910a9ae7310a48864e65d4c5244387aa6a629221d1dc753149108daed298a48852e7494c5244296ba4a6292211bdd95314910a5ee8a98a48852c7454c5244327328a629221c3d505314910e18a8298a4887457114c52443a3a9ec229221d114f6114910acae3318a48852f7458c52442963a2c62922159dc56314910ad6e0b18a48852e7418c5244296ba0c629221595c46314910ad2e0318a4885667190c52442b2b8c86292215a9c24314910ad2e1218a48870d4310c52442b33888629221595c44314910acae7b08a48876270d8452442a7b9ac029221531cd6014910a9ee6880a48854c73440524421f3a6cb992210f5d365cc9108eae3b2e648843f74597324421e3a2cb992211d9c465cc910c6ea930e648863454987324432ba9cc3992219514e61cc910ccea530e648866452987324423a3aac3992218dd5161cc910c68a8b0e648865753587324432a29a
  | 4 => 0xe6cb90a40106d063c8520082793b042900419cd942148020da0c610a40106e362085200833930ac1a9e210fdd16294f10878e8b14a78845f7654c53c430eb22a629e21875926314f10c74c8b00a78846e7299543c4236b94caa1e21471d15350f109e2e2302878846e72d9443c4236b96ca21e2187d954310f10c3acaa18878861e6498f52c430f322c7a96218759163d4b10cacc730ea5886556398752c432d31ac1a9621555cc6194b1087ce831aa58843d7418d52c4237bb2a4296219c9856014b1087ce832e658843d7419732c421f3a4cb196210f5d2658cb1087ce932a658843d7499532c421fba2ca996210f1d1654cb1087ce9b28658843d74d9432c421f3a0ca196210f5d0650cb10c3ac9298658861d6454c32c4272392c898e213c1c1644c7108ecec29a63886646294931c432d29ac018e211d5da53c8710a6ce829e43885357414f21c42ab39ea590e21555cf52c8710acce5a98438856572d4c21c429b3a0a610e214d5d05308710acce429843885657214c21c42ab39ea410e21555cf52087108eeeca9043885677654821c4333bb2a410e21d894a6008710ec4a4b00438861d6494f30c430eb22a798621475d0538c3108bced29a618845d76d4c30c428eba0a6186211b9da5248310ccca430a41886655218520c4236bb6a4106219c58660d4e108beeca98a70846e729954384236b94caa1c211b9c86510e108dae4328870846f765485284338b0cc0294210f9d2654ca1087ae932a650843f74595328421e3a2ca994210f9d3650ca1087ae9b28650843e74194328421eba0ca19421179da534c6108baeda98630856672d4f21842b3390a790c21d894a60c8610ec4a4b06430846e769492184236bb6a410c21599ca5308610ac8e4a9843084757614c218423abb6a410c21395db5208610bc4e1a9043085e27014821843b1380a410c219554d610c210ccca4b0c41086666294b108421f3a4c5a9a210f5d262d4d108eee2b16a68861f6499353442aab88c9a9a21565c064d4d10a3ce9b16a68851d74d8b53442aab8ec5a9a21565c362d4d10a3ce9316a68851d7498b53442abb8ac5a9a2147dd160d4d10a38e8b06a68861e64d4e534430eb26a729a218bd526294d10c9ea7314a68862f5458a5344327a9ac529a218b9926294d10c5ac9314a6886677198a5344317322c529a218b5916294d10ccee2b14a688666625865344317aa6c4a9a218bd506254d10c3ec9b1aa68861c64d8d5344317b26c4a9a218b1936254d10c9ec7b12a68866571d895344317b20c4a9a218b1906254d10c9ec6312a68866771189534431a326c2a9a219918b6154d10c70c9b02a68866862d81534422fbb2a629a2147dd15314d10a38e8a98a68854f7254c53442a6392a629a21479d26314d10a3ae9318a68854e7298c53442a6b94c629a210fd
  | 5 => 0x5e3704c821082b2ba86410841699d03208420b4ae81904210745530c821082e839ac010841789c26508420accebb18421056575d8c21082f1386c610841785c36308420bc6e0b1842105e07058c21082b33a8c610841595d46308420b4ce831842105a57418c21082f1380c610841785c06308420bc4e1a9842105a67414c21082d2ba0a610841d154c5308420bc4e029842105e27090c21082f0b84861084159dd54308420ac8eaa1842105e37050c21082f03828610841599d44308420acaea21842107854310c21082f0bb4c010841b8d966008420dc2cb30042105e27398021082b3baac01084171dcd6008420b88e6b0042106e37658021082f1baac010841d8dd56008420f86e6b0042105e07358021083e039ac010841701cd6008420b8ce630042105c57318021082f1380c0108410f9d2639402087ae931ca01047576c86500823abb04328041595d82194020ccaec10ca0106656508730083533204398041a959021cc020c74c929660106b264c8730083553244398041aa99021cc020d64c810e60106e16208730083713b04398041b85d821cc020dc2ca10e60107616508730083713204398041e899021cc020d44c810e60107a16408730083703204398041f09cc21cc020f82e610e601043e74d96300821eba6cb18041391c5628c020cceca10a601043e74194300821eba0ca18041391c5620c020caca6b086010655535843008272392c21804139dd8210c0209caec10860107c0214c0300823cba8c818041665d2630c0208f6eca9860104d97690c30082acbac861804196596430c020cb2caa1860106986450c30082e439286180411edd5620c020970e8b1060105e071588300832cb2c641804196594320c020b32e81906010671659843008338b2ac218041781c9610c020ab2ea18860104f176c843008338b2e4218041789c6210c020f846210860107c0310843008278bb042180419c594210c020f846410860107c03208430082f1bb04218041b89d8210c020bc2ec10860106e1760843008370b284218041b8990210c020dc0c810860107c37308430083e03984218041b898c210c020f84c610860107c25308430083e0a984218041f090c210c020f828610860105aa74cc32008236bb4a5100412e9d263880208f2ed29440105e1760862008370bb04310041b898c2188020dc0c610c40104e676c852008333b2e429004199d942148020d8ec610a40106c4630852008327b2ec69004193d946348020d18c831a401066765d852008333b28c290041b1d8c6148020d88c630a401065b65d8d200823cbacc6900412e9d263480209b4e731a401065b6518d200834db20c690041a61906348020cb0c729240106c8639492008339b2ec290041b418f6148020ce6ca30a40106d0631852008371b10c2900413c9db2148020c
  | 6 => 0x1482aa39a4028a410fdd165cc520878e8b2e629043f74596314821e3a2cb18a410f9d3654c52087ae9b2a629043f74594314821e3a2ca18a418e152600c520cb0a7300629067051980314831c2a2c018a419614d600c520caccba9e429071754d4f214823abb4a790a414d9d253c8520a6ae929e42904777654f214829bba2a790a414d1d153c8520ae6e0a9e42906566514f214838baa0a790a41c515053c8520cb0a7304429067051982214832c29ac110a419614f6048520cb0a6302429067351181214832b32ea610a41c5d5353085208eaed29842905367494c214829aba4a610a41559ce5308520acae529842904777654c214829bba2a610a414d1d15308520acee4a9842905737054c21482ab3a8a610a41959945308520e2ea829842907145414c214832ba9cc410a419514e6208520e8ea7310429074453988214821f3acc9982410f1d564cc12087eedaa6609043d76d53304821fbb0a9982410f5d854cc120c3cc9a9e609061d64d4f304830f320a7982418759053cc120c98a7316609063664d47304831ab26a3982418d99051cc120c6ac828e6090666621473048332b10a3982410f9d3654c12087ae9b2a609043f74595304821e3a2ca982418b153624c120c58a8312609064f531893048333b10a29824199188514c120c6ea9308609063454984304832ba9cc2182419514e610c120c6ea8b08609063454584304832ba9ac2182419514d610c1208eeeda88609047576d44304823bbb0a2182411d5d8510c120a74e929e409071b5414f204838c2a0a790241d414f51c8120ea0a628e409057275c8720483a829e43902415c9d421c8120ea0a610e409065753986204832a29cc31024195d4d6188120ca8a6b0c40907475308620483a22984310241c31505388120e8ea628c409074453146204821fba2c4a98410f1d16254c208beeca98a61061d6454c530832aa9ac229841875926314c20c5ac9310a61063664984530831ab24c2298418d9916114c20c6ac8b08a610656635845308338b0cc0298411d9c46590c208eae232c861047975982430823bb8acaa18411d1c56550c208ece232a861047571195430828e3a2a6a1841399c76250c208daea312861047975181430832ca98c0a18411b9c86510c208ece2328861047571194430830fb2a8621841875954310c20b18e4a1886104b874582320821f3a6ca190410f5d3650c820c3ac9298641061d6454c320823bbb2a2288419558d5114420970e8b04621043f74595310821e3a2ca988410f9d0654c42087ae832a621064d531893108338a88c0988414d9d053c8420a6ae829e42104d87358021082f13846210841785c23108420bc6e098842105e0704c421082e439ac0108414d9d05308420a6ae82984210565758c821082f0b84641084169dd13208420b48e8990421
  | 7 => 0xa9a418e1936054d20ce6c3b02a69067061d81534822fbb2a629a4147dd15314d20a38e8a98a6905577154c53482aa38aa629a41479d26314d20a3ae9318a6905567198c53482aab8cc629a410f9d06214d2087ae8310a69061e65d50534822ebb4a829a41559c65414d20aaae32a0a69045f7655053482abb8aa829a41551c55414d20c3ac8320a69054d7219053482ab38ec429a41555c76214d20a3ee8b10a69051c7458853482abb8ac429a41551c56214d20ab2e0308a69051e74d80534828eba6c029a4147dd12014d20a38e8900a69047671d96434823ab8ecb21a411e5c36590d208eee2b2c869047471596434823b38ecaa1a411d5c76550d208dee4b2a869047771595434823a38acaa1a411edc16550d20a3ce9a9a869047671d94434823ab8eca21a411ddc56510d208e8e2b28869047b70594434828eba0a621a41479d54310d20a38eaa18869061e6550c434830e32a8621a419314e6210d208d8eab10869068d43588434823b3acc3992418dd5261cc920c68a930e649065753987324832a29cc3992411d1d561cc920c6ea8b0e649063454587324832ba9ac3992419514d61cc920c70a9306649065853983324831c2a2c1992419614d60cc92087cebb22649043e75191324821f3b6a8992410f1db544c92087cec2a2649043c76151324830fb26a69924187193534c920c3ec829a649061c6414d324823b3aec2992418dd53614c920c68a9b0a649065753d85324832a29ec2992411d9d4614c920c6ea830a649063454185324832ba98c2992419514c614c920c76a9b02649063854d81324832c29ec0992418ed50604c920c70a8302649065b53181324832c298c0992410fddb540c92087aedaa0649043f76150324821ebb0a81924187993530c920c3ac9a98649061e6414c324830eb20a619241c5d5353d4520a6ce929ea2905357494f514829bba2a7a8a414d1d153d4520e2ea829ea2907145414f514838aa1887a8a411d5db32d45208eeec996a290537744cb514829a3a265a8a415cdc132d4520ae0e0996a290536740cb514829aba065a8a41559cf60d4520aaae7b06a29061e64d4e514830eb26a728a41879905394520c3ac829ca29065663d46514832ab1ea328a41179db5354520c3ec9a9aa29061c64d4d514822f3b0a6a8a4187d905354520c38c829aa2904777654451482abb9aa228a41551cd5114520caccba98a29071754d4c514823abb4a628a414d9d25314520a6ae9298a2904777654c514829bba2a628a414d1d15314520cacca298a2907175414c514838a2a0a628a415c5c06314520e2a86218a2905667210c51482b2b908628a411d5db32145208eeec990a290537744c8514829a3a26428a415cdc13214520ae0e0990a290536740c8514829aba06428a4155dcd6014520aa8e6b00a290557734805
  | 8 => 0x4614ca20cb4a6302651065953181328822ebb6a619441479d3530ca20c3ac9a98651061d6414c328829b3a6a728c414d5d35394620a6ce929ca3105357494e518829b3a0c728c414d5d06394620ae4e031ca3105677250e51882b23928728c41c550c4394620aace7b14a31055573d8a518823abb66528c411ddd93294620a6ee8994a310534744ca51882b9b826528c415c1c13294620a6ce8194a310535740ca51882ab398c128c41555cc60946208eceda9aa31053674d4d518829aba6a6a8c414d9d25354620a6ae929aa3104767614d518829b3a4c6a8c414d5d26354620acae531aa3105677258d518838aa1886a8c4155dcd6254620aa8e6b12a31047676cc9518823a3b264a8c414ddd13254620a68e8992a310573704c951882b838264a8c414d9d03254620a6ae8192a31047776544518821f3a6cb98c410f5d365cc620cccc4a8e631066462545318821f3a6ca18c410f5d3650c620ce4a2b00631047576d4f218829b3a6a790c414d5d353c8620a6ce929e43105357494f218823abb0a790c419c9456088620ce2a3b0243104e576d4421882f1386a210c41995965108620bc4e02884310565758c421882b2ba86210c41789c031086208eaeda98431053674d4c218829aba6a610c414d9d25308620a6ae929843104757614c21882d3ba26410c41691d13208620e8ca699043105a6740c821882d2ba06410c41d1d4c3208620acaebb1843105657518c21882d33a0c610c41695d06308620bc4e031843105e17018c2188272bb6a610c41699d35308620b4ae9a9843105e270d4c21882d33a4a610c41695d25308620e8ea729843104e57614c21882f1380a610c4159dd54308620ac8eaa1843105667510c21882b2ba88610c41e150c4308620ccacb30043105c77358021882e239ac010c41995946008620b8ce630043105c5731802188370b00c010c418d99251cc220c6ac928e611063664547308831ab22a398441a999021cc220d4ac810e611051d7494e308827238ac518441475d2530c2209c8e2b10611047575984308823bbaac218441391c9610c2208eaed2886110477765443088273bb04218441395d8210c220ccacb28e411066565547208829d3a4a7904419c59651c8220ce2caa8e411061f64993534828f3a6c5a9a41475d362d4d20aace3b16a69055571d8b53482abb8ac5a9a41551c562d4d20a3ee8b06a69051c74583534830f326a729a41875935394d20c6ea930ca69065753986534831baa2c329a4195d4d6194d20c6cc930ca690635649865348332b14c329a418d9916194d20c6ac8b0ca69063a64582534831baa6c2a9a418dd506154d20c3ec9b1aa69061c64d8d5348316326c4a9a418dd936154d20c68c9b0aa69065763d85534831bb20c2a9a418d1906154d20caec630aa69066762185534831db26c
  | 9 => 0xee8a90421853474548210c32ab2c6410861955943208430b2ae81904218745520c8210c30f3228728061475d03294030cacc728e801865563947400c32b31aa3a00619558d51d0030c3aa931c801865663546400c32ab1aa3200618719543100308eaed288801847776544400c31b324a3980618d59251cc030c6cc8a8e601863564547300c34ab24a398061a559151cc030d2ac990e601855575087300c34ab204398061b198821cc0308baed29c601851d7494e300c23cbb4a718061665d2538c030d94c51946018599740ca300c2b8ba8431806117dd5644c030998e4b2260184d471591300c32bb2ca29806195d95514c030caecb90a601855575085300c32bb284298061b1188214c03093ae9b0260184da76d01300c34cb208098061745c4404c030b34e929a60184da7610d300c3643146498061669d0324c030ce6cb28a601867365545300c26d3b662980619cd97214c030ae2ea10a601867365085300c370310429806117dd95314f20c3ac8a98a79061d6498c53c823b38ecb21e411d5c76590f20cb4a6b04879047671d9543c823ab8ecaa1e411d9c66550f208eae332a879051c7454d43c823b38eca21e411d5c76510f20c3ecaa18879061d6550c43c8346a1ac421e413a1c16210f20970e8b04659061d6494c32c830eb22a6196411ddd9511472087ce9b2c639043d74d9631c821f3a4cb18e410f5d2658c720aaae329c63904b87458231c823abb4a790e414d9d053c8720a6ae829e43904d87358021c823abb4a610e414d9d05308720a6ae829843905d07358021c830eb24a7986418759153cc320c72cb32661906396559330c8355324c598641ac99321cc320d64c810e619051d7414e30c822f3b4a698641175db530c320a3ae829861904e97219030c82ccba4c6186411e5db530c3209b2eda9861905ca72d4c30c82ccba0a618641729c8530c320ab4eb21861906986450c30c825c3a2c418641665d0320c320ce2cab08619055a750c430c8278bb642186413c5d8210c320c6cc930ea71063564987538831b322c3a9c418d59161d4e20c74c9306a71063964983538833930cc1a9c419c58660d4e20a3ce9a9ca71061d64d4e538830e39ac929c41479d36354e208beeca98a71051d7498c538823b38ccb21c411d5c66590e208ece232c871047571196438828eb9ca921c41479d35390e208ece332a871047571995438823b388caa1c411d5c46550e20a3ce9a9a871045e7614d438827338ec4a1c411d9c66510e208eae3328871047671194438823ab88ca21c41475d25310e208beeca98871051f7550c438828ebaa8621c41879954310e20c38caa18871058c7250c438828eba4a7994411d5d661cca208eeeab0e651051e74d4e328822f3b4a699441475d2534ca20c38c929a651061c6454d328823abaec2994411d5d
  | 10 => 0x5707050a510c2ab3988528861555cc42944308eaed994a218474764ca510c29bba265288614d1d13294430ae6e0994a218536740ca510c29aba065288614d9d06094430a6ae8304a21847676d51510c23b3b0a8a8861599c85454430acae42a2a2185d17090d510c2abbaa86a8861c515143544308eceda92a21866462949510c29bba2a4a88614d1d15254430cc8c4a92a21847676149510c29b3a0a4a88614d5d05254430aaaeb192a2186c4628c9510c2caba064a8861559ce6454430aa8e6b22a21856772591510c2b2392c8a88615c1c16454430a6ce931aa2185357498d510c2b3394c6a8861595ca6354430ae4e121aa2185717090d510c38aa1886a8861559ce6254430a6ee8b12a21853474589510c2aa39ac4a88615c1c162544308eceda12a21847576d09510c33231684a88611ddd942544308e8eca12a21855773509510c2aa39a84a88615cdc14254430ae0e0a12a21855673109510c2aab9884a88619918842544308eced992a218664628c9510c23bbb264a88614ddd13254430a68e8992a218664624c9510c2b9b8264a88614d9d03254430a6ae8192a218572700c9510c2b8b8064a88611ddd951144309b2e131e821865563547410c237b92caa08611b1c96550430caec6a8a821865463545410c338a8ec0a08619c5446050430caac7288821867251580410c338a8ac198861175d7648c4309b6e0b24621865565946310c24fba2c1188619c945600c4309b2e1b2062184db75580310c32dbaac018861361c9600c430da4a2b0062186d151580310c26cb84c7908619598d51c8430caac6a8e42185d1700c7210c2b3396cb90861959cf65c8430ccce5b2e421853674197210c29aba0cb908611d9db54c84308eaedaa6421847676153210c23abb0a990861599c854c8430acae42a642186576598f210c2e8b84c79086195d9563c8430a6ae929e42185557590f210c32ab2c8790861745c243c8430caacaa1e42187145450f210c29bba2a5908614d1d152c8430caacb1964218655650cb210c2caba065908610f9d3658843087ae9b2c421865563946210c33928ac1108610fdd16548430878e8b2a421865763545210c338a8ec090861175d7630843093ae831842184d97018c210c32ab2c6210861955943108430ba2e0188421856672d94210c333396ca108611d5da6508430ca8e6b28421853674194210c29aba0ca108615c9c065084308ecedaa0421847576d50210c2b3b92a810861591c954084308ecec2a0421847576150210c2b3390a810861595c85408430aaaebb18421865565d8c210c2e3396c610861555d46308430caaca31842185957418c210c2e3390c610861745c06308430a6ae929842185557590c210c32ab2c8610861745c24308430caacaa1842187145450c210c2e239286108611d5d66208430a6
  | 11 => 0x4c2a6392a918261551c5548c130e88a410c60984777158b540c23a38ac5aa0611d9ca61d5030cacc6b0ea81847472587540c338b0cc1aa0611ddc562950308e8e2b14a81847671d89540c23ab8ec4aa0610fdd95415030c5aa8b10a81866771988540c33238cc42a0611ddc562150308e8e2b10a81864e63588540c333b8ac42a061991c56215030cd0e0b10a81866662984540c332b14c22a0611d9ca6115030cccc4b08a81866562584540c23a392c22a061535c85490c308beeab0486184db75582430c32dbaac121861361c96090c30b34e1aa2861845e76151430c2a6b90a8a1861279d85450c30b1ae42a2861851e76151430c30f3b0a8a1861c39c85450c30a3ae42a2861870d72151430c286b90a8a1861c59c45450c30e2ae22a2861851e70151430c38d380a8a1861871506250c309b2e030a861843f76550430c28eb9aa821861a650e6010c308ece3324a41847571992520c23bb8ac9290611d1c56494830c3ce6322a41861d73191520c316b90c8a9061179da4354830c38c921aa41861c6450d520c31bb26c2a90618d1936154830c6ec830aa41863464185520c31db20c0a90618e1906054830ce6c2302a41867061181520c237bb2a4290618b59152148308ece3b2e841847571d97420c23b38ccba10611d5c665d08308eaeb30e841847775587420c34ca1cc1a10611d9c665908308eae332c841852c7454a420c38721aa5210611ddc565508308e8e2b2a841847671195420c23ab88caa1061879506350830c3aa831a841861c6550d420c32631ca4a1061c350d52508308eaebb0a841847575185420c31d2a0c0a10618e5506050830d3286302841866a52181420c23b38cca210611d5c6651083087aedaa084184d97098c420c30faa2c621061275da4310830c3acb218841847575987320c23bbaac3990610fdd1658c830878e8b2c641849f74596320c28e3a2cb1906136dc1648c8308baed2a4641845d76152320c30fb20a919061535c8548c830a38e8a9464184d970986320c2acbaec11906127dd1608c830c5ac9290641862d64548320c26cb86c819061275da640c830c3eeab20641861c75590320c22ebb4a81906187592540c830c3ac82a0641854d72150320c346b24a419061471d1520c830c3ac8a90641868d64548320c34cb24c019061a6991600c830acce42a4a21856572152510c2caba0c728861745c24394430e28a8a1ca2186666294a510c29bba2a5288614d1d15294430cccc4a94a2185367414a510c29aba0a528861655d03294430e8aa4194a21855673192510c2b9380c9288614d9d06394430a6ae831ca2187154310e510c29b3a6c5288614d5d36294430aace7b14a21857270d8a510c23b3b685288611d5db42944308eeeca14a2184747650a510c2abb9a8528861551cd4294430ae6e0a14a218
  | 12 => 0xa94611bdd95214a308ece3b2e851847571d97428c30fb2a87a14611d9c66590a308eae332c851847771595428c23a38acaa146187d954350a30d3286302851861e5458c428c30eaa2c621461275da4310a308baed2a4651861f64952328c24fba2c1194619a948604ca30c3acab20651861f75590328c34db82c819461a61c1640ca308baed2a0651861d64950328c30eb22a4194611ddd95114630c6ac8a88a31846e72d97418c236b96cba0c618795163d06309b0e6b04831849f74582318c26cb86c818c610f9d365c863087ae9b2e431843e74997218c21eba4cb90c614d9d365c8630a6ae9b2e431856672d97218c29b3a4cb90c614d5d265c8630e2ca8a1e4318595740cb218c24eba0c610c61365c063086309b0e6b0043186d231580218c2b3396ca10c614d9d06508630a6ae8328431856672d50218c2b2b96a810c61599ca5408630acae52a043185c672d8c218c2caba0c610c61719c86308630ba2e031843187165450c218c2e23928610c61655d03208630ce0cab0043185d073580218c369b1ac010c618759664cc230c3acab26611869564c87308c34ab204398461b198821cc230c72cb326611863965593308c23bb8ac5aa2611d1c562d51308eee2b14a8984747158a544c23b38ec4aa2611d5c76255130ccce3b12a89866571d89544c327b18c4aa26199dc46255130cc8e2312a89866762d85544c332316c2aa2611d9cb6155130caec630aa89866762185544c332310c2aa2611d9c86155130cd0c5b02a89867061d81544c21fbb2a82a2614b1c95415130a68e2aa0a89847771588544c23a38ac42a2618e15160d0d30c3ccaa18869846f76548524c2963a2a429261591c552149308eee2b20a49847471590524c23b388cba12611d5c465d0930ccea530e849866452987424c23b38ccaa12611d5c665509308eee2b28849847471594424c30faa2c6212618715163109309b0e0b18849864d63d48424c316326a4992618b190524c930ccea430a649866452185324c334296c0992611ddd95114530a68e8a88a29856472544514c22f3acc720a611bdc965105308d8e4b28829853674d97214c29aba6cb90a61599c865c85308eeecaa6429847476553214c2b3b92a990a61591c954c853087ee8b28429843c74594214c21f3a0ca10a610f5d065085308bceb318429856571d48214c33828ac010a614ddd16508530a68e8b28429855773594214c29b3a0ca10a614d5d06508530acce4328429856672950214c2b2b94a810a611ddd954085308e8ecaa0429856772550214c2b2392a810a61559d66308530acceb310429856576d48214c332bb6a410a6159dd85208530e8cc6290429874563148214c3b0294c010a615c1d56008530ce0cab0042986d163580214c3b0292c010a6187d5163d0130c38a8b1e80987605208730
  | 13 => 0x62953308e8e2b14a99852e7218e54cc296b90c72a6614d9c46395330a6ae231ca99853671d8a54cc29ab8ec52a6614e5c36295330a38e6b14a9985377158a54cc29a38ac52a6614edc16295330a3ce6314a9985397018654cc23b38ec4aa6611d5c76255330a6ce331aa9985357198d54cc29b38ec4aa6614d5c76255330a38e6b12a9985377158954cc29a38ac4aa6614edc16255330a3ce6312a99851e7398554cc29db82c2aa6614bdc96055330a58e4b02a9985377158154cc29a38ac0aa6610fdd954153308eee2b10a9984747158854cc31caa4c121e618e9526010f30c6ca930ea5986355498752cc31b2a2c3a96618d55161d4b30acce3a94a59863654d8552cc31aaa6c2a96618d9506154b30c6aa830aa59867361d8152cc33830ec0a96610f5da5414b3087eecaa0a59846f7654852cc23b38ecba16611d5c765d0b30c6ca930e85986355498742cc31b2a2c3a16618d55161d0b30c74a9306859863a5458342cc23bb8acaa16611d1c56550b30c3ca9b1a859861d54d8d42cc30f2a0c6a1661875506350b30c6ca9b0a859863554d8542cc31b2a0c2a16618d5506150b30c74a9b02859863a5418142cc31caa0c0a1661875526310b30c3ca8b18859861d5458c42cc31b2a4c3996618d55261ccb30ccca530e65986655298732cc31b2a2c3996618d55161ccb30c74a9306659863a5458332cc31b2a6c2996618d553614cb30c6ca830a65986355418532cc31d2a0c0996618e550604cb3087aeb320659843f7559032cc21ebb4a8196610fdd9540cb30c5ca9316a39862d5498b51cc3172a2c5a8e618b55162d4730acce5a8ca39843d7695051cc21fbb2a828e611ddd95114730c3aa931c839861d5458e41cc31caa0c0a0e618e9526010730c74a8b00839863a5498031cc31d2a2c018e610f9d265c873087ae932e439856672d9721cc29b3a4cb90e614d5d265c8730a6ce832e43985357419721cc21f3a4cb10e610f5d26588730c74a9304439863a5458221cc21f3a0ca90e610f5d06548730c74a9b02439863a5418121cc21f3a4ca10e610f5d26508730c3aa9318439861d5458c21cc2b3b8aa410e61599cb6508730a6ce932843985357499421cc29b3a0ca10e614d5d06508730acce42a043985657215021cc38aaa4c610e61c55516308730acaeb31043987265498821cc392aa4c410e61c99525208730e4aa929043985677694821cc3a331ca410e61d158e5208730e4ca8a9043987255454821cc2b3bb2a410e6199dd95208730ec6e0a90439861e5458f40cc30eaa2c7a06611ddc562d52308e8e2b16a9184777158a548c23a38ac52a4611d9c762552308eae3b12a91843f76550548c31aaa2c22a4618e5506050e30a3ced2a2871861e76951438c28eb94a8a1c61879506250e308ece3324a51847571992528c22e3b286
  | 14 => 0xeca1ca410ce67610e5208672bb08729043e150c4394821b8ce7b04a410dc573d82520863aba8c9990439559643cc821caacaa1e6410e946450f32086e23928799043e150f42cc8218eeeab1c6410e976410e32086e2b90871904399596528c821f08872146410d5575cca320863abacc1190432ddd1608c821968e8b046410e3765d91320863abacc8990433c9c2644c8219e2e13226410c77755913208673b92c8990433cdc1644c8219e0e0b226410cb676191320871bb28c899043a95c8644c8219aced21a6410e576590d320874a324869904395d95434c821d28c8a1a6410dc47250d320871bb24a4990438d192524c821d4ec92926410ea46494932087523248499043e190e424c8219c8eca126410dc47350932087c2a1a8499043a9193324c821caecb1926410e94648c93208739b2ec099043acd93604c821d60c9b026410ee252d813208739b28c099043acd90604c821d60c83026410ed2431813208768a18c099043b8dc8604c821dc4a43026410ee2421813208770a10c099043b8cc8604c821da4643026410cb674d94320865aba6ca190432d9d0650c82196ae83286410ce672194320865abb4c819043a51cd640c821d48e4b206410cd6731903208673390c8190431d5d6630c821d2ac92986410e956454c320866abb68619043a5593430c8219aaec2186410e956410c32086e2b9086190438d992520c821c6ac92906410ce5769483208732b2ca419043a9992520c821d4ac92906410dc5739483208672bb68419043a9593420c821f0e87a106410ce57610832086e2b988419043e110c420c821aaaeb9906410e9564cc83208752b246419043715ce320c8219aeec9906410d57754c832086ca3a26419043a5591320c821ba0e09906410ce7764c832086d23a26419043a9591320c821bc0e09906410dc7764c83208763bb2641904371dd5320c821e8eea9906410f87744c832086e33a26419043711d1320c821f08e89906410d84744c83208763b226419043e1991320c821d8ac89906410f85644c83208742b226419043f0dc1320c821b88e09906410fc0704c832086e038264190432d9d2639402196ae931ca010de27094a500874bb26c6a8043a5d906354021d28c831aa010ed17018d500872a31ea6a80435c1c15354021d8ec6312a010ec463189500872bb1ca4a80439518e5254021ae4e1292a010ec763949500876231ca4a8043789c25254021d2cc9318a010e966458c500874ab22c628043b198e6214021d8ac7310a010ec6639485008762b1ca4280439558f5014021da2c7280a010c7776540500872ab1aa0280433cdd95014021da2c6a80a010d73765405008739bb2a028043d4dcd5014021ea0e6a80a010f52635405008738b1aa028043d458d5014021ca2c6a80a010f607254050087b1312a0280431ddc5
  | 15 => 0x3e74d94320861eba6ca1904387592530c821c3ac8a986410d8c744c83208746b226419043721c1320c8219cae43266210ce772583310861f3a6cb188430f5d3658c4218eaebb246210ce572d9231086b8b80a7188431ddd5628c42196ee8b046210cb4745823108673b92c11884339dc9644c4219e6e0b226210cf070591310863b3b0a6988435c5c0534c4219cae5b026210c3e74194310861eba0ca188431d5d7640c4219e4e1b206210cf170d90310863aba8c818843395c8640c4218eeeca986210c77755883108673b92c0188431b5da528842196ce9b1c4210cb574d8e2108679386c7108433c5c363884218eaed2944210c757598d210863bbaac6908432ddd16348421968e8b1a4210cf37058d2108678382c6908430f9d2639402187ae931ca010e1f64d8d500870fb20c6a8043871906354021cace231aa010e557118d500872cb80c6a80439518e3154021ae0e098aa010c7b76540500872cb1aa028043399c262d4c2196ee8b06a610cb4745835308672392c929843719cb5394c219c8e4b04a610ce67219153086e3396a6a9843399cb6054c21d2ac9298a610c777654c530866bbb2a629843a55915314c21d4cc9310a610ea564988530876329cc429843b154e6214c219cce1310a610eb2649805308758b24c029843b898a6014c21dc0e5300a610eb2645805308758b22c029843b89896014c21ce6a6b00a610ed2535805308738a9ac029843b454d6014c21dc0e4b00a610ce6729964308673390cb218433c9c06590c219e2e032c8610c777558a4308673b92c121843391c96090c219cce532a8610cf3705954308678382caa1843399c86550c219e4e032a8610cf170195430872a32aa6a1843651d15350c218eaebb128610ce575d894308732baec4a1843399c36250c219caea3128610ec6531894308762a98c4a1843a990c6250c219cce03128610ce672d814308672b96c0a18431d9d46050c218eaea3028610ce6729944308673390ca218433c9c06510c219e2e03288610d957490c430866bbb28621843711c94310c21b2eeca188610e977650c430874bb2a8621843a55954310c21f0ee4a188610d947250c43087c23928621843611c94310c21f0a873108610ce5759884308673384c4218431ddd56210c21d2a86b108610cf3705884308678382c421843e150d6210c21bc0e0b108610ce7755884308733baac421843b190d6210c21d8a86b108610e85435884308771b82c421843391c16210c21dc0e0b108610ce070588430874aa1cc02184339dc96010c219c8e4b008610d367414e520869aba0a7290435c9c05394821ae2e029ca410d367418e520869aba0c729043c550c4394821b4ce831ca410da57418e5208762b18c729043699d05394821b4ae829ca410de27014e52086f0b80a72904339dd943948219c8
  | 16 => 0x871bb28c899643359da434cb21d28c921a6590e946450d32c874a32464996439cd97604cb21d66c9b026590eb064d8132c8739b28c099643acd90604cb21d60c83026590ed24318132c8768a18c099643b48c8604cb21d28e6b206590e956494c32c874ab22a619643355db430cb21d2ac9a186590e956410c32c874ab26641964335dd9320cb21b28e89906590e95644c832c86e8382641964339dd9320cb21d2cc931ea190e966458f50c874ab22c7a86435c9c353d4321cacc6a9ea190ec66398b50c8762b1cc5a86432d9d2639432196ae931ca190d7176d4250c8738bb6a128643d49cf5094321ea2e7a84a190f6272d4250c863bbb2a0286433cdd95014321c6cc930ea710e3564987538871d324c1a9c438e59260d4e21ce4c3306a710e3a64583538871cb22c1a9c439c98560d4e21a3ce9a9ca710d5a70d4e538868f3a6c6a9c43569c36354e2187ce9b02a710c3d74d81538862fbb2a629c431e9c06590e218f2e032c8710c7a70995438863cb84caa1c431e9c26510e218f2e13288710d1d7494c438868fbaa8621c43475d54310e21b18e4a188710e8d435884388674382c421c439554e61cca21c38c929a6510e1c6454d328872b298c2994439694c604ca21cb2a63026510d8c744c83288746b226419443721c1320ca21a6ce9a9e4310d3574d4f21886b9386a790c435c5c353c8621ab4e7a84a110c7b76540508861fba2c1a9a430f1d160d4d21c38c9b1aa690e2c64d89534871bb26c2a9a438d1936154d21c76c9b02a690e3864d815348739b0ec0a9a438ed906054d21c70c8302a690e5b631815348735b10c0a9a439cd846054d218beeca98a690d1c7454c53486ac382a629a431d5c76590d218f4e1b2c8690c7970d96434863bb8acb21a431d5c76550d218dee4b2a8690c7771595434863db82caa1a431e1c16550d218dae5b288690c7571d94434863bb8aca21a431edc16510d218f0e0b288690d1d7414c434868f3aa8621a43471d54310d21caea6b0e6490e1c64d4d324870e320a6992439514f614c921cb6a63026490e5853181324872629ac598a430fdd1654c521878e8b2a6290d377454f214869a3a2a790a435cdc153c8521ae0e0a9e4290c7b7654050486ac39aa0282430fdd160d4c21878e8b06a610c5f7654c530870eb22a6298439654d6014c21c3ac9318a610e3a64980530871cb24c0298438e9916014c21c72c8b00a610e5a63580530873930ac0298431e9c06590c218f2e032c8610c7575986430863db82caa18431e1c16550c218f4e032a8610c7970195430868e3a2a6a1843395c76250c218daea3128610c7575185430872aa98c2a18431e9c06510c218f2e03288610e1f6550c430870eb2a8621843631c94310c218daeb3108610e8d435884308673b8ac4218433a1c16210c218eaeb3088610c
  | 17 => 0xa4638d5506150e31ae2e030ca518c6f76548528c63d384cb214631e5c26590a318f6e0b2a8518c7870595428c70f2a2c621463875516310a31ccca430a6518e666294b318c61fba2c5284630f1d16294231c6ce2322a118e3571191508c63dbb2a0284638e5915014231ccae3b12a898e4f63189544c733b88c4aa2639918b6155131cd6c5b02a898e6862d81544c72db18c0aa2639ad886055131cd0c4302a898e7361181544c738b88c0aa2630fdd95415131a58e4aa0a898d3870550544c63db82c42a2631e1c16215131c68a8b0e8698c6f76548524c6963a2a4292635a1c152149318f6e0b20a498c7870590524c61fba2c0292630f1d16014931cc8a4b0e8498c7a70995424c63cb84caa12631edc165109318f0e0b288498e1f5458c424c70e2a2c6212639358f5210931c9ac62908498e2c64d49324c716320a4992639914b614c931cd6a43026498e6852181324c70e2a2c7a0a639998852cc5318f6eca80a098d3874540504c6b4392a0282630fdd16214131878e8b10a098e5a63583540c73930ac1aa063961cd60d5031a74e1aa4a818d3a70d91540c61fbb2a82a0631edc164948318f0e0b24a418c3f74582520c61e3a2c1290631bdd952148318f4e132e8418c7970997420c71aaa4c3a10631edc165508318f0e0b2a8418e1e5418d420c70eaa0c6a10638d9506150831c74a83028418e3954181420c733294c3990638755263904318baed29c6218c757694e310c733314a5188631d9cb654c4318e8ed2926218e6462949310c69d3a6a1280631edd9501403187ce9b02a790c3d74d8153c862fbb2a629e43875915314f21c3ac9318a790e2d6498853c863d386cb21e431e5c36590f21caca6b0c8790c7a7099543c863cb84caa1e43471d15350f21c3ecaa188790e1d6550c43c870eb24a61964387591530cb2196ee8b046390cb47458231c8726a98c498e433cdc1644c7219e0e0b226390c767694d31c8679386c818e433c5c3640c7218eaeda986390c3e7498e50c861eba4c7286431edd95014321b8ce5a9ca790dc672d4d53c865b3a6c0a9e432d5d36054f21d2ac9298a790c777654c53c866bbb2a629e43a55915314f21d4cc9310a790ea56498853c876329cc429e43b154e6214f219e4e1b2c8790cf170d9643c8673394cb21e43399c86590f21caccb29c8790ce67299543c8679384caa1e433c5c26550f219cce432a8790d947454d43c863b3a8c0a1e431d5d46050f219cce53288790ce67219443c866bbb28621e4365dd94310f21d2eeca188790e976550c43c874ab2a8621e43651c94310f21d2a86b108790cf37058843c8678382c421e43a550e6010f21d28c8a1e6590e976410e32c863abacc1196432ddd1608cb21968e8b046590e3765d9132c8679384c8996433c5c2644cb219e6e0b226590cf07059132c
  | 18 => 0x10c328baec21ca41951d75d0f420cb0eb2e87a10658d95261d0832c6aa930e841963654587420cb1aaa2c3a10658755263908328beeab1c841961d5458e420cb0fb288721065879536350832c3aa9b1a841961e5418d420cb0eaa0c6a1065279db4350832a3aeba1a841961f65d0d420cb1b2a6c2a10658d5536150832c6ca830a841963554185420cb1d2a6c0a10658e5536050832c74a8302841963954181420cb4da18c0a1065879516310832c3aa8b18841961d6510c420cb1b2a4c3990658d55261cc832c6ca8b0e641963554587320ca2fbb2a9990658799154cc832c3eecaa6641961c76553320cb8aaa4c399065c555161cc832c3aa9306641945d7694e320ca36bb4a7190650f9da544c832878ed2a2641943e76551320cb1b2a6c2990658d553614c832c6ca830a641963554185320cb1d2a6c0990658e553604c832c74a8302641963954181320cb0fba6ca99065871d3654c832c3ecbb22641945d75991320ca4f3a4c899065369c2644c832c3eca322641961d75191320ca2f3b6a89906587193544c832938ed2a2641951d75951320cb0fb2ca899065171d9544c832c38c8aa2641949c76551320cb0fb2aa89906587dd9544c832a3cecaa2641951c76551320cb0e3b2a899065071d9544c832c3aa9b12641961c64949320cb2bb2ec299065a5193614c832e2aa9b0a641965765185320cb4a320c299065c5550614c832cb6cbb02641969864d81320cb8caa6c09906587550604c832cb6ca302641969b64181320cb4c320c099065c6550604c832da6c230264196d061181320cb2daa0c099065a6950604c832cb2a8302641969954181320cb0caa0c0990658bdd3654c832c58e9b2a641962f65d91320cb17b28c8990658bd96544c832c5ecaaa2641968c64d8d320cb86aa4a699065719c6534c832ccecbb0a641966765185320cb52320c2990659ad97604c832cd6ca30264196a864181320cb65b18c099065b8184604c83287ee8b04a21943c74582510ca1ebb4a8288650fdd954144328eeeca88a21963a54980510cb1caa4c0288658e9516014432c72a8b00a21967151580510ca1fba2c3280650f1d1619403287aed2a0a01943f76550500cb1b2a4c2280658d5526114032c6ca8b08a01963554584500ca3dbb2a0280659c585501403287eecaa0a998e2d5458854cc733b8cc42a6639398d6215331ccee2b10a998e666258454cc61fba2c1296630f1d16094b318deeca90a598e2d6454852cc71aaa2c3a16631edc16550b318f0e0b2a8598e1e5418d42cc70eaa0c6a16639318e5250b31c98c6a928598e3654d8542cc733296c2a16638e9506050b31c72a83028598e6a5218142cc734a90c0a16639994961ccb31c5ac92906598e2d6454832cc63dbb2a0286631edc162952318f0e0b14a918c3f76550548c71caa2c02
  | 19 => 0x6a16a0995737150b504cab838a85a82655c9c732d4132ae2e3996a09953a74d87504ca9cba6c3a8265565cf61d4132ad2e5b0ea09963754986504cb1a2a4c3282658dd516194132c68a8b0ca09963664d46504cb1ab26a3282658d9905194132c6ac828ca09963a64d42504cb1cb26a1282659c9875094132ce2c3a84a09943e76d51504ca1f3b0a8a82658dd536154132c68a9b0aa09963754185504cb1a2a0c2a82651d9db5154132c6ec9a8aa09963464d45504ca3b3b0a2a82658dd905154132c68c828aa09947b76540504ca9dba2a0282654e1d15014132ae6e2a80a09957071540504ca1fba2c2282650f1d16114132c74cbaa0a09971b73d50504ca3cbb4a8282655c9c65414132ae2e32a0a09947b76550504cab9b8aa8282655c1c55414132c74ca2a0a09971973150504caad3ac8628265c6d524314132e30a9218a09971b5450c504cb8c2a28628265ca1533214132e36a9190a099718548c8504cb3932ea228265ccd535114132e60a9a88a09975243d44504cba8a1ea228265d48cb51141328f2ed288a09953a74944504ca9cba4a2282651edd95114132a76e8a88a09953874544504cb39328a228265ccd505114132e60a8288a09975243144504cba8a18a228265d8cc85114132ea464288a09955973990504caacb98c8282655a5c86414132ae4e2320a09957171190504caad39486282655adc94314132ad0e4a18a09971b7450c504cb8db228628265c61914314132e96e4a18a0995587250c504cba43928628265c650c4314132ae4e3b10a09957171d88504caad39e8428265565cf4214132e3287a10a09957271d08504cab8b8e8428265c690e42141328f6eca10a09955b73508504caac39a8428265c650d4214132ae6e2a10a09957071508504cab938e64282655c5c73214132ab6e9190a099559748c8504ca9dba264282654e1d13214132ae6e2990a099570714c8504ca9dba2c2282654e1d16114132ab6e6b08a09956b72584504caacb98c2282654d9c46395032a6ae231ca81951e73d82540ca9b388c12a0654d5c46095032c72c0304a81947671181540ca3ab88c0aa0654d9c66355032a6ae331aa81953a7098d540ca9cb84c6aa065479c06355032c38c7312a81961c63189540ca8f39cc2aa065471cd6155032a58e4b0aa81953b70585540ca9c382c2aa065479cf6055032a3ce7302a81951c73581540ca96392c0aa0654ddc56055032a68e2b02a81953671181540ca9ab88c0aa0658e580605503287eecaa0a81961e74597430cb0eb2ca9a18658755162d0c32c3aa9306861962d5458a430cb0fb2a8621865875954310c32c5ca8b10861951d75990430cb0eb2cc821865475d65410c328beecaa0861961e64550430ca8fbb2a82186587dd95410c328beeab10861961d54588430ca6c382c421865875526
  | 20 => 0x261582544cb38b0ac12a26595d8f6155132caec630aa89966762185544cb2db1ec0aa2659cd876055132ce0c3b02a89965b63181544cb35b10c0aa2659cd846055132ce0c2302a89943f76550544ca9bb8aa82a2654d1c55415132a76e0aa0a89953870550544ca9b38cc82a2654d5c66415132a74e1320a89953970990544ca9b38ec42a2654d5c76215132a6ee2b10a89953471588544ca9db82c42a2654e1c16215132a3ae7b08a89952d72d84544ca8eb98c22a265475cf6015132a3ae6300a89952d72180544ca9b388c02a2654d5c46015132c58a9316869961f74996434cb0f32ea921a65569c25490d32c38a9314869962f54189434ca8f3aec8a1a65569c25450d328bcec2a2869951e76151434cb0f3b0a8a1a65479c05450d32c38a931e849961c5458f424ca3b3acc3a12658dd5261d0932c68a930e849947475587424cb1baa2c3a12658d15161d0932a3ceb21c849961f5418d424cb0e2a0c6a1265871954350932c6ea930e649963454987324cb1baa2c3992658d15161cc932ab4e12a4649961d64152324cb0ebb0a9192655c9c254d4532ae2e12a6a29957370553514cab8382a9a8a65c55cc54d4532aaceb21ea2997145490f514cb8a2a287a8a65c515232d4532aaae6326a29956572193514cb8aa1887a8a651d5db42d45328eeeca16a2995577350b514caaa39a85a8a654d9d360d4532a6ae9b06a29955573d83514cab2b96c1a8a658d9935194532c6ac9a8ca29963b54982514cb1c2a4c128a659cd466094532c76a8b04a29963854582514cb39a8ac128a650f9db545453287cec2a2a29963b54d81514cb1c2a6c0a8a658ed506054532c70a8302a29947776544514ca9bba2a228a654d1d15114532ae6e0a88a29957070544514ca1fba2c028a650f1d16014532c6ccbaa0a29947576950514cab9384a828a655c5c254145328eeecaa0a29957370550514cab8382a828a658d9945414532e2ae62a0a2995567590c514cb8a2a48628a65c51514314532e48a9990a299714548c8514caaab98c828a6559dc94314532ac8e4a18a2997154310c514ca3abb68428a651ddd94214532aaee6a10a29955473508514ca9bba26428a654d1d13214532a6ee8b00a29953474580514caabb9ac028a6559dc96014532aaae6300a29947671993504ca3ab8cc9a82655c9c654d4132ae2e32a6a09957371553504cab838aa9a8265c65cc54d4132ab4eb21ea0997185490f504cb8c2a287a8265c615232d4132e66a9a8ea09973054d47504ca9d3a4a3a82654e5d251d4132a76e8a8ea09953874547504cb99aa0a3a8265cc15051d4132ae4e3326a09957171993504caacb98c9a8265c650c43d4132a74e9b16a09953974d8b504cab938ec5a82655c5c762d4132ae4e3a16a09957171d0b504ca3dbb285a826556dcd42d4132ab0e
  | 21 => 0xf87b9286a9087471c94354843e18e4a1aa421f1543d855210f8aa18c2a9087c650f6054843ce6c3b02a421e7061d815210f0ea18c0a9087c650c6054843ce6c2302a421e70611815210f2d218c0a90879650c6054843c3286302a421c9f7650c5210e37bb2a42908727dd943d4443d1a87316a221e8d4358b5110eb3396a32888727dd943144438eeeca88a221c9f7650f5010f0fbb28728087871d94394043a38e4a1ca021f1b7050e5010f8c38287280878750d62940438eee2b14a021c747158a5010e37b92c3280871b1c961940438ece3b12a021c7571d895010e4fbb28628087a350e6214043d1a86b10a021e95439845010f4aa1ac2280871edd95014043a74e1aa4a9994767118154cca3ab88c0aa6650fdd95415332ccac5308a99958d72d5143ccacd386a8a1e65179d85450f3293cec2a2879951e7615143ccb0f3b0a8a1e65c35c85450f32e2ce22a287997157115143cca8f380a8a1e65871506250f32d1a86b10879943f7458251cca1e3a2c128e655c9c35494732ae2e1aa4a3995577550e51ccb8a2a28728e65559cc6494732ae4e0324a3995717019251cca9b3a0c728e654d5d06394732ae4e031ca3995717018e51ccb8aa188728e65599c84394732acae421ca39953674d8a51cca9aba6c528e655c9c36294732ae2e1b14a39947576d0a51cca9bba2c128e654d1d16094732aa8e6b04a3995677258251cca9b3a0c128e654d5d06094732aace6304a3996716018251cca3b3b6a8a8e655c9c35454732ae2e1aa2a3994767615151ccaabbaa86a8e65c51514354732aace7322a3995677259151cca9b3a4c6a8e654d5d26354732e2a8621aa3995377458951cca9a3a2c4a8e655cdc16254732ae0e0b12a39947676d0951cca9bba2c0a8e654d1d16054732aa8e6b02a3995677258151ccb38b00c0a8e651ddd95114732c6cc928ea1996356494750ccb1b322a3a86658d59151d4332a74e9a84a19961e6450e50cca3b388c8a86651d5c464543328eaed288a1994777654450cca3dbb2a0286651d9c660d52328eae3306a91943f76550548ca2ebb6a821c65275db5410e32b1ce5aa0871951d76d50438cb0ebb6a821c65c39cb5410e32b1ce42a0871961f54588438ca6c382c421c6587d526010e32938e8b2e651951f74597328cb0e326a9994658799154cca32caacb30e651965565587328cb32b2cc3994659959561cca328eeeca88a31956472586508cb2bb9ac328465951cd6194232ccee4b0ca11966472586508ca3dbb2a0284651d9c660d51328eae3306a89953671d8b544ca9ab8ec5aa2654e9c362d5132a72e1b16a8995377158b544ca9a38ac5aa2654d9c660d5132a6ae3306a89951f73583544cb1baa4c32a2658dd516195132c76a9304a89963b54582544cb2cb1cc12a2659c9866095132ce2c3304a89967
  | 22 => 0x1003800801000b0030000010006000000000c001000804800a0010118000002001000803800400100000040000040040000000002000002c0060020000028030000000000800c0000000040008000000802000400000b00080000020000000000003003800c00400000000040040010010000002002001800000001a00080080020040010004000003001803402a00100080080020000010004000002003000002000d002000801e006002001000a0050000000010000000801400a00f001001800000400080000040090018008014002000000004000000b000000c00000300000020000008000018001002000800600f000800001c0000008000002025001800000000d000800000400b00000000440050000008002009008804000400500080140080040060004010007000000001c00200180000040010010000036004000001c0060020048004000000002000c002000000000400200100080000000010018028002009000004000000d000001800400d000006c0000000020024000001000802c0000010020020002002000801000000a0000004002001002000c0000010000000000000001003000200f00c8008004007000800800601100000080000020010008014000000000c00000200080240011d9c66094a438eae3304a521d2e72d0d5290e37bb2a4294871ddd95114643ce2a2b00a321c777158a5090e3a38ac5284871d9c762542438eae3b12a121c7b765405090f38b0aa0284871bdd95214943ac8e2a90a4a1d68705485250e96b9486292871ddc560149438e8e2b00a4a1c77765445150eb2392a228a875c1c151145438dee4b00a2a1c6c725805150e3bb8ac5a82871d1c562d41439c8e4b08a0a1c7b765405050eb4392a0282875c1c550141438eee2b10a0a1c74715885050e3b394c2282871bdc961141438d8e4b08a0a1d64725845050f2bb9ac228287951cd6114143ccee4b08a0a1c74725845050f32392c228287191c961141438baed2a48621e1d75d954310e4f396caa1887879db6550c43a3ae5b2a8621d1e70d954310ecb38ec4a1887655c76250c43a3aeb3128621d1f755894310ecbb8ac4a1887651c56250c43b36e0b128621d98705894310f0eba8c4a1887475d66150c43a3eeab0a8621d8f725854310ec6392c2a188766dc16150c43b30e0b0a8621e95611854310e8ebacc0a188747dd56050c43b1ee4b028621d8c725814310ecbb8ac0a1887651c56050c43b2ce23028621d95711814310f4cb00c0a188727dd943d4843d2a8730ea421e95435875210e4e3b28729087631c94394843acce3a94a421c76719825210e3ab8cc129087271d94354843b18e4a1aa421e9543d855210f4aa18c2a9087a650f6054843d3286302a421d4e7290d5210ea639286a908787dd94354843a38eca1aa421e1c7650d5210
  | 23 => 0xc000000800c00a001000000000c000000002c002003000003800a00b000002800600000080040060000008010000006000800800c00000400080000050008014004003000000000800c00300040000000050008000000004800400200a000000400200100000100060070030000000000000001000800400100000000070010000000000001001001000200080000060050008000002008000802000200d0010054006002002801c00a0000008008008000001000c006001003001800000000200040000010060000000001000801002002000a000000a008000000000a00500000680000010078000004000003000c02600000280000020010000010008000000001c002002001000c00200f000800800a0030010000000000009000c0060010000000014001000002400600100000240000010008004014000000800000400100b800c0120040000040018000000000000000600600080000000010004000002000801c00a003000800801a000004000c00600100100000000000000000002004007800c00c00200380000180000008008002004009000000600200000340040010000000000001000000800401500680000000000000078004004004007c00c004000001800400600000080160110018004000006002000000200600300200000000018000002002000000000800100800000160000008020000001002801c0020000000004004002001002c0000020010000006002000000400000100400000040020038000000000003000000600b0020004004049000800c0060040030024002004000000800000900180000060000018000004005000800800600a0000008008000001000001a0010018010028006000000800000500100000020000008024002000000000000a00100080140040070020018006000000000000000a00180000080060038000018000005001c00a002005802800000000000180080020008030000005000001c00000100000280080020000018018017000800001200c0010000024001000000801a0020008078018001002800400600f00300040000000028004004000000001000200500000240020030008014002004006800c0000020040004020000003000001200200080040280060008004006000000000801c004002006002a0060008000004003005000000c0000000000000000000000c016005000001c00a0060110000000000001000800a001001800400200100000040020030000048000003008800000000c0008028016006000000c00800000e0000008000002800400600f0050004002005003000002e000000800000001500a800c0040130010000006003000800400a005007000400000600200080000000000000008000003800000200700280040020000008010002000000800000200
  | 24 => 0x6e8c570cac98000529e383028f9e269603010307676946a92ad8e2acb6b1800074a00067680003886db1b5a4357aebc85d0a67cf004c83f48bb8cb4483dec800000000011e000000059674b2c814d60000001e5d4ba00061d0000cbc03800000006c100071317440000004608000b26ce16f8a3250920000d500010a8ab7667b4a0d48061000385067c7da63ab943482738121b26000000016b04e0000d400a349109100000000000988000008401a005001000c02400d0000000002000000800400000d00180000060000018004004000000800000a000000800800200200600000160000058010002002005000401e00100400000060000000024000000001804c000000000001000000e000800802e00200300140040010028008006006002000c0080050030000002000000003000a0340000008004000000801c0100000008000010004000000000400000080000000000030038000014009800000400c000801000200300000200040000030004000007003004000400500d801001200000e80000040000058000010001000000000000300100000040030000004008007000000c0020030008004002000006800000200900200140020010000030022001002801c00800300200100060010028040004000004800000a0140050004000003013800001800000100240020000008038000002000000800a0040038000012001000803c02000100700100580000000000010008000800000e001000001400200c0008004000003000000000000200280c4000000000000400a00100000080000000030004002000002000000400000100500180040000010010001000000c00001200100000000050008008008003002801c0080010018000002000000801000000b000800400400400400080060030018010002001000000800200100f00040000000018040004006000803000a000005000802600300200040000010000000010004001802000000b003000800c0050008004000018000800400000500080000000020000020006001000000800000000000080000030038010002000000000c00c00500580480000000008008000007000800c000000005800001c0090030010002001000001c00c0030008000016000000800000000000100100020010000044012001008800800000f0020008006000000000400400300100000040050030000004003000000800e00500180080000010040000006000005800400200e0088000000009002002800200e00000080000270008000006006002001002c0000000004000004000000000a000009000800800300000080000050000000004002002000800c004001800000000a0040008000002005803804a0010010010020001002000000000000000000040000000008000000000801400200100000
  | 25 => 0x1bd44400000000b8c00000016e351481e00000033a857600053d0ead2f7c38714b2999fa00000009c80000003e7e01c66a4af51f909c56cb8290aaee4000000000000184a000000030bb9c92e5cfa09532a42cc06c0015f264849c7024000ca109800016179dd1048c20b160005dd9b1cb6a000000092e33b27033a065aabc429513068cec044ab1bb708a88e0b013dd547b010e499f62c3aad4f496050cffa2980002d61c98c3ca028000000a17051054ef60ae800019fd12e6270002971508ae558c125800044c4c720f84a9dbc0649a4187c5ef00004e57fc3684c33ab840a6210190000000000375000089367b50714280000f212e0000000cff00000006426241d880005a0c786e40001aba3aa0f41fedcf45e21032fad6e89036875950a029a553ba967bb2c391a5c48e000d770000000000c4cf122e4d352000000194c00000000000012913075e4a2b9b8e0680002e340000006ef03860000001dd44a2bf4a7100000c400041966e0cbd14a000000000194eb9e259400000014b0003162000d686170001b5640e0002241b348cf000000079272832c4fe415ecc31261e915b80005e38000d00e9743281ec4c60004c8a3f0c920ba000076d544cbc0000000f0800034a3749bda0002dc0c4800000000000018080004bb00000ec0000a803d522e0000001b742b600039d800000032b0000000312b840000ad452c00066c390850286c000000000060857e9ad400076400007b1166525df829b117cb791fa16de63a0005952a583ce0005f6294064edc66fb04dcf6833f4138e0477605e104ccd11160006a300018f40000e52cf8000be80621246f8cdfc5da91f8c729c0000000125392c9c486dcbbe29f22b091a42217000000000007c90000568000000743000073aeac1ce013246dd614aea2a936600044a23d961e84702d8000d428df000000032c000271aa746fe8703b310d834ae102240fe85f643f00010e11da00056f94b26a84d942d905048cc8a80029d80000b20000e800000230000000e2a0003e0ae4a000000000000091e6f40001ac018e6a237ba56dbc20007450000b22e5c0000e6c7e3dca70996a086275207f20646b444630108980000a800037e052b0000000e1489cc030aa93a80000000000000a940001c80000000000000000060400043b333800000016c00000000000002981b0800059c48dc3f84755350000a0602420e1d65d1c000000000006f32aa669e3ce0c0003ea2d6566a00033284bcffe54f20600004ccea01568045b7345d4b231a41c0a5627439e424a8ab3e602cb52e4dc408b0b0bfa72433813aa00000068e8000685a1d0b31d898c5e572860839a4a00000036bc00011a00009d400000031d00000000000000a795e67ee00028edaca000000134749a9f23d8c0009442c200012da19ddf267323cc1
  | 26 => 0x6dc4ad413000114200004f16e236c5a46c9a8900001fb00013b00000744ed80017c20000001dea0000000002b7588e00000000000d7926610049f3aeacc65f000000050d00000000003624bc4000000857472c0013f106455d95d000002e88811ce00000000000009590000272378282aa062c8291a6c00000024cc0003862aa9ee5a940002ab260c0003c65b000017bac26cdcafd0d700b9bbe6f281ec6be8eb9abc13266439e2c640008a6080a05161843d13fa98c6549bc1ccd145010a910449024d7600032a824a50477b000000196ab810000000e166ac22e250b3fee78103a8dcead02c5139bf94feb2b4179ca95ac00042d20c56e4e6d00000000cb00005e800012ab340003469d128c036200000003a40000000fd4e544e3c00000087120075b0b780000000001cea00063400000002380000000000000000030c00000025c400000000000026a0774000000047869bcbf00008940004cc58da04c000000000000000000023a40000006e5000000000054e08380018b400000000000000000ee9c1400076e1ea98ba0002b1583000110a7394ce9c5831e867d0c972c9ec9004d188ae69c3320aea6baeecc5d13c38600000004cba3606167b235e0000000406000000000000050d89e4b0600000000000c7d2f6660960e863fc00000000cc4c126a8070aa600000000000003ff735000000011d64480005e20000c810925d452f2c3177000001932b0001214374074a5b964626257fb16f8782d412083146222e90000001c10a4a0000001202518000120c582000000231800000010407b40001fa0002dd40000000274000000000000000000000000036d8000594196c094239ca26ddb45ccc0e64609800125656c0003a9d80ec9d1ac0000d749c14bcf204bfb00000000000000000002c28000248065c0000000001d380010d04045168e840009c1bc2c00111c54300003944208ef2300000000000249d4dc000d0600012eed8a5728003254fc4b1300036799903065f503cd7e498766ca5301c82ec3471a04c7ed7a3c49660000bbc3fe088477b68f4273602ba47220001c313ad63524c0000000e0c000000000000000b60f5c54000225c00000082b0002fec2f6dcb571a51d184000302c0003fab011b01cc40000007119f44000bd58cd92c5020c214bf141d82c00009db355a60000147000066eac7b238000f020004a88001263c8200000ddb2404b8002879cb4000238c001a5a0b400000000000003d29d51d0ad3d534c00000057338f800072400064606e18304701f480019bc7856b38e65c7a55b2cc8afd6da7e4407aaf162c00000030888f05cd365a7c0c9c8721be07e40000006d12678d4a0006e1807aa0a5f610200000004950002c9c00000000016c4000000000000146656971d0000000cdd10e1d342f087f00000005363480
  | 27 => 0x1e8853801a51f04d096f429ad50927d4cc9925c29f6bd480a6bfb0b7946c5480027a0c5e0001f380011a45c200000000000000000000842000000305400020100035780005bf2068001cd053300000000001c90001760d062f80001c24000afc000077dae80003d1c2a8b340dd1239c1d9642a5017379983adc53ae9cc85018530000000000c7c0c434e5ca3000000000052800073f905422bda953902f2000000425800139a48c0990000424d6200030d93620006000000000109000000000021942f9ca40000000000000000d8edb59e59326000000031200000061a80003b88b6118a67041a06500038807904c95d9000000057a3919210ba8eb40000001c24570654500000089a4b62290000e5614bb44800000000000000000004b58fdc0003e8737965d5e40d70e803338fa32c3b8b8d524242f0000001be80003b2800187a00013b40000007995b22230218d29000000174c481000000066000000000008e200022cd7120f4e95800245926b0000002d6c000000000236d8fe197000028f81ee095582cfd2400003fc1945bfac5775b400000069a48c86d58fc0003c50974f340000000a8c1a28e66afa7bc000000000000017c113e1b8000c1cd581491d01086c50686f0b5c44000522b3acf33b781f00d1c67f00000000017520000ff0001620ac46308000efa3f3301800003000000000000007be658a78c0000fc800000000000061200000004a6512a7a896063024ba578fe40000000000588dd00000001be63bea958a5ed1689552da93c8b0b623a885249e0b32150929cee5e300f31874a8a448ae2b41d26c42c240327d5d204d5821fa124f4da00026e11e8d0b2f88680000000000183400000000002400000005b614f03b200000000000000000000ca4a760002495b5d5a29150000e6a000000000381429cb2e3632a206b5c1b303ab8880ea0d02440004ca431d172f386aa57211532440008a8000000030600000035fa000c5127200009d27e730903b80006ae0000000000af3f3000011060004ea85f014261a00031888eb00000024bf41801600000340009df305224c96800000010b4000ca78001ea80005a65ce04e2000c970001178bd85b90bd40000000006ee8c248d2aed19d2c684b68524477119924000000000188b4de0002ae80000002960000fe05662910001262aa700001ea00028514995a18200000001ee80002f70001ea190e5e65ef8000000000044c0002146a800000019a40ab4be0000489000000255c000000614b19400000015f2ddd8cd00062019b0000d0f5552200fac00054c000000093a8fc0be800083600031ac00021d11480014fc1583ce943c000bcdaed8001486003466800000000aed28000000ac868480007460000000000dc879027e97d16ce64f00002365128b700018c52c051100038e5
  | 28 => 0x80000000000000c2ea130000000000cc600015e43143f100002c6e56d752d72c14af856a0f4adbd470cad00025217b827167a892538412b86f14fc6c853e3b40d8c0beb9033a90da00032b8001f6dbb6834136800002aabe1510f5c21e74400010120000004d6b87151e44c90d260f14ece0637a26110e8e224908bc3ca575e143ae09482220280b7595062d3450000000000011098a97900013220e000000054600008960006c6713d56200016a9a2659c0003a580000007910ef36720004e200033c92f018431d80002daad05be89f541ec7b2a091b197000000034907da906701a6840b83b8b1919a13300000003965566000007024e7b25e00c9b8b43166c24f632406ca90e55a6aa43d638e689b92cf1a4c25bf3a487346720d0a6f60007ed0000c600000006c9c040000aac71700003cbc5648a000000000068d8d3a00000000024fcb887f9000000047d1e324f8e76056b664b1a92d26a8796d50bc0e9009b5f68f04b6cb541b3b304443ca40000ac8cfa828078423c9ae00047e92ea945baa000000071800071422d00000002c68000000988baf37b00006b905b7a09ad200000005f4ab000000009bc0000ec3fa0000000d3e00037342620004fa000046636c44fa2440009a7000104d1b50002310c354066ab00000000000002a3196d8c676f54023f88d44f75d740000000000002075ce46525858bf9d42b40155b8180009eb18a8d639b40d9b00322d50a28300019000000000000001af60000ab1d1ca4866760f9595234214717803da06de44a7b6d16e53e5d3728548ae00000001100004adc939bbc00061e4a4b0148c1bb108037885544400000001104bd1461853d52b42306a9c680002c5164b6084395cc1cc000166c00042a80014123dd206c001404b8b146afb8bc6984ac62a194ca58e4580000daa79e00005306e09fc07797c1374663b0d96a543e8c83e92f0c6f49396548050b3ac5f22d06716c635146e4000000000319a859146000000035224970f6ec0b797f000000000000008b90000f1c7b892f33cae90000c644d5b3a131bdba00025fc0004346a98000000b480001f2d0171bb3852cdd2b206d00000000000341e1dba40c6000000188dc820e32690000000000000000158200000000015f3b220001d3064a0000003068000d9f8002f6996ed9d4d70f9000094a4e90fa80001be5448be4000181853cc32000e3802e80018244b09194ce174a000000000000020080022120000000000000a0078b0001f0d34934895d1075bc3abf0001b3907e52d10340017c00007358001a5cead0000fd80000000000000000afe5ff8e597f400000000000000000003a0c00063c0002478000c347578c700000003be0000000479000000011a000664970c000b3c6b5a9507fc0000000c7d0780010000000f04e470002ef4f71120
  | 29 => 0x156100000007006400ef59a2943000000000000012ac00000023a8000abc000df56570084000000088aa40000c70ae338041cc97303ca5c8000c8300000000000000002d149731482154000c582fc1a30000d6c150eca134559c0000000000000a1100000008b2d5200034214a2000290800000096723723c400030c57a538000045208986745b68f929285e8620af0242a0b86519d81a219ac2dc24f62f769d7e6b75c1827b81c5129e25afe41abc52c741f1c5a2245efd846d254cfc0000f7ce82b1570786505279878002d7554abc2217c0008a8000000000000096608b80000006bff4800006e6e7d4000001ae617945925a400098962100b40004b96a48000b4228c31492380000001e9ba9429d0002bf0d4c3680a05cb26b0000cfa70b18e129a033f2d837147a71d2e3b1927649741c0000000009d420d07c18c9af1450000000d88447ad1d5384f8411a100000238f479d701e0c3f379919cc8caa63ab0188ea651653ab481b7cd957548d7822800019e36340000004f300000000001cb800000057700000011b20000000000000000000382800000028e0001434000000000000019800000003b4c4c00000011a60006e48922000080026016005e00049e000073d5ac44d8000000000511a9193c48c74f880009e2943800293183800001c4f3c0006e727f800182e11200012517eed19000020c000da100013980000000abe9c7919e9a1de60c84e9000000000029b31620d06440000000002758a043bf0001c402e6be400000000005950000000000aee295f458b806203d94269d6cdfa6ab8f1bab80572e79f70b0e923646800015ce7111a800000000048e096493aba700000006e28895d180013048d66c7000000098d3891d38000c0d6bb00000000000000e45d50d2b20b4001846b8c060936c266a61251979468a662b6887804f1d0217a80000e495a0000c91c0e153277262d28103663690b6dbc68eeb5117b60000006b2641837c6a2fb400145656d00000003340000001a186b700000000018d83004948bc800000035191ed694c320e9327800014070e80000000000000000f700001eb2da5b7a2ed4fb2380000000000000000087502ac1fc00001b00021bc0000000002f940004182a41a65d280000000000000e8000032f49be0004fea158fab57f0001b8965e1a2581ad844590db00000007a83e236f80004a21c574f06e40000006efb196b3c0001be40000009b000009394cc0000000fd5c76a7b000239e00085d56f000000000000003b498cbc40000000210e5152993e589c6d9235b29bb209ca0b5a0607a297a50201b98e70000000000000a68396a5dc000b8924f2081580000000173a77f494b4607607fa2e00a3d5c4000b1e5eab2589e4eb02b38000a285b35a223dcdf4a3a0bf95455260006198a10ee800002b39d
  | 30 => 0x5d84cdb06b3000075fb250000000000b1d052894c4e89843a940000000000001b04789000645c0000000005cd000103c00000006e8024000039800020c00028eb1cc0000000001a060000000002e541a02500a9000026c00051604b972ed83e4d37680fc0006253540000af839328a88d989c755105d3fcccd3979a5cea077074d86c4a7011c6eb800031d35723d0ca0f9a0976cf40010bceb2091175540eab400004f93e637e000000170c000000061cda0ae613e31a6000000000000140000000007bd6e60000000000e6a69c0000e79bfc0005a08d6d5f50000000000000aab194c0000003b70000d840665f500014d10c46d40654000bdacb037e000083c5d3716273889ebb88058014b9c7de62bc11c00000008680003320000000001c8a00044226ec00000000018aa000a3200039612b83ee202ee1cae7e870000e98e8ab7f00034610441642f4ae151a006c56526f85fe00026e9cf99de000000133da08d8936425606a58e713380000000006390000000e880003220e6e0000000c12fb136c80030ac2d80bf0691bc0000a0dc5c00017963ca6edc0000002e74bc8000f80c4322225ec9b00fb255393427e0000001a9c00095f156338c00000021129680000000000d0cd080000001dcc0941d1000033e0000e70002d406d20001b32f9d2840002fe0000d6ecf72212e5e5ded990000a748ee00054d8001c90463000000154637d3db07d40004cb00003280000001630001b0e000751800000000000000019dc38300011fc0124996aa34e9066db1000080c0000f80685c05a88bd831585d86b3a8b0758000a20dc105180000005f8514019cfec77980000012e00004cda3709a0000193000092060651a83093c769e5983699849461c58a731b881bd0c100010121009ba674c66c85c0001c450484348931099692000000210800062e1fc0d740000648000000e2e1bc00000018f20000001b68ed40000e98000000213000306a000000000000000066a42880000009242fd80000000000000000768d55430b7e5a3eb090499124f400dd80fc7c80009dc53a0a40ec7d5a587232ceea00002aade8000a9bb77309c0003131ba8410000000000000138e93d9010cb81f22cb000027ce600006e9b1141903e1293d403d6a6d300037bcfa953d6b20fbc21650454f3adc000000000000000000040542440000002e4a8c47530004cb0b200000000002da000066f00000000000004860c8105b0004d0000106ead86f580008200000000000000e6e259c0000000006b700000000000000000c507920001de5d184ef64e000007400073b85a5d08b330a69f94f423bb8c635453285e84fa80018cc81f249af48f94c4dc945608dcf3c0496ace00a615c62876d3d4400001456809ea2284d300000005188a8846bce80001a533585720000f22f4a0000b
  | 31 => 0xc2950c36e7e7b74b6c00122612f97a2160474d856a399a4000526ac203175ee18d0248f0d8e8e0d69c35042e8ab873e39400b4d8c1058d651c65804c53600fe604f00000000831b3000000050e5600002ec11887bd41d000179addc3d1ac8400040b2010dbc1b08d465a11f19c4da000000008c242442429b40007fe5569e4ce9269533f18600005da6d40f49ac00003220001aff7c535315902c00006628e3af7ed3237b00002fb03d25f3120856af6710b8688745080c28e1dd62ab64e32c2176e353a390001364000000087ce06bb30001a534f01240240000f4506a569a5880000003d314c43e80c680000009da119000158ca800082c48233208e6633994a01ffc415472710728376003119888ead502ca6d717871825700000000c18002f04f101ff71a2fc5658a0b543939c00003957510440000004ea2ee109e4a535500000000fc2918a2ccec000081800000000000000000007ad48907b80000000000000be64798002a092ca0000741c800001d4000000000011800009d9c6478c0b8b65caedcf3712aebda90c0e30ca949af0645000000000000013500000002c01afc0011c80d6e08800000083fa5b39a5892000638c00049a00015eba52000a41800000000000047f800000000000000003ec00006703e8c3800fed600000000004c280ecfa022727f2c7c00042825906180140000000b4999675f000000065ae330000de42b293b5a924df700515000000000071e18d0001c7c000672800175338b6a60000cbe2b82ae00748ec151a51c0006280000001e500a2200254a74419842a7248f112d400026180010da0ea00028616766e30985f38000a55093a2880000000000000000a9c8001720000cfe64a263c0000000668fec71400060a00004f57af02140004c0df03938e2600066abb38001baacc00000000102000000000171c6dc0000000a92b4f0e38d3d56400071fafd8204caf0210001b14acf2448000e7a000000000071ea9a59698d1afa71c16d34c4529aeb0f80e4c000298c9c313a8bf42eddd000130500000000000000131e70000176000000000000076131b0690c8655f3eb878800057821e323ca299bd6dc81bd110af162c00013c2000358ab8400000000016d00003950002ed000000063bae489f600000015742de23900012d6e6868568000019ecd91738000000000000000000000000580f08e4a8660601b0c0cd0000381f9902eb5c0000bac0549d5a4693cd2dab650d806540000000e6a52c000d1e731000140a827b49ae600006b3000000136c79f00000000000001edae800000002de8000e9e87b662241c698166c941f0a98ea103049a1dcba977edbb94c6820007188001a285b73ad80001ee0002970000876aaf0000001a4400000022bdb5c0000000908000000000179c5000002ee8c1400000000023
  | 32 => 0x6f232600000000006b6800000000009fc00145e75a43d0de011f0000d4000000060f06ca2748f593ef2f08ce684a143730412a360000d705780d28fb0e6360ca16183972a8888da0000000001b6a1f31c6800157200000008295d86131156eac34e9e700023e80000000bf40016d495014b4001d321545df80006324b540aa02d936c5b2df07dc000b5f2e7c9f923ac4d38dac70d6800ba32f4dc8aac84000088323068968e0000000009800000123e03f3209478000c0c116800000035c1f830bd1400006960000fbe2566451aa4000d9dbd62ff5ae0934b4b10b82e445f0001f10417bf50bf0001674000180800000000004639cda7600000000000007bb000000176ce554371898758dc009357799f000000000018c00000001b0028893a563b9ec90e000558c0f11bf1153ee987cc280000003a90ec59564c91bfc8de1af1ed36fd7bc295445164975ad6f4a90822fd83b01160001ba8a9409eb110934b8a0002d5800000062e0000a7466d05240000c01570b28214d2411670bb90cb1471422dd82c38c5a7495d1df628b023f015d569821ddeb17410527861c120b0000daebbc2ff0eddd4b32d77a54148054e40000000a12000000000052654f8000384000000011800000043c15f400000071b800000076c80000000007135632b252828ce2ce3918ac4b2840625c73ca2181912e5126e53517304d430244320d9704a26a29000109b17ac012560485c4e7c86d98000cb809c3a12f6c00077e0003559c6c425c88800000097537d800000002966f8aa41961750a3155c76f000000000000000000016940000005bb356c49672e4aa0d40c7c37200004820001ac0e58000000cac475968800056173189ec00000000000000000001f5a2b5d3a682755a0186ee5ba0bb9e9c254000000000133d4bc56295b80000004d040000006a0331b794000ba2665000000050e000095cb560005f480000003040000aa00390bc5e021cc1910b34019dc98544c042fee0396c8e11dc0db40002078039f612d0a3400026694920001710000000e400960000110000685053243cd343dbc86c63c68f939b97d798671120d51db5a04b000000000000047622d400000000008fc000cd70000000000a86d49334db1e0000000000237000522046702c00000000013b40002198f957101b20e714482d400069332e4000ada2a6a9640006cc50415506a41ad54ca42014e84d40100000006910000000a96000000000000000024e379cf6234a80002100000001440000864000438f7a854842004a33b14804bd26b000000000000037446d40a8dc8a4151f057614cb214646a6f5f78b652835500001191b630351580d1b6a2c6eae2f43169aa04c9b400049508a33d17f8000c6f80000015147ae4318001264000022b83906a3c505a97ac00098000000000006
  | 33 => 0x18d8000000e4f15a26dd52a00028c8001a2a441000219c6f63cd0003308dd68cc0000ea157a4bb5310368b7607d1b70b8400076dc9eba44dc0be62d68b4c2c642beac9ef0cba078056848783cd2100019284b40002d18a80d7a8dec812df029f05211712810882360003154fc2000000000000000006a03fc0008ac3909492000ad40000001a026773c1b78d5fd0005bdb24c0009a6ce583c538abe23b9c9003803de26a36c80000003bbac44000d4e19c8a9c37e0006bcad5d2688017409b60eeb94648811410e8b5e11ada6ceb0e4a70da3744d89aa39d00014bc0004ec891e00000018b9e38000e955240d52dac6bf30801ee2ce00011926d40008bb4fc80000004d3f2904b4000000647000000024a07e8508cae66e063e345b0caef0413341b30a16b760001bbf0000e42f3ad7c6e163b0000df00000000000a40a675d414e42c40002ffad1994082a3fd30c420754c6e78a984dc486026d894a1230a59ca8c074401e37e800095f0000000b3c00061608f82ef08c41200007591d20000c938b3a546980e1815b2aa3d01f18258000331241097977c000426000000034900000000000005f1800000034b22681000001ab0000000ca0e4e4069bc4000bd30000001b3e00033092e800076c4c2d5edb480006b9258400076d407000000000025f883dc564ec8001c34476000570051cfe20005a582180007193dab5f83d40cf0e780009ca0002a113299e000000000016b4000165269002e2681d724030d240340da6d09a651a4f49604000e110d480000006584282f3c00040a0138000000000356ba2c00053000001d469f93e0000000c0265970f821c957054095b36c61cb2405301c400087080009504465ee091834c158258f4e0000e045f700027926acaf452c00000000000001c204605065988a44000acd19e9e82a6441633129a55c8a8d21a8000000bc0a1f0000ec158840e2e0c00043000017657a10000002bd400056b0000000efe15f00000001c279b65297595500006180a6911a00030280008b606aa488000000ae756b8000008000117e781244000000388f042000435800027d1285344e21bdc8ba5c79d280001680002e430b28ee1de27ed548e9348d9e5476a39f36680002a521612293859f2e9f0458f98f66b173590414e580005ea0001beea0669180000000003870001bb300055080000008040000acc000a8152713f0000000000000044800029440000002e851cc0000000000002724000b4e2a902e0000d1134f8008fc627a023e4c000000070228d8b1e7ab00001acc22000000000000044a4e80001024b0d6058000000000172000000063d00dc2d800048b688250031c7f743212cc4684a12f90000000005cf6800047a34d37c8000ab40002758d000000002c831b90c0012b6901f14be0005c1003155c0000000
  | 34 => 0x99c5d7440800000000000000004614dad009b3c0004730001615bac00000016c8000b710c00000000c860000f2c00000000026300001958003a6000000033c000004cd273c3800156a2ae09554d800077a00005840000000100000000000262b43461e47d0000000000896000007c00000060119f052300000029cd1e0c0827d2eb0000a8321b931e124a06ccc8a3d39e56f62f010d0e7e6753e98111322614c4339d885000487ad551ca2864790000000000000350d9e2b074b880000009e439b2f414b1000420b8785860001b3c0014e57633fa8000a3ea470000000bf2e0034ea70db0f0001f634ccb5ebae11f0000000000346800058e00000019340000000001d180006c91c226040000000000000fdd1e13a9f5080008da61d837d9d2db800028851d447400000014aec524ef1004000cf415e0adc7e400047a800000002800000000000003f788305e6234d2d6d0dbc000000008ee00000000000004aaa3c31138540000003e137a14f20deca282e41e800000020b5a6a92ae3a53d0c54e650000000a2e0000001ccc278000213cc16000d8b80033500000003ce281676c00000000016e009841ca11578c4652e502d6382d7c56d8001b9800024512a10d40004d12510dd04686ffb438000eb319d80000008ca3b5867d13c9ac80004e8bc800016b80016a6e8d0000fdbb2c000000097cb60a420002f720001293ab8389b368770000001832e6c00000015f4b994beb2a973a00056938f0867b4206c592c000000701032600022b3210c0c000145000085d5b20000001020000c5329489498b30000a500008a6cfb0001c11652000730a494cc93330000000000bc50471f4c5980000f8800075aa7c65d8000000d4d0001a215869f717eb1ab0946ed01f069877200006be069472d9c45fb68d1247eb4b792dc8c97a911ee7e800096fe2a0000000c675381114000d810000001ae28a972200005ec0770001b297369c6800079a8c700000025390fc0003ec82a46be3af3ea8000766cc769e254cc2acb3212a6974c849b13b949c59a87c6d9ec488723a94df8ef80003cc65d000000000043e9999cfc000655a7e000079850e339000059f2f08678000d3f5103414b36b3d16f8000082000000242c060559278c001212b70935abed10c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1320c821ac0825c06354021d10741cd5014021e126458d5014021e116458d5014021a528758d5014021a508758d5014021e137458d5014021e107458d5014021c63761c95014021d40731c95014021e41631c95014021b05829514308630d06541c94308630a31841956008630a31841956008530e41631496008530c60711c16215030c0c865c85450c30d07815c85450c30d04815c85450c30d08805c85450c30d05729c45450c30d05725c45450c308c8825c06150c3090e8790d5290830c0f645c8548c830c0d645c8540c83081c87591520c830b05821514394430d05745483294430b05821514354430c24741895254430c457518a3254430c45731884254430c24741893254430a4682d9563c8430a158615143c8430b058215143c8430c15655d032c8430c51655c03108430c15655d06308430c51655c06308430c51655c243084309c0825c24308430a15861514308430b05821514308430d04541c94308430c15655d03208430b04845483208430d05745483208430c157559021cc030c457598821cc030c4575188214c030a8882590404c030a9081590404c030c6175188214c030c89431c16210f20a8982191430c32081e879954310e20a198494c604ca2081f87593530ca20b048250c4394620b058494d3208620d047494d3208620b0684d4c3208620d0574d4c3208620b0684d4e5308620d0574d4e5308620b4280d4e5308620b078550c4308620d067550c4308620cc1735806008620c0d645c86414d20a0c8550d6210d20c0c7550d6210d20d05435c843145209a0845c231084209a0845c23208420d057454c32084209a0845c36308420d057454c5308420d057550c43084209a2849ce6008420d83741cd6008420d80741cd6008420aa2849d821cc020c45531c9610c020a1985191430c020c88641c9430c020c19655d0320c020c61651c9610c020cc1760c8210c020e41650c8210c020b81840c8210c0208e187190210c020a6185190210c020ac186dcc210c020ac1861cc210c020cc1761cc210c020b41851cc210c020b81841cc210c020cc17698c210c020b818498c210c020ac18690c210c020e806450c210c020aa28498c2188020a0d82d954310f10960805c44314910c60521c161cc910a6280dd8528c510a6080590528c51086487590524c510a6080590524c510e105414c604c510e2354148604c510e2054148604c510e4353148604c510e4053148604c510a6280d8c52c8510e105414e60c8510e435314a60c8510e405314a60c8510a608058c5208510d10541c5300c110d40521c5300c11090c825d54310c10c90741cd6008410a3184d4d6008410a51831496008410a2584d4c6244010ac0835c06244010c45731885244010ca27418b3044010c61751883044010e41531883044010c617518a2044010
  | 1 => 0xc0a030080a050080c4600000040201c47731c96114143c44731c96114143a84825846150c43a90805846150c43984825c46050c43a88825806050c43a90815806050c43a848250c6154843a888250c6054843a1a80dd94354843b0681dc94354843a148650f6154843a148650c6154843a188650f6054843a188650c6054843e1143d846054843e11431846054843a488250c6054843e0b8250c6054843a188250c6054843e088250c6054843d05729c45450f32d05435c84394732c31745806094732c1b541c16210e32c47731c96194232b09821914314132924825c46055032a28825806055032a30815806055032c19541c16210c3281f87d974350832a1985d0c6050832a1a80dd9544c83281e869d9544c832a1486553614c832a1486550614c832a1886553604c832a1a86550604c832a1886550604c832e1154d84604c832e1154184604c832d05549c6534c832a60825c46055131a848250d6210f21c91431c16210f2189487591320cb21c91641c1320cb21d12749cf5094321d42739cb5094321d41739cb5094321a0f8550d6210e21c89431c16210e2188c87591320ca21c89641c1320ca21c0d651c94310c21c89431c16210c2188c87591320c821c89641c1320c821a51801955350c21a848454c6250c21c85861c94310c21c87651c94310c21c85651c94310c219848750e6210c21c177550d6210c21c91431c16210c219848750d6210c21d81431c16210c21c878750d6210c21a848750d6210c21c848750d6210c21c877550d6210c21e077550d6210c21e8143dc16210c21c85431c16210c21e81431c16210c21cc2431c16210c21cc1431c16210c21c81431c16210c21a848250e6010c21c857458c6394821c857650c4394821a158519143cc821c84641c943cc821c87645c8438c8219c0805c8438c821aa0805c8644c821a868690e424c821c84641cd424c821c847650d424c821ac08250c604c821e8243908604c821ac083508604c821e8143508604c821c84731c9640c821c85645c8430c8219c0805c8430c821c85645ce520c821a8586d0f420c821c8576d0f420c821c85645cc420c821c857610c420c821c1575593320c82189487591320c821c1775591320c821c91641c1320c821ca1641c1320c821986849d1320c8219c2809d1320c821c85861d1320c821c8474d91320c82198487991320c821a8586991320c8218c487591320c82198487591320c821c8787591320c821a8687591320c821a8487591320c821c8487591320c82188487591320c821c8775591320c821e0775591320c821d8074dc1320c821e8164dc1320c821c85641c1320c821cc3761c1320c821d83741c1320c821d80741c1320c821e81641c1320c821cc3641c1320c821d82641c1320c821cc1641c1320c821d81641c1320c821c81641c
  | 2 => 0x170006d86cc914400020893a00a42c0022c0000084000af2948196870254fb280a340c4d3ccc10c837000000705300000434272b6e41a0000002b208004203d1ec00000f090c002e200430122688381e330c41a244a2185061d0b6c3a18277051b88f03480001003d07e8e802330abb3cd01204e250d38d4290008a000002a86d2fc862e8fa436b8000002ded6308764380e344ef19034800d724c38054303b414298001c836000bc37c0015c40258d818c3c3b88e348b00e4f60001d0b0a8354f112c2032026800a11a8002c2ca12eec0ec0004cf52ba661e47f398f0000340fc00302c33a40e83eea2604738c00204fd00000058ac19cf901701370dca0c00010b426c590004532c091f0412e47d2720b154c7158de044b6000621d41e03c5b000000002117400000001247e338fe39c780005f000c19306f0001010244178ae300ad09423170873762d384850f80625cdb2d42800000318cd2a4714084229c85aacc513cb10889d148d3374000010700446290c40bcda270aa9e800000902f4e21288c2f888098eb3dc049dc6b2ecb33ba2081c9f3e06c000d4000543f0991f6af9a4650b909380d907c9200073410e52030a160243fc05180002dc033c8a28a800234b21c20c00050064002780000c54000503000030a0141a00000a0022b000080409020080005000c800110280402010280c04020400436050005004010400476420280c10020180c1c02058180c020001c0000038000806000000005020106c220100016020f83c000501034080904818
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x123a000000000b00000058000000000060a1a10002091878a80004a2802e700000000f9b0c4000e000c0001a005098242c930e0800031000004000791021810002020008004003580a478250c6054843a4049286382c421e4340b9550c705884388690521c3a86b108610d2025d43dc16210c21a404ba86382c421843405951907250f32087106c8402e421c6410e20590805c8430c821a414870eb22641904308697a1d644c8320869012eb26e09906410d20a5d641c1320c821a404bac83826419043810871d163540500868812eb18e4a80a010f001d1631c95014021c0243102b90a8a18618088620172151430c320102402e42a28618610594825c24308430a02cb0a83928610861104985d1520c8210c220f30ba6a619043106405d280d4e53086208834c4eaa188610c41881766103208430083402cac206410860106105d9851cc210c020c40bb30839842180418817661263084300829032e3228610860105806546450c210c020
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
  | 6 => packedAt gbK6 (36846+((h/519+packedAt gbK6 (30618+(h % 519)*12) 12) % 2489)*12) 12
  | 5 => packedAt gbK5 (274916+((h/2583+packedAt gbK5 (238754+(h % 2583)*14) 14) % 13618)*14) 14
  | 4 => packedAt gbK4 (203440+((h/1443+packedAt gbK4 (184681+(h % 1443)*13) 13) % 6285)*13) 13
  | 3 => packedAt gbK3 (17187+((h/103+packedAt gbK3 (16260+(h % 103)*9) 9) % 373)*10) 10
  | 2 => packedAt gbK2 (2427+((h/12+packedAt gbK2 (2343+(h % 12)*7) 7) % 69)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff01fff80ffffc0ffffff81ffc0ffcff1e3f
  | 1 => 0xc07ffe03fff01ffff03f01ffe0fff07f71e3c7
  | 2 => 0x7fffffffffffffffc001ffffffffff81ffff
  | 3 => 0xff800003ffffe03ffffffe0000ffff83fe03f8
  | 4 => 0xfffffffc0000003fffffffffff000003fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x43094c2888e2448c02cb2a59092c84e4370e1b
  | 1 => 0x952a14999121c91cb01568ab285594697162c5
  | 2 => 0x2a4428522244922155408134529a291280b56e
  | 3 => 0xc68b163448903b669a6cc0610e3ce23da03b0
  | 4 => 0x3070c183870e1c3b8e38f1c79c030843edd800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeae0e080eae0e080eae0e080eae0e080eae0e080eae0e080eae0e080eae0e080eae0e080eae0e080eae0e080eae0e080eae0e080eae0e080eae0e080eae0e080, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_36769
namespace PEqualNP.Outside.L_meta_36769
open PEqualNP.Outside.L_meta_36769.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 5 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeeeeeeeeeae0e080eeeeeeeeeae0e080eeeeeeeeeae0e080eeeeeeeeeae0e080eeeeeeeeeae0e080eeeeeeeeeae0e080eeeeeeeeeae0e080eeeeeeeeeae0e080
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373984 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36769.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.and,[0,4]⟩,⟨.or,[2,3]⟩,⟨.and,[0,1]⟩,⟨.or,[0,1]⟩,⟨.or,[5,6]⟩,⟨.and,[5,7]⟩,⟨.or,[8,12]⟩,⟨.and,[10,11]⟩,⟨.or,[9,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36769

open PEqualNP.Outside.L_meta_36769 in
theorem PEqualNP.Outside.L_meta_36769 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
