import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37363.Model
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


end PEqualNP.Outside.L_meta_37363.Model

namespace PEqualNP.Outside.L_meta_37363
open PEqualNP.Outside.L_meta_37363.Model
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

def SBf (j : Nat) : Nat := [5, 6, 6, 8, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37363

namespace PEqualNP.Outside.L_meta_37363
open PEqualNP.Outside.L_meta_37363.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfc07ffc0ffffff81fffff80ffe07fffe7f1e3f
  | 2 => 0xffffffff01fc07fe0f81fffffff81f0193ffcc
  | 3 => 0xfff81ffffe0007fff001fff03fffe001e3e3f0
  | 4 => 0x1ffffffffffffffe00003ffffffffc03ff
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x53044462448a180529259454622a54c270e15
  | 2 => 0x4851888a1c912a9605a0aa599aa896149176cc
  | 3 => 0x90a2d514483ab5aab05135652d36c42963a370
  | 4 => 0xc2c51a209123064d2964060831c518b1d801aa
  | 5 => 0xe3061c38e1c3c771ce79c78e018610c1fed800
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fccc0000fcccf0c0fccc0000fcccf0c0fccc0000fcccf0c0fccc0000fcccf0c0fccc0000fcccf0c0fccc0000fcccf0c0fccc0000fcccf0c0fccc0000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37363
namespace PEqualNP.Outside.L_meta_37363
open PEqualNP.Outside.L_meta_37363.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1000e92880002c8351900005bf43bd43be42bc42be41bc41f721f421bf40bd40f710f510
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x400003209a28a871d5310a3aa7a05914910
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
  | 3 => packedAt s1K3 (112+((h/1+packedAt s1K3 (108+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffc1ffffffff03ffffc0ff83fffffe7e31ff
  | 2 => 0xf81ffe03f03f07fc3e07ff07fc3e0781b3cecc
  | 3 => 0xfffffffc003fffffc007ffffffc007ffc3ff0f
  | 4 => 0x1fffffffc007fffff80007fffff801fc0ff0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x90444448820841008a494848805294a4161055
  | 2 => 0x32cc8c3926524b2c16c2d943a434350cb2c6cc
  | 3 => 0x4191109068a484554104a2954a804259416b0a
  | 4 => 0x651a21224c06969a6590308673296011e80da0
  | 5 => 0x861c39c38f38e7e3b9e73ce062318461ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37363
namespace PEqualNP.Outside.L_meta_37363
open PEqualNP.Outside.L_meta_37363.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x481992000565391404a3bf43bd43bf42bd42ee32ed32be41bc41be40bc40ee20ec20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x602040009a28a872d521066ca3205354c20
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => packedAt s2K4 (208+((h/4+packedAt s2K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s2K3 (112+((h/1+packedAt s2K3 (108+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffff83ffc1fffe0ff07ffffc1fc0fffe4ff33f
  | 1 => 0x81fffc0ffe1f07f0ff87c1ffe1ff0781b27dcc
  | 3 => 0xfe1ffff0001fffff0007fe1ffe0007ffc38e0f
  | 4 => 0x1fffffffe007fffff8001ffffff801fc0ff0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x840088a20204000230094224024250a404b115
  | 1 => 0x2c49186490284a505482d14d2096150c92554c
  | 3 => 0x18da2141b552c6b50c44b51b540c2659c30e0a
  | 4 => 0x5114420921029529895020129928a011680aa0
  | 5 => 0x6198738e399ce7ceee6739831030c461ffe000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeaa88eeeeaa00eeeeaa88eeeeaa00eeeeaa88eeeeaa00eeeeaa88eeeeaa00eeeeaa88eeeeaa00eeeeaa88eeeeaa00eeeeaa88eeeeaa00eeeeaa88eeeeaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37363
namespace PEqualNP.Outside.L_meta_37363
open PEqualNP.Outside.L_meta_37363.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x6345d7281c0802500bc0801aac28f4660b13105061e406451b440001d48003a700b1315064801c202c8aa3e1000952000215a18000c4007820047c8002004ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xe61bc41cc3dc43987b08730bfaa4617e548c2faa9185f15230bea9c61bf438c37a87185f94a30bea9461ee328c3da65185f94630bea8c61be418c3788318778c630ee18c61ee218c3d843185f94230ef98461fb308c2fea8985f95130beaa2617c544c37e86986f50d30bfa92617c524c3dc64987b4c930bfa8a617c514c37c82986f10530f710a61ec214c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861bf430c37a86185f94830f7290616e520c2faa4187b54830b6a9061ee320c3da64185f94430fb2886176510c2faa2187d54430baa8861be410c3788218778c430ee18861ee210c3d842185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c83dc85907b50b20f719641ed32c82fca3905f54720df20e41bc41c83dc43907b08720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20dfa1c41bd43882faa5107bd0a20f621441ee32883da65105f94620bea8c41be418837883107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20dfa1a41bd43483dc84907b50920f719241ed32482fea2905f14520df20a41bc41483dc42907b08520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c530837e86106f50c20bf29041ef42083d884107b8c820f6990417e51082faa2106f90420de20841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10dfa1e21bd43c42fea5885f94b10bea96217c52c43dc65887b4cb10df20e21bc41c43ec63887d4c710f710e21ec21c43f661887e0c310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53842faa7085f14e10dfa1c21bd43842fea5085f94a10f7294216e52842faa5087b54a10b6a94217c52843dc65087b4ca10bea8c21be418437883087b88610f610c217e50843f461087e4c210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c534437e86886f50d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910f719221ed324437c82886f10510fb18a21f531443dc42887b08510fd18221f930443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10dfa1821bd43042fea4085f94810bea90217c52043dc64087b4c810bf28821be410437882087b88410f6108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xe314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863bf430c77a8618df94831f7290636e520c6faa418fb54831b6a9063ee320c7da6418df94431df20863bc410c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21dfa1e43bd43c87dc6590fb4cb21df20e43bc41c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21dfa1c43bd43886faa510fbd0a21f721443ed42887d88510fbcca21f719443ed32887d86510df94621df20c43bc41887de4310fdc8621bf284437d50887dea910fb95221f6aa443ec54887dea710dbd4e21f729c43ed53886daa710fb14e21f7a1c43af43887dc8710fb50e21d6a1c43ec43886dca310fbd0621f720c43ae41887da8310fb10621d620c43ef31887dc6310fb4c621f618c43ef50887dca110fb54221f6284437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43bf434877a8690fb8c921f699243be41487788290fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610efd0c21dea18437e52087de8410fb90821f6a1043ec42087de6410fb8c821f699043ec32086fca210ef90421de20843ef21087ec4210fb48421fa908437e50086faa010fbd5021f72a043ed54087d8a810fbd4c21b7a9843ee53087daa610db54c21f629843ef430875e8610fb90c21f6a1843ad43087d88610fb94421b728843e651087de8210fb90421d720843ed41087d88210eb10421f798843ee31087da6210fb0c421f7a8043ee50087daa010fb14021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40f719681ed32d02fca3a05f54740df20e81bc41d03dc43a07b08740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de21481ee32903da65205f94640bea8c81be419037883207b88640f610c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940f719281ed32502fea2a05f14540df20a81bc41503dc42a07b08540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884207b8c840f6990817e51102faa2206f90440de20881ee21103d842205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330dfa1e61bd43cc2fca5987b94b30b7296617d52cc3daa5985b54b30f719661ed32cc2fca3985f54730df20
  | 2 => 0xb7e86216f50c42bf29085bf4210bdc84216f50842f6a1085ad4210afca2215f54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccb7e87996f50f32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65bf438cb7a87195f94a32f7a1465ee428cbda85197b10a32ef99465ef328cafca3195f54632bf284657d508cbdea9197b95232f6aa465ec548cadaa7197bd0e32d7a1c65ee438cbda87196b50e32f621c65ef518cbdca3195b94632f6a8c65ec518cbdea1197b94232f6a8465ec508cafea8995f95132beaa2657c544cb7e86996f50d32f7a1265ee424cbda84997b10932f799265de324cafea2995f14532bfa82657c504cbdea8997b95132f6aa265ec544cbdea69973d4d32f7a1a65af434cbdc86997b50d32d6a1a65ec434cbdea2997b94532f6a8a65ec514cad8a2997bd4132f728265ed504cbd8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32dfa1865bd430cafca4195b94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d07dc65a0fb4cb41bf286837d50d06faa920df94e41bea9c83bf439077c8720ef50e41de21c837e52906faa520efd0a41df21483bd42907788520fb8ca41f6994837e519077e8320fdd0641bf284837d509077ea720ef94e41dea9c833d5390778a720efd4a41df29483bd5290778a520efcca41df19483ae329077a6520eb4ca41de194833e519077ea120ef94241dea8483bc50906fea6a0df14d41dfa1a83bd43506fea4a0fbd4941b7a92837c52507d8a4a0db14941f719283ed32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077c8620ef50c41de218837e52106faa420efd0841df21083bd42107788420fb8c841f6990837e511077e8220fd90441dea0883f541106fca020df54041dfa9883be531077aa620cf54c41de29883bf521077ca420ef54841de29083bf321077c6420eb8c841de99083ad32107786420ef944419f28883b6511077ea020ef94041dea8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc77e8798ef50f31bf29663ee52cc6dca598df54b31f6a96636d52cc7dc6598fb4cb31df20e63bc41cc6fca198df54331bfaa463bf548c67ea918df95231beaa4637c548c778a918cf15231bea9c63bf438c77a8718fbd4a31bf294637d528c7d8a518fb8ca31f6994637e518c77c8318ef10631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131dfa1a63bd434c6fea498fbd4931b7a92637c524c7d8a498db14931f719263ed324c77c8298ef10531fb98a63d
  | 3 => 0x44a618650e4f897b263b228ceb261000e95a9acb1c8ad40030e3e40000039679000055a2e7b46412d3677c80007cbcd03a000252a27663cc4eb5f1e845c7707a19c22cedb66242234000ef0aa001f4bea020b4cd19d4030e3d7b3d04106493e10972eccd869bb6b43485c9485ba045c70df100bed119794001490a2ba05c2643091f1587c4e20003ea4d95f8003fa9e84718b2400000003a2462f4b60160960bc4b1042a6b71ee2f32fac48122420ca895381d05245c11c1e15fadf0599a862a2ec003c472400200401800000000000000060140000001401006002018038018020000101780200c0140d00500e0040000a0000040580000e01000809022000000110060040602103a0000400000c038000150000000000000a0040180501205c048000000340380d02a0040500700e018018060060380e80e01200001001000000000000080040000603e0180100100c00c0580001000402806000000018070020140800f0040000080700000005801004000060040000080000b04200000002000010058150120000a81301c01c0000501800c0280600002c0100500406000012000034018000100000000d00c0100000001e02c0180803a0140080b00c02c0200803c014000000040000880603200801801000004008090000040101000a000000000020000480900000c090000020800080000000004003004004008190020040000100c00c0200000000802806000000020010160780a0040080240180000206803802000000008010000140400c0140140080e00001802800000000010090020240081200a0040600e002030000000000000c8070020440401e0020000181a008008098000020080100100805c0000000402c0000400601c000050080540b003012004008060040000380600000c0001100400402df94b43bea96877e51d0efaa3a1df94343bea8687bf52d0f7ca5a1ef54b43de29687bf51d0f7ca3a1cf94743dea8e87bc51d0f7ea1a1ef94343dea8687bc50d0efaa921cf55243bf29c87bf4390fbe8721df94a43f7294876e5290efaa521fb54a43b6a94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be28287bf5350f3ea6a1efd4943df29287bd5250f78a4a1efd4543df28a87bd5150f78a2a1cf14543dfa8287be5050f7aa0a1ef14143bf2a0873e5410efca621efd0c43ef21887bd4310fba8621df94843f7290876e5210efaa421fb54843b6a90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42dea1e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42dea1a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d531
  | 4 => 0xc001c8ade6ca3301fa8e01e24527910000fd8002c609e0001c000562fa05e3a2704220d08ca78080cf228a028e78298904ea74caa2901820b1963713702793b000328001ec3642ee2dde603d072b9ddb3af000558ba2224382088534d4fae04000a2466079bb8da60a0a5900000007940000055caed3200000000122000000670da3a041e0800020c77aec00027800000000000592048000000000a9d7343164f8525a7b67a2a0001bf7f000cc8ad25387710805c4ae4880016d262000000000001d00029910acd5ac1c37da000c2be01880017a91a00087d2f0d3454f8d4624c3a26b8001493aeabdc38a75e4eada02c70d64156a800000e114fac014a000fda2f0000000000017c33400000258cc0001422fc0018a000000cb80004433ac5c3e000000ea199379000001240006267d16716e414b6c1b13d2f006c23bc5476a085c2501d4a9d9124604ef88f5ab3412d4800000000dc0001687002800000000a9254b12b20ccf80037d7e2001c41c8398de80031d4de8f4302514e8491722fa2f8085569ef000f24010005d6a100027e0b6000638cb33000194b42160d8c000931fe17c0018858a345ae2a119000019bbc7ba705e0b39000a61072b0000001468000000000000006a0014d000000cac8113313658ca808900098c208003566313fa36000000ffa2c154e750900014c8800398d000be5f9864282a24f42b2374001dc84d3320d1cd15b7deb8c6a3232946f49692a1b8dc93880059a7c0001347aa02d5e8006f01a8782d937cad07390d2d40016d02d15a4482436e39cb45b52813921000015c6186cce93731b6c2000000526000360690000000023212400083bd26ec72c3b8840008f90d82231e1c1ba8e90000010b9185c4000f700000000028800000000000000380003b000000000000003c4d3c0000000000166189364dd050b5974c7556135d278ad9da3ba1e2aa88a9cd1c6f9c068bf770178001581280000016b000000001825e2000000003b00013b8005fc2c5889da3be000398c64cc808fe34523c000c38005a80200025b21e001d50500fefd4000000001b800000000588002291c2f5ccfb6b192e8400383732f09d20cf260af80c9574ba5797632427e5bd4dac132e81c003be550f18858fa6da59800b6c5d2aa40020d2fe8605d3251385e8000d826e001328000006dc00319000001cc1c568800129af70000011829e66c18800000434c1c003181b299d0f00000000012895000218002ea62c3b521ae033c8f0d10b6000000b28001ee5cc000831ec95143000358fada5ab7000000000000009b000000000a00001e900000000252228f7c000002e200000000776ced4a80010e50d0091b46e00000291000c405aa736041c80038d6aa3898fb8928ad39d91a95ca6d4a70001f8960f311d3da23c2ca8b3d4e55e5a1946a5
  | 5 => 0x19300077893357000dfdaa38c70ad581330021c900b200001408d70a3a4e48152284226a8fd832f463ca741f00000018c57b4c0005356c0d777e97cfd0000006586aab80000001bb8a000a8db78002d2b286eae6556bc00012e114000cd00002ac9cd2b3c6bc611908c30cc3ec52227540bf0a59761d0001530003d80019b8005066c4460004c0f28fb000000000002d67d83817707e59e989f703136c9383a82800c12400000264e500035029e680f000000000072b4a3f295800000000eb40026e00084c9380000051000108716130000007e4f78000001d60002d2045861c4b93c7674929e7b2f7523b0159397a871c92a3165a25c0717b3006bcf190c000970ee8000005740034909c000c53460000012a8004d20006f13b636d058480031c000368002ea40c022c83ce300ad36051e1edfb8d640cd89120f8306f953599b7ac4e0b01280de1f5db8c50000005a01f662118000093f057da88c20aed8433bc35dea2094a4738ca5cd239b0008740b89f70c6e4d6858668c7000000000708002682223c9820005580000600000000000000000001d1a4d280884180ae394ce1620007208980000000000000000078ba0000005a09b5ed9a7000399b48983e6f64a91950000000022d4f200000000152e9d808001028a1a3bb51ea00000393000068000007e8458193ce000bb4a38000008580030b2ce701e89cf302dec003e67e00ec00000690c3c0032a00004d2cb7e0004709d1a60001156fb680a88e57c39c5721e1521460009a952959482b5c7e8fe2c2174002855fef4c8089a000d6cd8000634001cf95576210d850000d01e594234200eb0de2944564642b0001a000105a15422af0001aa67ec0cfb9133f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x421c42f1610c310f48c430c426e62d52109b58b548423d63952108fd8d548426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423e6494e108f592538426e6294e109b58a538423e6414e108f590538426e6214e109b588538423f65d0e108f597438423f6550e108f59543842b46150e108f993528423d64d4a10cb952528432d5494a109b58e528432f4394a10cb50e528432e5454a10cb551528426f6354a10cbd0d528432d4354a108f990528423d6414a109bd96328426d658ca10cb952328432d548ca109bd95328426d654ca10cb951328432d544ca10b9185328432e5290610cb54a418432e5210610cb548418432e5488610cb552218432e5408610cb550218423d63d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58c544423e61151108f184544431f54d4d10c7153534431f64d4d10c7193534434f62d4d10d318b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534423e6414d108f590534426e6214d109b588534425e6514d10c7d50534431c5414d10c7990534431d6414d10d3988534434d6214d10d558453443596014d108f997434423c65d0d10c7d4f434431c53d0d108f995434423c6550d10c7d4d434431c5350d10cbd53524432c54d4910d3d4f524434c53d49109b58f524432f43d4910cb50f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524426d6314910cbd0c524432d43149109b984524426c61149109b996324426c658c910cbd52324432c548c910d3d4e324434c538c9109b995324426c654c910cbd51324432c544c910d3d4d324434c534c9108f996414431f5390510c714e414432f5290510cb14a414423e6510510c7d4c414431c5310510cbd48414432c5210510d514e3144274654c5109b996214432f5488510cb152214434f5388510d314e214426e6508510cbd50214432c5408510d3d4c214434c5308510e9104214427a658c110d614e30443d2318c1109e1953044358534c110d614f104426f62550109b189540425e63150109758c540426e62150109b588540423e6494c108f592530426e6294c109b58a530423e6414c108f590530426e6214c109b58853042766114c109e980530431e5350c10c754d43042b46150c108fd91520423c64548108f990520423d64148109798c520425d6314810d394d320434d534c810b9185320423e64940108f592500426e62940109b58a500427965cc0109e59430042f1610c0109e596100427765440109ed9510042d86344010ec10510043e02144010
  | 1 => 0xc32d43948309b986520c32e5454830cb551520c32f4354830cb50d520c26c61548309b596320c32e548c830cb552320c26f654c830cb951320c32d544c830e350d320c3365494430cd552510c3665294430d954a510c3376494430cd192510c3374394430cd50e510c3676294430d918a510c3663294430d94ca510c23f64544308f191510c26f62544309b189510c3365454430cd551510c3665254430d9549510c3376454430cd191510c3374354430cd50d510c3676254430d9189510c3663254430d94c9510c37060544308fd96410c23d6590430cb94a410c32d5290430cd946410c33551904308fd94410c23d6510430cb948410c32d5210430cd944410c3355110430d5546310c26f65884309b596210c32e5488430cb552210c3665188430d9546210c26f65084309b594210c32e5408430cb550210c3665108430d9544210c371518c03097d95300c27b654c030e650d300c3c9324c030dc545300c25e63153209758c54c823e6494f208f59253c823e6414f208f59053c831e5350f20c754d43c832c5450b20d354e32c823f64547208f19151c836651087209d987548827561d52208f992538823d6494e208f990538823d6414e209d98453882756114e20cbd50428834d534ca208fd91518823c6454620cd94441883355110620d9946218823d63d51208f987544823e64951209bd89544823e65151208f58c544832d62151208f984544823e6494d208f592534826d6294d208fd91534823c6454d209dd8553482746154d208f990534823d6414d209b988534823e65d0d208f197434823e6550d208f195434826e6590920cb152424826c6550920cb151424832f548c920cb152324826c654c920cbd51324832c544c920d3d4d32482e8604c9208f993514823d64d45208f996414823c65905208f994414823c6510520cbd52214832c5488520d914621482ea6088520cbd50214832c5408520cb152204823d65950208f58e540823e61950208fd8d540832c62550208f185540823e64150209b988540823e64d4c208f593530823e6494c208f592530826d6254c208f990530823d6414c209b98853082766114c209d584530823f65d0c208f597430823f6550c208f595430826d65d0820cb553420826d6510820cb550420826d658c820cb952320832d548c820d354e32082e9608c820cb951320832d544c8208fd91510823c64544208fd96410823d65904208fd94410823d6510420cb952210832d5488420cb950210832d5408420d994421082e96008420cb553200826f6548020ab191200832d54480209ed95200826e62d53109b58b54c426e62953109b58a54c423e6494f108f59253c426e6294f109b58a53c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6494b108f59252c42f0604c710e910
  | 2 => 0x6190421cb94641087a651904219bd9541086ad6310421cbd4c410872d5310421ab98441087a66110421cb94441087a651104219b59731086ae64cc421ab59331087a441cc4219bd9631086af648c421ab192310874d538c4219bd9531086af644c421ab19131086eb604c421ba181310866e650c4219b59431086ae640c421ab590310874d530c421e910431086ea600c421ba58031086af6454021ab19150086ae6414021ab59050086ce6314021b358c500876950140219b98a53d026d6294f40c754f43d034e534cb40d354d32d026f62547409b18951d033651107409b98a539026d6294e40c754d439026f62546409b18951903365190640d9944219036551086409b988535026d6214d40c7d4d43502b86050d409b58f525032f43d4940cb50f525026e61d49409b58c525032f4314940cb50c525026e61149408f997425032c52d0940cb149425026e658c9409b196325026e654c9409b195325026e62d45409b58b515032f5290540cb14a41503345190540ae982415032f5210540cb148415026e65885409b196215026e65085409b194215032c52901409b98a531026d6294c40c754f43102b960d0c409b58e521032f4394840cb50e521026e61948409bd8d521032f4354840cb50d521026c61548408f596421032d5290840cb548421026f658c8409b596321026f654c8409b595321026f62544409b189511032e5290440cb54a411032e5210440cb54841103365110440ae580411026f65884409b596211026f65084409b594211032d52d00408fd9540102ac6250040cb549401027b65500409b98b54cc26d62d53308f98654cc23c61553309b98854cc26d6215330cb95252cc32d5494b30cbd0e52cc32d4394b309b98652cc32e5454b30cb55152cc32f4354b30cb50d52cc26c6154b30cb95232cc32d548cb30cb95132cc32d544cb308fd9151cc23c64547309bd8951cc26c62547308fd9641cc23d6590730cb94a41cc32d52907308fd9441cc23d6510730a758c41cc32e5210730cb54841cc26f65887309b59621cc32e5488730cb55221cc26f65087309b59421cc32e5408730cb55021cc2cd63087309bd89548c26c62552309b988548c26d62152308fd91528c23c6454a30e350d328c23f64546308f191518c26f62546309b189518c2d9600c6309bd89544c26c62551309dd85544c27461551309b988544c26d62151308f990524c23d64149308f993514c23d64d45309b98b514c26d62d4530a758c414c3375110530cd144414c2cd6308530d9d44214c36451085309b98b540c26d62d50309d987540c27561d50308f596540c23e61950308fd8d540c23d63550308f185540c23e64150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c23f6550c30cb952520c32d5494830cbd0e520
  | 3 => 0x31da4c9500c73a4154031ce105500c7723154031dc4c5500c63d63953218fd8d54c863e64d4f218f59353c867a60d4f219e58353c863e6494f218f59253c863e6414f218f59053c863f65d0f218f59743c863f6550f218f59543c86b46150f21cb95232c872d548cb21d354e32c872e544cb21cb55132c867a60d52219e583548863e6494e218f592538863e6414e218f590538867a6014e219e580538872e5450a21cbd5042886ae64cca21ab593328874d534ca21ab99032886ad640ca21ab99321886ad64c86218f992508863d6494221b998754886ea60d5221ba583548872f5495221b998454886e661d4e21d998753886ae6494e21ab592538874f6354e21ab99053886ad6414e21b998453886ea6014e21ba580538872f53d0e21cb54f43886ae61d0e219b996438866d6590e21e3d8d438872f5350e21cb54d43886ac6150e219b994438866d6510e21ab58e418872f5390621cb54e41886ad6310621cbd4c418872d5310621e998441886ae64cc621ab59331886af648c621ab192318874d538c621abd9131886ac644c621bad8131886e8604c621ab99031886ad640c621d354c31886ea600c621ba58031886ae64d4221ab59350886ae6494221ab592508876b50942218f58f544863e64951219b58a544866f62551218f994544863d63151218f992534863d6494d219b58a534863f6454d218f191534866f6254d219ed8153486786054d218f990534863d6414d218f997434863c65d0d218f995434863c6550d219b996324872f548c921cb152324866c654c921cbd51324872c544c921d3d4d324863e65905218f994414872f5488521cb152214865e63150219758c540867a60150219e580540863e6494c218f592530863e6414c218f590530866e6214c219e98053086796014c21c794d430871d5350c21ad185430863e64948218f592520866d6590821cb151420866d6510821cb550420866d65cc821ab99332086ad64cc8219b596320874d538c8219b59432086ae640c821ab59032086ae64c8421ab593210866f6548421abd9121086ac64484219dd95210863f64540218f19150086e661d5021cb55054086ce6315021b358c54086e66115021ba98054086e96015021b9987530866e61d4c21d9987530866d6594c21ab99253086ad6494c21d3d8d53086ae6414c21ab59053086e66114c21ba98053086e96014c21cbd4f430872d53d0c21ab987430866e6590c219b59643086ad6490c21d354e430874d5350c21b9d8543086e46150c21e3d8d430872f5350c21e394d430872d5350c21e354d430870d5350c21e9d8543086ac6150c21e918543086a46150c219b994430866d6510c21ab990430866d6394421cbd0e510872d4394421d998651087a74394421e950e510866d65d0421ab58e410872f5390421cb54e41086ae
  | 4 => 0xb98a53106ad6294c41ab98853106ad6214c41ad98453106ba6014c41ae58053106b661d4841a798c521069d6314841cb54852106b66114841ae98052106b960148418f997321063d65cc841c754f32106ad638c841cb54e32106ae618c841c754d32106b7614c841ad185321078f634c841e394d321072d534c841e354d321070d534c841e9d8532106ac614c841e918532106a4614c8418f994321063d650c841ab988321072e3294441cb4ca51107366194441e98ca51107a53294441abd8950106ac6254041a798c501069d6314041ab98850106ad6214041ce540501066e62d53319b58b54cc66e62153319b58854cc72e5494b31cb55252cc72f4394b31cb50e52cc72e5454b31cb55152cc72f4354b31cb50d52cc72e548cb31cb55232cc72e544cb31cb55132cc78d434cb31cb94a41cc72d5290731cb94841cc72d5210731c758f548c73661d52319b98a548c66d62952319bd89548c66c6255231c758c548c7366115231ad987438c6b46150e31cbd53528c72c54d4a318f992528c63d6494a318fd91528c63c6454a31cbd50528c72c5414a31cbd52328c72c548ca31b9986328c72f544ca31cb151328c6e4614ca31a758e418c69d63106318f992508c63d64942319b98a508c66d62942318fd91508c63c64542319bd89508c66c62542318f992544c66e62951319b58a544c67a60951319e582544c66f62551319b189544c67b60551319e181544c63e65151318f997434c6b661d0d318f195434c6b46150d31cbd53524c72c54d4931cbd0f524c72d43d4931cbd50524c72c5414931cbd0c524c72d4314931cbd52324c72c548c931b9986324c72f544c931cb151324c78d434c931b9185324c63e6590531cbd4a414c72c52905318f994414c72f5210531cb148414c73b54d4131ce153504c76b52d4131da14b504c73b43d4131ce50f504c76a32d4131da4cb504c73a41d4131ce107504c73b5414131ce150504c76b5214131da148504c73b4314131ce50c504c76a3214131da4c8504c73a4114131ce104504c75a31141319b98b540c66d62d50319e983540c67960d50318f596540c63e64150319b988540c66d62150319e980540c67960150318f992530c63d6494c318f597430c63f6550c31cb952520c72d5494831cbd0e520c72d4394831cb951520c72d5454831cbd0d520c72d43548319b596320c72e548c831cb552320c66f654c831cb951320c72d544c8318fd96410c63d6590431a758e410c72e5290431cb54a410c63f65104318f594410c69d6310431cb948410c72d521043197d95310c6d8604c4319dd95310c73a5494031ce552500c76a5294031da54a500c73b4394031ce50e500c76a3294031da4ca500c73a4194031ce106500c73a5454031ce551500c76a5254031da549500c73b4354031ce50d500c76a3254
  | 5 => 0x5210f2d43948439b9865210f2f4354843cb50d5210e6c61548439bd895110e6c6254443c754f43d0b1d5350e42c7d4d4350aac6250d42c754f4310aad62d0c42ab5924210a3f65508429bd954210aaf6550842cbd954210aaf6350842cb54d4210aac6150842ab1814210b2d4294442cb5095010a3e61953328f18554cca3f64547328f19151cca7a60152329e580548cb2c5450a32cb550428caae64cca32ab593328ca3f64546328f191518ca3f64542328f191508cacd63d5232cb550548cacd6315232ba980548cae96015232ab987438cb8f6350e32ab185438caae64d4632ab593518caea60d4632ba583518cb2f4394632cb50e518caaf6454632ab191518caaf6454232ab191508caae6414232ab590508cb6950142329dd85544ca7461551329ed81544ca7860551329b997424ca6c6550932cb151424cb2d5410932ab993324caad64cc9328f993514ca3d64d45328f990504ca3d6414132b358e544cacf6355132b9d85544cae46155132bad81544cae86055132cb550544cb8f53d0d32ab987434ca6e6590d32ab592434cb8f6350d32e3d4d434caac6150d329b994434caae6410d32ab993514caad64d4532abd91514caac6454532bad81514cae86054532cbd0c514cb2d4314532abd91504caac6454132b9d85504cae46154132ab990504caad6414132da540504ca6e62d50328f596540ca3e61950328f185540ca3e64150329b988540ca3e6494c328f592530ca3d65d0c328fd95430cb2f4394832cb50e520cb2e548c832cb552320ca5f654c832d3949320ca6f654c832cb951320cb2d544c8328fd91510ca3c64544329b98a53d066d6294f41c754f43d066d6394b41cbd0e52d072d4394b419bd8d52d072f4354b41cb50d52d066f658cb419b59632d066f654cb419b59532d06e4614cb419b98a539066d6294e41ab98a43906ad6290e41c754d43906ae6210e41ab588439072e5250a41ab98b41906ad62d06419b98a509066d6294241ad98753906ae6294e41ab58a53906ae6214e41ab58853906b66114e41ae98053906b96014e41ad98752906ba60d4a41ae583529072f5294a41ad984529063e65cca418f597329072d538ca41ab986329078f634ca41cb54d32906ac614ca418f994329063d650ca41ab98b50906ad62d4241ab98a50906ad6294241ced42509066e6214d419b588535063e65d0d41c7d4d435066d63d4941cbd0f525072d43d49419b58c525072f4314941cb50c525066e658c9419b196325066e654c9419b195325072f5290541cb14a415066e6294c419b58a531071d53d0c418f59643106ae6290c41ab58a43106ae6210c41ab588431072d5210841d394d321074d534c841b918532106ae62d0441ab58b411063f6550441abd8941106ac62504419dd95411066f62540419b18950106b661d4c41a
  | 6 => 0x5200024e8650131f88001a68000000002310001641f726e8361cca1100022e08380002c00000000026a80000003c00000000027223d0410002578a11c91a58db0001921a380014d14f90d8e50000d788090f98ca3f9ca936015272a0da5e96388da8b801000400000001401000000c00400400801800000001c00400000000000000000001400000800000000000c00000000000800405400400400800001c01401800800400400001c00800000400800800401400000000000400000c00000000400000c00400000006c00400400400400800000800000400c02400400c00000800000400000801001000802400000000400401000400401000000000000000000c00c00400800400000000000400000c00400800000801000c00001800400400802800000802403000c00801c00000400000400403c01000001400c00000000000401000000c00800000c00402000800400000001c00000000c00000400400001c01400000002000000c04800c00000000004801400c01000000400001400000000400000000000400c00400800000000400c00000000400800002000000000000800c00000000400800000c00000402801400002800000401400800400002401000000800000800000400000800005400400000400c00003400800000000000001800801800400000c00000003000000400400000400402000000400400001000400000000000000400400001402800001800c00800c00c01c00403c00400000000400c00400000802401000400400000400400400000800807001c01402c04400000001000000c00800403401800000800c00000800001402400400000401000000000400400c00401800c00000000001c00400000400000000800001002800000000000800000400401400000400c00000400400001400004c00001000800403800000000001400000000400c00400000800400000401c00000404000400000c00000000c00000800000000800001800000000c00000000000400400000800400400000000401000800400800001000401001403400c01400400001801800000e6f62547439b18951d0e6f62543439b18950d0f2d5214b43ae98052d0eb96014b43ab98b51d0ead62d4743ae98351d0eb960d4743abd8951d0eac6254743abd8950d0eac6254343ab98850d0ead6214343ce54050d0f2f4394a439b9865290f2f4354a439b1855290e6f62546439b1895190eae6290d43ab58a4350e6e62d45439b58b5150e6e62141439b5885050eb76154943ad1855250ebb6054943ae1815250f2d5214943ab98b5150ead62d4543abd895150eac6254543aed815150eb86054543abd895050eac6254143add855050eb46154143ab9885050ead6214143ce5405050e3f6550c4397d954310f1e5450c43cbd0e
  | 7 => 0x9228000000000001fd8000001f28f100000000000015080008b8828001060000ab99d00000011300000026a0001eea9f91600000023a9b48ba1798928f625724da7112612f84e8c7000214a5497a0dea6f2888190a18fc0000002269d501a9488000000000288000000000000001df0000000100000000340cb0308000000002740001968efa9099908c09e80000018892204180004488a0a49e080000000000007880011b118a1f9e51b90088f286c9d900794e1668eb99b0458000001310001e902f8a88001b12580001a80241830000ec0b89bda3325a000243a9b25880020693b00011a8000001f902500000017c80007680000000000000000000021827195f9aa24e00000007294500001381d80005a80004f255a70890a4f9b29eaa9e07d82c80000020282aa969aa80024526f80000000000000003e8000000dc800000247a162738428000001589109480000001d72810000001ee1d3a7aa481d49a489b8000778000001dc0000000000001e21dd0001490e40000001728001e105b00e87c80007f1d6000000140a3e0159de8cf000000108000133a7019795e13b80006e0002698000058000000000001330c58001828ef1a0a8304fa8585800000021ea9ca090000000000e598a97080000000001280000000015501a00000000009f80000018080021a193a9a215a3414680000f22c87380017b8000001ae1a912719988980024620416a92021f00000618b0000001ae9a98000001548500758000000000000000000dd9f80000b90d90001ea0541738002279f01918e080b9d01d180000000000021405e0168000002929e80f09d680000029880000028b0000af80000014200000000018b9cc00024a12d10d23b80000022d22f0750000660110000858068e20000000021c604d800000000054a8819526900013c80009a80024700000000000000000000000000000000000000028f0000000000fd00400015d90ea7e8000000000000002169418b500019004713280000000000000000000000018d22e80019c00d8002661b7a868000c0a639c222b24a8000000ae0002658f30000000000000000e30000000000000001f119a9fb86180027702980012380000028080009385b80000005399082700007902d9850000000d3a4d1ce8001cf91a26c8001c0a918000000b489f18e83e0000000baa3d97b00027912b1b0242818a931b68229119e4a321d11eba4080019100026b24b00000007e1c813a2599f480000007f800000000298000142a510001c49f40d20000000000000000001368000000000000210000000420000000000ce23b1788000000b38220611ef8000f800001700014617f12e0000bb8e8800000000000000115057823974289a5208794a1e3a3a00000016f8c7a6e0000000c98000000000000001f380000005e80
  | 8 => 0xea8000000000001199a798c2648000000000e780000012b87e886a518121af9dc9970df0fa0000000d198e0e916191e0218000001c980016600001d00015d13580000025d23e9350230000000b5a5390f00000027f80e0d81698000001f6143a0714da2407a8000aca9a8002128910000000001821a403c8a2000062800114945827a4c23490a88e9f6a2211817797d0d409d05c00000000002b8000aa8c880022580000009ca490000000000001cf0bf26d0000000000830a80000000000000001be0fa9891110b98000c28f409600000016c800000000000209800000000000000157278a8e0000000002678609a18000000000000958000002508000001001ad80000022600000000018800000021e1898d7000000000168a542100ae80b0000000000000658ac12180000000000000000011f80004d282800a2b9c58c00148891c286da051a0000000000000000000277a6880000000000000000000013e0001ab00000000000000008f8001ef235a2d90c00000025f8b080000016b8002848001e9a5b92095583d00000d221000038276984a4306a1bf0b619e80000009e20c8000001470000c917580000028200000016b1b70001f300026515300000000006b0328001ce00005f00000000012a80003698596a260a0f9e40000fea890e49a109b00492c1541e283180005d000144a8e8bd80000028d2950bf8a38cc0378f70000000000000312290e38001dba780c50ca9c880000000000000000000000008226b9bc00004699a2550001bd00002b2561c701c11d8000001529bc85d99b9ba85295c8f483f00000019814c03583b09814b1ec000000231a0100000000012a221a2a84820f20b80800289327600116828c1299259308142941b590296106221ba339278ed9068291e7a2713e8d300000000024188d00000021c9f212119d8cb8d501e93880007802628715b1050000f5a0a888a620dc14e95181f80025d95e90c80000000025b26c00000000000003a128800000000000207a8189414b8000bb0000680000000000000000490000000030678000770e993f9ff8001a30db800087109a93a4b9e5a1900011680011400005a1da00020c20d1da9a88000c31bf87d00000002ea9d0000000a518684012900009c00000025c0000000fe25300006727c17e0000fb1719b189786400021383008801615f0002232671011170cd0000000970000001ff0000000a60a784500000011018400020880000000012ca058430000a69c38000001931eb0000000000f500000009a0000b80398460000000001ab80011e99899f0d892f00000000000010e00000004e0001780000570599248a080009d8000209c10000a70da00002f00017200016300006f9f994f0f1a0a139a9d809a5f222a030002209e700013200012816d27f000160000000157
  | 9 => 0x17ea1d80017900000006480015b91c81c8949090cc8be9348000001e68000c12681e000022f8000000000000da9a60a40df8002731138000000b68f20bd0e28001d79c31b30000e61020268001811372108f78760eca5a981884903a7c8000669b38000aa20000028c8509c6a7d00017d82e13c00029600013d0591d882028407b99480000180006c000130000287a130000002838000000000001750000c20000000000000002600001ac244a248000eb00007a0000000fc80000023518013d81194400016700029b9018000000000000000000510000d10000c600000000010b112a4680000000000023c07186e8001fc0438338000408bc80029f1d580000016d9629380de1ad1d9a958b000000015a11780000000000000015103f8a90001de1b9a758000000000000001009251e30000001960690001c1a3c8002188000000000001390001cb00000000000003900004a8841878000000518001030e10000000000c80000001231d20000b11c00d686a8001fe1d80000000000000001d283a9e8896a8aa1996796f25c80000000029916084a08c9b200000021195c2500321b50000f0019a179a217695980000000016200000008500023880f8001db00000010b99e09200000000000000000000004997112d9df80000000000000028f80000016592682a0e020604885f80016529c2978d61240ea14304c91c0000000000000000000000000000000002150000001a280000000001b000000236000024800000000153834a402498000000701770000000000001fb0860000000588be000000000000150000279a4400000000000018fa8018f0000000000000c380000000700000000000000000000002d00014a8000000001b0a1209180019280000000000000016c000000156000081a238c6aa01bb000017a38239a4588a80013a9f08601f1a0080000000000000000000000000c0d01ca1078000ee87b0000000051b400001e0000258001d4000000000299a7d8000001dd80019c8039590000000000000000370f690413780000007499f9d080000006981080006f0000000000000000000000000000000000000000000000fd9860ca0000991ed22012e9ed80000000018385300023707100028da1b1f79b8068a74a300900d28000000002250000000000000000002328001cd0000001058001fd0000000000000b18000000ad00018a20e9cd8000001c40000c42921158000b780024f201a369760000b20f9a4880000000022c00003b8001648d08000000000000000000000000000000000dd00027b9fe80000028600005591f0000000b70000000000000440000000000002628090638001a70000180000000000000721318001f50000000b32750ce8000281d30000001a518da0815826193f00000017c24c80a8d98000a00000000
  | 10 => 0xa30f38000000000001f5a668d59af0e18000e808e0000000ffa948c180010a252a1a80028a0561521e1a03a642632289568000000000000c480014120b00003d80005500000000000022800000000028500004c20200000000000008025e1ac9c506d2379e605c96e2412611b61fa9be8a99748998b401b95a91b84ba3f1479498000b2a2a1ba0000000cd8000950000568f903526d80001f0000330000000ff08f0478000001cb8ab2170000000e690483887c25920e00000017f9b897327a1400000af0a28630d48798cf8000000f88000000000a58000000000000000000002900000ed00000000016900000000000000000014c80020480000018700021c0811fc97a8000000ad9ec8001c7a5699421d0bc06b80023904b23087419588b00017000029e8000001190ee00007080000010707300011d09880000000c8e71bb80029700010880000000000013429111227e27b0000000000000fb80a1fa24222980000016e80000
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x928400000018a80436543444464248c60200728e947c00a698aa14807e005838241e00000c6e000000be009e70006664b0001000ac0000ae903a000022dc00a400c49c526a1aceb24c283c008c00de5a0000b400780e3e4ab87a56000886d40076060a20d60000000000da0068bad29600c28a00b6269a826c00ca7432a2400050000000620012c82a88cc1c00a04e00c05c2e602c0000000000d030d85e0000bc16010000010a02000d0000000301050000130500010801020101020402000a00060700130004c52a4b00a5a1e296254050d0e9238aa4292874a1c15214943a50e4a80a0a1d30715405050f07b1aa6a1085491c54294442a52e02a2851962954580548cb14b22a028465491c55410932a50e0aa0849952471550544ca94382a82a265491c54314532a50e8a80a09956071540504cb06b1a87296834a9c35294a41a54e5a84a120e4553185321065238ac5298838358d5214841c52a4b00a420e15531853210782a9ec2990838354c614c841e0aa630a6420e86531853210712a98c299083a154c614c841c0aa630a6420e19635405010714b12a02808389150614ca31a48e2a18a498d0c7550d324c6c238a869926389150614c931d0a8630a6498d307150c504c784a1a6428263581c53214131c1ac6a908218d1973105500c686b9ca8996434a9c35410a21a54e1aa4a910e0d63d4c41886953a6a1284438554c6150c21a1ae62a28410d29701514208706aa2c62a0438a5516015021948e2b24a610e45531854308686baca6a1843c154f6150c21c1aa630a8610f05531854308713a98c2a1843a194c6150c21c4aa630a8610e85531854308702a98c2a18438358d5310421c1ec8a9c6210e0d6454c3108652bb0821884389594410c421b0ae62086210f05531043108724a9ac018843a8105600c421c52c8a80a010e4963540500869438286292818a14a6090540a4ce3a9082a044d731942150306b1a87290814a5c343548408c8e2b2a6420629525804110306b1aa420e61491c55210730a48e2aa0439860d5458c21cc382a1a64a8861c450d514c030e8264a8a601850d7315142c829338ea8214418a150604c92083ae6328829062854982214829338ea810a410d1c56550c20c52a8b04641050d739513208314aa2c0108410b1d95448020c1ac6a1ca5085247150e5284286b9ca89942189950614ca10e08a62084288652658c630443483188288021b018c2144010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x4819820010e9280030ab008150d3214131d01431c53214131c05655cc410c421c057654c410c421a8183105600c421e0153105600c421c05631c55210730a04815516308730c05631c54394a10a0583950614ca10
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 6 => packedAt s3K6 (864+((h/16+packedAt s3K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s3K5 (31188+((h/339+packedAt s3K5 (27459+(h % 339)*11) 11) % 1343)*11) 11
  | 4 => packedAt s3K4 (56486+((h/448+packedAt s3K4 (51110+(h % 448)*12) 12) % 2362)*12) 12
  | 3 => packedAt s3K3 (5784+((h/37+packedAt s3K3 (5488+(h % 37)*8) 8) % 162)*8) 8
  | 2 => packedAt s3K2 (612+((h/3+packedAt s3K2 (600+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf03ff81fff0fff07fc3ff83fc3fc0ffd9c739f
  | 1 => 0xffffffe07ff07ff83fc1fffffc1ff03e67fce7
  | 2 => 0xffc1ffff80007fffc001ffc3ffe0003f878f07
  | 4 => 0x1ffffffff83fffffe0003ffffffc3f80ff8
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x158488c5121411014c125a24c12425a48c318b
  | 1 => 0x208811432400a0281440a8494409608821d4a5
  | 2 => 0x431da28a0ead4b5ac23136a3ab40c333868f06
  | 4 => 0xa21441048880a94a2a4040232928a03500a50
  | 5 => 0x8c31871c70ce73e73b39c73023030c23ff6000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeec8c8eeee8080eeeec8c8eeee8080eeeec8c8eeee8080eeeec8c8eeee8080eeeec8c8eeee8080eeeec8c8eeee8080eeeec8c8eeee8080eeeec8c8eeee8080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37363
namespace PEqualNP.Outside.L_meta_37363
open PEqualNP.Outside.L_meta_37363.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x80f631f531
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (34+((h/1+packedAt s4K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe03fffffffffe07c0ffff03fffffffc8f1fff
  | 1 => 0x7fffffc07f03fff800f83fffff07c07f09fe67
  | 2 => 0x7ffc0fff8003ffffff003ffc1ff8007ff1e387
  | 3 => 0x80000ffffffc0fffffffc0001fffff83fe03f8
  | 5 => 0xfffff00000000fffffffffffe0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x298244912408401502a4b4123885344830cab
  | 1 => 0x5428c88724952a58245c15964d46852b087665
  | 2 => 0x185165120e5a46aad502265916d20a71b1a386
  | 3 => 0x51628a2448906b34a694809218672c235c0350
  | 5 => 0x61830c3870e38dc738e738e380843042efd800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfac8fac8aa80aa80fac8fac8aa80aa80fac8fac8aa80aa80fac8fac8aa80aa80fac8fac8aa80aa80fac8fac8aa80aa80fac8fac8aa80aa80fac8fac8aa80aa80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37363
namespace PEqualNP.Outside.L_meta_37363
open PEqualNP.Outside.L_meta_37363.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4817e51902faa3205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40dfa1a81bd43502fea4a07bd4940b7a92817c52503d8a4a05b14940bfa8a81f751502eea2a05f14540fa28a817451503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa518778ca30ee194617e518c2faa31877cc630ee98c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930bfa8a617c514c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a9061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861df310c3ba62185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83dc43907b08720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885107bcca20f6194417e51883eca3105d94620bea8c41f551882eaa3107bc8620f690c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483dc64907b4c920bfa8a417c51483dc42907b08520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107bd0820f621041ef32083d864105f94420bea8841ef21083da42105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c43dca5885b94b10bea9621ed52c42daa5885f14b10fb20e21f541c43ec63887d4c710fb90e21f421c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10f7294216e52842faa5087b54a10b6a94217c52842faa3087dd0610fa20c217e50843f481087e50210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fb18a21f531443ee42887d08510fd20221f940443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f741043e882085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350bde84a16f90942bfa8a85f75150aeea2a15f14542fa28a85745150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f721665ed42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7197790e32eea1c657e528cbde85197b10a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde84997b10932f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6197790c32eea18657e520cbdc84197b50832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0195f54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0fbd4941b7a92837c52507d8a4a0db14941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620df94841f7290836e52106faa420fb54841b6a90837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631fba0c63f4418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7bc8698f750d31bfa9263ef524c6dea498df14931f6292636c524c7be6498f74c931fba0a63f4414c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c87dc6590fb4cb21fba0e43f441c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef42887d88510fbcca21f6194437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f721243ed42487dc6490fb4c921fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410fbd0821f621043ef32087d86410df94421fba0843f441087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d02fca3a05f54740beaa4817e53902faa7205f94a40bea9
  | 2 => 0x64c0021e0000014b24749a75459a35000000c3000000494981a832a96c4a8ca18c61c5a9171981d411800000524001243e4000001bc4ba0dc88965000459391f71f02240016307e6d00000011c4509c2274a28e10c06b0000000000000090800004000938001c9000150a1182280000000000000000001e15c0010900032e8b887000410000000000000000000000029c000e900000000000000000f3287000574479a11b60000000003e000001b04445e8001a53ba7ac1e8002208ec5b0000c20008a94e4c406c280000000000022d0000014796f0007b4ce8000001f0000001a20010ea680003c0bb1db17aa24000000001bc0026352a600000c821a0011198d00000000041000000a1a7752e000fc8432fa2d00000028c000000003f40000013b3e80683b80028800000177186000a58735028a00019b4b20000017251070c42800000000000000000000006e27c0ac528673c05ad350003e68180000030a0004c9284c2940dc11b52217c001084984092fa80416000000d01286bc131274aa44cd00004ce9e000184000000000000006500019a15081400000004a08000000484748300001c000000bb000a342400000000000000000000000dd238000000004e0478f182e0742e01106d3f64d91b80a3e2000e4000000000b69ba0000000000039e6d8839793d82b080800000178000000000011f8003546fc0004621242caa0002565ccd88001b40480012300100a0040200d0000180100000000812800018000000010000000000100000001003000000018040020000280000e0380180000000c0180000001c03001008000000040020080000100200401801006000010000020000400001401000804000000000060000000980d0000080100200201c0301203e018000070040000080400000403017004000008000220140200600600000007004004008020040000200000e01c018020000000300000c0000000e0000300000000000c0280400000c00000000020000010160040080200a02c03807000018000000040040000200000001002000000028040020080280700000c0000100801c0400200000c008000020300080000000401008000024000000000000100500000000003000000000010000000780000a0080000000c00801801bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521fb94a43b7294877d5290fdaa521db54a43bf28c87f65190eeca321df54643faa8c87755190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e85de53d0abca7a15f54f42eea9e855d53d0afca3a15f54742bf286857
  | 3 => 0x7f00006a0000016c0e85780023e1062ac0013100055400000000000000190002e4fc21900000004000000000df0003ac6dc0010a4a4168eb8002ea9a45f89b1fa27d379513a2804c71263caa2c0a1f51da431130eb3c20000025a18200048800000000000000cc234ec8344d80000000000000c0000000000034800000324000722b61580015c000000000000000013680009e001182340000007ca4002e000000004586a4421a3000790000aa00067000000000000d58d41240005300000059c00000000000a28002f80002b87b0000001f0002243593209d37a9791d1cc2a09b87b82d3a0568ef9b30e018c6b8ce35a56000000098a28828000fc0000001c000000e204e000000148000000006c90f0005a8b711a000000ff8ee48c0000690008e8c42e21a064a10a400043824c518004fc388002862320000014d494924a097e0422b4e00a400062c1000000087d2b800076000000003820000023900000000000000000001533d0000001e2000000000002080bd460e8348000e70cd2e2834301c7000000f5000272164000b13b0a404d07950a25861129496000000000009f0000a10000000005d0001000088c10e9fc62000422384c4932000000002100008bcab0e326e9106e2561d8000590000000010b800526000000002f680c000004b05fc0021600093c002143dc000a78003ec000000421f660c000e646c000000ff456548dca02000000000270009f45d0763844d41800031e000000001444a88c1593a400038a8e000000e69681ec2dc0000002a000002090000000007f41412800000000000128000005e000058000000000000000007227b47a6b8788003584f40e8653e0000a6000000000578003f8000000000000000000000000000245000000000002780003520e4364887299213c0a8738003d20000000000004c290fc0008a40012f11403c0019100000062a48000894000000005900386800031cc09e71209ac000000007294900539600008a6000000000000364000b8062000000048000205994a2730c8000cb2133762a4e316212e37c000000005d00002800034800221000000d38984ec000cc082000000000000009e93293f0000014183c00083ce29570000001c8000003a80000000020069800000000000160001e8580004b815400018000620000003a6000fe8001ea0000000c000001330490004b067800000000700003140000000000035400000000000000000006640312e096114a51ef00032d039693a80000008b1de00000000000218c60000000000002c464000cf2244ea7686c12d0004d00022a0003d01b1470002213889c2408ccee2790003e899a740a20e0002430f02f91e21523e280600002be40c000f233e0002200000000000000000000000002c01f5061210d83cc408314826980580000
  | 4 => 0x2d96136a134002530004e90005300000000220066778000de4a87f800190000810000000002f0001a2
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xa320c31d540c830b5584320c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c31d54cc430d354b310c31d544c430b3189310c34d524c430d5945310c31d54cc03097d95300c31d544c030b3189300c27b654c0309798f54c825d63d53209d98754c827561d53209798e54c825d63953209d98453c82756114f20b918542c82cd63087209d987548827561d52209798c548825d63152209d984548827561152209d987538827561d4e208f990538823d6414e209d98453882756114e20b398f42882e5610ca209798e518825d6394620d598e51883556394620d9d0a51883644294620d9cca51883643294620d994721883665148620d9947208825e63951209758e544825f63551209718d544826f62551209dd85544827461551209798e534826f6254d209d98453482756114d2097994534834d6214d20d598453483556114d209b996424834c53909209b195424834c5350920b9185424826e658c920d314e324826c654c920d314d324834c53885209b99421482cd6308520d314c214834c5388120b9986204827761550209d185540825e63150209758c540826e62150209d984540827561150208f990530823d6414c209b98853082766114c209d584530826d65d0820b398f420826d65108209b597320826d650c820b9584320826f65484209bd9520082cc63480209ed95200825e63d53109758f54c426e62d53109b58b54c425e63153109758c54c426e62153109b58854c426e62d4f109b58b53c43566194f109b98853c426d6214f109798f52c425d63d4b10d394e52c434d5394b10d394d52c434d5354b10d918552c425e6314b109758c52c42e46250710d954a31c4356534c710b918931c4365524c710d954b21c42d563087109b98b548426d62d52109798c548425d63152109b988548426d62152109b98b538426d62d4e108f990538423d6414e109b988538426d6214e10d994b41843665210610bc58041842f06150210d994b108425f63551109718d544426f62551109b189544427761551109798c544425d63151109b988544426d62151108fd91534423c6454d109bd89534426c6254d109b988534426d6214d108fd91524423c645491097d8d524425c63549109d99641442746550510b91894144274654c510b918931442f0604c5109d99721442d563085109e19540442e662841109bd89540426c62550109798c540425d63150109b988540426d62150109d984540427a60150109bd89530426c6254c108f990530423d6414c109b988530426d6214c109d984530427661d48108f990520423d64148109798c520425d63148109798e510425d63944109b98a510426d62944109d59741042756510410bc580410426e62940109b58a500427965840109dd95100427b6544010
  | 1 => 0xc66e62953319b58a54cc6cd6290f319bd8950cc66c62543319bd89548c66c62552319b988548c66d62152319e980548c6796015231b9588418c6f160106319b98a508c66d62942319b98a544c66d62951319bd89544c66c62551319ed81544c6786055131b358a434c6d66190d3197195434c71c5450d31d390c524c74d4314931d9584524c74c52cc9319d997414c76452d0531b598c414c6e56210531d9148414c6f160105319b98b540c66d62d50319d987540c65e63150319b988540c66d62150319e980540c6796015031d354b310c765528c43197d95310c74d524c4319dd95310c765524c4319798e54c865d6395321b918542c86e56210721bc58041c865f63543219718d50c865e63152219758c548867a60152219e580548867a60d4e219e58353886ce63d0a21b958432886e4624c621f1cc9318865e63951219758e544866f62551219dd85544863e6494d218f592534866f6254d219b996424866c6550921b9185424866e658c9219b1953248674654c521f14c9314865e63d50219758f540865e63150219758c540866e62150219e9805408679601502197596530874c6254c219798c530866e6214c219d984530866d65d0821b398f420874d53d08219b594420874d53108219b597320874d53cc8219b594320874d530c821b9584320875553d04219d59441087555310421bc580410874d53c8421d554e210866f6548421d354d21086776548421d554d210866e6294f409b58a53d02766194f409d58653d02776154b409d18552d026f62547409b18951d026f6254e409b189539025f6354a409718d529025e63946409758e519026e62946409b58a519031c53d0d40d3d4f525034c53d4940d3d4c525034c5314940d5d4f515035453d4540d9d4b515036452d4540d5d4c51503545314540d9d4851503645214540dc580515034e5394840d354e521034e5354840d354d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d9549511031d53d0040dc546401023f6550040c754d401027b6550040dc545401026e62d53309b58b54cc27661d53309d58754cc26e62953309b58a54cc26f62547309b18951cc26f62552309b189548c27761552309d185548c26e62152309b588548c27661152309d584548c2ce62d0e30b5584328c26e62946309b58a518c2cc624c6309b98a544c26d629513097d8d544c26f62551309b189544c27761551309d185544c25e6590d3097195434c34e4314930d350c524c34c528c1309b98b540c26d62d50309d987540c27561d50308f596540c31c63550308f990540c25e63150309b988540c26d62150309d984540c275611503097597430c31d54d0c30b398b430c25d6510c30c7550430c32e5494830cb552520c32e5454830cb551520c31d548c830d354
  | 2 => 0x364244bc788000000003180000000042800000000980000002dc0000030a00000000000000001800d6001001880723a08e800092000000000980000018a000000840663187f800181000000f49ef0000000000033081c00105000000000000000000000000003ce413732c8540002c0001ccef12d36000000000000000b000033c000418000000008b8122f0000000000001c0001140000000016400022800000000000ef800000000000000001f08986526805c098003540000000000000000000000730001f90005b0920002fc0000000000000061000074000000000007948e000152170bf8f9188000a10001fe858000002785f4e98d0000000d717c0000000000000000200000001000000010020000180000400200000803000034000000000000000000200c000030020000000000000000009000000020020020040080000200001000000000020020000000100400a0000000000200000001000000000000020040000000a00004800004008000000020040100400000400800000000008000000000080100000000800002018020000000040080300000000000002000000000020100100000000001801004000000000060000180100000c00008000004000000000000000000c0000000000600000000000000000000020000000100a00000801000004000010000000080000000003001000006ce62d0e43d994a5190f655294643d99495190f655254643b398b4350e6e62145439b5885150e6e62141439b5885050e7661141439d5845050e3f6550c4397d954310e6f62544439b1895110e6f62540439b1895010e766194f429d58653d0b4d6294f42d598653d0b556194f42b398f4290a7661942429d5865090ace63d09429798c5150a5d6314542d598c5150b556314542d9d085150a3f65508429bd954210ae4615084297d8d5010a5c63540429d98754cca7561d5332b918542cca7761552329d185548cacd6290e32b398f428ca7661942329d586508ca5d63951329b58a544ca7761551329d185544ca7b60551329e181544ca6e65d0932b398f424ca6e65109329b98b540ca7661d50329d587540ca7661150329d584540ca7a60150329e580540ca5d6590c329b596420ca6f6550832b9185420ca5f654c8329bd95320cb564354432d550d510cb664254432d9509510cb573254432d98c9510cb553254432d94c9510ca6e6294f419b58a53d065f63543419718d50d066f62543419b18950d066f6254e419b189539066e62942419b58a509076452d0541d5986531074e5394841d354e521074e5354841d354d521076461548418fd9541106776550441b9189411075a5394041d654e501076a5294041da54a501075a5354041d654d501076a5254041da54950107724154041dc505501066e62d53319b58b54c
  | 3 => 0x13000000000b690a00069c158ee34402c000000007d400000000000000000000000000000070caf00037200021966000000a9800000000b4800000000b7056000358eb000192000000000000000002a0003c0000810002ac000000946c8000001b600000000000000f805d0002b8749e70d43d41700826c34800000000000e280018a640001840220000000000000103000298168001f30001f40e982000000fc14e000000d00000000000000042200000191418000000000e80000011b000000000001cc7eca800000000000000000000ba15b0004242400013200000000000000b980016600000000000000000001420f88f0001aa66ca50000801ec340041747c4d2892186764930cc00c00000000000000000001380000000000e000cb81600053c000901546ec0019a13e6bc000003285dc0015d10c00000000000000a2900000000000000003c8001180000003083b1e86182300039a000000000e4000000000002d88d000000144e10000004f805000000000000f604a61c000000002d0000bd000000000340420000000000000000000000000000cf3d00000000000000000000000000000f3000000000300b200000000000000000002864b830000000000458840000000000000024c0000000005102000000000000000fe000bb0003aa00000125356000f18000007b0000ef00000000000000000000950004e800000290000000000000000000026a584d4a08000000000d30000008319304825c00000000000001ad0002000000000041c0001b1d6000001892804ac279ca00026c940000000000000c00000000000000000000000007f400000000000de9442f6534001d0000000370003c02f800000000000000000000a46b91f000000728003484fc000fe01c6e05380041e000588b9194230000bb3801d45c158000378000000003800000034c31cf5000306000b28000004446d0000000009c000000224000b50000000021a3ba000258520005c00e000000000e58b00000003613900000099000000391058e109c55800000000000000190000001101e00000000000000000000000000000000000000000058266000001e6000000001c6000738001190000000006d33a0000000015e000561a30a000000000324000000000006e8000003fe49c0000000000053087000000bc87800000000171000000000003f8000000000fc0000000000017c0000000068400000000000000ed0000000015a11c62c861c700037cb5800000000000ad00000000000000000ec0002440000016f13400000000000000f9000000000001ac000000321b7000484001dc37c7d800000000280002171b82fc0000011e0000000036a000210e7000838a598d000000001552a80540001000074800000000000000000000b4000000660000000020600000
  | 4 => 0x80cba841000000f21d112c1c44405e0004a8988d807e000a09630000008099909a11ce21160ec0000006f000250488004320000001821c51c1a8002ae000a30000000000000000000000000000001050090003a80000000000087800000000fb800000000001041d800c6a0570000c4000000000f00000000000000000000000000000000000000000000000000150000001e1000000001cf0d200000000000000001ee00000065800382000000000000000000001a000918000007e86e8000000002a9020000000015200000109838000000ea0000000000d000000000000000000000f8000000001e8002e400000000000000001bc0000001016a000000000000000001b85400054400000000000000fb4026d04100000009c3b832000000881120000000000008a000010000000000000000000066800000000000000000000000000000000000000000000000c4000298002f42340000000000000000000860000000000000000000000000000000000000f8000000518000004345e000000670858a40000000005b2408404f000000000000000000bc0000018c57c1196800a3e8000d90004a452800000000000003da0a000000000570000001a20000000000000000000000000eb9b60007690687a2926fc0000031e58902a14276454f5879180274ca800000000d88a2350000718fc000000000000007d1010f73b6724000000002c80000000000000000000000000002b2000f1000000000000001c40040019f27a00000000412000000c800000000000000000b38670000004c1b3088000000c119c0000012c000000c70fd000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x50e18255744328c2530016161003d00004802c8340147000204010051915896194f42a8ce7a10a2a14c57198f424caa2b98c2a9083581c941540418caec2908298e6052580414c662b98c2a124313dd953d0821c8aa6b086410e51535804108706aa4c5a186185551610c830c1aa8312621860d54189300c2a339e8528c41515ce5148620c8ac4b08a6906445318542482a2b88a699241135d85308520c88a730c40905457318552c42323b2a498e21989496010610
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x190100845869cf4214542845869cf42946208458714c61509208458714e6188120
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1164)*11) 11
  | 4 => packedAt s5K4 (22451+((h/179+packedAt s5K4 (20482+(h % 179)*11) 11) % 1383)*11) 11
  | 3 => packedAt s5K3 (1265+((h/8+packedAt s5K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe07ff0ffffffe0f0e1fc3f03ffffffc09cfff
  | 1 => 0x3ff83ff1e07c3ff00fe3fc7fc1f0f03e367267
  | 2 => 0x3fffc001ff803ffff003ff8001ff003fc78387
  | 3 => 0xc0000001ffffc3fffffc000001ffffc3f803f8
  | 4 => 0xfffffffe000003fffffffffffe000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x82308210210800010204c0908c31118400c4ab
  | 1 => 0x94518c8247114a3046a1542384d8a2aa125265
  | 2 => 0x18a316a48a39b2d750839905196a8532c78386
  | 3 => 0x11c628c914611b6a6cc8100a218cce23780350
  | 4 => 0x210430001842218c8912224c30000801ad2800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeeaa80feeeaa80feeeaa80feeeaa80feeeaa80feeeaa80feeeaa80feeeaa80feeeaa80feeeaa80feeeaa80feeeaa80feeeaa80feeeaa80feeeaa80feeeaa80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37363
namespace PEqualNP.Outside.L_meta_37363
open PEqualNP.Outside.L_meta_37363.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c180017fd50057f54017f95005fd54005f55005fc5400ffd4c03fe5300ff54c03fc5300ffd0c03fe4300ff50c03fc43017fd4805fe52017f54805fc52007fd0801fe42007f50801fc4200ffcc803fe3200ff4c803fc32017fd4405fe51017f54405fc51007fd0401fe41007f50401fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc50007fd0001fe40007f50001fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xc2003bf98210067fea108013fe5084019fea842004ff14210007fe8108013fe4084001fd2042000ff50210007f28108013fc408400fff9842004ff8c21003ffa6108013fc3084001ff9042004ff88210007fa4108013fc2084007ff8842000fdc421001ff6210802fff65440177fb2a200bff99510015fcca8802ffd65440177eb2a200bff19510015f8ca88003ff64440017fb222000ff9911004dfcc888003fd64440017eb222000ff1911004df8c88802fff5444017bfaa2200bff9511005ffaa8880037d5444017fe2a2200affd8d10055fec68802bfe63440037f31a200aff58d10055fac68802bfc63440037e31a200affd4d10057fca68802bfd5344015fe29a200affd0d10057fc868802bfd4344015fe21a2000ffd8910005fec488003fe62440117f3122000ff58910005fac488003fc62440117e312200bffd491005ffca48802ffd5244017fe2922000ffd0910007fc8488003fd4244001fe212200affcc910057fc648802bfd3244015fe192200bffd451001ffca28802ffd5144007fe28a2000ffd051001ffc8288003f64144001fea0a2000fd5051001ff8828802bff3144007ff18a200afd8c510057fa628802bf53144007fe18a2000ffc851001ffc4288003fd2144007fe10a200bffd411005ffca08802ffd5044017fe2822000ffd0110007fc8088003fa4044001fea022000fe50110007f8808802bff3044015ff182200aff4c110057f86088003ff2044001ff1022000ff48110007f8408800fff1044007fd8822000ff84110007ec2088013ff65040077fb282003ff99410015fcca0800ffd650400d7eb282004ff1941001df8ca08013ff64040077fb202003ff9901004dfcc80800ffd64040017eb202004ff1901001df8c80801bff540400dbfaa02006ff95010037faa8080037d540400dfe2a02004ffd8c1001dfec60800ffe63040037f3182003ff58c1002dfac608013fc63040077e3182005ffd4c1002ffca608017fd530400bfe2982005ffd0c1002ffc8608017fd430400bfe2182004ffd881001dfec40800ffe62040117f3102003ff58810005fac408013fc62040077e3102006ffd4810037fca40801bfd520400dfe2902000ffd0810007fc8408003fd4204001fe2102005ffcc81002ffc6408017fd320400bfe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff0841003dfcc00801bff5004009ff2802006ff54010027f8a008003ff4004009ff2002000ff50010027f88008017ff3004009ff1802005ff4c010027f86008003ff2004009ff1002000ff48010027f8400800fff1004007fb8802004ff8401001ff4200800ffd1004001fa8802003fe44010
  | 1 => 0x3fe61080077f3084008ff58420005fac210013fc6108021ffa884010ff94420087faa210043fc5108001ffa084000ff90420007fa8210003fc410801fff988400fff8c42007ffa621003ffc3108011ff9084008ff88420047fa4210023fc21080237f3004010ffd4020027fca010043fd5008009fe2804000ffd0020027fc8010003fd4008009fe200400fffcc020027fc601003ffd3008009fe1804008ffc8020047de4010013fe2008011fd1004008ff48020007da4010023f92008007ffb2e2003bfd971001ffccb8800afe65c4007feb2e200ebf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc988026fe64c4007feb262000bf5931001ff8c98800efc64c401dffaa6200edfd5310077fca98803bfd54c4001beaa6200eff1531001ffec78800eff63c4007ff31e2001bf98f1001fbcc788006de63c4007feb1e200dbf58f1001fbac788002dd63c4007fe31e2003bf18f1006ffea788037fe53c401bfea9e200dff14f1006ffe8788037fe43c401bfea1e200dff10f1001ffec58800eff62c4007ff3162008bf98b1001ffac588002fd62c4007fe3162003bf18b10077fea58803bfe52c401dfea96200eff14b10007fe8588003fe42c4001fea162000ff10b1006ffe6588037fe32c401bfe996200dff0cb1001ffea38800ffe51c4007fea8e2003ff1471001ffe838800ffe41c4007fb20e2003ff50710007ea838800ffc41c4007ff98e2003ff8c71001fec638800ffd31c401bfa98e2003ff0c71001ffe438800ffe21c4007fe90e2003ff08710077fea18803bfe50c401dfea86200eff14310007fe8188003fe40c4001fea062000ff1031006ffe6188037fe30c401bfe986200dff0c310007fe4188003fe20c4001fe9062000ff08310027fecb08032ff6584019ff32c2002bf99610066fccb0800a7e6584019feb2c200cbf59610006facb080027d6584009fe32c2002bf19610027fec908002ff6484001ff3242009bf99210007fac908002fd6484009fe3242009bf19210067fea9080337f5484019ff2a4200cff55210006faa908033fc5484009ffb1c2007bfd8e1003ffcc708006fe638400ffeb1c2007bf58e10027f8c708006fc638400fffa9c2007ff94e1003ffaa70801ffc538400fffa1c2007ff90e1003ffa870801ffc4384009ffb142000bfd8a10007fcc508022fe6284001f73142000bb98a10007fac508002fd6284001f6b142000bb58a10027f8c508022fc6284019ffa94200cff94a10067faa508033fc5284001ffa142000ff90a10007fa8508003fc428400fff9942007ff8ca1003ffa650801ffc32840157eb0c200cffd461001ffca308033fd5184007fe28c2000ffd061001ffc8308003fd4184007fe20c2007ffcc61001ffc630801ffd3184007fe18c2000ffc861001ffc4308003fd2184007fe1
  | 2 => 0x20027f8c710006fc6388023ffa9c4011ff94e2008ffaa710047fc5388023ffa1c4011ff90e2008ffa8710047fc43880257eb144014ffd4a20047fca510053fd5288011fe2944000ffd0a20047fc8510003fd4288011fe2144011ffcca20047fc6510047fd3288011fe1944004ffd8620007fcc31000efe6188001feb0c4000bf58620027f8c310053ff5188029ff28c4014ff546200a7f8a310003ff4188001ff20c4000ff50620007f88310047ff3188023ff18c4011ff4c62008ff86310023ff2188001ff10c4000ff48620047f84310022fe6088029ffa844004ff942200a7faa110013fc5088001ffa044004ff90220007fa8110013fc4088023ff9844004ff8c22008ffa6110013fc3088011ff9044000fbc8220047f6411004fff65480277fb2a4000dfd9520004feca9004ffe65480057f32a4013ff5952009dfaca9004ffc65480057e32a4013df19520014f8ca90003ff64480017fb224000ff9912004dfcc890003fd64480017eb224000ff1912004df8c89004fff5448027bfaa24013ff9512009ffaa8900037d5448027fe2a24012ffd8d20095fec690003df63480016fb1a4012ff98d2000dfcc69004bfd63480257eb1a4012ff18d2000df8c69004bdc63480036e31a4012ffd4d20097fca69004bfd5348025fe29a4012ffd0d20097fc869004bfd4348025fe21a4013ffd4920047fca49004fee5248027fea924013fb54920047f8a490003ff4248011ff2124000fb90920007fa8490003ed4248011fe2124012ffcc920047fc649004bee3248025fe9924012fb4c920047f86490003ff61480017fb0a4000ff98520007fac290003fc61480077e30a4013ffd452009ffca29004ffd5148027fe28a4000ffd0520007fc8290003fd4148001fe20a4012ffcc520097fc629004bfd3148025fe18a4008ffc8520007fc4290003ee2148001fe90a4008ff08520007d8429004fff5048027ff2824013ff5412009ff8a090003ff4048001ff2024000ff50120007f8809004bff3048025ff1824012ff4c120097f86090023ff2048011fd9024000ff88120007dc4090013ff65080117fb284008ff99420015fcca100237e65080053f3284008ff59420085faca100237d65080013eb284004ff19420045f8ca10013ff64080117fb204008ff9902004dfcc810023fd64080017eb204004ff19020045f8c810043ff5408021bfaa04010ff95020087faa8100037d5408021fe2a04004ffd8c20045fec610023fe63080037f3184008ff58c2007dfac610013fc63080117e318400fffd4c2007ffca61003ffd530801ffe298400fffd0c2007ffc861003ffd430801ffe2184008bf98820047fea410023fe5208011fea904008ff14820047fe8410023fe4208011fea104008ff10820047fe6410023fe3208011fe9904008ff0c820027fec21002
  | 3 => 0xfb288009ff99440015fcca200277e65100053f3288009ff594400c5faca200277d65100013eb288004ff1944004df8ca20026fe6410013ffaa08009dfd504004ffca820027fd5410013beaa08009ff15040027fec620026ff6310013ff3188001bf98c4004fbcc620006de6310013feb188017bf58c4004fbac620002dd6310009fe3188001bf18c400bffea62005ffe531002ffea988017ff14c4004ffe8620027fe4310013fea188009ff10c40027fec420027fe62100117f3108009fb98840005dcc420027fd62100017eb108009fb58840005dac420013fc6210031ffa908018ff948400c7faa420063fc5210013ffa108009ff9084004ffa8420027fc421002fff9908017ff8c8400bffa642005ffc3210009ffb088009ff9844001dfcc220027f661100017b3088009ff58440005fac220027f561100017ab088004ff184400c7fea220063fe5110031fea888018ff1444004ffe8220027fe4110013fea088009ff104400bffe622005ffe311002ffe9888017ff0c440007fe4220003fe2110001fe9088000ff084400cdfcc020063ff5010009ff2808018ff54040027f8a020027ff4010013dfa008004ff9004004ff48020027fd4010001dea008009fe500400bffe6020013fe301002ffe9808004ff0c040047fecb90022ff65c8011ff32e4002bf99720047facb9005afd65c8011fe32e4008bf19720047fec990022ff64c8011ff3264009bf99320047fac990002fd64c8011fe3264008bf193200b7fea99005b7f54c802dff2a64016ff55320006faa99005bfc54c8011ffb1e4008bfd8f20047fcc790006fe63c8011feb1e4015bf58f20047f8c790022fc63c802bffa9e4015ff94f200affaa790057fc53c802bffa1e4015ff90f200affa8790057fc43c8011ffa964008ff94b20047dca590023fd52c802df6a964008ff14b20047fe8590023fe42c8011f72164008ff50b20007da8590023fc42c8011ff9964008ff8cb20047dc6590023fd32c802bf69964008ff0cb20047fec390023fe61c80077f30e4008ff58720005fac390023fc61c802dffa8e4016ff947200b7faa39005bfc51c8001ffa0e4000ff90720007fa8390003fc41c802bff98e4015ff8c7200affa6390057fc31c8011ff90e4008ff88720007dc4390023fd21c8011fe10e4008fb087200b7fea19005bfe50c802dfea864016ff14320007fe8190003fe40c8001fea064000ff103200affe6190057fe30c802bfe9864015ff0c320027fecb10052ff6588029ff32c4002bf996200a7facb10052fd6588009fe32c4002bf19620027fec910002ff6488001ff3244009bf99220007fac910002fd6488009fe3244009bf192200a7fea9100537f5488029ff2a44014ff55220006faa910053fc5488009ffb1c4011bfd8e2008ffcc710006fe6388023feb1c4011bf58e
  | 4 => 0x27bf43d0013ff21e8009ff50f400ef7a87a0027fc43d0013ffb168009ff98b40045fcc5a0027fd62d00017eb168009ff18b400f7fea5a007bfe52d003dfea96801eff14b4004ffe85a0027fe42d0013fea168009ff10b400effe65a0077fe32d003bfe996801dff0cb4004ffec3a0027fe61d00077f30e8009ff58740005fac3a0027fc61d003dffa8e801eff947400f7faa3a007bfc51d0013ffa0e8009ff9074004ffa83a0027fc41d003bff98e801dff8c7400effa63a0077fc31d0001ff90e8000ff88740007fa43a0003fc21d003dffa86801eff943400f7faa1a007bfc50d003bff986801dff8c3400effa61a0077fc30d0009ffb2c801cbfd96400e7fccb2000afe6590039feb2c801cbf59640027f8cb2000afc65900357eb24801cffd52400e6fea920027fe5490039feaa48000df5524004ff8a920013ff63900337fb1c8019ff98e4000dfcc720067fd63900337eb1c8004ff18e4000df8c720067ff5390033ff29c8019ff54e400cff8a720027ff4390033ff21c8019ff50e4004ff88720013ff6290001ff3148008bf98a40007fac520002fd6290009fe314801cffd4a400e7fca520073fd5290039fe2948009ffd0a40007fc8520003fd4290013fe2148019ffcca400cffc6520067fd3290033fe1948004ffd8640007fcc32000efe6190001feb0c8000bf58640027f8c320073ff5190039ff28c801cff546400e7f8a320027ff4190001ff20c8000ff5064004ff88320067ff3190033ff18c8019ff4c6400cff86320003ff2190001ff10c8000ff48640007f84320026fe6090039ffa848004ff942400e7faa120013fc5090013ffa048000efd024004ff68120067ff3090009ff1848019ff4c240027f8612006fff65500377fb2a801bff99540015fccaa006ffd65500377eb2a801bff19540015f8caa006fff5450037bfaa28009ff951400dffaa8a00037d5450013fe2a2801affd8d400d5fec6a006bfe63500037f31a801aff58d400d5fac6a006bfc63500037e31a801affd4d400d7fca6a006bfd5350035fe29a8009ffd0d400d77e86a006bfe4350035fea1a801aef50d4004ff886a0003ff62500017fb128000ff98940007fac4a0003fc62500117e312801bffd49400dffca4a006ffd5250037fe2928009ffd0940007fc84a0003fd4250013fe212801affcc9400d7fc64a006bfd3250035fe1928000ffd8540005fec2a0003fe6150001feb0a8000ff1854001df8c2a006fff5150037ff28a801bff545400dff8a2a0027ff4150001ff20a8000ff5054004ff882a006bff3150035ff18a801aff4c5400d7f862a0003ff2150001ff10a8000ff48540007f842a006fff5050037ff282801bff541400dff8a0a0027ff4050013fda028000ff901400077c80a006bff3050035ff182801aff4c1400d7f860a0013ff65100137
  | 5 => 0x822101ffac110802fd6088407fe3044224ffd4221127fca110893fd5088449fe2844223ffcc22111ffc611088ffd3088447fe1844222ffd9521115feca908037f65484013fb2a4222ff99521015fcca9088bfd65484457eb2a4222ff19521015f8ca9088b7c65484053e32a4200ffd9121005fec890803fe64484137f3224200ff59121005fac890803fc64484137e3224222ffd5121116fea89088bfe5448445feaa24200df55121117f8a890887ff63484437fb1a4221ff98d2100dfcc690887fd63484437eb1a4221ff18d2100df8c690887ff5348443ff29a4221ff54d2110ff8a690887ff4348443ff21a4221ff50d2110ff8869088bff5248411ff2924222ff54921047f8a490803ff4248411ff2124200fb90921007fa8490803ed4248411fe2124221ffcc921047fc6490887fd3248411fe1924222ffd452101ffca29088bfd5148407fe28a4200ffd052101ffc8290803fd4148407fe20a4221ffcc52101ffc6290887f63148443fe98a4221fd4c52101ff86290823ff2148411fb90a4203ff8852101fdc4290803ff60484017fb024200ff98121007fac090803fc60484017e3024222ffd4121117fca09088bfd5048445fe2824221ffcc12110ffc6090887fd3048443fe1824203ffd942101dfeca1080ffe65084057f3284203ff59421105faca1080ffc65084077e3284203ffd902101dfec81080ffe64084137f3204203ff59021005fac81080ffc64084077e3204220ffd5021106fea810883fe5408441feaa04200df55021107f8a81080fff63084077fb184203ff98c2100dfcc61080fde63084036f3184203ff58c210fdfac61080fdd63084016eb184203ff18c2101df8c61087fff530843fff298421fff54c210fff8a61087fff430843fff218421fff50c210fff88610822fe6208411ffa904208ff94821047faa410823fc5208411ffa104208ff90821047fa8410823fc4208411ff990421ffbcc821047fc6410823fd3208411fe1904208fb0c82101dfcc21080fff5108407ff2884203ff5442101ff8a21080fff4108407ff2084203ff5042101ff8821080fff3108407ff1884203ff4c42101ff8621080fff2108407f79084203ff8842101fec421080ffd2108407f69084208fd4842101ffec01080ffe60084017f3004203ff58021005fac01080ffc6008441ffa804220ff94021107faa010883fc500843fff980421fff8c0210fffa601087ffc3008413ffb2e8009bfd974004ffccba000afe65d0013bf32e80029f9974004ffacba007afd65d0013beb2e80009f5974004ff8cba0026fc65d0013ffaa68009dfd534004ffca9a0027fd54d0013beaa68009ff1534004ffec7a0026ff63d0013ff31e8001bf98f4004ffac7a0076fd63d0013fe31e8001bf18f400effea7a0077fe53d003bfea9e801dff14f4004ffe87a0
  | 6 => 0x7eeb188200b758c4101ff8c62080efc631044fffa988227ff94c4113ffaa62089ffc5310413ffa188209ff90c4104ffa8620827fc4310407ffb108203ff98841045fcc42080fee6210401773108203ff58841005fac42080fed621040176b108203ff18841147fea4208a3fe5210451fea908228ff1484104ffe8420827fe4210413fea108209ff1084113ffe642089ffe321044ffe9908227ff0c84101dfcc22080fff5110407ff2888203ff5444101ff8a22080fff4110407dfa088203ff9044101fec822080ffd4110407dea088209fd5044101ffe622080ffe3110407fb1888203ff4c44113fea622080ffc3110407ffb008203ff98041005fcc02080ffa60104017d3008203ff58041005fac02080ff960104017cb008203ff18041147fea0208a3fe5010451fea808228ff1404113ffe602089ffe301044ffe9808227ff0c041047fecb90822ff65c8411ff32e4202bf99721047facb9089afd65c8411fe32e4208bf19721047fec990822ff64c8411ff3264209bf99321047fac990802fd64c8411fe3264208bf19321137fea99089b7f54c844dff2a64226ff55321006faa99089bfc54c8411ffb1e4208bfd8f21047fcc790806fe63c8411feb1e4225bf58f21047f8c790822fc63c844bffa9e4225ff94f2112ffaa790897fc53c844bffa1e4225ff90f2112ffa8790897fc43c8411ffa964208ff94b21047faa590823fc52c8411ffa164208ff90b21047dc8590823fd42c8401f6a164208ff10b21047fe6590823fe32c8411fe9964208ff0cb21137fea39080ffe51c844dfea8e4203ff14721007fe839080ffe41c8401fea0e4203ff1072112ffe639080ffe31c844bfe98e4203ff0c721047fec190823fe60c84017f3064208ff58321005fac190823fc60c844dffa864226ff94321137faa19089bfc50c844bff9864225ff8c32112ffa6190897fc30c8407ffb2c4203bfd962101ffccb1080afe6588407feb2c4224bf5962101ff8cb1080efc6588407ffb244203bfd922101ffcc910826fe6488407feb244200bf5922101ff8c91080efc6488449ffaa44224dfd5221127fca910893fd5488401beaa44224ff1522101ffec71080eff6388407ff31c4201bf98e2101ffac71088efd6388407fe31c4203bf18e2111ffea71088ffe5388447fea9c4223ff14e2111ffe871088ffe4388447fea1c4223ff10e2110dfac510893ff5288411ff2944224ff54a21047f8a510803ff4288411ff2144200ff50a21047f8851088fff3288447f79944208ff8ca2111ffa6510823fc3288447f61944203bf9862101ffea31080ffe5188407fea8c4203ff1462101ffe831080ffe4188407fea0c4203ff1062101ffe631080ffe3188407fb18c4203ff4c62111fea631080ffc3188407ff90c4203fbc8621047ee431080fff6088407ff3044200bf9
  | 7 => 0xa0827fe43d0413fea1e8209ff10f4104ffec5a0827fe62d04117f3168209ff58b41005fac5a0827fc62d045dffa96822eff94b41177faa5a08bbfc52d0413ffa168209ff90b4104ffa85a0827fc42d045bff996822dff8cb4116ffa65a08b7fc32d045dffa8e8203ff94741177faa3a080ffc51d045bff98e8203ff8c74116fec63a08b7fd31d045bfa98e8203ff0c74104ffec1a0827fe60d04017f3068209ff58341005fac1a0827fc60d045dffa86822eff94341177faa1a08bbfc50d045bff986822dff8c34116ffa61a08b7fc30d0407ffb2c8203bfd964101ffccb2080afe6590407feb2c822cbf5964101ff8cb2080efc65904537eb24822cffd5241166fea920827fe5490459feaa48200df5524104ff8a92080fff63904077fb1c8203ff98e4100dfcc72080ffd63904577eb1c8203ff18e4101df8c7208afff5390457ff29c822bff54e4115ff8a720827ff4390457ff21c822bff50e4104ff8872080fff6290407ff3148208bf98a4101ffac520802fd6290407fe314822cffd4a41167fca5208b3fd5290459fe2948209ffd0a41007fc8520803fd4290413fe214822bffcca4115ffc65208affd3290457fe1948203bf9864101ffea32080ffe5190407fea8c8203ff1464101ffe832080fbf4190413fba0c8203ffcc64101ffc632080ffd3190407fe18c8203ffd824101ffcc120802fe6090407feb048200bf5824101ff8c1208b3ff5090459ff284822cff54241167f8a1208afff3090457ff184822bff4c24115ff861208abff65504557fb2a822aff99541015fccaa08abfd65504557eb2a822aff19541015f8caa08abff5450455bfaa28209ff95141157faa8a08037d5450413fe2a28229ffd8d4114dfec6a08a7fe63504037f31a8229ff58d4114dfac6a08a7fc63504037e31a8229ffd4d4114ffca6a08a7fd5350453fe29a8209ffd0d4114ffc86a08a7fd4350413fe21a8200ffd8941005fec4a0803fe6250401feb128200ff18941045f8c4a08abff5250455ff292822aff54941157f8a4a0827ff4250401ff2128200ff5094104ff884a08a7ff3250453ff1928229ff4c94114ff864a08abff5150407ff28a822aff5454101ff8a2a0827ff4150413fba0a8203ff9054101f7c82a08a7ff3150407ff18a8229ff4c54101ff862a0803ff60504017fb028200ff98141007fac0a0803fc60504017e302822affd4141157fca0a08abfd5050455fe2828229ffcc14114ffc60a08a7fd3050453fe1828203ffd944101dfeca2080ffe65104057f3288203df99441014fcca2080ffd65104517eb288203df59441004faca2080ffc65104077e3288209bf9904104ffea8208277f5410413ff2a08209ff5504104efaa820827fc5410407ffb188203bfd8c4101ffcc620806fe6310407ef3188201b798c4101ffac62089efd631040
  | 8 => 0xf94a42047faa521023fc5290811ffa148408efd0a4204fde8521023ff3290867f79948408ff8ca42047fa6521023fc3290811f61948408ffd8642047fcc32100efe6190811feb0c8400bf58642047f8c3210d3ff5190869ff28c8434ff546421a7f8a3210cfff3190867ff18c8433ff4c64219ff86321023ff6090811ff3048400bf98242047fac121002fd6090811fe3048434ffd42421a7fca1210d3fd5090869fe2848433ffcc24219ffc61210cffd3090867fe1848432ffd9542195fecaa10cbfe65508057f32a8432ff59542195facaa10cbfc65508057e32a8432ffd5142196fea8a1027fe5450865feaa28400df5514204ff8a8a10c7ff63508637fb1a8431ff98d4200dfcc6a10c7fd63508637eb1a8431ff18d4200df8c6a10c7ff5350863ff29a8431ff54d4218ff8a6a1027ff4350863ff21a8431ff50d4204ff886a10cbff5250811ff2928432ff54942047f8a4a1027ff4250813f7a128408ff909420477c84a10c7ff3250863f79928408ff8c94218ffa64a1023fc3250863f61928400ffd8542005fec2a1003fe6150801feb0a8400ff1854201df8c2a10cbff5150865ff28a8432ff54542197f8a2a10c7ff3150863ff18a8431ff4c54218ff862a1003ff60508017fb028400ff98142007fac0a1003fc60508017e3028432ffd4142197fca0a10cbfd5050865fe2828431ffcc14218ffc60a10c7fd3050863fe1828408ffd9442045feca21023fe65108057f3288408df99442014fcca21023fd65108617eb288408df59442004faca21023fc65108117e3288409bf9904204ffea8210277f5410813ff2a08409ff5504204efaa821027fc5410811ffb188408bfd8c42047fcc621006fe6310811feb18842fbf58c42047f8c621022fc631085fffa98842fff94c4217ffaa6210bffc5310813ffa188409ff90c4204ffa8621027fc43108117f3108408ffd4842047fca421023fd5210811fe2908408ffd08420477e8421023fe4210811f72108408ff508420477a8421027ed4210811ff9908408ff8c842047fa6421023fc3210811ffb088408ff9844201dfcc221023fd61108017eb088408ff18442187fea2210c3fe5110861fea888430ff1444217ffe62210bffe311085ffe988842fff0c442047fec021023fe60108017f3008408ff58042005fac021023fc6010861ffa808430ff94042187faa0210c3fc501085fff980842fff8c04217ffa60210bffc3010813ffb2e8209bfd974104ffccba080afe65d0413bf32e82029f9974104ffacba08bafd65d0413beb2e82009f5974104ff8cba0826fc65d0413ffaa68209dfd534104ffca9a0827fd54d0413beaa68209ff1534104ffec7a0826ff63d0413ff31e8201bf98f4104ffac7a08b6fd63d0413fe31e8201bf18f4116ffea7a08b7fe53d045bfea9e822dff14f4104ffe87
  | 9 => 0x800080080b00380080080180280080080500000000000200100200a80800000700200500180500000a00100b00180080080480100280180900500000200000180b80101200280280000000000980800080300381200200800000a80900000000200800400301800200000080000000002a00000100280b00100480a81800100080a00000580b80000001700100080084500101480600080400000500700480480000000200000e00280180a80001680000000100480980180180200280700080081c80280001000000000200281280200000001081380000380200980201d00000380a00000080000200000900080000380300280380080380180200280500082000000300f80080700080f00000080180100181400000100602f00280101700580200380000300880180e00000000080000c80180180800000000200b00200080000180180000800180400100100000300480080000100180000180080580000100380500101c02900f00800000b7f64550053fb22a802cfd91541befec6aa0df7e635506fbeb1aa837df18d5404efe86aa0df7e435506fbea1aa809df10d54006fec4aa0037e6255001beb12a800df189541befe64aa0df7e325506fbe992a837df0c954006fec2aa0037e6155001beb0aa800df185541befe62aa0df7e315506fbe98aa837df0c554006fec0aa0037e6055001beb02a800df181541befe60aa0df7e305506fbe982a837df0c15404ffecba1026ff65d0813ff32e8402bf9974204efccba100a7e65d0813feb2e8436bf5974204efacba10027d65d0813fe32e8409bf1974204ffea9a10277f54d0813ff2a68409ff5534204efaa9a1027fc54d0813ffb1e8409bfd8f4204ffcc7a1006fe63d0813ef31e8401b798f4204ffac7a10d6fd63d0813eeb1e8400b758f4204ff8c7a1006fc63d086bffa9e8435ff94f421affaa7a10d7fc53d0813ffa1e8409ff90f4204ffa87a1027fc43d086dffa968408ff94b421b7faa5a1023fc52d086bff9968408ff8cb421affa65a1023fc32d0813ffb0e8409ff9874201dfcc3a1027fd61d08017eb0e8409ff187421b7fea3a10dbfe51d086dfea8e8436ff147421affe63a10d7fe31d086bfe98e8435ff0c74204ffec1a1027fe60d08017f3068409ff58342005fac1a1027fc60d086dffa868436ff943421b7faa1a10dbfc50d086bff9868435ff8c3421affa61a10d7fc30d0811ffb2c8408bfd9642047fccb2100afe6590811feb2c8434bf59642047f8cb21022fc65908637eb248434ffd52421a6fea921027fe5490869feaa48400df5524204ff8a921023ff63908117fb1c8408ff98e4200dfcc721023fd63908677eb1c8408ff18e42045f8c7210cfff5390867ff29c8433ff54e4219ff8a721027ff4390867ff21c8433ff50e4204ff88721022fe6290811ffa948408f
  | 10 => 0xfa80002940188000f783e021d1c2c1ca47908a800062a52a3f486cc6480001c703b8a1c2ca16c0f08a4400026d17d40005b327918440006e600012b000067b0ea8000e44000000000000077000008ac97041b1e7800041c5013580fb026c35e1260000a7e0690000000dae00c4210ed046440c00001dc75656900011644185d90000000fb200006a00000006120f981210743f700017b8b325b52bb0528b742b910489f04ce00000008ec7441543fd1da400055b03d17d07bc6b22020e4ce3e0b833392e800055406f9a944ec5311931c944746b71ad8ce4b5065337ba1341300ef2348dec32442d0c690bce263c31ed809c9a45500560b105464a922311bc5e65c916d1608d8808b39f1fc40001393e40b9400000041e91550045a20000000742649105902489a3982b5041419816041a1f4007039b32781f00005713d914406ea81600380280400300700300000180700100000080000081400280780080100200000c80980480000000380200580002100080001b81600000180c00600a00000001281580100500100200880080000400000000000480180400080480980000900000900000000080a00000300981900000180d80200200000480281b00000c00280380080000780a80400500100480080000201600780200480000280080000000080080200100b80680001800380000000000100080c00680000580300300600101380380700600080000400000400a82580300f80000000200180680200000000400201080100680180f05200800a80480e00002380200d80000380500000000380000100001200581080000280600000180280100080080000380f80080081980000380081a80000100080580000400600180a80700080180180e00080e80300000100380000480c00680580282000c80000280180000280200980100180580200600202080000380100400080000000b80180200100500f00100400180080180000000000780200781980100480480000180000280a80600102c80000280580100080080781180200000180000780380100e00000100000280300100000880300080400180200100000300081100b80000880200000680100700380002e00100980500100e00080680380500580680000080800080080580000000000100a80600780000082280000480080100080600080100400200180380480080e80080080000381780200101000000c80180400200000000200800300300000080580300080080100300000000000880080300000000500000180000100000000480000680080400a80380a80100180080100580000000480000300180300200000000280480100580101001880e00000000f80500300000200501680100701400a00d80000580200200180000900981b80280102100181080c0068028008028
  | 11 => 0x183214868cdaa1860cb01d40005e015a93a8bec8473c68cfc81e8111a094840005e200010c02ac78620015d4d264d9319018093815c380190c00071a3b1977cc0e6e21a5047c00035300007dc07227f1a39ad8ea800000000006fa0001d1800077805d000063c34e46b000000000030a2ed00000000003bc988c0ca1e8264007826a06e2c8871c8be0ec1050f2c1f44600b298a0f9838c2481f6cd12450000000048e5161d91b083682d11118f7000000011300010760001c51f9400000009400000000ed155859d09c4b30fd80004600001828000e221a9322105c34c1ba000000070e55128f14f40003f412514ec7e41b01e39c548042571fe024083c0002ac988806a7a101e1b042a60d84120c6000079524a00006da016282177496a2e70000af000000000017780007473d800006cc240000000000005a1ba1d44856536000136cc185b00001304bae297000076400055d3be1104b9e0000e88138a3479a30e0e246345fa000110c0007c510d07f418e62f0e50a2c22009f31b02242e20003fa00004e80d12298d00e920000001ca82785bf1ae11f400029340d9f384e40003c80adc65a0000001b6400082b051957c0000000000000b8e73c27c94c00002430bc005c0a000021d94d0ffa61526506644de0003358000f5682e00000009cc76c41b0720f8261029c94e800003a1ac000108250020880009c87ac02199383d885102f185c1e20a50ca9e6c53a09a0d584dc00000005a87f81226d200019049be22500014b50885700000d2c5ba4620e0800033a0000e180000003821589864b403f30c100008d85852c5800405034e2c68000a587750e60f44d2e63c3751c3c0043972c41280b4e4a82460d88e562ac3ee95b024e6841298dc05a480507489c40007e73520000fea7d3221000077c48a0000848e5e00000000002ae2ce3a9005006c0000001bb00000003eb8638c1000032b0000df868124384200004b21289b68e964380619c847c871633e0b582c84e21db9890cca19427181b4aca3092618bb10720472c52114de66ad3b20f0062e25a07e9a6c000481396800021444c13d808c0a416100009a40001500418000e6c73d000059800011a08f0bb81e408d1d986450620003cf800033e00033000000002fe1d60b78a2400040e173415a5671e49cc8c3e0003da18a43b64332ea85a807a6f1000000000004410a8788000000002144c90a33026604b481a6c0341906400029f30692249a855a35500c86085b80389b900141c22ec18e080e0371949e4421e80c0d01e042d861b42a15880005ae0f70600bcc15823315c90066483250e005a87881e40d10fee6d64099d9411c2f93b51fec2e05811838c04a18728000180854273100001ec1a0658000135c7fc0052250d5464e7f81d78000cf460e0030818f7a2b600000acece21c3048
  | 12 => 0x1d044d8000000027000052026986703ac401154800077a11d2ed8a304620574148b2048a4ae1d680004420000001bfceb67ec3210bdc8646c513c80000006c71600000b7a0003650000f725fd00009a80000b42e28000f665f81a68bd046c0491891be48065642f99dd80004132f889b84b24c63028fc49d64fa2c00020e122752aa8dbcca21474030ca06ee1480539f348a28561d489ace900db0001060d586792850ce800051523c00004fc1bf26f06140004802249a180220002c90d849ba2bf1db0158a3a3882d094649ce52522a11908727e80fc845c09e84c4200e78d001773e78e80e020af3ef970c79a6fb18b03fc9044401991cb83640b914f0cd054e6ee34c16f90663b02ba00bc5542fb2508a3ce8453709f8acd05a53828e140cd1454c1069244c5a076337886c8e22a542493243a80121d38f7ca164582e88d1900e54e2058000eee18700011210601192ab96386445c626b00009f80003dd80003964861dd8cec2fa00016f9c744bc46817e814c7da5f205e9290ba87e3246986108c8213d7108016c0880860000d7a2f00001524d761fc3b113342441b83161e8caf217a0e690684e00a00508a4487802514b1aa06160fb0ee91b8d860580e016c86f845d217092cd5e28814c818c25228635a85fc66c0a83f80940b4605b3af812c6d82070000ce096e6a00f2019063a2622799ef8b0e21d41a81289c02281df84000d400727b00009c2000000000012c0000000000ca816e00000000000d937e800096264600015e80000003820000b340001ec8000ce66631f715708b60003130c84f0480d15e9bd000056631380009fc23914e17a06fc6500000d148e439f3109db4f3c42800006f0ffc76f2c49a68a3006637412201d07430cd9bbd0906a221e94bc3e823e195046c65c201341017c3d200015818fc11e55e1669674b4a0003df82545fe20536f8c8c97c1ae000153427a3fb10f0990d2411134a0a6c00049b26012740000000000e402484b008307607a8506000132ccae11c1ad01b00003200868a805c28190620bd800022c2531d4c3082ea0000000e6671b0001aa46282f13ea88e019a00012b1fc81ee14f1ec0000a822e60c081504261f02fc8678f2680f32c9ae504400000005d8cd21f236c1e107f02653238fa0a2250d14392606a26de1b200010024240199afc4100003d39cec3c07ea00006a07ca7c92ff00ec1906c90b785a00420ae37f083c7543951a7881106e6711f096ac1921bd02e05740006140461748e303da0261d642f2000021109c1e001f29204cc9ea3d700000001ec00000016d0cc4059223997832e3103bf09e000070816e00000005d000000009560fe17215140382413da9ac49720bf0000dc486866e3b40000ff209b12680003ca00020e800000022e000000000000006798ac64a0002131670000
  | 13 => 0x47a61dd1be8efe34c13e9aac2d66394050034e4c34219e1424fec47600000003ec06230508a4a3e0003bd99dc25e1cf2270ffc0000002a982286c640606b15587620201540a102243193e5862c8ca18805b80a4eb44310dd9148fd64c50001f801566dc15d04606223f60000f04e060002e104c4e8830d2b008dc73a1e7000019c00000017e0954f3a57d3ac00000004f0000000000000000000000000001d29f488ae63b23a86d8cec21f389064cab02772e518c00000d7113895002067200016ed03a56807a05c89441a22a59c9cd741b900004e8da67c70000c385762e222280007de8382f61db8bd63a80001dc4a887ff3331eb42fc0001481af00007a01fa8cbcb2e1f82fd80009d26c800d0000f2446d05800a83a451b05d20608383d040200003bc1750d8a0fcf806901bc80000006a721b00009320ea09d80005240722350f309fa00012900009aa15a3b30a8859e2a622f187819483c000000050a2183739800fa838b21f1c400006683ae8714fc83993f711100001c92938740f8c2162c80a9013a2b223f8c6ce0c00010a19fc330000000000000000024782f89fe00934400005ea65b0000000a1e01500014f00000002f696909e2000000000000015120f80000000002a31e880000000000000e680003db8000cbe0003a28000d423e62b79d7000071e3f692940007d8157825c81c00000000641086911da905897e1eb2cc021507c3133f0902097a22a2d302083ea35f01a098014c1300df16d8d4600000007fc0003851a49d300004af0000f187344a70131acc53004506a8000c5c3d625d81f4388273000173893443500002a400000000000005027b60001d540003d20000924bca4cf00da024c160003bd1b8000000000000000003eb0fd008800012a19e9d00a2e5782a3806000063d35c066800063e2d699a8d3a18a272919c00030200000000004ed11f9b44e8c0003769e941762c33b5a00000042200017dc4c62d90001cdc72c0001c0a1480007aa00015f04781231bb0a3479c81719617a4dea7fc3660864bc60e633a8134caa0f8295840410070532e0a08b5412e04094148f803e18f91d00003842e08b2c21658c14d0ba04da59432601544400e44081c2836a78500017900007742e9922c0007193f317f06183521d20bbc92a2c90001a346e67871c883848420000f089700006034091e5cf4866c1f805eca462c6000002c2e852e3c61f6903e4dc0a593b8e603a62e41c80342280413084481472c0af0000aa414c3cc8d5070c36839a98586d456136785b4c961ed26c1b400f001d0a48e34e0433e3631914fe67391c19508a1043713400007c600022583050340c50001d5806002e0001e3d05400000008bcb085330000510f8443f2ca849408c535263803cc545dc347030016400000012589080402419894a7c0e3000
  | 14 => 0x1c3824c0863b01ee09d00000438000f2807933f0a3800000325a1b8463c7af14a90a83a610300005083200da1450554afe0001bc1b50a9e2d51018ee40262be2a414084ba00003815b4c4000033c11e88ee3b83200000bac00027d93d10460001ee8000bd42e9000000000077318402c46ca2db386848496c5b11611e2cd0a5a92db8dc81bc75e0dba13c9842893a783f022658f051071903c52607c8fa49f06b4343923835e13e3c72154f940990d682782c64bc3cb080826400e412950d0a01ce3be8f281d60000001f886ce1522cd88d43c66f840a0a0c8587b123811f855a0e02990e485a07892e6183c94606b34e06a80fe12c1ea83741b86f234f9f586907290a098cce286a60c489088202f8255039c6ac65d162967c61e2cc10b9ee80fc5ac12f9984e7e10e2778f9c60c6e90af927cd2c30016089385a64f7157034c0586f01fc994800009204a210d05000031887a80005cb00011ecce05730a180000007a80378dfc280244383909444471c34605cd0962332b1961822c0a40551a7899c0613369170e9a7ef2319af820e0002b7000029a6130001b8c5f414e2e016580007232cf0d803584120000c70a526950120bace7068f0000db8228000366918400049719589e8c021d72f09f70d9c2d70001278f5269900015ec66637a00018d049040536e82f0f305ef0671b6cea078341380fcc9a18c15a01a0e74331375a0548ac74a239a14c2f84c420a87bc7383690ef9874cfa6e533a1f784204ec28a05a43e25ff419038901c63a3ab9f0ca5082c1331ab808265a10011684b6258039869072835d1a81e2858e000028800005a24f07983d4bce7d14058000b0644f1e28f106ae63705980009261344178b8c1a42e03c00f4c5e466400000002123fd3459b2c0005bc0000000a942b80000918b263430ed12b4e2e5403ce1344c0850717698181260001ac96e504012b0f30984be01450901248e9c77203a08f428c22d1c78eb834a6f63b095dce185af19ba0202087240ac84e06d64230ad905018c5c41f108909a01dc3e20fe866a102181832cafc63530d08d0ad61620611de109
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x75484110007755484110025f773841101fdf57384110027e67284110027e57284110025f67084110026f7608411001ff36084110027f24084110007f14084110004ff7559010014fe7559010004fd7559010014fc7559010024ff7459010026bf74590100067f5459010006be5459010006bd5459010004ff735901000cfe7359010004fd735901000cfc7359010006bf4359010006bd4359010004ff7259010044fc725901001cff715901001cfe715901001cfd715901001cfc715901001ebe415901001ebc415901004cff7059010024fe705901004cfd7059010024fc7059010026be4059010026bc405901001ef7105901001efa105901001ef910590100067f76550101de7e76550100067d76550101de7c76550101f57f74550100373f74550101de7f645501004e7e64550101df3e645501004e3e64550100067d64550101df3d64550100063d645501004e7c64550101de7f63550101be7e63550101ee7d63550101de7c63550101de7f62550101e67e62550101de7c62550100077771550101df7471550101de7e61550100667e60550101df7710550101df7a10550101df791055010004ff75588100067f75588100047f7558810014fe7558810004fd7558810014fc75588100067c75588100147c7558810004ff745881004cfc74588100067f54588100067d5458810004ff735881000cfe7358810004fd735881000cfc7358810024ff7258810026ef7258810006ee5258810006ed5258810006ee3258810006ed325881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec2158810044ff7058810024fe7058810044fd7058810024fc7058810026ee2058810026ec205881004cff76d0810024fe76d0810004fd76d0810024fc76d08100357e75d08100057d75d081004ebe64d0810006bd64d081002dde73d0810005dd73d0810044ff7690810024fe7690810004fd7690810024fc7690810046ee6290810006ed6290810004ff7650810024fe7650810004fd7650810024fc765081004ebe6450810006bd6450810046ee6250810006ed6250810005f7715081001df47150810044ff7610810024fe7610810004fd7610810024fc76108100357e75108100057d7510810004fd76d00100357e75d00100057d75d0010004ff76500101d6fa6050010004fd76c8010026ef62c8010026ec62c8010004ff76480100057f75480100357c7548010005df734801002ddc7348010026ef6248010026ec6248010025f77644010006f77644010004f77644010026f76444010006f564440101cf775444010007755444010026f763440101c6f56344010025f7704401001ff37044010026f66044010027f26044010027f250440101cff15044010027f24044010007f140440101c7f33044010027f03044010
  | 1 => 0x910004fd7650910004fc7650910046ee6250910006ed6250910044ff7610910004fe7610910004fd7610910044fc761091005d7e75109100057d7510910006bf641091004ebc641091001df67110910005f57110910005fa7010910005f97010910004fe76d0510024fc76d051005d7e75d05100057d75d0510006bf64d051004ebc64d0510005fa70d0510005f970d0510005f6769051001ef6769051023df5749051004ef6649051004ef4649051025777549051000775549051001df7739051024df5739051001ff37090510025f6709051001ff0709051001ef7609051001ff3609051004cfc7650510006bf645051004ebc6450510005fb7050510005f8705051001ff0105051004ef4765051004cf4765051001df7745051001fb77450510007b7645051004ef6645051004ef46450510007b4645051024777545051000775545051023df7735051023df57350510007f37050510025f47050510007f0705051001ef7605051001ff36050510004fe76c8510024fc76c8510006ef62c8510046ec62c8510005fa70c8510005f970c8510044fc76485100057f754851005d7c7548510006ef6248510046ec6248510005fb7048510005f8704851001cfe76d011001cfc76d011005d7e75d01100057d75d0110006bf64d011004ebc64d011001df671d0110005f571d0110004fe7690110005fa7690110006fa7690110235f9749011004efa649011004ef8649011022f7b5490110007795490110027f3719011001dfa719011001df87190110027f07190110026fb6190110007f24190110007f14190110227f23190110227f1319011004cff7650110004fd765011001cfc7650110006bf645011004ebc6450110005f7715011001df4715011001df8765011004ef8765011001cf87650110007bb7450110007bb645011004efa645011004ef86450110007b8645011021f7b5450110007795450110217bb4350110217b94350110007f3715011001dfa715011001df87150110007f07150110007f24150110007f14150110217f23150110217f13150110004fe761011005d7e75101100057d7510110055de7310110005dd7310110005ee7210110005ed721011001df67110110005f5711011020dfa701011001cfe76c811001cfc76c8110006ef62c8110046ec62c811001df671c8110005f571c8110004fe7688110044ff7648110004fd764811001cfc76481100057f754811005d7c7548110005df7348110055dc7348110006ef6248110046ec6248110005f7714811001df47148110004fe760811005d7e75081100057d750811005d7e75841100057d7584110005ee7284110005ed728411001dfa708411001efb608411001df67684110026f6768411001cf67684110027767584110027757584110025f77484110005f574841102077
  | 2 => 0x1ef576c42100277665c42100277565c4210026f764c4210006f564c42102777754c42100077554c421001fd673c421001fd573c4210026f763c421026ef563c4210027e662c4210027e562c4210027f260c421004cfe76d9110004ff75d9110014fe75d9110004fd75d9110014fc75d91100067f54d9110006be54d9110006bd54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d9110006be43d9110006bc43d9110044fe72d9110004fd72d911001cfe71d911001cfc71d9110024fe70d9110024fc70d911005d7e75991100057d7599110006bf6499110004ff7559110014fe7559110004fd7559110014fc7559110006bf74591100067f5459110004ff735911000cfe7359110004fd735911000cfc7359110004ff7259110044fc7259110004ff7159110006f77159110004ff7059110006fb7059110004fe761911005d7e75191100057d751911004ebe6419110006bd6419110055de7319110005dd7319110005ee7219110005ed72191100067f76551100067e76551100067d76551100067c765511005d7f745511005f3f74551100067f64551100073f64551100063f645511004e7e64551100067d645511004e7c64551100073c645511004e3c64551102667f63551101be7e63551102667d63551101be7c63551101e67e62551101e67c62551102677631551102677531551101df7b1055110044fe76d8910004ff75d8910014fe75d8910004fd75d8910014fc75d891004cfe74d8910004fd74d89100067f54d89100067d54d8910004ff73d891000cfe73d8910004fd73d891000cfc73d8910006ef32d8910006ec32d891001cfe71d891001cfc71d8910006f631d8910006f531d8910024fe70d8910024fc70d8910006ef62989100057f755891005d7c7558910005bf7458910005bc7458910005df7358910055dc7358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891004cfc7458910006bc745891004cbc74589100067f54589100067d5458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc7358910006ef7258910004ff7158910006f77158910006f63158910006f5315891025eee215891025eec2158910004ff7058910006fb7058910004fe7618910046ee6218910006ed621891004cff76d0910004fe76d0910004fd76d091004cfc76d091005d7e75d09100057d75d0910055de73d0910005dd73d091001df671d0910005f571d0910005fa70d0910005f970d0910044ff7690910004fe7690910004fd7690910044fc7690910006bf649091004ebc6490910046ee6290910006ed6290910004ff7650910004fe765
  | 3 => 0xc7358a10006ef5358a10006ee5358a10006ed5358a10006ec5358a10006ef4358a10006ee4358a10006ed4358a10006ec4358a10006ef7158a1025eee7158a10006ed7158a1025eec7158a10006ef5158a1025eee5158a10006ed5158a1025eec5158a1025eee4158a1025eec4158a10006ef3158a1025eee3158a10006ed3158a1025eec3158a10026ee7058a10026ec7058a10006ef5058a10026ee5058a10006ed5058a10026ec5058a10026ee4058a10026ec4058a10006ef3058a10026ee3058a10006ed3058a10026ec3058a1025eef1058a10026ee1058a10026ec1058a1004cff76d0a10024fe76d0a10004fd76d0a10024fc76d0a100657e75d0a100057d75d0a101b67e65d0a100067d65d0a1003dde73d0a10005dd73d0a10046ee62d0a10006ed62d0a10025fa70d0a10005f970d0a10044ff7690a10024fe7690a10004fd7690a10024fc7690a101a67e6590a100067d6590a10046ee6290a10006ed6290a10004ff7650a10024fe7650a10004fd7650a10024fc7650a101967e6550a100067d6550a10046ee6250a10006ed6250a10005f77150a1001df47150a10044ff7610a10024fe7610a10004fd7610a10024fc7610a100657e7510a100057d7510a101867e6510a100067d6510a10046ee6210a10006ed6210a10025fa7010a10005f97010a100657e75d06100057d75d06101767e65d06100067d65d061004ebe64d0610006bd64d0610006ee62d0610006ed62d0610025fa70d0610005f970d061004cff76506101567e65506100067d655061004ebe6450610006bd6450610006ee6250610006ed6250610005fb7050610025f870506101367e65c86100067d65c8610046ee62c8610006ed62c8610025fa70c8610005f970c8610044ff76486100057f75486100657c75486101167e65486100067d6548610046ee6248610006ed6248610005fb7048610025f870486100657e75d02100057d75d02100f67e65d02100067d65d0210006ee62d0210006ed62d0210025f97690210026f9769021001cf976902100277a659021002779659021004efa6490210027ba6490210027b96490210026f864902102877b5490210007795490210027ea6290210027e9629021001dfa7190210027f27190210027f17190210025f871902100de7e65502100067d6550210006ee6250210006ed6250210005fb7650210006fb765021027f7a6550210007796550210027bb745021004efa645021004ef8645021027f7b54502100077954502101d7bb43502101d7b94350210007ea6250210007e9625021001dfa715021001df871502100b67e65c82100067d65c8210046ee62c8210006ed62c82100057f75482100657c754821009e7e65482100067d6548210005df734821003ddc7348210046ee6248210006ed6248210025f576c4210
  | 4 => 0x521000774715521005e7d61552101de7e60552101df7b1055210024ff75d8a10014fe75d8a100267e75d8a100147e75d8a10004fd75d8a100267d75d8a100047d75d8a10024fc75d8a1004cfe74d8a10004fd74d8a100067f54d8a100067d54d8a10024ff73d8a1000cfe73d8a10004fd73d8a10024fc73d8a10026f571d8a10026fa70d8a10004fd7698a100067e6598a100067d6598a10026ef6298a10026ec6298a10004ed7698a10026ef6598a10006ee6598a100276e6598a100066e6598a10006ed6598a100276d6598a100066d6598a10026ec6598a10026ef6498a10006ee6498a10006ed6498a10026ec6498a100076f5498a100076d5498a10026ef6398a10006ee6398a10006ed6398a10026ec6398a1028feb1098a10027e81098a10046ef7598a10046ee7598a10046ed7598a10046ec7598a10046ef7498a10046ee7498a10046ed7498a10046ec7498a10006ef5498a100066f5498a10006ee5498a10006ed5498a100066d5498a10006ec5498a10046ef7398a10046ee7398a10046ed7398a10046ec7398a10006ef5398a10006ee5398a10006ed5398a10006ec5398a10006ef4398a10006ee4398a10006ed4398a10006ec4398a10046ef7198a10046ee7198a10046ed7198a10046ec7198a10006ef5198a1028eee5198a10006ed5198a1028eec5198a1028eee4198a1028eec4198a10006ef3198a1028eee3198a10006ed3198a1028eec3198a10026ee7098a10026ec7098a10006ef5098a10026ee5098a10006ed5098a10026ec5098a10026ee4098a10026ec4098a10006ef3098a10026ee3098a10006ed3098a10026ec3098a1028eef1098a10026ec1098a10044ff7658a100067e6558a100067d6558a10026ec6258a10004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7458a1004cfc7458a100067f5458a100067d5458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a10026ef7258a10006ef5258a10006ee5258a10006ed5258a10006ec5258a10006ef3258a10006ee3258a10006ed3258a10006ec3258a10024fc7058a10026ee2058a10026ec2058a10025ef7658a10006ef7658a10044ef7658a10026ef6558a10006ee6558a100276e6558a100066e6558a10006ed6558a100276d6558a100066d6558a10026ec6558a10026ef6458a10006ee6458a10006ed6458a10026ec6458a100076f5458a100076d5458a10026ef6358a10006ee6358a10006ed6358a10026ec6358a1025feb1058a10027e81058a10006ef7558a10006ee7558a10006ed7558a10006ec7558a10006ef7458a10006ee7458a10006ed7458a10006ec7458a10006ef5458a100066f5458a10006ee5458a10006ed5458a100066d5458a10006ec5458a10006ef7358a10006ee7358a10006ed7358a10006e
  | 5 => 0x5f7715031001df471503100757e75103100057d751031006dde7310310005dd73103100bede6310310006dd6310310005ee7210310005ed721031001df67110310005f571103100aede63c8310006dd63c8310046ee62c8310006ed62c831001df671c8310005f571c831008ede6388310006dd6388310044ff76483100057f75483100757c7548310005df734831006ddc7348310096de6348310006dd6348310046ee6248310006ed6248310005f7714831001df471483100757e75083100057d750831007ede6308310006dd63083100257f76596100667f76596100147f76596100057f74596100267f64596100267c64596100267f63596100067e63596100067d63596100267c63596100267f62596100267c625961029f7b10596100277810596100067f74596100047f74596100067e74596100067d74596100067c74596100067f73596100067e73596100067d73596100067c73596100067f43596100067e43596100067d43596100067c43596100067f72596100067e72596100067d72596100067c72596100067f32596100067e32596100067d32596100067c32596100667f715961029e7e71596100067d715961029e7c715961029e7e415961029e7c41596100067f315961029e7e31596100067d315961029e7c315961029e7e215961029e7c21596100667f70596100267e70596100667d70596100267c70596100267e40596100267c40596100067f30596100267e30596100067d30596100267c30596100267e20596100267c205961029e7f10596100267e10596100267c1059610024ff75d9210014fe75d92100267e75d92100147e75d9210004fd75d92100267d75d92100047d75d9210024fc75d92100067f54d9210024ff73d921000cfe73d9210004fd73d9210024fc73d9210044fe72d9210026ee72d9210044ee72d9210004fd72d9210026ed72d9210004ed72d9210026f571d9210026fa70d9210004fd76992100657e75992100057d75992100067e65992100067d6599210026bf6499210026bc649921004cff76592100657e75592100067e65592100067d6559210026bc6459210004ff7559210014fe75592100067e75592100147e7559210004fd75592100067d7559210014fc7559210026bf74592100067f5459210004ff735921000cfe7359210004fd735921000cfc7359210006bf4359210006bd4359210004ff7259210044fc7259210024fc7059210026be4059210026bc40592100057f76552100067f76552100047f76552100067e76552100057d76552100067d76552100047d76552100067c76552100657f74552100673f74552100067f645521004e7e64552100067d645521004e7c64552102967f63552101be7e63552102967d63552101be7c63552101e67e62552101e67c625521000777715
  | 6 => 0xf5459310004ff735931000cfe7359310004fd735931000cfc7359310004ff7259310044fc725931001cfc715931001ebe415931001ebc415931001efa105931001ef910593100067f76553101de7e76553100067d76553101de7c76553101f57f74553100773f74553101de7f645531004e7e64553100067d645531004e7c64553101de7f63553101be7e63553101df5e63553101be5e63553102b67d63553101df5d63553101de7c63553101de7f62553101e67e62553101de7c62553101df7641553101df7631553102b7753155310006df7558f10006de7558f10006dd7558f10006dc7558f10006df7458f10006de7458f10006dd7458f10006dc7458f10006df5458f100065f5458f10006de5458f10006dd5458f100065d5458f10006dc5458f10006df7258f10006de7258f10006dd7258f10006dc7258f10006df5258f10006de5258f10006dd5258f10006dc5258f1001edf7158f1001ede7158f1001edd7158f1001edc7158f1001edf5158f1001ede5158f1001edd5158f1001edc5158f1001edf4158f1001ede4158f1001edd4158f1001edc4158f1001edf2158f1001ede2158f1001edd2158f1001edc2158f1006edf7058f1006ede7058f10006dd7058f1006edc7058f10006df5058f10006de5058f10006dd5058f10006dc5058f1001edf1058f1001ede1058f1001edd1058f1001edc1058f10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b1004cfc7458b100067f5458b100067d5458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b1001eef7258b10006ef5258b10006ec5258b1001cfc7158b1001ef63158b10006f53158b1001eee2158b1001eec2158b1004cff76d0b1001cfe76d0b10004fd76d0b1001cfc76d0b100757e75d0b100057d75d0b1006dde73d0b10005dd73d0b101aede63d0b10006dd63d0b1001df671d0b10005f571d0b10044ff7690b1001cfe7690b10004fd7690b1001cfc7690b1019ede6390b10006dd6390b10046ee6290b10006ed6290b10004ff7650b1001cfe7650b10004fd7650b1001cfc7650b1018ede6350b10006dd6350b10046ee6250b10006ed6250b10044ff7610b1001cfe7610b10004fd7610b1001cfc7610b100757e7510b100057d7510b1017ede6310b10006dd6310b1001df67110b10005f57110b1001df77650710006f7765071001fb7745071004ef6645071001ef464507102af7754507100077554507102a5f773507102a5f5735071001fd6635071001fd56350710025f470507100757e75d03100057d75d031004ebe64d0310006bd64d03100eede63d0310006dd63d031001df671d0310005f571d03100cede6390310006dd6390310025f4719031004cff765031004ebe6450310006bd64503100d6de6350310006dd6350310
  | 7 => 0x94200467d21594200467c21594200867f70594200267e70594200867d70594200267c70594200267e40594200267c40594200067f30594200267e30594200067d30594200267c30594200467f20594200466f20594200267e20594200467d20594200267c20594200267e10594200267c1059420004ff7559020014fe75590200067e75590200147e7559020004fd75590200067d7559020014fc7559020024ff7459020026bf74590200067f5459020004ff735902000cfe7359020004fd735902000cfc7359020006bf4359020006bd4359020044ff7259020044fe7259020044fd7259020044fc7259020046be4259020046bc4259020004ff715902001cfc7159020024fe7059020024fc7059020026be4059020026bc4059020046ef20590201e57f76550200067f76550200047f76550201e67e76550201e57d76550200067d76550200047d76550201e67c76550202d57f74550200873f74550201e67f645502004e7e64550200067d645502004e7c64550201e67f63550201be7e63550202ce7d63550201e67c63550200076f72550201e76c72550201e67e62550201de7e61550200a67e60550201e76f20550201e77a20550201e7792055020004ff7558420014fe7558420004fd7558420014fc7558420004ff745842004cfc74584200067f54584200067d5458420004ff735842000cfe7358420004fd735842000cfc7358420026f77158420006f63158420006f53158420046f72158420046f4215842001cff7058420026f61058420026f4105842004cff76d0420024fe76d0420004fd76d04200857e75d04200057d75d04201767e65d04200067d65d042004ebe64d0420006bd64d042001cff7690420024fe7690420004fd76904201667e65904200067d659042001ef66190420006f56190420004ff7650420004fd7650420024fc76504201567e65504200067d655042004ebe6450420006bd645042001ef66150420006f5615042001cff7610420024fe7610420004fd76104200857e75104200057d75104201467e65104200067d651042007dde7310420005dd7310420045ee7210420005ed7210420025fa7010420005f97010420004fd76d00200857e75d00200057d75d00200f67e65d00200067d65d0020004ff76500200de7e65500200067d6550020025ef7648020006ef7648020004ef76480200076f75480202bf6c7548020026ef65480200276e65480202beed65480200276d65480200066d6548020026ef6448020006ed64480202bf6f54480200076d5448020007cf73480202c7cc7348020026ef63480202c6ed634802025eee6148020025ef7048020047eb7048020026ee6048020027ea6048020027ea50480202bfe95048020004ff7559310014fe7559310004fd7559310014fc755931001ebf74593100067
  | 8 => 0x5f970105200067f65885201267c6588520006df638852011edc6388520006f7618852001ef46188520005fa7088520005f9708852025def7588520335ed75885200076f658852032f6c658852025def7488520005ed748852032f6f54885200076d548852025def7388520325ed7388520007cf638852011eee638852011eec638852031fcc638852011ecc6388520045ee718852025eef6188520007e7618852025fe4618852025fe6318852031fe53188520025ee708852025fea708852025fe97088520046ef6088520047eb608852001cfc76485200057f754852009d7c75485200067f65485201167c6548520006df634852010edc6348520006f7614852001ef46148520005fb7048520005f87048520005ee7608520046ee7608520045ef7508520315ed75085200076f650852030f6c6508520045ef7408520005ed740852030f6f54085200076d5408520045ef7308520047ce7308520305ed7308520047cd7308520005cd7308520007cf63085200feee63085200feec63085202ffcc63085200fecc630852025dee7108520047e6710852025eef6108520025ee7008520046ef6008520047eb6008520044fe76d0120044fc76d012009d7e75d01200057d75d01200067f65d01200f67c65d0120006bf64d012004ebc64d0120006df63d01200eedc63d0120045ee72d0120005ed72d0120004fe76901200067f65901200e67c6590120006df63901200cedc639012004cff7650120004fd7650120044fc76501200067f65501200de7c6550120006bf645012004ebc6450120006df63501200d6dc6350120005ef7250120045ec7250120004fe761012009d7e75101200057d75101200067f65101200c67c6510120095de7310120005dd7310120006df63101200bedc6310120045ee7210120005ed7210120005f67110120005f57110120007b940101200067f65881200a67c6588120006df638812008edc6388120045fa7088120046fb6088120025ef75881202f5ed75881200076f65881202ef6c6588120025ef7488120005ed74881202ef6f54881200076d5488120025ef73881202e5ed7388120007cf63881202dfcc638812025dee7188120025ee7088120026ef6088120047eb60881200067f74594200047f74594200067e74594200067d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067d43594200067c43594200467f72594200467e72594200467d72594200467c72594200467f42594200467e42594200467d42594200467c42594200467f32594200467e32594200467d32594200467c32594200067f71594200067e71594200067d71594200067c71594200067f31594200067e31594200067d31594200067c31594200467f21594200467e215
  | 9 => 0xe50d8d20006dd50d8d20006dc50d8d2037edf20d8d20096dd20d8d2037edc20d8d20004fe76d0920024fc76d092009d7e75d09200057d75d09200067f65d09201b67c65d0920006bf64d092004ebc64d0920095de73d0920005dd73d0920006df63d09201aedc63d0920005fa70d0920005f970d0920005ee7690920046ee7690920045ef7590920375ed75909200076f659092036f6c6590920345ed749092004eee649092004eec649092036f6f54909200076d5490920045ef7390920365ed7390920007cf639092019eee639092019eec639092035fcc639092019ecc639092025dee7190920025ee7090920046ef6090920047eb609092004cfc76509200067f65509201967c6550920006bf645092004ebc6450920006df635092018edc6350920005fb7050920005f8705092004eec765092004cec7650920355ef7550920355ed75509200076f655092034f6c6550920045ef7450920047af7450920007af645092004eee645092004eec6450920007ac645092034f6f54509200076d5450920345ef7350920345ed7350920007cf635092018eee635092018eec635092033fcc635092018ecc635092025dec7150920007eb7050920025ec7050920007e87050920046ef6050920047eb60509200067f65d85200067c65d8520006df63d8520006dc63d8520004ff75d8520014fe75d8520004fd75d8520014fc75d852004cfe74d8520004fd74d85200067f54d85200067d54d8520004ff73d852000cfe73d8520004fd73d852000cfc73d8520006ee42d8520006ed42d8520024fe70d852009d7e75985200057d75985200067f65985200067c6598520095de7398520005dd7398520006df6398520006dc6398520006f761985200057f755852009d7c75585200067f65585200067c6558520005bf7458520005bc7458520005df7358520095dc7358520006df6358520006dc63585200067f65185200067c6518520006df6318520006dc631852001ef66118520006f56118520004fe76d0520004fd76d052004cfc76d052009d7e75d05200057d75d05200067f65d05201767c65d0520006df63d052016edc63d0520045ee72d0520005ed72d0520006f761d052001ef461d0520004fe7690520004fd769052001cfc76905200067f65905201667c6590520006bf649052004ebc6490520006df639052015edc6390520004ff7650520004fe7650520004fc76505200067f65505201567c6550520006df635052014edc6350520005ef7250520045ec7250520004fe7610520004fd761052001cfc761052009d7e75105200057d75105200067f65105201467c6510520006bf641052004ebc6410520095de7310520005dd7310520006df631052013edc6310520045ee7210520005ed7210520006f7611052001ef46110520005fa7010520
  | 10 => 0x952009e7c70d95200067f30d95200067e30d95200067d30d95200067c30d952038e7f20d952009e7d20d952038e7c20d952004cfe76d912009d7c75d91200067f65d91200067c65d9120006dc63d9120004ff75d91200067f75d9120014fe75d9120004fd75d9120014fc75d91200067c75d91200147c75d91200067f54d9120004ff73d912000cfe73d9120004fd73d912000cfc73d9120044fe72d9120044fc72d912001cfe71d9120004fd71d912009d7e75991200057d75991200067f65991200067c6599120006bf6499120095de7399120005dd7399120006dc63991200057f755912009d7c75591200067f65591200067c6559120005df7359120095dc7359120006dc6359120005f77159120005f47159120004ff75591200067f75591200047f7559120014fe7559120004fd7559120014fc75591200067c75591200147c7559120006bf74591200067f5459120004ff7359120006df7359120004df735912000cfe7359120004fd735912000cfc7359120006dc735912000cdc7359120004ff7259120006ef7259120004ff7159120006f77159120004f7715912001cfc7159120006f4715912001cf47159120004ff7059120006fb7059120004fe761912009d7e75191200057d75191200067f65191200067c651912004ebe6419120006bd6419120006dc63191200067f76551200057e76551200067e76551200047e76551200067d76551200057c76551200067c76551200047c765512009d7f745512009f3f74551200067f645512004e7e64551200067d645512004e7c64551203867f63551201be7e63551203867d63551201be7c63551203875c63551201be5c63551200076e72551200076d72551203876e32551203876d32551201de7c61551201e77b2055120095de76d8d20096de76d8d2000cde76d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d20006de64d8d20006dd64d8d20006dc64d8d200075f54d8d200075d54d8d20007cf72d8d20097cc72d8d20007ce52d8d20007cd52d8d2037fdb20d8d2037fd820d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d200065f54d8d20006de54d8d20006dd54d8d200065d54d8d20006dc54d8d20006df72d8d2037ede72d8d20096dd72d8d2037edc72d8d20006df52d8d2037ede52d8d20006dd52d8d2037edc52d8d2037ede42d8d2037edc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d20006de51d8d20006dd51d8d20006dc51d8d2037edf21d8d2037edc21d8d2037edf70d8d20096de70d8d20096dd70d8d20096dc70d8d20006df50d8d20006d
  | 11 => 0xcfc7359220006bf4359220006bd4359220004ff715922001cfc7159220024fc7059220026be4059220026bc40592200067f76552200067e76552200067d76552200067c76552200a57f74552200a73f74552200067f645522004e7e64552200067d645522004e7c64552203a67f63552201be7e63552203a67d63552201be7c63552200076f72552200076c725522009e7d62552201de7e61552201e67e60552201e77b20552200a57e75d0a200057d75d0a2004ebe64d0a20006bd64d0a2008dde73d0a20005dd73d0a20025fa70d0a20005f970d0a2004cff7650a2004ebe6450a20006bd6450a20005fb7050a20025f87050a2008dde7398620005dd7398620026f76198620026f46198620026f46158620004ff7558620014fe7558620004fd7558620014fc7558620004ff745862004cfc74586200067f54586200067d5458620004ff735862000cfe7358620004fd735862000cfc7358620006f75158620006f45158620006f63158620006f53158620024fc7058620026f61058620026f4105862004cff76d0620024fe76d0620004fd76d06200a57e75d06200057d75d062001cff7690620024fe7690620004fd769062001ef66190620006f56190620004ff7650620004fd7650620024fc765062001ef66150620006f5615062001cff7610620024fe7610620004fd76106200a57e75106200057d751062008dde7310620005dd7310620045ee7210620005ed7210620025fa7010620005f9701062001ef66188620006f56188620025fa7088620005f9708862001cff76486200057f75486200a57c754862001ef66148620006f56148620005fb7048620025f870486200a57e75d02200057d75d0220027b84050220025ed76c8220046ed76c8220026ef65c8220396ed65c8220026ef64c8220006ed64c82203976f54c82200076d54c8220026ef63c822039eed63c822028eee61c8220027ea60c8220027ea50c8220397e950c822009d7e76d952009e7e76d95200147e76d95200057d74d95200067f63d95200067e63d95200067d63d95200067c63d95200075c63d95200065c63d95200076f72d952009f6c72d95200076e32d95200076d32d952038f7b20d952038f7820d95200067f74d95200067e74d95200067d74d95200047d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d952038e7e72d952009e7d72d952038e7c72d952038e7e42d952038e7c42d95200067f32d952038e7e32d95200067d32d952038e7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067e31d95200067d31d95200067c31d952038e7f21d952038e7c21d952038e7f70d952009e7e70d952009e7d70d
  | 12 => 0xf74593200067f5459320006be5459320006bd5459320004ff735932000cfe7359320004fd735932000cfc7359320044fc7259320046be4259320046bc4259320004ff715932001cfc71593200067f76553201e67e76553200067d76553201e67c76553202d57f74553200b73f74553201e67f645532004e7e64553201e73e645532004e3e64553200067d64553201e73d64553200063d645532004e7c64553201e67f63553201be7e63553203e67d63553201e67c63553201e76e72553200076d72553201e76e42553201e76e32553203e76d32553201de7e61553201e76c2155320045ef7650b20006ef7650b203ddef7550b203dded7550b20047af7450b2004eee6450b20046ec6450b203d76f5450b200076d5450b203cdef7350b203cded7350b2018eee6350b20046ec6350b2028dec7150b20025ec7050b20004ff75587200067f75587200047f7558720014fe7558720004fd7558720014fc75587200067c75587200147c7558720004ff745872004cfc74587200067f54587200067d5458720004ff735872000cfe7358720004fd735872000cfc7358720046ee4258720006ed4258720046f77158720006f63158720006f53158720046f72158720046ec2158720046f4215872004cff76d0720044fe76d0720004fd76d07200b57e75d07200057d75d0720045ee72d0720005ed72d072001cff7690720044fe7690720004fd7690720045ec7290720004ff7650720004fd7650720044fc7650720005ef7250720045ec725072001cff7610720044fe7610720004fd76107200b57e75107200057d75107200adde7310720005dd7310720045ee7210720005ed7210720005fa7010720005f97010720045ed768872028eed768872028def75887203c5ed758872028def7488720005ed74887203bf6f54887200076d548872028def73887203b5ed738872011eee6388720046ec6388720047e67188720046ef618872028eed618872028fe631887203afe53188720025ee70887200b57e75d03200057d75d032004ebe64d0320006bd64d0320045ee72d0320005ed72d0320025ec729032004cff765032004ebe6450320006bd6450320005ef7250320045ec72503200b57e75103200057d75103200adde7310320005dd7310320045ee7210320005ed7210320005f67110320005f57110320024ff75d9220014fe75d9220004fd75d9220024fc75d92200067f54d9220024ff73d922000cfe73d9220004fd73d9220024fc73d9220026ed72d922001cfe71d9220004fd71d9220026fa70d9220004fd76992200a57e75992200057d7599220026bf6499220026bc649922004cff7659220026bc6459220004ff7559220014fe7559220004fd7559220014fc7559220026bf74592200067f5459220004ff735922000cfe7359220004fd7359220
  | 13 => 0x844004ef74098440026f6409844004ef54098440026f44098440006f73098440026f63098440006f53098440026f43098440026f62098440026f42098440004ff7558440014fe7558440004fd7558440014fc755844004e7f545844004e7d5458440004ff735844000cfe7358440004fd735844000cfc7358440004ff7258440044fc7258440026f77158440006f75158440006f65158440006f55158440006f4515844004ef7415844004ef44158440006f73158440006f63158440006f53158440006f4315844004efa405844004ef94058440026f61058440026f41058440006f77558440006f67558440006f57558440006f4755844004ef7745844004ef6745844004ef4745844004ef7545844004e77545844004ef6545844004ef5545844004e75545844004ef45458440006f77358440006f67358440006f57358440006f47358440006f75358440006f65358440006f55358440006f4535844004ef7435844004ef6435844004ef5435844004ef44358440006f77258440006f67258440006f57258440006f47258440006f75258440006f65258440006f55258440006f4525844004ef7425844004ef6425844004ef5425844004ef44258440006f73258440006f63258440006f53258440006f43258440026f67058440026f47058440006f75058440026f65058440006f55058440026f4505844004ef74058440026f6405844004ef2405844004ef5405844004ef14058440026f44058440006f73058440026f63058440006f53058440026f43058440026f62058440026f42058440044ff76c8440024fe76c8440004fd76c84401367e65c84400067d65c844012ede63c8440006dd63c8440046ee62c8440006ed62c844001ef661c8440006f561c844001cff7688440024fe7688440004fd76884401267e65884400067d658844011ede6388440006dd6388440046ee6288440006ed628844001ef66188440006f56188440004ff7648440004fd7648440024fc76484400057f75484400c57c75484401167e65484400067d6548440005bf744844004dbc744844010ede6348440006dd6348440046ee6248440006ed624844001ef66148440006f5614844001cff7608440024fe7608440004fd76084401067e65084400067d65084400bdde7308440005dd73084400fede6308440006dd6308440046ee6208440006ed620844001ef66108440006f56108440025bf7650040006bf7650040004bf76500400273e65500400273d6550040026bf63500400279e63500403f6bd63500400279d63500400069d6350040027ae6250040027ad6250040027b66150040027b56150040025bf705004004fbb7050040026be6050040027ba6050040027ba50500403efb95050040004ff7559320014fe7559320004fd7559320014fc7559320046b
  | 14 => 0x46ec7398840006ef5398840006ee5398840006ed5398840006ec539884004eef439884004eee439884004eed439884004eec4398840046ef7198840046ee7198840046ed7198840046ec7198840006ef5198840006ee5198840006ed5198840006ec519884004eef419884004eee419884004eed419884004eec4198840006ef3198840006ee3198840006ed3198840006ec3198840026ee7098840026ec7098840006ef5098840026ee5098840006ed5098840026ec509884004eef4098840026ee409884004eed4098840026ec4098840006ef3098840026ee3098840006ed3098840026ec3098840026ee1098840026ec1098840004ff7558840014fe7558840004fd7558840014fc755884004e7f545884004e7d5458840004ff735884000cfe7358840004fd735884000cfc7358840026ef7258840006ef5258840006ee5258840006ed5258840006ec525884004eef425884004eec4258840006ef3258840006ee3258840006ed3258840006ec3258840004ff715884001cfc7158840026ee2058840026ec2058840006ef7558840006ee7558840006ed7558840006ec755884004eef745884004eee745884004eec745884004eef545884004e6f545884004eee545884004eed545884004e6d545884004eec5458840006ef7358840006ee7358840006ed7358840006ec7358840006ef5358840006ee5358840006ed5358840006ec535884004eef435884004eee435884004eed435884004eec4358840006ef7158840006ee7158840006ed7158840006ec7158840006ef5158840006ee5158840006ed5158840006ec515884004eef415884004eee415884004eed415884004eec4158840006ef3158840006ee3158840006ed3158840006ec3158840026ee7058840026ec7058840006ef5058840026ee5058840006ed5058840026ec505884004eef4058840026ee405884004eed4058840026ec4058840006ef3058840026ee3058840006ed3058840026ec3058840026ee1058840026ec105884001ef7759844001ef6759844001ef5759844001ef4759844001ef7749844001ef6749844001ef5749844001ef4749844004ef7549844004e77549844004ef6549844004ef5549844004e75549844004ef4549844001ef7739844001ef6739844001ef5739844001ef47398440006f75398440006f65398440006f55398440006f4539844004ef7439844004ef6439844004ef5439844004ef4439844001ef7729844001ef6729844001ef5729844001ef47298440006f75298440006f65298440006f55298440006f4529844004ef7429844004ef6429844004ef5429844004ef44298440006f73298440006f63298440006f53298440006f43298440026f67098440026f47098440006f75098440026f65098440006f55098440026f4509
  | 15 => 0x7619054001ef46190540005fa7090540005f9709054001cfc76505400073d5450540006f7615054001ef46150540005fb7050540005f87050540004fe76c8540004fd76c8540044fc76c8540006f761c854001ef461c8540004fe7688540004fd768854001cfc7688540005fa7088540005f97088540004ff7648540004fe7648540004fc76485400057f75485400dd7c7548540004fe7608540004fd760854001cfc760854004dbe7408540005bd74085400d5de7308540005dd7308540006f7610854001ef46108540005fa7008540005f970085404073f54901400073d549014004dfa709014004efb6090140025bf73901403fdbd7390140025be7090140026bf609014004fbb609014004e7f745944004c7f745944004e7e745944004e7d745944004c7d745944004e7c74594400067f73594400067e73594400067d73594400067c735944004e7f435944004e7e435944004e7d435944004e7c43594400067f72594400067e72594400067d72594400067c725944004e7f425944004e7e425944004e7d425944004e7c42594400067f32594400067e32594400067d32594400067c32594400067f71594400067e71594400067d71594400067c715944004e7f415944004e7e415944004e7d415944004e7c41594400067f31594400067e31594400067d31594400067c31594400c67f70594400267e70594400c67d70594400267c705944004e7f40594400267e405944004e7d40594400267c40594400067f30594400267e30594400067d30594400267c30594400267e20594400267c20594400267e10594400267c1059440006df7558c40006de7558c40006dd7558c40006dc7558c4004edf7458c4004ede7458c4004edd7458c4004edc7458c4004edf5458c4004e5f5458c4004ede5458c4004edd5458c4004e5d5458c4004edc5458c40006df7258c40006de7258c40006dd7258c40006dc7258c40006df5258c40006de5258c40006dd5258c40006dc5258c4004edf4258c4004ede4258c4004edd4258c4004edc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c40006de5158c40006dd5158c40006dc5158c4004edf4158c4004ede4158c4004edd4158c4004edc4158c400bedf7058c40026de7058c400bedd7058c40026dc7058c40006df5058c40026de5058c40006dd5058c40026dc5058c4004edf4058c4004e9f4058c40026de4058c4004edd4058c40026dc4058c40026de2058c40026dc2058c40026de1058c40026dc1058c40046ef7598840046ee7598840046ed7598840046ec7598840046ef7498840046ee7498840046ed7498840046ec749884004eef549884004e6f549884004eee549884004eed549884004e6d549884004eec5498840046ef7398840046ee7398840046ed7398840
  | 16 => 0x8a40006ed5258a40006ee3258a40006ed3258a40004ff7158a4001cfc7158a40024fc7058a40026ee2058a40026ec2058a40046ee6290a40006ed6290a40025fa7090a40005f97090a40044ff7650a400073d5450a40046ee6250a40006ed6250a40005fb7050a40025f87050a400cdde7398640005dd7398640026f76198640026f46198640026f46158640004ff7558640014fe7558640004fd7558640014fc75586400067f54586400067d5458640004ff735864000cfe7358640004fd735864000cfc7358640004ff7258640044fc7258640006f63158640006f53158640024fc7058640026f61058640026f410586400073d549064001ef66190640006f56190640025fa7090640005f9709064001cff765064001ef66150640006f56150640005fb7050640025f87050640044ff76c8640024fe76c8640004fd76c864001cff7688640024fe7688640004fd7688640046ee6288640006ed6288640025fa7088640005f97088640004ff7648640004fd7648640024fc76486400057f75486400e57c7548640005bf744864004dbc744864001cff7608640024fe7608640004fd76086400cdde7308640005dd7308640046ee6208640006ed6208640025fa7008640005f97008640025bd76d024004ebd76d024004f3e75d024004f3d75d0240026bf63d024041ebd63d0240027ba60d0240027ba50d0240417b950d02400167f76551400e67e76551400de7d76551400167c765514004d7f74551400df3f745514004e7f645514040e7f63551401be7e635514040e7d63551401be7c635514004f3f435514040f3d43551401e67c62551401de7c615514004f3f41551400077b705514000778705514004e7f605514004f7b405514004f3c405514004f78405514004f384055140004ff75d8940014fe75d8940004fd75d8940014fc75d89400067f54d89400067d54d8940004ff73d894000cfe73d8940004fd73d894000cfc73d8940006ef52d8940006ec52d894001cfe71d8940004fd71d8940006ef62989400057f75589400dd7c7558940005df73589400d5dc7358940005f77158940005f471589400dd7e75189400057d7518940046ee6218940006ed6218940006ef6290940046ec6290940005fa7090940005f97090940044fc7650940006ef6250940046ec6250940005fb7050940005f8705094004fb840509400dd7e75d85400057d75d8540004ff75d8540014fe75d85400067e75d85400147e75d8540004fd75d85400067d75d85400047d75d8540014fc75d85400067f54d85400067d54d8540004ff73d854000cfe73d8540004fd73d854000cfc73d8540044fe72d8540004fd72d8540006f751d8540006f451d8540006f631d8540006f531d85400d5de7398540005dd7398540006f7619854001ef66118540006f56118540006f
  | 17 => 0x67f54580210067d5458021004ff735802100cfe7358021004fd735802100cfc735802101efb7058021006fa5058021006f95058021046fb2058021046f8205802101efb105802101ef8105802104e7f745974004e7e745974004e7d745974004e7c74597400067f73597400067e73597400067d73597400067c735974004e7f435974004e7e435974004e7d435974004e7c43597400067f72597400067e72597400067d72597400067c725974004e7f425974004e7e425974004e7d425974004e7c42597400067f32597400067e32597400067d32597400067c32597400067f71597400067e71597400067d71597400067c715974004e7f415974004e7e415974004e7d415974004e7c41597400067f31597400067e31597400067d31597400067c31597400f67f70597400f67e70597400067d70597400f67c705974004e7f405974004e7e405974004e7d405974004e7c40597400067f30597400067e30597400067d30597400067c3059740004ff7558b40014fe7558b40004fd7558b40014fc7558b4004e7f5458b4004e7d5458b40004ff7358b4000cfe7358b40004fd7358b4000cfc7358b4004eef7258b4004eef4258b4004eec4258b40006ef3258b40006ec3258b40004ff7158b4001cfc7158b40004ff7558740014fe7558740004fd7558740014fc755874004e7f545874004e7d5458740004ff735874000cfe7358740004fd735874000cfc7358740004ff7258740044fc725874004ef7715874004ef7415874004ef4415874004efa405874004ef94058740044ff76c874004cfe76c8740004fd76c87401367e65c87400067d65c8740046ee62c8740006ed62c874001cff768874004cfe7688740004fd76887401267e65887400067d6588740004ff7648740004fd764874004cfc76487400057f75487400f57c75487401167e65487400067d6548740046ee6248740006ed624874001cff760874004cfe7608740004fd76087401067e65087400067d650874004dbe7408740005bd74087400edde7308740005dd73087400167f76552400167c765524004d7f74552400e73f745524004e7d64552404267f63552401be7e63552404267d63552401be7c63552401e67e625524004f3f42552401de7e615524004f3c41552400077b705524000778705524004e7e605524004f3f405524004f7b405524004f3b405524004f784055240026ef6298a40026ec6298a400057f7558a400e57c7558a40005df7358a400cddc7358a40026ec6258a40004ff7558a400067f7558a400047f7558a40014fe7558a40004fd7558a40014fc7558a400067c7558a400147c7558a400067f5458a400067d5458a40004ff7358a40006df7358a40004df7358a4000cfe7358a40004fd7358a4000cfc7358a40006dc7358a4000cdc7358a40006ee525
  | 18 => 0xc6558121005bf7458121005bc7458121005df735812110ddc73581210067f65181210067c6518121006f96018121024ff7518121014fe7518121004fd7518121024fc751812104cfe7418121004fd74181210067f54181210067d5418121024ff731812100cfe7318121004fd7318121024fc7318121004ff7559021014fe7559021004fd7559021014fc755902101cff745902101ebf74590210067f5459021006be5459021006bd5459021004ff735902100cfe7359021004fd735902100cfc7359021044fe7259021044fc7259021046be4259021046bc4259021006ef3259021046ec325902101cfe715902101cfc715902101ebe415902101ebc415902101eef215902101eed2159021004ff7059021024fc7059021046ef20590210067f76550211de7e76550210067d76550211de7c76550211f57f74550211073f74550211de7f645502104e7e64550211df3e645502104e3e64550210067d64550211df3d64550210063d645502104e7c64550211de7f63550211be7e63550211df5e63550211be5e635502142e7d63550211df5d63550211de7c63550210076f72550211e76c72550211e67e625502142f6f32550211e76c32550210077771550211df7471550211de7e61550211df6f21550211df7621550211df6d21550211e7752155021006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c210065f5458c21006de5458c21006dd5458c210065d5458c21006dc5458c21046df7258c210fecf7258c21046de7258c21046dd7258c21046dc7258c21046cc7258c21046df5258c21046de5258c21046dd5258c21046dc5258c21046df4258c21046de4258c21046dd4258c21046dc4258c2101edf7158c2101ede7158c2101edd7158c2101edc7158c2101edf5158c2101ede5158c2101edd5158c2101edc5158c2101edf4158c2101ede4158c2101edd4158c2101edc4158c2101edf2158c2101ede2158c2101ed62158c2101edd2158c21046d52158c2101edc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21046df2058c21046cf2058c21046de2058c21046dd2058c21046dc2058c2101edf1058c2101ede1058c2101edd1058c2101edc1058c21024ff7598021014fe7598021004fd7598021024fc759802104cfe7498021004fd74980210067f54980210067d5498021024ff739802100cfe7398021004fd7398021024fc7398021024fe7098021026fa7098021026fa5098021006f95098021026ef2098021046fb2098021026f8209802101efb1098021026f81098021004ff7558021014fe7558021004fd7558021014fc7558021004ff745802104cfc7458021
  | 19 => 0x9121006bf43d9121006bd43d9121024fe70d9121004fd70d91211157e75991210057d75991210067f65991210067c6599121006bf649912110dde7399121005dd73991210057f75591211157c75591210067f65591210067c6559121004ff75591210067f75591210047f7559121014fe7559121004fd7559121014fc75591210067c75591210147c7559121006bf74591210067f5459121004ff735912100cfe7359121004fd735912100cfc7359121004ff7259121006ef7259121004ff7159121006f77159121004ff7059121024fc7059121004fe76191211157e75191210057d75191210067f65191210067c651912104ebe6419121006bd64191210067f76551210057e76551210067e76551210047e76551210067d76551210057c76551210067c76551210047c76551211157f74551211173f74551210067f645512104e7e64551210067d645512104e7c645512145e7f63551211be7e635512145e7d63551211be7c635512145f76315512145f7531551211e77721551211df6e215512101cfe76d092101cfc76d09211157e75d09210057d75d09210067f65d09211b67c65d0921006bf64d092104ebc64d092110dde73d0921005dd73d092101df671d0921005f571d0921005ee7690921046ee76909210076f659092144f6c6590921455ed749092104eee649092104eec649092144f6f54909210076d549092119eee639092119eec639092101dee719092101dec7190921046ef6190921047e76190921447e63190921447e5319092101cfc76509210067f65509211967c6550921006bf645092104ebc6450921005f7715092101df4715092101dec765092104eec765092101cec76509210076f655092143f6c6550921045ef7450921047af7450921007af645092104eee645092104eec6450921007ac645092143f6f54509210076d545092118eee635092118eec6350921007e7715092101dee715092101dec7150921007e47150921046ef6150921047e76150921437e63150921437e53150921044fe76d0521044fc76d05211157e75d05210057d75d05210067f65d05211767c65d0521006bf64d052104ebc64d0521045ee72d0521005ed72d052104cff7650521004fd7650521044fc76505210067f65505211567c6550521006bf645052104ebc6450521005ef7250521045ec72505210067f65d81210067c65d8121004ff75d8121014fe75d8121004fd75d8121014fc75d812104cfe74d8121004fd74d81210067f54d81210067d54d8121004ff73d812100cfe73d8121004fd73d812100cfc73d8121006ee42d8121006ed42d8121006f631d8121006f531d812128eee21d812128eec21d81211157e75981210057d75981210067f65981210067c6598121006fb60981210057f75581211157c75581210067f65581210067
  | 20 => 0x4fd7559221014fc755922101ebf74592210067f5459221004ff735922100cfe7359221004fd735922100cfc7359221006ef3259221006ec325922101cfc715922101ebe415922101ebc415922101eef215922101eed2159221004ff7059221024fc70592210067f76552211de7e76552210067d76552211de7c76552211f57f74552211273f74552211de7f645522104e7e64552210067d645522104e7c64552211de7f63552211be7e63552214767d63552211de7c63552210076f72552210076c72552211167d62552214776f32552214776c32552211de7e61552211df7631552214777531552211df6f21552211e77721552211257e75d0a210057d75d0a2104ebe64d0a21006bd64d0a2111dde73d0a21005dd73d0a2101df671d0a21005f571d0a2104cff7650a2104ebe6450a21006bd6450a21005f77150a2101df47150a21024ff7598221014fe75982210267e75982210147e7598221004fd75982210267d75982210047d7598221024fc759822104cfe7498221004fd74982210067f54982210067d5498221024ff739822100cfe7398221004fd7398221024fc739822101cfe7198221026fa709822101efb1098221026f81098221004ff7558221014fe7558221004fd7558221014fc7558221004ff745822104cfc74582210067f54582210067d5458221004ff735822100cfe7358221004fd735822100cfc735822101cfc715822101ef63158221006f5315822101efb705822101efb105822101ef810582211157e76d95211167e76d95210147e76d95210057d74d95210067f63d95210067e63d95210067d63d95210067c63d95210077631d95210077531d952146f7721d95214676e21d95214676c21d952146f7421d95210067f74d95210067e74d95210067d74d95210047d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95214667f72d952146e7e72d95211167d72d952146e7c72d952146e7e42d952146e7c42d95210067f32d952146e7e32d95210067d32d952146e7c32d952146e7f71d95214667e71d95211167d71d95214667c71d95214667e41d95214667c41d95210067f31d95214667e31d95210067d31d95214667c31d952146e7f21d95214667e21d95211167d21d95214667c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f30d95210067e30d95210067d30d95210067c30d952146e7f20d952146e7c20d95214667f10d95214667c10d952104cfe76d91211157c75d91210067f65d91210067c65d9121004ff75d91210067f75d9121014fe75d9121004fd75d9121014fc75d91210067c75d91210147c75d91210067f54d9121004ff73d912100cfe73d9121004fd73d912100cfc73d
  | 21 => 0xa5058041006f95058041006f8505804104efb405804104ef84058041006fb3058041006fa3058041006f93058041006f8305804101efb105804101ef81058041006fb7558041006fa7558041006f97558041006f8755804104efb745804104efa745804104ef8745804104efb545804104e7b545804104efa545804104ef9545804104e79545804104ef85458041006fb7358041006fa7358041006f97358041006f87358041006fb5358041006fa5358041006f95358041006f8535804104efb435804104efa435804104ef9435804104ef84358041006fb7258041006fa7258041006f97258041006f87258041006fb5258041006fa5258041006f95258041006f8525804104efb425804104efa425804104ef9425804104ef84258041006fb3258041006fa3258041006f93258041006f8325804101efb715804101efa715804101ef8715804101efb515804101efa515804101ef9515804101ef8515804101efb415804101efa415804101ef2415804101ef9415804104ef1415804101ef8415804101efb315804101efa315804101ef2315804101ef93158041006f1315804101ef8315804101efb215804101efa215804101ef9215804101ef82158041004ff7559321014fe7559321004fd7559321014fc7559321046bf74593210067f5459321004ff735932100cfe7359321004fd735932100cfc735932101cfc7259321046be4259321046bc4259321004ff7059321024fc70593210067f76553211e67e76553210067d76553211e67c76553212d57f74553211373f74553211e67f645532104e7e64553210067d645532104e7c64553211e67f63553211be7e63553214867d63553211e67c63553211e76e4255321007777155321007747155321045ef7650b21006ef7650b21047af7450b2104eee6450b21046ec6450b2147f6f5450b210076d5450b2118eee6350b21046ec6350b2101dee7150b2101dec7150b211357e75d07210057d75d072104ebe64d0721006bd64d0721045ee72d0721005ed72d072104cff765072104ebe6450721006bd6450721005ef7250721045ec7250721024ff7598321014fe7598321004fd7598321024fc759832104cfe7498321004fd74983210067f54983210067d5498321024ff739832100cfe7398321004fd7398321024fc739832101cfe7298321026fa7098321046fb2098321026f82098321004ff7558321014fe7558321004fd7558321014fc7558321004ff745832104cfc74583210067f54583210067d5458321004ff7358321006df7358321004df735832100cfe7358321004fd735832100cfc7358321006dc735832100cdc735832101cfc7258321046ee4258321006ed425832125eee2158321046ec2158321046fb7058321046fb2058321046f82058321004ff7559221014fe7559221
  | 22 => 0x884101eee215884101eec2158841004ff7058841024fc7058841006ef7558841006ee7558841006ed7558841006ec755884104eef745884104eee745884104eec745884104eef545884104e6f545884104eee545884104eed545884104e6d545884104eec5458841006ef7358841006ee7358841006ed7358841006ec7358841006ef5358841006ee5358841006ed5358841006ec535884104eef435884104eee435884104eed435884104eec435884101eef715884101eee715884101eec715884101eef515884101eee515884101eed515884101eec515884101eef415884101eee415884101eed415884101eec415884101eef315884101eee315884101ee6315884101eed3158841006e5315884101eec3158841006ef7058841006ee7058841006ed7058841006ec7058841006ef5058841006ee5058841006ed5058841006ec505884104eef405884104eee405884104eed405884104eec4058841006ef3058841006ee3058841006ed3058841006ec305884101eef105884101eee105884101eed105884101eec1058841024ff7598041014fe7598041004fd7598041024fc759804104e7f549804104e7d5498041024ff739804100cfe7398041004fd7398041024fc7398041044fe7298041004fd7298041024fe7098041026fa7098041006fb5098041026fa5098041006f95098041026f8509804104efb4098041026f84098041006fb3098041026fa3098041006f93098041026f8309804101efb1098041026f81098041026fb7598041006fa7598041006f97598041026f8759804104efa749804104ef97498041026f8749804104efb549804104e7b549804104efa549804104ef9549804104e79549804104ef85498041026fb7398041006fa7398041006f97398041026f87398041006fb5398041006fa5398041006f95398041006f8539804104efb439804104efa439804104ef9439804104ef84398041026fb7298041006fa7298041006f97298041026f87298041006fb5298041006fa5298041006f95298041006f8529804104efb429804104efa429804104ef9429804104ef84298041006fb3298041006fa3298041006f93298041006f8329804101efa719804101ef97198041026f8719804101efb519804101efa519804101ef9519804101ef8519804101efb419804101efa419804101ef9419804101ef8419804101efb319804101efa319804101ef9319804101ef8319804101efb219804101efa219804101ef9219804101ef82198041004ff7558041014fe7558041004fd7558041014fc755804104e7f545804104e7d5458041004ff735804100cfe7358041004fd735804100cfc7358041004ff7258041044fc725804101ef6415804104ef5415804101ef63158041006f5315804101efb7058041006fb5058041006f
  | 23 => 0x1e7f415944101e7e415944101e7d415944101e7c415944101e7f315944101e7e315944101e7d315944101e7c315944101e7f215944101e7e215944101e7d215944101e7c21594410067f70594410067e70594410067d70594410067c705944104e7f405944104e7e405944104e7d405944104e7c40594410067f30594410067e30594410067d30594410067c305944101e7f105944101e7e105944101e7d105944101e7c1059441006df7558c41006de7558c41006dd7558c41006dc7558c4104edf7458c4104ede7458c4104edd7458c4104edc7458c4104edf5458c4104e5f5458c4104ede5458c4104edd5458c4104e5d5458c4104edc5458c41006df7258c41006de7258c41006dd7258c41006dc7258c41006df5258c41006de5258c41006dd5258c41006dc5258c4104edf4258c4104ede4258c4104edd4258c4104edc4258c4101edf7158c4101ede7158c4101edd7158c4101edc7158c4101edf5158c4101ede5158c4101edd5158c4101edc5158c4101edf4158c4101ede4158c4101edd4158c4101edc4158c4101edf2158c4101ede2158c4101edd2158c4101edc2158c41006df7058c41006de7058c41006dd7058c41006dc7058c41006df5058c41006de5058c41006dd5058c41006dc5058c4104edf4058c4104ede4058c4104edd4058c4104edc4058c4101edf1058c4101ede1058c4101edd1058c4101edc1058c41046ef7598841046ee7598841046ed7598841046ec7598841046ef7498841046ee7498841046ed7498841046ec749884104eef549884104e6f549884104eee549884104eed549884104e6d549884104eec5498841046ef7398841046ee7398841046ed7398841046ec7398841006ef5398841006ee5398841006ed5398841006ec539884104eef439884104eee439884104eed439884104eec439884101eef719884101eee719884101eed719884101eec719884101eef519884101eee519884101eed519884101eec519884101eef419884101eee419884101eed419884101eec419884101eef319884101eee319884101eed319884101eec3198841046ef7098841046ee7098841046ed7098841046ec7098841006ef5098841006ee5098841006ed5098841006ec509884104eef409884104eee409884104eed409884104eec4098841006ef3098841006ee3098841006ed3098841006ec309884101eef109884101eee109884101eed109884101eec1098841004ff7558841014fe7558841004fd7558841014fc755884104e7f545884104e7d5458841004ff735884100cfe7358841004fd735884100cfc735884101eef7258841006ef5258841006ee5258841006ed5258841006ec525884104eef425884104eec4258841006ef3258841006ee3258841006ed3258841006ec325884101ef63158841006f5315
  | 24 => 0xe2158a4101eec2158a41004ff7058a41024fc7058a41046ee6290a41006ed6290a4101df67190a41005f57190a41044ff7650a41046ee6250a41006ed6250a41005f77150a4101df47150a41024ff7598241014fe75982410267e75982410147e7598241004fd75982410267d75982410047d7598241024fc75982410067f54982410067d5498241024ff739824100cfe7398241004fd7398241024fc7398241044fe7298241026ee7298241044ee7298241004fd7298241026ed7298241004ed729824101cfe719824101cf67198241026fa7098241026f7109824101efb1098241026f81098241004ff7558241014fe7558241004fd7558241014fc75582410067f54582410067d5458241004ff735824100cfe7358241004fd735824100cfc7358241004ff7258241044fc725824101cfc715824101efb705824101efb105824101ef810582410167f76551411de7e76551411567d76551410167c765514104d7f74551411573f745514104e7f645514148e7f63551411be7e635514148e7d63551411be7c63551411e67c625514104f3f425514100777715514100774715514104e7f615514104f7741551411df3e415514104f3c415514104f74415514104f34415514104f3f4055141004ff75d8941014fe75d8941004fd75d8941014fc75d89410067f54d89410067d54d8941004ff73d894100cfe73d8941004fd73d894100cfc73d8941006ef52d8941006ec52d8941006ef32d8941006ec32d8941024fe70d8941004fd70d8941006ef62989410057f75589411557c7558941046ee6218941006ed621894101cfe7690941006ef6290941046ec629094101df67190941005f5719094101cfc76509410073d5450941006ef6250941046ec6250941005f7715094101df47150941004ff75d8141014fe75d8141004fd75d8141014fc75d81410067f54d81410067d54d8141004ff73d814100cfe73d8141004fd73d814100cfc73d8141044fe72d8141004fd72d8141006fb30d8141006f830d81411557e75981410057d7598141005ee7298141005ed7298141006fb6098141006f96018141024ff7518141014fe7518141004fd7518141024fc75181410067f54181410067d5418141024ff731814100cfe7318141004fd7318141024fc7318141044fe7218141004fd7218141006fb3018141026f8301814104e7f745944104e7e745944104e7d745944104e7c74594410067f73594410067e73594410067d73594410067c735944104e7f435944104e7e435944104e7d435944104e7c43594410067f72594410067e72594410067d72594410067c725944104e7f425944104e7e425944104e7d425944104e7c42594410067f32594410067e32594410067d32594410067c325944101e7f715944101e7e715944101e7d715944101e7c7159441
  | 25 => 0x8042026f84098042026fa3098042006f93098042046fb2098042026f82098042004ff7558042014fe7558042004fd7558042014fc755804204e7f545804204e7d5458042004ff735804200cfe7358042004fd735804200cfc7358042046ee425804204eed4258042004ff715804201cfc7158042046fb705804204efb405804204ef84058042006fa3058042006f93058042046fb2058042046f8205804204e7f745974104e7e745974104e7d745974104e7c74597410067f73597410067e73597410067d73597410067c735974104e7f435974104e7e435974104e7d435974104e7c43597410067f72597410067e72597410067d72597410067c725974104e7f425974104e7e425974104e7d425974104e7c42597410067f32597410067e32597410067d32597410067c32597411767f71597411de7e71597410067d71597411de7c715974104e7f415974104e7e415974104e7d415974104e7c41597410067f31597411de7e31597410067d31597411de7c31597411de7e21597411de7c21597410067f70597410067e70597410067d70597410067c705974104e7f405974104e7e405974104e7d405974104e7c40597410067f30597410067e30597410067d30597410067c30597411de7f10597411de7c1059741004ff7558b41014fe7558b41004fd7558b41014fc7558b4101cfc7458b4104e7f5458b4104e7d5458b41004ff7358b4100cfe7358b41004fd7358b4100cfc7358b4104eef7258b4104eef4258b4104eec4258b41006ef3258b41006ec3258b41006f63158b41006f53158b41004ff7058b41024fc7058b41024ff7598341014fe7598341004fd7598341024fc759834101cfe749834104e7f549834104e7d5498341024ff739834100cfe7398341004fd7398341024fc7398341044fe7298341004fd7298341026fa709834104efb4098341026f84098341004ff7558341014fe7558341004fd7558341014fc755834101cfc745834104e7f545834104e7d5458341004ff735834100cfe7358341004fd735834100cfc7358341004ff7258341044fc725834104ef6415834104ef54158341006f63158341006f5315834104efb705834104efb405834104ef840583410167f76552410167c765524104d7f74552411673f745524104e7d64552411de7f63552411be7e63552414967d63552411de7c635524104f3f43552414973d43552411e67e62552410077771552411df74715524104e7e615524104f3f415524104f77415524104f37415524104f74415524104f3c4055241004ff7558a410067f7558a410047f7558a41014fe7558a41004fd7558a41014fc7558a410067c7558a410147c7558a410067f5458a410067d5458a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a4101eef7258a4101cfc7158a4101ee
  | 26 => 0x1be7e635514249e7d63551421be7c635514204f3f435514249f3d43551420076f72551420076c725514204e7f625514204f6f42551421e73e425514204f3c425514204f6c425514204f2c425514249f6f325514249f6c32551421de7c615514204f3f415514204f3c4055142004ff75d8542014fe75d8542004fd75d8542014fc75d85420067f54d85420067d54d8542004ff73d854200cfe73d8542004fd73d854200cfc73d8542006f751d8542006f451d8542006f631d8542006f531d8542024fe70d8542004fd70d8542006f761985420057f75585421957c755854218dde7318542005dd731854201ef66118542006f56118542004ff75d8142014fe75d8142004fd75d8142014fc75d81420067f54d81420067d54d8142004ff73d814200cfe73d8142004fd73d814200cfc73d814201cfe71d8142004fd71d8142006fb60981420057f75581421957c7558142005df735814218ddc7358142005f77158142005f471581421957e75181420057d7518142006f96018142024ff7518142014fe75181420267e75181420147e7518142004fd75181420267d75181420047d7518142024fc75181420067f54181420067d5418142024ff731814200cfe7318142004fd7318142024fc731814201cfe7118142004fd711814204e7f745944204e7e745944204e7d745944204e7c74594420067f73594420067e73594420067d73594420067c735944204e7f435944204e7e435944204e7d435944204e7c43594420467f72594420467e72594420467d72594420467c72594420467f42594420467e42594420467d42594420467c42594420467f32594420467e32594420467d32594420467c32594420067f71594420067e71594420067d71594420067c715944204e7f415944204e7e415944204e7d415944204e7c41594420067f31594420067e31594420067d31594420067c31594420467f21594420467e21594420467d21594420467c21594420067f70594420067e70594420067d70594420067c705944204e7f405944204e7e405944204e7d405944204e7c40594420067f30594420067e30594420067d30594420067c30594420467f20594420467e20594420467d20594420467c2059442004ff7558442014fe7558442004fd7558442014fc755844204e7f545844204e7d5458442004ff735844200cfe7358442004fd735844200cfc7358442046ee425844204eed4258442046f7715844204ef7415844204ef44158442006f63158442006f53158442046f72158442046f42158442004ff7058442024fc7058442024ff7598042014fe7598042004fd7598042024fc759804204e7f549804204e7d5498042024ff739804200cfe7398042004fd7398042024fc739804201cfe7198042004fd7198042024fe7098042026fa709804204efb409
  | 27 => 0xf7158f42006de7158f42006dd7158f42006dc7158f42006df5158f42006de5158f42006dd5158f42006dc5158f4204edf4158f4204ede4158f4204edd4158f4204edc4158f424aedf2158f424aedc2158f42006df7058f42006de7058f42006dd7058f42006dc7058f42006df5058f42006de5058f42006dd5058f42006dc5058f4204edf4058f4204ede4058f4204edd4058f4204edc4058f424aedf2058f424aedc2058f42004ff7558742014fe7558742004fd7558742014fc7558742044fc745874204e7f545874204e7d5458742004ff735874200cfe7358742004fd735874200cfc735874204eee425874204eed425874204ef7715874204ef7415874204ef44158742004ff7058742024fc7058742024ff7598342014fe7598342004fd7598342024fc7598342044fe749834204e7f549834204e7d5498342024ff739834200cfe7398342004fd7398342024fc739834201cfe7198342004fd7198342026fa709834204efb4098342026f84098342004ff7558342014fe7558342004fd7558342014fc7558342044fc745834204e7f545834204e7d5458342004ff735834200cfe7358342004fd735834200cfc735834204eee425834204eed4258342004ff715834201cfc715834204efb705834204efb405834204ef840583420167f76552420167c765524204d7f74552421a73f745524204e7d64552421e67f63552421be7e63552424a67d63552421e67c63552420076f72552421e76c725524204e7e625524204f3f425524204f6f425524204f2f425524204f6c42552424a76f32552421e76c32552421de7e6155242004ff75586420067f75586420047f7558642014fe7558642004fd7558642014fc75586420067c75586420147c75586420067f54586420067d5458642004ff735864200cfe7358642004fd735864200cfc7358642044fc7258642046f77158642006f63158642006f53158642046f72158642046f42158642004ff7058642024fc7058642024ff7598242014fe7598242004fd7598242024fc75982420067f54982420067d5498242024ff739824200cfe7398242004fd7398242024fc7398242044fe7298242044ee729824201cfe7198242004fd7198242026fa7098242026fa5098242006f95098242026ef2098242046fb2098242026f82098242004ff75582420067f75582420047f7558242014fe7558242004fd7558242014fc75582420067c75582420147c75582420067f54582420067d5458242004ff735824200cfe7358242004fd735824200cfc7358242044fc7258242004ff715824201cfc7158242046fb7058242006fa5058242006f95058242046fb2058242046f820582420167f76551421e67e76551421967d76551420167c765514204d7f74551421973f745514204e7f645514249e7f6355142
  | 28 => 0x85541df7631185540077531185540057e70185540057d70185540f67f64d81540f73f64d81540057f73d81541bd7e73d81540057d73d81541bd7c73d81540067f63d81540067d63d81541e57e72d81540057d72d81540067f62d81540067d62d81541dd7e71d81540057d71d81540067e61d81540067c61d81540dd7d74981540073d74981540dd3d74981540e67f64981540e73f64981540057f73981541bd7e73981540057d73981541bd7c73981541e57e72981540057d72981540067e62981540067c62981541dd7e71981540057d71981540c57e70981540067f60981540077b60981540e57f74581540073f74581540e53f74581540de7f64581540df3f64581540057f73581540075f73581540055f73581541bd7e73581540057d73581541bd7c73581540075c73581541bd5c73581540067f63581540067d63581540057f72581540076f72581540056f72581541e57c72581540076c72581540056c72581540067f62581540067d62581540057f71581540077771581540057771581541dd7c71581540077471581540057471581540067e61581540067c61581540077b60581540067e60581540f57e76181540c67f64181540c73f64181540057f73181541bd7e73181540057d73181541bd7c73181541e57e72181540076e72181540056e72181540057d72181540076d72181540056d72181540067e62181540067c62181541dd7e71181540057d71181540067f60181540077a60181540067d601815400779601815404e7f745974204e7e745974204e7d745974204e7c74597420067f73597420067e73597420067d73597420067c735974204e7f435974204e7e435974204e7d435974204e7c43597421b67f72597421e67e72597420067d72597421e67c725974204e7f425974204e7e425974204e7d425974204e7c42597420067f32597421e67e32597420067d32597421e67c32597420067f71597420067e71597420067d71597420067c715974204e7f415974204e7e415974204e7d415974204e7c41597420067f31597420067e31597420067d31597420067c31597421e67f21597421e67c21597420067f70597420067e70597420067d70597420067c705974204e7f405974204e7e405974204e7d405974204e7c40597420067f30597420067e30597420067d30597420067c30597421e67f20597421e67c2059742006df7558f42006de7558f42006dd7558f42006dc7558f4204edf7458f4204ede7458f4204edd7458f4204edc7458f4204edf5458f4204e5f5458f4204ede5458f4204edd5458f4204e5d5458f4204edc5458f421aedf7258f424aede7258f42006dd7258f424aedc7258f42006df5258f424aede5258f42006dd5258f424aedc5258f4204edf4258f4204ede4258f4204edd4258f4204edc4258f42006d
  | 29 => 0x48002000000801001c000001801c002000000800000c0250038004000016000800001a000000000c0000000000028000000005808800e01100380000020040010004012002000004800e00200080040040000008008002000001002c0180010000010016005000002c004004001001c00c00000000000040030000040020023000001c00000100080140000000000018002000002001c000013001000c00a001001803c02000c001000000000100080200140001b67f64d89541b73f64d89540057f73d89541bd7e73d89540057d73d89541bd7c73d89540076e32d89540076d32d89541dd7e71d89540057d71d89540057e70d89540057d70d89541957d74989541e73d74989541953d74989542d67f64989541a73f64989541e57f73989541bd7e73989540057d73989541e57c73989540067f63989540067d63989541e57e72989541e67f62989540076f62989541dd7e71989540057d71989540057e70989540057d70989541a57f74589540073f74589541a53f74589541967f64589541973f64589540057f73589541bd7e73589540057d73589541bd7c73589540076f62589541e67e62589540057f71589540077771589540057771589541dd7c71589540077471589540057471589540057f70589540057c70589541b57e76189542d67f64189541873f64189541e57f73189541bd7e73189540057d73189541e57c73189540067f63189540067d63189541e67f62189541e76e62189541e67d62189540076d62189540066d62189541e76e32189540076d32189541dd7e71189540057d71189540057e70189540057d70189541767f64d85541773f64d85540057f73d85541bd7e73d85540057d73d85541bd7c73d85541e57e72d85540057d72d85540077631d85540077531d85540057e70d85540057d70d85541557d74985541df3d74985541553d74985541f67f64985541673f64985541dd7f73985541bd7e73985540057d73985541dd7c73985540067e63985540067c63985541e57e72985540057d72985540067e62985540067c62985541dd7e71985541de7f61985540077761985540057e70985540057d70985541657f74585540073f74585541653f74585541567f64585541573f64585540057f73585541bd7e73585540057d73585541bd7c73585540057f72585540076f72585540056f72585541e57c72585540076c72585540056c72585540077761585541de7e61585540057f70585540057c70585541757e76185541f67f64185541473f64185541dd7f73185541bd7e73185541df5e73185541bd5e73185540057d73185541df5d73185540055d73185541dd7c73185540067e63185540067c63185541e57e72185540057d72185540067e62185540067c62185541de7f61185541df7661185541de7d611855400775611
  | 30 => 0x40008024022007001000800a001011000000e00100000140040000000004004012005002800401b00280040000120000010002005002803000404d000000000a00d00100300040030020008006011011800800001f003800000200400080180240010008018002003000800000001000080000040070010000000003000801400601d014800c00400000580040000000000000008001007001000000b008000407000700180840020030060000006009000000000000e0038000018003004001002801700080000200050058000002009000000000a00500000000260160108008000001002000400200300f8010000001000000000601500100040100080030014006002003800400000300180280080000030000022005000807000400a00900000000000010024032003000000800c00000000000080050000000024000005800805800a00d80340020020070000002002000800c000001001800c01400000e0000002008003000c002000002800c000000000000000400000200040000050000058002025002001c00200e0000000000001000001405e00600700200060080000024004006000007800800a00000000020020028030014003006000400802e000001000c00c001000401200300480400120060000040012002000001c020000003002c00000300080000080010000018002001000800c004001000000001200400100100000060000000002014004000c004001002800c030000000000000200800400600620080048000078000003800801c000001002c000001003800c06600500000780020010020020060000002802c000001000000005402100b002401400c00000280020000010024000000001000402600200180400100030038034012006000001400c0130028024002009004003400200000800100400020000018008001000000400000900000000000020018018010002006800400400700b809000000c0118000000007001800401400b0008000006000013808800c00000000000080070010004004000001000c00600800000c001200d001802000200401a8028022000000800000c009000801400200a00280a8002002001000800c0050008000000000000000c0060020078004006001000000000c01f000001800e002001801401800600080080040040000000004000000000407e0020000000000009001006000200000380000020010008004000002000002c004003001801400e006002000c0040060078000004001000000001602e0010000000000006000c006001000001000c006005001400e000000800001a0000018004006000002002401002e001800c000000001003c0100020020000004002000800001a000001801800800f00700000020090098004000004006004803a00000200040160020070
  | 31 => 0x800c00e00a00000380080060020040016001003802c016004000000403e00400000040040000038068000000001800800c000000000800a00c0000010008037000000401000a0000004004008000800800000300080480000020030024002002009000400000e00280140000210000020002005000800800000400000140180010050020018005001000001e002009800002000c001801c00200b001000000a00300000000020080068008010011004800400000a00180200000020008028004000000800000200a006000000002b0030004006000000800000000800100000120000008008006009001000001c000000804400a00100b8028000000000002c000001000000c01000100000140000030020000008001000801402c002002003c00400000000000000030020004000001005000400e00c002000c0000030000034006008001000001200a001000001e002000000001a00a000801400401100000040000020000060004013001800c00e00300180000060090028014000003003800000200100080000080010008000000000007000000000000300240020040020000000002004000400000100000100000000000008002007013000000800100000000040020048000038007006002400000e0010000020007000000801400400000c000000200580200b000f0010000000000001000001000500380380000020030028000006000000002200600b803c004001000803c000003001802c02800e00100040020000028000000000000004c000004005800400c0000018000026000000801c00000101700000000020000038012007014800800200100000ec01c0020000028014001000800000a001000003001a00b001801000c02000900480000040080000016005010001000401b002002c010007000801400800000000d000600900080040000000018024016000002800800c018000000000c00400100000000050028004000001005800401a00f00480180000010058018002008001800402000b001800000000c0040008002004000800800000f00080000020080000000000001025001000a002000000c0000050030000006003000001800000d000006802e01a000002401a016000800001e00100000000040000008000014000000000000e00000f800400600200480080000030058008000007006000400600300000040060060000008008000001000c00000500080540060040008004002000003000000400700180000000120010008000008001007c000001007800400400000180080100010058068040015004001c00200000380240000140038000002002000002007c02e0018000000000008000800600d0010000000003001800800200000200040040020020004022008000804c0200030000020000012003801401e
  | 32 => 0x8000000108676708a01c1a0c60001a82000088a000000000017b600012cc0000b88435000000011e68990a003f123b489a1f7e000015025180008dd80000c50e3a0f3000049280009c5800067d000055c9e16000000037d0ca44fe22a65771eb43bc0b3e98ba2820d986d630ea4fe0b4917a40e8f9e18a91ce0000000376052667405862f822d23cb22c84aca76205ba41800000000ca02b47c2097e56d94ca40284700150ac0990011a37f8c7275d08c600022a400022661a8a08a86d80008a1275c1979a249289f2000011680001ac8849a6785c899120e089dc056959200002c226d80003a000005b1a30800017c8000089e35b08240000000000000063480343b4811600000000001ae800016567b699ac00000001b2000000007167ab998c2f581b252580002e7a29e00008b00001a36000172a290231848a8d2856391b252293f2000050000000004410000000063200023be0001fc800000008ba1e9400017800001bd20002224558000000003f80000a8c69280000001a62877800043a0000105000000000004ab051c16d19cc24f160677080000001c2c6df000000020fe25880000cd1df67e38fa83c008e200024b400008f4000023612b82d84f21b48471a63a00014f20001bdc28a9d18065021e5dc904c5548c786c20d6e00014763a79a723c8a33e231000000023cc003000400600000000000120050030078002000002000004000c0008000002011000000400600d0000004000001005801001c00100580000020000008000008000003808400400000580200000060000000000003002003000400e0018008012003011806000400100d00300100000000000010001003808c034000004001400000a017800801200100100000060210000004014008000000402a0040018014000007002001405200400a007c00000a000000000c001000803003a00100180080000080030048000001002802000200200000cc00600c000800000c0030028000002001000000000200000180040040180018004002002029007400e00000000080180020000030014044001804c000008000000404800900a00000000280000070008003000000000400c005000400000000000140020120000040004004005000000a00300500000020010000014000000003001c008001000003c01600400900000100000000008012002007000001e00200100000000000018028004000000805400200600a000000200e004001402e00a000001c006000002001001a001006004c00401a0038010000000007800001a000004803c006000001000000800900000080300000000000022004001000c004004000800c004002000000803800300600000460010050000000000000000c000006005007c000000001000c00801700000000020000038000090013005
  | 33 => 0x4881b10342749f52000000080196dc0001df00001026494944a1f19a0a3a59bb09120ab28f791a21f51ee6517a42e1110b30670011c03190de6578fd696700009cea4a00001ee27a90000930a6ec30200005f1848c00026f68b5000098000007a48c120b9800003913a0000220a00002520001e1e6af8f7635c0b008a293bc02903625fc0b4400012ce000227254a0a243a1081a0c98000769a2ba00000006fe236696a19de00000005c6a4e293b87d038c800000026088d1a6de2e00b2879800009009e1c5ec8a2600000000001b72733258000004920001e4c0a3800000000ac000267c000246200000000000000767800045319c400000005e60000000170a0000bb4462200c708800000019748781ca05e681341bb906a61399780001cf63731dd43ea98da62a1da030b854a3f3018649aa0e44bb89444481b4e99505c69929b82000230e72180000c02400191212837da38e9ef25ce08c0bd0322a5306b486b26c50cae383854c997065657c8000529a2fa000234c06280000bc09980b40000714824a000000000000000000e3e2829e1200000006758e4800010bc274143801ca7463fe8a747db00005e29ace0001c184d412161e2086e47820988bc8000815008c63d8c2a4e880000000000000000000024061b990dc7ee00005f6a01e000000036d19662ab178c4d4800000003d65d0800009ea3f000021c800000008f38000074800055f00000000c8e7190b6810ba59a75e17887909f54425962064393ac3828df200000008c2800011ca50453d9ae00000bec45e1b208400000075800000027425029728513800000005fc6c28a0675f91fa327075a6299fbc31d95b42d2a5aa0be007c0001a9c0000000000264e0001850935944277680009d582ea022904000014d4000000061e19f20000000585000092e00002caa5d01431f4c2f308762de943e00013e878c80002b284b83ad80008e7800046922803219e6400000000c280000001af67d388187158000000000000007fe072a7a867080006788a7e0000000000068078d01287db86a06d88c3200009002581cba30187aa7f090d08958fd03851e307d701f05ff80040000ecc253800014b8ff6529166e7d6937853a0f400d080008da055c0001dbc1a11b9e6148cdc01617bc2219de44c307b06bd156a11681424fb09e26808f162838a9c696853c8c984ca86294dc6bba6568238a1c24aa73052c1e2426b045452112c69710dae50092aa55c231e398843a6c9020c66682627628f725888fea39b9f3a68e00ca5c987a61cd0bc647f0c1e535a0640b590641a300ee0000aae4cc00007240d748271dc094d0e364d8895e0851dd20000268000118a000059c000000000018aa395800074a80002d180000000acc817a0d20d390ec000000074e02c0516954800017d60001b3482002386b
  | 34 => 0xe382a494900005380a220e10000000044600000002470000000000000000000000000000000087287146fd0ad68258af23df00003ec0000000000012e84526c100008cb81a800000008cc24786b782320658000000067410704b4802a33823e0e78630000000000009340000000135400000004899f1000023ee8f501701db80008118af096893743f2979655b1dea1f9156677888a6000095056a000075920d06d825fa00018ec30400680000000115831a72a16e08e31f327bca76040ba2262d387ee152080876a87d27e2a2906bf93ba76403f22cb8372963827c285841a00022708d925dc1bf23c0654975454b1bc0348042210f00000001c680d700005a400003d580008cc90b23258a443e9104851914340001a48000103697f9bee3a2a0285db0000000000046b00002508000000258a6971d4000009384ba8000000000068f8a66000000081a800029b000013500009b5a342280800002c0f4214880004d380000f6800034c99bc12b189c2251660976150a3ce872a82c946a0ea869066395e400006f05739eba0af80000a604a878f89966a2205292280ec8579b100a2a1aa2641f427b000003bb884c091096c50c065c4980d187d1a4e04a215ca6ada5d600018106fb21a6322250000013d800011ae21920e295c98460000c2c6b1000008697ee000000004d93247ed19546e280005c50dc822094986b98f207c3a2da9481b2294214e238320da130858000024aa0f215882fd0b0c000000000023160000a92748055a000033020b1e066648ad892186cc0000000000000000000004389062750870a9e30000000000052500000001dd07530f94960800000000000000590474000081ea6be00025688800f5a2a200381638000931000000020e0000000000000001aa21f8272000067aa1ba60c00000000000000000015f00000000000000270825f25b6000237400021e882407e8991800051319a898091f61208de228405de00013446be169e2778cd62200d968f21c6077e80006650c8c7650000848915296ba4ba00004164f31d7668b80002c50b4208e9b38000000050d82f400000008c89dfc989a5507dc8d3085a24249251adc86d10024f40e2c07d1d2200c10ee27c0c0487312dc5070e548b11e623001bf65911af24040000379036077e1ef41b785f662f83046f419a088100000da0000418009000019ce0041cd8000000064780005f91b12062000000000000000c204b7911c640a79079006e854c234a0378b10000000000000000b8909a89d8ccc9b30000000000042117c0000155893500005a11d3200015da5b21a6000b20f81c80220178017817a97ac000040c3e20c80924825000000003e982969011efa6f28dd627d14bc0001056898859a052800051f870e22e80007b90000000197a000000029787e27c498c652d1e
  | 35 => 0x7369ce60002102464903c200923a000167e6d19a7e60f193c7339c3e62ba46a000000000012925f5069c00020ac000073e7e688743eb9faa57f0dac000083045027949a195e27c1a5c25f88de62e295e689f25228d80f6e09180004149f3822122386ef800004c800000010589ee127a58b105005d99ec5778ddc2d200008b898288fe0000000233c1b193180000c2654c804011e90d261d19aa000111e0000000580a3d87bf0f12312a3280c4000098f85a08819a400000d2e6e4875400021d245580000000fb2000007e2d59ac03c6a4a4000086845c000089e960a00018bc5338000000000000a07b20001cf200020bc000109858e9d5a000000000000000001fa800000002b1050207e904e0000000000000069d1d2e3d91ecc000171c000000000006220fd8d0c2549e7635e98660551fde1d08750000177e19e26ca0001a421c7155c16311de6dd14fe183268e1130fbe79e0d040df2540237921213a0052000000065ca538467195043600004000fee40c89e646a21da2ba9baa4939fee6081a863b8097630d94c82e48dca11aa59e2288000207a5f40258cf80001db00d41ed6215101c875083a20f22302afa42c8639e029bba2d668c800034081c08700000000000000005601b016f83d48f185a5119e0000f3442d9bb429e92e0596827e29c000086b06b80a6a25c43da0a24ea9a100a880009ab04120001a0c0000ae400001605a217a49339ed076da18052b1c44190800069595d49cc87e60e497666ff06b67dc1304678142465809ca59200007a800000000012000201412627585c380006ae97560f10b8282b94ea1a0a24e9a1001674d18dc2bb00008a580004ba18ea4d980000000d6a633a40e71c80000ec15be9328e7e18d88006b5a7ac00015aa00006a61bd911476695ea0001242828103e223800000022fe0000000000000078a947461d91ca000000096c8ec89cf92da6b60dbe1648f387a6916a9c00336495000069e9ef07f700002aaa0fa000094a6f59b6c8c014c4463a1785e0914e94425da2ed8024826a1668011ad472c80009d3095600000008bd1328442221c8bf11349550000000187c57b0eae00000005d90bca224000079616420000b5c64512660079e88000000092600000251c204a38f8055402ca00000000c70d800001ff0000000000020ce9558ade00009807a9884658c92b00000000764826c00004205fc9d6200000003641900000207e8059f9e0000000691240c4eb835a0000f1456107320000000000000000024207811bae8ad9a6e3a19c0082a01e08f980005ae8000812000004024be9b80d2c1b0876270586aa00000001cd8c7e2f88cc600b8124000180a54594b865326941a5054e9e6953e02e00004a41b6e029a62c5928b8e0ff80000ee0dee85820be0000af80000e08000000026b8e7a1
  | 36 => 0x7f280805679a7c72d90ce0000a1e1a380003b3800068200002a823c696e00005550000000237c0000bf692100006faa4a873c102285f036a5ff2114168800014395627c6000014616cc04a94868b3006e0001f807ec8afa65005ec87ca6b219407f204b88ee8b79d6c92f20789bf000038080001a7800037780000000828000000040e000098f0b3600001fe00008f2000229a00016a6000015c09a8c4e5f30d7618e80009d280000000b540b805fa6949b320d78000000049e48415fa0001e7428d128063908aa46080006ab800000000008c426101fb1a0010c000053e802050e931613d1b443470000835097200014d2000243c000097a0000f4a00021481b4a7148180000000068a0001d5800018b23ad00004308000000000066d800055d972499d8e8c00014be00012be000096a8bc00000000ac8000251462e8b500001b0e000279e3501dc6427000012409e0791038c5ba20b806d18023ba00000000000000000000011ec66c800000000000000000302813a3c3800037b000025a01b000022ac1bd243a8531dc800000000002724808a7a01f780001710000064954246e800000015ee0000000606114800017ca9130f0c0000ca27f400009a315123f380001e88000256204254e8d34000044022b000098586e43cb8bde1611334043807a00018f400000000002286645866a00000007d8a348000136e01981e8672a59205fa07c4a91c365800000000193426c904a727174000000000001686853951c82093fa93223fe0000ec636a1be00000dc037c166a891000085180009651f7a00000006d58000000089c00000000001d7c883977859b246e35088106ae14c07c984ec0000000071217671320b600004a696406fa2df263400013e44a5154c00019249d5000084200487b10cd8816935c9e70000000081206b00005559f287cc00001ca1d00000064a00000002fc800013c18f27bf830c00000001180000285000022c852a26399b890890ac70784788b9a69a0000b1a95f87f021e995a5aca2ec00000000000000000000000000000000000000000000010fe80624c67e620fc0000b8c000000070b9afa00000005fd800018410ae2a5949c60d9e80000197e886969242506fe37a1a1288400000c804b669301d00c492206ee9d88000247e2c58000794028001c07fa1ee1dd8000000e1410e6025ba3f494710e4527883e69a132c0001f1a0000fd47050000000236a75e8000831000007900005bb9d5e70aa1342cc949a8af0a98000210a00002847ff140e8708000193000021f115491ca6b43ed024e00000007468a8a2dd80001cb1f602a5165e2f3a6c800019561419ff400025c80ba00003be24fa00000000001bb824c12f24e3191a41f1edc000277200008ce01680000002466000194401280003008438565a6181c99a3a7250
  | 37 => 0x1e46456879e8e92076257000049b196486e0d5c000207200000007011a463a38982401000000016c0000000000000003bc84ee000115838e03b20001b504499f7c000247013002341b10f3233500e22128a5600022b06b6800029302c878895c400004b235292ec0000000000034a00016340000d3c0000b083e600003b40000000215c3178000236a00e182800000009ec31880009a21f2a076188600c8d9c5a700003d88000000220c00016405061ef80000000000070456ba14a36900000001d1c00000005f818cc000256080205d60001f5698825d24179b5a00011846c61fe677127b065a94c245b8d7c219993e0b5265003c8910085954e70406347b19c7e18126661e8128c5609d7250116a234900008790e528d402f22d49d4e98c1b1e4201412661913034205fe32ca0ba374123c7d41b5e000245670c20ca9980a129e39a6457d8000268217280b80003ff13060000bd251e18544efa4347318c48270038a5ad8dfa5b08c400238f9c39016763928e5e35a27686ca954072e0eb82b99e081e5904200014204800bbc4f3a12439700000001f24344a66e09795fe7f888fc0dd1e8200023e43a41624000033e000000000006683d78000729000098180009de0eaa0001c500001e8c47509bc34f947229498720000000386800000000002ee8000047a24a8eba4f05200d8e30e000086707247c7108a6f311666b19ae493b0000632a54c8c50000000063c2ea8f0241980007fb23e20f9000086400006cc1e1a9cf000000018d8162a15647a000060d11c850f1cfa000000068680001890a9e000241000000005c487ea8798000000000000012a28bb9d1e000162660100000000c745d2847c0000000817000000016a894290ba3d109947bda4f25ed23a01f704be3738c347ee99763c10b0e6f680006f380000aa84647b502fe0000000996121a2b519d85ae19849e1800000017440eb000031680009a980000000000000106e3f215a265610ea8fc800026a90b800020a40001be2628048674d80006cda4c0687000000000006bc23a621600e095a87722d980004441f4801080000000000000232000022889459e9e20ba1360000ef62f7257600022b85b2a4888ea8c301428a547321ae205607088c48ae20e7246026e132600001268ab83063ac91fe92b022a27e025644c84dc6aa917e55e9cfc29618569d90b7800000004bf1b78226181683080ba000107899f92687e80000832266458f0c462c60a8e71e8b9697893a600000002d7a5a000020a64369ff800000002dd2074490000000000008ec800000000008a8800040c04e08080ab8000260c59d116207f0a482c2a5f094697d279e801c7e21c422f2000072b8d624c2921c9a621fc069a53200000000000778000000010aa19a52aa5cc0140a7800180000000000000000086c8000
  | 38 => 0x47c08e2886c02da59898801bb19fe56b046620d101e00025f61b426bc3bb0000000165215e96542ff17849920ba41550eea6e993f0956a22e32ea0e81129e2c85b80002f695f859e1e365ea00000f600006940a82261800000000d400018c41222738000000000000000002384098019c8951d6a0000000357a452837000097819da0000bf803d80001090000000185e5b91c6a8249b1630f111280da76e5bd043e000234e9e2955e00017023b9a08458680005cea3d20ea137688a05b63e89ba8046000052200008398a3e57623ba57020126ef26d82628d8a511865a94325263248e9870e0e4c0000f363c99fc04ae9ffe0f885249ae86026d91a2a9e1272077b958a0cc8e42630a42a8c316d434980008d59c8c4d1865400012f60000ec27baa6ce138867218598829111aa624810f085c16721a1800000020ea438090e00009fc000173436898d48e01e5c0002446033a692892005c4e4a77e4e71b54306097463980000000000957000077a000000000000330efa0001a2205a905415618c824d07d8018120a000146e69613e23b600000000fc6539992e154000028a0000000000000005d80001d4400007520dfa2a834897a072a9938744009800026fa44a87a833b0adc68c16981998ff45a808a843e827000000005a595c83030f600611ba08788a60549155a26883467770dc240195221c3053a9ea84fe84b8c3e36a93da2e19bb63dd1c3a5031230000189047b91244220b620000c6e4f4a5361d80398386022402d17166a617be6fc085e4bfa49c071935600000007278ace000000027a03d080f8000543a1d000000009c4916c000055613e8180000000038581026e3871e47a93988189b6683300f82110dd496c0000000123e0000cf2000000000000002bf800000011b0000000000013406e318d07169d02547a02c83795188faa37a15a03dc1060e7671225a66e9000000000000000aa82c1a5e4443800033d16d81f000005171e525bc20b06108cd024f800016c00001b80bea0419fd40db800024d8c50524a4740000e64800948e00017909b1800000000003ef000000000007cf07e07de05642cb12220001ce40000ae87f49fd680705e209715f45db8e6a8e4a390907108c0348a86036800063f80000000618000204c0001eb67f1877657826d030682fa7eb88e64ff2050066144085605767189ea28cb0f840001894000000087a810c0300d723c78f7049e000020a81b600027800000a7c50b13880b11a2c00020403a814b68e61cdc64e9d2c3b68000245800012813c073408487f90ab42d9136a664210c0208bee5f7a3ac000245a44b272636e09ee4091c78000173c0faa116465972e3880bbe0fa01666e10e9a2a989c670ca034000041e0000000495800000011da1d19e385fd00005a91bf20001db8772a74049317ec5a0
  | 39 => 0x780000000f9254aa2420138862234272c9c28ea82c7000023e9f8497780004d200023d604de67e9b288d480264168bac000000000000000000948890022c3b90ab685092b870205e66fa17620f5000000000000a48000936992800000001821df45069c920000a1a5dd988877f9cf48569f6600000007b60cea69d800075c0000000040400005e800002729d983ec3050d54015a23a1d205709ef999c9589a2863ea7ae97c800003ea47c1e1975a3a9000091386b4179000088c80000281372101a752000254a00000000000e2615f851a00011c44a60c225408bfa3a9a15400000002c10cc261c00003969408450874419e880e2d007d6338251848526f86c68b3a36081da9238ea240b017c4be8e9c32e05287220be86519c0c000000000006be539000010a1a8499b03b422597708d50d581ac0d666e0189e32d1cee7ed88560fea56c61a056a21b099e3de9abc13ca66273a8000000127e5ba8e1e2b69ede9c41a703a5101876301204c689886f200000000000000263836d994e21c812c44e1ee800027b26fe80229509d3a84c25740ad8d4c7e598e819c07120d200ea2050da062e169a483a6124ca97e683c235c1c68bd8593979c73a1f82000000000019200ee9ad052b948c28e8000000001a0000000000000066b80009258c664f5982651622f800008ca9a7a6904e38d9800000002a9072e4600000126800009d20669b50c161dc0dba0000000000091e9cd88200000000000049600000002942220000000000013ee00000000000000000000004e0000000003e8de11b47311d2800005ae7aa96aa47880008e0831612c07308a318ac0eb8970000204e65222b40000e6616600f43b2833a58b83940001c6633c0f086d0000022f80001da81a29c1a416060950669e10087c2800000019829108ce867e21640548000000000000021921d9000041e92d432516585fa000000000006498b9000000002180aa200000002ea11be508988c341938620d92c84b41a6a761218c249924846500005b79c26027970610d8574432901416a02f69539f680d921d800025c045d9a5e00007da000081c8ef16b000019221a5a52800004d6607033852a00003b109d815e0000000077e70680000000b6e000000000003ca877241a28c0000789a1108949862541178e66580000000000000000078809c200002885748892000000000000000001da87b4a53c203000024c80000000000000067e84186ea4290abc36c80002169cd4000000075a137e9330d380001090000119a9a88d842550f060730e2e9208cc8177213e00023dc00009f24b898b00ef99a274380007e19bfe537a2940000000909927c0f787f48f089283df96d650a861297b8000022122e00026a09e60e68875a35809004bc88788708dc0cbc49c1de618c1e9c2410a0c4ec8c9a30381d
  | 40 => 0xcc1bc951a0d59f92354151474211d27eb02069828d781d6077421011b61f1135a4468cce38f1ec81c40064618000002fa302519a2c0650930e652800067a0fe6296934c0f99f407dd1b880001be63de0de071f02085da800000019a66e88ff0000115c528800000003f072d043200005aa717a57000000004df00000c0a4644579b8653b800074c22360b308ae26485b818f814035f8000000000005795368978000435800023c0000288000000000004f1800873e23fa000045041d886a3f69ebc9aba5e82fc1b6a4f289ba7a1000018180004b90000000039a47e27747378a4e00000000000bc00a80000000000060905c22e512500000cbe0000dd2000176814e000060025ec06a82826a290a800000008ff0fe200019984e505f0000243000f156e4aa0000000000000019dc486083828c8d468b926c200023240000000990800096300000cf13b61d7970c00012726190ba28ba8000809990400013e01e4800071b02ce066800059a263684691d60801f44514a29c3e3a17a14c856232793b894f82943438e4414b16109ba9e7c896901a396158c4cf972c2c910c067c26a43c4000057c173e89a83a000000000000cb64ed04580e9800000008043ca85c00000d6486b8e3420c8a4244611440000be613a98385cd991c862181235217ba00000009e49ab00001664000108258e1e6a00002ec79a000031f12c200014f458d863835482c66d4a77a00022e03ed8000795192a8f687984cd936812385ca13411aa91a08bc6a90e8884f26e215c85963209d543a481ea8359c120e780004cb800002707ae8e6800000022589dd9b966429b7e83d81e68679fea00000001290a9085a904653e07682df920651f02587d901dc45404c425912d228ba1f47e7000031c07ba59194fc5650f8a6de87ac55d231c97980002dc8c5633f9aec00006921549b067b287841ff0000884879418b1afc44f12b47e8a26012726c47521eb20bb85d474f98060001ce2384197067d8bc47f300c205587000fba6e807780004a991602058000000029c0218f9a59316ec05b211836497b087e8b7064208e87a41bc6000130232b09e48ee00009c11d4a83b80001188cc04b109da51b1b2e82d233a6c98cf631491f21ce86984459a8c3f6056e2ff9e0e7a180bc7518484000119000281f88ec1ff649d803a2220e24084175e3568cda67209080a413581109df24d0957838497740000000924000039b0000000000042791f4000000000000003fb00007fa061400000004a18000000114a000006c8b4105c2360b1e86f09240e5931c0000ca847c00009129d60551800017c935e5d8227895f01e25af95265400efe000000000001c260f800000000368c11d5c66c17ae45d00007cd1c4057a0676821900e00024144b995645df030877b01483e3000047600000f8032a94
  | 41 => 0x168df800016f69daa2140451b5851c1a0e27fa21804c06ca74193c23d405ce08700001b60dea2ec8b6c7a60dc619f168e000043494b800033905a40ef000031602a8063890283c92580db00000000540000000000019d49d2000050b968c6a4800000000005a28000226855e93f000028f060046e2702000211c6f08000720a48c0f480003d704c8248a26e00024328161c9861b80a20001fe010400004a125b432999fc65f14a095214561fe1fa43cf0a2c2eb84d818b844821391721ef8000051264c76c8d008aa8a625ab1a8e0000f6c78e8c4289b15b8629240a2a691c251884808619f90809004639c0d9e44a184018386f80000000869091a8e580006e500004969364000064882a822282780e8792a458092000026d1e4e3ae9ca200026aa00000002c0840800000006a50000000000034d912e5ee21c600000000000eb01e320388e880d831718d6743045c38aa3a8975058800022d87ae000019b80000e3a0701c881ce1e9266a2f0992c86087823ca24b014c074c7731cb00d30000448800093a80009aa00002668940160a3b6927a65a941a24c63e22ca4f79d500000d8842d216c366854473f929a5f6174e59ea6449a009cc38714004b614ba31b0cfa76621f6685247a5c016500179c702418d609620e4e1ed031862da73493788428d78f301b5182a27126fe815a4b61d393c44a5816884a96da03f16d048089ce4cc874a89f96309c696ae172113e891a5ac0001074487838680f0fe4196040a00009fa97f1a9e174a6240001d040001b0c0000e82841023c31a00000001eb04d2a5f841b059400000009810cc419180aa560000000018968689c760cb056c40310a64a280000000000000000008496fa000182c50a000085101a03918b6a5cc232a00018146f11b5c0e90e72637800090e25ca0000c7a4891c1c5bf13a49d392ca0001a1800000006c70000000000000000005811e187151b2c00021120000d1e000000000000000002450000000000000003e41f2c0000000000000000008c865880008ac924491723726eb0f4e00000000000b5811fa138125000023d87c8000141096f80002821da40321de06b2800041a04f808a00000001f766ab1b4295980000110e0000014b200005ee0001f160a78000000077c93924e85050cfc966214042c190c70a13dc0641ce0000082672000000000ab0000000058f8000473222c3151136136981e042000000013a81e6817482315ba26f8eac7039d3c1de90a000005109db0ed467980004c012f45d181640001f580b90ce600005be75480006a88000201a0f41e405465340000000000009099a40000000096846e9888000000206e49d00009ee80008d8894c000000027d95102b194ec5670000292a45458385a60001a0601d1dba4dc189a43115bc0861acc1af12049e08d141ef08
  | 42 => 0xafc1228bb863f249a09b890a1980112000095a3b584e6507999e87b946895927a422da4360ae9aa0000052000015860000000193a3860001c2406f800006e1dac3c29164700975c60b809200017047bba04a72f800054d14f088fa6f0000126400026c01a2027816f04002970c848fa16d232600001e7269c5ea9b3c05c80000001f1e3d500b60000ce251412bc54b9ebe9df000000000000000f6600023445e8a1960001e963180266000117c51500000000a1800020c0987864066003244698db0145132217e11bc6aa0bb0000000036f05361f086ba1390000000275a000000024b000040580001449ab461122c20f0045e000217e5d200007998af6145a5bc00024d851208d25c8073c51ea43e1c0a3d66ec88fe10093e6334800000017520001dbe6ce854261b00000001f4a000085c0000a382141d82000022e4ec12b608f925c662840e00007cc6e71d14951a61a4c4a38a0000dc43111c4a8db8f1c1768fac4de862800002642ae9dae4cf0000612a6d219b1e5e6e627967a3a7c205310c874583f494b22dc96e814e17413140e20ba062d27b689d00008a80000742923629b9e563c926b64f503760000b220001c3c2f510f47ef9234000188e5b880005c214068e522504c4000041f800006f00000000dda4631ca60c38f6a0000000000042c88f000057406a4018952097aa614411150c854979480c8b3c00004fc02c80000001cac40480007bb059e00002268f41b7000000000001b9a0000000573266829a000000010926a58fe04e00000000190600000003e180006461c0a048a1ec8a61da22e6a6e45ce1cc21db1f6a1b7187e95e0c6a03111c09b69f00628a4f439f242865717f8035907056c89ea03c0d1a4bc15b00f390a2713875659c05b29bca5580441c969c700788d693085b39b6850c82fc934a1841731a2608099c6907961e638939e000035879f80006c0a1504680cde61aa72869b162822e1b7679b157e73b061c86600000ed82de8cd809a00000002e100000001a04477265265a25442430c6400000d0000270e5b986ae6f617503ee82ac000262a000000018799364e0800000000003b780003d31e3c00006261ce00ae98c8d10603138a3e58ba616b00005f0a202498a22259f27a678310f80d117fa7b080007499cd258495c668795a60001e6e99d0000730000092b89663f788c05d30fe800000008e21f3600008d600014d80001dd600000008f10000000000000006ce0001a80943961c86a1a6639d00008fb080a21e12d600004746950e222a1229249ba5965059246518181a3ff825406314904e107ca3651a4e134902a3fe000065b09143940a645e49d6691d84aa0a995c23511c349c30b340e411860031822885800099c09125f10e30613180e000179e0210000275027600016fe997953c2232718865019e6
  | 43 => 0x212c0000b6068d1fc40001be4000185c440201a26920d8082a0886248cca16e83a256601ec04111e467b90be83b131e7e51a164e400001fd8000701878a3bd19d21b88a0488d0d8c66d211e7aa06642b8202a8b38fc20000af4000000048e000040a0a727a2a2be1c600004be1fce5e9800000000003539fd8466272e88a88a430900003af0c9032a80fe3ee0fdc000000060e800053681f65f3a3e001d80003619db458a968285d1e1021fa5528c192c032c139606b800000010cc00000000a18d2a00004f637f00003699ee000010f20839b4a7c8800000021ce05e80003d183c27449f5e26303fc3e095080f194c69ed0ff26baa75e99e800000014443e808dc00016f299c8000000274461ea31a000177a6261d2464c1eac3bf16bc0de1e145680000868000076589a88d01a20917a6e629d86200c8960c11d8ad0443256e61601ee48c82b272f05348a38000000000000a800065b99ba000000000010e66ac8b38058a53a7559bde8f2910284c99be2461e5a7fe82040ab800091b01a43f008225ad000096100000d0171e9a0851e939800000000006f5000098a0fd200000007639dde1d01e7000021c494080009100000569000071721fe000000054e1020761800000000009a280001420000000000000000000001320000213a345910a4ce80004820000735922c0001e280000ee200026b000000007211b00000044e230975800020686e41ece9e8846c14f913a000000093da58675ba0008df971897188e4000271e8cd260e22d07660d4966601a824c25e12ae929893a0001f149d401c831308e034e9f8c7268c1c5faa6f402a061a90484c658207ce431800029a99e42c9875c38113ea0000ca000000000af27881598000000078000013fe0000000722810a80c0426000000000010fc000000092c9a9a5e19fa68bda61c000000071ba4f888217d08e70000133922823a971080e84a27c31f3e7ec26dc2d30f3e3b71b3e8fd929e711a4809a58ebe8251568214892e1b687b67c104cc04f1dce0dc099c6d300002a0108e039a57a2bb8b987fc85f44e6920c27595d600000005861c8e566a2c600027705f7069a4a80b9c28d9616000136c6a41e0093700000000000000114671d10722f90cee006037a5208b20638129c3b000000000380000236c3428f680ae2408000000000026b853300005640000013032e9f0165c7328c284a080008481338804154426121be07c988450997329ca86ac7600ac22c4984864400000ac125e000013e60221f078b98f000525120c78e063d216c47829e722d6828c19493600000d569578000000252a05180000000ad24418a4600004684fd000026c204400010aa00000dc06e8000843a72263b866226980000d5198862288d47cb983268f25a47161fda0b708ec000154a000216264c80004fd8
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc3f74d516244013878e9aa2c488263171cf54589100043f43aa8b12200087c87551624400187ee8aa2c4880270f1d154589101be2e39aa8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f54dcd62440018baa9b9ac4880021fe1573589100143e42ae6b1220008bf845cd624401317908b9ac4880023be0973589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100066639ee4b122000cb474dc5624412f968e918ac488007351ce315891000c7a43a62b122096cb4744c562440011df0eb10c488002b320d62189100247a432e3a1220038f8865c342440111dd053b484880021fe1576909100143e42aed2122009aac8458a424406759906b1484880021fe1576509100143e42aeca1220008df835d942440031b906bb284880023de05765091004c7643ac4a122009aac84589424406359906b1284880270f19175109100061ebaec821220048f4865c442440071f10cb8084880272e191701091004e1e322eba0a2000c3d75d934144013c68c8aa482880271d1d9545051004f1a322a8a0a204b8ed87d8b2144013878c8bae80880030f5d764d011000c6f41ced20220008dd839da40440091eb033b480880278e191549011000798aa4832022004af08650640440017330632280880271e1d9545011004f1c322a8a022003cf07690540440135e10ca0a808800f3c1d9415011004f5832282a022000f315450540440091e9033b080880021fe1576481100143e42aec90220008bf845d9204401317908bb2408800237e0d764811000c6e41aec9022000ccc73d8920440091ed0db8a40880135c0417584110026d9202e90822009c767655210440011df04baac8080223b209755901001c7a40aeab20203ba3d8595164040091790eaa2c8080123e20173590100051ec2e86b202000aad82d0d64040091790ea1ac8080268f21376550100051fc22ecaa02000a6f825d954040794d904bb2a8080ee9d20576550100151f43ac8aa02002a3c875915404077c68e2b22a8080ef8dc4164550101df1d082c8aa0203be39105915404001c6ac9b8aa80800a1fa1f75588100043ec26eab10208c87e871d562040010fd0faa2c40800a1f21f54588100043f43aa8b10200087c8755162040010ff0ab9ac40800a1f2157358810016363aca4b1020048ec8754962040091d90e992c4080270f99175d08100061ebaac9a102009c9e645cf420400193ac8b9e84080021fe1576908100143e42aed210200087f855d942040050f90abb2840800e3d20576508100245e43ac8a1020048ec8758942040050fd0bbb280080021f61776500100043fc2aed900200287c855db20040091d904bb640080123b60b76480100063baa6ec8802004eb24059110040018eeecaa220080038d5915444010
  | 1 => 0xae639ac50812eb9a047358a1000572c08e6b142000e4f5394d62840011dd0fa1ac5080023b61f4358a100053742e86b142000a6d85d0d62840975cd0321ac508002b96064358a100053742886b142000a6d8510d62840095d50021ac508002ba6004358a1000537c2ae2b142000a6c855c5628400155f08b8ac508002ab2117158a1000567c1ae2b142000acc835c562840471df0e98ac50807e3b21d3158a1000537c2a62b142000a6c854c562840050fd0abb685080021fe1975d0a101e637312eba14200087f8759742840010fb0eb2e8508003179cd65d0a100062f32ae7a142000c5d655cf428412b99cc4b9e85080123be1d62d0a10006373aac5a142000c6d7558b428400199ce6b168508003335cd62d0a1000674b12e1a1420048ec8758942840979c8e2b1285080031d9977150a100143f42aec214200087f865d442840118dcc4ba885080021fe1d6510a100043ec3aca2142000c6e7558842840018daeab1085080233a9897010a100043fc32eba0c200087f8759741840018dceb31683080031b5d662d0610006373aac5a0c2000c6d7558b41840119d4c4b8643080021f61b754861046e37316ea90c208d87e8759521841330f90eb2a43080031bdd56248610006363aac490c2000ce962dc1218403d0ff0cbae81080321fe1d65d0210006373acc5a042000c6d7598b40840018dceab1681080031b5d562d02100053dc32a92042009c79765524084013c74c8aa481080029ee19545021004f1c322a8a04201387d86dd520840e38dcc5baa41080321f21d65482100062e39aca9042000c5e65dcd20840018bacbb9a41081bf3398b734821000637baac49042000c6c75589208400199ee6b124108003331cd62482100145fc3aa9b22200087f855cf64440050f90ab9ec8880023be0973d911004476412e7b222000a3d8510f64440010ff0ab96c88800a1f21572d91100046fc1ae5b2220018dc835cb6444013878c8bacc8880030f5d764991100046fc1aeab2220018dc835d564440011df04baac8880223b20975591100047bc0aeab22200087f855cd64440050f90ab9ac8880022fe11735911000477c12e6b2220088ec825cd64440011f700b9ac88800a1fa1771591100043ec2ee2b2220008bf87590644400147b093b2a8880028fe1176551100052fc1aecaa22037a5c835d954440014df04bb2a8880f29b20976551100053bc0aecaa22009a3e86d91544400547d0fb22a88800a8f21f64551100051f430c8aa220048f581dd762440015cb02196c488003b1cc931d89100043ec26eab1220008bf845d5624401317908baac48800237e0d755891000c6e41aeab122000c3f75dd16244001878ebba2c4880030fe1774589100061e42ee8b122000c3f751d16244001878ea3a2c4880021fa1f54589100143e43ea8b122000
  | 2 => 0xd71c83100062f31eea90620008dd86dcd20c40df1bd0eb1a418827a3721d63483100062fbaac69062000c5c7558d20c40018d8eab1241880031798d75083100062f3aac61062000c5d7558c20c400187ee93a2cb080129ea0274596104ed3cc04e8b2c2000a77815d165840a74e902ba2cb0800317dce73596100043f43e86b2c200087d87d0d65840014dd05a1acb080029b60b435961029d3b40c86b2c2000a758190d65840010fd0e21acb080021f61c43596100043f43e64b2c200087d87cc965840a74ed02192cb080029d60432596104e53dc02e2b2c209b87f874c565841350f90e98acb080029be0931596100053641262b2c205ac6e72d5364840018dea8b96c9080028f61265992100263d384cb324200c87f87596648400147f08b2cc9080131e9c165992100271d202cb3242000a3d849d5648400147f08baac90800a1fa1773592100043ec2ee6b2420088ee82dcd64840011db05b9ac9080122f21d43592100143f42ee4b24200087d85dc9648400147b093b2a9080f29ba0a765521000536c14ecaa42000a3f845d954840010ff08bb2a9080030fe1176552100063bc0aecaa4200087e871d954840794dd043b2a9080029b60876552100143f43ec8aa4203ca6e82d9154840014db05b22a90800a1fa1d64552100043ec3ac8aa42000c75761c554840010ff08baec50800a1fe1f54d8a100043ec3ea9b14200087f8755362840010fb0eaa6c5080029b6126598a1002733884cb3142004e651099662840014df08b2cc5080029ba166498a1000536c2cc93142004aea8099262840014df0daa4c5080029b61b5498a1000537c32a93142000a6d865526284001c5ea92a4c508002b9e055498a1028d7240aa93142000e2f845526284079c5ce8aa4c5080f38b5d15498a1000733c0aa93142000e64815526284001c9ea729cc5080223ba1f4398a1000476c3e873142000a6e85d0e62840014db0ba1cc508146b9a064398a1000572c0c873142000a6e8510e62840014db0a21cc50808e3be1d3198a100447643a633142000a6f854c662840014d90a98cc5080123ba1f5258a100247643aa4b1420048ee87cc962840014dd0b992c5080029b6173258a100247643a64b142001ccc734c962840015cb02192c5080029b6126558a1000537c22cab142000a6e8599162840014db0b322c508012baa026458a1000537c36a8b142000a6d86d5162840b58deedaa2c5080029be195458a1000536c32a8b14203cc6f76551628400159d073aac508002b360e7558a100053742ce8b142000a6d859d1628400159d073a2c508002b360e7458a1002575404e8b142000ae7815d162840014dd0a3a2c5080029b6147458a1000536c2ca8b142000e2f549516284001c5f08aa2c5080029ba145458a100053742ce6b142000a6d859cd628400199
  | 3 => 0xcaa0403ca6c825d954080798d8e4bb2a8100029de0576550201dd3a40aecaa0405a87f845d9540800187f08bb2a8100f31b20976550200063bc0aecaa04000c74815d954080798de40bb2a81000a1fa1d64550201e43ec3ac8aa04000a6d86dc954080018daedb92a8100021fe1573584200143e42ae6b0840a08ef825cd61080111d904b9ac2100123d21d31584200143f42aeda08400087f865d741080010ff0eb2e82100021f61d65d04200143f42aec20840038ed825d841080071f300bb082100021fe1975104200043fc3aca208400087d8759441080018bce6b2882100231b9c965104200263d382ca2084000c5e655cc41080018bacab9882100031b995721042000636b2ae42084000c7a655c041080018f2cab80821000a1fa1576d00200f43fc32eba00401087f8759740080010fb0eb2e80100031b1d776480200066639eec9004000c6f85dd920080018d90bbb240100031bd53764802002675286ec9004000ce950dd920080018deedbaa40100029ba1d65480202bd3643aca9004000a6f845952008001c98e6b2a40100131bdc1654802004735b82ca900400096c8755120080014db0caa240100031bdd9544802000667bb6e69004000e4d65dcd20080050fd0bb92c9880021f617725931000c6f41ee4b2620008dd83dc964c400147f08bb2a98800317dd67558f1000567414eab1e2000acd829d563c40075ad03ba2c788036b56077458f100052f42ce8b1e2000a5d859d163c400159d053a2c788002b360a7458f1001d6b40ce8b1e2054ad5819d163c40015b700ba2c78827eb62017458f100052f428e8b1e2000a5d851d163c400193ae83a2c7880ee976165458f100070faa4a8b1e2000e1f8455163c407d4bd0a2a2c78800297a177258f100052ec2ee4b1e2000a5e859c963c40014bb0b392c78800eb5a047258f1006d6ac08e4b1e2000a5f855c163c40014b90ab82c788002a7e117058f100054e422e0b1e2000acf825c163c400159904b82c788136b5e057058f100072da84a0b1e2000ace8214163c400159b04282c7880123d2057558b1001c7743ea4b162000c6f75d4962c40039ace698ac58800637a0d76d0b100062f31aeba1620008df865cf42c40011bf0eb1e85880023761d63d0b100062f3aac7a162000c5d7558f42c40071d90eb1285880031798d7510b100062f3aac62162000c5d7558c42c40079ace2b1885880033558d7110b1004f1a322a8a0e2000c5e635d740c40018bceab1e8188003175d563d031001e6a38ac6a062000cd563dc540c40018bcc6ba8818805e37e19731031006c6fc3ac62062000c5e7558c40c40018baeab18818800f359c563103100066731ce42062000ccd639c840c400199cc6b9081880033358d72103100066b31ae22062000cd5635c440c40079ace2b1e41880033558
  | 4 => 0x1480018becab9882900031719573105200046fc3ec620a40008dd87d8c41480018bcebb188290003175d7631052037e67396c620a4000c6f655c841480018d8cab9082900032bd91721052000667b1ae420a4000ccc635c841480019cae5b0882900031ed9670105200063c32ce020a4000cdb639c041480019b0c738082900031ed9570105200063c32ae020a4000cbb645c041480019b6c6b8082900033618d701052000679b0ae020a4003cf0615c04148001c98c7b2c42900033318d748852000536432a910a408ee4c63552214804759d0db1c42900021fa1b75485200062e31eea90a40a587e87d9521480018beebb1a4290003171d763485200063632cec10a4000e4c63d942148001998c6ba042900029b219540852000696ba2a810a4085e4c63550214803f99f0cb9842901827321973085200fe66432e610a401f8cc865cc2148001a9ecab984290003531957308520006a7aa2e610a4000d4d545cc214801199ec0b98429002372d817308520004e7c3ec610a409eace86d8c21481490f90cbae80900031718d75d012038c3fc3ecba02400087d87d9740480018bcebb1e8090003175d763d01200066631ae5a0240048ed829da40480010ff0abb2809000a1f21576501200046fc1aeca0240018dc835d940480018d8cbb92809000a1f216761012000c6e41cec20240048ec829d840480310f90cba880900031718d75101200043fc3eca202401387d87d9440480018bce7b2880901c71b9cb65101200bc6e432e62024000c5f655cc40480018b8cab98809000237e1f63101200946ec3ec62024000c5e75d8c40480018baebb1880901bf339cb631012000637b2ae42024000c6c655c8404800199ec6b9080900033318d72101200063bb2ce22024000c74659c440480019aec738880900033518e71101200063bb2ae22024000c74655c440480019aec6b8880900033518d71101200071db2a802024000d997350040480e38dcedb2c40901c79ad83658812000536432a9102406fcce76d8e20480b58de41ba2ca100030fdd2745942051d37c12e8b284008a6c825d165080014ef02ba2ca100029d20574594200062fb9ce6b2840a2a6f825cd65080114d904b9aca100021fa1f43594200043ec3e86b284008a6e82d0d65080014db05a1aca100029da0643594200053ac0c86b28400087e8710d65080010fb0e21aca100229ba0a715942050d36c14e2b284000a5e831c565080014bb0638aca100021fe1d31594200043e43a62b284000a6f824c565080114d90498aca100f28f612755902004476412eab2040008f7815d564080071e902baac81016a8fe1175590200143f42ee6b20400087d85dcd64080131db05b9ac810022aba0b43590200245e43a86b20400287e85dc564080010fb0bb8ac81000a1f61376550200051fc22e
  | 5 => 0x297a1464d8d200052ec28c9b1a4000a5e86d5363480014b90daa6c690263179db54d8d200052f432a9b1a4000a5c86553634806f8bcecaa6c69004ab3a1b72d8d200072632ca5b1a4000c5d751d763480df59d043aec690002b360875d8d200052f42ce9b1a4000a5d859d363480015af02ba6c690002b520574d8d200052f428e9b1a4000a5d851d363480df59d043a6c690002b360874d8d2053d2ec2ca9b1a4000e1f549536348001c3f08aa6c69029a97a1454d8d202c56d406e5b1a406fe4e52d4b63480014bd0bb8ec6900029761771d8d2037d67416e3b1a4000acd82dc763480011bd0e28ec6900023761c51d8d200072da84a1b1a406face82143634800159b04286c69000a1f21676d092000c6e41ceda12400087c865d742480018b8c6bae84900021fe1f65d09200043ec3ecba124000c5e73d9742480011b90cb9e849000317d9573d09200062e32ae7a1240008df87d8f42480011bb0fb1e8490003179d763d09200062ebaec7a124000c6c659da4248001c98c7b2c84900029b21954909204a72631aa9212409eace86d8e4248001c98c7b2a8490003a318f645092000717b28c8a124000a6c8655142480138d8ecaa284900278b191545092049f2631aa8a124031ace86d8d42480050fd0bb9ec2900021f61773d852004477416e7b0a404b8ed8790b61480975c902a16c290003179cf65985200062f398cb30a4000c5f655ce61480018b8cab9cc290003179d763985200062ebaec730a4000c5e7518e61480018baea31cc29000a1fa1b75585200043f43ecab0a4000c5c73d9561480010fd0e32ac290003171cc65585200061fb2ee8b0a4000c3c65dd1614800187eca3a2c2900030f194745852000c6f436e6b0a4000c5f65dcd61480018b8cbb9ac29000237a1f63585200062fbaec6b0a4000c5c75d8d614800193ee9b1ac290003271d363585200046f438c6b0a4000c5f7518d61480018b8ea31ac29000327dd063585200064e3a0c6b0a4000ec62118c61480011ef0eb08c290002ad21161185200143e42ceda0a400087f855db41480050f90abb6829000237e0d76d052000c6e41aeda0a400087c865d741480018b8c6bae82900021fe1f65d05200043ec3ecba0a4000c5e75d8f41480018baebb1e82900033318d72d052002476c14ed20a400087f855da41480050f90abb4829000237e0d769052000c6e41aed20a400287e85dd941480010fb0bbb2829000637a0f76505200046ec1eeca0a4000c6c65dc94148001998c7b92829000a1f216761052000c6e41cec20a40038ec829d841480091f1013b082900021fe1576105200143e42aec20a40008df835d841480031b906bb082900021f21975105200062e31aea20a400087f87d9441480010fb0fb288290003179cf651052038e37396ca20a40008dc865cc4
  | 6 => 0x43f43e87b2a400087d87d0f65480e34dd05a1eca900029b60b43d95200053b40c87b2a4000a758190f65480010fd0e21eca900021f61c43d95200053b40ee5b2a4000a7581dcb65480af4f501b96ca900021fa1f32d95200043ec3e65b2a4071a6e82dc765480014db05b8eca9000297a0e71d95200052ec1ce3b2a400087f874c765480010f90e98eca900029be0931d952038d3641263b2a400087e870c365480270fb0e186ca900028fa1030d95200051ec2061b2a4071a6e820c365480014db04186ca900029da0430d95200053ac0861b2a4000c5c7518f644800147b09baec8900028f61075d91200043fc2ae7b22400287c855cf64480111d904b9ec8900021fe1571d91200143e42ae3b224000c5e73d9664480018bce632cc89000317d9573991200062e32ae73224000c5e7518e64480018baea31cc8900021fa1f65591200062e39ecab22400087e8719564480018b8e632ac89000317d9773591200062e32ee6b224000c5f7518d64480018b8ea31ac8900031dd9771591200063a32ee2b224000cd463dc564480018eeca38ac8900031d19471591200066a318e2b2240008df835d564480031b906baac8900023be0975591200047bc0aeab2240038f4815d564481318b8e7aa2c8900fb1d1c754591200062fbaee6b224000c5c75dcd64480018bea9b9ac8900021fe1573591200143e42ae6b2240008f7815cd64480071e902b9ac89000317dd473591200062e3a8e6b224000c6c75dc964480018eeebb8ac8900031d1d771591200066bb9ee2b224000cd473dc564480018eea9b8ac8900031ddd471591200063a3a8e2b224000cb7741c564480019aee638ac890003351cc715912009c3ec3eca3224000a3d84d94644800147b08328c8900022fe1d64191200055a40ac83224000c5e7518c64480018baea318c8900de97a0f76551200052ec1eecaa2400087e869d954480018b8c73b2a8900028f61276551200043ec24ecaa24000c3d849d9544800147f08bb2a89000297e0d76551201bd2e41aecaa24000a6f825d954480014ef02bb2a8900ee9d20576551200062e318ecaa24000c6d821d954480018dc643b2a8900031b4c876551200143e43ec8aa2400087f8759154480050f90eb22a89000297e0d64551201bd2e41ac8aa24000a778159154480774e902b22a8900029ba1a7255120006363b4e4aa2406ab2d849c954480014d90cb92a8900031b1d9725512037597c22e4aa24000b64815c954480018bcedb2ec6900029761365d8d200046ec3ccbb1a4000a5e8599763480011bf0eb2ec69000297a1865d8d200062f3b0cbb1a4000a5d841976348001c9b0432ec6900023761e64d8d200052f42cc9b1a4000a5d8599363480011bf0eb26c69000297e1564d8d200052e42ac9b1a4000ad78159363480015a902b26c69
  | 7 => 0xe7824c561100015c90498ac220012bc201315844004d5b424eab088000ab5849d561100015ad063aac220002b560c75584400053bc2ae6b088000a74855cd611000156f08b9ac220026ad211735844000573c12e6b088000ae4825cd61100015e700b9ac220012bc20173584400072ba9ca6b088000a77855c961100014e90ab92c220026ad21172584400056b418e4b088000ad5831c9611001356d08292c220002ad610525844002579400a4b088000af18014961100014ed0b992c2200029d61732584400047b43864b0880008f5870c961100050f90bbb242200021fe1576484400143e42aec908800087d86dd521100018bcc7baa42202371b98b75484404663b30eea908800087e8759521100010f90eb2a422000317dd563484400062e3aac69088000c9f7458d2110013938e8b1a42200031bdd56248440006363aac49088000caf7458921100018eeeab0a42200031d1d561484400065bba2c290880018de835d821100018bce6b28422000237e1973084400062f32ae61088000c5d655cc211001199cc4b98422000f3598573084400046fc3ac610880008dd8758c211000199ce6b104220003335cd62084400066b39ac21088000cd5735842110009974a1bb280200032e54376500400264fb82c6a008009e9b7058d4010009d3440b1a80200f28f61654593200445e43aa8b264009a3c84dd954c80794dd05bb2a9900028fe1176553200151f43ac8aa64002a3c8759154c80798d8ecb92a9902a2cbe117255320005b240ae4aa64009e2e6455142c80050fd0fbaac3902371b1cb75587200043ec26eab0e40048ec825d561c81338d8e43aac3900021fa1f54587200143e43ea8b0e400087e8755161c80010f90eaa2c3900021fe1573587200143e42ae6b0e40048ec825cd61c80a31d90ea12c390146b920542587200447a43a62b0e400087f855da41c80050f90abb483900123b20976907200043fc2aeca0e400287c855d941c80091d904bb283900270f99175d03200061ebaac9a064000aad82d0d64880091790ea1ac91000a1fa1771592200043ec2ee2b244000a3d849d954880774ed033b2a9100029d60676552200051fc22ecaa44000c6d76dc954880018dcec392a9100272799173d0a200064eb22e7a14404bccd625ce61880010ff0ab9ac31000a1f21573586200056ac18a2b0c40048f4874c561880014e90a98ac3100031d1d561486200043ec3cc7b2a400087f8758f65480014ed0231eca900029d60463d95200062eba0c7b2a4000e4d8218f6548001cad0231eca900039560463d952009d37436e5b2a4000b6681dcb6548001c98c7196ca900039318d32d95200061eba0e9b2a4071a6e821d365480014db043a6ca90003175cc73d952038d37410e7b2a4000a6d821cf65480014ed0239eca900029d60473d95200
  | 8 => 0xea39ac52000b1b1d65258a400247643aa4b148001ccc738c962900091d90e992c520007331cd3258a4019d6641ac5214803ce2e62551429006359906b1285200034e5537050a400043fc2ae6b0c800287c855cd61900011df04b9ac3200223b20973586400247a43a62b0c8000e35545864190001a72a8b84832000237e0d76c864000c6e41aed90c8023acc8358a21900010ff0abb2432000a1f21576486400046fc1aec90c80018dc835d9219001199cc4b98432007eb320d620864000666b9ac410c8000c6d75d4b62500011df0eb10c4a00029b21562189400063bc0aebb0a800087d87d5361500510ff0eaa6c2a000a1fa1773d85400043ec2ee7b0a80088ee82dcf61500011db05b9ec2a00031d5d451d85400056ac18a3b0a80018f7874c761500014e90a98ec2a0002b920931d854001e6a30ae730a8000cd573d8661500011ef0eb08c2a00ef8d18554505400069caa0e0a0a80008df835db21500031b906bb642a000a1fa1676885400043ec2ced10a800287e859d921500010fb0b3b242a000f3518573085400066ab9ec210a8009d3a705524050013c76c0aa480a000317dce73594400043f43e64b28800087d87cc965100014ed02192ca200029d60432594400052f418e2b288000a5d831c565100010ff0e98aca200021f21d315944000537c1262b288000a6c824c565100018beeb3aac62000297a177258c400052ec2ee4b188000ad6811c963100015ab02392c620026a7a105258c400054ec20a4b188004ada8014963100015b300292c62000297e157158c400052e42ae2b1880aaa9f845c5631001353908b8ac620002b3e097158c4000566412e2b1880a9adb805c563100095b100b8ac620026a7a135158c400054ec26a2b1880008de8714563100011bb0e28ac62000393d4e539884000567418a33108000acd8314662100011df0e98cc4200223b21d319884000537c2a633108000a6c854c662100091dd0fa92c4200123b21d52588400247743e64b108000a6e85cc962100014db0b992c4200123b21d32588400057340864b108000ae5810c962100014dd0b39ac4200029b616735884000573408e6b108000ae5811cd6210001c9ea729ac4200029be1571588400053642ae2b108009aac845c5621000159d0638ac420002b360c715884000567418a2b108000acd8314562100011df0e98ac4200023b21d315884000537c2a62b108000a6c854c56210001caea729cc2200029da1732984400053ac2e6530880038f6870ca61100011eb0e194c2200021fe1573584400143e42ae6b0880098bc845cd61100011df04b9ac2200223b20973584400247b43ea2b088009ab684d4561100091e90ea8ac220002b5a0c51584400056ac18a2b0880048f687cc561100091e90e98ac2200029de1531584400053a42a62b088000a
  | 9 => 0x7558c2159566c14eab1842b1acf825d5630841159904baac610ac3331cb7458c2101d6b40ee8b18421fad581dd163084014bd0b3a2c610802976167458c2104567414e8b1842afacd829d1630855d59f04ba2c610822b32097458c214ae66392e8b184200a5e851d163084014bb0a3a2c610ab793dcb5458c212d726396a8b18423ee5621d5163084b5caa43aa2c61096b93c835458c211dd2ec2ca8b184200e1f54951630840159f04aa2c610822b32095458c210056bc0aa8b184203ad4815516308401c3f08aa2c61080393e095458c211e726412a8b184285e4f725516308479c98e4aa2c61080395e055458c211df2a40aa8b18423be56215516308479caa42aa2c6108f393c815458c211f52f428a8b184208acc82dc1630841159d05382c61097eb360a7058c2137e66394e0b184200a5f855c163084014b90ab82c610ab2b3e097058c2104566412e0b184200a5e851c163084014bb0a382c610802a7a107058c210054ec20e0b184208ace821c1630843f59b04382c610a7b331c87058c2101d6b408e0b18421fad5811c1630841159d05282c610802b360a5058c2101d6b40ca0b184200ad581941630841159d04282c610802b36085058c210043fc2ae6b00420287c855cd60084071f10ea82c0108268fa12735974055d1ec24e6b2e8000c5f739cd65d00014dd0539acba00029b60a73597400053b40ce6b2e8000a75819cd65d00014ef02b92cba00029d205725974000636b90e4b2e800087e87cc965d00010fb0f992cba00268fa1032597400051ec2064b2e8000a76810c965d00014eb02192cba00029be09715974000536412e2b2e8000a5e831c565d00014bb0638acba00268fa1331597400051ec2662b2e800087f874c565d00010f90e98acba00029be0931597400053641262b2e8082a3f845c165d00014bf06b82cba00029720d705974000537c12e0b2e8000a6c825c165d00014ef02b82cba00029d20570597400f43f43860b2e800087d870c165d001347d08182cba00028f61030597400053741060b2e8000a6d820c165d00014ed02182cba00029d60430597400047bc0aeab1680038f4815d562d00131dd0f992c5a0002b96043258b4000477c12eab0e80088ec825d561d00010ff0ab9ac3a000a1f215735874000477c12e6b0e80088ec825cd61d00050f90bbb243a00021fe1576487400143e42aec90e800087d86dd521d00010fd0eb2a43a00021f21d654874004e1f3a2ca10e8000c5e7359421d000187acaba043a00031799573087400062eb2ae610e80008df835d562900031b906baac5200021fa1f5458a404c62e39ea8b14803087c87551629006f8b8e6aa2c52000317dd77358a400062e3aee6b148000c5f54dcd62900018baa9b9ac5200021fe157358a400143e42ae6b148000c5f751cd62900018b8
  | 10 => 0xb2a428ca6d821cf65485194ed0239eca90a369d60473d95210043f43e87b2a420087d87d0f654851b4dd05a1eca908029b60b43d95214653b40c87b2a4200a758190f65484010fd0e21eca908021f61c43d95214643f43e65b2a420087d87ccb654851bc9864996ca90a6a1fe1d31d952146c3e43a63b2a4200a6f824c7654851b4d90498eca90a33950c531d952146d37416e1b2a428ca6d82dc3654851b4dd05386ca908029b60a70d95210043f43861b2a420087d870c3654840147d08186ca908028f61030d952146d3741061b2a4200a6d820c365485194ed02186ca908029d60430d95210051ec26ebb224200a3d841d764484010ff0ab9ec89080a1f21573d912150477c12e7b224200aad82d0f644840317f0ea1ec8908021fe1570d91210143e42ae1b224200c5e73d9664484018bce632cc89080317d9573991210062e32ae73224200c9f645ce6448413938c8b9cc8908021fa1f65591210043f438cab2242008ef825d564484011ef02baac8908021fe1573591210143e42ae6b2242008ef825cd64484011f700b9ac8908123e2017359121006363aee4b224200c7475dc564484450fb0fb28c8908028f61365191210051ec20ca32242a5c6d72194644840117f0eb20c8908021fa1a76551210051ec24ecaa2420087d849d9544840187b093b2a8908028fe11765512100537c12ecaa24200a77815d954484018ec623b2a8908031d4c476551210063b908ecaa24200c6e211d954484018d8423b2a8908031d08476551210143e43ec8aa2420087f8759154484050f90eb22a890a961f21975d09214643fc3ecba12420087d87d9742484018bce7b2e849080317d9573d09210062e32ae7a124200c9f645cf4248413938c8b9e84908031b196769092100536432a92124200c7465dc542485198d8edb2a84908038bd94645092100536432a8a124209c6c765514248413c58c8aa28490802f160c71509214cc3e432eba0a428d87f87d9741484010fb0fb2e82908021fe1576505210143e42aeca0a4200c6c65dc941484039ace698ec09080a1fa1b75581214643e436eab02420087e87d9560484018b8e7b2ac0908021fa1c65581210062e398cab024200c3f65dd16048401878cbba2c0908030fd9474581210061e328e8b024200c5f65dcd60484018b8cbb9ac0908023ee1d601812104476412eab2042038f4815d5640847747b0b2a2c81080e2f21d545902104476412e6b204295ccc325cd640841347909bb2a8108028fe1176550211e536412ecaa0423cc6c725d954084774e902bb2a81080a8fa1d64550210151e43ac8aa0423ce2c725915408401c5e64b22a8108f38b0c964550211df1a38ac8aa0423be2f215915408477c5a42b22a8108f38bc81645502100716b26e4aa04200e3564dc554084018beeb3aac610822b3a0a
  | 11 => 0x1041355d08182c420802ab610305884101d7340860b108200ae5810c16210401d8a62182c4208123e20175980410247c402e7300820087f855ca60104050f90ab94c02080237e0d729804100c6e41ae530082048f8805ca6010401cb6a729cc0208029ee1572980410053c42ae53008200adb835ca60104015b106b94c0208029ea1732980410053cc2e653008203af2810ca60104015e302194c02080e3ea1f505804104d5d426a0b0082038f88754160104075e102a82c020802baa08505804100574c10a0b0082038fa87cc160104075e503982c020803b44c6305804101c7c43a60b008200a7a850c160104014f30a182c020826aea1030580410057541060b008200ae9820c160104075e502182c020803b44c4305804104d5d424eab008200ab9849d560104015e702baac02080ebc205755804100575410eab008200ae9821d560104075e50339ac020802bc60673580410055dc22e6b008209ab8845cd60104014f50a39ac0208029e614735804104d5d420e6b008200ab9841cd60104015d50439ac020802ba608735804101d79408e6b008200af1811cd6010401cb6a729ac02080ebca06535804100578c0ca6b008209aba8414d60104015730829ac02080ebca04535804100578c08a6b008200a7b855c960104014f10ab92c020826ae21172580410056dc1ae4b008200ad8835c960104075e102b92c0208029ea1472580410053cc28e4b008200af38154960104075e102a92c0208029ea1732580410053cc2e64b008209aba84cc9601040157309992c02080ebca07325804100578c0e64b008203af2810c960104015e302192c0208039ce1531580410073842a62b008296af3844c5601052d5e30898ac020a5b9cd5131580414b738aa262b008203af3834c56010407da70698ac020803b4dcd31580410076839a62b008200ed2534c56010401da2a698ac020a5bb490d31580414b768a1a62b008200ee3824c56010401dc10498ac020803b4cc931580410076899262b00820287e85dcd64c84010fb0bb9ac9908223ba0b73593210051fc22ecaa64231ace83dd942c8413c58c8aa2859080237e0d755832100c6e41aeab0642038ec825d560c85318b8e7aa2c1908df171cd545832100c6f43ee6b064200c5f54dcd60c84018baa9b9ac1908c7331cd425832100572c0864b24420287e85dc164884010fb0bb82c9108028fe117655221006373b0e4aa4420087f845d660884098de40bacc1108131b48175982210143fc3ea9304420087d87d5260884010ff0eaa4c1108021f61d54982210061fba2a8b044209c3c7455160884010fb0f31eca908028fa1263d95210051ec24c7b2a420087f8758f654851b4e90c98eca908039518d31d95210061eba0e9b2a428da6e821d365485194db043a6ca90803175cc73d952146d37410e7
  | 12 => 0x8021fa1f5458a411843e43aa8b14820087f855cd62904050f90ab9ac5208021f61f54982412d637396a93048209c7671d52609043d0ff0eaa4c1208f31b9c9549824104e3b38aa93048200c6f545ca60904018daa8b94c1208021fe1573582410143e42ae6b0482008ef825cd60904111d904b9ac120826cd21071551410053742e65b128200ae5810cb62504011df0eb10c4a08029b21562189411e716312a8a12823bd3471551425040157308186c0a0802bc60430d81410047dc3ac03028209c7571d5060504010ff0ab90c0a080a1f21572181410062fb9ce6b288203a76819cd651056d4eb0339aca20ad69de05725944101d3a40ae4b28820087e87cc965104010fb0f992ca2080e9da0432594410053ac0864b2882b4a77815c165104074e902b82ca208029ba08705944100536c10e0b28820087e870c165104010fb0e182ca208268fa1030594410051ec2060b288200a6e820c165104014db04182ca2080e9da0430594410053ac0860b288200c5f759d563104014bd0bb92c620802976177258c4101d6b408e4b188227ad5811c9631056753f08b82c620826a72117058c410052f428e0b188200a5d851c1631041353d08382c62089ea76107058c4100567410e0b188200acd821c163104075ad02382c62089eb56047058c4100567410a0b188200acd821416310401c9ea729cc4208223ba1c509884100476c38a131082088ee870c262104011db0e184c4208029ba14309884100536c28613108209aae840c2621040155b08184c42080eb9a04309884100572c086131082038ee87d4962104071d90ea92c42080e3ba1f32588410053742e64b108200a6d85cc962104075cd03992c42080e3b21d325884101d7340864b108201cd6734c56210401d8e6498ac420803b14c9315884100573c0aeab108203ae4815d562104014dd0b39ac4208029b616735884104d57424e6b108200aad849cd62104075cd0339ac420802b9606735884101d73408e6b108200ae5811cd6210401c9ea729ac42080eb9a06535884100572c0ca6b108209aae8414d621040155b0829ac42080eb9a04535884100572c08a6b108200ce7874c562104019c90e98ac42080399e1531588410073242a62b108296e67544c5621052dccaa898ac42080eb9e0d315884101f63c1a62b108200ec6734c56210401d8ae698ac420803b194d315884100762a9a62b108296ec6434c5621052dd8a8698ac4208029be1570588410053642ae0b108209aac845c1621040159f06b82c420802b320d705884101d7240ae0b108200a6e851c162104014db0a382c420826aba13505884100556c26a0b1082008ee8714162104011db0e282c42080eb9a07305884100572c0e60b108200ec5318c162104011dd0e182c4208023b61c30588410053742860b108200a6d850c162
  | 13 => 0x52f428e0b1e8400a5d851c163d081353d08382c7a10d6a76107058f424ad67410e0b1e8400acd821c163d08015ad02382c7a1002b56047058f424ad67410a0b1e8400acd8214163d08010ff0ab9ac3a100a1f215735874200c6f41ee0b0e84008dd83dc161d08050fd0bb8ac1a10021f617715834204d96426e4aa4840287e87dd561908010fd0faa2c3210a21f21d54586420043fc2ae6b0c840287c855cd61908111d904b9ac3210223d21d315864204e37396a93048409c6e7255260908050fd0fbaac1210021fa1f54582420c43e43aa8b04840087f855cd60908050f90ab9ac1210223b20973582420163c3aca0b0484088f88754160908798daec392a8a1026cb21072551420143f42ee7b0a840087d85dcf61508015ab0628ec2a10063de1d31d85420053a42a63b0a84008df835c361508031b906b86c2a10023de1d61185420053a42ac230a840087f855c760508050f90ab8ec0a10023ee1d601814202637902ea3028404c6d205d460508010fb0faa0c0a10271b5cb54181420f43fc3aa83028400c5f739cd65108114dd0539aca212ea9b60a73594425cd37c12e2b288408a6c825c565108014bd0638aca210029760c715944204d1f42662b288400a3d84cc565108010ff0e98aca210021f21d315944200537c1262b288408a6c824c565108014bf06b82ca210029720d70594425c537c12e0b288408a6c825c165108114dd04382ca210c29b60870594420043f43860b28840087d870c1651081347d08182ca210028f61030594420453741060b288400a6d820c165108014ed02182ca210029d60430594420043fc2ae6b08840287c855cd61108111e90e98ac22100237e0d755804200c6e41aeab00840287e85dc560108010fb0bb8ac0210223e21d30580420062fb9ce6b2e8200a6e829cd65d04014db0539acba08ee9da0673597410053ac0ce6b2e8200a77815c965d04774e902b92cba08031b5c872597410043f43e64b2e820087d87cc965d04774ed02192cba08029d60432597415bd1fc22e2b2e8200a6f825c565d04014d904b8acba08268fa1331597410051ec2662b2e829b87f874c565d05350f90e98acba08029be0931597410053641262b2e8200a5f835c165d04014b906b82cba08029be09705974100536412e0b2e8200a77815c165d04774e902b82cba08029ba08705974100536c10e0b2e820087e870c165d04010fb0e182cba08268fa1030597410051ec2060b2e8200a6e820c165d04014db04182cba08ee9da0430597410053ac0860b2e82098ee87cc962d04015cb02192c5a0803b1cc93158b410043fc2ae5306820287c855ca60d04011bf06b94c1a08063720d72983410046fc1aeab0682018dc835d560d04011df04baac1a08223b209755834100e6a39a62b068209b3484dc554904050fd0fbaac520
  | 14 => 0xe8298c61550014eb03318c2aa0021f61c63185540053ac08c630aa800c5d7398861550018bae6310c2aa0031b5c8621855400732108c430aa80097787584615518166f08b08c2aa002d920961185540053bc326230aa837d56734c46155001cacc6988c2aa002d920931185540e49fc22e030aa83bd70105c0615506f0fb0fb1ec0aa0df179cf63d81541e43ec3ec5b02a800a748158b60550012df04b8ec0aa0f25b20971d81540052ec18c3b02a800c7571187605500127b09b9cc0aa0031b5ca62981540053cc04c5302a8bfd3974d82605506f2bd0fb9ac0aa00347dd373581540062fb26e6b02a800d1f64dcd605500127f08b9ac0aa0025be0973581541e4b6412e6b02a800977815cd60550772e902b9ac0aa00257a1c73581540068fba0e6b02a837c5c73d8d605506f0f90eb1ac0aa0029e201635815400697ba6e4b02a800d4f73dc96055001a98e7b92c0aa0031bd93725815400697b26e4b02a800d2f741c96055001a9ee6392c0aa003531cc72581542d637b20e4b02a800d2f641c960550018dec6392c0aa0031b58c72581540043f43ec4b02a83cc6c72d8960550798d8e4b12c0aa0029d20562581540069bba6e2b02a800d5773dc56055001aa8e7b8ac0aa00359dcb7158154006b2396e2b02a800c7764dc56055001a6ec9b8ac0aa0034ddd07158154006abb98e2b02a800d54731c56055001acee438ac0aa003591c871581541f63bb20e2b02a800d37641c560550018b8e730ac0aa0031b1ca61581540052ec18c2b02a800c5c7318560550018d8e430ac0aa0031ddc461581544169dba6c0b02a800c6c7298160550792dd05b98c0aa0025b60b73181541e697424e4302a83cd2d849c860550b58dec9390c0aa0034bd92721815400637b22e4302a800d2f645c860550010fb0f310c0aa0031b5ca621815400636b90c4302a800a7980188605505927f08b88c0aa0031b5cb60181545f59cc24c0302a80087f8758060550014d904b00c0aa0031b5c96018154004bdc3ac0302a8bdb3b8458060550018bee739acba10f29ba0a735974200536c14e6b2e8400a76819cd65d08014eb0339acba12f28fe1172597420053bc0ae4b2e8400a74815c965d08010fd0f992cba10021f61f325974200537c12e2b2e843ca6c825c565d08014bd0638acba10029760c71597420043fc3a62b2e840087c874c565d08014df0498acba10f29b209315974200537c12e0b2e843ca6c825c165d08794dd04382cba10029b60870597420043f43860b2e840087d870c165d081347d08182cba10028f61030597421e53741060b2e8400a6d820c165d08014ed02182cba10029d60430597420062fbaceab1e84bba9f845c963d08014bf0ab8ac7a1002972157158f4200567c12e2b1e8495acc825c563d08011bd0e28ac7a10023761c5158f4200
  | 15 => 0x540340b00000c401c03801000800000000c03800800800000008400000000002c00000001403400000401800000c0b400001c07400c0100e400000800401000400401c0a001001400800400800001003000800001003000418004002400402c00001c00000400000000800000000c08400c00001000400400400402400800800812804c00000401400000800000805401400000402806000800411807800400803001403000800400802c00400400c00806800002000006000001800001805800800000403c00001002c00c0300800040080040f004400c0000bc00000006400000800c01003400800000000000c00000c00003001004400c07005c01400000008804002400000001805409809403c05c00000400001c07c00800004400000001001c02401c05800000c0980100100400100080240580d406c00806000c0e407c0f400007801003003c01000c0200380400000000381000180140000d000400401800800000002000000400002003800002801003400406002003c00000c01404800005804c01c04c01000001400403402401403800401002800000800400009002c0f00700d800003400000402000c0000340080000000180040040200000340140300840000000680140200480000240d00000ac6f2df0e996c4aa0df539cd32d89540e49fc22e1b12a83787f8758e6255187a5ae9b14c4aa0024fe117358954004bbc0ae6b12a83b974815cd62550012f700b9ac4aa0025e20173589545e697ba6c4b12a800d3774dc562550018eec9b8ac4aa0034dd9371589540069bba0e2b12a83ec77641c56255001a6ec838ac4aa0ef55a0c71589541deaac18e2b12a800d67621c562550018ecc438ac4aa0031d18871589541bc3ec3ec6312a837c5e73d8c62550014db05b18c4aa0025be1d621895461597c22c4312a800b648158862550794df0eb10c4aa0031be1d62189542d537c22c4312a800e2f8458862550014df06b10c4aa00399e0562189540053640ac4312a800e648158862550014c902b10c4aa0029b201621895400536c3264312a80095f835c0625506f2b906b80c4aa0031b58970189541e4b7416e7b0aa80096d82dcf615506f2ef0e98ec2aa002d920931d85540dc9ec24e1b0aa80095f835c3615506f2b906b86c2aa003175ce639855400537414c730aa800a758198e6155183a6ae9b0cc2aa0f25ba0a7098554004b6c14e130aa80087f865cd615500127f08b9ac2aa0025be0973585541e4b6412e6b0aa80097b805cd61550012f100b9ac2aa0034bdd3725855400637b26e4b0aa800d2f64dc96155001a5ee8392c2aa16b1bd90725855400697b20e4b0aa800c6e611c961550018d8c2392c2aa2df4ddd36158554006b2396c2b0aa800c5c865cc615507d8bec8b98c2aa00347d9173185540062eb9cc630aa800a6
  | 16 => 0xb762092be8a60000000017949c0001131d586188f40003fb021873e29c381007c8aa71729a8140e0c3e61c293a47864633538064e8611f2600038d8000041c20080007ab0001394ae823600019b865c75d19a88b0cc086912919e8c5e3d307507cc892544224091c7404fd3e08378a7c2152c992b486c42508d203ccca6092ef140cec6000369a04000080900000000004601c8986c36a4c21fd94902a428b0259f2800000014a9b3cf8a09508700000000000000000aec00000000006a81472cd86403e21eb3a89b304da68941e1298d7640c000020820e28a2710a08c281e52699e849d0070239030c93c5420001c680004a70000a589863c21750000c6072d4008e502e841923b9b3878e00025c0ce024c0003b58000aaa5c600000000008280001e00b641f919b000070669c000000073606f2d48000a6e2251aca09ccde6d635e945cefa6db0001d245b409d03718780007ef28100000006b118815ec5a480b10205602de35e04583006522793290164d8200033b0a000000003fc80002a61791680000b9c46d26c1638fb207a25203ec9bc4f724d07fc9f42192e4001405800c00403000000009c0540040100280bc00001001400807800800401400c03800c02c00c00801002800402003401001000405401c01800c00000001c00801800c00000003002008c03002400000809817403c10c0480180100080240f800003403005402005805400002800c0100040480000680100a001400000c0440540ac01800400001000c00001800c0040040900f81b80a802000400c02000c00400800001c0040000000a005800002c00c00000001c03c0040000180240040000000540cc02c03803402c07400001801800401402000008806803400000c00800802001801c01801001406401c0180000b40040d00000340840580080000601b400800005000000401400c03800403000001001000c03c2b000007000000804000001016400002800800003800004001006c04c00000c00800005c00003400c12400800800006c0100000180000640400140240040100000080000f800002c00000411000000406001400c00000c00c0040b805800c00000000407c00002c00800800000c0a000800c0040c80000300040c400000000c00004000001000800400c0000b000802401000406000000801c05800c0080040000a006c00400800400400801c0a400800c01400000c04004c00019804000002801000000000000400801c01c04c00002805400002802003802c05401c01400001400000402c06401000000000004400009401c06800000c00c03800800c02402801401400c01c00800c00c00c00404400404c0202380040300040040240280a000000400c05c00000002400805401804402800000000400002802400000400000000001000801802c0040
  | 17 => 0x5dc58c7573c2139048a71c2a71d9c10a7d11321b288ec6932309860c4a043174000056a5d40000c104bc00031192480000002d500005061e415d1ba41a26c42b5000003c22d12c0d14e8c20c0b906648a870338a92ec15a72203a21b4b4006329402dc63c000000172455800039a954cb6241619e06947a40002998ec024a5291f19bfcd0c2a11851134000000000037076a0f61fb106096648b0001a480d81bb4168c2079400037f0da4f4e7010000758ebe14b105038032410d068040c0004640a680001f44962668df108052020f9ce800074200008a40000c92851e600003bb0ce0000f76000000166000000013805040007330de88e44ec2c314f000048c0002f199b412285f3429cc40001c40e69afc0000001f7800057685820f1148f3886305613510185e41ec9598e7885c1c588786ba00021f80000da2cc3ee00000000001861c7c1ce626000068ca7200010802b875a6c33cc802c72a0004278c80c1a6a90f49218f3a00016c0b580005ad00015447bc26c0000000f2250c2bf216cf580d51150c3856224e2b18ed86e00f742f00007aa6fa1ac07d80004070328ea0bf0570015161c0007870fa01e451a0000e10ecc1700000000000fd00001ff10ac7380043d015181d84f10b21bac82e5c43f882880782b23210000e9039305e00001ac0000f1000064c09a0c29d581105cc1e59280c246720000cc4ba20b33e104000004350000020244820000000035a00038b1158e6c0000ac83600006a5221999c95e5b43b40a90a2275205296190b40002e990bc00040e0eb9c78e548132ba946cbde42a30299a80001273970f1000010c00007245d883d07681080b000026799fc000257000168c6f60001131ab0ab67692ff921000059e13102c43a00000fd00cd0821ed1cb92445967b228314e0d6e63c1501528a9e59628584dc1083e203380088503f133190e45123b23b80f041e619b000000038a42e0001b809b43050e388181be4c1242855c71456c40b0ee819a85408c89f400003924f81ec9ac00020e902000000026b89a486e00033a8000b4427c0bf0aa45e684827711306b48352800e1c70c15509180000004270000000c5855827f0af400031300003040005b80d984f09383d604e13540000002c21a000006c9418963c4b400036a15480001ab1fc1bdc7487083478d3400053f0d395588d28071b980004a66163ee865cdb479f1e0000041a0000af9e6c7047240000e10a4a55d0001b883de628354000000045300007048121db00015e000078140a0f80fb429a0499338a6064c04f8624dae08d02a0c345680493cb12e84e67fb35d0d90b381b71cf187c6cc7bc1a50000bb441b197937011455c0a200004305ee2da82c00000004040000fcc79a346008c8224b7212128cdea48d2470000a320cb30080000007d60000000
  | 18 => 0xc00000035a1ef40007b11928e9c3ea638000000000011834710b00002ef0491380f6606405501f87902a80050fa909632700005cc0c40000000c440007b0000000030000000004704645f700014b000050500010843f86fc3150c1c8f20001bc0000fa66711f480005925b0415000056e72708780008600001de00000000af24487680003ce008034ca680002eb9c504be05a14c83a0d021140001f8424804d064120032a2e02229cac54a38e41b8000a3c5311c8062093079038016904dc1941f29b3400000024d8d2c00080d02f1a7c0b63dd1a91f6c08e24231d191062a7c31920088d100ef2a020f897a2c538d96e42ec5010b816dc16c7b82148ce438068a17210e01a433f0480bc44988223640970b161402621c440d46f11db8f24dca58c1138984a461672d3967cbaa43a1f707c87e031b2460d800062300bc18d8ea018c0549d7067c1150e40ebcad23123c182e509c6c63298ff0b744d134d1db02686a014d83f8d5e3e722091b0a7a0cc1a108902b41173c49cd0fc87c732a9ba892684627b1ef8da225416e1d38a1027f31a200ce8e7071109efc63200040d81acbec7f322f0dd882852d18b04a049e8243bd0e20abe5d93ef0ef4fd45fa1a49870ada5f20271d040a407500015e4f9660b37b0dc8eb42f00e60154dba6f82b7971d06861a0a6123cce64f839d84a8f981ec2839098c444bc26390c81fe5c524a934889c8683be0bd500a4b000296f85b21212b59a1cd223a20d889642e22e100006383302673a29f0077c0ba0bf88ecb2a16a04f0ab410636800606bcc2259a2090af01484c605f9228f6c5912c18f34d0665834d85ec4f651f34204fc04e67e32d11290c87ae06d86348e03eb30993e487c5592f0081c70232835a868037e2de1ff995cd8414e00011b907678804b81841dc5a83aa953460661913b92fc4e41b00ec84b90944f421a15dc11c7730709014bea0681408118fc03d117683e026a00026c80000004fb1580598da46ae1908ea84ca000000000000083239f83f50aa2633da0000bb81011b60000b7a4a84301a8c3084ed0001d800000000a500000004a243296248f881e1e2863cc8c51a00e884447480425893c07301b802e0be40003562a1852400e1d22560b7c0001432f3800080607639300000004cb39e97cc4d43341b0964905e1623d298f82f43cf2f08298b8027131580a4ef600042390c4eb65480001c384c0000018a0ad0cc7710000000a8a78e000000000000007a0c50d0449d06200000007c93120ae4de81c3277a038f5a45b1b88fb4ac20d92e9000072c0000000a7497c00000000000be000000000087674d31c8d0400025b1a407a8cbc40a15380005dc00035519f4a440001ea00000002b80159ca012c6211c788b80005e20000000ac85db00021087ee20b0ad9c9496c0000671840700713
  | 19 => 0xc34b114503e8170f021405d20c5387814d0ac21a0611cdc6867233b78be081a761409000050a23e34680000284230c392947ea78235c07c0302000000115ca4c7cf00984580000e232b000000036b10000d0b206e812b04a4ae46b608d8ce851e0bd3c790f07185e622f81f4c1e86134c8ccce3037427e192448830600000000001fd0d2072800027434b800000072f0a11b14f744f234a91f88c46d01b6981cbd245d1cd028cfb03d7271925d0587653070000c00000207985490e4403c321b0bd805d1d703905822d528b1f9c25a4013890e9463413022c1fdc1e40000001dfc4560711358cb0712044155a1480f8513171137447867c00017d0df22313170570cd221615f12e41424903c980f84443a13269bf494202817a1b2c1305410001f50f5e24a33606448ca6451a89b7c7c21ac2d70b74a080c61610558e141e62b7216499215d0f406882d60e5026162800000000002d000000030e92b81e25811378418cba7a62f802048380360000104ddc2ce3c51ce00000003ef9cf80020002e100000002db00000005fa50e00000000006be000000000000021e98cc0002cf000158026251d41d04e47be00010e9a600006ed00011980001d53f68000e607190001470d8e05721985f43ee7043bb9da8a9644b0b19ff0c7637e13418c850e00040a87b87b40cf1a80900fa035514a053c0000002fc8000b322ff36c8de4b4a00005f090c3a829f0000ff400000024a0fc80003180b69c1401e2b32388efc5f67200d49b7856c2130d08e650862f642480c0c7a3a9254800035c7752411a500ee13a088913c04a19f179031c8080000ee93d4bca28c20d060ce203ec2e08a9901421b3ac91689980a0046180c4a20992fd83502ea15008200fc5ca1381ab867802412b16b8d8cef25fe11b81fcbe22331b520687580092ec0ab860210a33a00d469c80000886f0c900003d402ac66e0003d112d40000002a49db4ff022800002c823c64e1579cb002c4ff184959400024d2418000eec82931b96fc6565a61da151c00000005389740000000aa0000b9a3cc0000000dc202000000001f200000010b400020217f0000cd65fc40e005c84445915f80e0e945fd33d80687f214815500004103670000000cd084d0000ee10d641305d8e345084ab00000002246080780000dd804536a8000d3c5a13f18000f9c00000000002206470000698d5a00033c064c7b000018000000000001470000bac3231878b4ca1a5b303493205f452e3aa1204ffc6b2394800000001b000155011e5c301ea1a8f720000000d4c00055005a8000fdc10b0000000a1e32d2b9800000027a3c920180f00000e311cccbe00000000000008260b00000680000000000000081104d91e05267fd0000bdc3040002bf92d0f8826610718287a00001730ddc68e58818e13cc0000603b90f6
  | 20 => 0x2903bf0d7c8ea3a62338b00f6e4021ae1acc4686202de1a903722a32b398fcdc86273149110ca8000000087cb9e836373800082a0001241e780001e342603981281d30d90b20e9e3e432d81980000e902008140004ca350895407422f2030dbc98a7c833109d4396758000062ca740a83da857800c7390241e5cbd040b38497acf486f3075a144000000000000105c0000000000ec800016a1578fd67f03a99108e3a6351f99f48ab44aa2379830ce06ef14411d0ebc00010b84ccdb067718b822423a01c0cd000000000008494a8b58165358174004c5103fd0b100001020b0990cd720003d49d300002eb028911c50c16c0000fd00006a2000000078c23537800000005180d4065800000037d80003b022014b9c3441e0001d88b340000001be8fa001a00037304bc7725b600006f80004e119d9650c94521000000108a46809b00b46883651d1965c1ba000027939c5a266113c20745f8249000021cc9647b2f51e549be33d0fd9e8c0001de3a21b8cedc77411e9040000330000158865444641816bcecc21424c81c869820128491701c61ba3f9088ca5e37a3280fe90ae65100018c4b048253b1180827a0733459fa45ce36e37918110882e335e079cfc44ec2891c2c2a251432e094006e7f418e8480e802381a31d2c84054c1ba96ac33a31f0ef9f5427664127506d8f1830b00c0d3c3b818a3bc05183c24d001d9f340485571c90a889b67ff2e594ec3540002f68870e420003991f5c1f839d40c80b826416e00a91a836858534e99901ea00006b80008002920b4985caf87ec109092c8fe4e63530a446c423f3c691f49d600016505143a258041c873c0ac58d3fa8d6c1b452b3860000a2a021316a0608a083f1bf8738c9e78b1639a406042410160000964853065177c2d057a2ee81280645ca0be208c0001f833c9ea8c805681019998a6c6062441674fca3dc0ff1b70f8c85d19119650c486709620cc27c1050842084ae23320401aac8d678529909f8f2853
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2500a000000d00142a002005648c0e3c00031008121c10c0d0a061c1290014032700002f3ea9a8000013806600b00004db091edc00000013002ee8dad0200000222c300000000000000210000000440171d4631639206400d09020000002000000000080061448106000124d93205621895400619e1c815886255001a469320562189540069164c8158862550012649161932189540049a241864c862550014649158970189540051a241625c0625500184d73a0a6318554004992498118c61550016259408462185540059164c211886155001464925c461d81540051a241631c960550018647220562581540041766073185605500184d831c8615815400591657324c5621040186487215315884100589650854c56210401645959cd3158841005a1652734c562104018c5874c4305884100691615310c16210401a85844c4305884100694615310c16010401ac1824c430580410058c650854c56010401651951cd3158041005a4650734c560104016c1921cd315804100698214824c5601040165195cc93158041005a4653324c56010401466919d872552210050b650211d95448401455930847655121006231c9841c16308401464915c872597400fc332617358821900018647620572553200041b662761c95488001466919d87255220006916098118f65480018647620572551200070318d74550214800184c86d95730852000613218655cc214815b84c86d51730852000513259545cc214810b84c8655173085204f433a5b87d8c214800141d9419573101200050d650655c440480018648220576550200061321c73595200800106c97619544802004e8c219545054044013c30765514150110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x22000302487650854c56210401510d210a41262b008200a22680726107058c21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4c
  | 6 => 0x4e
  | 7 => 0x124c
  | 8 => 0x3
  | 9 => 0x5
  | 10 => 0x94c
  | 11 => 0x94e
  | 12 => 0x124e
  | 13 => 0x138c
  | 14 => 0x138e
  | 15 => 0x8c
  | 16 => 0x8e
  | 17 => 0x128c
  | 18 => 0x98c
  | 19 => 0x98e
  | 20 => 0x128e
  | 21 => 0x150c
  | 22 => 0x150e
  | 23 => 0x10c
  | 24 => 0x10e
  | 25 => 0x130c
  | 26 => 0xa0c
  | 27 => 0xa0e
  | 28 => 0x130e
  | 29 => 0x180c
  | 30 => 0x180e
  | 31 => 0x20c
  | 32 => 0x20e
  | 33 => 0xb0c
  | 34 => 0xb0e
  | 35 => 0x140c
  | 36 => 0x140e
  | 37 => 0x154c
  | 38 => 0x154e
  | 39 => 0x28c
  | 40 => 0x28e
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0x148c
  | 44 => 0x148e
  | 45 => 0x184c
  | 46 => 0x184e
  | 47 => 0x40c
  | 48 => 0x40e
  | 49 => 0xd0c
  | 50 => 0xd0e
  | 51 => 0x160c
  | 52 => 0x160e
  | 53 => 0x188c
  | 54 => 0x188e
  | 55 => 0x104c
  | 56 => 0x94054
  | 57 => 0x94056
  | 58 => 0xa1254
  | 59 => 0x104a
  | 60 => 0x104b
  | 61 => 0x104054
  | 62 => 0x1a8a
  | 63 => 0x95254
  | 64 => 0x124956
  | 65 => 0x95314
  | 66 => 0xa0954
  | 67 => 0xa0956
  | 68 => 0x130954
  | 69 => 0x130956
  | 70 => 0x94a14
  | 71 => 0x94b94
  | 72 => 0xb8956
  | 73 => 0x95494
  | 74 => 0x148956
  | 75 => 0x98a
  | 76 => 0x104954
  | 77 => 0x139254
  | 78 => 0x139256
  | 79 => 0xa1256
  | 80 => 0x131256
  | 81 => 0x150a
  | 82 => 0x105254
  | 83 => 0xa4a
  | 84 => 0x138b94
  | 85 => 0xb9396
  | 86 => 0x105394
  | 87 => 0x98096
  | 88 => 0x98094
  | 89 => 0x104094
  | 90 => 0x1a8b
  | 91 => 0x128994
  | 92 => 0x99294
  | 93 => 0x128996
  | 94 => 0x99296
  | 95 => 0x20994
  | 96 => 0x98214
  | 97 => 0x20996
  | 98 => 0x98216
  | 99 => 0x140994
  | 100 => 0x99414
  | 101 => 0x140996
  | 102 => 0x99416
  | 103 => 0xd0994
  | 104 => 0x98d14
  | 105 => 0xd0996
  | 106 => 0x98d16
  | 107 => 0x160994
  | 108 => 0x99614
  | 109 => 0x160996
  | 110 => 0x99616
  | 111 => 0x12cb
  | 112 => 0x104994
  | 113 => 0x134b
  | 114 => 0x151296
  | 115 => 0x151294
  | 116 => 0x105294
  | 117 => 0x141514
  | 118 => 0x151414
  | 119 => 0x141516
  | 120 => 0x151416
  | 121 => 0x150d14
  | 122 => 0xd1516
  | 123 => 0x150d16
  | 124 => 0x105514
  | 125 => 0xa0116
  | 126 => 0xa0114
  | 127 => 0xa1314
  | 128 => 0x130a16
  | 129 => 0x104a14
  | 130 => 0x181316
  | 131 => 0x181314
  | 132 => 0x105314
  | 133 => 0x104214
  | 134 => 0xd0b14
  | 135 => 0xd0b16
  | 136 => 0x160b14
  | 137 => 0x160b16
  | 138 => 0xb0d14
  | 139 => 0x104b14
  | 140 => 0x164a
  | 141 => 0x14cb
  | 142 => 0x105414
  | 143 => 0xd1556
  | 144 => 0x105554
  | 145 => 0x104b94
  | 146 => 0x105494
  | 147 => 0x104d14
  | 148 => 0x105614
  | 149 => 0xe8b
  | 150 => 0xb4d
  | 151 => 0x144d
  | 152 => 0x1a8c
  | 153 => 0x2cb
  | 154 => 0x2cc
  | 155 => 0x14cc
  | 156 => 0x125396
  | 157 => 0x124a16
  | 158 => 0xcb
  | 159 => 0x138114
  | 160 => 0x170a
  | 161 => 0x8b16
  | 162 => 0x9716
  | 163 => 0x9896
  | 164 => 0x14b
  | 165 => 0x44a
  | 166 => 0x99a94
  | 167 => 0x99054
  | 168 => 0x151616
  | 169 => 0x11394
  | 170 => 0x11494
  | 171 => 0x180e96
  | 172 => 0x21294
  | 173 => 0x1a8214
  | 174 => 0x21894
  | 175 => 0x20d14
  | 176 => 0x178b
  | 177 => 0x21a14
  | 178 => 0x20d54
  | 179 => 0x29314
  | 180 => 0x29256
  | 181 => 0x29556
  | 182 => 0x28b56
  | 183 => 0x185496
  | 184 => 0x41296
  | 185 => 0x41416
  | 186 => 0x40cd6
  | 187 => 0x189614
  | 188 => 0x189616
  | 189 => 0x11316
  | 190 => 0x10a16
  | 191 => 0x180a16
  | 192 => 0x29496
  | 193 => 0x184b96
  | 194 => 0x41616
  | 195 => 0x188d16
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2135
  | 6 => 5090
  | 5 => 2158
  | 4 => 59
  | 3 => 3
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
  | 7 => packedAt gbK7 (87527+((h/711+packedAt gbK7 (78995+(h % 711)*12) 12) % 2563)*13) 13
  | 6 => packedAt gbK6 (266368+((h/1696+packedAt gbK6 (244320+(h % 1696)*13) 13) % 6719)*14) 14
  | 5 => packedAt gbK5 (135950+((h/719+packedAt gbK5 (127322+(h % 719)*12) 12) % 2590)*13) 13
  | 4 => packedAt gbK4 (4263+((h/19+packedAt gbK4 (4130+(h % 19)*7) 7) % 102)*7) 7
  | 3 => packedAt gbK3 (245+((h/1+packedAt gbK3 (243+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc1e0703fc1fe01ffffffffc2cc8f1c09cfff
  | 1 => 0xfffe007fc3fe0ffe03e0f807cd3309fe367267
  | 2 => 0xf07fff8003fff00003ff0007f1c3f1e3c78387
  | 3 => 0x7ffffffc00000003fffff83e03fe03f803f8
  | 4 => 0x7ffffffffffffffc0000003ffc0003fffc00
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x480201004c0920498710a344044830c00c4ab
  | 1 => 0x59460235414a049c09a8d05284130876125265
  | 2 => 0x645aea8103ada02832da40a711c1b1a2c78386
  | 3 => 0x486d536da8080050430ce5c22e035c03780350
  | 4 => 0x319c4a32314961600001003ba80001ad2800
  | 5 => 0x8e00180c20218181801086043ffeefd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37363
namespace PEqualNP.Outside.L_meta_37363
open PEqualNP.Outside.L_meta_37363.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 4 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 112 := (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 bs3_3_96))
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
theorem bs3_4_512 : Interval s3Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_544 : Interval s3Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_608 : Interval s3Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_640 : Interval s3Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_704 : Interval s3Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_736 : Interval s3Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_800 : Interval s3Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_832 : Interval s3Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_896 : Interval s3Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_928 : Interval s3Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_960 : Interval s3Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_992 : Interval s3Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1024 : Interval s3Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1056 : Interval s3Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1088 : Interval s3Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1120 : Interval s3Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1152 : Interval s3Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1184 : Interval s3Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1216 : Interval s3Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1248 : Interval s3Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1280 : Interval s3Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1312 : Interval s3Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1344 : Interval s3Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 bs3_4_192) (concat bs3_4_224 (concat bs3_4_256 bs3_4_288)))) (concat (concat (concat bs3_4_320 bs3_4_352) (concat bs3_4_384 (concat bs3_4_416 bs3_4_448))) (concat (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)) (concat bs3_4_576 (concat bs3_4_608 bs3_4_640))))) (concat (concat (concat (concat bs3_4_672 bs3_4_704) (concat bs3_4_736 (concat bs3_4_768 bs3_4_800))) (concat (concat bs3_4_832 (concat bs3_4_864 bs3_4_896)) (concat bs3_4_928 (concat bs3_4_960 bs3_4_992)))) (concat (concat (concat bs3_4_1024 bs3_4_1056) (concat bs3_4_1088 (concat bs3_4_1120 bs3_4_1152))) (concat (concat bs3_4_1184 (concat bs3_4_1216 bs3_4_1248)) (concat bs3_4_1280 (concat bs3_4_1312 bs3_4_1344))))))
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
theorem bs3_5_640 : Interval s3Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_704 : Interval s3Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_736 : Interval s3Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_800 : Interval s3Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_832 : Interval s3Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_864 : Interval s3Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_896 : Interval s3Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_928 : Interval s3Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_960 : Interval s3Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_992 : Interval s3Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 bs3_5_96)) (concat (concat bs3_5_128 bs3_5_160) (concat bs3_5_192 bs3_5_224))) (concat (concat (concat bs3_5_256 bs3_5_288) (concat bs3_5_320 bs3_5_352)) (concat (concat bs3_5_384 bs3_5_416) (concat bs3_5_448 bs3_5_480)))) (concat (concat (concat (concat bs3_5_512 bs3_5_544) (concat bs3_5_576 bs3_5_608)) (concat (concat bs3_5_640 bs3_5_672) (concat bs3_5_704 bs3_5_736))) (concat (concat (concat bs3_5_768 bs3_5_800) (concat bs3_5_832 bs3_5_864)) (concat (concat bs3_5_896 bs3_5_928) (concat bs3_5_960 bs3_5_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 48 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_4_0 : Interval s4Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 2 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 59 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_2144 : Interval gbAtlas 5 2144 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2158 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))) (concat (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896)) (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))))) (concat (concat (concat (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312))) (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))))) (concat (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 bgb_5_1856))) (concat (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 bgb_5_1984)) (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)))))))
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
theorem bgb_6_5088 : Interval gbAtlas 6 5088 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5090 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)))))) (concat (concat (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))))) (concat (concat (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528))))))) (concat (concat (concat (concat (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)))) (concat (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))) (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168))))) (concat (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488)))) (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648))) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)))))) (concat (concat (concat (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968))) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)))) (concat (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288))) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448))))) (concat (concat (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608))) (concat (concat bgb_6_4640 bgb_6_4672) (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)))) (concat (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928))) (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088))))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2135 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568))))) (concat (concat (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696)) (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824))) (concat (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 bgb_7_1952)) (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80feeefac8feeeaa80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074632 * 2 ^ 32 + 4277054080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37363.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,5]⟩,⟨.or,[4,5]⟩,⟨.or,[0,7]⟩,⟨.and,[1,6]⟩,⟨.or,[3,9]⟩,⟨.or,[0,2]⟩,⟨.and,[10,11]⟩,⟨.or,[0,1]⟩,⟨.and,[4,13]⟩,⟨.or,[12,14]⟩,⟨.and,[8,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4277054080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4277054080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37363

open PEqualNP.Outside.L_meta_37363 in
theorem PEqualNP.Outside.L_meta_37363 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4277054080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4277054080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
