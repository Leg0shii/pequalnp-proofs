import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36595.Model
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


end PEqualNP.Outside.L_meta_36595.Model

namespace PEqualNP.Outside.L_meta_36595
open PEqualNP.Outside.L_meta_36595.Model
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

def SBf (j : Nat) : Nat := [5, 4, 7, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36595

namespace PEqualNP.Outside.L_meta_36595
open PEqualNP.Outside.L_meta_36595.Model
def s0K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x284a000642f185c30dc41b083b087410
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x802320c020d030043808010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*4) 4
  | 3 => packedAt s0K3 (i*15) 15
  | 2 => packedAt s0K2 (i*26) 26
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (5+((h/1+packedAt s0K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s0K3 (96+((h/2+packedAt s0K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt s0K2 (80+((h/1+packedAt s0K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 4 => 0xefff0fffc3f8
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 3 => 0x244e89aa3346
  | 4 => 0x1888ee3323b0
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 30 s0Pos s0Neg, 0xccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36595
namespace PEqualNP.Outside.L_meta_36595
open PEqualNP.Outside.L_meta_36595.Model
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
  | 2 => 0xf807f807f80ffffffc0fc0fc0f80fffff24cff
  | 3 => 0x7fff8000fe03ffff000fff000fe07fc70c7
  | 4 => 0xfff80000000fffc07fffff000000fff81f80f8
  | 5 => 0xfffffffffff000007fffffffffff00001fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x48304850508020810430c50c508e164924955b
  | 2 => 0x95529534a316552a3a0b50b50d12ab96524cad
  | 3 => 0xc6a4e4a535aa93b45ed824db6424ccc79c70c6
  | 4 => 0xe4c6c6c6c6cd1a276f6db6824848f1e31f80f0
  | 5 => 0x7070707070e1c38738e38e38e7081041b6a00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36595
namespace PEqualNP.Outside.L_meta_36595
open PEqualNP.Outside.L_meta_36595.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa9314008ce042e6860000000244a340000a8569f00591002a9d61252000131c3c398167418000000a01000006120001b04a089920acf00140004080140018008180050210485ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21ee21fd21fc21ec21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x530020005534251719274244085626050064001166740060323816652f180069580f45735a6747335f46636b6e24713f3730003c004900132b70486a0e0b3e6c625b5c00065e514f003a1a2e4b4a222c0d005d21312a4e030029001f0057002d6d5207001d3d10001e004c431b350c54120104233959020000723b406f0009616800362814501c41004d150a000382010003800282800000000280809c800286000180801103800c8e030006808b85020a8285805b94b43b6a96877651d0eeaa3a1d794f42aea9e857651d0aeaa3a15dd4532ba28a65cd320cabca7a0d754f41b7296836d52d06bea6a0d714d41b7a92836c52506f6a0a0de14141b7296636d52cc6bca318dbd4931b6292633e540c67aa818e795031ceaa0635e510c7aca218f590431eaa08635e53c86baa790f50c721b728c43ce31887986310d7d4d21ae29a433e540867aa810f50c421d72a043ad54086dca210f994421f320843e541087ce6210f38c421e618843e431087886210e78c640ce18c81ae219035843204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521036ca2206d54440cf188819c311035c42206b084409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206215e53842baa7085b94a10b6a9421d431843c843084fd51109e2a2215f53442b8a6885bd4910b629221d431043c842086e10010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6a0a10291e6a680040802ca9488058001c612300b8e2010000062b1185320cac46250431b4181410c715540c421b118d41086e06050421b198631086a5640c421e19903108785640c421e19503108785540c421e10c421903155354440c9549511021d650c4408b5942110384310844099185520c2546154c20d194831843465308610e40c440043a02110010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x10c20a0aeb3206210c85769503108682ba86210881815943108440
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s2K5 (841+((h/15+packedAt s2K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s2K4 (3471+((h/39+packedAt s2K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s2K3 (952+((h/8+packedAt s2K3 (912+(h % 8)*5) 5) % 29)*6) 6
  | 2 => packedAt s2K2 (199+((h/1+packedAt s2K2 (196+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 1 => 0x7f01fc07ffffffff83e07c0f80ffffffc933ff
  | 3 => 0x7ffe0007ffe07ffffc007ff000fff83ff1c3c7
  | 4 => 0x80000007ffff81ffffff800000ffffc1fe03f8
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x914284011c104200c628c508e2c425212561b
  | 1 => 0x224c518b224a28c581a8350d12558ca4c930ed
  | 3 => 0x4c289ad54487516ab4125b64249ad23971c346
  | 4 => 0x68b1636689141db35adb024848e36711be03b0
  | 5 => 0x70c183870e1861dc631c638e70038421eda800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800eeaaaaaacc888800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36595
namespace PEqualNP.Outside.L_meta_36595
open PEqualNP.Outside.L_meta_36595.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x5870a0001e1c2912a24a4d0100ac01f0050009228d30050900184a200271800000004c6ad3680a83421800004b0780085ce903864b000410001c900009d5c00c1ff43fe43fd43fc43ff42fe42fd42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31f731fe31fd31fc31f431ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x6200001623651e1800061a6c10503a4924030c112b082d1f541c004c17222f310000002e1467295f4f45584b3600000039004300255773275b3f1d55416860666d09260a725c040700281900005a0032383e01136470000015004200443347406b0271300e6a590b694a536e4d3d3b48355d375e51203405001b566f2c215212000f610000003c4e0d74632a460c0587000d04810380010b008584008000048201818000050002008a82808680008102040604805b94b43b6a96877651d0eeaa3a1dbd4943b629287775150ee8a2a1ded4143bc282875e53d0abaa7a15d94742baa8e856e528caeca3195d54632bba8a6574514ca7ca8194f55032d72a065ad540cadca6197394c32e721865cd430cabca7a0d754f41b7296836d52d07ce6598f90cb31b7294636d528c7986518dd94631b7a92636c524c67ca818cf55031e619063b6540c76aa818dd94c31eb29863d6430c7aa8618f9cc831eb19063d4320c7c86418f10c831afa9a435c53487ca4210ebcca40d619481b7319036863204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521035e64206b0c840db28881b5511036e62206d0c4409f28081ba501027ca9984f55330dc206616e528c2daa518730ca30bb28c6175518c3a863184fd51309e2a2616f524c2d8a4985dd4530ba28a61cc320c3a862186e100309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520bb2884175510827ca9884f553109faa2213c54442bea6885714d10b7a92216c52442dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1600a8809800003948100a4018b04000a8048c780206000700ba8680000042080002000b1185430cac86050c32c3550320c6c46250c31b4181430c6c6628c831a5590320c786640c831e1590320c786540c831e1550320c6c46348421e10c8319030d53548408b594321031553544408d5943110384320c440d10ca518c346520c630e20c8400c39031100309518d510824c6354810
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xb40000a0aeb3206418c8576950320c682ba8641888181594320c440
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s3K5 (826+((h/15+packedAt s3K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s3K4 (3471+((h/39+packedAt s3K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s3K3 (960+((h/8+packedAt s3K3 (912+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s3K2 (200+((h/1+packedAt s3K2 (196+(h % 1)*4) 4) % 13)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 1 => 0x3f01fc07ffe07fff83e0f81f80fff83fd333c7
  | 2 => 0x3ffe0007ffff81fffc00ffe000ffffc1e3c3f8
  | 4 => 0xc0000007ffffffffffff000000fffffffc03ff
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8114282011c104200c6118a28e2c214a05561b
  | 1 => 0x924c51ab224728e581a86a9b1255a92cd332c5
  | 2 => 0x24289ab5448a1d6ab410b6ca249ab58963c368
  | 4 => 0x30b16346891451935ada041048e34631bc01b6
  | 5 => 0x38c183870e1861dc631cc71c70038421faa800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaaaaae8e80000eaeaaaaae8e80000eaeaaaaae8e80000eaeaaaaae8e80000eaeaaaaae8e80000eaeaaaaae8e80000eaeaaaaae8e80000eaeaaaaae8e80000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36595
namespace PEqualNP.Outside.L_meta_36595
open PEqualNP.Outside.L_meta_36595.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x70000016004e3000000344172600d2400a4316063c1252010000382839d36850222a796990024905300400b467ca2a56988a800000030030db0400c0000188100ff43fe43fd43fc43ff42fe42fd42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31f731fe31fd31fc31f431ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2006640410625f2c214600030e082b71510055113f436d3700472f252e0c15671e0a6b3c0000391a63576e00000538004100004b69285e2d6f68261d23271c17006a4e07365a094818001b32654f13736100580031010000666c00590f520072330200000b005c35243d404a49535b3a344456454c00125d42161f500060291422302a4d3b0d70193e547400000200800080060009030003828080808300830a8001000201000088038f00800480908001000082db94b43b6a96877651d0eeaa3a1dbd4943b629287775150ee8a2a1ded4143bc282875e53d0abaa7a15d94742baa8e856e528caeca3195d54632bba8a6574514ca7ca8194f55032d72a065ad540cadca6197394c32e721865cd430cabca7a0d754f41b7296836d52d07ce6598f90cb31b7294636d528c7986518dd94631b7a92636c524c67ca818cf55031e619063b6540c76aa818dd94c31eb29863d6430c7aa8618f9cc831eb19063d4320c7c86418f10c831afa9a435c53487ca4210ebcca40d619481b7319036863204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521035e64206b0c840db28881b5511036e62206d0c4409f28081ba501027ca9984f55330dc206616e528c2daa518730ca30bb28c6175518c3a863184fd51309e2a2616f524c2d8a4985dd4530ba28a61cc320c3a862186e100309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520bb2884175510827ca9884f553109faa2213c54442bea6885714d10b7a92216c52442dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x91a00009060c812b0602600011c38000002e008a0a58000002a0000000007a2500086002001003b1185430cac86050c32c3550320c6c46250c31b4181430c6c6628c831a5590320c786640c831e1590320c786540c831e1550320c6c46348421e10c8319030d53548408b594321031553544408d5943110384320c440d10ca518c346520c630e20c8400c39031100309518d510824c6354810
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xc20010a0aeb3206418c8576950320c682ba8641888181594320c440
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s4K5 (826+((h/15+packedAt s4K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s4K4 (3471+((h/39+packedAt s4K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s4K3 (960+((h/8+packedAt s4K3 (912+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s4K2 (199+((h/1+packedAt s4K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 1 => 0x3f01fc07ffe07fff83e0f81f80fff83fd333c7
  | 2 => 0x3ffe0007ffff81fffc00ffe000ffffc1e3c3f8
  | 3 => 0xc0000007ffffffffffff000000fffffffc03ff
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8114282011c104200c6118a28e2c214a05561b
  | 1 => 0x924c51ab224728e581a86a9b1255a92cd332c5
  | 2 => 0x24289ab5448a1d6ab410b6ca249ab58963c368
  | 3 => 0x30b16346891451935ada041048e34631bc01b6
  | 5 => 0x38c183870e1861dc631cc71c70038421faa800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaaaeaaae800e800eaaaeaaae800e800eaaaeaaae800e800eaaaeaaae800e800eaaaeaaae800e800eaaaeaaae800e800eaaaeaaae800e800eaaaeaaae800e800, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36595
namespace PEqualNP.Outside.L_meta_36595
open PEqualNP.Outside.L_meta_36595.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2433f54486fca890df55121be2a243bc5448678a890dfd4d21efa9a435f53486fca690df54d21be29a43dc53486b8a690fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea96817e51d02faa3a05f55240bf29c817d53902fca5205f54a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940be292817f51502f8a2a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40bf290817d52102fca2205f54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a9987790f30eea1e617e52cc2faa5985f94730bea8e61fb40cc3f081985fd5230bf2a4617d548c2f8a9185f54e30bf294617d528c2fca3185f54630ef18c61dc318c2fca11877cc230fd984617f544c2fca8985f55130be2a261de434c3ba86985fd4930be292617f514c2f8a2987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c2fca4185f54830bf288617d510c3bc6218770c430bf28061fb400c3f0801877cc030fd18061dd300c3f260185fd5320bf2a6417d54c82f8a9905fd4f20bf29e417d53c82f8a7905f94720bea8e41ef21c83da43905fd5220bf2a4417d54882f8a9105fd4e20bf29c417d53882f8a7105f54a20bf28c417d51883dc43107b08620bf28441ef20883f641105fd5120bf2a2417d54482f8a8905fd4d20bf29a417d53482f8a6905fd4520be28a41ef21483da42907ec8120f7102417f54082fca8105f55020be2a0417f53082fca6105f54c20be298417e52082fca2107d94420bb288417d51083eaa2105d54420f710841ec21082fca0107bc8020fd10041ed20083f240107a48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c43f641887e08310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec42887d48510fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0x14000000d0200300401000050380002c0a0141700408018000040300806000140042900c010dc0102c0406c0202c0c00002004000040301c2500401094030480001c14002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa9287ef5250edea4a1df14943f6292876c5250efea2a1fdd4543bba8a877c5150fe8a2a1dd14543bfa8287fb5050ef6a0a1df14143fc28287785050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42dea1a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf29885de5310abca6215f54c42eea98855d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e65ef42ccbd885995f94732bea8e657e50ccafaa1995fd5232bf2a4657d548caf8a9195f54e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a8997790d32eea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32bf29065ef420cbd8841977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41ef29e835e53d06faa7a0f754f41aea9e837e52d06faa5a0df94341bea86837d54906fca720df54e41dfa1c83bd43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50906faa120dfd4d41be29a837f52506f8a4a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077e8620ef50c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998df94b31bea9663f741cc7e88398df94331bea86637f548c6fca918df55231be2a4637d538c7bc8718f750e31bf294637d528c7bc6518f70ca31bf28c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a2637f524c6f8a498fdcc531ef18a637f504c6f8a098dfd5031bf2a0637d540c6f8a818df94c31ef21863dd430c6fca418df54831ef19063dc320c6fca218fdd0431fa20863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52886fca310fbc8621fb90c437e50886faa110dfd5121dfaa
  | 2 => 0xe1520005a4f40de0003585380036e41c001280d42d4e61b433a514612460c467c16830446784841ab31c5b8361d70985d4809b026c7c07311839a7dcfa8423a6000870a63ca4f47912a30036cc38ef3b4164e805438a1c4978101fe318469963cc60c0422a1a83b0c294c0cc4f0601602ee0347180245e3a47b88439e478000344763f0a99380224ecc901a3f26783a8d33f079ca78e22ae828ff21d1ce3b4000a000087000000000000512170000003000035c62c9718f07c19c7a9972525cd1b0ac478698ab24512615d17123136844548da23a494a11654560001e0b70001605c0f91540bc000000000010f88109e254001991940000008c0002b4899620000000000020a3a0dd885434028258000ac0fc000001be000e89d402e680dc943044000bd1ca0e0878801323701acfd1e40008182982709c90400000030114ae91733830d0805b2c680c781a141a89c2408a3f8620f99eb1e81bce11ec458894659900661002e89f4163e0a38e142a4248e0692bc248680070bc1280d88b3c00907282a35e058fd89c2582446781929a1f8ac1c8000054000642ce450032052cc0007e9590000002300000066800097000628e317621a8dc0000010e000d18001b8260e49d9400884170a42f66d4002292965f9211ce174274192282727bc219343aa6247d8001826044ca1910c3e81288f0002fc000bb1fc6cc000002621f48623304c0b03b0653824cc4810326a0050707901e0380010b0005041e8d73a4000ae000000000249ff0e80005792d3ac2951a83a00000000000106000000a82a22b8b51200005210618d008804ed838220761078c724e584b90e43c66a4f88eb2fa568c3000222418628230ee348e580040400120078156134d891208e610cc0891884e86707200055000000204239220f328846d038003bc71c060ee00077c001042a0690f120912c0005f1a50c64fc0f80047a000ba13e00091d042301280011c800474000b797f0267740000b24c000001bf3045e41087317228cb61a23807a40a1aa358898aaa243860acf70ea34e7701b8bd4688891c10a0a26b4bc1401904682f80532600000000244490a300016090d1f8d9364000668280001e8100b22d6538980d11924acb405206c880400290887a8001164260011f0392be000188b137c1040e800000860048f63da86c000001680002002000000030240706c070041100c0501c0d0600000c13038060980000c0c0140000c1a034000180003004000000000001c06008010080006402010201200400c000140100003004060041e0342006c2806c020000a0000f0380102c7e0400101c00028040000e02831078030200101c0000406038210080103c0203c0001c0200c030a81000c02000000140201007008070580508003008000001301c01004010341100405010000080600
  | 3 => 0x48410cc1105c4b68d53ec6a04f000000650f914a0c27f4701bd134525190500001fcde18c0f68112490f00047c50a48374000c88002422d80e1153884650b01e0d04dcfa03b2c8000b806e0006d83e06d0b80d459a3145a56c2d2121ba00c000003360002a8001e2850000d8000654000000005f05
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x53086796014c219bd9521086e860484219dd95210876b2154021dc88550087692154021dc48550086b86050f4097d8d519025c6354640c714d43503586054c40c754e411031d5310440c754f401023f6550040c754d401027b65500409b98854cc26d6215330c715143cc2d86050f30e650f40cc2d963103309b98b548c26d62d52309d987548c27561d52308fd91518c23c64546309bd89544c26c62551309dd85544c27461551309ed81544c25c6550d30c7151434c23d6595030ce181540c23e64150309798c540c31d548c430c7550310c33954d00309e594400c31d54cc03097d95300c31d544c0309ed95300c25e63153209758c54c823e6414f208f59053c82e860487209798c548825d63152208f990538823d6414e20ba580218825f63551209718d544827761551209d185544825e63151209758c544823f6454d208f19153482776154d209d185534823e6414d208f590534826e65c8520ba181214827661d50209d587540825e63150209758c540827661150209d584540827661d4c209d587530823e6414c208f59053082766114c209d584530823f64544208f191510825f63544209718d51083376454420cd19151083576354420d518d510837060544209b59621083655188420d954421082e96008420d954720082e96288020dc546200826f6548020d9545200827b6548020dc54520082eb6548020dad9520082e86148020f894520083695148020f8545200836151480209798e54c425d63953108f99253c423d6494f10bc18121c43e121c8310dad4820c42f16108310f888420c425e63152109758c548423e6414e108f590538423e64d4a108f593528425e63d4a109758f528436852482108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427b60549109b994524432f5414910cb150524434f5314910d314c52443656114910da580524436452885109d195214427a6588110da14a20443e221881109e19520443685248110f8485204436852c41109b98b540426d62d50109798c540425d63150109b988540426d62150109b98b530426d62d4c108f990530423d6414c109b988530426d6214c109b596520436860548109b988520427661148109e980520427965c8010da54b20042796508010da54820042f16108010d954b10042796584010da54a10042776544010d9549100427b6544010ba18910043695244010
  | 1 => 0x8004a1d41fabaa3238818d0000001786e009bc000a06e8a2878f03b8009c8000004e3e83a70000748007196200000990000013e000000000000000000007900064934b2000002580000016800002ea00268430080000030a1a3500000001000020200100000008000000002c000600000000000070000f004010100201c0000c0401403034010080001c0f000020000401c00004030200b008020000a00403000030000000c050040600c0000001008000000500400000000000100401008010040500c00004030040101400008000000000004008000080a010000000000801004060000800003010020040200001008000080a014020036752d4543d914b5150f675214543d91485150f6b52d4143da14b5050f7351d4143dc1475050f6b5214143da1485050f735114143dc1445050e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43e3d894310f8c6250c43e5d854310f946150c43e6d814310f986050c43c750d5210f1d4394443c750d5010eac6250f4297d8d5190a5c6354642c714d4350b4c6254c42c754f4210a3f6550842c754d4210a6f65508429e98054cca796015332c715143ccacc6250f32e350f42ccacd6310b329d987548ca7561d52329e983548ca7960d52328fd91518ca3c64546329bd89544ca7761551329d185544ca7b60551329e181544ca5c6550d32c7151434ca3d6595032cb189540ca3e64150329798c540cb2d54d08329b594420cb1d54cc83297d95320cb1d544c8329bd95320cb576154f41c794d43906ac6250e41ae181439069d6310a41a758f41906ac6250c41add8543106b86050c41a758c421069d63d04418fd9541106776550441cdd8554cc73554107319b98b548c66d62d52319e983548c67960d5231c7951438c6cc6250e31b6181438c69d640ca31a7593318c65d63951319bd89544c66c62551319dd85544c67b60551319e181544c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c31c7151430c6cc6250c31b5d85430c6d86050c31a7590320c6d563d04319d594410c7954310431a7593310c65f654c4319dd95310c65e63153219758c54c863e6414f218f59053c865e63952219758e548863e6494e218f592538863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544871f54d4d21c7153534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c7150534873b54d4121ce153504875b53d4121d614f504873b5414121ce150504875b5314121d614c504876a21141219e983540867960d50219798c540865d63150219e980540867960150219e983530867960d4c218f990530863d6414c219e98
  | 2 => 0x400ca000005d2d0669e60000061832000000b18c00000a200000000000008f15e6c8002796800000248847b0000017c00000491a8002d8541800011e9013c0015c00000000000000095000000580005083a44642e20001caaa1c5c800770b2150ba9d0002a93a5106200178000002e0003917e0017a0029e001260000000000001f20010a800960000068800aa00000000000ea520000000000000088007c1ce56800a802e00280480000c000808008403ebb01a811b86b0f60012c002265a9fa00000651a000000002a60026c532d21e9ee0d12a920a8000c84da8a0019c828001091c82170851a60000000090000000000000000000000000000000af80005800001107f9fc9d9e069000051c87a85215800002c6599884cae45ba8e5d8009729c7d2e80011a998dc002dc382ae002a40013800122b0000b3800000002900000000131028ea62348004b804359308884a00000420cc708001a000002e62680000060b318e2d894948883894a500c6581529aa0c0029a02812ad0001f086001e823824190de00000002e03698420a5e00000000f40027e861f81e0be8c04600066002f20000000000000000000000000000ae9e8e8100443c9be000b0b7800002d6002564180093800ae11239806000002f1547d800002dabb8760005c00000000008c800000000000000000af072a4260000f8000000000030000001d01a800000005903cb522e000d8539c43f800001b40a25a001cc0000000278001e200000000480018200158a5104228a6082420024a001de0000000298a180000038728c42b02aa88000000000098001aa9f0000024c000000000000000519b00000000296000ceb1000002b20001e002f4060000000045a122d234ac0000009c3b0005b000001d800000ad80000080438008aa920000000000002369b8741c2f055a826780000284000008914200000940000000046000880109c1d623000030001b0006ba3e91998b2a2cab22885800000000000e0998a0d9da00000b080000000001963f1146d
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x10900800051054a0002d31d23c300100014038044c18d083005a001742310c2a1887a21886050c43d20c23028621d197015143cca86b90a8a1863465c05450c31b08e4a188218d907050c410c686b90a8a1e61851906354420cc0eca8a40107237454520083903a2a290041d0dcd5148020e80e6a8a40106635258420c4270bb44210621985856014910cc4cb10c4088560754852044330a92c2100211a1d95244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x22000c20761d15148020c40761cd5148020d00741cd5148020
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 586
  | 4 => 379
  | 3 => 22
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
  | 5 => packedAt s5K5 (17772+((h/195+packedAt s5K5 (15822+(h % 195)*10) 10) % 704)*11) 11
  | 4 => packedAt s5K4 (15662+((h/126+packedAt s5K4 (14402+(h % 126)*10) 10) % 665)*10) 10
  | 3 => packedAt s5K3 (1113+((h/7+packedAt s5K3 (1078+(h % 7)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (183+((h/1+packedAt s5K2 (180+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7e03ffffc07fffc0fff07e0ffff83ffb88fe3f
  | 1 => 0xfffc07ffff80ffff03fffff03fffc0fcff1fc7
  | 2 => 0x7ffff80fffff01fffc007fffc1ffff070fe3f8
  | 3 => 0x8000000fffffffffffff800001fffffff003ff
  | 4 => 0xfffffff0000001fffffffffffe000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x229850a4471224c02cb416456a5915a9886e1b
  | 1 => 0x4293140890e484b0150aa510ca944303b16c5
  | 2 => 0x4850a26912241d5554084d698935a6260da368
  | 3 => 0x6162c58e244891a69a6d010c21c638c7d001b6
  | 4 => 0x7183060c3870e1b8e38e718e30043087e6d800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xece8e800ece8e800ece8e800ece8e800ece8e800ece8e800ece8e800ece8e800ece8e800ece8e800ece8e800ece8e800ece8e800ece8e800ece8e800ece8e800, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36595
namespace PEqualNP.Outside.L_meta_36595
open PEqualNP.Outside.L_meta_36595.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x400f6b8a60c48c63800056014e88000000006849b4a005c11401120d8816460e9150850a4c99bf10f1c16aa1802e9899d1e8691f200138d28300162d2688aaa5f099021a04005000000312003021c00f10060007ff53017f94c07fd53017f14c05fe43007f50c05fc4301ffd4803fe5201ff54803fc52017fcc803fe32007f4c803fc3201ffd4407fe5101ff54407fc51017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc2101ffd4007fe50005f94007fd5001ff140077c50017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c2000ff58e10005fac708013fc63840057e31c2008ffd4e10077fca708023fd538401dfe29c200eff90e10007fa870803bfc4384009ffb142000bfd8a1006ffcc508006fe6284001feb142000bf58a10027f8c508006fc6284011ffa94200dff94a10047faa508037fc528401dff994200dff8ca10007fa6508037fc32840197eb0c2008ffd4610047fca308023fd5184011fe28c200effcc610007fc6308003fd318401dfe18c200dffc8610007fc4308003fd218401bfe10c2007bf98210047fea108013fe5084009bf2842008ff54210027f8a1080137c508401dff9842004ff8c210007fa6108013fc308401bff9042004ff88210007fa4108013fc2084001ff8842000fdc4210007f62108033ff65440197fb2a2000dfd9510004feca88033fe65440077f32a200cff59510065faca88033fc65440077e32a200cdf1951001cf8ca88003ff63440017fb1a2000f7d8d10005bec68802ffe63440057f31a2000ff58d10005fac68802ffc63440057e31a2000f718d10015b8c688033ff5344017ff29a200cff54d1005ff8a68802ffe4344001fea1a200bff10d10007fec488002ff6244001f7b122000bbd8910057fcc488006fe6244001feb122000bf58910057f8c488006fc6244001f63122001bb18910067fea48802bfe5244019fea92200aff1491005ffe648802bfe3244001fe992200aff0c910067fea288033fe5144019fb28a200cff54510067eaa288033fc5144017ff98a2000ff8c510007fa628802ffc3144015ff90a2000ff88510007ec4288003fd2144001fa90a200aff08510067fea088033fe5044001bf282200cff54110067f8a0880337c5044017ff9822000ff8c110007fa608802ffc3044015ff9022000ff88110007fa408802bfc2044001ff8822000fec4110007fc2088003f61044009ffb282007bfd941003ffcca0800efe650400ffeb282007bf59410027f8ca0800efc6504009ffb182000bfd8c10037fcc60800afe6304001feb182000bf58c10027f8c60800afc630400fffa982006ff94c1003ffaa60801bfc530400dff2182000ff50c10037f88608013ff62040017fb102005ff9881000dfcc408003ee6204003773102000ff58810005fac408003ed620400176b102004ff1881000df8c40801fff520400bff2902007ff5481002ff8a40801bff320400bff1902000ff4c81002ff86408026fe610400fffa882007ff9441003ffaa20801ffc510400dff9882000ff8c410007fa620801bfc310400bff9082000ff88410007fa4208017fc21040117f3002007ffd4010027fca0080137e500400ffea802004ff14010026f8a00801bff3004009ff1802000ff4c010027f86008017ff2004009ff1002000ff48010027f84008003ff1004001fb8802004ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0xefc6588009ffb1c4000bfd8e2009ffcc71000afe6388001feb1c4000bf58e20027f8c71000afc6388029ffa9c4013ff94e200a7faa71004ffc5388027ff21c4000ff50e2009ff88710006fd6288003ffa944001ff94a2000ffaa510007fc5288003ff9944001ff8ca2000ffa6510007fc3288009ffb0c4000ff98620005fcc310003fd61880017eb0c4004ff186200a7fea310053fe5188029fea8c4014ff1462009ffe6310003fe3188001fe98c4013ff0c62000ffe4310007fe2188001f710c4001ff4862000ff84310007ec21880037f3044014ffd4220027fca1100137e5088029fea844004ff14220026f8a11004fff3088009ff1844000ff4c220027f86110007ff2088003f79044001fec8220027f84110007f82088025ffb2a4012bfd9520006feca900027f6548025ff32a4003bf99520097faca9004afd6548025fe32a4003bf19520096f8ca9000e7c6548001ffb1a4000bfd8d2008ffcc69000afe6348001feb1a4000bf58d2008ff8c69000afc6348025ffa9a4011ff94d20097faa690047fc5348023ff21a4000ff50d2008ff88690006ff6248003ffa924001ff9492000fdca490007fd5248025f6a924001ff1492000ffe6490007fe3248003fe9924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148025ffa8a4012ff94520097faa29004bfc5148023ff98a4000ff8c520007fa6290047fc3148003ff90a4001fbc852000ffc4290007fd2148001f690a4001ff0852000dfec09004bff5048025ff2824000df94120097faa09004bfc5048025be2824011ffcc120007fc6090003fd3048023fe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f82048013ffb2e2009bfd971004ffccb8800efe65c4013bf32e20039f9971004ffacb88026fd65c4001beb2e20009f5971004ff8cb8800efc65c4001ffb1e2000bfd8f10087fcc78800afe63c4001feb1e2000bf58f10087f8c78800afc63c4013ffa9e2010ff94f1004ffaa788043fc53c4021ff21e2000ff50f10087f88788003ff62c40017fb16200fff98b1000dfcc588003fd62c40017eb16200fff18b1000df8c588027ff52c401fff2962009ff54b1007ff8a588043ff32c401fff1962000ff4cb1007ff86588027ff51c4013ff28e2009fd9471004ffaa388027f551c4013fe28e2010ffcc710007fc6388003fd31c4021fe18e200fffc8710007fc4388003f621c4001fe90e2000fd4871007ff84388027ff50c4013ff2862000df9431004ffaa188027fc50c4013be2862010ffcc310007fc6188003fd30c4021fe186200fffc8310007fc4188003fd20c401ffe1062004ffd9610045fecb08023fe65840077f32c2008ff59610045facb08013fc65840077e32c2004ffd8e10005fec70803bfe63840057f3
  | 2 => 0x50026fec5280737e6294001beb14a004df18a500eefe65280737e3294001be994a01cdf0ca50026fec3280037e6194001beb0ca004df186500eefe63280037e3194001be98ca01ddf0c6500e6fe43280037e2194001be90ca01cdf08650026fcc12800e7e6094007bd304a01ddfcc250026f861280737f2094009be104a004ffd96300ddfecb1806ffe658c0077f32c601bff596300ddfacb18013fc658c0077e32c6004ffd9230005fec91806bfe648c0317f3246000ff59230005fac918013fc648c0317e324601bffd52300d7fca91806ffd548c035fe2a46002bf58e30017fea71800bfe538c005fea9c6002ff14e30017fe871800bfe438c005fea1c6002ff10e30027fec518067fe628c0037f3146000ff58a30005fac518013fc628c0037e314601bffd4a300cffca51806ffd528c033fe294601affd0a300cffc8518003fd428c033fe2146002ffcca30017fc651800bfd328c005fe1946004ffd8630007fcc318002fe618c001feb0c6000bf58630027f8c31806fff518c037ff28c601bff546300dff8a31806bff418c001ff20c6000ff506300d7f8831800bff318c005ff18c6000f78c630017fa631800bfc318c005ee18c6019ffc8630007fc4318003fd218c033fe10c6002bf982300dffea118013fe508c009bf284601bff54230027f8a1180137c508c035ffa046004ff90230027f8811800bff308c005ef9846002fecc230027f8611800bf8308c033ff9046004ff082300bffeca9805eff654c001bfb2a60009fd95300bffcca9800efe654c02ffeb2a6017bf595300bff8ca9800efc654c02fbe32a60039f19530007fec898002ff644c02dff3226018bf99130007fac898002fd644c02dfe3226018bf191300bffea89805bfe544c02ffeaa26016ff15130015fec69800bff534c005ff29a6002f794d30017faa69805fdd534c005fe29a6002ffd0d30017fc869800bde434c005fea1a6000f750d30017f88698003ff624c0017fb126015ff9893000dfcc498003fd624c02bfe3126001bf189300bffea498057fe524c02ffea926015ff149300b7fe8498057fe424c001fea126015ff10930017fe649800bfe324c005fe9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c02fffa8a6017ff945300bffaa29805ffc514c02dffa0a6000ff90530007fa829805bfc414c005ff98a6002ff8c530017fa629800bfc314c02bff90a6000ff88530007fa4298057fc214c0057fb026017ffd41300bffca0980037e504c02ffea826017ff141300bef8a09805bff404c001ff2026000ff501300b7f8809800bff304c005fd9826002ff8c130007bc609800bfc304c005ee1826002fe0c1300affe4098057fc204c009ffb2c4014bfd96200a7fccb1000efe6588029feb2c4014bf59620027f8cb1000
  | 3 => 0xfb2a6224bfd9531127fcca9880efe654c449feb2a6224bf59531127f8ca9880efc654c401ffb226200bfd913111ffcc898862fe644c401feb226200bf5913111ff8c898862fc644c449ffaa26223ff95131127faa89888ffc544c4057fb1a6202ffd4d31017fca69880bfd534c405fe29a6202ffd0d31017fc869880bfd434c405fe21a6200ffd8931005fec49888bfe624c4037f3126200ff58931117f8c498806fc624c449ffa926222ff94931127faa49888bfc524c447ffa126222ff90931007fa849888bfc424c405ff9926202ff8c931017fa649880bfc324c4057fb0a6224ffd4531127fca298893fd514c449fe28a6223ffd0531007fc8298803fd414c447fe20a6202ffcc531017ee629880bfe314c401ef18a6202ff0c531017b8629880bf4314c445ff90a6222ff08531007fec098802ff604c401ff3026200ff58131007f8c098802fc604c449ffa826224ff94131127faa098893fc504c449be2826223ffd013111ff8809880bff304c405fe1826222ffc8131117f84098887ff65884437fb2c4221ff9962101dfccb10887fd65884437eb2c4221ff1962101df8cb10803ff63884017fb1c4220ff98e21015fcc710803fd63884017eb1c4220ff18e21015f8c710887ff5388441ff29c4221ff54e21107f8a710883fe4388401fea1c4220ff10e2100dfac510807ff5288403ff2944201fb94a2100ffaa510887ed5288403fe2944201ffcca2100ffc6510807fd3288403fe1944201bf9862110ffea310887fe5188443fea8c4221ff14621107fe6310803fe3188401fe98c4220ff0c62100ffe4310807ef2188403fb90c4201ff0862100fe84310803ff6088401ff3044200bf98221007fac110802fd6088401fe3044221ffd422110ffca110887fd5088443fe2844221df14221107fe6110883fc3088403ff9044201ff0822100fd8411087fff654843f7fb2a421fff9952101dfcca9087ffd654843f7eb2a421fff1952101df8ca90803ff63484017fb1a4200f7d8d21005bec69087bfe63484057f31a4200ff58d21005fac69087bfc63484057e31a4200f718d21015b8c69087fff534843dff29a421fff54d210f7f8a69087bfe4348401fea1a421eff10d2100dfec490807ff5248403ff2924201ff5492100ff8a490807ff3248403ff1924201ff4c92100ff86490806ff614843fffa8a421fff945210fffaa29087ffc514843dff98a4200ff8c521007fa629087bfc3148403ff90a4201fdc852100ffc4290803ee2148403fe10a4201fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc60484017e302421fffd41210fffca09087ffd504843ffe282421fdf141210f7fe609087bfc3048403ff9024201fbc812100ff840908137f639403bbf31ca000df58e50026f8c7280777e4394001bea1ca01ddf10e
  | 4 => 0x803ff6250c017fb128600fbd8943005dec4a18abfe6250c037f3128600ff58943157f8c4a1806fc6250c01f63128601bb1894315ffea4a18abfe5250c57fea92862aff14943017fe64a180bdf3250c05ff1928602ff0c943007fec2a1802ff6150c01fbb0a8600bdd8543007fcc2a1803fd6150c01fe30a8600bf18543007e8c2a1802f46150c57ffa8a862bff9454315ffaa2a18affc5150c05ff98a8602ff0c543017b862a18abff2150c55fe10a8600ffd8143005fec0a1803fe6050c01feb028600ff18143005f8c0a18afff5050c57ff282862bff5414315ff8a0a18af7c5050c05ff9828602f7cc143017f860a18abff2050c55fe1028629ffd953214dfeca990a7fe654c8077f32a6429ff5953214dfaca990a7fc654c8077e32a6400ffd9132005fec8990a3fe644c8317f3226400ff59132005fac8990a3fc644c8317e3226429ffd5132147fca8990a7fd544c851fe2a26401bfd8d32017fea69900bfe534c805fea9a6402ff14d32017fe869900bfe434c805ef21a6402ff50d32007ba869900bfc434c8037fb126401ffd493200ffca499007fd524c803fe2926401ffd093200ffc8499007fd424c803fe2126401ffcc932017de6499007fe324c803ef1926401ff0c93200fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf1853214ffea2990a7fe514c853fea8a6429ff14532147fe82990a3fc414c805ff98a6402ff0c53200ffe4299007fc214c801ffb026400bfd8132007fcc099003fd604c801fe3026400bf1813214ffea0990a7fe504c853fea826429ff1413214ef8a0990a3ff404c851fe2026402ffcc132017f86099007ff204c803fe1026427ffd963113dfecb1889ffe658c4077f32c6227ff5963113dfacb1889ffc658c4077e32c6200ffd9231005fec91889bfe648c4317f3246200ff59231005fac91889bfc648c4317e3246227ffd5231137fca91889ffd548c44dfe2a46202bf58e31017fea71880bfe538c405ef29c6202ff54e3113fbaa71880bfc538c405ffa1c6202ff90e31017bc871880bfd438c401eea1c6202ff10e31007fec518897fe628c4037f3146200ff58a31005fac518897fc628c4037e3146227ffd4a3112ffca51889ffd528c44bfe2946226ffd0a3112ffc8518803fd428c44bfe2146202ffcca31017fc6518897de328c405fe9946202ff0ca31017b8651880afe618c44fffa8c6227ff9463113ffaa31889ffc518c44dffa0c6200ff90631137f8831880bff318c405ef98c6202fdcc631017f8631880bf4318c44bff90c6225ff08631007fec118803fe608c4017f3046200ff58231005fac118803fc608c44fffa846227ff9423113ffaa11889ffc508c44fbe2846226ffd0231137f8811880bff308c405fe1846202f70c23112ffe4118897fc208c449f
  | 5 => 0xcfb4e0631fd40c0001098000ad37c2422782d8a2d1841660f736635411f2ff1bd17a03f27d0540a702f1802ef25105100005a37535e1a3b1d1cf43400039d00018e12138a2cb8d4b630170ee2902181ab3be2b602d3c42a236f08cba712610f1849172a83c12d21a73cd09741402a00010c45b43e0ee80011e41535d0860c1250048108b001bc0ba00a3f040f0ce0dcc4108e1200b22e6c5307b27326100000000039c0000003ae2761b18002c280020331091d80042c2680000003924318002433693101a12112922e93163178792a30004219383ee00323026b3bb04e45646203600023e07c3051463e623100024444086522c37f2720000c000028a3d939312d0000002418002caa5706880016100038e28b96bbf204483c3a343b4071d90e928097f2401eb1450d006691400000029080402e0240000100c020008070300040000200000001010000064018010020040100401a0dc0000000201402008008000000080000000400104e00800800000000000140060300000101a0000400301c03c00022000038010020260040001f00202000000000008008100000340900e0780180880200e00c0002e01a0000000001000c0780000c010008080000000001100c0181b003006018028040040000000b002024008280020200200600001005809004008010030000080300500e0200d0030000500200b0000180400f000010028030000000000600e0900080501a0340680000408406807014008000070180140f001002038060150260741f804002014000010140240000d0160300781004602004001008000040030340081180001800c000000080000000103e0b40080000e01c0380100600006014002038008040140800d8010000900a0040280040a81d00a00c06801004048018050000300000000000406014012000018060140000100f0000040280207403c000000000000480102600c0d0060280240000401603c10805014038010030120000180600000000800052004010020380b80000003a0000000000c0040080200800001804000000018000060080581501a0000101504401c0000200205c0100400a0280902d01a004000000000500700003a0000000000400c0700700a0000a80a00200c040090140500100701a06c0080400c0040200100a008020030040040080400c00406808006004068030180081e0010100080001207200400001008040000080760040300a000000000120040080500004c02c0000001c00800000058008000050000240580308e0240000602204c0100803600c0000107e000000000002bffd954315dfecaa18affe6550c077f32a862bff5954315dfacaa18affc6550c077e32a8602bfd8d43017fea6a180bfe5350c05fea9a8602ff14d43017fc86a180bbe4350c05fe21a8602f710d430173886a1
  | 6 => 0xa2343041a586b0e50001bf29f10a96f0c425a0ac0393583b20cd0002d10bb1b38de8b40002bf0728980f03960001238002fd41f9860002ea00011129513600028621913d0604483203118ea057baf0bc83ebcb1fb1f20ada37be713016d9adc230c29be01aafc1198439d519536c1742fb1d62ce2b444430904c0000470571350841b2abc2d2a8345946315301916f9228000fe071a7f80007509184a4599650004273291aa30207d18b0003083a90000002f98f51cc0001ff0000003d100000000045c0000002c11f50000c50d31f10002363a501cb8300000008ac582700000000002b81790cb08d8003a4000200a4a37722500035b000258454894c05106170bb83d40000db99b20f3f900032216d2b9bff9490452a3c3a45d0be0002ae44f0000d780026e00b0b00acb19a122bfa970b10420141480bd01a45112509e1b540a3ab27b38514a8bc0522390c81b994cae800043c00012b37819203a9b88003350fb25d00000000015500007033129c9c20000002d803fc04026bea0c30000003c9039ac226604d3b612a2c90ba98399128533d00033f1390832ee3c51ec0ed8daac72d64011b41560e0b0e21d38c41e00e1881241230f233004b14206e44716a2b90000081a01af8001a60d914a2c522944e0810a010b3562d9a812cda061af166aa625b23525311b11ba151e43a82ba08a000274236b9f3393c232542f2bb15b8720000002e003338827e05831500006832d00000001b00000000020a2f73380131c81c11ae43728f11a19f3ce3620a80ae0001ee13c2c00a5000000122000000374069c0e2b7a6000045a0310599751dc2f8a563fc0432fabac34d2f6000165a520001cd8003a20709040010001e0b2639e36e36d0000001e10001ce0000002d39c00d40150212f21f0125ad314b2590002dd26c09c2d6b2c4202e23eb0000001718000002a90000db0dd1413bc4418000e200000035c0000004568002e60731bb42089436800000000008b42d0002ec44c085292c5501800000043f0000002f800042a124c0600000019e19004080030fb760ec2a40f905c2010898b81ef18200010e45ba1609695122403e1a944500b8002f031b0000e0304a8400000029b24d313201858c0085d1d29ba20e3980100b987603406a2ca2e718106c0693de3702232d90bb8951f91d10271d23f740d34430b1cd2db1e314703b83b16b2980a31f619d26f1e21570321dd30e94300019c16ac10291c160710002453b30000000678000000920000e71ed0e637200039444d13989a3322080aa1b00001df21b11c0003fe0b313e03a1e626d2f91f18043192672b52eb0350b900024f00041d07e3c83fa3b700018f3f60000d595c3170000000000002cf00039b0004362b896700000000023d1679020c5b1aa202b6b271a4b911270002f344032a0419102
  | 7 => 0x2f1432087c3121c0d64461b11d417b0ff00c11d31429e8d69b49da15a8821a400003722e1c702840807390918504020c0ef000024b5f3f421400c9963e50d52b33674001fc37d2d1bf31372319f335a892ada9b725f0801a297028b05914409f2e5107bd8197986b0a3c710085303d8f0c2b0dc2620de4611ca2a280033b045ab2289886c0b20431397e34c3d50cc29120b0000053b013a3e4252aa54428003613fb00031a16315e0003e10ddb3413a88eb521b62381598000002c30670002cc0003181542ed00000000000000000000005e2ad11fa770000002cca4c35900011800710a34f3bd1a534b8001db1d315d1ac169c5731100042220000038909b11e8003ed2d4b2e02345434b1df8003c300043829c185ad423f2cb0b62de02b4180000000efa131c42aa31e2d73038f306f1e51031b0b8f0a918a18911c8c93970412410931991341770ca3fd1720f436519839045f0200e810d1971012d51001a800000000000027a00029ba7500000000000029a00024900029d9582f40000252470640000003c031f03d195a223821d8a273d31a31e90959f83791b79081330002333188fea8e00032300d3811c92711d836a23a3e901c42e056b0c34541238b2df3db2da26930739a0d73028001501cb0003cc17c05b3b900023c01dadc40200000000e8003460001b69d0430a542a1129000074023ac621a3129713a008880008830615a0913aea870000000d99692a0000099000000000288a2a3570df93b1f400000037a0002070fa0000c4b430000eb14dc1700000031680002c33a14c20d0f13ec3aa2631873b108728aad004f2d58b541a2e112841f32144b3601190d23df0cf0c3c2602613cb843a63481588381b929423b20516e4302e424b0ab2cd3da2d0c58bdd2e306d13234a3e20c708c3ad3ef2324490003531ad03ca7f121b9eb0112f3801622822020abc438002460220d8a2634001100000000d96c8000000123282fe3e827c01d2881b346441101e42101f2f508bb8d0d13861b812e02941c25e1731522c195b3ca33600042800016e93ba17164293a8d3cf06200045cb950960a4120824457bd701b87a2b13e019300000008d0fc28c21013f0ffab03123f132f0e122845e3c60771688554091f70a6280194b14c423032370fdac80781603491d72fa14038717829d35a2c44033f814f14e2c0996c2545214d1c329a8e4046000042bd01d7a5c0002ab00017d1ea0004292be2e7b641160c22fba2b07f14bc1900022f1b228900000015f37b0df34216c32b1590f8255301bdc2409e72cec3d33c00034136b1c518337e0a10002ac0ed18c00029e4353500890094500f62d78bf2651943a100600f21e26a2211150fd08f3550003b429608f9ae80011227941b11a8000003ba2642093473bf24800030d1311fe33e3d60d80443ff44
  | 8 => 0x2b73710b700043909380024e1073b531583030f0a20908da1a21e039909012c33faa71fa0501de4434600000000000003243e31e83511760000000000001131b582582e3d200021f09d0000003730aa98d000261c5a8564133330e31050610163f529319a2af04942f96805f0af0000000000000020004240000000000663ad8002992bd0000c64331c631c337
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7658810026ef6558810006ee6558810006ed6558810026ec6558810026ef6358810006ee6358810006ed6358810026ec63588100276e50588100276c5058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ee4358810006ed4358810006ec435881002eef7158810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef3158810006ec315881002eef7058810026ee7058810026ec7058810006ef5058810026ee50588100266e5058810006ed5058810026ec50588100266c5058810006ef3058810026ee3058810026ec3058810026ee1058810026ec1058810004ff764c810024fe764c810004fd764c810024fc764c81000eee624c810006ed624c810005f7714c810005f4714c810084ff768c410024fe768c410014fd768c410024fc768c410016de638c410006dd638c41012eee628c410006ed628c410025fa708c410005f9708c410084ff764c410116ee624c410006ed624c41007cff7688410024fe768841000cfd7688410024fc768841000eee6288410006ed628841007ef66188410025fa7088410005f9708841007cff7648410005df7348410035dc734841000eee6248410006ed624841007ef66148410074ff764c0100057f754c01003d7c754c0100aeee624c010006ed624c01006cff76480100057f754801003d7c754801000eee6248010006ed624801003d7e75c40100057d75c401007eee62c4010006ed62c401007ef576c40101877675c40100077575c4010026f765c4010186f565c4010026f762c4010027e662c4010006f562c4010027e562c4010006e562c4010025f570c4010026f660c40100277650c40100277450c4010025f97684010026f9768401000cf97684010027ea6284010027e9628401017df97184010176fa6184010027f26184010004ff76440100057f754401003d7c7544010005df7344010035dc7344010005ef724401002dec7244010056ee6244010006ed62440100277a5044010027785044010025f77644010006f77644010004f7764401000777754401016f747544010026f7654401016ef56544010007d77344010007d47344010007e77244010007e47244010026f76244010027e66244010006f56244010027e56244010006e56244010025f77044010026f66044010027765044010027745044010027f22044010007f12044010005fb7644010006fb7644010004fb76440100077b754401016f787544010007db7344010007d87344010007eb7244010007e87244010007ea6244010007e96244010025fb7144010027f37144010166fa6144010007f26144010007f22144010007f12144010
  | 1 => 0x81100967c6548110006df634811008edc6348110006ef624811000eec6248110005f77148110005f47148110007e521481101a7785048110057e820481100657e75c41100057d75c41100067f65c411004e7c65c4110006df63c4110086dc63c4110006ef62c411007eec62c41100077a50c411019f7850c411019f7a75c41100077975c41100077b65c411019f7865c4110007db63c4110007d863c4110007eb62c4110007e862c411019ff251c411019ff151c4110007f221c4110007f121c41100067f65841100467c6584110006df6384110076dc6384110006ef628411006eec6284110055f67684110025f77584110195f5758411000777658411018f746584110007d76384110007d46384110025f77284110005f57284110007e76284110007e46284110007f36084110027765084110027745084110024ff75d8c1001cfe75d8c10004fd75d8c10024fc75d8c100c4fe74d8c10004fd74d8c10024fc74d8c10034fd73d8c1000cfe72d8c10026ee72d8c1000cee72d8c10004fd72d8c10026ed72d8c10004ed72d8c10024fc72d8c10084fe71d8c10026f671d8c10024fe70d8c10026fa70d8c100267e50d8c100267c50d8c10014ff7658c10026dc6358c10004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c100c4fe7458c100c4fc7458c10026df7358c10036de5358c10006dd5358c10036de4358c10004ff7258c1000cfe7258c1000cfc7258c10014ff7158c10014fd7158c10034fc7158c10036dc3158c10014ff7058c10024fe7058c10014fd7058c10024fc7058c100267e5058c100267c5058c10026de3058c10026dc3058c10004ff7650c10024fe7650c10004fd7650c10024fc7650c10016de6350c10006dd6350c100379c4350c10005ef7250c1002dec7250c10156ee6250c10005f77150c10005f47150c10024ff75d881001cfe75d8810004fd75d8810024fc75d8810014fe73d8810004fd73d8810024fc73d881002cfd72d881007cfe71d8810026f671d8810024fe70d8810026fa70d88100267e50d88100267c50d8810004ed7698810026ef6598810006ee6598810006ed6598810026ec6598810026ef6398810006ee6398810006ed6398810026ec6398810026ee60988100276e50988100276c509881000cff7658810026ec6258810004ff755881001cfe7558810004fd755881001cfc7558810004ff7358810014fe7358810014fc7358810026ef7258810006ef525881002eee5258810006ed525881002eec5258810006ef325881002eee325881002eec325881000cff715881000cfd715881002cfc715881002eec215881000cff7058810024fe705881000cfd7058810024fc70588100267e50588100267c5058810026ee2058810026ec2058810025ef765881002eef765881000ce
  | 2 => 0x66c6518910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910057e57118910007e65118910007e551189100076c5018910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91014e7c654c910006bf644c910146bc644c910006df634c910016dc634c910006ef624c91000eec624c910074fe768c5100067f658c51013e7c658c510006bf648c510136bc648c510006df638c510016dc638c510006ef628c51012eec628c510014fc764c5100067f654c5101267c654c510006bf644c51011ebc644c510006df634c510016dc634c510006ef624c510116ec624c510005fb704c510005f8704c51006cfe76885100067f658851010e7c6588510006df6388510106dc6388510006ef628851000eec6288510005f6768851006ef676885101c5f775885101c5f575885100077765885101bf746588510007d76388510007d46388510055f57288510007e7628851000ef6628851000ef46288510057e4628851000ee46288510057e652885101bfe55288510025f670885101bf745088510057e4208851000cfc76485100067f65485100fe7c6548510005df734851005ddc7348510006df63485100f6dc6348510006ef624851000eec6248510057e42148510005fb7048510005f87048510055f4764851000ef4764851000cf476485101b5f775485101b5f575485100077765485101af746548510007d77348510007d47348510007d76348510007d46348510055f77248510007e77248510007e7624851000ef6624851000ef46248510057e46248510007f37048510025f47048510007f070485101af745048510057e720485100057e76941100267e769411004c7e76941100067f63941100075f63941100065f63941100ee7e63941100067d63941100ee7c63941100075c63941100ee5c63941100067f62941100076f62941100066f62941100e67e62941100067d62941100e67c62941100076c62941100e66c62941100277771941100277471941100267f61941100077621941100077521941100257e70941100277a70941100267f6094110084fe768c1100067f658c1100de7c658c110006bf648c1100d6bc648c110006df638c110016dc638c110006ef628c1100ceec628c110014ff764c11005cfd764c110014fc764c1100057f754c1100657c754c1100067f654c1100be7c654c110006bf644c1100b6bc644c110006df634c110016dc634c110006ef624c1100aeec624c110005f7714c110005f4714c11007cfe76881100067f65881100a67c6588110006df638811009edc6388110006ef628811000eec6288110007e6218811002778508811000cff7648110054fd764811000cfc76481100057f75481100657c75481100067f654
  | 3 => 0xc7258d1000cec7258d10074ff7158d10006f77158d10084ff7058d10006fb7058d100067c5058d10005de7618d1005ede7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d10007d65118d10007d55118d100075c5018d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1015e7c6550d10006df6350d10016dc6350d1005f9c4350d10005ef7250d10055ec7250d10156ec6250d10005f77150d10005f47150d1000cfe76d89100067f65d89100067c65d8910006df63d8910006dc63d8910056ee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910014fe73d8910004fd73d8910014fc73d8910006ef52d8910056ee52d8910006ed52d8910056ec52d8910006ef32d8910056ee32d8910056ec32d891000cfe71d8910054fd71d891000cfc71d8910056ef21d8910024fe70d8910054fd70d8910024fc70d89100067c50d8910056ef20d8910055ee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e771d8910007e651d8910007e551d89100076c50d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910056ee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef31d8910006ec31d8910006ef70d8910056ee70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d89100066c50d8910006ef30d8910006ec30d89100057f75589100657c75589100067f65589100067c6558910005df735891005ddc7358910006df6358910006dc6358910056ec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc7358910054ff7258910006ef725891006cff7158910006f7715891007cff7058910006fb70589100067c5058910005ee7618910056ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c6518910
  | 4 => 0x95100067e63d95100067c63d95100067e62d95100067c62d95100077771d95100677471d95100257c70d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067c32d95100067f71d95100667e71d95100667d71d95100667c71d95100067f31d95100067c31d95100067f21d95100067c21d95100067f70d95100667e70d95100247e70d95100667d70d95100667c70d95100247c70d95100067f30d95100067c30d95100067f20d95100067c20d95100667d10d9510014fe76d8d100067f65d8d100067c65d8d1005ede63d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d100c4fe74d8d10004fd74d8d100c4fc74d8d10006df53d8d1005ede53d8d10006dd53d8d1005edc53d8d10006df43d8d1005ede43d8d1005edc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d1005edf32d8d10006de32d8d1005edc32d8d10014fe71d8d1005cfd71d8d10014fc71d8d1005edf31d8d10024fe70d8d1005cfd70d8d10024fc70d8d100067c50d8d1005edf30d8d1005dde76d8d10014de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dc64d8d10006de62d8d10006dc62d8d10007d651d8d10007d551d8d100075c50d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d10006df71d8d1005ede71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d1005ede70d8d10006dd70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d100065c50d8d10006df40d8d10006dc40d8d10006df20d8d10006dc20d8d100057f7558d100657c7558d100067f6558d100067c6558d10005bf7458d101cdbc7458d10006bf6458d1005edc6358d10005ef7258d10055ec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d100c4fe7458d100c4fc7458d10006bc7458d100c4bc7458d1005cff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006e
  | 5 => 0x4d7c754c3100be7e654c3100067d654c310016de634c310006dd634c310005f7714c310005f4714c310054fd76883100a67e65883100067d6588310006ef628831000eec6288310007e6218831000cff764831000cfc76483100057f754831004d7c75483100967e65483100067d654831000eee6248310006ed6248310005f77148310005f47148310007e52148310024ff75d8e1001cfe75d8e10004fd75d8e10024fc75d8e100c4fe74d8e10004fd74d8e10024fc74d8e10074fd73d8e1000cfe72d8e10004fd72d8e10024fc72d8e10026f571d8e10076dc31d8e10026fa70d8e100267e50d8e100267c50d8e10014ff7658e10026dc6358e10004ff7558e1001cfe7558e10004fd7558e1001cfc7558e10004ff7458e100c4fe7458e100c4fc7458e10026df7358e10076de5358e10006dd5358e10076de4358e10004ff7258e1000cfe7258e1000cfc7258e10006de3258e10076dc3258e10076df3158e100267e5058e100267c5058e10026de3058e10026dc3058e10004ff7650e10024fe7650e10004fd7650e10024fc7650e10016de6350e10006dd6350e100779c4350e10005ef7250e1006dec7250e10005f77150e10005f47150e10024ff75d8a1001cfe75d8a10004fd75d8a10024fc75d8a10014fe73d8a10026de73d8a10014de73d8a10004fd73d8a10026dd73d8a10004dd73d8a10024fc73d8a1006cfd72d8a10026f571d8a1006eec21d8a10026fa70d8a100267e50d8a100267c50d8a10026ef20d8a1000cff7658a10026ec6258a10004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7358a10014fe7358a10014fc7358a10026ef7258a1006eee5258a10006ed5258a1006eef2158a100267e5058a100267c5058a10026ee2058a10026ec2058a10004ff764ca10024fe764ca10004fd764ca10024fc764ca10005f7714ca10005f4714ca1005cfd768c610006df638c610016dc638c610014ff764c610024fc764c610016de634c610006dd634c610005fb704c610025f8704c610054fd7688610006ef628861000eec628861000cff7648610024fc7648610005df7348610075dc734861000eee6248610006ed6248610005fb7048610025f87048610034ff764c2100057f754c2100457c754c21002cff76482100057f75482100457c7548210026ef6248210026ec6248210027785048210027e820482100457e75c42100057d75c42100277a50c42100277850c4210025f576c4210006f576c42101d77675c42100077575c4210026f765c42101d6f565c4210026f762c4210006f562c42100277650c4210027f250c42100277250c42101d7f150c42100277450c4210005f976c4210006f976c42101d77a75c42100077975c42101d7f251c42101d7f151c42100657e76d95100667e76d951001c7e76d
  | 6 => 0xe53d8f10006dd53d8f10086de43d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006f671d8f10006f970d8f100067c50d8f10086dc30d8f10014ff7658f100067e6558f100067d6558f10086dc6358f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f100c4fe7458f100c4fc7458f10006df7358f10004ff7258f1000cfe7258f1000cfc7258f10086dc3158f100067c5058f10086df3058f10004ff7650f10004fe7650f10004fd7650f10004fc7650f1015e7e6550f100067d6550f10006df6350f10016dc6350f100879c4350f10005ef7250f1007dec7250f10005f77150f10005f47150f1004d7e75d8b100057d75d8b100067e65d8b100067d65d8b1007eee62d8b10004ff75d8b1001cfe75d8b100067e75d8b1001c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfc75d8b10014fe73d8b10004fd73d8b10014fc73d8b1007cfd72d8b1007eee52d8b10006ed52d8b10006f671d8b1007eef21d8b10006f970d8b100067c50d8b1007eec20d8b1000cff7658b100067e6558b100067d6558b1007eec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7358b10014fe7358b10014fc7358b10006ef7258b1007eec2158b100067c5058b1007eef2058b10004ff764cb10004fe764cb10004fd764cb10004fc764cb1014e7e654cb100067d654cb10014fd768c71013e7e658c7100067d658c710016de638c710006dd638c710005fa708c710005f9708c710034ff764c7101267e654c7100067d654c71000cfd768871010e7e65887100067d658871000eee6288710006ed6288710005fa7088710005f9708871007df5768871000ef5768871000cf576887101f5f775887101f5f575887101ef76658871000775658871000ef6628871007fe66288710007e5628871000ef4628871007fe652887101efe55288710025f67088710007f27088710007f170887101ef74508871007fe4208871002cff76487100fe7e65487100067d6548710005df7348710085dc7348710006ef624871000eec624871007fe42148710005f7764871002ef776487101e5f775487101e5f575487101df766548710007756548710007d77348710007d47348710007e77248710007e7624871000ef6624871000ef4624871007fe46248710025f470487101df74504871007fe720487100057d76943100267d76943100647d76943100067f63943100ee7e63943100067d63943100ee7c63943100067f62943100e67e62943100067d62943100e67c62943100277771943100277471943100267e61943100077621943100077521943100257e70943100277a709431005cfd768c3100de7e658c3100067d658c310006df638c310016dc638c310014ff764c310014fc764c3100057f754c310
  | 7 => 0x852006ef521d85200067c50d85200957e75985200057d75985200067f65985200067c6598520006f76198520055f970985200057f75585200957c75585200067f65585200067c6558520005df735852008ddc735852007dfb70585200067f65185200067c6518520006f56118520004ff751852001cfe7518520004fd751852001cfc7518520014fe7318520004fd7318520014fc731852002eee5218520006ed5218520006f73118520006f4311852002eef211852002ef6211852002ef521185200067c501852002eec2018520004fe768c520004fd768c520004fc768c5200067f658c52013e7c658c520006df638c520016dc638c52000dee728c520005ed728c520004ff764c520004fe764c520004fc764c5200067f654c5201267c654c520225ef7548520225ed75485200076f654852021f6c6548520007cf7348520007cc734852000def714852000fe77148520007e76148520006ec6148520007e46148520007eb7048520025ec7048520007e8704852000eef604852000feb604852021f6c50485202157e76941200267e76941202147e76941200067f63941200ee7e63941200067d63941200ee7c63941200276f72941200276c72941200267f62941200067f61941200067c61941200e76f21941200076d21941200257e70941200277a70941200267f60941200e77b20941200276c209412002778209412020cfe768c1200067f658c1200de7c658c120027e8208c120014ff764c12000cfe764c1200acfd764c12000cfc764c1200057f754c1200957c754c1200067f654c1200be7c654c120006df634c120016dc634c120005ef724c12000dec724c1200afe8204c120025ef7588120205ed75881200076f65881201ff6c6588120005ed7188120006ec6188120025ee7088120027ea7088120026ef608812000feb60881200276e50881200276c508812004d7f765971004e7f765971001c7f76597100067e63597100067c63597100067e62597100067c625971000776715971004f7571597100067f73597100067e73597100067d73597100067c73597100067e43597100067c43597100067f72597100067e72597100067d72597100067c72597100067f32597100067e32597100067c325971004e7f71597100067e715971004e7d715971004e7c71597100067f31597100067c31597100067f21597100067c215971004e7f705971004e7e70597100067d705971004e7c70597100067f30597100067c30597100067f20597100067c205971004e7f105971004d7e75d8f100057d75d8f100067e65d8f100067d65d8f10086de63d8f10004ff75d8f1001cfe75d8f100067e75d8f1001c7e75d8f10004fd75d8f100067d75d8f100047d75d8f1001cfc75d8f100c4fe74d8f10004fd74d8f100c4fc74d8f10084fd73d8f10086d
  | 8 => 0x56f62158620056f52158620056ec2158620024fc70586200267e50586200267c5058620056ef2058620026f61058620026f41058620004ff768c620024fe768c620004fd768c620016de638c620006dd638c620004ff764c620004fd764c620024fc764c620005ef724c62000dec724c620246ef6588620246ed658862000dee718862000fe67188620007e66188620006ed6188620007e56188620007ea7088620005ed7088620007e9708862000eee608862000fea608862023f6e508862023f6c508862022cff764c2200057f754c2200a57c754c2202157e76d95200967e76d952001c7e76d95200067e63d95200067c63d95200076f72d95200e76c72d95200e76f21d95200257c70d95200e77b20d95200e76c20d95200e77820d95200067f73d95200067e73d95200067d73d95200067c73d95200067e43d95200067c43d95200e67f72d95200e67e72d95200e67d72d95200e67c72d95200e67f32d95200e67e32d95200e67d32d95200e67c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067c31d95200e67f21d95200e67e21d95200e67d21d95200e67c21d95200e67f70d95200967e70d95200e67d70d95200e67c70d95200067f30d95200067c30d95200e67f20d95200e67e20d95200e67d20d95200e67c20d9520014fe76d8d200067f65d8d200067c65d8d2008ede63d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d200c4fe74d8d20004fd74d8d200c4fc74d8d20006df43d8d2008edc43d8d20024ff72d8d2000cfe72d8d200ccfd72d8d2000cfc72d8d200cedf32d8d200cedd32d8d20004fe71d8d20004fd71d8d2008edc31d8d2000cfd70d8d200067c50d8d2008edf30d8d200057f7558d200957c7558d200067f6558d200067c6558d20005bf7458d20235bc7458d2008edc6358d20005f77158d20005f47158d2022dfb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d200c4fe7458d200c4fc7458d20006bc7458d200c4bc7458d200ccff7358d20006df7358d2008ede4358d200acff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d2022cff7058d20006fb7058d200067c5058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d2015e7c6550d20016de6350d20006dd6350d2008f9c4350d20005ef7250d2000dec7250d20005f77150d20005f47150d200067f65d85200067c65d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520014fe73d8520004fd73d8520014fc73d8520006f731d8520006f431d852006ef621d
  | 9 => 0xd74185300c4fc7418530036de5318530006dd5318530036de4318530006dd431853000cfe7218530004fd721853000cfc7218530006f74118530006f44118530036f63118530036f53118530006f72118530006f421185300067c5018530036dc3018530004fe7690530004fd7690530004fc76905300067f65905302967c6590530006bf64905300c6bc64905300079d4390530004ff7650530004fe7650530004fc76505300067f655053028e7c6550530004fe7688530004fd7688530004fc76885300067f658853010e7c6588530006ef628853000eec6288530004ff7648530004fe7648530004fc76485300067f65485300fe7c6548530005bf74485300b5bc7448530005df7348530015dc73485302857e76941300267e76941302847e76941300067f649413027e7e64941300067d649413027e7c64941300275f73941300275c73941300267f63941300ef5e43941300075d43941300067f62941300e67e62941300e67c62941300067f61941300067c61941300257e70941300277a70941300267f60941300ef7b30941300275c3094130027783094130274fe76901300067f659013026e7c6590130025dc7390130014fe7650130264fd7650130014fc76501300067f655013025e7c6550130005df7350130015dc73501300079d4350130025df758c130255dd758c1300075f658c13024f5c658c130025df748c130005dd748c130006dc618c130025de708c130027da708c130026df608c130017db608c1300275e508c1300275c508c130024ff75d8e2001cfe75d8e20004fd75d8e20024fc75d8e200c4fe74d8e20004fd74d8e20024fc74d8e200acfd73d8e20026ed72d8e20004fe71d8e20004fd71d8e20024fe70d8e20026fa70d8e200267e50d8e200267c50d8e20014ff7658e20026dc6358e20004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e200c4fe7458e200c4fc7458e20026df7358e2009ede5358e20006dd5358e2009ede4358e200aedf3258e200aedd3258e20004ff7158e20004fc7158e2009edc3158e20024fe7058e20024fc7058e200267e5058e200267c5058e20026de3058e20026dc3058e20004ff7650e20024fe7650e20004fd7650e20024fc7650e20016de6350e20006dd6350e2009f9c4350e20005ef7250e2000dec7250e20005f77150e20005f47150e20026f76198620004ff759862001cfe7598620004fd759862001cfc7598620014fe7398620004fd7398620014fc7398620006f65198620006f5519862007ef6219862007ef52198620024fe70986200267e50986200267c5098620026f61098620026f41098620026f46158620004ff755862001cfe7558620004fd755862001cfc7558620004ff7358620014fe7358620014fc7358620006f65158620006f55158620
  | 10 => 0x95300c4fe76d91300067f65d91300067c65d91300b6be64d9130004ff75d913001cfe75d9130004fd75d913001cfc75d9130024ff73d9130014fe73d91302c4fd73d9130014fc73d91302c6bf43d91302c6bd43d913000cfe72d9130004fd72d913000cfc72d9130006be42d91300b6bc42d9130004fe71d9130004fd71d91300b6bc41d9130014fd70d91300067c50d91300b6bf40d91300057f75591300bd7c75591300067f65591300067c65591300b6bc6459130005ef72591300adec7259130005f77159130005f471591302bdfb7059130004ff75591300067f75591300047f755913001cfe7559130004fd755913001cfc75591300067c755913001c7c7559130264ff7359130006df7359130004ff7259130006ef7259130004ef725913000cfe725913000cfc7259130006ec725913000cec7259130004ff7159130006f77159130004f77159130004fc7159130006f47159130004f471591302bcff7059130006fb70591300067c50591300b5dc7650d300c6dc7650d300c4dc7650d302b5df7550d302b5dd7550d300075f6550d302af5c6550d30015df7450d300179f7450d300079f6450d300c6de6450d300c6dc6450d300b79c6450d300c69c6450d30007cf7250d30007cc7250d300b79f4250d30007d77150d30007d47150d300b79c4150d30007db7050d30025dc7050d30007d87050d30016df6050d30017db6050d302af5c5050d300b79f4050d3000cfe76d89300067f65d89300067c65d89300aeee62d8930004ff75d893001cfe75d8930004fd75d893001cfc75d89300c4fe74d8930004fd74d89300c4fc74d893000cfc73d893009ede43d8930006dd43d8930006ef42d89300aeec42d89300aeee32d893009eed32d8930004fe71d8930004fd71d89300aeec21d8930014fd70d89300067c50d89300aeef20d89300057f75589300bd7c75589300067f65589300067c6558930005bf74589300b5bc74589300aeec6258930005f77158930005f471589302a5fb7058930004ff7650930004fe7650930004fc76509300067f655093029e7c65509300079d43509300067f65d85300067c65d8530004ff75d853001cfe75d8530004fd75d853001cfc75d85300c4fe74d8530004fd74d85300c4fc74d853000cfe72d8530004fd72d853000cfc72d8530006f741d8530006f441d8530076f631d8530076f531d8530006f721d8530006f421d85300067c50d85300bd7e75985300057d75985300067f65985300067c6598530006f7619853005df970985300057f75585300bd7c75585300067f65585300067c6558530005bf74585300b5bc7458530005ef72585300adec7258530085fb70585300067f65185300067c6518530006f56118530004ff751853001cfe7518530004fd751853001cfc75185300c4fe7418530004f
  | 11 => 0x24fc7058a300267e5058a300267c5058a30026ee2058a30026ec2058a30004ff7650a30004fd7650a30024fc7650a30005df7350a30015dc7350a300dd7e75986300057d7598630026f76198630004ff759863001cfe75986300067e759863001c7e7598630004fd75986300067d75986300047d759863001cfc75986300c4fe7498630004fd74986300c4fc749863000cfe7298630004fd729863000cfc7298630006f65198630006f55198630006f74198630006f44198630086f63198630086f53198630024fe70986300267e50986300267c5098630026f61098630026f41098630005bf74586300d5bc7458630026f46158630004ff755863001cfe7558630004fd755863001cfc7558630004ff7458630006bf7458630004bf74586300c4fe74586300c4fc7458630006bc74586300c4bc7458630004ff725863000cfe725863000cfc7258630006f65158630006f55158630006f74158630006f4415863005ef6315863005ef5315863005edc3158630024fc70586300267e50586300267c5058630026f61058630026f41058630004ff7690630024fe7690630004fd76906300c6bc6490630004ff7650630004fd7650630024fc7650630005df7350630015dc73506302d6df658c6302d6dd658c630006df648c630006dd648c63012ede628c63012edc628c630015de718c630017d6718c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c630016de608c630017da608c6302cf5e508c6302cf5c508c630004ff7688630024fe7688630004fd7688630006f66188630006f56188630004ff7648630004fd7648630024fc7648630005bf74486300d5bc7448630005df7348630015dc734863000eee6248630006ed6248630006f66148630006f561486302857e76d95300be7e76d953001c7e76d95300067e64d95300067c64d95300075f73d95300ef5c73d95300ef5e43d95300067e62d95300067c62d95300257c70d95300ef7b30d95300ef5c30d95300ef7830d95300067f74d95300067e74d95300067d74d95300067c74d95300ee7f73d95300ee7e73d95300ee7d73d95300ee7c73d95300ee7f43d95300ee7e43d95300ee7d43d95300ee7c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067c42d95300ee7f32d95300ee7e32d95300ee7d32d95300ee7c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067c41d95300ee7f31d95300ee7e31d95300ee7d31d95300ee7c31d95300067f21d95300067c21d95300ee7f70d95300be7e70d95300ee7d70d95300ee7c70d95300067f40d95300067c40d95300ee7f30d95300ee7e30d95300ee7d30d95300ee7c30d95300067f20d95300067c20d
  | 12 => 0xc61586500277461586500257e70586500257c70586500267e60586500277a60586500277610586500277410586500057f768c6500257e768c6500057d768c6500257c768c6500057f748c65027d7e748c6500057d748c65027d7c748c6500ed7d738c6502cf5f638c6502cf5c638c6500ef5e438c6500075d438c6500e57e728c6500057d728c6500e57c728c6502df5e328c6500ef5c328c6500ed7e718c6500ef5f318c6500ef77318c6500ef74318c6500257e708c6500057d708c6502867e608c65013f7a608c6502cf5c308c6500057f764c6500257e764c6500057d764c6500257c764c6500057f744c65027d7e744c6500057d744c65027d7c744c6500ed7f734c6500057f724c6500e57e724c6500e57c724c6500ed7f714c6500ef77314c6500075e314c6500ef5c314c6500ef74314c6500057f704c6500257c704c6502867e604c6501277a604c6500057f76886500257e76886500057d76886500257c76886500057f73886500ed7e73886500057d73886500ed7c73886500e57d728865023f6f628865023f6c62886500e57e71886500077661886500077561886500e76f21886500e77721886500e77421886500257e70886500057d70886502167e608865010f7a608865023f6c20886500057f76486500257e76486500057d76486500257c76486500057f73486500075f73486500055f73486500ed7e73486500057d73486500ed7c73486500075c73486500ed5c73486500e57f72486500e76e62486500076d62486500e57f71486500077661486500077561486500e77721486500076e21486500e76c21486500e77421486500057f70486500257c70486502167e60486500ff7a60486500e76f2048650024ff75d923001cfe75d9230004fd75d9230024fc75d923000cfe72d9230026ee72d923000cee72d9230004fd72d9230026ed72d9230004ed72d9230024fc72d9230004fe71d9230026f671d9230004f671d9230004fd71d9230026f571d9230004f571d92302c6dc31d9230024fe70d9230026fa70d92300267e50d92300267c50d9230026df30d92300c4ff7659230026bc6459230004ff755923001cfe7559230004fd755923001cfc7559230026bf74592300d6be5459230006bd5459230266bf4359230266bd4359230004ff725923000cfe725923000cfc7259230004ff7159230004fc7159230266dc3159230024fe7059230024fc70592300267e50592300267c5059230026be4059230026bc4059230266df305923000cff7658a30026ec6258a30004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a300c4fe7458a300c4fc7458a300ceee5258a30006ed5258a30006ef4258a300ceec4258a300ceee3258a3008eed3258a30004ff7158a30004fc7158a300ceef2158a30024fe7058a30
  | 13 => 0x81210067c50d8121006f850d81210067850d812107efa20d81210f5de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581210fd7c7558121005df73581210f5dc7358121006df6358121006dc6358121006df6318121006dc6318121006f96018121007785018121024ff751812101cfe7518121004fd7518121024fc7518121014fe7318121004fd7318121024fc7318121026f57118121006ee211812102eec2118121006fb50181210267c5018121026f85018121026785018121026ef2018121026fa201812102ef920181210257f7658e500057f7458e5027d7e7458e5027d7c7458e500257f7358e500275f6358e500ee7e6358e500267c6358e500275c6358e500265c6358e500ef5e4358e500057f7258e500e57e7258e500e57c7258e500267f6258e500057f7158e500057c7158e500267f6158e500257e7058e500257c7058e500267e6058e500277a6058e500275e3058e500275c3058e500057f7650e500257e7650e500057d7650e500257c7650e500ed7f7350e500ef5e6350e500075d6350e500ef3e4350e500ef5c4350e500ef1c4350e500057f7250e500076f7250e500056f7250e500e57e7250e500e57c7250e500076c7250e500e56c7250e500ef5f3250e500057f7150e50007777150e50005777150e500057c7150e50007747150e50005747150e500ef5c3150e500057f7050e500257c7050e502867e6050e5015f7a6050e500ef5f3050e500257f7658a500057f7358a500ed7e7358a500ed7c7358a500267f6358a500067d6358a500257f7258a500276f6258a500e67e6258a500267c6258a500276c6258a500266c6258a500057f7158a500057c7158a500e76f2158a500257e7058a500257c7058a500267e6058a500277a6058a500276e2058a500276c2058a500057f764ca500257e764ca500057d764ca500257c764ca500057f744ca5027d7e744ca500057d744ca5027d7c744ca500e57f734ca500ef5e434ca500075d434ca500e57f724ca500ef6f324ca500e75e324ca500e75c324ca500e76c324ca500057f714ca500057c714ca500057f704ca500257c704ca502167e604ca5014f7a604ca500257d76986500ed7e73986500057d73986500ed7c73986500e57e72986500057d72986500e57c72986500257e71986500267f61986500277761986500277461986500257e70986500257c70986500267e60986500277a60986500277610986500277410986500257f76586500057f73586500075f73586500055f73586500ed7e73586500ed7c73586500075c73586500ed5c73586500267f63586500067d63586500057f72586500076f72586500056f72586500e57e72586500e57c72586500076c72586500e56c72586500257f71586500277761586500067e61586500267
  | 14 => 0xf6df30d8d210f6dc30d8d212edde76d8d21014de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d210079f64d8d210069f64d8d21006de64d8d21006dc64d8d2112fd721d8d2112fcc21d8d2112fd421d8d210075c50d8d2112fcf20d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d2112edf72d8d2112ede72d8d2112edd72d8d2112edc72d8d2112edf52d8d2112ede52d8d2112edd52d8d2112edc52d8d2112edf42d8d2112ede42d8d2112edd42d8d2112edc42d8d2112edf71d8d210f6de71d8d2112edd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21006df41d8d21006dc41d8d2112edf21d8d2112ede21d8d2112edc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d210065c50d8d21006df40d8d21006dc40d8d2112edf20d8d2112ede20d8d2112edd20d8d2112edc20d8d21005bf7458d212fdbc7458d21006bf6458d210f6dc6358d212f5f77158d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21006bf7458d21004bf7458d210c4fe7458d210c4fc7458d21006bc7458d210c4bc7458d2112cff7358d21006df7358d21114ff7258d21006ef7258d212f4ff7158d21006f77158d21004ff7058d21024fc7058d210067c5058d2112dde7618d210f6de7618d2112cde7618d210f75e7518d210f75d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d210079f6418d210069f6418d21006de6418d21006dd6418d21006dc6418d210079c6418d210069c6418d212eedf6218d212eedf6118d212efd72118d212efcc2118d212efd42118d210075c5018d212efcf2018d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d21016dc6350d210f79c4350d21005ef7250d2100dec7250d21005f77150d21005f47150d212ecfe768c521006bf648c521136bc648c52112edf638c521016dc638c521014ff764c52100cfe764c521114fd764c52100cfc764c521006bf644c52111ebc644c521006df634c521016dc634c521005ef724c52100dec724c5212e6ef65885212e6ed6588521007cf6388521007cc638852100dee718852100fe6718852100eef618852100fe76188521005ed70885212e76c50885210fd7e75d81210057d75d8121006df63d8121006dc63d81210077850d8121004ff75d812101cfe75d81210067e75d812101c7e75d8121004fd75d81210067d75d81210047d75d812101cfc75d8121014fe73d8121004fd73d8121014fc73d8121006fb50d
  | 15 => 0xe765053130cfd7650531014fc7650531005df7350531015dc7350531306df658c531306dd658c531006df648c531006dd648c53112ede628c53112edc628c531015de718c531017d6718c531016df618c531017d7618c5313075c508c5311257e75d81310057d75d8131004ff75d813101cfe75d81310067e75d813101c7e75d8131004fd75d81310067d75d81310047d75d813101cfc75d81310c4fe74d8131004fd74d81310c4fc74d813100cfe72d8131004fd72d813100cfc72d81310067c50d8131086fa30d8131006fb60981310057f75581311257c7558131005bf745813111dbc7458131005ef7258131115ec7258131006f96018131024ff751813101cfe7518131004fd7518131024fc75181310c4fe7418131004fd7418131024fc741813100cfe7218131004fd7218131024fc7218131006de3118131036dc31181310267c5018131026fa3018131036f93018131106de63d8e212edf671d8e21004ff75d8e2101cfe75d8e21004fd75d8e2101cfc75d8e210c4fe74d8e21004fd74d8e210c4fc74d8e21114fd73d8e21106de43d8e21006ed72d8e2112ede32d8e2112edc32d8e212ecfe71d8e21006f671d8e21024fe70d8e21004fd70d8e210067c50d8e21014ff7658e21106dc6358e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e210c4fe7458e210c4fc7458e21006df7358e21116df3258e21116dd3258e2100cfc7158e21106dc3158e21004ff7058e21024fc7058e210067c5058e21004ff7650e21004fe7650e21004fd7650e21004fc7650e21006df6350e21016dc6350e211079c4350e21005ef7250e2100dec7250e21005f77150e21005f47150e2100cff768c621014fe768c62100cfd768c621016de638c621006dd638c62100dee728c621005ed728c6212f4ff764c62110d7e75d82210057d75d8221006fb6098221024ff759822101cfe7598221004fd7598221024fc7598221014fe7398221004fd7398221024fc7398221026f671982210267c5098221026fa209822106ef920982210057f755822110d7c7558221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7358221014fe7358221014fc7358221056ee5258221006ed5258221056ef21582210067c5058221056fa2058221056ec2058221006f96018221014fe76d8d210f6de63d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d210c4fe74d8d21004fd74d8d210c4fc74d8d21006df53d8d210f6de53d8d21006dd53d8d210f6dc53d8d21006df43d8d210f6de43d8d210f6dc43d8d2112cff72d8d2112cfd72d8d2112edf32d8d2112edd32d8d2100cfd71d8d210f6df31d8d21024fe70d8d21004fd70d8d210067c50d8d21
  | 16 => 0xe31007cc7250e3112dcc7250e311379f4250e31005df7150e31007d77150e31007d47150e31016de6150e31017d66150e311379c4150e31005dc7050e3133f5c5050e311379f4050e3112eee62d8a31335f671d8a3100cff7658a31015dc7358a3112eec6258a3112fce3258a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a310c4fe7458a310c4fc7458a310f6de4358a31006dd4358a31006ef4258a3112eec4258a3112ede3258a3112eee3258a310f6ed3258a3112edc3258a31014fc7158a3112eec2158a31004ff7058a31024fc7058a310067c5058a3112eef2058a31004ff7650a31004fd7650a31004fc7650a31005df7350a31015dc7350a310079d4350a310c4fe7690631014fd7690631015de7390631005dd73906310079d439063113d7e75d82310057d75d8231006fb6098231024ff759823101cfe7598231004fd7598231024fc75982310c4fe7498231004fd7498231024fc749823100cfe7298231004fd7298231024fc72982310267c5098231026fa3098231076f930982310057f755823113d7c7558231004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff74582310c4fe74582310c4fc745823105ede5358231006dd535823105ede4358231006dd4358231004ff725823100cfe725823100cfc72582310067c505823105efa305823105edc305823112dee7218231005ed7218231006f960182310c4fe76d913111ebe64d9131004ff75d913101cfe75d9131004fd75d913101cfc75d913111ebe54d9131006bd54d913132cff73d913132cfd73d913132ebf43d913132ebd43d913100cfe72d9131004fd72d913100cfc72d9131006be42d913111ebc42d9131014fd71d913111ebf41d913132edc31d9131024fe70d9131004fd70d91310067c50d913111ebc40d913111ebc6459131005ef7259131115ec7259131325f77159131004ff755913101cfe7559131004fd755913101cfc755913130cff7359131006df7359131004ff7259131006ef7259131004ef725913100cfe725913100cfc7259131006ec725913100cec7259131324ff7159131006f77159131324f7715913130edc3159131004ff7059131024fc70591310067c505913100cfe76d8931116ee62d8931004ff75d893101cfe75d8931004fd75d893101cfc75d89310c4fe74d8931004fd74d89310c4fc74d8931116ee52d8931006ed52d8931006ef42d8931116ec42d8931116ee32d8931106ed32d8931014fd71d8931116ef21d8931024fe70d8931004fd70d89310067c50d8931116ec20d8931005bf745893111dbc7458931116ec625893131df77158931004ff7650931004fe7650931004fc7650931314fe76905310c6be6490531014f
  | 17 => 0x6f47159132004f47159132004ff7059132024fc70591320067c505913200ddc7650d320c6dc7650d3200cdc7650d32015df7450d320179f7450d320079f6450d320c6de6450d320c6dc6450d321479c6450d320c69c6450d32007cf7250d3200dde7250d3200ddc7250d32157cc7250d32016df6250d32017cf6250d321579f4250d321579d4250d32007d77150d32007d47150d321479c4150d323575c5050d321479f4050d32004ff75d853201cfe75d8532004fd75d853201cfc75d85320c4fe74d8532004fd74d85320c4fc74d853200cfd73d8532014fd72d8532006f651d8532006f551d8532006f741d8532006f441d853231ef631d85322f6f621d8532024fe70d8532004fd70d85320067c50d8532006f76198532005bf7458532145bc7458532006f56118532004ff751853201cfe7518532004fd751853201cfc75185320c4fe7418532004fd74185320c4fc741853200cfd7318532336de4318532006dd4318532014fd72185322eede32185322eedc3218532006f65118532006f55118532006f74118532006f44118532336f531185322eef52118532024fe7018532004fd70185320067c501853214d7e75d81320057d75d8132004ff75d813201cfe75d81320067e75d813201c7e75d8132004fd75d81320067d75d81320047d75d813201cfc75d81320c4fe74d8132004fd74d81320c4fc74d813200cfd73d81322a6de43d8132006dd43d8132014fd72d8132004fe71d8132004fd71d81320067c50d81322a6fa30d813222efa20d8132006fb60981320057f755813214d7c7558132005bf7458132145bc7458132005f77158132005f47158132006f96018132024ff751813201cfe7518132004fd7518132024fc75181320c4fe7418132004fd7418132024fc741813200cfd7318132014fd7218132004fe7118132004fd71181320267c5018132026fa301813234ef93018132026fa201813220ef92018132136be64d923112dee72d9231005ed72d9231315f671d9231004ff75d923101cfe75d9231004fd75d923101cfc75d923100cfe72d9231006ee72d923100cee72d9231004fd72d9231006ed72d9231004ed72d923100cfc72d9231314fe71d9231006f671d9231314f671d9231024fe70d9231004fd70d92310067c50d92310c4ff7659231136bc6459231004ff755923101cfe7559231004fd755923101cfc7559231006bf745923130ebf435923130ebd4359231004ff725923100cfe725923100cfc7259231014fc7159231136bc4159231004ff7059231024fc70592310067c5059231135df7650e310c6df7650e310c4df7650e31345df7550e31345dd7550e31015df7450e310179f7450e310c6de6450e311379e6450e310c69e6450e310079d6450e310c6dc6450e31007cf7250e3112dde7250e3112ddc725
  | 18 => 0x44318543006f76218543007e76218543006e76218543006f66218543006f56218543006f46218543007e46218543006e46218543317d73218543007745018543317d73018543006f77518543006f67518543006767518543006f57518543006757518543006f47518543316f77318543316f67318543316f57318543316f47318543316f75318543316f65318543316f55318543316f45318543316f64318543316f54318543316f44318543006f77218543006f67218543006f57218543006f47218543006f75218543006f65218543006f55218543006f45218543316f73218543316f63218543316f53218543316f43218543006f77018543006f67018543006f57018543006f47018543006f75018543006f65018543006f55018543006f45018543006745018543316f73018543316f63018543316f53018543316f43018543006f72018543006f4201854315d7e75d81430057d75d81432bf9c43d8143006ef62d8143006ec62d8143006f761d8143006f461d81430077850d8143004ff75d814301cfe75d81430067e75d814301c7e75d8143004fd75d81430067d75d81430047d75d814301cfc75d81430c4fd73d814300cfe72d8143004fd72d814300cfc72d8143004fe71d8143004fd71d8143006fb50d81430067c50d8143006f850d81430067850d81432befa30d81432c79c4398143155ee7298143005ed7298143006ef6298143006ec6298143005f67198143005f57198143006f76198143006f46198143006fb60981430057f755814315d7c75581432679c4358143005ef7258143155ec7258143006ef6258143006ec6258143005f77158143005f47158143006f76158143006f461581432779c4318143006ef6218143006ec6218143006f76118143006f46118143006f96018143007785018143024ff751814301cfe7518143004fd7518143024fc75181430c4fd7318143026dd731814300cfe7218143004fd7218143024fc7218143004fe7118143004fd7118143276dc3118143006fb50181430267c5018143026f85018143026785018143026df3018143026fa3018143276f930181430c4fe76d9132146be64d9132004ff75d913201cfe75d9132004fd75d913201cfc75d9132154fd74d9132146be54d9132006bd54d913200cff73d913200cfd73d9132376bf43d9132376bd43d9132014fd72d913236ebf42d9132004fe71d9132004fd71d9132146bc41d9132024fe70d9132004fd70d91320067c50d9132146bc40d91320c4ff7659132146bc6459132365df735913235def7259132005f77159132005f47159132004ff755913201cfe7559132004fd755913201cfc7559132364ff7359132006df7359132154ff7259132006ef725913235cef7259132004ff7159132006f77159132004f77159132004fc7159132
  | 19 => 0x8943006ee70d8943006ed70d8943006ec70d8943006ef50d8943006ee50d8943006ed50d8943006ec50d89430066c50d894335eef30d894335eee30d894335eed30d894335eec30d89433979c4358943156ec6258943005f77158943005f4715894335dee7618943156ee76189431576e75189431576d7518943006ef6518943006ee6518943006ed6518943006ec6518943157ce7318943157cd7318943366ef631894338fae431894338fcc431894338f8c431894338fcc31189430076c501894338fcf30189433279c43d8543006ef62d8543006ec62d8543004ff75d854301cfe75d8543004fd75d854301cfc75d85430c4fd73d8543386dd73d854300cfe72d8543004fd72d854300cfc72d8543006f751d8543006f651d8543006f551d8543006f451d8543326f631d8543326dc31d8543006f721d8543006f421d8543024fe70d8543004fd70d85430067c50d8543006f765d8543006f665d8543006f565d8543006f465d8543327d673d8543387d573d8543327b643d8543327d443d85433279443d8543006f762d8543007e762d8543006e762d8543006f662d8543006f562d8543006f462d8543007e462d8543006e462d8543327d732d85430077450d8543327d730d8543006f775d8543006f675d8543006f575d8543006f475d8543326f773d8543326f673d8543326d673d8543326f573d8543386d573d8543326f473d8543326f753d8543326f653d8543326f553d8543326f453d8543326f643d8543326f443d8543006f772d8543006f672d8543006f572d8543006f472d8543006f752d8543006f652d8543006f552d8543006f452d8543326f732d8543326f632d8543326f532d8543326f432d8543006f770d8543006f670d8543006f570d8543006f470d8543006f750d8543006f650d8543006f550d8543006f450d85430067450d8543326f730d8543326f630d8543326f530d8543326f430d8543006f720d8543006f420d854332f9c4398543155ee7298543005ed7298543006ef6298543006ec6298543006f7619854330f9c4358543005ef7258543155ec7258543006ef6258543006ec625854315d7e75185430057d75185433179c4318543006ef6218543006ec6218543006f56118543004ff751854301cfe75185430067e751854301c7e7518543004fd75185430067d75185430047d751854301cfc75185430c4fd731854300cfe7218543004fd721854300cfc7218543006f75118543006f65118543006f55118543006f45118543316f53118543006f72118543006f42118543024fe7018543004fd70185430067c5018543325f67618543006f67618543007767518543007757518543006f76518543006f66518543006f56518543006f4651854337fd77318543317d47318543317b64318543317d443185433179
  | 20 => 0x1400000600880000060000008000006000002800400600000100000180080010058000001001802401200800180080000100000008004002007002c016002000000c00000300000000020000000010014006001001c0000060048000006012001800000000200100000020010020028004001000008400800100900c8000002003800c00000700c000000800600780140000070008004000008000000000400000400000060050020008000003000000c00e001007000400a00c00780000040000018004008001006001800a00900000000080120010014000027004006c004010000000400200100000180000000070008048000001000401400400180100080030000014008000000800001200400000000080070000000010000000000400202b00000200000000020000002000000800002c0080008008008000002000c000015005000400a0050018000000017001001801e00000080000060040000000000000000000000002e0000034050000001000800e00700000200000040068008000007003002001001300200040020010010010006000001000c000001003801c00400000b000c00800300680000000000038000000006001001c004004001000c00800000000100040070028004018026002800000800c00000f8000000000802401600a009000400000000100180020070020034002000000802000800200100100000000050010004009000000c004000005003400e002002003c00e000000800000000000000000000000060008008002003000000e00000000000020070008018002000000000401000e000800000e00000580240040020000004000000016001802c005000800800000a004006c000006003800800400b0000008002000001000003a00900cfe76d894335f9c43d8943156ee62d8943004ff75d894301cfe75d8943004fd75d894301cfc75d89430c4fd73d8943006ef52d8943156ee52d8943006ed52d8943156ec52d8943156ee32d8943004fe71d8943004fd71d8943156ef21d8943156ec21d8943024fe70d8943004fd70d89430067c50d8943156ef20d8943156ec20d8943155ee76d894300cee76d8943006ef65d8943006ee65d8943006ed65d8943006ec65d894339fcf73d894335fcc73d894335fae43d894335fcc43d894335f8c43d894335fcc31d89430076c50d894335fcf30d8943006ef75d8943006ee75d8943006ed75d8943006ec75d894335eef73d8943156ee73d894335eed73d894335eec73d894335eef53d894335eee53d894335eed53d894335eec53d894335eee43d894335eec43d8943006ef71d8943006ee71d8943006ed71d8943006ec71d8943006ef51d8943006ee51d8943006ed51d8943006ec51d894335eef31d894335eee31d894335eed31d894335eec31d8943006ef70d
  | 21 => 0x10000002008001000801a00000000000060020018000002001000800400400c000001000800300000000160000060004000001003000000000c0000008002002001000001a009001803801e0000008020000009005000400a00f000001001a000003002400000d000801c000000004000800000200000100000060040004006004002001000a00400500040000070040010002007000000000000000c000000200d002000c0000000018008000000004000001a004008800000a00900000240000020000004008001002001402a003000801000201100a803000a000002000002c0030008024000000002800801a0000020018000004000800000c0000000008000007002000000000a000001400000a004000800a00000000000140010000008014000000803c0280000000014000000001800400a00000280b003400101080000040040000020000000000000400400000500000020010000054004000000000001e00600380000020000000000002001002001800000b001002c000007001800800600000180000020000010000002006000004c000000000000c0000000000010016000000002c00000300280000020030000000002006000001c00c0000008034022004000000000a00e0028008008001001800800400c00100140020090040040004009008800c00e003002004400a020002004c00000000680240020090008008000000000000c000000000000000000600800040000010018030004000000806801000100100000080000018008000003000000001e000000000400200000b80380000020000010000002000002c0020010010008024000000800800800600000080060030058000000005001003801600000700340020020000030000002000800c006000005801400600600300040100000020000002001001000400800000980040040080000008000002003800801e00000000440060000008000000003003002401c006000000c006001002801c0000050010008004000000003402000b0028008006000003003800200a003001800402a0068030008000001804c008003003001000000000180040140060068000000001001000000a003000800000a00700000180020000040008004000000000c00000300b80040000000088044010000000000400800100480000000000000058000005004001802c0020068008000010000000c0240020088000000000000000c0040030000014002002003804800e004000800000000000480540100050000004000001016800400200000080000000000040000008000000000000a002000800800000000080000020050000008002012000801800400000000080140000000070004002003003c00200200880080000040000000000004000801801a00000000300020000008
  | 22 => 0x66f5d480000000002190d4866aa7963cb5f861eb3245a808cd7a000286c0019c080300000011260003a300009e60fb13eb24a91e59e0002f90a5cb3b47cc7b447e173184a8483e2d6247d80017a4c2aeb91454dbe00051518a5a749555208000ee80000000000f76c9660b8000458473b42aa2d446cb12e6997499b04a5abc0004d4d0b0c319cd706a31c23963000066012259763c79bd21b06b0ffc9372c3a1ec7fa58961bc8cd7180000bc6efc6a95f051b173f25cbd6543070800000000000003ec48134d0000bca00058d96e00009da076908b0d60001a2ab801f40000002bd4086252cd700010040000003131a7e0001f4800000081b00000000000ae0bca9849c84d7e8c81096ae1fe90387551ed0000000724d68d02684e5b2cee00007c8000cf40bc0002944000a1b5f2800000000000000005aa00065980006800001d02d62000193958aa4800089a6449c9cc6ab0f68f288aa6a4d925720643be53113200016b20000002c0000000055698280001fe000304200000026d2bcc77c0000c4a02cd120003f899b039f35401222607c826bde31e5400000061d800000063a00033fe00000000000000006ec0000001740738434000175ab5e1d7c0003263f55ab2bbe0008b608080004961db00031417d9a4d20ba1818c60004b1ccee37846951f05918d20005b58d40ff48a2e4c8ca1964131393000053c77e23980040270020000008006002800c00200200500000060060018004000005000004c0160020008024004005001801001000500000000020050018000000003001001000a0020000000000005000000402200000c80280000000000000002002000800c00200000180000020000028000002007000000000a000000000000000000100040000000070004002000001000c0080000020004000008002002800000d006800000000900280000040030050000016001004800000400500100700020000068000002004001001000000c000001400200f00180000220050018068000007004000000400e006800002600000000040080020000004024000005800000200c002000c00000200500240020030010014000011000000000e005000000400200000e000000201f001000000000f0020004002002007000000c003000000c0000060000030002001000002c002001001801000c00400380000020010008008000000001800c00800500000080160000000028000002003001c02a003000800400a0010018000004001005800000000000200080000000008004002004001001c00000c004800800a00a0038000004009000800800600100000080040060040004002001000002c008005000803c01200800200000020030010000000000000802401a002000000801e001000801000000200000000000020058000000
  | 23 => 0x800099b1118ba8a2600000030d1818000323143b28fd7c48096595fac0f9365c2ca5f30d3ce1b2190934b2b1293c4ec4fe8001bcd1ce0000758899274cda6362a513f46f76b262642ac00026280000000dfb4b9ed600000000035af8261c4b0780017368d5117000000000a68ace4d177aeda49000000000000009340000003f18c0156800035d8000cf614c00024216840006911cd56dc000000000188c6858002b4cf5200000012e40007560000ab4e56c6e0000000dceaa30000000000215800000000000031c8b8587c0001421a8cb64b51e1b1ef00000000fbce880000005e100004162a0000221789600000000000000000000000b062592df23f000098e0f1000000000000000000000004d1863200000028eb47c8ae39cbc300c44c64760000001adacbc8000000bee9430000468b542c346d8000000b8f20c27c80000000a9b1e388073e26b75fc2bab953fe1ab8c40caca1f0000000698da89a80000cfe000265d046209000000161cce60000000000120000282c000520a0a40013144b803785614e03fa0000000000000056000000000028527d96570005111cfc0000004e0800196c7730003338e1b000232800197c582198ee65ae800000001493dcb123f634e63149e3049c00000000000000000000003e493c8462248000227c000d5c52400000000003c600955fc0000e4000136207f69080000000000000000000000000190120a0003aeaa401360cb11e04e02c25d40000000000095bf68000a3200000026d46528e22ee0d8c0008c40f840f000000000010f40000003608000000aeb27c8ce11486a55f734ac00029f528145cb7bae60059f204e4cb912c0000000d688002a7000000000000680002b5000041000082600000000000002f200000000001912d3a0002d12158000000b365dc0000000ce91e300000001f1b5600006c472d64e1e41aa00da0002c96000000000000071450e000000050a0565da8000448000000301e00000041c8001280aa9000256000010b00000006149504eea12c0002770001778d860004804000000000000258568e0032cc92fe00054e0b780010669b456c1f958fc00000000000002d809c8000a9840a349426037a2b000000000000000fec001556a26341a47927e00005f8400e0405a98a1181a1cbd519f80c11020000526f75456000000000000000000021240005334a11b8465a00000000000005c649e91842841e734305b4d003743aaa010984d238c940000005c42c69601ae60f58fc933193c4fa52e00006830000000000790000671400000000014108440960003bc00001dc0000001f00000539d210374aca0000000fc00001b80000000b8a0e11ff31620009af0002fd322218e31300003400003802578206c90b7a17d076313d41e8734c8a5d9000236f8020002dc8000000000
  | 24 => 0x80baa5952f84bf00033b939616b23c0000000000024810051eb0a0001441a2c72f0001a34000851bb88000000bd70510000000be88000000000000000000000000000033878140003cf8adcabc0004f6000000000002c2c40679d37002017d54e4af0001c7d5996c463980009f80003996df1ab4281583894c1d00005062ff854e00000000080006270000d60000ba437d12ed384cc96848dd477e7a438707d0b4cc8e6a5000000000000008cf95a00000035aafdc13c4f0007e530b8767135491402715e723339b863b08ba7519fb1d742f96bc7bc3d704a20d0602b2f5a7c0000000804898001aa27bd00012e2000cff0000b7c1d8c29927a7f008887328031616820006408001124c0705c80005840006b280000004d00df0000000d3604408923d4aa6cf4800000099f45c2d520001f880022a4a828b5c374a88000bc04c9997ae13aef3fc25e95f88aa3cf047d888956c9c150000016bd332b7542e18d800187c0000005a7890464685107540013e6bdf3678cf8f821342068dfb2e065418800019989ad4bd91441aa4c8b8cb0a8684098e02800000062464e80012d2699000215901a0000f7a1b76e4bea0a4084a0000000dd0d193b023e000357c00065300009cc85d3640000d0c0001e88001e8200036e0002d500d40824d3954800000000000000009b04458ec00007d400005d80000000000c650943b505d61c800081e12d8bf036e33661e8c4977255063fb3a80ba38217780009c423f97621906f40c33791f98146000000086d8c87a028b332820ca630000000000609615c4ac000914000335800053e80015d584ac552b4962c0000171d0abb5114c9836590c000000000000006f27dc60a80010af88d0000000ece9a5069216d988a4347699613ef0002abb42e7000002ce0000000b195508000000296421316cb76975c5ec00176e00023e23500000f21b680011d60006300c08000d8100000000001d80002ab0c041f23f01338000abd632874c000d55000069634e74436c8001380ce3000000192200012a00004f84bc00013c4000a450cb80004c20000000196ca04cf10bc00013ac7a10c2f68ef8cd70fcc00132247a612355a19d339000000096871b000320885e00015985edac245a000000018200003f70b8000000668b2548b000051940014919d0000063a0009968001de8e840005ce00013560003490000000a25000054800057200000000003ac5b380000006d74980000f8a035237300c00019b000000000093b800073a00000000030c800050465b80000000000458000000d665bc28c82106d238a8000000000000000000023700017320005f10cc8750accc261d880016be53f17ba4b56c5698305937cf6678100000000000000000000000000000000134cb86662ab954d48b451cb645ac60000000000dcc000688a3b
  | 25 => 0x19262ee00026880008c90da72e0b8e000362872c7803ed56bd5a9688b8a0000c6c8ce65a04601a400000000006ac0005700000001612000244694965807000000015aab1300026173b2c906532c9c73ad8300000016c42870002ed9173000220000081e4a7068000106c000000281c8fec83800099c000431000000129f53a58898511f198d222a5a833a29153b345e42c33a05dede5388c91b2d87315505c302280011a6a1568e0001b0448a1eb30e05908f50000bf8000000114f4eb136b2a80027c471200049d9acd1280005aab43000000024a088afef8d637034b47988504f51afc000083000000000000000013d693e9ed0002e5cdde15f00000000000000000000f9a000000253b9b25d795ea074fc878300016a4b3ec66174000000000002709ca0000000000000ade55a18a8000000d8921baa90748abc06f08507f209aa7a068400047e2d680011ca2500da08e000025a000165d02c00e63a1c90efead641f84083a01bf54b0ae4e24be8349a6b0000be227f20e8d1066641d800099648900006d473e7e901bacf13100000002b1400009c0fd56f40e66af060d92cbc689057900009ce000000000000050d000253138c1803d294f753061c1a5ebe0abe25f0000000aee8f1325359e98c4e853f35788b1029675b4ed2f218fa4f0000fb0000088b5e40003130640d32000cf12760cccbbea5b10d13853760001d380000000000002a0084c70944032620001de65580000006430f2c000a0459dd04b2fc83e1845e383c073b15b00012c116f88811a8f4c6e271a0e330082325f31de111d51802c29321fc2f550156fa14f0aa0ad56ba5b8b9dbe61da2ef4eb62aa00005f80008f6000059c0000003ee8dac0000001354000a7c88433a19f048b442590925c000296848b4e03e600034e0d54000000000000000000000022e40000000e5000000078f31ba3fc45e0006049c741e600000000003fe5588133217508a91474000105e7b81989c4048000000007900006eb5fe2d2524e0000001c9427600000034b00002bc0000a5c6c0b026a4ee8c0000000b02f296d95390002cdd8f8278000204800034db7c8b95042830235000000001d44380001b00c534883eae8200000023f94d200051fade8000bf60f48001b1949a00000004aa67268c4000f6300000003dec8ebf222950e561a55b2bc029984e82261aad3444e9252fc2fa544e0000001868c2b0004682522000000000000079a0550002b38c06405a3317ac0000006992d0000ad5d00000000000005e200000007b54819eb84a700052b000000057b0002f2c000000694a07c0004415928000a1f000488c000796d863179aad95c9900001ec4198b4a00035b8000be125216ccdb000021aadc40a8caa3d414a80005850174000bfcad92231e14ce05e7000277ceb060393f0be0ff258
  | 26 => 0x352400000000000000260000000000e8e913de600007fb00000020a4738b2780000010a869d0000000c540000001234d182f953e9ac0000b6922fc0004de9b62ed2b296a40001964aec802bfb0ee25d4a8fcf61e1b4c4000c309468000606d250000001aec00000000000006a4098244072300000000004b80000001ccd914668000000000000000009acd23000348335400032c00000000000005f1995c8983db000000000040500000000006f1800291c0000000a2258895226c5c6b2f40000002098000000000000132000071332c80000000e40000000000000256a51100e7682c9658d6e0bb20d8876a524d781b531d9ae1a5a3a55c5d39a5f680000017c035949500005580000000aaca308cb1fa24f16402ce2590269054c8280034a958e56b21f80000004740002cc12d61f51b4813443a00059f295128a00063e84948c6a130738222ceac18000030a000c720002df40004ac000285800038b000244a0000006491b5102e56c2d2000000000000000000008e662480008322dc225800000000050735660008b21cc1c160006da0000215750ac439515d0188000000254200084861988040000ab0000000000b3a55f000185600f4ca4044082b5826cd4a24242c900004b057e19f1b08cc8d549540000000000a0a000000000012e04b00b6a769d734a32941c0c96e4d2a39504c546b89f18bc095a29906bc0c60330b51e69ad64593b78ddcd6aa3111d04caa929363d39c2261126000000000000000000000000000419000012600008c0000a88928003a78870e7e100000000000000001b8c0002fa200243c00000000001d3a8e93e4a49dc069c1468ae00000002755c7099400000000000000000001b60000000c7000000000004dd28d80000001852d80000ff6b4e04a73eb4c84383412da83677ac0001d2db145c820ac0001cc0d42ca95c4a4e3b945d907464c01e8002214000d87000000000000067200000007773660a4d70a75158f0dfc246c426b7a938253413a72855452f92660e2dd59f93a940ccd5cb1486662c993090a079248a6dcf447883df05b9ad0731480000000048b26009b8a6145b100000146600000017e4000000000000000000000000008428f7050346c000000000000137c98210791285e200000033407dc0000000000aba89680011a0a429a90e900000002d40002e40000a9e09a92a8f5600000000015540000000000000c958d1c00000027ae16000000000047200000000870000000000546561090b366b01665b2a000000046100000000003be800063c0001441e480004a859aaf0c1d40002281d840000004e89648b1e00054d8b3c08c5ce50d0ba512c8af60c800000000053924c40006a10000000e800000392a1400000053ab06c0008c3006ae040000000002e894f63f152b837c19bcf460000
  | 27 => 0x1e44765ed6c28000ce37f50000000028131da80a7b596097e82400087489d39b0266b1c5a510f890e8de11e105064982ca29051cea09442cb288453cb8074a0002aaa8e40d600035d200000029a0000d523c428fa37c28b0000e707eec0ca3b000328c000000000000000000018e00000003e6109ab305ea34a03b06ca0176612936d8754f0cf42f05887664992901cb00447230002dbc000aaf2ec4278d440002d9c00154543400032e8c5c19098213995bc7169d86208c7c0004a4c00000025d0000e48c5a48034214c01de65537f2b0c251498000326d75c24e0001f08ef23f74df816600092b5df257050b00000010cc000b4c27719700000005a1b0720000004ce3600cfeaf603ab45c0000000b918120000000001490b585583b115b4a6e0000efe9101845760e208640008ad4a881f2cbe8f80001c883f66cd38f2a880da9fb35c85d27772c46b3a62c1a6d4f14a0000dc891d694000104a8d728a0000418315b10c00150e73b1be068a2369894e918e1264cc700014304f330b37fac700001905168d35a8862c11427bc00012d0002fc407cc870003414ca2a931fc2b88f5449ee728eac1621f700000007ec0004ab00000001e03d683259f6c51458921cb8208d5c5b16845200067680000008465aeadb1b080fd471ce1064e3c9519c001a0638d486a3d6a566193208630ba05591b41a285d6000583060d6500006460001112a58000000000000026225a000000024e9fe20000003682114847a7f0000001929283288b5080b2c8d69719f5049573610996ee92000000307d1e4c2d14632c039ed1d09f000068eacd20d30a0000617000273c5325f200029a00000000001c14fce05a490a3480000000000c272db0000002e4d32a19a0001094ab5d2308a0ff15e067e2bd000153e0665ec261c78ebbb18f838cc0544f4ca15f4406a9d5761a583dcc12e54a7d02129d60452d9522990b49785000f405c1680d4caaabff4820c951bcd3e4e28d9cc412219c29fa99df86c12383c4e10a385cd0144cc816d8e09dd959039956031b537121698b1e8dad2745506a27800000032402e60000000000b8144300022b21e157eb66520000000088f0e2b0e400086f55d8285a860840002c2c000aae162400000000010b9da96340002c3000000000054d172e000aee000000046900009f8dcc12a00039ba1f18eb4243abadd97f2d58b35b5b1690962caba6e94ee0001a88a842f45566bbb6380006d661f8dc1a97bb306f42d0f1a799247166d728018680b0206f63ef0fe2bc517c948466000173a33c1459e3875b7da00000000000004b8a040fae0004bb8000000b24800058c3c283e4a2400071ca4c43c800000000000014a000000056ed54c80c00000000000c419165ab30000000000000008aa000171800000000068b65659c700032ad40c0000
  | 28 => 0x15f6cc30001d650a500000030782f031d4cb26620000006a43080feea4a6a540017e10003770000ecc18722a00000000001d731d55ceb960ca07b283cadc2d0132800000006b9640376cdf28794211c637d03bf3b000000000012c45da0000002dedae00006bbc69260e29f80003f186e5473221f4c0000200000df93b8000216b284000000000186056c00000010a40bc0994fa800020e82c179b018d848f339c976c03664f4ef0538bec7e2112b52c7f677543298fda2aa2086324b0000d5900010a1acd00000014f445467151e1f4485c72005f1af8ec89fd50f32d03b4a0603da9b4000a62201b4994f028e205a000000000067c00000000000002e921c0000000001502000000000000000012a5b180000000002684d6400069e00016b800000000000009a405d8120000ad88002ec00003bb0001d7862300045f8d278908521f0b2bcc6c0000002a94000302a78111114c00064fe680000cf0a830e5453605716611d2e22611420adfc0000000000001aae93cd7180011d400000022ea000ab500014480001053e7215d460000238000000000000000000000000000ad110640926d8000348ce70000000fb28b01e8251a0000001862fe9a7ad34cad80010410000a680017109e74e39f6c000acf0a896e922e0001d7b3dcfacc9791c9f0ca9e0000001bd834ab980000ef308800000000000001f8000000101ebc90be80011e82a51010f945ba0000001688000952000363c9b05fd0000000000000345d174ad09ca0908e5da8c42c0001187572000000135894ca211a9c00000018d4832d80000c4f0000001570ca000000000007936980000b6c9340002189aed0003a7ac2163a75a500052d98243b00017089abb4600006a40005cf40600016a60000000b918ba0b500834510d70005c216f000039a00000013aab915d7a0715a2b28de889fda5965cb2486600007a600029acbaebf50000b4800038c252b14cd74d3566e800007200014d00000000001310376000a3a3290bed12a0f56978025910000000000129410e203a6489a6d4c5ad00ac6484755ed8ed8a3f91c41c2b50c44cde11909096d022d605913400059fcf3000128c166000174990827380016a13b684f1c41fd8f749d34e426e4a908c64cbc474ba2cf929b103000000040321e96b694724108f460a667297a31cb9bc854a7b4600007cc00000000000000091e1c51200012f0838000153a7bad425648ef05e8ee00006c05d2a664f045c4cbfaba496e0000001b4400000042ac568000000133000014e03d0000000c2c0004fc00004a403203c142c000baa0002dd14ce48434f2fcc1a102f000279418001c5690a8c000728c2a62f30260001e0814d4aa08e5da0000dfa5090b630887c000066328bd43268766255903fa1881ee26c8f2275300014e13020000001
  | 29 => 0x33f0a0e3722358140c100005910000c5609000015f98b80003f5800052a0001cdc00173c83c00014e329c00036f000101c0000001124000ca700000000000003a623f5022000000297c000bac0001c1a5508a16092c5000000000030a400033755d0000000ba7381f1c57a056100000018607294890d74ec00861e29ed18bc3411e135ed81c97e524d24122c2db19d99589b8bfd0cb343d09c00000000000ee02e15201b0000c2f5a5c71c000cabc70000105a662618a2dc00024451005a4cda0002ce8bc80000e20000000000000309d1b40002c880000015128ba6c900017780002b1800156e2e200023640002c635396c474a0383003410754b611235d209d235c380cb4d4689535998000890b3f4d415e400080959c9774145d90097b4e22c13200b28d9400000010200003cab4b4028000494d0080016dc06c0004be9220de20474beea989fa7075b1a4d470c799a153114ace4e009d2fc12301813698bf4b307ca46780002382558a18e58f5e01f00000010ad15280012580000b71a1400014a97600023750fca7445c5255762c9426080019165489f981aa9fe00000006c08a661e00031ec3d017c30216697564cd3ca00000fb76b58b236924659350c1be002a2510931b2498e167a7585c1b1000000000009740002be323c00071656d95440006fc00000002669fe0922cc4000a6058a8bfd0d49aa1bb00000000000862acd9eabf700000012b10000000001a66bef0001717a0700026912818c40002969494000cf853632ed7a614736d7050c20a5349ee14cd16d1209113620f8000000287d4020000000ffcdc4a1100000012040000e1b5f40005b41f919b90b03ad3198001822210000044103000014ea0a171200ac0a05d036c00054506707ce4520ee6370d940003099a0441099820a80004685e10000906665ab000009a4000631000091800012a67e80000002a9367133a0009f700000007b400048485fd0144598000e40570ae40000000e5c18b2f10000804cc84780000000284e8834192ce32a48c9ce800000000033e800088600011ec0d013cb6e8f740000002f480010d90000000df7182472874a5e14488671c88000000d72b7291dcd7800000033ba000000000000000000000000005b2000000000070285d0d307b145ccd84900a524ad76e0eb0ab88c860c00009ed9f7a5d1e7055c886c3a216c3af16d00060800000000000000de00009ce65200019a800000014f000087d50800000000d954c800000065e41a9e2400000000012711ef493501000000000035400005140000dc80011500002ab4000acd15954409584290005c3512e22ca04250a0210572f62d70226000230190818458ac1d5e081c4000c77ba81302440c0f26b800022ad02b5302d80004fb0000000db80004309058000b240000000f6e64d2e535d4d5a
  | 30 => 0xa7c5fc0000574000209189400000050a10f00000000000d0e40ccac00012f848a00043a00001701a3255a66800004f0b8b20d60623ee698fb04f45236adb3c94dc6210002a3519000000021b80003d443ba0049ead600fd08ad11c00c25b27e545033400000008081370000b5c69e7b263b570a6beae834d8000000000000315d7cf00000009031f400005980016dd3442c21ba4d8e84d00000008287df187084e00018f01080000000003e3800000027180018d000000050e000193ed2b8002100b283bd26f126cd6c28669c9ee4ac069f67f62cc00000000000006cc00000000006ac9ff000000178a0001e7aca4000ba62948000277d1a1d31ae00000003db62b0000a710000000e0cc770002b1830400064ba09c7645ac80003d12968cdb8e31280006f5163ad901a2837649c00000074d5918ee899f743000094600007e381b63000000069a344c3d600000006d681c0003750cb80000000002090c781270000b99b2600056811385e85b5276800000047d000000040a0000002b0490ca1d00035050ea7ef621aac829406e5cf888821e4c30000000000c610001b6c5ac7d530a49c00000000002bdc627d8d38500005380000000000e020002ff8d6d8119835fa026e00041c197800000030f80032f000077b4b21fc00000003a3d3a89a290a4c269e87d6c675751c1054cbeb2fe06b86900cd59a18493782f0157b38222488c45e043588e20d3e5a4e519434c1ca1e6a0001770000af8e420004abd1820000002f70000000cae83023340008e10001188000b0c0000000000000000027c0000000d68f60000000000000009800018880000000006268001ac73e3000000000000039e00017005d603c55344230003aa00000000000000000a8487600029942922490000001a4e0000001986000c684675bb400035a0001fcd9b6d4d000000123e7344672536000000000351400002d33b34eed2a4dfdf6198c00255c0b41414b79d65e50f348b42bcd5b68000c7a70f1d19170bf41d901f80000003df000036c000a83000000000095d0f82a3cc0e6d5085296497a5f0d1a937ba101dd33c00005827de33535e80000004a0893e00000000000000000006290b348bc4d43fa02bcb029c3507a41d33ac5f3dde6117b800036ad59e00000069e4f2800021c00014700000002f4354c53170080002a8c1a5a710f0018e7a03a0000e42000c78680e3004e8b45148117d30ad22cf0a63c9dea37692025c2bc5f5072823c0d601e00021640000000408000b22000455b41d9db1951368b78a3c1e63b629792525cb42c73840009eb00011b082d000000000060c5ea4e6152c15252c27c23ee0000925932f501f74b33190f48b877f20001cc804e06706707450dad8b438a9cd29a86358f98399d000007c16fc000a95597000112239e251a49109864e000
  | 31 => 0x14b5ab00034284ae75f06503fd9440004a2eee8f08a463b6af788442c048aa0814928971c7a29400031a3f4318ac846b11f41e6181a0002a5051589c32b6359d8c000907800227026c5450000000822933595b550846b7358c0000bb01c580025b1a80623000000000021546c00015400f72042f656087d238ac000f3a00055b18043640000001c0a000113000000000036f000075a00000000025b46bc00000020b81fcd6400023e5a9c8433b488aa76ed000d41ca19e62da5e433bcf6c3492b700002500a46b52f9d8465d500030f0c603aeccf15fd5f21fcd7d35596fc0002139ffccd20f600007bb40a000000030e000830800000000076500025d19e095f24197b03c66b75c12cf55e879b263c001654191b4063a4000000000000046c00053780000000003b9106cc367304b780000000006021ba0aaf6f057f81d17da00064300015920000001e8400000045389e4344980028c000d1e00000010802823d92e62314000000000263018ec6a3a71e58a443ab800259906286905900004d000005407008e248796500000003d13c580010b86050000001ab0b2d000150c70661d61b45400000000001efd562000468a7c0f2e8a2486246cb46a0300020698345b280000015c2d87800000096a00000027910e078a17380000000004c3088f3d013200012318dea9751e8c20ba65e626a89301b84102fd8000f9e000394cc5c0000163e200000fa00000027250b45c90000cc000000040aaabe00045584b4000000d0d044857f3703184518518d1c910d8b800000000012180017420004b90f883547d0000016c00000041598551d85ef00018a0eb8000516000190000000000000000002acc2c115c1b369005518826794b98942e2803b56d1ec07aa00001a00000004f645e8000000b38000000195b00000000000006fb0001e007d434a99e8020ffa3ace612ddc252000000019000000000024892340000000884000000015000000001900000000000006abc0018ac4c9032a92ca340006678000000000666800000096033295500000000000000050a086a66c15a6d70c6bac00000039b000138dad37520cf000172453cde79c600000000001c3450
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe73619431044001cd0ca31620880331d9db658411005e6b3b6c70822002cd67618e1044001d28c831c208802b399db628411000e733b0c50822000ec46318a1044001ce6cbb0420880131b94172d8c1002636282e5b1820048dc8754d63040031d905bb286080023be097650c1000c76412eca1820648f7815d943040091b90eb1a8608062a72116350c1000476c36e4a182000ce662dc543040011eb0c38a860818b3598c7150c1000673310e2a1820048f8805d562040091dd0fa92c4080031bdd752588100247643aa4b102004ae88054962040091dd0f992c4080031bdd6755881000575c02eab102004ae8805d5620400155f08b9ac408002ab21173588100057240ae6b102000a6e851cd62040014db0a39ac408002aba10735881000556c20e6b102000e4f5394d62040011df0ea1ac4080023b21d435881000573c0a86b102000ae48150d6204001d1a8621ac4080029ba16715881000536c2ce2b1020058ee87d4562040011db0fa8ac408002b3a0f515881000566c1ea2b102000e675194562040095d50128ac408002ba60251588100055742662b102000aad84cc562040014dd0a18ac4080029b61431588100257540062b102000ae9800c562040094dd0ba82c4080129be1550588100053742e60b102000a6d85cc162040091d905bb264080022fe11764c8100c45e422ec99020048ec8758932040019cac5b8a64080023d618714c81000672b10e299020048ef8758a21040099d4e0b1442080033a589708841012e67316e69082000ccf735892104001998e6b1242080031b98b754c01000637baac49802000c6c7558930040398dcc5baa40080031bdd56248010006363aac49002000c6e625d710040018dceab1620080031b5d562c401004e3abb2eb8802000e667558b1004001ccaeab162008013395c162c401002733282c58802004e645058b10040031d905bb220080131e94376440100263c286ec8802000c6e62dd5100400199cc5b9a200802a3b61b72440100047743ac488020058ec8758910040018deeab1220080031b1d5624401000667b9ac48802000ccc735891004009cd0a0b1220080031d1d7764401000673c16ec8802000ce482dd910040098eca1bb220080131d14376440100063bbb6ea8802000cd776dcd10040019aeec39a2008003651d0734401000673bb6e48802000ce7761c91004001b88e63922008002b9a1d62440100057243ac48802000e67755891004001cc8eab122008003b1dcd62440100076239ac48802004ce7705891004009ccca0b1220080139914162440100063c3aeec8802000ceb82dd910040019d105bb220080031eddb75440100066dbb6e68802000cdb761cd10040019d6edb9220080033add87244010006b43a8e48802000ceb7698910040019d6ecb122008003b858a6144010
  | 1 => 0xcec318c48800393d94631891000726328c63122000e8f6418c6244001d18c8318c488003b15c463189100073232ca23122000ec46394462440015c90ca88c488003b118d511891000537430a03122000e4f631406244001c98c6280c4881df9ad80501891001c3f42eec992200087d85dd9324403117d09bb264880022f613764c9100043fc2aec992200387c855d9324400117f08bb264880622f211764c9100046fc1aec99220008ef825d932440011ef02bb2648800637a1f634c9100147743ec49922000cdb631c13144001cc8c5b2c4288003b118b63885100066b3b0c710a2000e946418e2144001d88c431c4288006b9a1b6288510006733b6c510a2000c5c73d952144001cc843b2a428800237a1b73485100062fb2ee690a2000c5c65dcd2144001938c9b9a42880973318b73485102ec6f43ec690a20258dc87d8d214400193ee9b1a4288003271d3634851000667b9ec490a2000ccc73d8921440018f0cbb8242880031e194704851000675b10e090a2000c7476d952144001cc8c5b2a4288097351db73485102ee6a3b0e690a2000d94741cd21440019a8edb1a4288003351d863485100074a320c690a2000ec46218d21440039c8edb92428802b391db6248510006f1b90e090a2004c77619da50440ed4bd0db1ca088003179db63941100070fb26c72822059c5e70d8e50440b3cb4e1b1ca0880021fe1d63941100051fc22c7282204fa3c8458e50440014df04b1ca0880729b20963941102cd2f430c72822000c5e7618e5044001c3ec831ca0880038719063941103ad37436c52822000c6e76d8a5044001c9ec7b14a0880039318f629411023e37386c52822047e6a70d8a50440010ff0eb14a08800297e0d62941100ed2e41ac52822047a6e8618a50440018dcec314a08800393d8c629411000726318c5282203dc76768865044039cc8c510ca0880129d21921941101de3b3b243282200087e86dd53044001878c9baa60880771718f754c11000636316ea982205087e87d95304403b0f90fb2a60880030fdd7644c1100061e3aec89822000c5f75d8d30440018b8ebb1a60880031bdd7624c110006363aec49822000cb464dc530440019c8c5b8a60880032d190714c1100066bb18e29822000ce4621c5304401f9cced10c408811fd814221881100043f436ea9022000c5c63dd520440398d8c5baa408810a1fa1f65481100e43e43eca9022000c5f75d8d20440018b8ebb1a4088003b2083634811000637baec49022000c6c75d8920440019a8c7b8a40880033518c714811000673b10e29022004ae48648520440097c10090a40881d3d814121481100243e432eb8822000c5c635d710440018d8c4bae20880121f61f65c41100062f3aec78822000c5d75d8f10440018dcebb1620880031b5d762c41100263d3b4a18822004
  | 2 => 0x763d89100072632ec7b122000e8f64d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f6244001c9eca31ec4880039319463d891000747b20c7b122000e8c6418f6244001cc8cb28ec4880029ba1850d891000727b18a1b122000e4c6314362440018daea3aec488002b9a0475d891000572c08ebb122000a6e859cf62440014db0b39ec488002aba1273d891000556c24e7b122000e4f5394f62440011df0ea1ec4880023b21d43d891000573c0a87b122000ae48150f6244001d1a8621ec488002b3a0f71d891000566c1ee3b1220008ee87d4762440011db0fa8ec488002b3a0f51d891000566c1ea3b122000aae84cc7624400155b0998ec4880029ba1431d891000536c2863b122000a6e85dc362440014db0bb86c4880029be1570d89100053642ae1b1220008ee8714362440151db0e286c488002b3a0c50d891000566c18a1b122000ae68114362440015cb02286c48811f1ba1c50d891023e36c38a1b122047e4e83143624408fc9b06286c48811f99a0450d891023f32c08a1b122000a6e85cc362440014db0b986c488002aba1030d891000556c2061b12200387e86dd562440018d8c5baac4880021fa1f65589100062e39ecab12200087e8719562440018b8e632ac48800317d9773589100062e32ee6b122000ccc62dcd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c6b122000c5c7518d624400193ee831ac488003271d0635891001c3f43eeab12200487e80dd562440011bf06baac48800a3720d755891000477c12eab1220008fb805d562440010fd0e3aac48800a37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880031bdd77258910006363aee4b122000ccf73dc96244001998e7b92c488003351cf71589100063c3aee0b12200087e8714162440018bee6282c488143171cc50589103be3db80a0b122000c6e76d946244001ccae3b28c4880023b61e65189100053742cca3122000ace83994624400159b07328c4880023be1d651891000567c1aca3122000acc8359462440015d700b28c4880029ba186518910006373b0ca3122000e65811946244001ccce2328c488003995c465189103ad36400ca3122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000ec571d8c62440011db0f318c4880029ba16631891000536c2cc63122000aae8498c624400155b09318c488002b3a0e631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000ace8618c624400199
  | 3 => 0xab1a2000c3c74d9563440018d8e5b2ac6880021fa1c6558d100061e3a0cab1a2000c6c72195634400187ecbba2c6880030f1977458d100064e31ee8b1a2000c3f75d916344001878ebb22c6880032b1cb6458d1000637b2ee4b1a2000c6c65dc9634400195ec9b92c6880033318f7258d1001c3f43eeab1a20008bf845d5634403117908baac68800237e0d7558d1000477c12eab1a20018ec825d563440010fd0e3aac6880622fa1f7458d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000c7743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880032d1d37158d1000672396e2b1a200087e87141634400187ee8282c6881e30f1d05058d1000637b90a0b1a2042c6c7214163440018bcedb28c6880023761e6518d100052f42cca31a2000a9e84994634400153b09328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440014bd0c328c688003179d86518d100072ac08ca31a2076a5c80194634400193cedb20c68800387d976418d100070e32ec831a20008dd8799063440014bd0b320c688002976166418d100054f424c831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d100064f3b0c831a2000e1f651906344001c38ca320c68800297a166218d100052ec2cc431a2000a9e84988634400153b09310c688003951965118d100074a324a231a2000ad4865446344001d28c8a88c68800297a185018d100070fb20a031a2000e1c6414063440070fd0bbb286880021f6177650d1000c77416eca1a20008ed82dd94344001938873b286880063ba0a7650d1000476c14eca1a200087f855d943440070f90abb2868800237e0d7650d1000477c12eca1a20018ec825d943440011ef02bb286880032710c7650d1000c76410eca1a20628f4811d94344001c3887b2a86880031b1cb6550d100c46f43ec6a1a2018a9e84d8d4344001998e5b1a86880023ba1b7250d1000637b2ee4a1a2000c6c65dc9434400199ec7b9286881af3318f7250d100247b436e2a1a2000c7765dc543440018e8cbb8a86881933518f7150d1000672316e2a1a2000975851c543440018eeca38a86880031d1947150d100066bb18e2a1a2062cd4631c543440019c8c438a86880031b5d752d891000572c0ea5b1220038ef8754b624400159d0732ec488002b360e65d891000567c1acbb122000acc835976244001ccb0232ec48800393d9
  | 4 => 0xc40a10f90eb2a618802b395da21883100043ec36ea906201c87e8759520c40850f90eb2a41880123721d5358e100246f43c64b1c200387e85dd943840010fb0bbb287080023be097650e1000c76412eca1c20048dc8758d438403153908b1a8708003331c96350e103266b31ee2a1c2004c5e505cf62840098b8a0b9ec5080123b21d5258a100063b3aaed8842000ae7825db1084009ce4a0bb621080031d5d975c42100063d3aaed8842000c79765d7108400147d0931eca880028f61263d951000537414c7b2a2000a6d8298f65440014bd07316ca880029760e62d95100653b436e3b2a2000c5d731cf65440018dae4396ca880e29da0472d95100053ac08e5b2a2079a7a801cb65440014f300396ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca880b69ea0371d95100051f42663b2a2000a3d84cc765440010fd0e18eca880321f61c31d951016d3b40ee1b2a200087e87cc365440010fb0f986ca880028fa1030d95100051ec2061b2a200087e87c8365440010fb0f906ca880029da0420d95100062ebaea7b1a2000ad581d4f63440071bf0ea9ec688002a7a1265d8d100054ec24cbb1a2000ace82997634400159b0532ec688002a7e1165d8d100054e422cbb1a2000acf82597634400159904b2ec6880039560465d8d100070fb2ec9b1a2000e1c65d9363440014bd0b326c6880029761664d8d1000567414c9b1a2000acd8299363440014bd0b316c6880029761662d8d100054f424c5b1a2000a9d8498b6344001ca8cb28ec68800297a1850d8d100070fb20a1b1a2000c5d751d763440015ad023aec688002b560475d8d1000567416e9b1a2000acd82dd363440015ab03ba6c68800327dd274d8d100070faa4a9b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a2000ad6811cb63440015ab02396c68800393d4a52d8d100046f43885b1a20008dd8710b63440014bd0a216c6880029761442d8d100054fc22e3b1a2000a9c845c763440011bd0fa8ec6880023761f51d8d100054f426a3b1a2000a9d84d47634400159d05a8ec688002b360b51d8d100046f43e83b1a20008dd87d0763440014bd0a20ec6880029761441d8d100052f42ee1b1a2000a5d85dc363440014bf0ab86c6880029721570d8d100046f438a1b1a200b8dd87143634400153d08286c688002a761050d8d1000567410a1b1a2000acd8214363440015ad02286c688002b560450d8d102ce2f438a1b1a2059c5d8714363440b3c3d08286c6881678761050d8d102cf27410a1b1a2059e4d8214363440b3cad02286c6881679560450d8d100052f42e81b1a2000a5d85d0363440011bd0e206c68802e3761c40d8d100052f42e41b1a2000a5d85c8363440015ad02106c6880031718f7558d100043f43ec
  | 5 => 0x127aa037250d200063bb2ee2a1a4000c7465dc543480018eeca38a86900031d1947150d200055b42663b0a400387e86dd561480010fd0fb2ac290003171cf65585200043f438cab0a4000c5c7319561480ef8f6e032ac29000317d9773585200062e32ee6b0a40008f78758461480015a906b08c2900063e603751852000574402a430a4000ab684cc461480858f2e0280c2901d79a08050185200043fc2aed18a400387c855da31480070fd0bbb262900021f617764c520006c63a0e690a400f8ee871852148001cceca30a429000372dcc70485200043fc3ac72824000a3f8458e504809f47908b1ca0900029de0563941200053a40ac72824042c6e7648650480850fd0dbaa60901421fa1f654c1200e43e43eca982401cc6e76d962048039cd6c1b2c40900063b61c618812000672b88c31024000a3e8498d65c400147b0931acb880269d61a7159710005b2c14e2b2e2000a3e849cd65c400147b0939acb8800317dce735971000637b94e4b2e2000a76819c965c40794eb03392cb880029ee0172597103dd3c402e4b2e200087e870c965c40010fb0e192cb880028fa1032597100051ec2064b2e2000a6e829c565c40014db0538acb880ea9ea0271597100051f42662b2e2000a3d84cc565c40010fd0e18acb880021f61c31597100052fc1ae0b2e2000a5c835c165c40014df04b82cb880029b20970597101d53bc0ae0b2e200087e87cc165c40010fb0f982cb880028fa1030597100051ec2060b2e200087e87c8165c40010fb0f902cb880029d60420597100043ec3ccbb1e200087f8759763c40010fb0f3aec78800e1fe1d75d8f1001c6fc3aa7b1e200087d8714363c40070fd0b3b287880021f6167650f1000c77414eca1e20008ed829d943c40011df04bb287880063b2097650f1001c3f428eca1e200087d851d943c4001c3886b2a87880031b1c96550f100c46f43ec6a1e2018a9e84d8d43c40018dccbb9287880031b5977250f100063b32ee2a1e2000c7565dc543c40091eb0c38a87880025d6147150f100063b328e2a1e2000c75651c543c40070ff0cbaec5880021f61e65d8b100043fc3acbb16200087d879d762c40070ff0ebaec58800e3be1d52d8b1000574402a5b16200087d8714362c408fcd040286c58800e1fa16764cb100043ec2cec99620188be849d932c400117b093b2658800e1fa14764cb100043ec28ec9962000c757659621c4001cccc4b2c4388003171cd65487100073210aca90e2000c5e65dcd21c40018bacbb9a43880123ba1f624871000732312ca90e207acd7761cd21c4001b28e839a4388002f860362487100263b30aed2862004d72105da50c40010fb0fb1ca1880021f61f62943100253ac34432862037c757688650c40096e50110ca1880d71d5d921943100043ec36ea986201d87e875953
  | 6 => 0xc54e4328720a6000c9e7650e414c0070fd0bbb282980021f61776505300043fc2aed10a600387c855da214c0070fd0bbb242980021f61776485300c45f424ec90a60008bd849d9214c0051b9063b242980030f1d365485300ee2e39eca90a6000c3f65dd1214c001878cbba2429800317d9773485300062e32ee690a600087f87592504c0014df04b24a0980729b20964941300053bc0ac92826000a7481592504c0094b90ca1ca098143179d9439413027f0e32287282607887e87d95404c03b0f90fb2a8098012a721943501300164e3b286a026004b988050d404c03b8bcedb2c609807796d83658c1300246e43aa6b1c40188be84dc5638800117b09b8ac71000e1fa177650e200043ec2eeca1c40008f7815d943880011e902bb287100123721d6350e200c54e422c6a1c406bcce63dc943880c59acc638a87100033558c7150e200247d406eb30c40048f58794661880078eceb28cc3100123d21d515862006c77c3ac310c400f8ef865c2218808fad4a0b8443100028fa1063d95200051ec20c7b2a4012a6e86dcb65480fb6d501b96ca900028fa1073d95200051ec20e7b2a4000c5d731cf65480014bf06b8eca900029720d71d952000537c12e3b2a401ca6c825c765480394dd0438eca900029b60871d95203e53d400e3b2a401ca79801c7654800147d0998eca900028f61331d95200043f43863b2a400087d870c765480390fd0f986ca900021f61f30d95200051f42061b2a4000a3d840c365480070fd0b38ec6900021f61671d8d200045fc22e3b1a40188bc845c763480010fd0fb2ac6900030f1d36558d200043f438cab1a4000c3c74195634800187ecbba2c6900030f1977458d200063bb2ee2b1a4000c7465dc563480018eeca38ac6900031d1947158d200066a318e2b1a400387e87dd5634800117f08baac6900622f2117558d200047bc0aeab1a40008f4815d563480010fd0e3aac6900622fa1f7458d200061fbaee8b1a4000c3c75dd1634800187eea3a2c6900030f1d47458d200064e3a6e6b1a4000cac74dc963480018eeebb8ac6900031d1d77158d200065bba6e2b1a4000cb474dc563480018eeea38ac6900031d1d47158d200065bba0e2b1a4000cb4741c563480019aee638ac69000339dc87158d200066b218e2b1a400087e87141634800187ee8282c6901e30f1d05058d200063bb88a0b1a4000c747114163480070fd0bbb286900021f6177650d200064e21ceca1a40008f6819d943480011eb033b286900021fe157650d2001c3e42aeca1a40008df835d943480011df04bb286900023de057650d200047a40aeca1a4000c9c431d943480031d9043b286900038710f6550d200e636396caa1a40188dc8758d434803153908b1a8690002b52056350d2002477436e4a1a4000c6f65dc943480018d8cbb92869
  | 7 => 0xdf87586318c00153f08b0c631804237e19708c6302cead282e118c600387e85dda218c0010fb0bbb443180123d61e618863001c3f42eec90c600087d85dd9218c00117f08bb243180622f211764863012e67316e690c6000cac74589218c001968e930a431800335dce61486300247a43ac290c6000cb474585218c02f4bd0db9eca980030f5d074d95300ed2f418e9b2a6000a5d831d3654c0018dae4396ca980021fa1c42d95300043ec3885b2a601da5e8310b654c0014bb06216ca980028fe1171d95300051e422e3b2a6000a5f835c7654c03b4b906b8eca980029be0971d953000536412e3b2a601da5e83d07654c0014bb07a0eca980021fa1c41d95300043ec3883b2a601d87e87d03654c0010fb0fa06ca9807697a0c40d95300ec3f43e41b2a600087d87c83654c0014ed02106ca980029d60420d953001c3f42ce3b22600087d859c7644c0051b906b8ec8980021fa1f655913000636396cab22600087e87195644c0018d8e432ac8981ff1edc0655913000637b2ee4b226000c6c65dc9644c0018eecbb8ac8980031d19771591300063bb28e2b226000c74651c5644c001968c838ac89800e1fa1f755913000477c12eab2260018ec825d5644c0011ef02baac8980023d20575591300047dc02eab22600087e871d5644c0031dd0fb92c8980031bdd77259130006363aee4b226000c6f751c9644c0018d8ea392c89800333dcc72591300063bbaee2b226000c7475dc5644c0019cee5b8ac898003391cb71591300063bba8e2b226000c74751c5644c0019aee638ac89800339dc8715913000672390e2b226000c7875dc1644c0010fd0e282c8980031bdc8505913021636390a0b226000c7771141644c0018e8e2282c8981ff1edc050591300062e3b6caa1a6000e1c64d95434c03153d0db2286981cf331db7250d3039f46326e4a1a607eccc761c9434c0fdd18c839286981c3351db7150d303874a326e2a1a606fcd4761c5434c0dfd28c838a8698003711c87150d300c64e3a287b126000e8d43d0b624c0010fd0fb2ac4980030f1d365589300043f438cab126000c3c74195624c00187ecbba2c4980030f19774589300063bb2ee2b126000c7465dc5624c0018eeca38ac4980031d194715893000672310e2b12600387e85dd9424c0010fb0bbb28498003271d9435093001c3f436eab0a600087e87d95614c001878e9b2ac2980031b1cb65585300043f438cab0a6000c3c74195614c0018d8e432ac2980030fd9774585300061e32ee8b0a6000c6f65dc9614c0018d8cbb92c2980023de1d61185300055a422c230a6000ae482584614c0078bceaa98c298063271d143185300045fc22e430a60188bc845c8614c0015ab07a08c298003a550c411853000578c008230a6000af180084614c0010ff0abb4829800e1f21576905300
  | 8 => 0xea31ac090803171d463581210064fba0c6b024200c9c7418d604851d9aee231ac0908023ee1d60181210053c42ac03024200e5b631406048401cb0c6280c0908063b61e211812100574c04423024247e685088460484094f50ba80c0908031e9837650e50004b7c12eca1ca01c96c825d943940012ef02bb287280025d2057650e50024ae43ac6a1ca004c5c7658d439409f63908b1a87280725ba1f7250e5046f8621ee4a1ca08cc6e60dc94394001ad4c1b92872822fc310c7250e504578a21ee2a1ca000d6772dc54394001ac8e5b8a872822b55a0f7150e5044eaac1ee2a1ca088c7660dc54394001ae4c1b8a87280121fa187150e500043ec30e2a1ca087f14431c54394001acee438a8728003591c87150e500063b430e2a1ca000c75861c5439410d8ecc038a87280035c9807150e500e43e43ac6b14a01dc5c7358d62940394d904b1ac5280024fe11764ca5027c9e422ec994a000977815d932940012e902bb265282165be09744ca50004bbc0ae8994a000974815d132940392b90ea1a652813f471d1434ca503b4af43ee6b0ca000d1f74dcd61940b38bcc1b9ac3281675698373586500068fba0e6b0ca000d1c741cd619403b0f90eb1ac328077171cd63586503acb743ee4b0ca000d4f73dc96194001a98e7b92c32811f1bd8f725865000636b1ee4b0ca047c6e60dc9619408fad4c1b92c32800353dcc7258650006a6398e4b0ca059c5f635da31940392dd05ba463280025b60b748c650424bb40ee918ca04f95f8750e319409fa3ce8a1c632816ed3209438c6500049fc22ec98ca04f93c845d931940b32bf06bb263280025be09764c6500e4b6412ec98ca00096f825d131940392d904ba2632820e5de05744c65023e37b12ed10ca0049758798621940396c904b0c43280031e9837648650004afc1aec90ca01d95c835d9219408f2df04bb2432807657a1f73486500068fba6e690ca082c5e60dcd2194001ab4c1b9a43280024fe11734865027c9e422e690ca08195e871cd2194001a3ee839a4328003471d07348650024b643ac490ca004c6c7658921940092e90eb0a43280131b94172d923002636282e5b24600387e859c7648c0010fb0b38ec9180031da1671d92300063ac2ce3b246004c76509c7648c0098e8a138ec9180033520d71d92300263b282e3b246004c74505c7648c0091790eaa2c9180123b21d5258a3001c3fc3aeb30c600487e805d6618c0090f900bacc3180123d61e519863001e3b3aca330c6003c7675546618c0015ab07a0cc3180029d61441986300045fc22eab0c60188bc845d5618c03117d0fba2c3180032d60774586300064e18ee8b0c6080c3e50dd1618c101878a1ba2c3180123d21d51586300053ac2882b0c6000cb774105618c0070fd0bbb483180021f617769063012d67416c918c600e8
  | 9 => 0x74d8d210064fba4e9b1a4200a5e851d363484014bb0a3a6c69080387d5254d8d2112c6f43ea3b1a42008dd87d47634840153d09a8ec690802a761351d8d2112d67416a3b1a4200acd82d476348401caea328ec69089637a1f41d8d210046ec3e83b1a4200a5e8510763484014bb0a20ec69080297a1770d8d210052ec2ee1b1a4200a9e849c3634840153b09386c69080297e1570d8d210052e42ae1b1a4200acd821c3634844b5ab02386c69080237a1c50d8d210046ec38a1b1a4200a9e84143634840153b08286c690896b3a0850d8d2100566c10a1b1a4200ad68114363484015ab02286c69080317a1c50d8d210062ec38a1b1a4200e1e841436348401c3b08286c690a5793a0850d8d2100726c10a1b1a4200e56811436348401cab02286c69080297a1740d8d210052ec2e81b1a42008de8710363484011bb0e206c6908032718f7458d210045fc22eab1a42188bc845d563484011bf06baac6908023ee017558d210247c402eab1a42188be87dd1634840193ee9b9ac690803271d37358d21006563a6e4b1a4200cb474dc563484070fd0bb82c6908021f6177058d210061fba0a0b1a4278c3c7414163484018f6e0282c6908131e1c05058d210046ec3cca31a4200a9e84994634840153b09328c690802b360a6518d214a56ac0cca31a42008df87594634840153f08b28c690802a72116518d210056dc02ca31a4200ad880594634852793cedb20c690803879d76418d210070ebaec831a42008dd87990634852553d09320c69080237e1d6418d2148d6bc0ac831a4200a5e8519063484014bb0a320c690a43279d86418d210070f3a8c831a4200e1d75190634851fd2e42320c690a3fa30846418d2147f4a108c831a428fe8f2019063484012bb0e280c69080387d905018d210070e320a031a4200c9c439d943484011bf06bb286908023be097650d210047bc0aeca1a420387e851d943484010fb0a3b286908032710c7650d210c46f43ec6a1a4218a9e84d8d434844b998e5b1a86908023ba1b7250d2135e6631ee4a1a42018f686dc543484c99a8c7b8a869080335d8c7150d213166a318e2a1a4225ccc72d8d3148401958c9b926290803a319063885210062f3aec7b024200c5d75d8f60484018bcea31ec090803175d463d81210072db18a1b024200e586314360484070ff0ebaec0908031ee0175d81210063cba8a1b024200ae98214360484015e302286c0908029e61c50d81210063cc38a1b024200e5a831436048401cb306286c0909df9aa0850d812100734c10a1b024200e72811436048401ce302286c090803279d363981210064eba6c73024200c9e7418e604840193ae831cc0908963721b73581210046f43ec6b024200c5f75d8d60484018b8ebb1ac09080327dd363581210064e3a6c6b0242008de8718d60484018be
  | 10 => 0xb22640387e85dc1644c8010fb0bb82c8990031ddc450591320063a388a0b226400c7b70141644c8098f0e0282c899062a7a1b6450d32156663b6e4a1a6473e8c64dc9434c8e19a8edb8a86991c3a51937150d3237e6a3b0e2a1a646fe94641c5434c801b88e438a869900e3de1d51d85320053ac2883b0a640087f855c3614c8070f90ab86c2990023de1d61185320055a422c230a6497ad783584614c831938e8a18c29900e3d61e511853201e3b3aca230a6400ad583d04614c8014eb0a208c299003a550c411853200572c108230a640087f855c0614c8070f90ab80c2990022fe1170185320c45e422e030a640087d879d7604c8070ff0ebaec099063271d143d81320047dc3ac030264008bf845c4604c83117908b88c0990063ba0b75d923100476c16ebb2462008f681dd7648c4091f501baec9188023e60375d923100c77c3ae5b246200ce6729c7648c4019cae538ec9188021fe1570d923101c3e42ae1b246242c6e72143648c4018dae4286c9188131e9c050d92310063cb80a1b24620387e85dc1648c4010fb0bb82c918862a7e196450e3112ce743ee4a1c6273ccf76dc9438c4e7d1cc9b9287189fb33dd87250e313f747320e4a1c62618dd86dc5438c4c99acc3b8a871899335ddb7150e313274b326e2a1c626fcd7761c5438c4dfd2cc838a8718803711c87150e312ceac280e0a1c6218c9e7450d628c44b59904a1ac518803a350f4258a3101c3f42ee0b14620087d85dc1628c4053390ea1a851880327dd94350a310c54fc328720c6202c9d7650e418c52771904a1c8318802e5e05439063101c3f43eeab046203c5c7554d608c43193ce8a1ac1188023ee1d601823101c5fc3aa9b22620087f855c3644c4070f90ab86c8988023be09755913100c76412eab2262008f7815d5644c4011f700baac8988123e201755913100c7743ee4b226200ccf731c9644c4019cee5b8ac898803391cb715913101c3f42ee0b22620087d85dc1644c4018dee4282c89890b1b1c850591310063db80a0b226204c7870141644c4071df0ea96c4988021fe1570d893101c3e42ae1b1262188df87592314c44b59904b24629880e1fe1d75d81310047dc3ac03026296ce5729c763884010ff0ab86c71080e1f21570d8e2101c3f42ee0b1c420087d85dc163884011ed033b2871080e1fa147650e210043ec28eca1c42188de87d8d438843153d09b1a87108063d6187150e2101c3f43eeab044203c6c7554960884011f70eb00c110803175d753d8d2101c6fc3aa7b1a420087f855c363484070f90ab86c690802a7a1265d8d210054ec24cbb1a4200a9f84597634840153908b2ec690802b6e0165d8d210056c402cbb1a4200a5e8519363484014bb0a326c690943179d850d8d210070fb20a1b1a4200c5d751d7634840159b05ba6c690896b5607
  | 11 => 0x50c014ed0a390c2a18029d61472185433156b418e430a866fad5831c86150c015e500390c2a1802bc600721854300733a94a430a8662ad6831486150c015ab06290c2a18029da1770185430053ac2ee030a8600c7575dc06150c014ef0ab80c2a18029d21570185430063abaae030a869bad7835c06150c015cf04b80c2a1802b920970185430053b428e030a8600a75851c06150cdf5ab06380c2a1802b9a08701854300572c10e030a86008f6871406150c011eb0e280c2a198ab5a0c50185430056ac18a030a8600ae6821406150c015cb04280c2a18029de1c50185430063b438a030a8600a75871406150c018eb0e280c2a18021d61c50185434ff2b418a030a8600e55831406150c01ccd04280c2a18039960850185430053b42e4030a8600a7585c806150cc55ad07900c2a1802b560f20185430047b4384030a86008f5870806150c01a3886baec0a18031b9d762d814300636baec5b028600c6e7518b6050c018daea316c0a18031d9d761d81430063abaec3b028600c76751876050c018eaea30ec0a19ffc610c50d814300735b10a1b028600e68621436050c01ce6c2286c0a18039c18450d81430043ec3cebb02860387f875d76050c018f700baec0a18063ba0a71d814300476c14e3b028600c7975d436050c018f2ea286c0a1802b660c50d81430053cc38a1b028600c79871436050cffcb506286c0a18039660c50d814300735410a1b028600e69821436050c01ce502286c0a18039c60450d8143006c621ae5302869ee8c4318a6050c01b288738cc0a180339d8a719814300672314e33028600d94435c66050c019cec4b8cc0a180339189719814300673396c33028600ce572d866050d3bd288630cc0a1803399c8619814300672b90c33028600d1c43dd56050c551d90db92c0a18036310f72581430047743ec4b028600c6f75d896050c018d8ebb12c0a18023ba1c625814300637ba8c4b028600c6c751896050d3999ee6312c0a18036510f715814300673b16e2b028600ce462dc56050c01b288638ac0a180339d88715814300672310e2b0286008f687d856050c018eeebb0ac0a18031d1d7615814300673b96c2b028600ce472d856050c011ed0e30ac0a18031ddd461581430063a3a8c2b02869bcd7731856050c019cee430ac0a1803391c861581434d746218c43028699e94431846050c011f70eb00c0a18029e21560181434c78c218a03028600e6b621406050c01cd0c4280c0a18039cd84501814300738308a030286048f8805d46050c011df04b88c0a18063b20971181430253d42ea030286038bf87553644c8010ff0ab86c89900e1f21570d91320065a320e2b2264008ef825d5644c8011ef02baac8990023d20575591320047dc02eab2264048f8805d5644c8019cee5b8ac89900335dcc715913200673b90e2
  | 12 => 0x9c2b560f75d85430063aba8ebb0a8664ad6831d76150ce15ab063aec2a1802b9a0875d854300572c10ebb0a8670ad583dcb6150c014ed0a396c2a18029d61472d85433256b418e5b0a8670ad5831cb6150c01ccea5296c2a18029da1770d85430053ac2ee1b0a8670ad583dc36150c015cd05b86c2a1802b960b70d854300573414e1b0a8600ae5829c36150c014ef0ab86c2a18029d21570d85433856ac18e1b0a86008f6871436150c011eb0e286c2a1992b5a0c50d85430056ac18a1b0a8600ae6821436150c015cb04286c2a18031da1c50d85430063ac38a1b0a86b0e56831436150c01cab06286c2a1ac3959cc50d854357f2ab98a1b0a8600e66821436150c01ccb04286c2a18029da1720d85430053ac2e41b0a86008f6870836150c011eb0e106c2a18036310d729854357746218c530a8600ce672d866150c019cae5b0cc2a18036310f72585430047743ec4b0a86008ee871896150d5b99ee6312c2a18034710d7518543006373aec430a8600c6d75d886150c018dcea310c2a18031b5d462185432ee66398c430a86a2e8c431886150c011ef0eb08c2a1802b9e09611854300572412c230a860087d879d46150c070ff0eba8c2a18031d20575185430243e402ea30a8600c7575d446150c015ab07a88c2a1802b9a0b511854300572c16a230a86038f5879446150c078eceb288c2a180f1d9d551185430043fc2ae030a860387c855c06150c011df04b80c2a18063b20970185430243fc38a030a860087d871406150d59d28873b0c2a18031d9da75185430078a21cea30a8600c76765d46150c01e2886ba8c2a1aafa510f65185430047ac3cca30a86a1ad5839946150c015cd05328c2a1802b960a65185430047bc3aca30a86aae94435946150c015cf04b28c2a1802b9209651854300579c02ca30a8600af0805946150d539ccedb10c2a1aa3e110f6218543007333aec430a8600e6575d886150c011eb0f310c2a1a9fa510e621854353573414c430a86008f7875886150d415af06b10c2a18029da1462185430053ac28c430a86a2e94431886150d4b5cd0c310c2a1a93399d86218543517c2218c430a8600e66851886150c01ccb0a310c2a1803999d4621854300732ba8c430a86a2ec6831886150d47d8b06310c2a1a8fb1dcc621854351762398c430a86a2ea6431886150d45d8886310c2a1a8ba110c621854351763980c430a8600975871406150d3fe2886280c2a180399d88501854300732310a030a8600c77759d46150cc55ad073a8c2a1a86b560e751854300573414ea30a8600ae5829d46150c014eb0f3a8c2a180395a0e75185430072ac1cea30a8600e66829d46150c01ccb053a8c2a18029da0275185430063bc3aea30a8600a74805d46150c014ed0a3a8c2a18029da1772185430053ac2ee430a86a0ad7835c861
  | 13 => 0x80480181d80000080000080200100500180000700080600780a00000181880b00280100000100200200380180080280300900100080780500000280000000180100e00200000100701100d00000200080300000100080280100000200280000400300000480d00180080480280a00100000000380000080080480000980100080100380700080780000280400601900680200080080580180000080000000180a00900b80100700080280080500080000100380100000580180080100100000580780380201d00000080180080e00180000280080280000200100180080300000e00000600200000180000000001a00400280180980580000100000000000000200080500000000101880200000800280000180080300600200300480400000280600000700401d00480280100000080200680100180300780100f00380200200400900280600580180080000280280080b80a80080b0000018018000000000008078008010078090020000058158000000028000010030031b5d752d894301c77c3aa5b12860087f855c36250c070f90ab86c4a1802b9a0665d894300572c0ccbb128600ae7815976250c015c902b2ec4a1802bae0165d894300574402cbb128642c6e761436250d6fe1886286c4a18031b5d475d894339d66c1ee3b128600a6e851c76250c014db0a38ec4a18023ba1f51d894300476c3ea3b12866bace83d476250c0159b07a8ec4a18029ba1770d894300536c2ee1b128600ae6819c36250c015cb03386c4a18033adc270d894300537c2ae1b128600a6c855c36250ce759b06386c4a18023ba1c50d894300476c38a1b12866bace831436250c0159b06286c4a1802b9a0450d894300572c08a1b128600c6e871436250c018db0e286c4a1adf93a0c50d894300726c18a1b128600e66811436250c01ccb02286c4a18036510f715894300672316e2b128600d94431c56250c019c8c438ac4a1adba310f651894300476c3cca31286b5acd839946250c015cd03328c4a1802b9606651894300477c3aca31286b4e8c435946250c015cf02b28c4a1802b9205651894300575c02ca3128600ae8805946250c012db0e280c4a1acfc310c50189430c46ec1eebb0a8600c7575d476150c015ab07a8ec2a1802b9a0b51d854300572c16a3b0a86038f7875476150c010ff0ab86c2a180e1f21570d85433c62eb98a1b0a8600ae6829976150c015cb0532ec2a1802b9e0965d854300572412cbb0a8600af3805976150c015e100b2ec2a1aa7e110f62d854354f6339ec5b0a86b2ec573d8b6150c014ed0a316c2a18029d61462d8543527c2218c5b0a8600e668518b6150c01ccb0a316c2a1a93b1a0c62d854358f62c18c5b0a86a4ec67318b6150d63d8ae6316c2a1ac3c510c50d854300733b10a1b0a8600e64621436150cc95ad07baec2a1
  | 14 => 0x4f4a005d3690002750003780430130001912f11325962bd00000071651aa065c100042c7225dc69660e2455e500072144e000000000379507e0100000000073f49a00000010f000582ae600033000014573872980000026d63200000027b14b01a8006f97567443965f40003862b90005100006e26e800000017800061a40f62b0000000006610000000002b70b24a1f5e00000017080000021a0004ed69c8000ed0002961cf00008289ea916f386872300048e0002b019c41d2f400013438037d6d12494f90005fc0000001c76f401723f23365e80067e4694be70c00000000345130c00011f55f4e53d15b503509a02900035265f39e0002a7b9536e4e300001600009b00000000071c615505a362a818e416511b7b6ed2ac0006baea35977430005c90000000486d227f00056444a2e5000000194df83881710213dc1540000004fd00000180000400380000a00080780500500080280401a00280280200080180080380380000180d80180000180000b00200180000280280081402180180100000400000000980400100000880180000001700880200100400e00080180100380000080000180080080080300100480100400281700080100000080000400000000080380000100000780100500000480000000580001180000100180280100580180400000580180280280480300080100100000480780100380000180300100380100580000900000080380300180000100100100180680000380080080000001200101600200e80500080001f80080000400000280080600400100000000080300600280080c00180080a00381500180100000200080080080300000200000000a00080000180000180280100580000000100000000000000100080000100580680080000080100300400380100480000280080000300b80800400200000000400000b80000000181200080580180800901980100080000400081980900400000780580000280800000000700000000400100300100100380000100000000100900200180480000080000300000080000180680300880080780200780000000100280000380a80200c00000700080180000200680400a80480280300700000280200400600000000380280000000780000900380180001500000500080580780080200000500200000900100000000100080180600000100080780101180400000300000000000180000000080580881d00104900180080300480800180180080080080000100280100980000000800000100100480000000000500280000080180000880000e81080100100080300080100180780200c00200080000000680000000000280d00000000000600600000380300281d00000d00980780000181080080180080400400c80380300280280100080000b80380380d800006
  | 15 => 0xe57d6901fa0000b50b72864430004110005eda2a0002a05634c23820126915060fe6ac2aa0000001120002170004396c70a52ab3ee0007275d700018a00000000025400000068700000020171d4dc0000007069fe3c96120cd0003d674563e00000010a98ff244755ed0000000006b96cd8000004a9098a524716b82a92710e7ae24b26a259abde59d35939a7139e150f21f72919e0015ae62a417082487892f4e6dc70e0004741dbe694004b11050005805ca7091e703d9020000716ba5d56ec65b32e7614f55b2331f52e024af12300058e00000044b0490000000000006678000000007133d900000000000030a0001cb2470000d730348200035b61d00050d0001062070005d056247b4550c973b49655b6686240fb7099905af0a02002fa19472f0aadf002d00000000000000026e30961280064a23e6f31130001154421e86b009f659ba405066050382a65e10b22e66e7410995fa5bc2724ac45d4e8aed3480000000003c00000000000000005556db11c67a0004e90c41e90000000005abe816840005e80000000000005a200036b00000000025338529a0000000004a78000000000000000bb0c370a8d34fe9950005b14f280000000000000000062f19f3a700025764029e5cd3c72735fe72392706c3c85a911462660d2644142eb6da4621260efc020000000da2c8da40001dfbcc12429500009000051c8001f730f4d41a700059967000000020e4cd2a368e10100015e1f61160003140860c568f6710a60006ea7180272f300047d74697b5206c00006782a155d61c5b01764671a06eb1ca6cf4886a957c69918750b40805e6f53813bd3aa0bc0d56986ca0673a918d25f1c924b67d19d63b48f00000000043f03b07900069ae7fa56429000437000100333b412b814e1ed5656803b41250000000000000000000001206920410001ec0000007152bc6be25b3a1b422b161956a3c40003348870005bf5f54662c127c50bcd9b5700016f60600000047674d0000000000000000000004890ca0000007350003e25014941b480003453400028d1384790000004480000000007523af0cb6f4d485f675a0000002d34ad2d53e90000005704ba00f0007262934475ce0004d165f8000000004ff62739217c80052c0000003584709f910431e00e36d32453d1b960c1c55c33f6affc936133a3332146f2e67300000000000033e1ee4f1a3a6161a600034a65652b00049e55a34c0004b45537519fc02f4f253933f2f82bb07c00000c4a60451725722da21c36563f0000000000002fed300d40000000007340001d873069bb264ee3503df0f70ad6d320c1dc1f549c4fad6f7192800105d11b0947bd729f1de00000070a00025c5240005523d551a745e6a0000001a50004e98002f751605a68c8005f21fb00000030000071b8007466c34b864e7
  | 16 => 0x73c0b400026b7118003d000000022600011d00068640752d30d2ae1b146e460c503cb80012f2ad64c20b0002080000e750e05c2f948c00000007a0000260000572c21ae66d5815de0005ebbb56033564b927846142200026109864471f00019f8000004363644591100ec0cc0000000000006cb0000003fd1268a28000001662ce0199ab09255c1bb9743fa124db46cd0000000000002dd6b22ec0c5a7758f2d14daa295eb1c40280ae43d5051b25884090d922125169de6c6095684494aa2396a40eb21858d64550c0002e3f0f30747200034e44c1ce4313682a23402f069352f5b91a0c2d0ee34ec8774c0000000bcc910004f00ba2024c55605574d63b30000004e23368dc34b47a1981792443616799224104e85943dd0006335db5224544c4322125b6338969d3f200008e000000559338f530001c34fe5d60003940005f947e00029b29c3f92ea00070dbb175c119058d28522800319636282409887d665fd0001cd00064b486f122e966774a7474b742458360053224b8000006641cf8001a25be53b2e85180ef6884452be0000000000000001ff12b5090000d16e60c16bc50a5aa0314fb8000000002ca00000012e6f71730dd5231c0143b9945e00000045c0001a58003a5084000153dee3353ec51b80058722c4eb8004774db1334a24a436757326044f5616dd132e91ef8501800410f2a00000008321b62c19b5fb3bb0001c14968be0001d556746d38405556b6773c57493336723450af0c771e2d048a1364d035a22313d00685416542845a31d0d4c5f3b75696490181448006d4334010ef211e1083e613c0001756ad0004734d30e60690005d90003294dd5b865d28a0766e96a700023812c00006f6853160005bca7e6fd5c556c15196272c58605120f5e9dcf04e53c61e57f5791fd7498000000000d66e54c3757ca720d0000000c600004200000026a5e76437643d81b466ddec0ab1960000000000002fd42f0002b54ab38700007e25e0bd69721d1517371e015d2a52f57111428fd6a16fb14608b0f521013b6147012304201175a849f00068d2c00e12355ff0373e475700000000011b55e0003c36a018c63a1482e36ebceb7600885c25503203ab0de54408f3915f32d60387283490749c67424e1bc1346c0472048b668a637324ca03f1d3139bd30f30d030414729d36c0bf0111a4c844cc3e554754c28743844d022ddd2091562ba26641f3710a91805ba3621b50722b64fc69f0581bc22775b24209366b15f38317e0301865ef0f833c3212143e30f267f131b2f4263740324a28002500000001b03cf40a00043b70d0006102344a133d42775f3750532c77513f35e97061d11df6fc14df5d4dff14a3b5b33ea4855250ce4f1658ed72dc00d2990001e53919aaea86e018900028e000193057c8317fd260005ab21
  | 17 => 0x3d2055b70000b12370970000e03cd6ee70b6352cb00000000053800004c1922b35f70655020855294ce5890a440e5b488c2974323704ea6e12031b371af172620003d456e5744f353304a38e1b80000002fb1110002a402545200005b30e1ac299b0226900000000000044463c89103d16b64f4da1098190001be0002fe00001f46f04449700000000000039d18eeb60003f48003ad00021641c5910002df5e24bf6b463d00000014c0c253f00000000000021900006a2c93eb31f4010a2405337193d496304900560d86173fc4861d703a13012842b4531e64d24e69d90000002841dd5d301c4702410022551ad59f6d06b1492112ec12f63511a81e300006e00060a6ab5a750352e0332b457e0ea6394646946344b501a40356d6ff32a3550003bf5f1514a224c614d2ee2a757146a1f435e00049f81459b0c851b4fb00909d4bc2833fa8001813f000006b0000004a528c0000005464ef1500003313e86221522d809e00025a26c1da00013562066f169ac64f700032c48d3903fb4d77540003a61e7ed7be10000db0622b20002c864616a67c682ae45a14e771441a1993f80000001db53a71b0005da0007330000000003a869b0a83930000000000005f88004e493880049be380000000001534e41f211a14a00000019700000027a6083120c98b847f7583081605821e43c20466bf0000940000000005452813b24d515514c8005771571683433da1180158000002121b59e8e523a0dc60e24f80000000000df00030b67539b59000000647808d75513a24e54117f41800060f00a0000000001bb0000000000001bd6662fc5083f708900000000049d36f5274b6000672dd443422f2156fee1f32b6b300036a6e33ac5006bd5c00002706482cd1586ecec908a00058c53e7085e60005b624013ecd95e400002b2652892244b300042a07b0733a200049503e8000000005beef11675a003c5121e27590814351c4dcc6c62cf18800730142e5d86e713700065c13900004740d0000003287000b62205ea4c800000064738a0004986c80e865900004f6af0000002d90cf0000005bb0006c20000000007076d500000037f0000001290001eb0002af29880023d71a0000000001d200067b000225419000736ef02c30001c834f5931b6504b053cb07f51376239803610e8226b751d0005ac00015b80040b3be2a632d21107d6290f01d618326f28544668b8005856516cc34d70331c4fa6df20454f0005750f44680000003db4c00003ef55438b4b00005a50007487103b01af0000006b50003908b95a60c0bce3e73534ae52a0000770001f17043b96ae10c8004120003662744c380004d0000000001cc1b70005e00000000e9c3023c51f703a321422c582357b00037215c9aa50720a65800058a0f92d20954df73946b1a324319a1f012169e8006d6
  | 18 => 0x40c1096ce6d90a10006408004806aa115d3600064d1d02676740000003c600011380000039f69a099e6217c00000059c3a04e61592580200000000000000e90752db59200049cca30000c4d5124d35c0003a280049b5e13ae0005401035a370ce3100062317a158d1551e18b63c5376d813d93f4580bb80033b38d3b6195bba33a00018f4d800067600013c80007851431a0000000f10006a541500000046517bde35422686bb01d33651c6110e32cc7055c86909ea43310a5ad114cbb61b4237408744bd2f23766de24a32700000068b54e00029045600785f3fc81b1f847d8004f63b86371406410591bf6ef377086e8c0004630006250000000002d469980000016f8001ba0004130003b0800317156efa0000002d700016132533825d17000051100000000000000036041e4a0d5615de97ae000034737a75000069e0006ddbf600000565700000039c58b07000055814f0003f400031337c0e6a9267a8d23ff2940631693975cb4f47635d20e46eebe001557600406454324c31b13e0000006e4000607702a310000bf9f316e42554d0005c77254ec15f9c20000000000003100004c938f1430a72ef65468203e46c00000028b15a34665514160437e5310006a63f8e211490ca80030600000fe184de0004990000f600002e4e03ca0006050000000000000000003540238002131771e69845b984b3f543a2bf2593fe5c400000b72b6f780000062d0002de00000054b0000000003d200000000000000022d00043c35f16c1a1180a793c1f2d59863d9441a40006a9bed16d3248fa0004c495b50467ef3a4e16420000e56655780000606280004cf73f80012a0000ff02c1ddc063bc00000054a13165a0aa73658474045710d4fce631abc604c14cb59e0f7a4865071280035d0001ef22b0520005bd44100010e0083150000c00002ff000000679000621e832280b06f60000f28000fc10700000018569c0400005211a3b4406d24672b80000015c44000000000000053562e00038c57a2c551903917d68928f00001e24f70210c68a12d08016447c3390660004a812f8006536c432318273e0000000000960000000001a2bf159531127d0006950ac7315b6ba12981d445b6c52e760b2e102406108ec3e16a8002760000001a96fe31800012e89c0000000000000002c40b30000000000a36edddf4211634c751748141b74b59a0002883737
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x70364e1000860038194a008b226e040e58665a180a421b3e3c3a25685d245703008445007d8a52344706761a7e8f1e515c880059722a6416561c406c12447c005e1400808100828e2e02504654484c00620078280000602c260000000020087a007430326a8c0c000008010085021a101010068800001d085000c007012800f00613a1d831436250c018658760450d89430069160d811436250c01a84432056518943006a210c805946250c0190c4361c501894300499660621436150c018568760c50d85430061961d821436150c01a458360850d85430041b662751886150c01c0c435d46218543006a110c825946150c01a904320165185430068510d851886150c01e0443a1462185430078110d851886150c01265989d462185430078110e751886150c01e04435d462185430064510d871406150c0186587d88501854300499660621406150c018658718850185435df8110c621406150c01a458360a75185430041d662871406150c018568361c50185430061561d831406150c0186587a0850185430061961d821406150c01a458360850185430041b6627518b6050c01075989d461d81430049a660621436050c012719818450d81430069260d821436050c01a518360450d81430072110c629c66050c01c84439c861981430049a660621406050d75e084318850181430049c660611406050d73e1043184501814353721190721c5434c801a8543608411853251f21990721c5438c40181d8761050d8d2100613a1d821436348401a0d8460850d8d2100615a1d811436348401a158460450d8d210060761f64140634840181d871905018d210241e241851d9434840148d9210c7650d21004176627518f60484012599818c50d81210069260d821436048401a518360450d812100496660631406048571d04431c87150e5051f21190721c5434c001a9143600411853000525650631c5634800109d9810c7650d2000519a5c6259521c40014999010c7650d100041d660651c5434400148c9750c43588100063121c735891004001c84741cd6244010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xeca268040000540b4421b0a310c2a1802a05a810d851886150c01902cc0873a8c430a8600c8110d98188501854300700886c38c4280c2a180320843660621406050c0190821b30308a030286009212859210c7650d21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4e
  | 8 => 0x124e
  | 9 => 0x138e
  | 10 => 0x94b
  | 11 => 0x94c
  | 12 => 0x94e
  | 13 => 0x124b
  | 14 => 0x124c
  | 15 => 0x138b
  | 16 => 0x138c
  | 17 => 0x98c
  | 18 => 0x98e
  | 19 => 0x128c
  | 20 => 0x128e
  | 21 => 0x9cb
  | 22 => 0x9cd
  | 23 => 0x9ce
  | 24 => 0x5
  | 25 => 0x12cb
  | 26 => 0x12cd
  | 27 => 0x12ce
  | 28 => 0x134b
  | 29 => 0x134c
  | 30 => 0xb0c
  | 31 => 0xb0e
  | 32 => 0x140c
  | 33 => 0x140e
  | 34 => 0xb4b
  | 35 => 0xb4d
  | 36 => 0xb4e
  | 37 => 0x144b
  | 38 => 0x144d
  | 39 => 0x144e
  | 40 => 0xccd
  | 41 => 0xcce
  | 42 => 0xe8b
  | 43 => 0xe8e
  | 44 => 0x95396
  | 45 => 0x94056
  | 46 => 0x125396
  | 47 => 0x4956
  | 48 => 0x138056
  | 49 => 0x124956
  | 50 => 0x95256
  | 51 => 0x138956
  | 52 => 0x98956
  | 53 => 0xb0956
  | 54 => 0x94b16
  | 55 => 0x140956
  | 56 => 0x95416
  | 57 => 0x94d
  | 58 => 0x139256
  | 59 => 0xb1396
  | 60 => 0x138b16
  | 61 => 0x141396
  | 62 => 0x139416
  | 63 => 0x128996
  | 64 => 0x99296
  | 65 => 0xcb
  | 66 => 0x14b
  | 67 => 0xb0996
  | 68 => 0x98b16
  | 69 => 0x168b
  | 70 => 0x98d
  | 71 => 0x1409
  | 72 => 0x141296
  | 73 => 0x12c9d6
  | 74 => 0x9d2d6
  | 75 => 0xa0e
  | 76 => 0xa0c
  | 77 => 0x130e
  | 78 => 0x10c
  | 79 => 0x134d
  | 80 => 0x14c
  | 81 => 0xb8e
  | 82 => 0x148e
  | 83 => 0xd0e
  | 84 => 0x150c
  | 85 => 0xe89d6
  | 86 => 0x9ce96
  | 87 => 0x180c
  | 88 => 0x130c
  | 89 => 0x1449
  | 90 => 0x1452d6
  | 91 => 0x145353
  | 92 => 0x140b16
  | 93 => 0x24b
  | 94 => 0x16cb
  | 95 => 0xb0d
  | 96 => 0x144b56
  | 97 => 0xb8c
  | 98 => 0x28c
  | 99 => 0x154c
  | 100 => 0x184c
  | 101 => 0x148c
  | 102 => 0x20c
  | 103 => 0xe9456
  | 104 => 0x144e96
  | 105 => 0x8c
  | 106 => 0xe8cd6
  | 107 => 0x188c
  | 108 => 0x18cb
  | 109 => 0x178b
  | 110 => 0x160c
  | 111 => 0x24d
  | 112 => 0x16cd
  | 113 => 0x40c
  | 114 => 0xd0c
  | 115 => 0x170d
  | 116 => 0xb09895e
  | 117 => 0x209
  | 118 => 0x249
  | 119 => 0x15393
  | 120 => 0x14d
  | 121 => 0x95296
  | 122 => 0x24053
  | 123 => 0x138096
  | 124 => 0x99256
  | 125 => 0x98096
  | 126 => 0x3cd
  | 127 => 0x15814
  | 128 => 0x1489
  | 129 => 0x135453
  | 130 => 0x144153
  | 131 => 0x135854
  | 132 => 0x134294
  | 133 => 0x135894
  | 134 => 0x28154
  | 135 => 0x29354
  | 136 => 0x184154
  | 137 => 0x16d355
  | 138 => 0x185354
  | 139 => 0x41354
  | 140 => 0x188154
  | 141 => 0x189354
  | 142 => 0x25253
  | 143 => 0x28253
  | 144 => 0x29453
  | 145 => 0x25853
  | 146 => 0x24293
  | 147 => 0x149453
  | 148 => 0x24bd3
  | 149 => 0x15453
  | 150 => 0x20b14
  | 151 => 0x25453
  | 152 => 0x14114
  | 153 => 0x28114
  | 154 => 0x40114
  | 155 => 0x252d5
  | 156 => 0x3d2d5
  | 157 => 0x29314
  | 158 => 0x41314
  | 159 => 0x14294
  | 160 => 0x255d5
  | 161 => 0x24ed5
  | 162 => 0x40294
  | 163 => 0x3c255
  | 164 => 0x41854
  | 165 => 0x29894
  | 166 => 0x28414
  | 167 => 0x160294
  | 168 => 0x188294
  | 169 => 0x189854
  | 170 => 0x104294
  | 171 => 0x194294
  | 172 => 0x184294
  | 173 => 0x3d455
  | 174 => 0x41494
  | 175 => 0x156d5
  | 176 => 0x15854
  | 177 => 0x3d6d5
  | 178 => 0x1716d5
  | 179 => 0x14414
  | 180 => 0x104414
  | 181 => 0x3ced5
  | 182 => 0x194414
  | 183 => 0x15894
  | 184 => 0x402935c
  | 185 => 0x281411c
  | 186 => 0x401411c
  | 187 => 0x401429c
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 45
  | 7 => 1125
  | 6 => 3476
  | 5 => 1893
  | 4 => 72
  | 3 => 8
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
  | 8 => packedAt gbK8 (1310+((h/20+packedAt gbK8 (1170+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (46707+((h/462+packedAt gbK7 (41625+(h % 462)*11) 11) % 1664)*12) 12
  | 6 => packedAt gbK6 (184294+((h/1342+packedAt gbK6 (166848+(h % 1342)*13) 13) % 5847)*13) 13
  | 5 => packedAt gbK5 (120291+((h/717+packedAt gbK5 (111687+(h % 717)*12) 12) % 2842)*12) 12
  | 4 => packedAt gbK4 (5236+((h/28+packedAt gbK4 (5040+(h % 28)*7) 7) % 104)*8) 8
  | 3 => packedAt gbK3 (656+((h/2+packedAt gbK3 (648+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffc07ffc03f00ffffe01fff463c7ffb88fe3f
  | 1 => 0xc01ff80fffffff01ffffe03fb9d3a664ff1fc7
  | 2 => 0x1ffff0003ffffe07ffffc0c1e3c7870fe3f8
  | 3 => 0x1fffffffc0000007fffffffe03f807f003ff
  | 4 => 0x1ffffffffffffff8000000fffc0007fffc00
  | 5 => 0xffe000000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x43cc00b2c20b042aa960855502040aa9886e1b
  | 1 => 0x844458055855650932aca12618d1a6603b16c5
  | 2 => 0x896ad500426b6cc24d6d984c162c7860da368
  | 3 => 0x111b3669ae801060871b1e38ee037807d001b6
  | 4 => 0x221bc78e3738d8f1c0020c10f7bc0007e6d800
  | 5 => 0x3c0204003800e081001c1020fdfbf550000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36595
namespace PEqualNP.Outside.L_meta_36595
open PEqualNP.Outside.L_meta_36595.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 3 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 24 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 117 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 24 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 24 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 117 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 22 := block_range (n:=22) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 22 := bs5_3_0
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
theorem bs5_4_352 : Interval s5Atlas 4 352 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 379 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 586 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)))) (concat (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 (concat bs5_5_384 bs5_5_416))) (concat (concat bs5_5_448 bs5_5_480) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 8 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 72 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_1888 : Interval gbAtlas 5 1888 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1893 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928))))) (concat (concat (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152))) (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888))))))
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
theorem bgb_6_3456 : Interval gbAtlas 6 3456 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3476 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)))) (concat (concat (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)))))) (concat (concat (concat (concat (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)))) (concat (concat (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336))) (concat (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560))))) (concat (concat (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 bgb_6_2784))) (concat (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 bgb_6_3008)))) (concat (concat (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232))) (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456)))))))
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
theorem bgb_7_1120 : Interval gbAtlas 7 1120 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1125 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 45 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800eeeaeaaaece8e800
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372906 * 2 ^ 32 + 3974686720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36595.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.and,[3,4]⟩,⟨.and,[0,6]⟩,⟨.or,[7,8]⟩,⟨.and,[2,8]⟩,⟨.or,[2,9]⟩,⟨.and,[0,5]⟩,⟨.and,[1,6]⟩,⟨.and,[11,13]⟩,⟨.or,[12,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3974686720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3974686720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36595

open PEqualNP.Outside.L_meta_36595 in
theorem PEqualNP.Outside.L_meta_36595 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3974686720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3974686720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
