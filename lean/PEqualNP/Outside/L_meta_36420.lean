import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36420.Model
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


end PEqualNP.Outside.L_meta_36420.Model

namespace PEqualNP.Outside.L_meta_36420
open PEqualNP.Outside.L_meta_36420.Model
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

def SBf (j : Nat) : Nat := [6, 8, 5, 7, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36420

namespace PEqualNP.Outside.L_meta_36420
open PEqualNP.Outside.L_meta_36420.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x80ee21ec21
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (34+((h/1+packedAt s0K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffe07ffff083fc3fc3fffe1fffe0113f3fc
  | 2 => 0xf07c3ff83e1fffc3fc3fc381fe1c0ffeeccccf
  | 3 => 0xff803fffc01ffffc003ffc01ffe00fff0f0f0f
  | 4 => 0x3fffffe00fffffc00001fffff003f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x6108023084001004404c048c6024621801515c
  | 2 => 0xa5104451902a0141c4144114a208a4a864c4c5
  | 3 => 0x422aa8a20d548a9c222aa829554149530b0b0a
  | 4 => 0x8a5331052906aceaaa82204199938063b00ea0
  | 5 => 0xc6221c63198cf333333327011020183dea000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcfcfcccfcccf000fcfcfcccfcccf000fcfcfcccfcccf000fcfcfcccfcccf000fcfcfcccfcccf000fcfcfcccfcccf000fcfcfcccfcccf000fcfcfcccfcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36420
namespace PEqualNP.Outside.L_meta_36420
open PEqualNP.Outside.L_meta_36420.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x30007802400000480098034000004c00a9d1418000004112536a00003c08400008158000000010011080005cc801c0000352011800001380002c60500a8000001c00000580003800000004400d005001f000000012000000000002000608000000c001ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461bf428c37a851877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea1061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20dfa1641ee42c837a85907b50b20d6a1641df32c83dc6590774cb20f699641cd32c82fca3905f54720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441df32883ba65105f94620bea8c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e84907b90920dea1241ed424835a849077cc920f719241dd32483da6490734c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041df32083ba64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6588774cb10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10ef99421dd32842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa1221bd42443be6488774c910fb20a21f541443ec62887d4c510fb10a21f521443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810ef99021dd32042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc525077e84a0ef50941ef99283dd32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083bf421077a8420f7cc841ee990837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31dfa1663bd42cc7be6598f74cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718f790e31eea1c637e528c6faa518efd0a31dea1463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931dfa1263bd424c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863de430c7ba8618df94831bea9063bf420c77a8418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643bd42c87be6590f74cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21f721443bd42887da8510eb50a21ef99443ee32887ba6510fb4ca21e6994437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c534877e8490ef50921ef99243dd32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410efd0821f721043bd42087da8410eb50821ef99043ee32087ba6410fb4c821e6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40ef99681dd32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a852077cca40ee994817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940ef99281dd32502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea1081df32103ba64205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28
  | 2 => 0x801002024018010020000208100002800005000000000050000080180000e0340000000e0000301e0040041400f0040180100600c004050010000080e800004006fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7c87a16f50f42de21e857e51d0afaa3a15f94342bea8685bf53d0b7ca7a16f54f42de29e85bf51d0b7ca3a16f54742de28e85bf50d0b7ca1a16f54342de286857d5490a7aa9215f94e42ef29c855e5390afaa7217754e42aea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f90d42dea1a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142dfa9a85be5350b7aa6a16f14d42dfa9285af5250b7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050afca8214f95042bf29885de5310abca6215f54c42eea98855d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ef21e65dd43ccbb887996fd0b32dea16657e51ccafaa3995f94332bea8665df54ccbbca9997755332ee2a665df42ccb3e85997790b32eea16659d42ccbb8859977d4732ef28e65dd51ccbb8a39977d4332ef28665dd50ccbb8a1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32aea9c657e528cb7e85197b90a32dea1465ed428cb5a851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265df434cbbc86997750d32ee21a65bf424cbdc84996f50932f6a1265ad424cbde6499778c932bfa8a657c514cafea0995f14132efaa265de544cbbaa8997715132efa9265cf524cbbe849967d0932ef21265ce424cbba84996750932e6a12658d424cbb8849977d4532ef28a65dd514cbb8a29977d4132ef28265dd504cbb8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32af298657e520cb7e84196f50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf29683ee52d06dca5a0df54b41f6a96836d52d077e85a0ef50b41ef99683dd32d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720efd0e41dea1c837e52906faa520efd0a41dea1483df32907ba6520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837
  | 3 => 0xa4480a8881aaac0411e24689743b00519cdc449ab80007c4000006ee000951b4448b0c078fc0002e4f9ad13ce8ac000005545cc45a31432dd0f71833d800139030338554000000ee5d8000946ea44c8fafe6649940026300000000000000bb5179ba000000810b40006180000035200174000632b180010d5f20000000046ca7c5b9510002a5491670a66b112b6e1d4971aa8a84c47587bb6f5fe6d4192ac458965698f93b00e8a00004940009f3470000f400120000da0000205f8000c735e1d62b4c39bb09c170819f901c5f56431f49e0000007e0000a88618100000140a752a0724310951a00c4002780003089e18b6621f4b6a201f0c78002ea000939370c057233d051ca000100001f56aea95b81710bab102584f5b85810a90e196000000000009c00034500000042000670041b6b02000000000000007688d8236580008eabf4a000179a831341a8238006025a541000048b2519952164000aa000622c341f32d396744002fa000de0002dd000a4400243470018e7000000000c92ef000d640012d000154d2800684000fc32443ed6d1eb4b00093400000000335aa0002486c0432cf50ccdd090126149bd23ab254e1055d8432925a8a710800031549b3300e0a49c8833d0568308dc3124882d800000000001110006f44789900000000000000515a71cd62ea309d800000641009e44421e119168232d24000f14260000000025e0019d000566dd9918001a6528c7a644e67c83494d5409dd6ba9650ec540000003e440848001e4d11173265e8a782b28539e14400313000c38f79015827acd91f427431d892560a8980768006ca25995b03000000709213a6620511bf58a43c532cd13888843a6d5c2c60a10f36000504fa4852e6f0b71de6522493d34c4503b0000000000000012960ac2ca78d430481da188a682da92080027a82c3d00058e348771fb0e617921000006016004028010000100000100401c010050000000280a016000000000040200600100e00009004000014010020160001d002026010028000000200182e00402407800020034000000000040800500200001016000000000000000180100100a0180a8040000080000100400800001004000000000020240180b000040010020200102d0000000000000002200c0000702a0000600e0000040002000c034020050020140300401400000013012000000000220080380001c004008060000000000c00200402800000004008060260200100a00001806804012000020050020100801a00202400808002000050010000200d01200000c000080100100000100c00c0300903803c00802004000018040160040000700a0000000a00000c068030000080300b00000c058010000340100800400006004016004008040060400180e0000000280400800000801002028070060
  | 4 => 0x36ea70468260000009b0a70e4664002fb0000740027600000000052454b98280800000b12f0641b00017b2a138c7703881e0009ed4a800030a740492e0f8cb84f0000000000000051e00000058000000fd0004527f19db516129a01100017a124bf254000000bfaca512aa48f3270b4214d081342eb009c1e50ca0b4a632104ab08728fa6a0de5338002565ad013142162c56d28e22e6e0580001400010619e0d0064379ae6c451c8207017e820ea24400066cbb80057c2f0982f02be290e1b0720e1157483540639c91a695f06450b3581e8a504728a2ae021901d034e0012933d2f6ad588162420700d520d0d637db93160ea861b327e3883a0000f50062cd1bb2528c659720ab5cabc40094b1e0a34f81310000015219d2f03681c26a000000002e0000cf98e00a69a7748027d2140000003b1c80fc001742f83d92322d6b41b4d98e33d2000ada1b3a4000ea84432a58db0800000a009b8371fa000000004fe7f80019f36c1191c9b156c09d1a9610ae5bdaf80265e36d481b95eea6db63394a2ac42f9f74ae000002de0380000001a000698001a305ed3c33b36000570f0004000b4877800078000000001302941b2ab0007b400097598b888e1930006340023a000ca0001140008453cb670721d1a907955056577021136c200027c4c2285a9800608389878000000015d00c3c2001b98004125d400000694000001cc0009157eb300fe7f400000000d7460800000af107a4016a0000000055a97c00000510a68a086667830cbd1330008016580005c06d5eb0c4d85603623b4b42ec9616c000d5800000000000001ea1460016b0000006302633500000092811068000000000000008b165000000002236442d8001d735a9c5830c444e661758be38a0010d0001a2000ec8425a0b8ccbaa64b6b64d200041c02cb90aa350b51951270f6b605798a02e600931ab3ec5989a3641980cc002ae000a888a99a26454c749a018ccfd5a0c900079800048000998ed97944c0014c0006689ac000000008f1a336b000374448285be6143004a3908505d24963a9600009d1204fc8c1e3290000b235c47c034002af690bc800170056818318d71ac8fcc2000384000460000008748315e000c68d10002880006424b234a8d3a3636c01b9020002ba001b4935158adc00000000001738163be2447f0e038e378002f54a60016d9be25000040a0538200000000000000000003fe000002555323fd6700000000000194000bb10f31b0009306521c170000ab23015ca10a18000000007d90500036545b4035e3996a85909
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x2528423d6494a109798e528425d6394a108f990528423d6414a109798c528425d6314a10cb949428432d5250a10d3949328434d524ca10e350932843a94248210f24c9208423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58854443356115110c7d53534431c54d4d109758b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425d6214d10d5584534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109b994524432f5414910cb150524434f5314910d314c524432e6414910cb590524434e6314910d358c52443656114910da580524423e65d09108f197424431f53d0910c714f424432f52d0910cb14b424423e65509108f195424431f5350910c714d424432f5250910cb149424425e65cc91097197324431f54cc910c7153324434f52cc910d314b324425e654c91097195324431f544c910c7151324434f524c910d3149324438d424c910cd15241442d563905109d19541442b5648c510d514e3144274654c510d914a21443a54288510f14ca21442746548510da14a20443e221881109e19520443a94248110f24c920443e121481109798f540425d63d50109b98b540426d62d50108f596540423d62950108fd89540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c109758a530431e5454c10c7551530425f6254c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48108f992520423d64948109798e520425d63948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520434e6394810d358e520432e5454810cb551520434e5354810d354d520432e6454810cb591520434e6354810d358d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d525081097d97320425d65cc810c7953320431d54cc810d394b320434d52cc81097d95320425d654c810c7951320431d544c810d3949320434d524c810e3509320433554c4010d554f100436552c40109e596100436952840109dd9510043355444010d554d100436552440109ed9510043695244010
  | 1 => 0x82af6550b20cbd9542c832f5350b20e394d42c832d5350b20e354d42c830d5350b20c795332c831d54ccb20e350b32c82ad648cb20cb55232c831e544cb20c755132c838f424cb20e350932c832d544cb20d394d32c82cf654cb20d3d9532c834f544cb20e395132c834d544cb20e355132c830d544cb20cb50a51c834d3294720ab59321c82cd63c872097d8d548825c63552209798c548825d63152209d984548827561152208fd91538823c6454e208f990538823d6414e209d98453882756114e20e3509328823f64546208f191518825f63546209718d51882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d20ab59242482cd63909209b195424832f6550920cb195424832f5350920cb54d42483ab6050920ea181424838d42cc920ab59232482cd638c920e3d09324838d424c9209b195324834f654c920d3195324834f544c920d355132483cb604c920f2181324823e64145208f590514825e63145209758c514832d4214520d34c8514826e65c8520ab59321482cd63c8520ea50b20483c932c81209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c2097d89530825d6254c208f990530823d6414c209798c530826e6214c209d98453082756114c208f992520823d64948209798e520825d63948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420825d65cc820c7953320831d54cc82097d95320831e544c820c7551320834e524c820e350932083365494420cd55251083565394420d554e51083374294420cd50a51083573294420d54ca51083365454420cd55151083565354420d554d51083374254420cd50951083573254420d54c9510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020d9545200827b6548020dc545200825e63d53109758f54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c432f5250b10cb14942c434f524cb10d314932c438d424cb10b558e41c42b5648c710e950a21c43c5328871097d8d548425c63552109798c548425d63152109b988548426d62152108fd91538423c6454e108f990538423d6414e109b988538426d6214e108f99
  | 2 => 0x5350840c754d421032e525084097d97321025d65cc840d394b321034d52cc84097d95321025d654c840d3949321034d524c840e350932103565394440d554e51103665294440d954a51103374294440cd50a51103573294440d54ca51103565354440d554d51103665254440d954951103364354440cd10d51103374254440cd50951103573254440d54c9511023d6590440a798e411031d5390440cb54a41103355190440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401029c6350040c754d401032d5250040cd545401027b65500409b98854cc26d6215330c715143cc23e6494b308f59252cc32e5250b30cb54942cc34d52ccb30e350932cc23e64947308f59251cc29d64cc730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b3588438c23e6494a308f592528c32e5250a30cb549428c34e524ca30d3549328c38d424ca308fd91518c23c64546309bd89518c26c6254630a7992318c23d62d51308f992544c25f63551309b988544c26d62151308f994544c2ad6215130c758c544c32e62151308f588544c32d62151308b588544c25e6590d30c7152434c25c6550d30c7151434c23e64149308f590524c23e65d09308f197424c23e65509308f195424c31f54cc930c7153324c31f544c930c7151324c34f524c930e3509324c25e65cc530a7593314c31c54cc530b358b314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c31c63550308fd89540c23e64150309798c540c26e62150309b588540c27661150309d584540c25d65d0c30c7553430c25d6510c30c7550430c2cd6210c308f992520c23d6494830cb952520c32d5494830cb992520c32d6494830cb951520c32d5454830cb991520c32d6454830d398d520c34f4354830d310d520c23f65d08308f597420c32e52d0830cb54b420c23f65508308f595420c32e5250830cb549420c31e54cc830c7553320c34d52cc830c7951320c31d544c830d3949320c38d424c830cd952510c3355494430d994a510c3655294430cdd0a510c3354294430d5cca510c3553294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430cdd09510c3354254430d5cc9510c355325443097596310c29e648c430c7552310c34d528c430d5546310c31d540c430d3548310c355510c430c7553300c34d52cc030d5547300c25f654c030a7191300c31d544c030d3549300c355514c0309ed95300c25e63d53209758f54c832e62953209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20d398a53c831e5454f20c755153c823e6414f208f59053c831e53d0b20c754f42c82cd6390b20d354e42c831e5350b20c754d42c832e5450b20d354d42c
  | 3 => 0xa21d355132887c7614ca21f118532886ad64c8621b358f218863f64542218f191508865f63542219718d508872d4254221d34c9508865e63d51219758f544865e63951219758e544866d62951218f993534863d64d4d218f992534863d6494d219b58a534878d424c9218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540872e62950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c218f992520863d64948219798e520865d63948218f597420871e53d0821c754f420866d6590821ab59242086cd6390821d354e42086e561908218fd95420871e5350821c754d420872e5450821d354d42086af6550821cbd95420872f5350821e394d420872d5350821e354d420870d535082197597320871e54cc821c7553320878d42cc8219b59632086ad648c821cb55232086cd638c821b9586320865f654c821c7951320871d544c821e3d09320878d424c821cb551320874e534c821b3d95320874f654c821d3d51320878e544c821d3551320878d544c821c3551320872d4294421d34ca51086ad64c8421b358f21087a54288421f14ca210866f65484219dd9521087a74248421f1cc9210873a5494021ce552500875a5394021d654e50087a94294021f24ca500873b4294021ce50a500875b3294021d64ca500872d4254021d34c9500873a5454021ce551500875a5354021d654d50087a94254021f24c9500873b4254021da90950087394254021da50950087294254021d6cc9500876a3254021d64c950087693254021d24c9500876b2154021dc88550087692154021dc485500865e6394b409758e52d032d52d0b40d394932d034d524cb40e350932d025e63947409758e51d029d63d0740ab58b41d02ad6210e409798e529025d6394a40cb949429032d5250a40d3949329034d524ca40e3509329025f63546409718d519026f62546409b189519029e63906409758b535026e6214d409b58853502cd6214d40d3988535025d6214d40d3588535024d6214d408f997435031c53d0d40c714d435025e63149409758c525031f53d0940c714f425031f5350940c714d425032f525094097997325025c65cc94097995325025c654c940e3509325023e65d0540a758f415031c53d0540ab58b415031c5350540c714e405025d6294c4097d89531023d6590c40c754e431031d5310c40ab588431025e63948409758e521034e5394840d354e521034e6394840d358e521034e5354840d354d521032e6454840d398d521034d6354840cb90d521032c4354840c794f421031d53d0840cb54b421031e
  | 4 => 0xb94942d065f65ccb419759732d074e52ccb41d354b32d065f654cb419759532d074e524cb41d354932d078d424cb419b98a539066d6294e41b358a539074e6294e419758a539074d6294e419358a539065f6254e41c794f439071e5350e419798e529065d6394a41c794f429071d53d0a41c794d429071d5350a41cb549429065f65cca4197597329065f654ca4197595329078d424ca41a758f419071e53d0641ab58b419063e6510d41ab588435065e63149419758c525072f5250941cb14942506b46150941d3d49325074c524c941e3509325069e63905419798c505065d63141419b988505066d62141418fd95431065e63948419758e521072d52d0841ad587421074e524c841d3549321078d424c841a758f41106ad62d04418fd954110677655044197d8d501065c63540419b98b54cc66d62d53318f58a54cc71c63553318fd8954cc66e62153319b58854cc71d54d0f31c755043cc6cd6210f318f99252cc63d6494b31cb95252cc72d5494b31cb99252cc72d6494b31cb95152cc72d5454b31cb99152cc72d6454b31d398d52cc74f4354b31d310d52cc63f65d0b318f59742cc72e52d0b31cb54b42cc63f6550b318f59542cc72e5250b31cb54942cc71e54ccb31c755332cc74d52ccb31c795132cc71d544cb31d394932cc78d424cb319b98a548c66d6295231ab58a548c71d6395231cb98a548c63d6295231cb58a548c62d62952318fd89548c71e5490e31c7951438c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c71e54cca31c7553328c71e544ca31c7551328c74d524ca31e3509328c69d64cc631c7953318c6cd62cc6319758e544c66e62951319b58a544c65e65d0d3197994434c71d5410d31b3588434c63e64149318f590524c72f5250931cb149424c74f524c931d3149324c78d424c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c3197d95430c71c5450c318f992520c63d6494831cb949420c72d5250831d354b320c6d561cc831e3509320c63e64944318f592510c69d64cc431b358b310c65f654c4319dd95310c63f64540318f191500c65e63d53219758f54c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e53d0b21c754f42c871e5350b21c754d42c871e54ccb21c755332c871e544cb21c755132c878d424cb219798f548865d63d52219798e548865d63952218f993538863d64d4e218f992538863d6494e21b358e428872f6550a21cb195428872f5350a21cb54d42887a76150a21e9185428878d42cca21ab592328878f424ca21e3509328874f654ca21d3195328874f544c
  | 5 => 0x50d0b4e6294e42c794f4290b1d53d0a42ab98a4350b1c5350d42ab9884350a9e6390942a758e4250a5e63d45429758f5150a5e63141429758c5050a7661141429d5845050aad6294d42ad9865350ab56194d42abd895350b1d5314d42ab58f5250aae61d4942ab5835250a9e63d4542a758f5150a9e6394542a758e5150b355114542a7d8d5050a9c6354142add855050ab46154142a798c5050a9d6314142ad9845050ab56114142c794f4210b1d53d0842d354e4210a3f6550842c794d4210b1d53508429bd954210b2e5450842d354d4210a7661d53329d58754ccb1c5450f32c755043cca3e64947328f59251cca3f64543328f19150ccacd62d5332b598754ccad561d5332c755054ccacd6215332e3d8942cca9e64d4732a759351cca9e6494732a759251ccb555114732a7d9150cca9c6454332a799050cca9d6414332b598450ccad56114332cb98a548cb2e5450a32abd95428cb2f6550a32c7953328cb1d54cca32cb50a518cb2d42542329d986544ca75619513297997434cace62d0d3297195434cb1c5450d32c7550434cace6210d32ab592424cace63909329b195424cb8f4350932e390d424cb8d4350932e310d424cb2f6550932cb195424cb8f6350932e318d424ca9e648c932a7592324cb8d428c9328f993514ca3d64d4532cb508514cb2d42d41328f990504ca3d64141329d984504ca756114132b358a544cad66195132b5586544cacf6255132c7550544cacd64d4932b3987524cacd60d4932e3d4b424ca5e6590932a7592424cace6590932d3996424cacd6490932a3592424cace6190932b3582424cb8f6250932e3d49424cace6550932b3195424cb8f6450932e3d51424cb8c5450932b3185424cacf6050932e3d95424cb8e6550932e3595424cb8c6550932e3d85424cb8e6150932e3585424cb8c6150932e3d81424cb8e6050932e3581424cb8c605093297994424ca9e6410932b3988424cb8d4210932a7993514ca9d64d4532e350b514ca9e6494532a7592514cb8d4294532e3509514cb8d4214532d5544514cb8d42d4132e350a504ca9f6454132a7191504cb8d4254132b5d85504cad46154132a7990504ca9d6414132e3508504cad66114132b5584504ca5e63d50328f596540ca3e64150329798c540ca6e62150328f992520ca3d64948328f597420cb1e53d08328fd95420cb1e5350832cb949420cb1e54cc832c7553320cb2d548c83297d95320cb1e544c832c7551320cb8d424c8329bd95320cb2d544c832d394d320ca5d6294f4197d8953d071d5390f41c754c43d06ad6210f419798e52d065d6394b41d394e52d074d5394b41d398e52d074d6394b41d394d52d074d5354b41cb99152d074e6354b41d358d52d072e4354b41cb10d52d071e53d0b41c754f42d072d52d0b41c794d42d071d5350b41c
  | 6 => 0x98a501b9d41e72570000000a31f52180dd8b91a389f12794382317e022a119e101d9fe863a0a1b81d2a8c1671848001da8e598d8e69bf8ec01e2811481be11602d80027e15f2759c79b60000000001d686419500014b2109479b40f60138751a90000c70ea87693aa2b00020621200029418f0709f41019450001d000024f224262169a6a8d781b0000f3a748091271c00d213590a8000000e7a8280000003480028a85c16e27400797d152a281b3a8303d9e828f94ea6f0390080809860038000000cc0180201c00c0080005800c1f8020520000100d000004000170000180200f000000000110000200080200a0400a0000060040000100000410801004014190000060000481800204c068000060440000000a00007000000008000000040400101700203c0080101606c1f8080000000180700000000816014000060380080041b80106200c008030020700000401000c0100300405c0000500e0000002f01600c000010040281000100c05c0201101a0002787d0000041b80309a094000050020040501e00401c0081601a000000040020500580c0100041000505605c0080a00a0600300700a010010020000e80080300000c0200e0001600d0010080580001a0000301d0000000000500102800001800002024018000020000000000201403018000004000000080000181700801c0180001c05c0100204a010008030080040000701001802802052008000000000000580200000c0281500001003813062010020050000140d80a06400c01000006000000000140000883b01004400808002000000040020040100000200011863012000000140000000080a0000140b0000080301400400a0000280d0540080000901a150008170000380a8030060103b80000c06c00000054020010270000000080b028000020260000000380a0200700000201a000008780000300002a10802c0000502a010028240100041d00f008000028010020080480606e014040040000040000d00800402001014008008140160080402001a0180480000e00c0500400800c0480b00c000020000100141100200200800800000000040010000081280d00a00401001004010038000680080802b9b98b5150e6d62d45439b9885050e6d62141439d9845050e756114143a75924310e3f6550c4397d954310e9f6550c43c7d954310e9f6250c43a7d854310e9c6050c43e350e5210f1d4354843e350d5210f2e6454843d398d5210f2f4354843d390d5210f2d4354843d350d5210f0d4354843c750e5110f1d4354043c754c43d0a5e63947429758e51d0a5f63543429718d50d0aad62d4f42ad98753d0ab561d4f42c754c53d0aad6214f42a798f51d0a9d63d4742a798e51d0a9d6394742cd54451d0a9f6354342a718d50d0a9e6314342a758c50d0ab66114342ad584
  | 7 => 0x9a404fa2f9e1a0695622a0668a617121423a93d9078be8290688d922708b0d51961ba86b199a939e308f1432018f10a91a2a610d615e0191ea82ba7f9ec1b009585689829d8399099429311a72358bd85793e8de1c5a7e84a9e20f709d9f11c280d8f917026e1908822581c71a589502821325da5f8718df9590840721770fd0792040af11e2538189ab8468001e09761461e500006ca0f2252900d29120130741ac1cf84205608600019900120821f27988009b04a27389280010c89600000000003d0001418c788fa4702483724a09b9872188eca680c39130cc208a690948111a699192c26ca71a0920d14898c11e8002339c0864a988000e0840a289f20000d888b87600000001f8f30b58099300dc9fd00007c0ab1fa12ba9528700002c0f49ed27d9c123b0000000001b28521411810000000001de13b0118fa9bc9a800006e13603500011793d28500000000003b0cd800266179a8593924e26495b93e1660e921f938a408771a193c9e90001fe0001011f80fc8da0b39c480011d0001caa890000000002468ba87f80006628d00016800b91480000019000000000016f0f5820a559598218000000a700000012695080000023300000013684909a9068001d50002020220149dd0630999752999531a2055986a04a260001fc17fa8391517aa789f920c0c30c227015d9558000419580df0bb02b08582396482f8cfa8b10d91f8dc0cba2d15025105187b00008803800283080000026d24383a0000b8091a38188a16a9c982100a6da8895114d23d9ada3f0f09570e60001b915a00e0f7a1b9190ad219a5027a00012128401589300013f8d38ae0000a127080000000026b96020d806a5680000480000000000029718900000003226400000012986803380013725080c294a2d80007993285b13182421b1f59fb25c800075a678991c60001ff27686200026680005080019d800071055000158a969471f485d97e8ce80007d8000001ac97a0000001189220590000698000000001ee8000d980000000000002d0000000c80000000001a100010f0000002848000001f886fa4c85b9e28c98000000001241d119306c1ed9bf0b980004280002e8aa0001669b70b70bc9b129d22f0000a28000ee22594a0fe16d0f89468000e995b00009897c000128a6710590b14998a2860e8a3e2929218000818610001dc8e100a8001250000fda052629550250ac2098bfa3d16400005001a8c6104a38a639d706908e8000d10c48b505418b0000f016517318a80a1e78fc27120b1cd1e8a3189200027f12ca5497f08a9808ada600851e00001789c400003f27a8968c08000000000ff16f89018501507ca0c90423402a0f405e1c50a80870d81ef0001b98fa0000b29d899b8000f284d0fb88c230175a0e11f05300020f80011c2791139b8952000265848a6
  | 8 => 0xd321e21d85a8e481e8ed81c08e00027624b1cb18ea23a4907a26e90ba881d91539e3a1609707020310c0c89060b1a9c0498aca1488a0939af92000017080026c19804ea6091109f8000d4a2914929aa7c25ba8b8001b30d199a11724da2b8539e58000ab8318ed03602c82a909000102a588000060000000cf01400018f9b5800061a7b0831b7a4787480021a9768e380426fa8004e03a957a079238000c680022196186f00005fa0b90800000023900006780028f1978001f09dd837a770fb00012e28c925a5e8f6a42a311449928c59c910d05812a8730eb80b0f18261ee0a5835a101eb8300510b114403f9628db0019fa8b695c81d1421e492d0000b406a8cd26b22e99e80017208280025f1cf1b081082593a0000000e224484b96a832935072a599b69e60038479c981c9e68482730d084615686d1780de828a3e9dc0ff8002990fe8000e71df89d0e81c880024b99f95d012059a12a0005a25196e897a4104389083313088da3710321a29a0c505ea618ea1719728001881a786096c94c02108c97417d91ca46000177a910898451ab00009e88480028086511012b0001d30002208000000000a00a99631020000000000000da8001da00028ea5b03691a8868001a50f800000000012614da90a15a0e8c19ad1f39228e500014fa27a3fa0a8b498b9d787d0001bd07380016c03c1878810d003b8dd05d27816b29219f1d191b98c8b78f5054a9b9ce017a2025504d93f13c1f02869381bda820bc0a39bb9910eb29b1828bb8002299a325794ca1511d86719a9291ae8279be8a49cc8198c90e31c1951a37a3a0a41859089c20be0b01398a89791940ba22307e1818e29339688e417b8a21d604f0aea728e18d724d19c0459ce9eb2269db91087b93494f027277a1e9ef97b1a4a1900598423c16b98e21117c84702690025d1a610e8ee8c4275297803008920994918196a688c124512488895f841235232a5619e15400004024f81712f86d9159b518380027218d1f607e8589e40529a99d3a0394083e80019b1ea23c89e26315ea9300d0a7a958cc8e021d03ca059ec9af0a08000f98000000001d496d96109100ca138162432528001738ca23214b9a00f221c9bc0ef84b13b94e00007802027d195a6508d0b080013780f23080020280000018329810a0db99c8000d400000009c2211f70001f287a91400000006b92d8940000000000001c69d0a540001f30000000000000001232878000001c801a00024400014a80001800000000000008916380005f0000000bf0001e99898b88000000001cc1b180011680022a8021801f69939fb9c3a7c8001cba418a19690658c00aa9cd9fc87799722ca5a883816932162167a9628a10fa009a8a4222e1341d80afa24a6a1df02f2171402348c28389bb1071c32522591ae1aaa7b81f16596083e1b4
  | 9 => 0x2011f79921ca2399f9911a1793309a0b30070bd00e8441de91a11b24e95c0602229d221c04305c8ef16a1fd86286a24c1aa0d5a4000090e1b2198887a5e0a6a4885700524982e1050448b20298102070788cb0b628d8000128002459d592a23600004c0d69ba25a24a80f9748ca9f189c9128000000ce25329184ca5c236a2203415a9549a09d99ff91992800019d28180000024803106e80028e12f07f1db00014590380000028980012e80023ba2c0
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x98e0d6358a548c70739ac52a463835cd6295231a1ae52a48718d0d72951438c686b94a999463435ca544ca31a1aeaa126518c1d76953318c686b94a998c638395162cc631c1aa8b108698d0d74149324c742a10c299263235ca648c531a1ae42a28618d1970151430c616b90c8a8063435cf6550a21a1ae9b2a6510e0f635095088707b2264a8443135ca63d512185ae5326a690d2970d4d4208686baca6a10438359542cc821a1aeba126410d4970d513208686baca899043c254d4294021e12a8994a010f09424ca5008695baa84a8043c294d4254021e12a6a12a010d4b754c950087852a264a8043c25513254021a92e7212a010d61719095008784a1664a80434a5d23254021ac2e3192a010f0b424c95008784a1264a80434a5d32154021a92e790aa010f214288550087a099442a8043c8d092154021e866490aa010c4d7298e51d0286b9ca4a1481235ca6390640c1ce8b10a6a060d745885350286b90a7a1a81435c85350d40a1ae429e84a050d7214d425030732a8499281435c853d0540c18a6b1682a050d7214d4150286b90a7202818354d6210c40a1ae529a842050d739494210307b2a8499081c15093294440a4ae421aa220705424c95110246b94c7208818398d5290440c2cc6a8c822048d7218d401030631aa4a00818518d5150040a1ae42a2879842d7299251cc307aa2c421c61435d2524ca3091ae5324631860d63588544c30739ac42a261835cd6215130a1ae42a4869850d72151434c286b90a999261435c8544c930a1ceaa12649841d76153314c286b90a998a618315162cc530a1ae42a2629850d72152304c286b90c6aa061835516210c30a1ae52a2641850d74949320c287baa8499061c15093294430a8ae421aa218705424c9510c246b94c91886107dd9548c430c1cc8a94621861664546310c246b90c898061071d9544c030c18c8a92601861464545300c286b98caa12410b1d95350920a48e2a9a84905a1711814248286ba0ca99241131d9544c920a88e2aa264905c1711813248306b1a8428a41835913214520a1ae7292841050d725513208286ba4a49904143dd5424c820c1ecaa126410705424ca5108382a1264a88418a5516008420c92a6b00421044d7298f54c4216b94c9a9e21435cc5250b10a1ae8292658844d7218d5484216b90c8a9c21435ce5250a10a1ae9292650860f64d8f5244306b22c6292218a5916014910c92c6b00a488661615805244286b90a6a1221435cc5250910a1ae42a2648850d7414932442873aa8499221431d5424c910c1ccaa12648860c6550932442923aa8510a21511d53288510c50caa124088648654c92044306b22c729021835916354810a1ae529a840850d739494204286b94a899021435d2524c810a1eeaa12640850d755093204307b2a849902183595424c810
  | 1 => 0x698e0000001b6d72c000a6dc5f9d4bc4c44240d2c37108c16972d9d902003d2a1400d4037400c45a8280cc84f10d5c605d1a000b216820c4295e2d0a4002b27148003c361520918b406a4859a38fe1c2487d5a853699d24a768b30324f559cd226f44a7cf2cb4e98c6c6508318e4981fb505644098e88ed3461859a22138005c4d5812d46770b95404bb0008440166515142000600108000020c002a3e000820000258dcd61f2a88428709684800000001e576fb3c00ac4a2c400000c000b2000e8113687001b0fca64a9c40a3813324fa8d71a6460645bb39bcd25b0041c5c001ed7a000a8006eb819a89346b1a2bc06e05f1445e3b0a140e0326c8f08a00331d1aa8a62800004e5280000003501d26000000000000006d82006d23c3c5f41300724a45a198400000b000405c9748c121e8444a0004402000184c10010000000000980c12011581c0e021500c080a0000c1a0700000000004028021f0d87800001581c0203020040a0402820421b038240c0500004260202028040302004000202008240c00008061491ae5b0a8621c8d721814310e4ab88c0a188743dc94354843a1eeaa1aa421d25719915210ea2b8cc6a908743dd94354843a1ee2a1aa421d0c7050d5210e8bb8a87288878354d6214f4291ae730ea4a148f735835250b06aa2c42a665831954350932a4ce3b2a849948d74987524ca47ba2c1a9265319c66550932b0ce3b2a849958571d95424cac338ccaa1265615c66550932c1aca32a849950e75d85424cb42b08c2a126561dc56050932b08e2b02849950e75181424cac3388c0a1265615c4605093291eeca16a29970542544514cb42a16c2a8265a1508615413291eeca10a09968542984504cb42a12c2282658354d6210f41a1ae529a85a0d0d7394942d0707b2a8499683839d16294e41c1ae8b14a720d0d7294f4390686b94a6a1c83435ca53d0a41a1ae529a8520e0d655093290686b94a7a0c838394d62d0641a1ae629284a0d84715093250646b94c720a83135c86354041a1ae431aa998e0d5458843cc686b94a899663435d2524cb31a1eeaa1265
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xc5011870050b4a862001a2018d90581dd94354843905811c14354843a05819d16294e41a05819cd629523180d8795162cc631a05819d16214d40a058298d5190440a058218d5150040a05819cd621513080d8715162cc53080d87991528c430a0582991518c43080d87191524c030a0582191514c030
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
  | 2 => 14
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | 2 => packedAt s1K2 (i*60) 60
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (6+((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s1K6 (802+((h/14+packedAt s1K6 (704+(h % 14)*7) 7) % 99)*7) 7
  | 5 => packedAt s1K5 (27286+((h/296+packedAt s1K5 (24030+(h % 296)*11) 11) % 1175)*11) 11
  | 4 => packedAt s1K4 (55826+((h/446+packedAt s1K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s1K3 (11856+((h/76+packedAt s1K3 (11172+(h % 76)*9) 9) % 274)*9) 9
  | 2 => packedAt s1K2 (860+((h/4+packedAt s1K2 (840+(h % 4)*5) 5) % 18)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfe1ffff0ffff87f83f0fc3ffe1fff83f44f3cf
  | 2 => 0x3fe1e1ff0f0ff87fc7f0fc387e1c3fc7bb4d33
  | 3 => 0x3ffe01fff00fff8ff800ffc07fe03ff8c38e3c
  | 4 => 0xc00001fffff0000fffff00007fffc000fc0fc0
  | 5 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2000010000008000001004800240800001045
  | 2 => 0x84484222241500814310441122089286194512
  | 3 => 0x2884954442aa441a9888aa8255412530c28a28
  | 4 => 0xa1d55988aa83552cedaa220479938192ec0f80
  | 5 => 0x3119910ecccc664f36ccf32711020624f7e000
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaaafaa0fafafaaafaaafaa0fafafaaafaaafaa0fafafaaafaaafaa0fafafaaafaaafaa0fafafaaafaaafaa0fafafaaafaaafaa0fafafaaafaaafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36420
namespace PEqualNP.Outside.L_meta_36420
open PEqualNP.Outside.L_meta_36420.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x9d43
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | 3 => packedAt s2K3 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s2K3 (17+((h/1+packedAt s2K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc3fe1ff0ff87ff87c3f87f07f0fe0fff53333f
  | 1 => 0xfc1fe1ff07f870f8fc3f87f87f0ff0e0adcdcc
  | 3 => 0xffe001fff8007fff003ff8007ff000ffce0e0f
  | 4 => 0x1ffffff80ffffc000007fffff00f00ff0
  | 5 => 0xfffffe00000000ffffffffff80000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x48402012100800004048091110122222011115
  | 1 => 0x88c4022231008108441882313104624605454c
  | 3 => 0x118d5544635568bb223550626aa0c49cce0e0a
  | 4 => 0x3311998886442ad5aa8440844cc98c08f00aa0
  | 5 => 0x2219110cc4664ce6b32664c608810810faa000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeeeeeeeeeaa00eeeeeeeeeeeeaa00eeeeeeeeeeeeaa00eeeeeeeeeeeeaa00eeeeeeeeeeeeaa00eeeeeeeeeeeeaa00eeeeeeeeeeeeaa00eeeeeeeeeeeeaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36420
namespace PEqualNP.Outside.L_meta_36420
open PEqualNP.Outside.L_meta_36420.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x28000000ce04008c0053e4832900994003c6c71510000213234d0c26012980e005912050001009c00f04584a43a890002e00a00008509c081184203ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xe80100a0000000000000000000000008e010b001a0f000b8000000000001700098000078005800004000a99000d80001400089800000013861980000000148f838008000c1095800011801c800000020281800000169880001f80000000000d208012931f1d800007001b000c9c001780000900031d001e1b9615200480110000001e9a8000000006800012000000050000000000800180400001014100000100018000000001c0c06dca5a1db54b43b7294876d5290eeea2a1dd14543cea18875e53d0abaa7a14f953329eaa6655e53106baa620db94841b6a90837a50106f2a020cf950319eaa0636e520c6daa418de94031bca80637a50886f2a110dd94640baa8c816f52502d8a4a05794c40aea98816e52102daa4205d94440baa888176518c2eaa3185bd4930b6292613e540c27aa8185b94830b6a906176510c2eaa2185d94620baa8c413e540827aa8105794c20aea98417651082eaa2105b94b10b6a9621e652c43caa5885d54610f9a8221f240443e280887c8c110f898221f320443e040885d94410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x64080200a029c5805150ee262d4110b818940442e0624c110ac59020442d16308110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (756+((h/14+packedAt s3K5 (672+(h % 14)*6) 6) % 56)*7) 7
  | 4 => packedAt s3K4 (1958+((h/22+packedAt s3K4 (1782+(h % 22)*8) 8) % 151)*8) 8
  | 3 => packedAt s3K3 (236+((h/2+packedAt s3K3 (228+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fe1ff1fc3fe3fe1c63f1f83f8fc1ffe13333f
  | 1 => 0xe1fe0fe3fc1fc71e07c7e3fc3f1fe1c02dcdcc
  | 2 => 0x1fff003ffe007fff807fc003fe001ffce0e0f
  | 4 => 0xfe000003fffff81ffff800003ffffe01f00ff0
  | 5 => 0xfffffffc0000001fffffffffc0000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x44242020484040000209048888244444011115
  | 1 => 0xc444620488c40822024321189908c48c05454c
  | 2 => 0x9888c649118c960ec806483132418938ce0e0a
  | 4 => 0x8198892221802555490004224931811700aa0
  | 5 => 0x11110c0033112499a524926300021021baa000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefeeeeeeeeea0a0fefeeeeeeeeea0a0fefeeeeeeeeea0a0fefeeeeeeeeea0a0fefeeeeeeeeea0a0fefeeeeeeeeea0a0fefeeeeeeeeea0a0fefeeeeeeeeea0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36420
namespace PEqualNP.Outside.L_meta_36420
open PEqualNP.Outside.L_meta_36420.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x11200200002800000067c00000015804e3401d3438028484000c389400914994912a802160e19505360001844051970084c8b3c000131e24054100710000400000fff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41f741fe41fd41fc41f441ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3800d4015920d80088740000bc195129151800fd4c2c24480400351d11240000c8ac00008060007000580000644401053c2168cc4c080000dc00d13000014400a000b4b8000000b138315ce4e041607ce9410148549c001c940028005c68a80c8411348c00010cc4ec006d64f4010800507800012c00149000f000f8c03c0000000154a49800020a060614020200340e100a1000120000005002020002000000020a056e52d0edaa5a1dd94643baa8c87775150ee8a2a1d794f42aea9e85765190aeaa3215dd4542ba28a853e540ca7aa819734c832bb2886575510caf4a0195e54032baa86837651906bca620d754c41b7290836d52106f4a020de54041bb2a083b654107aca620f554c41dba1883b543107cca420f954841dba1083b542107e4a020dd54041f8a808371501067ca998cf553319f2a6433d54c86eca3205d54640da20c817751502e8a2a05794c40aea98816e52102daa4205d94440baa8881b441102eca3185d54630b7a92616c524c27ca8184f55030b7290616d520c2eca2185d54430bb28c417551882bea6905714d209f2a0413d54082bca6105754c20bb288417551082eca9885d15310baa8c213f5444278a8886dd5110bb2a221745444368a8884d15110f9a8221f240443e280885d94410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x94400380000a16600900880baa000000020b08c0000000069c79298a00400000000c18000000300000800107493254032a958b43107455354841a558f42107525354041d454d50107625254041d854950107334354041cc50d50107334254041cc50950106b16010640c554c411032552104408d191518c23464546208d99254443166315110c558c54443266215110c958854443316015110cc15240442706550110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x810004c001485cb4354041a22e7a12a020e05635885444308b1ac02a221885896015110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 4 => packedAt s4K4 (2697+((h/30+packedAt s4K4 (2457+(h % 30)*8) 8) % 133)*8) 8
  | 3 => packedAt s4K3 (998+((h/8+packedAt s4K3 (950+(h % 8)*6) 6) % 52)*6) 6
  | 2 => packedAt s4K2 (249+((h/1+packedAt s4K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fe1ff1fc3f1ffe18e3f1f81fc707ffe1330ff
  | 1 => 0xe1fe1fe3fc01c71e0fc7e3fe1f8070e06dcccc
  | 2 => 0x1ffe003fffe07fff007fc001fff80ff8e0f0f
  | 3 => 0xfe000003fffff81ffff800001fffff01f00ff0
  | 5 => 0xfffffffc0000001fffffffffe0000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x44244020482200000209048444101224011055
  | 1 => 0xcc4cc60488e48a260643211c5c83264c254ccc
  | 2 => 0x90808a491140940a90064828892500988e050a
  | 3 => 0x8191492228102552c900051124a4c01700aa0
  | 5 => 0x1111180033092499c9249261800c0811daa000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeefeeefaa0faa0feeefeeefaa0faa0feeefeeefaa0faa0feeefeeefaa0faa0feeefeeefaa0faa0feeefeeefaa0faa0feeefeeefaa0faa0feeefeeefaa0faa0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36420
namespace PEqualNP.Outside.L_meta_36420
open PEqualNP.Outside.L_meta_36420.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x3401900980005000000308401b009002a3a00000003c12200000000000000288cd0000000250c406000000000020100000002a91038f802a00e0000281930e00bab4e000000024000087801600008921600000000000100000808000001010604081ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41f741fe41fd41fc41f441ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xb313b091b00530030000014410044081f2c4c1800074f56170043523d1d00000440160236482d1e0019513825122e0f0e4a00470023240005000032372a581c01394e49350000213e3c34555950450029220c2f2813203a060a15005a4b334d03460d542700422b3f1a571026110800000042810501065802032280034c1800206385830008382016e52d0edaa5a1dd94643baa8c87775150ee8a2a1d794f42aea9e85765190aeaa3215dd4542ba28a853e540ca7aa819734c832bb2886575510caf4a0195e54032baa86837651906bca620d754c41b7290836d52106f4a020de54041bb2a083b654107aca620f554c41dba1883b543107cca420f954841dba1083b542107e4a020dd54041f8a808371501067ca998cf553319f2a6433d54c86eca3205d54640da20c817751502e8a2a05794c40aea98816e52102daa4205d94440baa8881b441102eca3185d54630b7a92616c524c27ca8184f55030b7290616d520c2eca2185d54430bb28c417551882bea6905714d209f2a0413d54082bca6105754c20bb288417551082eca9885d15310baa8c213f5444278a8886dd5110bb2a221745444368a8884d15110f9a8221f240443e280885d94410
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2e28000e68092030659ea182009a2502a9c01213002c40a530000133493254032a958b43107455354841a558f42107525354041d454d50107625254041d854950107334354041cc50d50107334254041cc50950106b16010640c554c411032552104408d191518c23464546208d99254443166315110c558c54443266215110c958854443316015110cc15240442706550110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4008c01001485cb4354041a22e7a12a020e05635885444308b1ac02a221885896015110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (802+((h/14+packedAt s5K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s5K4 (2667+((h/30+packedAt s5K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s5K3 (990+((h/8+packedAt s5K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (249+((h/1+packedAt s5K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1fe1ff1fc3f1ffe18e3f1f81fc707ffe1330ff
  | 1 => 0xe1fe1fe3fc01c71e0fc7e3fe1f8070e06dcccc
  | 2 => 0x1ffe003fffe07fff007fc001fff80ff8e0f0f
  | 3 => 0xfe000003fffff81ffff800001fffff01f00ff0
  | 4 => 0xfffffffc0000001fffffffffe0000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x44244020482200000209048444101224011055
  | 1 => 0xcc4cc60488e48a260643211c5c83264c254ccc
  | 2 => 0x90808a491140940a90064828892500988e050a
  | 3 => 0x8191492228102552c900051124a4c01700aa0
  | 4 => 0x1111180033092499c9249261800c0811daa000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0feeefaa0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36420
namespace PEqualNP.Outside.L_meta_36420
open PEqualNP.Outside.L_meta_36420.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1802601e381e397803ee8007622c01c14896232200339500800018f44174ac16a46e99a1b3ab868076842896cc80ab0058a00669d0000000d193054f355440904526a300830e040001608003105c0876638382027fd5007fe54007f55007fc54027fd4c05fe53007f54c05fc5301ffd0c05fe43007f50c05fc43027fd4801fe52007f54809fc5201ffd0801fe42007f50807fc42017fcc801fe32007f4c805fc3200ffd4403fe5100ff54403fc5100ffd0403fe4100ff50403fc4100ffcc403fe3100ff4c403fc3100ffc8403fe2100ff48403fc21027fd4001fe50007f54009fc5001ffd0001fe40007f50007fc40017fcc001fe30007f4c005fc30007fc8001fe20007f48001fc2000ffc4003f71000ff84003fd10007d44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xa4001bf9852007ffac29003efd614801ffe30a4001bf1852007ffea29003ffe514801ffea8a400fff1452007ffe829003ffe414801ffea0a400fff1052007ffe629003ffe314801ffe98a400fff0c52007ffe429003ffe214801ffe90a400fff08520097fea090017fe5048001fea824005ff1412008ffe8090017fe4048001fea024005ff10120087fe6090017fe3048001fd1824000ff4c120007f26090017fc3048001ff9024000fec812002ffc4090017ee204801fff882400ffdc412002ffc209003ffd104800bfe0824005ffd942002dfeca10017fe65080097f3284005df99420024fcca10017fd65080017eb284005df59420004faca10017fc650800b7e3284005ffd902002dfec810017fe64080077f3204005ef9902001d7cc810017fd64080017eb204005ef590200057ac810017fc640800b7e320400dffd5020067fca810003fd5408019fe2a04005ffd8c2002dfec610017fe63080057f3184005f798c20015bcc610017fd63080017eb184005f758c20005bac610017fc630800b7e318400dffd4c2005ffca610003fd5308017fe298400cffd0c2005ffc8610003fd4308017fe218400ebf9882006ffea410027fe5208001fea904009ff14820067fe8410027fe4208001fea104009ff1082005ffe6410027fe3208001fe9904009ff0c82002ffec210016ff610800bff3084001bf9842002fecc210006f6610800bfeb08400abf5842002feac210002f5610800bfe3084005bf18420057fea21002bfe5108015fea88400aff14420057fe821002bfe4108015fea08400aff10420057fe621002bfe3108015fe988400aff0c42004ffe421002bfe2108015fe9084009ff0842002dfcc010017ff500800bff2804005ff5402002ff8a010017ff400800bff2004005ff5002002ff88010017ff300800bff1804005ff4c02002ff86010017ff200800bf79004005ff8802002ff44010017fd200800bf69004000fe4802002ffe2010017f7100800bff0804005ff4402002ff82010003f76544011fb32a2000fd59510047e8ca88003f7644400ffb3222000fd5911003fe8c888023f7544400ffb2a22000fd5511003fe8a888003f7634400dfb31a2000fd58d10037e8c688023f7534400dfb29a2000fd54d10037e8a68801ff7434400dfb21a2000fd50d10037e88688003f76244001fb3122000fd58910007e8c488023f75244001fb2922000fd54910047e8a48801ff74244001fb2122000fd5091003fe8848801bf73244001fb1922000fd4c910037e86488007f760440037bb022001fcd8110047eea088017f65044001f92822000fd54110007e2a088017f4504400ffba022005fd90110007e48088003f54044001f8a022005fd10110037ee6088017f63044001fa9822005fd0c110007ee4088017f62044001fa9022005fd08110
  | 1 => 0x3fd43c802ffe21e4019ffd4b2004ffca590003ee52c8001fea964000fb54b2004ff8a590063ff42c8013ff2164000fb90b20007fa8590003ed42c8013fe2164017ffccb2004ffc6590003ee32c8001fe9964000fb4cb2004ff86590027ff61c801d7fb0e400eff9872000dfcc39003bfd61c801d7eb0e4009ff1872000df8c39003bff51c801dff28e400eff54720077f8a39003bff41c801dff20e400eff50720077f8839003bff31c801dff18e400eff4c720077f86390027ff21c801dff10e400eff4872004ff84390067ff50c800bff2864000ff5432002ff8a190063ff40c800bff2064000ff5032002ff8819005fff30c800bff1864000ff4c32002ff8619003bff10c801dfb8864005ff84320077fa2190017fc10c800bffb2c4005bfd962002ffccb10012fe658800bfeb2c4000bf5962002ff8cb10016fc658800bffb244005bfd922002ffcc91000efe648800bfeb244000bf5922002ff8c910016fc648802dffaa44015ff95220007faa910057fc548800bffb1c4005bfd8e2002ffcc71000afe638800bfeb1c4000bf58e2002ff8c710016fc638802dffa9c4014ff94e20007faa710053fc538802bffa1c4014ff90e20007fa8710053fc438801f7eb144016ffd4a20007fca510003fd528802dfe2944015ffd0a20007fc8510003fd428802bfe2144014ffcca20007fc6510003fd3288029fe1944005ffd862002dfec310017fe61880037f30c4005fd9862000decc310017fd61880277eb0c4005fd58620005eac310017fc618800b7e30c4013ffd462009ffca31004ffd5188027fe28c4013ffd062009ffc831004ffd4188027fe20c4013ffcc62009ffc631004ffd3188027fe18c4013ffc862009ffc431004ffd2188027fe10c4005bf9822002ffea110017fe508800bfea844005ff1422002ffe8110017fe408800bfea044005ff1022002ffe6110017fe308800bfd1844005ff4c220007f26110017fc308800bff9044005fbc8220007f64110017ff108800bfb8844005ff8422002ffa2110017fc1088001ffb2a4000bfd9520097fcca90012fe6548001feb2a4000bf59520097f8ca90012fc6548001ffb224000bfd912008ffcc89000efe6448001feb224000bf5912008ff8c89000efc6448025ffaa24011ff95120007faa890047fc5448001ffb1a4000bfd8d20007bec690002df6348021ff31a4002bf98d20007fac690002fd6348021fe31a4002bf18d20007b8c69000adc6348025ffa9a4010ff94d20007faa690043fc5348023ffa1a4010ff90d20007fa8690043fc4348025ffa924000ff94920007dca490003fd5248001f6a924012ff1492008ffe8490003fe4248001f72124000ff50920007da8490047fc4248021ff9924000ff8c920007dc6490003fd3248001f69924010ff0c92007ffec29003eff614801fff3
  | 2 => 0x3002df8cb18017ff648c00b7fb246005ff9923001dfcc918017fd648c0017eb246005ff1923002df8c91807fff548c03dff2a46000ff552300f7f8a91800afd638c005ffa9c6002ff94e30017faa71800bfc538c005ffa1c6002ff90e30017fa871800bfc438c00bffb146005ff98a30005fcc518017fd628c0017eb146005ff18a300fffea518003fe528c001fea94601fff14a300f7fe8518003fe428c001fea14601eff10a30017fe651800bfe328c001ef1946002ff4ca30017f8651800bdc328c00bffb0c6005bfd863002ffcc318006fe618c00bfb30c6001bd9863002ffac318076fd618c00bfab0c6000bd5863002ff8c318016fc618c03bffa8c601dff946300effaa318077fc518c03bffa0c601dff906300effa8318077fc418c005ff98c6002ff8c630017fa631800bfc318c03bff90c601dff886300effa4318077fc218c00b7f3046005ffd423002ffca118017fd508c00bfe2846005ffd023002ffc8118017fd408c00bfe2046005ffcc23002fbe611800bfb308c00bfe1846005fe0c23002ffe2118017f7108c00bff0846005ff4423002ff82118003ff654c0017fb2a601cff99530025fcca98003fd654c0017eb2a601cff19530025f8ca98003ff644c0017fb22601bff9913001dfcc898003fd644c0017eb22601bff1913001df8c898073ff544c037ff2a26000ff551300dff8a898016ff634c005ffa9a6002ff94d30017bca69800bfd534c001eea9a6002ff14d30017fe869800bfe434c005ef21a6002ff50d30007ba869800bfc434c001ffb126000bfd8930007fcc498003fd624c001fe3126000bf189300e7fea498003fe524c001fea92601cff149300dffe8498003fe424c001fea12601bff10930017fe649800bdf324c005ff1926002ff4c930007ba649800bfc324c035ffb0a601abfd85300d7fcc298006fe614c035feb0a601abf585300d7f8c298006fc614c035ffa8a601aff945300d7faa29806bfc514c035ffa0a601aff905300d7fa829806bfc414c005ff98a6002ff8c530017fa629800bfc314c035ff90a601aff885300d7fa429806bfc214c0057fb02601cffd413002ffca098003fd504c00bfe282601bffd013002ffc8098003fd404c00bfe2026002ffcc130017f66098017fe304c00bef1826005ff0c13002fb8609800bf8304c035ff882601afdc413002ffc209806bfd104c00bfe0826009ffd9720005fecb90067fe65c80097f32e4000ff59720005facb90027fc65c80097e32e4009ffd9320005fec990063fe64c80077f3264000ff59320005fac990027fc64c80077e3264019ffd53200c7fca990003fd54c8031fe2a64009ffd8f20005fec79005ffe63c80057f31e4000ff58f20005fac790027fc63c80057e31e4019ffd4f200bffca790003fd53c802ffe29e4018ffd0f200bffc879000
  | 3 => 0xe98aa026ff0c550137fe42a809bfe215404dfe90aa026ff08550025fec0a8013ff5054009fda82a005ff9415002efca0a8017fc505400bbe282a004fe14150147fe80a8017fc405404fff982a005ff0c150137fe20a809bf7105400bff082a026fe84150137fa20a809bf9105400bfe082a005ffd964002dfecb20017fe65900097f32c8005ff59640005facb20017fc659000b7e32c8003bf5924001ffea92000ffe5490007feaa48003ff1524002ffec720017fe63900057f31c8005ff58e40005fac720017fc639000b7e31c8025ffd4e40127fca720003fd5390049fe29c8003ffd0e4001ffc872000ffd4390007fe21c8005ffd8a4002ffcc520002fe629000bfeb148000bf58a4002ff8c520097ff5290001ff2948000ff54a4012ff8a52000fff4290007ff2148003ff50a4001ff88520093ff3290001ff1948000ff4ca40127f86520017ff619000b7fb0c8005ff9864000dfcc320017f661900037b30c8005ff5864011dfac320017f561900017ab0c8005ff1864002df8c32008fff5190047ff28c8023ff5464011ff8a32000fff4190007ff20c8003ff5064001ff8832008fff3190047ff18c8023ff4c64011ff8632008fff2190047ff10c8023ff4864011ff84320016fe609000bffa848005ff9424002ffaa120017fc509000bffa048005efd024001ff68120017fc409000bfc2048005ffcc24002ff86120017ff109000bfb8848005ff8424002ff42120017fd1090047fc8848005ff04240007fecaa0002ff6550045ff32a8004bf99540007facaa0002fd6550045fe32a8004bf1954002dfec8a000fff5450007ff2a28003ef9514001ffaa8a0003bd5450007fe2a28000ffd8d40005fec6a0087fe63500057f31a8000ff58d4010ff8c6a000afc6350045ffa9a8021ff94d40007faa6a0087fc5350007ffa1a8003efd0d4001ffc86a000ffd4350001dea1a8003ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0002fc6250045ffa928000ff94940007faa4a008bfc5250007ffa128003efd094001ffc84a000ffd4250001dea128003ff1094010ffe64a0003fe3250001fe9928021ff0c940107fec2a0082ff6150041ff30a8001bf98540107fac2a0082fd6150041fe30a8001bf18540107fea2a0083fe5150041fea8a8020ff1454001ffe82a000ffe4150007fea0a8003ff10540107fe62a0083fe3150041fe98a8020ff0c540107fe42a0083fe2150041fe90a8020ff0854001dfec0a008bff505000bff2828000ff5414002ff8a0a000fff4050007fda028005ff9014002f7c80a0017fc405000bde2028003fe1014010ffe60a0017fc3050041ff8828020fdc414002ffc20a0083fa1050041fe8828020fe4414002ff820a0017ff658c00b7fb2c6005ff99630025fccb18017fd658c0017eb2c6005ff196
  | 4 => 0xbfe434c805fea1a6402ff10d32015fec4990bbff524c801ff2926400ff54932177f8a4990b7ff424c801ff2126400ff5093216ff8849900bff324c805f79926402ff8c932007bc649900bfc324c805ee1926402fb0c9320179864990b3ff614c8597fb0a642cff9853200dfcc2990b3fd614c8597eb0a642cff1853200df8c2990b3ff514c859ff28a642cff54532167f8a2990b3ff414c859ff20a642cff50532167f8829900bff314c805ff18a6402ff4c532017f862990b3ff214c859ff10a642cff48532167f84299003ff604c8017fb026400ff98132007fac099003fc604c80b7e302642effd4132177f8a0990b7ff404c85bfe2026402ffcc132017be609900bfc304c859ff882642cfdc4132167fc20990b3fd104c859fe0826404bf5965002ffec928017fe64940077f324a005ff59250005fac928017fc649400b7e324a004ffd5250027fca928013fd5494009fe2a4a005ffd8e5002ffcc72800afe639400bfeb1ca000bf58e5002ff8c728016fc6394009ffa9ca004ff94e50027faa728013fc5394057ffa1ca02aff90e50007fa87280abfc439400bffb14a005ff98a50005fcc528017fd62940017eb14a005ff18a50027fea528013fe5294009fea94a004ff14a5015ffe8528003fe4294001fea14a02bff10a50157fe6528003fe3294001fe994a02aff0ca5002ffec328016ff619400bff30ca001bf9865002fecc328006f6619400bfeb0ca029bf5865002feac328002f5619400bfe30ca005bf18650027fea328013fe5194009fea8ca004ff1465014ffe83280a7fe4194053fea0ca029ff1065014ffe63280a7fe3194053fe98ca029ff0c65014ffe43280a7fe2194053fe90ca029ff0865002dfcc128017ff509400bbfa84a004fed425002ff8a128017f8509400bffa04a005ff1025002ffe6128017fc309400bff884a005fdc425002ffc2128017fa109400bfe884a029fe4425002ff82128016ff6554001ffb22a000bfd9150147fcc8a800efe6454001feb22a028ff1915001df8c8a8013ff5454009bfaa2a004ff95150027faa8a80037d5454009fe2a2a000ffd8d50005fec6a809ffe63540057f31aa000ff58d5013ff8c6a800afc6354009ffa9aa004dfd4d50027fca6a8013fd5354001bea9aa004ff14d50147fe86a809ffe4354001fea1aa027ff10d50007fec4a8002ff6254001ff312a000ff58950007f8c4a8002fc6254009ffa92a004dfd4950027fca4a8013fd5254001bea92a004ff14950147fe84a8003fe4254001fea12a028ff1095013ffe64a8003fe3254001fe992a027ff0c950137fec2a809aff615404dff30aa001bf98550137fac2a809afd615404dfe30aa001bf18550027fea2a8013fe5154009fea8aa004ff14550137fe82a809bfe415404dfea0aa026ff10550137fe62a809bfe315404df
  | 5 => 0x864204ff84321027ff6090801ff3048405bf98242007fac121002fd6090813fe3048437ffd42421bff8a12100fff4090807fe2048436ffcc2421b7f861210d7ff109086bfb8848435ff842421affa21210d7fc1090801ffb2a8400bfd95421a7fccaa1012fe6550801feb2a8400bf595421a7f8caa1012fc65508077fb228403ffd514201ffca8a100ffd5450807fe2a28400ffd8d42005fec6a10cffe63508057f31a8400ff58d4219ff8c6a100afc6350869ffa9a8433ff94d42007faa6a10cffc5350807ffa1a8403efd0d4201ffc86a100ffd4350801dea1a8403ff10d4201dfec4a10d3ff5250801ff2928400ff549421a7f8a4a100fff4250807f7a128403ff909420077c84a100ffc4250807de2128403fb1094219ffe64a10cffc3250865ffb0a8432bfd8542197fcc2a1006fe6150865feb0a8432bf58542197f8c2a1006fc6150865ffa8a8432ff94542197faa2a10cbfc5150807ffa0a8403ff9054201ffa82a100ffc4150865ff98a8432ff8c542197fa62a10cbfc3150865ff90a8432fbc8542197fc42a10cbfd2150865f690a8432ff08542007fec0a1002ff6050801ff3028400ff58142007f8c0a1016fc6050869ffa828434ff1414201ffe80a100fbf4050807fe2028433ffcc14219ff860a10cbff1050865fb8828432ff84142197fa20a10cbfc1050813ffb2c6400bfd963218ffccb19012fe658c801feb2c6400bf5963204ff8cb19012fc658c813ffb246400bfd9232187fcc91900efe648c801feb246400bf5923204ff8c91900efc648c863ffaa46430ff95232007faa9190c3fc548c8057eb1c6402ffd4e32017fca71900bde538c805fea9c6400f754e32017f8a71900bff438c805ff21c6402f790e32017fa8719003dd438c805fe21c6402bf98a3218ffea519027fe528c801fea946409ff14a32187fe8519027fe428c801fea146409ff10a32017fe651900bdf328c805f79946409ff0ca32017d86519027ff618c85f7fb0c642fff9863200dfcc3190bffd618c85f7eb0c6409ff1863200df8c3190bfff518c85fff28c642fff5463217ff8a3190bfff418c85fff20c642fff5063217ff8831900bff318c805ff18c6402ff4c632017f86319027ff218c85fff10c642fff4863204ff84319027ff608c801ff3046405bf98232007fac119002fd608c813fe3046431ffd423218ff8a1190c3ff408c861fe2046402ffcc232017f8611900bdc308c85fff884642ffdc423217ffc21190bffd108c85ffe0846400ffd9532005feca990bbfe654c8097f32a6400ff59532005faca990bbfc654c8097e32a6400ffd9132005fec8990b7fe644c8077f3226400ff59132005fac8990b7fc644c8077e322642effd513216ffca899003fd544c85bfe2a26402bfd8d32017fea69900bfe534c805fea9a6402ff14d32017fe8699
  | 6 => 0x1beaa4a404ff1525204ffec7290f3fe63948057f31ca400ff58e52005fac729027fc63948057e31ca404ffd4e52027fca729013fd5394809fe29ca43dffd0e521e7fc8729003fd4394879fe21ca404bf98a52027fea5290137f5294809f7a94a409ff14a52027d8a5290f7ff4294813fe214a43cffcca5204ff86529027ff61948777fb0ca43bff9865200dfcc3290effd61948777eb0ca409ff1865200df8c329013ff5194809ff28ca404ff54652027f8a3290efff4194877ff20ca43bff506521dff883290efff3194877ff18ca43bff4c6521dff86329027ff2194877f790ca43bff886521dffa43290efed2194813fe10ca409ffd8252007fcc129016fe6094801feb04a400bf5825204ff8c129013ff5094809fe284a43dffd02521eff881290f3ff3094879fe184a43bffc42521dfee21290effe1094877fe884a43bff04252025fecaa9003ff64548017fb22a43aff9915201dfcc8a9003fd6454875fe322a403bf19152027fea8a9013fe5454809feaa2a404ff15152007fec6a9002ff6354873ff31aa402bf98d52007fac6a90e7fc63548057e31aa404ffd4d52026fea6a9013fe5354809fea9aa400df54d52027f8a6a90ebff4354873ff21aa400ff50d521cff886a9012ff6254809ffa92a404fbd4952027fca4a90037e5254809fe292a404df14952027d8a4a90ebff4254875fe212a439ffcc9521cff864a90e3ff61548717fb0aa438ff9855200dfcc2a90e3fd61548717eb0aa438ff1855200df8c2a9013ff5154809ff28aa404ff54552027f8a2a90e3ff4154871ff20aa438ff505521c7f882a90e3ff3154871ff18aa438ff4c5521c7f862a90e3ff2154871f790aa438ff885521c7fa42a90e3ed2154871fe10aa400ffd8152005fec0a9003fe6054801feb02a400ff1815202df8c0a9013ff5054809bfa82a404ff141521d7fe80a90ebfc4054873ff982a439ff0c1521c7fe20a90e3f71054871ff082a438ff441521c7f820a9027ff65908017fb2c8437ff99642025fccb21003fd65908017eb2c8409ff19642025f8cb2100efd6490807ffaa48403ff9524201f7ca92100ffd5490801deaa48403ff1524204ffec7210dbfe63908057f31c8400ff58e42005fac721027fc63908057e31c8437ffd4e421b7fca721003fd539086dfe29c8403ffd0e4201ffc872100ffd4390807fe21c8403bf98a421bffea521027fe5290801fea948409ff14a4201ffe852100fbf4290807f7a148409ff10a4201fd885210dbff3290813fe1948409ffd86421adfec3210d7fe61908037f30c8435ff586421adfac321027fc61908037e30c8435ffd46421affca3210d7fd519086bfe28c8403ffd064201ffc832100ffd4190807fe20c8435ffcc6421affc63210d7fd319086bfe18c8409ffc86421afde43210d7fe219086bfe90c8435fb4
  | 7 => 0xaa00fbf4155007ff20aa803ff505542177a82aa00ffc4155085ff98aa842ff8c554217fa62aa10bfc3155085ff90aa842ff88554217fa42aa10bfc2155001ffb02a800bfd8154007fcc0aa003fd6055001fe302a805bf18154027fea0aa0137f5055009fe282a803ffd015401f7e80aa00ffc4055087ff982a843ff0c154217fe20aa10bf71055085ff082a842ff44154217f820aa00aff6554c01ffb22a600bfd915320ffcc8a980efe6454c01feb22a641ff1915301df8c8a9813ff5454c09bfaa2a604ff95153027faa8a98037d5454c09fe2a2a602bfd8d53017fea6a9813df5354c05ff29aa602df94d53017f8a6a980b7c5354c05ee29aa602ffd0d53017fc86a980bde4354c05fe21aa600ffd8953005fec4a9803fe6254c01feb12a600ff18953005f8c4a9813ff5254c09bfa92a604ff1495320ffe84a9907fc4254c05ff992a602ff0c953017b864a9903ff6154c817fb0aa640ff9855300dfcc2a9903fd6154c817eb0aa640ff1855300df8c2a9813ff5154c09ff28aa640df94553027faa2a9813fc5154c09be28aa640ffd0553207fc82a9903fd4154c81fe20aa602ffcc553017be62a980bfe3154c05fe98aa640f74c553017f862a9903ff2154c81ff10aa640ff48553207f842a9803ff6054c017fb02a600ff98153007fac0a9803fc6054c0b7e302a604ffd4153026fea0a9813fc5054c83ffa02a641ff10153017fe60a980bdf3054c05fe182a640ffc4153207ee20a9903fe1054c81fe882a640ff04153007fecaa1802ff6550c7fff32a8604bf99543007facaa1802fd6550c7ffe32a8604bf19543015fec8a180fff5450c07ff2a28603ef9514301ffaa8a1803bd5450c07fe2a28602bfd8d43017fea6a180bfe5350c05ef29a8602ff54d43007baa6a180bfc5350c05ffa1a8603f7d0d43017fc86a180bbe4350c05fe21a8602ef10d43017b886a1803ff6250c017fb128600ff98943007fac4a1803fc6250c017e312863fffd49431fff8a4a180fff4250c07dfa128603ff10943017fe64a180bfc3250c05ee192863effd85431f5fec2a18fbfe6150c037f30a863eff585431f5fac2a18fbfc6150c037e30a863effd45431f7fca2a18fbfd5150c7dfe28a8603ffd054301ffc82a18fbbe4150c07fea0a8603ff1054301f7882a180bff3150c05ef98a8602ff8c543017fa62a18fbdd3150c05fe18a863effc85431f7fc42a18fbfd2150c7dfe10a8600ffd8143005fec0a1803fe6050c01feb028600ff1814302df8c0a18ffff5050c7ffe2828603ffd014301f7e80a180ffc4050c05ff9828602f7cc143017f860a18fbff1050c7dfb882863eff841431f7fa20a18fbfc1050c097eb2ca409ffd92521effcc92900efe6494801feb24a400bf5925204ff8c92900efc6494809ffaa4a404dfd5252027fca929013fd549480
  | 8 => 0x1402e02402600401c04406800601400200000a00600203a03200a01e00001400001000600c00200002400e01002804400e00a00200800e00600402201601202000a03e02201000c00800401800001200e00200201404e01800001e01401602206600600200c00a00000000c01400001000e0ca00400000200000200e00000c01a00000e01200600a00a00000000400800000200e02000402800000000801200000600200004204a00800c00600200607c01401c00c00600000000a07800801000000601000c00200e00201600200001800200a00001400000200600000a00000204a00e04600400602601e01800000200801600802601600e01400600600000600200200200002a00201e00801400200e09200001c00000400000200000000000200000400000e06000c00000000c01600001000400200e02601401800800004200a00c00200401a00000e01000000202200000c00000600200801000404000201200200003201801a04801c00a01a00e00201400201c05e00200c00400201c00c00807a01000400000800800c01000600400400000000a00000202405a00a00000404200000600400000801600000200000200003000c00a01800c03400200000600a00000400a01402200400002a01000200000c02c01e00c02001000001a00000c00000800800800001a00604200400800800c00a00002c00400200200000000000400000000600406802400200000601400001001200001e00200a00601600000000000200202402600600001000a02200200e00805601203000203208c00400600000000200400400001a00600400200601c00000401800a00202a00600602c01200e00001c01200000001200200000600800400000600201000401c00a00202200200200000000600000200400600000003c00a00000202400000200200e01000001c00600a00004e01c00001400000c00000406400002c00800000201c01c01000401605600a01203c01201804000000000400000200c04a00a02e00001808a01600601800001000400001c00e01200603bfd955401dfec8aa00fff5455009dfaa2a803ff9515401efca8aa00ffc5455007be2a2a803ef1515401e78a8aa003ff63550017fb1aa843ff98d54015fcc6aa003fd6355087fe31aa802bf18d54027fea6aa0137f5355009ff29aa804ff14d5401ffe86aa00fbf4355007ff21aa803ff10d54007fec4aa002ff6255001ff312a800ff58954007f8c4aa002fc6255009ffa92a804ff14954026f8a4aa00fff4255007fe212a803ef1095421ffe64aa10ffc3255085ffb0aa842bfd8554007eec2aa002f76155085ff30aa801bf98554217fac2aa10afd6155085fe30aa801bf18554217e8c2aa006f46155009ffa8aa804dfd4554027fca2aa013fd5155085bea8aa804ff1455401ffe82
  | 9 => 0x1b75a54001c18345a91318ed8245b98c8c8a156cde8b217889ac19cfd5acc4ecbb4f951f50cc0b16a994dab56c105d60c1d91a552c190001541a3d74cf1c2b9934851960c4962545c88456c928cfc1057000012e897c0000015882e91300002d95c578c001c318810a1418d001f5c08001300b9cd39bac4e8334164fd80a58480c59145dd0fce743a198c26c1a0fcccc02409f079d4fc001a5cde4d3d9a17f5bfda6d84452db80f101450701cd16445400090c80044d7d805d24c13971d88d0f062c7644154a529dc819748e1430255028b8d708001669770488808000a508257d0ef4029900708ed0e3400122590cd904d970c3209d82e08159e0b312457b06e182160042dc0db5054871c000bed7c438cbe4799568aa0fc983cdd4001220e6800032c9617998f40018713b5b2061c001424001bd0000000899644000001a01a3894000000000050cd089d1c296b1b38b04a80000728001740c740011cca69414e603b555dbf18b9a980585fc27c00000107db2923d65c4c4b919c047d33953407564000000172c0015259489580000006dcdc014c5a17f08884d1a2daa40016e4014c713a458d91c001211884a94c99994374000001a40769274828744ef95f4964dccb1404d001399138249321584b4c11000006c0015e11a8000001b18000001af80010741fd0e54ac2c5828ac96314f80dc7a800013d3f0ae80008dcfc0ec49680e4c1d0850591693680000007200007fc37d774000001a443d8e10000000b40c6025828d2540011fc82099c000000cd1445954810001134f89101bd8aac100270a3960411d4894381a4001330e65209a0cc2c6fd3ac6c08a8f68a09b085089dc000000468000ae00008495b00009a5311a9c001615895ac41f8784000dac0006cd5b94dc001814d74aec950f8ccad2e0974bc0578c4d628a347e09cd2f48f9a240010945c07485e54694a0d31ba59858e8e802adbb5a94af02dc00067493c8d15300d93c59acee4c5867d9400912fc3e519d6187c0315a50734ffdc2009db0084007966d8889a8001ae0838000be000199c7d9308000d549315780000019f54d5290be82640e8f180000011b51ec099158001340d64bd986c00022c3d406985868dba000191821d090ff0280908d51a61794b80b554a912d4e11940011ac0000480006152ac0d47e40000000004b41f110435cbac5855ccb3c3bd7f99dc6f824c00800002a00801200603600600603000200000e00000601c00400c00800000002402800000000800200600600200002202e01402801000c04600000400001001a00001e00002001000200200005e00203600200000401202800000000000002602008e00201000601000400c00001000c02802600401200200800801a04c07c03203001c06801808c0060320060000020020b800400e06c00e0040000
  | 10 => 0x44c6953b8bd0d79a217256c4df4428d2c33933c92db100000000012a4eb02843980000648713240000005881acb956dc92031d43d264000000d199cd30ca2c47800000126153860d178cb000167c00184da7c8ed9ecb688c5af4f30480000b5d670f3cb0c54ca5da090c56b4b01bd4d8c000650188080208b391445bc6bd1e5570e38a8c7b808c4908a44ddc2c330d0d2f8001c443858a95612301140000310c02284bd7c959cdd8db876c545bf54700f1abc00037033c75001cda40cc0012f0184d58a44cbd18dc10ad4000000000001214c24eec000000000e3000145800000088d1e98c863c001650340a3c504000934a9cab180c6987880002791c50695004d55046a935d50cd68bc41c5354c045f4425278c80e519f837864880537012d8a081c29d4f50b17e1480dd05956d44e1bbc77d12000083554456436c5e0000eb82f47f8ddc1743c80f8ee06d03ad5dd1e12700001e4529c489ed4c459c0000000000004e58b117c925a158ed268000000000c19aa8001bdc0000017a43943299f0a30de0854cd40387ccff9634000000771a84900000420001afc4640016845b58e47ac44443559109d4902955f831834c9b01b8c64b2d20c00015d0a9990ea04959d41605688ac7a0550ec875ccf5bc0000ccc9e9809218c44abc5f8088e7028830d050dedaf016d968e3c000bb80012d89893b0000020001c34001a7054162c4cce2d391464b2560987d82cc5c6f4000c68e9c43c00121c5b00d00019bcd70b64dc80014084b98cd6384f00005cc2d05ec2e400181800039cdb00000f4001005bf8000b84aa9b68ea8000000ec138c0000000000000000012d403d0dc4ac084001c748197fc00163c001698000bcd161a7445949dbcd29527db251916e8fa8a84d9c2b5ae4d61054c6cff49f4a21b3dbb87017cdac96fc7b40fd7b5ad8f6d32c85ca05be4b61b0d2058b448526c474ca954dc383e96ac6309fdaa07616891518649e149585d37c3fcd4db918c023cd8910cefd2d02ecbdcb44e09228d28e042157a02a01c96203889b8f61beccd8514d0489d8a4000e5da8d945c607a55989196815c81194351d87c5a040000006f00013a80011816f90ed47dc50000000001b1c8b09800b4cc9648fc4c54000f35690000001360000678361b5c001755a647785d573007ca88c786d8c400015497bd5d86ac48c66cca0d495ed1c0001c04000e8506c539950120ba085802c1bc298f0d3746013dd0254413bce240017840013c000000197040c000c3515c000000000150b59869854a1dc70db5b6c0006d480c001748000000000221b897d4640b28000000520000001365c88000349979ab80000018dc9bd14ccb577c795c65298c153d5718f2c625b95674618f900011c80c0000e1821089486c3cd4740017e91110e0018404704724b08a110d98343f
  | 11 => 0x1768655199958fe52848bc639a4d5d4ca4140f4d0341b164d5c03f4d5cc8900ca0ccc46b53d08e5c7c998194369b2c000000f8496dc8cfd0001980d24a7961c2503c4c7c0016ec0000009a13a12c91d0c113fd761a4887c30196cf51a10001c419e4ba80010640004b181d9fc41d68d9b00ed0389154cc65800113c64c685720e98ce0000c9c6a0c5086410cda8759124ee82c8fbd03c0a08690317ad5e495c1256f1080461580edc440e1d8041e9c908310b4000fe84305c8561a35c849d45e80000004a1b14000c21928af8130d4017800141c3c0000a70bf800000065c000e5478d11c001044acc0000002a5040158f5cf3951cb88000facd980000001e05ad5f000146c0000000000000000000018d4af48d58f801046cea51dda28ebd02c731c4c0c9ad44380000000000442010ac948054001518d7c5306e540dba86c8f14e013e4070239c3ce5918800104855da1c000170e4d7e40010b89540017140014ec0013c91d4688644a98a6000000128cbf52b95bdb4d8118786b017cae40000018256787f03a4669a803e10bc0015592ecb482c0c39410001bc4634f0072c1800012ccb7d1b995d801b043b14e99c8cf8881288cb939d358ab58d00956a5bb05d01b5610861b35170001304628b747ec5811403f8e6d5e8ce8f99898d34c916f5ae85117059315d12c42617a8a55ac0a4925d909128c290a51f0ad04c0b19251b7d728bb020548dc7957ca403581ec00179cd806b873c714f788fd3293e14d97b8604c08e8c790d44f7c55511816800051cadc5a58c50f40008459d14bc00176cf9c1ddb452487dd16d69d0c8e40a180009c4000b6cfa40000013818d94b9665add34cce40011f80012b14b4f201a82f818c15425c001514001c553d934589d7115fd07870c4fc0004089900003dc0000018e0000001738000001830000001018148001a18001174df80002a8000f700018ac0000012bdaac0012417dd4607c9060000000001a89660e900014d12a00000ace146a59a93797c00005d92800004000009b40001082257599387d43d049891ca7d964128004000000719c6938400074101c8756c8a2457ca759e8938c95b554c0000000c0c000f748f03808c96956e0000b98f58e898bc000d1c00000192daec275c1c30538942d2345c4000000000a6d8f09c99b5744000cdcda0000ecc000a1498d9a41c0fec944000f5558dc14910bf19999b8774000570355b6108dad1010710008001020001450001b48e20e780016540000000009858900415a80b9259479401b9c5353e9a794b1c25511508b50b79a68e449797ec1d4664448c849056cd314410ed5b315652b474d3cc94d73c4a59d8000f080002d5a589f845136d874f250f80a92e4a006e88909e5014fb44f83a9860ac0ba4f44000001394cec0000018386613500000002f1
  | 12 => 0xad9334eacfa03913f9b597914e4fdc3514c8e95be175c03591045d405b402cc025c59bc94490e9b64bd47e8c01b8d6bd0d4aa4680ac4afdc6c574b71088f640016d8199750bc88c0a4cb115a553c8e83b8324ef1be9554e7cd15c5d7806ec3ed5ad31c73869c00d45597d734ab80005000000008b8fe0000000bfc5b83088f400053c84c001348000a295b42913f4dfc8780004f42fc0012dc9c0e28365154f04470418a919c4a58cf19892c15286908ccdbcdf07d1550134620a6421883db78d851140004c94f0000000000001850050558fb95a193d6a0fb1594670000dc59040012a8000001b8592082c0000016d1a307bce487f48b44a8f48d6c5180010999240002345a94985f0001764f29148d202b1520bbd23977849c0000618fcc3c0011a00000005915747b0995184e0c0e020d6b8000000000d9400104c000eb510875460922d1b1009c01658f814842bc6c51bc8d9420310524268b1c0bc1d0599b70d10000230000f40b350d1428c30971840781ab13ec6112
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x1655011023ff0655011002ff3745011002df3745011002fb3745011003ff36450110007b3645011003ff26450110107f1645011003ff0645011003fb0645011003ff3545011003ff2545011003fb2545011003ff15450110007b1545011003ff05450110007f37350110237f27350110007f17350110237f07350110007f36350110237f26350110007f16350110237f0635011023ff35350110237f25350110007f15350110237f0535011003ff3435011003fb3435011003ff2435011003ff14350110007b1435011003ff04350110007f37250110007f27250110007f17250110007f07250110007f36250110007f26250110007f16250110007f0625011023ff35250110007f25250110007f1525011023ff0525011003ff3425011003fb3425011003ff2425011003ff14250110007b1425011003ff04250110237f33250110007f23250110007f13250110237f0325011022df7764c11000df6764c1100d5f5764c11000df4764c110005f7754c110045f6754c110005f5754c110045f4754c110005f7744c11003df6744c110005f5744c11003df4744c11002df7734c110007d7634c110037d4634c110037d6534c110007d5534c110037d6434c110007d5434c110005f7724c110005f4724c110037d7324c110007d5324c11002df7704c11002ef7604c1100d7f3604c11002ff2504c110007f1504c11002ff2404c110007f1404c110037f3304c11002fd6304c11002fd4304c11002ff0304c11002fd0304c11002ff2204c11000df676c811000df476c8110005f775c8110045f675c8110005f575c8110045f475c8110005f774c811003df674c8110005f574c811003df474c8110005f773c8110035f673c8110005f573c8110035f473c811002df672c8110007e762c8110007e462c8110007e652c8110007e552c8110007e642c8110007e542c8110007e632c8110007e532c811002df570c811002ef760c8110077f360c811002ff250c8110007f150c811002ff240c8110007f140c8110227f330c811002ff030c811002fe620c811002ff220c811002fe420c8110075f7764811000df6764811007df5764811000df47648110005f77548110045f67548110005f57548110045f47548110005f7744811003df67448110005f5744811003df47448110005f77348110007d77348110005d77348110035f67348110005f57348110035f47348110007d47348110035d4734811002df77248110007e76248110007e46248110007e65248110007e55248110007e64248110007e54248110007e63248110007e5324811002df7704811002ef7604811007ff3604811002ff25048110007f1504811002ff24048110007f1404811002ff23048110007f13048110007f3204811002fe6204811002fe4204811002ff0204811002fe02048110
  | 1 => 0x411002f737554110047f36554110007736554110047f26554110137f16554110047f06554110047706554110007f37454110005f3745411026ff27454110007f1745411026ff07454110007f3645411026ff26454110007f1645411026ff06454110047f35454110047735454110047f25454110047f15454110007715454110047f05454110007f37354110267f27354110007f17354110267f07354110007f36354110267f26354110007f16354110267f06354110047f35354110047735354110047f25354110047f15354110007715354110047f0535411026ff34354110267f24354110007f14354110267f04354110007f37254110007f27254110007f17254110007f07254110007f36254110007f26254110007f16254110007f06254110047f35254110047735254110047f25254110047f15254110007715254110047f0525411026ff34254110007f24254110007f1425411026ff04254110267f33254110007f23254110007f13254110267f0325411002ff2769011025df2769011002ef2769011002ff3759011002df3759011002ff2759011002ff17590110005f1759011002ff07590110007f36590110257f26590110007f16590110257f06590110105f1749011011ff3649011003ff2649011003ff1649011003ff0649011003ff3549011003ff2549011003ff1549011003ff0549011002ff3739011002ff2739011002ff1739011002ff07390110007f3639011024ff26390110007f1639011024ff06390110257f3539011024ff25390110007f1539011024ff0539011003ff3439011003ff2439011003ff1439011003ff0439011002ff3729011002ff2729011002ff1729011002ff07290110007f36290110007f26290110007f16290110007f06290110257f35290110007f25290110007f15290110257f0529011003ff3429011003ff2429011003ff1429011003ff0429011024ff33290110007f23290110007f1329011024ff03290110245f7765011000df67650110105f5765011000df47650110005f77550110045f67550110005f57550110045f4755011002df77450110007b7645011003fb4645011003fb65450110007b55450110005f77350110035f67350110035f4735011003fb74350110007b54350110005f77250110005f4725011003fb74250110007b5425011002df7705011002ef76050110107f3605011023ff3505011002ff25050110007f1505011002ff0505011003ff3405011002fb6405011002fb4405011002ff04050110237f3305011002ff2305011002ff0305011002ff2205011002ff02050110107f2765011000df27650110107f0765011000df07650110007f37550110005f3755011023ff27550110007f17550110005f1755011023ff07550110007f3655011023ff26550110007f
  | 2 => 0x2adf77250910007e66250910007e5625091003fe74250910007b6425091003fb4425091003fe44250910005f7705091002df6705091002df47050910196f76050910197f3605091003fb74050910005f7768c910005f6768c910005f5768c910005f4768c910005f7758c910045f6758c910005f5758c910045f4758c910005f7748c91003df6748c910005f5748c91003df4748c910165f5738c910007d7638c910037d4638c910037d6538c910007d5538c910037d6438c910007d5438c9102a5f6728c910037d7328c910037e7328c910037e4328c91002df6708c910005f5708c91002df4708c91017ef7608c91017ff3608c91029fd6308c91029fd4308c910005f7764c910005f6764c910005f5764c910005f4764c910005f7754c910045f6754c910005f5754c910045f4754c910005f7744c91003df6744c910005f5744c91003df4744c91017df7734c910295f7724c910037e7324c910007d6324c910037d4324c910037e4324c910037c4324c910005f7704c910007f3704c910005f3704c91002df6704c91002df4704c910007f0704c91002df0704c910166f7604c910167f3604c910037d7304c91002ff2769411028df2769411002ef27694110135f1759411014ff36594110047f26594110047f16594110047f0659411002ff3749411002ff2749411002ff17494110005f1749411002ff07494110007f36494110287f26494110007f16494110287f06494110047f35494110047f25494110047f15494110047f0549411002ff3739411002ff2739411002ff1739411002ff07394110007f3639411027ff26394110007f1639411027ff06394110047f35394110047f25394110047f15394110047f05394110287f3439411027ff24394110007f1439411027ff0439411002ff3729411002ff2729411002ff1729411002ff07294110007f36294110007f26294110007f16294110007f06294110047f35294110047f25294110047f15294110047f05294110287f34294110007f24294110007f14294110287f0429411027ff33294110007f23294110007f1329411027ff03294110275f7765411000df67654110135f5765411000df4765411002df77554110007776554110047746554110005f7745411003df6745411003df47454110047775454110007755454110005f77354110035f67354110035f47354110047775354110007755354110005f77254110005f4725411004777525411000775525411002df7705411002ef76054110137f36054110047f3505411002f76505411002f74505411002ff0505411026ff3405411002ff2405411002ff04054110267f3305411002ff2305411002ff0305411002ff2205411002ff02054110137f2765411000df27654110137f0765411000df0765411002ff3755411002df3755
  | 3 => 0x74050d10037d73050d10045f675d8910005f575d8910045f475d891003df674d8910005f574d891003df474d8910035f673d8910005f573d8910035f473d8910006f763d8910006f563d891009ef760d891009ff360d8910045f67598910005f57598910045f4759891003df67498910005f5749891003df47498910035f67398910005f57398910035f47398910055f67298910006f76298910007e7629891007df57098910007f1709891007df17098910076f76098910077f36098910005f77558910007777558910005777558910045f67558910045f47558910007747558910045747558910005f77458910007b77458910005b7745891003df6745891003df47458910007b4745891003db47458910005f77358910007d77358910005d77358910035f67358910035f47358910007d47358910035d47358910006f76358910006f56358910007e76258910006f66258910075f77058910007f37058910075f3705891007ef7605891007ff3605891009df67618910045f67518910005f57518910045f4751891003df67418910005f5741891003df47418910035f67318910005f57318910035f47318910006f76218910007e66218910006f56218910007e56218910056f76018910057f36018910005f77694910005f67694910005f57694910005f476949101c5f5759491000777659491004774659491003df67494910005f5749491003df47494910047775494910007755494910035f67394910005f57394910035f473949102c5f67294910007e66294910007e56294910047775294910047e75294910047e4529491002df67094910005f5709491002df470949101def760949101dff36094910005f77654910005f67654910005f57654910005f476549101ddf77554910005f7745491003df6745491003df47454910005f77354910035f67354910035f473549100477753549100077553549102bdf77254910007e66254910007e56254910047e75254910007765254910047745254910047e45254910005f7705491002df6705491002df470549101c6f760549101c7f36054910047775054910005f77690910005f67690910005f57690910005f47690910005f77590910045f67590910005f57590910045f47590910195f57490910007b7649091003fb4649091003fb65490910007b55490910035f67390910005f57390910035f473909102b5f67290910007e66290910007e5629091003fb7429091003fe7429091003fe4429091002df67090910005f5709091002df470909101aef760909101aff36090910005f77650910005f67650910005f57650910005f47650910005f77550910045f67550910005f57550910045f475509101adf77450910005f77350910035f67350910035f4735091003fb74350910007b54350910
  | 4 => 0x911003fb743d9110005f672d9110005f572d911003fb442d911011ff370d911002df670d911000df570d911011ef760d911011ff360d911003fb740d9110005f77559110007777559110005777559110045f67559110045f4755911000774755911004574755911011df77459110007b7645911003ef6645911003ef4645911003fb4645911003fb65459110005f77359110035f67359110035f47359110005f77259110005f47259110245f77059110007f37059110245f37059110106f76059110107f36059110005f77655110006f77655110004f77655110005f67655110005f57655110005f47655110006f47655110004f476551102fdf775551100477665551100077565551102f5f7745511003fb66455110007b56455110047b7545511003f76545511003f74545511003fb4545511003f345455110005f77355110035f67355110035f4735511004777535511003fb74355110005f77255110005f4725511004774525511003fb44255110005f7705511002df67055110007f27055110007f1705511002df47055110216f76055110217f3605511004777505511003fb740551102edf676d8d10045f675d8d10005f575d8d10045f475d8d1003df674d8d10005f574d8d1003df474d8d10036f663d8d10037d663d8d10036f463d8d10005f672d8d10005f572d8d10037d432d8d1002df670d8d1000df570d8d100eef760d8d100eff360d8d10037d730d8d10005f77558d10045f67558d10045f47558d10005f77458d1003df67458d1003df47458d100edf77358d10007d76358d10036f66358d10036f46358d10037d46358d10037d65358d10037d64358d10005f77258d10005f47258d1022df77058d10007f37058d1022df37058d100d6f76058d100d7f36058d10005f77654d10005f67654d10005f57654d10005f47654d102e5f77554d10007776554d10047746554d10005f77454d1003df67454d1003df47454d10047775454d10007755454d102ddf77354d10037d66354d10007d56354d10047d75354d10037765354d10037745354d10037d45354d10037d64354d10005f77254d10005f47254d10047775254d10037d43254d10005f77054d1002df67054d1002df47054d10206f76054d10207f36054d10047775054d10037d73054d10005f77650d10005f67650d10005f57650d10005f47650d10005f77550d10045f67550d10005f57550d10045f47550d102d5f77450d10007b76450d1003fb46450d1003fb65450d10007b55450d102cdf77350d10037d66350d10007d56350d10037d65350d10007d55350d1003fd74350d10037b64350d10037b44350d10037d44350d10005f77250d10005f47250d1003fb74250d10037d43250d10005f77050d1002df67050d1002df47050d101f6f76050d101f7f36050d1003fb
  | 5 => 0xccff76548200267e65548200067d65548201d6be6454820006bd64548201cede6354820006dd63548200ceee62548201c6f661548200c4ff76508201a67e65508200067d655082001ebe6450820006bd645082019ede6350820006dd63508200c6ee6250820196f661508200bcff764c8201767e654c8200067d654c82016ebe644c820006bd644c820016de634c820006dd634c8200beee624c82004fcc324c820166f6614c820006f77558420006f67558420006f57558420006f47558420006f77458420006f67458420006f57458420006f47458420006f75458420006f65458420006f55458420006f45458420006f77358420006f67358420006f57358420006f47358420006f75358420006f65358420006f55358420006f45358420006f74358420006f64358420006f54358420006f44358420056f7725842004ef67258420056f5725842004ef47258420006f7525842004ef65258420006f5525842004ef45258420006f7425842004ef64258420006f5425842004ef44258420006f7325842004ef63258420006f5325842004ef4325842002ef7705842002cf7705842002ef6705842002ef5705842002cf5705842002ef4705842002ef7505842002ef6505842002ef5505842002ef4505842002ef7405842002ef6405842002ef5405842002ef4405842002ef7305842002ef6305842002ef5305842002ef4305842002ef7205842002ef6205842002ef5205842002ef4205842002dfb7648020006fb7648020004fb764802002f7a654802002f79654802002fba644802002fb96448020007db7348020007d8734802002efb634802002fda6348020006f9634802002fd96348020006d9634802002dfb724802002feb724802004efa624802002fea624802004fea3248020007e9324802002ff2614802002ff1614802004feb2148020307e9214802028df676d9510046f665d95100477665d9510046f465d951003df674d9510005f574d951003df474d95100077654d95100477454d9510035f673d9510005f573d9510035f473d95100477753d9510005f672d9510005f572d95100477452d951014ff370d951002df670d951000df570d951014ef760d951014ff360d95100477750d951014df77559510007776559510046f66559510046f46559510047746559510005f77459510007b77459510005b7745951003df6745951003df47459510007b4745951003db47459510047775459510005f77359510035f67359510035f47359510005f77259510005f47259510275f77059510007f37059510275f37059510136f76059510137f3605951025df676d9110045f675d9110005f575d9110045f475d911003ef664d911003fb664d911003ef464d9110007b754d911003fb454d9110035f673d9110005f573d9110035f473d
  | 6 => 0xe3159020006bd3159020006bc315902004ebf2159020006be2159020006bd215902004ebc215902002ebf705902002ebe705902002ebd705902002ebc705902002ebf505902002ebe505902002ebd505902002ebc505902002ebf305902002ebe305902002ebd305902002ebc305902002ebf205902002eaf205902002ebe205902002ebd205902002ead205902002ebc205902002ebf105902002eb7105902002ebe105902002ebd105902002eb5105902002ebc1059020004ff765502002cfe7655020004fd765502002cfc76550200267e65550200067d655502001ebe6455020006bd64550200673c545502021ede6355020005f77155020055f47155020216f66155020004ff7558c20024fe7558c20024fc7558c20004ff7458c2001cfe7458c2001cfc7458c2002cff7358c2002edf7358c20006df5358c2005ede5358c2005edc5358c20006df4358c2005ede4358c2005edc4358c20014ff7258c2004cfe7258c20014fd7258c2004cfc7258c2004ede3258c2004edc3258c20004ff7158c2000cfe7158c20004fd7158c2000cfc7158c2005edf3158c20006de3158c20006dd3158c2005edc3158c2002cff7058c2002cfe7058c2002cfd7058c2002cfc7058c2002ede3058c2002edc3058c2002eef2058c2002efa2058c2002eed2058c2002ef71058c2002ef51058c20006df7558c20006de7558c20006dd7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c20006de5458c20006dd5458c20006dc5458c2005edf7258c2004ede7258c2004edc7258c20006df5258c2004ede5258c2004edc5258c20006df4258c2004ede4258c2004edc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df5158c20006de5158c20006dd5158c20006dc5158c20006df4158c20006de4158c20006dd4158c20006dc4158c2004edf2158c20006de2158c20006dd2158c2004edc2158c2002edf7058c2002ede7058c2002edd7058c2002edc7058c2002edf5058c2002ede5058c2002edd5058c2002edc5058c2002edf4058c2002ede4058c2002edd4058c2002edc4058c2002edf2058c2002ecf2058c2002ede2058c2002eda2058c2002edd2058c2002ecd2058c2002edc2058c2002edf1058c2002ed71058c2002ede1058c2002edd1058c2002ed51058c2002edc1058c20004ff7654c2002cfe7654c20004fd7654c2002cfc7654c200267e6554c200067d6554c2020ebe6454c20006bd6454c20016de6354c20006dd6354c20005ef7254c2004dec7254c20206f66154c20004ff7650c2002cfe7650c20004fd7650c2002cfc7650c201fe7e6550c200067d6550c2001ebe6450c20006bd6450c20016de6350c20006dd6350c20005ef7250c2004dec7250c201f6f66150c20
  | 7 => 0x8120007e952c812004fea42c8120007e942c812004fea32c8120007e932c812002cff755942002e7f7559420004ff745942001cfe745942001cfc745942006e7f54594200067e545942006e7c5459420004ff7359420014fe7359420014fc735942006e7f53594200067e535942006e7c5359420024ff725942004cfe7259420024fd725942004cfc725942004e7e525942004e7c5259420004ff715942000cfe7159420004fd715942000cfc715942006e7f51594200067e51594200067d515942006e7c515942002cff705942002cfe705942002cfd705942002cfc705942002e7e505942002e7c505942002eef205942002eed205942002ef7105942002ef510594200067f74594200067e74594200067d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067c435942006e7f725942004e7e725942004e7c72594200067f425942004e7e425942004e7c42594200067f325942004e7e325942004e7c32594200067f71594200067e71594200067d71594200067c71594200067f41594200067e41594200067d41594200067c41594200067f31594200067e31594200067d31594200067c315942004e7f21594200067e21594200067d215942004e7c215942002e7f705942002e7e705942002e7d705942002e7c705942002e7f405942002e7e405942002e7d405942002e7c405942002e7f305942002e7e305942002e7d305942002e7c305942002e7f205942002e6f205942002e7e205942002e7d205942002e6d205942002e7c205942002e7f105942002e77105942002e7e105942002e7d105942002e75105942002e7c1059420004ff7559020024fe7559020024fc755902002cff745902002ebf7459020006bf5459020066be5459020066bc5459020004ff7359020014fe7359020014fc7359020066bf4359020006be4359020066bc435902001cff725902004cfe725902001cfd725902004cfc725902004ebe425902004ebc4259020004ff715902000cfe7159020004fd715902000cfc7159020066bf4159020006be4159020006bd4159020066bc415902002cff705902002cfe705902002cfd705902002cfc705902002ebe405902002ebc405902002eef205902002eed205902002ef7105902002ef51059020006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006be5359020006bc5359020066bf725902004ebe725902004ebc7259020006bf525902004ebe525902004ebc5259020006bf325902004ebe325902004ebc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf5159020006be5159020006bd5159020006bc5159020006bf3159020006b
  | 8 => 0x5ed755092008def7450920007af7450920007af645092001eee645092001eec645092008fac6450920005ef7350920007cf6350920007cc635092008faf4350920007ad435092032eef615092032eed6150920007eb705092002dee705092002dec7050920007e8705092008faf405092032fe710509200a4fe768c920006df638c920016dc638c920005ee768c9200a6ee768c920005ef758c920005ed758c920005ef748c920005ed748c920085ed738c920007cf638c920016ee638c920016ec638c920087cc638c920016cc638c920087ce538c920007cd538c920087ce438c920007cd438c92004feb708c92002dee708c92002dec708c92004fe8708c92004eef608c92029fce308c92029fcc308c920327e7108c92002cfc764c920006df634c920016dc634c920087cc324c920005fb704c92002df8704c92002dec764c920016ec764c92002cec764c920005ef754c920005ed754c920005ef744c920005ed744c920085ef734c920007cf734c920007cf634c920016ee634c920016ec634c920087cc634c920016cc634c920007eb704c92002dee704c92002dec704c920007e8704c920087cf304c92031fe7104c920024ff7654120094fd7654120024fc76541200067f65541200267c6554120006df635412013edc6354120005ef7254120005ec72541200076d525412001cff765012008cfd765012001cfc7650120006bf645012001ebc6450120006df635012010edc6350120005ef7250120005ec7250120007ad4250120005fa768c12002efa768c120085f9738c120007db638c120016fa638c120016f8638c120087d8638c120016d8638c12002feb728c12004dfa728c12002fe8728c12002efb628c12002feb628c120007ea528c120007e9528c120007ea428c120007e9428c120007da328c120087ea328c120007ca328c120087e9328c120087d8328c12002ff2718c12002ff1718c120014ff764c120084fd764c120014fc764c120006df634c120016dc634c120005ef724c120005ec724c120007cd324c12002fd8304c12002fe8204c120317f3104c120085f8764c120016f8764c120014f8764c12002dfb734c12002fdb734c120007db634c120016fa634c120016f8634c120087d8634c120087da534c120007d9534c120087da434c120007d9434c120007eb724c12004df8724c120007e8724c12002efb624c12002feb624c120007ea524c120007e9524c120007ea424c120007e9424c120087db324c120087ea324c120007d9324c120087e9324c120007c9324c120006df63c81200bedc63c812002dee72c812002eef62c812030ff310c812002dfa76c812002efa76c812002cfa76c812004dfb73c8120005f973c8120007db63c8120007d863c812002dfa72c812002efb62c812002feb62c812004fea52c
  | 9 => 0xc51d8d20006df41d8d20006de41d8d20006dd41d8d20006dc41d8d20006df21d8d20006de21d8d20006dd21d8d20006dc21d8d20006df70d8d2029ede70d8d20006dd70d8d2029edc70d8d20006df50d8d2029ede50d8d2029edc50d8d20006df40d8d2029ede40d8d2029edc40d8d2029ede20d8d2029edc20d8d20006df10d8d20006d710d8d2029ede10d8d20006dd10d8d2029edc10d8d20086dc6358d20004ff7558d20024fe7558d20024fc7558d20004ff7458d2001cfe7458d2001cfc7458d20084ff7358d20006df7358d200a4ff7258d20006ef7258d20004ff7158d2000cfe7158d20004fd7158d2000cfc7158d200bcff7058d20006fb7058d20006f71058d20005de7618d20086de7618d20004de7618d200875e7518d200875d7518d20006df6518d20006de6518d20006dd6518d20006dc6518d200879e7418d200879d7418d20006df6418d20006de6418d20006dd6418d20006dc6418d20087cd7218d2034edf6218d20087d67118d20087d57118d20006df6118d20006de6118d20006dd6118d20006dc6118d20087d97018d2034fce2018d2034fcc2018d20007d71018d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200267e6554d200067d6554d20006df6354d20016dc6354d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2001ebe6450d20006bd6450d20006df6350d20016dc6350d200b4fe7694920006df63949201e6dc6394920005ee76949200b6ee7694920095ed7594920026ee6594920026ec6594920005ed74949200976f54949200076d5494920005ed7394920007cf6394920007cc6394920346ef6194920346ed619492002dee709492002dec709492004eef6094920347e7109492002cfc76549200067f65549200267c6554920006df63549201cedc63549200976c5254920005fb705492002df8705492002dec7654920026ec765492002cec7654920095ef75549200076f75549200076f6554920026ee6554920026ec65549200976c6554920005ef7454920005ef7354920007cf6354920007cc63549200976f53549200076d535492033eef615492033eed6154920007eb705492002dee705492002dec7054920007e870549200976f505492033fe710549200acfe7690920006df63909201b6dc6390920005ee76909200aeee7690920005ef7590920005ed759092008ded749092001eee649092001eec649092008fae5490920007ad5490920005ed7390920007cf6390920007cc6390920336ef6190920336ed619092002dee709092002dec709092004eef6090920337e7109092002cfc7650920006bf645092001ebc6450920006df635092019edc635092008fac4250920005fb705092002df8705092002dec765092001eec765092002cec7650920005ef7550920
  | 10 => 0x952000cfc71d95200067e51d95200967c51d952002cfe70d9520094fd70d952002cfc70d95200967f50d9520006f710d95200967c6559520005df7359520085dc7359520094ff75595200067f7559520004ff745952001cfe745952001cfc7459520004ff7359520006df7359520004df7359520014fe7359520014fc7359520006dc7359520014dc73595200967f53595200b4ff7259520006ef7259520004ff715952000cfe7159520004fd715952000cfc71595200ccff7059520006fb7059520006f7105952001cfe76d912008ebe64d9120024fe75d9120004fd75d9120024fc75d912008ebe54d9120014fe73d9120004fd73d9120014fc73d912004cfe72d912002cfd72d912004cfc72d912008ebf42d9120004ff71d912000cfe71d9120004fd71d912000cfc71d9120006be41d912008ebc41d912002cfe70d912008cfd70d912002cfc70d912008ebf40d9120006f710d912008ebc6459120005df7359120085dc7359120004ff7559120024fe7559120024fc755912008cff7459120006bf7459120004ff7359120006df7359120004df7359120014fe7359120014fc7359120006dc7359120014dc735912008ebf43591200acff7259120006ef7259120004ff715912000cfe7159120004fd715912000cfc71591200c4ff7059120006fb7059120006f71059120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200267c6555120006bf645512001ebc645512008f3c545512021edc6355120005f7715512007df47155120014fe76d8d20086de63d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20006df53d8d20086de53d8d20086dc53d8d20006df43d8d20086de43d8d20086dc43d8d2004cfe72d8d2002cfd72d8d2004cfc72d8d20086df32d8d20004ff71d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20086df31d8d20006de31d8d20006dd31d8d20086dc31d8d2002cfe70d8d20084fd70d8d2002cfc70d8d20086df30d8d20006f710d8d20085de76d8d20014de76d8d20006df65d8d20006de65d8d20006dd65d8d20006dc65d8d20006df64d8d20006de64d8d20006dd64d8d20006dc64d8d2029fcf72d8d20006df61d8d20006de61d8d20006dd61d8d20006dc61d8d20007db70d8d2029fce20d8d2029fcc20d8d20007d710d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d2029edf72d8d20086de72d8d20006dd72d8d20006df52d8d20006dc52d8d20006df42d8d20006dc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d20006de51d8d20006dd51d8d20006d
  | 11 => 0x4ff7458e2001cfe7458e2001cfc7458e2002edf7358e200a6de5358e200a6de4358e200a6df3258e20004ff7158e2000cfe7158e20004fd7158e2000cfc7158e2002cfc7058e2002ede3058e2002edc3058e2002eef2058e2002eed2058e2002ef71058e2002ef51058e20004ff7654e2002cfe7654e20004fd7654e2002cfc7654e200267e6554e200067d6554e20016de6354e20006dd6354e20005ef7254e20005ec7254e20206f66154e20004ff7650e2002cfe7650e20004fd7650e2002cfc7650e2001ebe6450e20006bd6450e20016de6350e20006dd6350e20005ef7250e20005ec7250e201f6f66150e20094fd7694a201def66194a20024ff7654a2002cfc7654a200267e6554a200067d6554a201c6f66154a20005fb7054a2002df87054a2008cfd7690a201aef66190a2001cff7650a2002cfc7650a2001ebe6450a20006bd6450a20196f66150a20005fb7050a2002df87050a20084fd768ca2029edf638ca20016dc638ca2017ef6618ca2002df8708ca2029fda308ca20014ff764ca2002cfc764ca20016de634ca20006dd634ca200a7cc324ca20166f6614ca20005fb704ca2002df8704ca20006f77558620006f67558620006f57558620006f47558620006f77458620006f67458620006f57458620006f47458620006f75458620006f65458620006f55458620006f45458620006f77358620006f67358620006f57358620006f47358620006f75358620006f65358620006f55358620006f45358620006f74358620006f64358620006f54358620006f4435862009ef7725862009ef67258620006f5725862009ef47258620006f75258620006f65258620006f55258620006f45258620006f74258620006f64258620006f54258620006f44258620006f73258620006f63258620006f53258620006f4325862002ef7705862002ef6705862002ef5705862002ef4705862002ef7505862002ef6505862002ef5505862002ef4505862002ef7405862002ef6405862002ef5405862002ef4405862002ef7305862002ef6305862002ef5305862002ef4305862002ef7205862002ef6205862002ef5205862002ef4205862002dfb764c22005efb764c22002fdb734c22002fdb634c220016fa634c22002ef8634c22002fd8634c2200a7da534c220007d9534c2200a7da434c220007d9434c22004df8724c2200a7db324c220007d9324c22002ff2614c22002ff1614c22002df976c822004ef976c822004dfb73c8220005f973c822002fea72c822002ff261c822002ff161c8220024fe76d95200967e65d952001cfe74d9520004fd74d952001cfc74d95200967f54d9520014fe73d9520004fd73d9520014fc73d952004cfe72d952002cfd72d952004cfc72d95200967f52d9520004ff71d952000cfe71d9520004fd71d
  | 12 => 0xf7454b20005ef7354b200cf6f5354b200076d5354b20376ef6154b20376ed6154b2002dee7054b2002dec7054b200cf6f5054b20377e71054b2002ded7690b2004eed7690b2002ced7690b2004def7590b20005ed7590b2001eee6490b2004fae6490b2004fad6490b2004eec6490b200c7ae5490b20007ad5490b20005ed7390b2004eef6190b2036eed6190b2002dee7090b2004fea7090b2004fe97090b2002dec7090b2036fe71090b20064ff7650b2004ebf6450b2004ebc6450b2004fac4250b20005ef7650b20066ef7650b20005ef7550b20005ed7550b2004faf7450b2004faf6450b2001eee6450b2001eec6450b2004fac6450b20005ef7350b200c7af4350b20007ad4350b20366ef6150b20366ed6150b2002dee7050b2002dec7050b200c7af4050b20367e71050b2002ded768cb2004eed768cb2002ced768cb2004def758cb20005ed758cb2004def748cb20005ed748cb20016ee638cb2004fce638cb2004fcd638cb2004eec638cb200bfce538cb20007cd538cb200bfce438cb20007cd438cb2002dee708cb2004fea708cb2004fe9708cb2002dec708cb2029fce308cb2029fcc308cb2035fe7108cb2005cff764cb2004edf634cb2004edc634cb2004fcc324cb20005ef764cb2005eef764cb20005ef754cb20005ed754cb20005ef744cb20005ed744cb2004fcf734cb2004fcf634cb20016ee634cb20016ec634cb2004fcc634cb20016cc634cb2002dee704cb2002dec704cb200bfcf304cb20357e7104cb20024ff765432004cfc76543200267e65543200067d6554320005ef725432004dec72543200076d525432001cff765032004cfc765032001ebe6450320006bd6450320005ef725032004dec7250320007ad4250320014ff764c32004cfc764c320016de634c320006dd634c320005ef724c32004dec724c320007cd324c32002e7f7559620004ff745962001cfe745962001cfc74596200b67f5459620004ff7359620014fe7359620014fc73596200b67f53596200b67f5259620004ff715962000cfe7159620004fd715962000cfc715962002cfc705962002e7e505962002e7c505962002eef205962002eed205962002ef7105962002ef51059620004ff7559220024fe7559220024fc755922002ebf74592200aebe5459220004ff7359220014fe7359220014fc73592200aebf43592200aebf4259220004ff715922000cfe7159220004fd715922000cfc715922002cfc705922002ebe405922002ebc405922002eef205922002eed205922002ef7105922002ef51059220004ff765522002cfe7655220004fd765522002cfc76552200267e65552200067d655522001ebe6455220006bd64552200af3c5455220005f7715522009df47155220216f66155220004ff7558e20024fe7558e20024fc7558e20
  | 13 => 0x13010cfd7650130014fc7650130006bf645013001ebc6450130005df7350130015dc73501300079d43501300ccfd75d972001cfe74d9720004fd74d972004cfc74d97200ce7f54d9720014fe73d9720004fd73d972004cfc73d972004eee72d972004e7f52d972004cff71d972000cfe71d9720004fd71d972000cfc71d972004ef970d9720006f710d9720024ff765972004e7c655972004e7f7559720004ff745972001cfe745972001cfc7459720004ff7359720014fe7359720014fc73597200ce7f535972002cfc725972004e7e525972004e7c5259720004ff715972000cfe7159720004fd715972000cfc71597200ce7f5059720006f71059720024fe75d9320004fd75d932004cfc75d93200c4fd74d93200c6be54d9320014fe73d9320004fd73d932004cfc73d932004eee72d932004ebf42d932004cff71d932000cfe71d9320004fd71d932000cfc71d932004ef970d9320006f710d932001cff765932004ebc6459320004ff7559320024fe7559320024fc755932004ebf7459320004ff7359320014fe7359320014fc73593200c6bf435932002cfc725932004ebe425932004ebc4259320004ff715932000cfe7159320004fd715932000cfc71593200c6bf4059320006f71059320004ff765532004cfe7655320004fd765532004cfc76553200067f65553200267c6555320006bf645532001ebc64553200c73c5455320005f77155320075f47155320024fe75d8f20004fd75d8f2004cfc75d8f2001cfe74d8f20004fd74d8f2004cfc74d8f200bcfd73d8f200bede53d8f200bede43d8f2004eee72d8f2004edf32d8f2004cff71d8f2000cfe71d8f20004fd71d8f2000cfc71d8f2004ef970d8f2029ede30d8f2029edc30d8f20006f710d8f20014ff7658f2004edc6358f20004ff7558f20024fe7558f20024fc7558f20004ff7458f2001cfe7458f2001cfc7458f2004edf7358f2002cfc7258f2004ede3258f2004edc3258f20004ff7158f2000cfe7158f20004fd7158f2000cfc7158f200bedf3058f20006f71058f20004ff7654f2004cfe7654f20004fd7654f2004cfc7654f200267e6554f200067d6554f20006df6354f20016dc6354f20004ff7650f2004cfe7650f20004fd7650f2004cfc7650f2001ebe6450f20006bd6450f20006df6350f20016dc6350f2002ded7694b2004eed7694b2002ced7694b20026ee6594b2004f6e6594b2004f6d6594b2004eec6594b20005ed7494b200cf6f5494b200076d5494b20005ed7394b2004eef6194b2037eed6194b2002dee7094b2004fea7094b2004fe97094b2002dec7094b2037fe71094b2006cff7654b2004e7f6554b2004e7c6554b2004f6c5254b20005ef7654b2006eef7654b2004f6f7554b2004f6f6554b20026ee6554b20026ec6554b2004f6c6554b20005e
  | 14 => 0xe75f5254d30396df6154d30396dd6154d303975e5154d300e75c5154d30007db7054d3002dde7054d3002ddc7054d30007d87054d30016df6054d30017db6054d300e75f5054d30397d71054d3002ddc7650d3001edc7650d3002cdc7650d30005df7550d30005dd7550d30006df6550d30006dd6550d30015df7450d300179f7450d300079f6450d3001ede6450d3001edc6450d300df9c6450d300df9e5450d300079d5450d30005df7250d300df9f4250d3038edf6150d3038edd6150d3038f9e4150d300df9c4150d30007db7050d3002dde7050d3002ddc7050d30007d87050d30016df6050d30017db6050d300df9f4050d3038fd71050d30024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d893002cfd73d8930006ef52d8930006ec52d8930006ef42d8930006ec42d89300a6ee32d89300a6ed32d8930004ff71d893000cfe71d8930004fd71d893000cfc71d8930006ef21d8930006ed21d8930006f710d8930006ef6298930085f970989300bdfb70589300e57e75189300057d75189300ddbe7418930005bd7418930006ed62189300d5f67118930005f57118930024fe751893004e7e75189300247e7518930004fd751893004e7d75189300047d751893004cfc751893001cfe741893004ebe741893001cbe7418930004fd741893004ebd7418930004bd741893004cfc741893002cfd731893005ede5318930006dd531893005ede4318930006dd4318930006ef521893004eec5218930006ef421893004eec421893004edf321893004eee321893005eed321893004cff711893000cfe711893004ef6711893000cf67118930004fd711893004ef57118930004f5711893000cfc711893004eef2118930006ed211893002cfe701893004ef9701893002cfc701893034ede301893034edc3018930006f71018930004fe7694930004fd769493004cfc7694930015de7394930005dd739493002dfa7094930005f97094930004ff7654930004fe7654930004fc76549300267e65549300067d6554930015de73549300075d5354930004fe7690930004fd769093004cfc7690930015de7390930005dd739093002dfa7090930005f97090930004ff7650930004fe7650930004fc765093001ebe6450930006bd6450930015de73509300079d435093002cdc764c930005df754c930005dd754c930005df744c930005dd744c930015df724c930017cf724c930007cf624c93004edc624c930007cc624c930006cc624c930007db704c93002dde704c93002ddc704c930007d8704c930016df604c930017db604c930387d7104c930024ff7654130014fe765413013cfd7654130014fc76541300067f65541300267c6554130005df7354130015dc73541300075d535413001cff7650130014fe765
  | 15 => 0x773586300eef67358630036f573586300eef47358630036f75358630036f65358630036f55358630036f45358630036f74358630036f64358630036f54358630036f44358630006f77258630006f67258630006f57258630006f47258630006f75258630006f65258630006f55258630006f45258630006f74258630006f64258630006f54258630006f44258630036f73258630036f63258630036f53258630036f4325863002ef7705863002ef6705863002ef5705863002ef4705863002ef7505863002ef6505863002ef5505863002ef4505863002ef7405863002ef6405863002ef5405863002ef4405863002ef7305863002ef6305863002ef5305863002ef4305863002ef7205863002ef6205863002ef5205863002ef42058630024fe76d95300e67e65d953001cfe74d9530004fd74d953001cfc74d953002cff73d9530014fe73d953002cfd73d9530014fc73d95301567f53d95301567d53d9530156de43d953004cfe72d9530004fd72d9530004ff71d953000cfe71d9530004fd71d953000cfc71d9530014fd70d95300e67f50d9530006f710d95300e67c6559530005ef7259530005ec72595303a5fb7059530154ff75595300067f7559530004ff745953001cfe745953001cfc74595300e67f545953013cff7359530006df735953013ede4359530004ff7259530006ef7259530004ef725953004cfc7259530006ec7259530004ec72595300e67f5259530004ff715953000cfe7159530004fd715953000cfc71595303a4ff7059530006fb7059530006f7105953001cfe76d91300debe64d9130024fe75d9130004fd75d9130024fc75d913002cff73d9130014fe73d913002cfd73d9130014fc73d9130126de53d9130126bf43d9130126bd43d913004cfe72d9130004fd72d9130004ff71d913000cfe71d9130004fd71d913000cfc71d9130014fd70d91300debf40d9130006f710d91300debc6459130005ef7259130005ec725913039dfb7059130004ff7559130024fe7559130024fc7559130124ff7459130006bf74591300debe545913010cff7359130006df735913010ede5359130004ff7259130006ef7259130004ef725913004cfc7259130006ec7259130004ec72591300debf4259130004ff715913000cfe7159130004fd715913000cfc715913039cff7059130006fb7059130006f71059130004ff7655130004fe7655130004fd7655130004fc76551300267e65551300067d655513001ebe6455130006bd64551300df3c5455130015de7355130005f771551300d5f4715513002ddc7654d30026dc7654d3002cdc7654d30015df7554d300175f7554d300075f6554d30026de6554d30026dc6554d300e75c6554d30005df7454d30006df6454d30006dd6454d300e75f5454d300075d5454d30005df7254d30
  | 16 => 0x41400267c6554140005bf745414001dbc74541400073d545414002e7f7559630004ff745963001cfe745963001cfc74596300fe7f545963013e7f535963013e7d5359630004ff725963004cfc72596300fe7f525963013edc3259630004ff715963000cfe7159630004fd715963000cfc715963002cfe705963002cfc705963002e7e505963002e7c505963002edf305963002edd305963002ef7105963002ef51059630004ff7559230024fe7559230024fc755923002ebf74592300f6be545923010ebf435923010ebd4359230004ff725923004cfc72592300f6bf425923010edc3259230004ff715923000cfe7159230004fd715923000cfc715923002cfe705923002cfc705923002ebe405923002ebc405923002edf305923002edd305923002ef7105923002ef51059230004ff765523002cfe7655230004fd765523002cfc76552300267e65552300067d655523001ebe6455230006bd64552300f73c5455230005f771552300edf47155230216f66155230024fe7598a30004fd7598a3004cfc7598a3001cfe7498a30004fd7498a3004cfc7498a3002eee7298a3004eee3298a300beed3298a3004cff7198a3000cfe7198a30004fd7198a3000cfc7198a3002cfe7098a3002efa7098a3002cfa7098a3002cfc7098a3002eee2098a3002efa2098a3002eec2098a3002ef71098a3002ef51098a30004ff7558a30024fe7558a30024fc7558a30004ff7458a3001cfe7458a3001cfc7458a3002eef7258a30086ee3258a30086ed3258a30086dc3258a30004ff7158a3000cfe7158a30004fd7158a3000cfc7158a3002cfc7058a3002edf3058a3002edd3058a3002eee2058a3002eec2058a3002ef71058a3002ef51058a3004cff7694a3002cfe7694a30004fd7694a3004eee6294a30006ed6294a301def66194a3002dfa7094a30005f97094a30004ff7654a30004fd7654a3002cfc7654a300267e6554a300067d6554a30005df7354a30015dc7354a30006ee6254a30006ed6254a301c6f66154a3004cff7690a3002cfe7690a30004fd7690a3004eee6290a30006ed6290a301aef66190a3002dfa7090a30005f97090a30004ff7650a30004fd7650a3002cfc7650a3001ebe6450a30006bd6450a30005df7350a30015dc7350a30006ee6250a30006ed6250a30196f66150a3029edf658ca30006dd658ca3029edf648ca30006dd648ca30015de728ca30017ce728ca3029fce628ca30006dd628ca3029fcd628ca3029fd6618ca3029fd5618ca3029fda708ca3029ddd708ca30007d9708ca30016de608ca30017da608ca3029fd7108ca30006f77558630006f67558630006f57558630006f47558630006f77458630006f67458630006f57458630006f47458630006f75458630006f65458630006f55458630006f454586300eef
  | 17 => 0x3c6bd61551401173f51551403c73d5155140007bb705514002dbe705514002dbc7055140007b8705514001ebf605514001fbb60551401173f50551403c7b710551403c7ba10551403c7b91055140014fe76d8d4010ede63d8d40024fe75d8d40004fd75d8d40024fc75d8d4002cfd74d8d40014fc74d8d400f6be54d8d40006bd54d8d4010ede43d8d400f6dd43d8d4004cfe72d8d40004fd72d8d400f6bf42d8d4010edc32d8d40004ff71d8d4000cfe71d8d40004fd71d8d4000cfc71d8d4001cfd70d8d4010edf30d8d40006f710d8d4010edc6358d40005ef7258d40005ec7258d403bdfb7058d40004ff7654d40004fe7654d40004fc7654d400267e6554d400067d6554d4001dbe7454d400073d5454d40016de6354d4002dbc7650d40016bc7650d4002cbc7650d40005bf7550d40005bd7550d40006bf6550d40006bd6550d4001dbf7350d4001f9f7350d400079f6350d40016be6350d40016bc6350d4010f9c6350d4010f9e5350d400079d5350d40005bf7250d4010f9c3250d401f6be6150d401f6bc6150d4010f9f3150d403b79d3150d40007bb7050d4002dbe7050d4002dbc7050d40007b87050d4001ebf6050d4001fbb6050d4010f9f3050d403b7b71050d403b7ba1050d403b7b91050d40024fe75d8940004fd75d8940024fc75d894002cfd74d8940014fe73d8940004fd73d8940014fc73d89400aebf43d8940006bd43d89400aeee42d89400aeed42d8940006ef32d8940006ec32d8940004ff71d894000cfe71d8940004fd71d894000cfc71d8940006f710d8940006ef629894008df97098940005df735894010ddc73589400c5fb7058940006ed6218940024fe7518940004fd751894004cfc751894002cfd7418940066be5418940006bd5418940014fe7318940004fd731894004cfc731894004ebf421894004eee4218940066ed4218940006ef321894004eec321894004cff711894000cfe7118940004fd711894000cfc7118940006f71018940004fe7694940004fd769494004cfc769494001dbe7494940005bd74949400073d5494940004ff7654940004fe7654940004fc765494001dbe745494002cbc7650940005bf7550940005bd7550940005bf7350940006bf635094001dbf725094001faf7250940007af625094004ebc6250940007ac62509403afaf21509403afad2150940007bb705094002dbe705094002dbc7050940007b8705094001ebf605094001fbb60509403afb710509403afba10509403afb91050940004fe768c940004fd768c94004cfc768c94001dbe748c940005bd748c940006df638c940016dc638c9400079d438c940004ff764c940004fe764c940004fc764c94001dbe744c940005bd744c94010fcc324c940024ff765414001cfe7654140144fd765414001cfc76541400067f655
  | 18 => 0xf7158a4000cfe7158a40004fd7158a4000cfc7158a4002cfc7058a4002ebf4058a4002ebd4058a4002eee2058a4002eec2058a4002ef71058a4002ef51058a4004cff7694a4002cfe7694a40004fd7694a4004eee6294a40006ed6294a401def66194a40004ff7654a40004fd7654a4002cfc7654a400267e6554a400067d6554a40006ee6254a40006ed6254a401c6f66154a4004cff768ca4002cfe768ca40004fd768ca40016dc638ca4004eee628ca40006ed628ca4017ef6618ca40004ff764ca40004fd764ca4002cfc764ca40016de634ca40006dd634ca40006ee624ca40006ed624ca40127cc324ca40166f6614ca40006f77558640006f67558640006f57558640006f4755864011ef7745864011ef6745864003ef5745864011ef4745864003ef7545864003ef6545864003ef5545864003ef45458640006f77358640006f67358640006f57358640006f47358640006f75358640006f65358640006f55358640006f4535864003ef7435864003ef6435864003ef5435864003ef44358640006f77258640006f67258640006f57258640006f47258640006f75258640006f65258640006f55258640006f4525864003ef7425864003ef6425864003ef5425864003ef44258640006f73258640006f63258640006f53258640006f4325864002ef7705864002ef6705864002ef5705864002ef4705864002ef7505864002ef6505864002ef5505864002ef4505864002ef7405864002ef6405864002ef5405864002ef4405864002ef7305864002ef6305864002ef5305864002ef4305864002ef7205864002ef6205864002ef5205864002ef42058640024fe76d95401167e65d954002cff74d954001cfe74d954002cfd74d954001cfc74d954015e7f54d954015e7d54d9540014fe73d9540004fd73d9540014fc73d954015ebf43d954004cfe72d9540004fd72d9540004ff71d954000cfe71d9540004fd71d954000cfc71d95400067e51d95401167c51d954001cfd70d95401167f50d9540006f710d9540006fa10d9540006f910d95401167c6559540005f77159540105f471595403cdfb705954015cff75595400067f7559540144ff7459540006bf7459540004ff7359540014fe7359540014fc73595401167f5359540146bf4359540004ff725954004cfc7259540004ff7159540006f77159540004f7715954000cfe7159540004fd715954000cfc7159540006f4715954000cf471595403ccff7059540006fb7059540006f71059540006fa1059540006f9105954002dbc7655140026bc765514002cbc765514001dbf755514001f3f75551400073f6555140026be6555140026bc65551401173c65551400263c6555140005bf73551401173f5355140005bf72551401173c5255140007b771551403c7b471551403c6bf6155140
  | 19 => 0x8950014fe73d8950004fd73d8950014fc73d89500b67f53d89500067d53d89500b6ee52d89500b6ed52d8950006ef32d8950006ec32d8950004ff71d895000cfe71d8950004fd71d895000cfc71d8950006f710d8950006ef6298950095f97098950005df735895013ddc73589500cdfb7058950006ed621895002cfd751895001cfe7418950004fd741895004cfc741895006e7f54189500067d5418950014fe7318950004fd731895004cfc731895004e7f521895004eee521895006eed5218950006ef321895004eec321895004cff711895000cfe7118950004fd711895000cfc7118950006f7101895002c7c76549500057f74549500057f73549500067f63549500257f72549500276f72549500076f625495004e7c62549500076c62549503d76f21549503d76d21549500077b705495002d7e705495002d7c70549500077870549500267f60549500277b60549503d77710549503d77a10549503d7791054950004fe7690950004fd769095004cfc76909500257e75909500057d75909500073d5490950004ff7650950004fe7650950004fc76509500257e75509500057d7550950004fe768c950004fd768c95004cfc768c9500257e758c9500057d758c950006df638c950016dc638c9500075d538c950004ff764c950004fe764c950004fc764c9500257e754c9500057d754c95013fcc324c95002e7f75596401467f54596401467d5459640004ff7359640014fe7359640014fc735964012e7f5359640004ff725964004cfc725964012e7f5259640004ff715964000cfe7159640004fd715964000cfc715964002cfe705964002cfc705964002e7e505964002e7c505964002ebf405964002ebd405964002ef7105964002efa105964002ef51059640006f91059640004ff7558e40024fe7558e40024fc7558e4002edf7358e40126de5358e40126de4358e400dedd4358e40004ff7258e4004cfc7258e40126df3258e40004ff7158e4000cfe7158e40004fd7158e4000cfc7158e4002cfe7058e4002cfc7058e4002ebf4058e4002ebd4058e4002ede3058e4002edc3058e4002ef71058e4002ef51058e40004ff7654e40004fd7654e4002cfc7654e400267e6554e400067d6554e40016de6354e40006dd6354e40206f66154e40024fe7598a40004fd7598a4004cfc7598a40014fe7398a40004fd7398a4004cfc7398a4002eee7298a4004eee4298a400c6ed4298a4004cff7198a4000cfe7198a40004fd7198a4000cfc7198a4002cfe7098a4002cfc7098a4002eee2098a4002eec2098a4002ef71098a4002ef51098a40004ff7558a40024fe7558a40024fc7558a40004ff7358a40006df7358a40004df7358a40014fe7358a40014fc7358a40006dc7358a40014dc7358a4002eef7258a4008eee4258a4008eed4258a40004f
  | 20 => 0x6f67358650006f57358650006f47358650046f75358650046f65358650046f55358650046f45358650006f74358650006f64358650006f54358650006f44358650006f77258650006f67258650006f57258650006f47258650046f75258650046f65258650046f55258650046f45258650006f74258650006f64258650006f54258650006f44258650006f73258650006f63258650006f53258650006f4325865002ef7705865002ef6705865002ef5705865002ef4705865002ef7505865002ef6505865002ef5505865002ef4505865002ef7405865002ef6405865002ef5405865002ef4405865002ef7305865002ef6305865002ef5305865002ef4305865002ef7205865002ef6205865002ef5205865002ef4205865001cfe76d9150146be64d915002cfd75d915001cfc75d9150146be54d915012ebd54d9150014fe73d9150004fd73d9150014fc73d915012e7f53d915004cfe72d9150004fd72d9150004ff71d915000cfe71d9150004fd71d915000cfc71d9150006be41d9150146bc41d9150024fd70d9150146bf40d9150006f710d9150006fa10d9150006f910d9150146bc6459150005f77159150135f471591503f5fb705915002d7c765515001e7c765515002c7c76551500257f74551500273f74551500073f645515001e7e645515001e7c64551501473c645515001e3c64551500057f73551501473f43551500057f72551501473c42551500077771551503ef7471551503ee7f61551503ee7d61551501473f41551503ef3d41551500077b705515002d7e705515002d7c70551500077870551500267f60551500277b60551501473f40551503ef7710551503ef7a10551503ef791055150014fe76d8d5013ede63d8d5002cfd75d8d50014fc75d8d5001cfe74d8d50004fd74d8d5001cfc74d8d500fe7f54d8d500067d54d8d5013ede53d8d500fedd53d8d5004cfe72d8d50004fd72d8d500fe7f52d8d5013edc32d8d50004ff71d8d5000cfe71d8d50004fd71d8d5000cfc71d8d50024fd70d8d5013edf30d8d50006f710d8d5013edc6358d50005ef7258d50005ec7258d503e5fb7058d5002d7c7654d500167c7654d5002c7c7654d500057f7454d500067f6454d500257f7354d500275f7354d500075f6354d500167e6354d500167c6354d5013f5c6354d5013f5e4354d500057f7254d5013f5c3254d502067e6154d502067c6154d5013f5f3154d503df5d3154d500077b7054d5002d7e7054d5002d7c7054d50007787054d500267f6054d500277b6054d5013f5f3054d503df771054d503df7a1054d503df791054d50004ff7650d50004fe7650d50004fc7650d500257e7550d500057d7550d5001ebe6450d500073d5450d50016de6350d500075d5350d5002cfd75d895001cfe74d8950004fd74d895001cfc74d
  | 21 => 0x7108c9320bfcc32d8132024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d8132004ff71d813200cfe71d8132004fd71d813200cfc71d81320befa30d8132006f710d8132006fa10d8132006f910d81320a7cc3298132165f67198132005f57198132006fb6098132087cc32581321757e75181320057d751813216dbe7418132005bd741813229edf631813205fcc3218132165f67118132005f5711813202efa6018132006f9601813202ebf745925015ebe5459250116bd5459250004ff7359250014fe7359250014fc735925015ebf4359250004ff725925004cfc725925015ebf4259250004ff715925000cfe7159250004fd715925000cfc715925002cfe705925002cfc705925002e7f505925002e7d505925002ebe405925002ebc405925002ef7105925002efa105925002ef51059250006f91059250004ff7458e5001cfe7458e5001cfc7458e5002edf7358e50156de5358e500e6dd5358e50156de4358e50004ff7258e5004cfc7258e50156df3258e50004ff7158e5000cfe7158e50004fd7158e5000cfc7158e5002cfe7058e5002cfc7058e5002e7f5058e5002e7d5058e5002ede3058e5002edc3058e5002ef71058e5002ef51058e50004ff7650e50004fd7650e5002cfc7650e5001ebe6450e50006bd6450e50016de6350e50006dd6350e501f6f66150e5001cfe7498a50004fd7498a5004cfc7498a50014fe7398a50004fd7398a5004cfc7398a5002eee7298a5004eee5298a500ceed5298a5004cff7198a5000cfe7198a50004fd7198a5000cfc7198a5002cfe7098a5002cfc7098a5002eee2098a5002eec2098a5002ef71098a5002ef51098a50004ff7458a5001cfe7458a5001cfc7458a50004ff7358a50006df7358a50004df7358a50014fe7358a50014fc7358a50006dc7358a50014dc7358a5002eef7258a50096ee5258a50096ed5258a50004ff7158a5000cfe7158a50004fd7158a5000cfc7158a5002cfc7058a5002e7f5058a5002e7d5058a5002eee2058a5002eec2058a5002ef71058a5002ef51058a5004cff7690a5002cfe7690a50004fd7690a5004eee6290a50006ed6290a501aef66190a50004ff7650a50004fd7650a5002cfc7650a5001ebe6450a50006bd6450a50006ee6250a50006ed6250a50196f66150a5004cff768ca5002cfe768ca50004fd768ca50016dc638ca5004eee628ca50006ed628ca5017ef6618ca50004ff764ca50004fd764ca5002cfc764ca50016de634ca50006dd634ca50006ee624ca50006ed624ca50157cc324ca50166f6614ca5014ef7755865014ef67558650046f5755865014ef47558650006f77458650006f67458650006f57458650006f47458650046f75458650046f65458650046f55458650046f45458650006f77358650
  | 22 => 0xe3241cff7654a3204e7f6554a3204e7c6554a32015de7354a320075d5354a321cfcf3254a32414ff7650a3204ebf6450a3204ebc6450a32015de7350a320079d4350a3217df67198232005f5719823204efb609823202ef8609823204ef86058232004ff7558232024fe7558232024fc7558232004ff745823201cfe745823201cfc7458232086de5358232006dd5358232086de4358232006dd435823204cfc7258232086df3258232004ff715823200cfe7158232004fd715823200cfc7158232086fa305823229edc305823204efb205823204ef82058232006f71058232024fe76d95321767e65d95321e7cc32d953201cfe74d9532004fd74d953201cfc74d95321767f54d953204cff73d95321e4fd73d95321e67f53d95321e67d53d9532014fd72d95321767f52d95321e6dc32d9532004ff71d953200cfe71d9532004fd71d953200cfc71d953202cfe70d9532004fd70d95321e6df30d9532006f710d95321767c655953241def72595321cfcc32595321e4ff75595320067f7559532004ff745953201cfe745953201cfc74595321ccff7359532006df735953241cff7259532006ef72595321cedc3259532004ff715953200cfe7159532004fd715953200cfc7159532004ff705953202cfc70595321767f50595321cedf3059532006f7105953201cfe76d913216ebe64d91321b7cc32d9132024fe75d9132004fd75d9132024fc75d913216ebe54d913204cff73d91321b4fd73d91321b6bf43d91321b6bd43d9132014fd72d913216ebf42d91321b6dc32d9132004ff71d913200cfe71d9132004fd71d913200cfc71d913202cfe70d9132004fd70d91321b6df30d9132006f710d913216ebc6459132415ef725913219fcc3259132004ff7559132024fe7559132024fc75591321b4ff7459132006bf745913219cff7359132006df7359132414ff7259132006ef725913219edc3259132004ff715913200cfe7159132004fd715913200cfc7159132004ff705913202cfc705913216ebf405913219edf3059132006f71059132004ff7655132004fe7655132004fd7655132004fc76551320067f65551320267c6555132006bf645513201ebc645513216f3c545513221fcc3255132005f77155132165f4715513240cfe76949321776f529493204fcc3294932024ff7654932014fe76549321ccfd7654932014fc76549320067f65549320267c6554932005df7354932015dc73549321cfcc3254932404fe769093204fcc329093201cff7650932014fe765093219cfd7650932014fc7650932006bf645093201ebc6450932005df7350932015dc735093219fcc3250932006df658c932006dd658c932006df648c932006dd648c93204dde728c93204fce728c932015ce728c93204edf628c932017cf628c932005dd708c9323ffd
  | 23 => 0x437b71090942024fe75d8142004fd75d8142024fc75d8142014fe73d8142004fd73d8142014fc73d81420c6bf43d8142006bd43d8142004ff71d814200cfe71d8142004fd71d814200cfc71d81420c6fa40d8142006f710d8142195f67198142005f57198142006fb6098142005df735814219ddc73581421a57e75181420057d751814219dde7318142005dd7318142195f67118142005f5711814202efa6018142006f960181421ccfd75d963201cfe74d9632004fd74d963204cfc74d963218e7f54d963204edd73d96321e6de43d963204cfe72d963204eee72d963204e7f52d963204cff71d963200cfe71d9632004fd71d963200cfc71d963202cfe70d9632004fd70d9632006f710d9632024ff765963204e7c655963204e7f7559632004ff745963201cfe745963201cfc74596321ce7f53596321ce7d53596321cede435963204cfe725963204cfc725963204e7e525963204e7c5259632004ff715963200cfe7159632004fd715963200cfc7159632004ff705963202cfc705963218e7f5059632006f71059632024fe75d9232004fd75d923204cfc75d923219cfd74d9232186be54d923204edd73d92321b6de53d923204cfe72d923204eee72d923204ebf42d923204cff71d923200cfe71d9232004fd71d923200cfc71d923202cfe70d9232004fd70d9232006f710d923201cff765923204ebc6459232004ff7559232024fe7559232024fc755923204ebf745923219ede535923219ebf435923219ebd435923204cfe725923204cfc725923204ebe425923204ebc4259232004ff715923200cfe7159232004fd715923200cfc7159232004ff705923202cfc7059232186bf4059232006f71059232004ff765523204cfe7655232004fd765523204cfc76552320067f65552320267c6555232006bf645523201ebc64552321873c5455232015de7355232005f7715523217df4715523218ddf7654e32026df7654e32024df7654e32015df7554e320175f7554e32026de6554e3218f5e6554e320075d6554e32026dc6554e32005df7454e32006df6454e32006dd6454e3218f5f5454e320075d5454e32005df7254e32007cf7254e32007cc7254e32016de6254e32017ce6254e3218f5f5254e3242edf6154e3242edd6154e3242f5e5154e3218f5c5154e3229ddc7054e3218f5f5054e3242fd71054e32185df7650e3201edf7650e3201cdf7650e32005df7550e32005dd7550e32006df6550e32006dd6550e32015df7450e320179f7450e3201ede6450e321879e6450e320079d6450e3201edc6450e321879e5450e320079d5450e32005df7250e32007cf7250e32007cc7250e32016de6250e32017ce6250e321879f4250e32426df6150e32426dd6150e324279e4150e321879c4150e3229ddc7050e321879f4050e32427d7105
  | 24 => 0xd7654e4204cfc7654e420267e6554e420067d6554e420073d5454e42016dc6354e42005ef7254e4204dec7254e42454ff7654a4201dbe7454a421d7af4254a421adf67198242005f5719824204efb609824202ef8609824204ef86058242004ff7558242024fe7558242024fc755824208ebe5458242006bd5458242004ff7358242014fe7358242014fc735824204cfc725824208ebf4258242004ff715824200cfe7158242004fd715824200cfc715824208efa405824204efb205824204ef82058242006f71058242024fe76d95421a67e65d954204cff74d95421ecfd74d95421ee7f54d95421ee7d54d9542014fe73d9542004fd73d9542014fc73d95421eebf43d954201cfd72d95421a67f52d95421eebc42d9542004ff71d954200cfe71d9542004fd71d954200cfc71d9542006ef21d9542006ed21d954202cfe70d9542004fd70d95421eebf40d9542006f710d95421a67c6559542455ef7259542005f77159542195f471595421ecff75595420067f75595421d4ff7459542006bf7459542004ff7359542014fe7359542014fc73595421a67f53595421d6bf4359542454ff7259542006ef72595421a67c52595421d6bc4259542004ff7159542006f77159542004f7715954200cfe7159542004fd715954200cfc7159542006f4715954200cf47159542006ef2159542006ed2159542004ff705954202cfc70595421a67f50595421d6bf4059542006f71059542014fe76d8d4219ede63d8d42024fe75d8d42004fd75d8d42024fc75d8d4219ede53d8d4219ede43d8d42186dd43d8d4201cfd72d8d4219edf32d8d42004ff71d8d4200cfe71d8d42004fd71d8d4200cfc71d8d4202cfe70d8d42004fd70d8d42186bf40d8d4219edc30d8d42006f710d8d4219edc6358d4244def7258d42004ff7654d42004fe7654d42004fc7654d420267e6554d420067d6554d42006df6354d42016dc6354d42005ef7254d42005ec7254d4219dbc7650d42016bc7650d42014bc7650d42006bf6550d42006bd6550d4201dbf7350d4201f9f7350d420079f6350d42016be6350d42016bc6350d4219f9c6350d4219f9e5350d420079d5350d42007af7250d4204dbc7250d42007ac7250d4201ebf6250d4201faf6250d4219f9c3250d421f6be6150d421f6bc6150d4219f9f3150d424479d3150d42447af2150d42447ad2150d42005bf7050d4219f9f3050d42447b71050d4243cfe76949420267e65949420067d65949421a76f529494204fac4294942024ff765494201cfe76549421d4fd765494201cfc76549420067f65549420267c6554942005bf745494201dbc74549421d7ac4254942006bf6590942006bd6590942005bd739094204dbe729094204fae729094204ebf629094201faf629094204faf2190942437ad2190942005bd7090942
  | 25 => 0x8d521cedc6358d5247def7258d521cd7c7654d520167c7654d520147c7654d520067f6454d520257f7354d520275f7354d520075f6354d520167e6354d520167c6354d521cf5c6354d521cf5e4354d520076f7254d5204d7c7254d520076c7254d520267f6254d520276f6254d521cf5c3254d522067e6154d522067c6154d521cf5f3154d524775d3154d524776f2154d524776d2154d520057f7054d521cf5f3054d52477771054d52004ff7650d52004fe7650d52004fc7650d5201ebe6450d52006df6350d52016dc6350d520075d5350d52005ef7250d52005ec7250d520067f64949520057d739495204d7e729495204f6e729495204e7f62949520276f629495204f6f219495246f6d21949520057d709495246f77109495201cfe74d8152004fd74d815201cfc74d8152014fe73d8152004fd73d8152014fc73d81520ce7f53d81520067d53d8152004ff71d815200cfe71d8152004fd71d815200cfc71d81520cefa50d8152006f710d81521c5f67198152005f57198152006fb6098152005df73581521cddc73581521d5be7418152005bd74181521cdde7318152005dd73181521c5f67118152005f5711815202efa6018152006f960181521d4fd75d964204ebd74d9642014fe73d9642004fd73d964204cfc73d964204cfe72d964204eee72d964204cff71d964200cfe71d964204ef671d964200cf671d9642004fd71d964204ef571d9642004f571d964200cfc71d964204eef21d9642006ed21d964202cfe70d9642004fd70d9642006f710d9642024ff765964204e7c655964204e7f75596421d67f54596421d67d5459642004ff7359642014fe7359642014fc73596421be7f535964204cfe725964204cfc725964204e7e525964204e7c5259642004ff715964200cfe7159642004fd715964200cfc71596420067e51596421be7c5159642006ef2159642006ed2159642004ff705964202cfc70596421be7f5059642006f710596421bdbf7655242026bf7655242024bf765524201dbf755524201f3f7555242026be65552421bf3e65552420263e65552420073d6555242026bc65552421bf3f5355242005bf7255242007af7255242007ac725524201ebe625524201fae62552424673e52552424673c5255242007b7715524245fb4715524245ebf615524245ebd61552421bf3f515524245f3d515524245faf215524245fad21552421bf3f505524245fb71055242014ff7658e4204edc6358e42004ff7558e42024fe7558e42024fc7558e4216ebe5458e42006bd5458e421b6de4358e4216edd4358e4204cfe7258e4204cfc7258e4216ebf4258e4204ede3258e4204edc3258e42004ff7158e4200cfe7158e42004fd7158e4200cfc7158e42004ff7058e4202cfc7058e421b6df3058e42006f71058e42004ff7654e42004f
  | 26 => 0x4fd72d81433bebf42d8143004ff71d814300cfe71d8143004fd71d814300cfc71d81433befa40d814339efa30d8143006f710d81431f5f67198143005f57198143006fb6098143005ef7258143005ec72581431fd7e75181430057d7518143005ee7218143005ed72181431f5f67118143005f5711814302efa6018143006f9601814301cff765925204ebc64592521eebe54592521a6bd5459252004ff7359252014fe7359252014fc73592521eebf435925204cfe725925204cfc725925204ebe425925204ebc4259252004ff715925200cfe7159252004fd715925200cfc7159252006be41592521eebc4159252006ef2159252006ed2159252004ff705925202cfc70592521eebf4059252006f710592521ed7f765525201e7f765525201c7f76552520257f74552520273f745525201e7e64552521ef3e645525201e3e64552520073d645525201e7c64552521ef3f43552520057f72552520076f72552520076c72552520267e62552520276e62552524673c425525200777715525248f74715525248e7f615525248e7d61552521ef3f415525248f3d415525248f6f215525248f6d21552521ef3f405525248f771055252014ff7658e5204edc6358e52004ff7458e5201cfe7458e5201cfc7458e521767f5458e520067d5458e521e6de5358e52176dd5358e5204cfe7258e5204cfc7258e521767f5258e5204ede3258e5204edc3258e52004ff7158e5200cfe7158e52004fd7158e5200cfc7158e52004ff7058e5202cfc7058e521e6df3058e52006f71058e52004ff7650e52004fd7650e5204cfc7650e5201ebe6450e52006bd6450e520073d5450e52016dc6350e52005ef7250e5204dec7250e521ddf67198252005f5719825204efb609825202ef8609825204ef86058252004ff745825201cfe745825201cfc74582520967f54582520067d5458252004ff7358252014fe7358252014fc735825204cfc72582520967f5258252004ff715825200cfe7158252004fd715825200cfc7158252096fa505825204efb205825204ef82058252006f7105825201cfe76d91521d6be64d91521d6be54d91521bebd54d9152014fe73d9152004fd73d9152014fc73d91521be7f53d9152024fd72d91521be7c52d91521d6bf42d9152004ff71d915200cfe71d9152004fd71d915200cfc71d9152006ef21d9152006ed21d915202cfe70d9152004fd70d91521be7f50d9152006f710d91521d6bc6459152485ef7259152005f771591521c5f47159152014fe76d8d521cede63d8d5201cfe74d8d52004fd74d8d5201cfc74d8d521cede53d8d5218edd53d8d521cede43d8d52024fd72d8d521cedf32d8d52004ff71d8d5200cfe71d8d52004fd71d8d5200cfc71d8d5202cfe70d8d52004fd70d8d5218e7f50d8d521cedc30d8d52006f710d
  | 27 => 0xd53d954304cfe72d9543004fd72d95434bedc32d9543004ff71d954300cfe71d9543004fd71d954300cfc71d95434bedf31d9543006dd31d954302cfe70d9543004fd70d95434cebf40d95434bedf30d9543006f710d9543024ff76595431fe7c65595434b5bf74595434c5df7359543005f771595431f5f471595434bcff75595430067f75595434b4ff7459543006bf745954321cff7359543006df7359543004ff725954304cfc725954321edc3259543004ff7159543006f77159543004f7715954300cfe7159543004fd715954300cfc7159543006f4715954300cf4715954321edf3159543006dd3159543004ff705954302cfc70595431fe7f505954320ebf405954321edf3059543006f71059543015bc7655143026bc7655143014bc765514301dbf755514301f3f75551430073f6555143026be6555143026bc65551431ff3c65551430263c65551430079f7355143015be7355143015bc735514321f9c735514301ebf635514301f9f635514321f3f535514321f9e535514321f3d5355143005bf72551431ff3c525514321f9c3255143007b771551431f5be71551431f5bc71551434afb471551431f5b471551434aebf61551434aebd61551431ff3f51551434af3d515514321f9f31551434af9d3155143005bf70551431ff3f505514321f9f30551434afb7105514301ddc7654d43026dc7654d4301cdc7654d43015df7554d430175f7554d430075f6554d43026de6554d43026dc6554d431ff5c6554d430079f7454d4301dde7454d4301ddc7454d4320f9c7454d43016df6454d430179f6454d4320f5f5454d4320f9e5454d4320f5d5454d431ff9d5454d430071d5454d43005dc7254d431ff5f5254d4320f9f4254d434a5df7154d434a5dd7154d4349edf6154d4349edd6154d4349f5e5154d431ff5c5154d4349f9e4154d4320f9c4154d43005df7054d431ff5f5054d4320f9f4054d4349fd71054d43024fe75d8943004fd75d8943024fc75d8943014fd74d894301cfd73d894344edd73d894344eee42d8943416ee32d8943416dc32d8943004ff71d894300cfe71d8943004fd71d894300cfc71d894302cfe70d8943004fd70d894344ebf40d8943416df30d8943006f710d8943006ef6298943006ed6218943024fe7518943004fd751894304cfc7518943014fd741894304ebd7418943496be5418943006bd541894301cfd7318943406de5318943006dd531894304ebf421894304eee4218943496ed421894304eee3218943406ed321894304cff711894300cfe7118943004fd711894300cfc711894302cfe7018943004fd7018943006f7101894302cfe76d8143024fe75d8143004fd75d8143024fc75d8143014fd74d81433bebe54d8143006bd54d814301cfd73d814339ede53d8143006dd53d814304cfe72d8143
  | 28 => 0x815400cf471d81543f6fa50d81543cefa40d8154006f710d815415f3c5498154215f67198154005f57198154006f76198154006f46198154006fb60981541473c5458154005f77158154215f47158154006f76158154006f461581544f73c541815421dde7318154005dd7318154005ee7218154005ed7218154215f67118154005f57118154006f76118154006f4611815402efa6018154006f9601815401cfe76d915320ebe64d9153014fd75d915320ebe54d91534eebd54d9153024fd73d91534b6bf43d915304cfe72d9153004fd72d91534b6dc32d9153004ff71d915300cfe71d9153004fd71d915300cfc71d91534b6df31d9153006dd31d915302cfe70d9153004fd70d91534ee7f50d91534b6df30d9153006f710d915320ebc64591534e5df7359153005f77159153205f471591530157c765515301e7c76551530147c76551530257f74551530273f74551530073f645515301e7e645515301e7c645515320f3c645515301e3c64551530075f73551530157e73551530157c735515321f5c73551530267f63551530275f635515321f3f435515321f5e43551530057f725515320f3c425515321f5c32551530077771551532057e71551532057c71551534df7471551532057471551534de7f61551534de7d615515320f3f41551534df3d415515321f5f31551534df5d31551530057f705515320f3f405515321f5f30551534df771055153014fd75d895301cfe74d8953004fd74d895301cfc74d8953024fd73d895347edd73d895347eee52d895341eee32d895341edc32d8953004ff71d895300cfe71d8953004fd71d895300cfc71d895302cfe70d8953004fd70d895347e7f50d895341edf30d8953006f710d8953006ef6298953006ed6218953014fd751895304e7d751895301cfe7418953004fd741895304cfc74189534d67f54189530067d5418953024fd731895340ede431895304e7f521895304eee52189534d6ed521895304eee321895340eed321895304cff711895300cfe7118953004fd711895300cfc711895302cfe7018953004fd7018953006f7101895302cfe76d8153014fd75d815301cfe74d8153004fd74d815301cfc74d81533e67f54d81530067d54d8153024fd73d81533a6de43d815304cfe72d8153004fd72d81533e67f52d8153004ff71d815300cfe71d8153004fd71d815300cfc71d81533e6fa50d81533a6fa30d8153006f710d8153205f67198153005f57198153006fb6098153005ef7258153005ec725815320dbe7418153005bd7418153005ee7218153005ed7218153205f67118153005f5711815302efa6018153006f96018153024fe76d95431fe7e65d954321cfd75d9543014ff74d9543014fd74d95434ce7f54d95434ce7d54d954301cff73d954301cfd73d95434be7f53d95434be7
  | 29 => 0xcfe71d8d54004fd71d8d5400cfc71d8d5402cfe70d8d54004fd70d8d544e67f50d8d544c6bf40d8d54006f710d8d5420f3c5458d5421edc6358d54005f77158d54215f47158d54006f46158d544573c54d895421dde73d8954005dd73d8954006f461d895401cfd75d89544567d75d8954024fd74d8954486bd74d8954014fe73d8954006de73d8954014de73d8954004fd73d8954006dd73d8954004dd73d8954014fc73d89544867f53d8954456bf43d8954486ee52d89544867c52d8954456ee42d8954456bc42d8954004ff71d895400cfe71d8954004fd71d895400cfc71d895402cfe70d8954004fd70d89544867f50d8954456bf40d8954006f710d89541ef3c5498954006ef6298954215f67198954005f57198954006f461989541d73c5458954005f77158954215f47158954006f4615895443f3c5418954006ed6218954006f4611895401cfd7518954024fd7418954014fe7318954004fd731895404cfc731895404eee521895450eed521895404eee421895443eed421895404cff711895400cfe7118954004fd711895400cfc711895402cfe7018954004fd7018954006f71018954215f676d8554216f676d855400cf676d85544ff7775d85542177475d8554507b774d8554217b474d8554507b754d85544ff7654d85544ff7454d85544ffb454d85544ff3454d8554006f763d8554006f663d8554006f563d8554006f463d85545077753d85544ffb743d8554006f762d8554006f662d8554006f562d8554006f462d85545077452d85544ffb442d8554005f570d85545077750d85544ffb740d85544fef775d8554216f675d8554216f575d8554216f475d85544fef774d8554216f674d8554216f574d8554216f474d85544fef754d85544fef654d8554216f554d85544fef454d8554006f773d8554006f673d8554006f573d8554006f473d8554506f753d8554506f653d8554506f553d8554506f453d85544fef743d85544fef643d85544fef543d85544fef443d8554006f772d8554006f672d8554006f572d8554006f472d8554506f752d8554506f652d8554506f552d8554506f452d85544fef742d85544fef642d85544fef542d85544fef442d8554006f732d8554006f432d8554006f770d8554006f670d8554006f570d8554004f570d8554006f470d8554506f750d8554506f650d8554506f550d8554506f450d85544fef740d85544fef640d85544fef540d85544fef440d8554006f730d8554006f430d855402cfe76d81543cf3c54d8154215f471d8154006f761d8154006f461d815401cfd75d8154024fd74d8154014fe73d8154004fd73d8154014fc73d81543f67f53d81543cebf43d815404cfe72d8154004fd72d8154004ff71d8154006f771d815400cfe71d8154004fd71d815400cfc71d8154006f471d
  | 30 => 0x13002801c00e000001001c008000009800000a01f000807c00e0490008034010041004001403600100580880100020000008010003000001400000300180080040000198000024004001000c03600500100a405401e001801c00e00000c800000000000280080020000020040006004005001c006004018800000e005000800401a00002300100080060080030002000024800c018005006800401c0020000040018000001000800200300b000c00e0000000028000000000000c000001003000c002003005803000203b0000018008021019800c002000007800400801200a0000004022001004c00000a00080000240100040000008000004800400a001012800400001100e8010006013002002c00000f002801807c00000d8008004002001807403000201000080000080028040002011007800000000100d0000006001002000000601e002000401400b00e8004030001009000004c016005803c016000002000400000a003000001000b006000402c00e000000c000000002000401800300800140220030010000006006000005000e001026002c008001000001000c00400180480760070000000020000002806c03e00301e80980040030018054000000004802c000006000800800000d000003000400400f001c002011001000c00c00e00500000080210000054010004006001400000201b0004002005003004c00e012008000000000200f000000401400e8050004004001800805a001006001003200e000003c01c00301380440120000008004000008001000800e00c0000054002005000809407400000200080060000168000016061000002c00800000000300000070018054002000001806c00400200501ac00e000000812c0160000130000008000007007c00e00100b8038004000004800000e0080048018000009000806400a003008000000800a000000000400901800000160000000000004005006800002400500f802c00000d008000c02000b00b00b801c00a00b000c002000000800000000000a003801a00000c800000a0100000010000006006800c000001000004800800b002000404200000080000140030008000002001000806c00c01b004800800401a0038000002000005001403200000281100000010000000000000000000400000400480180000130008170002002009805800000300c800800a000000800400e000002000000600b0008004000006001001804600a000002802a0000008008000003000000402400d000005400201600300f801202500000100020000100000000003000000401801b001002800600c014fe76d8d544c73c54d8d5421ede63d8d54006f461d8d5401cfd75d8d54024fd74d8d5421ede53d8d5421ede43d8d5404cfe72d8d54004fd72d8d54004ff71d8d54
  | 31 => 0x800400a020000001001a000000000000602f0018108016006000800000e002009801802202b001006c012000003802c00800f002000002801700080380260250000000000002001003401e0280028020074012000802400000200000cc0000010040068000018000001c03c01e00c80080060020010008002000008800402200300980100000040000008008010004000003000300c8010068006001001c00000000f804402e004000003000200100000000040000000004004007003809000200e000005c016006000802800e006014001400e006000800000c054013001801000501b001001200000180440080180020020008006009807800c00000d000c00000000a80780180100000064002002000001000e0000038000002019000800000600000800000040080048020044012002001003c000000800c0120080038000000000001800000c000002812c008001001000c040003002808403001200080ac00000f005012c000016002804800000700c003400a00000000b400200101a801400600a0000000000029013800003200000a000400e0020000034006011000001001a002001000802600100500a0002010005000800c000000806c00e003000000400c007000013c0040000008000016015001002c00800100280e400000200600040020130018008002000000802403e00f005000000002700e802000401f0000008004000009802401800200500100040000020070000000019808c02c001001000c00c001000801c022004004000003601800000000120010028008054002000001000a014000000000c00000200000000000000078008008000801801203c00100240020050070008008029017800401e00c0000000000000000000800e034001001401c007009801800e0030018068014000001001401a0010010048002034004003800a000000000004e004000000004c00e0018034034000004000800a00200080f40380000000000058003000000000000d003801c00c01e0008030012013000808c02e000008810401601200300b400e01400500240100080038088014000007000002a006005800405600400e0088004000000000001a01000000f8000004001000000a00300000080000300020104008001017801000400700000a401a005012800001200500080900000080008040006000002003c002000000002c034020001800002a027001800000000000a0004010047000000002a00001000e4002000001801c022001004800003a00000000000080210030000002008003000c002001000000001200f001002406e0000070060000000000000c0020030000000000013000000004c003000002c00a01000880000000000010000000002000001402e00b00100280020020040008000005000800801200200000000
  | 32 => 0x18c000000000012a8000218e2e61c8a5ed0d921f8a788000146444100000001f5e00000009d41f7e000066c39a80000000000968800000006b68d2800060491ba15a950c0001f0c000000098080007d0937a18985be71114f00039d4298e909616a8a8412024b2000109a00000000000000469147847d89ac7378a8e000051615f08d88ba10241c7800000021f07480c8e9d2120c1b40b8404782dc31e9e202920dd400024d049b9ac838196f24cf099a0001fb23049b9a64e804083c12fc000105c0001bd60001c9c41392ba88e226c2b6a6300000be014206fa9e495e01aca38e0638000009001000c004003000000003400000c800400c00a00f000c000000000801c008005001000000e002001806400000d000000c000001000000c03e0070158048002000000000000200000d001800200300680080000340010000004001002007400402b008000000e001001003003001200180cc01e005002801c00803f00b00100020170010024002000003800803200300180540000010030058026000005807400400000100000000130010014086030000001c004009004000c00c001000001801800b0018004008003002000c11c001000002800a0000018000008003018002402400b000800001e0160108008010000001001800600b002800400000001c0030000027002000000000000100b001e003000000400a000000000400600300d800000400100000380000010008008000001003000004801f000001001800f0098010002007000801400e00d00000100100000018028068003000000801a005000804002a000000000c01a000000000405201800b00d404c00c000800800000000d8000006008004801005201301c000c00000300100140000040060000006001007002800200000000040000000048004016000000014001c064001000000000b00d001c00600f003800000e0010008004000002000003c00e00b000800000c0020000000002000006007c00400000100440480040040018000009004005c00400c0000000004029004006400000e0088044000006003006c02605800200080000010000004000001000800000200102c800800c001004000c008000000001404a0030150018062006000803804a00300000000000020080024002000018000000400900100dc008000000807c03406d001001000002500f801401a007000005c00a0010100008038002000000000400000200100220350010000002000003807000000700d801003000c000000000a0000038000000002001003001200100c006c0540020000004000004006000800000000000180040270000068008000004803801c00202b0024012002001006801e0040028044024002004805800001500680200040030060004002008001800c004004003000000400a0
  | 33 => 0x37e8000000000091121262d41b164f7000000000000000cba90e09c8232145e00000000db0b406430000134a52e5be8000908126665da31488a0ba80001ba800002f44fa8e6458984347f8800000022fe9af88c622291e065e8d98000000000000007a4887a5f580003c3955085603f000014ee0001f6024f921e40e17843f99f929a21d7a6ab0000199000000013a295f20306e282be4a495f60000bb200d07d68e4040068a94e43a3200416821220b20cfe0159d6c26104d8060149496116361c519163dd881a14ea3183718258348a0de5691dda27f92d4000210e1ba0f6a9d3042a2440b3037c171c94b273039181344011bbc71500001a3000000000003020000225825238f9b26793031a45e0bec000000000003f800000008f011662c4114e00015b026f800068190e82eb00000781f44000254883d80009c58000a00824200025fe000000000000007c7a1c21951ca05fb238c1a487a60c52550254890a102897c107911040aa6780f9a5743e517b05699ea471307b807715561b8854a82098d801e000000005fa00005ec2d68000000205c8ca8fa47ad85fe3bea4283ce20d28f980aa1da221e45b052e25e13660001dd6780800029c039a2540e2e056976c6d3a3402e786862571c165438e34238209a9d48b8e6c083be50f84086a593d653a8b4e1a6a07e9e980004ed1e3a2b90f4a000245030d85c468406f00b30000561130e7f10a1a0001aae4900eb400012c2000000053980000001b469fd00007c28eba000000073f845a00014b87120aec0000000580172c9508eee68881145df8b2476d90e483817e84038ab286902fa6caa79685c85ee5581f660789c7059e9cb80d9896c1f20c326091d5c00020c01889f9e9050ab643600007248c886ba0318000264664522d63b2a47000018dc766800004202060d880001a412a0446000007a185a9da000013d08628e5800079d00001cc1e3c000269842f0b080000000681078400001fc07686de7c10c5a00000000000cb4000067209a00008d18000013881e000066e0000000000000097426d84e600002ed80007549a92000148c92480004ad19c63700be6172800072b09127c61a2800012e005f8000834235c0000d8600023aa8c721dc654871c6fe1760121963c970823c0000a80214898a51aa6441de03aa2b484529f324c675d0aa671aa74e660a0787ef977a8c996828aa09140001e8a9ac954006c81b668098be6a79e6c230800061fa466504821475c80004518e1e92f19945110cac7e00dde0000fec97ba5720000f221af9bbe2901ba0442a218295a2ba363173046a139e00da6044d782e23c29a6c02f0a548a2225882503102eb938408d24ea0dba25e45d820c2f4a69e7af27b81ca800038f18869d51e8c78e173a9148c3400004a40000c5422780002c096ec00002207bb9
  | 34 => 0xa7208ad800005e26e69939ddc00017020000736557202e4559b1a89a8000029800000001960000000921976867109820001d6a70b0b7c0ad80006460d3697999cc206060a9668f9e0000750334854401d1a78194920483680000ff26a8687a418447195e9d626ec0590d9635c87240a080b800022e64b485ae89e245e1e5800093390fe4ba9ffa3e41bac7610c6e1db9b8e00007746e624f86e0060203800007c9210a548930400014626d980005bc11245ec9a2e2a0a2f233a181c2ce99c041f9426293101220398f4623836a6f18aac000161a000068e6e216a0006a09200017082bda4248a096dc3ef9fc24e9006a4320000520981a4e5800024680005e4978a63793820799f4a915246c7558dec2659cf8177038c205838209122fc516a55e66b84ae0001d3a6fa80005419af8248003e30824ee49c847889024b414e000086a800000011080001262000182a08d87424bb26de0af000025c9fe476e9f140001acc28980f800000004a691ea00000006e0a558701a65a0001bf0000272400000002b8a08652f8b1c5e0929815c002828084ca000000041e85400000276000246a00000000b400000001f706da800000000004d4886431d8514186813020880000000832369920832a83fa2dc0bc46b780001b50bc6951800000025b48e2122e8a1047696e80008af8000107000082f97d28e8227a7a987ea94d813a14c875491681ea3830de404600003c40c5c13e8e4a1a800004ec05fc3870f5854d800000000009f6066685000000000f1c941019a00013021d4a48842a88c49d8061c61c21a8503a77e1b21ba66f08fea775208e526046200000001a6073c67690a25c924724c187f2093a7a27b708007902656893231a47906201280bba9d0139c85221a044996ea66627320000fe29c380004220a1c36918600de9a9834d23a2385053e54b957c4b99ce6000001e2bba2b839e07724cb98b638a238486c0a0c5ada0ca2e8800027b000079510ea8a2991c6279fb609220cc0000b66071072219f8b328190ed889c0000396a40a15b134c2879cc2178153c8ba8766944a5da8ed9a6600000008969aea29f1e1e0000000901a5100000e20000034820a206c0000936000085c69c905e88c00002d5166e29f8000700045c309a0020001d3e7ea00007541fee7e390ee000186881d11cc0000126000196878023b4000000005780008fd927839600001f400008b00d900000de02b580001fb000086c8bd61278d0a662185c84700007fc8c048d0943c80b02283a203a218c0b3e8319a567b18f424fc26869b712fe78ba53a7eb1a0e2ff9c4e5a607f635109dc94a9eb27af9baa633a21085c1c9484503126e191b416e26a07c8824c35311ca33f265e017a7d298483da0a9a63e79e04b48f90a666198df80a8030665708ea59785da353a4121bb2044
  | 35 => 0x24ad80003f280ea000214a00012bc48a212000022265ee0eec2c51a80343954a0000f74827039e46625a423e8000594840c0000ca0000000015d0aa40041d5414d8f5e75602903fc26740000000000000000000008e7194a08b838a0091f208cda2a2840a73c40722d08491f2698c95e84d280004a500007e623949d58642826152c2d12268732091c07b05f655385f84d5253e00009229b59288973115a31089007f403ee4459b5e22e183e5c303e44cc000099492489b41b52986a72e57a902c39c000000024943688e123639aca5f78166612016a6fc8f249dc000030182b437c8000400855493c800035a10703ef15f464b8000650208c66321e80001c9e0000e7a000000065081567401e7600000008d617489a40b5661f0ce400003342b71c7c9d180007349c8c54918a47970bca488a37002ca32c32da25400018640001276000232428107d818116c29b3971601a172a21000003c2000080618ec1eb000073d000074b800055e80000001aa600009ea0000fa600000000001bfc00000000000000378a090000236e0000ca2226942c128852c32c909257291f8513a1085182054000000000000000ea1bd40000000000079200024c458c00009a480000e980000e7129021d800069f9e08000031c66c1d22590a54c4629030a0022f09421054529215286106564cfa12c31915be10e116442426fc95681280b3907209903ec0350c461f6a1d290d93a89638578054168c4980d1a61c8c301fc1ed0291922a370932288201bc4cc827a8e1963846380006698b485a1814604b8420223a44a000000000000ee67a224466a0c2c78fa51e00017000000000012a3fe00008944f30100152030a53880001740886112a01e000000022f00008dd85a600011961419c363f00756341a65c78a800096a95f2159a23c71805b48d513c40cf192463580003470b58000000039d2446857048a6c6145c7ec1cc69e01404000092400005901011e184d394723cc106e0001df24e31a5868c8de65c180004c21d8200022c200b02e89f1261c1ea071a44f813e0d500002421d1a00002fe228a03400025c40239a903ac8000677116800000006979c5c1db002e1b70e5452aa7c60fc992c256150a56c83c21ea88de90892366b481ae1e60a5c5830f505d4161e0c901b436d25940001566000000019d8ffa19a86182a41370020a57e75c18a26b606a23db009444c87b479e80c4202014267514bc76d15c446c1d0a676079e00000e865b962c18207107ed258c6cb9e5a00000005b7a16a106000041a89707451aba6611fbc8a6807c98e000060122cc00022f43b180002f8800020f00005d288360001b5444a039456d1de851d26c8205008c0000e1600009b400f2462000093476c25a64d199489a3a5265838db00e604942240c0c7a5073800000009659f581b2
  | 36 => 0x30e440d800007ab201c21d0376144a12839701540bc883a54d0bee05f17ac9fe13689861f6a6d58fb0a0290805a99fa44f48986000260a3e61b287aa9a6e67e00000001f168c31c7684d8c3c3d3000085b000000011725ff035012e16bc62700008fa1cba00980001b803c057f266c0000c808e785828eb9be42b80e0a462243a3db826e9940d8061d905a3710ad43a7a24868215b69bc8176415901470f9be899c96c67e416ba8ac80003cb9cc02c4a15a96180009a29ff47cd8a0051f1fe600000009369282080a33e3f100008d400000001174275800059a12f00001df691e800000017620000000000213861e9d660000cc222203b2410060025fa1fa6f3000059a973e50892cc595949a00026e8718a4c80000bc84c01bb4034000080c9abe56e0000000019e35c0a4a00012380001e6e2a5093c00000005ee9a3816d82d47ac20082040d7a3c981a411c163a2ee0b7200004ee00023cc00005d696800009b00bdc03e8000000214c1069ac4774098826a94dc00008d60001dfe24780000001f3e4e38ab40001b4a71f9e342e696e89278ffe0e8179875f80003d80000000000060280003e0211e0aa80b0112192295c0ee45b40cbe7b09d4839415d410f934484e8d32881805a013017a000236a69f14a654118401e7280c9dd07445b621ee77000a43869ce2631115c534a0f801993e832092587e5000028b9ae67729f0000000000000e9a000044e5aa00008d78000000184213c248042a00000001fe006189066850fce000106679781e47118000000120626da75c64991203741fe835e162419e8712000204a668800009b0afa1100fe48ef15fa3af03ea312256664d16f440f926c00010369a997aa000261029920d400009fc17a07022911ca46880fc602e9c3c000122c11d153084f0000709800064292c600000004c705042fe9b5c00011be505000044f000093b26da8aa83c467a82ac1d29a3e97aa1169a6a33a86e11a64211a4c999199c41809683431ee23ea0a6a4fe07a08389d629a080004ee0000787162e0001afe79800000000bd4904000004813f49cd914044880004ae14ae0000f527ea93d028a000041480005f412ce3b319ec19883b48599f641818250759164a82a9634000110e5378838000161098906f699ea26620fa76600000008142552000159e5451f8415180005b022361b6902203d9aa47b28a9822b203a90000005761c8e95e00009caa5dc0cd9770000254e9ab15da31899b255c135a3a00d3055f91d839c83b64cb021c7100b6420a8ce29330f0c41316b472619b8573058c7e6a7ec1e091803b11a3c0ac968e62b17268f791d019a247e11b84447498d5655c9bee0b90f7a96f142a86f210008e8b3c9e522620001b0458096043da144890097c60000a7800004aa15419ca7c6800009d1c740001654000158
  | 37 => 0x575a0566c380002530ce016692e25819b3650609765af90fc11f80006b0808400027ba4779a5048d276276c9cea75d88ba5fba6169f510cc5d380009f20000895825a4c90f360a196c448c983692f9360305016e777979c773a75e5009e9a855800021300000981cee3fb800087f84e82d8230a80498ba5da81380a100c80b997be00015ce1c323f2000143868b213e7ee9b344fd975e28280580001b48000000000000008a511aa18f000030690ce0001b6e00010fa0001ae05aa9086000000011c90c20001d68516239a000021e31c00004b615d000023be67216fe41b0db82ae8c7843ca4a04fc857e86423ba7f59b7a2cd27044f6a5e27200000000000030b96e46fb1e4a8590000000074e4992362000123a00022c84060d7c65119923ce994e07280fc47c110021619001c1119c3b98b7674f06c61018abc064007202200005669b787cca51c0ae26d46dc0e6643c01de0bba2924d2167814307a29748a866e486e6995029e000038692080ec53d81744520d0228593b622da02285e83701fb9b4443703cc5be0930000220c34e81126aa22b02ef20fa28515686080fe00001e701ee9bb842303741c99c0e117828c0f4155840f1f303c61964229a4d869d80001af000066f848c0629c1e2bd0a3611e892e1f9800029b171200026145b3a2d845800008c080000001ff63898a6208024264978e849bfa03e3c18c3897d0000967957476b010e678800000019360001e14000000014a12502f91a4e000087c000000094815a8634000093f859c8c000000001b7e00021ba2179e9048980ae6b18000017205e000000000014700001d1c5f88ec047b93fe40b83ba9ad0e0854c8ffc692887e2ec12ca23d96722c1271e5318bf216195783768a300df86386b596e052d01044511502560093a5f90c405498c5e48f8d603e4800036f16d247ca29876f927460210c693e881c40c8a5a9b915e43cc98a0000255c28920ec0000edc6ce97dc903800000000002c8178636e8804359a36c18e80000fa00000b58d5867785762e1800056195985de032603f9b6041d9a126a2077a33d800033003680aea0a661d08be8539ba490b8000000075e690117e00008ce000000066380004380afc48523ac00018f2000034a6b012f20cb0000000280407d000000000000000eda990800001900009a700000001bf400000000001dfc778800000011029988000000219c3c596a23728c9a733000081a840e43e1628536a4aa08aa0a42a800000011ef8348095e9c6055e55a8e6c9e6800023b000083b98b896f800087c800057e09ca0bda4c22de24ca00012d0000233277804328fba7ce0000a4e0561b6c00000000001f3a4bd0fb84f2031e0e49e4e3f080dc21680004be1e6a9be84d48d100007a71f72a0180003a09640314a19e0000a3a040953a000064c2f
  | 38 => 0x7c48a58d741be141e04aa7e23b08b0c979262a76f1bda00000008a716da00022140001b069b1800064694b646e256000000007aa0d5400591c001491a0000177467488ca91300009271fae00023d20001ad49558da034205847a5814a8df9b840001cfc5040542844000088c8b5e000092c039000085a00004f01d1881091c201b859836126803df9d907129cda61180006800d04717a7262ca25ce427142e7f31b7c23fa72270e141c3a3a6b02df99586bc8c747391d5e21811943290b067310b5c350a27608e243e00013e03891fd499a800067c256c8b5205857b009c00018fc3591e881788c9c240922480e09a00860d3c000274471e219419205cc98d935012d99fe5d9152a612a28047896cc86b81aa94c00009ce12e8626856293987d416f11fe863201400004be7c0a6705db996a0f60bd08a78cf027795548da22c47df25de220086c3948000279169a419094a5f000c623897a27b98f844e9980e5cc99a028f08c092e80001d921b6314232800000003be25f2104089c52380000888a7648480000000490000074685d80000ca84e00000c6c1ec0552000094454799fa0000048331055821c91d6239895400017e0000115e39a00004020cdc79f00009c00ed482b1ed897c18c6785928e5c69d080001fea813072e000144007d8f5a42f808a49f9e0a7431d860001d4474d800048410a0000166405b1d8c05a180c9bd212e00e134006496329fd94005222588644170e2a6820e5689318659893268e837222b8cc84c6988800c0188988843a1050ff40001b2400021fc234027c67981d28af1db834a219800088480898eaa000018c00017d885194f40000000485899c917277c4a122206c727ea620161435a9486372002a5eb87f400000004e180001aa24d262a84ac6bb832e4868f342751f888ad222a0001c4296b00a00118000000094e21a80000000cfa97e89b2000000000013de0000b6c78c0b2e3ca1b401590f042700ee279c86940001e101210208905a0703a4117a89f80008870bf64908ed22711f287ee1dc623f14b26d9000096414cc91213fa3e711c42bc079a7e180da25018e047194542738a9e26a221614c278c59f800000016967b520a200000220000b8227e800038b2160274a7e82cd8c189c0810a9241cb244da10678104f24c980000001c029ff1518082936a6ad8bea9eb096600001be2e8000c7c21bba9db13423079a705471f2e99203084d88d9436b00007d409bc89b9ede79215dc93804a600000007c19e7e9f811fa8cb87c249e87205ac969e02b0cf457fa5b07b491ec5b8982c8f2186201b1538606001828e1fd819806362e98d827d511e65058ac6164a7aa630912a0001b9c1a107622b311b20001dee1fe938824a857200018000000db270803f495a800000000000001f481650d129b2a29026500
  | 39 => 0x940869684000000000000007ae067c08c00000001dec29400000001f4645600006051d2a3c5000048080001ff81823338466781a1ac036024655d9d0e1df16a4000000052c000000017807b81878689244e53fa5447d31a944f620725ff80001ff00005c5059632c21e038e800073c18b07bf9f9654595e613b000042913ee0001abc8e488ee2caa0f29be00003e3997266d17f63cf94fc59998ee82004c804b1a307ae975400189e045f1b0a31a26689e8075c126956456b92802799dc400500442a8928668319706231c2400018fe4298ece38e27c25211b0c7d68eea0f50cf27a6266e8940124000000000000005708e367cb26f023a1d2826c1bb69258cbc34597ca42d22a480983780671da238c82ae76900000cc19d60f18000000080c197916a7190e10000000083f9e841a2800000000000000c0e8d5835a0730f2c32290ec60d000054403880001b3895e85b000008f043d136c000070e00023e2941800000013e444b055c00000008eca1e650926b80a909c26c812ac0000cda18a14565ef17944dd183c4479ae28f3a3c405300002d2896470d23482bfa0068990e425918fcc70222ce63209040001c2234900006a100005bf0d2a7b58dea3c81fec5920000524224a76b850200000006e78740000000053a23ec50198981f818bc46400001858a8c3ee8000000000039f17667d8855645b9a7a00026ba5a708a078d889296d9e2c88921ce66e8b9098183bc6f38c009291caa2bc9e6287a82b0116210c6c220b21a98ac25a2926851294e01e220003a4963e90106d89af11f41058e7637da41e1baa1d852e8f6684c0f8a1c611ce70422de96480000001ca274900005f094ec068246e000097a0000c960fd959c00000001a200002ba1cce15380005fa9ffe89482de4ac000000010d42c8812226e970a0000e30673800000001ac411000092280de94d000000008f26a080000000f6405005d40c01bb26098240236a73a00000009fc82ca367800059109e87bc81847ce125c74e24f607b87bc5989d3400000004cd1738000025e98790b034006100241a86788940a000000060c0fae0001a2624300007418000000084a00000004079e68000000000000008b49cd8190102056a99ac9ab83d639591da96010da35fa7f029a061207206a404190b25d1a4a6403000000007e46bf27a40000f78315a20e1f0104869824de9ff800000018ca72596701b4904a000262022d25b202680008b708266418db684aa67c1300f1a00000003a29f5200010ba138a0360000f1e2d480000289fc898d278a753a25c0001aa2952a35291e1e8e5cf15ac000183a29e8000130954c0000dce34b15e20701f4e97215a01340d5c74424f089819124e414ca31813107a88ed6514000028ca15e5659f3c098886827e0fe803c9184875137c1c0000084695120
  | 40 => 0x1b903089ad06f70abe6c000003a99162008025c460a0c82f600000950d140000000000000050300004b900006208e60000083497023fa46b0e48741237c640a4a808110ca0002372803179a31293ec7d580002690bce766166c806a3108621f8a04402fc269933a1318f547c393ce5cb9e807299336423a78e3ea877e4748f0085f0b9c3b788f486fa4ae4418b4c5e2062a5628c7e84d013c9230e2225209ae62d0d5a0469a0a24a0efe962800019c217e0b11fc08c120286f023d665315de95da6e02f0a28e13f944672c1cd6877a6586150096185271c63e927c975a5ca7341eea54028145620a889de80000f8082442d837c1ad00001910aae313213294516b8000096291d800044c00000000e9644e8ad08f6a05a67b9a625b99d8e073a09e70c2784327960a2c787ce4c30f5661588503dc97343f78fdc15805a49bb80e213da16e29782ea179a21290c09c63f501c242289167caa7e63f6977c66f0346288800820c00ce54f8c444a88f125e8017014d1c662b01bf666417cc06a02f02e9065a5bb91e8054a37482d89e206e00009cf8e0414a9d782460cd80000b421f797a412f14360001daa1491cae9ed810c714984c9cd22ec814a7ca6cb24e4850862c942a22e5569544557835816c8e18058172205110748f70a588728b0a7868280572054c82e898072d11526d600002370f623988bf44b122ee2ba90d600017a800004f872099280001bd854699a43250ddc6ae099e0001f74000256e8358ea0004800083d14d0597196c9ea18e468d000000000003bc10de357a18a19400000000734639a4e265181a67f70d3828d1b424ce27989e7057a62b8cca10d9a6400001d600015ba000026692c00d6000000088b05c620088cc000000000014965131f829d0800035480005e5800096a27766bb07d2147800053e8d267601af403d1e0c000228c6f409429e40e02916243c3dc0d1062c829802603284d5846897506ba7500fd01b01c7284124fc07403b833423668d80dfe0e427b2466a6b64a311c800003b043424ac8510a2c00017720001ca8861a4845311b5a1d822426540b466862564a0411506ff9c2e00011380001c0c00024dc0001562084879000019305d6061e1191a529c6800005c901073c8fa2282051017480001108fb6323000056426260bb0000000069e000156c0000fa07949d1600023ea0001e9e9b8851c0000000018069c00014803ab06fe37a1d0211187b630f992a8ff124a8fe23304dca3824f2962241096164eea59c56f038046f063e2b39fa642b93209cb046c3afa0c432183dc83a9d4697a06cc3a61cca020050a50e85a29f681b03261b6277093aa8fc1852617853c0a6a2724e48b8043d978c8080ac41aa852607509563f20f4e18d0d6e77208e498a00004c293be50c8fb49dc9c7a085a1d04ab80007371
  | 41 => 0x7e0000765000002d011c37d1c32564800005727e40aa1a466f48d760001a1c3589a9a2840f880000dd60d700008f291b6976000030e954282104ce4b002da000021000025f83aba0a87e814206a3999e5749ef08229c6806e9a6888f97f84828b1861116ac52814d81330da89460ea227616c850212d632a0c665940ca6204979082584b05b584601d20cee20b02d89f5800016a1a5c87d10b802d98a697d9884000159445c007a000067870a80006bea40891f000060a00008e000004d604fc2dd20b8115800034b96f64be86b08f524402ea94c081f1a746e5271259600f0427974495a1c6c1f31da09e19e243f5a7dc65d14a20278f029c30938137800094f1eb4438800082d0c1646899aa00013281130ade6908270273029400023783f61154943898c35227281ce880649195465c11e6473a17c86dca196790986c7ff00000001a487e300000001c3a000149e98f00009501b308d3058a87003ce93d003a64120c20b48cec519a5381d69ec4362988a6c5000094900005e79ec081199b60001fc67fe1fde00007ca000129e7620f3c0001b226a31a5a177800a7fc09f43240e5e6f817ce00021780000e4c6b68b009351c869180f406559d9c4a2a80801c1e446910ef48bd90c472222009718a968cf13141cca02454a16885c78854714193840a09f276797200c38f5c2ef8b6a87d849c3090c7c81213b23d1925a4b2000000000000001b3c07e900a86680000e5924e17a86ac1e2a322000270810a000067f0f8c00000000001b7461b942816000000000aca00017d464f04ba0000000000000000000005939f5c63a05c82ce13d48a197180000dee98ba60000000005719d924019e1283a09b87798cf85a48aa83e1870a52482c63e580cc43004d64caa7d099fa1c43bf27de2028a0686d0e9c36b849890a94f230a0ab07de0a7290b149c40e83fe65f8000350027e7c70000268a11246b800070600001089ea04431c148be17101da94308b9123c94094ac1310000000270a00010500000cb816e86962b20be836698104c480004c5a15098b1a3697f07be0000ec844698581249e826388cd625d27ee000000000000000000e869ba8fac51a0402765865c7db1bb07bb16807b3175688e83564161ae463e1ec8530886676a0b261cf886e1839b3e2110d9c62a24326582068915842458a859e6e3038e21c22ae81e89466d3198a0eb858e73e93766c427066551f76176165a506937e2ff19d00301dd28c78ee89ef95ee0000cea11403ac208090e3bd9ee42d8956e3b40a6e72f1ef698227c01390ae64099c562be0bda1ae1e261e912f671600a880290d26708ab872fa4a20ce26d263009902290000818a6602fc279e7e8850e65685f2264967483725ec2119b12876a1c665f193e69511fc5d08eb8380078600004960e1233459d855a
  | 42 => 0x810983a431c9c1c878a06e77c0daa0b080000000fb2196185000000000001be200024985d4a3f42f79896955004209280e69b0a676514a1a230a937894c87f8034a20a2661c0a4eb8a746ac924c41f00009c5146c9780c1000019803d11d2c9070c1c9b116127da22e0122138a0000bb4000050034604820c11d4c99990e63939e2827c19860d11a8a7b69be608b047c31392be81003209eba1f800000be1480000183268491906d6836095a63513ac47524d6643a06000002882cb19f40219c6e74c043091081f277e00ca6f210686b38c849609c1a5d31e3249a83406f1191e09e233864219e03fc87b28b192de7699d1e1f70e2a82f01629d290825a422ac9830f482f018f04e5177670a074c75f0e9473d82e03e08ea848618da92e17fa4838d3e488068277e8b9477d17f43ad800000004540a2925410b856882804ea6008dfc0001816000000083985ce08c83d28810c0a0f7a6f6548131e00017400650a0e4bb89da4e000004001f1017d12aa418912e411950835b1d123a913bc0d913fc6a707286fe98320001e669a3056e8c8000081985c275b90ac762982e4d91660930276a263a76e926a4b69ef0706477264c0a591120001d6000006ce8a98a181f1884252282c025ba3a83e6a80e4f1984e69a98908e9914a893805488884124f8a40c80f20e472d95c080385182e223d850d22e21e31de41c2000063323e08ee0ef27bf033e0001adc74c8d1e48024682fe22462e284e6000264a73b164c5f687580000b681e01ee8000000082b9192000046a27d8a2a9ec0f2a8b683ca9aa80006cc84a8193918600018f67f499e461a99328d3a4e8906a3a460e27fa72400007f680003518aaa6e586800cea1926589b5007c2180000227c0688000756800067c8a6096b8a1248c00003b8019877a901a383800000ca5b85638c589de15525e998069a880007731dd83f4835283f0ff841e0a529239aaa10b2474946862e00003e25358a3e68592da36f9f3422a9af012c80000c5a37a7528000179035e4f9939a030a1e42b623648be9f124948b0e22c1c9a1e50b9240d064a02485f08f4147624981168c39ba2445158c5ab947a4959b1e6dd8a922209f7a00001d80000a202de8a4233523b07ab9e4619192a464821c885d23989901c04796023e5a504dc1bf11340d319f658812dc426005031aa30863a88b25d7001c36217361b101fe96600001bb90162db82f88f1800000025280001c841621ece704800000006f47db800094892a65d6a50082c0000000129c8d6800021580007f2882e6250eb04d71af65320cc61e3a1182a700007d000009d68d4a52a013287580000000000000000000000006ac000000001c637488986658000000000004d800000000000001892234834e0001bae09a9bde4a5a07627ba764000030200016081eb96ca354
  | 43 => 0x13a05b527b40a8a1828a803220000716213877010f029c78388840001bca000052232b8000258077681380000000000000014e00003c839f972800000009a500004f08000000147e453251679580006668b168c5a2027f3822400012b20000000000000021e223437306e453e1618274000022a20165f9825663485ac0000ce6018967c6da06ae822178e53517b61fa221a6a821a657c202a735048e0cc919e2a28b9619d17c48339ce065e18223762312a048b1a5fc096a9430ccc552072c8f08e406ad05c0510924409c81488e296b09c42782235007601f8c0239ba6cc18c8c927e70cde7a191429a5946e9a91efa804181e85502924db830c79421cc2e3260e90d21621369c5a4871a1a0d094ce8c19ef48b2961c49c028e1890f7c958888c87b06c23fd97f289d06f214688f
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf907350d404408df24c6a1a8088003e458d4350110237c929a86a022000f915350d404400176704a1a808811be40c94350110005e9c1ae4a022046bd0835c94044001bc2e4392808801eec213625011003cf943cc4a0220009f187989404400f765093128088002ec6126250110004f9c3ac4a0220079f08758940440016e70ab12808811edc2156250110005d9c22c4a022007bb08458940440017a706b12808811af420d625011003dd9420c4a022000bb184189404400f765092928088002ec612525011000798aa4a4a022007bb284549404400b7650ea128088016ec21d4250110005d943284a022000bb08650940440017670aa128088002ec6154250110005d9c1a84a022007bb382509404400ff4704a128088003e8dc94250110007d039284a022000fa2625094044001f42c4a12808801eeca123250110005d8c2464a022000f91438c940440013e70e99280880027c21d325011003dd942264a022000bb1844c9404408df8064992808800279e09754c110004f2412ea98220009e7825d130440013c904ba26088016f4a03634c11002cea43aa69822005bd08054d304400b3a90ea1a6088016f4201434c11009c7b430e498220068f5861c930440112ed0a39260880025d614724c11003cdb420e498220009b5841c930440d3ba06039260880167521d324c110006e2392649822005bd0804c9304400d3e10ea8260880035cdd5504c110035e841aa09822000f5153541304400d3e10ea0260880036cdd1404c110035e841a809822000f914350130440a7ba061b9e40880167961e52c811002cf2c3c8590220059e5878cb20440a7f8061196408801b711cd32c811002df0402659022044fc3304cb20440113e70ea8640880235c9d550c8110006b8baaa19022000f6152543204400f3e70ea06408801f6c9d140c8110006d8ba2819022000fa142503204400b3e101baa408800275e0d7548110034ea41aea90220059f080dd120440013af06ba2408801a7520d744811034ceb43ee69022053fc020dcd20440a79aec1b9a408800374d83734811029ee9286e69022053dd240dcd20441453e700b9a408814e75a1c734811034fe0100e69022005be080949204400b3c90ea924088016f8201524811002df04048490220059e487509204400b7c100a12408801b711ce324811002df0404649022053fc2308c9204400b3c90e992408801b711cd324811002df04026490220089f0875412044001ae6eaa82408800374dcd5048110266e839aa09022000be0825412044001ec2a4a82408801e7c21d4048110006d9ba2809022000dd373501204408dba0e6a024088002f82094048110007d0a128090220069f0874c1204400dba0e69824088002f82093048110007e09926090220059f287c812044089ba0e79024088016f8a0b2048110
  | 1 => 0x706a92a088022dce095254110047b1c12a4a822000f63725495044001ec0e4a92a088003d89895254110007b0b12a4a822008b728590950440016e30b212a088003cc5524254110045b942a84a822000b718550950440116e50b192a088002dc6163254110007a8a9c64a8220009f3874c950440013e10e992a088022dca153254110005b8c2a64a82204cfc0324c9504414b3e10cbac80880175ce157590110256b832aeb202204dd73545d6404409bae2a8bac808812b5cd4d7590110256b9a92eb20220009f387d964044001ae2ebb2c80880027ce1d6590110005d9c22cb2022007bb08459640440013e70eb1c80880035c5d55390110004f8c3cc520220009f38758a40440016e70ab14808812adc2156290110005d9c22c52022007bb08458a40440017a706b148088126f420d6290110006b8baaa520220009f3874ca404400b3e10e9948088127f00c9329011003cf8c06eaa0220008f7865d540440031e90cbaa80880166d21d54501100055a432a8a022008d3475551404408fe66a0aa2808801e7c603735011002cda43a86a022046f933050d404400b3690ea12808801e7c21d5050110006b9baaa0a022000f315454140440a33e50dbaa808828e7c617755011023eb832eeaa0220059f384dd5404400b3e309baa80881435cd537550110286b8aa6eaa022050db343dd540440015e70cbaa8088082bc2197550110005d9c22eaa022000cf3865d540440033e10cbaa80880033c219755011000c78432eaa0220a49f3855d54044001ae70abaa808828e7ce117550110006d9c22eaa022047d73535d5404409bb6686baa80880067ce1f655011014cf843ecaa022000d7375d95404400f76109b2a8088003cc9536550110004f9c3acaa0220079f087595404400176708b2a808801eec211655011002dd943ec8a022005bb087d91404400f7650db22808801faca1b645011003f59bb6c8a022007eb076d9140440017630bb228088002ec60f6450110005d8c16c8a022005bb287551404400b7610eaa28088003ace195450110005d9432a8a022000bb0865514044001d610caa2808801eece15545011003f99c2aa8a022000f3375551404408fe60eaaa2808811fcc995545011000798b2aa8a022000bb383551404408fe66a6aa28088002ece09545011023f98292a8a022046dd0735cd40440017c704b9a8088002f8209735011003dd8426c6a0220009f38758d404400f3e10eb1a8088002ece11635011003dd8422c6a022000d717554d404400f76508a9a8088003cc551535011002dd943a86a022005bb08750d40440017650ca1a8088002ec21943501101f6d93b286a02203edb07650d40440017670aa1a8088002ec6154350110006d9baa86a022000db17550d404400f76706a1a808801fe4e0d4350110007c9b9a86a022046
  | 2 => 0xa324c91002cf943ee09922044fc032dc132440033e50db8264880067c21b704c910004f8c2ee099220009f184dc132440016e30a3826488002ec610704c91029ee9b98e099220a6fc0321c132441493e10cba4a0880176ce117494110286d8322e92822050db2545d2504408fb62a8ba4a0881436cd0d7494110286d9a12e928220009f387d925044001b62e9b24a0880027ce1d6494110005b9c2ac92822008b708559250440013e70eb1ca0880036c5d14394110004f8c3cc528220009f38758a50440016e70ab14a088022dc2156294110005d9c22c52822050bb08458a50440017a706b14a08813ef420d6294110006d8ba28528220009f3874ca504400b3e10e994a08813ff00c93294110044f8c06e8a8220059748755150440014e90caa2a08801f4d1d1545411026f99a02a8a8220089f180dcd504400b2e90ea9aa088133d4cc1535411002cba43aa4a822005b7287d95504400b6e10fb2aa088022dca1b655411004739436caa822008e7376d955044011ce0edb2aa088002dc6136554110005b8c1ecaa822000b7182d9550440973e50dba2a0880167c617745411026ed8326e8a82204ddb254dd15044095b62a9ba2a08812b5cd4f745411000579c32e8a822026af0865d150440473e10fb22a088022dc2176454110006d9ba6c8a822000f3354d9150440013e70eb22a0880227c21d6454110005b9c2ac8a822008b7085591504400b6e50eaa2a088016dc21d545411000739c32a8a822000b728655150440016e10caa2a0880039c2195454110045b9c22a8a822008f33845515044001e66e8aa2a088137cc1d1545411026f99322a8a822000f316455150440016e706aa2a088137ccd0d5454110005b9c12a8a82204df30425515044099ba0e6b9aa088002f8e097354110005f0412e6a822008b7085d8d50440013e70eb1aa0880227c21d6354110005b9c2ac6a822008b708558d504400b6e50ea9aa088016dc21d5354110005b9432a6a822000b708654d5044081ae4eca9aa0881035c1d95354110005b9c22a6a822000d737454d50440116e706a9aa088023d4e0d5354110007a9b9aa6a82204cf507354d5044099ea4c6a9aa088003d458d5354110267a921aa6a822000b738254d5044099ea064a9aa088022dca154354110005b8c2a86a822000f315450d5044001ea2a6a1aa088002f4e0d7254110265e841ae4a822000de1721c950440116e10bb12a0880227ca1e6254110004f8c3cc4a822008b728598950440016e30b312a0880027ce1d6254110044f843ac4a822000b738558950440116e10ab12a088002ece11625411026dd8422c4a822000bd38358950440997a106b12a088022dca146254110005b8c28c4a822005b7287549504400b6e10ea92a088002dca195254110005b8432a4a822000b738454950440016e
  | 3 => 0xca9a20009e4825d953440013e700bb2a68801a5da1f6554d10034ba43aa8a9a2000a7486551534400fa68e8aa2a6880227521d6354d10565e9c02c6a9a20059f2801c953440013e300392a6880027c6037650d10004bbc2aeca1a2008974855d943440013cf04bb28688002792097650d10004f9c02eca1a20008f7865d543440011e90cbaa868801a6da1f6450d10034da43aa8a1a2000ab4865514344011a68eaaa2868801e7521d6350d1055de9c02c6a1a20079d48754d4344001e2aa8a9a86880167ca007250d10004f8c00e4a1a20068f587d8f6244155bc2e1b14c4880225da1f7558910006b9c06eab122000c7760dd56244001ae6c1baac48801e6da1f74589100069bbaee8b122000d3475dd16244001b6701ba2c4880032dd837458910006d9b06e8b122000d37751d16244001a68ea3a2c48801a75a1f7358910006abbaee6b122000d5475dcd6244001b2ee9b9ac488003651d373589100066bb06e6b122000dd360dcd6244001aaeea39ac488003551d47358910006cbba0e6b122000d94741cd624400d9a8e7b1ac4880035cdd77058910006b83aee0b122000db374dc16244001b60e9b82c48800374dcf7058910006e839ee0b1220a9de372dc1624408b3e700b98c4882a2f860262189100047bc3ac431220009e787588624414f7c700b10c48801e6da137694910004dac26ed29220009f180dda52440013e700bb4a48801e5de1d54949100053a432a92922007d367455252440013e700b9ca4880167c2017394910044f2c3cc52922008b668598a52440d17c301314a488022d9215629491037df1c02c529220009f180dd952440012ef0abb2a4880026de11765491003cda422eca9220009d7835d9524400d3a906bb2a4880027ce017654910034ba43aa6a922067be18098952440113c90eb12a4881baf8e016254910044bb42eed212200097585dda42440013e301bb484880027ce0176909100047b436eb21220008f586dd6424401136f0eaa48488002ad21954909100469b3aaa921220009f3805ce424400b3e100b9c848801e7961e6290910335f0c04c52122007ba48458a42440db7c700b1484880027c6037650910004bbc2aeca122008974855d9424400136f08bb2848800275e0d7650910034ea41aeca1220009f3805d942440011ef0cbaa84880023d2197550910034da43a86a122065be180989424400f3c90eb1284881b2f8e016250910004f8c06ed1922000977855da32440112e90abb464880026de11768c91003cda422ed19220009f3805da32440113af0ea9c648801e75e1d438c910004f8c06ec9922000977855d932440112e90abb264880026de11764c91003cda422ec99220009d7835d932440013e700bb264880027ce01754c91002cf8402ea99220009f3805d1324400b3e100ba2648801af1a0
  | 4 => 0x1080015ad07a12c210002b560f425842004f6219264b084000cdb83dd920080019b107bb2401000336ddb73480200066dbb0e69004009eca3258d20080015b50eb1a4010002b621d634802004f65412c69004005cdb7258d200800bd96e4b1a4010027b2c8563480200076490ac69004000ec9634c920080913e700ba6ca880167c20174d95100053ac34a9b2a2000d357495365440016e3012a6ca881167ce0173d951002cf8402e7b2a20059f2809cb654401f3e301396ca880026de1172d951003cda422e5b2a20009d7835cb654400d3a906b96ca8803a7ce0172d951002cf8402e5b2a20079b687dd16544001b6701ba2ca880032dd837459510006d9b06e8b2a2000db250dd16544001b62a1ba2ca880032ddd874595100069bba8e8b2a20b1d7375dc16544001b66e9b82ca880036c1d37059510274f9c02ebb2220059f0805d7644400156b0daa6c8880034d5d754d9110005d8c06a9b2220459f3805cf644400b3e100b9ec8880167ca0272d911007cf8c04e5b222000977855cb64440112e90ab96c88800275e0d72d9110034ea41ae5b22200e9f3805cb644400b3e100b96c8880225da1f7559110006b9c06eab222000c7760dd56444001ae6c1baac8880035c9037559110006b8a06eab222000c77761d56444001a68ebb22c8880035cdd77059110006b83aee0b2220b0db374dc164440013e301bb2a8880038d15376551100047ac06ecaa22000cf180dd954440019e4a1bb2a8880033c90376551100047b434ecaa22000d34549d954440012ef0abb2a8880026de117655110004f9c02ecaa22000d34541d9544400d3ad063b2a8880027560c7655110004f3410ecaa220009e5821d95444001c68a83b2a8880031da1476551100063ac28ecaa22000cb6841d9544400196b083b2a8880032dd5076551100063b2a0ecaa22000c74541d95444001968a83b2a8880030d15076551100066b418ecaa22000cd5831d954440018eea63b2a8880032dd0c765511000673410ecaa22000ce5821d954440018e8a43b2a8880032d108765511000678c00ecaa22000c77501d954440019e4a03b2a8880033c54076551100065ba00ecaa22000cf2401d954440019e2803b2a88801e5d21d65551100063a3b2caaa22007b3484595544415f6e700b2aa8880226d21d64551100065a3b2c8aa22008b3485591544415d76700b22a8880167ca037355110004f8c06e6aa220069d683dc954440013ab07b92a8880167ca037255110004f8c06e4aa220059f2801c954440013e300392a8880063d21b705511000679bb4e0aa22000cf0769c154440a1e60a9382a88810abc2197055110006783b2e0aa2204df30545c1544400b3e501396c68803e7c60272d8d1056ee9b9ee0b1a20009f180dd9534400136f08bb2a68801e6d2117654d10004f3c12e
  | 5 => 0x28fa1731590200051ec2e62b204009aae828c5640800155b0518ac810016aea0231590200055cc0462b204000c3c54dd954080031e903bb2a8100030f15176550200047bc0aecaa040018f4815d9540800b0f90eb2aa81000e8f21165550200063a38acaaa040058bc8759154080094790ab22a8100032d1c564550200047ac36e2aa040a0c7665dc554080018eacbb8aa81027f2d99371550200065ab26e2aa04000cd663dc5540800b1bd0fa9ac61001637a1f4358c200243f42ee2b18400087d85dc5630800717d09b8ac6100022f6137158c2002c6f43c62b184009ace828c5630800b5b50118ac6100163721d3158c2004d66412eab184000a9e841d5630800153b083aac610026b32097458c200052f428e8b184000a5d851d16308001c3ea92a2c610002b5e055458c200056a40aa8b1840008de8715163080011bb0e2a2c610003875505458c2005c6f43ea4b1840008dd87d49630800153d09a92c610002a76135258c2005c6f43e84b1840008dd87d0963080014bd0ba12c610002976174258c200052f42ee2b184000a5d85dc5630800153d09b8ac610002a76137158c2004d67414e2b184000acd829c5630800b5b50138ac610002b66027158c200046f438a2b1840008dd87145630800153d0828ac610002a76105158c2004d67410a2b184000acd82145630800b5b50028ac610002b66005158c200046f43882b1840008dd8710563080014bd0a20ac610002976144158c2004d6741082b184000acd82105630800b5b50020ac610002b66004158c2002c3e42eeca9840098ec825d9530800b0f90eb2aa6100271b1c96554c2004e56392c8a9840058dc8758d5308013998e4b1aa6100023b61b7254c2000636b2ee4a984000cad64dc9530800199ac7b92a6100162f2137650c2002c6e41eeca1840098ec825d943080138d8e4b2a86100162f21d6450c2004e56392c8a1840058dc8758d4308013998e4b1a86100023b61b7250c2000636b2ee4a184000cad64dc9430800199ac7b928610027930c9654c82004f46192c89904009acc8258d320800156d083aac210002ad61075584200056b418eab084000ad5831d561080135cd043aac21002ab9608755842002d79400eab08400aaf1801d561080014ed0a3a2c2100029d61474584200056b418e8b084000ad5831d161080135cd043a2c21002ab9608745842002d79400e8b08400aaf1801d16108001c6ea92a2c2100023de1d54584200047a43aa8b084000e355415161080015ad062a2c210002b560c54584200053b42ce6b084000a75859cd610800156d0939ac210002ad61273584200055b420a6b084000ab58414d61080014ed0a21ac2100029d61443584200055b426a4b084000ab584d4961080015ad07a92c210002b560f52584200053b42e84b084000a7585d096
  | 6 => 0x2d36432a4a824005b68805495048001998c7b9280900033318c725012002cd643a84a024005aac86509404800b75100a12809000ab6a1b638c1200066d3b6c71824053bc882d8e304800179706a946090002f2e0d428c12034d6d434651824069bca868ca3048029d950d1946090003729da328c12029f653b4651824053fc2718ca30480a7f82e319460900163ba1b724c120004b6c28e498240009ad841c9304800199ec639260900167321d324c12002d66432649824002ccc764c9304800b7910099260902cbf0c41324c1200866c3b6c69824002cd87654d30480059b0eca1a6090002da614724c120005d4c20e49824069dcb731c93048001793072926090003d254d524c120005e4c1c849824000f8943509304800b3b10e9926090027361d9324c12004ee4392649824005bc8874c9304800b7950c9926090016f2219324c12001764432649824002ecb764c93048021b90ec992609000bb21d9324c120016643b2649824000bcb854c930480017930a9926090002f2e11324c120005e4c22649824009dca325cf20480a79b4edb1e409000b369d863c812004ee5b9a65902400587e87951650800187ee92a2ca100161fa1e535942002c3f43ca2b28400587c87545650800187ee93a2ca100029de0574594200053a40ae8b284000c3d741d165080014bd063a2ca100029760c745942004d36412e6b284000a3e841cd650800147b0839aca100021fa1c43594200043ec3886b28400d87e87d0965080010fb0fa12ca1000297a0f42594200052ec1e84b284000a3e841c5650800147b0838aca1000297a0c71594200052ec18e2b284009a6e821c5650801b4db0438aca100169ea00715942006d3cc00e2b28400087e8710565080010fb0e20aca1000297a0c41594200052ec1882b284009a6e8210565080014db0420aca100169ea0041594200053cc0082b28400087e87cc565080010fb0f98aca100028fa1331594200051ec2662b284009a6e828c565080014db0518aca100169ea0231594200053cc0462b2840058be87d51640800187eebaa2c8100162fa1e435902002c5f43c82b2040058bc87505640800187eeb3aac810002ade0575590200055a40aeab204000c3d751d5640800153d063aac810002a760c755902004d56412e6b204000a3e851cd640800147b0a39ac8100022fa1c53590200045ec38a6b20400c8be87d49640800117b0fa92c810002a7a0f52590200054ec1ea4b204000a3e851c5640800147b0a38ac810002a7a0c71590200054ec18e2b204009aae821c5640801955b0438ac810016aea0071590200655cc00e2b2040008be87145640800117b0e28ac810002a7a0c51590200054ec18a2b204009aae82145640800155b0428ac810016aea0051590200055cc00a2b2040008be87cc5640800117b0f98ac81
  | 7 => 0xde87dcd6448001998e7b92c8900021fe1571591200243e42ae2b2240008bf845c564480011bf06b8ac89000a3720d71591200066bb9e20b2240b3cd473c4164480051bd07bb2a8900023760f765512000c7b40cecaa240008f5819d954480011bf06bb2a89000a3720d76551200047bc0aecaa240018f4815d954480070fd0fb2aa89000e8fa1365551200063a38ecaaa240048be87d91544800947d0bb22a8900032d1c764551200066a31ee2aa24000acd82d4f63480010ff0ab8ec6900121f21571d8d200045fc22e3b1a40038bc845c763480031bf0e98ec690002a7a1265d8d200054ec24cbb1a4000a5e8599363480014bb0b326c69000297e1561d8d200052e42ac3b1a4000a9f84587634800153908b0ec69014f72dcb70d8d2034e6b3b621b1a4000a9e849d7634800153b093aec690002b3a0875d8d2029d66c10ebb1a4000a5e859d363480014bb0b3a6c690002b3a0874d8d2029d66c10e9b1a4000e1f5495363480015af02aa6c690002b520554d8d200046f438a9b1a40008dd871536348001c3aa82a6c69014e37a1f52d8d200046ec3ea5b1a4000a9e84d4b634800153b09a96c69014e37a1f42d8d200046ec3e85b1a4000a5e85d0b63480014bb0ba16c69000297e1571d8d200052e42ae3b1a4000a9f845c7634800153908b8ec69000237a1c51d8d200046ec38a3b1a4000a9e84147634800153b0828ec690002b3a0851d8d2000566c10a3b1a4053ada8014763480015b30028ec69000237a1c41d8d200046ec3883b1a4000a5e8510763480014bb0a20ec690002b3a0841d8d2000566c1083b1a4053ada8010763480015b30020ec6900021fe157158d200243e42ae2b1a40008bf845c5634800717908b8ac69000237e0d7158d200046ec3cca31a4000a9e84994634800153b09328c69000237e1d6518d200046ec3cc831a4000a5e8599063480014bb0b320c69000237e1d6418d200046ec3cc231a4000acd8298463480015b301308c69000237e1d6118d200052fc2ac231a4000a5c85584634800153f08b08c690002a72116118d200046fc1aeca9a40008ef825d953480050f90eb2aa69001237a1f6354d200046fc1aeca1a40008ef825d943480051790eb22869000e37a1f6350d20006673b0c72924053ccc76d8d52480d3998ec31aa490002f260c7054920006673b0c721240058ec865d5424800b3d100baa849014f331db635092034e663b0c6a124000bc9831c142480011dd0dbac64900023ba1b748c92001567436c71924000cce76d8e32480015990ca9c6490002b3219438c92004d67416c69924053cd870d8d324800b1d90cbaa64900163b219744c9200a567436e69924002ccc76dcd324800559d0db1a649014f331db634c92029ee5b98e09924000ccc63dc95048001998c6392a0900165b21d52541200
  | 8 => 0xa312649802793614624c93004f47420c49926009e8d84189324c013d8d023126498027b1604624c93004f64c00c49926000ec710189324c00b2b90ea9aa09801697219535413002dac402a6a82600599c8750d404c00b5390ca1a8098016e620143501300146f41eecaa640008dd83dd954c800b1dd05bb2a9900023de05765532000c7a40aecaa6400387e87d9554c800747d09b2aa9900122fa1f64553200251f42ec8aa640058ee82dd953c80130f90eb2aa79001237a1f6354f2002c77416eca1e40098bc8759143c80071bd0fb1a87900026b6137654b20004e6c1eeca96400096d85dd942c800139b07bb285900165b21d525432002cd643a84a064009ccc7258d30c800b3990e9926190027331d9324c3200045fc22e2b2c40038bc845c565880010ff0ab8ac9100121f215715922000c7a40eecaa440008f7815d954880031e902bb2a9100161f21d655522001d1e422caaa440058bc8759154880094790ab22a9100023d61b715522002c3e43acaa9c40058dc8758d538800b1790eb2287100163721d6350e200055bc22eab0c4000ab4845d5618800156d083aac310002ad61075586200056b418eab0c4000ad5831d561880275cd043aac310002b9608755862002d79400eab0c4013af1801d561880014ef0aba2c3100029d21574586200053b428e8b0c4000a75851d161880015ad063a2c310002b560c745862009d73410e8b0c4000ae5821d1618800b5e5003a2c31004ebc60074586200071baa4a8b0c40008f78755161880011e90eaa2c3100038d55054586200056b418a8b0c4000ad583151618800b5e5002a2c310002bc60054586200053b42ce6b0c4000a75859cd618800156d0939ac310002ad612735862002d79404e6b0c40b5af1809cd618800156d0829ac310002ad610535862002d79400a6b0c4000af18014d61880014ed0a21ac3100029d614435862002d7940086b0c4000af18010d61880014ef0ab92c3100029d21572586200055bc22e4b0c4000ab4845c961880015af06b92c310002b520d72586205a579c02e4b0c4000ab684d49618800156b09a92c310002b5a0f52586200056ac1ea4b0c4005af280d4961880015e301a92c3100029da1742586200053ac2e84b0c4000ad683d0961880015ab07a12c310016bca03425862000578c0684b0c4000af3804c9618800b5e100992c31004e3da1c32586200047ac3864b0c4000a76850c961880014eb0a192c310002ada1032586200055ac2064b0c4000ec5320c9618800b5e500192c310002bc6003258620005e5c12a69844000bcb8250d3088013b90e49926110043b2589324c2200146f43ee6b2a4000ccc73dc965480010ff0ab8aca900022fe11715952001c5e422e2b2a40008df835c565480051b906b8aca9000335dcf105952059e6a39e20b2a40028
  | 9 => 0x74586300053a42ae8b0c6000a76851d1618c0014eb0a3a2c318076b5a0c74586300056ac18e8b0c6000ae6821d1618c0015cb043a2c318016bca0074586300ed78c00e8b0c6000e3754951618c0011ef0eaa2c3180023d21d54586300071aaa0a8b0c6006ad683151618c0015ab062a2c318016bca0272586305c578c04e4b0c6000a77855c9618c0014e90ab92c318002ade1172586300055a422e4b0c6000ad7835c9618c00d5a906b92c318002ada1352586300055ac26a4b0c6006ad683d49618c0015ab07a92c318016bca00525863000578c00a4b0c6000a7685d09618c0014eb0ba12c31801ab5a0f42586300056ac1e84b0c6005af280109618c0015e300212c31800a3720d72d953000667b98e4b2a6009c6e851c9654c0018dea8392ca980033390c72595300045fc22e2b2a60038bc845c5654c0011df04b8aca980263b209715953000673b9620b2a6000ce472c41654c0051b906b96c89800333dcc725913004e57420e4b226000cae541c9644c00199ca6392c8980021fe1571591300243e42ae2b2260008ef825c5644c0131d904b8ac89800339dcb10591300067239620b2260018f6819d9544c0011eb033b2a8980023be09765513004c76412ecaa260008f7815d9544c0031e902bb2a89800e1f21d655513001d1e422caaa26000a6c82595544c0091790eb22a8980128f215645513000556412c8aa260048dc87591534c00159904b22a698003875915454d30395aa40aa8a9a60698de86dc9534c00179304382a698016372197550d3002cec402eaa1a60038dc87595434c00159904b2a8698003875955450d3038dca40aa8a1a60698de86dc9434c001793043828698002aba1352d893000566c1ea5b126000a6e85d0b624c0031df0e90ec4980023be1d62189300062f21aea3126009c6c825d4624c0138de42ba8c4980271bc8175189300064f29ae83126009cac825d0624c01395e42ba0c4980272bc8174189300262f3aaa63126000c9d7454c624c00159f04a98c498003175d5431893001e4f3a2863126000acf8250c624c0018daeba90c498002aba13521893000566c1ea43126000e4d53d48624c0014dd0ba10c4980032b5d3421893000566c1e843126000e8d43d08624c0019aca6b88c4980033554d71189300066b21ae23126000cd5435c4624c1671ef00b88c4980031b5d5211893000656ba2423126001ce671484624c0031ef0f880c4980023d61f10189305be3b3ae203126000c7575c40624c16d96ce9880c4980032d5d3101893002e6ab9e2031260b3cf170c40624c0131f10cb84a49800e2fa1076549300045ec20eca92600987c87595524c0131f10cb8484980121fa1476509300043ec28eca1260098bc87591424c00b1b90cbaa649801637219744c9300bd67438c49926009cce87189324c013c9d
  | 10 => 0xb148053c9d40dcd62900a79ae21b9ac52014f354437358a400043fc2ae2b14800487c855c562900011bf06b8ac52000a3720d7158a400046fc1aeca9480028dc835d9529000b1d90eb12a52000ab320d628ca4004d66412c69948009acc83989329000b1d90eb12652000ab320d624ca400055bc22eab0c8007ab4845d5619004756d083aac320002ad61075586400056b418eab0c8000ad5831d561900015cd043aac320002b9608755864002d79400eab0c8023af1801d561900014ed0b39ac3200029d616735864003d5b424e6b0c8000ab5849cd619000f56d0829ac320002ad61053586400053bc2ae4b0c8000a74855c9619000156f08b92c32001ead21172586400056bc1ae4b0c8000ad4835c9619000f56d09a92c320002ad61352586400056b41ea4b0c8000ad583d49619000b5e500292c320002bc60052586400047b43864b0c80008f5870c961900014ed0a192c3200029d614325864003d5b42064b0c8000ab5840c96190001d8a64192c320016bca00325864000578c0064b0c80038bc845cb65500011bf06b96caa000a3720d72d954000e7938a21b2a8000e72514436550173ce0a2886caa00063da1f71595400043fc2ae2b2a80008bf845c565500011ed0e38acaa00031ddd471595400065bba0e2b2a8001cf07184165500031f10e882caa00128fa1b6555140004cec1ee4aa280a0cb476dc55450141c68cbb8aa8a0002ec60470551400261e3aaa9b1a800087f855c763500090f90ab8ec6a000a2f21171d8d4000666318e4b1a800287c8759553500814e902b2aa6a00030f1d95454d4002c5e432eaa1a80028bc87595435007d56902b2a86a0003875955350d40005d8c08e0a1a8002c9e7350f625000155b08196c4a0003a350c32d894000574c0065b1280008ef87588625000159906b10c4a00130f1d5541894004e66192e63128005cb574c40625000727f0eaa4a4a00030f9d9549494002c5e432eaa128000bb1811c1425000733f0ea1c64a000aa7219438c94000666194ec9928000ccc321d9325000b1790cba264a00030fd97745414002c9e43aa8a828005a3c865515050007878ecaa2a0a0016ce201545414000666196e4b2c60008bf845c5658c00717908b8acb18003330cb72592300043fc2ae2b24600487c855c5648c0031e903bb2a9180023de05765523000c7a40aecaa4600587c87595548c00747908b2aa9180162f21d64552300251e42ac8aa460008f586dc5548c0010ff0ab8ac5180121f2157158a300045fc22e2b1460038bc845c5628c00b1d90eb12a5180163b21d6250a3034c6fc3ac51946000ab7845d5618c00156908baac318002ada1075586300055ac20eab0c601dad6831d5618c0015ab063aac318002b9a08755863000572c10eab0c6005af2801d5618c03b5e3003aac3180029de15
  | 11 => 0x8c8090f90ab8ac1190022fe11715823201c5e422e2b0464038be84dc7654c80117b09b8eca990121fa1771d91320043ec2ee3b2264008dd83dd9544c8031ed033b2a8990023d60676551320047bc0aecaa264018f4815d9544c8011f700bb2a8990163e201765513201c3f43ecaaa26403a3e84d95544c80917d0fb22a8990128fa176455132006e2196e2aa264048df87596324c8071bf0eb24649900a37219708c93229e6c302e11926409dcb205c2324c8031f70e886c099003710c9719813202e78302e33026400cf171d82604c8a78bec6ba8c099003530c9751813229e4fb1ae83026400d8c325d0604c801b8864b88c0990023ee1d601813200e7938a20b24a0008ef825d943940131d904bb287280162f21d6450e5002c6e43ac6a1ca0028de87dcd62940a78bea1b9ac52814f175437358a5029e6b886e6b14a053cd510dcd629400117f08b8ac52800e2f2117158a500046fc1ae2b14a0028dc835c562940011bf06bb2852800a3720d7650a5002c7643ac4a14a002acc8358a329401359904b1a6528026b320e624ca5002c7643ac4994a002acc8358932940014ef0aba2c3280229d215745865014d3b428e8b0ca000a75851d161940015ad063a2c328002b560c745865000573410e8b0ca000ae5821d1619400b5e5003a2c3280a6bc60074586500453b42ce6b0ca000a75859cd619400156d0939ac328002ad61273586500453b42886b0ca000a758510d61940014ef0ab92c3280229d21572586500055bc22e4b0ca000ab4845c961940015af06b92c328002b520d72586500453b42e84b0ca000a7585d0961940015ad07a12c328002b560f425865002d7940084b0ca000af18010961940011ed0e192c3280023d61c32586500453b42864b0ca000a75850c9619400156d08192c328002ad61032586500076299064b0ca005af2800c961940015e300192c32800e1f21572d91500046fc1ae5b22a0028dc835cb64540039e4e2886c8a8003ac90510d915051f5820a21b22a003a3e86d9154540012bb07b92a8a827f1d1db71551504ff1a326e2aa2a000b71811c15454007878e8aa6c6a800a1f21571d8d500045fc22e3b1aa0038bc845c76354001998c6392c6a8002dc6047054d5002c3e432eaa1aa000c3c7655143540058bce6a9ec4a80029b61732d895000536c2865b12a000e4d530cb62540015d300196c4a80023be1d62189500056641ac4312a003c3c74550625401399864b98c4a80171d5d71018950005b8c08e0a92a00493f87552425400187cecaa484a80161f21975509500062ebaec7192a00495f8754e32540054b90ca9c64a8003330ca764c95000666190ec992a00587c865d532540039e4e2882cb200023be097654e4004c76412eca9c800587c87595539000b1b90eb1aa72000a37a1f7358a4029e4fa06e6
  | 12 => 0x8023da1c715954300c6e43a62b2a86008f687c416550c031e90f882caa18128fa1b6555143006ca38ee6aa2860299e83dc95450c7d36d0fb8aa8a1a832d1db71551435071a32ee2aa2863e9b481dc15450c056390eaa2a6a180f4721d5454d430158f432a8a9a8602b1c865515350c09c390caa2a6a181387dd95454d4301e8f3b2a8a9a8603d1c765515350c09c38ecaa2a6a180f071d95454d430058fc12a8a9a8600f17815515350d2763d02aa2a6a1a4ec72055454d435d78a40aa8a9a8693b14815515350d77a3ee2aa2a6a1aef475c55454d435d70fb0aa8a9a86bae1d615515350c0163f00aa2a6a1aebc5c415454d4301ccf420e4a9a8600d1d541c95350c01a3aa9b82a6a18121fa1771d89430043ec2ee3b1286028bd84dc76250c071bb07b8ec4a1adb355cf10d894300477c3ac43128604c3c755506250c098bceaa98c4a180387551531894359e5aba62031286008f7815d76050c031e902baec0a18130f1d554d81430070eaa2a7b0286028bd84dc76050c011f70eb00c0a180e8fe1964552521a43ec36e4aa4a40493d84dc9549493f8eeedb8aa92927f8d993715525201e1f3a2a8b1ca4038be84dc5639480117b09b8ac7290263b2097650e5204c5e43ac8a1ca403a3f86551439480187eecaa287292334b1c95450e5200c7b40ee8b04a4008f581dd1609480787ce8aa2c12900e37a1f6350d520152e432a6a1aa4048ee86dc94354801a9aa639286a90275ac8170949520047bc0ae9b02a4018f4815d360548011f70eb00c0a90023de0171d964200e7338a43b2c84018f787c4365908011eb0f886cb210261fa1e51596420251fc32caaa4843a8bd86dc9549080727b0bb92a9212334b94b72552425065bbb6e2aa484a0e3665dc5549080987ceaaa2c7210121fa177158e420043ec2ee2b1c84098ec825d953908130f90eb2aa7210128fe195454e420061fbb2a8a9c848cd2c7255153908031ed03baac1210023d60775582420261f3aaa8b0484098bd84dc765508031ed0fb8acaa10023d60371595420047b438e2b2a8401ce471c8565508031d90e90acaa10023da1f105954200c7a43e20b2a840287c8759553508814e902b2aa6a101237a1f6354d4201c77436e4a9a84028bc87595435087d56902b2a86a100b271d95350d420070eb2aa6a1a8400b8c8254d43508070ff0eb2ca4a10030fd9774549420245fc3acb2128409dab205c242508011ef02baec0a10063d20575d81420047dc3ac030284008f7815d9548c8031e902bb2a91900e1fa1f655523201d1f426caaa464048be87d91548c80947d0bb22a91901237a1f6454e320070fb22a8a9c6485b5481551538c8731bb0db92a71900e37a1f6550e320070fb2aa8a1c6484b9481551438c8671bb0db92871920f17dd95354a324164fbb286a14640087f855c560
  | 13 => 0xf1a2a0c2b1aa800af1801856355001a38a8b9ec4aa2ff1d5d461d89545f65aba0c3b12a8c4e345418762550019ace630ec4aa003355cc61d895400578c00c3b12a800c5d759cf625500193ae939ec4aa00a37e1d73d89540062ebaae7b12a800c9d745cf62550018bea0b9ec4aa00327d0173d895401c3ec2ee3b12a8048bd84dc762550051bd07b8ec4aa0023760f71d89545b63abae21b12a8b7cb574c4362551679ace7886c4aa003355cf10d89540069a2a2e3312a8c2c7575186625518796ae830cc4aa002bc60061989540069a2a6e2b12a8c2e345418562550015e30030ac4aa0023be1d621895400578c00c2312a8008f58798f61550011ef0eb1ec2aa002b5a0f62d85540056ac1ec5b0aa8008f58798b61550011ef0eb16c2aa0034d15170d85545053b428e7b0aa89fa75851cf615513f56d0839ec2aa282ad61073d85545053b42ee5b0aa89fa7585dcb615513f56d09b96c2aa282ad61372d85540056b41ee5b0aa800ad583dcb61550011ed0e196c2aa0023d61c32d85545053b42865b0aa800a75850cb615513f56d08196c2aa002ad61032d85540057940065b0aa800af1800cb61550019e6e1386c2aa2829da1470d85544fd3ac28e1b0aa89fab6841c3615514156b08386c2aa002b5a0c70d85540056ac18e1b0aa800ae6821c361550015cb04386c2aa0023da1c30d85540047ac3861b0aa8a0a76850c361550014eb0a186c2aa27eada1030d85540055ac2061b0aa800ae6820c361550015cb04186c2aa0023de0573d815400c7a40ae7b02a8008f7815cb60550031e902b96c0aa002bc60371d815400578c00e3b02a800d34545c66055183c68a830cc0aa002bc600619815400c7b436e2b02a8428f486dc56055001a68a9b8ac0aa0023da1f61581540047b438c2b02a8c1c7775185605518196ee830ac0aa003471517318154006962a4e4302a800d2c545c86055001a68a8b88c0aa0173c98171181542147ac3ec2302a800cd673d8460550019aae7b08c0aa003399cb611815400672b96c2302a800af180d84605517f8eaea308c0aa2fb2d5d061181545ef1a2a0c2302a800cd67318460550019aae6308c0aa003399c8611815400672b90c2302a800af18018460550011f70eb00c0aa0033c5c5601815400666192e5b22a60287d85dc76454c0747d0db22a8a9803551c77355153014af41ee4aa2a64097687dc55454d3f8e8edb8aa8a9a7f8d1937155153204ba40ee0aa2a60287d85dc76254c0717d09b8ec4a98022f61371d89530246ec1ee3b12a6b7cd573c436254c011df0eb10c4a980f0f1d1541895359e3abae20312a6008f7815d36054c031e902ba6c0a980f0f1d154d81530143ec2ee3b02a6008fb875806054c0199864b96caa180a2f61371d95435e61fbaee8b2a86018f687dc56550c011eb01b8acaa1
  | 14 => 0x37f1d976432800020245531200300080180000000000080500080100000080300000000000000080080000080100080200080000200380300280880080100300200000180580180000000200400100380180000000200000380300000280400300000000200000180500180000200080000000080000800100000080100000180480000081580100000080200080000600780000100000080280280080000500400100080180000280080000200900200300880000200400280000000180100080000100000000200000180080680200280280280080180000000080080280100080600280380200100080080501580100000080580000280780900000d00800480280000680000000580000000380080000300000000080100080080000000080200080200000180000200000000080000000080400080200500000000080400480900000100000000780100000180100100400000000000280400100080180180000000000280080001100100080080080300100400000000880400100200000180080080280100100000080000000000400880200000000100000000000500000000080080000100000100480000180700100100480180280780480000000000180000280100000000080000000200000200180080000000000000080180600200280000180100080300180280000000000100100000100000000000000080100000000180100000180300080000000000000300580000080000000000280000100000080000000100800180080780100200680600000000080100000080580000000180000100000000080200380100480000100000280000100080000000000180000000000280280000200000100480000600000000080d00000c00000380000080b80180080100b80a80280300080000700080100000080680000000500100680200080080200200000000380000080080080300480080000100000300080400000480100380000000000080000000080480680000000380400000c00000080000580180280180080080380080100000081700f80100000100480000000180180080080180000000100200200080000180380080080080000080000000380300000000200080100000100900000000000000180200200180080080000000000000000080300000300400000480380000400100300300180180180080080000400100000080000000080000480100280080200000000480000080180180000380400080080000400000100180000300000000280400000000480000080280700600000100000000380100480180280180200000000080180000000280300080200000580180000000000300100000100000300000000116f1d1d461d8d542ce5a3a0c3b1aa8c6e345418763550015e30030ec6aa0034d1537158d5462
  | 15 => 0x29826600074f0501790003cd4be0824885d51ef07334644271d0606815916320000000002f30000000000000001cc00000063c4e60000000001200000005a439744d3b50d40000000000b15743152d161f0006b600003a36c0000000003e311b0000000003d967172721e1881566965dc13c0000410531531b839976279c2ae3e15786042435632e37772d833345d3b129b40171541f0a53cc4ac00043e54676d4056285150000000000000000220002ab36068061a4c81470004943f13c23774542e63d30002640000004b50000000000000000002cd0d670f3532f91eb44e3c15d42260bb78479100007663100071e2042bb4a62830005a60ca0000000000004490000005b652f13b23f0000000005160000004b30003a10001b21c80000002702fa12c5da2d217211f0e875004f5c107d08a00040300030524100014540c3eb00061819d17315123300000000000000004600077900035700000008d2284642f50be02e3201a20906976562253043d10d200041053e0000001be00029e16a6d507100048045b78e7083ee68400032737d31f0006a34d40000002b623e00043653a0000001dc6f70001693940000003f00000000004654711fe00067f5cf4f10000ac3fb00039b7350000005ba00031d0310320000004ec50354277e5596e565400030d5680005bb4580000005a30000ec0000000e032200000000000000000011376010a5a277300000000000e0006ec43d00000074647d00069a0005640000006004ce0005515760006a83190945436c56d70005960003fc3d500000038020e0fa45c3dc0003216025bd00072e00055a2453a37050000003624de3c966006f00000006200016d0001163021250000000005f012a23a44013f0000000003e72296194f21354e46897020000000a35d364600050f6250007323714fc2632df2a57041952b56e203c0006f24d100018f4e30004460000000006fe2be09631e00000000000000055e07f00000000000065f0000005cc0002820000000000006ad4d26262526301416741104983b638b3882a74e144c6ce00000049f60d0003635450b84593794f500005b5ea1bc5ed22729654720700023201d0424a151164d00053945200034252803d2cc0002ed4171bb0000000007966d36851855900003492213b300004506100000000000045600076e00000068f11843500008b5c80005fd00039c0002c615e0004040e200001e0004ba51a0005db0000004662e40002d40001b100000000000000000000032a19900000000074d00026a57b00000059404a21029000028b0000000000000004ae2f20000000000005d100000000000000074a6d15974a500000010f2600ea7410000000006db0000000006ae6750006b15180111f80000005de12f0000007390006c12b138575e1a70003db00062400
  | 16 => 0xe656d00009c5720007480000000000003180006cc00000000013a0c26e30da2cb00040d5ad0000000000e500000000000010d30a0000670000b600024f00000000061c00000000000000072b68b6eb00027571247875151412400700034c56f2c05dd3650006e100029300000000017c0bc00000054d2793a200008f00039f00000000b0005ca39100075a5730002994191ee4ed3ea7632a800024a50a00000066414a0002de0006330000207340001a800000052b1980f200044700000043800000000042870b67d0006f934d0a91550051030000801c369f0636d600050e00d00072200000069b0c068359516e0000000f50003ec00035f6bc0000000980000000000001f70002815370000000000005e941600000000071f00000300046e34500052500000061d4a318012855b0371a03a76e90001a32c20003343e513237810e69e3703313bf1d20006c93670000005bc62c19661600050b5aa0005d90000790001f30001b400000000000000000038700000026e34174b67000000059c36d0000a03897400000e337c54c1220006f548c3520000006f10c35b218c34458d00000000000000000000000017f3fd00000047b68226109500059b6410006b920300000009166300062200000000019c36a0000000000007071db65b3660006692763552d61573c40d80af2a64695e40002002d50001f03f71f662d3935f40004200830002504f07252720005f367228a0004531142130001175b016c74256b47a2b73473687133f328f3a578c7694071e200063d7470ba6680007110000001ad1b90fe0b300000000075706d00032655f5d06f600000928022265900000025f00000042120a0004a22050c538a68717835e0002c900000000049120d00000040f7586cf00014800065349a53300053b0000000000bd00000029c50d1d642b00031c73d3646cb2e02202773e80005b91b300000f06619e00000037673a0000005e70004f30003d00870006b30001d100000000000000000000000022f4b122b2912ea00005400047300015b0001e500000000000016800013d00044f2b900062a4e700057529d0000004ff40e2f002b71602630e00000000077000000014e0003af18700067e20f65e0000007820004ab3ac37a6521c60f061561743334b2730000000003104c200015854b1b662314000022a70e53f5d213100007b5775c90006900002420720dc00000046770d2ce3a000000042f30b00000000000060f0000444a80000006430683bd5f64d70005673066110001642620000000002884f40004d62946a16424bf00045100000000000055627a10c1ae0000000001dd0004d06500000000004ef7562db4500700ed0000000005810000000000000000005850a84b83df00047200000000076a36e5836010000770562f75b46863be26c409
  | 17 => 0xad66d3823e40000001507200006981774814fa00009272d73800040a00001300000033c00054a0000000000000000000003380000000000006881b56c71ff00077466c00057049200000000000052c77b0000ef63a53134f4326910005f572403942908509d59f4007900000000000000000000043842e10000000000000000001110c449d0000000000000000007451e411500018a6a026b4f60fc00078635400055840671a0000005e86f812b0000003235321910000cf13358e0000000865017550005a51c24d344a48d58427e20b00000000000047900079a0000000000cd10942d2cf24e1e85f86dc0000002740bf00000050600000067336100000000044100050054e0000002ef00078b0002540000000002461b74a900000023d47500044841a1e00000000000000000000000005eb31b0000001040005932c702a6392e264a6093954311a40ee5621ca0a127c40211a0000000000000000003b20001052304b90003d65ef00008e3f942649545725800000024b00000000030f3f465a5c749b1430000000000004e87766ed4c32863e20000000000006d200000000006e0007360000b500000000000000046072152a70635c5570992170002bc10b37e2e81a15fb3d70000003130000000000001650000000174db0000002470000004b200055200000063f00000022e26f59800046a0000004230003c356100000060b05e0000002ec05a6a542e0f95b13a90000001263f600040b60500058000000019359900065500000000018978565c00032e0005e50006945102af0000006fc0000000ae06468c20671400075d0000000000000000005050000935340004130006611cb0340000001f900000000000033018435a51c6ab7752d30003f500015464968a0000006d000021f6363982bf04000041c5af57c3c701b73c0000004b000070a47f5b30de33700000060a3ce3ab00000049e58a0003480004760000150003430000006d84fe0433da1fd16100013933537b0e953066e6207950000000000004aa11900000054f5d71c17666fd00000000057d75300000007a0000005cd2c46af2ad61e0002481810003030000000000000005e20000000062c800035644446b60c5242090004965ec30162b0000002011cf00020c45a26d6ba12916712d38600076f5090dd00036900064448f0006aa60e0000001d405c56c1ac0b01d023159e3a673700047400062e6b707e6be00000078d5415f76e70000523d400056e0000000000000000002ba00000000000070350400024047e0005ee64700069267845f55400000060800076500025b46d23b39243f00000075c43c33962f0301714973ad3006571a62142ac64e0333721fc0fb73e0000007187985cb4154d944502354019a4830007813327090aa00047061241e42451b3750
  | 18 => 0x109a6bb73078f0005820000004681e30000000000002395e60c13ae0002160005870000004227671706f033f5d66b84d57971d55fc2840000006b525100000048b6e606a0001527235ac59d6075e32a072600066a0000002e51bd0000000973744af00067b4cf00000000000048e38c59200068d00000029748264800000058c26502843a2dd18235b02d0001aa5274c103614b0005c20007430780002a44e05c31de05d3240081e900006c45e1660002f60002f10e40000000005fe0000006f30003c00006c800000000000023800005700002f0f60000003e66d41210001071300005c400039e3cb6030000003142fe0000001e158f69300000004b2890f433a0fd0e12b805f3c63403d20000001df79b27f00069900000061b0000000000005b70180003b70005a70750000002676b209e72838e3072a928e01f21900000000246371c6c443702c52620862919f36b2370004fb0d90000000380d14c704971b0003f211e3511745be4bb6c32594ca5202bd21133d2fd08974418653c21839d63813e0d051d4ee09f5b500079969500000073b00000000043b0001632c118d28c72f25c2c542704e59a27d00000000050c15d5293094342ee71000077167a25d0f16a600050718e6620c71620003b96e40000000000000003d856655d04c11c00046f5e00000000000000005f90000000000000004dd0a75e100000000003e0003dd15961438f5bf77f28700a78900000000021d00016b0000000000001a50b900000031a3ba6210006de4cd0db4dc0b75a01fb1cd00000000000000000000000000053d00000000000000000056901014d39a42c6d900038d0000000000002230004c90005535a152166700000007c00068e4fd0002d900000017d0002f80000001f200000000052300005950877241d1c50007521370006064c61ec2347880000000001440001ba0000004b62957610000005c570c0005550000000000002711ab00000046115f00063e0004140001020210000000000002e90005860000000000000f865d00000000076b39000033600000000000052e00000016f74e6cd0f74b70000d300009b57e75b2786450007590120251da6fb0000007920000000002f44840df5384080003ca3e941833b0886350001011381ed5795f257100061367921c2e751f34a4f800035d0005a80744a00004435194860000006a977c0000000000000001f10000470001c70000000006b00e76a467c15c3e03813960003b02b27010001944bd7002c36b46a200056a00011d0002856100000001d314c0000c600000000000000000057f5490000000004e225a00042a00000000029a46c3ed0000002575ce5893fa32528d0000ab56566600033e24d2d70000004e50006c02a348900063434e7941c432d0000005170005df6510eb3732ff00032900
  | 19 => 0x4da1bf00055c17e7931b003f25614f3b84cb3ef0ff0552361f56400162b032b1ea0004bc0000000002490000000000196e071747c2121760000005ae5120f313475f4e903b0a416000069c00000000000004d0006da0005600000002b46ea73f2d05026ef1e600000024c0000000000002920846ee0000000002554d800018b00000077a4775b82441a90cb6650296fa4f93cf0000000650001065ff21b57a3de0ce3113176274874124994ea0003b40000000000007195c62aa72a4391081c93086ca0000000140cc0006c20005885483c82a10d519b1d72fc05148a53676800005821512e2eb0007310000001363ff4eb4850004f71460000004b432f4a70000356370273a429f3590000004a469d0000001425440000001af0002683bc64f6ff3fe0000c94936c61fa15a78a00036f4c578322c41b00046230c01c19017b2693bb76c19743041152258b72c2a208c0a252d0005506a70001120000000480000000000000000003580003aa6581275c06bd00038325e0005ab4251c064c5d80000000815a96bf22d2240000004c077817a2ca64b4c43501751d80005f100000049006b12327b66b00000078001a2dc77d6df3166dd0000b27541920006f42fb06951e3c50006e800018321a0006760000b41e778773323c00000049c4cc0000000000002530000000000000002350000000000007290c80005355fa1000240006771ce32c66f44b0000a64df0000000000004ad0000003f81f474c00c1490002b35136ac63b0002da3a87490d7
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x11359815076551100050d658541d954440015159315076551100054c640541d954440014369715076551100058564c541d9544400163190150765511063e8c600541d954440014b190d5076551100050da52541d954440014719095076551100051564c541d954440014719015076551100052564c541d954440014b19015076551100050de60541d9544400143598150765511000705a4c541d954440014359315076551100070564c541d954440014159315076551100050da48541d95444001c329015076551100050d640541d95444001c319015076551100050c640541d95444001c1454a0c765511000705151831d954440b787180d4c76551100050d257431d954440b38b180d0c765511000709152821d95444001c245460876551100063160d821d954440014349510876551100061c615801d954440018b18460076551100070c151801d954440018d28360076551100063460d801d954440018e282600765511000638609801d95444001c305494076551100050d257401d95444001c305490076551100060d210765955444001834851d964551100070c150769c154440010f2981d970551100061ce14765c154440018b3841d970551100060d1d0865515344001834752195450d1003e4521d5454d4344001614965515350d100060d9d086552524400183675219549091029e54dcd851c13244001b4032614704c91029e64dcd841c13244001b8032610704c9100060d1d08655150440013339460b6554110004d4e4d82d955044001351932195454110004d8648865515044001a33842195454110044cc2616455150440115309759154541100068c21964551504400135193e095454110006701cc825cd50440113509858d53541100057024d721c95044011360985895254110044cce615490950440113539854e3254110006700c8874c9504400b1709761532541100060d1d486551404400f9308755150501100058c2595454140440030f298e1975501100061c21b855d540440018b086e1175501100064ce17845d540440013339560b6450110004e4e4d82d914044001391932195450110004e8648865514044001a3385219545011003ccc26165551404400f5309759554501100068c21965551404400139193e095450110006701cc825cd4044081470965d553501101f52c2597550d404400f3909858d4350110007445d55350d40440015c0935c8725011003ccce6154949404400f3a098589425011003ce4e61438c940440019c03221d325011002c6c25d844c9404400b3509854d504c11002ce42614350130440019c073209504811002cd82615254120440019c073209404811002ce8261425012044001361952093048110004e8650824c1204400b3c0984c9304811002d7025d324c1204400d9c0874c93048110
  | 1 => 0x21a0080002000d80408000001c0202000001a0500018020d0303800000200c24030282804070200012030301c01a305460061d8d540050da5854dc56355001515931537158d540068c15180185635500111d9815173d895400507a58545cf62550010d5989cc61d8954007051517318762550018717560061d89540062c5d1801876255001a305460061d8954006349cd8018762550018d17360061d89540050da58545c662550015159315171989540061c5d58018662550018b17460061989540050da5854dc562550015159315371589540068c1518018562550014369615170d85540054564c545c361550014369615171981540054564c545c66055001a305460061981540050da5854dc5605500151593153715815400447660545cc605500141e9615173181540050ba58549c8605500150d9315272181540050ba58545c8605500150d9315172181540054a640545c860550014369615171181540054564c545c4605500153190151711815400705151731846055001c24545c861181540061c5d58018460550018b1746006118154006349cd8018460550018d1736006118154006389c98018460550018e172600611815400532640325cb6454c01551901c7735515300532640325cb6550c01591901c7735514349cc5a63815515350d3fc1476e055454d4349cc5247805515350d27614915955350d4202507a5f64551538c80741e97d955450e320057064032dc5544c8015c1900c9719813200552640325d4604c801589900c9741813200570640325c4604c801ac132600325865000523650631c96354001a495360032d895000532640329d932540014c9900c8764c950006b04c9800c9619000144d9518c7258d4049d852456554d4350001a894360032d894000532640329d932500014c9900c8764c9400053264032dc9658c0014c9900cb72592300048de6154151618c0014349755054586300068555183151618c00941c975915454d300058324964551534c00741c975955450d300058324965551434c167ac180c40624c9300048de6154151618800143497550545862000685551831516188001a31546005458620006b04c9800c96188001471901c765551200052c64071d9154480012d19020554d8d2000487e6154153634800181e8755054d8d200040fe61741d1650800181d7460c74594200040fe61751d5640800181d7560c75590200040fa6054dd9540800141d9315376550200040fa60545d9540800141d9315176550200051c6407159554080014b1901c56455020004b464081551630800121f985505458c200060761d541516308001237985505458420006855518315161080014369715376551100058564c54dd954440016319015376551100044d660549d954440015159315276551100054c640549d95444
  | 2 => 0xc34536c000022a09be690c8000000001398e5e0033000002a0f058490b0f5b4b100001c48700001b8bf00000240000000360e38abd8a007090520b4302f46e5f610bdc89747b3560404f299643e0023000502314c3e005518c14ac000012a003424d78510000152422b988687b648b46a7e23b59366f3c8016c646c28d4ad033959a4064d04c96cb572dd72004e32040de138a4da5b2a90c0010181b0000039800000042000caad6cae01a0000001c60000000b2151d0000a0067001ba5210874468335050c2483b1fd00d40e1ac3c2b50008dc985da506232630009e3f2d00c2277001d16a005400000003c19800001d8250a0c13111c0000031008d70021870703a8213eba5f0a91a002e0b98236599f1a6004e804003312930007a68a38000f25285aa0000000304d2c1c8008b00068005d0000000a4000000ea23e888489205800008848a6580171ca052ccf142ad94a744832030200800000100000000000804080000004000100006020200002080e8000c17000540600008002
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x4498740058e880cc2084c838005cc400bc0078e0fcc001044090f8ac7c0cd8b014a8a460003c0008d000f08848189ce4240004004c1000a03430f494b86454280068dc2c1d000000ec70506cd40108b48c04011000408200483861c0c101381c20216100002832a7151801876355001508d18a8c00c3b1aa800a0ca9c546006158d54005423462a30030ac6aa002415a9151731876255001418d38a8c00c3b12a800a8468c5460061d8954005445442a30030ec4aa003810545cd801876255001419538a8c00c2b12a800a8468c5460061589540050634e2a30030cc0aa002a11a315180186605500120ad48a8b98c2302a800b0168c545c86118154005843402a2e4308c0aa002814a755183151618c00140a53aa8c18a8b0c4000a0c29d546005458620006063014b8a83b2a8880032118064c541d9544400120ad1f302a0ecaa2200090c68398150765511000482f50c98a83b2a88800341193a40541d95444001a0949b202a0ecaa22000d0464d90150765511000486750c80a83b2a888002415a9152831d95444001608d00a9418ecaa220009056a45460c7655110005823402a3063b2a888002431a0257431d95444001602d18a9410ecaa22000b0868054a08765511000504b502a3043b2a888002c05a3151821d95444001610d00a8c10ecaa22000e0115183608765511000406b504a8843b2a888002415a3254421d95444001218d012a210ecaa2200090c6a4546007655110005063502a3003b2a888002c11a3151801d95444001c082a306c00ecaa22000e08151826007655110005823462a4a03b2a888002415a3257401d95444001608d18a9200ecaa22000a0568c841d9655511000502b46428ecb22a888002831a8150769c15444001608d18a83b4e0aa22000c0521c965515350d1000502b473a10caa4a488002815a39d486552424400140ad18e8432a8a822000a0ca9f8421954541100060612e432c8aa2a088002981a41cc825cd504400140ad18ea432a8a022000c0c21c9655150501100050654fc290caa28088003030972196555140440014a0d28e6412e6a022093b042997554d4350110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x862a0000400004811ba1517360061d8954004805ba151836087655110005801b0151836087655110004811ba151836007655110005021b9151826007655110005801b3151826007655110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x94c
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x3
  | 10 => 0x8a
  | 11 => 0x8c
  | 12 => 0x8d
  | 13 => 0x8e
  | 14 => 0x150a
  | 15 => 0x98a
  | 16 => 0x98c
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x128a
  | 20 => 0x128c
  | 21 => 0x128d
  | 22 => 0x128e
  | 23 => 0x150c
  | 24 => 0x150d
  | 25 => 0x150e
  | 26 => 0x9ca
  | 27 => 0x9cd
  | 28 => 0x9ce
  | 29 => 0x12ca
  | 30 => 0x12cd
  | 31 => 0x12ce
  | 32 => 0xa0a
  | 33 => 0xa0c
  | 34 => 0xa0e
  | 35 => 0x130a
  | 36 => 0x130c
  | 37 => 0x130e
  | 38 => 0xa4a
  | 39 => 0xa4c
  | 40 => 0xa4d
  | 41 => 0x134a
  | 42 => 0x134c
  | 43 => 0x134d
  | 44 => 0xcca
  | 45 => 0xccd
  | 46 => 0xcce
  | 47 => 0x15ca
  | 48 => 0x15cd
  | 49 => 0x15ce
  | 50 => 0xd0a
  | 51 => 0xd0c
  | 52 => 0xd0e
  | 53 => 0x160a
  | 54 => 0x160c
  | 55 => 0x160e
  | 56 => 0xd4a
  | 57 => 0xd4c
  | 58 => 0xd4d
  | 59 => 0x164a
  | 60 => 0x164c
  | 61 => 0x164d
  | 62 => 0xe8a
  | 63 => 0xe8e
  | 64 => 0xeca
  | 65 => 0xecd
  | 66 => 0x104a
  | 67 => 0x104c
  | 68 => 0x150954
  | 69 => 0x168a
  | 70 => 0xa0954
  | 71 => 0xa0956
  | 72 => 0x180a
  | 73 => 0x130954
  | 74 => 0x130956
  | 75 => 0x10a
  | 76 => 0xa4954
  | 77 => 0xa4955
  | 78 => 0x198a
  | 79 => 0x134954
  | 80 => 0x134955
  | 81 => 0x14a
  | 82 => 0x170a
  | 83 => 0x15c9
  | 84 => 0x3ca
  | 85 => 0x188a
  | 86 => 0x40a
  | 87 => 0x1a0a
  | 88 => 0x44a
  | 89 => 0x18ca
  | 90 => 0x178a
  | 91 => 0x1a4a
  | 92 => 0x17ca
  | 93 => 0xca
  | 94 => 0x1a8a
  | 95 => 0x194a
  | 96 => 0x98092
  | 97 => 0x150992
  | 98 => 0x9c992
  | 99 => 0xcc992
  | 100 => 0x15c992
  | 101 => 0xd0992
  | 102 => 0x160992
  | 103 => 0xd4992
  | 104 => 0x164992
  | 105 => 0x3c9
  | 106 => 0xcd512
  | 107 => 0x15d512
  | 108 => 0xd1512
  | 109 => 0x161512
  | 110 => 0xd5512
  | 111 => 0x165512
  | 112 => 0xcc9d2
  | 113 => 0xe89d2
  | 114 => 0xec9d2
  | 115 => 0x180c
  | 116 => 0x198c
  | 117 => 0xd0a12
  | 118 => 0xe8a12
  | 119 => 0x168d
  | 120 => 0x104a12
  | 121 => 0x198d
  | 122 => 0xd4a52
  | 123 => 0xeca52
  | 124 => 0x168e
  | 125 => 0x104a52
  | 126 => 0x180e
  | 127 => 0x15ccd2
  | 128 => 0x40c
  | 129 => 0x44c
  | 130 => 0x188c
  | 131 => 0x1a0c
  | 132 => 0xe95d2
  | 133 => 0xed5d2
  | 134 => 0x160d12
  | 135 => 0x44d
  | 136 => 0xe8d12
  | 137 => 0x170d
  | 138 => 0x1a0d
  | 139 => 0x105612
  | 140 => 0x104b
  | 141 => 0x164d52
  | 142 => 0xecd52
  | 143 => 0x170e
  | 144 => 0x188e
  | 145 => 0x105652
  | 146 => 0x3cd
  | 147 => 0xece92
  | 148 => 0xe8ed2
  | 149 => 0x104e92
  | 150 => 0x1a8c
  | 151 => 0x194c
  | 152 => 0x1a4d
  | 153 => 0x17cd
  | 154 => 0x3ce
  | 155 => 0x104ed2
  | 156 => 0x18ce
  | 157 => 0x178e
  | 158 => 0x14d
  | 159 => 0x19cd
  | 160 => 0x184e
  | 161 => 0x40e
  | 162 => 0x95514
  | 163 => 0x94a55
  | 164 => 0x95355
  | 165 => 0x95316
  | 166 => 0x8954
  | 167 => 0x9512
  | 168 => 0x8992
  | 169 => 0x151292
  | 170 => 0x128992
  | 171 => 0xe9692
  | 172 => 0xed692
  | 173 => 0x1692d2
  | 174 => 0x105812
  | 175 => 0x105992
  | 176 => 0x181312
  | 177 => 0x199352
  | 178 => 0xcc9c99a
  | 179 => 0x138c
  | 180 => 0x129512
  | 181 => 0x1289d2
  | 182 => 0x138d
  | 183 => 0x138e
  | 184 => 0x12c992
  | 185 => 0x94a16
  | 186 => 0x104ece9a
  | 187 => 0x104e8eda
  | 188 => 0x1a9954
  | 189 => 0x2c155
  | 190 => 0x28e
  | 191 => 0x2cd
  | 192 => 0x29316
  | 193 => 0x2d355
  | 194 => 0x2cd55
  | 195 => 0x28d16
  | 196 => 0x2da15
  | 197 => 0x2ced5
  | 198 => 0x2da55
  | 199 => 0x75052
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1829
  | 6 => 5131
  | 5 => 1949
  | 4 => 229
  | 3 => 67
  | 2 => 6
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (74981+((h/609+packedAt gbK7 (67673+(h % 609)*12) 12) % 2195)*12) 12
  | 6 => packedAt gbK6 (268518+((h/1710+packedAt gbK6 (246288+(h % 1710)*13) 13) % 6158)*14) 14
  | 5 => packedAt gbK5 (122779+((h/649+packedAt gbK5 (114991+(h % 649)*12) 12) % 3111)*12) 12
  | 4 => packedAt gbK4 (16714+((h/76+packedAt gbK4 (16030+(h % 76)*9) 9) % 302)*9) 9
  | 3 => packedAt gbK3 (5581+((h/22+packedAt gbK3 (5427+(h % 22)*7) 7) % 81)*8) 8
  | 2 => packedAt gbK2 (560+((h/2+packedAt gbK2 (552+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f1f80f861c3f8fc07f8e03fffc842661330ff
  | 1 => 0x87e3ff0781fc3f1ff83f003838108db86dcccc
  | 2 => 0x7fc0007fe003fe0003fffc03fe731c18e0f0f
  | 3 => 0xf8000007ffffc000003fffffc0383e01f00ff0
  | 4 => 0x7ffffffffffc00000003fc001fff000
  | 5 => 0xfffffff80000000000000000003ffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x9048210004048241088200888800022011055
  | 1 => 0x83210e1180c4190870b90191918004a8254ccc
  | 2 => 0x6481422a2003240a1124a80270311c08e050a
  | 3 => 0x5000284555aa80014224952700382e01700aa0
  | 4 => 0x400040867933249387000602023dc001daa000
  | 5 => 0x649270e01022000204001804043efb54000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36420
namespace PEqualNP.Outside.L_meta_36420
open PEqualNP.Outside.L_meta_36420.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 2 := bs0_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 14 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_96 : Interval s1Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_128 : Interval s1Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_160 : Interval s1Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_192 : Interval s1Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_224 : Interval s1Atlas 3 224 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 228 := (concat (concat (concat bs1_3_0 bs1_3_32) (concat bs1_3_64 bs1_3_96)) (concat (concat bs1_3_128 bs1_3_160) (concat bs1_3_192 bs1_3_224)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_160 : Interval s1Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_192 : Interval s1Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_224 : Interval s1Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_256 : Interval s1Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_288 : Interval s1Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_320 : Interval s1Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_352 : Interval s1Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_384 : Interval s1Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_416 : Interval s1Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_448 : Interval s1Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_480 : Interval s1Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_512 : Interval s1Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_544 : Interval s1Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_576 : Interval s1Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_608 : Interval s1Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_640 : Interval s1Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_672 : Interval s1Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_704 : Interval s1Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_736 : Interval s1Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_768 : Interval s1Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_800 : Interval s1Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_832 : Interval s1Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_864 : Interval s1Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_896 : Interval s1Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_928 : Interval s1Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_960 : Interval s1Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_992 : Interval s1Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1024 : Interval s1Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1056 : Interval s1Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1088 : Interval s1Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1120 : Interval s1Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1152 : Interval s1Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1184 : Interval s1Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1216 : Interval s1Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1248 : Interval s1Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1280 : Interval s1Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1312 : Interval s1Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128))) (concat (concat bs1_4_160 bs1_4_192) (concat bs1_4_224 (concat bs1_4_256 bs1_4_288)))) (concat (concat (concat bs1_4_320 bs1_4_352) (concat bs1_4_384 (concat bs1_4_416 bs1_4_448))) (concat (concat bs1_4_480 (concat bs1_4_512 bs1_4_544)) (concat bs1_4_576 (concat bs1_4_608 bs1_4_640))))) (concat (concat (concat (concat bs1_4_672 bs1_4_704) (concat bs1_4_736 (concat bs1_4_768 bs1_4_800))) (concat (concat bs1_4_832 bs1_4_864) (concat bs1_4_896 (concat bs1_4_928 bs1_4_960)))) (concat (concat (concat bs1_4_992 bs1_4_1024) (concat bs1_4_1056 (concat bs1_4_1088 bs1_4_1120))) (concat (concat bs1_4_1152 (concat bs1_4_1184 bs1_4_1216)) (concat bs1_4_1248 (concat bs1_4_1280 bs1_4_1312))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_64 : Interval s1Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_96 : Interval s1Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_128 : Interval s1Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_160 : Interval s1Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_192 : Interval s1Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_224 : Interval s1Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_256 : Interval s1Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_288 : Interval s1Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_320 : Interval s1Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_352 : Interval s1Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_384 : Interval s1Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_416 : Interval s1Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_448 : Interval s1Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_480 : Interval s1Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_512 : Interval s1Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_544 : Interval s1Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_576 : Interval s1Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_608 : Interval s1Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_640 : Interval s1Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_672 : Interval s1Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_704 : Interval s1Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_736 : Interval s1Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_768 : Interval s1Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_800 : Interval s1Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_832 : Interval s1Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_864 : Interval s1Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 890 := (concat (concat (concat (concat bs1_5_0 (concat bs1_5_32 bs1_5_64)) (concat (concat bs1_5_96 bs1_5_128) (concat bs1_5_160 bs1_5_192))) (concat (concat bs1_5_224 (concat bs1_5_256 bs1_5_288)) (concat (concat bs1_5_320 bs1_5_352) (concat bs1_5_384 bs1_5_416)))) (concat (concat (concat bs1_5_448 (concat bs1_5_480 bs1_5_512)) (concat (concat bs1_5_544 bs1_5_576) (concat bs1_5_608 bs1_5_640))) (concat (concat bs1_5_672 (concat bs1_5_704 bs1_5_736)) (concat (concat bs1_5_768 bs1_5_800) (concat bs1_5_832 bs1_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_32 : Interval s1Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 44 := (concat bs1_6_0 bs1_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
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
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 6 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 66 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 42 := (concat bs3_5_0 bs3_5_32)
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
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 5 := bs4_2_0
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
theorem bs4_4_64 : Interval s4Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 91 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
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
theorem bs5_4_64 : Interval s5Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 91 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 6 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 67 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_224 : Interval gbAtlas 4 224 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 229 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224)))
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
theorem bgb_5_1920 : Interval gbAtlas 5 1920 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1949 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928))))) (concat (concat (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152))) (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664))) (concat (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792)) (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920))))))
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
theorem bgb_6_5120 : Interval gbAtlas 6 5120 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5131 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)))))) (concat (concat (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))))) (concat (concat (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528))))))) (concat (concat (concat (concat (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)))) (concat (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))) (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168))))) (concat (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488)))) (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648))) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)))))) (concat (concat (concat (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968))) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)))) (concat (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288))) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448))))) (concat (concat (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608))) (concat (concat bgb_6_4640 bgb_6_4672) (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)))) (concat (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928))) (concat (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024)) (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120))))))))
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
theorem bgb_7_1824 : Interval gbAtlas 7 1824 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1829 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768)) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896))))) (concat (concat (concat (concat bgb_7_928 (concat bgb_7_960 bgb_7_992)) (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 bgb_7_1120))) (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 bgb_7_1344)))) (concat (concat (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 bgb_7_1568))) (concat (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696)) (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 32, 34),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0fefefeeefeeefaa0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124270 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36420.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.and,[0,3]⟩,⟨.or,[3,6]⟩,⟨.or,[4,5]⟩,⟨.or,[2,9]⟩,⟨.and,[0,10]⟩,⟨.and,[1,9]⟩,⟨.or,[7,12]⟩,⟨.and,[2,8]⟩,⟨.or,[13,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36420

open PEqualNP.Outside.L_meta_36420 in
theorem PEqualNP.Outside.L_meta_36420 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
