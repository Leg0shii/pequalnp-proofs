import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36298.Model
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


end PEqualNP.Outside.L_meta_36298.Model

namespace PEqualNP.Outside.L_meta_36298
open PEqualNP.Outside.L_meta_36298.Model
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

def SBf (j : Nat) : Nat := [6, 6, 6, 7, 8, 5].getD j 0

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

end PEqualNP.Outside.L_meta_36298

namespace PEqualNP.Outside.L_meta_36298
open PEqualNP.Outside.L_meta_36298.Model
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
end PEqualNP.Outside.L_meta_36298
namespace PEqualNP.Outside.L_meta_36298
open PEqualNP.Outside.L_meta_36298.Model
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
end PEqualNP.Outside.L_meta_36298
namespace PEqualNP.Outside.L_meta_36298
open PEqualNP.Outside.L_meta_36298.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xa62048000000bf43bd43ef42ec42ee32ed32
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x2029aa6216350d32
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
  | 4 => packedAt s2K4 (104+((h/2+packedAt s2K4 (96+(h % 2)*4) 4) % 10)*4) 4
  | 3 => packedAt s2K3 (56+((h/1+packedAt s2K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x81fffe07ffc1fc1ff0ffc1fff07fc0fd38fe73
  | 1 => 0xfe07fff81ffe0fe0ff0ffe0fff83ff02cf1f9c
  | 3 => 0xfff83fffe0000fff000ffff0fffc00030fe3e0
  | 4 => 0x3ffffffffffffff00000fffffffff003ff
  | 5 => 0xffffc00000000fffffffffff00000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xac108231448a44053012c85532154258186e31
  | 1 => 0x4b10450c90854a051054a46529196084b1694
  | 3 => 0x1863a8a283ad6d6b0889ad64eb590c330da3e0
  | 4 => 0x5144310412210a528aa021008c6228a3a0014a
  | 5 => 0x618621c71c318b9cecce3188084030c3f6d800
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee88eeee0000eeeeee88eeee0000eeeeee88eeee0000eeeeee88eeee0000eeeeee88eeee0000eeeeee88eeee0000eeeeee88eeee0000eeeeee88eeee0000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36298
namespace PEqualNP.Outside.L_meta_36298
open PEqualNP.Outside.L_meta_36298.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x5872e0001c2429485204d38100a8a9d00844801e892004c7c020508c4251a0000018b08800000f19061968230ac000085001a1c58d800c0340182000041080100ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xaa006e7a5414c2869c3e647018005ebe8200028c0000007c000a00003c00006c56389a3a325a7440a6a41cba0c006200000e247e280030007626b0a800a03498bc94125c885268962eb20816424ab8b6921ac0acc44684724c2c00aea2004490108e50600004588a066a4e2a1e2000669e8022b4483678043c11634003324418480080012e255419106003020a18181721422c1f3e51d0e7aa921db94a43b6a9487775150ee8a2a1e7d4d43dba8a873c5150f68a2a1cd145439f2a0876e5210edaa421d794c42aea98853e54cca7aa9996750f32b6a9c65af438cb5a87196750d32e7a9a65af434cb9c86996b50d32e6a1a658d434ca7ca8194f55032b7290653d539075c6520eb4ca419f28c833d531075c6420eb4c8419f28883b6511067ca998cf55331b7296636d52cc7688398cfd52319e2a463cd328c67ea898cf151319f2a0633d540c6dca418db54831e699063b4410c6f4a018de540319f2a6433d54c86bca790d754f219faa2433c54486eca3205d54640b7a92816c525027ca9984f55330b7296616d52cc39a6598734c9309f2a0613d540c2dca4185b54830bb2886175510c27ea8904f151209f2a0413d54082bca6105754c20bb2884175510836883884f952109eaa4213f5444278a88857d4d10ae29a216f52442d8a4886d10510
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2a688000001c31890000009a78001000e2000120140000161840200280000c200000026946150f32a9185438ca946150d32a3592434caa46150d32b1185434cb876150d32a3185434cb846150d32a1185434cb0d534c841c3d51328c70d544c8318d594410c7853210431d24c9500c73041540319358c52502346155330c355132cc3145310510
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x88000605654c8410c78099082a8063411c5544cb30
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 4 => packedAt s3K4 (2904+((h/33+packedAt s3K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s3K3 (840+((h/7+packedAt s3K3 (798+(h % 7)*6) 6) % 42)*6) 6
  | 2 => packedAt s3K2 (150+((h/1+packedAt s3K2 (147+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fff07ff87ffe0ff0ff87fe1fc0fffd31f33f
  | 1 => 0xf81fff81ff87c3f0ff0ff87fe1ff0702ce7dcc
  | 2 => 0xffe1fffe0007ffff000fff8ffe0007ff0f8e0f
  | 4 => 0x1fffffff803fffff0000ffffff803f00ff0
  | 5 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x5040111440810002301280920242514810b115
  | 1 => 0x12c4230c900a0450510588262096121846554c
  | 2 => 0x218d44283554a2b50889550d540c24b30b0e0a
  | 4 => 0xa51188412440ab298aa044099928a023a00aa0
  | 5 => 0xc6190e71c66733ceecce66411030c0c3fde000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeee8e8eeeea0a0eeeee8e8eeeea0a0eeeee8e8eeeea0a0eeeee8e8eeeea0a0eeeee8e8eeeea0a0eeeee8e8eeeea0a0eeeee8e8eeeea0a0eeeee8e8eeeea0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36298
namespace PEqualNP.Outside.L_meta_36298
open PEqualNP.Outside.L_meta_36298.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x386c019000000a003098e0068e80000079100400000c90a02427800552494000058f970000001000000000806a60094480009c0004600587080c0000020c220000a8000000008002080020210005020000aff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41f741fe41fd41fc41f441ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x681bf42d037a85a05f94740bea8e81f741d03e883a05f55240bf29c81de53902bca7205f54e40eea9c815d53902fca5205f54a40bf28c81f651902eca3205f54640faa8c817551903ee83206f90640de20c81f4419036883205f94240dfa0481fb40902fea6a05f14d40bfa92817c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a817451503ee82a07d10540fda0281be40502fca8205f94c40bea98817e52102faa4205f94440bea8881f7411037c82206f10440fa20881b441102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a99877d0f30ee21e617e52cc2faa59877ccb30ee996617e51cc2faa3987dd0730fa20e61df31cc3ba63985fd5230bf2a4617d548c2f8a9185f54e30bf294617d528c2fca3185f54630fba0c61f4418c2fca1187ed0230fc20461df308c3f661185fd5130bf2a2617d544c2f8a89877d0d30ee21a617f524c2f8a49877cc930ee992617f514c2f8a2987dd0530fa20a61df314c3ba62987ed0130fc20261fb304c3bc60985fd5030bf2a0617d540c2f8a8185f94c30bf290617d520c2fca2187d94430bb288617d510c3eaa2185d54430fba0861f4410c2fca01877cc030fd18061dd300c3f26018764c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83ee83907d10720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c41f741883e883105f94220fd18441f930883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20bfa8a417c51483ee82907d10520fd18241f930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2107dd0420fa208417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fba0e21f441c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e50843f461087e4c210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ee82887d10510fb18a21f531443ec42887d48510fd18221f930443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52042faa4085f14810bf28821f741043e882085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5410afca6215f54c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9995f55332be2a6657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a8997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cbbe86197710c32bf29065df320cbdc6419774c832f6990657e510cbeca2195d94432bea8865f5510caeaa2195f94032fd280657a500cafaa0197e54032bca80657e53d06faa7a0df94b41bea96837e50d06faa1a0fdd4f41fb29e83f553d07e8a7a0fdd0f41fb21e83f543d07e887a0fdd4b41fb29683f552d07e8a5a0fdd0b41fb21683f542d07e885a0fdccb41fb19683f532d07e865a0fdd4341fb28683f550d07e8a1a0df55241bf29c837d539077c8720ef10e41bf294837d529077e8520ef50a41bf28c8376519077e8320fdd0641bf284837d50906fea6a0df14d41bfa92837c52507ee82a0ef90541bfa82837c50506fca820df94c41bea9883be43107788620df94841bea9083bf421077a8420df94441dfa0883f6411077a8220fd50441bf280837d50107eca820dd95041db2a083f753107eca620fd54c41fa29883f743107ec8620ed90c41faa1883f443107688620fdd4841fb29083f552107e8a420fdd0841dba1083f642107ea8420ed50841fa21083f732107ec6420fd4c841fa19083f750107eca020fd54041fa280837f54cc6fca998df55331be2a6637e52cc6faa598fdd0731fa20e637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31bf294637d528c6fca318fdd0631fa20c63df318c7ee6318df94231bea84637f544c77ea898cfd5131bf2a2637d544c6f8a898ef151319e2a2637f524c6f8a498fdd0531fa20a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863f7410c7e88218f7cc431fb18863dd310c7ea6218df94031fd280637a500c6faa018fe54031bca80637f54c86fca990ef953219f2a6437d54c877aa990cf55321be2a6437f53c86fca790df54f21be29e43f741c87e88390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52886fca310fdd0621fa20c43f631887ea6310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdd0521fa20a43f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843f741087e88210fbc8421fb10843ed21087ea4210df94021bea80437e53d02faa7a05f94b40bea9
  | 2 => 0x74989d80014e0000109b06000011c4012c0003cc0017700063144124000001421b40940f8c00004002112f0000004b86500006e8c0628000000000000005a48000260320470e02b10020013f1912ac520819254fe3e4b09e5418a3c000000000013a0ee02a8148d2380000000012a1de488000290000000000f000530dd80000000000000000308888002d6a290187d33a000280000005340024a3b800000000512000ba82e000000aa00035aa3851a722f8000f11df0000013213b19e000ea9c356800006800014678000d518e7bc258223c6000ada0d53c0e1091cc000a0cc500012a224269ee38e7ad4e0ae4b44a14e800466000000000001c50200000000000068000870000000000000016d1d0ac88228c000000001530000004782f0000000000000024c0002310e001008e1000a54000450008f82785b45a0ecbd0001fc3b09e0004f055543963196501310990cc908e4a734dc190d880056c55c89172000ab8ed10e504710969fc02c5a4001a3000000000000006fc780003c24983f964558435229bd26a0020040280b0000040080000e0280100000000c00800000008028010000000080000200000806000020000000100040080800a00804803010008010070060180080000000c00000008014000000080140100101400000000002000008020060400000100a014000010000000380900002001000002008000040020040480f0000100100000c00c0080000000400000020030000000000000000100000c008050040100000500200801000000000000000040000000200000400800006000010000020080000001400000800002018008000060040080300000400007000004020000000040000100200001000000004000000000100780300a0000000e002000038000040000100b0040000300200400c00804000000010000060000580500000000000002014020000000000100000200c068010020080000e0040040300200b7e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190feca321dd94643bea8c87f55190eeaa321df94243fd284877a5090efaa121fe54243bca8487df4350f7c86a1dfd4943be292877f5150feea2a1ddd4543be28a87f45150ee8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42dea1e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42bf29485bf4290bde85215f94642fb28c85765190afaa3217d54642baa8c857e5090afaa1215fd4d42efa9a855f5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150beea2a15dd4542be28a85f45150ae8a2a15fd4142fda82857b5050af8a0a17e14142bc282857
  | 3 => 0x8b7000000001d9086000010003b65809c8274f695400000024000de29b30866c5f9d7232aa8b613d0aa0d8861c2000000071b00fcabd21a5c39e0014d1aa53269c00000520000000000000004400000a0000000000081d540000006dc458004321e04128630c3900001000000048000456000be8000002887e2250a6598c486d47a000000000006ac631710560000000022e99c001e000000000000000000fa8000004c0bf0000009945224646c454001ff1144080019939a0000000000000000000000000000002749342c856370000001f0000000cd0000009c40000025e000000c8082111530003da93d529761640190ba473fa5e0d48fb00030518a7c000078001930980004da16000000580cc4365440027a316ae4000b11a8000000005283980000000047c3c80000000159a394de0703b9ac0000003d8000000000011d294920ce18d00088ca1aa74cc000f480038c0002e00c000000000000000008c0000000010f000000000d10a61803f5258001fe27c00000000000000003fca441f840000000001104640001a8000301e8000005460002486a0ce0000000001600000000000000569a14fa000000b910a6a00000016a0000006e0000004e0000000000000000065c0414f302358000001b4504599083e416949a0f0000d0002701684183a8001da324000004b236c160003cc704000003304c4a9000412a91468dc0321bc0006c00000000092000001170000000000008320e0012980004c388000001861891797b000258001a6000000000000003641c9470000000000003a74cc18760008d07a14226600055800154000ad0002285940a020422a493511e33e0004e9b51ce044001dd00000000000000001341490003dcd99820000012b0d738a000000a030e34000000000000180df5162ec538001d4000000a91c0840000000000011d8e50ba72c000000008dc0000000000000052000000a2000000000f4000000000000480d61082c0005600006200000000000000000000000004260a00015f000178000001d6588fb8000002a0958003d40000000047411800218000000000e917423410a2400000000000000a0478a613409a400000000000150000001a4000fa00000000000000000c92443e8000b40003f40000008c000000878000000011600021600000000000ad40023c16c1440005f45400043000000000198724d8348d20ce2120009f000000000000000e85b95b800374000000000003e14b2282f2564fc9f846a4292b8940742600016f19a4043198f000621209214a80006ea220003d92f8d13a8728af0f20c24fc47000000818001f6000000489290000012d800000880a58000e60006c00000000000000000001511580000c91f8000ca204df07c0000012900000000000031000001249d20002f80012735e0000396
  | 4 => 0x1a53c8570ec26b3649380011b41474050a1543448cd70af3a2000002750004e00002426879cfd9ce00089800000500000001d648000000105264000c70004420000003d000000000bd2e6000bf99600087d2809e0001500000045215c00000000820000004c60007aaad43a0000000002e000898000006d9502514160014b8a504a4585e145000000000003e600c2729f0e00010a0000005a800000404000f8a580000005c0000009e55595057425c000004ba00000000000000000e30006500da775520004d0000000000010032a3790717428cae00983c54207c699de000000c29ec0000000000000089c0029850a00000000000000000000002b0e400026e00004800000574001b92e006936
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4410c3375410430cd150410c35551cc030b658e300c371518c03097d95300c355514c0309ed95300c371514c030b6d95300c35b654c030d6951300c358544c030d6549300c3d2514c030d6545300c3d1514c030d4545300c3d3414c030f4105300c27661d53209d58754c825f63553209718d54c827761553209d18554c823e6414f208f59053c82766114f209d58453c83365410720cd55041c83b041103209798f548825d63d52209d987548827561d52209dd85548827461552209d98453882756114e208fd91518823c6454620cdd5041883345410620d614d308827661d51209d587544825f63551209718d544827761551209d185544827b60551208fd91534823c6454d209dd8553482746154d209d98453482756114d20cdd50414833454105209e1953048358534c120ba189304825e63d50209758f540827661d50209d587540823d6595020cdd86540833461950209dd8554082746155020cdd8554083346155020ce181540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c209e98053083365494420cd55251083565394420d554e51082766494420cd95151083355454420d594d510835553544209d191510827765d04209d597410833654d0420cd553410835653d0420d554f410827765104209d59441083365410420cd55041083565310420d554c410833954d0020d654f40082796510020d654c40082e96210020ec104400835953880209bd95200827b6548020d654d200823e6494b108f59252c43365410710cd55041c42b4644c7109798f548425d63d52108f993538423d64d4e108f990528423d6414a109798c528425d6314a10cd95341843345410610d614d308433561d51108f992544427761551109d184544423e6515110cdd84544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524427665d0510cd15341442f260d0510cdd5041443345410510cd1523144274654c510ad1913144334544c510cd15221442746548510cd15121442f06048510ce1523044278654c110ce1513044358534c110f44c5304433454841109798f540425d63d50109d987540427761550109798c540425d63150109b988540426d621501097596530425e6314c109d984530427a6014c109798f520425d63d48108f990520423d64148109798c520425d63148109d984520435653d0410d554f41042756510410cd95041043565310410d554c41042f16010410d554f10042796584010d654e10042776544010ad191100435553440109ed9510043595344010
  | 1 => 0x6b464cc841ad99232106b5648c841e510e32106b7644c841ad1913210676650c8419d59432106b6640c841ad5903210794430c841bc98032106f1600c841b598c50106d56314041b998850106e56214041dc540501067a60d53319e58354cc73654d0731cd15041cc63e6494a318f592528c7365410631cd550418c73561d51318f992544c67761551318f994544c73761151319d997414c73454d0531b598f414c7375410531cd150414c73454cc5319d987540c67a60d50319e583540c66e62150319b588540c67a60150319e580540c6756510431cd950410c6d5631043197d95310c677654c431ad191310c7734194031dc106500c7734154031dc105500c75b3154031dc8c5500c7593154031dc4c5500c7376195321cdd8554c863e64d4f218f59353c863e6414f218f59053c867a6014f219e58053c873654d0721cd95041c873554107219798f548865d63d52219e983548867960d52219e98053886796014e21cd95041886b4644c621ad993218865f63551219718d544867761551219ed81544867860551218fd91534863c6454d219ed8153486786054d219e98053486796014d219d997414873454d0521b998b414873654105219d19531486b4644c521d514d31486b664c85219798c504865d63141219d987540865e63150219758c540867a60150219e580540863e6414c218f59053086766114c219e98053086796014c218f992520863d64948219d59441087365410421cd55041086e562104219bd95210867765484219d98653d02756194f409d98652d02756194b40ae18142d03565394640d554e51903565354640d554d519035653d0640d554f419031e5390640c794c41903355110640d594c41903555310640ad59441903356510640cd94c41903965310640c594c41903955310640cd548419035953d0240cdd08515033542145409d99741502766510540cd14640502b66190440cd94c41103355210440ec98041103b16010440cd10650102d96390040ec106401023f6550040ad185401027b65500409d98754cc27561d53309dd8554cc2746155330cd95041cc3355410730e510c41cc29c644c7309d987548c27561d52309dd85548c2746155230cd950418c3355410630ec104408c27661d51309d587544c26f62551309b189544c27761551309d185544c25e65d0d30b6983434c23e64149308f590524c27661149309d584524c34c524c930b6181324c3375410530cd150414c3944310530a7191314c2d8604c5309e997404c2da63d0130ec104404c25e63d50309d987540c27561d50309e983540c27761550309d185540c26e62150309b588540c27661150309d584540c27664944308fd91510c23c6454430ad191510c33764544309d191510c33464544308d191510c27765d04309d597410c27765104309d59
  | 2 => 0xd06c010000101c5d01812088070000a02802004040040e02c0102401018010340000400010010040100001004000440c0180d000010200b0000304801034040002501401000010180101008000000000b0181a000020140e008030000103c06004009d98652d0e756194b439d98650d0e756194343dc9465090f715194243dc9455090f715154243d6d0d5090f364314543b65824310e3f6550c43ad1854310e5f6550c439d98653d0a756194f429e98253d0a796094f42ad18543d0a5e63943429758e50d0a7661943429d58650d0b374294642c714f4350ab46150d42ad9864250b5753d4542d514f5150b575314542d514c5150b5b53d4142d614f5050b7351d4142dc1475050b5b5314142d614c5050b735114142dc1445050a3f65508429bd954210a7661d53329d58754cca7a60d53329e58354cca7761553329d18554cca3f64547328f19151cca7661d52329d587548ca7761552329d185548ca7b60552329e181548ca7661d51329d587544ca5f63551329dd85544ca7461551329ed81544ca7860551329d984504ca7561141329d987540ca7561d50329e983540ca7960d50328f596540cb376195032cd186540ca7761550329d185540cb1c6355032cdd85540cb3461550328f990540ca7661150329d584540ca7a60150329e580540cb1d54d0c3297594430cacd6210c3297d95320ca6f654c832cd952510cb3554944329d992510cb365454432cd551510ca746454432ce952500cb395494032dc946500cb715194032ce951500cb395454032dc945500cb715154032d6d0d500cb584354032d6cc9500cb5932540329e98253d06796094f419798e50d065d6394341d5d4e53d06f26094f41bc58253d06f26090f41bc58243d07675294b41b5d8d42d06d46350b41bcd8142d06f06050b41e950842d0676650cb419d59432d06b6640cb41ad59032d06f2600cb41bc58032d06d66394341b558e50d07735094341ae982439069c6350a41cb94942906b86050a41ad58643106ba6090c41a718d42106b76150841ae181421063f65504419dd9541107366495041ad98e54106b56295041ad98254107555314c41b998853106e56214c41bc98053106f16014c419d59643106f26090c41bc58243106b56590c41cd59643106b66390c41ad58a43106b66090c41ec98243106b26090c41ec58243106776550c41ad98c43107966310c41e594c43107955310c41ad58843106b66010c41b598c52106d56314841d954852106f26014841bc58052106b663d0841e994b42107a552d0841ad98342106756590841ad59242106776550841b5d8d42106d46350841bcd8142106f06050841add9542107376550841e5d8d42106b46350841e518d42106946350841e9d8942107b36050841ad18142107b06050841ac18142106b66410841add93321
  | 3 => 0x400045000480218703707e09d92100004c348000280005700036e36c839b533a3388a8fd356000c90001fe3e00000044c11cac000000398a80953581391d9ec2da000001253400010a000000000000000008a4f59040a4000002620e45c8000004d644c000b30ee00063a682348850802e1b26f43e0003a0118b10053f40011b88b0002bc9f9ee000274000163b0000bc099338110c69c63904982994633054c058ec2209606602f2c64087798b400394198b612e5cd0d8640322c0e025f2b400119054000874cd9d20002686c0002e882ca716915026d231230826591c80030600000000000000aa8000000005010c0000000000005a0009c99f3e40003a8000007c4d78d148857000189000204f816714e0003584f2c2000000000981e8b21a1044160c29374c04d8000c03ec3d4001810006cc000003d02c51691b2d66f0000ad2f8690e380022e93ca280027c7d477216000548329c9000804bc9ce00c0008c1301b84c89a0001d02249a90000012c00000462034eb1bf1fc1b47b0001ce72c3c800000334460da4308b80e26c0180011b2090ac2d1211423ba3e8050c23b82a4000000000004f10621c134000002546f8000000007b4b0000492200680000009200007e4260006a0000a292c3386e1d4559038c3000000e7a230d0000379164c25749123f3a600000000480288000000ae40c001933ee83c000f244e0f0000002163cca42472ea0000f000454228d700017807c558cb14c49cbb2570548acfc93802a968002334146c4001954a80005f9822cc0f51f03435223400000328000630000008100020e1c005cc811f3182180d9cc146420b78014a60000021c3c25500007b000000968002bc000d30630000745280000051cdd8a42320012e800000000000000007f4a0a1a3e8750db02139a7442f266274904000ca000001229e71d6849368004e20004f86000016c13031410314a2073052000f28002d4168c70000e80011c0002e0000000de2483c10a86a3945283891d2120000000000083125228458844e09b00103a45f1aa4ca99c158181e80f8ef8ed43e890cf0b71f8000078aa0008f528000000530000000003900016e1260c0000404442844180009408000000000000138f71a60d8970d62780006b8000008e8411fc0005e8e2000000470bf0e30005ec7887833209000177384534711710fe834ed16c02406c0201c1100000084030000300c090180000402028000040400408000440100e0080001407018000500c0000b01c0001c27014050100f0001c008000000302c0e04c0001405020050b01b000000001306c140000100c160001e01400000000140100c1700801000090ac010ac060000000c01004000000f01803004000000009c0e0081601c1b00808028000280900401000080180300c04030030040405401000
  | 4 => 0x12f0bd40c4282aa521744444221e00643c002174d28bcda1d70fa1b003a022ca9a87d94332e57d019a30724789997f3de8d07ca302a2044691ff4a2039379ba06a5a06e8663b64a4d11910088944714b4982703b0c12ae618c38983fc4bc000000004505a90d256384cd092224250808090000b0f30000000000015926200067838000001100b8000000241c3000310961de0002212b000000140d92433d43212d9d92b64a04b14f314500f182310a109270b20042b0f20252fa600080c92921851a8df0c4954439ad27a965381051226a12e1e011e174eaa050507ccf11fb49a990001c5478864482634dc6200d03f3086e4d28003d20c8001a70b82ec1b8591723540003b0000002f83a00063c0000000012
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x18000e1d9680131f001089000e8c800d00001d069880000000111b0012088a828a248703808615819fa5011a8b9721119e19878c1c0f09979a000800000f841923a0000585140b0014a422800da221938023001ca09612950000000002001b901e8004830a0a000458002000151a200000000100000c08302a00c3474584504cb0a318c2aa065525c84354032ca6a6b04a7a0e5163d4250d0659384c72a083259ce6095041c8aa6b10a620e515358053106c8b84c6218839158d5214841cc2a4b00a420cb27098f421064b39cc1a1083a418f6050841d26c63028420e90631814210659386c9990832c1c1648c84192aec2186420e156510c32106c2b908619083a410d600c841ca2c6a80a020e6162540501070a2a4c7a0a63345c263d0531aa2e620aa018d30744c5500c70a320a698a43545c0534c521d22c620c80204d171983434c268b88c099261345c663d0130a2ce7aa0821853270d50410c292b90a820861451d151cc030a60e8a8c601851474545300c2983a2a298061525c8544c030aa2e22a2601851874545300c2c83a2a298061c4dd1514c030aa0e8a8a601871074545300c2883a2a29806154dd7414c030aa2ea20a601871054105300c28a39aa820e410d1d16114e20a2ce7aa083105517114d308821a3a2c229a41545c4534c120c60c2302a810649535884008298ba882200418c5944110020e22a620880106a16210440083182a4c1a0a21345ce60d0510868ec2a26288630541812144268b98c090a21541d5314c110b20e898a6088710544c53044328a9ac020821851915344010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1ca05258042c6430800004000021c05655c8430c841a818210d600c841c10545c263d0531c10645c0534c521890845c4604c930b0182150414c030910845c4534c220910845c4534c120c21755884110020e01535884110020c10545ce60d0510c10545cc604851091087151314c110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
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
  | 6 => packedAt s4K6 (770+((h/14+packedAt s4K6 (672+(h % 14)*7) 7) % 80)*7) 7
  | 5 => packedAt s4K5 (21436+((h/233+packedAt s4K5 (18873+(h % 233)*11) 11) % 1226)*11) 11
  | 4 => packedAt s4K4 (25868+((h/208+packedAt s4K4 (23788+(h % 208)*10) 10) % 827)*11) 11
  | 3 => packedAt s4K3 (3850+((h/25+packedAt s4K3 (3675+(h % 25)*7) 7) % 100)*8) 8
  | 2 => packedAt s4K2 (800+((h/4+packedAt s4K2 (780+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe0ffff03f87ff078fc3fe3ff8781ff91c7e4f
  | 1 => 0x3ff03fffc007e1f80ffc3fc7ff801e01e39f8c
  | 2 => 0x3fffc0fffffffffff0003ff87ffffffe03e3ff
  | 3 => 0xc00000fffff801ffffffc0007fffe007fc03f0
  | 5 => 0xffffff00000001ffffffffff80000007fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x92a284118929490182d14a0aac4892d10c2e45
  | 1 => 0x94658a2287328b38055516435cc1543161978c
  | 2 => 0x80112441204004a100024901112492202c09a
  | 3 => 0x114a2c892420cd94a999800266659045b40360
  | 5 => 0x218c300e384710e74e22392400060186db7800
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee8fee8f0a0f0a0fee8fee8f0a0f0a0fee8fee8f0a0f0a0fee8fee8f0a0f0a0fee8fee8f0a0f0a0fee8fee8f0a0f0a0fee8fee8f0a0f0a0fee8fee8f0a0f0a0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36298
namespace PEqualNP.Outside.L_meta_36298
open PEqualNP.Outside.L_meta_36298.Model
def s5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (6+((h/1+packedAt s5K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe1ffc3fc1f87fc38f0fe3f81ff0f03fe4cce4f
  | 1 => 0xfe0ffc3fe00787c0ff0fc7fe0ff003c073738c
  | 2 => 0xfff0003fffffffff000ff8000fffffff8383ff
  | 3 => 0x3ffff807fffff000000ffffc01fc03f0
  | 4 => 0xffffffc0000007fffffffffff0000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x24a12604c129240834520a8465891254444645
  | 1 => 0x4c62a24847322cc05546431c2b982a8c51538c
  | 2 => 0x804488910a040151000c90288222492883809a
  | 3 => 0x198b3322942336aae66002514cccb2117c0360
  | 4 => 0x110c000318444334888924618000c021aaa800
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xfeeef0a0feeef0a0feeef0a0feeef0a0feeef0a0feeef0a0feeef0a0feeef0a0feeef0a0feeef0a0feeef0a0feeef0a0feeef0a0feeef0a0feeef0a0feeef0a0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36298
namespace PEqualNP.Outside.L_meta_36298
open PEqualNP.Outside.L_meta_36298.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c180017fd50057f54017f95005fd54015f55005fc54007fd4c03fe53007f54c03fc53017fd0c03fe43017f50c03fc43007fd4801fe52007f54801fc52017fd0805fe42017f50805fc4200ffcc801fe32007f4c803fc32007fd4401fe51007f54401fc51017fd0405fe41017f50405fc4100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc21007fd4001fe50007f54001fc50017fd0005fe40017f50005fc4000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42004ff08210027fe2108013f71084007fd8842000ffd9510005feca880037f65440013fb2a2000ff99510005fcca88003fd65440017eb2a2000ff19510005f8ca880037c65440013e32a2009ffd911004dfec888003bf64440015fb222009ff99110015fcc888027fd64440137eb222009ff19110015f8c888027bc64440055e3222009ffd511004efea888027fe5444013feaa22009df5511004ff8a888003ff63440017fb1a2008ff98d1000dfcc688003fd63440017eb1a2008ff18d1000df8c688003ff5344011ff29a2000ff54d10047f8a688027ff4344011ff21a2009ff50d10047f88688003ff62440017fb122000ff9891003dfcc488003fd62440017eb122000ff1891003df8c488003ff5244001ff2922000ff54910007f8a488027ff4244013ff2122009ff5091004ff88488023ff3244001ff1922000ff4c910047f86488003ff5144001fba8a2003ff94510007faa28800ffc5144001fa28a2009ffd051001ffc8288027f64144013fea0a2009fd5051001ff88288023ff3144007ff18a2000fd8c510007fa6288003f53144007fe18a2000ffc851001ffc4288003f62144001fe90a2000fd4851001ff84288003ff5044009ff2822000ff54110027f8a088027ff4044009ff2022009fe9011004ffa8088027f94044009fe2022008ffcc110027fc6088003fa3044001fe9822000fe4c110027f86088003ff2044009ff1022000ff48110027f8408800fff1044007fd8822004ff84110027ec2088013ff65040097fb282004ff99410005fcca08013fd65040017eb282004ff19410025f8ca08013ff64040097fb202004ff99010015fcc808013fd640400d7eb202004ff19010025f8c80801bff540400dbfaa02006ff95010037faa80801b7d540400dfe2a02004ffd8c10025fec608013fe63040037f3182004f798c1000dbcc608013fd63040017eb182004f758c10005bac608013fc63040097e3182000ffd4c1002ffca608003fd530400bfe2982006ffd0c1002ffc860801bfd430400bfe2182004ffd8810025fec408013fe620400f7f3102004ff58810005fac408013fc62040097e3102000ffd4810007fca408003fd5204001fe2902006ffd0810037fc840801bfd420400dfe2102005ffcc810007fc6408003fd320400bfe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802003fe44010
  | 1 => 0xffc410801dff9884000ff8c420007fa621003bfc310800fff9084007ff8842003ffa421001ffc21080097f3004004ffd4020027fca010013fd5008009fe2804004ffd0020027fc8010013fd4008009fe2004004ffcc020027fc6010013fd3008009fe1804004ffc8020027de4010013fe2008009fd1004004ff48020027da401001ff92008007ffb2e2003bfd971001ffccb88002fe65c4007feb2e2000bf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc98800afe64c4007feb26200dbf5931001ff8c98800efc64c401bffaa6200ddfd531006ffca988037fd54c401bbeaa6200dff1531001ffec78800eff63c4007ff31e2001bf98f1001ffac788002fd63c4007fe31e2003bf18f10007fea788033fe53c4001fea9e200cff14f1006ffe8788033fe43c401bfea1e200cff10f1001ffec58800eff62c4007ff3162007bf98b1001ffac588002fd62c4007fe3162003bf18b10007fea588003fe52c4001fea962000ff14b1006ffe8588037fe42c401bfea16200dff10b10067fe6588003fe32c4001fe996200cff0cb1001ffea388003f751c4007ff28e2003ff5471001ff8a38800ff451c4007ffa0e2003ff9071001fec838800ffd41c401bfaa0e2003ff1071001ffe638800ffe31c4007fb18e2003ff4c710007ea638800ffc31c4007ff90e2003ff8871001fec438800ffd21c4001fa90e2003ff08710007fea188013fe50c4001fea862004ff1431006ffe8188013fe40c401bfea062004ff10310067fe6188013fe30c4001fe9862004ff0c310007fe4188013fe20c4001fe9062004ff08310027fecb08012ff6584009ff32c2000bf99610027facb08002fd6584009fe32c2004bf19610027fec908012ff6484009ff3242002bf99210027fac90802afd6484009fe3242004bf19210057fea90802b7f5484015ff2a4200aff55210056faa90802bfc5484009ffb1c2004bfd8e10027fcc708006fe6384009feb1c2000bf58e10027f8c708012fc6384001ffa9c200bff94e10007faa70802ffc5384015ffa1c200bff90e10057fa870802ffc4384009ffb142004bfd8a10027fcc50801efe6284009feb142000bf58a10027f8c508012fc6284001ffa942000ff94a10007faa508003fc5284015ffa14200aff90a10057fa850802bfc4284017ff9942000ff8ca10007fa650802ffc32840137eb0c2000ffd461001ffca308003fd5184007fe28c200affd061001ffc830802bfd4184007fe20c200bffcc61001ffc6308003fd3184007fe18c2000ffc861001ffc4308003fd2184007fe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fd2042004ff50210057f28108013fc4084009ff9842004ff8c210027f46108013fd3084001fc9842004ff0c210027fe4108013fe2084009fe9
  | 2 => 0x2003ff8a51004fff428800fff2144013ff50a2003ff8851004bff328800fff1944000ff4ca2003ff86510013ff6188009ff30c4003bf98620027fac310002fd6188009fe30c4000ffd4620007fca310003fd5188001fe28c4013ffd062009ffc831004ffd4188027fe20c4012ffcc620007fc6310003fd3188025fe18c4007ffc8620007fc4310003fd218800ffe10c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fd1844004ff4c220007f26110013fc3088009ff9044004fbc822003ff64110003ff65480017fb2a4000ff99520005fcca90003fd65480017eb2a4000ff19520005f8ca90047ff64480237fb224011ff99120015fcc890047fd64480237eb224011ff19120015f8c890047ff5448023bfaa24011ff9512008ffaa8900477d5448023fe2a24000ffd8d20005fec690043fe63480037f31a4000ff58d20005fac690043fc63480037e31a4000ffd4d20087fca690003fd5348021fe29a4011ffd0d20087fc8690047fd4348021fe21a4000ffd492003ffca490003fd524800ffe2924011ffd092003ffc8490047ee4248023fea124011fb5092003ff88490043ff324800fff1924000ff4c92003ff86490003ff61480017fb0a4000ff98520007fac290003fc61480077e30a4000ffd4520007fca290003fd5148001fe28a4011ffd052008ffc8290047fd4148023fe20a4010ffcc520007fc6290003fd3148021fe18a4007ffc8520007fc4290003fd214800ffe10a4000ffd4120027fca090003fd5048009fe2824011ffd0120027fc8090047fd4048009fe2024010ffcc120027fc6090003fa3048001fe9824000fe4c120027f8609001fff204800ffd9024004ff88120027dc4090013ff65080097fb284004ff99420005fcca100137e65080013f3284004ff59420005faca100137d65080013eb284004ff19420025f8ca10013ff64080097fb204004ff99020015fcc810013be64080055f3204004ff5902007dfac810013bd64080015eb204004ff19020025f8c81003fff540801fbfaa0400fff9502007ffaa81003f7d540801ffe2a04004ffd8c20025fec610013fe63080037f3184004f798c2000dbcc610013fd63080017eb184004f758c20005bac610013fc63080097e3184000ffd4c20077fca610003fd530801dfe298400fffd0c20077fc861003ffd430801dfe2184007bf9882003ffea41001ffe520800ffea904007ff1482003ffe841001ffe420800ffea104007ff1082003ffe641001ffe320800ffe9904007ff0c820027fec210013fe61080077f3084004fd98420005ecc210013fd61080017eb084004fd58420005eac210013fc6108001ffa884000ff94420007faa210003fc510801fffa08400fff9042007ffa821003
  | 3 => 0xfb2a6000ff99530005fcca98003fd654c0017eb2a6000ff19530005f8ca9805bff644c02d7fb226016ff99130015fcc89805bfd644c02d7eb226016ff19130015f8c89805bff544c02dbfaa26016ff951300b7faa89805b7d544c02dfe2a26004bfd8d3000ffea698003df534c003ff29a6001ff54d3000ff8a698007dc534c003ffa1a6001ff90d3000fbc8698007fd434c02deea1a6001ff10d30007fec498002ff624c001ff3126000ff58930007f8c49801efc624c001ffa926000ff94930007faa498003fc524c02dffa126016ff909300b7fa849805bfc424c003ff9926001f7cc93000ffc6498007fd324c001ee9926001ff0c930007fec298002ff614c001ff30a6000ff58530007f8c29800efc614c001ffa8a6000ff94530007faa298003fc514c02dffa0a6016ff905300b7fa829805bfc414c003ff98a6001f7cc53000ffc6298007fd314c001ee98a6001ff0c530007fe4298003fe214c001fe90a6000ff0853000dfec098003ff504c009ff2826000ff54130027f8a09805bff404c009ff2026016ff50130027f88098007ff304c003fd9826004ff8c130027bc6098013fc304c009ee1826001fe0c13003ffecb9001eff65c800fff32e4000bf9972003ffacb90002fd65c800ffe32e4007bf1972003ffec99001eff64c800fff3264002bf9932003ffac990056fd64c800ffe3264007bf193200affea9900577f54c802bff2a64015ff553200aefaa990057fc54c800fffb1e4007bfd8f2003ffcc790006fe63c800ffeb1e4000bf58f2003ff8c79001efc63c8001ffa9e4014ff94f20007faa790053fc53c802bffa1e4014ff90f200affa8790053fc43c800fffa964007ff94b2003ffaa59001ffc52c800fffa164007ff90b2003fdc859001ffd42c802bf6a164007ff10b2003ffe659001ffe32c800ffe9964007ff0cb2003ffec39001ffe61c80077f30e4007ff58720005fac39001ffc61c8001ffa8e4000ff94720007faa390003fc51c802bffa0e4015ff907200affa8390057fc41c8029ff98e4000ff8c720007fa6390053fc31c800fff90e4007ff8872003ffa439001ffc21c8001ffa864004ff94320007faa190013fc50c802bffa064004ff903200affa8190013fc40c8029ff9864004ff8c320007fa6190013fc30c8009ffb2c4004bfd9620027fccb10002fe6588009feb2c4000bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc91000afe6488009feb244013bf59220027f8c910012fc6488027ffaa44013dfd522009ffca91004ffd5488027beaa44013ff15220027fec710012ff6388009ff31c4001bf98e20027fac710002fd6388009fe31c4004bf18e20007fea71004bfe5388001fea9c4012ff14e2009ffe871004bfe4388027fea1c4012ff10e2008dfac510003ff528800fff2944000ff54a
  | 4 => 0x3fd6254001fe312a007bf18950007fea4a80037f5254001ff292a000ff54950006faa4a8003fc525403bffa12a01dff909500effa84a8077fc4254039ff992a000ff8c950007fa64a8073fc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa003bf18550007fea2a8003fe5154001fea8aa000ff145500effe82a8077fe415403bfea0aa01dff105500e7fe62a8003fe3154001fe98aa01cff0c550007fe42a8003fe2154001fe90aa000ff08550007fea0a8003fb5054009ff282a004df941500effe80a8013fe405403bfea02a004ff101500e7fe60a8013fc30540377f328a004ffd9050025fec828013fe64140057f320a004ff590500cdfac828013fc64140097e320a01affd50500cefea828067fe5414033feaa0a019df550500d7f8a828013ff6314009ff318a001bf98c50027fac628002fd6314009fe318a004bf18c500d7fea628063fe5314001fea98a01aff14c500cffe8628063fe4314033fea18a018ff10c50027fec428013fe621400f7f310a004ff58850005fac428013fc6214035ffa90a000ff94850007faa42806bfc5214033ffa10a019ff908500cffa8428067fc4214031ff990a000ff8c850007fa6428063fc3214009ffb08a004ff9845001dfcc228013fd61140017eb08a004ff184500d7fea228003fe5114001bf288a000ff544500d7f8a2280037c5114033ffa08a019ff904500cffa8228067fc4114031ff988a000ff8c450007fa6228063fc3114001ff908a000ff88450007fa4228003fc21140097f300a004ffd4050026fea028013fe5014009fd280a004ff54050026faa028003f95014009ffa00a004ff90050027fa8028013fc4014009ff980a004ff0c050027fecb18012ff658c009ff32c6000bf99630027facb18002fd658c009fe32c6004bf19630027fec918012ff648c009ff3246002bf99230027fac91805efd648c009fe3246004bf192300bffea91805f7f548c02fff2a46017ff552300befaa91805ffc548c0037eb1c6001ffd4e3000ffca718007fd538c003fe29c6001ffd0e3000ffc8718007fd438c003fe21c6004ffd8a30027fcc51801efe628c009feb146000bf58a30027f8c518003ff528c001ff2946000ff54a30007f8a51805fff428c02fff2146017ff50a300bff88518007ff328c003ff1946001ff4ca3000ff86518013ff618c009ff30c6003bf98630027fac318002fd618c009fe30c6000ffd4630007fca318003fd518c001fe28c6017ffd06300bffc831805ffd418c02ffe20c6001ffcc63000ffc6318007fd318c003fe18c6000ffc8630007fc4318003fd218c001fe10c6004bf98230027fea118013fe508c009fea846004ff14230027fe8118013fe408c009fea046004ff10230027fe6118013df308c003fd9846004ff0c230027f06118003ff654c0017
  | 5 => 0xc42101ffc621080ffd3108407fe1884203ffc842101fde421080ffe2108407fb1084203ff4842101fda421081ff52108407ffb004203ff98021025fcc01080ffd60084017eb004203ff18021117fe801088bfe4008445fea004222ff1002110ffe6010887fc3008435ffb26a01bbfd93500dffcc9a800afe64d4037feb26a01bbf593500d7f8c9a800afc64d4035ffaa6a01bdfd53500dffca9a806ffd54d4037beaa6a01aff153500d7fec7a8083fe63d40037f31ea000ff58f50005fac7a806bfc63d40037e31ea01affd4f50107fca7a8003fd53d4035fe29ea01bffd0f50107fc87a806ffd43d4041fe21ea01affd8b50007fcc5a801efe62d4001feb16a000bf58b500d7f8c5a806bff52d4001bfa96a000ff94b50007faa5a80037d52d4035fe296a01bffd0b500dffc85a806ffd42d4037fe216a020ffccb50007fc65a8003fd32d4041fe196a01affd8750007fcc3a800efe61d4001feb0ea000bf587500d7f8c3a806bff51d4001ff28ea000ff547500d7f8a3a806fff41d4037ff20ea01bff507500dff883a8083ff31d4001ff18ea000ff4c750107f863a8003ff21d4001ff10ea000ff48750007f843a806fff40d4009ff206a01bff50350027f881a8083ff30d4009fe186a01dbf59650027fec928012ff6494009ff324a002bf99250027fac92807efd6494009fe324a004bf192500fffea92807f7f549403fff2a4a01fff552500fefaa92807ffc5494009ffb1ca004ff98e5000dfcc728013de63940036f31ca004ff58e50005fac728013dd63940016eb1ca004ff18e50025f8c728003ff539403dff29ca000ff54e500f7f8a72807fff439403dff21ca01fff50e500f7f88728013ff6294009ff314a007bf98a50027fac528002fd6294009fe314a000ffd4a50007fca528003fd5294001fe294a01fffd0a500fffc852807ffd429403ffe214a01effcca50007fc6528003fd329403dfe194a004ffd8650027fcc32800efe6194009fb30ca000bd98650027fac328002fd6194009fab0ca000bd58650027f8c328003ff5194001ff28ca000df94650007faa328003fc5194001be28ca01fffd06500fffc832807ffd419403ffe20ca01effcc650007fc6328003fd319403dfe18ca000ffc8650007fc4328003fd2194001fe10ca004bf98250027fea1280137f5094001fda84a004ffd0250027fc8128013fd4094009fe204a004ffcc250027f86128077ff645403b7fb22a01dff99150015fcc8a8077fd645403b7eb22a01dff19150015f8c8a8077ff545403bbfaa2a01dff951500effaa8a80777d545403bfe2a2a000ffd8d50005fec6a8073fe63540037f31aa000ff58d500e7f8c6a8006fc6354001ffa9aa01cff94d50007faa6a8073fc535403bffa1aa01cff90d500effa86a8073fc4354001ffb12a000bfd8950007fcc4a8
  | 6 => 0x7ff32c4200bf9962101ffacb10802fd6588407fe32c4203bf1962101ffec91080eff6488407ff3244202bf9922101ffac91089afd6488407fe3244203bf19221137fea91089b7f548844dff2a44226ff55221136faa91089bfc5488407ffb1c4203bfd8e2101ffcc710806fe6388407feb1c4200bf58e2101ff8c71080efc6388401ffa9c4225ff94e21007faa710897fc538844dffa1c4225ff90e21137fa8710897fc43884497eb144200ffd4a2103ffca510803fd528840ffe2944226ffd0a2103ffc851089bfd428840ffe2144225ffcca2103ffc6510803fd328840ffe1944203bf9862101ffea31080ffe5188407fea8c4203ff1462101ffe831080ffe4188407fea0c4203ff1062101ffe631080ffe3188407fb18c4203ff4c621007ea631080ffc3188407ff90c4203fbc862103fee431080fff6088407ff3044204bf9822101ffac110802fd6088407fe3044226ffd0221137fc811089bfd408844dfe2044225ffcc22112ff86110803ff65484017fb2a4200ff99521005fcca90803fd65484017eb2a4200ff19521005f8ca90893ff64484497fb224224ff99121015fcc890893fd64484497eb224224ff19121015f8c890893ff5448449bfaa24224ff95121127faa8908937d5448449fe2a24200ffd8d21005fec69088ffe63484037f31a4200ff58d21005fac69088ffc63484037e31a4200ffd4d2111ffca690803fd5348447fe29a4224ffd0d2111ffc8690893fd4348447fe21a4200ffd492103ffca490803fd524840ffe2924224ffd092103ffc8490893ee4248449fea124224fb5092103ff8849088fff324840fff1924200ff4c92103ff86490803ff5148407ff28a4200ff5452101ff8a290893ff4148407ff20a4224ff5052101ff8829088fff3148407ff18a4200fd8c521007fa6290803f53148407fe18a4207ffc852103fee429080ffe2148407f710a4200ffd8121005fec090803fe6048401feb024200ff18121025f8c090893ff4048449ff2024224ff50121127f8809088fff3048447fe1824203ffd942101dfeca1080ffe65084017f3284203ff59421005faca1080ffc65084077e3284203ffd902101dfec81080ffe64084057f3204203ff59021115fac81080ffc64084077e3204222ffd5021116fea81088bfe5408445feaa04222df55021117f8a81080fff63084077fb184203ff98c2100dfcc61080ffd63084017eb184203ff18c2101df8c610803ff5308443ff2984200ff54c2110ff8a61088bff4308443ff2184222ff50c2110ff8861081efe620840fffa904207ff9482103ffaa41081ffc520840fffa104207ff9082103ffa841081ffc420840fff9904207ff8c82103ffa641081ffc32084077f3084203ffd442101ffca21080ffd5108407fe2884203ffd042101ffc821080ffd4108407fe2084203ffc
  | 7 => 0x18807fe538c403fea9c6201ff14e3100ffe8718807fe438c403fea1c6201ff10e3101ffec51880ffe628c40f7f3146203ff58a31005fac51880ffc628c401ffa946200ff94a31007faa518803fc528c455ffa14622aff90a31157fa85188abfc428c403ff9946201ff8ca3100ffa6518807fc328c4077f30c6203ffd463101ffca31880ffd518c407fe28c6203ffd063101ffc831880ffd418c407fe20c6203ffcc63101fbe6318807f7318c407fe18c6203fd0c63101ffec11880ffe608c4097f3046203ff58231005fac11880ffc608c455ffa04622aff90231157fa81188abfc408c403ff9846201ff0c231007feca98802ff654c401bfb2a62009fd9531007fcca98802fe654c401feb2a6200bf59531007f8ca98802fc654c401be32a62009f1953114ffec8988a6ff644c453ff3226202bf9913114ffac8988a6fd644c453fe3226202bf1913114ffea8988a77f544c453ff2a26229ff5513114efaa8988a7fc544c4077fb1a6201ffd4d3100ffca698807fd534c403fe29a6201ffd0d3100ffc8698807de434c403fea1a6229f750d3100ff88698803ff624c4017fb126200ff98931007fac498803fc624c40f7e3126200ffd4931007fca498803fd524c401fe2926229ffd093114ffc84988a7fd424c453fe2126201ffcc93100ffc6498807fd324c403fe1926201bfd8531007fea29880ffe514c401fea8a6203ff1453114ffe829880ffe414c453fea0a6203ff1053100ffe6298807f7314c407ff18a6203f78c53101ff8629880fdc314c403fa18a6200ffd8131005fec098803fe604c401feb026200ff18131025f8c0988a7ff404c453ff2026229ff5013114ff88098807ff304c403ef9826201ff0c13103ffecb9081eff65c840fff32e4200bf9972103efccb908027e65c840ffeb2e4200bf5972103efacb908027d65c840ffe32e4207bf1972103ffec99081eff64c840fff3264202bf9932103f7cc99080abe64c840ffeb264228bf5932103f7ac990802bd64c840ffe3264207bf19321147fea9908a37f54c8451ff2a64228ff55321146faa9908a3fc54c840fffb1e4207bfd8f2103ffcc790806fe63c840ffeb1e4200bf58f2103ff8c79081efc63c8401ffa9e4227ff94f21007faa79089ffc53c8451ffa1e4227ff90f21147fa879089ffc43c840fffa964207ff94b2103ffaa59081ffc52c840fffa164207ff90b2103fdc859081ffd42c8451f6a164207ff10b2103ffe659081ffe32c840ffe9964207ff0cb21007fea39080ffe51c8401fea8e4203ff14721147fe839080ffe41c8451fea0e4203ff1072113ffe639080ffe31c8401fe98e4203ff0c72103ffec19081ffe60c84097f3064207ff58321005fac19081ffc60c8451ffa064228ff90321147fa81908a3fc40c844fff9864227ff0c32101ffecb1080eff658840
  | 8 => 0xf54e51187f8a7288c37c5394463ffa1ca230ff90e5118ffa87288c3fc4394407ffb14a203ff98a5103dfcc52880ffd62944017eb14a203ff18a51007fea5288037f5294401ff294a200ff54a51006faa528803fc5294463ffa14a231ff90a5118ffa85288c7fc4294461ff994a200ff8ca51007fa65288c3fc32944077f30ca203ffd465101efea328803f75194407ffa0ca203ff9065101ffa832880ffc4194407ff98ca203ff0c65101ffec12880ffe60944097f304a203ff58251005fac12880ffc6094463ffa04a231ff9025118ffa81288c7fc4094461ff984a230ff0c25117ffec8a88beff645445fff322a202bf9915117ffac8a88befd645445ffe322a202bf1915117ffea8a88bf7f545445fff2a2a22fff5515117efaa8a88bffc5454401ffb1aa200bfd8d51177fcc6a8806fe6354401feb1aa22eff18d5100df8c6a8803ff535445dff29aa200ff54d51177f8a6a88bfff435445dff21aa22fff50d51177f886a8803ff62544017fb12a200ff98951007fac4a8803fc625440f7e312a200ffd4951007fca4a8803fd5254401fe292a22fffd095117ffc84a88bffd425445ffe212a22effcc951007fc64a8803fd325445dfe192a200ffd4551007eea2a880ffe5154407bf28aa22fffd055101ffc82a88bffd4154407fe20aa22effcc55101ff862a8803ff60544017fb02a200ff98151007fac0a8803fc60544097e302a22fffd015117ffc80a88bffd405445ffe202a22effcc151177f860a88b6fe6514407ffb20a203bfd905101ffcc82880afe6414407feb20a22cbf5905101ff8c82880efc6414435ffaa0a22cdfd5051167fca8288b3fd5414459beaa0a21aff1505101ffec62880ffe63144037f318a203ff58c51005fac62880ffc63144077e318a21affd4c5115ffca6288af7e5314401fea98a21aff14c5115ef8a6288b3ff4314457ff218a22cff50c5115ff8862880fff6214407ff310a207bf9885101ffac428802fd6214407fe310a21affd4851006fea428803fe5214401fea90a200df548510d7f8a4288b3ff4214459ff210a22cff50851167f884288afff3214401ff190a200ff4c85115ff8642880efe6114407ffa88a203dfd445101ffca22880ff65114407fea88a203df54451007eaa22880fff4114459fba08a203ff9045101ffa822880ffc4114407fa208a203ffcc45101ff8622880fff6014407ff300a204bf9805101ffac028802fd6014407fe300a22cffd0051167fc80288b3fd4014459fe200a22bffcc05115ff8602880fff658c4077fb2c6203ff99631005fccb1880ffd658c4017eb2c6203ff1963101df8cb1880fff648c4077fb246203ff99231015fcc91880ffd648c4557eb246203ff1923101df8c9188abff548c455bfaa4622aff95231157faa9188ab7d548c455fe2a46201bf58e3100ffea7
  | 9 => 0x869ffaa46434dfd52321a7fca9190d3fd548c869beaa46434ff1523200dfac719007ff538c801efa9c6401ff94e3200ffaa719007fc538c803ee29c6401ffd0e3200ffc8719007de438c803fea1c6434f750e3200ff8871901efe628c80fffa946407ff94a3203ffaa51901ffc528c80fffa146407ff90a3203ffa851901ffc428c80fff9946407f7cca3200fde651901ffc328c80ff61946407ffd863203ffcc31900efe618c80ffeb0c6400bf5863203ff8c3190d3ff418c869ff20c6434ff506321a7f88319007ff318c803fe18c6407ffd823203ffcc119012fe608c80ffeb046400bf5823203ff8c1190d3ff408c869ff2046434ff502321a7f88119007ff308c803fe1846400ffd9532005feca99003fe654c8017f32a6400ff59532005faca99003fc654c8017e32a6433ffd913219dfec8990cffe644c8057f3226433ff5913219dfac8990cffc644c8057e3226433ffd513219efea8990cffe544c867feaa26433df5513219ff8a89901eff634c803ffa9a6401ff94d3200ffaa699007fc534c803ffa1a6401ff90d3200ffa8699007fc434c8037fb126400ffd493203ffca499003fd524c80ffe2926433ffd093203ffc84990cffd424c80ffe2126401ffcc93200fde649901ffe324c80fef1926407ff0c93203fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6403bf1853219ffe82990cffe414c867fea0a6433ff1053200ffe6299007fc314c801ffb026400bfd8132007fcc099003fd604c801fe3026404bf1813219ffe80990cffe404c867fea026433ff1013200ffe6099007df304c803fe182641affd935116dfec9a88b7fe64d44057f326a22dff5935116dfac9a886bfc64d44057e326a21affd535116efea9a88b7fe54d445bfeaa6a22ddf553510d7f8a9a886bff63d4465ff31ea201bf98f51007fac7a8802fd63d4435fe31ea201bf18f510d7fea7a88cbfe53d4401fea9ea21aff14f5116ffe87a88cbfe43d445bfea1ea232ff10f510d7fec5a8803fe62d440f7f316a200ff58b51005fac5a886bfc62d4435ffa96a200ff94b51007faa5a886bfc52d445bffa16a22dff90b5116ffa85a88b7fc42d4465ff996a200ff8cb51007fa65a88cbfc32d445bffa0ea22dfdd075101ffc83a88b7fd41d4407fe20ea22dfd10751197fe63a880ffc31d4435ffb06a200ff98351025fcc1a8803fd60d44017eb06a21aff1835116ffe81a88b7fe40d445bfea06a22dff10351197fe61a88cbfc30d445f7eb2ca203ffd925101dfec92880ffe64944057f324a203ff5925118dfac92880ffc64944077e324a231ffd525118efea9288c7fe5494463feaa4a231df5525118ff8a92880fff6394407ff31ca201bf98e5101ffac728802fd6394407fe31ca203bf18e51007fea7288c3fe5394461bf29ca200f
  | 10 => 0x61a90e6fd659480fffb24a407bfd925203ffcc92900afe649480ffeb24a43bbf5925203ff8c92901efc6494877ffaa4a43bdfd52521dffca9290effd5494877beaa4a43bff1525203ffec72901ffe63948037f31ca407ff58e52005fac72901ffc639480f7e31ca400ffd4e521d7fca729003fd5394875fe29ca43bffd0e521d7fc87290effd4394875fe21ca407bf98a5203ffea52901f7f5294801f7a94a407ffd0a5203ffc852901ffd429480ffe214a407ffcca5203ff8652901fff619480fff30ca403bf9865203ffac329002fd619480ffe30ca43bffd06521dffc83290effd4194877fe20ca43affcc6521d7f8632901fff609480fff304a404bf9825203ffac129002fd609480ffe304a43bffd02521dffc81290effd4094877fe204a43affcc2521d7f861290e7ff64548737fb22a439ff99152015fcc8a90e7fd64548737eb22a439ff19152015f8c8a90e7ff5454873bfaa2a439ff951521cffaa8a90e77d5454873fe2a2a400ffd8d52005fec6a9003df63548016fb1aa438ff98d5200dfcc6a9003fd6354871fe31aa401bf18d52007b8c6a9006dc6354801ffa9aa400dfd4d521c7fca6a9003fd5354801bea9aa438ff14d521cffe86a90e3fe4354873fea1aa438ff10d52007fea4a9003ef525480fff292a407df949521cffe84a901ffe4254873fea12a407ff109521c7fe64a901ffc3254801ffb0aa400bfd8552007fcc2a9003fd6154801fe30aa403bf185521cffe82a90e7fe4154873fea0aa439ff105521c7fe62a90e3fc3154801ffb02a400bfd8152007fcc0a9003fd6054801fe302a404bf181521cffe80a90e7fe4054873fea02a439ff101521c7fe60a90e3fc305486f7f328a407ffd905203dfec82901ffe64148057f320a407ef990520157cc82901ffd641486d7eb20a407ef590520057ac82901ffc641480f7e320a41affd50521b6fea8290dbfe541486dfeaa0a436df550520d7f8a82901fff631480fff318a401bf98c5203ffac629002fd631480ffe318a407bf18c520d7fea6290d7fe5314801fea98a41aff14c521b7fe86290d7fe431486dfea18a435ff10c5203dfcc42901fff521480fbfa90a407ff9485203fdca42901ffd521480fbea90a400fb5485203ffe842901ffe421480ffea10a407ff1085203ffe642901ffc321480fffb08a407ff9845201dfcc22901ffd61148017eb08a407ff184521b7fe82290dbfe411486dfea08a436ff104521affe62290d7fc311480fffb00a407ff98052025fcc02901ffd60148017eb00a407ff180521b7fe80290dbfe401486dfea00a436ff100521affe60290d7fc301480fffb2c6407bfd963203ffccb19002fe658c80ffeb2c6400bf5963203ff8cb1901efc658c80fffb246407bfd923203ffcc91900afe648c80ffeb246434bf5923203ff8c91901efc648c
  | 11 => 0x200100180100000300000000080080480c80680081100280480000080200b80780580380700600400280201100080300680280001180000280b00200280000c00380181180300180000100380480080300c80b80480000700000c80b00200800200000880300300080180100100000000880282300000000002000080000000080200280480080000000200400500080000480800000500400b002006fe65d4c35ffb26a63ebfd93531f7fcc9a980afe64d4c7dfeb26a63ebf593530d7f8c9a980afc64d4c35ffaa6a63edfd53531f7fca9a98fbfd54d4c7dbeaa6a61aff1535300dfac7a9807fe53d4c03bf29ea601f794f5300ebca7a9807fc53d4c03be29ea601ffd0f5300ffc87a9807fd43d4c03fe21ea61affd8b53007fcc5a981efe62d4c01feb16a600bf58b530d7f8c5a98fbff42d4c7dff216a63eff50b531f7f885a9807ff32d4c03fe196a601f70cb530d7fec3a9803fe61d4c077f30ea600ff58753005fac3a986bfc61d4c7dffa0ea63eff907531f7fa83a98fbfc41d4c03ff98ea601ff0c7530d7fec1a9803fe60d4c097f306a600ff58353005fac1a986bfc60d4c7dffa06a63eff903531f7fa81a98fbfc40d4c03ff986a601f7cc35300ff861a9806ff6554c7bffb22a63dbfd91531effcc8a980afe6454c7bfeb22a63dbf591531eff8c8a980afc6454c7bffaa2a63ddfd51531effca8a98f7fd5454c7bbeaa2a63dff1515300dfec6a9807ff5354c01efa9aa601ff94d5300efca6a9807fc5354c03be29aa601f714d5300ffe86a9807fe4354c03fea1aa601ff10d53007fec4a9802ff6254c01ff312a600ff58953007f8c4a981efc6254c7bffa12a63dff909531effa84a98f7fc4254c03ff992a601ff0c953007fec2a9802ff6154c01ff30aa600ff58553007f8c2a980efc6154c7bffa0aa63dff905531effa82a98f7fc4154c03ff98aa601ff0c553007fec0a9802ff6054c01ff302a600ff58153007f8c0a9812fc6054c7bffa02a63dff901531effa80a98f7fc4054c03ff982a601ff0c1530d7fec9a90deff64d486fff326a402bf993521bffac9a90defd64d4835fe326a402bf193520d7fea9a90df7f54d486fff2a6a437ff553521befaa9a906bfc54d4835ffb1ea43cff98f5200dfcc7a9003fd63d48017eb1ea41aff18f5200df8c7a906bff53d4801bfa9ea43cff94f52007faa7a90037d53d4835fe29ea437ffd0f521e7fc87a90dffd43d4879fe21ea437ffd0b5203ffc85a90dffd42d480ffe216a43cffccb5203ff865a906bff61d4801ff30ea403bf98752007fac3a9002fd61d4835fe30ea437ffd07521bffc83a90dffd41d486ffe20ea43cffcc7521e7f863a906bff60d4801ff306a404bf98352007fac1a9002fd60d4835fe306a437ffd03521bffc81a90dffd40d486ffe206a43cffcc3521e7f8
  | 12 => 0xe80100000080800180180300180180200a80081080a80200080000000000480080200100d00b80580380000000500000100500100400580280100000300580000000e00180a80000180100000000180080000000000000200200000000a80000980300100680100180100700280900f80180200000100080180100c00180380300000200000000800900080080080a80080180900880880180100100000280880000800080580600280000680080400580880200400280080800880800000b00280100e01800800580380180700080500080000380280380100602680000680080c80180100201600000200380000880700000080000680380080000181080080280400000080200280180080200580400000580200080080000200000000100000400080000780500100800080000000180600100680200000580000181c80180180000300280000000080300800080700800300000380500000100200000000000080402b00580000100000080100000080600080280100000000080300180200280580001180180280b80300000300400380200080480080400000080000100000580100b00780880580100000a00280c80b01700000d80400100080100180200100180000380000000180080100000001880000000000a00001f80180300000300b00100000600080100200000000380380180000400000100480480200080100080780080080080300300081080100b80380080181b80180300200000100680180700600a00000400300380080d00100080300080580080000080000500300380280081a00e80080280280100000280000380100400000780000000000080480000780080500180000000a80400100000100080e00000180180b80500100080380400200500080000001780100180080300700080200000100100200000080000700480200100000200080600000100200000300280000380180000100800000280b80200280580300000000680180200100000080000200000480300000000000080000080000080200100100000080000000000000000080480000481080080180380000100000380080080000000700100000180000000400000100000081500080280100100000180000d00080980280000080300300600600300080180200100080000000d80b00101600400480000080100280100500000080600000001200000600700100000000100000100180200d80b00380800000880080200280200000080380080000000080280100100300000080000000100100080a00000680000280080080280201780080080a00080000380080400000100600800000000180000180000000800200080200100200180080000c00080180100100100900001700380000500000000000300200380000000180600080180000
  | 13 => 0x6d41a500000000b054000000006160001019ae933290029c116c05446d08e0888b484b22b00268b325d44e914d89221a111087ed17215d1f38c2064c6083caa7dc0588bd05d80000006130000b4d0ee707024000023c4713668000d5c5ad34198bc5a49bd0289cc000472900002a10f200013d00011ee00010e1ac80002960f222ad3a02cd000079c0006aa000000000052a3e0a19825654600000000000003101184000a3e2ad18082903331bd8f153aa000275966872e04d113255028c00000006cc0000000000558000000000259000016d0e980001cc8b51b1a31064841a14a1731328000000016400000000015d80005120c800006de4fa2010000a5800000000000002d74059afc0008a21299f44100000423952c5807c83fb95ac83c87c3bf15607fa3fc4a508681fa1d11820c5800083b36e0df416c9ec327096825c0002001da928e0002a1261d3166dd0fb9110dfa58f2cd9fe50ba3341658afd23a09d28f9db0eec0005090000bda99a0349a0412c15e000205c4de9c948f80004045a61b000000008e833200bc0002273c5024c71a00006d809cc141872ef072c9100002b627d40000000000a2414c2101f8800004a92513118190b440c00000005b000000000009d200000017800000b843e80000006800d4000000000000000000005a83621b880000832fd270947a24a1f698e54224cd19c0000000137000201470a19c1eb0814000a3905f006821835d0001ce52f662942908348ee000138968c816000241a1611be00011580000a893c24a043400097e12380008d68220001288c56a2b43a0000a607fc2bea124dd67874dc1190f6082b2bf96f81082dc45386654088200d89918ef01aa00002f0d1000014082bc6cc2f81b5a7f08848cf00024a4f2401b096a6bd15289c1271efd1d609f4e5186c26a54715a814809c76f3df01042fa3c94d59088496000000156c5760d312b09e09a807a0000000f2c03141806e8ed031f27803140000000000168000000000250800085e34320785be01208a09e40003b0000229460e0000770000000215000000000000000025a8000000000000000096d1ce178c00019419b00000005f941e22b8cb45482ed9be09dc7da2c21f383643182ec84910de6f948420cc58c3411cf269ca2881a2bd9bf0cc600008e8ad84520002d5865800079e00001cc3d678d1a20ed8f5c0003488000000000000000000042d4ef85050c200000019980005a5224803422081600100300080100000000100080700000200c80300701380280200080900100000000100800080080280000000780080080200680100000000081e001801805001000801800000002801004800000802800806009801806800008002004800002000000803004800803802002802007000001800001006801800001000805000001000
  | 14 => 0x12a1018b9474100000005160004be1c141bc9bb4cba83cdcc2d000025acf725df2918c3125832b36b000095090951916300008a31d900006b63090c68d8940091828da1212449b1000045c0000004089eec1524c600000001b845d3288d280000ca11016380009a80000000000000000000090e25200000002882453150c0c6440812d48448fe84404e6800022a00004f0dc05a2524000000047a3de00000013d6000000006400067b3fb210c5ec846450a4d006066c44d2840430000033a5e400054f000057c24a2ee28480012380e94db94740002b444700013c80000001da400048d4c087d00002c904e137820c7e2253a53423087215d0000e948f4000000000094500007200000004fa1d4c0003df0000c5c00031c000000005c9852ee00003d411115080009626692988e6400000033a8000f288272eea7f4d8a55011680000000a400000006da9cb000084cb7e68a3950acc00041f0001f754489e54851f2c97a33139600000003001ec07780008cc0000000a0a39d000104145c4d100000000000001621d445524d91a71aa0000496112130c0e85d100000010ce1700000000b2600000013cc0000003140d500003a92c5245527e4371e40038d2816e2da1ff50f400000017d4c2058830c11d4e7c2d501e05bd0520001f18000ee08ce1b28000000a354ed14ac0002412baa4a07fc3ab1e1a564d9426c2b183d800000000027994446f320a8dcc6d82f207a998521a0572bd095516ca081ea149415443241a01dcdde89f4499228ff6426501048472a5e41ab08306a00003ba96b03240100a9a4dc34c76e4b1986860c00007780000008a442689a4a1044c3ef893123c564000011c00013b2a504040006b712104c052214a49f1a5800035239e21d45f808b0d01d507363e429da698af84b32f124ac1e06cb44a898c0007db010155414e2f317f1a9039c4ca00000000007a92e498c43487cc00016a800059d4ab83e8dc0378487155cfc60000000000a7a9060f1234c0007021a316546b02e0000000000000000000002fe00026281fc000128000000031e0002b90c64cde00000018b84da0000ac95581da0000001a6848601811ba1940004a300027310d00001f500006ea000000222800000000017140004a40000000f385c0321a0845e86cf3c31ee08142e8457994d22466244b9f950a274336323449761c5439a07c0006ea000140924e00000000012d800007d8a3c16a72e4f09d580004ba0000828c2c64100000000009aa000000125e0e10001d3d44038622a19c80000000000e886e200000023ec8300003a9157c0000002d9856cbf07f1135000000061100000000007612e11f850880002931bc939e0000000e8039800005713940006901971c58b040a545822dc87c93a38d0cb13c481d02000001303ce4f9215c0000b707f94e4
  | 15 => 0x4278000233a5e0cfc7e94bf896c4ba7aa3470858b6076406ba18c0000680988498cec69b1c11910e6a7a43919c3896a58000000013c03b54db0fe04742990230cc8008503000000032a29a1cc1e412203794b326c0b702c720721c137230e48d1384fcc1ca3280fac9083bf3a692305d629b2eb9b60da005e49810d87680391128fa03ac31442b0014d468073ab8d78dc61764d105e93581683ff8000d9c0000eb80003b00001d41cac0003282c891485ac87b000065d0480003b928b53ce7402e90000b281e1255a5b80007a7228a8347ae2b910e92550a636e1ee0a9ccae62328c800000064d02f970c0006673f623cc0005113de905898435100000000005e606908b8faa43a05828e89e46f04b3a7644ec70d1e115a43f495d167289499e67c1a7a31d13a53c1fd000020045c4f8000133a3aa4d18709270108387a32d46881006ca0108be717256013d3f40002ba01080003dd00000010f00000d7987800000007f20544122a318098508284080000000cbe065060937c7a600000000000006ee1b392250d67d92b518ccdd09243d400000000000b10d640008ba432055000093616f28982a40001e89b688d47d20f020e07aa3424b12359124000079912c6e8463000000000000035ea40c4886b54b895b87087131b09b00296390000185c4683451de84a4dea0d8256800093a000000109023e000000000000007100000000002f50c02260b5e14f0ff00006a66604839e88b240000fb253c7002514e4003046c2e5345a108c1e0f427b9d191caa1b4df81b000088250c287ca7480d34610e0a34a270002770f945b73ada63c57a780173a22424e11a00400006fc5701c581b83084f44d709902b461918100e8a2e9f800522803c610a37f0bf41320001d200005fe000171a6347d200000000001d64f60c50f841922fa4b980ac49e000000278c0005f436405250fe37638a0000bd27d80000fb800067100000000005831420000000a143db800000090b03017bd3a600000000000000000001010d380000c110353520004a9204c25e7ea00000005c26e44f992082e45f73cd1bc46785794c9000082e000039120400000010586f524086c226a5d81c815c0001260000000146800069027413914a12c244f41c95053683720610ce4e3647b11889fc33426842024e4ae605025c190941820131d994866e17511d971c33e6b114c0000e76265051a7c480a9ea412800000022c0002384ff00000d693e05d80f815f1cb40cc1a33728f9845410e11786acc801b804b94fc0de2dd2e4254c0000003c8a23138a4934908ca8a0870a000000132600001487542c276b0000c9c0002db1e2121800000008b00011f47491b2000000017e1cb2824000000394000000021f005a2c80763053561300000000273167000062d04404a88528b13228fd80006fa
  | 16 => 0x935108450980004fd9964dae1c40fe9e3c00000048c9ac0a9c00029125703ea06213f000000037a1e09a552e84fd4cc0b0c4fa000442012d19a34324b9f90a200f24ce0a941426f71c0816c0008f60001cbc4607554d9000061e626000042414400010726380000332ff86dcfa860537d86d846a7c72e089dcc780344ec1c940009bc18a9c740004121e6800057800000010ccd727b600000000002e64eb1e7400014d47118fd38071900000006744ae27f1d3871e00009c000000000000023fc0001b0000021800000020d995893400000023209d0107000000000064b21f85a88ac00014101240000002ec19b806ca3c0b19ef00000001f111b09386851de1a5c000a28109200497c66b3491cc90aa95a234858055c3cf03ea4b54168f03a3a88c0001bb00023554709f913a9848dfe3930879aec0004b43261dcc00000000aa2e14600b326593fce621ef480915c6800d628aa8689da0cf23e0540c4859e360a3c81ca9c60d70a312be3b3400138c1642000c5a7753145341b40c68cbc738000267c50669d2d896ec4660003ba0230e8a6c902200000007a500000013043cb000000000088600000000007c9135a329218727000000000040310796885c80001dda08c00051e0000f4800000032e8f68e101bc00001d800000000003a09787eb4eda1b42a27c21611e8cbce9b522c1de8a5e7e827a9e252ee18900005f0bd01322230000000000210000017200000005b0b205431338000fae6733888df009863512f800132a000472067822649f0000a1c0004110c8800100605c000051c11c329145220c91c000022805cf861861510d24a0e00000025e81f20003e0173caa24d810f205091663444009407224d71f79d780000000e025d52d23770efa0dd38205d5108000caa66511e230543a00000000005f69b349726947ea000000236101e8d43881ce8d4e2cf4a011e889c2081a3a368b1a78215899e52906b6176a2348fe6e7000101c1e20004f480001200004c400003e614202515489823f30e380012469040118000c1c7c44151a805c495511c8000f9e94b1381ec80006d32f887c929c000399a70c3d21e600010c00000b411910c424400042528cc3304dc20992002ae0d01331bd05d4785068804d11607b3a41b5510e00037692bd2620002870c78000a2f03c80000001a93e8022450a4bf48b800074a000008800000042800010ad42a4a1000028126a9ce0ce8e982f0a1733d007800000001900000006de00000000000000000000e682b200018f400021423c0000beca310df000000018c47c80012a000015400014541190818000b420003dd000095499009f1e8087a2c5000000000058b41f238c00054c27221b93da43500013748e000000002e8990a05000000064096f2e32048a4e8b33faa59400030d0bc8244adaa36082a68
  | 17 => 0x29c70146194014762040ba1a10e489c40b5a71c12a65820498d88a069e4991e6cbd648f00026e89d48dc043a264c946e90c186d0676996000142c10a0da25305cc3f80004050074a667a112496d43e07fa3528070b7292638f1df49d88a64ff00010d227c00012640000003b680000007a60000a5c540169156a3bcb2e1dd28601f88bc9602bba2a033667419a9c2c1042732af11ccc6e59818d9594ce00c341a98f83d00162f093f134020738206d400000050c80000008262f60e300000001e5033449a1ee22ca3744500000002164a3068d302000000000029b95343a89ff1608b6466044319180012bc00004680000000000000000e6e1e5516000023687e1d695f8e841ac0000c8533c1431979114000021478903c0007de4c002f40006012b3281c43266d000048d29865b00001f06967062328ee8000000111814cc58638000244442e00023f154c4dc68741b00000287ee0000b28cfe00000000011bc75a0fc20b07e84a03b388f8ab88ea42f99f45900004681d7c00000000000005a887100023240007ad0001b505de0000000eb80000004a21c4911e280000023c34e0002778fb018e1452d00000a3800001ba6109c4000038239d43c35500000000440002aa00000000003e293801965d00001278b9c0000000388cb800019e9d700000003d79d2d0d426014e06e40006a13e994d4050000000056000000000000012b03a71cd07244ae85446c91552fa2b01ab9ec41ba8944561064fe44d53c61ad040c061287a87128c39f34c8ebcd6661c35f1abc8021d93f01d881280000f89aad30c31206fa170c3a819262000000010428b0c4016244809b1f708c069f01310ec53a0000a6010c83a47400022040000003e683111b695134490e47e4561000068800000036900007fe0002eaa3f419c8c2306995000000000022153226f633527789ac0001e6000122c28e2e591c8fe67502f994343b435c280a0a01805fc1d6280540c6b8000282912c0002549de42684b927884b0ace42e23715113127880719cd80ac95647f134905a7632899cf50c06e127d85c48d058603a95148ec2b8460131c8f21f93109c814522930000adc00029e1532008000562000000000000000000000002463c2003c06a42f1e3800000000000024ec0007221c50e24c905d623102480008c52b40f643b6a033ae8408e8817b2428fe40002f70e81ed067c1ec196a26cf584661ed91691da000064235c04816533b9128ae25bc0001ddc1aa3be0000000ecc8bc407064d3de5811c196c8db200007012401981670001e0400052001c109c0002ab2cb000031ca0e0000000310000000246c00000023e988800006a000148528281c2ed000047068f4b40000d2625c3eb00004bc4da000000000c00000000000003f700000008a69a400023190963b81c717c00002e
  | 18 => 0x5b483a000000000072131823990300003a61dc49f200020e1ab40006272fe8000000a133bfa138114600304839c0008413cc0001018258312a4cc27a3e52a4a3492e053e14f9e2c03e70947e1f9cffc5852671b310b62aa000169c0001770002220e7e00022380009ce13f000018c0002900559e7c2cc90f000000069800000012c038600000000000006683801734eb0000000073407a6031490d343b88ad05f9b08d8e5fb18517b8b1284f11fa0b8c925e51e81c30b6c3e01fd8ab00da7594df28591dc0551e321d906224035e0c4cb7a2f038aa7b8dd87f026813246225c40049b44272678448073d17c5ba00024080003a11b49b6c1587b54d68a907288aa2118bc47241ed47c01ac1f8578090167c000000448991c1a883d192831807c71f003a630c749d400000000004b7000108400000026d800000000000021402744b631920fc0000003d59c0d08a8ec29722d0a1452d3f7a2fc000000470000000091430a80000007b34f41d94c1633f51b9d810c40002d701e070e60c24910f000031d35300001d86c30008590a5242a04da2ec43642540302b4000808075000077200000000009a65d307b993c6be3f0000000088256f4a480b428060701f842cef60001e00b3000082f0000000d5200024d80010361814eb87fca0c4cc00011bc52a00049e8a204904340000000f1c1550e309653360000000e2000000000000000005870001c980009f61431e652b63b71d88000a645ea2f90be400089e1ad00003a492a0001e4c30a809099a3a4bfc9d14b90e8c3826984a1800000061f2ac9b7c6fe0003be00000007ed00010b12267c64c186fc0009053411e5c00055d41909ec0c80000019e0ce388f500000000002610000abc0004a538c00
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7258c1002edf3258c1002edc3258c1001cff7158c1001cfe7158c1001cfd7158c1001cfc7158c1001ede3158c1001edc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10026f71058c10026fa1058c10026f51058c1001ef91058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c100065f5458c10006de5458c10006dd5458c100065d5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df4258c10006de4258c10006dd4258c10006dc4258c1001edf7158c1001ede7158c1001edd7158c1001edc7158c1001edf5158c1001ede5158c1001edd5158c1001edc5158c1001edf4158c1001ede4158c1001edd4158c1001edc4158c1001edf2158c1001ede2158c1001edd2158c1001edc2158c10026df7058c10026de7058c10026dd7058c10026dc7058c10026df5058c10026de5058c10026dd5058c10026dc5058c10026df4058c10026de4058c10026dd4058c10026dc4058c10026df2058c10026de2058c10026dd2058c10026dc2058c10026df1058c10026d71058c10026de1058c10026da1058c10026dd1058c10026d51058c1001ed91058c10026dc1058c100d4ff76d4c10024fe76d4c10004fd76d4c10024fc76d4c1000ede63d4c10006dd63d4c1002f5e53d4c10004ff7654c10024fe7654c10004fd7654c10024fc7654c1000ede6354c10006dd6354c10004ff75588100d4fc7558810004ff7458810014fe7458810004fd7458810014fc74588100067f54588100067d5458810004ff735881000cfe735881000cfc7358810024ff7258810026ef7258810006ee4258810006ed425881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026f510588100d4ff76d4810024fe76d4810004fd76d4810024fc76d48100d67e65d48100067d65d48101e6de63d4810006dd63d481003cff7694810024fe7694810004fd7694810024fc76948101d6de6394810006dd639481003eee6294810006ed6294810004ff7654810024fe7654810004fd7654810024fc76548100067e65548100067d6554810005df735481002ddc73548101c6de6354810006dd635481003eee6254810006ed625481003cff7614810024fe7614810004fd7614810024fc7614810035be7414810005bd74148101aede6314810006dd631481003cff768c810024fe768c810004fd768c810024fc768c81000ede638c810006dd638c810004ff764c810024fe764c810004fd764c810024fc764c81000ede634c810006dd634c810
  | 1 => 0xc1100077b658c11000778658c110025fb748c110215f9748c110007bb648c11020fb8648c11020f7b548c11020f79548c110045f9738c11000efa638c11000ef8638c110006fb628c110006f9628c110027f3718c11001dfa718c110025f8718c110027f0718c110026fb618c110027f3618c110007f3518c110007f0518c11020ff2418c11020ff1418c110047f2318c110047f1318c110007f2218c110007f1218c11000cff764c110044fd764c11001cfc764c1100067f654c1100067c654c110006bf644c1100b6bc644c110006df634c11000edc634c110005f7714c11001df4714c110007d5314c110027d8304c110027f0104c11001df8764c11000ef8764c11001cf8764c1100077b654c11000778654c110205fb744c110205f9744c110007bb644c1101ffb8644c1101ff7b544c1101ff79544c110025fb734c110027db734c110007db634c11000efa634c11000ef8634c110047d8634c110007db534c110047d8534c110047da434c1101ffd9434c110006fb624c110006f9624c110047db324c110007d9324c110007f3714c11001dfa714c11001df8714c110007f0714c110026fb614c110027f3614c110007f3514c110007f0514c1101fff2414c1101fff1414c110047db314c110047f2314c110007d9314c110047f1314c110007d1314c110007f2214c110007f1214c11001cfe76c811001cfc76c81100067f65c81100067c65c8110006bf64c81100aebc64c8110006ef62c811003eec62c811001df671c8110005f571c8110027f010c811003cff7648110004fd764811001cfc76481100067f65481100067c6548110006bf644811008ebc6448110006ef624811003eec6248110005f7714811001df47148110024fe75994100267e75994100d4ff7499410014fe7499410004fd7499410014fc74994100d67f54994100067d549941000cfe7399410004fd739941000cfc739941003cfe7299410004fd729941001cfe719941001cfc719941001e7e519941001e7c5199410024fe7099410024fc70994100267e50994100267c5099410026f71099410026f51099410024ff75594100267f7559410004ff7459410014fe7459410004fd7459410014fc74594100067f54594100067d5459410004ff735941000cfe735941000cfc7359410004ff725941003cfc725941001cff715941001cfe715941001cfd715941001cfc715941001e7e515941001e7c5159410024ff7059410024fe7059410024fd7059410024fc70594100267e50594100267c5059410004ff7558c100d4fc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c100067f5458c100067d5458c10024ff7358c10026df7358c1002ede5358c1002edc5358c10006df4358c1002ede4358c10006dd4358c1002edc4358c10004ff7258c1003cf
  | 2 => 0x255f5748c510007b7648c51024fb4648c51024f77548c51024f75548c510045f5738c51000ef6638c51000ef4638c510005f5728c510006f7628c510006f5628c51001ff3708c510025f6708c510025f4708c51001ff0708c51001ef7608c51001ff3608c51024ff2408c51024ff1408c510024fc764c5100057f754c5100057c754c5100067f654c5100067c654c510006bf644c51014ebc644c510006df634c51000edc634c51001fd4314c510005fb704c510025f8704c51001ff0104c510025f4764c51000ef4764c510024f4764c51000777754c510005f6754c510005f4754c51000774754c51000574754c51000777654c51000774654c510245f7744c510245f5744c510007b7644c51023fb4644c51023f77544c51023f75544c51001df7734c51001fd7734c510007d7634c51000ef6634c51000ef4634c510047d4634c510047d6434c51023fd5434c510005f7724c510006f7624c510006f5624c510007f3704c510025f6704c510025f4704c510007f0704c51001ef7604c51001ff3604c51023ff2404c51023ff1404c510047d7304c510024fe76c8510024fc76c85100057e75c85100057d75c85100067f65c85100067c65c851004dbe74c8510005bd74c8510006bf64c8510146bc64c8510006ef62c851003eec62c8510025fa70c8510005f970c851001ff010c8510005f6768851001ef67688510005f6758851001df4758851000777658851000774658851001df77488510235f57488510007b7648851022fb4648851022f77548851022f75548851001df77388510005f57388510006f76388510006f56388510225f5728851003ef6628851003ef46288510025f67088510025f4708851001ef7608851001ff3608851022ff2408851022ff14088510024fc76485100067f65485100067c6548510006bf6448510126bc6448510006ef624851003eec6248510005fb7048510025f87048510025f4764851003ef47648510024f47648510005f67548510005f47548510007776548510007746548510225f77448510225f57448510007b7644851021fb4644851021f77544851021f755448510005f77348510005f57348510006f76348510006f5634851001df7724851001fe77248510007e7624851003ef6624851003ef46248510007e4624851021fe6424851021fe54248510007f37048510025f67048510025f47048510007f07048510025f0704851001ef7604851001ff3604851021ff2404851021ff1404851001cfe76d41100067f65d41100d67c65d4110006bf64d41100debc64d411001df671d4110005f571d41100d4ff7654110004fd765411001cfc76541100067f65541100067c6554110006bf64541100eebc6454110005f7715411001df47154110027785054110027f01054110005fa768c110026fa768
  | 3 => 0xd5458910004ff7358910006df7358910004df735891000cfe735891000cfc7358910006dc735891000cdc7358910006ef7258910006ee4258910006ed4258910004ff7158910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc641891003eee6218910006ed62189100d4ff76d4910004fe76d4910004fd76d49100d4fc76d49100067f65d49100d67c65d4910006bf64d49101bebc64d491003cff7694910004fe7694910004fd769491003cfc76949100067f65949100067c6594910006bf64949101debc649491001df67194910005f57194910004ff7654910004fe7654910004fd7654910004fc76549100067f65549100067c6554910006bf64549101cebc6454910005df7354910045dc7354910005f7715491001df47154910005fb7054910025f8705491003cff7614910004fe7614910004fd761491003cfc76149100067f65149100d67c651491004dbe7414910005bd7414910006bf64149101b6bc641491001df67114910005f57114910025fa7014910005f9701491003cff768c910004fe768c910004fd768c91003cfc768c9100067f658c9100067c658c910006bf648c9101a6bc648c910006df638c91000edc638c91001df6718c910005f5718c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9100067c654c910006bf644c91019ebc644c910024fe76d45100067f65d45100d67c65d4510006bf64d451016ebc64d4510025fa70d4510005f970d4510025f676d4510006f676d4510024f676d451001df675d4510006f765d45100077765d4510006f565d45100077465d451027df774d451027df574d4510007b764d451016ef664d451016ef464d4510287b464d451016eb464d45102877754d45102877554d4510005f573d4510005f572d4510025f670d4510007f270d4510025f270d4510007f170d4510025f470d451001ef760d451001ff360d4510287f240d4510287f140d4510024fc76545100067f65545100067c6554510006bf645451017ebc645451001f745154510005fb7054510025f8705451001ff01054510005f6761451001ef6761451027df6751451001f767514510006f76514510007776514510006776514510006f5651451000774651451001df77414510275f57414510007b76414510166f66414510166f4641451025fb46414510166b4641451025f77541451025f755414510005f5731451026f76531451026f745314510005f57214510007775214510007755214510025f67014510025f4701451001ef7601451001ff3601451026776501451026774501451025ff2401451025ff14014510005f6768c51001ef6768c510005f6758c51001df4758c51000777658c51000774658c51001df7748c510
  | 4 => 0x9110006bc72d9110006bf32d9110006bc32d911028ebf71d9110296be71d911004ebd71d9110296bc71d9110296be51d9110296bc51d9110006bf31d9110296be31d9110296bc31d9110296be21d9110296bc21d9110296bf70d911028ebe70d911004ebd70d911028ebc70d911028ebe50d911028ebc50d9110006bf30d911028ebe30d911028ebc30d911028ebe20d911028ebc20d9110296bf10d911028ebe10d911004ebd10d911028ebc10d911000cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10046de63d8d100d4fe75d8d10004fd75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d100067f54d8d100067d54d8d1003cfe72d8d10004fd72d8d10046dc32d8d1001cfe71d8d10024fd71d8d1001cfc71d8d10046df31d8d10024fe70d8d1001cfd70d8d10024fc70d8d10046df30d8d100057f7558d100057c7558d100067f6558d100067c6558d10005bf7458d1004dbc7458d10006bf6458d10006bc6458d10046dc6358d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d100d4fc7558d100067c7558d100047c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d100067f5458d100067d5458d10044ff7358d10006df7358d10046de4358d10006dd4358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d1005cff7158d10006f77158d10064ff7058d10006fb7058d100d4ff76d4d10004fe76d4d10004fd76d4d100d4fc76d4d100067f65d4d100d67c65d4d10006bf64d4d101f6bc64d4d100475e53d4d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100067c6554d10006bf6454d101eebc6454d10005f77154d1001df47154d1003cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d89100d4fe75d8910004fd75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d89100067f54d89100067d54d891000cfe73d8910004fd73d891000cfc73d8910006ef32d8910006ec32d891001cfe71d891001cfc71d8910024fe70d8910024fc70d89100057e75989100057d75989100067f65989100067c659891004dbe7498910005bd7498910006bf6498910006bc6498910006ef62989100057f75589100057c75589100067f65589100067c6558910005bf745891004dbc7458910006bf6458910006bc6458910005df7358910045dc7358910004ff75589100067f75589100047f75589100d4fc75589100067c75589100047c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc74589100067f54589100067
  | 5 => 0xd67f54995100067d549951000cfe7399510004fd739951000cfc739951003cfe7299510004fd7299510004fd71995100d6f57199510004fd70995100d6f97099510005bf745951004dbc7459510006bc64595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510004fd7459510014fc7459510006bc7459510014bc74595100067f54595100067d5459510004ff735951000cfe735951000cfc7359510004ff725951003cfc7259510004ff7159510006f77159510004ff7059510006fb7059510004fe76195100067d6519510006bc64195100d67e75195100d4ff7419510014fe7419510004fd7419510014fc74195100d67f54195100067e54195100067d54195100d67c541951000cfe7319510004fd731951000cfc73195100067e53195100d67c531951003cfe7219510004fd721951001cfe711951001cfc7119510024fe7019510024fc70195100057e76195100067e76195100047e76195100057f74195100057d74195100067f64195100067e64195100067d64195100067c64195100073c64195100063c64195100067e63195100067c63195102677771195100077641195100077541195100077a401951000779401951029f7b101951026776101951026774101951029f7810195100d67f74195100047f74195100067e74195100067d74195100047d74195100d67c74195100d67f73195100067e73195100067d73195100d67c73195100067f43195100067e43195100067d43195100067c43195100d67f72195100067e72195100067d72195100d67c72195100067f42195100067e42195100067d42195100067c42195100067f32195100067c32195100d67f711951029e7e71195100067d71195100d67c71195100067f411951029e7e41195100067d411951029e7c41195100067f311951029e7e311951029e7c311951029e7e211951029e7c21195100d67f70195102667e70195100067d70195100d67c70195100067f40195102667e40195100067d40195102667c40195100067f30195102667e30195102667c30195102667e20195102667c201951029e7f10195102667e10195100067d10195102667c101951004dbe76d911004ebe76d9110014be76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d911028fb771d911004fb471d9110297bb70d911004fb870d9110297bb10d911028fb610d911028fb410d9110297b810d9110006bf75d91100063f75d9110006be75d9110006bd75d9110006bc75d91100063c75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006be53d9110006bc53d9110006bf72d9110006be72d9110006bd72d
  | 6 => 0xc7614a10055be7414a10005bd7414a10025fa7014a10005f97014a1003cff768ca10024fe768ca10004fd768ca10024fc768ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca1000ede634ca10006dd634ca100d67e65d46100067d65d4610025fa70d4610005f970d46100067e65546100067d6554610005fb7054610025f8705461000cff764c610024fc764c6100057f754c6100057c754c61000ede634c610006dd634c610005fb704c610025f8704c6100057e75c86100057d75c8610055be74c8610005bd74c861003eee62c8610006ed62c8610025fa70c8610005f970c861003cff764861003eee6248610006ed6248610005fb7048610025f87048610025fb764c21002efb764c2102bdfb744c2102bdf9744c2102b77b544c2102b779544c210027db734c210027db634c21000efa634c210026f8634c210027d8634c210007db534c21005fd8534c21005fda434c2102b7d9434c210026fb624c210006f9624c21005fdb324c210007d9324c21001dfa714c21001df8714c21005fdb314c210007d9314c210006bc64d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100067f54d95100067e54d95100067d54d95100067c54d951000cfe73d9510004fd73d951000cfc73d95100067e53d95100067c53d951003cfe72d9510004fd72d9510006f571d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067e63d95100067c63d95100077571d95100077641d95100077541d95100077a40d95100077940d95102af7b10d95102a77610d95102a77410d95102af7810d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067c32d95102a67f71d95102ae7e71d95100067d71d95100067571d95102ae7c71d95100067f41d95102ae7e41d95100067d41d95102ae7c41d95100067f31d95102ae7e31d95102ae7c31d95102ae7e21d95102ae7c21d95102ae7f70d95102a67e70d95100067d70d95102a67c70d95100067f40d95102a67e40d95100067d40d95102a67c40d95100067f30d95102a67e30d95102a67c30d95102a67e20d95102a67c20d95102ae7f10d95102a67e10d95102a67c10d95100067f659951004dbe7499510005bd7499510006bc64995100d4fe75995100047e75995100d4ff7499510014fe74995100d6be7499510014be7499510004fd74995100d6bd7499510004bd7499510014fc7499510
  | 7 => 0xc7102ddf5744c7102d777544c7102d775544c71001fd7734c71001fd7634c71000ef6634c71001ef4634c71001fd4634c710067d6434c7102d7d5434c710005f7724c71001ef7624c710006f5624c710025f6704c710025f4704c710067d7304c71001df77648710006f77648710005f67548710005f475487102cdf774487102cdf574487102c77754487102c7755448710005f77348710005f5734871001ef76348710006f5634871001fe7724871003ef6624871001ef462487102c7e642487102c7e54248710025f67048710025f470487100d67e65d43100067d65d431001df671d4310005f571d43100067e65543100067d6554310005f7715431001df4715431000cff764c31001cfc764c31000ede634c310006dd634c310005f7714c31001df4714c310007d5314c31003eee62c8310006ed62c831001df671c8310005f571c831003cff764831003eee6248310006ed6248310005f7714831001df471483100267e75996100d4ff7499610014fe7499610004fd7499610014fc74996100d67f54996100067d549961000cfe7399610004fd739961000cfc73996100067e53996100d67c539961003cfe7299610004fd7299610024fe70996100267e50996100267c5099610026f71099610026f510996100267f7559610004ff7459610014fe7459610004fd7459610014fc74596100067f54596100067d5459610004ff735961000cfe735961000cfc73596100067e53596100067c5359610004ff725961003cfc7259610024fc70596100267e50596100267c5059610004ff7558e100d4fc7558e10004ff7458e10014fe7458e10004fd7458e10014fc7458e100067f5458e100067d5458e10026df7358e1005edc5358e1005ede4358e10006dd4358e10004ff7258e1003cfc7258e1005edf3258e1005edf3158e10024fc7058e10026de3058e10026dc3058e10026f71058e10026f51058e100d4ff76d4e10024fe76d4e10004fd76d4e10024fc76d4e1000ede63d4e10006dd63d4e1005f5e53d4e10004ff7654e10024fe7654e10004fd7654e10024fc7654e10004ff7558a100d4fc7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a100067f5458a100067d5458a10004ff7358a1000cfe7358a1000cfc7358a10026ef7258a10006ee4258a10006ed4258a10024fc7058a10026fa3058a10026ee2058a10026ec2058a10026f71058a10026f51058a100d4ff76d4a10024fe76d4a10004fd76d4a10024fc76d4a100d67e65d4a100067d65d4a1003cff7694a10024fe7694a10004fd7694a10024fc7694a10004ff7654a10024fe7654a10004fd7654a10024fc7654a100067e6554a100067d6554a10005df7354a1005ddc7354a10005fb7054a10025f87054a1003cff7614a10024fe7614a10004fd7614a10024f
  | 8 => 0x156be648c420006bd648c42000ede638c420006dd638c42001ef6618c420006f5618c420004ff764c420004fd764c420024fc764c4200057f754c4200057c754c4200067e654c4200067d654c42014ebe644c420006bd644c42000ede634c420006dd634c420005ef724c42003dec724c42001ef6614c420006f5614c42001e7e75997100d4ff7499710014fe7499710004fd7499710014fc74997100d67f54997100067d549971000cfe7399710004fd739971000cfc739971003cfe7299710004fd7299710024fe719971001e7e519971001e7c519971001e7f7559710004ff7459710014fe7459710004fd7459710014fc74597100067f54597100067d5459710004ff735971000cfe735971000cfc7359710004ff725971003cfc7259710024fc715971001ef47159710024f4715971001e7e515971001e7c515971001ef45159710004ff7558f100d4fc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f100067f5458f100067d5458f1001edf7358f10066de4358f10006dd4358f10004ff7258f1003cfc7258f10024fc7158f1001ede3158f1001edc3158f1001ef62158f10066df3058f1001efa1058f1001ef91058f100d4ff76d4f1001cfe76d4f10004fd76d4f1001cfc76d4f100675e53d4f1001df471d4f10004ff7654f1001cfe7654f10004fd7654f1001cfc7654f10005f77154f1001df47154f10004ff7558b100d4fc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b100067f5458b100067d5458b10004ff7358b1000cfe7358b1000cfc7358b1001eef7258b10006ee4258b10006ed4258b10024fc7158b1001ef63158b1001eee2158b1001eec2158b100d4ff76d4b1001cfe76d4b10004fd76d4b1001cfc76d4b102fe7f65d4b100d67c65d4b1001df471d4b102ff7451d4b1003cff7694b1001cfe7694b10004fd7694b1001cfc7694b1001df67194b10005f57194b10004ff7654b1001cfe7654b10004fd7654b1001cfc7654b102f67f6554b102f67c6554b10005df7354b10065dc7354b10005f77154b1001df47154b102f7745154b1003cff7614b1001cfe7614b10004fd7614b1001cfc7614b1006dbe7414b10005bd7414b1001df67114b10005f57114b1003cff768cb1001cfe768cb10004fd768cb1001cfc768cb1001df6718cb10005f5718cb10004ff764cb1001cfe764cb10004fd764cb1001cfc764cb1001df6714cb1001df576d4710006f576d471001f7675d471001ef765d4710006f565d47102edf774d47102edf574d471016ef664d471001ef464d47102e77754d47102e77554d4710005f573d4710005f572d4710025f670d4710025f470d471001df7764c71002ef7764c71000777754c710005f6754c710005f4754c71000774754c71000574754c7102ddf7744
  | 9 => 0x7729842001ef6729842001ef5729842001ef4729842003ef7529842003ef6529842003ef5529842003ef4529842003ef7429842003ef6429842003ef5429842003ef4429842003ef7329842003ef6329842003ef5329842003ef43298420026f77098420026f67098420026f57098420026f47098420026f75098420026f65098420026f55098420026f45098420026f74098420026f64098420026f54098420026f44098420026f73098420026f63098420026f53098420026f43098420026f72098420026f62098420026f52098420026f42098420004ff75584200d4fc7558420004ff7458420014fe7458420004fd7458420014fc74584200067f54584200067d5458420004ff735842000cfe735842000cfc7358420026f77158420006f74158420006f64158420006f54158420006f44158420006f73158420006f4315842003ef7215842003ef42158420024ff7058420024fd7058420026f61058420026f41058420006f77558420006f67558420006f57558420006f47558420006f77458420006f67458420006f57458420006f47458420006f75458420006775458420006f65458420006f55458420006755458420006f45458420006f77358420006f67358420006f57358420006f47358420006f75358420006f65358420006f55358420006f45358420006f74358420006f64358420006f54358420006f4435842003ef7725842003ef6725842003ef4725842003ef7525842003ef6525842003ef5525842003ef4525842003ef7425842003ef6425842003ef5425842003ef4425842003ef7325842003ef6325842003ef5325842003ef43258420026f77058420026f67058420026f47058420026f75058420026f65058420026f55058420026f45058420026f74058420026f64058420026f54058420026f44058420026f73058420026f63058420026f53058420026f43058420026f72058420026f62058420026f52058420026f420584200d4ff76d4420024fe76d4420004fd76d44200d67e65d44200067d65d442016ebe64d4420006bd64d4420196de63d4420006dd63d442001ef661d4420006f561d442001cff7694420024fe7694420004fd76944200067e65944200067d659442018ebe6494420006bd6494420186de6394420006dd639442001ef66194420006f56194420025fa7094420005f97094420004ff7654420004fd7654420024fc76544200067e65544200067d655442017ebe6454420006bd6454420176de6354420006dd635442001ef66154420006f5615442001cff7614420024fe7614420004fd76144200d67e65144200067d6514420166be6414420006bd641442015ede6314420006dd631442001ef66114420006f5611442001cff768c420024fe768c420004fd768c4200067e658c4200067d658c420
  | 10 => 0x9020006bc7159020006bf3159020006bc315902003ebf215902003ebe215902003ebd215902003ebc2159020026bf7059020026be7059020026bd7059020026bc7059020026bf5059020026be5059020026bd5059020026bc5059020026bf3059020026be3059020026bd3059020026bc3059020026bf2059020026af2059020026be2059020026bd2059020026ad2059020026bc2059020026bf1059020026be1059020026bd1059020026bc1059020004ff7558c200d4fc7558c20004ff7458c20014fe7458c20004fd7458c20014fc7458c200067f5458c200067d5458c20024ff7358c20026df7358c20076de5358c20076dc5358c20006df4358c20076de4358c20006dd4358c20076dc4358c2003cff7258c2003cfe7258c2003cfd7258c2003cfc7258c2003ede3258c2003edc3258c20004ff7158c2001cfc7158c20076df3158c20076dc3158c20024fe7058c20024fc7058c20026de3058c20026dc3058c20026fa2058c2003ef92058c20006df7558c20006de7558c20006dd7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c200065f5458c20006de5458c20006dd5458c200065d5458c20006dc5458c2003edf7258c2003ede7258c2003edd7258c2003edc7258c2003edf5258c2003ede5258c2003edd5258c2003edc5258c2003edf4258c2003ede4258c2003edd4258c2003edc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df4158c20006de4158c20006dd4158c20006dc4158c2003edf2158c2003ede2158c2003edd2158c2003edc2158c20026df7058c20026de7058c20026dd7058c20026dc7058c20026df5058c20026de5058c20026dd5058c20026dc5058c20026df4058c20026de4058c20026dd4058c20026dc4058c20026df2058c20026de2058c20026da2058c20026dd2058c2003ed92058c20026dc2058c20026df1058c20026de1058c20026dd1058c20026dc1058c200d4ff76d4c20024fe76d4c20004fd76d4c20024fc76d4c200d67e65d4c200067d65d4c201f6be64d4c20006bd64d4c2000ede63d4c20006dd63d4c200775e53d4c20004ff7654c20024fe7654c20004fd7654c20024fc7654c200067e6554c200067d6554c201eebe6454c20006bd6454c2000ede6354c20006dd6354c20005ef7254c2003dec7254c2001ef7759842001ef6759842001ef5759842001ef4759842001ef7749842001ef6749842001ef5749842001ef47498420006f75498420006775498420006f65498420006f55498420006755498420006f4549842001ef7739842001ef6739842001ef5739842001ef47398420006f75398420006f65398420006f55398420006f45398420006f74398420006f64398420006f54398420006f4439842001ef
  | 11 => 0x67d74994200047d74994200d67c74994200d67f73994200067e73994200067d73994200d67c73994200067f43994200067e43994200067d43994200067c439942003e7f729942003e7e729942003e7d729942003e7c729942003e7f429942003e7e429942003e7d429942003e7c429942003e7f329942003e7e329942003e7d329942003e7c32994200d67f71994200067e71994200067d71994200d67c71994200067f41994200067e41994200067d41994200067c41994200067f31994200067c319942003e7f219942003e7e219942003e7d219942003e7c21994200267f70994200267e70994200267d70994200267c70994200267f40994200267e40994200267d40994200267c40994200267f30994200267e30994200267d30994200267c30994200267f20994200267e20994200267d20994200267c20994200267f10994200267e10994200267d10994200267c1099420024ff75594200267f7559420004ff7459420014fe7459420004fd7459420014fc74594200067f54594200067e54594200067d54594200067c5459420004ff735942000cfe735942000cfc73594200067e53594200067c535942003cff725942003cfe725942003cfd725942003cfc725942003e7e525942003e7c5259420004ff715942001cfc7159420024fe7059420024fc70594200267e50594200267c50594200067f74594200047f74594200067e74594200067d74594200047d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067d43594200067c435942003e7f725942003e7e725942003e7d725942003e7c725942003e7f425942003e7e425942003e7d425942003e7c425942003e7f325942003e7e325942003e7d325942003e7c32594200067f71594200067e71594200067d71594200067c71594200067f41594200067e41594200067d41594200067c41594200067f31594200067c315942003e7f215942003e7e215942003e7d215942003e7c21594200267f70594200267e70594200267d70594200267c70594200267f40594200267e40594200267d40594200267c40594200267f30594200267e30594200267d30594200267c30594200267f20594200267e20594200267d20594200267c20594200267f10594200267e10594200267d10594200267c1059420006bf7559020006be75590200063e7559020006bd75590200063d7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006be5359020006bc535902003ebf725902003ebe725902003ebd725902003ebc725902003ebf525902003ebe525902003ebd525902003ebc525902003ebf325902003ebe325902003ebd325902003ebc3259020006bf7159020006be7159020006bd715
  | 12 => 0xa70d4920005f970d4920024fc76549200067f65549200067c6554920005df7354920085dc7354920005fb7054920025f8705492003fe82054920024fc764c920006df634c92000edc634c920005fb704c920025f8704c9200d4fe75d8520004fd75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d85200067f54d85200067d54d852000cfe73d8520004fd73d852000cfc73d8520006ee42d8520006ed42d8520024fe70d8520024fc70d8520006f761985200057f75585200057c7558520005bf745852008dbc7458520005df7358520085dc735852001ef66118520006f56118520004fe76d4520004fd76d45200d4fc76d4520004fe7694520004fd769452001cfc76945200067f65945200067c6594520004ff7654520004fe7654520004fc7654520004fe7614520004fd761452001cfc76145200067f65145200d67c651452003dee7214520005ed7214520025fa7014520005f97014520004fe768c520004fd768c52001cfc768c520006df638c52000edc638c52001ef6618c520004ff764c520004fe764c520004fc764c5200057f754c5200057c754c520024fe7688520006f7618852001ef46188520025fa7088520005f97088520024fc7648520006f7614852001ef46148520005fb7048520025f8704852003cfe76d41200067f65d41200d67c65d412003dee72d4120005ed72d41200d4ff7654120004fd765412003cfc76541200067f65541200067c6554120005ef725412003dec7254120027e82054120005fa768c120026fa768c12030f7b548c12030f79548c120085f9738c12000efa638c12000ef8638c12003dfa728c120025f8728c120026fb628c120027eb628c12030fea428c12030fe9428c120006fb618c12000cff764c120084fd764c12003cfc764c120006df634c12000edc634c120005ef724c12003dec724c120027d8304c12003df8764c12000ef8764c12003cf8764c1203077b544c12030779544c120025fb734c120027db734c120007db634c12000efa634c12000ef8634c120087d8634c120007db534c120087d8534c120087da434c120307d9434c120007eb724c12003dfa724c12003df8724c120007e8724c120026fb624c120027eb624c120307ea424c120307e9424c120087db324c120007d9324c120006fb614c120087db314c120007d9314c120024fe75994200267e75994200d4ff7499420014fe7499420004fd7499420014fc74994200d67f54994200067e54994200067d54994200d67c549942000cfe7399420004fd739942000cfc73994200067e53994200d67c539942003cfe729942003cfc729942003e7e529942003e7c529942001cfe7199420004fd7199420024fe7099420024fc70994200267e50994200267c50994200d67f74994200047f74994200067e7499420
  | 13 => 0xc620006f5618c620004ff764c620004fd764c620024fc764c6200057f754c6200057c754c62000ede634c620006dd634c620005ef724c62003dec724c62001ef6614c620006f5614c62001ef66188620006f56188620025fa7088620005f9708862001cff764862001ef66148620006f56148620005fb7048620025f87048620025fb764c220076fb764c2203177b544c22031779544c220027db734c220027db634c22000efa634c220026f8634c220027d8634c220007db534c220097d8534c220097da434c220317d9434c22003dfa724c22003df8724c220097db324c220007d9324c220006f9614c220097db314c220007d9314c220004ff74d9520014fe74d9520004fd74d9520014fc74d95200067f54d95200067d54d952000cfe73d9520004fd73d952000cfc73d95200067e53d95200067c53d952001cfe71d9520004fd71d95200067f65995200d4fe75995200d4ff7499520014fe7499520004fd7499520014fc74995200d67f54995200067d549952000cfe7399520004fd739952000cfc7399520004fd72995200d6ed729952001cfe7199520004fd7199520004fd70995200d6f97099520005df7359520085dc73595200067f7559520004ff7459520014fe7459520004fd7459520014fc74595200067f54595200067d5459520004ff7359520006df7359520004df735952000cfe735952000cfc7359520006dc735952000cdc7359520004ff7259520006ef7259520004ff715952001cfc7159520004ff7059520006fb7059520004fe76195200067d65195200d67e75195200d4ff7419520014fe7419520004fd7419520014fc74195200d67f54195200067d541952000cfe7319520004fd731952000cfc73195200067e53195200d67c531952003cfe721952003cfc721952001cfe7119520004fd711952000cfe76d8d20086de63d8d200d4fe75d8d20004fd75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d200067f54d8d200067d54d8d20086dc53d8d20086de43d8d20006dd43d8d2003cfe72d8d20024fd72d8d2003cfc72d8d20086df32d8d2001cfe71d8d20004fd71d8d20086dc31d8d2003cfd70d8d20086df30d8d200057f7558d200057c7558d20086dc6358d20004ff7558d200067f7558d200047f7558d200d4fc7558d200067c7558d200047c7558d20004ff7458d20014fe7458d20004fd7458d20014fc7458d200067f5458d200067d5458d20084ff7358d20006df7358d20094ff7258d20006ef7258d20004ff7158d2001cfc7158d200a4ff7058d20006fb7058d200d4ff76d4d20004fe76d4d20004fd76d4d200d4fc76d4d20006df63d4d2000edc63d4d200875e53d4d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20024fe76d49200067f65d49200d67c65d4920025f
  | 14 => 0x67e65947200067d6594720025fa7094720005f97094720004ff7654720004fd765472003cfc765472001cff761472003cfe7614720004fd76147200d67e65147200067d651472003dee7214720005ed721472001cff768c72003cfe768c720004fd768c72001ef6618c720006f5618c720004ff764c720004fd764c72003cfc764c7200057f754c7200057c754c72001ef6614c720006f5614c7200d67e65d43200067d65d432003dee72d4320005ed72d43200067e65543200067d6554320005ef725432003dec725432000cff764c32003cfc764c32000ede634c320006dd634c320005ef724c32003dec724c3200267e75996200d4ff7499620014fe7499620004fd7499620014fc74996200d67f54996200067d549962000cfe7399620004fd739962000cfc739962001cfe7199620004fd7199620024fe70996200267e50996200267c50996200267f7559620004ff7459620014fe7459620004fd7459620014fc74596200067f54596200067d5459620004ff735962000cfe735962000cfc7359620004ff715962001cfc7159620024fc70596200267e50596200267c5059620004ff7558e200d4fc7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e200067f5458e200067d5458e20026df7358e20096dc5358e20096de4358e20006dd4358e20096df3258e20004ff7158e2001cfc7158e20096df3158e20024fc7058e20026de3058e20026dc3058e200d4ff76d4e20024fe76d4e20004fd76d4e20024fc76d4e2000ede63d4e20006dd63d4e200975e53d4e20004ff7654e20024fe7654e20004fd7654e20024fc7654e20005ef7254e2003dec7254e200d67e65d4a200067d65d4a20025fa70d4a20005f970d4a200067e6554a200067d6554a20005df7354a20095dc7354a20005fb7054a20025f87054a2000cff764ca20024fc764ca2000ede634ca20006dd634ca2003fcc324ca20005fb704ca20025f8704ca20004ff75586200067f75586200047f75586200d4fc75586200067c75586200047c7558620004ff7458620006bf7458620004bf7458620014fe7458620004fd7458620014fc7458620006bc7458620014bc74586200067f54586200067d5458620004ff735862000cfe735862000cfc7358620026f77158620006f64158620006f54158620024fc7058620026fa3058620026f61058620026f410586200d4ff76d4620024fe76d4620004fd76d462001ef661d4620006f561d462001cff7694620024fe7694620004fd76946202a67f65946202a67c6594620004ff7654620004fd7654620024fc765462001cff7614620024fe7614620004fd76146202667f65146200d67c651462001ef66114620006f56114620025fa7014620005f9701462001cff768c620024fe768c620004fd768c62001ef6618
  | 15 => 0xd731453015f5c5314530025fa7014530005f97014530024dc764c5300075f754c530005de754c530005dc754c5300075c754c5300055c754c53032ddf744c53032ddd744c530326df644c530326dd644c5303275f544c5303275d544c530005df724c53000ddf714c53000fd7714c530007d7614c53001ede614c53001edc614c530007d4614c530007db704c530025de704c530025dc704c530007d8704c53000edf604c53000fdb604c530004fe76c8530004fd76c853003cfc76c85300057e75c85300057d75c85300b5be74c8530005bd74c853000dde73c8530005dd73c8530025fa70c8530005f970c8530004fe7688530004fd768853001cfc768853000dde7388530005dd7388530006ef628853003eec628853001ef66188530007d53188530025fa7088530005f97088530004ff7648530004fe7648530004fc764853000dde7348530005dd7348530007d53148530004fe7608530004fd760853001cfc760853000dde7308530005dd7308530006ef620853003eec6208530025fa7008530005f9700853000cfe76d413000cfc76d41300067f65d41300d67c65d413000dde73d4130005dd73d41300277a50d41300d4ff765413000cfe76541300e4fd765413000cfc76541300067f65541300067c6554130005df735413000ddc7354130027d8305413003e7e75997200d4ff7499720014fe7499720004fd7499720014fc74997200d67f54997200067d549972000cfe7399720004fd739972000cfc7399720024fe729972003e7e529972003e7c529972001cfe7199720004fd719972003e7f7559720004ff7459720014fe7459720004fd7459720014fc74597200067f54597200067d5459720004ff7359720006df7359720004df735972000cfe735972000cfc7359720006dc735972000cdc7359720024fc725972003e7e525972003e7c5259720004ff715972001cfc7159720004ff7558f200d4fc7558f20004ff7458f20014fe7458f20004fd7458f20014fc7458f200067f5458f200067d5458f2003edf7358f20024fc7258f2003ede3258f2003edc3258f20004ff7158f2001cfc7158f200a6df3058f2003efa2058f2003ef92058f200d4ff76d4f2003cfe76d4f20004fd76d4f2003cfc76d4f200d67e65d4f200067d65d4f2031edf63d4f2000edc63d4f200a75e53d4f20004ff7654f2003cfe7654f20004fd7654f2003cfc7654f200067e6554f200067d6554f20004ff75587200d4fc7558720004ff7458720014fe7458720004fd7458720014fc74587200067f54587200067d5458720004ff735872000cfe735872000cfc7358720024fc725872003eee4258720006ed425872003ef7715872003ef7215872003ef421587200d4ff76d472003cfe76d4720004fd76d472001cff769472003cfe7694720004fd7694720
  | 16 => 0x953000cfc73195300d67f53195300c67d531953003cfe7219530004fd721953001cfe7119530004fd7119530025de76d4d30006de76d4d30024de76d4d3000dde75d4d3000f5e75d4d30006df65d4d300075f65d4d300065f65d4d30006dd65d4d300075c65d4d3034ddf74d4d3034ddd74d4d303475f54d4d303475d54d4d30005dd72d4d3031edc62d4d30005dd71d4d30025de70d4d30007da70d4d30025da70d4d30007d970d4d30025dc70d4d3000edf60d4d3000fdb60d4d300d4fe75d8930004fd75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d89300067f54d89300067d54d8930024fd73d8930006ee42d8930006ed42d8930096ee32d8930096ed32d893001cfe71d8930004fd71d8930006ef6298930085f970989300057f75589300057c75589300a5fb70589300057e75189300057d75189300b5be7418930005bd741893003eee6218930006ed6218930005f67118930005f57118930004fe76d4930004fd76d49300d4fc76d49300d67e65d49300067d65d493000ddc73d49300075f53d4930006ef62d493003eec62d4930004fe7694930004fd769493003cfc76949300067f65949300067c659493000dde7394930005dd7394930025fa7094930005f97094930004ff7654930004fe7654930004fc76549300067e65549300067d6554930005df735493000ddc73549300075f5354930004fe7614930004fd761493003cfc76149300067f65149300d67c65149300b5be7414930005bd741493000dde7314930005dd7314930006ef621493003eec6214930025fa7014930005f97014930024dc764c930005de754c930005dc754c93033ddf744c93033ddd744c9303375f544c9303375d544c93000ddf724c93000fcf724c930007cf624c93003ede624c93003edc624c930007cc624c93003ecc624c930005df714c930007db704c930025de704c930025dc704c930007d8704c93000edf604c93000fdb604c9300d4fe75d8530004fd75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d85300067f54d85300067d54d8530024fd73d853005ede43d8530006dd43d853003cfe72d8530004fd72d853005ef631d853005ef531d8530006f76198530045f970985300057f75585300057c7558530005bf74585300b5bc7458530005ef7258530005ec7258530065fb705853001ef66118530006f56118530004fe76d4530004fd76d45300d4fc76d453000ddc73d4530004fe7694530004fd769453001cfc76945300067f65945300067c659453000dde7394530005dd73945301875c5394530025fa7094530005f97094530004ff7654530004fe7654530004fc7654530005df735453000ddc7354530004fe7614530004fd761453001cfc76145300067f65145300d67c651453000dde7314530005d
  | 17 => 0x1cfc7158a30024fc7058a30026df3058a30026dd3058a30026ee2058a30026ec2058a300d4ff76d4a30024fe76d4a30004fd76d4a300d67e65d4a300067d65d4a3003cff7694a30024fe7694a30004fd7694a30025fa7094a30005f97094a30004ff7654a30004fd7654a30024fc7654a300067e6554a300067d6554a30005df7354a3000ddc7354a3003cff7614a30024fe7614a30004fd7614a300bdbe7414a30005bd7414a30025fa7014a30005f97014a30004ff75586300d4fc7558630004ff7458630014fe7458630004fd7458630014fc74586300067f54586300067d5458630004ff725863003cfc7258630026f77158630006f64158630006f54158630046f63158630046f53158630024fc7058630026df3058630026dd3058630026f61058630026f410586300d4ff76d4630024fe76d4630004fd76d463001ef661d4630006f561d463001cff7694630024fe7694630004fd76946300067e65946300067d6594630025fa7094630005f97094630004ff7654630004fd7654630024fc765463001cff7614630024fe7614630004fd76146300d67e65146300067d651463001ef66114630006f56114630025fa7014630005f9701463003cff76c8630024fe76c8630004fd76c86300057e75c86300057d75c86300bdbe74c8630005bd74c8630025fa70c8630005f970c863001cff7688630024fe7688630004fd768863001ef66188630006f56188630025fa7088630005f97088630004ff7648630004fd7648630024fc7648630005df734863000ddc734863001ef66148630006f56148630025fa704863001cff7608630024fe7608630004fd7608630025fa7008630005f97008630004ff74d9530014fe74d9530004fd74d9530014fc74d95300067f54d95300067d54d9530024ff73d9530024fd73d9530006dd73d95300f67f53d95300f67d53d95300f6dc53d953003cfe72d9530004fd72d953001cfe71d9530004fd71d95300067f65995300e5f970995300d4fe75995300d4ff7499530014fe7499530004fd7499530014fc74995300d67f54995300067d5499530104fd73995300d6dd739953003cfe7299530004fd729953001cfe7199530004fd71995300e4fd70995300d6f97099530005ef7259530005ec7259530105fb70595300067f7559530004ff7459530014fe7459530004fd7459530014fc74595300067f54595300067d54595300e4ff7359530006df73595300e6dc5359530004ff7259530006ef7259530004ef725953003cfc7259530006ec725953003cec7259530004ff715953001cfc7159530104ff7059530006fb70595300f4fe76195300067d65195300d67e75195300d4ff7419530014fe7419530004fd7419530014fc74195300d67f54195300067d5419530024ff731953000cfe7319530024fd731
  | 18 => 0xd628c850004ff764c850004fd764c850024fc764c8500057f754c8500d57c754c85000ede634c850006dd634c85003eee624c850006ed624c850004ff7458450014fe7458450004fd7458450014fc74584500067f54584500067d5458450004ff735845000cfe735845000cfc7358450004ff725845003cfc7258450026f771584500d6f751584500d6f45158450006f64158450006f54158450026f61058450026f41058450004fd76944502a57d769445029e7d769445029d7f749445036d7d74944502a67f64944503667d64944501867e63944502a67c63944500067d62944500d57e71944502a67f619445029e7d61944502a57f70944502a57d70944502a67e60944502a77a6094450004ff76544500d57f741445035d7d74144500d67f64144503567d641445015e7e63144500d67c63144500067d62144502a57e71144500d77671144500d67f61144500d776611445029e7d61144500d775611445000675611445035777411445029f7441144500d57f70144500d77a70144502657d70144500d77970144500057970144502667e60144500d77a601445026777101445001cff768c450024fe768c450004fd768c45001ef6618c450006f5618c450004ff764c450004fd764c450024fc764c4500057f754c4500d57c754c45000ede634c450006dd634c45001ef6614c450006f5614c45003cff76c8450024fe76c8450004fd76c84500d57e75c84500057d75c84500cdbe74c8450005bd74c845003eee62c8450006ed62c845001cff7688450024fe7688450004fd768845001ef66188450006f56188450025fa7088450005f97088450004ff7648450004fd7648450024fc76484500057f75484500d57c754845003eee6248450006ed624845001ef66148450006f5614845001cff7608450024fe7608450004fd7608450025fb7654050006fb7654050004fb7654050025fb75540500277b75540500d6fa65540500277a65540500d77b51540500077951540500267e75996300d4ff7499630014fe7499630004fd7499630014fc74996300d67f54996300067d54996300d67f53996301067d539963003cfe7299630004fd729963001cfe7199630004fd7199630024fe7099630024fc70996300267e50996300267c5099630026df3099630026dd30996300267f7559630004ff7459630014fe7459630004fd7459630014fc74596300067f54596300067d54596300e67f53596300e67d5359630004ff725963003cfc7259630004ff715963001cfc7159630024fe7059630024fc70596300267e50596300267c5059630004ff7558a300d4fc7558a30004ff7458a30014fe7458a30004fd7458a30014fc7458a300067f5458a300067d5458a30026ef7258a30006ee4258a30006ed4258a30086ee3258a30086ed3258a30004ff7158a30
  | 19 => 0x49500257c70d49500d67f60d4950024fe76949503957d7594950006ef629495003eec6294950025fa7094950005f97094950024fc7654950005df73549500e5dc7354950006ef625495003eec6254950005fb7054950025f870549500247c76549503957f74549503957d745495038e7f645495038e7d64549500075f73549500075c73549500067f63549500076f72549500076f625495003e7e625495003e7c62549500076c62549502f67c61549500077b70549500257e70549500257c7054950007787054950004fe76149503857e75149500edbe7414950005bd7414950004fe768c950004fd768c95003cfc768c9500057e758c9500057d758c950006df638c95000edc638c950004ff764c950004fe764c950004fc764c950004ff74d8550014fe74d8550004fd74d8550014fc74d85500067f54d85500067d54d855000cfe73d8550004fd73d855000cfc73d855003cfe72d8550004fd72d8550006f741d8550006f441d85502a67f6598550006f76198550005bf74585500edbc74585502667f651855001ef66118550006f56118550004fe76d4550024fe7694550006f7619455001ef46194550025fa7094550005f97094550024fc7654550006f7615455001ef46154550005fb7054550025f87054550004fe761455001ef66114550007755114550004fe768c550004fd768c55001cfc768c550004ff764c550004fe764c550004fc764c5500057f754c5500057c754c550004fe76c8550004fd76c855003cfc76c85500057e75c85500057d75c85500edbe74c8550005bd74c8550004fe7688550004fd768855001cfc7688550004ff7648550004fe7648550004fc7648550004fe7608550004fd760855001cfc76085500057e75085500057d7508550025fa7008550005f970085500257e75d41500267f65d4150024fa76d4150025fa75d4150026fb65d41500277b65d41500d77b54d415037f7954d41500d77b52d41500077952d415000cfd7558c50004ff7458c50014fe7458c50004fd7458c50014fc7458c500067f5458c500067d5458c50026df7358c500d6df5358c500d6dc5358c500c6de4358c50006dd4358c50004ff7258c5003cfc7258c500c6df3258c50004ff7158c5001cfc7158c500c6df3158c50024fc7058c50026de3058c50026dc3058c50104ff7654c50004ff7458850014fe7458850004fd7458850014fc74588500067f54588500067d5458850004ff735885000cfe735885000cfc7358850026ef72588500d6ef52588500d6ec5258850006ee4258850006ed4258850004ff715885001cfc71588500267f50588500267d5058850026ee2058850026ec2058850004fd7694850004ff76548503767e6554850005df73548500c5dc735485003cff768c850024fe768c850004fd768c85003eee628c850006e
  | 20 => 0x3be7d64946501867e63946502a75e63946501865e63946502a75d63946502a67c63946500067d62946502a67f61946502a77661946502ae7d61946502a77561946502a77a70946502a57d70946502af79709465001cff7654650176de6354650006dd635465001ef66154650006f56154650005fb7054650025f8705465015ede6314650006dd631465001ef66114650006f561146502657d76146502ae7d76146502ad7f74146503b57d74146502667f64146503ae7d641465015e7e63146502675e631465015e5e63146502675d63146502667c63146500067d62146502af7671146502667f61146502677661146502ae7d61146502677561146500067561146503af7741146502af7441146502657f70146502657d701465026777101465001cff768c650024fe768c650004fd768c65000ede638c650006dd638c65001ef6618c650006f5618c650004ff764c650004fd764c650024fc764c6500057f754c6500057c754c65000ede634c650006dd634c65001ef6614c650006f5614c65003cff76c8650024fe76c8650004fd76c86500057e75c86500057d75c86500fdbe74c8650005bd74c865013ede63c8650006dd63c865001ef661c8650006f561c865001cff7688650024fe7688650004fd768865012ede6388650006dd638865001ef66188650006f56188650004ff7648650004fd7648650024fc76486500057f75486500057c754865011ede6348650006dd634865001ef66148650006f5614865001cff7608650024fe7608650004fd760865010ede6308650006dd630865001ef66108650006f56108650025fa7008650005f97008650025f976d42500d6f976d42500277a75d42500d77b54d42503a77954d4250027da63d4250027d963d42500d77b53d42500077953d4250027f261d4250027f161d425000cfe76d8d500e6de63d8d50024fd75d8d5000cfc75d8d50004ff74d8d50014fe74d8d50004fd74d8d50014fc74d8d500067f54d8d500067d54d8d500e6de53d8d5003cfe72d8d50004fd72d8d500e6dc32d8d5001cfe71d8d50004fd71d8d500e6df30d8d500e6dc6358d50005ef7258d50005ec7258d500f4fe76d4d5000ede63d4d500e75e53d4d50024fc7654d50006df6354d5000edc6354d50005fb7054d50025f87054d50004ff74d8950014fe74d8950004fd74d8950014fc74d89500067f54d89500067d54d895000cfe73d8950004fd73d895000cfc73d8950006ef32d8950006ec32d895001cfe71d8950004fd71d8950006ef6298950005df73589500e5dc73589500edbe7418950005bd741895003eee6218950006ed6218950004fe76d49500057e76d49500067e76d49503857f74d49503857d74d495039e7f64d495039e7d64d49500067f63d495003e7e62d495003e7c62d49502fe7c61d49500257e70d
  | 21 => 0xe6354a50006dd6354a5003eee6254a50006ed6254a50005fb7054a50025f87054a500fdbe7414a50005bd7414a501aede6314a50006dd6314a5003cff768ca50024fe768ca50004fd768ca5000ede638ca50006dd638ca50004ff764ca50004fd764ca50024fc764ca500057f754ca500057c754ca5000ede634ca50006dd634ca5001ef7759865001ef7749865001ef6749865001ef5749865001ef47498650006f75498650006775498650006f65498650006f55498650006755498650006f4549865001ef7739865001ef6739865001ef5739865001ef47398650006f75398650006f65398650006f55398650006f45398650006f74398650006f64398650006f54398650006f4439865001ef7729865001ef6729865001ef5729865001ef47298650006f75298650006f65298650006f55298650006f45298650006f74298650006f64298650006f54298650006f44298650006f73298650006f63298650006f53298650006f43298650026f77098650026f67098650026f57098650026f47098650026f75098650026f65098650026f55098650026f45098650026f74098650026f64098650026f54098650026f44098650026f73098650026f63098650026f53098650026f43098650026f72098650026f62098650026f52098650026f42098650004ff7458650014fe7458650004fd7458650014fc74586500067f54586500067d5458650004ff735865000cfe735865000cfc7358650004ff725865003cfc7258650026f77158650006f74158650006f64158650006f54158650006f44158650006f73158650006f43158650026f61058650026f41058650006f57558650006f77458650006f67458650006f57458650006f47458650006f75458650006775458650006f65458650006f55458650006755458650006f45458650006f77358650006f67358650006f57358650006f47358650006f75358650006f65358650006f55358650006f45358650006f74358650006f64358650006f54358650006f44358650006f77258650006f67258650006f57258650006f47258650006f75258650006f65258650006f55258650006f45258650006f74258650006f64258650006f54258650006f44258650006f73258650006f63258650006f53258650006f43258650026f77058650026f67058650026f47058650026f75058650026f65058650026f55058650026f45058650026f74058650026f64058650026f54058650026f44058650026f73058650026f63058650026f53058650026f43058650026f72058650026f62058650026f52058650026f42058650196de63d4650006dd63d465001ef661d4650186de6394650006dd639465001ef66194650006f56194650025fa7094650005f970946502ad7f74946503c57d74946502a67f6494650
  | 22 => 0x4b500075c7354b500067d6354b500d76f7254b5003e7e6254b5003e7c6254b502f67e6154b500257e7054b500257c7054b5003cff768cb500d4fe768cb50004fd768cb500d57e758cb500057d758cb50004ff764cb50004fd764cb500d4fc764cb502a67e65987500d6f7619875001ef461987500d6f46158750024fc7558750004ff7458750014fe7458750004fd7458750014fc74587500067f54587500067d5458750004ff735875000cfe735875000cfc7358750004ff725875003cfc72587500d6f751587500d6f451587500d774515475001cff768c7500d4fe768c750004fd768c750004ff764c750004fd764c7500d4fc764c7500057f754c7500d57c754c75003cff76c87500d4fe76c8750004fd76c87500d57e75c87500057d75c87500ddbe74c8750005bd74c875001cff76887500d4fe7688750004fd7688750025fa7088750005f97088750004ff7648750004fd76487500d4fc764875001cff76087500d4fe7608750004fd76087500d57e75087500057d7508750004ff7458e50014fe7458e50004fd7458e50014fc7458e500067f5458e500067d5458e50026df7358e500f6de5358e50006df4358e500f6de4358e50006dd4358e500f6dc4358e50004ff7258e5003cfc7258e500f6df3258e500f6dc3258e50004ff7158e5001cfc7158e500f6df3158e500f6dc3158e50024fc7058e50026de3058e50026dc3058e50006dd7558e500f6dc7558e50006df7458e50006de7458e50006dd7458e50006dc7458e50006df5458e500065f5458e50006de5458e50006dd5458e500065d5458e50006dc5458e50006df7258e50006de7258e50006dd7258e50006dc7258e50006df4258e50006de4258e50006dd4258e50006dc4258e50006df7158e50006de7158e50006dd7158e50006dc7158e50006df4158e50006de4158e50006dd4158e50006dc4158e50026df7058e50026de7058e50026dc7058e50026df5058e50026de5058e50026dd5058e50026dc5058e50026df4058e50026de4058e50026dd4058e50026dc4058e50026df2058e50026de2058e50026dd2058e50026dc2058e50026df1058e50026de1058e50026dd1058e50026dc1058e500e4fd76d4e5000ede63d4e500f75e53d4e5000cff7654e5000ede6354e50006dd6354e50005fb7054e50025f87054e50004ff7458a50014fe7458a50004fd7458a50014fc7458a500067f5458a500067d5458a50004ff7358a5000cfe7358a5000cfc7358a50026ef7258a50006ee4258a50006ed4258a50004ff7158a5001cfc7158a500267f5058a500267d5058a50026ee2058a50026ec2058a501e6de63d4a50006dd63d4a501d6de6394a50006dd6394a5003eee6294a50006ed6294a50025fa7094a50005f97094a5003cff7654a50005df7354a500f5dc7354a501c6d
  | 23 => 0x57f75581210057c7558121005bf7458121125bc7458121005df735812111ddc735812111dde7318121005dd7318121026fa6018121006f9601812101cfe759942101e7e75994210d4ff7499421014fe7499421004fd7499421014fc74994210d67f54994210067d549942100cfe7399421004fd739942100cfc739942103cfe729942103cfc729942103e7e529942103e7c529942101cfe719942101cfc719942101e7e519942101e7c5199421024fe7099421004fd709942101cff755942101e7f7559421004ff7459421014fe7459421004fd7459421014fc74594210067f54594210067d5459421004ff735942100cfe735942100cfc735942103cfe725942103cfc725942103e7e525942103e7c525942101cfe715942101cfc715942101e7e515942101e7c5159421004ff7059421024fc7059421004ff7558c210d4fc7558c21004ff7458c21014fe7458c21004fd7458c21014fc7458c210067f5458c210067d5458c2101cff7358c2101edf7358c2110ede5358c2110ede4358c21006dd4358c2103cfe7258c2103cfc7258c2103ede3258c2103edc3258c2101cfe7158c2101cfc7158c2101ede3158c2101edc3158c2101ef62158c2103ef52158c21004ff7058c21024fc7058c2110edf3058c210d4ff76d4c2101cfe76d4c21004fd76d4c2101cfc76d4c210d67e65d4c210067d65d4c2110f5e53d4c21004ff7654c2101cfe7654c21004fd7654c2101cfc7654c210067e6554c210067d6554c2100ede6354c21006dd6354c21004ff75580210d4fc7558021004ff7458021014fe7458021004fd7458021014fc74580210067f54580210067d5458021004ff735802100cfe735802100cfc735802101ef6215802103ef5215802101efb7058021006fa4058021006f9405802103efb205802103ef8205802101efb105802101ef8105802100cff7658f500d6dc6358f50024fc7558f50004ff7458f50014fe7458f50004fd7458f50014fc7458f500067f5458f500067d5458f500d6df5358f500d6dc5358f50004ff7258f5003cfc7258f50004ff7158f5001cfc7158f50106df3058f500c4ff7654f500d6ef6298b5003eec6298b500d6ec6258b50024fc7558b50004ff7458b50014fe7458b50004fd7458b50014fc7458b500067f5458b500067d5458b50004ff7358b5000cfe7358b5000cfc7358b500d6ef5258b500d6ec5258b50004ff7158b5001cfc7158b500247d76d4b500d57f74d4b503dd7d74d4b500d67f64d4b503d67d64d4b500067d63d4b5003e7e62d4b500d76e62d4b500d76d62d4b5003e7c62d4b502fe7e61d4b500257e70d4b500d77a70d4b500d77970d4b500257c70d4b50005df7354b50105dc7354b500057f7654b500067f7654b503cd7f7454b503cd7d7454b503767f6454b503767d6454b500075f735
  | 24 => 0xe51595212f67c5159521004ff7059521024fc7059521004fe76195210067d65195210d67e75195210d4ff7419521014fe7419521004fd7419521014fc74195210d67f54195210067d541952100cfe7319521004fd731952100cfc73195210067e53195210d67c5319521024fe7019521004fd701952100cfe76d8d2111ede63d8d210d4fe75d8d21004fd75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d210067f54d8d210067d54d8d2111edc53d8d2111ede43d8d21006dd43d8d2101cfd72d8d2111edf32d8d2103cfd71d8d2111edf31d8d21024fe70d8d21004fd70d8d2111edc30d8d210057f7558d210057c7558d2111edc6358d21004ff7558d210067f7558d210047f7558d210d4fc7558d210067c7558d210047c7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d210067f5458d210067d5458d2111cff7358d21006df7358d2112cff7258d21006ef7258d2113cff7158d21006f77158d21004ff7058d21024fc7058d2111edf3058d210d4ff76d4d21004fe76d4d21004fd76d4d210d4fc76d4d21006df63d4d2100edc63d4d2111f5e53d4d21004ff7654d21004fe7654d21004fd7654d21004fc7654d2101cfe76d49210067f65d49210d67c65d492101df671d4921005f571d492101cfc76549210067f65549210067c6554921005df735492111ddc735492103f6c5254921005f7715492101df4715492103fe4215492101cfc764c921006df634c92100edc634c921005f7714c92101df4714c92103cfe76d45210067f65d45210d67c65d452103dee72d4521005ed72d45210d4ff7654521004fd765452103cfc76545210067f65545210067c6554521005ef725452103dec725452101fe42154521005f6768c52101ef6768c5213ef77548c5213ef75548c52111df5738c52100ef6638c52100ef4638c52103df6728c52101df4728c52101ef7628c52101fe7628c5213efe6428c5213efe5428c521005f5708c52100cff764c52111cfd764c52103cfc764c5210057f754c5210057c754c521006df634c52100edc634c521005ef724c52103dec724c52103df4764c52100ef4764c52103cf4764c52100777754c52100774754c5213e777544c5213e775544c52101df7734c52101fd7734c521007d7634c52100ef6634c52100ef4634c52111fd4634c52111fd6434c5213e7d5434c521007e7724c52103df6724c52103df4724c521007e4724c52101ef7624c52101fe7624c5213e7e6424c5213e7e5424c521005f7704c52111fd7304c5210d4fe75d8121004fd75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d81210067f54d81210067d54d812100cfe73d8121004fd73d812100cfc73d8121006ee42d8121006ed42d8121006f631d8121006f531d8121006fb6098121
  | 25 => 0x8321006ed425832103ef6215832103ef5215832103efb705832103efb205832103ef8205832101e7e75996210d4ff7499621014fe7499621004fd7499621014fc74996210d67f54996210067d549962100cfe7399621004fd739962100cfc739962101cfe719962101e7e519962101e7c5199621024fe7099621004fd709962101ef7109962101e7f7559621004ff7459621014fe7459621004fd7459621014fc74596210067f54596210067d5459621004ff735962100cfe735962100cfc735962101cfc715962101e7e515962101e7c5159621004ff7059621024fc7059621004ff7558e210d4fc7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e210067f5458e210067d5458e2101edf7358e2112edc5358e2112ede4358e21006dd4358e2112edf3258e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e21024fc7058e2112edf3058e2101ef71058e210d4ff76d4e2101cfe76d4e21004fd76d4e2101cfc76d4e2100ede63d4e21006dd63d4e2112f5e53d4e21004ff7654e2101cfe7654e21004fd7654e2101cfc7654e210d67e65d4a210067d65d4a2101df671d4a21005f571d4a210067e6554a210067d6554a21005df7354a2112ddc7354a21005f77154a2101df47154a2100cff764ca2101cfc764ca2100ede634ca21006dd634ca21005f7714ca2101df4714ca2101df7764c62110ef7764c62100777754c62100774754c6213f777544c6213f775544c62101fd7734c62100ef6634c62101ef4634c62112fd6434c6213f7d5434c62103df6724c62103df4724c621005f7704c62112fd7304c621004ff75582210d4fc7558221004ff7458221014fe7458221004fd7458221014fc74582210067f54582210067d5458221004ff735822100cfe735822100cfc735822101cfc715822101ef63158221006f5315822101efb7058221006fa4058221006f9405822101efb105822101ef81058221004ff74d9521014fe74d9521004fd74d9521014fc74d95210067f54d95210067d54d952100cfe73d9521004fd73d952100cfc73d95210067e53d95210067c53d9521024fe70d9521004fd70d95210067f65995210d4fe75995210d4ff7499521014fe7499521004fd7499521014fc74995210d67f54995210067d549952100cfe7399521004fd739952100cfc7399521004fd72995210d6ed7299521004fd71995210d6f571995212fe7e51995210d67c5199521024fe7099521004fd7099521005df735952111ddc73595210067f7559521004ff7459521014fe7459521004fd7459521014fc74595210067f54595210067d5459521004ff7359521006df7359521004df735952100cfe735952100cfc7359521006dc735952100cdc7359521004ff7259521006ef7259521004ff7159521006f771595212f67
  | 26 => 0x67e73597210067d73597210067c73597210067f43597210067e43597210067d43597210067c435972103e7f725972103e7e725972103e7d725972103e7c725972103e7f425972103e7e425972103e7d425972103e7c425972103e7f325972103e7e325972103e7d325972103e7c32597210067f71597212f67e71597210067d71597212f67c71597210067f41597212f67e41597210067d41597212f67c41597210067f31597212f67e31597212f67c315972103e7f215972103e7e215972103e7d215972103e7c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067e40597210067d40597210067c40597210067f30597210067c305972103e7f205972103e7e205972103e7d205972103e7c20597212f67f10597212f67c1059721006bf7559321006be75593210063e7559321006bd75593210063d7559321006bc7559321006bf7359321006be7359321006bd7359321006bc7359321006be5359321006bc535932103ebf725932103ebe725932103ebd725932103ebc725932103ebf525932103ebe525932103ebd525932103ebc525932103ebf325932103ebe325932103ebd325932103ebc3259321146bf71593213febe7159321006bd71593213febc71593213febe51593213febc5159321006bf31593213febe31593213febc315932103ebf215932103ebe215932103ebd215932103ebc2159321006bf7059321006be7059321006bd7059321006bc7059321006bf3059321006bc305932103ebf205932103ebe205932103ebd205932103ebc20593213febf10593213febc1059321004ff7558f210d4fc7558f21004ff7458f21014fe7458f21004fd7458f21014fc7458f210067f5458f210067d5458f2103edf7358f2101cfc7258f2103ede3258f2103edc3258f2113edf3158f2103ef62158f2103ef52158f21004ff7058f21024fc7058f2113edf3058f210d4ff76d4f2103cfe76d4f21004fd76d4f2103cfc76d4f210d67e65d4f210067d65d4f211f6be64d4f21006bd64d4f2113f5e53d4f21004ff7654f2103cfe7654f21004fd7654f2103cfc7654f210067e6554f210067d6554f211eebe6454f21006bd6454f210d67e65d47210067d65d472116ebe64d4721006bd64d472103dee72d4721005ed72d47210067e65547210067d655472117ebe6454721006bd6454721005ef725472103dec725472100cff764c72103cfc764c7210057f754c7210057c754c7210067e654c7210067d654c72114ebe644c721006bd644c72100ede634c721006dd634c721005ef724c72103dec724c721004ff75583210d4fc7558321004ff7458321014fe7458321004fd7458321014fc74583210067f54583210067d5458321004ff735832100cfe735832100cfc735832101cfc725832103eee425
  | 27 => 0x67194931005f57194931004ff7654931004fe7654931004fc76549310067f65549310067c6554931005df735493100ddc7354931004fe7614931004fd761493103cfc76149310067f65149310d67c651493114dbe7414931005bd741493100dde7314931005dd731493101df67114931005f5711493100cfe76d453100cfc76d45310067f65d45310d67c65d453100dde73d4531005dd73d453101f7651d45310d4ff765453100cfe7654531174fd765453100cfc76545310067f65545310067c6554531005df735453100ddc735453101fd431545310067f65d81310067c65d81310d4fe75d8131004fd75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d81310067f54d81310067d54d813101cfd73d8131066de43d8131006dd43d813103cfe72d8131004fd72d8131066fa30d81310057e75981310057d75981310067f65981310067c6598131006fb60981310057f75581310057c75581310067f65581310067c6558131005bf745813114dbc7458131005ef7258131005ec72581310067f65181310067c6518131026fa6018131006f9601813103e7e75997210d4ff7499721014fe7499721004fd7499721014fc74997210d67f54997210067e54997210067d54997210d67c549972100cfe7399721004fd739972100cfc73997210067e53997210d67c539972101cfe729972103e7e529972103e7c5299721024fe7099721004fd70997210d67f74997210047f74997210067e74997210067d74997210047d74997210d67c74997210d67f73997210067e73997210067d73997210d67c73997210067f43997210067e43997210067d43997210067c439972103e7f729972103e7e729972103e7d729972103e7c729972103e7f429972103e7e429972103e7d429972103e7c429972103e7f329972103e7e329972103e7d329972103e7c32997210d67f71997212fe7e71997210067d71997210d67c71997210067f41997212fe7e41997210067d41997212fe7c41997210067f31997212fe7e31997212fe7c319972103e7f219972103e7e219972103e7d219972103e7c21997210d67f70997210067e70997210067d70997210d67c70997210067f40997210067e40997210067d40997210067c40997210067f30997210067c309972103e7f209972103e7e209972103e7d209972103e7c20997212fe7f10997212fe7c109972103e7f7559721004ff7459721014fe7459721004fd7459721014fc74597210067f54597210067e54597210067d54597210067c5459721004ff735972100cfe735972100cfc73597210067e53597210067c535972101cfc725972103e7e525972103e7c5259721004ff7059721024fc70597210067f74597210047f74597210067e74597210067d74597210047d74597210067c74597210067f7359721
  | 28 => 0x9531175f571995310d4fe759953115c7e75995310d4ff7499531014fe7499531004fd7499531014fc74995310d67f54995310067d5499531194fd73995310d6dd739953103cfe7299531004fd7299531174fd71995310d6f57199531024fe7099531004fd7099531196df3099531195f771595310067f7559531004ff7459531014fe7459531004fd7459531014fc74595310067f54595310067d5459531174ff7359531006df7359531004ff725953103cfc7259531194ff7159531006f77159531004ff7059531024fc7059531184fe76195310067d65195310d67e75195310d4ff7419531014fe7419531004fd7419531014fc74195310d67f54195310067e54195310067d54195310d67c541953101cff731953101cfd73195310d67f531953115e7d531953103cfe7219531004fd7219531024fe7019531004fd701953115edf30195311857e76195310067e76195311847e76195310057f74195310057d74195310067f64195310067e64195310067d64195310067c641953115f5e43195310075d431953115f7731195314075e31195314075c311953115f74311953115f5f30195310d67f74195310047f74195310067e74195310067d74195310047d74195310d67c74195310d67f731953115e7e731953115e7d73195310d67c731953115e7f431953115e7e431953115e7d431953115e7c43195310d67f72195310067e72195310067d72195310d67c72195310067f42195310067e42195310067d42195310067c421953115e7f321953115e7e321953115e7d321953115e7c32195310d67f71195314067e711953115e7d71195310d67c71195310067f41195314067e41195310067d41195314067c411953115e7f31195314067e311953115e7d31195314067c31195314067e21195314067c21195310d67f70195310067e70195310067d70195310d67c70195310067f40195310067e40195310067d40195310067c401953115e7f301953115e5f301953115e7e301953115e7d301953115e7c30195314067f10195314067c10195310067f65d89310067c65d89310d4fe75d8931004fd75d8931004ff74d8931014fe74d8931004fd74d8931014fc74d89310067f54d89310067d54d893101cfd73d8931006ee42d8931006ed42d893112eee32d893112eed32d8931024fe70d8931004fd70d893112edf30d89310057e75989310057d75989310067f65989310067c659893114dbe7498931005bd7498931006ef629893111df571989310057f75589310057c75589310067f65589310067c655893113df771589310067f65189310067c651893103eee6218931006ed6218931004fe76d4931004fd76d49310d4fc76d49310067f65d49310d67c65d4931004fe7694931004fd769493103cfc76949310067f65949310067c659493101df
  | 29 => 0x4fd729963101cfe719963101cfc719963101e7e519963101e7c5199631024fe7099631004fd709963101ef7109963101e7f7559631004ff7459631014fe7459631004fd7459631014fc74596310067f54596310067d54596311767f53596311767d5359631004ff725963103cfc725963101cfe715963101cfc715963101e7e515963101e7c5159631004ff7059631024fc7059631004ff7558a310d4fc7558a31004ff7458a31014fe7458a31004fd7458a31014fc7458a310067f5458a310067d5458a3101eef7258a31006ee4258a31006ed4258a3111eee3258a3111eed3258a3101cfc7158a3101eee2158a3101eec2158a31004ff7058a31024fc7058a3101ef71058a310d4ff76d4a3101cfe76d4a31004fd76d4a312fe7f65d4a310d67c65d4a3103cff7694a3101cfe7694a31004fd7694a3101df67194a31005f57194a31004ff7654a31004fd7654a3101cfc7654a312f67f6554a312f67c6554a31005df7354a3100ddc7354a3103cff7614a3101cfe7614a31004fd7614a31155be7414a31005bd7414a3101df67114a31005f57114a31004ff75582310d4fc7558231004ff7458231014fe7458231004fd7458231014fc74582310067f54582310067d5458231004ff725823103cfc725823101cfc715823101edf315823101edd315823101ef6215823101efb7058231006fa4058231006f94058231046fa305823101efb105823101ef81058231004ff74d9531014fe74d9531004fd74d9531014fc74d95310067f54d95310067e54d95310067d54d95310067c54d953101cff73d953101cfd73d95311867f53d95311867d53d953103cfe72d9531004fd72d9531024fe70d9531004fd70d95310057f74d95310057d74d95310067f64d95310067e64d95310067d64d95310067c64d95311875e43d95310075d43d95311877731d953140f5e31d953140f5c31d95311877431d95311875f30d95310067f74d95310047f74d95310067e74d95310067d74d95310047d74d95310067c74d953140e7f73d95311867e73d95311867d73d95311867c73d95311867f43d95311867e43d95311867d43d95311867c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067d42d95310067c42d95311867f32d95311867e32d95311867d32d95311867c32d95311867f71d953140e7e71d95311867d71d953140e7c71d95310067f41d953140e7e41d95310067d41d953140e7c41d95311867f31d953140e7e31d953140e7c31d953140e7e21d953140e7c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d95311867f30d95311867e30d95311867d30d95311867c30d953140e7f10d953140e7c10d95310067f659
  | 30 => 0x554d4551004ff74d8151014fe74d8151004fd74d8151014fc74d81510067f54d81510067d54d815100cfe73d8151004fd73d815100cfc73d815103cfe72d8151004fd72d8151006f751d8151175de7398151005dd7398151006fb6098151005bf745815117dbc74581512a67f6518151026fa6018151006f96018151004ff7458c51014fe7458c51004fd7458c51014fc7458c510067f5458c510067d5458c5101edf7358c510d6df5358c5115e7e5358c5115e7c5358c510d6dc5358c5115ede4358c51006dd4358c51004ff7258c5103cfc7258c5115edf3258c5101cfc7158c5101ede3158c5101edc3158c51004ff7058c51024fc7058c5115edf3058c5101ef71058c51194ff7654c5140d7f7554c51004ff7458851014fe7458851004fd7458851014fc74588510067f54588510067d5458851004ff735885100cfe735885100cfc735885101eef72588510d6ef52588510d6ec5258851006ee4258851006ed425885101eee215885101eec2158851004ff7058851024fc705885101ef7105885103c7d76d48510d57f74d48514357d74d48510d67f64d485142e7d64d485115d7e73d48510d57c73d48510067d63d485103e7e62d48510d76e62d48510d76d62d485103e7c62d48510d77671d48512fd7d71d48510d77571d48512fe7e61d48510d77661d485142f7741d48512ff7441d48512657e70d4851004fd76948512f57d7594851004ff7654851005df735485115ddc73548512f57f76548510067f76548514257f74548514257d74548512f67f645485141e7d64548510075f735485115d7e735485115d7c73548510075c735485115d5c73548510067d63548510d57f72548510d76f725485103e7e625485103e7c62548512f57f71548512f67e61548512f776615485141f7741548512f77441548512657c705485103cff768c85101cfe768c851004fd768c8510d57e758c8510057d758c85115f5c538c85103eee628c851006ed628c851004ff764c851004fd764c85101cfc764c8510057f754c8510d57c754c85100ede634c851006dd634c85103eee624c851006ed624c85101df77654451006f77654451004f7765445101df7755445101f7775544510d6f6655445101f766554451165f67454451165f474544514177654544510d7745454451005f77054451004ff7458051014fe7458051004fd7458051014fc74580510067f54580510067d5458051004ff735805100cfe735805100cfc7358051004ff725805103cfc72580510067f52580510067d525805101efb70580510d6fb50580510d6f85058051006fa4058051006f9405805101efb105805101ef8105805101e7e75996310d4ff7499631014fe7499631004fd7499631014fc74996310d67f54996310067d54996310d67f53996311967d539963103cfe7299631
  | 31 => 0x8a5101eec2158a51004ff7058a51024fc7058a512fd7d76d4a510067d76d4a514657f74d4a514657d74d4a512fe7f64d4a5145e7d64d4a511857e73d4a511857c73d4a510067d63d4a5103e7e62d4a5103e7c62d4a512fd7d71d4a512a57e70d4a5103eee6294a51006ed6294a5101df67194a51005f57194a5103cff7654a51005df7354a51185dc7354a5103eee6254a51006ed6254a51005f77154a5101df47154a5103c7f7654a514557f7454a514557d7454a512f67f6454a5144e7d6454a510075f7354a511857e7354a511857c7354a510075c7354a511855c7354a510067d6354a510076f7254a5103e7e6254a512f76e6254a5103e6e6254a512f76d6254a5103e7c6254a512f57f7154a51007777154a512f7747154a512a57c7054a5118dbe7414a51005bd7414a5103cff768ca5101cfe768ca51004fd768ca510057e758ca510057d758ca5100ede638ca51006dd638ca511875c538ca51004ff764ca51004fd764ca5101cfc764ca510057f754ca510057c754ca5101df576d46510d6f576d465101f7675d465116ef664d465101ef464d46510d77754d46514477554d46510d77753d46510077553d4651004ff7458251014fe7458251004fd7458251014fc74582510067f54582510067d5458251004ff735825100cfe735825100cfc7358251004ff725825103cfc72582510067f52582510067d5258251006f7515825101ef4515825101efb7058251006fa4058251006f9405825101efb105825101ef8105825100cfe76d8d51176de63d8d5101cfd75d8d51004ff74d8d51014fe74d8d51004fd74d8d51014fc74d8d510067f54d8d510067d54d8d51176de53d8d5103cfe72d8d51004fd72d8d51176dc32d8d51176df31d8d51024fe70d8d51004fd70d8d51176df30d8d51176dc6358d51184fe76d4d511775e53d4d5101cfc7654d51006df6354d5100edc6354d51005f77154d5101df47154d51004ff74d8951014fe74d8951004fd74d8951014fc74d89510067f54d89510067d54d895100cfe73d8951004fd73d895100cfc73d89512fe7e51d89512fe7c51d8951024fe70d8951004fd70d895117dbe7498951005bd7498951006ef6298951005df7358951175dc735895103eee6218951006ed6218951004fe76d495101cfe7694951006ef629495103eec629495101df67194951005f5719495101cfc7654951005df7354951175dc7354951006ef625495103eec6254951005f7715495101df47154951004fe761495117dbe7414951005bd74149510076d5214951004fe768c951004fd768c95103cfc768c951006df638c95100edc638c951004ff764c951004fe764c951004fc764c95101d7e75d455101e7f65d455101df675d455101ef765d455101f7765d455116ef664d455116ef464d45510d77754d455143f7
  | 32 => 0xd67f53195321ae7d531953246ede321953246edc321953201cfe7119532004fd7119532024fe7019532004fd70195321aedf301953200cfe76d493200cfc76d49320067f65d49320d67c65d493200dde73d4932005dd73d493203f6e52d49320d4ff765493200cfe76549321c4fd765493200cfc76549320067f65549320067c6554932005df735493200ddc735493203fcc32549320d4fe75d8532004fd75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d85320067f54d85320067d54d853203cfd73d853213ef631d8532024fe70d8532004fd70d853213edf30d8532006f761985320057f75585320057c755853201ef66118532006f561185320d4fe75d8132004fd75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d81320067f54d81320067d54d813203cfd73d813201cfe71d8132004fd71d81320a6fa30d8132006fb60981320057f75581320057c7558132005f67118132005f57118132026fa6018132006f9601813200cff7658f510d6dc6358f5101cfc7558f51004ff7458f51014fe7458f51004fd7458f51014fc7458f510067f5458f510067d5458f510d6df5358f510d6dc5358f51004ff7258f5103cfc7258f51196df3158f51004ff7058f51024fc7058f5115cff7654f510d6ef6298b5103eec6298b510d6ec6258b5101cfc7558b51004ff7458b51014fe7458b51004fd7458b51014fc7458b510067f5458b510067d5458b51004ff7358b5100cfe7358b5100cfc7358b510d6ef5258b510d6ec5258b512f67e5158b512f67c5158b51004ff7058b51024fc7058b51005df7354b51195dc7354b510d76c5254b5103cff768cb510d4fe768cb51004fd768cb51004ff764cb51004fd764cb510d4fc764cb512667e6598351195de7398351005dd73983510d6fb6098351026f860983510d6f8605835101cfc7558351004ff7458351014fe7458351004fd7458351014fc74583510067f54583510067d5458351004ff735835100cfe735835100cfc7358351004ff725835103cfc72583510d6fb50583510d6f85058351004ff7458e51014fe7458e51004fd7458e51014fc7458e510067f5458e510067d5458e5101edf7358e511867e5358e51186de5358e511865e5358e511867c5358e51186de4358e51006dd4358e51004ff7258e5103cfc7258e51186dc3258e5101cfc7158e5101ede3158e5101edc3158e51004ff7058e51024fc7058e51186df3058e51174fd76d4e514057e75d4e511875e53d4e5100cff7654e5140d7f7554e5100ede6354e51006dd6354e51005f77154e5101df47154e51004ff7458a51014fe7458a51004fd7458a51014fc7458a510067f5458a510067d5458a51004ff7358a5100cfe7358a5100cfc7358a5101eef7258a51006ee4258a51006ed4258a5101eee215
  | 33 => 0xd5258052004ff715805201cfc715805203efb70580520d6fb50580520d6f8505805203efb205805203ef8205805203e7e75996320d4ff7499632014fe7499632004fd7499632014fc74996320d67f54996320067d54996320d67f53996321e67d539963203cfe729963203cfc729963203e7e529963203e7c529963201cfe7199632004fd7199632024fe7099632004fd709963203e7f7559632004ff7459632014fe7459632004fd7459632014fc74596320067f54596320067d5459632006df73596321c67f53596321c67d53596321c6dc535963203cfe725963203cfc725963203e7e525963203e7c5259632004ff715963201cfc7159632004ff7059632024fc705963231ddd76d4e32006dd76d4e3200dde75d4e3200f5e75d4e3231edf65d4e3231f5e65d4e32006dd65d4e3231f5d65d4e320065d65d4e3247ddf74d4e3247ddd74d4e324775f54d4e324775d54d4e3231fce72d4e3231ddd72d4e32007cd72d4e32005cd72d4e3200ede62d4e3200fce62d4e3231f5f52d4e3231f5d52d4e32004ff75586320d4fc7558632004ff7458632014fe7458632004fd7458632014fc74586320067f54586320067d545863211ede4358632006dd435863203cfc725863203ef7715863211ef6315863203ef7215863203ef42158632004ff7058632024fc7058632004ff75582320d4fc7558232004ff7458232014fe7458232004fd7458232014fc74582320067f54582320067d5458232006df5358232086dc5358232086de4358232006dd435823203cfc725823203edf325823203edd3258232004ff715823201cfc715823203efb7058232086fa305823203efb205823203ef82058232004ff74d9532014fe74d9532004fd74d9532014fc74d95320067f54d95320067d54d953203cff73d953203cfd73d95321d67f53d95321d67d53d953201cfe71d9532004fd71d9532024fe70d9532004fd70d95320067f65995321c5ed72995320d4fe75995320d4ff7499532014fe7499532004fd7499532014fc74995320d67f54995320067d54995321e4fd73995320d6dd73995321c4fd72995320d6ed729953231ede329953231edc329953201cfe7199532004fd7199532024fe7099532004fd70995321e6df30995321e5ef72595320067f7559532004ff7459532014fe7459532004fd7459532014fc74595320067f54595320067d54595321c4ff7359532006df7359532004df73595321e4ff7259532006ef7259532004ff715953201cfc7159532004ff7059532024fc70595321d4fe76195320067d651953219dbe7419532005bd74195320d67e75195320d4ff7419532014fe74195320d6be7419532014be7419532004fd74195320d6bd7419532004bd7419532014fc74195320d67f54195320067d541953203cff731953203cfd7319532
  | 34 => 0x8552004ff74d8552014fe74d8552004fd74d8552014fc74d85520067f54d85520067d54d855200cfe73d8552004fd73d855200cfc73d8552006f741d8552006f441d8552024fe70d8552004fd70d85521c5de7398552005dd7398552006df6398552006dc6398552006f76198552005fa7098552005f97098552005df73585521c5dc7358552006df6358552006dc6358552006df6318552006dc631855201ef66118552006f56118552006df63d8152006dc63d8152004ff74d8152014fe74d8152004fd74d8152014fc74d81520067f54d81520067d54d815200cfe73d8152004fd73d815200cfc73d815201cfe71d8152004fd71d8152006fb40d8152006f840d81521c5de7398152005dd7398152006df6398152006dc6398152005f67198152005f57198152006fb6098152005df73581521c5dc7358152006df6358152006dc6358152006df6318152006dc6318152026fa6018152006f960181521b6bf75590520d6be75590520063e75590521b6bd75590521b63d75590520d6bc7559052006bf7359052006be7359052006bd7359052006bc73590520d6bf5359052006be53590520d6bc535905203ebf725905203ebe725905203ebd725905203ebc725905203ebf525905203e3f525905203ebe525905203ebd525905203e3d525905203ebc525905203ebf325905203ebe325905203ebd325905203ebc3259052006bf7159052006be7159052006bd7159052006bc71590520d6bf51590520d6bc5159052006bf3159052006bc315905203ebf215905203ebe215905203ebd215905203ebc2159052006bf7059052006be7059052006bd7059052006bc70590520d6bf50590520d6bc5059052006bf3059052006bc305905203ebf205905203ebe205905203ebd205905203ebc2059052004ff7458c52014fe7458c52004fd7458c52014fc7458c520067f5458c520067d5458c5203edf7358c520d6df5358c520d6dc5358c5203cfc7258c5203e7f5258c5203e7d5258c5203ede3258c5203edc3258c52004ff7158c5201cfc7158c521aedf3158c52004ff7058c52024fc7058c521aedf3058c521e4ff7654c521e67e6554c521eebe6454c52006bd6454c5203def7654852006ef7654852004ef765485203def755485203f6f75548520d6ee655485203f6e655485203fae645485203fad6454852007cf7354852007cc7354852004ff7458452014fe7458452004fd7458452014fc74584520067f54584520067d5458452004ff735845200cfe735845200cfc735845203ef771584520d6f751584520d6f4515845203ef7215845203ef42158452004ff7058452024fc7058452004ff7458052014fe7458052004fd7458052014fc74580520067f54580520067d5458052004ff735805200cfe735805200cfc735805203e7f525805203e7
  | 35 => 0x3ef7215865203ef42158652004ff7058652024fc7058652004ff7458252014fe7458252004fd7458252014fc74582520067f54582520067d5458252004ff735825200cfe735825200cfc735825203e7f525825203e7d5258252004ff715825201cfc715825203efb705825203efb205825203ef8205825200cfe76d8d521c6de63d8d5203cfd75d8d52004ff74d8d52014fe74d8d52004fd74d8d52014fc74d8d520067f54d8d520067d54d8d521c6de53d8d52006df43d8d521c6de43d8d52006dd43d8d521c6dc43d8d521c6df32d8d5201cfe71d8d52004fd71d8d521c6df31d8d521c6dc31d8d52024fe70d8d52004fd70d8d521c6df30d8d521c6dc30d8d521c5de76d8d5200cde76d8d5231f5f75d8d52006df64d8d52006de64d8d52006dd64d8d52006dc64d8d520075f54d8d520075d54d8d5231f5e52d8d5231f5c52d8d5231edf75d8d521c6de75d8d52006df74d8d52006de74d8d52006dd74d8d52006dc74d8d52006df54d8d520065f54d8d52006de54d8d52006dd54d8d520065d54d8d52006dc54d8d52006df72d8d5231ede72d8d52006dd72d8d5231ede52d8d5231edc52d8d52006df42d8d5231ede42d8d52006dd42d8d5231edc42d8d52006df71d8d52006de71d8d52006dd71d8d52006dc71d8d52006df41d8d52006de41d8d52006dd41d8d52006dc41d8d5231edf21d8d5231edc21d8d52006df70d8d52006de70d8d52006dd70d8d52006dc70d8d52006df40d8d52006de40d8d52006dd40d8d52006dc40d8d5231edf20d8d5231edc20d8d521c6dc6358d52005de7618d521c6de7618d521c75d7518d5246edf6518d521c79e7418d521c79d7418d52006df6418d52006de6418d52006dd6418d52006dc6418d520075f5418d520075d5418d5246f5e5218d5246f5c5218d521d4fe76d4d5200edc63d4d521c75e53d4d520057e76d4d521d67e76d4d524a57f74d4d524a57d74d4d5249e7f64d4d5249e7d64d4d521c57d73d4d520075f63d4d5200e7e63d4d5200e7c63d4d521c75c63d4d5200e5c63d4d5203d7e72d4d5203d7c72d4d520d67f62d4d5231f5c32d4d522f57e71d4d520057d70d4d521c75f30d4d5203cfc7654d52006df6354d5200edc6354d52005ef7254d5203dec7254d5203d7c7654d5200e7c7654d5203c7c7654d524957f7454d524957d7454d5248e7f6454d5248e7d6454d521c57f7354d520075f7354d520075f6354d5200e7e6354d5200e7c6354d521c75c6354d520076f7254d5203d7e7254d5203d7c7254d520076c7254d522f57c7154d520057f7054d5203d7e75d495203e7f65d4952006df63d49521e6dc63d495203dee75d495203eef65d495203f6f65d49520d76f54d49524876d54d4952007cf63d4952007cc63d49520d76f53d49520076d53d4952006df63d8552006dc63d
  | 36 => 0xd74d8553014fc74d85530067f54d85530067d54d855303cfe72d8553004fd72d8553006f741d8553006f441d8553196f631d8553024fe70d8553004fd70d855340e7f6598553006f7619855340e7f651855301ef66118553006f56118553004ff74d8153014fe74d8153004fd74d8153014fc74d81530067f54d81530067d54d8153006df53d8153106dc53d815303cfe72d8153004fd72d815301cfe71d8153004fd71d8153106fa30d8153005f67198153005f57198153006fb6098153005ef7258153005ec7258153026fa6018153006f9601815300cff7658f520d6dc6358f5203cfc7558f52004ff7458f52014fe7458f52004fd7458f52014fc7458f520067f5458f520067d5458f520d6df5358f520d6dc5358f521e6de4358f52006dd4358f521e6df3258f52004ff7158f5201cfc7158f52004ff7058f52024fc7058f5203d7d76d4f5200e7d76d4f5203c7d76d4f520d57f74d4f524cd7d74d4f520d67f64d4f524c67d64d4f5200e7e63d4f520d75e63d4f5200e5e63d4f520d75d63d4f5200e7c63d4f5203d7e72d4f520d76e72d4f520d76d72d4f5203d7c72d4f5231f5c32d4f522fd7e71d4f520057d70d4f521e75f30d4f521acff7654f520057f7654f521ae7f7654f524bd7f7454f524bd7d7454f524b67f6454f524b67d6454f520d75f7354f5200e7e6354f5200e7c6354f5203d7e7254f5203d7c7254f522fd7c7154f520057f7054f520d6f7619875201ef461987520d6f4615875203cfc7558752004ff7458752014fe7458752004fd7458752014fc74587520067f54587520067d5458752004ff735875200cfe735875200cfc73587520d6f751587520d6f45158752004ff7058752024fc70587521e5de7398352005dd7398352005f67198352005f571983520d6fb6098352026f860983520d6f8605835203cfc7558352004ff7458352014fe7458352004fd7458352014fc74583520067f54583520067d5458352004ff735835200cfe735835200cfc7358352004ff715835201cfc71583520d6fb50583520d6f85058352004ff7458e52014fe7458e52004fd7458e52014fc7458e520067f5458e520067d5458e5203edf7358e521d6de5358e5203cfc7258e5203e7f5258e5203e7d5258e5203ede3258e5203edc3258e52004ff7158e5201cfc7158e52004ff7058e52024fc7058e521d6df3058e521c4fd76d4e5200edc63d4e521d75e53d4e5200cff7654e5200ede6354e52006dd6354e52005ef7254e5203dec7254e5203ded76d4a520d6ed76d4a5203f6e75d4a520d76f54d4a524af6d54d4a520d76f53d4a520076d53d4a52004ff7458652014fe7458652004fd7458652014fc74586520067f54586520067d5458652004ff735865200cfe735865200cfc735865203ef77158652006f74158652006f44158652
  | 37 => 0x16000800000180010008002004c004000000b0004000002001b0004003001c000001c001000c005000000300000060000006005400200200030074005000c0090008002000000d003c0080008011000000b00240000008001000c003005400500000010010000000800000180010040023000400d0010003002400700140090010003001c00000000030018005001800200040000010001000400400000040000006001800700080030020010000c001000800100100100040001000000000040050070000000c000001c0020000001003402e001c00e000c00000080000000003001001800100000054001000c000009c00200140090108004002c013004400100080010004003000400b00040150004001001c00e000800000000040008000000000a00040140004004001000e001800a0030007001c006000c00000080010000000000800300300050008000001400200100000024000000c003000c00f005401200040010008003002400200240270028008001c011000c02700000010024001002400200000020008002001c0000094002002800a001400800180000008000000000f00080020034005000800f004c00500740000000007000000a001c00300040240004007000400200180051d75e5398b530d6ef6298b5303eec6298b531c75e5358b530d6ec6258b5300cfc7558b53004ff7458b53014fe7458b53004fd7458b53014fc7458b530067f5458b530067d5458b530d6ef5258b530d6ec5258b53006ee4258b53006ed4258b531c6ee3258b5331edc3258b53004ff7158b5301cfc7158b53004ff7058b53024fc7058b531c6df3058b534067e65987531875e53987530d6f7619875301ef461987531775e53587530d6f4615875300cfc7558753004ff7458753014fe7458753004fd7458753014fc74587530067f54587530067d5458753004ff725875303cfc72587530d6f751587530d6f45158753176f63158753004ff7058753024fc7058753176df30587530f75e5398353005f67198353005f571983530d6fb6098353026f860983530e75e53583530d6f8605835300cfc7558353004ff7458353014fe7458353004fd7458353014fc74583530067f54583530067d5458353004ff725835303cfc7258353004ff715835301cfc71583530d6fb50583530d6f850583530e6fa305835300dde75d4d5300f5e75d4d5300edf65d4d5300f5f65d4d5300e5f65d4d530d75f54d4d534d75d54d4d53004ff74d8953014fe74d8953004fd74d8953014fc74d89530067f54d89530067d54d8953006ee42d8953006ed42d89531e6ee32d895301cfe71d8953004fd71d8953024fe70d8953004fd70d8953006ef62989531edbe7418953005bd741895331edf631895303eee6218953006ed6218953004ff74d8553014fe74d8553004f
  | 38 => 0x20024004000000600040200024003004000100100010010009000c004000800000240010004000000000100080000028001003800d000000600040030000001000800000000000010005002000000f00000000003000000100000330000001000000f00000090000001002400200200020000002000000000280040010000002000b001800200080000010001002801e0008009001c00100700040024000012000000080000010014003c0020014000001000000000050004002000c004000c0060000001000c0000010004002400000040080010001006800000000060020001005400200040240040000000c01900000080000000004800300040000004012009c007002400000180040004000000c00e00000060020001001c0010000003006402a002c01c004c0010030003004000900000030008001000400100000000008007000c01300380000070012000800100000010008000000802300040010010002002400100140010000000003c0000000003002400000000010060000001000900180040000000000c004000c0080020004002c004001c004001000700080070004008001c00a00000000004002009800800000100004003004c006000c000000000300180060000004000000000080010008001000000000d800b002400400000010008000001000200d0004000000e002800200500000000004000400000040000000004000c000001c0070000027000402300000060000003000c01d00100000004002001800f0000003001000000040290000001000000500080000014007000001b003802300080020000004000400000280000008003007401000080000004005000c000001c0050000006001c0040000002004c0020010004000c00000100000034000002800100180170018001000801f000c0110024002001c00e003c0010038001003c00000040260008009005000300000040000000000800200540010000001000c00300000010004000000400300000000024008000000b000c0010004009008800100180110010006001000c0134003000c0160038000003c00e0004009007c00500e80000010002000400d0028001003c0050010000000800200100020018015000c00400040030000000000400600000050008000000c00000840030044001001000a0018004000c0000000002000000000000080000004007000100000060000001000c00e006800200000000000009000000000d401a000c0060004005000800000500030004001000c0120014000001c002001800200000060008014001400700b8002001800000280050010015001000200000060034009007c0070000001008c00100340150000007000000400240000008000005c00000040000044004000400700080000000000000001900040020008003000
  | 39 => 0x24000000400000000090004003002c0010004000002400000000030000002000c00300140000014007000000000000000004007000400f000000b00500160000002000c006001000000040030004002007400e0000001000c000000000500280080020000001c0020008001000000200000010048000002000a00000070024017000c0000008000001800700040000000014003001200180010000004004c0090014000001000000000010000002001c0050030009000000000000000004001000c024005c000000c006000c00800040010000003000400000240000004002000800100340000000009002400c0018009001000000100030048006000c007000800000540050000000000800f00000040000016000000000080210008000000000c0044014000c0030000001000400300900000000000000001a000400b000c009001000800000000008000002400e0088000002400b0000000000c002001800600140280018000000400c00040080008000000800300140000014005002800600000000068001003000100040230014002001c0000000002007c0070040016001400a0004000000000500080030000000001400000440000000000000c00900a40050000014002800d000c000000000b00140030000020000000600240010054001002400b002800c000000100a8013001400000280000004001003400c00f00000074005001400e00140000064013001c000000000100100000004004000c01000040060010006003000d00140010000000000401700040080000000001400000400000010009007000000000020030002000800b0018017000c0050004000003800600300050008000000800200040080000001004c00000300030018005000800200000020000000000c009002c0000048000000c002000c00100400120004010000000400300140008001000000d000400600c000e004000f0000008000c0000028002001c000000000200000050000000000c00a002000700000010014002000c0010050000000000100340050008005004800100040050024000000400d001c000000401f00ac0010014000002800c003c0070038024004402900000030000000000000a00000190008002000400300000050008001000400000140020098000000c00400340000004015002c0040004000003000200000000000010000000200040020018003000400e006800e0014002001800600140020008001000400100000050020001001400100840000008002007c002000000f00040030028002000401c0000018000000a0018006000c0000004008001400b001c00100080000020019005403d000c008000400b000c0040048000000000100200030034004000000a0000016002c00000500070008000000802400ac002000c001001800
  | 40 => 0x1e00100000040001003c001000400600000000008000000c003000000300080050084004001c0010020004000800200000010000000001402a002000b000c00100000030000001000c00c01ac0060008001002400000b40000084005000400b002000000000010004001001800200080000000000002c0000000000001c00f000c015003c02f0084001000000c00000000000009001800400340000004004001401600040030000005001c0070028004002c028001c01f0004039000000000080000030002003000500100000000000001c0020000007000001c002c0000024013002c0020000003000800000d0000001c004000400000040000004004000000100b800400140000054002001400c00100030000011004800700080090000004004c003001401c00680050034002000c007000400f000c0200028000000000b001c000001c00000380000000001006c000000000800000290000000003000000180160054000000400100040070008004005c00200040020018006000000100200020004013001000400140020000008000001e0000000004c0020000004000800d0004004002400a00000030038000000000000000010020001000401d000c00300040010004000000000200180130000000000000000040020014000001c000000401b000000200240030000000001800000040020008008000c000000c0000000008001c0030000005001c008000800c000400000a00070008000000000e00140000010000000000100280010048002003c0000000043000c0020008008000000e00000030014000002400500100020004023000000200000040014005002c009001c011000000200140000000004000400c000000100000010004004000c000000800500100000004000001c00c000000b00080060010001000c0060004012000c001000400700180160008003000c001000000e0010001000000f0000000000000e001c0020004000000000000040040010040000000100000010000000000000000000000000000000400b0004000000000e007400f003c0130000000000c002001c001001c000000000b0024002001800000cc00100040000064000000400300880050024000000800200280040050000000801000180080000000001c00000140090020000000002c0084006001000c0044001000c000000001b00000020000004000800200300060008002000000001c80060000021000000000080110000000000000000040010000001001000100140100004007002c002000400200340000004000001400100500000000001000000000140010008012000000400200010060006000800300080000000007000000000140040050003001400b000800300000000000003004c0010000002000c0000028003004001d000000100
  | 41 => 0xef00a8364a51020882680d8980823d286e6778cfab8c2c764d6abdc158a1dc0360be409e1a3eae00d1cc0613721511fa09c0afe85750c7a7fd8f9674c00b88e61b90b0695a200022c62f02bc69d08000b5880005a7800000024a43f98000000000000004f22d4962a28300000001a648b580006bd000091313c45fe800000018520000f560000efcc2b8e40ac31b42000199e000059a000053250f8dde0002c169058000a200d8220404ba2d41fc89cb2e2045a9e581220804000000067391c4731a0221c595dca841cf65149a2416b1e0c0001588751a9da0bf1bbebdda4aea2305c82c3221e72a12fe3aa12f01db1fa24d7120425830a8baa8394be280004122d66bf71f74a9e000069caf268559dec04b000096714a41d38000b161578765ad6a6c6b020892909832d9ed44c80cc65528356b2f97e40098f72bd287d42a3275885c948671603023ae1bb89ad0f7887e86c2afc0ebabae85bebc388243df0d4a2b880008f1a2ce3d48ce8194a91a4ea87e07db8126415800087d1d0c6691e0a52480008c800009fc80006d72734ae704fea48000021c80007260000000079034f2d1485d80003e680000002926030277e3c397d87b2000000f00000001edc837902c9ff01e8176914e00009422cf103a3ce0568000000000017e09b212e67030ff02c100007cf85b00001e1800000000240000000000083f97e264e00001f39f780000d86be000000001db62749c5600029be84000005ec20460000000276a1c00001be24130110bf1232c1c190be4a214d23500000c1d80001a91df245a000034e8000178ad0456b9d449321a287dfa35c41a033229e9d5426d0b5606515ba31c88340002f5891780009ce00001b88ddcc4c1d4a62a89729db800072500000000000a4d8d583bd25fea1a8dae02c9cd80002d22626800000000000000000000000000016a005e874226a98e2000100800013ecb6ca02c15f07cc145111eaa01d8606e2086336240e4a704080ed03064aa8e443fe89f233993129d7ac604f81da00518172590298ec63800010c2012288893817a0a3c8b0800070aaa8c68480004520b4a38915220a40e1a00002283c22b76000000079d82a6000000000007b20001bde0000f1e8442d1e0001430000301e40c1be4000c00000000000000003000000b00000080008002000000f004c002000000c000800300000020010009000400400680230000000001800200000060004002000800d00000000000008000401100000000004005000400000080000004008000800b000400800140050034023008c013002c0000008000000800c0000000000400100380020000000006401f000400c0000000001c027000800100480010018000000800000280040018005000000000140040000001000000e002000300000090004000002400000600
  | 42 => 0x6c000000660002532000257c00000005008e5c00027240001a203e70676a3b1aa24d508ac00016060001e30000090e7e30936b4d23ee64d1d3a4f91450000281cba5000000019a80cb962c000260c00000008e81aa6525800000011765b50000b9680003169998617072e00000000a08c74c2e290800025441692354bcf0eae74f2b24ad49936000000091593689a6ad8297a80e09e4a18eab88000ab1317625eaa9e6aa261414622164d984549560dbec5a8000bb28ae4c2c8ef68cca506a5f92286c82d78833a19c995236e000294a5eea0449f000000001fb6af794b6000050400026cc00026e800024740000000000000030726840399a680001286ba30a120b9232a5b58db45d3800000000002bea8e883415ac6f58776b6580007ec0000c581dc83d320c600019b0c3296640789a4883b8000419a33ec7300006a9139000029de00000003579f6090e0000aad259454790bc0002c8c965ae849e018c4b4b28505080b820000c40624afacaba9bfec659e8e18999240018000adc05f8c2aa6ecb7a9a1a51d26e675d96505090a6c005281ec7aaf9cc3a16fe5269d8496222ee8c795aab4323a43280d3e8a723ea26896c837103ec0ee1e9897109e2985a8ce9819b92031121853f151c6fe20904c5268e9bf1bee86220104b6918a7a323f80000c92b948cea3b29b040d724100001e7407620160000f665b789020002766000301ca9d841c7e2957600015d000029a0000269c70180000df2e020001f4005009c6c5c8f103a88f2a0000000000000000000007c59f3000028f2c4917da0001f985160d067c8062a0000000000000000000004910a68000000000027ba61580000001a0a00000000000076a74a2724b8124cb620c9687318a27bc2dd0c2f180e32426867c00908c18243c8d097468c28b680000000bdd169a96c1ec6c5a000000012fa000174200000006dd9d480000000a6c894082e2ab848d000086b83e67cf0f2e8742a0092400003ca16609218cac4042fba262000008ca51448fa118becadaa392acf20000000a2d94140000000000122a000000035a80000002c1200012a46a504003a22d283cfa5e050421507ad9b707ea00c82b81b0641d210c3e3059064c05725c294e2b4e82101e68deeaaa26bc593af6c721adac16706b6bb99c5a4a086c89978ab40c9015e4060d328990b6a7f000000001b5e9e6800097e9e1279f000023917ee8428000642a01ab3f213a8c1ac4628d29c6c430000000000000010502b4230caac8fb80081b783a7075a10f1b725a4919a9332c2800007361c8113ec6e98f412b0000a2f00000000000501800000000000912b12befa8540e1211c23480000000cce000000026280006c72dd40000000000000022ba3b43f380000001e48ba80944ad205922519d4e12d80003f50000c811f64c771bea4
  | 43 => 0x19ae8ac878a61e25a89919fcc58223904c09962a0f800068aa4403dd00000002e700000000c560000695a3a6000141e0001c40bb900009eb80000000e2a34100000002abc000000088088764ef8000000312600000000000000523000000027146e312eabce80002598aea000056cb7203e0a9b800059d2b38373000034000000000d80a7412e2afdaedc0002eee11c9734700800004e2cce9c19c1899a80000000000000000074280000002ffe8bd9ebc000176e00000003b331327e22a0c0001cd0000058821d1e149309b485b7000043ca748b40ae9a26102969b4223406fa8885ed8508bc0a6ea4ec28d69770e4c77ba85600020243808000b26211e7ea9d6000000006f0000074393760aca43e8d115b45c300003a29634002a8ba8898d20c4ea692768aec06420000a0b04107492872c4b000000021280000000000227018f80000ae0000000000000000000002cbc0002dd87ad0000603000069e2910000104254082e800000000b0800000000000000b9c9dd00007db195e28b80001f9aece06c00005dc80000000cb2a4704406b6061a95b000063000000329b8e00000001c498a80000000598800000000000000000000226e1fd8000623871a76900001c9acdabbc0800000000075e1aca98e31b60001bd8008aa30375a9183dc1702c2d305ea8b1c1c8e48c948310cec9a811904e0129200000000000000ad5affca98a8be69795a06e71e10801a844b4e07da1910ffcaa1a2286aa80000000abe0001ca028a233453d8ca67190f12935881a3cb000056005ee00001d67a8313c518033e00011505400398548046200000000001648b75957296d9e5ec608c3c0000986a970ebc13a00004372f900002cb00000b1649a0422aca1e08a5b8beea09a00414016424600eb6ac40a54c4102425633120c3da11a1e02fa26cd8672a79262e3a90722950ae7c5e500640290000769aba037d97a260600000000000ba78000000000063182f239406b400008268410000763ab3e63f0ca40001c6c00000007d48f1c0002fb4bda80008ee8e1caab00000000310ad81eb870d0000000004c00000000920ec201b8c3428a978e98e9c00c3b957c08506009e8008268b89e823c8f9e1c2b08022880000002bb02568dba19d020678f295ab3d1a8a12e0eb430500000000000000000060284bc0a018b0c368000b709a08884250e1ba153c22a84e2759a6b6233a96a0002882b1a9fd86742fc8641800019780005658ed0668a26251f9b944b39480b37225e0e68350154889660b800000023be00000009890000c29aa0ea73a9c835b2e6c9cd80ac607afe000002b05870c3636f276c76a9360000000000025ac000000088e00005340000bc3000093c8000068800007fa46c48180000002c2e54a00000439300ac5a4048f728d400000007f89a50ae69
  | 44 => 0x8870691186646d190e5b98da620c800029c0e0065200000001de28592e86000111c7a423fc655a95687a855a00012a265aa7a6000000054916f606297acaa81c1e199000037500005d40f0cb54800000003f03c621c83fba8fc1328fac86db02a4f88b0070400527d59fda00014129ae8000000000000016ec000181a0000000b120000000303e9808000000000072b00000000d7c12b800085f2d5c000284ca2a000077980000000000092957a1d816f45c003ba0001df8680000000000000180000000000081384cc0000000000253e000124a1faa3005a980000000000900881c7b280960000000b0c2fa833ba8460f520eab690a1eabf22764f6aea4bd78b4c8852074289945e4adac662a4a5547a5b186b5800006440000b138f142b612acc488a5099c045c4f98f8e614105862f02ca825aceac6003c400000002bf08f65882d944ae87a05891b84000084c85f8000a92800000000008518a30077000000000005db0956000165830b8c780000000000316c0002ce6000000084c187637e8000000092090707788ba8efa6018980000180400000003a50000a2c1b4c3f200000000000463800082f000000000009b685fc9a58d0a000186e5dfa95e0002ad43858000376b0c251a091a95a93de000238c00000000000000000000000020a40002f5a7b0a600637071e000000000000000002b4c00019be00007f4a7598862660000737b10a86900001aaa432865b056bfd923000016d80000000000076a00aafae0000ed618e800000000004b500000000af600000000002a160000ec80000000018af1e06caccc2cda338bf19868bd219d41522d506fb29e20002d2eae991e850605dc0001cb49d5a5b2b030a180000000000000076480002b79db0adf1dc2134944e00013fe290904e159924896e97f002029b0074800038500000000ea64ff00008c0946c0f380000000c3a191860ac25ae40000306e000163a490a5027d70000000000000000000000000000000014f8382b8c800050a249a9e3202a82086ca00020d60000000c28169c0000c462fe8000a16039e38a22fe600000000012120000000000000099e1ddc627846c08012c200030981b38000000199caafa1821b123a8b999ad26719ec440f0dc6000000000031bc0001e6400015c0a71032c0000bde1aa000020486567a1000000009d67d6800024900000000000bb213f808380009a60d9400000000000000b5a0000b07b17400000000000000432a948b55a8a222e9364000228e0001e8800022004678b928780e6aa9f8ac87c40ba89ef8a445d8133e81014fe97f040400020480000d5477f00000001cb83cd24f05c788ea00000000002aa60000000000000000015c800012dc2ae000090a9dba000182a9fd2cd66d2868a74086d88d1972a7ff92200f889ee93488b82bb86ec
  | 45 => 0x85410000888000000005aa2cb002e8db0c600c88000132293092fb2002b5801a5d68996a94000034480000002938000106e0000bf40002d860002d8e06aa1f20000f5011126503d723b26fe8000b392934a981bd2c1621ee070a3f600008d8c748d5c95c8d840000000059aea212a89c2aaaa39429d1586300000090b9bb4537276099917a850cadf8c67b11ec7da9f243589e00001b22000160e0541078000000009b000000031f20000386bc20000421102e9daafdea1b1bf40000000aff8ea000021c41bf8000046af108a51d2e5a28556000000000000002a40fa0000000000005227d401280001fca00000000b68000c78aebe48ba5d400015ec00013580002eb0ad61ffc4c59a885df0d644eb30a29e201f29e793328300338408a902865287a923a25caeb209434a9cbc14da39c4eda5c86c7a8fa85100001291d905e180000000000000122cb2e0976007a99a912ae0000003e88d320b2000048e0001a1e7701cd4a7800000f1a4b483893922a2a2e44588000a870000c1d15388b12ef808130087052e347568e1e8af3026b1b022c0003208000000066f069818217e68f42f62c79000038e0000a5ea8eaac7981282a184a3ab01ac2059f4e82e9b62c6300000570ffe03480000001304ab28f04000264c0001a98000000089e80000c285c22712ca60001dda99d9d6876280000002a3646c0000bb19706427978c2148cd4b5b10366202fe4a3980006210b7c18c2660a65a33a78b11322c98700b9a304ab4006543a5a4340750ff6641000096f9bc65718a8e0cea4e000025508038e6872e82c076e22e05648c0e15081eead51478c1f10ee0e4296caad874c000174a60d31da05d00008b9a52e90b000042b00006408000833107a000000065085020000a5a8fe8234a412e4e0bc1b6891a0ab619a0a4040f99f65f4a8ac0b60000a03133c02d000000000000003194578a9a6b2da23c1e126f21532a3200000005ceab180cf25f865021d857330c4c0a043400019680000ece54c08583548a066ca00f6afb27a419804ee127974cb24991a9b287e27a7906c00014b41780000a3012166fc8cfe87a00f271c18389b588c250d10f616e903400000008c1000093f8fd20deace000008e61c53206c6b00005c21ab0996a1f04ac00008e021b40001a42b55000000031a604c281a00012be16d8000c37886a0070000be9080840a051c36794de8ae90020c78c42c4f83de7890c5426fafd07082c7a4e0a32e5319c5c8509bc8000220c77a000038b9a5a67080009ee22b0a5e098c4d199f8b972cd40d013c6c38aa94c5c179a16a316e76f996493d8d7ebbc97b4000068200027b67dc30485e2800061f04a60a8800000000000000a96000000059790fa0000e0a04d0ada55721a259e8bf6000000033ca6d28c700001200ca874980000000000c4a
  | 46 => 0xa86de0000e802dd312800000000002de47e924a00000f922e525e215e94460000000428b000000273a47c0000b0607b600000006bf8000b6a00004648e5ac7d1bba000156c15d8000196b0ccb7480009bd127e866013654d834e4d587709370e18b2c80009aa0c6a02500000000000000000036c9b8a9191b16b209ef6b090ad20a71d9437aaa4c7e688fa29480000001c2e20d90de3bb1950c3005ec9d701fcc61117432c2d10718a6622c915f057fad265d5800020800007570e2cb300982b6eb1543b60000000067e000132a75f041a4c600000002f2cb3e00000000bfc0000000000278a3d0aa3abc7073e5449f280000b7e03b94f40000632000006a7678b203e52fd47acaf360001d5e41f98d84f3a7ee59100004730000c1a8000117aa9cb9e000098fa6448a6933a57d1f9095b80002f42076949944267a01c02b380000000000505a44e5102bbc1eb30f032e13ae632950e000068e651800055a0a1cafe00004c98000c0d80000000c82417a0b00000e361fe8f4ac629092bfc9c8c25b05f230c0000000293a10ba408000000018780005b30558bf08dac49602d69f1228241c268cb5ca07c1b19d42459afe2a4b2292754a5603d69afa9f62e8a0cc137e5a39bda2c286cc97dab0e95e11c8690115a5a101e6c779438c11908872695144511b98c31acde86a8de472085ccaa0800012c18b60e88000bce24c60001fb400017ccb41ae2a35421b2b97932e0002c3c0001d50a0800003e600000002da614eaea80000000a028000ae78000c57a28c4392db61f787f041827820000000876ad5a0002cfa4fc2d909612ebc1039b24abd0814000272e037ad20000000000000002d3918400019c02989d580000000000000034e10d2000000000000008a1000036398e06bc800000000000000b4200000000001a2281c80002a18000b259f18afa8000826a02800013a4597000098c80000001f4447ba2662e31ba6ac88000067a0a21318000b5d15b262580007e70000343800076000009cc309000000000590208bbe910e0000000a55000011e9a76027000000000000002a24b4380007b98b9e82f8000bc48000000173264484d8616aca852ba70400015f23b4a7fac7e800013e1ef2a6f00008f68000425804200e08489b3800000000005360000a59800000030306b50b1800024a6000213e378270c44e2ec4000000090980009e60000000000000026dcabb87c4787aa3ec05af180000aa6442304200004602c71df03f11e544d080000002492bfb8000b26997e9f2a4067fe9a32c39000038117800002e4270e80008e6acee000000000003460000000381ae7e151b00e00e80007b880001fb91c083a08ee00002e200000007da928091c8000222013e85a80000002d180002d4666a80000de2d5e1798528089a0a045780008521cf450b01f
  | 47 => 0x3188c64000000042c000009da48a62222a26d4091409fa3d84d39396ab2000044c3070c26893aab400000001a60527271608e0cf8143000099228023010b088188ba020b09ba11d16aa28b09523881b7c9538100a2d0614a7d266e68d8fe27faa290b3186a6a0603682cf9d2c1a481240fa9bfca6b83720002c6428e1b0c9848906100adb867c80006649824ba3815822682f47b82a420001ca20002cf600000000000b8600000000000afe63a95e894e811c0002b824ce308a7ecb1c2c558000494ade63e98e0893622be89516fcad2ad2a00030667c503a093a000094719e03f40e1227f031c10e19e611a14be39fa16e02e908a10b1a806ab8e3c244239e17e88e813002f6729988c218a76424580005608000000000069b0318b0a817e7f99730000000001180004799ae2aea04569dea0544492ab068980008649cdc70880002bd2d6e000123876d03a6000132c4608fe06183150000191e80ba05c74680009ec2dbe9f4000000000000769f5400000000002548000000000000005f080004e880be0002b94bbf259266d8e460680dfe99f0a3a9c6af7a98c0d16a65304456e11aea428000000289c0001cfa9b904da0000900203198000021520002daea6e9f6882a97147b020ca4c18b1252c814c00000002f718ee0000ac0bccb20c39482bc003a33c90d94001e58170837307207180006a300007ccb1f82fc27e4b9eae4a52a903284d2d9836a0000425010c0001eec334b01a2fb000084f00000c49fae11e23a283b00000000e903ec2ad82f2895010eac9eb718000030808e00017ae1ec1e1c428262a44e800084b80105598000c421dea2a90aba26680000001a4679e90ce33898546f32fec6111d0095d1cca80c30d244d299e0248c8e000000000000005be1b6e78d28520000000bf627204d20b70c03091cb2016b6000231a3c280000000000345233631100005cf8000000000034bad16000000024b06861ef00007b6886c6bc000000009b844b943c59d800000000001fb00000a6107283981325951f4a9f4965628d968858c80001ed15e0000017c44f0f268560bb8111a34000022b8446a924767100484d8000bd3a77290e8c6600000003faa85a000000000000000968000acc00002bcb1a245ba106c6d00001e30f8a0000000b292fa60001298a452656a0204ea412800000020ae3978ee837400006f72a3400000000000000959000070f92a00a2b0507f5821cc1b184e021184878018221080f9047380008f31e427228154000000045e8250c6700c6a24192a9c607020001c7c9c0120849185541139426af4ab201acaa2800000000000ac4000000000010b8000000000000000000000000081e00000009fd8b6658dad4810483fa2572e10bd082d0000077c8861af632f80000d98ce42ec00006d02b5eb3b00000002768c3
  | 48 => 0xe3984c8df287e3342e26a610bfe2dc92e45a58860021a212420119620e117810ca83653011ea3d50f44a6a26800152dde14a9b565fa093e72d8aa8bd0027a6999ede1940114b8b1c8e6ac8fe80001baa9842812a3900000000230000000010d80000002116a570fde1f4946e183a7c6232869610a28e023190e89d322cc0000aca54200008a0145c00009945199ada00022d2a5101780000898000183640197dca561a0ebe82c4a099983e662000088e8e584b2a1607aa944a5bab0d806d0e42163162865603741d2870e89f0222beda3ac2f2006c79e120c00000007af88e20001a7400027e2a9126b02ab80000cd80004fbab06943012037f30844a501825308b227a7226038f800000000fe301800068b110411d80009708904000000000000004951a0c00000000000aa2b71000022080000000000b2d00007e9ab8821f000070f040a0001d40000000011f80002d02e1800023e87a008de23585e402c2d3eae623b814c00000000000ae3148a00000000000000000000000004820000a940001dc400001f600000000000e620cd16ee8c8800068606121bd8000a0900005e5800042b80000000a080000000000000088a8a58c5184b40002382c79aaf00b386d0911000094d826e0001274bb8a9740288498252ac026951fe0bf2a8fe5e08c6e1ca28060ca936a4c21bb21169e2a4f4a1c247f11ca11418d48c4215e9d295e49839d200c025c60000ef0b28ae3e16f15fc00022368490fb4994a07ab4d953eb2229c089019eea2ab1f0c13a24609531ee420b0d439b1484a7a06e645580cc00022d400001ce21f8000000280000024804bd31a086a153a1fa19664172fda5d49d6c313ae6492089300001c1a0000000698816c00027d64bb87c8b4ca178959adbc9bd8000445814a8610928aa697ce2b0958eb0c80000002bcca6d8d4e000122422fa01e00000000001fd4000193cb1c20360002a7c00026400000000000000006400007590000306810ab4c00000000750000000040900000002faa2b5000064b0000309a7b20000c6c00031a456a19161a01abec6a2f064150e9e78388847811cbeb2aa7de8fc91602d219f000019ea4a3224855102584b028107e590e62d92d0800010461f91eea4e3209e758a9700000eee96e142283c80002e28000000041e0000000000101600003d28a280005e9226a83d98be2ef8eb20001fb847d096854980000002ac64e721869e5029a00024ee54d31340002be0367088ab9b8de20dc2e1aa601d389530000b82a9aa4b21598c7006a22fa1dd8c222068035a71e5abac5e27fa66894788fc9739c96525088e0001d6eb0b2e969629e6c000165abb580001371be6570800019b8e7800005401e1a07eb5c315a0000000b91af44a5887300a800000001e161efa11255515fa00000000001f72c1a00004e800
  | 49 => 0xdec00013d6bf02f4c69f12b898d910a228206086682609ed285e00000f4000140aa8f000000000005e70c2036690a69f300003b819900000000a770d8c7a298de0000c2c0001ccebe499208fc22c000000000b70e606511334000126633d09324c282ae0000000ac123e6be3961653e99180000000c0b8224c3d000000000009e18dce1fe229800000005798ff2000219e0000f1a000076285c2fb03eb8bb262900003a622ecab32f9a5c903fe00000000001a5c8759b2c0b10000ae1800017fa18a000000027222f2095800000000006b10eaa00022de0000000b7d138e00000006731aee58891fe0000f629d4207800c8000c510000000000026800000002e62000061c5ae981666080007d982ac0001abc000000096aab5091f9c28bba92108deaad600012f21a69cfc434298818a2d1c4b5a7840000000a088e2228500fa9220058b9610aa96f14c4aee1d1c4d78daa9028000bd80000000099e269131aa250000b7fa7dc09a858e823a9b43431be8084ab347dda3142929e866282504000000000012bc75d08c41e499e44db1a106299336735942a4ba0cd62982c8a7131f623dda67ea900d36c292674744319887f2cae89300500002a92c39902a8ab8ec430fa8a060099a625f128e225019c693810838c93d8afa1b1035d2e4c000214098b225809c005e4310000933914c8e3aa8a0782b4000906da4c31c6e84b01a4b7d80d47ba2aa20002732a0a800422c0b5e792aeb4ab080007c980000f7300a0000000c0e97f418f187294680006530000000179000000009ef0000a95993a00009b000015a467d0a5c70cad3c7e38000c66800000000000002a6c000311221527fe00000002868606bbb1c7400007446682e1284c80009559efc5188000ab98000000252200000000002ddc8529dd20002b46c7f80008c200007e01dfa3a12fe63060d24061030818e14a887185c04c89b747de9e020ea059697c2cf006392b4974aadc00022520002cd095e8d5a00000006c28866000000056106bcbd4280e000242281b9ed2513099200028f01149dd6819315239b8b7a791800037e0000676048496080000f91e060711a02793000000000008d2a83273680001e89a90000000000000000000000000284ab0d866c00012223db84d000026c06d9b1885c493b8b3100000001d9800014e400014ea9fa189497d25ee0002a38717950a94d00006d68000000092a26c97f60000000203878ec0d0000ba48b844b1835200008eca1080001cc84a2036811671fa60445b1e220d6204c9860e8200022d080003b20002694aba12ae6ce800037083267df192200000000e707b89c2a5a443f96722a72538ac50c5e753042685b273ec371b00478049600007a825386b0161a0185b1038892e9df449da1e210a855c79a977a3089aac4d1064a0d80520c5395940
  | 50 => 0x904a7a810fa0c800023ec93b107649ea892c01000000000000001ab40000494c3f95566a4899c0449cd217197387458f005679ae65c394b802681cc10920fc0b522d896b86422739f8670208b6c7515bc42d86b8b02096a08a8000000024e0002c74ac2ae769142c842301ae45afade88dd80001be800050d912c4a58ba2b9c91861903202409a0f4168836e22a0bc686420da28f8b58566901c7151874200a2885810d105ee2bc2bfa92720668e705d01b0e16080004c91c4a0000af800015eaaf00da2b32000000020028071ecc6d10000aa39ae83ef1f381ba928a000237414b2e3c30a1c306a79e5a403297c9b8a4aa5e6292a51f1ff8000000092108c80000000b681b60bee1d140002e883fe2dc09c480002b71704a64b1e89d11af877282a48198584b0980000000000122800027505a00000c3202319c82d1800000024d4000000000000006c2000000017ea0522b2c000000000013f20000000b3280000002c862eb00000f60000bd5000000600001bf002c0bea7ac00018ce20a2bd60002a5e7558000000000000000000002250bc80758a6e08cc5b184f0515aedab63181c2028b54440a95279c196c0001b820000fa200027c8552163c66e85502200e7aa3ba4d00002960a9624e2c4183c059c195a0558658000242809888a46bb0fb232322b68d41be00869398520a2860a389fa5b0883c67892a86b4317ec0e2c348d982b64d01dc699600009afa83052891126cd2ca0aa426fea8128c2332166eb821c38546a3d202b8b963ed930e3c92b447fa2ac0b832d76b56260a22c9f9e293a8f61f0af3426b214ca139a6e2dd83f2a36869080f99b2b50088671e24a87d20f7e223027456d9c360001e200000b9000021b80a480008248000144ab621742c3e18d1db2000069c38e91d696014e8c4bb1e000001e46571eae47780004de80006b20068000072caed25f20000cfc61a8000000000000000002ce8000be5000001fa5d86bf00005b48d982f524c089e075695011d0000000000000000000000bde1cc4a69166c00026ac000121aac08d8a67588683daaf00b60117c29e00006b800004d48000bda000032b9d9a37c19960d79e362c08c7cbe08de8a279ff4000000053685600000000000109c00019fe0001f3494591da31312b22e92af89999c76bf3a84804796e88ed800000018fab1f834a1bd194e52eac109b630863d00efe8d80864c050d1863091409b1affa1a81cea498159c00030f2407a47092611369f68000000100a8aa84e00002a8477d8000000000081c255ea5dabc491a824666d1a7068717f8000090a0000000703987a1269eee5549d822fc84fc9a2000044500000000000174a6a4000119400031d68bc0000b10ac8e0e31ef8b5f00006e004b24828000000000006f28e200d0cde404acba3f92b7a620af9e1c90
  | 51 => 0xb1fc8128ee6000192853b2d64b8103d0b85808a2c38b44a4f8000146928446a000063490baada88d0bb60b2e7b91386b89064c57299b84878a0439396bc2eaa204c6c02862aa876469f9f2e71380002732e2808821ca00009ae2641c50532a96800000003690e860000fca41a800000022424570000000026400002a81da226c00021807a89bd037605d8906aa521f180007e5143a52f12569120070ad69f0e85385f62cc2ff469e80009a4131034a2424072b10e000275246b00008ad1aea2c18000ab92ee8000051059e00001f023c208d885a9779014a9e8abc02aa5d031a31ca00009de23530940000000000232646aa29e43d27ecb72a508469186c99717d617583f46b3a1542102ad2a62a15a29990d4a9c279626a0be024d00d00001e6858b978435a000000000003baadb00000000000000000000000000000000017600000009b5000064307086e580003f61d883efa1de61780001dd000075fb0228a98000a7c0000b490000000000092ca3860000a10000301206d86be0002a747f0ac382ba17620000d56000020ab5f897841f212a65b94ac93d2f22189085e61fa3121311d3e92f2928993905a609a90e9b08316022245aa2e235835daba451a8000888a5da0d32c4421e9ef42d691b27be873ca9682c86b796b8000279045289ec3f728dea5c83ae5b29c12605086e3f59c800002b92000103830e2866a76258ea8a8d30ac981628b2000000000005f2aaf2a2117a099ea4ea00000006d51b388ef2dfa34081184789ba89700000abdac5455000001b5ac7c0ed8fec798000033c25e423faa9803a906445f8000000000000012329f510900001cf200a054a2eb80008682fcc0000a7200000002ee800000000000001f1200020521dcaada73a19c416999da64503ee4550f160e000005d91ff04ea00007bf97aa73305380aeae1eb888eb082b0000a1c24da81b175e4cc26b21a50000bb79a1419390b40000f8860f2e4806307d600006628be000000000000002dee00027aac6e1e2eb8b98327781ab6368137814f00008262ff00002bd09c9a5a66b32fd28ba00006ae9bcec6b94d65842d84a9925687b38000000137407c126a0001a34b6880562f303288d480009799f1c58f8000bd71106c1904ce0000bda5da8000915013a2fe00000bb30f85c4314c5331612000044c692991c25f8000000090cc761cae0000830ae5800006b86023830746c7418d61d003cc972a8c89fe0f864ed0d34b25125a0002f9865c96ac15f800000021d420e80000bb80000002b4e00018ba49f0000b0e800031c1e4e6fd80003ea85d449b96a20391774ae4000062d00008bd00000000ab262b8000000007a25300008be96f2000075c03f0e9aafc97c8ae1249c56f8f6c49882ea9c70db66b7172c00001ea794ac5051d8ef23b68a88694800000006f8
  | 52 => 0x624b90867630cba5c70a980c39de463d98468231e447fb96b232697167b41da812431aa8b70b38afe8a7617a8b883040c2a1eb9ea801f00005da00004039b3e3129bc20538a7e4fd2d4a0000000128000000000000000000a18131c0000000639249688680003cc80006a68e7699b03c80002bbab85160c1ff8000000000000031640001bbcab79e500002f4607b1ea44a69a9c000021634b0d70a53800049428f45711bb0c0188b41d4800046d9c8446f241400031ce51ea9468d222a09109fce2ca308e14780008aa25e85150f601ce91be2cd07ca0c816264f0927052826fac401f584f0198e71a9d063b000003201c7a6da95581a7901a11089bc62ca40c6cc8bc400025d60a52c222170844ba01718b672d9ebdc11426b087104c7a8cc896a0388938fda0001aa078995f800029ec00005c43158f023f3096412a16b4c3824fc28823e00f584e40389bf0672ab1cc3b05948f100000000fc011200000002524b00057066181bab95abd80000de635b9ad663e217a00022e2a84800000001d039f000076b31160000a845f180000001f1a4e5000046e86780dfa22c7fcaf1ab7f313800000000000418a7f00000000000786ac1460c079e00011dc0002a180000218b530000065800038393fa32f0122000000000003445508caa24891528f9155e0002fd6263a1fe6a580000000d888f78a32527b1182a694e614d06188de2dda332aa6a2de1cec12300001e2305292b00006d49cf80000bd8709000073b8954ba080003cf171a3700000000237263b235a91e0b1a00023f487b000066b000200000000c5000091714ee000000000024b82d7089253c80007b611a26a10000591a6a69572b7e5a61dd4466141a7d097f24ca0000ab81b3c0e58000c20867a94831b23b8952c0110970af29dbc802ac780b300007f7a36a6c500008bf27789d6800068100000000000592a37e68c00006a1afbcc35ac0a054862eb5e91729abad12a7f814491f0142ba983aab3a237065e8ce07a98466000220e64980366eb24760000a9e49e0000be11ed600019760000a0a00000001d511d480f000000030fc00000001b7000059a1b7aaca9728a7e1a38476294c3e08a023b929acaa9054e594800071a000000000004f3179e92321ac00000004d283dab8384f4a7e8d1e1f62a4e43b150c1e60666c3229820002328000047005b8106b78800c4f516380000c1e00000002ed87a40001fc637d298c0000dc8b81800000001de17c00002702df0ac2000020a91a05590e64c2c23b00b8000000030021881ac67c0820c0002058aef9f361270ba6485015a090012e00000003958000322800043c16e27c22eac0001f22be5800060b10cc80c8962351060c577961e177955a3e92c5c6a0ad4267f24307478b100001448426868428391d227600000121e66abe868cb53
  | 53 => 0xea1d2bb09ce02ca966a21182887e49b861052c4c0001e629e894440002906b0190a8bae1c26968abaac188a6e78e2d1a65831104d3172e661126406028aea59167e00c0ac6a91ab685ec8d9073fb04c06a290c907821e3f0a4ca35e0000b14a990b9811b800008f898a0000418867c0001470399800086f80001378000012a98600004fa000082e927b1be0000000000160033d8000bb3000000000005581862bc580002919e405be9200636836411a8342105a9ee858a7401bcaa0a8798af015e203aa9a13cab912b74a238c883ea1e28a8813c83312cfe3b18c84a2629ea9c380000ad077a86e80000001720000285c7c1a7e05442418a708856c2b264238d0bd20a32e3600012cc1e5000000000000000000a542886aeca3d4c5216a40d206d43c18c0cad0a0148109cb259314c854613dc83919701f716f0c83b0d0a4498104a79d70ae289486e902de68f000029200005d7000000001a68f8a3c898f000000025cc714aeb20b4a0d29083192000262007e837600026080001fdcad70000820000025600000001ba05b38a16029a83c01d2b2e633311c83ea0c247caf0a7112a26bd911c67240ed45b80e8e5338cc200005b400000007322ace7ae97786f11726ade084ec52aed25010272bdf80dc7290f6811924a24971b468e106ba27e112aa72a4b0535291e88caa88429000087e155047dabc874a0f7a490215c6668a00372a6a22f083f899280000000000a9c8186afb8000a2c80003120000000173c00029407121b88a68a80454b803e6399c42918023a4899d22a88a17424f235e6cc15f6314960a5a18c080582c9091e89ca0ec1fd200007aa00000002f5ac687ac227463a09260000000000167c0000000c712aec295a6aa11286eec7b24c43c809e40b18edc65e279c7182be6914a93c22726b80e4876e7eb00006c616822f9af7c81a97a64709d0817282f87efaa085ff075e7f900000002230be220503530a64b1683040411d1804097bc00000000000000000000000000006528000000320a000000014980003508bbc5999b6c0002cd20172206bbf86d22018e72a1a1a3aa0500000000000000035a52c315c5f000000000000000072a00000009bc0d264e10000000000083e2e1c000197c00029cc9be11ec0000000064a8d842380009518000a349fba000168c000317a0aa816a04f198a4ec800000031140001b4e00009e600000000000000448141c18da10864c80007c12df20100000000023c7c328d000000008438000072119c430aa1431d8e747d3055e3d19f24c508000000000000000002bb1a6a000274e9a2a4f80138000ba431c8000000000009dcc24a6e000004f6a328f4e1359b9e000000074a954c7ef0ef887900002ab1cc08ea96a819a9516000000043e0cdabcc000070b2e9884999fa00026349fa8a5e000313
  | 54 => 0xce84805f400000000001b7e4e69cb04a98000be328780ef0000a1d8e8c2449b2a5fb1d341c300000002a54b9414f80bf800016b91588f2800042314f0a7d9c16a66193e863205e72a925e346a356342305a9f9940eaeba36891619dc10193708c91842af899747d7a1bcb8ea466a0b954665526de2e69362aeda59e60e8000432000001e00009dd800052996e489a13a64148ccc522000080d000079f84ec0a79f1e1ee8188585000045c00003c8920e0002ed02b9ae3844a2c72937a208a4880002b32b6c75aa1f68cc2c400282e9cbc120888eb9fc489f929063215a60fd80e89b118fe03c0f802371952bb500001429a1679bacc2c1e303c5b6831aa0e95d21592682188830c4b109f45f780003fd1bae1e72bfc6cbac0eb6287a6829ab327d1b1c674d97c4a81963075ca4623598000000095e000000044993888d90b803372b6430287820db0d60bab80000ff05b21f4051671990c600013ea000000047e2afe8ff93e86932f5200028748c380000002626000009e5a00000160000072480002e60c16141800000025700002f86b7b0e92bfe252829f1898b3880000001c461b800000000000463110c00000000001a5808f97364b782e63d20000a86800003b177012fadb491180005d10000b2b29e65d2305ca1f140c00000007f400000000000966af2400000000000b60000256273089a6ac68000000000042cab36c5e00004b625980e90000987a0b46d600000000000964255a8b280008f5800000020d8af5157e1840000c0900009bbb10205a000000002be0000000000258cafd000003395d61c1161a7a503c238c2bda09f06c061c08f000000002ed059ea922b6662e0000000000000028a4a0d0000944800095fad92c0b12f69c2240035180003898a8235217584e2a21c2db049282709740000c50774056ac50145a2062b3c9619f2c1c60000523800000000005539e3a1a21722000307a15b89eac5988bc00028640000000000224400024e69a780b6000205698680003170918a40000049b30400001c9e000179200013f6000009848e8000c3e8000777a3625ac10e277f80002c50000328877e9ca800091b8be262b00009391570000084a36c083eb071b26326311a0f2a7cea2687668168a6a79c9cf00971a063ee914601685b813500005628ede0000f3a31f8b6e9c4000017389d01ff0000a3113ba02f00006271ce24698878bbd8f300002f2e0002bce50208507738fc6000238888ba0f0a3718289889f2aace9562a75289603e2b8e97b00000001e9ab9d05984db8000000000000000003d610fcc2daa2e00025000000b1e84880000000000bc50000bdb86e457380009d8b010093261cb1ba2a4946062c7ce891e93ea3963841eac795ac9c1ab0000097956a44015dab42ab6e2fab1902299dae4df2f2a79703be739a25635
  | 55 => 0x1dcc0002a02000309ca4c8b6218590c006631625f522da162a2ac0020cb40000000000150660800009d51c9c50b81f4000255214380008a586ae00000006ed94905d980007a48000c5f00000001b6461630ba4b400008211900519253c3659ac01c70b3201c924e1cd277c952a0262932862005af665efa494c27969056400000000000236ae54000000000000009ca2f56c2f969400021380002e6a000000000000004e7a1b06241574aae904499c921c54a89f047ea08a78c852e4bf0000348ade085a00000000c12ac020203951ba237486f067b022e0000604000047c000123c845065cb1597d08c589f60000000000252a1ce2dcc2f39c0a54c8f8400000006632ba24002d441309d7a00028f89cf1236321977619c0ab09fc038a3301bca7220a801920000b080000a319164bbd156e000000043a8e4800012f8479046ea100aa0526200c0eb147282da20a2e38c9c116074883820084d40c9e96d252c2380000aa58000942800025b98f0bca28165761d32af902840001f829c88000a0a29429dc000095d9d12436988a000238a227a78eb011b029f0ac620000000000000036e0f6415d16d0674a8383cd992e000288a358800074123ce5e21c0435c9bd47fb2eb64620000873a53096800005ff9c7266500000000000739299c0000c586a392ec121884230910d804a8000000040c0002aae0002ee000016188891ab8c1521667c2800000012d244883548f00a24b66800037c9118139aa66869911078f836a57b88908c6000056c00000000000000184092d975400027463008000c0c82520001040a878000adcadcea4b80007e1000014909b6bdcaf3e4f400008d38ebe0001e8200002020049b1288facd8634000000018f24809864a4580006e687f2840b08c3d7a8a600014e083510e0c1f80000001020000160200030
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe386419530440a5970edb226088002b6a1b534c11000765996c498220018f88758930440013e50fa8a6088002f460c514c11026fa8298a298220049d8874c530440079b0ec98a6088002d6215314c11001ee838a629822004bd0874c53044007ba10e98a6088012f4a19314c110025e8432629822001ed0864c53044003da6ec98a608800f749d9314c11001ee83b2629822001ed0764c53044001ea70a98a6088002f4a15314c110005e842a629822000f50854c530440016a10a98a6088003d4d95314c110007a832a6298220a1bd3844c530441437a30898a608828374dd1314c110506e8ba2629822000f93644c5304413ff20c898a608827fd4d51314c1104ffa8aa2629822000bd3824c53044001da6c498a6088003b4589314c110005e8c1c4298220009f08748530440017a30690a60880021fe1576481100d43e42aec90220008bf845d9204400517908bb2408800237e0d764811000c6e41aec90220048f686dc520440050fb0aba4ca0806b0fd5174994100d61fba2a93282003a748155265040011bf06b94ca080063720d72994100143e42ee8b28202d8f7815d165040071e902ba2ca080121f21d54594100061fba2a8b282003a7481551650400587ce8aa2c6080030f5d15458c100246f43e86b182000a5e85d0d63040014bb0ba1ac608003875534358c100056741686b182000acd82d0d63040091b90ea1ac608003875514358c100062fbaceab182000a9e841d5630400153b083aac60800297a167458c100052ec2ce8b182000ace829d1630400159b053a2c60800297a147458c100052ec28e8b18209be5710d516304137cb421aa2c60826f954435458c104f72c886a8b18209da5d859516304001c3ea92a2c608002b5e055458c1001d6a40aa8b182000e1f845516304001c3ce8aa2c608003875d15458c100072bc0aa8b18209ce5481551630413bcae20aa2c608277968415458c104ef2a882a8b18209ce591055163041374bd0a2a2c60800297e157258c100052e42ae4b182000a5e851c963040014bb0a392c608002a7a107258c100054ec20e4b182003ad6811c9630400b5ab02392c608012b6a007258c1002d6cc00e4b1820008de87d0963040011bb0fa12c60800297a174258c100052ec2e84b182000e1d54d096304001c3aa8a12c60800297a144258c100052ec2884b1820048df8758f53040014bf0ab1ea6080123721d6354c100161f3a2a8b102000c3d7455162040091d90ea12c4080038b551425881000c6e41eeca9020008df835d952040031b906bb2a4080121f21d65548100046ec36e6a9020008de8758d52040011b90eb1aa4080123b21d62548100064f31ae82902000c9e7458c520400193ae8b18a40801237e1d638c8100246e41eec990200087f855d932040350f90abb264080123721d634c810
  | 1 => 0x100b8c648806a1fa17764c9100043ec2eec99220028be84dd9324400117b09bb264880021fe15764c9100d43e42aec99220008bf845d9324400517908bb264880023be09764c9102a6b9386cba8a202dab48459751440998ecec32ea2880038d19065d4510266b9380cba8a202dab686d9351440a396cedb26a2880038dd9764d451028ed9386c9a8a204cd72759c351440017a307386a2880127ce1d70d45102a63c386caa8a20048f587d945144001c68c9b28a2881329d61f65145102a63ac3eca28a20008f787594514405956908b28a2881569da1865145100063b3b0ca28a2000e3464194514414956d0db20a2880038dd976414510024f8402e428a2000a7686d48514410bc68c9a90a28820f8d191521451026daa41aa428a204cb708054851440093e5013ac62880038d190658c510024f8402e518a2001ad48358a31440990fd0dbaa62880030f193754c51040eb8086ea98a205487e861d53144001878c83aa62880ae1fa1f654c5102a43e43eca98a2055e5431d9531440610fd0e32a628806a1f21c654c5100061fbaec898a2000c3c75d9131440618e8edbaa62880123da1a754c51051cbb42cea98a20049f2809d531440578e8ec3aa62881525da18754c510004bbc20ea98a2000975841d53144001a68c83aa62882031dd80754c510406b9b00ea98a2000d72401d53144001ae2803aa628813755cc0754c51026eb9180ea98a204dd71301d531441472ed0fb2a62881531d1db654c5100072a31eca98a204c9748719531440998e8ec32a62880038d190654c51028e5a3b6c898a2000d3475d9131440031e90eb1262880035c1d7704c510006b9ba8e098a205487e869d72144001878c93ae42881321f21975c85100061e322eb90a205ed70105d721440a90ff0fb2e42880021f61f65c85100061f3a6cb90a201a87f8719721440010fb0e32e42880030f9d065c85105145e432e990a2000c3f655d32144001878caba642881ff6c04174c851028c5fc3ec990a20008bd87d93214400187cebb2642880030f5d764c8510024f9404eb10a2000e3464196214400f5c904b1c42880123da1a7548510024f9404ea90a2054c7476d9521440a9ae0e1b2a42881331d1d865485100071a320ca90a204cd707019521440a3968edb2242881476c1c364485100247a432e690a2000974855cd21440093e100b9a428801e3d21d634851000733b28c490a20049f287dc121440017a30638242881521fe1576541100045fc22eca8220028bc845d950440ab8e8e3b2aa0880032d19371541100071c320cb1822001ad88358a30440093e50fa8c60880127c21d218c110005e9c1a431822054e5830d9530440093a90e98a6088012b5219314c110005aa42a629822004bd0804c530440ab8f0edb2a60880039618f654c11029e3c3b0ca9822000
  | 2 => 0x176d4d100070f29ec9a9a20028be84dd9534400117b09bb2a6880021fe157654d100045fc22eca9a20028bc845d953440011df04bb2a68801e3b2097654d1000c3f43ecaa9a2055c7471d9553440091ed0db8aa6880032d1937154d10024f9406e2a9a2000c3f745536244005878e8aa6c488002b960432d891000574c0065b122000c3e74d96624400187ce832cc4880030fd9574989100061e32ae93122000c3e75d92624400187aebb24c4880030f9d464989100061eba8c9312200087e87d956244001878e9b2ac488003171cf65589100043f438cab122000c3c7419562440018b8e632ac48800a2fa1b745891028c5e436e8b122000c3f65dd16244001878cbba2c4880022fa1f64589100061fbaec8b122000c3c75d916244001938e7b22c4880022fa1c64589100061fba8c8b122000c3c751916244001938e6322c48800317d9773589100062e32ee6b122000c9f64dcd6244001938c9b9ac4880021f61375589100043ec20eab122000c3f75dd16244001878ebba2c4880030fe1774589100061e42ee8b12200087f855d162440350f90aba2c48800237e0d745891000c6e41ae8b122000c3f751d16244001878ea3a2c4880021fa1f54589100d43e43ea8b122000c3f74d516244005878e9aa2c4882a3171cf54589100043f43aa8b12200087c87551624400187ee8aa2c48800b0f1d1545891053e2e39aa8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f54dcd62440018baa9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac488003331cf7258910016563a484b1220a6ccc7390962440051d90ea12c4880038b551425891052e6639a84b1220a2cb57119062440011df0eb10c488002b320d621891003c3e42aeda9220008bf845db524400517908bb6a4880022fe1176949100145e422ed2922055c7671d9652440091e90cb8ca4880032d1917194910024f8402e329220028be84dd9524400117b09bb2a48800637a0e76549100046ec1ceca9220008bf845d9524400517908bb2a48800237e0d765491000c6e41aeca92201a87c851d9524400f0fd0fb2aa488003171cf65549102ae3a38ecaa922054c7870d9552440018b8e632aa488003271cf64549100062fb2ee6a922000c5c65dcd524400193ec9b9aa4880032719373549100247b436e2a922000c7765dc55244001968c9b8aa48800e3ea1b70549100063db2ee0a922000cb864dc15244005179093b0a4880022fe1176149100145e422ec2922000c3e74d9452440011790cba0a4880030fd9574149100d61e32ae829220008bf87d90524400117b0fb20a4880123d219711491001c7c432e0292200087f855da32440350f90abb464880022fe11768c9100145e422ed19220048f4865c632440093e
  | 3 => 0x432a2000a7581908654400187ae8a10ca8806a1fa1c42195100043ec388432a201a87e870c865440010fb0e190ca880028fa1032195100051ec206432a2053a76810c865440014eb02190ca881329ea0032195100053cc006432a201ac74715c465440350fd0fa08ca880021f61f41195100d63c382e032a201a87e87d0065440010fb0fa00ca880029de05401951029d3a40a8032a2000a3e86dd7644400187cedbaec8880028fa1875d91100061f3b0ebb222000c3e76d976444001c6b03b2ec8880022f61e65d91100051f42ccbb2220008bf87597644400147d0c32ec8880030f9d865d91100051f42cc7b222000a3d8598f64440a556d03baec888146ad60775d91100071b40eebb222000e3581dd7644400147d0b3aec8880030f5d475d91100051f438ebb222000c3e871d7644400187eebb9ec8880028fa1673d91100051ec2ce7b222000a3f855cf64440014790ab9ec8880030fdd573d911000557c12e7b222000aac825cf64440a556d0239ec888146ad60473d911028d5d400e7b222052ab9801cf644400117d0e29ec8880022f61c53d91100061fbaee5b222000a3e859cb644400147b0b396c8880028fe1572d91100051e42ae5b222000c3f755cb644400153f06b96c888002a720d72d91102955b408e5b222051ab5811cb644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb64440a556d02196c888002ad60432d911028d5d40065b222000ab9800cb644400187ee8aa6c68800b0f1d154d8d100043f43ecab1a2000c3c74d9563440010fd0e32ac6880030f1d06558d100061fb2ee8b1a2000c3c65dd1634400117d0fb22c6880030fdd76458d100061e3aec8b1a20008be87191634400187eea322c6880030f1d46458d1000637b2ee4b1a2000c6c65dc9634400195ec9b92c6880032b1937258d1000637b28e4b1a2000c6c651c9634400195ec8392c6880032b1907258d1000666318e4b1a201a87e87dd563440010fb09baac6880021f6107558d100145f43ee8b1a2000c3f75dd16344001878ebba2c6880030fe177458d100061e42ee8b1a200087f855d163440350f90aba2c6880023be097458d1003c76412e8b1a20008be871d1634400187eea3a2c6880030f1d47458d100043f43ea8b1a201a87c87d51634400187ee9aa2c68800b0f1d35458d1055e36396a8b1a200087e8755163440010f90eaa2c6880030fdd15458d100161e3a2a8b1a20aac6c7255163440051b90ea1ac688003875514358d1054e6639286b1a20078ee87dc963440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018dea9b92c6880031b5537258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a200187c855db534400117f08bb6a68800a2f21
  | 4 => 0x5440a94f5003a6ca881569e60074d95102a53ac0ee7b2a2000a3e849cf654400147b0939eca88003175cc73d95102ad3b408e7b2a2054a75811cf65440a94f50039eca881569e60073d95100043f43e87b2a200087d87d0f654400187ee9a1eca880029ba0b43d951000536c1687b2a2000c3f7450f65440010fd0e21eca880021f61c43d95100052f41ee5b2a2000a5d83dcb65440a94eb03b96ca881569e60372d95100051f424e5b2a2000a3d849cb65440a94eb02396ca880021fa1f42d95100043ec3e85b2a2000c3f74d0b65440014bd07a16ca880029760f42d95100061fba285b2a200087e8710b65440010fb0e216ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca881569da0432d95100053ac0865b2a2054a7a800cb65440014f300196ca880031ddd171d95100063aba2e3b2a205487e87d0765440010fb0fa0eca88157958c731d95102ac3f43e81b2a200087d87d03654400187ce9b2cca880030fd9574995100d61e32ae932a201ac3f545d2654403587d0aba4ca8800b0f9d154995100061eba2a932a2000c3f75dd1654400187f0bba2ca880021fe1574595100047bc0ae8b2a2000c3f751d165440010fd0faa2ca880030fdd354595100161e3a6a8b2a200287c87551654400187ee8aa2ca8800b0f1d154595100065a3a6e2b2a200087f87594654400147f08b28ca880028f21165195100d43e42ae832a201ac3f545d065440071e902ba0ca880021f61e54195100d61fba4a832a201ac3f7455065440014ef02aa0ca8800237e0d721951000c6e41ae432a200087d849d865440010fd0dba0ca880021fe1f64195100061eba6c832a200087d8799065440010ff0eb20ca880021f61c64195100061eba0c832a2000a5e8319065440014bb06320ca880029ba08641951000536c10c832a2000c3d871906544001c3d06320ca880038760c641951000717410c832a2000e2d821906544001c6b02320ca882b38ddc464195100071cc00c832a20ace36101906544159c6820320ca880028fa1263195100051ec24c632a2000a76869046544001c68c9208ca881329d21941195100071a3228232a2000e38649006544001e6483200ca8814e9e21940195100043ec3ce832a201ac3f749d065440014ef02ba0ca8814e9d20574195100d43fc22e832a201ac3f845d065440018ef02ba0ca880031d20574195100d62fb9ce632a201a87e87d0c65440010fb0fa18ca880030f5d34319510005374168632a2000a6d82d0c65440a74ed03218ca880029d60643195102653d4048632a2000a798090c654400187ae8a18ca8806a1fa1c43195100043ec388632a2000a5f835c865440014b906b90ca8806a1fa1f42195100043ec3e8432a2000c3d74d0865440014bd07a10ca880029760f421951029d3b40c8
  | 5 => 0x121f61576144200247ac0aed18840048dc83dd931080091e903bb262100021fe15764c4200d43e42aec988400087d86dd5310800187cc9baa62100c31798f754c42040e3b30eea988400087d861d5310800187cc83aa62100af1798c754c4204063b308ea988400087e8799531080350f90f32a62100021fa1d654c4200043e43aca9884000c3f755913108001878eab22621001f2b1c9644c4200062fbaac69884000c5c7558d310800195ac9b9262100033358f724c4200247a43ac29884000c777558531080018e8eab0a621000339dc9614c4200d61faa2e932e2003a748155265c40091e902ba2cb8826f1d1c7545971001c3e43aa8b2e2000c3f7455165c40074e902aa2cb882771d1c5545971001c6e43a86b1e2000e1d5450d63c40091e902bb6a7880123d2057654f1001c7643a84b162000e2d5450962c400f0f90abb6a5880123d20576d4b1003c3ec2eeca9620008df835d952c40031b906bb2a5880123d2057654b100247b40eec99620048f78759751c40012ef083aa63880025d610754c71056eab980ea98e2000974855cd21c40a90ff0eb2ea1881321fa1e6554310024ea43a629862000b54854c530c403587ea8ba4cb080029de0554996100243e42ae732c200487c87551658400187ee8aa2cb080121fa1e53596100062fb9ca6b2c2000a3d8414d65840091b90ea1ac708003875514358e100246fc3ac7a9c2000a5f8558f53840091d90ea12c5080038b5514258a100046fc1aeca9420018dc835d952840091f100bb2a508003171ce6554a100243e43acaa942000c5c7359552840091b90eb1a65081321fe1d65d46102a43f43ccaa8c202bc5e631d531840018b8eab1a630801f2b98974c861000656ba2c590c2004ada86d4d30840093b10e98a6108002d6215314c21004768b0a6298420a2cb57119365440091eb03ba6ca880030fdd354d95100161e3a6a9b2a209bc7571d53654400187ae92a6ca880029d60654d95100053cc04a9b2a200287f87553654400187ae8aa6ca882771d5c554d95100062eb9ca7b2a2000a758194f65440014f30129eca880028fa1053d95100051ec20a7b2a2000c3d74d93654400187ae8326ca8800297a0c64d95100052ec18c9b2a2000a6e8219365440014db04326ca880030f61c64d95100070f418c9b2a2000e1d831936544001c5d04326ca880038b60864d95100071ac08c9b2a2000e3980193654400147d0931eca880028f61263d95100071a322e3b2a2000e346490765440a94e90ca0eca880038e19240d95100079920c81b2a2055a788650365440ab4ed03ba6ca881529d60774d95100063b40ee9b2a2000c7581dd3654400187f08ba6ca880030f5d074d95100052f418e9b2a2000a5d831d365440014dd043a6ca880029b60874d95102ad3b408e9b2a2054a75811d36
  | 6 => 0x52f42e86b184000a5d85d0d6308001c3aa9a1ac61001eb3a0b4358c200246e43a86b184000e1d5450d63080018beeb3aac61001eb32097558c200054f420eab184000a9d841d563080014bd0b3a2c610002976167458c2003d67414e8b184000acd829d163080014bd0a3a2c610002976147458c204df2d106a8b1840abe5920d51630813b4bb0b2a2c61000387d525458c200056bc0aa8b184000ad48155163080015b700aa2c610012b62015458c200070fc22a8b184000e1e745516308001c3ae8aa2c6102ab87d095458c205570ea12a8b184000e57815516308001ca902aa2c61000396e015458c204ef2c402a8b18409de5a205516308155cb240aa2c61026e97a145458c200052fc2ae2b184000a5c855c5630800f59904b8ac610012b6a007158c200756cc00e2b184000a5e85d0563080014bb0ba0ac61000237a1c4158c200046ec3882b184000a5e8510563080014bb0a20ac61001eb3a084158c2000566c1082b184004ada8010563080015b30020ac6100031794d76d4c2000d2f41acba984000e1e5359353080091bf0eb1ea61000297e1563d4c2003c76412eca98400487c87595530800f958e4b22a6100123721d6354c2000636b2ee4a984000cad64dc9530800199ac7b92a6102769d61654984200071baa4a930840008f78755261080071e90eaa4c2100031de1d54984204e63a43aa93084000e37845526108155c6e84aa4c2102ab8d50954984204dd3b428a93084000e575394e610800156d0829cc210002ad61053984200053b42e873084000a7585d0e6108001c6aa9a1cc21001eb9a0b439842000572c16873084000e355450e61080014ed0a21cc2100029d61443984200247b43e82b084000a7685d0561080014eb0ba0ac2100123d21d41584200053b42882b084000a758510561080015ad0620ac210002b560c415842003d7341082b084004af28010561080095e50018ac2100029da1674584200053ac2ce8b084000a76851d161080014eb0a3a2c210002b5a0c74584200056ac18e8b084007ae6821d161080015cb043a2c210012bca00745842000578c00e8b08409da75859516108001c6ea92a2c2100023de1d54584200047a43aa8b084000c778755161080018e90eaa2c2100038de1154584205571ba12a8b0840aae354255161081374ed0a2a2c2100029de1573584200053a42ae6b084007ae4825cd61080095e50039ac210002bc60073584200072ba9ca6b084000ab68414d610800156b0829ac2100029da1743584200053ac2e86b084000e3554d0d610800f5cd05a1ac210002b960b43584200071aaa286b084000a768510d61080014eb0a21ac2100131e9c165944200265d382c92884004cda7058e51080018f2cab84a2100032e59170944200066cb1ae12884003cf2615c251080090f90bbb2a21
  | 7 => 0x7c855d2650803587ea8ba4ca100023de05749942001c7a40ae9328409d87d87952650803587ee92a4ca1006b0fdd154994200053bc0aa93284000a748155265080090f90ab9cca1006b17dce53994200243e42ae3328409d87d879d2650803587ee93a4ca100029de0574994200053a40ae9328401a87f845d2650803587f08ba4ca102ab0fd0974994205561ea12e93284000c77815d265080018e902ba4ca1006b17dce73994200d43f43e87328400087d87d0e650800187ae9a1cca1001e9ba0b439942000536c16873284000c3d7450e65080350fd0e21cca100021f61c43994200d43f43e83328400087d87d0665080350fd0e20cca100021f61c41994200052f418833284000a5d83106650800f4dd0420cca100029b60841994200253d400833284000a798010665080094f50018cca100029e60031994200047bc0ae8b2840038f4815d165080091f100ba2ca1000b0f9d354594200061eba6a8b28400487e87951650800187ee92a2ca100121f21d54594200061fba2a8b284000a778155165080014e902aa2ca1026e1fa1c54594200243f43ca6b284000c5f7394d650800147d0829aca100028f61053594204ec3ec3ce8b284000c3f749d165080014ef02ba2ca100029d20574594200053dc02e8b284004a78805d1650800187f08ba2ca100031de0574594200063a40ae8b284000c7b805d1650813b8f100ba2ca1026e1fa1c74594200062fb9ce6b284007a6c825cd650800147d0839aca100028f61073594200043f43e86b28400087d87d0d650800187ae9a1aca1001e9ba0b435942000536c1686b284000c3d7450d65080010fd0e21aca100021f61c43594200253d404e2b28400087e87d0565080010fb0fa0aca100021fa1c41594200043ec3882b284000a5e8310565080014bb0620aca1001e9ba08415942000536c1082b284004a7a8010565080014f30020aca100129ea0031594200053cc0062b284000c3f759d5640813b47b0f3aac81026f8bc8275590204df16904eab204000ab7815d5640800156902baac8102baaee0175590200255c402eab204000c3f875d5640815587ee4baac8102ab0f5c975590200071bc0aeab204000e34815d56408001c7700baac8102778e20175590204ef17902eab20409de2d205d5640813747d0a3aac8100028fa1773590200051ec2ee6b204000c3d75dcd640800f55d05b9ac81003eab60b73590200061ebaae6b204000a3e851cd640800147b0a39ac8100022fa1c53590200045ec38a6b204000a3e85dc5640800147b0bb8ac8100028fa1471590200051ec28e2b204000a9e831c5640800153b0638ac81001eaba08715902007d56c10e2b204004aba801c5640801f5730038ac810012aea0031590200055cc0062b204002c3e74551630800187ae8aa2c61001237a1f4358c200
  | 8 => 0x2aa2cb9000637a1f73597200062faa6e6b2e4000c5d54dcd65c800587ce8aa2c7900030f5d15458f2000d2e41acba9e40638df835d953c800f0f90eb2aa7900038b55142587201852e41acb28e4000c79655c251c80011bf06bb2a3900063720d765472015d2e41aca28e400087f855d931c80350f90abb2639001e3d21d614c72003e66392c6986401ac3f545d265880011ef02ba2cb1000e3d20574596200243e43aa8b2c4000c3f7455165880091b90ea1ac710003875514358e200246fc3ac7a9c4000a5f8558f53880010fb09baac3101531d60775586200043ec20eab0c40028be87dd1618800187eebba2c3100030f1d774586200061fc2ee8b0c4000c3c85dd161880010ff0aba2c31006a1f21574586200061fba8e8b0c4000c3c751d161880010fd0faa2c31006a1f21f54586200061fba6a8b0c4002c3c74d5161880010fd0eaa2c3100021f21d54586200061fba2a8b0c4002c3c745516188005968e920ac3100123d21d415862016d5a422c3a8c40008bf845d9518800517908bb2a3100029de1561146201655a422c228c401ac78655c051880010ff0abb2631006a1f215764c6200045fc22ec98c40028bc845d931880578bcc63aa63102031d984754c6200062e3aac698c40048f48758531880018e8eab0a63100133c1c161486200256d436a698440049d8874c9308800fb90e49926110002d6215314c220005e5c12629844000ed1614c530880071ed03ba6ca900023d60774d95200143fc3aa9b2a4000c3d7455365480014e902aa6ca90003175ce53d95200053cc04a7b2a4000a3d8414f654803587ea8ba4ca9000237e0d745952000c6e41ae8b2a40008f7815d165480071e902ba2ca900023ee0174595205462e39ea8b2a400287c87551654800187ee8aa2ca9029f171cd54595200062faa6e6b2a4000c5d54dcd65480018beea39aca90003331cf72595200043fc3aca32a4000a5c83594654803587ea8ba0ca900029d20554195200146fc3a87b1a4000e1d5450f63480018b8c63aac69006a1fa1f7558d200043ec26eab1a400087d841d563480010ff0aba2c69006a1f2157458d200047bc0ae8b1a40038f4815d163480010fd0faa2c69006a1f21f5458d200043f43aa8b1a400087c8755163480018b8ebb9ac6900031b1d77258d200052ec2ec7a9a400087f855d953480011df04bb2a690003171cf65549200062e398caa924002cae7450b6148001c5aa8a16c2900023de1d61185200046fc1aec28a40018dc835d851480358d8cab90a29006b1e195701452001c7b40ced18a401a87e859d931480010fb0b3b2629000f3c18570885200046fc1aeca8240018dc835d950480015b50da9a6090007361db534c120005d4c20e498240049d8874c9304800f9b0ec992609001f721c9324c120005ac42a6298240048
  | 9 => 0x62c845000656ba2c5908a0008df835d921140031b906bb2422806b1d1d561484500d61faa2e932c6000a7481552658c0011ef02ba2cb1800e3d20574596300247c402e8b2c600487c87551658c00187ee8aa2cb180029d20554596300247643a84b146000e2d54509628c0350fd0bb8ac5180021f6177158a300062f32ee6a946000c5d65dcd528c00187ee8aa2c31800b0f1d154586300247a43a82b0c6004c7a70596518c0091f501bb2431800335dcd61486300246ec1ee9b2a60038f681dd3654c0011eb03ba6ca980063e60374d95304de2eb9ea9b2a600287f87553654c00187ae8aa6ca9800297e0d54d95304ee2eb9aa9b2a6000a7481553654c03587ea8ba4ca980023be09745953003c76412e8b2a60008f7815d1654c0071e902ba2ca982af1b1cb54595300143e43aa8b2a6000c3f74551654c1558d8e4aa2ca980031bd53725953000636aa6e4b2a6000c6f751c9654c00199ee6392ca980021fe1d651953000536412ca32a601ac3f545d0654c0014e902aa0ca980723761f65d4d300e52ec3ecba9a6000c5d87d97534c0091bf0eb2ea69818eb320965d4d300f52f430cba9a6000bd1819c3534c0093b70eb86a69800a3be1d42d893000716aa285b12600087f855c7624c0350f90ab8ec4980022fe1171d89300145e422e3b1260008ef87588624c0014d90ab10c49801e1fa1676d493003d36412cba926000c5e76d4f524c0c7c98c5a9ea49800317d95739493003c7c432e129260018dc831d9524c0010fd0f32aa49801e1f21d655493003d36412caa9260049da80dcd524c0018b8eda9aa4980021f61f65149300061fb2ae8292601ac3c655d0524c00f958c4ba0a49801f33189731493000656ba6c429260078f8865c0524c00f9d0c4b80a49801237a1a754c93031e66314ea99260049da809d5324c00133b083aa649823733188754c93003d67436c49926000bd1811c1324c001c3aa8a1ec2980023de1d61185300062fb2ae728a60038f8865c2514c0093b501b9aa2980023be09761453003c76412ec28a601ac5c655cc514c0071f10cb80a29806b1e195701453040e2e3b6ea98a60048de869d5314c0572bd0b3aa629801276a02754c5304062e3b0ea98a600095f841d5314c0012bb083aa62980af17d80754c53015eadb00ea98a6000d5875dc1314c001ab6ea382629801e3e21970c853001c7b40ced10a60038f8865c2214c001ba262b844298012372197348530004ae42ae690a600087f855d8214c0350f90abb0429801f33189730853001c7c432e010a6007ce8625c0214c0018becbb9aa09806b0fd5174997200d61fba2a932e4000a748155265c80011bf06ba2cb900063720d74597200047bc0ae8b2e40038f4815d165c81518b8e7aa2cb9001e1f21d54597200061fba2a8b2e40a7c5c7355165c80014e9
  | 10 => 0xb0ca000af180951619405b1ef0eaa2c3280b23d21d545865016e3bc3aa8b0ca000a748755161940598e90eaa2c3280038de1154586500053b42ce6b0ca000a75859cd619400156d0939ac328002ad61273586500053bc2ae6b0ca004af2801cd61940015e30039ac32800395d4e535865002579404a6b0ca000af18094d619400156d0829ac328002ad61053586500053b42e86b0ca000a7585d0d6194001c6aa9a1ac328002b9a0b435865000572c1686b0ca000e355450d61940014ed0a21ac3280029d61443586500053ac2ce4b0ca000ab6849c9619400156b09392c3280029de1572586500056bc1aa4b0ca000ad48354961940015e700a92c328012bc20152586500055b420a4b0ca000ab58414961940014ed0ba12c3280029d61742586500071aaa684b0ca000ad683d0961940015ab07a12c3280038d55142586500053b42884b0ca000a758510961940011ed0e192c3280023d61c32586500053b42864b0ca000a75850c9619400156d08192c328002ad61032586500257940064b0ca000af1800c961940099b4e0b1ca3280033658d709465001e7930ae128ca055d70515c251940019e2c3b82a3281571ddd161146500063aba2c228ca0048dc83dd931940618bcc7baa63282071d987754c65015e2f318ea98ca080c76611d531940018beeab1a6328003171d5634c6500247a43ac298ca000c747558531940018bcc73ae432817f1d98675c86500062f31aeb90ca05ec76615d7219400193cc6ba643281ff2d98574c86500062f3aac790ca000c5d7558f219400193ce8b1e4328003275d163c86500063b3aac390ca000c7575587219400196ce8b0e43280032d5d161c86500062f31eea90ca000c5e631d521940018e8eab0a4328013369c163086500066cb1ae010ca003cf2615c0219400187ee8aa6c6a80033318c7258d500061fba2a9b12a000a6d850cb62540015d300196c4a80022fe1171d89500145e422e3b12a0008ef87588625400159906b10c4a8003331cf625495031e2e3b6e6a92a08dc5c761cd52540018baebb1c64a80029d61741d85500053ac2883b0aa000af18010761540011ef0eb08c2a8002ad21161185500d63c284eda8aa01a87c851d9315400f0f90b3b642a80123721d4358c500070eaa286b18a000a748155162140091d90ea12c4280038b55142588500257440284b10a0048ec8758932140a70f90eaa2c2280030fdd1545845029d3a40aa8b08a0048f48750561140354e90aa0ac22806b1d14576944500d53bc3ac2288a054c778758451140358eee8b08a2280031d5d161144500d4bdc32e0288a055c7b865c051140358f6c8b80a2280031e59170144500063cb12e0288a08187f855d931140358b8eab1a62280123d21d614c4500d63a3aac2988a00787d855db211400f95cc4ba6422806b1b9d5
  | 11 => 0x9400159f04baac728002b32097558e500052f42ce8b1ca000a5d859d1639400159d053a2c728002b360a7458e500f52f428e8b1ca000a5d851d16394001c3ea92a2c728002b5e055458e500056a40aa8b1ca000adb8055163940095b100aa2c72800387e115458e500070f3a2a8b1ca000e1d745516394001caf02aa2c728003952055458e500072dc02a8b1ca09de588055163940014bf0ab92c72807a97a147258e500052ec28e4b1ca000a9e841c9639400153b08392c728003335c87258e500056b408e4b1ca000ad5811c963940095b500392c72807ab66007258e500046f43e84b1ca0008dd87d0963940014bd0ba12c728002976174258e500070eaa684b1ca000e1d5450963940014bd0a212c728002976144258e500052fc2ae2b1ca004ada801c5639403d5b30038ac72800297a174158e500052ec2e82b1ca0008de8710563940011bb0e20ac72800297a144158e500052ec2882b1ca000ace82105639400159b0420ac728012b6a004158e500056cc0082b1ca000cd963dc1539400187ae8aa2c5280029d2055458a500247643a84b14a000e2d5450962940099b4e0b1ca5280033658d7094a500046ec36e6a94a08d8dc8758d529400193cc6ba0a528003279d16314a500064eba2c6294a00093d841d532940018beeab1a6528003171d5634ca5003d66412c6994a000e3754952619405b1ef0eaa4c32800e3d21d549865016e3bc3aa930ca09cc74875526194001c6f08aa4c32800395d4e53986500055b420a730ca000ab58414e61940014ed0ba1cc3280029d61743986500071aaa68730ca000ae682d0e61940015cb05a1cc3280038d55143986500053b4288730ca000a758510e61940015af06a94c328002b520d52986500055b420a530ca000ab58414a61940014ed0ba14c3280029d61742986500071aaa68530ca000ad683d0a61940015ab07a14c3280038d55142986500053b4288530ca000a758510a61940014ef0a994c3280029d215329865001c7b4386530ca0008f5870ca61940014ed0a194c3280029d61432986500055b4206530ca000ab5840ca61940095e500194c328002bc60032986502ac3f43ea8b0ca000c3f74d516194005878e9aa2c3281569d20554586500053ac2e82b0ca0048f48750561940014eb0a20ac328002b5a0c41586500056ac1882b0ca000ae68210561940015cb0420ac328012bca0041586500053ac2e62b0ca004af2800c5619400156f08baac328002ad21175586500053b42ce8b0ca000a75859d161940014ef0aba2c3280029d21574586500053b428e8b0ca000a75851d161940015ad063a2c328002b560c745865000573410e8b0ca000ae5821d161940095e5003a2c328002bc60074586500053b43ea8b0ca000e3774d516194001c68e9aa2c3280038dd52545865002579404a8
  | 12 => 0x81eaba0b735932114556c16e6b264200c3d755cd64c840147d0a39ac9908028f61473593210045f438a6b2642008bd8714d64c855f55f04b8ac9908028fa1770593210051ec2ee0b264200a3e851c164c840147b0a382c990802a7a0c70593210054ec18e0b264207aae821c164c845155b04382c9909feada0470593210055ac08e0b26427fab6810c164c840156b02182c99080b0f9d15458f210061eba2a8b1e4200e1e5359353c840f0f90eb2aa79086b1b99572d472100636b2ee4a8e420087d86dd531c840187cc9baa63908021f618754c7210061f320ea98e423087e8799531c84350f90f32a63908c21fa1d654c72115c3e43aca98e4200c3f7559131c8401878eab22639081f2b1c9644c72100656b26e498e4202cae7450960c8401c5aa8a12c19086b0fd51749962101d3a40aa932c42038f4815d165884070f90eaa2cb108030fdd1545962101d3a40aa8b2c42038dc8750d6388401c3aa8a1ac71080e37e1d63d4e210052fc2ac7a9c42018de83dd560884011bb07baac1108030fdd154582210161e3a2a8b0442038f887501608840f1eb03ba6ca9080a1fe1d54d95210061eba2a9b2a4200c5d7394f65484014eb0329eca908028f61053d95210d61faa2e932a425fa748155265484011bf06ba2ca908063720d74595210047bc0ae8b2a42008fb805d165484091f100ba2ca90aa3171cf54595210143e43aa8b2a4200c3f74551654854f8b8e6aa2ca9097a9d20554595210062faa6e6b2a4200c5d54dcd65484018beea39aca908021fe1d65195210052e41aca32a421ac3f545d065484014ef02aa0ca9080a37e1d43d8d210070eaa287b1a4200c5c631d563484350fd0fbaac6908021f6137558d210043ec20eab1a4200c5f301d563484010ff0aba2c69086a1f2157458d210047dc02e8b1a42048f8805d163484010fd0faa2c69086a1f21f5458d210043f43aa8b1a420087c8755163484018b8ebb9ac6908029761763d4d210043fc2aeca9a4200c5c73d9552484018b8e632aa49097a1f61f65d45210046fc1aeca8a42018dc835d951484bf0fd0e32aa2908af1718c754c5210062e3aec698a4230c7476dd531484578e8ec3aa629080359dd4724c5210046fc1aebb0242018dc835d76048401c5aa8a16c0908133698173181210047dc3ac03024200cd973580604843587ea8ba4ca1086b0fdd1549942101d3a40aa932842038f4815d165084070f90eaa2ca108030fdd1545942101d3a40aa8b284202c3e74551630840187ae8aa2c61080e3721d4358c210070eaa286b18420387c8759553084071b90eb1aa61080e3e21d40580210145f426e2b16a0008bd84dc562d40018beec39aa5a80030f5d15458e500052ec2e86b1ca000e1d54d0d639400159d05a1ac728002b360b4358e500246e43a86b1ca000e1d5450d63
  | 13 => 0xe56312e93126200cad74d8a624c4010fd0fb2ac4988021fa1c655893100477c3ac43126281c7671d96524c40f1e90cb8ca4988c3171cf655493115e2e398caa926200c5f65dcd524c4018b8cbb9aa4988030f9d365149310061fb2ae8292621ac3c655d0524c40f1e90cb88a4988c3171cf65545310062fb2ee6a8a6200e1d5450f604c49b8eae232cc0988021fa1f65581310061e3a6cab02620087e87195604c401878e832ac0988030fd9774581310061e32ee8b026200c6f65dc9604c4018d8cbb92c0988031bd94725813100636328e4b0262008fb87580604c40f0f90aba4cb9086b0fd5174997215543ec3ca932e421ac3f7495265c843587ee8aa4cb908029de05549972103c3e42ae732e42aa87d879d265c843587ee93a4cb908029de0574997212fd3a40ae932e421a87f845d265c843587f08ba4cb90aab0fd0974997215561ea12e932e4200c77815d265c84018e902ba4cb9086b17dce73997210d43f43e8732e420087d87d0e65c840187ae9a1ccb9081e9ba0b439972100536c168732e4200c3d7450e65c84350fd0e21ccb908021f61c43997210d43f43e8332e420087d87d0665c84014bd07384cb908029760e70997210053ac0ce132e421a87e87d0265c84010fb0fa04cb9086a1fa1c40997210043ec388132e4200a5e8310265c84014bb06204cb9081e9ba08409972100536c108132e425fa768110265c84014eb02204cb9097e9da0430997210053ac086132e4202c3e74d5165c840187ae9aa2cb9081e1fa1e54597210061fba4a8b2e420787c8755165c840187ee8aa2cb90aae1fa1c545972103c3f43ca6b2e4200c5f7394d65c840147d0829acb908028f61053597215543ec3ce8b2e4200c3f749d165c84014bd073a2cb908029760e745972103d37414e8b2e4200a6d829d165c84014ef02ba2cb9097a9d20574597210061fc22e8b2e4200c77815d165c84018e902ba2cb90aae1fa1c74597210062fb9ce6b2e4200a3e841cd65c840147b0839acb908021fa1f43597210043ec3e86b2e4200c3d74d0d65c840f4dd05a1acb908029b60b43597210061eba286b2e420087e8710d65c84010fb0e21acb9080297e0d71597210052e41ae2b2e420087e87d0565c84010fb0fa0acb9080297a0e70597210052ec1ce0b2e4200a75819c165c84010fd0fa02cb908021f61f40597210043f43880b2e420087d8710165c84014bd06202cb908029760c405972103d3741080b2e4200a6d8210165c84bd4ed02202cb908029d60440597212f53b40860b2e4200a75810c165c840187eeb3aac990aaa8f61e75593210055bc0aeab26427fab4815d564c840187f0ebaac990aab0fdc975593215561eb92eab264200e37815d564c8401c6902baac990aae8fa1475593210051f42ee6b264200a3d85dcd64c840187aebb9ac990
  | 14 => 0x88750160144354f10aa02c02880ebc20540580510d61faa2e932c6203a7481552658c4071e902ba2cb1880e1f21d54596310061fba2a8b2c6203a7481551658c4071d90ea12c5188038b5514258a3103c3e42aeda94620787d85dd9528c40187ee8aa2c11880b0f1d1545823101c7c43a80b0462018f581dd3654c40187ae92a6ca988029760e54d95310143fc3aa9b2a6200c3d74553654c40187ae9b26ca988029ba0a64d953100536c14c9b2a6200c3d74193654c5034b90ca1eca9880347dd143d95310070e32287b2a6281a7681dd3654c4614eb03ba6ca988030fd0f74d95310061ea1ee9b2a6200c7681dd3654c4018eb03ba6ca988021f61e74d95310061fc22e9b2a6200c3d741d3654c4614bd063a6ca98a069760c74d953140d2ec1ee5b2a6200a3e849cb654c40147b09396ca988c29d60472d95310043f43e85b2a620087d87d0b654c40187ee9a16ca988c297a0f42d95310052ec1e85b2a6200c3f7450b654c4010fd0e216ca988021f61c42d95311843f43e83b2a620087d87d07654c5034bb06386ca988c29d60470d95310043f43e81b2a620087d87d03654c4010fd0e206ca988021f61c40d95311852f41881b2a6200a5d83103654c4014dd04206ca988029b60840d953140d3b40881b2a6200a7581103654c43587ea8ba4ca988021fe1574595310047bc0ae8b2a620087e87d51654c4050f90eaa2ca988030fdd154595310043fc3aca32a621a87c855d0654c43587ea8ba0ca988021f61e54195310053bc0aa832a620087e86dd0654c4010ff0fb20ca988030f5d364195310043ec3cc832a6200a6e82990654c4014db05320ca988021fe1d64195315853bc0ac832a620087d87190654c40187ae8320ca98a029721943195310068eba28632a6200c5f30dd0654c4010fb0f3a0ca9886b0fdd274195315853bc0ae832a6280a74815d0654c4350ff08ba0ca9886b0fe1174195310061fa1ae832a6200c3d435d0654c4018ef02ba0ca988031d20574195310061f20ae832a6200c3c415d0654c4018be60ba0ca9880297e0d72195310d43f43e8432a620087d87d08654c40187ae9a10ca988ae97a0f42195310052ec1e8432a6280a7681908654c4014eb03210ca988030f5d142195310d43f4388432a620087d87108654c4350fd0fa08ca988021f61f41195310052ec1ce032a624da75819c0654c4350fd0fa00ca988021f61f40195310061eba68032a622ba5e83900654c4014bb07200ca98a029da0640195310053ac0c8032a6200c3d74500654c4350fd0e200ca988021f61c401953115d2f4188032a6200a5d83100654c4014dd04200ca988029b60840195314053b4088032a6200a7581100654c4051df0ea16c4988038b55142d89310061f3a6cb3126200c3e74196624c40187ecaba4c4988030f195749893103
  | 15 => 0x438ac8290daab60871590520055d400e2b20a400ab9801c564148015750018ac829002ae60031590520d51f42ee0b20a436a3d85dc1641483547d0a382c8290da8f61470590520054f418e0b20a400a9d831c1641480f55d04382c8290daab60870590520055b408e0b20a400ab5811c1641480156d02182c829002ad60430590520161f3a2a8b18a400c3d74551631480199eedb9aa42900333dd873548520d61faa2e932c641ac3f74552658c8014e902aa4cb190023de05745963201c7a40ae8b2c64008fb805d1658c8091f100ba2cb1901e1f21d54596320061fba2a8b2c6400a5f83551658c8014e902aa2cb1918e9761576d4e3246c6fc3acba9c643aa5f87597538c91b8bf0eb2ea71918e73e1972d4e3200667c32e5a9c6400d4f545cb538c801a9aa8b96a7190038755143586320070eaa286b0464038f681dd3654c8011eb03ba6ca9900a1fe1d54d95320161f3a2a9b2a6400c3d74553654c8014e902aa6ca9906b0fd5174995320d61fba2a932a64008df835d1654c8011ef02ba2ca9900e3d20574595320047dc02e8b2a64048f8805d1654c8050f90eaa2ca990030fdd154595320062faa6e6b2a6400c5d54dcd654c8010ff0eb28ca9906b0f99574195320061eb2ae832a641ac3f545d0654c83587d0aba0ca9906b0fd4d74195320061ea9ae832a641ac3f525d0654c80193c64ba0ca99003270c974195320d61e28ae832a641ac3c505d0654c80193e60ba0ca9900b0f9d154195320061eba2a832a6400a7481550654c80147b0832aa49900317d9773549320062e32ee6a926402c3e74553614c80187ae8aa6c2990023de1d61185320161f3a2a9b026400c3d74553604c8011f70eb00c09917a9d2055458b511843f43ea8b1ca230a5e83d51639440187ae8aa2c7288c297a0d5458e5101c6e43a86b1ca200a5f8550d6394401c3aa8a1ac728a0717dd56354e510061eba2a8b14a2038ec875096294401c5aa8a12c5288c21fe1d63d4a511862f39ac7a94a23095e87dcd52944c78beedb9aa52898f9398b7354a5146e2fbb0e6a94a28de4e621cd5294401aa8e239aa5288c3171cd6354a51006abb9ee2a94a200c5d7558e329440127b083aa6528a065de1d53d46512a43f43ea8b04a200c3f74d516094405878e9aa2c1289521fa1f52582512a53c402a4b04a2038f887501609440187ee8aa6c6a88030fdd154d89512fd3a40aa9b12a2008ef8758862544018dceca90a4a88023ee1d601815101c7a40ae8b18a22b87c8755163144071b90ea1ac628803875514358c5101d6a40a86b18a2038ec875096214401c5aa8a12c42880eb9205425885115caf43ee6a90a22b87c8758d52144071d90eb12642886b1b1d5624c8512643e43aa8b00a200c3f7455160144994f100aa2c0289321f21d52580512653c402a4b00a2038f
  | 16 => 0x4583520161f3a2a8b1ca400c3d7455163948014eb0ba0ac3290029d61441586520056ac1882b0ca407ae68210561948015e30020ac3290030fdd154d8d520052ec2e87b1aa400e1d54d0f63548051bf0ea1ec6a90038755143d8d520056bc0ac9b1aa400ad48159363548015b700b26c6a9002b620164d8d5231d2e432a9b1aa4a7c5e765536354801c3ec8aa6c6a90038719154d8d52005aa40aa9b1aa438a5e859d363548014bb0b3a6c6a900297a1474d8d5231d2ec28e9b1aa463ace821d3635480159b043a6c6a900387d5254d8d520056bc0aa9b1aa400ad4815536354801c3f08aa6c6a900387dd154d8d520070e3a2a9b1aa400e57815536354801ca902aa6c6a90038755054d8d5231e66392e5b1aa4008de87d0b63548011bb0fa16c6a900297a1742d8d520052ec2e85b1aa400e1d54d0b6354801c3aa8a16c6a918e9761771d8d520056d404e3b1aa400ad9809c763548014bd0ba0ec6a90029761741d8d520046f43883b1aa4008dd8710763548014bd0a20ec6a90029761441d8d5231d6741083b1aa400acd8210763548015b50020ec6a9002b660041d8d520056b40ce1b1aa400ad5819c363548019b6e1386c6a918e9761470d8d520052f42e81b1aa400a5d85d0363548011bd0e206c6a90023761c40d8d520052f42881b1aa400a5d8510363548c759d04206c6a9002b360840d8d520056b40881b1aa400ad58110363548011bb0f320c6a9002976166418d5200566c14c831aa4008df8759063548015af02b20c6a9002b52056418d520056dc02c831aa400ad88059063549514bd0a320c6a9236972195418d520070fb22a831aa400b548155063548034bd0db1ea6a9003179db63d4d5231e66396c6a9aa401c5c76dcd53548c78b8edb1aa6a918f53dcc7254d5231f27b2ec7a92a45e87d87d53615480587ce9aa6c2a90030f5d354d85522f53a40aa9b0aa400a7585d0761548014eb0a20ec2a9002b960841d855200578c0083b0aa400cdb639c261548019b0c7384c2a900336d8d70985520066c31ae130aa400cf3615c261548079e0c2b84c2a900237a1f63585520046f438c6b0aa4008f78758461548014f30ba06c0a90029e61440d815200574c1081b02a400af18110360548019aec738cc0a90033518e71981520066bb1ae3302a400cd4635c660548099e0c0b8cc0a90033c5c7609815231c6e436e6b02a4008de87d8d60548011bd0e31ac0a90023ee1d60181525551ec3ceab20a41ac3d879d5641495747b053aac82906b8b60a75590520d51f42ee6b20a436a3d85dcd641480187aebb9ac82901eaba0b73590521b556c16e6b20a41aa3e851cd641486d47b0a39ac82906b87d4e53590520d51f42ee2b20a436a3d85dc5641483547d0a38ac8290da8f61471590520054f418e2b20a400a9d831c5641480f55d0
  | 17 => 0x800001c0080008008002005000801c00200200100000080000000004000002000000000800300080000000030000000000003000001c002002003004c01600600000000060000000000000002000001c00e00000a800c02e0000000004008003000800c0060000000008000003000000400200200400140240000040000000001002000800000200000000000080018000004004001800000000000080300000000008000008009000801c0000000008000000000004800400200500180040020010010030006002000000000000400100300000020000008002004000000000e00000000180020070000004000001000801c00000000000000080030018004002001001802000200000080000000000000000004001000000c0180070060008008000003800000800700080040060040000004004004000000400200300180080000000020000000000000000c006002002801000000000080000060040020004012002001804000c0000000018000000000002400c0010000038008000000800000c000000003c000004001001c01000000180280000000000000000005000000000800400580100040090008000000007001002000800700300000000000008008002003001000000a0000028014002002001000c00000000480040080010020020000000004001000c0100008014000000000000000000000080000080020010000008002000000400800f006002c00800000000000000000000000004003002000000000000400000000060000000006000000000000e001000800800000000000000020020000000012007000802000400c0000000006002000000001a0020000000002002000000c00e000000000400600a0000000002000000002000a0000008000004002000000800c00f0058014000008003800000000200000180020020028028002005000000c00000f000001800600100180240040000000010002004002003c000003000002000000a000000c000000000001800e000001000000000000000000000000010018000001000002c0020050008000006005000000400200100380000160010030014008001000000c00200400400000020070000000002003000000000600100000000080000008010006000002800000000500000040187ee8aa2c5a980a3b21d4258b5300716aa284b16a600acf8350962d4c0187ee8aa2c3a98035594e7198353006ab29ae3306a600c3f7455160d4c0187ee8aa6c4a980a3be1d42d895300716aa285b12a6008ef875886254c014eb0ba0ec2a98029d61441d85530056ac1883b0aa600af1801076154c011ef0eb08c2a9a069de1561185530047dc3ac0302a600c3f7455163d48051b90ea1ac7a9003875514358f522fc3e43aa8b0ea400c3f7455161d48bf4e902aa2c3a90030fdd15
  | 18 => 0x21745aa87c1471f74d7a3fe336000000009a32f0dc800009512902612424c00001e6c0000000000a4800000000000003c815548e82a400000000000007980000001fd100c0bf00000000004140000000000000000085444e1c133e00000007ec2eb89fc8947781a50820dd88f31b98ba457434944223f4cfa17f3bf252c4c47ad22f9c190540e100da32cc3c0b345780000860002f2203c000000000000000030700009c000003b000172c0000000b00000ec800011321f48e20000000ad40001300b323380000000000000956000000000000000000019acce465300000000007e3391a148626000487000000000000000000007280000a28000901000000000000025e94f4f4c5c9000000041e2fc000018c0008040001cc000075300019a00001560000b741d86540eb93640000001669bd4cec67b2aa018000000000000000002e7000000000029a000086400000046b1d08e1e5383e48920c0e21d0001e9c50413d27e029411e339302026c0da91000000000000002e70000d6e0fd00000001840003bb80000000002bd051c8ea7cb000168c0004c3000189400014d3fd9674e8e000000000000000000013ec0004fe00000000003ff0001ba8000000000000000085e0001bb80000001b18b3808a33e2eda1e80de0cb000000000000000019948ae0000000000ac80000000edc00000000004a0bea0001ae878c0000001a989c41fe14b000246400000000000005460001a709780000001ba9fe000025400000001480001b40b2c00000027b10182ea316158908c0000008004002001000000000c002000000000a0030008010008003000800c000001000000800000100180300020010000000006009001000000000d0018008000004002000000401000280080000000008000002004008800400000100000340000000030000000000000001400e00000000200040040000000004000000800000000b0018000002000003002000400100080080000000020038004004003000c00000500180000020090020004000004000000400a00000980000000090020010002003002000c00600c0000004000000006000000000100000040000000008000002005003000400600c005000c0000120018004002003000000000000f00080040060020018004006003000000000000a003001c0000010050000006002003801001c00500100000020010000000004000001001c0040010000000006002000000000000100180240060000008000000003000000400200000080000020020000004002002001000c00200200300040000020008014000004000801c0020080000000000004000000000c0020028000000000000000401000000200040040030008008002000003801c00c0010030008000000001800000000600000040040050010004000009
  | 19 => 0x20045863a44d93cc55c0000c500000000521dc9d5c0008d90e98000000000000000000000045f80006200000ce80980000001ea800000074800000000000001ee800118a5b01c920751404b61a09c3066e0000000d9800031c0559a585de0004a41a74b984e71d9135c00012b0198000b8e0004641a042c40002001b7c00025f0000000fe276100008d04ba26b4a0800000000000011440000fb00006601b47d62db89a40000c400000000000002bf00010c8000476179449a000075000000000044aa31800045c0000000f6600000000005c04621a01af111e39b12607a825a00024b8000000000000000000000000000000004980002104216272456000075000027a8245126000000000000000000004e80003e10df951400000000007340005922b78000f6a36b0001e700002f800018445006aa26d2400ed00003030000000000000000064000003f000000000005b1dd4000000000037c53860032d8cc00008cc2ec800000000009c88b86780b439680686da1183c114dd25c39f3851504bba908250060c28a73130180000000000000000000000000000000042800000003e24ea0001efc0005dc00010a800064d179949020211c266000000057f0001ad00008bb2ac050091a00044e0ca800001d10496200002a946b8000000678000000000078a000066800000024506e80002bd4231c78000385148000000000000000012184193cc06140001d111e8f507e48551de20340385b60ee86f922400000006240000750000bdd1b40000000000c1094e0000a3c7946e636b0000fe477100004c800000000000002988d445d000117c0002299720c8482525381b000000040980000002041c40000a8800016005b40002c30c3224000000031a02706b08ef2b6947c6002930a112bc0000153a504144dc59b18280000000001dc0b7c0000000000000e7603236300004821da0001b3067083300000000421c54009c502680000001f0000000000002180000eb1c380000000000880dc0000000018800081400048898f8bf80000ca234872e24a08180012a20000001da80006eb000144c00000043892d08366882900b78000000000000070c89827700000007072ae8b40bd009d000000038800018900000005e12b610d00000003b6184cf1c3231e30d6886232c3f580000000003dd9c6460200006b0ef8bb05340de83407400001d3127800000030900008668b719e800000000000002a80000000000000e340003be24e000046730498c000000000000000003521d2000000000000000005da63100000012120002e01f2800000000000000007e600000010c02a4000000112215b48d00001282ee43fa08c7f800000021380006f637a00012780004440000e9a72c0000a5800000000016f40000001f200003ca00000000bc0000003db
  | 20 => 0x30000000000271952c0000003520d940002f910d0d5470276d4131d6c4c000048500000000000000d64af23a344020ec0004630d780000000003c78001088000000069caae0003711a9c00000000020282241d600002143905472079c2c6322aa0001fcc00e93b4542194e3600020600000000000000000000000064800082491b1e2000078a7130000000000000464800000007f23f80011a227a000000000000000000000000000c00594ac275407ba3fc9cc5fd17600000008f2000000000000000000002322ff10c079c0000003ac00000000000001104ca253a3448c9428292a0f08de50960004638000000000000153c29e820224800000052d106800001c00034696000003780001dac00000024c949c000000000017c88a5ae45087b4a58000000205842000041e907c0008a43f1228835a82d0000048b261f010603009c40003e38c848dc000000166400025120e11a80009490000b0800034f0ea00000000000000000da0803000000000000000000000004dc00005200003ad000000011418d06a000034433b21003600000000000000be80c500021a40008592e68510ffe86d005212901c5330a50000fa83bf26298040005eb2270000a98000000000065c3612da00009a407002c039047c000000000000000043b80004a0000000218c0008d000000009060000001ff43de36040a00004fc000000000000000000006cc5a86b608a08e84786be2a7186800000034394289ca31820d204109083710b8becc4447b3f781211f01fa0001084f262d1357054919a42914d8f2c0e20e9429800000000000000001e000042a01e42480000000000bce0000001494000000000000000034b000000103e8cf1d590784f263b2889e84a1a34c1990a800003a91c118d42e077a4750d5cf0a0001be99e40004a4380a308c14000000000000069315920b0a0c15800002f121a46d12300000000000001424926000050a2a834a80900000000008c10000bd90dc5b1000078000085c00015400000002be247c0008740dc04bcaea000217803caee000430890cd380002230b5c89a1e84711274f0e5703c0000052e1c0459a1e4eba7ab33680008ec857000000000000000013d00000000000000b2e000144073c000682000093c1640000000000000228000000125a8990000000d085820000000d3c00000015480000003990000964000000000000000027680004720001ba00000009391fd00007749040fa93a033e245000039c87e0003399c94ea00000ae8f602543d70ce0000a2000042100602bc00d0e10108df04b00000348000000000039800017b00000000005143c0800035600022f01a8f5c0c31e4100c86c32941c9b0520a00042d2488cfc7e73ef9d945325280000435226503160897000000003d8e000008511f1a3e4c1e1b1319208800
  | 21 => 0xb61f8258a268b440001059fb400022b0e580000005e01299320e8c00000018551b00001c70e7071e7622a303e08880000000000ea48e735290c81ae000000000031065917180000005a700014f91d000017080000008960f60000f1a2dc23218700001511750000438117000065c0000000001a004468673ff00000000003ef00000002d32b400000000000001dcc000000372066d036000000000010800020c00007e20003bd800000057412c911c0005314260b18b540001a20ab44de5830788ff41ba34518f06a404a336497800000059400004947821f41628000bda7d30ab80000b60003d11d711800000000000000000000000000025600003880004e147300000000001508000f72875000133c00000000000002586c53af80000000000001f109ee26801a04cc1c60760002470c1a8bd00011ac0f40000001294f346fd3100b880000002ab10348aa0000000000b3010e0fc817084a1cc48b8000f707c61a8000000071f000000000086a3380814000000202860400088b20e80000000000000eb00000004a38000e4e77d07400002d626728d112cb408a70000c9c0003d246d80000007a447e000000045900014780006db100800120c23207c84a400000036380002b800000019708a800000024b00000000001b54d884f23589bfc3d200000605cce707094559cf40000e01ee17ecc040db1fa8000c8a79f3f722980000000bc0878d9000000000000000000000f780001d8350070c0005b237008c40000000001f6450658936e99fc0002a60001344ad20ce02c9860faa8703e2874000041705c00800004d40000fc000000000000000000000000000000000000000000066e0c38000d5e69703c000000088d00020200000000001ab0f289262f11cdc4763ce19a81ac00000900000000000000002084ef2000000000127455c324068c50c1db00000000007a530a17bd2500000b080000000004588000db000026ea27400039437ca2940006fb173015912800020980010a06e900080000208810000d909505122fc0b110cc53b3d9195400034d000000000000000000009386560000000000000000000084c79d00010b89340001088000aaa2d800024f43b25020da80591727fc0299fa83f851711488dc7d635f0d092ec63436200006c00000000000000fb00000000000000000315800000000000000000320000000d080008f7068a0c80008350501ec10f059a00023a4fa462a000000095c5a92780f880003980000000bbc4ad0001d2c00000000000000004020000000e2a5af2a9977c1048fb0001d640003ee2c2862c7cc2f13508f447f20000000c50b02685000000000038400000000000000000334000000186800000053230b94f000087e00011a44ec66a44f8000d203960000000b5669a031000056c31f00016285e00001a
  | 22 => 0x107400031396e800091500012e8000000000000000007c3290000dc60003bf80002a800000000000000000000ca00007bd422800000072900000a43320020b18bc849c2330002494cc408c2ad9cf007c00015289d0000442287101c7c05302d6033124e2bf18885a082a0c6004000050e22518187c8f2c0663bb130800074308f00001903c008a80000006673149a2c00015a35c97a477648f0001a8c70613f47000001620000000178d7478610f8000d940003a60000d360002ac800100a02c21e8c2524048600000000000000000aac0008ad14592cca8654d1d980000002fd0169f40000000000190052a0000001d9c0007a33b918fc0000000000000e3a00000000000000000001470b4c4ff3f818e50564812de015c00022a0fba06124600031e0a3128c4161f7800000000000017f800021213ba0710b681a1de88c000017d0001198cd2566000000000000000000000000000000000000000000000000029d000242d09a00000013ac53c82f1998124cde18e00000000000000000c380008de03380000000000000000000000000000000000b3e1800000000049fa228000000000000000000000000004ea039000121c53e00000000000000000a312dc00062c0000b240004f83f09b8407451513280d4e560000000df832a3e5000000000011f3320458000000000220c0000000000000000000000000000000000015ec54e0000000220b880000001aec00023605e800000046c44f00000008760fb034c6145ca000000015a00000000008ba3ae0000f7c9fa5f347717e40000001c58000a3a00000000000000000001200e2400048f000022600022788d42a0439379831cbcc4600000000bc6000349000000006800001101bc0003f0000c816000000000000070500023700002160000118bdc6f14188ab01066c013c0e4cdbc00043919e800047002600009460000001c0c4362661f68000000000000000032400023f0000e808f4000000026e0000000000000000000210c00042d00000003640001bd000000000015f0990a367da46e9088abe56e1bd8000c8862800000000000000000000eaa08b30c800000000000000000001df000190d1be91400000005e80000000b20fd200018b97a8c3600000000000000000000000ad60004239f9000000003900000008fe0000000000000208824c0007db00000000000000000f407f000021204ecb160004990d50e4873a4a600000009023b7a534e0400008504e072a00000003cc00038a00f0000d9c873000000000000000000000003f30bd000100400014a175400072f00007ec00000018780002220000000718d9a41023e800007e0002d29b480004ef02586dc66807425a909c3501211448b490247cd3cb934c09e0002e0827c2ee2982b1032901638921c06780d200000006808
  | 23 => 0x59435c2630000f061ca2d42310732000000158c000000244000020c548000000000044808d80000008ae00000000000000399414944661098a21400000000000000008380000f24ee800000010f00003a1000085000000000022d024633f2a8800020800000022c836c7aa2e3000062a60e17f0a451f494239a80012803ec4310000ea200000000004f86fe31c00000005fa05780003fc2402158fd8c6600000001400006e82cb0000000108308000019e4c10d5161005c82923e19d08ac2cf020064d28a71140c8000b2284f16c943c00081100010202f80000000000b720001399c8815002316600000005f20000000d662fa0000224d920003f40000f900000001fdc00048b29c88e016e000028805c13c60b25e00008ee16738ba2e11e049400015d800000044314d4a320000000000d0600016b04680002b70000000000000000000116c00000000ac00076000000000000ac15c800000000000000000004300000000d6a86b00013c43080003ca9ef897204a10302c00ee4de1100000b427b7101800000000024480008f400000020d000018f295800014c0000000000448000000084c00058e2a10000da23080000fa89542b039a07b80007100000044f780000001338000000000000000000000000006fe3a5000148c2e857d0001ce498e000000110ce1c0003169aac7f60001e9864455e1eb2c818d800020e3fd00000006490000000000000000000024e62336b8a10f183693eb8ce865600000019c4f164523590000c3e00000000000006bf2b500e114600005d8088b84000000000000000004912480c21d536580000000003cf00000000f50da16e0f627990000000e5443739b1da49c000026f80000004bf0000aa0c2c27d3258e880000002908000000000009800014400000003b800000012ba3b4a1064e28b198076c16c1b613e400047300000001e8000000000000000000000000000000000000000000000015000059e36a18844d483c2309ed0b1a646000114000000000001f4edc86f19684f0c4c5ad037043c1ec367000000000057807e011c28620a000238c2d400040f17680000004170000b380ef3478000000000282000000047800000000001c70000000eac817000000000000000011bc48e495000096000000000012e07622da0000b1c06c5d31b780006d44090dc8408cc60000000000e3000000000010921790000fa40000000000df0e88000000174800000000000000004d628002e410200000013e80000001b88000a1663d0f98f9c7689302470954cb445a0c613a4000000354a3d927c0001d50724df404e00002388e41dc1c6000076000000000000003d600000011c84cd21d92447340240de1c002e4000000000094c0003e60000e400000000af0dca0003d4000126e0973781194ebc00000011e404e0000
  | 24 => 0x16d9ae0e9e7c10b886b80001533a700000000000000000c180000000000000000000000032c000000000000044c0000cc4808000000132cf5e1260001a180000002b91bf000065703296f8a927920a715c425c30b0a48aecc9893318614d8b487a01e1800000070841f93408d000000000000000000000565080000000127cba238d4438000db43db4139e40d841900000ad1112000294931039c00014681540000000001d0400000006a800000000037b89ec34c44048b1fd83fa1ff0481eb015c3a71368000d221e601b9ac0eb4000216140499435118d8000a4c000000030400000000000000000000001aa00000002d9800000000000004300000001a38c100820000000d586900000000c74fa243a04ca1a026a00041f00000003432c31a380005f000000005d6000373a54003e00000006ec00017e000000000071c0b49ab464c90f0af9998ba80281e7800045a2610790000c8e2441fb821c9365bf00000000000001e6800000000000010f8d8600000000000000003930e441fc6950000ebd2860043b8047481c00000000003a400000014bc9d85f649a0dd929e0000001a600003d907d06b000003c2eb1d8cb0e263297000000012232e9a640000000000000e9283042c189000000038200002400002f8840097c61d00000000007f500021ec00000006c80f400000000000000007c20001cfc0000000000000000000000000000000000016d4000435000042414e4c931b8000000000000000027c6dc00000000006d900020a00000000000000000565353000000000000000186bc55e17a8fa05d000047a800073a0000000000000000000000060c3c20838acc9526584580014a947cf0001210b3e0000001360c82000000000000000044b8000000000000028c00028126d91d0d2867746a8000f221e248380000002b8000000000058c1cf0ed4c0a0000001e240000e53f2a3840000004a2240d256000000000000000024100000000002950968fb800005a9a28dda00010003700008b5032017450a35b00002e900e20700005bcab462f29f97406dc000000000011a00000000002c80000002248c5c0002e18000000000000000000069f39988bc00004d00000010d888c4470000ae60002e28000000000400000000000042b000000073e00000000004580000b9400000000000012627ce192000000000002d000126c0000000000000000000000000000011100000003c70000e400000000c10f687e848c3a28000cea24b367800064400042f80000000000000808bfe00005f005126a78804b2528a4450c00017b044288232f800000000000019409c80302fb941cde400000000000007f9197869106c0000000000d1864a0bb1284e428eb4651500f520ed0000000ac02492c785b854481509b2490000401000000000000048c1240
  | 25 => 0xe2c0003699e111a625b24b1d98e1a0000ef000090a824377800101800000000004844ac47280006048f1454a30c5c80001bb96540008bc000000000023f13614600000000000000b7602a0001ee80006a2000159c9aa0000000000000000494973ce5c64f
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x24001e160d2b80258f06972da1889180941d168c070f8580152ca79b1a00282c2292000300178000002900090d9ea6000028990024a9839281a500111480002201210200048c8b052a0287a695801c98802b239c002a8e1d80131f8b86000ea00809ad1a800019841b80000000271f13a3208a980a0000001090038304340011008016001000432000011c000020600b09040428b006835538350962d4c018567620554d8d520058364874553635480121f9855054d8d5200607a1d54d0b63548018d181dc270d8d520160b60975dcd6414801499900c974195320060d5d081550654c80141d9419773549320050b64b43dd3654c40181f7460f42d95310050b64b435d0654c40141d9310574195310050b648415d0654c401439901057419531006075d183d08654c40182d7460b43997210060b60975dcd64c84014599018c7558d210068355182d0d639400160d929d15458e500069420081551639400181d875534258e500058924554509629400141d941d5634ca500068955182d0e6194001a155460f42986500048d650854ca619405983487e1154586500068955182d0d6194001a155460f42586500058924554509621400188c62610754c930006151cc8155165c8001a5085585314c2200060b5d182d0e65080018708020574594200068c200815d5640800182d825d773590200058364a745516308001a50802055458c200068955182d0e6108001a255460b43584200068360d821936544001a298260064d95100060bdd182d0f654400181f7460f42d9510006075d183190654400182d7460864195100060761d83190654400182d8760864195100068360d821906544001a2982600641951059d8ca5a41900654400182d7460b4319510006075d183d08654400141d939db75d91100050b64a76dd7644400182f75e0973d911000607dd7835cb644400581c875514358d10597031c95450d634400582c87551425891058f031cd545096244159c327019065d45100041d259841d5314400155193900754c5100064c611401d5314415983487190654c5105670c1c064195214410395087e15314c1101869421b854c530440091d297a15314c110024b4a5a854c5304414735295a15314c1102a4d4a58854c5304400135394215314c110004d4650854c53044001b1064215314c11051cd4a63654c530440a9a5086d95314c1102af141db654c5304409935098195314c11000784190654c53044001b1085d91314c1100247425d8348530440013509560d214c1100068355182d0d630400160d929d15458c1000487650855c9630400181d875534258c10
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x800011285332842a6298220acc8426064195314c110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4c
  | 6 => 0x4d
  | 7 => 0x3
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x124d
  | 11 => 0x124c
  | 12 => 0x138c
  | 13 => 0x138d
  | 14 => 0x8c
  | 15 => 0x8d
  | 16 => 0x98c
  | 17 => 0x98d
  | 18 => 0x128c
  | 19 => 0x128d
  | 20 => 0x150c
  | 21 => 0x150d
  | 22 => 0x9cd
  | 23 => 0x12cd
  | 24 => 0x14c
  | 25 => 0x14d
  | 26 => 0x6
  | 27 => 0x198d
  | 28 => 0xa4c
  | 29 => 0xa4d
  | 30 => 0x134c
  | 31 => 0x134d
  | 32 => 0x198c
  | 33 => 0x20c
  | 34 => 0x20d
  | 35 => 0xb0c
  | 36 => 0xb0d
  | 37 => 0x140c
  | 38 => 0x140d
  | 39 => 0x154c
  | 40 => 0x154d
  | 41 => 0xb4d
  | 42 => 0x144d
  | 43 => 0x2cc
  | 44 => 0x2cd
  | 45 => 0x19cd
  | 46 => 0xbcc
  | 47 => 0xbcd
  | 48 => 0x14cc
  | 49 => 0x14cd
  | 50 => 0x19cc
  | 51 => 0xccd
  | 52 => 0x15cd
  | 53 => 0x44c
  | 54 => 0x44d
  | 55 => 0x1a0d
  | 56 => 0xd4c
  | 57 => 0xd4d
  | 58 => 0x164c
  | 59 => 0x164d
  | 60 => 0x1a0c
  | 61 => 0xecd
  | 62 => 0x1a4d
  | 63 => 0x9c955
  | 64 => 0x949d5
  | 65 => 0x12c955
  | 66 => 0x952d5
  | 67 => 0xb0955
  | 68 => 0x94b15
  | 69 => 0x140955
  | 70 => 0x95415
  | 71 => 0xb4955
  | 72 => 0x94b55
  | 73 => 0x144955
  | 74 => 0x95455
  | 75 => 0x2c955
  | 76 => 0x2c9
  | 77 => 0x2c954
  | 78 => 0x942d5
  | 79 => 0x959d5
  | 80 => 0x19c955
  | 81 => 0x1489
  | 82 => 0x130a
  | 83 => 0x14a
  | 84 => 0x14c9
  | 85 => 0x134a
  | 86 => 0x9d255
  | 87 => 0x1249d5
  | 88 => 0xb1395
  | 89 => 0x138b15
  | 90 => 0xb5395
  | 91 => 0x138b55
  | 92 => 0x19d395
  | 93 => 0x1399d5
  | 94 => 0xd4a
  | 95 => 0x1a0a
  | 96 => 0x9c995
  | 97 => 0x12c995
  | 98 => 0x9d295
  | 99 => 0x1a4b
  | 100 => 0xb49d5
  | 101 => 0x9cb55
  | 102 => 0xcc9d5
  | 103 => 0x9ccd5
  | 104 => 0x1a49d5
  | 105 => 0x9da55
  | 106 => 0x2c155
  | 107 => 0x142d5
  | 108 => 0x14c155
  | 109 => 0x154d5
  | 110 => 0xd5995
  | 111 => 0x198a55
  | 112 => 0xa5a15
  | 113 => 0xd4a55
  | 114 => 0xa4d55
  | 115 => 0x1a0a55
  | 116 => 0x199355
  | 117 => 0x2d355
  | 118 => 0x1342d5
  | 119 => 0x14d355
  | 120 => 0x1354d5
  | 121 => 0x198d55
  | 122 => 0x1a1995
  | 123 => 0x199a15
  | 124 => 0xb4b15
  | 125 => 0x144b15
  | 126 => 0xb5415
  | 127 => 0xd0a
  | 128 => 0x5ca
  | 129 => 0x17ca
  | 130 => 0xbc2d5
  | 131 => 0xd42d5
  | 132 => 0x2cd55
  | 133 => 0x1a02d5
  | 134 => 0x2da15
  | 135 => 0x19cbd5
  | 136 => 0x19d4d5
  | 137 => 0xd54d5
  | 138 => 0x14cd55
  | 139 => 0x1a14d5
  | 140 => 0x14da15
  | 141 => 0x5cb
  | 142 => 0x1a55d5
  | 143 => 0x15da55
  | 144 => 0x1a0d55
  | 145 => 0xecd55
  | 146 => 0xd4ed5
  | 147 => 0x1a4d55
  | 148 => 0xd5a55
  | 149 => 0x1a1655
  | 150 => 0xeda15
  | 151 => 0x1a0ed5
  | 152 => 0x1a5a15
  | 153 => 0x1a1a55
  | 154 => 0x1a4ed5
  | 155 => 0x1a89
  | 156 => 0x104a
  | 157 => 0x1049
  | 158 => 0x1a8a
  | 159 => 0xb49c95d
  | 160 => 0xb4949dd
  | 161 => 0x9c94b5d
  | 162 => 0x289
  | 163 => 0x942d4
  | 164 => 0x10a
  | 165 => 0xd0c
  | 166 => 0x160c
  | 167 => 0x104c
  | 168 => 0x1a8c
  | 169 => 0xe8b
  | 170 => 0x104b
  | 171 => 0x1a8b
  | 172 => 0x282d1
  | 173 => 0x2d394
  | 174 => 0x9995
  | 175 => 0x155415
  | 176 => 0x2d854
  | 177 => 0x104d14
  | 178 => 0x104e93
  | 179 => 0x2c291
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2623
  | 6 => 6408
  | 5 => 2386
  | 4 => 92
  | 3 => 2
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
  | 7 => packedAt gbK7 (107539+((h/874+packedAt gbK7 (97051+(h % 874)*12) 12) % 3462)*13) 13
  | 6 => packedAt gbK6 (337488+((h/2136+packedAt gbK6 (307584+(h % 2136)*14) 14) % 8459)*14) 14
  | 5 => packedAt gbK5 (151109+((h/795+packedAt gbK5 (140774+(h % 795)*13) 13) % 4192)*13) 13
  | 4 => packedAt gbK4 (6650+((h/30+packedAt gbK4 (6440+(h % 30)*7) 7) % 122)*8) 8
  | 3 => packedAt gbK3 (164+((h/1+packedAt gbK3 (162+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff870783fc3fc03ff87807ff14c8e3e4cce4f
  | 1 => 0xf0ff807fc1fc3ffc07f8007802b0f1ce73738c
  | 2 => 0xff0fff8001ffc00007fffffffcc301f18383ff
  | 3 => 0xffffffe00000007ffff800f03fe01fc03f0
  | 4 => 0xffffffffffffff80000000ffc0001fffc00
  | 5 => 0xfff0000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x15810190a40540932c4824aa0048616444645
  | 1 => 0x1069802948c4193815cc05506010b0ca51538c
  | 2 => 0xaa02a48001aa80504111292544c1016083809a
  | 3 => 0x4d5975ac0010a0a66656408b02da017c0360
  | 4 => 0x88066e46313322c2c00018010fe80001aaa800
  | 5 => 0xcc800c0420220303000060060fff6dbc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36298
namespace PEqualNP.Outside.L_meta_36298
open PEqualNP.Outside.L_meta_36298.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 21 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 99 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
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
theorem bs4_2_0 : Interval s4Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 13 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 11 := block_range (n:=11) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 75 := (concat bs4_3_0 (concat bs4_3_32 bs4_3_64))
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
theorem bs4_4_608 : Interval s4Atlas 4 608 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 626 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)))) (concat (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 (concat bs4_4_416 bs4_4_448))) (concat (concat bs4_4_480 bs4_4_512) (concat bs4_4_544 (concat bs4_4_576 bs4_4_608)))))
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
theorem bs4_5_672 : Interval s4Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 699 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 (concat bs4_5_192 bs4_5_224)) (concat bs4_5_256 (concat bs4_5_288 bs4_5_320)))) (concat (concat (concat bs4_5_352 bs4_5_384) (concat bs4_5_416 (concat bs4_5_448 bs4_5_480))) (concat (concat bs4_5_512 (concat bs4_5_544 bs4_5_576)) (concat bs4_5_608 (concat bs4_5_640 bs4_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 42 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_4_0 : Interval s5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1 := bs5_4_0
theorem alls5 : ∀ k ≤ 4, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 2 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 92 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_2368 : Interval gbAtlas 5 2368 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2386 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)))))) (concat (concat (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))) (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760))))) (concat (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)))) (concat (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208))) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)))))))
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
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6408 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)))))) (concat (concat (concat (concat (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)))) (concat (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368))))) (concat (concat (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)))) (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))))))) (concat (concat (concat (concat (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))) (concat (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)))) (concat (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744))) (concat (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)) (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 bgb_6_3968))))) (concat (concat (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))) (concat (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)))) (concat (concat (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448)) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544))) (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 bgb_6_4768)))))) (concat (concat (concat (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960))) (concat (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056)) (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)))) (concat (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344))) (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568))))) (concat (concat (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat bgb_6_5696 (concat bgb_6_5728 bgb_6_5760))) (concat (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856)) (concat (concat bgb_6_5888 bgb_6_5920) (concat bgb_6_5952 bgb_6_5984)))) (concat (concat (concat bgb_6_6016 (concat bgb_6_6048 bgb_6_6080)) (concat bgb_6_6112 (concat bgb_6_6144 bgb_6_6176))) (concat (concat bgb_6_6208 (concat bgb_6_6240 bgb_6_6272)) (concat (concat bgb_6_6304 bgb_6_6336) (concat bgb_6_6368 bgb_6_6400))))))))
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
theorem bgb_7_2176 : Interval gbAtlas 7 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2240 : Interval gbAtlas 7 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2272 : Interval gbAtlas 7 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2336 : Interval gbAtlas 7 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2368 : Interval gbAtlas 7 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2432 : Interval gbAtlas 7 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2464 : Interval gbAtlas 7 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2528 : Interval gbAtlas 7 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2560 : Interval gbAtlas 7 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2592 : Interval gbAtlas 7 2592 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2623 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)))))) (concat (concat (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)))) (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 (concat bgb_7_1728 bgb_7_1760))) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 (concat bgb_7_1888 bgb_7_1920))))) (concat (concat (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 (concat bgb_7_2048 bgb_7_2080))) (concat (concat bgb_7_2112 bgb_7_2144) (concat bgb_7_2176 (concat bgb_7_2208 bgb_7_2240)))) (concat (concat (concat bgb_7_2272 bgb_7_2304) (concat bgb_7_2336 (concat bgb_7_2368 bgb_7_2400))) (concat (concat bgb_7_2432 (concat bgb_7_2464 bgb_7_2496)) (concat bgb_7_2528 (concat bgb_7_2560 bgb_7_2592)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 33, 41),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 33, 35),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0feeefee8feeef0a0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075688 * 2 ^ 32 + 4277072032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36298.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.or,[2,4]⟩,⟨.or,[4,5]⟩,⟨.and,[1,8]⟩,⟨.or,[0,6]⟩,⟨.or,[9,10]⟩,⟨.and,[3,8]⟩,⟨.or,[7,12]⟩,⟨.and,[0,9]⟩,⟨.and,[11,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4277072032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4277072032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36298

open PEqualNP.Outside.L_meta_36298 in
theorem PEqualNP.Outside.L_meta_36298 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4277072032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4277072032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
