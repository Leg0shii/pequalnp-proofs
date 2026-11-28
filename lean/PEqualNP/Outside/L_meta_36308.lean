import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36308.Model
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


end PEqualNP.Outside.L_meta_36308.Model

namespace PEqualNP.Outside.L_meta_36308
open PEqualNP.Outside.L_meta_36308.Model
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

def SBf (j : Nat) : Nat := [6, 6, 8, 8, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36308

namespace PEqualNP.Outside.L_meta_36308
open PEqualNP.Outside.L_meta_36308.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x14c38610228d00f20724b0010c04000081006ddf43be43bc43dc439c43bf42bd42df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x610a74800b30d000880a012524794e438ea90871d5110e3ca021c714d428e2a6651c544ca38a6a0c7153318e2a2631e539023ca9184715030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x308808558454cca0d621533183588540c2156115030
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (297+((h/5+packedAt s0K4 (272+(h % 5)*5) 5) % 21)*6) 6
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 17)*5) 5
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff07fffc1ff83ffff07ff07ff07fe7cf3cf
  | 2 => 0xf07fff83fffe1ffc1f07f87ff87ff83fa33cf3
  | 3 => 0xff83fffc1fffe1ffe007ff87ff87ffc1c3cf3c
  | 4 => 0x3ffffe00001fffff80007fff80001fc0fc0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x8108111084820000a5090089008902940c5145
  | 2 => 0x24112209091030940a42485248525028a12492
  | 3 => 0x4222442052210329408495049504a501428a28
  | 4 => 0x6b5b894a43b555ce73d0c447e660318df40fc0
  | 5 => 0x8c630e739c3999f39ce7e660c440c631fbf000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36308
namespace PEqualNP.Outside.L_meta_36308
open PEqualNP.Outside.L_meta_36308.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xc018000f10008024a40520000e00c04000b00734000980bf43de43bd43dd439d43bf42bd42df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe61a0044823080145a801c28600081e91002298a0208c2747552438fa92871f5150e38a0a1c754f429aa8e851d54ccaaaa39947551328ea9e832d52d063aa998d354b318eaa2631d531025aa4204d544408faa4611d540c29aa4185554430
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x4061000855875250e0d62d4543835885050e156114143
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (297+((h/5+packedAt s1K4 (272+(h % 5)*5) 5) % 27)*6) 6
  | 3 => packedAt s1K3 (602+((h/7+packedAt s1K3 (567+(h % 7)*5) 5) % 26)*6) 6
  | 2 => packedAt s1K2 (156+((h/1+packedAt s1K2 (152+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x87ffff0ffffc1ff83ffe0fffc1fffc1f9cf3cf
  | 2 => 0xf8783ff0f07fe1ffc707f0f0fe1e1fe3eb4d33
  | 3 => 0xff803fff007ffe1ff807ff00ffe01ffc738e3c
  | 4 => 0x3fffff80001ffff80000ffffe0007c0fc0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80000100000020000008011000220400001045
  | 2 => 0x1212522244a90309434290a252144943294512
  | 3 => 0x2124a4442952103298852a04a5409298528a28
  | 4 => 0x7557388aac1b555cedd18888f999c0c97c0f80
  | 5 => 0x466630ecce63999f36e7ccce311103127fe000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36308
namespace PEqualNP.Outside.L_meta_36308
open PEqualNP.Outside.L_meta_36308.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x2018e0000010023ea0c01005800b009800048846050024b8f1a009000000380000018000005130000e80000000036ad1002a451844e000005450f001064d005294702800e04180000021c1004080ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461bf428c37a851877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea1061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20dfa1641ee42c837a85907b50b20d6a1641df32c83dc6590774cb20f699641cd32c82fca3905f54720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441df32883ba65105f94620bea8c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e84907b90920dea1241ed424835a849077cc920f719241dd32483da6490734c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041df32083ba64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6588774cb10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10ef99421dd32842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa1221bd42443be6488774c910fb20a21f541443ec62887d4c510fb10a21f521443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810ef99021dd32042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc525077e84a0ef50941ef99283dd32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083bf421077a8420f7cc841ee990837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31dfa1663bd42cc7be6598f74cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718f790e31eea1c637e528c6faa518efd0a31dea1463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931dfa1263bd424c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863de430c7ba8618df94831bea9063bf420c77a8418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643bd42c87be6590f74cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21f721443bd42887da8510eb50a21ef99443ee32887ba6510fb4ca21e6994437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c534877e8490ef50921ef99243dd32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410efd0821f721043bd42087da8410eb50821ef99043ee32087ba6410fb4c821e6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40ef99681dd32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a852077cca40ee994817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940ef99281dd32502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea1081df32103ba64205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28
  | 2 => 0x400006006020038090040000300f0140040480200c0000000900200002008000000058020000180180500a0000080000200c060050060000200a03200801806026002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7c87a16f50f42de21e857e51d0afaa3a15f94342bea8685bf53d0b7ca7a16f54f42de29e85bf51d0b7ca3a16f54742de28e85bf50d0b7ca1a16f54342de286857d5490a7aa9215f94e42ef29c855e5390afaa7217754e42aea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f90d42dea1a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142dfa9a85be5350b7aa6a16f14d42dfa9285af5250b7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050afca8214f95042bf29885de5310abca6215f54c42eea98855d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ef21e65dd43ccbb887996fd0b32dea16657e51ccafaa3995f94332bea8665df54ccbbca9997755332ee2a665df42ccb3e85997790b32eea16659d42ccbb8859977d4732ef28e65dd51ccbb8a39977d4332ef28665dd50ccbb8a1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32aea9c657e528cb7e85197b90a32dea1465ed428cb5a851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265df434cbbc86997750d32ee21a65bf424cbdc84996f50932f6a1265ad424cbde6499778c932bfa8a657c514cafea0995f14132efaa265de544cbbaa8997715132efa9265cf524cbbe849967d0932ef21265ce424cbba84996750932e6a12658d424cbb8849977d4532ef28a65dd514cbb8a29977d4132ef28265dd504cbb8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32af298657e520cb7e84196f50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf29683ee52d06dca5a0df54b41f6a96836d52d077e85a0ef50b41ef99683dd32d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720efd0e41dea1c837e52906faa520efd0a41dea1483df32907ba6520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837
  | 3 => 0x3c59325d5ca8ece9b3a41a63c699c00ac528080005407a1599b8000c556ba9608c534bb109000000882c15e88f47903a032d10da2a60000d114313682a788087a0000442731236a4e80000005e610d10ed61c31c7095f4d6259958a60c22883e10f58ab843429713448443800000081170f313eca4c4006698270d98006325b8000926d47c4b022c080db4a7a7660a4a4000d46860009e88a600644000000563482784b0e0c2cca0ee0000014e000000235639365ec0000025c14ebec00000000cfc000000000000021a2389406c12f4fa01d50800000a08000000000010406a6ca8014aa9d0000b88d8000000004f0000000a8001ff00019000000000000bf800576751a880035067042a406125f8eaa5e64e774f633b5522f40000000074147a790000009c05c41ede56514c0003e93fb504cc79895821584c508b8002165ad6d00065e2c0e30a0330000000316c49a032a4400098c9613017e291180804300543f04557c710d70bc20a5dd748005e0d60f592313055c198005286b07a23e67c9f0001e011c7a560281446ad539af82f6c412cb074f0cf4a3a652c41d4e92012f0d991885a6423b1312e46e43d4753255e23c0fc0df15695c2890616890c988e941c368a5b2051ab801d91d548c71251ca4fc7848034d3b29d4850274a40a0720eb2ea39cbe00001297c7b35a516521418e36c256c2d9460bc648000002c6000ca8003624dcf68390003f40000048e2cd148c35741b47403f000ad80016f6be36cae20a536000df2100b0bdd9ca7735aac4e129046ec8d6f26e25c6c00034f0007dd0eb36000001400443647ec778004829c0e634a0a00015580014a981692e209a0004b98d0006400021e0ceca166205000000c980000002034a5130a6e5b3b524b0450ac874610bb8398a103c0c0000001c4c3c110000006080037340c41c0c000000510002390008a8fe002024002000048010000180080500c0400180201601802000000004000050120000000500c000000060080180100000600c0380e0000240000001401c0180001401c0980400001400000000014000010080000200f0040040000000e04400001002000000010000000300f02400c0380000a014010020000000000c00a010080000180140280000c0000080600600c038040060000000b000004028000040000280500003c000020060700180001a04c010000000040100a0600180083d00c0000880700401c00009014000000040080180100500601c0480000e01000008002030060000060080280400a004000030440100302300200001003010088000000040000080000c00c0600000e04c0280200200400000006004010020020040000f01a018028050000040280101600c02006000004008070020040580100c0101b80a01a0200480200e00801801036010000060
  | 4 => 0x17eb30000d50608b50fad747307b0c66ac0019900000435800000db15e288596ab4002335347695e97a0004cd120e534e07d862490008099e16c6802ecac356000000000004de78c000001464b56b1e724a9559a800064514330005ea630a199a0004590483c0c45945b14100071d3900050800000306000ba175a14000001369d6000345682d90002f9128005b05c8001dc2ccc0d718aa268ca82b8383d47c85798a19849d1a1534ce4995700a6ecd19b5ad4000454c0000000b38001ee19260d190c626476d5a23862e0000017954400000000668000000000000012a1e2000374a10004a6000000002c288044adf174a618e96445e8b48c27427ebc8120006902740000003a0001180046c5c00035c1200006b2a80007f98d08c000b9cdf80455e1b06b8000006e9b18c8234a8c0021b0000d80000026a7e45603e6c000103ab72ba0006f0590000007f04c0be000000913422c56d8e025014c4091e000000e4b6900000000000000a644d9d833677c302ec35e000cf1f34963fda99bb0001c52624515c2e0000002ac3280031b36c10c7d800000c590b0005140010f8d51b20016a888224ac041212000ae1138ce4781d8fe893184dc51f8002540002e800000b0c7e000172000002aa5a20000008b00a04d05872444720000000000001499d0001551a9aa0ee98534afe22655553800000cc80111f0000004a00b00000176800426000810496ea6182100021add17cac60008985bb0400054502000456001528000002a4b3a712e6001b701400000d7f8a86de1b8e2a56558d547ca0333ed2569a6a386a252d00c2803dda3acd0004800035e6d04f8faa9f2fa65cd2afc346000c384a2066380002c01a604242c83e82b4000000008448600051cc7c1a93c0000f4ba0001a0000a82210009099898b1f0cb8b68cf12a75c3caea37a96c3f8b25247458f2b96ae0016e0c0000000b8b7050eb1000000000439429cb39c264f8000000314fb3450000001288419693c0002d000ce000000000cb1812bf38211c0003732cbcc00169082c0437a4e00000000152684b24aa30d0a4000d30000000000000065a00000000622a457d0006449200b2dd000de13d2ef0007e90e000000d6400000432c900d9cd000069ad95e0006dc0034b630000001bc19a0000027b66e0000700059e218a4854564c29060c429c5a8ad2153488e8921a9272410f2a864d89906e0835cc6254990802e48999b7700023c889e404c001a724d000000001a0038049461cf27685cef1ef2d00003c00000000007800000919b211900
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2528423d6494a109798e528425d6394a108f990528423d6414a109798c528425d6314a10cb949428432d5250a10d3949328434d524ca10e350932843a94248210f24c9208423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58854443356115110c7d53534431c54d4d109758b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425d6214d10d5584534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109b994524432f5414910cb150524434f5314910d314c524432e6414910cb590524434e6314910d358c52443656114910da580524423e65d09108f197424431f53d0910c714f424432f52d0910cb14b424423e65509108f195424431f5350910c714d424432f5250910cb149424425e65cc91097197324431f54cc910c7153324434f52cc910d314b324425e654c91097195324431f544c910c7151324434f524c910d3149324438d424c910cd15241442d563905109d19541442b5648c510d514e3144274654c510d914a21443a54288510f14ca21442746548510da14a20443e221881109e19520443a94248110f24c920443e121481109798f540425d63d50109b98b540426d62d50108f596540423d62950108fd89540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c109758a530431e5454c10c7551530425f6254c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48108f992520423d64948109798e520425d63948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520434e6394810d358e520432e5454810cb551520434e5354810d354d520432e6454810cb591520434e6354810d358d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d525081097d97320425d65cc810c7953320431d54cc810d394b320434d52cc81097d95320425d654c810c7951320431d544c810d3949320434d524c810e3509320433554c4010d554f100436552c40109e596100436952840109dd9510043355444010d554d100436552440109ed9510043695244010
  | 1 => 0x82af6550b20cbd9542c832f5350b20e394d42c832d5350b20e354d42c830d5350b20c795332c831d54ccb20e350b32c82ad648cb20cb55232c831e544cb20c755132c838f424cb20e350932c832d544cb20d394d32c82cf654cb20d3d9532c834f544cb20e395132c834d544cb20e355132c830d544cb20cb50a51c834d3294720ab59321c82cd63c872097d8d548825c63552209798c548825d63152209d984548827561152208fd91538823c6454e208f990538823d6414e209d98453882756114e20e3509328823f64546208f191518825f63546209718d51882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d20ab59242482cd63909209b195424832f6550920cb195424832f5350920cb54d42483ab6050920ea181424838d42cc920ab59232482cd638c920e3d09324838d424c9209b195324834f654c920d3195324834f544c920d355132483cb604c920f2181324823e64145208f590514825e63145209758c514832d4214520d34c8514826e65c8520ab59321482cd63c8520ea50b20483c932c81209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c2097d89530825d6254c208f990530823d6414c209798c530826e6214c209d98453082756114c208f992520823d64948209798e520825d63948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420825d65cc820c7953320831d54cc82097d95320831e544c820c7551320834e524c820e350932083365494420cd55251083565394420d554e51083374294420cd50a51083573294420d54ca51083365454420cd55151083565354420d554d51083374254420cd50951083573254420d54c9510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020d9545200827b6548020dc545200825e63d53109758f54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c432f5250b10cb14942c434f524cb10d314932c438d424cb10b558e41c42b5648c710e950a21c43c5328871097d8d548425c63552109798c548425d63152109b988548426d62152108fd91538423c6454e108f990538423d6414e109b988538426d6214e108f99
  | 2 => 0x5350840c754d421032e525084097d97321025d65cc840d394b321034d52cc84097d95321025d654c840d3949321034d524c840e350932103565394440d554e51103665294440d954a51103374294440cd50a51103573294440d54ca51103565354440d554d51103665254440d954951103364354440cd10d51103374254440cd50951103573254440d54c9511023d6590440a798e411031d5390440cb54a41103355190440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401029c6350040c754d401032d5250040cd545401027b65500409b98854cc26d6215330c715143cc23e6494b308f59252cc32e5250b30cb54942cc34d52ccb30e350932cc23e64947308f59251cc29d64cc730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b3588438c23e6494a308f592528c32e5250a30cb549428c34e524ca30d3549328c38d424ca308fd91518c23c64546309bd89518c26c6254630a7992318c23d62d51308f992544c25f63551309b988544c26d62151308f994544c2ad6215130c758c544c32e62151308f588544c32d62151308b588544c25e6590d30c7152434c25c6550d30c7151434c23e64149308f590524c23e65d09308f197424c23e65509308f195424c31f54cc930c7153324c31f544c930c7151324c34f524c930e3509324c25e65cc530a7593314c31c54cc530b358b314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c31c63550308fd89540c23e64150309798c540c26e62150309b588540c27661150309d584540c25d65d0c30c7553430c25d6510c30c7550430c2cd6210c308f992520c23d6494830cb952520c32d5494830cb992520c32d6494830cb951520c32d5454830cb991520c32d6454830d398d520c34f4354830d310d520c23f65d08308f597420c32e52d0830cb54b420c23f65508308f595420c32e5250830cb549420c31e54cc830c7553320c34d52cc830c7951320c31d544c830d3949320c38d424c830cd952510c3355494430d994a510c3655294430cdd0a510c3354294430d5cca510c3553294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430cdd09510c3354254430d5cc9510c355325443097596310c29e648c430c7552310c34d528c430d5546310c31d540c430d3548310c355510c430c7553300c34d52cc030d5547300c25f654c030a7191300c31d544c030d3549300c355514c0309ed95300c25e63d53209758f54c832e62953209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20d398a53c831e5454f20c755153c823e6414f208f59053c831e53d0b20c754f42c82cd6390b20d354e42c831e5350b20c754d42c832e5450b20d354d42c
  | 3 => 0xa21d355132887c7614ca21f118532886ad64c8621b358f218863f64542218f191508865f63542219718d508872d4254221d34c9508865e63d51219758f544865e63951219758e544866d62951218f993534863d64d4d218f992534863d6494d219b58a534878d424c9218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540872e62950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c218f992520863d64948219798e520865d63948218f597420871e53d0821c754f420866d6590821ab59242086cd6390821d354e42086e561908218fd95420871e5350821c754d420872e5450821d354d42086af6550821cbd95420872f5350821e394d420872d5350821e354d420870d535082197597320871e54cc821c7553320878d42cc8219b59632086ad648c821cb55232086cd638c821b9586320865f654c821c7951320871d544c821e3d09320878d424c821cb551320874e534c821b3d95320874f654c821d3d51320878e544c821d3551320878d544c821c3551320872d4294421d34ca51086ad64c8421b358f21087a54288421f14ca210866f65484219dd9521087a74248421f1cc9210873a5494021ce552500875a5394021d654e50087a94294021f24ca500873b4294021ce50a500875b3294021d64ca500872d4254021d34c9500873a5454021ce551500875a5354021d654d50087a94254021f24c9500873b4254021da90950087394254021da50950087294254021d6cc9500876a3254021d64c950087693254021d24c9500876b2154021dc88550087692154021dc485500865e6394b409758e52d032d52d0b40d394932d034d524cb40e350932d025e63947409758e51d029d63d0740ab58b41d02ad6210e409798e529025d6394a40cb949429032d5250a40d3949329034d524ca40e3509329025f63546409718d519026f62546409b189519029e63906409758b535026e6214d409b58853502cd6214d40d3988535025d6214d40d3588535024d6214d408f997435031c53d0d40c714d435025e63149409758c525031f53d0940c714f425031f5350940c714d425032f525094097997325025c65cc94097995325025c654c940e3509325023e65d0540a758f415031c53d0540ab58b415031c5350540c714e405025d6294c4097d89531023d6590c40c754e431031d5310c40ab588431025e63948409758e521034e5394840d354e521034e6394840d358e521034e5354840d354d521032e6454840d398d521034d6354840cb90d521032c4354840c794f421031d53d0840cb54b421031e
  | 4 => 0xb94942d065f65ccb419759732d074e52ccb41d354b32d065f654cb419759532d074e524cb41d354932d078d424cb419b98a539066d6294e41b358a539074e6294e419758a539074d6294e419358a539065f6254e41c794f439071e5350e419798e529065d6394a41c794f429071d53d0a41c794d429071d5350a41cb549429065f65cca4197597329065f654ca4197595329078d424ca41a758f419071e53d0641ab58b419063e6510d41ab588435065e63149419758c525072f5250941cb14942506b46150941d3d49325074c524c941e3509325069e63905419798c505065d63141419b988505066d62141418fd95431065e63948419758e521072d52d0841ad587421074e524c841d3549321078d424c841a758f41106ad62d04418fd954110677655044197d8d501065c63540419b98b54cc66d62d53318f58a54cc71c63553318fd8954cc66e62153319b58854cc71d54d0f31c755043cc6cd6210f318f99252cc63d6494b31cb95252cc72d5494b31cb99252cc72d6494b31cb95152cc72d5454b31cb99152cc72d6454b31d398d52cc74f4354b31d310d52cc63f65d0b318f59742cc72e52d0b31cb54b42cc63f6550b318f59542cc72e5250b31cb54942cc71e54ccb31c755332cc74d52ccb31c795132cc71d544cb31d394932cc78d424cb319b98a548c66d6295231ab58a548c71d6395231cb98a548c63d6295231cb58a548c62d62952318fd89548c71e5490e31c7951438c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c71e54cca31c7553328c71e544ca31c7551328c74d524ca31e3509328c69d64cc631c7953318c6cd62cc6319758e544c66e62951319b58a544c65e65d0d3197994434c71d5410d31b3588434c63e64149318f590524c72f5250931cb149424c74f524c931d3149324c78d424c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c3197d95430c71c5450c318f992520c63d6494831cb949420c72d5250831d354b320c6d561cc831e3509320c63e64944318f592510c69d64cc431b358b310c65f654c4319dd95310c63f64540318f191500c65e63d53219758f54c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e53d0b21c754f42c871e5350b21c754d42c871e54ccb21c755332c871e544cb21c755132c878d424cb219798f548865d63d52219798e548865d63952218f993538863d64d4e218f992538863d6494e21b358e428872f6550a21cb195428872f5350a21cb54d42887a76150a21e9185428878d42cca21ab592328878f424ca21e3509328874f654ca21d3195328874f544c
  | 5 => 0x50d0b4e6294e42c794f4290b1d53d0a42ab98a4350b1c5350d42ab9884350a9e6390942a758e4250a5e63d45429758f5150a5e63141429758c5050a7661141429d5845050aad6294d42ad9865350ab56194d42abd895350b1d5314d42ab58f5250aae61d4942ab5835250a9e63d4542a758f5150a9e6394542a758e5150b355114542a7d8d5050a9c6354142add855050ab46154142a798c5050a9d6314142ad9845050ab56114142c794f4210b1d53d0842d354e4210a3f6550842c794d4210b1d53508429bd954210b2e5450842d354d4210a7661d53329d58754ccb1c5450f32c755043cca3e64947328f59251cca3f64543328f19150ccacd62d5332b598754ccad561d5332c755054ccacd6215332e3d8942cca9e64d4732a759351cca9e6494732a759251ccb555114732a7d9150cca9c6454332a799050cca9d6414332b598450ccad56114332cb98a548cb2e5450a32abd95428cb2f6550a32c7953328cb1d54cca32cb50a518cb2d42542329d986544ca75619513297997434cace62d0d3297195434cb1c5450d32c7550434cace6210d32ab592424cace63909329b195424cb8f4350932e390d424cb8d4350932e310d424cb2f6550932cb195424cb8f6350932e318d424ca9e648c932a7592324cb8d428c9328f993514ca3d64d4532cb508514cb2d42d41328f990504ca3d64141329d984504ca756114132b358a544cad66195132b5586544cacf6255132c7550544cacd64d4932b3987524cacd60d4932e3d4b424ca5e6590932a7592424cace6590932d3996424cacd6490932a3592424cace6190932b3582424cb8f6250932e3d49424cace6550932b3195424cb8f6450932e3d51424cb8c5450932b3185424cacf6050932e3d95424cb8e6550932e3595424cb8c6550932e3d85424cb8e6150932e3585424cb8c6150932e3d81424cb8e6050932e3581424cb8c605093297994424ca9e6410932b3988424cb8d4210932a7993514ca9d64d4532e350b514ca9e6494532a7592514cb8d4294532e3509514cb8d4214532d5544514cb8d42d4132e350a504ca9f6454132a7191504cb8d4254132b5d85504cad46154132a7990504ca9d6414132e3508504cad66114132b5584504ca5e63d50328f596540ca3e64150329798c540ca6e62150328f992520ca3d64948328f597420cb1e53d08328fd95420cb1e5350832cb949420cb1e54cc832c7553320cb2d548c83297d95320cb1e544c832c7551320cb8d424c8329bd95320cb2d544c832d394d320ca5d6294f4197d8953d071d5390f41c754c43d06ad6210f419798e52d065d6394b41d394e52d074d5394b41d398e52d074d6394b41d394d52d074d5354b41cb99152d074e6354b41d358d52d072e4354b41cb10d52d071e53d0b41c754f42d072d52d0b41c794d42d071d5350b41c
  | 6 => 0x8b80009a80002a600000076e5a4a6c14a00064c86e1a458c0003ee0003d49f000094e20a67c0000002940001a800000066491e00000000000063200048c6d00000009c67025c40e60009a04aa50489c3a600000000004200073046479010a82a80a7360000da5162f476485272038a6203644b65ec8e8766646a683a827075445000000000000000100000200000100000200100600000500d00d00700100000000000001400100000600600000000000c00100200000000300200600000600300000800300000300500500400100a00100500000000000100200800d00000500100000500600000000100000000000800000200000000300000200100400100600000100600000100400000000000301000600000000000100100500000100100200000e00700100100200100300000000400200000700200100200100000e00300200300200000200000100900300000401900100100400400300300000100200501300000600700600002900000100300200800200600000200200100100300100800000000900300000300000900000000000000a00600900300e00100000100000d00700100200700000300500000300100500200000100000b00000000200600000000100200100000200100200900400000000100500000100300700200300200000100600300100700400400000900700100300000000600100000000c00200000800000000100700300600000100f00100400000000a00800000000000000300000800000c00200200200000100000900400000000000000000000000000000000000400500200000700500200200300a00000f00900600000000000800600100500000700400800000000000700000900900100000000100000200200300000200200200000000100600200000300000200000300300500b00100200200500700000100400200000000200300000700300400500600200000100100100700100100200400300000500600500100000000300200500500e00c00000b00100000000301000600a00000100100000b00200000000400100100400600c0010090040010040000020000030050000000000010020000050000140060009b98b5150e6d62d45439b9885050e6d62141439d9845050e756114143a75924310e3f6550c4397d954310e9f6550c43c7d954310e9f6250c43a7d854310e9c6050c43e350e5210f1d4354843e350d5210f2e6454843d398d5210f2f4354843d390d5210f2d4354843d350d5210f0d4354843c750e5110f1d4354043c754c43d0a5e63947429758e51d0a5f63543429718d50d0aad62d4f42ad98753d0ab561d4f42c754c53d0aad6214f42a798f51d0a9d63d4742a798e51d0a9d6394742cd54451d0a9f6354342a718d50d0a9e6314342a758c50d0ab66114342ad584
  | 7 => 0xb89680005400ac7b68e676a000246000154a4a00000076c6424b437e0009e09942fa3325e800072a9d85280ce35e8302443a08c80007a259e00a6c44dc0006c60005126600000000000007b84ee0006126b21ea32e9641e22da7c06f20000000000000005dc00047682400036a0000385385a693859a5622d007a81828e0e20008640aa42600086000000001840c3961d83ca0007680000000000000000000001ae89e0006988ae80c2328ee03c000000000842a4089834e1420dc3c82fe8ec8389428367d40001c80680000003e0000444000832a286ac6ee9c8a381f20000001b84346fa27634c06097039c1325640000000000000000000008dc5d23de45a56640a0000004fe55a0009f23dc5584f8a6e00018c000000a320000007fc0000000002c09ac23e63a50e00022249a35a46e7966d447a2826568a60100000000007846e28fe3920560c8a062780000000000000002926105ca00084c0000000000000fc00029c8ea4bc0000000007fe3fe7c69ae9e84562b42d44869340000000000009dc84016637600000000088200000000008242400000000061657413047001a57266808e4d40f633e1e613c3b454248a7462280005b000003e0002546d27a607ca4698a6d616800043c00093aa0a38817ea2469a14694000087a6de000000a2005e2a80027181c096c13402a5dea361aa00047c00086a07000000005278e7040000000000200003c24609724f67e875a43a10606a00000000000018271217c2a00008969ce00067899e9a40005e20000002b875600047e6be69e9b46b48de15a0000003ce67488488a0d88b08c28080000007140000000006b6000000330000000000000000000000000000000242432000810886062178000a7600000090240400000000000000000098e00051e2f000019a7ba580000490990000a1679277a0a04981d60000000000009f80008666080849ca090000000306000a122980000008720000000004543ea00052a7bc9044ca00000000000067612e00035c208000000a001b01029fa3e419c37a8460d28d453683a13e8ba2bc06e3980bc71c0007c81fc000000174000a0468a6a27600000004c47e04380002d243021e3784d67446268164e62ce4f022a28c5e08028ac0ba6388508584ba61e4ec9542ac79400055600031a0009980007b41de0c281a7d084439e6000000000005b2004000202948140000000a2a1a60000000004200000000002802389fe66c0000000003c40000720000003280000000000000000000009e400081e0000000005f85143349ba70e0002f600010400000000062e000000000284a5430e5f492800000000000000033600000065200043e5be0007da8fa00c000a642fc9c40000007ec0000009f40fa000322000a021200004fa0000008f40000000000a60f400058600
  | 8 => 0x4475271045c6aa3846e44281882a41e40ca8b63569149220c41c24400086ea00050200004a7d68b489000080e000000a0c00034200000000000003a53c3f253219e06c58400000086c8f600000009416a21a0003d60008040503da0000000008a00000009629de7d800000000077e6040001d20000000000000000005240000ae0f2000000a101ac00000000000000060a00000000000031c2149d26180d400000012a7000a27a02e000000096a5ee0000000002cc8d20001986887f07be000000a6031842a00000040800010e82656055281c4ea472288a4e64ea084889b0a3a0ea00058a43679c71683e0f84d244c0000006b84e096e22642c70a0004d80009b81ee9e21b273e00000022c3d099a7f40007fa3ae75c72e1840001228143688aa00064800055e0006ce00067a05827296601e00032a3008000000000000000000805fe38e6a05883040005203c009a6ca3be0004946921266dc0004c011832c35800027c1be748a260e06e81703c66283147625781f89800005c000007800014825241a0005f215ca5e11009e21c9ea94692e0003860005e40005083cc87661a0000005760000003264ac00000000044a33a1560000000000002640009bc0009867ca00059400056a5820000006700000000008d800006600000031200000012400077602e00060608c03600072c00000059225c8740fe93018a0761f60280000000005aca426360000000000004587d20000003020000009cc952418640a3e74092435200000000000095090e75893200095a00000000078200000019000000013a5ea8d00004141763820005960008bc7880008c69fc00000000036c1c494c48400087800000023446c0004e20000000000008a42e200000000017a00000060c2101bc6c85b60006f09880002163b00981cc00075e99282e57e16e95c0000001720009a60000005f05ae8060000003ec4c85bc00e41200000030a26223657c0009260eea660000009841fe000000a748f20547ea7c223c1807506860cc0000004b80000000000006fe55c4c20000000340000000002eaa4400000000000000065e0001ec04c48e4d000011600000000000050a000000000000000256a3c00056e1e00007385c253400004e31e7aa8f83e20009d600000000077c0006240e897e9124ae000000346a1e00000091a1e80009da70c10c00063e00000000044e8caa3022ea1a0b20006a80000004f487c00000081200044600000046a0003804da1ba2185d03d8a1868c0008204020f058ea228da2be13869491c2746f80000000006340006e07080007720005a22a20001a25f60002960003fa7cc0009d456800000025086205a97860e0009f61865aa00000045e84867200039a0000001622600000000007e46c05d60002208c400000092c000000000a2e000194654258224
  | 9 => 0xbe16045240e00029014e0009767de000000a7278c11e08a4f220494a7a80007f60005fa2ca0002e44803f60480ec15800097c0000002c80000007800000c000000000000015200000037400000000057a1dc5b88349e63aca2ca705fc1b47868a282269c04423a7e20000000006d80003b200029e0009100000000003a20000000000000004ce0000000b000000000000000012c1280000000003729968d63f43bc6ba6e60000001d00002ae0000008922f8000a560008f002400000000031091624c0000002b64620003b615004000000079a74e54623020e2ba66600098c000522526248000100000000000906000000000a5051095e00000000069000097a4be0000009582d687e0000000000006da28a02264a0000008b29ec0000004e40000004740006440000000006f40008686a600000000000000000085401c500a4c79800000011c5c600000020014c00000000000066200035449226a33808601200073200000005ca5c544a1c41e25a8cc4a60001a04665b427a46865066a89462c00074a65c2060000d60001965507ae5d85ba93c26809c11200000000000000000000000000000000000000082800042e00000000041c0000000001da0003160001920006c274c8800000000266ec63050c84e52c49c25e06434a9be1367b0614a589208be3620145480006026b07ac0000000003aa00068e51c2dc4a80000006bc0000003204a00000000002e82ee9564de1b653e00016c0000009c00009aa2e60000006220463900007420000002860004b00306800000008e018e6f60000000000000000000000000000008e4a5a0de00000000026e1d46840000d09a200065a0007260000007c437c7a49746581ca73a51a0003707780009c29ee63c54a5a06a40000008880005c80000000000960b4a0e0003d22405901147700004cc83c0003e873c000554a6a5061c654e0006cc8ce1f00882c42de02c0000009d00009820005ce2c614420c7dc5d493e9b668200038c6960000e415e4003e60164c68fc61c000000a3499c0740000003a47f20002c229a00000000000085a00026c5cc52e56c4101fa3f824a448000a480b60c67ce09284a0000000009186fc54c87090a0008560002d80003943500000003f00001ce78a27e49e30c2f20a85da2b22b07e688c36673400003200077471e212000000000478a624e810800000000000000000000000053a7ee92a00066e53000088e0000008a800000089a79e0004a200051882c9009080007223ba2aa33c85e00670634011a496348a524060000009600001643240002ec4220002668e2598a140000000000000000003b89445e685c4160a459c0007b23fc00000062a7f83084fc4a43600000008c036e90c7280004820006ae67e57000007e00000071a9365a80009b24b21f444224e3
  | 10 => 0x72400
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x98e0d6358a548c70739ac52a463835cd6295231a1ae52a48718d0d72951438c686b94a999463435ca544ca31a1aeaa126518c1d76953318c686b94a998c638395162cc631c1aa8b108698d0d74149324c742a10c299263235ca648c531a1ae42a28618d1970151430c616b90c8a8063435cf6550a21a1ae9b2a6510e0f635095088707b2264a8443135ca63d512185ae5326a690d2970d4d4208686baca6a10438359542cc821a1aeba126410d4970d513208686baca899043c254d4294021e12a8994a010f09424ca5008695baa84a8043c294d4254021e12a6a12a010d4b754c950087852a264a8043c25513254021a92e7212a010d61719095008784a1664a80434a5d23254021ac2e3192a010f0b424c95008784a1264a80434a5d32154021a92e790aa010f214288550087a099442a8043c8d092154021e866490aa010c4d7298e51d0286b9ca4a1481235ca6390640c1ce8b10a6a060d745885350286b90a7a1a81435c85350d40a1ae429e84a050d7214d425030732a8499281435c853d0540c18a6b1682a050d7214d4150286b90a7202818354d6210c40a1ae529a842050d739494210307b2a8499081c15093294440a4ae421aa220705424c95110246b94c7208818398d5290440c2cc6a8c822048d7218d401030631aa4a00818518d5150040a1ae42a2879842d7299251cc307aa2c421c61435d2524ca3091ae5324631860d63588544c30739ac42a261835cd6215130a1ae42a4869850d72151434c286b90a999261435c8544c930a1ceaa12649841d76153314c286b90a998a618315162cc530a1ae42a2629850d72152304c286b90c6aa061835516210c30a1ae52a2641850d74949320c287baa8499061c15093294430a8ae421aa218705424c9510c246b94c91886107dd9548c430c1cc8a94621861664546310c246b90c898061071d9544c030c18c8a92601861464545300c286b98caa12410b1d95350920a48e2a9a84905a1711814248286ba0ca99241131d9544c920a88e2aa264905c1711813248306b1a8428a41835913214520a1ae7292841050d725513208286ba4a49904143dd5424c820c1ecaa126410705424ca5108382a1264a88418a5516008420c92a6b00421044d7298f54c4216b94c9a9e21435cc5250b10a1ae8292658844d7218d5484216b90c8a9c21435ce5250a10a1ae9292650860f64d8f5244306b22c6292218a5916014910c92c6b00a488661615805244286b90a6a1221435cc5250910a1ae42a2648850d7414932442873aa8499221431d5424c910c1ccaa12648860c6550932442923aa8510a21511d53288510c50caa124088648654c92044306b22c729021835916354810a1ae529a840850d739494204286b94a899021435d2524c810a1eeaa12640850d755093204307b2a849902183595424c810
  | 1 => 0xb2cd4925158dc450580005651c89a00659ac7c300430c8660228ed1a381b2cdbe1f46274e2190a06c002300000000052af5b400000000000001e4003f3d97cf8d9099e0685e0012c002e00afd3004270c81aae35088b68130aa800244b801a41c000a560a32b0007a7e59001407f60b59b01a1600150a65b97400b9620550c512c15c843331925c42f3bb80c40029001a200000003c00002f874d75592800406437800124280054ce0000000000035000005c0002e0027954ce00000e4202b0613090d50027da6bb2d0008e00000000000412598ea9001116c701300082000000000000026c00c0708013480320014eb56497122003e87412ad6814c00b14f0d52637002f17418419bc1caf37238a89505801980039a404200002d14850610f0506d051d822654e285b6004ca1cd00044b7406cf2309dc68b101d108a2079b11e66441e85a00189d40e25033158c02001a400000080e000000402010181800060980010010d004140e0000002060002c30000203800000880c000600064040000014000300814280400010022101808020003008020e120000e0c03034120b02804080300000001b91ae5b0a8621c8d721814310e4ab88c0a188743dc94354843a1eeaa1aa421d25719915210ea2b8cc6a908743dd94354843a1ee2a1aa421d0c7050d5210e8bb8a87288878354d6214f4291ae730ea4a148f735835250b06aa2c42a665831954350932a4ce3b2a849948d74987524ca47ba2c1a9265319c66550932b0ce3b2a849958571d95424cac338ccaa1265615c66550932c1aca32a849950e75d85424cb42b08c2a126561dc56050932b08e2b02849950e75181424cac3388c0a1265615c4605093291eeca16a29970542544514cb42a16c2a8265a1508615413291eeca10a09968542984504cb42a12c2282658354d6210f41a1ae529a85a0d0d7394942d0707b2a8499683839d16294e41c1ae8b14a720d0d7294f4390686b94a6a1c83435ca53d0a41a1ae529a8520e0d655093290686b94a7a0c838394d62d0641a1ae629284a0d84715093250646b94c720a83135c86354041a1ae431aa998e0d5458843cc686b94a899663435d2524cb31a1eeaa1265
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x6808a40c07000cc00029594442c0090581dd94354843905811c14354843a05819d16294e41a05819cd629523180d8795162cc631a05819d16214d40a058298d5190440a058218d5150040a05819cd621513080d8715162cc53080d87991528c430a0582991518c43080d87191524c030a0582191514c030
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
  | 2 => 14
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | 2 => packedAt s2K2 (i*60) 60
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (802+((h/14+packedAt s2K6 (704+(h % 14)*7) 7) % 75)*7) 7
  | 5 => packedAt s2K5 (27286+((h/296+packedAt s2K5 (24030+(h % 296)*11) 11) % 1175)*11) 11
  | 4 => packedAt s2K4 (56272+((h/446+packedAt s2K4 (50920+(h % 446)*12) 12) % 2139)*12) 12
  | 3 => packedAt s2K3 (11856+((h/76+packedAt s2K3 (11172+(h % 76)*9) 9) % 301)*9) 9
  | 2 => packedAt s2K2 (860+((h/4+packedAt s2K2 (840+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfe1ffff0ffff87f83f0fc3ffe1fff83f44f3cf
  | 1 => 0x3fe1e1ff0f0ff87fc7f0fc387e1c3fc7bb4d33
  | 3 => 0x3ffe01fff00fff8ff800ffc07fe03ff8c38e3c
  | 4 => 0xc00001fffff0000fffff00007fffc000fc0fc0
  | 5 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2000010000008000001004800240800001045
  | 1 => 0x84484222241500814310441122089286194512
  | 3 => 0x2884954442aa441a9888aa8255412530c28a28
  | 4 => 0xa1d55988aa83552cedaa220479938192ec0f80
  | 5 => 0x3119910ecccc664f36ccf32711020624f7e000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeaaee88eeeeeeaaeeaaee88eeeeeeaaeeaaee88eeeeeeaaeeaaee88eeeeeeaaeeaaee88eeeeeeaaeeaaee88eeeeeeaaeeaaee88eeeeeeaaeeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36308
namespace PEqualNP.Outside.L_meta_36308
open PEqualNP.Outside.L_meta_36308.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x15a4003c0004000980500021738140183a944030e24d9e2001080524468100580260018000240001f009ca94168d50034646024428700000010404011c70404c0003ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461bf428c37a851877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea1061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20dfa1641ee42c837a85907b50b20d6a1641df32c83dc6590774cb20f699641cd32c82fca3905f54720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441df32883ba65105f94620bea8c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e84907b90920dea1241ed424835a849077cc920f719241dd32483da6490734c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041df32083ba64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6588774cb10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10ef99421dd32842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa1221bd42443be6488774c910fb20a21f541443ec62887d4c510fb10a21f521443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810ef99021dd32042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc525077e84a0ef50941ef99283dd32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083bf421077a8420f7cc841ee990837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31dfa1663bd42cc7be6598f74cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718f790e31eea1c637e528c6faa518efd0a31dea1463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931dfa1263bd424c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863de430c7ba8618df94831bea9063bf420c77a8418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643bd42c87be6590f74cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21f721443bd42887da8510eb50a21ef99443ee32887ba6510fb4ca21e6994437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c534877e8490ef50921ef99243dd32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410efd0821f721043bd42087da8410eb50821ef99043ee32087ba6410fb4c821e6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40ef99681dd32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a852077cca40ee994817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940ef99281dd32502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea1081df32103ba64205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28
  | 2 => 0x800800000800000000000000000c00400000000000800400000000400400000000000000000000000000800400800800400000000000000800800401000000000000c00afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7c87a16f50f42de21e857e51d0afaa3a15f94342bea8685bf53d0b7ca7a16f54f42de29e85bf51d0b7ca3a16f54742de28e85bf50d0b7ca1a16f54342de286857d5490a7aa9215f94e42ef29c855e5390afaa7217754e42aea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f90d42dea1a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142dfa9a85be5350b7aa6a16f14d42dfa9285af5250b7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050afca8214f95042bf29885de5310abca6215f54c42eea98855d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ef21e65dd43ccbb887996fd0b32dea16657e51ccafaa3995f94332bea8665df54ccbbca9997755332ee2a665df42ccb3e85997790b32eea16659d42ccbb8859977d4732ef28e65dd51ccbb8a39977d4332ef28665dd50ccbb8a1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32aea9c657e528cb7e85197b90a32dea1465ed428cb5a851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265df434cbbc86997750d32ee21a65bf424cbdc84996f50932f6a1265ad424cbde6499778c932bfa8a657c514cafea0995f14132efaa265de544cbbaa8997715132efa9265cf524cbbe849967d0932ef21265ce424cbba84996750932e6a12658d424cbb8849977d4532ef28a65dd514cbb8a29977d4132ef28265dd504cbb8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32af298657e520cb7e84196f50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf29683ee52d06dca5a0df54b41f6a96836d52d077e85a0ef50b41ef99683dd32d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720efd0e41dea1c837e52906faa520efd0a41dea1483df32907ba6520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837
  | 3 => 0x11480000000000000322ad00033f4ee19c0000062c0000000000000000000000000002dc00076162800000024d0b4100000055800000000000e80000000000000000000000000000001de000001540000000000000000000000000000000e3b470000000020e02c000000000000000011400000000345000000000000000000000043e000000000000000000000000000197000000b3af31d277d06b7600000000000000000001a600000000253000000000562fa0f56ca1e00000000000000d6999000000000ca00005800000000000d54000000000000000000000000062000001248000000009b8000003c8448005d49400007212a0000000000000000177000000000004f0a2d048000000006e8004ce984b2000000000002961b22f8000000e2001aa2024ecc6175941000000000000000000000000080c000002aa520000000d2295a198c00058c43000000000001bc000cc46d800000000000002840000000000074800000000358000000000000000051e00000000000001948005462000016b000000000000006ec000000000002c80000073c580002d2000001f00000000000000000000012000511818000000017e00017e53cf000019e00000000000144000000000000000061c3bc000000000000000051a3acf9000000b98e20a16dc0000000000056c0000054e0000000000000000000000001118000000000030a1dc0014a92a65a0000011f0000000000000000035a43000000d78000000005134b00000000000000de00000000000000130560bc476000000000002e3344000000000000000000000000000000000000000003d06c4002550000006580056a0000000000000000000000000fd8005620000019f0f0000000000002600000000041000000000400000000000000000000000000000000000000000800000000000000800800000000400800000000000000000000400000000400800800000000000800000000800800800000800000000c00000c01000000000001000c00001000000000000400000000000000000400400400000000000000000400400000000000000000000000000000c00000000000000000000000400000400000000000000000000400000000000400800000000000400000000c01400800800400000000000000000400800000400000400000000000000400000000400400000000800000000000000000000000800000000000400000800000000000400000800800000000000000400400000000400400000000000000000000400400400c00000400000000000400400000000400000000000400000000000000400000000000000000400800400000000800400000c00000400000000800000800000000800400000400c00400800000400400000000000c0000000000100040100
  | 4 => 0x80000000000000000850e50000000000000000000000000000238000000000000000000000000000000c040024030c00021800000a68d58000004a1500000000008722b000dc4968003389e45700000012c000000000014200000000000000000000000005b60b800242000000001232a0a70000000000000000000000000212000000001f91a20000000000000000000332000000000000000017905a000001530000013d0006000000000003486400000000000000c5116570001ac0005ec0033716a76802907000000000000000000017800000000000000000000000000000000069413102000218000a480000000000000000000002dd000d98000002b000000000000000000000000016001e0003f80025e00000000000000000c10000000000028000000000000000d40002cf000a90002df0000000029d5fc000000000007d1598000000000002020000000000000000001e200000000000000000199d600000000000000000000000000000014e0007b14f8000000000000041e00000000000000000000007acf08000000000036300000187a730008800000000000000000640000000002420000000000000125800000000000030000000000000000000000000c10000000000000036b2646cc0002b000000002060000000012021e000002691ee0000000000000000000000000e000000016c608b9000bf58e800000000001315da0018d9fd61200000000000d10000000007fc00000022000000000fa00000000000c2cb2800000000000000000000009d000c8c000006ba000fe0005dc000002c1000000000000000000000000000000000000001028000000000000000000000000000000dea2f0006b442b58000b9002288000000ea00000026400000000000002c400000000000000001a700048e000001a800000000000000000000d0046000000000a40000000018e00000000000598a90f55ac3880000000047800000000960000fb0000000000000000000000000001b900000000000000000000780000009896b800000000002a20000014800043630c00000000000000001fa000c00000005f00000038a00000000000b2c00000352000001d0000000000000000008aa5f2100000000036a0000000000000000000000000001560000000000000000024b3026c35cdf00000000000000348744000000000000000022e00000183000458002380003e85500029a1d905800000000000000a800000000000000000000008045a1e70000000021a000000000005740000000000000000000000a9800000000000000000004fc00217252000001b8000000000000000000008a0000008122700000000000000000000000da000000000000900000000000000000000000002da000000000000000000023b000b24d00000000000000
  | 5 => 0x61c000000002a0000000000000000000000000000000000000000000000015d000000000000000000017613e00000000000000000000000000027c5a80004f00000000000000000648c80210000015781831a000000002be0005b800000000000001201b8000000000000000048a0013d80000000000036000000000005940000014b000001a40003da000003174fe2d800000382000000000004f40000007e00000075192001ac80010e0880b80000000000000000118a50c800013800000000ae000241000001448003de000000000000000034d0008f4002f727898c1b800000000000404e884d10a9200039c000000000000000000000000000000001488004680000000032a64c00000000001b200047e00000000000000000000ee001618a90001080000000055c6a000000000000000000000010500000000000000000000000000000024d00000000000000000000e600000000000000000000000000000000000000000000000000000000000016f00000000017a6b0aa00126000000000d800012c0000000000000000000000000a300000000018000000000000001e200000000000998000002f400135000000000000f600062c0000024a0018e0000000000000000000000000000948000000000003f000000c889c00054a418000003ea000000000000018601b00000000000000000000000008580027015e0000000000000000000000980000000000000016e000000f30000000019f2c264e000000000008940e80000014c00000000000000000000015b00062a000b41ea0000000002a000000001fa0000007c1244b4000002fa0000000000000000000000000000001e3000000000002a230000000000000003331248f0000004ac5d40033900000000000000000000ea0000000000027693c00000000000000000000000000000000000000000000000000000004a2480d00014b9186744895f0000004280000069e00000041000de400000000b34000000009f8000003020000000026600000000000000002e10e8368ee8002d400000000564425b12bf2b2180a2984000000000006ac000002a90000000000000000000000000000308003aa000ff000000000000000000000019a000000cb0570000000000000000000198670000000006c25840000000000000236000000000000000000000025e000000003dcb30000005ceaf00008f39800000013000bd4000000000000000006200000230000000000000000000000001e000000000000008691a018000000000000000000000000000091000000000000000000000000072400000000000000000000018d3282de000000005fe000000000000019eaf40000007000000075c001c61020001a0000640000036a0003cc2f0000000000003a0000017db1f15a17d92
  | 6 => 0x7f8bc6420017402533600000367000281778636760016a8003e2c6400000000000000005d8000000000000000000046600000000000000000000000000000000000000000000dc000000000000002720000000000019a00053850000000000000000009f00005000000000032000000d300000000000000830d5000000000000ba07888814a990000006500024e000278840000010e800000c0982a943b600000000000000000000000000000000000000000000000000005a2000003260000011c8000000000000055800000000000614f4a930000009cb4200000000000000624000004da0000015a0000ecb9b680000017cad2000000002f6000000000000000006c00037e001568000000000006f0000000000000000052000000ddc000002e8000000002c4000000000000000028123837c000000000009601000000000000000d7c06800000000000000000000f8004fac3413271000001a88000000000002739c000001ba000000002c747c2e000228000000001cd3ee0000005a0000000000000000000000000d800000058c000672180000e40014c00000000235000001ba80000000044000000000002570000015d80000000000000000000bf8001f8cac000004dc000000000000000000000000000000000000000000001e8000ed0000000000000000000000000001082f800097000000138000000006b60000000000000000000000ab8000002567d8d915e626001a9000000000000004b200000000000000000004b67e09304d000000000000000014335c0000000019e0000000022a0006e4000000006d14d800000000ce9c8000348000000000000024e280000000000000000000000000100000000318000000001ec00000000001160000000014500000000000000000a38000000009b00000006a000000000900000036c1c600000000000c1859800000000002e2000000000000f2000000000042c846800000000000000000000007f000000000ac000b6000045000000729a75d20005e800202000000001b80000000000000000000000950000000000000000000000169a8c0ba00000000000000000644ca31023800000001089a50008c8000010000006f0000000000024600c4d40000000000000000698b40000000d4000000006800000018a000000f28006587651880053c000000000000000000000000000000000000bf0000000007200000024c7a00065e00122083000000002830000004d98f0000000000000000000000000000b00a61f2c40a38b100000000000000000000006de4e8000001180000000000000041000000000000000000000000000000000000000b20001b612e6200004a00087081b11000d7885800000000000000009d42c00060e001670000000000020a0000000022e00000000000000000
  | 7 => 0x1c000000000000000000000007c6380000000033000172000000001d35c00000000000070c00000000000000002200000000066a000000004c80000011d000001288000000011b919000000001e45540000000045a0000000063c00000000000ae4000000000000011200000088a986d2199b28c24de85400000000001038000000000000000046dba000556170050005e4001ab808000000002b7000000000000000000000035c0003296c000000002bd00000000000000a09a30bb0000380000000000000000016cd8038d50e00000025d00000142a26000a84000000009a00000000000104000000000000000e60000000000068c0000000072c000000008e800000000000ee000000000000000000000024a44800000000000000aa0005e000000000286cf00ab2e0000000000000000000000000000000002e21f000000000000002e56da00000000000000001132da7cd890006540000000000000000000000000708000000000000000000000353000000000002e000000000000000000380280004d0006100000000000000000000000000000000000000012e0000000000000028d8a000000000000000006dd9a000000001b9b240007089a2876920002206c000000000000000
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x2528423d6494a109798e528425d6394a108f990528423d6414a109798c528425d6314a10cb949428432d5250a10d3949328434d524ca10e350932843a94248210f24c9208423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58854443356115110c7d53534431c54d4d109758b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425d6214d10d5584534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109b994524432f5414910cb150524434f5314910d314c524432e6414910cb590524434e6314910d358c52443656114910da580524423e65d09108f197424431f53d0910c714f424432f52d0910cb14b424423e65509108f195424431f5350910c714d424432f5250910cb149424425e65cc91097197324431f54cc910c7153324434f52cc910d314b324425e654c91097195324431f544c910c7151324434f524c910d3149324438d424c910cd15241442d563905109d19541442b5648c510d514e3144274654c510d914a21443a54288510f14ca21442746548510da14a20443e221881109e19520443a94248110f24c920443e121481109798f540425d63d50109b98b540426d62d50108f596540423d62950108fd89540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c109758a530431e5454c10c7551530425f6254c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48108f992520423d64948109798e520425d63948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520434e6394810d358e520432e5454810cb551520434e5354810d354d520432e6454810cb591520434e6354810d358d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d525081097d97320425d65cc810c7953320431d54cc810d394b320434d52cc81097d95320425d654c810c7951320431d544c810d3949320434d524c810e3509320433554c4010d554f100436552c40109e596100436952840109dd9510043355444010d554d100436552440109ed9510043695244010
  | 1 => 0x82af6550b20cbd9542c832f5350b20e394d42c832d5350b20e354d42c830d5350b20c795332c831d54ccb20e350b32c82ad648cb20cb55232c831e544cb20c755132c838f424cb20e350932c832d544cb20d394d32c82cf654cb20d3d9532c834f544cb20e395132c834d544cb20e355132c830d544cb20cb50a51c834d3294720ab59321c82cd63c872097d8d548825c63552209798c548825d63152209d984548827561152208fd91538823c6454e208f990538823d6414e209d98453882756114e20e3509328823f64546208f191518825f63546209718d51882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d20ab59242482cd63909209b195424832f6550920cb195424832f5350920cb54d42483ab6050920ea181424838d42cc920ab59232482cd638c920e3d09324838d424c9209b195324834f654c920d3195324834f544c920d355132483cb604c920f2181324823e64145208f590514825e63145209758c514832d4214520d34c8514826e65c8520ab59321482cd63c8520ea50b20483c932c81209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c2097d89530825d6254c208f990530823d6414c209798c530826e6214c209d98453082756114c208f992520823d64948209798e520825d63948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420825d65cc820c7953320831d54cc82097d95320831e544c820c7551320834e524c820e350932083365494420cd55251083565394420d554e51083374294420cd50a51083573294420d54ca51083365454420cd55151083565354420d554d51083374254420cd50951083573254420d54c9510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020d9545200827b6548020dc545200825e63d53109758f54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c432f5250b10cb14942c434f524cb10d314932c438d424cb10b558e41c42b5648c710e950a21c43c5328871097d8d548425c63552109798c548425d63152109b988548426d62152108fd91538423c6454e108f990538423d6414e109b988538426d6214e108f99
  | 2 => 0x5350840c754d421032e525084097d97321025d65cc840d394b321034d52cc84097d95321025d654c840d3949321034d524c840e350932103565394440d554e51103665294440d954a51103374294440cd50a51103573294440d54ca51103565354440d554d51103665254440d954951103364354440cd10d51103374254440cd50951103573254440d54c9511023d6590440a798e411031d5390440cb54a41103355190440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401029c6350040c754d401032d5250040cd545401027b65500409b98854cc26d6215330c715143cc23e6494b308f59252cc32e5250b30cb54942cc34d52ccb30e350932cc23e64947308f59251cc29d64cc730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b3588438c23e6494a308f592528c32e5250a30cb549428c34e524ca30d3549328c38d424ca308fd91518c23c64546309bd89518c26c6254630a7992318c23d62d51308f992544c25f63551309b988544c26d62151308f994544c2ad6215130c758c544c32e62151308f588544c32d62151308b588544c25e6590d30c7152434c25c6550d30c7151434c23e64149308f590524c23e65d09308f197424c23e65509308f195424c31f54cc930c7153324c31f544c930c7151324c34f524c930e3509324c25e65cc530a7593314c31c54cc530b358b314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c31c63550308fd89540c23e64150309798c540c26e62150309b588540c27661150309d584540c25d65d0c30c7553430c25d6510c30c7550430c2cd6210c308f992520c23d6494830cb952520c32d5494830cb992520c32d6494830cb951520c32d5454830cb991520c32d6454830d398d520c34f4354830d310d520c23f65d08308f597420c32e52d0830cb54b420c23f65508308f595420c32e5250830cb549420c31e54cc830c7553320c34d52cc830c7951320c31d544c830d3949320c38d424c830cd952510c3355494430d994a510c3655294430cdd0a510c3354294430d5cca510c3553294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430cdd09510c3354254430d5cc9510c355325443097596310c29e648c430c7552310c34d528c430d5546310c31d540c430d3548310c355510c430c7553300c34d52cc030d5547300c25f654c030a7191300c31d544c030d3549300c355514c0309ed95300c25e63d53209758f54c832e62953209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20d398a53c831e5454f20c755153c823e6414f208f59053c831e53d0b20c754f42c82cd6390b20d354e42c831e5350b20c754d42c832e5450b20d354d42c
  | 3 => 0xa21d355132887c7614ca21f118532886ad64c8621b358f218863f64542218f191508865f63542219718d508872d4254221d34c9508865e63d51219758f544865e63951219758e544866d62951218f993534863d64d4d218f992534863d6494d219b58a534878d424c9218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540872e62950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c218f992520863d64948219798e520865d63948218f597420871e53d0821c754f420866d6590821ab59242086cd6390821d354e42086e561908218fd95420871e5350821c754d420872e5450821d354d42086af6550821cbd95420872f5350821e394d420872d5350821e354d420870d535082197597320871e54cc821c7553320878d42cc8219b59632086ad648c821cb55232086cd638c821b9586320865f654c821c7951320871d544c821e3d09320878d424c821cb551320874e534c821b3d95320874f654c821d3d51320878e544c821d3551320878d544c821c3551320872d4294421d34ca51086ad64c8421b358f21087a54288421f14ca210866f65484219dd9521087a74248421f1cc9210873a5494021ce552500875a5394021d654e50087a94294021f24ca500873b4294021ce50a500875b3294021d64ca500872d4254021d34c9500873a5454021ce551500875a5354021d654d50087a94254021f24c9500873b4254021da90950087394254021da50950087294254021d6cc9500876a3254021d64c950087693254021d24c9500876b2154021dc88550087692154021dc485500865e6394b409758e52d032d52d0b40d394932d034d524cb40e350932d025e63947409758e51d029d63d0740ab58b41d02ad6210e409798e529025d6394a40cb949429032d5250a40d3949329034d524ca40e3509329025f63546409718d519026f62546409b189519029e63906409758b535026e6214d409b58853502cd6214d40d3988535025d6214d40d3588535024d6214d408f997435031c53d0d40c714d435025e63149409758c525031f53d0940c714f425031f5350940c714d425032f525094097997325025c65cc94097995325025c654c940e3509325023e65d0540a758f415031c53d0540ab58b415031c5350540c714e405025d6294c4097d89531023d6590c40c754e431031d5310c40ab588431025e63948409758e521034e5394840d354e521034e6394840d358e521034e5354840d354d521032e6454840d398d521034d6354840cb90d521032c4354840c794f421031d53d0840cb54b421031e
  | 4 => 0xb94942d065f65ccb419759732d074e52ccb41d354b32d065f654cb419759532d074e524cb41d354932d078d424cb419b98a539066d6294e41b358a539074e6294e419758a539074d6294e419358a539065f6254e41c794f439071e5350e419798e529065d6394a41c794f429071d53d0a41c794d429071d5350a41cb549429065f65cca4197597329065f654ca4197595329078d424ca41a758f419071e53d0641ab58b419063e6510d41ab588435065e63149419758c525072f5250941cb14942506b46150941d3d49325074c524c941e3509325069e63905419798c505065d63141419b988505066d62141418fd95431065e63948419758e521072d52d0841ad587421074e524c841d3549321078d424c841a758f41106ad62d04418fd954110677655044197d8d501065c63540419b98b54cc66d62d53318f58a54cc71c63553318fd8954cc66e62153319b58854cc71d54d0f31c755043cc6cd6210f318f99252cc63d6494b31cb95252cc72d5494b31cb99252cc72d6494b31cb95152cc72d5454b31cb99152cc72d6454b31d398d52cc74f4354b31d310d52cc63f65d0b318f59742cc72e52d0b31cb54b42cc63f6550b318f59542cc72e5250b31cb54942cc71e54ccb31c755332cc74d52ccb31c795132cc71d544cb31d394932cc78d424cb319b98a548c66d6295231ab58a548c71d6395231cb98a548c63d6295231cb58a548c62d62952318fd89548c71e5490e31c7951438c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c71e54cca31c7553328c71e544ca31c7551328c74d524ca31e3509328c69d64cc631c7953318c6cd62cc6319758e544c66e62951319b58a544c65e65d0d3197994434c71d5410d31b3588434c63e64149318f590524c72f5250931cb149424c74f524c931d3149324c78d424c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c3197d95430c71c5450c318f992520c63d6494831cb949420c72d5250831d354b320c6d561cc831e3509320c63e64944318f592510c69d64cc431b358b310c65f654c4319dd95310c63f64540318f191500c65e63d53219758f54c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e53d0b21c754f42c871e5350b21c754d42c871e54ccb21c755332c871e544cb21c755132c878d424cb219798f548865d63d52219798e548865d63952218f993538863d64d4e218f992538863d6494e21b358e428872f6550a21cb195428872f5350a21cb54d42887a76150a21e9185428878d42cca21ab592328878f424ca21e3509328874f654ca21d3195328874f544c
  | 5 => 0x50d0b4e6294e42c794f4290b1d53d0a42ab98a4350b1c5350d42ab9884350a9e6390942a758e4250a5e63d45429758f5150a5e63141429758c5050a7661141429d5845050aad6294d42ad9865350ab56194d42abd895350b1d5314d42ab58f5250aae61d4942ab5835250a9e63d4542a758f5150a9e6394542a758e5150b355114542a7d8d5050a9c6354142add855050ab46154142a798c5050a9d6314142ad9845050ab56114142c794f4210b1d53d0842d354e4210a3f6550842c794d4210b1d53508429bd954210b2e5450842d354d4210a7661d53329d58754ccb1c5450f32c755043cca3e64947328f59251cca3f64543328f19150ccacd62d5332b598754ccad561d5332c755054ccacd6215332e3d8942cca9e64d4732a759351cca9e6494732a759251ccb555114732a7d9150cca9c6454332a799050cca9d6414332b598450ccad56114332cb98a548cb2e5450a32abd95428cb2f6550a32c7953328cb1d54cca32cb50a518cb2d42542329d986544ca75619513297997434cace62d0d3297195434cb1c5450d32c7550434cace6210d32ab592424cace63909329b195424cb8f4350932e390d424cb8d4350932e310d424cb2f6550932cb195424cb8f6350932e318d424ca9e648c932a7592324cb8d428c9328f993514ca3d64d4532cb508514cb2d42d41328f990504ca3d64141329d984504ca756114132b358a544cad66195132b5586544cacf6255132c7550544cacd64d4932b3987524cacd60d4932e3d4b424ca5e6590932a7592424cace6590932d3996424cacd6490932a3592424cace6190932b3582424cb8f6250932e3d49424cace6550932b3195424cb8f6450932e3d51424cb8c5450932b3185424cacf6050932e3d95424cb8e6550932e3595424cb8c6550932e3d85424cb8e6150932e3585424cb8c6150932e3d81424cb8e6050932e3581424cb8c605093297994424ca9e6410932b3988424cb8d4210932a7993514ca9d64d4532e350b514ca9e6494532a7592514cb8d4294532e3509514cb8d4214532d5544514cb8d42d4132e350a504ca9f6454132a7191504cb8d4254132b5d85504cad46154132a7990504ca9d6414132e3508504cad66114132b5584504ca5e63d50328f596540ca3e64150329798c540ca6e62150328f992520ca3d64948328f597420cb1e53d08328fd95420cb1e5350832cb949420cb1e54cc832c7553320cb2d548c83297d95320cb1e544c832c7551320cb8d424c8329bd95320cb2d544c832d394d320ca5d6294f4197d8953d071d5390f41c754c43d06ad6210f419798e52d065d6394b41d394e52d074d5394b41d398e52d074d6394b41d394d52d074d5354b41cb99152d074e6354b41d358d52d072e4354b41cb10d52d071e53d0b41c754f42d072d52d0b41c794d42d071d5350b41c
  | 6 => 0xa1d794627b8990ef14a83d13b818a6ea7a03aa9b9868a38ea82196625125c9871db9ad9f61ed201a4e1072909a49efa118370128b22169998f4a88a769f48441a89508c398313f20fa961bd85d1ae22aa9d09b0f09f29f9023a0811c266a3d0958418eda2102a9c48f21f39e908a9b705211fa84851a62a279fd1d30f30580750dd1319cc1d724116c95e23c8a890a95c87483012608783b01699a156279a0080928305f89a28a26fa51860a488ed0000c8a160cb8d729199d80003626080300909a00000808000004030580040000301f02c014098090080040101006e008018010000240080c00a0180000100a0101903a000040040040120180581100207c0e0000100000200000600c1780702c000170010060100680101e0140e0300080000100000c0cc0200209a004018070000000380003a000028000000680a00203a004020120160100600203602c2e80000002c000000020480880402c0c40c00f00000400824032014010000000b80080700602c0000103601c058010020580080a0020040000a018004000040160100880f000090020000120000000103601c0200700e05c0400201a02000000000070020000160100780d0000000a8000420580000c0060200100802012c0280400c0101c0020040000000101005c0080000002c0500d00c0c80a018014024130000020100001b00400c0501900200c0000200000c098210000141580602e0200080001400401000006014000030020081400000c07c00002002000020030000a81780108a0980200c01a01c010050320040080500a0000300b000024080050040140700000404c0080e0020040100a00c0100200f0100000081700a01c0080701e0180100901005401000000018000260000140681d0000280100101c0a40f80900401000003030000050000280100601a018008030060060c4008070280080600000005c1e81600004000000000008028000260340d00500000005800022010010010600140002d01e010018010080601480a02a0000c00303a0000000400e024048000000140580101400c03802002060000000040080180000c0380500101200c14014000028070120040003b80000a048010019b98b5150e6d62d45439b9885050e6d62141439d9845050e756114143a75924310e3f6550c4397d954310e9f6550c43c7d954310e9f6250c43a7d854310e9c6050c43e350e5210f1d4354843e350d5210f2e6454843d398d5210f2f4354843d390d5210f2d4354843d350d5210f0d4354843c750e5110f1d4354043c754c43d0a5e63947429758e51d0a5f63543429718d50d0aad62d4f42ad98753d0ab561d4f42c754c53d0aad6214f42a798f51d0a9d63d4742a798e51d0a9d6394742cd54451d0a9f6354342a718d50d0a9e6314342a758c50d0ab66114342ad584
  | 7 => 0xec92f000107a691c01408078548c589792f9a38000001f124380023f9ad01e1b7919a21a6da6f15180d06f000103a0ba0f19b1be87911317aa951bb17124324592e806a0a98fa2a05510a0421f8055a2c8e48f18fc10f80e09e9eb1380fd8f881f04319ba5e86106a90b973a652809378f2a070c70049c30910918391b19da0d39f18cf2758b2a4b8fba869ac85105390e98aa9a96a9a6a1ea2909721a17820e9ee9bc9ca01c95fa3906c08703517f0159dc8a590910296315789095692110216c1d8a79019a34a9d96f00e9a803c0c99551468b812297c83783e9d004124c99c1249800aa1728b380f1b3971a011be0b682c80a8a4a86108246a8b0001ce8002182638000b880012e2921fe0b0a1095ba2717d81a91283389f9bc0d212b24f80996018b12a8000a916921380000b0000001a580007d8001c71670000000001991440268c40ea0fb0c914180016e9140459858fa0b611c89f08203f14484c910974159a5725d1118038e101521c00016b1de1a907f9f79f5a2b28289227620a05699208980018622c1ce06800009821999280507f00026a0001410000000b00001b58000498000798bc97917c21d82c29a15c1aa10323783229904380011a8cca5691a2590f794c0001b08c28951358251420000bf15a84e9ac05716202d12809a84b07e042a5614e1658001810ac8030648002958d4258293210181a9120d242038231a2028200019480002b99e13da3e8a20489010938130b7800265876a1c94ba501d18000e500004a0df953a0929c95f0001e88230669b003b9e410e29c07a97b9850da14da901492301cb1c61df0120000000e080000011b82080008da1e02a0f580008a00000007222480001d0000000000000000001cd1890000cf94c8a68000a00000000010000a08000001258bb8001d625a8002398001e38161c50001398998a829b1180000000000001170000809d49b40e28308310d0a4a14b02025d8000eb0002619b21c8954a890988002320000000000d52781d295b12184720406f8270e41b68e398d1fa1849cf152a3f10199819022f9c09b9a5f0e90000000000000000c4a3b1c40562980058001158de8e98000e586ca7b0002252620001ea0002810cd03a00000001780000000c8000000000001f08000f70ac1571c824f08e2371758000001d803400011e8b72222648fe966a238000f01af1c915a18205ca2898a0540171e123c0d29ab04d1ca9c280000017493a14f8892938000a410b04787096d24c00000010c00026a97f9b8a1b83317d12726b17b0d90658001e792d800150036a07a310eb8ce07013205e8d320310d024a5f85c28c96b80622e8001e31241731230291f00aa9fb2882052140101ba2720ee257972059082a732729612039289328530ba16985a9b90c693c0b126028e0141d9a8413414887
  | 8 => 0x18c100d9b113902d9e68001f5092a1f1c203e22693a8ab1388be9480c5136297a0b17681481d8c194a18e9938328d580028b9e591d1a780019700000018d8002681fc1a4164a702159499af80027e1968dc1479d58001438f41ae8002709ffa4618f0002170ec00009611f1148000de0e18000000000080000619369f71d39a31a00788638d6a00164129819116a149cda0c90699f23b86b14520488609c0882998000b58001a727d89c8138718a704e1cf87e840160a089279d127191506e17619619f8000b906300020e1c10c30948d00830001f68a1a7a96fa5c0001679139dea928f111da021bf8a98020001db17ea1205f00021306b9580ae05b24010c8000ca04f9950941ba9b815594d0088661370000af8240210000be26e04f00000019d00000000c0001a20481c58000f92190002338b32778ff0c001f8001bd0fa884a4d96e1b29fca1f87388b8001472971ec8001458001e28000001daa7ea4995d1e026c2382478aea5580009d00000000fa508001532630000001c79a0800118a298000000c81431ef0e31bf1fb8d48778cda3a8468f8158982a8a82586d17e05a13f8d79778e00bb00022b80002e2208e897717507c8bc25a0041b51e1a068000a60001958dd85014283480018e294120205a1d19a80004b800183a96a7c8001cb8dc9d68839e20000968db12087627f81b1dd1251220a79bba74000212a259a60759c180028f2419fa84097a0efa481e72260b526727727d086a7c23319108fa5b80728c15d80008003f8bf8000fc8002660ff80000000000025880000028d1b30000452748c09cca0626111016898092c80016818c800000105a2300025484c23a00006406880000000b822a1b00001e80000027380000000006292d0000ce8001f980000000000006e8600001628000002689521ab9c98000001ff0f38389238690ada0c0000df28980008b22f10400008c2110001f300000000000000004d9888002698319a98000000b192907100007d0f52151880a302f23280013387718c00000000023680000025980001819400000016da5e0e6a85800000134989a3d80a252a752440588e60460b990da67a3502802fa539a10028528d601a1651c6a6ca7893ea4098b91111607b22e13e0c7a4a9308889dc0001e62450bd000228287011800222a7f21a96a28d8001c38000000000002470001fe900926a49170a4b08f07313112a1511988da9ed9ee1f409e07c24d119000209a8e8000af0001f21a199182605b9931d09a525b1d419e82994e93ca800900620cb0fd1d516193301085985093d08d0a280007800023611799c9e991b0d98f608181b9e828f8e70d18f68c21a2a8392b9aa85793b08120d88c90615ea7106d8851df8000000ba8001e49351098698fe000159197a520ee82e8670ca80014022d8000d1170000
  | 9 => 0x39979a2411e26b8002389ec05d8000000a10278008001b600023e0652948289120000ad2540cc02b0000358ab80000000017884910f18424e8448e210483d86a0000d807b9dda189f884a81c14f2852819b49fd9088110db89da530000678e78742028e81d912c0841d21050d8a341300000b49002879639908000bd800187a2d2989eba3082208ea6d2552642358002179ea8000728b409ba449e085e09303c8859540002428f98a50000001e50c60
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x98e0d6358a548c70739ac52a463835cd6295231a1ae52a48718d0d72951438c686b94a999463435ca544ca31a1aeaa126518c1d76953318c686b94a998c638395162cc631c1aa8b108698d0d74149324c742a10c299263235ca648c531a1ae42a28618d1970151430c616b90c8a8063435cf6550a21a1ae9b2a6510e0f635095088707b2264a8443135ca63d512185ae5326a690d2970d4d4208686baca6a10438359542cc821a1aeba126410d4970d513208686baca899043c254d4294021e12a8994a010f09424ca5008695baa84a8043c294d4254021e12a6a12a010d4b754c950087852a264a8043c25513254021a92e7212a010d61719095008784a1664a80434a5d23254021ac2e3192a010f0b424c95008784a1264a80434a5d32154021a92e790aa010f214288550087a099442a8043c8d092154021e866490aa010c4d7298e51d0286b9ca4a1481235ca6390640c1ce8b10a6a060d745885350286b90a7a1a81435c85350d40a1ae429e84a050d7214d425030732a8499281435c853d0540c18a6b1682a050d7214d4150286b90a7202818354d6210c40a1ae529a842050d739494210307b2a8499081c15093294440a4ae421aa220705424c95110246b94c7208818398d5290440c2cc6a8c822048d7218d401030631aa4a00818518d5150040a1ae42a2879842d7299251cc307aa2c421c61435d2524ca3091ae5324631860d63588544c30739ac42a261835cd6215130a1ae42a4869850d72151434c286b90a999261435c8544c930a1ceaa12649841d76153314c286b90a998a618315162cc530a1ae42a2629850d72152304c286b90c6aa061835516210c30a1ae52a2641850d74949320c287baa8499061c15093294430a8ae421aa218705424c9510c246b94c91886107dd9548c430c1cc8a94621861664546310c246b90c898061071d9544c030c18c8a92601861464545300c286b98caa12410b1d95350920a48e2a9a84905a1711814248286ba0ca99241131d9544c920a88e2aa264905c1711813248306b1a8428a41835913214520a1ae7292841050d725513208286ba4a49904143dd5424c820c1ecaa126410705424ca5108382a1264a88418a5516008420c92a6b00421044d7298f54c4216b94c9a9e21435cc5250b10a1ae8292658844d7218d5484216b90c8a9c21435ce5250a10a1ae9292650860f64d8f5244306b22c6292218a5916014910c92c6b00a488661615805244286b90a6a1221435cc5250910a1ae42a2648850d7414932442873aa8499221431d5424c910c1ccaa12648860c6550932442923aa8510a21511d53288510c50caa124088648654c92044306b22c729021835916354810a1ae529a840850d739494204286b94a899021435d2524c810a1eeaa12640850d755093204307b2a849902183595424c810
  | 1 => 0x10e8b2a0f144ad2c9b9a2b542b2506303aa41620000090fad40588400ca001180073680a0000000034005515a4912c75418c0000000004a383b0013ad50011110363120536bd0d0018811630c548dc3d25c00be5286c0abf1989818d96f00c006400138de083f13400af1ea8c00343c234b60020874f6601bb887cb734ae000005004130a670000006b5900000003a00008db00121588e000e978b46ea4c007900801180017179a60024a0800ba0a800121f612e400b0391489471111f186002d160ba613508d9a2f6b14400006400024d21613000864facc3cd71db000e5071b6128324ab7c0056000e400004b12db4350c8001c4f4891ca60000000042a2003cb83f6097c869c5599c40005d800002d0015c00007080100aa00000fe133680000840a32c380632a7800cf000000000000002c2945060000a21000ee2700314d8ae5b000e099331a14ece54b31428f4d05c8a00820040d000000c0a0000c00060082000050000c040301804300b0001404020f00404010502814050000014160102000080080000140103802030780c0c030800804070801c0000028180a000080000000c0083a0091ae5b0a8621c8d721814310e4ab88c0a188743dc94354843a1eeaa1aa421d25719915210ea2b8cc6a908743dd94354843a1ee2a1aa421d0c7050d5210e8bb8a87288878354d6214f4291ae730ea4a148f735835250b06aa2c42a665831954350932a4ce3b2a849948d74987524ca47ba2c1a9265319c66550932b0ce3b2a849958571d95424cac338ccaa1265615c66550932c1aca32a849950e75d85424cb42b08c2a126561dc56050932b08e2b02849950e75181424cac3388c0a1265615c4605093291eeca16a29970542544514cb42a16c2a8265a1508615413291eeca10a09968542984504cb42a12c2282658354d6210f41a1ae529a85a0d0d7394942d0707b2a8499683839d16294e41c1ae8b14a720d0d7294f4390686b94a6a1c83435ca53d0a41a1ae529a8520e0d655093290686b94a7a0c838394d62d0641a1ae629284a0d84715093250646b94c720a83135c86354041a1ae431aa998e0d5458843cc686b94a899663435d2524cb31a1eeaa1265
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xd190cb6000000000004402a000380000000000000501204000490581dd94354843905811c14354843a05819d16294e41a05819cd629523180d8795162cc631a05819d16214d40a058298d5190440a058218d5150040a05819cd621513080d8715162cc53080d87991528c430a0582991518c43080d87191524c030a0582191514c030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
  | 2 => 14
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
  | 6 => packedAt s3K6 (788+((h/14+packedAt s3K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s3K5 (27582+((h/296+packedAt s3K5 (24030+(h % 296)*12) 12) % 3041)*11) 11
  | 4 => packedAt s3K4 (55826+((h/446+packedAt s3K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s3K3 (11856+((h/76+packedAt s3K3 (11172+(h % 76)*9) 9) % 301)*9) 9
  | 2 => packedAt s3K2 (864+((h/4+packedAt s3K2 (840+(h % 4)*6) 6) % 36)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfe1ffff0ffff87f83f0fc3ffe1fff83f44f3cf
  | 1 => 0x3fe1e1ff0f0ff87fc7f0fc387e1c3fc7bb4d33
  | 2 => 0x3ffe01fff00fff8ff800ffc07fe03ff8c38e3c
  | 4 => 0xc00001fffff0000fffff00007fffc000fc0fc0
  | 5 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2000010000008000001004800240800001045
  | 1 => 0x84484222241500814310441122089286194512
  | 2 => 0x2884954442aa441a9888aa8255412530c28a28
  | 4 => 0xa1d55988aa83552cedaa220479938192ec0f80
  | 5 => 0x3119910ecccc664f36ccf32711020624f7e000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36308
namespace PEqualNP.Outside.L_meta_36308
open PEqualNP.Outside.L_meta_36308.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0xdab4e21700003d3000000019004c58e343000000000000000014147162f482401000a8105000141200b4687406020000000000054f233a000a12c5c180000000000a52804400000000000000440003e00006000000080020008108080060000081ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xa61dd314c37c80986f10130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6186fd0c30dea18617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea10617e510c3eca2185d94430bea8861f5510c2eaa2186fd0430dea08617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c837e85907b90b20dea1641ed42c835a85907b8cb20f6996417e51c82faa3906fd0720dea0e41ef21c83da43906f90320de206417f548837ea9104fd5220bf2a4417d54882f8a9106f152209e2a4417f53882fca7105f54e20be29c41bf438837a87105f54a20dfa1441bd42882fca3105f54620dfa0c41bd41882fca1106f90220de20441fa30883f261107bc8220fd904417f544837ea8904fd5120bf2a2417d54482f8a8906f151209e2a2417f53482fca6905f54d20be29a41bf434837a86906fd0920f721241bd42483da84906b50920f719241ed32482fea2905f14520dfa0a41bd41483de42907b48520df20241bc40483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c530837e86106f50c20bf29041bf420837a84105f94420fb288417651082faa2107d54420baa8841bf410837a82105f94020df20041bc40083de40107e88020f690041f920082fea9885f95310df2a6213e54c42faa9886f553109eaa6217c54c42fea7885f94f10bea9e217c53c437e87886f50f10bfa96217e52c42faa5885f14b10dfa1621bd42c437e83887d90710dea0e21f541c436a83887d8c710fa98e21f621c43ea43886f90310de206217f548437ea9084fd5210bf2a4217d54842f8a9086f152109e2a4217f53842fca7085f54e10be29c21bf438437a87085fd4a10bf294217d52842f8a5086fd0a10dea14217d518437e83086f50610bf28421be408437881087e8c210fc98421fa20843f241087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53442fca6885f54d10be29a21bf434437a86885fd4910bf292217d52442f8a4886fd0910dea1221bf41443ec82886f50510faa0a21b541443ec62887d4c510fb10a21f5214437c80886f10110fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437e86086f50c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810dfa1021bd42042fca2086fd0410dea08217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xe53886faa710df14e21dfa1c43bd43886faa510efd0a21dea14437e518877e8310ef50621fb18c43f531887de4310fdc8621bf284437d50886fea890df95121df2a2433e54486faa890ef551219eaa2437c54486fea690df94d21bea9a437c534877e8690ef50d21dfa1243bd42487dc6490fb4c921dfa0a43bd41487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21dfa1843bd43086fca410efd0821dea10437e510877e8210ef50421f790843f621087da4210fd48421f2908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681bf42d037a85a05f94740bea8e81bf41d037a83a05f55240bf29c817d539037e87206f90e40dea1c81bc43902fca5205f54a40dfa1481be429037a85206f10a40bf28c817d519037e83206f90640dea0c81bc41902fca1206fd0240fda0481bf539037ca7206f54e409ea9c81bc539037ea5206f94a40dea94813d5290378a5206fcca40df19481bd329037865206fd4640df28c81bd519027aa3206f14640df98c81be319037a63206f0c640df90c81be219037a43206f086409f284817f53502f8a6a06fd0d40dea1a817f52502f8a4a06fd0940dea12817f51502f8a2a06fd0540dea0a81fb405037c80a05f95040bf29881de53102bca6205f54c40eea98815d531037e86206f90c40dea1881bc43102fca4207b94840b7290817d52103daa4205b54840dfa1081be421037a84206f10840bf28881f651102eca2205f54440faa888175511037e82206f90440dea0881bc41102fca0206fd0040fd20081bd40103f280206fd4c40df298819e531037aa6204f54c40cea98811d5310378a6206fd4840df29081ae521037aa4204f54840d6a90812d5210378a4206fcc840df19081bd321037864206fd4440df28881b6511037aa2204f54440daa8881355110378a2206fcc440df18881bd311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc37e87987790f30dea1e61dd43cc33a87985f94b30bea9661bf42cc37a859877ccb30ee996617e51cc2faa3986fd0730dea0e61df31cc3ba63986f90330de206617f548c37ea9184fd5230bf2a4617d548c2f8a9186f152309e2a4617d538c37e87186f50e30bf294617d528c37e85186f50a30bf28c617d518c37e83186f50630bf28461be408c378811877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261bf434c3bc86986f50d30eea1a619d434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c37e82986f50530ef98
  | 2 => 0xcafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7196fd0e32dea1c657e528cb7e85196f50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132df2a2653e544cafaa8996f551329eaa2657c544cb7e86996f50d32dfa1265bd424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865bf430cb7a86195f94832dfa1065bd420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077c87a0ef50f41de21e837e52d06faa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0ef54f419ea9e83bc53d077ea5a0ef94b41dea96833d52d0778a5a0efccb41df19683bd32d077865a0efd4341df286833e50d077aa1a0ef14341beaa4833d54906fca720df54e41dfa1c83bd43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077c86a0ef50d41de21a837f52506f8a4a0efd0941df21283bd425077884a0fdd0541df20a837f50506f8a0a0efd4d419fa9a83be535077aa6a0ef14d41dfa92833f525077ca4a0ef54941de29283bf325077c64a0ef4c941de19283bf515076ea2a0efd4141df28283bd5050778a0a0cf14141bf2a0833e54106fca620df54c41dfa1883bd43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a663bf43cc77a8798df94b31bea9663bf42cc77a8598f7ccb31ee99663bf41cc77a8398df94331bea86637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c77e8718ef50e31bf294637d528c77e8518ef50a31bf28c63bf418c77a8318f7cc631fb98c637e508c6faa118dfd5131bf2a263be544c67ca898df55131deaa2633d544c6f8a898efd0d31dea1a637f524c6f8a498efd0931dea1263df324c7ba6498efd0531dea0a63f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77e8618ef50c31bf29063ee520c6dca418df54831f6a90636d520c77e8418ef50831bf28863bf410c77a8218f7cc431fb18863dd310c7ea6218f54c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c877e8790ef50f21dfa1643bd42c87dc6590fb4cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437
  | 3 => 0x30000040000200c00c0001700c01404000012000020020060000000901011401000010008020030000000000400002c0181a00200000000000000028010040180000602c0240080101c0000080100200401000000000010100060080100000003c02804000000000030000100100400e00000006008000080020040240180100000c05800006008008000000180180000400001000002000000000000080080000200000802000008008070000000000a03a01800002000000000000000100180000202c0080000c004000000020040100402600400805006004008000000080180000400000002000004000010000000200001600c0101602600000001002008010080060140500100001c008030000040a00c0060000480600201c0100001200402000000014008000040180200a004010010020080180180d004008000000060000000a010000040040000000101000a01800006004000008010080000100400001400802000034000000120080000700001400005008008008000000000380600000c0280a004000000040100140880000200002000000008000010000140080001000800006002000010020020000000500000c010000040000000000400001801004014058030000000200000000402002000022fca5a1df54b43bf28e877d51d0efca1a1df54343dfa9687be52d0f7aa5a1cf54b43de29687bf51d0f7ca3a1ef547439ea8e87bc51d0f7ea1a1ef943439f28687bd50d0f78a1a1df552439eaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa92873f5250f7ca4a1ef54943de29287bf5150e7ea2a1ef94543dea8a87bc5150f7ea0a1ef94143dea8287bc5050e78a0a1df950439f2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e853d53d0b78a7a16fd4742df28e85bd51d0a7aa3a16f14742dfa8685be50d0a7ca1a16f54342de286857d5490a7aa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85be4350b7a86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050b7ea6a14fd4d42df29a85bd5350b78a6a16fd4942d7a9285bf5150a7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050a78a0a15f950429f2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccb7e87996f50f32dfa1665bd42c
  | 4 => 0xb60001000000000003a80006ee00062e7260000000000004ec7ce3e60002ea0000002c40005445d20000000000002ec22031630a07452273400053e4f232035600000000000000000000019e0005b202200069e6441ae0005420000008463c20640000007585c61080004660005780001480000002de0001e400000000053c6220001c600017218a00048a82641a0c87166a06ce0e84d86542b00004c083442879e85800005a80400000a0000000000000000006ea1e83962840fe2026c20cc58426a09850c45c0601101e058a4fc5fc7bc2d62b42823f074c03e1fa14a0006a25b857a6b00a025237083e2a07ea00058672c0005180da7ba03a0007f883c0003be00016200082e0000000000000005920005585c800015c3fe00022200021e0000000000000000000000003980007001dc0000002b20004ae0000000002dc8440004300000001ac0000000000008360ea55c00059800017400000000000051a2a22ca0001ec4426ec4043ec4780003740002802e44fa8145ca24c8206086e81c80005f059c33806a0007ac83a5ec38c7d67d830449c4ca7a443a14600059428e1da3a400c5622084b04f41c21f004c1de7dc0c44e205200031e75e1421b80000000000000004844988566a876463e1284544b25263d22287445e642605c31022458c3b44187860260b866465228c6504cc0000bc4906600000000000005960004360007505c479266a1d018434013241038a00025c59e00023e11455a09200009e6bc48220426c7b67c83240c600045800037c00000030079c06c00004a24e0e60861ba1600102ba35073a67000081000000000060a7d20006040006728282423b029400054c5e45a636280e13463871070a4322f20a229002e6a61b273259a00056a50a6d83880004386c800081a28a00016400000071c00035c00000026e6f62fc2747740003ac23222a51c68004e2460000000000000003641f400000080a2e20000007aa0000000004a43660000006961be41c00076042a00000000076c6cc5ee0001408602bc4e60000000000000000000000002642560000000001d273c34a5d400000040671e3360f600066c20a0000000005fe0000000000000007e23ca47200000000006800000000000000000000e0004f000085248e0f81940000000002be7e00001fc2140007401ce4021780000006125b434836a0000007fc0446c40000004a00007ec1927621a400000078823411e00012c5742480000000005aa8240004446480000000000000007ee0003ce00000076680662060200025a00000000000065c50400000000000000000000000000000083204034610a3907800000000000003280000003cc0000000000007040002f80000c04ba45e0006b244a0000005ba5da226000000000078000000400280000200000001000028008
  | 5 => 0xe0421867d42da0000ac3e841418c00201a0a66b485a7300003f22382600004b450044c12648c00000000000020e0001ea3d60460a43081303ba79865a0007282fa49a6e40007e87f200000024401816634e00000000000007c0003aa4620000003ee7567a202a8407a00000e03300000003920000003f40000005608380000005f447074842231a3f655235a0546927846ca49437200000025000076a0000f000000000000056e0000000000000003801f85884c825e00060028819013c00000000067e00000000077854881200000074e6b84f80003b805855448600000056662a3de5be00820c23a0001886c60320000001380000007b27d00363340000007fa2780000002c041e00035836000065600000072e39a64c0003e00003325a022e0005e00000000000000dc68c46e29c84c75a70c13e1e27061d427252e37617051e00000000045009c4885164161c00624481b43680000ca00000072485e00000080208a31432e0007524da00000000060c82254a4346aa3a233a3dc02019a72010e0000006e60000004d66d00004080006d45d80000000000005822300003da0006300000000004be71800000061e01e84a8507ae2b82a62cc00021c67423c0005760001b60000aa69c8081ee17661a2762f600024a54631200015e7c647a3a000016e00000066200000078e0004000005f25080000d20004760000002a400000043c6d66dc0000000000006767da5cc00000052a05e2aa6c00000003060003182e049e5b032600000000067877266e0000001f200037e18e0000b40000000960000000ce3420008620000ec16a0b60000004b600000000000034400000000000000000008244e0000000000000000002c80007ca00064e3866f017a4d40002925ce10615a2f44920000487a80000f260e6145fa5a230203821a00043e77a00000045a7e600000085440c00011a0000005b60ee1680a80007f04201a800021600000077e00000067a7f617e42400055600055e00000016c0000000002fe1aa0000000004745ea26600036c81629e12a6ac08001c2703f80006fe1986160246d25a40003c42ac00000050e4400000002544b879430c15200012e6185020000000000000002ce3ea00000080c13a0006060040003e25641d806e1b000000000005033e28601482a09015427c0000000004a66943c00007a600000046435e6ae3d05dc7e42ee03c00000073e5e26b600000000063c3e40e20000004e02c64d200053646a0fc15068237a0b20004520000d00001127f46ba00000000000040a0006264e87be8420704ce42e7820160ba32a11c78c71a8000766e22000000d872200062c0000000000004800000000004f60007420001820000002585300de4c27700000004d000000000039400068600079000000000068e54059075c79a0003843
  | 6 => 0x14e0001a000054e29a5140000000000000be6f20000007de3820003c82960007766900003a60005386f861000000074a07a1040c21962e84aa5d003400084e0000002d002812019c0007cc1e60003787b04606400000000000002360003540000000000000000005c25207464ea24000000055081e64a0006285720007025065328300000000000000000000001581bc0940000000000002106fa0000001180007146de5c07fe0000005e84dc0005de00068a2d84a26344e400013638e22c0e40007120006da1a200053a00063a00000000027a4c40d40006665246be0000000003fa02c10200033c0ae09a00000021800000017c00051229870800057c6844bc6322e65f670e00015645636e65e1f646878a6365701a647c4de07277c1cc46c7c453430e1242b64ee08408814c5a84c600000000000082c7c20000000000124a87c04960000060007683fc2627360000000000b05d631c5bc0008186a472a08c0001800000000000000560303b26425802120002f00003527b869857e00052c4fe00000000000047e73839c4ac1d60fa5103c62c26f43d479664600000085c56c00000006600081c0000000000000006582d200010c0f469a0000005f827e40e39e1c400000000041276e6680000005ac2680006e000034c5ae6fc1ca44608e7b411662467c32c75407800007e5680005281fe0008480002a800032268858e00042c0002060000000001440000d62d40000001220003bc3ae61c3d80002a
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x9208433754c42108f58f544423d62d51108f992544423e65151108f58c544423d6215110cd584544423e60151108f180544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534423e65d0d108f19743442b561d0d108f995434423c6550d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d0910ad587424423e65509108f195424423e65d0510ae98341442b56490510cd152414423c6550510ae18141442746550510bc18141443376550510cd19541442346550510add8d41442b76250510ecd8141442b46050510ec18141442b06050510ad5923144274654c510ad5913144354534c510ad59221442746548510ad591214436452485108f996404423e6510110a758c40442ad6210110ad58440443b1418c1109e1953044399434c110ec50530443d1314c110ec50620442786548110ea50920443b14148110f848520443b141c4110add92104425e63d50109758f540426e62d50109b58b540423d65950108f58e540423d62950108fd8d540423f62550108fd85540423d61550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c108f992530423d6494c1097596530431e5494c10c7552530431e6494c10c7592530431e5454c10c7551530431e6454c10c7591530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108fd97430423d65d0c10c794f430431d53d0c108fd95430423d6550c10c794d430431d5350c108f993520423d64d48109798f520425d63d48108f992520423d64948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520432f4394810cb50e520432e5454810cb551520434e5354810d354d520432e6454810cb591520432f4354810cb50d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d52508108f992510423d64944108f597410431e53d0410c754f410432e52d0410cb54b410423f6550410c794d410431d5350410cb949410432d5250410cd945410423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010a758c400431e5310010c754c40042ad6210010cb948400432d5210010ad584400433554c4010d554f100436552c40109e59610043595384010da54a10042776544010cd55110043555344010d954910043b040440109ed9510043595344010da54910043b34144010
  | 1 => 0x823d61950208fd8d540823f62550208f589540823f61550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c208f992530823d6494c2097596530831e5494c20c7552530831e6494c20c7592530831e5454c20c7551530831e6454c20c7591530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c208fd97430823d65d0c20c794f430831d53d0c208fd95430823d6550c20c794d430831d5350c208f992520823d64948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420823e64944208f59251083365494420cd55251083565394420d554e51083366494420cd59251083374394420cd50e51083374294420cd50a51083365454420cd55151083565354420d554d51083366454420cd59151083374354420cd50d51083374254420cd509510823f65d04208f597410831e53d0420c754f410833651d0420cd547410823f65504208f595410831e5350420c754d41083365150420cd545410823f65900208f596400831e5390020c754e40082ad6290020cd946400833551900208fd94400823d6510020a758c400831e5310020c754c40082ad6210020ad58440083365110020cd544400832d54c8020d354f200836551c8020d654e200837151880209bd95200832d5448020d354d20083655148020ea101200827b6548020d654d20083ab4248020dc545200823d63953108f58a54c433661953108fd8d54c423f62553108f99353c423d64d4f108f99253c423d6494f108f99053c423d6414f109b98853c426d6214f108fd9743c423d65d0f10ad58743c423f6550f108f59543c423e64d4b108f59352c423e6494b108f59252c423e6414b108f59052c425e6314b109758c52c423f65d0b108f59742c42b561d0b108fd9542c423d6550b10cd95141c42b76550710cdd9541c42b76350710add8941c42b46050710ad59231c42b5644c710d514d31c42b56488710ad59121c43645248710a758c40c42ad6210310ad58440c423d63d52108f58b548433561d5210ce983548425e63152109758c548426e62152109b588548429d6315210ab588548431e63152108f58c548431d63152108758c548432e62152108f588548432d62152108b58854843356115210ce980548423e6494e108f592538423f6454e108f191538423e6414e108f590538426e6214e109b588538423e65d0e108f197438423e6550e108f195438431e5350e10c754d438423e6494a108f592528423f6454a108f191528423e6414a108f590528425e6314a109758c528423e65d0a108f197428423e6550a108f195428432e5250a10cb54942842ba60d0610ae18141842b56190210a758c40842ad6210210ad5844084399434c210ea50
  | 2 => 0x4294430cd50a510c3365454430cd551510c3665254430d9549510c3366454430cd591510c3374354430cd50d510c3374254430cd509510c23f65d04308f597410c32e52d0430cb54b410c33651d0430cd547410c23f65504308f595410c32e5250430cb549410c3365150430cd545410c23f65900308f596400c29d6390030cb94a400c32d5290030cd946400c33551900308fd94400c23d6510030a758c400c2ad6210030cb948400c32d5210030ad584400c3365110030cd544400c31d54cc030d354b300c35551cc030da54a300c371518c03097d95300c31d544c030d3549300c355514c030e6101300c27b654c030e6d0d300c369524c030dc545300c23d6395320cb98a54c823d61953208fd8d54c823f61553208f99353c823d64d4f208f99253c823d6494f208f99053c823d6414f209d98453c82756114f208fd9743c823d65d0f20ab58b43c823f6550f208f59543c832e5450b20abd9542c832f6550b20abd8d42c82af6150b20ab18142c82ad648cb20ab59132c834c534cb208f99251c823d64947208fd9741c823d65d0720ab58b41c823f65507208f59541c82ad64c8720ab59121c829d6310320ab58840c82b561103208f58f548832d62d52208f587548833a60d52209798c548825d63152209d98454882756115220a758c54882b56115220c798c548823d6315220c758c548821d6315220cb588548833661152208f584548833561152208d584548833a60152208f992538823d6494e208fd91538823c6454e208f990538823d6414e209d98453882756114e208f997438823c65d0e208f995438823c6550e20c794d438831d5350e20ae98342882b86050a208f992518823d64946208fd91518823c64546208f997418823c6550620cd94541883355150620ab58a408829d6310220ab58840882b56110220e650d308832f54c82208f58f544823d61d51208f992544823e65151208f58c544832d62151208f584544823e6494d208f592534823f6454d208f19153482776154d209d185534823e6414d208f59053482766114d209d584534823e65d0d208f19743482ad62d0d208f995434823c6550d208f99742482ba60d0920ab592424832c54909208f19542482b860509209b19542482e86050920cbd95424832c65509208b19542482af6350920abd8542483ab6050920ab18142483a86050920aa18142482ad648c9209b19532482ad644c920d314d324823e64145208f590514825e63145209758c514823e65d05208f19741482ad62d05208f995414823c6550520ab59321482ad6448520d9145214823e65901208f994404829d6310120ab58840482b56110120ea50a3048278654c120e650d30483a9424c120f24c930483a942c8120abd92204825e63d50209758f540827661d50209d587540823d65950208f58e540
  | 3 => 0x4408f596211031d5388440cb54a211033551884408f595211031d5348440cb549211033551484408f994211023d6508440a798c211029d6308440c754c211032d5208440cd54421103a52108440ae98021102b96008440c794e501031d5394040cb94a501032d5294040cd94650103355194040ce982501039a5394040e654e50103aa5294040ea54a50103b25194040ec546501031e63953308f58a54cc23d61953308fd8954cc23f6155330c795143cc29f6550f30c7d9543cc29f6250f30a7d8543cc29c6050f308f99252cc23d6494b308fd9742cc23d65d0b30a758f42cc23f6550b308f59542cc29d64ccb30a759132cc23e64947308f59251cc23f65d07308f59741cc29d63d07308fd9541cc23d6550730a759331cc29d644c730a758c40cc2ad6210330ad58440cc31d63d52308f58b548c23d61d5230ce983548c26e62152309b588548c27661152309d584548c2ad6215230ad584548c31d6315230cb988548c23d6215230cb588548c22d6215230cd984548c23d6115230cd584548c2356115230ce980548c2ba60d0e30ae181438c23e6494a308f592528c23f6454a308f191528c23e65d0a308f195428c32e5250a30cb549428c23e64946308f592518c23f64546308f191518c23e65d06308f195418c3365150630cd545418c29d6390230a758c408c2ad6210230ad584408c31f54cc2308f58b544c23d61d51308f992544c23e6515130c758c544c23d62151308f584544c23e65d0d30ae983434c29d6490d30c7152434c23c6550d30ae181434c25c6550d30b6181434c31f6550d30c7195434c21c6550d30a7d89434c29f6150d30e6d81434c29c6050d30e6181434c2986050d308f990524c23d64149309d984524c27561149308f997424c23c65d0930a758f424c23e65509308f195424c29d64cc930a7591324c34c524c9308f990514c23d64145309b988514c26d62145308f997414c23c65d0530a758f414c23e65505308f195414c29d64cc530a7591314c354514c5308f996404c23e6510130a758c404c2ad6210130ad584404c39943cc130a7d92304c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c23d61950308fd8d540c23d63550308fd89540c23f61550308f990540c25e63150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c23f6550c30c794d430c23e64948308f592520c32e5494830cb552520c32e6494830cb592520c32f4394830cb50e520c32e5454830cb551520c32e6454830cb591520c32f4354830cb50d520c23f65d08308f597420c32e52d0830cb54b420c23f65508308f595420c32e5250830cb549420c23e64944308f592510c3365494430cd552510c3665294430d954a510c3366494430cd592510c3374394430cd50e510c337
  | 4 => 0xd50951103344254440c794f411031d53d0440cb94b411032d52d0440cd547411023d6590440c754e411032d5290440cd546411031e5350440c754d411032e5250440cb54941103365150440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401031d5350040cb549401033551500409ed9540102ae62d4c40ab58b53102b661d4c40ad58753102ba60d4c40a7596531023f6254c408fd85531031f6554c40c7d89531031e6254c40c7589531031c6254c40c7d85531031e6154c40c7585531031c6154c40c7981531031c6054c40a798c531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae980531029e63d4840a758f521031e53d4840c754f52102b661d4840ad58752102ba60d4840c754e52102ad6594840cbd4e521038e5394840cb54e521038d5394840c354e521031e5354840c754d521023f63548408fd85521032f6554840cbd4d521032e5354840e394d521030e5354840cb54d521038d5354840c354d521032c5354840cbd8d521032e6354840cb58d521032c6354840cbd85521032e6154840cb585521032c6154840cb981521032c6054840a798c521029d6314840c754c52102ae6214840cb54852102b66114840ad58452102ba60148408f997321023d65cc840c754f321032d52cc8408f996321023d658c840c754e321032d528c8408f595321031d534c840cb549321023e650c8408f594321031d530c840cb548321038d320c840ad98432102b5610c840ae98032102b9600c840a798f511029d63d4440c794f511031d53d4440ab98b51102ad62d4440cb94b511032d52d4440ae983511031d5394440cb54a51102b56594440cdd4e51103965394440cd54e51103955394440c554e51103375294440e994a51103355294440e954a51103255294440c794d511031d5354440cb949511032d52544408fd8d511023f6254440cdd9551103375354440cd94d51103965354440c594d51103355354440e554d51103155354440cd14d51103375254440cd94951103a65254440c994951103355254440e954951103255254440cd14951103376354440cd98d51103356354440cd18d51103376254440cd98951103356254440cd18951103373254440cd8c951103353254440cd0c951103366054440cd181511029e6314440a758c511031d5314440ab98851102ad6214440cb54851102b66114440cd54451102ba60144408f997311023d65cc440c754f311032d52cc440cd547311023e658c4408f596311031d538c440cb54a3110335518c4408f595311031d534c440cb5493110335514c4408f994311023d650c440c754c31102ae620c440ab588311032d520c440cd5443110395310c440ae98031102b9600c4408f997211023d65c8440c754f211032d52c8440cd547211023e6588
  | 5 => 0x430863f6550c218f595430871e5350c21c754d430863e64948218f592520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420863e64944218f592510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410874d53c8421d554e21086e562884219bd95210874d5348421e9d0521087a541484219dd9521087555348421e9d0921087a54248421b9d9521087676548421e999121087a56448421e995121087a55448421d9d4d21087c65348421d954d21087c55348421d154d21087a74348421e950d210873a5494021ce552500875a5394021d654e50087e12194021ced9250087386494021ced0e50087394394021ced0a50087394294021ced06500873941940218fd91500863c6454021d9485500873a5454021ce551500875a5354021d654d50087e12154021ced9150087386454021ced0d50087394354021ced0950087394254021ced0550087394154021dac8550087722154021da48550087712154021d8485500871d53d0f40cb54b42d033551d0740c794d439031d5350e40cb949429032d5250a40cd94541903355150640ae983539031f5394e408fd89539023f6154e40ab98853902ad6214e40ad98453902b56114e40ae98053902ba60d4a40cbd4a529023f6354a408fd85529029e6314a40a758c52902b66114a40ad58452902ba6014a408f997329023d65cca40c754f329023e658ca408f596329032d528ca408f595329031d534ca40cb549329023e650ca408f594329038d320ca40ad98432902b5610ca40ae98032902b9600ca40ae983519033751946408fd8d519023f6254640a798c519029d6314640ab98851902ad6214640ae980519023e65cc6408f597319031d53cc6408f996319023d658c640cd546319023d654c640c754d3190335514c6408f994319023d650c640ab98831902ad620c640e54c431902ba600c640ae580319023e65c86408f597219032d52c86408f996219023d6588640cd546219023d6548640cb549219033551486408f994219023d6508640a798c219029d6308640e948421902ba6008640ae580219023e65d0d40c7d4d435023e65d0940cbd49425023e65d0540cdd45415031e6454c40c754f431023d6590c40c754e431031e5350c40c754c431034e5394840d354e521032f4394840cb50e521034e5354840d354d521032e6454840cbd0d521032e4354840cb50d521032c4354840c794f421031d53d0840cb54b421023d6590840c754e421032d5290840c794d421031d5350840cb949421031d5310840cb54842103565394440d554e51103665294440d954a51103374394440cd50e51103374294440cd50a51103565354440d554d51103665254440d954951103366454440cdd0d51103364354440cd50d51103344354440cdd0951103364254440c
  | 6 => 0x72e6454831cb591520c72f4354831cb50d520c63f65d08318f597420c69d63d0831cb94b420c72d52d0831ad587420c63f65508318f595420c72e5250831cb549420c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc431b558e310c765528c43197d95310c74d524c431e5d05310c795414c4319dd95310c797434c431e550d310c765524c431b5d95310c757654c431e5991310c795644c431e5951310c795544c431f1949310c755524c431f1549310c745524c431e5d09310c795424c431ce952500c7395494031da94a500c7695294031f44c6500c73b6494031ce192500c73b4394031ce50e500c73b4294031ce50a500c73b4194031ce506500c63f64540318f191500c7553154031ce951500c7395454031da949500c7695254031f44c5500c73b6454031ce191500c73b4354031ce50d500c73b4254031ce509500c73b4154031ce505500c75b3154031dc8c5500c7593154031dc4c5500c75131540318f58e54c863e60953218fd8d54c863c60553218f99353c863d64d4f218f99253c863d6494f218f99053c863d6414f219e98053c86796014f218fd9743c863d65d0f21ad58743c863f6550f218f59543c874c534cb21ab58b41c86af62507218fd9150c863c64543218f58e548863e60952218fd8d548863c60552218f993538863d64d4e218f992538863d6494e218f990538863d6414e219e98053886796014e218fd97438863d65d0e21ab58b438863f6550e218f59543886b561d0a21add854288754534c6218fd91508863c64542219798e544865d6395121a758e544871e63951218f58e544871d63951218758e544863d6295121cb58a544863d6195121cd586544863e60951218fd8d544863f6255121cbd89544863f6155121cdd85544863c60551218f993534863d64d4d218f992534863d6494d218f990534863d6414d219e98053486796014d218fd97434863d65d0d218fd95434863d6550d21c7d4d434871c5350d21ad58742486b761509219b195324874c534c921b918532486ad62d05218fd95414863d6550521abd894148674654c521d514d31486e4624c521f14c9314863e64d41218f593504863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f58e540863e60950218fd8d540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530863e6494c218f592530865d6594c21c7952530871d5494c21c7992530871d6494c21c7951530871d5454c21c7991530871d6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f65d0c218f597430871e53d0c21c754f43086ad62d0c21ad587
  | 7 => 0x294032dc946500cb715194032ced92500cb386494032ced0e500cb394394032ced0a500cb3942940328fd91500ca3c6454032d34c9500cb3a5454032ce551500cbc93254032dc945500cb715154032ced91500cb386454032ced0d500cb394354032ced09500cb394254032d6cc9500cb6a3254032d64c9500cb693254032d24c9500cb1d53d0f41cb54b42d06ae62d4f41ab58b53d06b561d4f418fd8953d063c6054f41ad58453d069e63d4b41a758f52d06b561d4b418fd8d52d063c6054b41ad58452d063e65ccb418f59732d072d52ccb418f99632d063d658cb41c754e32d063d654cb418f99432d063d650cb41c754c32d072d520cb41e34c832d06b6610cb41ad58432d06ba600cb41ae58032d063d63943418f58a50d069e6314341a758c50d06ae6214341ab58850d071d5350e41cb549429071f5350d418f994435072f52509418f994425065e63141419758c505066e62141419b588505063d62d4d418f98353506b56194d41add85535063d63d49418f98352506b56194941add85525063e65cc9418f597325063e658c9418f596325063e654c941add8532506b4614c9418f994325063d650c941e34c832506b6610c941ad58432506ba600c941ae58032506b560d4541a798c505069d6314141ab98850506ad6214141c798c505063d6314141c758c505061d6314141cb988505063d6214141cb588505062d6214141c754f431063f6550c41cb54b421063f65508418fd9541106776550441cd951411063d62953318f98254cc63f62553318f18154cc63e6494b318f59252cc63f65d0b318f59742cc6b561d0b318fd9542cc63d6550b31a758f41cc69f63507318fd9150cc63c64543318f58a548c63e60952318fd89548c63c6055231ad587438c6b76150e318f992528c63d6494a318fd97428c63d65d0a31a758f428c63f6550a318f595428c63f64542318f191508c66e62951319b58a544c6ad62951318f58e544c71d6395131cb98a544c63d6295131cb58a544c62d62951318f586544c73561951318f982544c63f6355131c7d8d544c63f62551318fd85544c73761551318f181544c6b561d0d31add85434c63e64d49318f593524c63e64149318f590524c67a60149319e580524c63d65d09318fd95424c72f5250931cb149424c74c524c931b5185324c69d63d05318fd95414c63d6550531a7d8d414c63e64d41318f593504c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f58a540c63e60950318fd89540c63c60550318f990540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63d65d0c318fd95430c63e64948318f592520c72e5494831cb552520c72e6494831cb592520c72f4394831cb50e520c72e5454831cb551520c
  | 8 => 0x300003800700a00203a00400a00400000500d00100900200100000103300100000d00500000500800300300000000200cad98752d0eb561d4b438fd8552d0e3c6054b43ab98b51d0ead62d47438fd8951d0e3c60547438f58a50d0e3d6194343ab98850d0ead6214343ad98450d0eb561143439b9885050e6d62141439d9845050e756114143a75835350e3d61d49438f9835250e3d62d45438f9835150eae6214143ab5885050eb66114143ad5845050f2e62141438f5885050f2d62141438b5885050f3661141438f5845050f3561141438d5845050e3f6550c4397d954310f1e5450c43c754f43d0aad62d4f42ad98753d0ab561d4f428fd8553d0a3c6054f42ab58853d0a9e63d4742a758f51d0a3f63547428f18151d0a3d63943428f58650d0a9e6314342a758c50d0ab66114342ad58450d0b1d5350e42c7d4d4350a3e6510d429798c5050a5d63141429d9845050a7561141428f5875350a3e60d4d42ab58a5350aaf6254d42ab5835250a3d63d45428f9835150a9e6314142a758c5050ab66114142ad5845050b1e63141428f58c5050b1d63141428758c5050b3661141428f5845050b3561141428d5845050b1d53d0c428fd954310a3f65508429bd954210b2e54508428f58654cca3e60953328fd8554cca3c6055332a758f42cca9f6350b328f99251cca3d64947328fd9150cca3c64543328f586548ca3e60952328fd85548ca3c6055232ab58b438caaf6250e328f992518ca3d64946328fd91508ca3c64542329d986544ca756195132ad586544ca3d6395132c758e544ca3d6295132cb58a544cb3661951328f586544cb3561951328d586544ca3e60951328fd8d544cb1f63551328fd89544cb2f62551328fd85544ca3c6055132ab58b434caaf6250d32a758f424ca3f65509328f595424ca9f63509328f993514ca3d64d45328f990514ca3d64145329e980514ca7960145328f993504ca3d64d41328f990504ca3d64141329d984504ca7561141329d987540ca7561d50329e983540ca7960d50328f596540ca3d61950328f982540ca3f61550328f181540ca3e64150329d984540ca7561150329e980540ca7960150328f992530ca3d6494c328f597430ca3f6550c328f992520ca3d64948328f597420ca3f6550832b358e320ca5f654c832e3d09320cb8d424c8329bd95320cb8f434c832e350d320cacf654c832d3d95320cb8e644c832e3591320cb8e544c832e3551320ca3e64944328f592510cb365494432cd552510cbc53294432cd992510cb356494432cdd0e510cb354394432cdd0a510cb354294432d34c9510cb365454432cd551510cbc53254432cd991510cb356454432cdd0d510cb354354432cdd09510cb354254432d5cc9510cb663254432d54c9510cb653254432d14c9510cb3a5494032ce552500cbc93
  | 9 => 0x138b48dbc776000818ee000083c95631810ccc008448692a0001fa992e08ab6c9c3c0904af61f07da3da4f407a4c4be8000d9446edd661ca4a000f001b876600038600079c2ae000000bc8d00c72d10a66aec790da28ea6a8000242e405d89da964ba47f80000001ba6da3ac00000300900002b00000a00b00102100100500000600502600100100d01300a00501f00600100a00900000100d00400000500a00000706302301b00100000600000400500100000200100d00c00200500101800500a00100200900900301700300700200f00300500300000400a00100000400000800100001300002100000200000300300400f00400401a00000200200b00400000100100202000400000000100100001101300100200700101801400400100501300000202300d00200000000402b00000000000500000200002400302a00001800300400600402100800c00300001100d00200d00600100600300300100000000000900a00000200a00d00303205e00100000802200001804e01800200b00000b00000400400700600200700001601001801600001700800500000000800000600200502100400100000100901000200300000b01d00700000002500300403500000200a00300100200c00000400f00200c01701600000400a00200e00800300400001200803e00100b03c00400002900101a00004f01100200000801f00300500400302000002d00300200800300700200601d00401d00000400700100500100900400c00000000001200d00004300200200100200b00000500100100200400406f00500300200400400e00600001301a00500e00300701100301005d03900000600000600100600f00c00300000301304100000200100100100200000d00600600400001100400000200300000900200100000900600400000c00200500900800b00100500200f0040000330000010000000020a600000100000401400301900001e00000600600500800102900100000001400000001801500b00105201001600000700100200005800500100300600600100000000900801300700100300000000200400600100200c01700900000000501300101000601600900300009600300100300400e00800f00000000000e00000700600001000400000300500f00c00000100100400200100d00300a00400500500000000700700500000f02300100300700900c02001201500b00300200200000101500500100200800d01000000001300201000000e00300100500000200100000100400100800900100902c00900200100101100400500001300800e04000300000b00200601600600800200000001100100000001300b00900600101000300301200000d00800200400000001600b00400001200300400000200300000200200000000200f01900000200
  | 10 => 0x88be29400fa9d66ac0000004f2000e66e245ee00073e6be0003f200099623a1f85b600075e49e96c56445219e1881b0d5600000065e000bccaa0e86b685e235235000cd2ee7e9581d056e00000000052000000000000000011c21ec965a0d4a0c6cc60002f653ea82e04484706000ad82b0978000a22d2ca86b0463c11ae34894022a5448c0007a45560000007820006b04fa2f4158e1652e190e2e24e000392000b1a3e83f0eea0006c218e4184e422c2ea7780de4de4e6c246aa796dea27872249400029e658000ca6b124664141c4c860002be27e222000a7e0001f6206422382db24b048e00092400012c9dc00000071a8ee00000016c000efe0580c86ccc92066bfe8100e45406ee862d6a9b440e1dc9ca67a2944243d097058496837ed5432e914e7043c0006364fc0009e8000e7c000ef00ee8d2e06000a88c18f0e562beade4b72c62c3893c514000302074ce8638b069f0dfc454c307ba7ee7f06e466aebc31c0546743561ceefc3c8b7c000000a1a25821c0ca00061e0007846fe95e5943b80001ac234000de08a033a4205326fc0006f6d0601407c8a225496a71c000984ece1806f2e6c00035a5920000000000000009ac2e27b441a21a000000004000ae8000df6b9a4e2c00edc0000000000000002ee842d8a12e60e0ae00080443aa78000458d7277ed5c22e6e801cb6259e76a576ceed041786d20acdf2640b1600000080e00000085800072c9a60000000002a6cce0006f4000884cac16e692d384d887273a724a4e5343060006eaa045983b6046000df8bf4000e88f0a79251c370000a7aae6c2ea80a747d80443be5bc49a0007aeeb0c462a4ed4092b8457034ea6c0e850a496916c7874e1e6bf014ac5a3d2a0266c0009fe000b0c286bca5da0b62f8bb800079e1a4d867e24ac4628a63aeabc66e0b406c0aae8a36455825628c538000b3a0002d2aa2eca2509280002148a81a83381980005c667e0001e4536076008000a94a8e20487e8762ec9447ea000db47acbb0774b5e1865e4000dd0c1204caee560a960005c82d886000047e0008148f0c9a000834000852274d088e68366a0cc4c4eb08d22b4686c4c62c66dec9edc470e0008200005b01f41400001ee1b4264372a8ce80120d783f6e50b7abdcc2a3a6c90000b564be6b62b6d48cb0bb66bae0e7de1e0124d1a010ef4de251a68600aa008388c6b92a0e02e7c8428000ee6738eb28ecb501c2000af81a6cdc000000000990e26d5ea765e089eee431a52c95aa28cf4b60b643e42d4000000f12aa8bb25f49466785ce34a4ae0000000008320000006c620e78c394000000e844cc000ed600036e3265f24a6da04f8000e4ada60003cc000b6ecf8ac8a246349882fe3a060a000a58d0ae5c322f043d664aaa600039a000bda4a2144a30000192e4c000abe0003285d4034
  | 11 => 0x5615c37894a50c5ec78e8b030a8d6e8c4bcdc87fc476b449a4e32bbaa2e7548c8000e1c71887c57ae9e788390000c6a0003d8488aaa000000000000ea42ca524c5e9e65488501f2d8270c0beb3cd90ca80a0d18aeab4ccfe6ce92e8905128080d6ac43425f6ec8a44ba8d3ad365080ce91a9bc16a8bace441e8e0000bd6d6404a000550d504f689268429a6ae00037c0000004ca8b811e000000c0acc872e5a27c24127d40b87705d63ead326c0ddce1eefaaf42304da87400044c1169bac7c00057ea2c70864c000000c3a9a2c8e00000000000001ecba000000d7000000036622000000055ceae2a0000ad61a00180f6da40000000001c8bc0dc626cd440000009d2000cae0000000000006d6000000156ec435cab2078ccaa260000002a282e000d52000000c680d40007e620859028a8009fc0000002c40009aa000e5a000000dca38c3dc4ce54613258aeb48c200032a00077a6e2582336daab94702c6c668b8897200053c00000009402a000be6a46bc6e1a0005064dcbb4a5a5dee10000304ec60f85ca5228da134966232e94e620000f054c64803a000e9acec0000006f07f6032eee0e68e4000e4e000000c74ede33228e59c9fab280002704b80987e0dfeb2008e000ac2e1232495c05e18c2e0eac9c0c140961a29d847471e000000a5e8d8d6c9629d045662e3804ece46e6805cc486e65b844ad6e46000019c9f8c60e4293ec56346b4a9e0dec0000002f0ea6a1caa430c2ba1fc5aeb38042a1072a3c281e408afa86aafe2d60baa62cbced880aaf0248a3ce90cb23fe0e2a5c12aa42400cdeba69820ec62c938c08d5a986de6b8a2aa14e606154a64eb6712618e52c06000118a18ae293aafc090000128a98444000e547145ac1ae0c053a272e48434a3a552cf03b45880000007b03c600040c00058c000000b52e82b90898528e6a112586c10ad04ba5d200008c244daeb323140009be7d08308aa00000013c5d0c28e76d0e758416000000d8c8ded0257463ae6e740734954b5ae28806b100003a276042e5a890ab14b8c8862902ce26e5ea87a39c8dc1c054a55edeeac650479ad9247c4d27a23ce57c45e440acc84e0f2000000dc2c4a906846e36b2c2da000cbe54e000000000948a40cda78038ec3c682becc7eba27bcb7e20084cb668f6406732d8014cd9a7f4a6a5007e48aebc2b0a5a6a7298c1c6614ab017689c4a07fa7282c88b22ac888e748c0d8e6b234ca388fe0dc680c701aa44e7b6b34cb80000b200059a000c5803c55a94e630cd0db608aeecdac0000008e8880c5c45a9f6a70e8eb9e26611078a17c9cea56d4e84aea088ef02d76d9c23e854000be0d20000404c26000c1a000388cd40005026767cea9a6087f2ee216261a654baa5546bcb2656cb42adcada6106c4bc4868c825f8930100aacb023743e025c83a6
  | 12 => 0x76e7046968560004ead165a429675a6265f027a64e1502e60801061e2b9c000ebecf60003b27c4726000742c767100000f4516000b989b08447624aaa9e8d46708223c4000000e18ca2000000ce2af275276c000c7ac88102368d6009a97e0008a4b862de68a6444c8000d9600000000064200000000056a2b817018ae98d4c17a1480000009a8b5c490b6c81aa14902ec20623aaccc69885a7ec6502d07aa000b2ac3e4b49268705ccbeeae0be437add45c07bee2c8242e81681d490c79450e7b26123dee386d0c229b2ce6622eda7860bc4d6922e3edf47c0cfc8cacb48d099804840a13088c46410854481c530a123306dc2469f4ee89d4e729e25c4d3e7166b41b269e3f4aceadea6e8023444eedbad3c52629c48236c580bdeb3e182b2498e4d024c9f2122dda3fc6ec1fe4e0000a68a48000d1ec84000a201601eaa928be42ce56c42ce0bce8ac320ca015e312362000000000000000000000d58a90050d9eb36e5e000024114000ef64928bc00051004e3d4a84a1e000a06b00126dd83481366e022acd296e000f0c6b897c1b642a2402386a2396baceb88f4ba0d7e0c23f800091085e646a2a5660000001de3ca1bc662000b40e00000104df0d7c24ae028c46d83ecdbe00000000005a85c334c36284c02b1e00015a0005c200077201abd0616ed2ea2d680004b2ad221800000062466486454277cebad24ef2d46744b4e1e8d402fab8ee1470069cec099c5ba1d62fc4b6c1eb6a4d4cc2c647c6994292020340dc021625e00072045003ee9c920c94bd8b96cf200083e000000000000c8030ec0eb7010e3ee000de87fe2241ca91c5dc10a000e3c14600046a1ecb78d12e0a252384cd899ab58596e3a2b467c000908e921da628cb60360382c2030000ddec40e6419a0003b0a9c7a6000000980c160009ded98000276d74e7a9740009ec2bc35406438a41c194b18e200000000cc2980fe13aa1681600ed8802ceaa00065c21268c47ae2a000000000b54262b0eae43a80eac52000812882e9669a58e756000a3ec8c36009e26a0005b28280003160000007984720001ccbf85fe95098a00073c000a60000936000ef83580e046c0004489180007a0602572bfa000000000e2228213e3e2268d34912a32ecc4682f29b8202d28d1c25a4a8c442dc6a6d0c33c578c320008267d6bae01635e0828b436a9ae694d2a7360002e400073051e43628089acaaa7c4e89765fcc049c67b82268f8000d3017e4c0a34ab80a80d86a476480caba438470d66000da81422a89a075c8480006669ea0d0a0c072c5091e27c88a9ccb76d62070750c0c5b40a420c0001be000060bbea52000236480b1c000410b826c82889324fe308dce1d2a0acd65be9347dcc2cbfc300aae000cea99e9c865a4020d27e8442ca4a083fa90e4c26f88b66d445cdb826032ced
  | 13 => 0xe0c0000009ee4265e6c206320a606e8fadfa6723988660002283bc000c4c3a48e2000d4202882c20aa500001520007a8bd40000000128ce02631e310960000c8aa8ae7892c00068e7680006607ca0fc432e5852a942aca000000b2e518c340009005e800021000243e09cf06bbc652600f100002b26906209b60062c01660b07484a433e6fa376a36b3008839e9c2dcc95200060497ad7a06a0000000000a2ea870a07e086000000000000000478c54430c66000000ac0cfae30b80000bf61d8068052b22ad45aa8f294c9c474c0405681648ccab487862ab749e48403e6656e603ba00000044660cbd27460c4bf2c1c23cd1463e86ec6e498c9849cd262cc00082adb01745fa4f07cc0da000a4c184e44dd28fc0006ca8960007d200019600074a48a172d84f08
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x904a57118142c82a2b88a699641075cf65d0720c52c5306a91060e635885488306b1ac42a4418558e6115220c4ac5308a91061663584548830ab1ac22a44189589611522086ae232e871043571195438824cb98c0a14412c5c46050a2083ae632a83105187550d30882163aac5a1a412a1c162d0d20932e630284904b1711814248264b98c0a1241385c4605092091ae630284904a57118142482c4b98c0a1241685c46050920954ea302849062a751814248345398c0a12412a5cc6050920d12e63028490489731814248351388c0a12412a5c46050920d42e230284904a1711814248254382c9192410b1d5644c920950e0b2264905457114d3248254382c5a0a412a1c164c8520950e0b2242905457314521482543b28518241461d5434c120950eca126090648654c930482c4ba264982410bdd56290020c1aa6b14801062562546400820eb9eca2004107dd5631002083aed298801041d7654c400830729ac4200418354d621002086eeab08801061653584400830aa9ac2200410d5da5110020c2ac7288801062562944400830ab1aa220041895895110020a52ea2024010589731012008384a988090041685c44048020e42a2202401052975d092008384a9e8490041c8d09514802085ae5b2e878841d73d9742c424ab98c0a0e21295c86050710a8ae429a63885457314921c4318b0cc1aa4218358e6215210c1cc6b10a90860d63588548430b31ac22a4218558d6115210c4cc4b08a908625625845484216b90cba1c210b5c86550e1083ae632e850841d73195428424cb98c0a0c212a5c86050610a30eaa1a610852875509208420eb98c02a2210b5c86015110868eab0e86884b070587434421a3aac3a12212c1c161d0910932e630282884a9721814144268b98c0a0a21385c8605051092ae630282884a57218141442c8b98c0a0a21685c86050510964ea3028288632751814144349398c0a0a212c5cc6050510d22e63028288491731814144351390c0a0a212c5c86050510d42e430282884a1721814144258382c918a210d1d5644c510960e0b2262885457214d3144258382c910a210d1d56448510960e0b2242885457314921442583b28318221461d5434c110960eca0a6088650654c530442c8ba262982212c1d94188110a50eaa1240884b076505204433032a4290221685d1214811086eeab0c8008615535864004312a92c320021075cf651001085ae5b28800843571594400420fbaac620021075da531001083aeca98800842f75588400430729ac4200218354d621001085aed290800860d639484004216bb2a4200218358d5210010c2ca6b088008615535844004313292c220021895496110010a62ea2022008591731011004388a988088021685c84044010e42a4202200853175d051004388a9e8288021c854b4144010
  | 1 => 0x511028ab9ea528881c154e5294440e0ca6a94a2207055354a5110293396a6a8881495cb5354440a2aeb29aa2204367614d511028b398a6a8881499c85354440a4ae429aa2205327014d511028b39ea4a8881455cf5254440a4aeb292a220706539495110382a9ca4a8881c194d5254440e0aa6a92a22043676149511028b398a4a8881455cc5254440a4ce4292a22053270149511030ab18c6a8881499c86354440a4ae431aa2205327018d511028b398c4a8881455cc6254440c4ac4312a22053270189511021b3b064a88810d5d83254440e0a64192a220532700c95110298b8064a8881459cc6054440a2ae6302a220526721815110292b90c0a888107dd95314440c1aa7310a22060d535885110217bb2a4288818398d5214440c1ac6a90a220615539845110312a94c2288818598d5114440c2ac6a88a220626625445110312b12a2288818654e6014440c52a5300a22042d729973110216b94cb188810b5ca650c44085aeb310622060d539883110306a9ac4188810bdd9520c44085aeca906220626625443110312b12a218881455d5310c440c2aca9886220685624c43110382a9262188818654e600c440c52a5300622063151980311030ca9ac0188818a549600c440c62a2b00622069131580311020eb9ccb90881075ce658844083ae7328422041d7598c211020fbb2a610881075d95308440c1cc6a90422060d63548211030b31aa2108818558d5108440a4aea9084220625654842110342b1a4210881c154d2108440c32a73004220629529802110318a8cc0108818654d6008440c52a4b00422063151580211035090ac010881c254d5294040e22a6a8ca020721525465010246b90c0a1e61255c46050f3086ae3b2e859842d72d9741cc30cb1cc1aa4618358e6215230c1ac6b10a91861563984548c312b14c22a4618558d6115230c4cc4b08a91862562584548c254b90c0a1c612c5c46050e3086ae232a851842d72195418c254b90c0a1a612c5c46050d30992e430286984d171181434c246b90c0a1a61255c46050d30b12e4302869859171181434c24d3a8c0a1a61869d46050d30d14e4302869849972181434c344b90c0a1a61225c86050d30d24e2302869849971181434c348b88c0a1a61245c46050d30930e0b1e849849870593324c24c382c899261515c4524c930930e0b1e829849870593314c24c382c898a61515c8514c53083eeab1c801860d6354a400c30ab1aa3200610bdd5621003085aed290801860d63948400c306b1aa4200610ddd56110030c4ca4b08801862552584400c21abb4a2200618558e5110030c4ac5288801861563544400c312b12a220061465d4404c030b12e4202601870952101300c2c8b888098061c4544404c030a32eba1a601870b43549300c389a1aa2980610d5c765d0f2091ae630285
  | 2 => 0xa498863255db424c431e0aa5a126218f0552509310c7a0a9263280634a5c8649403185ae4322a018f12544c5500c788aa262a8063d09493154031e82a498aa018d2972191500c68cb9e84a80634c5c74254031e268298aa018f11414c5500c789a1a62a8063c450d3154031e24e898aa018f11744c5500c789b2262a8063c41913154031e268498aa018f11424c5500c60eb98c0aa643525c0534cb2183ae6302a910d517014d318870731ac52a2438598d619512183ae6302a890c2d72d97434861ab8ecba1a430e1c16550d21a32e029a8690d497014d3248670b80c299243075cf6550521aa2e029a6290ce17018931486a23aa6498a4391195324c52183ae7326a090c1d731815408706a9ac5a18438554d61d0c21e0aa7a0a4210f05535052108782a9e8490843c154d4248421a4aeb3224210d85739912108693baac890843585c35348421a8aeb29a4210f065454d2108782aa2a690843c19d15348421e0ae8a9a4210f066454d2108782b22a690843295db4348421e0aa7a1a4210f055350d21087a0a9a4328043465cc649402183ae6322a010f22544855008790aa242a8043d094d2154021e82a690aa010d19731915008694b9686a80434c5c74354021e468290aa010f21414855008791a1242a8043c85092154021e44e890aa010f21744855008791b2242a8043c81912154021e468690aa010f2143485500861bb8aca9948183595320ca40d0a64b086520689325803290217b92ca98c8185595310c640d0ac4988632069131580319020fb9aca90c81895952108640d0ac690843206a1215802190306b10c4a9881459c46254c40a2ae2312a62051a701895310287390c2a9881435c86154c40c2ac230aa62051a701855310287390c0a9881435c86054c40a2ce2302a620515711815310306a9cc4298818354d6214c40c2aa7308a62061553584531030aa9cc3a90818594d61d4840c2aa6b0ea42052571d4e521029338ea6a9081495c75354840a1aeb29aa42042e7614d5210287398a6a9081499c45354840a4ae229aa42052a7014d5210306b18c6a9081499c46354840a4ae231aa42052a7018d5210287398c2a9081435cc6154840c4ac230aa42052a701855210287398c0a9081435cc6054840a4ce2302a42052571181521020fbb2a6290818354e6214840c1cc6a90a42060d63548521030aa9cc2290818954a6114840c2aa6b08a42062552584521030ca9cc0290810d5c665cc84086ae332c6420435719943210286baa641908183595320c84086aeb3086420615539843210312a94c2190818554d610c840c4aa4b08642068532584321030ca9cc0190818a54a600c840c32a6b006420629525803210344992c0190818354e62d4440c1ca6b16a22060d5358b5110306b1ca5a88818398d52d4440c1ac6a96a22052572d4e
  | 3 => 0x6f00072400169430851058ee000790000000000e4ff9c624a000000003320000000000025c00242000318be0002b4000970a33883410499f00027c0000007e578609d238a761098083841051581216688433a203b41b4e9a3d290444538aa23055d0c9362081c4541b32820246d068210000000e80000000014c272264000ad00000064000000000000004023d4eb88632e5291f00000a7bcb09ac000000001920000007d8f2288000038001b05c000000000000000883d83709c1620428e0021ed286134ff000000000000000006d4c98e0044204120003b65dc1907c1120003803604e000000001740000018e2c0000001684104500000039e52c3c92f0663880400000004010020100800802018020200a0200000800000080000202818020100000200806010000000c0100601000010000000000000040080080000000038180c8020180004806008060000a0200a01800010060100c0001a0081a0080000004008020100801800090120000e0003c008020180c00000028000180001000008100100003800078000000a000100000607002010080300000004000040380200006010000080c028020080c008000502604002000000480c008020000c028020180a0a804008120400006800000000100e00800040020400001024028260000000002000000180a008000000c0000000004004357118152d0e16b90c0a8e878958a6114143c4cc4b08a0a1e25625845050e1ab88c0a9e85075cc6054742c2ac7308a0a1616635845050b0ab1ac2282850d5c4605533286ae2302a91961563986544cb12b14c32a2650d5c4605513286ae3326a09943571181540ca86bacc899065615c6644c832a1eeab226419706544c9510cb82aa264a8865c1d093254432e0a84992a219707434c9510cb82a1a64a8865c19d13254432e0ae8992a219706644c9510cb82b2264a8865d04c95194032a62e2324a01943571191500cb852a264a8065c25513254032e826528aa01974132545500ca98b88c8a8065c2d093254032e1284992a01970b434c9500cb84a1a64a8065c29d13254032e12e8992a01970b644c9500cb8432264a80650b5c86054f4183ae6302a5a0d0d754c832d070aa9ac21968389549610cb41d0a64b0865a0e195358032d0714a92c019683a24c9600cb41962e030a64a0e85325843250744992c0192838358e6214141c1cc6b10a0a0e0d635885050616b90c0aa6630b5c86055231c1ac7314a898e2662586544c616b90c0aa2634a5c05250931a92e02926498cd170185324c616b94c9a82630b5c86055031c1ac6a968418e2552587420c782a968298863c1549414c431e0e86a926218f0543549310c68abacc898863615ca644c431a2eeab226218f0654549310c782aa2a498863c19d1524c431e0ae8a926218f0664549310c782b22
  | 4 => 0xa1cb0985b00019c00011c0004a46a1d8000e90001e0661f80745f8ae8c517e3ac00000280000000002fe898dc135000000000001ca198000000f43648c80006245c980002e61bc000f04925587c0001cc86c8380045e3745e800000000000960ba6d016800000280000001f8000000003cc000000000b077c5598d22c5f4060e3380078000ac3dc594ce92a30c7e4ef000304000d18003480000980039a5400015f01c068000650001840013d318000181dd3763d0c011b422000ee054000000001ea000000d38000000010f01800072000000446000810000b86f04d0003a000000189276890c084034c3d8cd00021c0dc0004f05000000000000000001881860010a8000003a80005f2f4058001200008b83986c1485e0d58001bc3240f83c0000009200045a0009f0003165550820f0fa000cf0ef000000000003220010000000049d2380041460c708001ce7a48d08e2780002d9a03c21f8152322e281cf91fa0146881000042c874000000007ccd780048c000912361885ec118b20001fc000c702e7640011347228800072000000320000a00006780f000000001263ee02c000002d62d8809310c60005798423c334000000000008510c1a22f88780000066c370002ea0001c1eb00005520194000524b522a2b26c4f18b53f6000001b70002480000000000000000000000bb0c0000308000000000f8000000000005700000085c00227056910dd1330a47c0d92282122ed018d4000050fe10b40812ce192c11e0740000004c448b19a50d4270dc954178000bc80014a000000000380080d8a11963b02704908a40c418d24608c4482050004d00021f0008e80000038e90400000000570588013c40ecd723f0060007d0001ee000428f11f200000121000000ba1c10000b8e70000000008803500090c001232560008e800490000001464587c4001b613c000fb23c05e00030093000000cc0d52e416800000000818d69580b20011d80046e00000000000000d5000086000e50001721d0b685500047c80000000000f400029c000d409b2641d469800000000000a9000000001a93fa91400000000358001d400051c00164122000721cc05811846167000434211bd0d6754830871fc0940012932a2102f1d61da1dc221f50002e00019641a000001871fa000f280030a338000003a2000ad80000003400000000000df0003420009680000063c5a0b00520f43d89d0006fca28000008a400000000000000510ae000fa2222a4064000000004140000014c040001b00002509d0004345444a80000037c0000016e838000f300000000190130000000801ae00109000404158a78823ce22c0001100036d060000000000014d0008cc001370005b92500000001800000114780000ca11a000a9a340005988e0000d24a09f8ff0a618800225000508001
  | 5 => 0x6282400022a8701
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x160000000000005e527a488a500000246858784000444a74006a8400180000704e00007c000060908c6e920426463c00006400000000000000000800426c86004c008e6200003014660038321000222e7e82025c000000361e88003400009a00941a561200543e5a967200002c002a0000000c00200e9800000a762800801c00063a00000003050200071302000001050005030000030f01070002010002a05869d13254432b01819d13254032b01811913254032a05854c9610cb41a09854c9600cb4190587991524c431c057654b424c431b01829d13154031b0182191315403191187d093154031905879915348421c057654f4348421b01839d12154021b0183191215402192187d0d2154021c05625c46254c40c05725846154c40c05635c46354840c05735846154840a05854c9610c840a09854c9600c840c05635c86354440c05735886254440c05764c83254440d01325c03254440c0575589310c440a0586549310c440a11854c5600c440e01524c5600c440c057558d2108440a058654d2108440a21854856008440e01534856008440c81729c46050d30c82725c46050d30c81725c46050d30891811c163d0930891811c164cc930891811c1644c930889821c163d0530889821c164cc530889821c1644c530d01525c4404c030d0172544404c030911811d5434c2208a1811c162d0d20c81739c46050920c82735c46050920c81735c460509208a1811c1648c9208a1811c1644c920889831c162d0520889831c164c8520889831c164485208a1811d9428c120908855d1324c1209098754c4048020d01535c44048020d01735444048020909821d5434c210909831d542482108a1821c161d0d10891831c161d0910c81739c86050510c82735c86050510c81735c860505108a1821c1648c5108a1821c1644c510891831c16488510891831c164485108a1821d9418c110910855d1314c110891831d94188110920855d121481109118754c4044010d01535c84044010921875484044010d01735484044010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1074
  | 4 => 1930
  | 3 => 587
  | 2 => 78
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
  | 6 => packedAt s4K6 (880+((h/16+packedAt s4K6 (768+(h % 16)*7) 7) % 99)*7) 7
  | 5 => packedAt s4K5 (32936+((h/358+packedAt s4K5 (28998+(h % 358)*11) 11) % 1713)*12) 12
  | 4 => packedAt s4K4 (81056+((h/643+packedAt s4K4 (73340+(h % 643)*12) 12) % 2317)*12) 12
  | 3 => packedAt s4K3 (30713+((h/195+packedAt s4K3 (28763+(h % 195)*10) 10) % 937)*11) 11
  | 2 => packedAt s4K2 (4888+((h/26+packedAt s4K2 (4680+(h % 26)*8) 8) % 136)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc3cf3f9fff0e38fc7e318f8ffc71c7c784f0cf
  | 1 => 0xfc0fc7e38ff03f1f8fc1f1f1c381f9f99b4333
  | 2 => 0xfff007fc0fffc01ff1fe01fe03fe01fe638c3c
  | 3 => 0xfffff8000fffffe001fffe0003fffe007c0fc0
  | 5 => 0xfffffffff000000001fffffffc0000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x410080010041008000020240104040001045
  | 1 => 0x44221108122090281040909088809091094112
  | 2 => 0x8880a201244402500292012411240124228428
  | 3 => 0x11040052488820012525240022492400540a80
  | 5 => 0xe228b45b00ed349a49f9c9c9380c34357fe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36308
namespace PEqualNP.Outside.L_meta_36308
open PEqualNP.Outside.L_meta_36308.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x1756314002a8c48f3851486007d01d5404f1100b8d19043910d48bd39600400210028588361d6ac260028400949000600c260018a24c020588001180000105ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa61dd314c37c80986f10130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6186fd0c30dea18617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea10617e510c3eca2185d94430bea8861f5510c2eaa2186fd0430dea08617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c837e85907b90b20dea1641ed42c835a85907b8cb20f6996417e51c82faa3906fd0720dea0e41ef21c83da43906f90320de206417f548837ea9104fd5220bf2a4417d54882f8a9106f152209e2a4417f53882fca7105f54e20be29c41bf438837a87105f54a20dfa1441bd42882fca3105f54620dfa0c41bd41882fca1106f90220de20441fa30883f261107bc8220fd904417f544837ea8904fd5120bf2a2417d54482f8a8906f151209e2a2417f53482fca6905f54d20be29a41bf434837a86906fd0920f721241bd42483da84906b50920f719241ed32482fea2905f14520dfa0a41bd41483de42907b48520df20241bc40483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c530837e86106f50c20bf29041bf420837a84105f94420fb288417651082faa2107d54420baa8841bf410837a82105f94020df20041bc40083de40107e88020f690041f920082fea9885f95310df2a6213e54c42faa9886f553109eaa6217c54c42fea7885f94f10bea9e217c53c437e87886f50f10bfa96217e52c42faa5885f14b10dfa1621bd42c437e83887d90710dea0e21f541c436a83887d8c710fa98e21f621c43ea43886f90310de206217f548437ea9084fd5210bf2a4217d54842f8a9086f152109e2a4217f53842fca7085f54e10be29c21bf438437a87085fd4a10bf294217d52842f8a5086fd0a10dea14217d518437e83086f50610bf28421be408437881087e8c210fc98421fa20843f241087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53442fca6885f54d10be29a21bf434437a86885fd4910bf292217d52442f8a4886fd0910dea1221bf41443ec82886f50510faa0a21b541443ec62887d4c510fb10a21f5214437c80886f10110fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437e86086f50c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810dfa1021bd42042fca2086fd0410dea08217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xe53886faa710df14e21dfa1c43bd43886faa510efd0a21dea14437e518877e8310ef50621fb18c43f531887de4310fdc8621bf284437d50886fea890df95121df2a2433e54486faa890ef551219eaa2437c54486fea690df94d21bea9a437c534877e8690ef50d21dfa1243bd42487dc6490fb4c921dfa0a43bd41487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21dfa1843bd43086fca410efd0821dea10437e510877e8210ef50421f790843f621087da4210fd48421f2908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681bf42d037a85a05f94740bea8e81bf41d037a83a05f55240bf29c817d539037e87206f90e40dea1c81bc43902fca5205f54a40dfa1481be429037a85206f10a40bf28c817d519037e83206f90640dea0c81bc41902fca1206fd0240fda0481bf539037ca7206f54e409ea9c81bc539037ea5206f94a40dea94813d5290378a5206fcca40df19481bd329037865206fd4640df28c81bd519027aa3206f14640df98c81be319037a63206f0c640df90c81be219037a43206f086409f284817f53502f8a6a06fd0d40dea1a817f52502f8a4a06fd0940dea12817f51502f8a2a06fd0540dea0a81fb405037c80a05f95040bf29881de53102bca6205f54c40eea98815d531037e86206f90c40dea1881bc43102fca4207b94840b7290817d52103daa4205b54840dfa1081be421037a84206f10840bf28881f651102eca2205f54440faa888175511037e82206f90440dea0881bc41102fca0206fd0040fd20081bd40103f280206fd4c40df298819e531037aa6204f54c40cea98811d5310378a6206fd4840df29081ae521037aa4204f54840d6a90812d5210378a4206fcc840df19081bd321037864206fd4440df28881b6511037aa2204f54440daa8881355110378a2206fcc440df18881bd311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc37e87987790f30dea1e61dd43cc33a87985f94b30bea9661bf42cc37a859877ccb30ee996617e51cc2faa3986fd0730dea0e61df31cc3ba63986f90330de206617f548c37ea9184fd5230bf2a4617d548c2f8a9186f152309e2a4617d538c37e87186f50e30bf294617d528c37e85186f50a30bf28c617d518c37e83186f50630bf28461be408c378811877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261bf434c3bc86986f50d30eea1a619d434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c37e82986f50530ef98
  | 2 => 0xcafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7196fd0e32dea1c657e528cb7e85196f50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132df2a2653e544cafaa8996f551329eaa2657c544cb7e86996f50d32dfa1265bd424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865bf430cb7a86195f94832dfa1065bd420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077c87a0ef50f41de21e837e52d06faa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0ef54f419ea9e83bc53d077ea5a0ef94b41dea96833d52d0778a5a0efccb41df19683bd32d077865a0efd4341df286833e50d077aa1a0ef14341beaa4833d54906fca720df54e41dfa1c83bd43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077c86a0ef50d41de21a837f52506f8a4a0efd0941df21283bd425077884a0fdd0541df20a837f50506f8a0a0efd4d419fa9a83be535077aa6a0ef14d41dfa92833f525077ca4a0ef54941de29283bf325077c64a0ef4c941de19283bf515076ea2a0efd4141df28283bd5050778a0a0cf14141bf2a0833e54106fca620df54c41dfa1883bd43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a663bf43cc77a8798df94b31bea9663bf42cc77a8598f7ccb31ee99663bf41cc77a8398df94331bea86637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c77e8718ef50e31bf294637d528c77e8518ef50a31bf28c63bf418c77a8318f7cc631fb98c637e508c6faa118dfd5131bf2a263be544c67ca898df55131deaa2633d544c6f8a898efd0d31dea1a637f524c6f8a498efd0931dea1263df324c7ba6498efd0531dea0a63f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77e8618ef50c31bf29063ee520c6dca418df54831f6a90636d520c77e8418ef50831bf28863bf410c77a8218f7cc431fb18863dd310c7ea6218f54c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c877e8790ef50f21dfa1643bd42c87dc6590fb4cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437
  | 3 => 0xa02002000012024000048060000080f80101c0300a004026004020010120380001a01e0140000105a0141780006c0001a00003a004000000000001f80b00c0b40780c02200c0a002002034050040000080100001a0185c80801a024030000100240000d01801c0080a0180000283507c034028620020000080001c0040083c0281000300403a0001a80700404c000000040001d00100a000018000020080001f00c0100580e0000041804c0860380b8000520100181001a00404043008000030010080040001400c2100483101201c0280109e060000380001ec230060020300080105001c0f01d000018040010280000000a00e0000c802000000000020040e00300700c05001802124054028020020400080300602c02806002024010010020080a81604a0584003b02e0000080200c0006600001004c01816006020000240020040000d0000040b80b046010000060100500280700000c1600500c00002800004004020030000a41a03601a0c813801000004010010020240f81201800000803000000028030ba00400005008024000150020440000300002c000030f6030078020000480480400600c030140000100380b01e014000000020000380d01801c1f00000200c01837000008138030060001380203e002fca5a1df54b43bf28e877d51d0efca1a1df54343dfa9687be52d0f7aa5a1cf54b43de29687bf51d0f7ca3a1ef547439ea8e87bc51d0f7ea1a1ef943439f28687bd50d0f78a1a1df552439eaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa92873f5250f7ca4a1ef54943de29287bf5150e7ea2a1ef94543dea8a87bc5150f7ea0a1ef94143dea8287bc5050e78a0a1df950439f2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e853d53d0b78a7a16fd4742df28e85bd51d0a7aa3a16f14742dfa8685be50d0a7ca1a16f54342de286857d5490a7aa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85be4350b7a86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050b7ea6a14fd4d42df29a85bd5350b78a6a16fd4942d7a9285bf5150a7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050a78a0a15f950429f2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccb7e87996f50f32dfa1665bd42c
  | 4 => 0x3009c72e1a43240000004a00003624ce5bc06a09e0000003526fa36c12c00067e1d21cc0003123f043442879200000070800007020607670666268874e2840965a80003bc0ce6361440c256e0006540000000000463f200080065e00049c3280a247c2e453a4761863227365284f01285a03ea0002020006080001c855a49a13200029235a5680006127484ae7d612400000000000065a5366285987904aa78600056c0f41fa7980000005ec0a40780000000007a40000003ba0005d25a46140000006842c40004b80005d800000029400006c0005ae0002500006064de23a42a00064e3ec2e83a45de5740000005780005be73235821400044000044e0001a00000205ba5b60a809a7161263320bc6f86566526ac0000000980361044fe06e7767a200002c4ea1f42b68245dc0847a06342aa00c16228e76c31024c63029814c10000000073800021c00081a1e40000003745561e200000008e4780000000244f800000000010e00000040e1ba11800284200000039819a4dc0802781900007fe44a3d80000000000001fe78a31c8020f60002860008200c453c5a252400046c0f80004f468659c7c669a00040400050e7707b67c27a675e00034e3fc0162fc7ea2f827633e00020a0001f04d64f66a200043e5b80422d866072024400011c4964e643a50c0007aa5540006662fe5142662ee8146a457c4d861e74c3c484874a61c51a0b84202744823846f233c37a4483de1881fc3b43aa0524c031a3e27dc47a84e30668a31e0543d679a5f06da5a62de23e44c11411e03e48815c08a7345d48342261b270469e7583ac03a48a0b453e04e7ce2323e66ce8266c45644020a00584842ba18241a49827a3c653413c4747024ca39067a0da3960885383a64b20860220c035013a5fe6e04701223d03860d24b634a3c27544be5f62244a824a0147466240dc5e801062c69c2366d01aa49460c0cc55e4a25304ec2dc7f23e843c00028c6a865c61a60e7a84a485c0e42f65d005a68c00000051c2465fc5821f26c26c06467f06a67ee5721c44320683003d438230826a4cc0e001a21225c0b65e23167f62da6703fa2886b451600017e4268460e27005f20505ee51839c73a50207c2d66f02046b064484060a64c49026e6004542fa1b650063e1ec5524c86fc7285200e862a64a0ac85a0003b614a0006267940000006482e001e7d02725ca2521ea81e5c259e1300ee5e01500000007640006e20004e43ae2f20003dc0004da00039a00000000000054c0260002003a800083e00000000069478268000080c0002280c85ac59a73052c7142820406de0000604500000004e25f80000000000001526400002b04ac8544d45c600035e10a1ee3444424384143c04920001e04460940002d07e00ba86271e03207c0680500a0100000600003402809004014000
  | 5 => 0x42c2302bc5500b27962c272c27e0080003307b47403d214e21680482a5ce0fc57009200067c66c6c62a87be26c5da1b448e0000901ae3560000000008181801060000002620003be0000005442ea38a1ce2645e67842d40ec08285275c68243681630e2b86ec2b412a00a7ae5fa52e0ea6e600000000045200030200086000082c2e60d40005c01c201c07417056a7121d44fa17a00000038c0000000003ee19c2f038e3fe6dc3a01024580007ba2a451e00e4644d034005602a40875600023885081c5320063180d07741d020e19e71c0a629c77e0321c01781ca0006101e61926583b08566e877c22e2545cc54e2707ca6762205480005964ba1da5c84183ca3466be24e1c639237629e1d61125ea7e646079e76657e40c2d27527107c011a23c1983da48c50416e41217c76a18e00000052a6d81a25126bc49e0007426ee2c86e445e2f430a6ba00000001870e2ca35400062e7f47e400057600064248083a02e70c5400004561560000000002b267818a00000077a76800000000015a13800073c1d804c1a600045a0004b40be00000071a25830c00040676266e7601100000ca2ec0001e878c0000000003788120001580000006b26200d650a4d22cc3942ae00000025a4620b00003700000000007c46d200058a58c8380001a800000000010c0005800000c621084c15e4c41de1f68222a229082e7e86fe6986020004c666a6a040032c07a1541ac33a2347ac1365882688440006960d867283617428a45c3ce04873e1bc63c03c46600416080e81084a5863207da80836416800026025627c5663042a621836a51050848612034c0006748326641dc37e62200011600032e0442ac54a72a5600e620c0fa5940007b02be8580124c25626503b883c7ec3486b876e77863832678e1645aa8302225906c86163c836e6ca3f83f46f43363b23e41be0ae21a20855c5b424875a4720aa03846a85e05c17229a1664e01764444bc3a20f075059241c3800fe7225f43664fc2a04e87cc4224a60303e07f81b04680f22c019432a79c2ce3cc1405586cc21e2405b054674414204a5d60de7b87727fc22c5c407e6d612e6b605e28000029658416c58e35c6687d46927c87fa5e463218434247e33840a3f61464f263a72671841e00008c80a7de0662e23722c60000341346f61f842e41025e38852278836068e5064b00626d43681b83142426ae7e26ea6187b27d814854237c5b28284ee00069019622a46e7bc8067d200072406407200039e0006aa70a13e00000016a18c60433402842410841678052657a0004
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x9208433754c42108f58f544423d62d51108f992544423e65151108f58c544423d6215110cd584544423e60151108f180544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534423e65d0d108f19743442b561d0d108f995434423c6550d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d0910ad587424423e65509108f195424423e65d0510ae98341442b56490510cd152414423c6550510ae18141442746550510bc18141443376550510cd19541442346550510add8d41442b76250510ecd8141442b46050510ec18141442b06050510ad5923144274654c510ad5913144354534c510ad59221442746548510ad591214436452485108f996404423e6510110a758c40442ad6210110ad58440443b1418c1109e1953044399434c110ec50530443d1314c110ec50620442786548110ea50920443b14148110f848520443b141c4110add92104425e63d50109758f540426e62d50109b58b540423d65950108f58e540423d62950108fd8d540423f62550108fd85540423d61550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c108f992530423d6494c1097596530431e5494c10c7552530431e6494c10c7592530431e5454c10c7551530431e6454c10c7591530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108fd97430423d65d0c10c794f430431d53d0c108fd95430423d6550c10c794d430431d5350c108f993520423d64d48109798f520425d63d48108f992520423d64948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520432f4394810cb50e520432e5454810cb551520434e5354810d354d520432e6454810cb591520432f4354810cb50d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d52508108f992510423d64944108f597410431e53d0410c754f410432e52d0410cb54b410423f6550410c794d410431d5350410cb949410432d5250410cd945410423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010a758c400431e5310010c754c40042ad6210010cb948400432d5210010ad584400433554c4010d554f100436552c40109e59610043595384010da54a10042776544010cd55110043555344010d954910043b040440109ed9510043595344010da54910043b34144010
  | 1 => 0x823d61950208fd8d540823f62550208f589540823f61550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c208f992530823d6494c2097596530831e5494c20c7552530831e6494c20c7592530831e5454c20c7551530831e6454c20c7591530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c208fd97430823d65d0c20c794f430831d53d0c208fd95430823d6550c20c794d430831d5350c208f992520823d64948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420823e64944208f59251083365494420cd55251083565394420d554e51083366494420cd59251083374394420cd50e51083374294420cd50a51083365454420cd55151083565354420d554d51083366454420cd59151083374354420cd50d51083374254420cd509510823f65d04208f597410831e53d0420c754f410833651d0420cd547410823f65504208f595410831e5350420c754d41083365150420cd545410823f65900208f596400831e5390020c754e40082ad6290020cd946400833551900208fd94400823d6510020a758c400831e5310020c754c40082ad6210020ad58440083365110020cd544400832d54c8020d354f200836551c8020d654e200837151880209bd95200832d5448020d354d20083655148020ea101200827b6548020d654d20083ab4248020dc545200823d63953108f58a54c433661953108fd8d54c423f62553108f99353c423d64d4f108f99253c423d6494f108f99053c423d6414f109b98853c426d6214f108fd9743c423d65d0f10ad58743c423f6550f108f59543c423e64d4b108f59352c423e6494b108f59252c423e6414b108f59052c425e6314b109758c52c423f65d0b108f59742c42b561d0b108fd9542c423d6550b10cd95141c42b76550710cdd9541c42b76350710add8941c42b46050710ad59231c42b5644c710d514d31c42b56488710ad59121c43645248710a758c40c42ad6210310ad58440c423d63d52108f58b548433561d5210ce983548425e63152109758c548426e62152109b588548429d6315210ab588548431e63152108f58c548431d63152108758c548432e62152108f588548432d62152108b58854843356115210ce980548423e6494e108f592538423f6454e108f191538423e6414e108f590538426e6214e109b588538423e65d0e108f197438423e6550e108f195438431e5350e10c754d438423e6494a108f592528423f6454a108f191528423e6414a108f590528425e6314a109758c528423e65d0a108f197428423e6550a108f195428432e5250a10cb54942842ba60d0610ae18141842b56190210a758c40842ad6210210ad5844084399434c210ea50
  | 2 => 0x4294430cd50a510c3365454430cd551510c3665254430d9549510c3366454430cd591510c3374354430cd50d510c3374254430cd509510c23f65d04308f597410c32e52d0430cb54b410c33651d0430cd547410c23f65504308f595410c32e5250430cb549410c3365150430cd545410c23f65900308f596400c29d6390030cb94a400c32d5290030cd946400c33551900308fd94400c23d6510030a758c400c2ad6210030cb948400c32d5210030ad584400c3365110030cd544400c31d54cc030d354b300c35551cc030da54a300c371518c03097d95300c31d544c030d3549300c355514c030e6101300c27b654c030e6d0d300c369524c030dc545300c23d6395320cb98a54c823d61953208fd8d54c823f61553208f99353c823d64d4f208f99253c823d6494f208f99053c823d6414f209d98453c82756114f208fd9743c823d65d0f20ab58b43c823f6550f208f59543c832e5450b20abd9542c832f6550b20abd8d42c82af6150b20ab18142c82ad648cb20ab59132c834c534cb208f99251c823d64947208fd9741c823d65d0720ab58b41c823f65507208f59541c82ad64c8720ab59121c829d6310320ab58840c82b561103208f58f548832d62d52208f587548833a60d52209798c548825d63152209d98454882756115220a758c54882b56115220c798c548823d6315220c758c548821d6315220cb588548833661152208f584548833561152208d584548833a60152208f992538823d6494e208fd91538823c6454e208f990538823d6414e209d98453882756114e208f997438823c65d0e208f995438823c6550e20c794d438831d5350e20ae98342882b86050a208f992518823d64946208fd91518823c64546208f997418823c6550620cd94541883355150620ab58a408829d6310220ab58840882b56110220e650d308832f54c82208f58f544823d61d51208f992544823e65151208f58c544832d62151208f584544823e6494d208f592534823f6454d208f19153482776154d209d185534823e6414d208f59053482766114d209d584534823e65d0d208f19743482ad62d0d208f995434823c6550d208f99742482ba60d0920ab592424832c54909208f19542482b860509209b19542482e86050920cbd95424832c65509208b19542482af6350920abd8542483ab6050920ab18142483a86050920aa18142482ad648c9209b19532482ad644c920d314d324823e64145208f590514825e63145209758c514823e65d05208f19741482ad62d05208f995414823c6550520ab59321482ad6448520d9145214823e65901208f994404829d6310120ab58840482b56110120ea50a3048278654c120e650d30483a9424c120f24c930483a942c8120abd92204825e63d50209758f540827661d50209d587540823d65950208f58e540
  | 3 => 0x4408f596211031d5388440cb54a211033551884408f595211031d5348440cb549211033551484408f994211023d6508440a798c211029d6308440c754c211032d5208440cd54421103a52108440ae98021102b96008440c794e501031d5394040cb94a501032d5294040cd94650103355194040ce982501039a5394040e654e50103aa5294040ea54a50103b25194040ec546501031e63953308f58a54cc23d61953308fd8954cc23f6155330c795143cc29f6550f30c7d9543cc29f6250f30a7d8543cc29c6050f308f99252cc23d6494b308fd9742cc23d65d0b30a758f42cc23f6550b308f59542cc29d64ccb30a759132cc23e64947308f59251cc23f65d07308f59741cc29d63d07308fd9541cc23d6550730a759331cc29d644c730a758c40cc2ad6210330ad58440cc31d63d52308f58b548c23d61d5230ce983548c26e62152309b588548c27661152309d584548c2ad6215230ad584548c31d6315230cb988548c23d6215230cb588548c22d6215230cd984548c23d6115230cd584548c2356115230ce980548c2ba60d0e30ae181438c23e6494a308f592528c23f6454a308f191528c23e65d0a308f195428c32e5250a30cb549428c23e64946308f592518c23f64546308f191518c23e65d06308f195418c3365150630cd545418c29d6390230a758c408c2ad6210230ad584408c31f54cc2308f58b544c23d61d51308f992544c23e6515130c758c544c23d62151308f584544c23e65d0d30ae983434c29d6490d30c7152434c23c6550d30ae181434c25c6550d30b6181434c31f6550d30c7195434c21c6550d30a7d89434c29f6150d30e6d81434c29c6050d30e6181434c2986050d308f990524c23d64149309d984524c27561149308f997424c23c65d0930a758f424c23e65509308f195424c29d64cc930a7591324c34c524c9308f990514c23d64145309b988514c26d62145308f997414c23c65d0530a758f414c23e65505308f195414c29d64cc530a7591314c354514c5308f996404c23e6510130a758c404c2ad6210130ad584404c39943cc130a7d92304c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c23d61950308fd8d540c23d63550308fd89540c23f61550308f990540c25e63150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c23f6550c30c794d430c23e64948308f592520c32e5494830cb552520c32e6494830cb592520c32f4394830cb50e520c32e5454830cb551520c32e6454830cb591520c32f4354830cb50d520c23f65d08308f597420c32e52d0830cb54b420c23f65508308f595420c32e5250830cb549420c23e64944308f592510c3365494430cd552510c3665294430d954a510c3366494430cd592510c3374394430cd50e510c337
  | 4 => 0xd50951103344254440c794f411031d53d0440cb94b411032d52d0440cd547411023d6590440c754e411032d5290440cd546411031e5350440c754d411032e5250440cb54941103365150440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401031d5350040cb549401033551500409ed9540102ae62d4c40ab58b53102b661d4c40ad58753102ba60d4c40a7596531023f6254c408fd85531031f6554c40c7d89531031e6254c40c7589531031c6254c40c7d85531031e6154c40c7585531031c6154c40c7981531031c6054c40a798c531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae980531029e63d4840a758f521031e53d4840c754f52102b661d4840ad58752102ba60d4840c754e52102ad6594840cbd4e521038e5394840cb54e521038d5394840c354e521031e5354840c754d521023f63548408fd85521032f6554840cbd4d521032e5354840e394d521030e5354840cb54d521038d5354840c354d521032c5354840cbd8d521032e6354840cb58d521032c6354840cbd85521032e6154840cb585521032c6154840cb981521032c6054840a798c521029d6314840c754c52102ae6214840cb54852102b66114840ad58452102ba60148408f997321023d65cc840c754f321032d52cc8408f996321023d658c840c754e321032d528c8408f595321031d534c840cb549321023e650c8408f594321031d530c840cb548321038d320c840ad98432102b5610c840ae98032102b9600c840a798f511029d63d4440c794f511031d53d4440ab98b51102ad62d4440cb94b511032d52d4440ae983511031d5394440cb54a51102b56594440cdd4e51103965394440cd54e51103955394440c554e51103375294440e994a51103355294440e954a51103255294440c794d511031d5354440cb949511032d52544408fd8d511023f6254440cdd9551103375354440cd94d51103965354440c594d51103355354440e554d51103155354440cd14d51103375254440cd94951103a65254440c994951103355254440e954951103255254440cd14951103376354440cd98d51103356354440cd18d51103376254440cd98951103356254440cd18951103373254440cd8c951103353254440cd0c951103366054440cd181511029e6314440a758c511031d5314440ab98851102ad6214440cb54851102b66114440cd54451102ba60144408f997311023d65cc440c754f311032d52cc440cd547311023e658c4408f596311031d538c440cb54a3110335518c4408f595311031d534c440cb5493110335514c4408f994311023d650c440c754c31102ae620c440ab588311032d520c440cd5443110395310c440ae98031102b9600c4408f997211023d65c8440c754f211032d52c8440cd547211023e6588
  | 5 => 0x430863f6550c218f595430871e5350c21c754d430863e64948218f592520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420863e64944218f592510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410874d53c8421d554e21086e562884219bd95210874d5348421e9d0521087a541484219dd9521087555348421e9d0921087a54248421b9d9521087676548421e999121087a56448421e995121087a55448421d9d4d21087c65348421d954d21087c55348421d154d21087a74348421e950d210873a5494021ce552500875a5394021d654e50087e12194021ced9250087386494021ced0e50087394394021ced0a50087394294021ced06500873941940218fd91500863c6454021d9485500873a5454021ce551500875a5354021d654d50087e12154021ced9150087386454021ced0d50087394354021ced0950087394254021ced0550087394154021dac8550087722154021da48550087712154021d8485500871d53d0f40cb54b42d033551d0740c794d439031d5350e40cb949429032d5250a40cd94541903355150640ae983539031f5394e408fd89539023f6154e40ab98853902ad6214e40ad98453902b56114e40ae98053902ba60d4a40cbd4a529023f6354a408fd85529029e6314a40a758c52902b66114a40ad58452902ba6014a408f997329023d65cca40c754f329023e658ca408f596329032d528ca408f595329031d534ca40cb549329023e650ca408f594329038d320ca40ad98432902b5610ca40ae98032902b9600ca40ae983519033751946408fd8d519023f6254640a798c519029d6314640ab98851902ad6214640ae980519023e65cc6408f597319031d53cc6408f996319023d658c640cd546319023d654c640c754d3190335514c6408f994319023d650c640ab98831902ad620c640e54c431902ba600c640ae580319023e65c86408f597219032d52c86408f996219023d6588640cd546219023d6548640cb549219033551486408f994219023d6508640a798c219029d6308640e948421902ba6008640ae580219023e65d0d40c7d4d435023e65d0940cbd49425023e65d0540cdd45415031e6454c40c754f431023d6590c40c754e431031e5350c40c754c431034e5394840d354e521032f4394840cb50e521034e5354840d354d521032e6454840cbd0d521032e4354840cb50d521032c4354840c794f421031d53d0840cb54b421023d6590840c754e421032d5290840c794d421031d5350840cb949421031d5310840cb54842103565394440d554e51103665294440d954a51103374394440cd50e51103374294440cd50a51103565354440d554d51103665254440d954951103366454440cdd0d51103364354440cd50d51103344354440cdd0951103364254440c
  | 6 => 0x72e6454831cb591520c72f4354831cb50d520c63f65d08318f597420c69d63d0831cb94b420c72d52d0831ad587420c63f65508318f595420c72e5250831cb549420c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc431b558e310c765528c43197d95310c74d524c431e5d05310c795414c4319dd95310c797434c431e550d310c765524c431b5d95310c757654c431e5991310c795644c431e5951310c795544c431f1949310c755524c431f1549310c745524c431e5d09310c795424c431ce952500c7395494031da94a500c7695294031f44c6500c73b6494031ce192500c73b4394031ce50e500c73b4294031ce50a500c73b4194031ce506500c63f64540318f191500c7553154031ce951500c7395454031da949500c7695254031f44c5500c73b6454031ce191500c73b4354031ce50d500c73b4254031ce509500c73b4154031ce505500c75b3154031dc8c5500c7593154031dc4c5500c75131540318f58e54c863e60953218fd8d54c863c60553218f99353c863d64d4f218f99253c863d6494f218f99053c863d6414f219e98053c86796014f218fd9743c863d65d0f21ad58743c863f6550f218f59543c874c534cb21ab58b41c86af62507218fd9150c863c64543218f58e548863e60952218fd8d548863c60552218f993538863d64d4e218f992538863d6494e218f990538863d6414e219e98053886796014e218fd97438863d65d0e21ab58b438863f6550e218f59543886b561d0a21add854288754534c6218fd91508863c64542219798e544865d6395121a758e544871e63951218f58e544871d63951218758e544863d6295121cb58a544863d6195121cd586544863e60951218fd8d544863f6255121cbd89544863f6155121cdd85544863c60551218f993534863d64d4d218f992534863d6494d218f990534863d6414d219e98053486796014d218fd97434863d65d0d218fd95434863d6550d21c7d4d434871c5350d21ad58742486b761509219b195324874c534c921b918532486ad62d05218fd95414863d6550521abd894148674654c521d514d31486e4624c521f14c9314863e64d41218f593504863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f58e540863e60950218fd8d540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530863e6494c218f592530865d6594c21c7952530871d5494c21c7992530871d6494c21c7951530871d5454c21c7991530871d6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f65d0c218f597430871e53d0c21c754f43086ad62d0c21ad587
  | 7 => 0x294032dc946500cb715194032ced92500cb386494032ced0e500cb394394032ced0a500cb3942940328fd91500ca3c6454032d34c9500cb3a5454032ce551500cbc93254032dc945500cb715154032ced91500cb386454032ced0d500cb394354032ced09500cb394254032d6cc9500cb6a3254032d64c9500cb693254032d24c9500cb1d53d0f41cb54b42d06ae62d4f41ab58b53d06b561d4f418fd8953d063c6054f41ad58453d069e63d4b41a758f52d06b561d4b418fd8d52d063c6054b41ad58452d063e65ccb418f59732d072d52ccb418f99632d063d658cb41c754e32d063d654cb418f99432d063d650cb41c754c32d072d520cb41e34c832d06b6610cb41ad58432d06ba600cb41ae58032d063d63943418f58a50d069e6314341a758c50d06ae6214341ab58850d071d5350e41cb549429071f5350d418f994435072f52509418f994425065e63141419758c505066e62141419b588505063d62d4d418f98353506b56194d41add85535063d63d49418f98352506b56194941add85525063e65cc9418f597325063e658c9418f596325063e654c941add8532506b4614c9418f994325063d650c941e34c832506b6610c941ad58432506ba600c941ae58032506b560d4541a798c505069d6314141ab98850506ad6214141c798c505063d6314141c758c505061d6314141cb988505063d6214141cb588505062d6214141c754f431063f6550c41cb54b421063f65508418fd9541106776550441cd951411063d62953318f98254cc63f62553318f18154cc63e6494b318f59252cc63f65d0b318f59742cc6b561d0b318fd9542cc63d6550b31a758f41cc69f63507318fd9150cc63c64543318f58a548c63e60952318fd89548c63c6055231ad587438c6b76150e318f992528c63d6494a318fd97428c63d65d0a31a758f428c63f6550a318f595428c63f64542318f191508c66e62951319b58a544c6ad62951318f58e544c71d6395131cb98a544c63d6295131cb58a544c62d62951318f586544c73561951318f982544c63f6355131c7d8d544c63f62551318fd85544c73761551318f181544c6b561d0d31add85434c63e64d49318f593524c63e64149318f590524c67a60149319e580524c63d65d09318fd95424c72f5250931cb149424c74c524c931b5185324c69d63d05318fd95414c63d6550531a7d8d414c63e64d41318f593504c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f58a540c63e60950318fd89540c63c60550318f990540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63d65d0c318fd95430c63e64948318f592520c72e5494831cb552520c72e6494831cb592520c72f4394831cb50e520c72e5454831cb551520c
  | 8 => 0xd00000200200c00500b00004600300100800500200800503e01400400600902b005007005001001001002007001000003ad98752d0eb561d4b438fd8552d0e3c6054b43ab98b51d0ead62d47438fd8951d0e3c60547438f58a50d0e3d6194343ab98850d0ead6214343ad98450d0eb561143439b9885050e6d62141439d9845050e756114143a75835350e3d61d49438f9835250e3d62d45438f9835150eae6214143ab5885050eb66114143ad5845050f2e62141438f5885050f2d62141438b5885050f3661141438f5845050f3561141438d5845050e3f6550c4397d954310f1e5450c43c754f43d0aad62d4f42ad98753d0ab561d4f428fd8553d0a3c6054f42ab58853d0a9e63d4742a758f51d0a3f63547428f18151d0a3d63943428f58650d0a9e6314342a758c50d0ab66114342ad58450d0b1d5350e42c7d4d4350a3e6510d429798c5050a5d63141429d9845050a7561141428f5875350a3e60d4d42ab58a5350aaf6254d42ab5835250a3d63d45428f9835150a9e6314142a758c5050ab66114142ad5845050b1e63141428f58c5050b1d63141428758c5050b3661141428f5845050b3561141428d5845050b1d53d0c428fd954310a3f65508429bd954210b2e54508428f58654cca3e60953328fd8554cca3c6055332a758f42cca9f6350b328f99251cca3d64947328fd9150cca3c64543328f586548ca3e60952328fd85548ca3c6055232ab58b438caaf6250e328f992518ca3d64946328fd91508ca3c64542329d986544ca756195132ad586544ca3d6395132c758e544ca3d6295132cb58a544cb3661951328f586544cb3561951328d586544ca3e60951328fd8d544cb1f63551328fd89544cb2f62551328fd85544ca3c6055132ab58b434caaf6250d32a758f424ca3f65509328f595424ca9f63509328f993514ca3d64d45328f990514ca3d64145329e980514ca7960145328f993504ca3d64d41328f990504ca3d64141329d984504ca7561141329d987540ca7561d50329e983540ca7960d50328f596540ca3d61950328f982540ca3f61550328f181540ca3e64150329d984540ca7561150329e980540ca7960150328f992530ca3d6494c328f597430ca3f6550c328f992520ca3d64948328f597420ca3f6550832b358e320ca5f654c832e3d09320cb8d424c8329bd95320cb8f434c832e350d320cacf654c832d3d95320cb8e644c832e3591320cb8e544c832e3551320ca3e64944328f592510cb365494432cd552510cbc53294432cd992510cb356494432cdd0e510cb354394432cdd0a510cb354294432d34c9510cb365454432cd551510cbc53254432cd991510cb356454432cdd0d510cb354354432cdd09510cb354254432d5cc9510cb663254432d54c9510cb653254432d14c9510cb3a5494032ce552500cbc93
  | 9 => 0x2b6000e406a45e219c96c9aab648f25ccd021c400017e00021e366946000000ba85963485ba41c000000000164d7400000072c0546c8e78abe78e85e878c5c66a0000000005f45be98c2529ecc740002aa8d847658a6d43c6e54e862626565b289c13edd009e91661a46c1cc00801400000000900101401d00701500100400300000200800903900200a00e00200000d00200000300c00000003000401200901000400500100000000501600100200c00100500000300f00c04400000000000100a02f01800200300000100000400e00000300000600300800500500d02200f00000400101100200300a00200100000600001000600103200002f00000000e04100000900100000000000100700000a00100001700000000800700300700400001100600700000400700400a00600400000000200500901701900700800000200100906200b00903900000000801100301000000500200000801900600100800900805b00100b00501301500100500100c00501c00a00500c00301901600001002200000500600100000400700200102e00500500a00100600200700000c00000a01300000000000704d00100202300400000100800600000000e00f00300300000000100000000301400b00000601000701700000100602500600800400100000401102400b00100100100a00400500000301001200e00200000100000900700c01800100702500500900600b00303900500200e00700a00000500000a00000603900800000401100000f00e00300201c00000300500100300400800000e00500f00100200200600100103000302100100000e00800800000102101d00100000d00d01800000f00000001000200500101100104e00600002600000200c00d00e00306f00200100001400300200800a00100100600500000300000700000000100901800b00b00000100600000008700802f00405300000e00b00700e00000100401000000505e00600201300100000100000900500200d00100e00a00900300e04d06300d00000201600000200100700100100001300500000000001000302801700200100a00200300000301000000600602403302e00a00b00200001700700100200400f00000300d03700e00100200900100300000600e00300000101000900000900900500000000000f00000300200100b00300000000000800000501100600200300100300101000000300b00000c00200500000000200c00002c00002200105600000b00600100000b00100900200200000000000100300600b00400000701500503a00200b00c00000b00000000100001101100300100601e00200100400100e01700100100800000f00500400000600001700200100300005600201c00000b00200700200000000804502000100600003000000003901600000f00
  | 10 => 0xf80ca19e6221a21044d4c8c3aa944d96ea0766388462be8968c68d94a4ac6e25c16056a06e04ec42e8a2e8b18050870228a666ce74683c9da59c55c40c962ba2bb8e7623221229a65e4aa9d447e54a80a35ceb8c480a64927ceb9e1020126f6d2629636297a9d652edfa6404405606cadbeafe7926ba1369b27b06c603854c38a57ee90e3c326094110d54c2a63031e1be3a203662c01eaf2a8ab2e876e6844634e9ee00070060c88cb301fea68b2ad36000e34a5016c0005d0002668a8453a0005186d8ca0976a900006fe006000d42c6cab60004a424e8e4a200000000884f200000088000000000000051075c00039e832a5aa8608690079a336a5c000bfc00059230e6987505783dc0000000000003ae6f41f6c347307a2cf8ebca1ece46fcd40856894000000000d5611ab7473c30690e0001da5240c4000b58ab078634ac32dde1580000005b824cca82c2ae400066200052cb40a4c0fece20dad609c07dc4f6d84862728000e587c88f84e4cf2e4e2a848a172964c766ec6deb824f81a80006063de000000b986281b4bd06a00004de5203f651e838b9c3e627a498000a220000623c8b206b6b7c000254000000692bee12400010a000d92dce000ee4000170000384de68bae62000a4200098ad10d3e000b8600000000000000000064a97e1f2600758ed6cde89a516b0e000000c9c000674000244330baa0008a6000000f08aa883e0005ee922dc07faec0d0c346ca6ce0154a3a8d6000000854000e7c0003e0a4e00025a0deea859044e00055e71248e000ef868e90a21c4ce08ab1e88e82a868714934d380bcd2223a4007aa168450dba55092e81aaa47d8998130522c4e0000009e20004a0966000970e50000410e4200052a7be34c69c000246688000000a6e0ea4e208c05c7e0020000c224b4e2c5143166c245ee741766b023673ac9826617a100d1c556bcad1a512dfe2a60cc954000d3c05e0007440685d61e42f6632c62320d582261bc14e06a6bc1141e0270554000000000c56d7c7c0a6232a2224da0461d4e9c044ed2e6a87c19a1c28d2bb60f222ab4ebfadf29380e800038eddc8648267e2e5600015a12a000a180008daafa0c269ad7eeeaa2a8e8bd82ea452dd41d21ecc6aaa6ade4b0c602980002d6afc734b04c9e5ead50dea71a02c9e66942caa0c2845e43b8e1846ec0204a94e1ae5dea8201a56c2d009241225e40e4b27cc586b8e768b0a06cca4c3ea6ccd259e1940b0d46282b9640acdc1120fce98e0c5c81e84b618a000906c20ad6e704c01f08021466f2000aba340204eb203225899c70a2926a65dace8c0e10eaf461c81e35eb6af0c3ba0f65fe77ab5a0001841de0006acc54d982240002ce6be1ca7d6efeb5c99a000b78cd68aa22e99e43c4581c0120e4cbf40008508966e8b56b52000e4a2c4c16f000002a4
  | 11 => 0xee488b66782f46fab5e42c04c3b44645022dec949a464c0a8000aa02d27b6d1e9fc612c4c85c00000000c4907ec96eb68534cae604000c5ed088d4ce67c65a8a96376148784d4a5dc4566e6b925a0a48d66b00e04ad8824000d248048ec7f4000a600000343722c648c00057a62492aac2000b4c4805f0594572c1cc3623c21639244cbd61900003b63100b65e018eaf02cc732df026ec24eacea4e8c9905666dc69e9247bc6604723c4edc0b47d42642ae8a01fcde427ea7ea46cea7641b256213a6d28c48863825caaae3f4000eb60000000000000006b412cc82000000000da00000000005d21224028fa000654000996278ece20681c000000ea63d00009ca87a000000c90470000000a3e16ee6cc46bf2000166c140001ee676dfce06e12d0ac1842a5d4c723ee000812a009e85fc6b25f80740000000000000009f0000ec8000000d200000c6cd831ce2eeb014223480c000000cc8d4e000d4c00000000000000096a92cef4056cda0a033a00000000000000e116000000000666dd6014000cba000d2a0000003a4000742000a3ca5895edece3e5a4528b1cb60ba47c2ae871898445ce640042d4000030c44000b9ae1a93c000cec51c752e6e008cca3806a8052000b028b82ee048cc4d5cd5e4a60000000005c6cb084e07a0000dc0006187ba4dcbdc4c6c9ab168fc000000000be4350420d148226c4bea30a3b01961fadda1aa78a9c2000af639c8bcc5036c8a2208de84be61e598140000000efc00007e3d2000992000df8466000e669fea8000000067c338558000e4618cc78000000d30bde438b80a7a0008885525749101e64bc7a4b8474aab23e4c8eae6da27ea7fc8303b2a744ca808286cb426a000ab8a1c00000000043477c36046a20a4ac0d4cbc89ed6ae36000aa228c1867c4682736568d8680e332e26eca00094c890bc0ae2664bec15607605abe637c7f8a8e84a0007b275a4f0f021e2c08bb2066a88db4d687b43f0354828442ee00000000000002f2000b06a78042df40004eab082fa0d62e60009a60009b06447622fce5cd70b128443da4d6b466d63027402badb6f0a5b0dd8422b6e0aad7aec2b7a4c487240676c8be58c9a0ab42a27544e83feb28b7015c32cd78d484d00c8a8c0ce200000cfe26c00041a58e00a91ab72d88a9800036e582000a143a8010672b508cea28bd4ad2028b90cb686617cd047e40000001ba8e602a0000d88c6f063640007240002888f48f00d03440000268ac546000e7e50ec0a4ae3ac000000394cf6b3e91894aa9ac3a86c1520005a6adc93a7aced8e280e6a129c41a66964c2e92162d8ab48e30baea5617446008050674eac64a22380003220843d68cccbe5004ee77015e5306ea90c67a378846ede760000b0c1381787eedbc85a7e872684039a42e602952e16c88be2c269d266cbce0
  | 12 => 0x898670aeca2e9089ea51a8c8000d0e78c5bcd3a0000008a474882ceae3d877200057cc105e6488c008b442891cbc2c5a93e000852a640009dcaea0be47c432bc89dea06cfa34254ea440002680580009bc9507de16a41e000000a24858000930064b26cd43860002be8069e4f049be6263fa7027d2708000ef0cc6cf411e090040000a54d18c8a00000071c000da4974686e5a0000bae102b4000d6eb6cc069ba2c8bc6000272000a2c0009124180009a2cce356cf06588165ace227e6000e1c810ebee8431435877ea34eba8200187a63682b008275653c1983ca3c0722c96d440f483af1279030031a97831810643e276000a26a92132902b8cb629ac2e2078a4000035ae3883463886e800deec5212828a86ac2c2e49ae4d80e43ea8363e279e960000dca000e445b4cd003a000b888d02b82e09a8482ae00003ec1c875ee1470e00006068a14424079845aa381b0ed418203c00014a62e3f2430cac32827cee8a04d8e5cee88e5ea3653ed2ce940ee000b948926e213420e11c49c0007a07f64cc36a65037024aa0abbe2560002b2c86000b22d348c2e969f4564d009264fa3be1ce4b809828e4089d850a44874c324c408e0096904584d1267ea0277847a13cace62050cada000a083960001b856e70c00039021a0000003bce7aac471e4e00003fcb4ada6e8e72e7da8ea576b3a7200009f27d0aac0007806f8c802f09e0bc4000a32776000b3c0001d622cc0c6460000000003d4000a102f8248bb00002d8c4a55a0e29948c0b36986000982d2ebbad5a2500007cadae000000588e241dcbe05f6ba0ee60ec118dd23340000d2414000b5449abb40007a80c00000f095864800097cbda940bac6420002ecef6436000e725ec000e02000bf08ee000d16000000000aeea5202e0a2b7e308cb8de04964ba0006083c2000000000dc4000e6000088acee0007f0956532424874000ca2948dc6c30e0a1d8cfc794a9ee0e000000972214000000000000d72cc2ed0a1a38cd06000b1a03e70460a000000b143ce0000000005040000005fa00018023e634000db82909201f8dc2c666ae0ae09ab2cc924942daec400063a44a000d32db20005c46c05405268ca0ac928b6695a72a000000dac2fe000c12ad0d80000000eccbf8c38ad44fceaa65acaa3041d01ac542c3c1a409caaa00014cc64022000220c700000fa8602bc000000d9a000000000000b347f25d8db054459aa3066e782444000478000acc0006a24e60000006e0000942df6738c8412e6dab329f69ce1b6bcc63e3f8274d7649e29ea70e1ee32000a5e5c04166b8000000484000b44a7212665cd285a2c7c352ea26908b00007b80006ccbd2000eee000000000374f100008b20000004260000b8d64ccc5382101ea2c0710000a942ace00efa00033c19295c0000000b26f018893276
  | 13 => 0x65298e60e218882e3a0e08845f268c988684bf679608e1a0dcceda9fab104c800098087e5aed9c0000008184febfe84cc1a9b84a807cd6c91e7ae01c4f457037a848d9e3e85b637e294ac010cd524ec53679cee2d9032ee9abbce809f8c7ecc06ee0168de91430c2dcf0e62a2806366aa202788eb49c6a7cc587745c2000b8ac0484282ee2076a242a0ec283a6e826d0474e2aa9cac8daab384d2716da868061629c64e6e4312ef20008a84540728dc000ba69cc4045e8070936d62706b769b48e20005aa0a4468000b42c2e000a6a43a4861f49c8548230abcc1e8148f6150ec66100005800003a0c7acb29d0260a1620c1c6000af8eec0248ae7fea762a010850800063caca614de2b248fe73e0009b6e08000d820003cc000000000d8c33ee9ee52398000dc8
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x904a57118142c82a2b88a699641075cf65d0720c52c5306a91060e635885488306b1ac42a4418558e6115220c4ac5308a91061663584548830ab1ac22a44189589611522086ae232e871043571195438824cb98c0a14412c5c46050a2083ae632a83105187550d30882163aac5a1a412a1c162d0d20932e630284904b1711814248264b98c0a1241385c4605092091ae630284904a57118142482c4b98c0a1241685c46050920954ea302849062a751814248345398c0a12412a5cc6050920d12e63028490489731814248351388c0a12412a5c46050920d42e230284904a1711814248254382c9192410b1d5644c920950e0b2264905457114d3248254382c5a0a412a1c164c8520950e0b2242905457314521482543b28518241461d5434c120950eca126090648654c930482c4ba264982410bdd56290020c1aa6b14801062562546400820eb9eca2004107dd5631002083aed298801041d7654c400830729ac4200418354d621002086eeab08801061653584400830aa9ac2200410d5da5110020c2ac7288801062562944400830ab1aa220041895895110020a52ea2024010589731012008384a988090041685c44048020e42a2202401052975d092008384a9e8490041c8d09514802085ae5b2e878841d73d9742c424ab98c0a0e21295c86050710a8ae429a63885457314921c4318b0cc1aa4218358e6215210c1cc6b10a90860d63588548430b31ac22a4218558d6115210c4cc4b08a908625625845484216b90cba1c210b5c86550e1083ae632e850841d73195428424cb98c0a0c212a5c86050610a30eaa1a610852875509208420eb98c02a2210b5c86015110868eab0e86884b070587434421a3aac3a12212c1c161d0910932e630282884a9721814144268b98c0a0a21385c8605051092ae630282884a57218141442c8b98c0a0a21685c86050510964ea3028288632751814144349398c0a0a212c5cc6050510d22e63028288491731814144351390c0a0a212c5c86050510d42e430282884a1721814144258382c918a210d1d5644c510960e0b2262885457214d3144258382c910a210d1d56448510960e0b2242885457314921442583b28318221461d5434c110960eca0a6088650654c530442c8ba262982212c1d94188110a50eaa1240884b076505204433032a4290221685d1214811086eeab0c8008615535864004312a92c320021075cf651001085ae5b28800843571594400420fbaac620021075da531001083aeca98800842f75588400430729ac4200218354d621001085aed290800860d639484004216bb2a4200218358d5210010c2ca6b088008615535844004313292c220021895496110010a62ea2022008591731011004388a988088021685c84044010e42a4202200853175d051004388a9e8288021c854b4144010
  | 1 => 0x511028ab9ea528881c154e5294440e0ca6a94a2207055354a5110293396a6a8881495cb5354440a2aeb29aa2204367614d511028b398a6a8881499c85354440a4ae429aa2205327014d511028b39ea4a8881455cf5254440a4aeb292a220706539495110382a9ca4a8881c194d5254440e0aa6a92a22043676149511028b398a4a8881455cc5254440a4ce4292a22053270149511030ab18c6a8881499c86354440a4ae431aa2205327018d511028b398c4a8881455cc6254440c4ac4312a22053270189511021b3b064a88810d5d83254440e0a64192a220532700c95110298b8064a8881459cc6054440a2ae6302a220526721815110292b90c0a888107dd95314440c1aa7310a22060d535885110217bb2a4288818398d5214440c1ac6a90a220615539845110312a94c2288818598d5114440c2ac6a88a220626625445110312b12a2288818654e6014440c52a5300a22042d729973110216b94cb188810b5ca650c44085aeb310622060d539883110306a9ac4188810bdd9520c44085aeca906220626625443110312b12a218881455d5310c440c2aca9886220685624c43110382a9262188818654e600c440c52a5300622063151980311030ca9ac0188818a549600c440c62a2b00622069131580311020eb9ccb90881075ce658844083ae7328422041d7598c211020fbb2a610881075d95308440c1cc6a90422060d63548211030b31aa2108818558d5108440a4aea9084220625654842110342b1a4210881c154d2108440c32a73004220629529802110318a8cc0108818654d6008440c52a4b00422063151580211035090ac010881c254d5294040e22a6a8ca020721525465010246b90c0a1e61255c46050f3086ae3b2e859842d72d9741cc30cb1cc1aa4618358e6215230c1ac6b10a91861563984548c312b14c22a4618558d6115230c4cc4b08a91862562584548c254b90c0a1c612c5c46050e3086ae232a851842d72195418c254b90c0a1a612c5c46050d30992e430286984d171181434c246b90c0a1a61255c46050d30b12e4302869859171181434c24d3a8c0a1a61869d46050d30d14e4302869849972181434c344b90c0a1a61225c86050d30d24e2302869849971181434c348b88c0a1a61245c46050d30930e0b1e849849870593324c24c382c899261515c4524c930930e0b1e829849870593314c24c382c898a61515c8514c53083eeab1c801860d6354a400c30ab1aa3200610bdd5621003085aed290801860d63948400c306b1aa4200610ddd56110030c4ca4b08801862552584400c21abb4a2200618558e5110030c4ac5288801861563544400c312b12a220061465d4404c030b12e4202601870952101300c2c8b888098061c4544404c030a32eba1a601870b43549300c389a1aa2980610d5c765d0f2091ae630285
  | 2 => 0xa498863255db424c431e0aa5a126218f0552509310c7a0a9263280634a5c8649403185ae4322a018f12544c5500c788aa262a8063d09493154031e82a498aa018d2972191500c68cb9e84a80634c5c74254031e268298aa018f11414c5500c789a1a62a8063c450d3154031e24e898aa018f11744c5500c789b2262a8063c41913154031e268498aa018f11424c5500c60eb98c0aa643525c0534cb2183ae6302a910d517014d318870731ac52a2438598d619512183ae6302a890c2d72d97434861ab8ecba1a430e1c16550d21a32e029a8690d497014d3248670b80c299243075cf6550521aa2e029a6290ce17018931486a23aa6498a4391195324c52183ae7326a090c1d731815408706a9ac5a18438554d61d0c21e0aa7a0a4210f05535052108782a9e8490843c154d4248421a4aeb3224210d85739912108693baac890843585c35348421a8aeb29a4210f065454d2108782aa2a690843c19d15348421e0ae8a9a4210f066454d2108782b22a690843295db4348421e0aa7a1a4210f055350d21087a0a9a4328043465cc649402183ae6322a010f22544855008790aa242a8043d094d2154021e82a690aa010d19731915008694b9686a80434c5c74354021e468290aa010f21414855008791a1242a8043c85092154021e44e890aa010f21744855008791b2242a8043c81912154021e468690aa010f2143485500861bb8aca9948183595320ca40d0a64b086520689325803290217b92ca98c8185595310c640d0ac4988632069131580319020fb9aca90c81895952108640d0ac690843206a1215802190306b10c4a9881459c46254c40a2ae2312a62051a701895310287390c2a9881435c86154c40c2ac230aa62051a701855310287390c0a9881435c86054c40a2ce2302a620515711815310306a9cc4298818354d6214c40c2aa7308a62061553584531030aa9cc3a90818594d61d4840c2aa6b0ea42052571d4e521029338ea6a9081495c75354840a1aeb29aa42042e7614d5210287398a6a9081499c45354840a4ae229aa42052a7014d5210306b18c6a9081499c46354840a4ae231aa42052a7018d5210287398c2a9081435cc6154840c4ac230aa42052a701855210287398c0a9081435cc6054840a4ce2302a42052571181521020fbb2a6290818354e6214840c1cc6a90a42060d63548521030aa9cc2290818954a6114840c2aa6b08a42062552584521030ca9cc0290810d5c665cc84086ae332c6420435719943210286baa641908183595320c84086aeb3086420615539843210312a94c2190818554d610c840c4aa4b08642068532584321030ca9cc0190818a54a600c840c32a6b006420629525803210344992c0190818354e62d4440c1ca6b16a22060d5358b5110306b1ca5a88818398d52d4440c1ac6a96a22052572d4e
  | 3 => 0x18c0dd080000000000015400079c00000354000000ec000678000002c6000cd8fb4922b9090ed0006dc89072068750001280001f00002c0004600015a0b2000708001fe000001cf08c00000066000000000004420010e800242754328001c6914000003fc0000020f3ca0010b03b2a664c660000f20c07284902c5f4c78001ee000000003160000002d0000003da350001409f0000000e4000000a20000019024000000189356544000632ce538000000000000021715629c0000001a000ad8002262cc20000000000da0000ee3b8000692944b0b78900001085b83308e0000000000046cd2124000000004008000000040180200000c020010080040180300200400000004010058010040000080000000001000000004000020020040000000c0240080200602400001000000008060060080080700000001802008000000020040000000000200401006002004048040000000000500600000001000004010020020200100200001400002004008000030000080100100000c02801000008000000000000180100201800001000000008010000200100300000000003006000000010040180000000a008010010000000080100000400007000000010000000000100100000000004000000008040000040200100a01400000002000000000080040000000a0240080800000000001000000004357118152d0e16b90c0a8e878958a6114143c4cc4b08a0a1e25625845050e1ab88c0a9e85075cc6054742c2ac7308a0a1616635845050b0ab1ac2282850d5c4605533286ae2302a91961563986544cb12b14c32a2650d5c4605513286ae3326a09943571181540ca86bacc899065615c6644c832a1eeab226419706544c9510cb82aa264a8865c1d093254432e0a84992a219707434c9510cb82a1a64a8865c19d13254432e0ae8992a219706644c9510cb82b2264a8865d04c95194032a62e2324a01943571191500cb852a264a8065c25513254032e826528aa01974132545500ca98b88c8a8065c2d093254032e1284992a01970b434c9500cb84a1a64a8065c29d13254032e12e8992a01970b644c9500cb8432264a80650b5c86054f4183ae6302a5a0d0d754c832d070aa9ac21968389549610cb41d0a64b0865a0e195358032d0714a92c019683a24c9600cb41962e030a64a0e85325843250744992c0192838358e6214141c1cc6b10a0a0e0d635885050616b90c0aa6630b5c86055231c1ac7314a898e2662586544c616b90c0aa2634a5c05250931a92e02926498cd170185324c616b94c9a82630b5c86055031c1ac6a968418e2552587420c782a968298863c1549414c431e0e86a926218f0543549310c68abacc898863615ca644c431a2eeab226218f0654549310c782aa2a498863c19d1524c431e0ae8a926218f0664549310c782b22
  | 4 => 0x40000508002190000005a800000000b9a13000868af097360288000000000000000000000000000000000e803519c000089582da3cc0000000000000010000000000000000000000000039000000164890f700047e6f001068000000b51f30000000018a340000218000007e000000000000000000000006c06f34c000000004105a0b280000001c000001020000000013086c4008e000000b58000000000000037e0004d0000001a85692241800116947000000002034941d0140d424c001118000000008196c00028cf40000000000000c0007c800000000644000ac00091c0002235e234980000000000005b37c000000002962847e000000000000cb000000ac8df1125e914894000000888000005ec0000000000000000000000b200000004c001b543c1604f000000000000000000008300000031d180540000000008248c30c14a43000400ec80037409c7e8000745e02412300035c2a9693380011704a000090640000000000017c000000001290000000001d0c4000000950060e02b18200050ceb82339400000179398000c08001100000000017017c000000000000a0002a400036800000000579c5396000b117f16c5c80020b0002a4b00003640001780531c4109e8c00000004c8000000000000011e000000db4220011ba0000020cb889c040000c307500015cef9553a40002d0000000003712e23a0f42582e0004280008a000000000000000000000013a064000000000011d8003ea8606213409e000d39c429a49cce87d3f2000839dd3ec0006e800000738f58ea0bc61c00a28000174000003d20000000017a70c8701b000000000000000680000041c00035800262000ef000428388c000000000000156000000000e6402000000860000004f8003525202600025e00000000000000000001b40011a07f2be0005010500000000000000000000002128f4f88000007449d800472000000003060d80016e00800000000000001110000000785803f288000ff80023c000f8199392000001d80000000022c000000000000000000000000000106800000654d40000000005e0000001f8000000004200022b0006cd1998d0003ac000002fc000001741f20004380000000000000000000000003de0000000017e0000e1c60007f000000000000000001c00007f0002ae824000c10008d87a800376348d718522e81cc4000000000000000000acca000216894c600006229800000470514000003cc000648701501906c800000000001771720608b10200c00000000474000001da1d04709580000000000000000000490000421e8459e2000000000000000010f80035a685211e33da3540000022071c00000000000b320500000000000000000000783e8000000003ee184001b8000000000002980007c00010a00004800000000b8000
  | 5 => 0x8a8000003e849800000720000001ac2a80000034600000000000000000001e2000000000000011900002a7f4000320003780012d292000000670008987a00012c00000000000000001fb4080000021c000000000000008f800000000000001bd00000000000000000000000000009b000000000001ec00078000000000000000003f46480024848065c0000000005c0013c0a400000044000464c20000784e8e005317c53c610002b82d0001e14405409b8083b82902680038400073800108910000710006680000036c000000000000000014124a00000000000000000000004d4778ca01c1b06e0003580000014603e4352092a01647c002022ea0000010c000574050000ec314001e40007340002a00043c6800045e0000000004a3c8e980027000000000000244001ea00075852a0602403c000000002c4d88000003440011a228000000cf0000000000000000000000000000000002024cc9c8000000000019600076cdc8000c07040008c2c289c0000008a660cf800000000698002ec0001f000000001050264780000007309c00000000454694000000000009f80034400066a1500000000041000000000f6000000002310000002e1321e00005d8e900026c5d1
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xd1686800c048ea0909998249b028509000007831611000005948f800b8011800008990000001300240000001e8000001c1a80000b00060d8f1f899e000c8010200000260022950000172380001783958e1d9f0408000a8026800012071ba5a181989412a3139d00821a250021221c8a010081002010504241810004080100048f1208001000d005a05869d13254432b01819d13254032b01811913254032a05854c9610cb41a09854c9600cb4190587991524c431c057654b424c431b01829d13154031b0182191315403191187d093154031905879915348421c057654f4348421b01839d12154021b0183191215402192187d0d2154021c05625c46254c40c05725846154c40c05635c46354840c05735846154840a05854c9610c840a09854c9600c840c05635c86354440c05735886254440c05764c83254440d01325c03254440c0575589310c440a0586549310c440a11854c5600c440e01524c5600c440c057558d2108440a058654d2108440a21854856008440e01534856008440c81729c46050d30c82725c46050d30c81725c46050d30891811c163d0930891811c164cc930891811c1644c930889821c163d0530889821c164cc530889821c1644c530d01525c4404c030d0172544404c030911811d5434c2208a1811c162d0d20c81739c46050920c82735c46050920c81735c460509208a1811c1648c9208a1811c1644c920889831c162d0520889831c164c8520889831c164485208a1811d9428c120908855d1324c1209098754c4048020d01535c44048020d01735444048020909821d5434c210909831d542482108a1821c161d0d10891831c161d0910c81739c86050510c82735c86050510c81735c860505108a1821c1648c5108a1821c1644c510891831c16488510891831c164485108a1821d9418c110910855d1314c110891831d94188110920855d121481109118754c4044010d01535c84044010921875484044010d01735484044010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1074
  | 4 => 1930
  | 3 => 587
  | 2 => 78
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
  | 6 => packedAt s5K6 (864+((h/16+packedAt s5K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s5K5 (32936+((h/358+packedAt s5K5 (28998+(h % 358)*11) 11) % 1289)*12) 12
  | 4 => packedAt s5K4 (81056+((h/643+packedAt s5K4 (73340+(h % 643)*12) 12) % 2317)*12) 12
  | 3 => packedAt s5K3 (30908+((h/195+packedAt s5K3 (28763+(h % 195)*11) 11) % 1246)*11) 11
  | 2 => packedAt s5K2 (4862+((h/26+packedAt s5K2 (4680+(h % 26)*7) 7) % 113)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc3cf3f9fff0e38fc7e318f8ffc71c7c784f0cf
  | 1 => 0xfc0fc7e38ff03f1f8fc1f1f1c381f9f99b4333
  | 2 => 0xfff007fc0fffc01ff1fe01fe03fe01fe638c3c
  | 3 => 0xfffff8000fffffe001fffe0003fffe007c0fc0
  | 4 => 0xfffffffff000000001fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x410080010041008000020240104040001045
  | 1 => 0x44221108122090281040909088809091094112
  | 2 => 0x8880a201244402500292012411240124228428
  | 3 => 0x11040052488820012525240022492400540a80
  | 4 => 0xe228b45b00ed349a49f9c9c9380c34357fe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36308
namespace PEqualNP.Outside.L_meta_36308
open PEqualNP.Outside.L_meta_36308.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x40a900b919a1b16109a8000030580079100209408a11e920f821915000000008d9f02929480068e0013818d0b050c99848e9b9f89011793000700099c8008060c001d98000a1c03989596a197201d1e0f050400103800e00005040c08300040060e2000301ffd5007fe5401ff55007fc54017fd4c057f53017f94c05fd53015f54c05fc53017fd0c05bf43017f90c05fd43016f50c05fc4300ffd48037f5200ff94803fd5200df54803fc5200ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803fe3200ff4c803fc32027fd4409fe51027f54409fc5101ffd0407fe4101ff50407fc41017fcc405fe31017f4c405fc3100ffc8403fe2100ff48403fc21027fd4009fe50027f54009fc5001ffd0007fe4001ff50007fc40017fcc005fe30017f4c005fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x22200dff1911001df8c888037bc64440075e322200dffd511006ffca888037fd544401bfe2a2200cffd8d10065fec688033fe63440057f31a200cff58d10065fac688033fc63440057e31a200cffd4d10066fea688033fe5344019fea9a200cdf54d10067f8a688033ff4344019dfa1a200cff90d10067fa8688033bd4344019fe21a200bffd891005dfec48802ffe62440037f312200bff5891005dfac48802ffc62440037e312200bffd491005efea48802ffe5244017fea92200bdf5491005ff8a48802fff4244017dfa12200bff9091005ffa848802fbd4244017fe212200bffcc91005ffc648802ffd3244017fe192200effd451002ffca28803bf6514401dfea8a200efd5451002ff8a288037ff414400bff20a200dfd9051006ffa8288037f5414400bfe20a200cffcc51002ffc6288033f63144019fe98a200cfd4c51002ff8628802fff214400bff10a200bfd8851005ffa428802ff5214400bfe10a200effd4110037fca08803bfd504400dfe282200dffd0110037fc8088037fd404400dfe202200cffcc110037fc6088033fa3044019fe982200cfe4c110037f8608802fff204400dff102200bfe8811005ffa408802ff9204400dfe1022005ffc411002ff6208801bfe104400dfb0822006ffd9410035feca0801bfe65040097f3282006df99410024fcca0801bfd65040157eb282006df59410004faca0801bfc650400d7e3282006ffd9010035fec80801bfe64040077f3202006ef9901001d7cc80801bfd64040137eb202006ef590100057ac80801bfc640400d7e3202009ffd501004ffca808027fd5404013fe2a02006ffd8c10035fec60801bfe63040057f3182006f798c10015bcc60801bfd63040117eb182006f758c10005bac60801bfc630400d7e3182008ffd4c10046fea608023fe5304011fea982008df54c10047f8a608023ff4304011dfa182008ff90c10047fa8608023bd4304011fe2182006ffd8810035fec40801bfe62040037f3102006fb9881000ddcc40801bfd620400f7eb102006fb58810005dac40801bfc620400d7e3102007ffd481003efea40801ffe520400ffea902007df5481003ff8a40801fff420400fdfa102007ff9081003ffa840801fbd420400ffe2102007ffcc81003ffc640801ffd320400ffe1902005bf9841002ffea208017fe510400bfea882005ff1441002ffe8208017fe410400bfea082005ff1041002ffe6208017fe310400bfe9882005ff0c41002ffe4208017fe210400bfe9082005ff08410035fcc00801bff500400dff2802006ff54010037f8a00801bff400400dff2002006ff50010037f8800801bff300400dff1802006ff4c010037f8600801bff200400dff1002006ff48010037f8400801bff100400dfb8802006ff84010037f4200801bfd100400dfa8802005fe44010
  | 1 => 0x6fc65c400bffb262005bfd931002ffcc98800efe64c400bfeb262015bf5931002ff8c988016fc64c402bffaa62015ff953100affaa988057fc54c400bffb1e2005bfd8f1002ffcc78800afe63c400bfeb1e2014bf58f1002ff8c788016fc63c4029ffa9e2014dfd4f100a7fca788053fd53c4029bea9e2014ff14f100a7fe8788053bf43c4029ff21e2014ff50f100a77a8788053fc43c400bffb162005bfd8b1002ffcc588006fe62c400bfeb162013bf58b1002ff8c588016fc62c4027ffa962013dfd4b1009ffca58804ffd52c4027bea962013ff14b1009ffe858804fbf42c4027ff2162013ff50b1009f7a858804ffc42c4027ff9962013ff8cb1009ffa658804ffc32c400bffa8e2005ff9471002feca388017fd51c402dfaa8e2005ff1471002ffe8388017fe41c400bfb20e2005ff507100afea8388017fc41c400bff98e2005ff8c71002fec6388017fd31c4029fa98e2005ff0c71002ffe4388017fe21c400bfb10e2005ff4871009fea4388017fc21c402dffa862006ff943100b7faa18801bfc50c402bffa062006ff903100affa818801bfc40c4029ff9862006ff8c3100a7fa618801bfc30c4027ff9062006ff8831009ffa418801bfc20c400dffb2c2006bfd9610037fccb08012fe658400dfeb2c2012bf59610037f8cb0801afc658400dffb242006bfd9210037fcc90800efe648400dfeb242011bf59210037f8c90801afc6484023ffaa42011ff9521008ffaa908047fc548400dffb1c2006bfd8e10037fcc70800afe638400dfeb1c2010bf58e10037f8c70801afc6384021ffa9c2010dfd4e10087fca708043fd5384021bea9c2010ff14e10087fe8708043bf4384021ff21c2010ff50e100877a8708043fc438400dffb142006bfd8a10037fcc508006fe628400dfeb14200fbf58a10037f8c50801afc628401fffa94200fdfd4a1007ffca50803ffd528401fbea94200fff14a1007ffe850803fbf428401fff214200fff50a1007f7a850803ffc428401fff994200fff8ca1007ffa650803ffc32840177eb0c2012ffd461002ffca30804bfd518400bfe28c2011ffd061002ffc8308047fd418400bfe20c2010ffcc61002ffc6308043fd318400bfe18c200fffc861002ffc430803ffd218400bfe10c2006bf98210037fea10801bfe508400dfea842006ff14210037fe810801bfe408400dfea042006ff10210037fe610801bfe308400dfd1842006ff4c210087f2610801bfc308400dff9042006ff88210037f4410801bfd208401ffc9042006ff08210037fe210801bf7108400bfd884200effd9510075feca880037f65440013fb2a200eff99510025fcca8803bfd654401d7eb2a200eff19510025f8ca8803b7c65440093e32a200dffd911006dfec888003bf64440015fb22200dff9911001dfcc888037fd644401b7eb
  | 2 => 0x1467b918d40d81f8009f0687100097800740ae211662c81e0a2d254974000003b000000004d0f66da9e1c01a35800000000022a641409e0fc0032c000b881878001a2208026c2481d03ca51b8dd800111608d0c8001e200000be05c9faca000005a3482d8009c930449eac60ea471a4000004399e1cb04001706ea921d93c31a42683520eae624b80c4b421f2f200058002109280018a004d80a69842003623920a001bc50a96000000000094800048047f15c6f8202fb1ab3ae2cb9a80007a3c000000f2002c4dc21eb00004c80038800de32242226002ee0016271958ac232000088f9c02800062800000000013e3bae8bd280001ae2f000d329874800720001b102c3b824521c7da580e30a030000023a26800229d60002e9b09c91010892ac0000079000b9000000543d1d4c50262e88c95198141d8ac9f080a903333c1a82adc85ebc358002820016cdea9a158000000000000002b86b0004b800b18f81025aaa36064800608000000000194768fe9e80032800d3954000d000000000009389408aae61064d2a56a38006aa1a7991a5a9ec47a6457a74002a0c927655aaa0000033800003060031e99a367735e000364e818b8030d120c0028c052b6cd35ad1a080024c00000370000000000240590008e1160018c000000033600000d7000002ccc7222d904e002d0058000033072aa200000c4308002460003e000003680003a04bb1224b10a9b92800000410000000073000000000017aa100052326000342380000000df000b233ec586e000000014c00000129f286212db1505f9f83a17c41924000000000000000130003500000000241380c9b2430fab7adab52ba25abe118e660286cc800073668c328002fa4a986da288881f400354980a87a05a5b8002b2a466afe528a4001b400302000000000000000af0d253ad60002c7e800df8e0002509a19c85aea638a649800620aaad000dba2c220a277944440005d800002dcce0000000037800000008baa6a295a9880000320c000600086001e0bf048caa148a2705e25cda82427a6a00066481fe00000d58001480000000a70c44023cb60002000000000002f62d098d0000002c22c0c0ce8000000070800001ce658070080200c00000190000103c010340a0000201c0701000000010000b03000014060000600c020080e000000080400003014020000601803010000000000c000000000002008000080505c000100000c0003005024020000200c04004010000200c05000000200100813024000140101801000040080b02005008070000001809020000080400000004030000d0040708c0200c0201401008000000002005004020040700000000000080c00014000030080001c0000c00014010200bffb2e2005bfd971002ffccb88012fe65c400bfeb2e2016bf5971002ff8cb8801
  | 3 => 0x3080083b0c18172003740
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc315901002ebf215901002ebe215901002ebd215901002ebc2159010036bf7059010036be7059010036bd7059010036bc7059010036bf5059010036be5059010036bd5059010036bc5059010036bf3059010036be3059010036bd3059010036bc3059010036bf2059010036be2059010036bd2059010036bc2059010036bf1059010036b71059010036be1059010036bd1059010036b51059010036bc1059010006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c100069e7458c10006dd7458c100069d7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c100065f5258c10006de5258c10006dd5258c100065d5258c10006dc5258c10006df4258c100069f4258c10006de4258c10006dd4258c100069d4258c10006dc4258c1002edf7158c1002ede7158c1002edd7158c1002edc7158c1002edf5158c1002ede5158c1002edd5158c1002edc5158c1002edf4158c1002ede4158c1002edd4158c1002edc4158c1002edf2158c1002ede2158c1002edd2158c1002edc2158c10036df7058c10036de7058c10036dd7058c10036dc7058c10036df5058c10036de5058c10036dd5058c10036dc5058c10036df4058c10036de4058c10036dd4058c10036dc4058c10036df2058c10036de2058c10036dd2058c10036dc2058c10036df1058c10036d71058c10036de1058c10036da1058c10036dd1058c10036d51058c1002ed91058c10036dc1058c10006ef7558810006ee75588100066e7558810006ed75588100066d7558810006ec7558810006ef7458810006ee7458810006ae7458810006ed7458810006ad7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006af4358810006ee4358810006ed4358810006ad4358810006ec435881002eef715881002eee715881002eed715881002eec715881002eef515881002eee515881002eed515881002eec515881002eef415881002eee415881002eed415881002eec415881002eef315881002eee315881002eed315881002eec3158810036ef7058810036ee7058810036ed7058810036ec7058810036ef5058810036ee5058810036ed5058810036ec5058810036ef4058810036ee4058810036ed4058810036ec4058810036ef3058810036ee3058810036ed3058810036ec3058810036ef1058810036e71058810036ee1058810036ea1058810036ed1058810036e5105881002ee91058810036ec1058810
  | 1 => 0x91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d91100063d52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d91100bebf71d91100c6be71d911006ebd71d91100c6bc71d9110006bf51d91100c6be51d9110006bd51d91100c6bc51d9110006bf31d91100c6be31d9110006bd31d91100c6bc31d9110006bf21d91100c6be21d9110006bd21d91100c6bc21d91100c6bf70d91100bebe70d911006ebd70d91100bebc70d9110006bf50d91100bebe50d9110006bd50d91100bebc50d9110006bf30d91100bebe30d9110006bd30d91100bebc30d9110006bf20d91100bebe20d9110006bd20d91100bebc20d91100c6bf10d91100bebe10d911006ebd10d91100bebc10d91100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100063f43594100067e43594100067d43594100063d43594100067c43594100067f72594100047f72594100067e72594100067d72594100047d72594100067c72594100067f42594100063f42594100067e42594100067d42594100063d42594100067c42594100067f32594100067e32594100067d32594100067c325941002e7f715941002e7e715941002e7d715941002e7c715941002e7f415941002e7e415941002e7d415941002e7c415941002e7f315941002e7e315941002e7d315941002e7c315941002e7f215941002e7e215941002e7d215941002e7c21594100367f70594100367e70594100367d70594100367c70594100367f40594100367e40594100367d40594100367c40594100367f30594100367e30594100367d30594100367c30594100367f20594100367e20594100367d20594100367c20594100367f10594100367710594100367e10594100367d10594100367510594100367c1059410006bf7559010006be7559010006bd7559010006bc7559010006bf7359010004bf7359010006be7359010006bd7359010004bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd53590100063d5359010006bc5359010006bf7259010004bf7259010006be7259010006bd7259010004bd7259010006bc7259010006bf52590100063f5259010006be5259010006bd52590100063d5259010006bc5259010006bf3259010006be3259010006bd3259010006bc325901002ebf715901002ebe715901002ebd715901002ebc715901002ebf515901002ebe515901002ebd515901002ebc515901002ebf315901002ebe315901002ebd315901002eb
  | 2 => 0xa0180000001010000100a0041d000080000f0041300c0c00800030050080d00000014030100100c000080200c0200c000757e76d95100767e76d95100247e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100073f43d95100073d43d95100057f72d95100057d72d95100067f62d95100067e62d95100067d62d95100067c62d95100073f42d95100073d42d95100cf7771d95100777471d95100077641d95100077541d95100077631d95100077531d95100077621d95100077521d95100077a30d95100077930d95100077a20d95100077920d95100d77b10d95100cf7610d95100cf7410d95100d77810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100063f43d95100067e43d95100067d43d95100063d43d95100067c43d95100067f72d95100047f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100063f42d95100067e42d95100067d42d95100063d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100ce7f71d95100d67e71d95100767d71d95100d67c71d95100067f41d95100d67e41d95100067d41d95100d67c41d95100067f31d95100d67e31d95100067d31d95100d67c31d95100067f21d95100d67e21d95100067d21d95100d67c21d95100d67f70d95100ce7e70d95100767d70d95100ce7c70d95100067f40d95100ce7e40d95100067d40d95100ce7c40d95100067f30d95100ce7e30d95100067d30d95100ce7c30d95100067f20d95100ce7e20d95100067d20d95100ce7c20d95100d67f10d95100ce7e10d95100767d10d95100ce7c10d951006dbe76d911006ebe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110005bf73d9110005bd73d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100073f53d91100073d53d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006bc62d91100073f52d91100073d52d91100bfb771d911006fb471d9110007b651d9110007b551d9110007b631d9110007b531d9110007b621d9110007b521d9110007ba30d9110007b930d9110007ba20d9110007b920d91100c7bb10d91100bfb610d91100bfb410d91100c7b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110004bf73d9110006be73d9110006bd73d9110004bd73d9110006bc73d9110006bf53d
  | 3 => 0x800020a2c0027e2b95a0000000000ae8ac7432000000fa0a61503e0000000094b391c6f16eb1820e333c000eca183478264db000673505a17a7691a000003600089800db84ee91a86b0a2a0130eb2f081218002aad0800aa01e043640018e0019000000550000002e328e653a140021e838009d01c0129ed7800480000038e3a00000200e4b9a00358000007590a000c4cc04cda05c00220002ac953560a800001c2fa80000000000007d9b0ac83a7a0007500000000c21160a142000004dad0b8000e624c871ee62270cdaeca9b722a962f41185d8d45e124c423c38abe79394002c2a1000c00928f800c12fcd68b800230c6800003067796a1232aae3ae9cba01913c6e0b4738fe94b9c19b627031c41158fb2fe2138062800000005481a6f800001ae34000b9000111cc9e00000000003de4b00000800439348da6a52800000dc001320009a00000f989e00174001bad4bc24880021824220fc0000000388000000007400000001f4deb48ea206632c034862ef0007a80a47be49392ea6040b5800332ca77208002942cb789805200292052b0c2b2ca41147fa5c23bb48b9660387c36b389686cc3908cf948f68000000040800001f83e8000000000000202b6543c00037c1bb2e27172e2800a70000019810b9eba112809cabc96c0f22808a9a2f906000000005af719665000000c00008add3c623032b3146032f83d21658000000a8000723d8002f06a840000026ee58000b28200000f5800b7a8e0000000000000000000000000efbaa892d200000e407697a3250016ed8009e800fb800d31a6001b2003609137061a2a7f376001b6710009a314062a4a8bb00015c86800001829899200000003225c0008e0000030200000b689837926000ea7c9380012a000008d000001ecd1800000003cb40001d2be800df80043068eeb1688800610000036af395e000a4001e284a7cb200000000002560013e003e0000000000000000e1000929a4f603630a8a8e8006d000a33664027655af62400002000e9a96390000000000386831f0b135c71bccca000002eaab9c8001d8d3a6cc6128999aa00000943d400000c4800680e00c3a217860f20784e8b6532403bad8d504ae0ab42e8f85fae2b98700033ac3050b70f0d28c835be2920965f16400000bd00000000b524600000d10260007a00258c98006005600288678cec7bb8002ee03c010481e00c0a028000482100013000060680701c090080200003024000140000404018000000200004000010340500800004000180700c01004010180501802010000140200c070040500c0904002028000000e000010001300802000000140001c01000030141202c000000300c00004020000a000010000200c0301407000000041800c00004050d011048000040005800014000040000c1c01c00010000040
  | 4 => 0x3c468800f487e44000cd1442c00004800ecaa0c90000005811bca00242af332001e6000c60000000000001fa01a0a000380019a2
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe1d52d096304047d2e21a12c60808fa68434258c1011f4a88684b182026e9910d0963040014bd0b212c608002976164258c1012d4ec2484b182000a9f87509630400153b0ea12c608003879d54258c100070ebaa84b182000e8f825096304001c3ea4a12c608003875494258c1012f4790284b182025e8d20509630404bd2e20a12c608097a68414258c1012f4a88284b182024e991050963040014bd0a212c608002976144258c1011d4f42084b182000aae84dd5620400155b09baac4080a69b61e755881000536c1ceab102027e67109d5620404fcd4213aac40809f99442755881015734884eab102000c6f875d562040014df06baac4080a71bdc1755881014e36b82eab102029e67105d56204053cd420baac4080a799441755881014734882eab102027a6e851d5620400155d083aac408002ab61075588100053742ee8b102000a6d85dd1620404b55b0f3a2c4080038b9d6745881000716bace8b102000aad839d16204047d4e213a2c40808faa842745881011f52884e8b102026ea9109d1620400195f0eba2c4080038b9d5745881000716baae8b102000aaf835d1620404b95ee0ba2c4080972b5c1745881012f53882e8b102025eaa105d1620404bd4a20ba2c408093aa441745881000537428e8b102000a6d851d1620404755d083a2c4080038bd52545881000716aa0a8b102000a6e85dcd62040014db0bb9ac408002aba13735881000556c26e6b102000a6e859cd62040014db0b39ac408002aba12735881000556c24e6b102000a6e851cd62040014db0a39ac408002aba10735881000556c20e6b102000ccd731cd620400b5cd0239ac40801eb9604735881003575400e6b102007ae9801cd62040014df0fa9ac4080029b61f5358810007173a6a6b102000e2d74d4d620403fcce21a9ac40807f9a84353588100ff32886a6b102022e6910d4d62040434db0b29ac408002aba12535881000556c24a6b102000a6f8754d62040014db0ea9ac4080038b9d1535881000716ba2a6b102000e4f8354d6204043c9e60a9ac408087934c1535881010f33882a6b102021e6a1054d6204043cca20a9ac4080839a44153588100fd37428a6b102000aae8414d620400155b0829ac408002abe1f435881000556c3e86b102000e2e75d0d6204001c5aeba1ac4080038bd4f435881000716a9e86b10201bea710d0d6204037d5421a1ac40806fa944343588100f75488686b102000a6e8590d62040014db0b21ac408076ab612435881000557c3a86b102000aad8750d6204001c5ceaa1ac4080038b5d5435881000747c1a86b102000e2f5350d6204001c5aa6a1ac408077a3cc143588100ef4698286b10201dea71050d620403bd5420a1ac408077a944143588100e75488286b102000a6e8510d62040014db0a21ac40806eaba104358810
  | 1 => 0xa20b92c80808e2fa1c72590100051f428e4b202000a3d851c9640400147b07a92c8080030fdcf52590100061eb9ea4b202000c3f72d49640400187ae5a92c80809f8dc43525901013f1a886a4b2020008be87949640400117b0f292c8080a68f61652590100051fc1aa4b202000c3f73549640400187ae6a92c8080038be0952590100061fb92a4b202000c3d725496404053c5e40a92c8080a78b481525901014f1b882a4b202029e3510549640400117d0e292c8080022f61c525901013d1f428a4b2020008be87cc9640400117b0f992c8080028fa1732590100051ec2e64b2020008be878c9640400117b0f192c8080028fa1632590100051ec2c64b2020008be874c9640400117b0e992c8080028fa1532590100051ec2a64b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202000e8d320c9640400b56d02192c808002ad60432590100355d40064b202000ab9800c9640400153d09baac608002a76137558c1010d2ec3ceab182000a5d829d5630403fcae213aac60807f968427558c100ff2a884eab182022e59109d563040018bf0ebaac60800297e097558c1010e2fb82eab182021c5d705d56304043cae20baac608087968417558c1010f2a882eab182020e59105d5630403f4bd0a3aac608002a7a107558c100054ec20eab182000a5e85dd163040014bb0bba2c608076a761e7458c100070f3ace8b182000e1d759d1630400153b053a2c60806fa5c427458c100df4d084e8b18201be95109d1630403dd32213a2c60800327e1d7458c100070f3aae8b182000e1d755d1630400153f04ba2c60807727dc17458c100ee4eb82e8b18201de97105d1630403bd3420ba2c608077a54417458c100e74c882e8b182000a5e851d163040014bb0a3a2c60806ea7a107458c100070faa4a8b182000e1d5415163040014bd0bb92c608002976177258c100054f426e4b182000a9d84dc963040014bd0b392c608002976167258c100054f424e4b182000a9d849c963040014bd0a392c608002976147258c100054f420e4b182000a9d841c9630400199ae4392c608016b5a047258c100456ac08e4b182006ada801c963040115b300392c60800297e1f5258c100052ec3ea4b182000e1e74d496304001c3ae9a92c60809f95c435258c1013f2d086a4b182027e5510d496304055cb221a92c6080a6976165258c100054f424a4b182000a9d8494963040014bf0ea92c6080029761d5258c100070f3a2a4b182000e1d745496304001c9f04a92c6080a793c815258c1014f26902a4b182029e57105496304053cb420a92c6080a7954415258c101472c882a4b182027a5e85149630400153d08292c608002a76105258c100054fc3e84b182000a9d87d096304001c3ceba12c608003875d74258c100070fa9684b182000
  | 2 => 0x373594100fe3a886e6b28202187d879cd650400147d0939aca080028f61273594100062fc1ae6b28200087f825cd65040438ee20b9aca080871d44173594100fc3f438e6b282000a3e841cd650400147b0839aca080030fdcf43594100061eb9e86b282000a3d82d0d6504037c6e21a1aca0806f8d44343594100043f43c86b28200087d8790d650403b47b0921aca0800387e0d43594100061fb9a86b282000c3d7350d650400147f04a1aca0807787cc143594100ef0e98286b28201de371050d650403bc6a20a1aca080021fa1c43594100043ec3886b28201ba3e8410d65040010fb07b92ca080030fd0f72594100061ea1ee4b282027c7710dc9650404f8ea21b92ca080a61f61e72594100051f424e4b282000a3d849c965040010ff06b92ca080030fd0d72594100061ea1ae4b282000c6f825c965040538ee20b92ca080a71d441725941013c3f438e4b282000a3e841c9650400147b08392ca080028f60f42594100061fb9e84b282000c3d73d09650400187ee5a12ca080030f5cb425941011f1b88684b282023e3510d0965040010fd0f212ca080021f61e425941012d1ec2484b282000a3f83509650400187ee6a12ca080030f5cd425941000717c1284b282000c3f72509650400187ae4a12ca080978bc81425941012f1690284b282025e3710509650404bc6a20a12ca080021fa1c42594100043ec3884b282023a3e8410965040010fd0f992ca080021f61f32594100051f42664b282000a3d84cc965040010fd0f192ca080021f61e32594100051f42464b282000a3d848c965040010fd0e992ca080021f61d32594100051f42264b282000a3d844c965040010fd0e192ca080021f61c32594100051f42064b282000a3d840c96504001c9a64192ca080169da0432594100053ac0864b282006a7a800c965040014f300192ca080030fdd675590100061eba8eab2020008bd82dcd640403796e21b9ac80806f2d44373590100ec5ec3ce6b202000a3e859cd640400147b0b39ac80800327e0d73590100045fc12e6b20201dcb7105cd640403b96a20b9ac80806e2fa1c73590100051f428e6b202000a3d851cd640400187ee7a9ac8080030f5cf53590100051ec16a6b20201fe3710d4d640403fc6a21a9ac8080022fa1e53590100045ec3ca6b202021a3d8594d6404001c3f06a9ac8080030fdcd53590100061eb9aa6b202000a3f8254d6404043c3e60a9ac808087874c1535901010f1b882a6b202021e351054d640400117d0e29ac8080022f61c53590100fd1f428a6b2020008bd83dc9640400187ea7b92c8080030f54f725901011e5b886e4b202023cb510dc9640404b17b0f392c8080028fa1672590100051ec2ce4b2020008bf835c9640400187ea6b92c8080030f54d725901000657c12e4b202025cb7105c9640404b96
  | 3 => 0x3b222017ab4864c76444001d28c698ec88805ead21921d91100075231243b222018ab8864c36444001b36e6986c888003c654d30d9110007c898a61b222018ab8864836444001b56e4906c888003ca54920d9110007d090a41b222000c3f759d7644400187aea3aec888062ada0475d91100bd5ac08ebb2220008bd82dcf644400117b0f39ec8880028fa1673d91100051ec2ce7b222000c9f835cf644400117f04b9ec8880022fa1c73d91100051f428e7b222000a3d851cf644400155d0439ec888002ab60873d91100c55b408e7b222017ab5811cf644402f5750039ec888062ae60073d91100061fb9ea7b222000c3d73d4f644400147b05a9ec8880022fa1e53d91100045ec3ca7b22202fa3d8594f6444001c3f06a9ec8880030fdcd53d91100061eb9aa7b222000a3f8254f644400117d0e29ec8880022f61c53d91101751f428a7b2220008bd83dcb644400187ea7b96c8880030f54f72d91100045ec3ce5b222000a3e859cb644400147b0b396c8880022fe0d72d91100061fa9ae5b222000c3d535cb644400195f04b96c8880022fa1c72d91100051f428e5b222000a3d851cb644400153d06396c888002a760c72d91100c55b408e5b222017ab5811cb644402f57500396c888062ae60072d91100051ec1ea5b222000c3f73d4b644400187ae7a96c8880030fdcb52d91100061eb96a5b2220008be8794b644400117b0f296c8880b68f61652d91100051fc1aa5b222000c3f7354b644400187ae6a96c8880038be0952d91100061fb92a5b222000c3d7254b644400117d0e296c8880022f61c52d91101651f428a5b2220008be87ccb644400117b0f996c8880028fa1732d91100051ec2e65b222000c9d73ccb644400117d0f196c8880022f61e32d91100051f42c65b222000a3d858cb644400195ae5196c8880022fa1d32d91100045ec3a65b222000a3e854cb644400147b0a996c888003275cd32d911000656b9265b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000e8d320cb644403156d02196c888002ad60432d91100bd5d40065b222000ab9800cb644402f17d0fa8ec8880022f61f51d91100bc5f43e63b2220008bd87cc7644400147d0b98ec8880028f61731d91100c74a18a63b2220178be87c87644400117b0f90ec8880028fa1721d91100051ec2e43b222018ea421487644405717f0ea86c8880622f21d50d91100c45f43e61b2220008bd87cc3644400147d0b986c8880028f61730d91100064fb9e61b222000e1d53cc3644400193ee6986c8880038754d30d91100c45f43e41b2220008bd87c83644400147d0b906c8880028f61720d911000657b9641b222000e2d52c83644400195ee4906c8880038b54920d91100061fba4e8b282000c3d741d165040010fb05b9aca0807f1dc4
  | 4 => 0x54400187ee7a16ca880030f5cf42d95100061fb9685b2a2000c3d72d0b65440010fd0f216ca880021f61e42d95101b51ec2485b2a2000a3f8350b654400187ee6a16ca880030f5cd42d951000717c1285b2a2000c3f7250b654400187ae4a16ca880021fa1c42d95100043ec3885b2a2035a3e8410b65440010fd0f996ca880021f61f32d95100051f42665b2a2000a3d84ccb65440018bae7996ca880021fa1e32d95100043ec3c65b2a2000a3e848cb654400147b09196ca880031b5ca32d95100043f43a65b2a200087d874cb654400147d08996ca880028f61132d95100062eb9a65b2a2000c6d724cb65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb6544001c9a64196ca8806a9da0432d95100053ac0865b2a2019a7a800cb65440014f300196ca880661fa1f41d95100043ec3e83b2a201987e87cc765440010fb0f98eca880028fa1331d95100051ec2663b2a201ae54314c765440330fd0f90eca880021f61f21d95100051f42643b2a2000a3d84c876544035cc84290eca880d21fe1d40d95100d43e43a81b2a201a87e87cc365440010fb0f986ca880028fa1330d95100051ec2661b2a2000c5f73cc36544001c3a87986ca8800317dcd30d95100070ea1a61b2a201a87e87c8365440010fb0f906ca880028fa1320d95100051ec2641b2a2000c6f72c836544001c5a85906ca880031bdc920d951000716a1241b2a2000c3e76d97644400147b07b2ec8880028f60b65d91100045ec3ccbb222000a3e85997644400117f0eb2ec8880028fa1865d91100061f3b0cbb222000a3d83197644400147b0432ec8880038d60465d91100045f436e7b222000c3f65dcf6444001878cbb9ec8880030fd9573d91100061e32ae7b2220038bf87d8f644400193ae7b1ec8880022f61e63d91100051f42cc7b222000a3d8598f644400117f0eb1ec8880028fe1563d91100051e42ac7b222000aaf8258f644400155904b1ec8880362f61c63d91100051f428c7b222000a3d8518f644400193ae631ec888002aba0863d911000556c10c7b222000a3e86d4f64440014790da9ec8880cf0f9db53d91100051f432a7b222000a3c8654f644406587ceca9ec8880022fa1b72d91100061fb2ee5b222000c3c65dcb644400187ecab96c8880030f19572d911001c5fc3ec5b222000cad72d8b644400117b0f316c8880028fa1662d91100051ec2cc5b2220008bf8758b644400147f0ab16c8880028f21562d91100054fc1ac5b222000a9c8358b644401b17b0e316c8880028fa1462d91100051ec28c5b222000a9e8318b644400153b06316c8880032b5c862d91100051f436a5b222000a3c86d4b644406387ceda96c8880028fa1952d91100051e432a5b222030c3e7654b644400136d0f28ec8880038d19651d91100bd5a432a
  | 5 => 0x8008000080000000100000400801000004000000080080000000200001000004008018070000000000300e00402805006000008000000040700100000401001000004018000020000000000000001001002004000000000000700000c0180200000000005800002010000000040100000000200002002006000008010060000000000200000000002010010fb0f326ca880021fe1d64d95100051ec18c9b2a2000a3d821936544001c6b02326ca880021fa1b73d95100061e326e7b2a2000c3c645cf65440090ff0fb1eca88003175cf63d95100043ec3cc7b2a2000a3e8498f654400147b0931eca880021fe1d63d95100051fc22c7b2a2000a3c8458f65440014df04b1eca880029b20963d95100743ec38c7b2a2000a3e8418f654400147b0831eca88003175cc63d951000537410c7b2a2000a6d8218f654400147d0da1eca880028f21b43d95101e61f3b687b2a2000a3c8650f654407787ceca1eca880021fa1b72d95100061e326e5b2a2000c3c645cb65440090ff0fb16ca880031b5cb62d95100043ec3cc5b2a2000a3e8498b654400147b09316ca880021fe1d62d95100051fc22c5b2a2000a3c8458b65440014bf06b16ca880029720d62d95100743ec38c5b2a2000a3e8418b654400147b08316ca8800297a0c62d95100052ec18c5b2a2000c6d7218b654400147d0da16ca880028f21b42d95101d61f3b685b2a2000a3c8650b654407387ceca16ca880025da1e41d95100071a32483b2a2019a748650765440334e90c98eca880039518d31d95100cd3a43243b2a2000e646248765440354f10c986ca8800356dcd30d95100078ca1a61b2a2000f51314c365440354f10c906ca880035adc920d951000794a1241b2a2000f6121483654400187ee93a6ca880030f5d074d95100d53b408e9b2a2019a75811d365440010fb05b9eca880021f61e73d95100051f424e7b2a2000a3d849cf65440018bf06b9eca880021fe0973d95100043f438e7b2a2000a3e841cf654400147b0839eca880029ba0873d951000536c10e7b2a201aa76811cf65440334eb0239eca880669ea0073d95100d53cc00e7b2a2000c3f73d0f654400187ae7a1eca880028f60b43d95100043f43c87b2a200087d8790f654407147b0921eca8800387e0d43d95100061fb9a87b2a2000c3d7350f654400147f04a1eca880021fa1c43d95100043ec3887b2a2037a3e8410f65440010fb07b96ca880030fd0f72d95100061ea1ee5b2a200087d879cb654400147d09396ca880028f61272d95100043fc1ae5b2a2000c3f435cb654400187a86b96ca880031be0972d95100043f438e5b2a2000a3e841cb654400147b08396ca8800297a0c72d95100052ec18e5b2a201aa76811cb65440334eb02396ca880669ea0072d95100d53cc00e5b2a2000a3d83d0b6
  | 6 => 0x56a00000000000000000001722a8899be2f4229769c005a000000000000013e8b50003a00019204800000000000c20000002cc000000770000002830e60c4b5661d7578000dd00a0006355c98717a40c540971005b591aee40667c0003e000c61260000000f0000205fa00000000000aa90a000496674ca0001a64c84200059a6b546a8a000564000000000d800000000000000000000000000004e2448e94c04216035000000164368000001b88003b5be000000a0000a842a9cf4f00006915800005c51ad70000005222500056800000522000f600030a000000000005109f8000000012e80022e0001c8c30000009780000000000173000338000000000000009300000000293462000001645e0420000000002c0000000000016580003c6f40010c000000dc9150000013380000077824000000c2800255000000001fd128000000000000000000036e00000000000000000253e2aac08ad631e000b500013c0000015e2720000018e4dc0000f8003568b457845490000a70005e62698a97d38e900c40000000000000051800039800000001969b02aeab07f0001f01d0c025805000000000000000d79cb4188f50515c000000000002ea0000008f000000170000000000000000000000000000450a0a370749656e9a23e4b1c430e200000000143000038f427a5d02d80000000000000000000000190ed05e0000026300000000000000001522462ac184001820f00000019b0303114b887634000888790000000000000000000213096bd8000001e8aa40008d000000000b2484a142123f248a40d018148200000247000000d3800000001190ae000478f48000007e58a3025660006a18a000854000000000014e8004a297c5c0b35a6c05751b32a814941b1f0000000002200000011b0d000a180025600003c0000036c0013dad93f40000011c0009c0001900007ec000005760000000000000129800000618000004c0770ff000000a380023019a000eb00025800000a0f1aaad80000000000000000000215681ca2dcb380029414c9411b1f31ee17d7625c0663400018300002c6e8004de3207d00057e8ac000000004591d0000000000000000000000800002000000000020020080000200001400001000000008030000000000100000403800002010000000000000000201201401005006000010030000080000100a000000020040000000200000000000002010000010020000100201c00000801000004010000000040200000200000003002000038000020040000000200000001002000010000020140000400000c00000004000008000000080000200200000000000000028010020080100000e01801801004004040010000200000000400002801000000010010000000000e004000008010040000000400400c060020000000100
  | 7 => 0xe154c3c44d800000000c480028a0117a800000000002e734a465612025d200060afc4d418c61210000000470000000000000038a00193800000070e687b024bd00000000000000000000000002f7000000000000008380021f0000013414926814c0e8e337088432316000aa10d1ee656c14000000000014e0f63e8000b88003769480000003200000000000794001e34bc0016d0000000006e0003d48253c8d10000ad3fa982964684c8000000015ba0125c358e1800000020942613329d4000002c24355180015200000000000000000003ecb140000000000000000000a1d901631ae6a00000042400000307432000000000007b400000000000000000009885b80020800087b1339c0013980001a67000000000000000000000000000000000073000000b60000000003182886f4e817400000000a880000024c000000003a4000000985940000028b0005949080000000048000000b94000000002ec1ea8200016ca800000000000000000654e20374ec3a8001d432c0000021d0001305e000000000760000000000000040a0000000000000000000000000001010001f8001f500004d3310a000000000006523140000000022c9e0000000000004d0000000022c000000002fe192000000002900000000000000000000000001068f53b405000000000418002c425200002b0921c0000000000c000000002e469000152000be98e000000328918000009691320000000000000000000001770000009e88136a000000cf000000fbaad068b003e17900046c2480046a000310005120005880000019400000362001100000cc000a3000000b0c49000000000f2000000000001700000000000059200000000000000b12be08c104001b2000000000000000000018c0ac00187b120001acaf8fc15895c001310000005f130000000fc18b0000000016c1420000014f1fa001910001f6798000004700000000007e8cc2b8540000000006c000000950006486a86c0003ce364002274d600074800000000000a20ce0690404300059d818ef3b002400218000910000003c400000000000000000001e40000027e492000001470000000032a560000000004f800000000204294938002a600000000000000000000005bc0000000000122a3c20e0088584a000b88000004545f14f8000f4000000003ba000998000004d9322e363a5282d1a35024e082b2c00039c00000000000f580000000000000452000000002ba000e9800138a810f2cf2440000000000093c202800000000027248620d93109000740271f0476a202784700000103a6500000000000000ae80030062ec2c780000000000a85c000494558160006d00017f000000ba197000000000000000018200000000000000000000fe0001e632cbc140198000001764e2000000000001d87c800
  | 8 => 0x448001d9532378000955f25083f896000000f780000000000000000a6934800000000000000c05ac7700049ca9414a0617e8882f2eb3784e8220e535800000155000000000000000006f875104abd172d22fc000000000000000000000000126ae15b6ad00028f1fe0006031b000001732c10000e1118004b66780000053c000001e0000368638000000011224a04c5a4001d1000001642950000019280052c7091f0000e4000000005b800000000000000b40004da0009f29264227570000334000000000000c11ca040000c400000650000000000000000000000022000089018000000ad0008440000038c00016000230000348000000d4001c9000ac972000000660e42f142caf4000000000009a800000000a69a654e73000000000000c98eb5bc0000000000047c001df000bfd860001c84ad8c8000e20015c0003aa8700000026e000000000000000000000000000000000000000000000000022f3826b93602a622000000a7000a10000000360000000000000000191000000002d45f0000000000007fc002ae000785588001688a00000000000000000620000d4ac663c000000005a2000000005aa9dcb00db220040000000000000000000001c000000004ec0000000000000000000bc80000000056c0000042e544000004a80000018400000000000468000000005f6000461a1000000000000000004faef0001a00187d000000000000e0000000000000005d00000000000000000a6cbd80000082c001bf24000000000436380ed8
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1b00000129b70e402c5e640040045ab006ac022500120d3a0000e0e2118a6480100527c7b12a9c0061684e006878bb30001b982698280020000012000000000d00000000000b8916000001420a800018b40838002000000008681105408004000030050764c64dcf654400184d7360863d95100050b64864dcb654400184d835c862d951000591648634c765440016459318921d95100d694219314c36544035a608648520d95100040fe61741d3654400142d92d0f72d951000607e0d435cb654400181d83dcf42d95100050be497350b654400184d874c832d9510006914c9810cb6544001a493260032d95100050764c65dcf644400188d7360863d91100050b64865dcb644400188d835c862d9110005a1648634c764440016859318921d91100c6a4219314c36444031aa08648520d91100040fe61751d7644400142d92d4f72d911000607e0d535cb644400181d83dcf52d91100050be497354b644400188d874c832d9110006a14c9810cb6444001a893260032d91100040fe61741d1650400181d8350f72594100050b64b435c9650400181d835cf42594100050b64b735096504001a45326043259410006924c9800c9650400103f985d475590100060760d53dc9640400142d92d4d72590100060760d73d49640400142d92dcd5259010006a14c9810c96404001a8932600325901000487e6154151630400181d875d35258c100058364a74549630400181d875d74258c100058364a75509630400122f98550545881000631605731cd62040018c9805cc73588100060b61d74d4d620400160d939d153588100060b61d75d0d620400160d939d54358810
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x1
  | 7 => 0x4b
  | 8 => 0x4c
  | 9 => 0x4d
  | 10 => 0x4e
  | 11 => 0x94b
  | 12 => 0x94c
  | 13 => 0x94d
  | 14 => 0x94e
  | 15 => 0x124b
  | 16 => 0x124c
  | 17 => 0x124d
  | 18 => 0x124e
  | 19 => 0x138b
  | 20 => 0x138c
  | 21 => 0x138d
  | 22 => 0x138e
  | 23 => 0x1489
  | 24 => 0x130a
  | 25 => 0x14c9
  | 26 => 0x134a
  | 27 => 0x18c9
  | 28 => 0xe8a
  | 29 => 0xe89
  | 30 => 0x18ca
  | 31 => 0x1a49
  | 32 => 0xeca
  | 33 => 0xec9
  | 34 => 0x1a4a
  | 35 => 0x1889
  | 36 => 0xd0a
  | 37 => 0xd09
  | 38 => 0x188a
  | 39 => 0x1a09
  | 40 => 0xd4a
  | 41 => 0xd49
  | 42 => 0x1a0a
  | 43 => 0x10e
  | 44 => 0x95a15
  | 45 => 0x94d55
  | 46 => 0x95a55
  | 47 => 0x94ed5
  | 48 => 0xd4d
  | 49 => 0x1a0d
  | 50 => 0xecd
  | 51 => 0x1a4d
  | 52 => 0x14d
  | 53 => 0x95896
  | 54 => 0x94d16
  | 55 => 0x958d6
  | 56 => 0x94e96
  | 57 => 0xd0e
  | 58 => 0x188e
  | 59 => 0xe8e
  | 60 => 0x18ce
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 68
  | 7 => 450
  | 6 => 504
  | 5 => 814
  | 4 => 58
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
  | 8 => packedAt gbK8 (1922+((h/22+packedAt gbK8 (1768+(h % 22)*7) 7) % 82)*8) 8
  | 7 => packedAt gbK7 (18150+((h/150+packedAt gbK7 (16650+(h % 150)*10) 10) % 654)*10) 10
  | 6 => packedAt gbK6 (25872+((h/168+packedAt gbK6 (24192+(h % 168)*10) 10) % 731)*10) 10
  | 5 => packedAt gbK5 (51007+((h/271+packedAt gbK5 (48026+(h % 271)*11) 11) % 1727)*11) 11
  | 4 => packedAt gbK4 (4193+((h/19+packedAt gbK4 (4060+(h % 19)*7) 7) % 92)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x830fc3ffc60c3f0fff1c1c1f83f1442784f0cf
  | 1 => 0x3f0fc38380fc3f0e0e01fe3fc72b8da1b4333
  | 2 => 0xfc00ffc03ff003ff00ffe003ff8cc31c638c3c
  | 3 => 0xffff00003ffffc0000fffffc000f03e07c0fc0
  | 4 => 0x3fffffffff000000000ffc007ff000
  | 5 => 0xffffffffc000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10048000004012004040080000000801045
  | 1 => 0x110441088044110422009412860184a094112
  | 2 => 0xa400aa81129002aa044940025304c114228428
  | 3 => 0x4aaa0002252aa80008929298000b02a0540a80
  | 4 => 0x608822043fcf33cc9e00c0c8192fec007fe000
  | 5 => 0xf3ccf3278182208810030310624ff7ff000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36308
namespace PEqualNP.Outside.L_meta_36308
open PEqualNP.Outside.L_meta_36308.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 13 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 17 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 14 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_96 : Interval s2Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_128 : Interval s2Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_160 : Interval s2Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_192 : Interval s2Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_224 : Interval s2Atlas 3 224 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 228 := (concat (concat (concat bs2_3_0 bs2_3_32) (concat bs2_3_64 bs2_3_96)) (concat (concat bs2_3_128 bs2_3_160) (concat bs2_3_192 bs2_3_224)))
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
theorem bs2_4_96 : Interval s2Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_544 : Interval s2Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_608 : Interval s2Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_640 : Interval s2Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_704 : Interval s2Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_736 : Interval s2Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_768 : Interval s2Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_800 : Interval s2Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_832 : Interval s2Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_864 : Interval s2Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_896 : Interval s2Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_928 : Interval s2Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_960 : Interval s2Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_992 : Interval s2Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1024 : Interval s2Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1056 : Interval s2Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1088 : Interval s2Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1120 : Interval s2Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1152 : Interval s2Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1184 : Interval s2Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1216 : Interval s2Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1248 : Interval s2Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1280 : Interval s2Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1312 : Interval s2Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128))) (concat (concat bs2_4_160 bs2_4_192) (concat bs2_4_224 (concat bs2_4_256 bs2_4_288)))) (concat (concat (concat bs2_4_320 bs2_4_352) (concat bs2_4_384 (concat bs2_4_416 bs2_4_448))) (concat (concat bs2_4_480 (concat bs2_4_512 bs2_4_544)) (concat bs2_4_576 (concat bs2_4_608 bs2_4_640))))) (concat (concat (concat (concat bs2_4_672 bs2_4_704) (concat bs2_4_736 (concat bs2_4_768 bs2_4_800))) (concat (concat bs2_4_832 bs2_4_864) (concat bs2_4_896 (concat bs2_4_928 bs2_4_960)))) (concat (concat (concat bs2_4_992 bs2_4_1024) (concat bs2_4_1056 (concat bs2_4_1088 bs2_4_1120))) (concat (concat bs2_4_1152 (concat bs2_4_1184 bs2_4_1216)) (concat bs2_4_1248 (concat bs2_4_1280 bs2_4_1312))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_704 : Interval s2Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_736 : Interval s2Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_768 : Interval s2Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_800 : Interval s2Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_832 : Interval s2Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_864 : Interval s2Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 890 := (concat (concat (concat (concat bs2_5_0 (concat bs2_5_32 bs2_5_64)) (concat (concat bs2_5_96 bs2_5_128) (concat bs2_5_160 bs2_5_192))) (concat (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)) (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 bs2_5_416)))) (concat (concat (concat bs2_5_448 (concat bs2_5_480 bs2_5_512)) (concat (concat bs2_5_544 bs2_5_576) (concat bs2_5_608 bs2_5_640))) (concat (concat bs2_5_672 (concat bs2_5_704 bs2_5_736)) (concat (concat bs2_5_768 bs2_5_800) (concat bs2_5_832 bs2_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 44 := (concat bs2_6_0 bs2_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 14 := bs3_2_0
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
theorem bs3_3_96 : Interval s3Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_128 : Interval s3Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_160 : Interval s3Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_192 : Interval s3Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_224 : Interval s3Atlas 3 224 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 228 := (concat (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 bs3_3_96)) (concat (concat bs3_3_128 bs3_3_160) (concat bs3_3_192 bs3_3_224)))
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
theorem bs3_4_1312 : Interval s3Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 bs3_4_192) (concat bs3_4_224 (concat bs3_4_256 bs3_4_288)))) (concat (concat (concat bs3_4_320 bs3_4_352) (concat bs3_4_384 (concat bs3_4_416 bs3_4_448))) (concat (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)) (concat bs3_4_576 (concat bs3_4_608 bs3_4_640))))) (concat (concat (concat (concat bs3_4_672 bs3_4_704) (concat bs3_4_736 (concat bs3_4_768 bs3_4_800))) (concat (concat bs3_4_832 bs3_4_864) (concat bs3_4_896 (concat bs3_4_928 bs3_4_960)))) (concat (concat (concat bs3_4_992 bs3_4_1024) (concat bs3_4_1056 (concat bs3_4_1088 bs3_4_1120))) (concat (concat bs3_4_1152 (concat bs3_4_1184 bs3_4_1216)) (concat bs3_4_1248 (concat bs3_4_1280 bs3_4_1312))))))
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
theorem bs3_5_864 : Interval s3Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 890 := (concat (concat (concat (concat bs3_5_0 (concat bs3_5_32 bs3_5_64)) (concat (concat bs3_5_96 bs3_5_128) (concat bs3_5_160 bs3_5_192))) (concat (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)) (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 bs3_5_416)))) (concat (concat (concat bs3_5_448 (concat bs3_5_480 bs3_5_512)) (concat (concat bs3_5_544 bs3_5_576) (concat bs3_5_608 bs3_5_640))) (concat (concat bs3_5_672 (concat bs3_5_704 bs3_5_736)) (concat (concat bs3_5_768 bs3_5_800) (concat bs3_5_832 bs3_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_32 : Interval s4Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_64 : Interval s4Atlas 2 64 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 78 := (concat bs4_2_0 (concat bs4_2_32 bs4_2_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_128 : Interval s4Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_160 : Interval s4Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_192 : Interval s4Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_224 : Interval s4Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_256 : Interval s4Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_288 : Interval s4Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_320 : Interval s4Atlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_352 : Interval s4Atlas 3 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_384 : Interval s4Atlas 3 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_416 : Interval s4Atlas 3 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_448 : Interval s4Atlas 3 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_480 : Interval s4Atlas 3 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_512 : Interval s4Atlas 3 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_544 : Interval s4Atlas 3 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_576 : Interval s4Atlas 3 576 11 := block_range (n:=11) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 587 := (concat (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96)) (concat (concat bs4_3_128 bs4_3_160) (concat bs4_3_192 (concat bs4_3_224 bs4_3_256)))) (concat (concat (concat bs4_3_288 bs4_3_320) (concat bs4_3_352 (concat bs4_3_384 bs4_3_416))) (concat (concat bs4_3_448 bs4_3_480) (concat bs4_3_512 (concat bs4_3_544 bs4_3_576)))))
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
theorem bs4_4_608 : Interval s4Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_640 : Interval s4Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_704 : Interval s4Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_736 : Interval s4Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_800 : Interval s4Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_832 : Interval s4Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_896 : Interval s4Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_928 : Interval s4Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_960 : Interval s4Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_992 : Interval s4Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1024 : Interval s4Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1056 : Interval s4Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1088 : Interval s4Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1120 : Interval s4Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1152 : Interval s4Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1184 : Interval s4Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1216 : Interval s4Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1248 : Interval s4Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1280 : Interval s4Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1312 : Interval s4Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1344 : Interval s4Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1376 : Interval s4Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1408 : Interval s4Atlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1440 : Interval s4Atlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1472 : Interval s4Atlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1504 : Interval s4Atlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1536 : Interval s4Atlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1568 : Interval s4Atlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1600 : Interval s4Atlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1632 : Interval s4Atlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1664 : Interval s4Atlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1696 : Interval s4Atlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1728 : Interval s4Atlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1760 : Interval s4Atlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1792 : Interval s4Atlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1824 : Interval s4Atlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1856 : Interval s4Atlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1888 : Interval s4Atlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1920 : Interval s4Atlas 4 1920 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1930 := (concat (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat (concat bs4_4_96 bs4_4_128) (concat bs4_4_160 bs4_4_192))) (concat (concat (concat bs4_4_224 bs4_4_256) (concat bs4_4_288 bs4_4_320)) (concat (concat bs4_4_352 bs4_4_384) (concat bs4_4_416 bs4_4_448)))) (concat (concat (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)) (concat (concat bs4_4_576 bs4_4_608) (concat bs4_4_640 bs4_4_672))) (concat (concat (concat bs4_4_704 bs4_4_736) (concat bs4_4_768 bs4_4_800)) (concat (concat bs4_4_832 bs4_4_864) (concat bs4_4_896 bs4_4_928))))) (concat (concat (concat (concat bs4_4_960 (concat bs4_4_992 bs4_4_1024)) (concat (concat bs4_4_1056 bs4_4_1088) (concat bs4_4_1120 bs4_4_1152))) (concat (concat (concat bs4_4_1184 bs4_4_1216) (concat bs4_4_1248 bs4_4_1280)) (concat (concat bs4_4_1312 bs4_4_1344) (concat bs4_4_1376 bs4_4_1408)))) (concat (concat (concat (concat bs4_4_1440 bs4_4_1472) (concat bs4_4_1504 bs4_4_1536)) (concat (concat bs4_4_1568 bs4_4_1600) (concat bs4_4_1632 bs4_4_1664))) (concat (concat (concat bs4_4_1696 bs4_4_1728) (concat bs4_4_1760 bs4_4_1792)) (concat (concat bs4_4_1824 bs4_4_1856) (concat bs4_4_1888 bs4_4_1920))))))
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
theorem bs4_5_672 : Interval s4Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_704 : Interval s4Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_736 : Interval s4Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_800 : Interval s4Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_832 : Interval s4Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_864 : Interval s4Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_896 : Interval s4Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_928 : Interval s4Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_960 : Interval s4Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_992 : Interval s4Atlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_1024 : Interval s4Atlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_1056 : Interval s4Atlas 5 1056 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1074 := (concat (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 bs4_5_224))) (concat (concat (concat bs4_5_256 bs4_5_288) (concat bs4_5_320 bs4_5_352)) (concat (concat bs4_5_384 bs4_5_416) (concat bs4_5_448 (concat bs4_5_480 bs4_5_512))))) (concat (concat (concat (concat bs4_5_544 bs4_5_576) (concat bs4_5_608 bs4_5_640)) (concat (concat bs4_5_672 bs4_5_704) (concat bs4_5_736 bs4_5_768))) (concat (concat (concat bs4_5_800 bs4_5_832) (concat bs4_5_864 bs4_5_896)) (concat (concat bs4_5_928 bs4_5_960) (concat bs4_5_992 (concat bs4_5_1024 bs4_5_1056))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 48 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_32 : Interval s5Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_64 : Interval s5Atlas 2 64 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 78 := (concat bs5_2_0 (concat bs5_2_32 bs5_2_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_128 : Interval s5Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_160 : Interval s5Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_192 : Interval s5Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_224 : Interval s5Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_256 : Interval s5Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_288 : Interval s5Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_320 : Interval s5Atlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_352 : Interval s5Atlas 3 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_384 : Interval s5Atlas 3 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_416 : Interval s5Atlas 3 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_448 : Interval s5Atlas 3 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_480 : Interval s5Atlas 3 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_512 : Interval s5Atlas 3 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_544 : Interval s5Atlas 3 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_576 : Interval s5Atlas 3 576 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 587 := (concat (concat (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96)) (concat (concat bs5_3_128 bs5_3_160) (concat bs5_3_192 (concat bs5_3_224 bs5_3_256)))) (concat (concat (concat bs5_3_288 bs5_3_320) (concat bs5_3_352 (concat bs5_3_384 bs5_3_416))) (concat (concat bs5_3_448 bs5_3_480) (concat bs5_3_512 (concat bs5_3_544 bs5_3_576)))))
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
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_736 : Interval s5Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_800 : Interval s5Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_832 : Interval s5Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_896 : Interval s5Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_928 : Interval s5Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_992 : Interval s5Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1024 : Interval s5Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1088 : Interval s5Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1120 : Interval s5Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1184 : Interval s5Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1216 : Interval s5Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1280 : Interval s5Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1312 : Interval s5Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1344 : Interval s5Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1376 : Interval s5Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1408 : Interval s5Atlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1440 : Interval s5Atlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1472 : Interval s5Atlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1504 : Interval s5Atlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1536 : Interval s5Atlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1568 : Interval s5Atlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1600 : Interval s5Atlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1632 : Interval s5Atlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1664 : Interval s5Atlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1696 : Interval s5Atlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1728 : Interval s5Atlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1760 : Interval s5Atlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1792 : Interval s5Atlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1824 : Interval s5Atlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1856 : Interval s5Atlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1888 : Interval s5Atlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1920 : Interval s5Atlas 4 1920 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1930 := (concat (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448)))) (concat (concat (concat bs5_4_480 (concat bs5_4_512 bs5_4_544)) (concat (concat bs5_4_576 bs5_4_608) (concat bs5_4_640 bs5_4_672))) (concat (concat (concat bs5_4_704 bs5_4_736) (concat bs5_4_768 bs5_4_800)) (concat (concat bs5_4_832 bs5_4_864) (concat bs5_4_896 bs5_4_928))))) (concat (concat (concat (concat bs5_4_960 (concat bs5_4_992 bs5_4_1024)) (concat (concat bs5_4_1056 bs5_4_1088) (concat bs5_4_1120 bs5_4_1152))) (concat (concat (concat bs5_4_1184 bs5_4_1216) (concat bs5_4_1248 bs5_4_1280)) (concat (concat bs5_4_1312 bs5_4_1344) (concat bs5_4_1376 bs5_4_1408)))) (concat (concat (concat (concat bs5_4_1440 bs5_4_1472) (concat bs5_4_1504 bs5_4_1536)) (concat (concat bs5_4_1568 bs5_4_1600) (concat bs5_4_1632 bs5_4_1664))) (concat (concat (concat bs5_4_1696 bs5_4_1728) (concat bs5_4_1760 bs5_4_1792)) (concat (concat bs5_4_1824 bs5_4_1856) (concat bs5_4_1888 bs5_4_1920))))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_736 : Interval s5Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_800 : Interval s5Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_832 : Interval s5Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_896 : Interval s5Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_928 : Interval s5Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_960 : Interval s5Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_992 : Interval s5Atlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1024 : Interval s5Atlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1056 : Interval s5Atlas 5 1056 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1074 := (concat (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 bs5_5_224))) (concat (concat (concat bs5_5_256 bs5_5_288) (concat bs5_5_320 bs5_5_352)) (concat (concat bs5_5_384 bs5_5_416) (concat bs5_5_448 (concat bs5_5_480 bs5_5_512))))) (concat (concat (concat (concat bs5_5_544 bs5_5_576) (concat bs5_5_608 bs5_5_640)) (concat (concat bs5_5_672 bs5_5_704) (concat bs5_5_736 bs5_5_768))) (concat (concat (concat bs5_5_800 bs5_5_832) (concat bs5_5_864 bs5_5_896)) (concat (concat bs5_5_928 bs5_5_960) (concat bs5_5_992 (concat bs5_5_1024 bs5_5_1056))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 48 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_4_32 : Interval gbAtlas 4 32 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 58 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_800 : Interval gbAtlas 5 800 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 814 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))) (concat (concat bgb_5_608 (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)))))
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
theorem bgb_6_480 : Interval gbAtlas 6 480 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 504 := (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480))))
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
theorem bgb_7_448 : Interval gbAtlas 7 448 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 450 := (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 68 := (concat bgb_8_0 (concat bgb_8_32 bgb_8_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 34, 50),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8feeefeeafeeafee8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276813544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36308.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[0,6]⟩,⟨.or,[2,3]⟩,⟨.or,[0,1]⟩,⟨.and,[2,3]⟩,⟨.or,[9,10]⟩,⟨.or,[4,5]⟩,⟨.or,[1,12]⟩,⟨.and,[7,13]⟩,⟨.or,[8,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276813544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276813544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36308

open PEqualNP.Outside.L_meta_36308 in
theorem PEqualNP.Outside.L_meta_36308 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276813544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276813544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
