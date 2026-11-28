import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_38005.Model
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
noncomputable def anyEq2 (m c d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || (eqF (masked d v) c || ih)) l
theorem anyEq2_eq (m c d : Sig) (l : List Sig) : anyEq2 m c d l = (anyEq m d l || anyEq c d l) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || (eqF (masked d v) c || anyEq2 m c d vs)) =
      ((eqF (masked d v) m || anyEq m d vs) || (eqF (masked d v) c || anyEq c d vs))
    rw [ih]
    cases eqF (masked d v) m <;> cases eqF (masked d v) c <;> cases anyEq m d vs <;> cases anyEq c d vs <;> rfl
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d ||
    cond u (anyEq2 (masked d a) (masked d (neg a)) d pool) (anyEq (masked d a) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  cases u
  · simp only [availF,cond_false,availableB,eqF_eq,anyEq_eq,Bool.false_and,Bool.or_false]
  · simp only [availF,cond_true,anyEq2_eq,availableB,eqF_eq,anyEq_eq,Bool.true_and,Bool.or_assoc]
noncomputable def memF (x : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF x v || ih) l
theorem memF_eq (x : Sig) (l : List Sig) : memF x l = l.contains x := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF x v || memF x vs) = _
    rw [ih,eqF_eq,List.contains_cons]
noncomputable def subF (a b : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => memF v b && ih) a
theorem subF_eq (a b : List Sig) : subF a b = a.all (fun x => b.contains x) := by
  induction a with
  | nil => rfl
  | cons v vs ih =>
    change (memF v b && subF vs b) = _
    rw [ih,memF_eq,List.all_cons]
noncomputable def sameWordsF (a b : List Sig) : Bool := subF a b && subF b a
theorem sameWordsF_eq (a b : List Sig) : sameWordsF a b = sameWords a b := by
  simp only [sameWordsF,sameWords,subF_eq]
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
    (links (keySet (choiceVal op::rest))).any (sameWordsF (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,sameWordsF_eq,Bool.or_eq_true,List.any_eq_true] at h
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
def M152 : Nat := 2^152-1
theorem not152 (x : Bits) : (~~~x).toNat = x.toNat ^^^ M152 := by
  rw [BitVec.not_def,BitVec.toNat_xor,BitVec.toNat_allOnes,Nat.xor_comm]
  rfl
def natBv (d x y : Nat) : Nat :=
  cond (Nat.beq d 0) (x &&& y) (cond (Nat.beq d 1) (x ||| y)
    (cond (Nat.beq d 2) (x &&& (y ^^^ M152)) ((x ^^^ M152) &&& y)))
theorem natBv_eq (d : Nat) (a b : Bits) : (bv d a b).toNat = natBv d a.toNat b.toNat := by
  match d with
  | 0 => simp [bv,natBv]
  | 1 => simp [bv,natBv]
  | 2 =>
    rw [show bv 2 a b = a &&& ~~~b from rfl,BitVec.toNat_and,not152]
    rfl
  | n+3 =>
    have e : bv (n+3) a b = ~~~a &&& b := by
      unfold bv
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    rw [e,BitVec.toNat_and,not152]
    rfl
def natCol (d : Bool) (x y : Nat) : Nat := cond d (x &&& (y ^^^ M152)) (x ^^^ y)
theorem natCol_eq (d : Bool) (s : Bits × Bits) : (column d s).toNat = natCol d s.1.toNat s.2.toNat := by
  cases d
  · rw [show column false s = s.1 ^^^ s.2 from rfl,BitVec.toNat_xor]
    rfl
  · rw [show column true s = s.1 &&& ~~~s.2 from rfl,BitVec.toNat_and,not152]
    rfl
def covFail (d : Bool) (t : Bits) (op : Nat) (a b : Decor) : Bool :=
  !(Nat.beq (t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat)) M152)
theorem covFail_eq (d : Bool) (t : Bits) (op : Nat) (a b : Decor) :
    covFail d t op a b = ((t ||| column d (dbin op a b).2) != BitVec.allOnes 152) := by
  have e : (t ||| column d (dbin op a b).2).toNat =
      t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat) := by
    rw [BitVec.toNat_or,natCol_eq]
    simp only [dbin,natBv_eq]
  unfold covFail
  rw [←e]
  generalize (t ||| column d (dbin op a b).2) = X
  by_cases h : X = BitVec.allOnes 152
  · subst h
    decide
  · have h3 : X.toNat ≠ M152 := fun q => h (BitVec.eq_of_toNat_eq (by rw [q,BitVec.toNat_allOnes]; rfl))
    have h4 : Nat.beq X.toNat M152 = false := by
      cases hb : Nat.beq X.toNat M152
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h3
    rw [bne_iff_ne.mpr h,h4]
    rfl
noncomputable def allD (f : Decor → Bool) (l : List Decor) : Bool :=
  @List.rec Decor (fun _ => Bool) true (fun v _ ih => f v && ih) l
theorem allD_eq (f : Decor → Bool) (l : List Decor) : allD f l = l.all f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v && allD f vs) = _
    rw [ih,List.all_cons]
def opsAll (u : Bool) (f : Nat → Bool) : Bool := f 0 && (f 1 && cond u (f 2 && f 3) true)
theorem opsAll_eq (u : Bool) (f : Nat → Bool) : opsAll u f = (opsOf u).all f := by
  cases u <;> simp [opsAll,opsOf]
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
def quickPairN (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    covFail (!c.2.2.2.1.2) (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2)) op a b
  else Nat.blt c.1 (c.2.1+1) &&
    (covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2)) op a b &&
     covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2)) op a b)
theorem quickPairN_eq (c : NodeContext) (a b : Decor) (op : Nat) :
    quickPairN c a b op = quickPair c a b op := by
  simp only [quickPairN,quickPair,covFail_eq]
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    allD (fun b => opsAll ctx.2.2.2.1.2 (fun op => quickPairN ctx a b op || testPair ctx a b op)) bs
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,allD_eq,opsAll_eq,quickPairN_eq,List.all_eq_true] at h
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


end PEqualNP.Outside.L_meta_38005.Model

namespace PEqualNP.Outside.L_meta_38005
open PEqualNP.Outside.L_meta_38005.Model
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

def SBf (j : Nat) : Nat := [6, 7, 8, 7, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_38005

namespace PEqualNP.Outside.L_meta_38005
open PEqualNP.Outside.L_meta_38005.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xbd43bf43
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
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/1+packedAt s0K4 (32+(h % 1)*1) 1) % 2)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x80ffffc0fffffe07ffffc0fffe07fffcf8fe3f
  | 2 => 0xff03ffff01fc0ff83e0fff07fff83e034f1fcc
  | 3 => 0xfffc0ffffe000fffc00ffff83fffc0038fe3f0
  | 4 => 0xffffffffffffff000003ffffffff003ff
  | 5 => 0xfffff00000000fffffffffffc0000003fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xa6082046244842014a12c42946214a98186e15
  | 2 => 0xa58c48a1c915658168555259aa92c294b16cc
  | 3 => 0x14316914483a6aaac109a6b12d3588528da370
  | 4 => 0x58a28e2091230d34a5a0308431c63163e001aa
  | 5 => 0x60c30c38e1c38dc739ce38c601842183f6d800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000fcccfcc0fccc0000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_38005
namespace PEqualNP.Outside.L_meta_38005
open PEqualNP.Outside.L_meta_38005.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x12010814404a824034928000008034208c14e000fd43fe10ff41fd42de32fc20fe43fc31dc32ff42de43fd20ff31fe42fc21fe20fd21ff40fc42ff43dd43ff32fd31fe21fe41ff20fd40fe40ff10fc10ff30fc43fd10fc32fc40fe30fc41fe31fd30ff21fd41fd32fc30fe32
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x40200240058000b010b0c95087301000012001a95c081023a2000012044809612dea4a1d754f41aeaa4873f54482baa919730c920bba8a413d540c67aa910d794f40ae29a215c5250edca42057d5032b6a96836e52d067ca8085754e21b7a92215f548cb9865906795032aea98833e540c67aa8085794c40aea9e819d540cabaa7105d544409f2a4435e528cab8a6a15794e20b7290216d528c2dca5186750c40cea1c815f53486eaa3a14f95330aeaa0655e520cb3ea8a1f314943afa9a851d540cae8a2905314943b6292215e5290ebaa6084f15120e6194439d43d0b3a86a0cf95032b7a9263cc420cad8a498cf15110af29e85ce520ca7aa8195754c42cea1a856c5250ebca7a0db548109faa221cf420ca7aa99873d4943afa9a415e5310ebca6086750f41ae29a435e53886eca220730c821afa9a215e53106baa6205754f42af298855c53482daa4205d94742
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x7000000c05000002826700cc61828c6250c4087590534868c6250f42a3189435064c6254c41c3189540ca8d640c82187596540ca8c6250e40c550d51103154354742c3553420cac661d0832a318943d068d640cb20c350d52d068d640ca2187592538830e540ca21a3590324830c540c9209318953d024d6510832c350d52103443214520
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x280000030000302aa4c3a1065035d8540c920a08e4a1aa220505740c85148206bb4a819443411c94354742
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | 2 => packedAt s1K2 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s1K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/37+packedAt s1K4 (2430+(h % 37)*7) 7) % 90)
  | 3 => 2*((h/22+packedAt s1K3 (950+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/16+packedAt s1K2 (294+(h % 16)*3) 3) % 6)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 2 => 0xe07f07ff83fffffc1e0ff8781ff87fff4e4e3f
  | 3 => 0xff8007fffc0fc3ffe00fff801fff87038f8fcc
  | 4 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x420a00230020800062110088c50089281090d5
  | 2 => 0x89144a441945212c0c8648510a4852d146462a
  | 3 => 0x4526948928ea0655a10b95025395041a8b8b4c
  | 4 => 0x9658e7125283ab9ad7a0c4449ce66063f00db0
  | 5 => 0x1860c61c630c33e319cce66700c44083ed6000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_38005
namespace PEqualNP.Outside.L_meta_38005
open PEqualNP.Outside.L_meta_38005.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x210604000900024710004124300400240008d001fe30fd21fe43ff10fc30fe40fc31fd41fc40fc32fd43fc41ff41fe21fc43fe32ff32fd32fe20fd20fc42fd40ff42fd30fc20fc21ff30ff31fd31fd10ff40fe31fc10ff43fe41fe42ff20ff21fe10fd42
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x441de53042fea898778c630be2a0637c54ccbf260885bd4943bea80857d54907ba86987b08420bea9841dd43cc2fca3907b94810df212857e50ccaf8a0a15f94f21dfa0c837d52cc7da6590ef95221bea9843bf43103ec83886f50f41be2a4437e500c7d864906f10b41f719441fa300c2faa121df54032bfaa263ee42887baa6215fd4910f6a9021ed21c82fca9084f55330f721085ef4290bde40105f54241efa1c87bf4290af8a6885f95043bfaa4437d53486daa4205714d10bf284817e529037c80a07dc8621be296217c5350bf220087d8c431f7102417e53043ea82886f90541fd100417d50c86faa3a1f794f41b7296617e50042fca6196f10941bfaa2415e53042dca4085fd5021dea1a83de43ccbbc8618dfd4132b7290817c53882fca318df94743f7908437d510c27aa8195f94441beaa2417f5408378a8885f54b43bea8043bc41903de43906f50740bea86877e50d06faa8105f94a42bfa9a41df300c3dc8519778cb30bfa9c21be54cc2fca3995fd4121bea88817e54482fca421df55130df208816d52043ba60185f55131ef29885f7415077e86a17bd4931ef192617f52043ec4210df95010dfa1e857f53c83da65105f15331f629263bd54043ec20886fd5110bea9e417c544c2fca3205f94430be28a61f5310c77a86207b10b32bea8e417e508cb7884205b54a30bea9881ed320caf8a9086fd0040eea18877c53043dc84907754c10dfa0a81ef32887ba86995754c40beaa0616e528c3eca2205f14f20f7a16657e54443ee4290dfd5310bf288657d54c42fea2a05f55243bea84655d53d07f620885f94421dea0a817f524c2fca7a05f54e30fc98421bd43d0af8a0a0df95042be29a417f53887daa5a0fdc4010beaa485bf41106f8a8195f15231b6a90635d5310afea990df54f10bea9e81df320cafca2215f94042f6190433d54042fea2a1df94e10fd08021de43cc2fca5087b0cb20af29c41bd401027aa818df54a40bf29c41f6414427ca910df54910fd904417f52506fca618770c831bf2a6217e5110fd8431077cc431aea98217f54883f280205f95331bf284857e540cafea4a07b94831bf29c436e52d06d8a4885f54e40bfa9421de434c2faa6086f50842f7994657d5190efca9195f54c42bf2a2436e529077a8220df94831f6a1085ef20883dc84995f54830f7a1285dc534437aa8196fd0842dea1a857a500c7da8510df942309f2a6617e520cafca818df54b40df2a0637d5010efaa3195f54640bea9c43ef32482fea2987dd0641beaa461dc318c3ba6218df15232ef192657d52882fea9905fd5331eea1c637e51906fca1087794c40bea9e437d52d06fca598efd5120be28263de434cbea4210df54a21f6a94837d5210efaa8885f95131be2a2217c5050efea9986f10440b7a92217d54902fea098df95020
  | 1 => 0xe5390ef8a498df54b30ef29c417d5190afea6885f54740beaa4637e5310ff2a018fb50920ef194637e50c87bc62185f54e41be2a6437c53c86f8a610f7cc230beaa4657e51082fca521df94221bfa98417c50486faa221f7cc530f7992657d538cbdc42104f95010ee98e61be42902fca2087b10921bea9a413e540caf8a898fb94843bea9083ef42486faa910f78c130bea9883ee21487b8a690df94040bfa9287ec42082dca421df94343f7990437e54087de84105f94243be282657e51882f8a2a06f90b41bea80637f53042f8a6a05f95230dea18877e5390afaa110fb54840bea88857c548c3baa7a0df14543ee98a617e53906b8a690df55210bf284837f5150af8a690df94910beaa2437f540cafca6906f90d43f6292217e528cafaa1995fd4520f7a9281ef32c83dca4207b50932f6216437d50cc6faa521df94830bb288817d51ccafaa9985f94621fd20081ec5250efaa4205794f41bf28c617f54ccaf8a2a17bd0b21beaa643ef21886fca4105f94730bf28c857c54486faa2105f94b30bfa82857e53c82fca4206fd0e40eea9c417f530877aa910fb48520bf29e837f548c3be86a1fb54b30bf28863de438c7dc64105f94810fc90041ef5250efca618fb8c921bf28e855e5310bdea4887dcc631de2a2417c540c2faa2195b94831be290217d5390bba87997d50441beaa0657c54082f8a4985f95130eea98817e53082fea7107e8c210bea86837d52042fca6215bd4940f6900417e500caf8a6107b94a41f6a16417c53506daa5a0dfd5132b7a92637e54c87dca5a0ef55031f6a10437e518cafea790df94b10df212837d52842f8a988774c832bf29843dd430c6fca0105f94d21bea94617e51d02faa3985fd4141f6292813c54483d86510f7d4d219f2a0637d54c82fea5887b8cb21be292837f54842fca420df14e10df20c817e528c2faa5885f546109e2a2217e52d03daa418df54e31fda04817d54087d884195f94b41be2a043f541c42fca0187bc8520f7a10655e53103bea6887dcc531be28a41bd54cc2f8a5085fd5231dfa1e835f53487d885105f94d10bf298817d520c77a87205f95221bf2a4416d52907dca5985f54e10bea8c617d54042fea690df94643de214817e50cc6faa518df55332df210816c524c77e81204fd5110f710c417e5210bf640905f94440b6292817f5350af8a488770ca31bfaa2437f53503de85106fd0740beaa0636c5250ef8a9987b54843bea9e85df328cbbc6418efd0d41b6a90876d52cc2fca820f70c430baa8881df318c7da6490df94c41ef18a63fa500c6fca1a16f95032fb884217d51883da64105f94041bf294837f5050efea8185e54031be28a657d53d06faa1215f14e21bf2a0817e54cc3ec8220fb48421bea9a217e5010efea7884f55221bea8685ee320cbf661185fd4d41be2a
  | 2 => 0x2c0502c1f01c05064020041e12c100002301c1c02000094110180c0304c00000004010540e00025004c80580300c0000c0407c0000003028723501901001014170080000008108760140602805110110ac08014090000b000010141413000000000d004038030682600c2b0f4010180e010060340504400004020404e0a5420a0000280202c0a01400010260bc170080f0400d01c0002c270e03a194010040f088610082001c01000160005000010014040ac32020010240b03821014020048000c3e0000002019000000d003000b2030000f40600806850030ac010001a024040047d08411000000041e01421018100400701c400a007004050000012003074050100104c000280001c00000049d80131c1607409000001381d03802008090000609c170100100000054320180d09c000001d3b80f0440000006014030144f0001f008050040f9faa2417d54cc6fca7205f94231bfaa0635d53882fca9905fd4931beaa2657c54482faa9105f95030dfa18877e52086fea9196fd0e43df2a021ee42086fea8085f94f42bf2a2657d53882fca518df15132fd982617c53c43dc85907d54440bf2a6657f514cafaa118df94220be2a021fa30442faa520dfd5110bf29687ed428caf8a9905f94f10bf280437c5250ff621085f95231ee192617c52503ea20085f54742fda02817d50107daa518770cb30afa9a21ee528c3bc8621fe4c030ef98e617
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x534863e6494e10ab590328866e62942438f593530432c52d05408f994544425f6354b109b58a544423f65504419bd9532082ae6290640cd50d51102766115010d354d520434f53149109b997324825d63d48109b98a51d033554440109798c540ca756115220b358c42cca6e6214c219b58854cc63d6494d20c7d53534434e5388620da94a500c66d6294243c7590534865e63152209b588548c27a60d503197d954310e5e65cc530d354e520426c6254c419758c54c866f65508429798c540823f6454a10d594e511031e5454c108fd954210b2d54d0832d394f42882796014c219b58a544875931540319b98853c434e52cc2309758c540863e64148109b58854042b46150d419b98b538426d65d083297596430c72d5454831ab18943d07595384010ce551500c63f6550c439b58a51d025e63150218f596411032e5450a21d350d52cc2cc6348720da549500c65f6354640b398a304c31e5450c319bd89548434d53508429b594320866e6215130b6580318c23c64540219758c548425e6395121d394d520423e64d4810b3189430c66e658c921c754d4210a6e6215030b358c420823e6494421c7551320ca3d6595031cd909511026e65d09219b195324872c54d49109ed95401025d639402097d8d544432d4354840cb95252cc34e539481097195434ca3e64d4e21b318943cc38d43d0b32ce552500c66c6254643d314d324863e6494c309b596320826d6215210c7952530425d658c4309b58b548c66c6255131cb149415027960150219b98b548c65c63546409b98b540426f6255130d554d51103695294031ab189401026d6214c109b58854cc276611522097d8d5190a746154d209e195304426c62542319b189519031e63952219718d5190a5c6354b109bd89501066f6255110cb14a405026e6215210b3189310c6cc624c7308f592524434c53d49109b195424ca3f6454d209798e524426c6255110d394d52d074d6214d219dd95210863f65500408f990530834e53c8220cb189540ca3e6414e219b988535066e6215230d994a511025e6514d10d354e521031d63151209b58b54cc25d6315010b3189434c26d6295231cdd0d511035a43540319b98854cc23d6414c10cb150524427a6014c10d394a318c277654c431d354d52d066f6254d21cb550420ca5f63549109b597320866c6254f408f59253842cc624c530c798e54cc34e5310a20ab18943506786055131cb54a421025e6394d21cb952520c72d544c832d654d100426e65109219bd89544826e65c85209b189510c31d54cc832cd152414425e63150308f99352c423d6414e218fd91508c74e534ca209d584548c25c6354420d390d520c73442544408fd91508cb4d528c8319b98854cc67a6014c219758f548829d6310b41cd545401026c6254d109b588505063d6595010
  | 1 => 0x835653544409758e50c866f62553319b597420825e63953108f59352042ae64886208f992518ca5e63d50108f992544434d4354831d6580534426d6214f108f990530874e53948408fd91534434d5394b41cd546411023c64542329758c505063e6414c109758e548874d43548439d185544c35943540319758e5090a6c65509209bd89508c66c6255130ce951500c63e6415031d3948318c25d63148108f99251c826f654c8329bd895190f4e53548408f997415027a6014e219758c540823d6494e209798c54c826e6214141c7552530425f654c832ce952500c71e63151209798e544432f54d49109798c54c866e6295110cb95152cc25e6394d10cb950328863d64944219b58a544c72e52d06419758c54c827860551219798f548831e6494e209798c540433554c40109b98a54c423d6494632cb552320ca5d6395121cb54a42d063e64d4c10ab590324832e5490a219d984540c26e6294e40cd544411031e6414d21d314f424866d6294d10cb50d5210e6f62546408f590530826f6255131b398e204823d6414f219bd89510c35553944409b996424826e6214c10a7590324c23e6494d208f990514c25e6315210d9549511027b65440109bd89534432d5454b309d586544cb2c540c920cbd0d5210e3e64951209bd8950d0f2c5450920cb151214826d6510832cb153214823d6414c219b98b54cc32f54149109d584530823c6454d209b98a50cc66c6254f10d9949511026d62d4c109718d524423e64150109b58a53902766115020b358c42486d9600c4309b98a548c65e63d4a109b58b538426d6510820c798e540c676619513297d95310c71e5350c40c754f4210a6c62543439bd8953d02ad640c8219798f520426f6254c419b588544c23d64d4b109b59652042766114c209b588540c69d640ca31d394c218823f6454910d314e214866d62d52309b98b540c66e6214810cd584544423d6414f20cb153324832f4354b419b18954cc65f63544208f59353886756115020b318943ccaae62905419bd95420874e4354b3097195434c2ac64480209b98b548c3583254031ab98a411027761551309b189540c23d6494720ab992210826f6255030d3d4f524432d54548109b994524427561150309b58a538423e6414d21c7592538832d54948319e596100426d62947439798c544826e62145309bd8953c426d62145309b988540ca6e65909329e583540c74d528cb308f59053c435b3154031d358a538831e5350f41d31895310aae64885218f992534426e62d4c209758c548827b60551319b58a54c423c6454d109e58354cca5d63953109ed95200832e54c862197d8d544876a5254031cb58a548865e6314141d314c424872d54948109bd89544cb2e54cca21c7150534426e62949109bd95200827a60d5332b358c420cacd6310b218f59
  | 2 => 0x1740c044040900033c01034001a00000000020000046e0080508810034010001906c10000020040003c07078000058a0080301006184120380a0a81e1600d000000087404c1832402000032c01c018250e8060ec010300d0a06b0d0000100401c0606c17034001bc1308c09034233340207c0b00c0001000268010444a0006c0f0e1024101207900c0000c020ec0c0384d0081d00c570f00a02c0000803004070142d1a80c108061a008028070949c00423064020008f0002400000064010842115c052082e0100d22800028000300f0e80b1503f078000051301c000644300001000230002e14c1506c0900002258010026e62951318f99053c866e6294e108f191528434c538c9219b189548423d6414530cd547401026e62d53109b59642086ac6250e40ab18943102776154d20d314c524426d6294331a759032cc26c62540419b988540426d62150309718d544436552944409798c520434d5354840cb951520425d63d4a10cb951520c6cc6250e31cb55252cc23e6494910d68c9500c63c6454910cb588544834e43548439b988540826d6588420c7d50534426e62d4c10cb952520426d6214d418f99253882776550441c795143cc32f43548409758e544c69d6310840d394e52d063c645423197596530425e6514d219b58b540c65c6355121cb152204829d640c8319b98a534426d62d53109758c544826f65484219b98b540863e641503297d95300c23e6414f108f596540cb1d63952219798e500823d6494d109e580538874c528c5319798e5488758538c110a758c425067a6015031d354e4210b1c54d4d109d195414423d6494c30d394e328825d63949109b58b540425e63943219ed81544863e6515120ab59032c827765440109b98a51d0e7b654c030c7551530427960150319b58a534825d6395110ab18943d0a7a6015021e350d424cb2d4354b41b6181434c29d6310a409d984548c2cc6348520b318d210863d64148109b988540c63f64540218f99053c826e650c9209798e5090a5d63d50109798c53042cd6310a20cb152424
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x40020070000049020000044041835916214d21a32e8192a018e0c5498e2048306b1ac42a2410b5da540ca2189aed298851050d7414d3248707324a710c41835516310832c48c4a8a802060d6458a5388307320a710a43831506348520a90e4a1aa018d0d731514248286b9ca8a1443521c93154031a1ae929a651064a52580318c28ab9884a8881491c94354440c1ac6b14a910c4d7614c4248713312a3208810b5d8540c920
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x80d87992538862080d87150634852080d87152638812080d879905388521
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 7 => 2*((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s2K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/263+packedAt s2K5 (17928+(h % 263)*10) 10) % 664)
  | 4 => 2*((h/193+packedAt s2K4 (20482+(h % 193)*10) 10) % 539)
  | 3 => 2*((h/22+packedAt s2K3 (1225+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s2K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x87ffffc0ffc3fe0ff0ff0ffff87f03fd31f3cf
  | 1 => 0xf81f87ff0ffffff07f0ff0e07f87fffece4c7f
  | 3 => 0xffe007fff003e3ff800fff007ff803830f8f8c
  | 4 => 0x7fffffc03fffff000007ffffc03f00ff0
  | 5 => 0xfffff800000003ffffffffff80000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x908500460084400190110123280910a81091c5
  | 1 => 0x242088825010050210610441082495046441a
  | 3 => 0x314b551263aa86b6888baa095d502a1b0b8e8c
  | 4 => 0x659466248a20cb2b5aa088126664b023b00b60
  | 5 => 0x46184438cc3313cc6ccccc9c0440c043ed6000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888eeeeeeaaeecc8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_38005
namespace PEqualNP.Outside.L_meta_38005
open PEqualNP.Outside.L_meta_38005.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x3000040016000253501003181382580081580349fc30ff42fe21fc32fe32fe43fc40ff40fd42df30fd30ff32fc43fe41ff41fc31fd32fc41fd41ff21fd20fe42fd31ff43fc10dd30fc21fd10ff30de31fe10dc31ff31fe30fd43ff20ff10fe31fc42fd40fc20fe20fd21fe40
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x3000000a2104c23d00001801c0cd0304082aa9400f014b280b304b43050c0c110aea9821d9308439aa5985754f21af28c635d538c2b2a018d754c40b7290875e53d06dea4a05d94420ec982213f54482baa118d714d21b7290813f54442bca7084f15110b6a96839d540c6daa520cf55020aea80633e540cabca6204f953309f2a0217551082d8a4a05b94810af28e61d9500c67ca818d794f21eb288633c54482daa421d794c20ae28a615f53486baa6215794c429eaa0639d54cc33ca9985754e40af29c413d54886bea6a0cf55330aea9c216e529067aa8196795031af29821ad4210a7ca990db94b419f2a0417651102bca218d754c20ae29a217a500c6bea6885b14910e729063da500c6daa4085b54831af298615e539027ca910d714f10e6a90633d54042dca5985b54840baa88816d52cc2baa7105714d41b7a92213d54c87b6a09857d4f10aea9e83ce52cc2f2a018db94831
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20c0040d2949500c70d5350842d2549500c70d5454831c6551500c658654c110c355152cc31a5454031
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s3K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/37+packedAt s3K4 (2484+(h % 37)*7) 7) % 92)
  | 3 => 2*((h/9+packedAt s3K3 (304+(h % 9)*3) 3) % 8)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc7ffff83fe1fff07f0fe1fffc3f81ffe98f39f
  | 1 => 0xf81f0ffc3fff0ff87f0fe1c1fc3ffc1f674cf3
  | 2 => 0xffe00fffc01ff1ff800ffe01ffc01fe1878f1c
  | 4 => 0xfffffe001fffff00001ffffe001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x40840088002200009010024480488488081185
  | 1 => 0x82421110940810282106208844124854234432
  | 2 => 0x114aaa218d54835b088b54116a815345858e18
  | 4 => 0x3594cc4a2906a595daa11025b3258189d80bc0
  | 5 => 0x261888733198c9e66ccd993822060211f6e000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaececa8a8eeeeeaeaececa8a8eeeeeaeaececa8a8eeeeeaeaececa8a8eeeeeaeaececa8a8eeeeeaeaececa8a8eeeeeaeaececa8a8eeeeeaeaececa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_38005
namespace PEqualNP.Outside.L_meta_38005
open PEqualNP.Outside.L_meta_38005.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x241a40002a4400001a001280049200002388000000fd43fc20fc21ff21fc30fc40fd42fd30ff10fe43fe30fc32ff43ff40fd32ff30fd21dd30fc43fe31fe32fe42fc10fd40ff31fd31fd10ff41fc41df43fe10fe41fd20fc31dc43ff20fc42ff32fd41fe21df30ff42fe40fe20
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xc437c544cbb6a0985794c20bfaa621df43082fea2997e4c030bea9841dc53506fca021f7d0d20af29c837e53442faa7885f54e32beaa2637d51103baa021f710d31eea1261de328c7be61085f94d20efa18637e5190efea610f710c40ef90e617e544c6fea4a1f7d0c10bf29c837d5190efca210dfd4930bea88877e510cbba85985754e40bf288855e54cc2fca821fe84010bfa9283df42cc2fea9195f54642fd884217e50083ba6108770c831ef90a617f540c6fca82077d0f10eeaa6617c544c6baa6105f15030bf28e81dd53103bc65985f54b41fba0a43df4350fda401077cc730bf2a261df324c37e8220df94621efa12617d510c3e883087d8c521fb10a21f451503be8720f7cc631bf290415f53502faa690fb54840efa1e817d50d0afea690778c930f6212437f53c87bc839877cc530beaa241dc41cc2f8a4985795043bf288637e52d07b886885f94631bea9e41dc31cc3dc85905f14543bf294657e5090efea9997754e42b7294837f50507eaa2195f95121bea9e437d54ccafaa910df54e41fa98a437e54c82f8a5887750530af2a261df30082e8a2a05f55031df21a877e52106f8a6a0f70c530bf280617e540c2fca5a1f710e40fc90041dd41cc3be60907710d40f699643dc4310af8a918df14c10ee20a61bd54043baa720fd50441eea9c217f50487dca520df54b10f7992657d52906faa9907bc8421f790e41ef42882faa810efd0842bf284817d52cc3de4310f794e41bfaa4417e50d0fee21087794730aea9c83df434cbbe60085fd4a10ee980417d5210f7e8320df95210be2a0417f53502b8a6a0ef50842ee982417e500877a84a077d0e20f729081de524c2f8a2a07b50b20efa1c43df51d0fbe61885f94c30bfa82657e52d02fca820f794343dfa1281fa40102f8a4a07d90441bea8487dd30042faa510f7d0c21eea1e617c53c82faa7185f14f219eaa0217c514cafca2105f55010ef296617e50887f280207d54642bfa8263dd30c43ea428877d0f20dea1887de54cc3dc64195f94341efa8087df5350afaa6905f54221efa86875e530c3bea7a05fd5231f290843dd310c6fca1187750d30ee990657e52042eea2a05f94a40efa1865de414c3e882085fd5330df2a021df30882faa610df94910f7102417c54486f8a6105f14143fb20e217f514c2faa718df54031bea9e837d520c3ea838877d0e30bfa9c21df51cc2f8a498f794b43bf29061bf4390f7e85215754e30beaa643dc5350afca5217b14940bea8e61de53842fca7a0f708730dea0a81df52cc2fca018f710e42dfa0e81be4250afca7105f94a43ef298217d5310bbea8985f15130be294217e51902fea9187bc8020ee288877c54cc3be8718df94642ef10e617d53842faa3087e88020efa1a43dc53502faa2194f95010f7a1243f710042faa1997714743
  | 1 => 0xd53882f8a91977d0c42efaa6617e54ccafea498e795043bfaa221f65190ab8a9985d94432ef28887dd300c2fca91857d4d42be2a0637d52d03b881987750c43be2a461dd51cc3ba63987754443f6908437c540cafca8995f94231fa20a437c53886faa4085b94810bf294217e528c3ee6298df54910bf298837d53103bea2985f15210f6a90637d54883baa3a1f7cc431bf29043be54083bea6a0f754930ee98a61ec42083be60886f50441ee20261755190bb8a8985f54841bf2a0857d50d06faa9885f95220aea9881ee21486f8a99977d4443f6992437e500cafca0085f94f42beaa6617e5090afaa5a1df54c41dfa18877d508cbbca021f78c831fb188637c53443bca2985f55242b6292817e51d0fec20885f14810bf29865f741042faa5205fd4520eea9c41df53502fca910dfd5120beaa4657d544cbb8a7a07d48710bf280857c54042f8a910dfd4540bf28c657f54c877e82a06f90140bea9c43f651082fca4197ed0240f690e417e530c6fca7887790330ee29687f6510cafea6a0fe44010bf29663f621087bca821df54b31ee21a657c5050bb887105f94630fba0c837f5050b7a80207710f40ee216617c53503ea6218f74c110ee21c43dc43086fca610df94342bf29e417d51c83ba80985b54831efa1c85fb104427ca8105f54242beaa663dc50d0efca8107750330df20a83dc43c82fea8995f54f40bea9e85de404c3dca418f7d4b43bfa82877f53082fca320fdd4540dea1681dd52d0fb884987715330ee29a437f53883ea4210df14d20f7a1643f5414437e85a05f94a41f7a12857e54cc3baa8985f55241ee218657f54c83ec6310d794e40bfaa443fb308c3bca6205b94840f719643df43842fca1105f15220faa8841dc438c2fca8887bcca32bfa9221dd514c2bca610df54a43bea94417e51042bea6a0f7d0f32efa1e437f53c82eca2107d94440f7212417c5350afca190d714d40efa1a857f54487f460185fd4b10be2a043df320cafca7215fd4810ef28e87dc434c3be87a15f94210ee21e83df53487eaa2205f94730be2a2417f54842faa0217dd0621bf288877c51483bc64995fd4e21bfa9821df438cbba6598fd44010ee21e61de53083be8798df95331eea90876d52103be65985b94831be28a85dd53083d885106f50740fb20a216f52502faa8187bc8520ee21a437d5490fb8a3985fd5010bea8e857e51106fca710f790c43f6a90215e5390afca5987790b30bfaa0617c5250fb8a021df95031fd982617d54442fca2205f94e40af29c87dc438c6f8a0a0d714d42bf2a6437e50106eca3215d54432bea8e81df43106faa7207ed0140bf298417d508c6eaa2105fd5021be2a663ef42082f8a2985b54810bf2a465ed42483bca610f7d0d41bf298877d54487b886187790930bea80877c54c82fea89877cc931fa98
  | 2 => 0x24034060fc0101212810040ea0580200000000000081009872000020a0060b8d60080c0403c520720001c1c006010681e0561780c1700a02922000160102e0b0e0030001403801016000820387800104058064480200c802c042138181c0080b8cc0de1a0d97200000008ea02000000020000201858048e0030e2118020001c00806568001e06c000000681a34894010220a83200086028080601200806098460000001818008b80100a0000008002078260383401814001581180800014178fa10812100283b0000881a078001781e36804000260c004128120009a07824000020000c000480f0060107a0600211804010a80201001c000702a028009b832018042384803046020fa02808001840f8060485a02820620080387a08800090000183e05808090232b000020003286c0080013840040020b9c8230182780001012000060487e00840968005700c00a407c8120a01c03f710f21bf2a0215d5010f7aa810774c220ee99661df40cc3ee4310f7d0e43bea80837d5390abaa610f7d0f30ee28a61ee32487ba6498df54732f7a92817d51082faa91877d0f41bf2a065dc43ccabca7107710e10be29221df404c2b8a8985f15310bea86877e53102f8a4a0dfd5131efa1a61dd324c2baa72177d0d31bea9063bf40103bea421f710d42bf29463fb20483baa60877cc320bf2a463df430c2fca120f710f42bfa9e21dc214c3b88798f70cb30beaa421dd30c82faa6087788530bea8c813d54083b887195fd4542bf2a6217e50103bc6298df54442bf28465dc328c7be6118770c930bfa8a87df524c3dc84215fd5331aea9c217e51ccbb8a421f795130beaa2615d50d0fb886a0df55240bf28e85de53882fca3905f95120beaa041df43103da42905f54021af29881dd53086f8a0995754c10ee292617e53042fca421df54743ee218837c53486bca7085f94f40bfaa0417551103daa520df14e10ef18261de53902fca1995f54d10bfa9a85f741506fea6885d94440be282437e510c3e88310df94620ae29a437e52102fea8195f94b10eea9661dd53902faa190df55231ee218417e5210bee83085f14e20bf290637e53843da84215f95021dfa0481f721487ba43985b54a41f7a1485de43cc3d88590df54620ef996637d500cbde41105fd4d21af298217d540cbbe83985f14c21bfa92817c54c87b88618f7cca32bea8c65dc43482faa120f754343bea9c41dc52cc3bca421f78c730fb10e21df43442fca198f790d30efa8261ed320cafaa3187ec8220f7290217e53487be86a05f54331fb98c637d52102faa50877d0530be29e21dc43042fca6217748530efa1c817e53c86fca721f794e42ee21c837c54442f8a098df54a30ee21e21de314c3be60185f54a31afa9a435
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x153042cd629073097d8d51c83665294440d954b41907645214540d354b310c7645248710c7950430c365524c43197997434ca5e6315021b658354cc2ce6210130b558752d0e5e6510d429d987548ca5e6494c309bd95320ca766194b43d310e520c756535442097d9743086d661d4b43d3d0e529071e5410f32c7552530423f6454d109dd952108754435442097d95300c25f63553219b588540425e63d5032b6d81524c2d56110330d9485500865e63940428f99353c86d5610c831b558652d0e5c6454e109b988540c65d63942429b19532486d66114343d354852cc365525444097d8d54486d661149308f596540434e5394a41cb14b425034d524c010d3d0d520c65f65d0c10d954b10042ce62d0d329bd954210b1e54cc0109798e52d065c63550109b58b54c431c54d0d30f110d210865f65487309b597420825d6510c32d314e324865e63d50319b98853086d960153309b58853c431e5454c2097d94430834c43948408f99053082ce6290530b358b51d0e5e63d52219758e544865d6394740cb55042c866d6294740b558642cc2746154d20b358840cc34d520c8319719542cc2756114930d594d51102d561909309719153882766114c219ed9540102d761503309d987540ca5f654c832c7953438cace620c730c75504308367534842197594430c66e6215030b6580424c2d56114b30cd552510825e6394b409758e52d06d4615033097d97438431d544c020979925388365514802097597430825e63940219758c52c425f6510e20d9145214825f6355320d594d5190b3554106218f191524434c435481097d95424c2766194b409718d524429c6454930c7953438c3653254432d9d4b5150355539442097997434c26e6214c10b3189544c25f6355010c795043cc25e6494c109d58754c825d63d50109d984540436652544409798c52042d5611434397596424c2796015031b598642cc25d631452097d8d52d025d63d48109798f54482756194b40b55845010e5d6315010d3588534865d65d0c219799743506d66194b4397d94430867661d5330cd551100435443546429b988548423e6415020b3d8940cc31d5494c20d5547300825e63149109b988548c25e65d0d31d354e529066d62951319d984520425e631522097994404c23f655004097581530426c62551109798c514831d54d0c1097997435036442544209d18554483675214540e310d4210b5653944409b988520433554104108f59052842756114c2097597430425d6510c308f59353042e561909209dd85534825d6315021d354d52042cc6254530d99512108754439442097992530865c6510d219b58b548c674654c521b59845010f4e5394810b6582524c25d63d531097191530865c635472097195214c25f6510c30cd147415026d62d50319758c5050a796015032
  | 1 => 0x425e6510d41b65805210ecd6290530d510d510ca5e63951219798e50d07655348421d954a511023f65504419718d54c426f62552109798e508865d63d5110b958a41c434d5354a41d9151210871f6395020d5cc9510cb5743544209d997414867561d4c209b98a51d0f55534842197d95300825d6314121d3d0e520c677654c431b3189404c23d64d4e218f99053042d96010e209b588548c23d65950209b98a51d0365528c4319d185548825e6494c20b9d95210865d63d512197d8d52442d5610ca319b58b54cc34c5314940d310f52503c46348421d9d09510825d658c83197596530834d53948409758c548426d6214141d954720082cf62545309798f540875443145409798c54083c76348421d354e52042d561101309d984540c25c65d0d219d584540825e6414d21d9549100425e63d5321b3d89544c25d60d4d429e580540872e5494810b598754cc25e6590730c795130043355150040d514e31487c7434842197583535065c6548730c79925410ece6214343d9d095190b1c6355020d310d52906d96010e10b598432cc25d6314a1097d8d544827860551219758f544831e54cc020b598440cc2cd62140439e59610043365454420d310c525025f6054e42d394b300425e6590d309b98b540863d6414121c799054cc25e63150309759642cc2cd6210130b6d81544c31c54105309798c530434c524c9309b98b54cc27661951329e980540c6d76150130d3d0d520435651cc02097994534865d63d50219ed95300c3655210410cb54940102d46150130d510d511026e62d5010c755043c866f62551109d58652d0f1f6355020b5185544c25d6594c21d514c51502e661d0921c7950430425d6094e4297d9541cc2d96010f40c795043cc67561141429798c5050b1e5410e218f990528425f6355130d5d0d5190a5d6094e419d984548c25c63550209dd85544832d54548108f191534435553546429759443082d5610cb309b189534425d63152209758e5010b1e54d0e319d996414423f6454910b5986424c2ce62947439798e5090ace62145309d58454882d661148439798f544434c4354840f1484214c23e64d4c209ed95100431d54d0c20d510f515032d52d0040b3d89404c2d56114843b658343102ce621473097597300425f65501309798f54042da6014843c7d50434425f6355020d5545300831c54501309798c52c425f6354b109b588514c2756115230c7950430c65c6354841cb55342082e56190b20b3988314c36452d4540d594e5190a3e64d4c109719541cc34c53d494097996404c23c6454d20d5d0e5190acd6214343d5544514c32d54c8020d3548524c2776155130c7990544c3994010130b318940cc25c655013097d8d540c26e62d503197195434c25d631481097d8d544cb575194743c7153404c25d63d5210c795
  | 2 => 0x654c43197992538423e64d4810d5d0f515025f6054c109758f548831e5494c1097191530425c6354b40cb552520426c6255210f14c9314865e65d0d219b98b54c425f6054c21b3588430ca5d63942218f593520427561150329d594410426d62d4c108f990520431c6395020b5185524c35553544209b195424826e6215010b998b414865d639424197594438431e54d03309e980540867a60150329798c548425e6394241b658043482766114142c7153434c65f6550b30b398b54cc27561951329d195214423d64d4f21c7550430425e63141219759743842756114f209758e50d06cd62947439d587540ca5d6095130d394d5210276611522097d8d54c435753d4540b6580414c25f635513197994434863f6454d20d3d0c525023f6550842b958a414425f6548530d310d520c65f6550530d354d210865d6394010d3949300427461551309b98a544c65c65505309798f548827661d5021d5d4c515025f6510e10d3d0d5290794435044197d8d521065e63d48109758f528426e62d523197594430865f6355220b958a411065f6354442d35485210e5e63d5210b5d85524c25d6510c1097d8d544425e64951309758c540834c43948109718d544433654944209718d548825c6354b10b5984324c34d520cb3097580535065d63d5321d5945300835553544409bd89544826e62141419798f528425c6355210d3d0f525031e544c020d154d21086d661d0d319dd95411065f6355221d3549310c65c63551209798f540c25e6590b30b6d81514c25d65cc0209758253087574354440d354d521034f5294b43c7551530433461550109b988540831e5410c20e6d0d401023d6414c10c7953430434e5354a419758353487c6328c5219799443502cd62147309798f544863d64148109798c53087555114443d554431cc2d960d4730979974350ad5610c9308fd954310f555114730b9189314874f53d4940c7952530825d6394b40c7d8e54042766115032b39885010e5e63d531097596414c25f63547409758f54c825d6014d21d694d300c27661d5020d3d0d52102d96095130b65805110f5443944329798f54c825c63551219ed8154487544394642f154d210875553884219d984530825d63940209d984540831c54905309758e51d0a6d62d50109bd952108757431454097d9530043676548421d594e510827561150309718d540874e5394840975805350a5e63943429b189544c25e6394010b5584524c31d5454c20b6980424c34d53c8421a7d91524c27661149309b596520427561d5330c7553300425d6508530d514f515025d6510e20d5145314c2cd620c730cd55341042d96010d10b398b51d0f4e5354810c7d50434825f65d0e20d554e5190b1c54109309d98453c825e639474297597438834f43948409758f540825c6454c2097d94430
  | 3 => 0x20040c0f00a0201c094060cc0200c0a0a40103cd800000014fb1b4080043c0cc030481404003000040180705c2c000060d40650400028000f458060000642f0240224c39000090180009247009580089606807084240104d0500001471034020006501431000050541c2000200d08020030d80912804000110200444c5d018211301a00004054180090a0001f03402044012d8a116842004a20bcca2bc1603414001230000717c01065c4144000440dc280202c01000110002a00c060000239420000130d40c000780214a06c00008281540400c000004d002020c00001c06008400001b025ab0080900016018010040100c492140c3280004c09064271200c00031048600287501c01620171280a0a8000140207c00094173041a0600021401005120800728401054040004d0288f0780b08885489250080009c0215c010040000c170195c05009004a202e5e6394321c718d540425d6394342f148421cc25e6314c20b398840cc29c645453097d954310e5e6314a10cd55151083596015330cb951520425e639402097d81539065e63d50209718d54c82d66114b3097996424c32c6255020c7150434425f6355210cb551200827561d50209798e51d031c63950109759641cc25c6315130d54c9510ca5e6508730d510e511034c4394a41cd54740102746550510f194d210866e6214f10b658052cc25d63149109d597410434d52cc0109d98754c825d63d52219b996424825e6315010b3588514c31c5410d20b69805110f6552d0410d98c9510ca7b65480209758c505071e5410f219758e50106d56110c319b58a51d0f1e5410c32b9185324863e6414121d554e51102d960d4b30c7d8d540425c6355221c795140cc25c6354442d354a320c66d6214c10b658051cc26e62d4c108f993538865e63141419b5885484357439443297195424c26e65d09219759421cc3574394440c7152424c25e65905309b594420831e54d0c209dd95100426d62150319b588540c359609513097d8d540865f65d0c20b5d85544c357435443297596530425e639404197597430c34f43948109bd8953442d96094530d914921442ce6290730b6580431031c54d0d32c755330082e562884219798e53487574394420b358b54cc25e64d4d219b988514c27661d4c209758e50086776155220d558453486d561d533097997324c71d5410e21b5984404c25c6354740b658343d026f6548020b35885110e3d6414c2097994214c26f6255130b6980414c2ce6214443b95864210a5c63553219dd85544434f5314940c7551300433554c40108f593530823e64150109d587548ca5d6394321cb55042082cd620c530a7d91514c25f
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1980800010080010cb2c01b21c03df040151001032040003a8ae229264985497010d52103062a4c520a61851506150130c8aca90842985517010d51102a2b98a290a41071d16508530a8ae421aa2196185458043442a3396a328e87915895114530a8aeb29a4210cc5739874248722b2a4210e61511d52108530c92a4b00a421e45525845210eb0b80a890843451d15114530a8ceca9a4210e0c54189404c322b12a228887511c55214930c8ac5a8ca3a1e18545804348323a92c329687315ca61d0d31d22c2a008098651515805110ea2b8886a9063165c06510d21c8aa4b0865985477054d2108722a92c229661319db4348421a8ae6292438854472544514c262b9cc5a0a43915896114d21a88e8a9a4210d457510d2108722b12a218e61515c8514c530a8ce3a94a5a1cc57198b434ca863a2a429261851526190930c8aa4b08a498545731512108744b128020261511d95348421c34c8b00a99854775d0d2108722b12a228e61515cc5248510
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1084686dd74348421906849d95348421c04745895114530a04845496114930844875952108530a04845952108530
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 7 => 2*((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s4K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/274+packedAt s4K5 (21627+(h % 274)*10) 10) % 801)
  | 4 => 2*((h/267+packedAt s4K4 (29678+(h % 267)*10) 10) % 781)
  | 3 => 2*((h/32+packedAt s4K3 (2744+(h % 32)*6) 6) % 56)
  | 2 => 2*((h/2+packedAt s4K2 (360+(h % 2)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xff87ffffffffff81e1e1f87ffffffffc063fff
  | 1 => 0xff81f8f07ff0ffe01fe3f8e0f0ff07e39d273
  | 2 => 0xfffe00ff83ff0fffe003ff00ff0ff83c1e39c
  | 3 => 0xf000000fffc000ffffffc0000fff0003fe03e0
  | 5 => 0xfffffff0000000fffffffffff0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8082010002000020204012221112100204a5
  | 1 => 0xa51245123294549608ca1a84458aa16a18d252
  | 2 => 0x4621492451a845aaca082b2089a8cd0ac16318
  | 3 => 0x64759648a50e66cd6d6c82012ecc86336e03e0
  | 5 => 0x88461800c630887191913449c0000841b5b800
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8feeafeeaa8a8a8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_38005
namespace PEqualNP.Outside.L_meta_38005
open PEqualNP.Outside.L_meta_38005.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2140081016280200011844002140142540003000080140007fe42fe10fd21fc43fd40fd10ff40fc10fc30df31ff20fd31fd43ff42ff21df43fd41fc41fe30ff32fd32fc42fe41fd30ef21fe40fd42fe32fc21fc40ff41fe43ff10fd20dd31dc43ff31fe21ed21fc20fe20fe31ff30ff43fc32fc31
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x400224647800034005000802b000098100083002e3c00000206817034001000060d00040800c00000000448000003950008d0024000820000014000018102000010000001016e52086bca72079d45219f2a4615e53082bea69057d4d409eaa461755190a7ca8105794e42afa9a8577515039e8790f9487109f2a0215c5350baa6310db54831af298435e538878a6290f54c521e621a435d538c6bca620dd94642aea9c819c544c6eca21973cc521baa88416d52907ca42885754e21aea9c835d53086baa721794c521baa88657451502baa221e710c41b6a94436e529073ea898f34c721af29c835e544c6b8a898f3d0d21ce21a815d53082bca7885794e43eba8a636e52c42b8a6907910521b7a9281765108278a898c715131af298635d53043988790d794c10ce21c833d54042daa420db14940bd280835e54cc67aa8105b54a319faa2636e520c6bea6a0dbd4930aea9e215c535079e6390de54041b7290215d53106b8a6a06710f40ae2a663cd31486daa588798c521cf2a0875e5410ebaa3a1db94841b6a90216e528c7ce8290db14930
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x200615a022088460821e6495131e119131486c6644c521c610d50107455348710b158c41486c4644c521a51913188694644c521b158443486c5638c521a319131c86656114930a9191314878443105218719153c428c644c521e1d913148684644c521c510c51502e16010521
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x5047454d21c434021ac020a43219d2644c521
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 6 => 2*((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/36+packedAt s5K5 (736+(h % 36)*6) 6) % 46)
  | 4 => 2*((h/82+packedAt s5K4 (2673+(h % 82)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s5K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/8+packedAt s5K2 (147+(h % 8)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf83ff87ffffffe0f8787e1f81ffffffc0e73ff
  | 1 => 0xffc1fff81ffc3ff007f8fe3ffe1fe07e319e73
  | 2 => 0xfffe007fe0ffc3fff800ffc01fe1ff83c1e39c
  | 3 => 0x7fff0003ffffff00001ffe0003fe03e0
  | 4 => 0xffffff80000003ffffffffffe0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa082089084800028281404904222a500630a5
  | 1 => 0x50845410c211523021282a10cb15412a108652
  | 2 => 0x6114952246a116d52820ac825351950ac1c318
  | 3 => 0x45b9664494399b69b5b208049d9906337a03e0
  | 4 => 0x8621800718c2218e4644d12700001841ad7800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeca8a8feeca8a8feeca8a8feeca8a8feeca8a8feeca8a8feeca8a8feeca8a8feeca8a8feeca8a8feeca8a8feeca8a8feeca8a8feeca8a8feeca8a8feeca8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_38005
namespace PEqualNP.Outside.L_meta_38005
open PEqualNP.Outside.L_meta_38005.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa282140040000089040027fd5001fd3102ff14005fe5200ff04005fd2100ff88405ff21007f4c00bff53017fc8009fc40017f90803fe41017f8c805fc42007f94007fe5300ff08407fe43017f54805fc5200ff10401fd51017f08009ff4101ff14c05fe20027f90007fc3001ffcc40bff51017f50809fd41017fcc807fc43007f44001fd5000ffc4009fc54007f84003fe5100ff8c409fd40027fd0c05fd20017fd4803fc5102ffd4009fd43027fd0009fd54017fd0803fc31027f95005fc32017f4c807ff30007f54c01fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2aa004bf99130137fa42a9817ff519400fffa922006ff1423001fb8a6a9807ff10544057f3142005ff94d51007faa088012be648c03fffb126220bf5913103ffe408802ff94084021fe9026000ffd815302efea92800ffe5354c097f324a009ff1511013ffac8a9883fd404c431bea92a000ff5853002ffca6a807ffc424c449ff322a203ff4c930137fc40a987ffd204c4017eb0ca006bf192100bffcc2a8003fd635444ffea0aa603fe0c13000ffe208809bfd6254c03fe98c2000efd913100ffe429881bfd208403fffa926210ff5093000dfac30801efd62440097e322a601ffd4510097fea09809bff4254c0dfe31c2006bf18a1000ffca30801bfe208c00bfe29aa006bf181510e7fc852801bfc105403ffea926200ff5953002efea8a8843ff214c023efa1a6001ff8c61002ffea6a8857ff548c021fe2126005fed415010ffea098807de314c445ff212a206ffd961005ffe870807ffd424c40bffa9ca006ff94110037fa8118012fc644400dfc284a006ff59230035f8c0a9817fe5254403fe20c2003ff94e300affa831804ffe218c00dfeb24a014ffd0a30035f8c31803ffc614c00b7e32a6027df55153007fcc0a981afe6084049feb22a206ff5021013dfac8a9817fc529400bffaa2a007fd4851000dfcc2a800fff438c00fff212201edf55250007fac09880ffd314c00b7e32a6203ff0c63008ffe829801bfe205400bfe292a218ffc855013ffcc8a980ffd324c4037f30ca006ff98a30067faa50806bfd4154007fe9946004bf19150057fea688063ff425402fff10aa001ff48531037fcc91801bfe649400bff294a005ff14e50037fcc31801bfd618c00dfeb2c2002bf98a50007fec09884ffe518c02ffe18aa000ffd95310adfac918002ff605444dffb12a613ff10630037fea108032fd6284019fea142007ff1491001df8c6a8873fe3294007ff18aa608ff98d10087fa4298003ff654c035fe322a003ffcc530037f86098007ff2184013fe3222003ffd0d53037f8cb1801bff409400dfb082200cff10a100bff882a8017ff5054c0dff32c2006ff4c21001ffc6318063fe6254021ee9926023ff18d5111ff886a8817fd5254c4bfe20aa61ff74c93103ffca488023fc534403dfea1ca015ffd063013ffa80a989bfd2054c35ffa1aa006ff19610067fa650801bff648400bbfa8aa000bfd8153005fac318093fd4354401ff3026205dfd415102578c89880ffe434c001ee98a6007ff8c91000efca2a881bfd6484007fe1926006dfd4250037fe6128006ff634c40bfea8ca013ff086300eff88728006fe618c033fe31aa009ffd0110107fec89881bdc304c001fe98aa006ff59630037fac328047fd544c007fe182a606ff08250037fa411808fff305444dfe212a606ffd963001ffaa698003ff6154003fa28aa206ffd8a10
  | 1 => 0x7fd215440d7e3246012ff1953000ffe629881afc6394017fea1c2000ff58d10037e8208806bff645400bfe292a619ff98d50037fcc70806afd645400dbe282a021ff19531117fec4a880afc62544037f30aa606ff94210037fc409800ffc534c003fea8c2001bfd8110037f0210806aff645400dfe0826006ff141300e5fac52809fff4054c31ff212a003ffd4e30105fec898806ff6154445ff192a201ff48510037f8608801bfc2084007ef9826221ff14131037fe610809eff6454c0bffaa2a603bf98d500effe632800afc6254c0bff292a603ff14d3108dfec898007ff515440dfe3242005ff54d510057ac9180077c5154403ff20aa205f7d4d5300fec4298807ff31544497fb22a200bf5953101ffca69880ffe3254c13ffb222000ffd8d5008ffea89801bfe104403dffa0ca006ff18a100fffc4098847fc644c041ffaa2621fffd093102ffea6a8007f621440057f312a605ff1495001ff8609881bff408c003ffa0aa203ff94d30037f8c528007fc515440bfeaa4a011ff5053008dfac898063fe3254007fd9846003ff50d5300ffc4298843ff424c003ff98a200fff88530067fe8508017fd5454413fd2022000bfd8d5000ff84298807fd414c429ff2946003bfd8d530e7fe652800fdc534c43bff21ca005ff54e5001ff886a980ffc314c03d7eb24a005ff14151117fe64a8893ff4054439fe194a022bfd895100ffe8288003fd518c00dfe0842023ff90d51057f8ca88037fc538400bff2a2a206ff14210125fac8a8803fc6054c0bff292a003ffcc15301ffc629808bfc325441fff28a6026ff0815304ffaa888017f8505400dfe204a003f794d30037fc8128017fc519400b7f32a6200ffd8d5110778c89881bfc108c04bfe10aa603bf98d1004ffac88806ffe4194049ff202a206fdc421003ffec488093fc405440fff9922005ff54550047fc8688003fd534400d7e3026201ff88610037fca11802fff548404ffe322a61affd015003ff86488017fe5494035fea1aa00dff94e1002ffca2a983ffc414c00dfe102a000ffd8d10037f8411801bfe208400bfe282a606f7cc23000ff8630800ffc438c00ddf3246010bf58930037fac52801bff308c00d7f304a001ff50610037f88088007f6514400dff2022001ff1451002ffea52801bfc5054003fd8822006ff1863001ff8a718006fe614c00dff282a001ff9051004ffcc888017ff525440dff904a006ff58a10015f8c498097fc1054c03fe20a620fff085300cff886a8017fc549400dff1822003bfd8130117fe40a8812fe6484007ffa1a6009ff9511001ff8a6a980afe624c033ff982a003f7cc15300ff84308007dc314c40b7f32a6005ff15151037f8c918012fe644c40dff884a001fd0c53101ffe64a9807fe514c403ff18a6203bf98e1008ffa8098043fd524c00d7fb
  | 2 => 0x3000ffc8308063ff625400d7fb142000bf58d1001ffaa71801bff64940097f324600cffd4a10037faa10801bfd63840037e30aa006ff90230037fcc52800ffe4354c07fe192a601bf18530005fec2a9857fd548c00dff31ca010ff9093002dfccb1802ffc548400bfda84a000ffd9510117fcc4a8807ff5184049ffa1aa219ffcc5500c7f8c4a806ffc2194007fe1946003ff90e3002ffca32806ffe3194045feb12a206ff1023001ffea69801bff108400dffb1ca010ff1493000ff842a8852fd628c049fe322a21effd0e5013ffc80a9862fd6254003ff18aa227ff1015302ff8a2a9847ff404c00dffb14a009bfd911001ffe651801aff614403fff2926200ff581510dff88328007fc415442bfe2a46011ff59130087fca498017fe5454c01ff302a21ffd485310d7fe82a801bfd4094047ff31aa222ff50951087fac498002ff654c00d7fb146006ff58e5001ffe869881bff628c00dfe904a001ff08510127fa80a8806ff614c403ff28a2001ff8c510107fe809887ffc524c40bfe2a2a622ff4815101ef8a6a9816fc6544007fd9826025ff90553037fcc508027ff4344045fe212a213ff146300c7f864a801bfe405400bfea9aa019ff90d500affca91801bfc619401dffa9c2000ff18131047f8c688017fd5294003fe20a2022ff4c951087fcc49800afc624c407ff1926207ff98910037fe4118033fe4284039fea14a009ff50110035f8c52801bff509400dfe202a005ff5495101fee6298873fc429404bff882a616ffd463003ffa4088043fc624c04bff30aa604bf191310e7fe432800afe624c4017fb0a6003ff50d3004dfac888003fd654400dbf282a005ff1455012ff8c2a9853ff528c00dff8846000bfd8d5100ffe42a889bfc6254c25ff32a601cff4ca50007eaa288087df534c401bea8aa005ff95150067f8a50801bfd508c04fffb22a607ff54910037fca098007fc314c415ff32a2000ff5855301ffa8698802ff6344041ff3226203ff10d3003ffa848801eff624400bffa92a00affd411009ffc8318016fd6594001fea8a6007ff1091002ff8a8a8007fd514c401fe98ca006ef5923001ffe6098063ff2054003ff90a2006ff081300fdfac49880ffc434c4077fb2aa614ff14a30025fcc88809bfe4254c037e30aa626ff98953107fac898817ff5154c07ff9826205dfd5153067fca50801ffd324400dfe324a003f710d30035fec69800f7e5354c23ff3226017ff90550067fc650806bfd6454001fe9822001ff041310bffe20a800ffc3154c43ff32a6225ff88553137fe40a981bff40840217fb12601fff08131025fcc8a883ffe614c0017eb1c2003ff50e3003ff8c488073fd219400dfe184a003ffd4d5300ffa6288083dd434c40dff3242014ff90a3001ffc65180937d545440bffa8aa023ff0c15106ff8870800
  | 3 => 0x4000bc4e0000008008214021041c4740a010bd138491d803000023a802000460001c69c061009f040010043d07c0200000008040006f014b80d0e7019400ac41000750300f02400028001183d030a215c0056412010014b42a0dc13fea1a2000ff1815101ffa64a989bfd4254c49ffb22a206bf196300fffcc49888bfc205442fff18aa005ff94550037fec91805ffc2154029ff90c6022bf58951007fac0a989bff2154c03fe90c2005ffd4150037f8809801bfc308404d7eb12a601ffd0531047fe608800efe6354403fea8a2006bfd9610047f8868806bfd4054045ffa12a206ff9013000ff02088007ff418400dfe314601fbfd8931005facb1801bff508c00dffb1c2006ff08110025f8c8a881ffd62440017fb0aa004bf991530fffc8498883fd544c407ff9926020ff10131007fec298002bf644c4037fb2aa214ff54a30107f8c89881aff6494031fe902a003f7cc53002ffaa4a800afe6254007ef9926200ff5855002ff8a6a881bfc1094029fea146006bfd963001ffe649880ffe434c407fea9a6203bf18d100a7f8851809aff6254c0dfd2042006ff14250037f8c72800ffc324c403fb882a201ff0415100ffe630801bfe619400dfc184600fff1453007ffe209800afe62440017eb2a2002bf9895101df8c6a8002fd6394007ef9926011ff951300fff8c498863fd425400bffaa2a21fff58931005faca98063fc4254041ff2026201ff1453102efea4a8017f7515440dff1826000ff58d500c7fa64a801afc628c001fea9c2000ff54130035f8c708017ff54940057f3146006ff04110035fec52802ffd548400b7f32a2005ff94e50007fec2a987bfd41940017eb2c2006bfd9230037fc412801bfc504400def1826003ff4c630087fe409806ffc3194037ff10ca020ff95131087fea498047fc544c0017fb2a201aff99150007baa698016ff6054003fea0aa222ff8815100ffc829880efe639401bff21c2001fec4210067fe6508033fc328400dfeb14601cffd0a5001fbc869883ffe414c03fff9026203ffd4d3100ffc42a8817fd5454c0d7e30ca006ff0c230025fcc8a8007fc518400dff32c6009ffd51100a7fa4318007fc3154441fe2a26210ffd893001dfac718023fe5344007ff98aa601ff50510097fea29800fff318c00dff1022006ff90210007fec0a881aff648400dfe2042001ff0c51000ffc4288047ff644c00dffb0c6022ff18951037f860a805ffc615400b7f32c2006bf19250015f8c488007ff104c431fe90aa000ff5953113ffe82a981afc658400bffa92a606ff8c21000ffca2a881fff42440177eb242000bfd813100ffea298817ff505440bfeaa2a018ffcc9500c7fac4a802ffe54840057e312a006ffd865001ffc649801afe608c013fca022006bfd8e10037fe4108062ff62540017fb2a6204bf191
  | 4 => 0x402408004000080949f0101c5603029000020100608c0200816018000b83003c0a0403b0180000025010090102305804ac0000b80b05c0d046b111c120040f6480100c0607801234010002c6f8060201814434060690205a284041387c004050880400800000140fc02134451143c0140e014050089b3480a0f80000000464000740008421320430bb360081e06c0b054360141000003014c5030170081900004010210e1a5030480740103c2f1cc0f0742014c09000001840b004001e82108430000311040100041038000000600c000fc000205a2780057c1e09408000190651d024231e0090f00350c0d00030040060ec0300400004000780b0200301978040010040c1b05c0285a028311
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7058e50034fd705961017dfb705853002cfc7558d100be7f51596101c79c31d9131034fc7059630004ff7458e5001cfe73d9530004fd75d8131004ff7459531004fd75d8d10036bf70592301f67d53d9531024fc7459610004ff7059531004ff7258d10135ec725815300cfc75d8550006bf5159230006be72d9131006f77159531176dd644c530046dc32d8d1000cfe765411001ede634c65007edd3158e101eedc53d85531cf9f32d9131024fc74d81511c6bf31d91310bef710d8550185df7254d300ee7d53d9530006be62d9131004ff7458e1002ef66554510147f240545100075f6554d30024fe7458e100057f75585300975f5454d30004fd73d81511c6be10d9131024fc74d95301c6bf21d9131014fe72d95101e67d51d953101edf604c530006f77159510014fc7258e500067e51d95300967c6559530155fb7058d10034fd75d855000cfe76d8553034fe70d9531004ff7359510004fd74d95310dcff7559510004ef7258d10024fc7458630004fd7459610004fd7654e10014fc7258d1000cfe71595301dddf7359531036bf505923016ddf724c53002cfe75d8d100067e52d953014df57254510035f6705451015cff7059510004ff74d8d51006bc641813102d7f71545500067d52d9531004ff74586500567c52d95101cebe32d9131014fc72d85530067f6554110006be215923007edf3158e101c6bc31d9131035f470545100de7f51d9510126be645463019ebd735923000cfd73d8131006bd2159230004fd7259610004fe7654530024fc7458d1000cfd75d8d51004fd74d8d51004ff74596101dcff73595311cebd53d913101cff71d9531006dd3258e50004ff7258e5001edc634c110034fe76d813101cfe76d8d101cebf32d9131006bf70d913102cfc75d8131014ec7258d101c6bd31d91310975c6554d30014fe725963008ddc744c5301cebc30d9131004fd72d9531035dc704c53000cfc764c110004fd745953001cfc7358650024fe74d8d500cedc43d8d5001cfc7359610024fe74d95300057f7558d100def6215865007ef661d8530006bc62d9131006f52158650006bf7458d100567f50d9510007f3705451002cfe7558d101c6bc73d9131006dd6354e101c6bc10d9131006f521586301c6bd51d913100cfd75d8151004ff72d8530006de32d8d101c79f73d91310367c5059630006be52d9131036f71059610004fd72d8d10004fd7258e10006bd52d9131024fc74d95100bef651d855000e7c6154550004fd74d85531c6be51d9131014fe7258650034fe70d8d51004ff72596100967e65d953002cfe76d9531004ff745951001cfc765413006edf3258e101c79e31d9131004ff72d813109edf31d8d1000cdd73d953109ef6215863000ede614c530185dd7254d30085ec725953010e7f52d953100cfe7159630
  | 1 => 0x95310067e52d95100def651586501fdf77158d51006df4358e50014fc72d9530006df7358d1000df47154110014fc7258e10004fd7458d100067f7559510004fd72d855012ef651d8553014fe72d85500567e65d9510034fe7059630014fc725951014df772545100de7d51d951001cfc73d951002cff7659531034ff73d9530035de7054d30034fe7058630046f53158630004fd7654d100357c76545501b6fa50d815100cfe76d853002e7f6054550036bc3059230006bf64981311c6bf71d91310cede63d8d5002cff7654130006f56154630004ff7359610006bd755923011ede53d8d5101cfe73596100567f5458650046df30d8d10006bc7159230006bc755923001cfd75d8153006bc21592301cebd32d91310cede53d8d50034fd7058e10004fd76546300967f5458e501fe7f54d8553006bf52592300957c755853000ef760545101bdfb7058d50014fe7258d1001edc634c550036be305923018f5d5454d30036dd3059630156f621d8131024fe74d9531006bf72d913100cfc71d8d10006f521d8131004ff725953004dbc7458d1012ef631d855302ef476545100f5bc744c650034fc70d8d10036be5059230014fe7259510006de32d8d50004ff72595310bf77105455002cfe7558e10006dd32d8131004ff72d8d510079f744c530006dd3258e10006be7159230004fd7258e50034fc70d951007fd4614c530004ff7458d100b67f5159630004ff72d855001fdb604c5300557c7558d1008ddc7454d301ae7d6454550036bd1059230007db704c53010e7c6559531014fe7259530166df624c53019ebc735923001ddc735413001fdb6054d301eedf30d85530bcff715951002d7c754c65001fd7714c5301cebe53d913108dde7454d300b6dd53d8d50004fd74d8151024fc74d81310767f5259610036bc2059230194ff7059530004ff725951009ef63158630004fd74d8d1010e7e65d9531004ff74d95300cedc32d8d500d5bc744c550004fd72d8131036bd505923001cff764c11009ef621d8d1002cfd70d8d5001cfe76d8d5007ef62158d1012cfd75d95310367e5059610006f52158d10034dc7654d30024fe745953100f77755451006ede5358e10034dc764c530024bc7459531024fc7458650006bc6459531004ff74d8d50006df634c550014fe7259531006dd3258d10004ef7259530024fe74595301dedf31d8d51006ec7259530006ef7258d10004fd7258630024fe745961001ede6354e10006bf75592300067f7559530005dd754c53017efa30d81311c6bf10d9131024fc7458e10024fe74d8d100cedf31d8d50006bd20d913100cfe71d8d501cebc32d91310567c65595100ecff75595301c6bd73d913100cfc71d9530006f521d8d10004fd7259531006dd32d853001cfc73d8550014fc7259531006df7359530034f
  | 2 => 0x6ec7258d10035dc7654d3015efa10d81510967f54d953001ddf714c530014fe72586301f67f53d9531004ff764c550006bd725923000cfe71d9530006fb60981531c6bf73d913106ef531d85301cf9c53d9131004fd7458e50024fc74d85530067d65546301fedf53d855311edc43d8d5102cfe75d8530004ff74d95100079f53d91310eedc4358e500067d525963000cfc73d8530006bf21592301c6bc51d9131034fc7059610006bc7459531005bf7458d1000cfe71d8153034ff71d9510034fc7058e1000ff360545100ee7f53d9530156fa10d813101cfe73d855007ef46158530004fd72d9510006bc50d9131004ff74595300ccfd7654130014fe72d8151005bf7458530006be70d9131024fc74d8153034fe76d81530047f7558d10034fc70d8530004fd72d8d5110e5f53d95310cedf30d8d50004ff7654d100067d54d85530357e70545501a57d7254550014fc725953011edc6358d51195fb70595300357c7054550036df3058630005bf7458553004fd74d8d50036f61058650035f4765451019ebe3259230006bd5259230035dc7054d30004fd7259530014fe72d9531034fe76d81510367f7559630004ff72d8153006bf65d9131004fd74d8550014fe7258e501c6bf51d9131004fd7258650196fa30d815302f7b605455000cfe71d8d101cebf53d9131024fe745865019ebd5359230014fe7258e1008dbc7458530014fe72d8530004ff73586501cebf30d9131006fb70595101befa50d815319ebf3259230024fc74d85500b67f5259630006bc525923019ebf7359230005bf7459531024fe74d8d51006bf64581310bf74615455000edc614c530004ff7158e50036bd3059230004ff74d8131036f6105863019ebd3159230004ff74d8553006bd6454630036f41058650005ed721815101cfe73d9510105bc7458131034fe70586501c7b621d913107ef631d85300079d32d9131004fd74d853019ebe7359230007b521d9131036bc1059230034fe70d8530007d8704c530034fd7058630004fd72d853010d7c7558131007f07054510034fc705953101cfd70d9530004ff7258630004ff74d8530024fe74586300bcfd76541101779c744c530014ec72595301ae7f6454550006be515923002cff765411001cfe7359510034fc705865010ede654c530004fd72d9530115ee72181510cedc6358d5009ef65158630006be7559230004ff7459630024fe74d815100cfc71d9510006bd62d9131014fc7258630006f741d855002cfc7558630004fc7654530024fe74d85531f6dc53d95311f6df30d9531005f7714c11002cfe75d8131014fe7259610034fd75d8d5012ef661d8553036f41058630024fc74595311edf7715953100ef66154630056f55158650014fc72596100be7d5159610006bc70d913102cfd71d8d5110edf53d
  | 3 => 0xf7258e10006df43d8d510bef441d8550125be7418151206dd53d8d51036fa6018131024bc7458d1002c7c7558d10096dd5358e50024fc74d8d1002cfd70d8550105bc745953102e7c655413002cfc75d8d1001cfd71d9531147f14054510024be76d913108d9c744c5300067d54d9530085ec7258530036bf1059230006bf50d9131034ff71d8d10005ef72595301a57f725455011edf3059531036f5105961019ebd3259230004fd74d9510106be76d9131034fe70d8553024fe7458d1002ef46554510004fd71d8d50006dd634c65011edc535953102cfd73d8153034ff7058630004fe7654d1010edf535953107ef710d85301c6be21d9131035de704c530006fb7058d10014fc72d8d51034fc705863001cfd71d8131004ff7159530014fe72d9530004ff72d953100ddd73d953119ebc315923002edc7654d3002ede6554d3000cfc765411001cfe765413012cff7159531006bf64181311c6bd21d9131005ef7258530024fc7459630004ff74d8d100967c51d9530006bc7259230034fe70596100367f7559610105be74981310067d5259610004ff74d81530367e5059630034ff7059610014fe72d8d50057775454510036df7358e10034fd71d951015dfb7059510024fe7459510004fd7459510005ef7258d501cf9f30d9131006df4358e101c6bd71d9131004fd70d8553006bd72d91311d5be76d9131014fc72d95100367d5058650004fc7654d1019ebe5359230004fd74d81530067d5458e50036f77158630004fd75d853000cfd70d8d10004fd7458630024fe74d8530006bd7159230036df7358e50005bd7498131005ef7258d1001cfc73d9530014fc72d8151024fc74d8530036bf2059230007db7054d3001ddf7554d3012ef46158553046de63d8d10004ff74d8550014fc72d8530004ff765453002cfe7558630004fd725951000cfc71d815300cfc715963011ede63d8d51006be7259230005df7154d30034fd71d8d10005bf745813110f5f53d9531034fd73d9530007d7614c5301c6bc71d91310067f7558d1001cfd70d8530024fe74d8550036dc3058e50034fc765463000e7c765455000cfd73d9531006fb609813103dec7258d1001cfe76d8d51024fe74d8131034f47654510005dd7318151166dd624c530024fe7459630014fc72d85500ce7d5359630006bc65d91310067e53d9510004fd74d813119ebc3259230004fd7458e1000cfc7159530036dd30586300057f754c650034fe70d8d10036be2059230034fc7058e500057f7558131036bd205923000cff73d9531006fb6098151004ff7654630004fd7258d10004fd74596301e6dd73d95310367f5058650006bf62d9131046dc6358d10004ff72586501cebc53d91310bef46158550036be1059230006bf64d8131014fe72d8d1019ebf3159230006bf75d9131
  | 4 => 0x815100777615455001dde73d95311c6bc21d91311c6be31d913100cfc7158e50006bf52d9131006ef7259530176df644c530057775054510007776554510006bc51592300eede5358e50024fc74d8d5008dde744c53001cfd75d855302cfd73d85530347c765455002edc6554d3000df4714c110014fc72d815300cfe71d951010e7f5459531004fd72d8d501cebe30d9131154ff7058d1002e7e655463000cfe764c1100067d545865001f5f7554d30005bf744c55002e7c6554110036bc50592301c79c73d913101cfc7359510006bc64d9531004fd71d815300cfd70d9510034fc764c650007d87054d30024fe7458e50024fc7459510036bd7059230006bc20d913109edd31d8d100067f7559531006df7359531034fe70d9510024fc74d8d51036be70592301cfb731d9131005bf7458d51004fd71d9530036dc3058e10034fe7654e10004ff72d8151004fd74d95301c6bd10d9131004fd7458650024fc74d953110edc654c530006f96018131004ff74d9531005ef725815301cfc73d8151004ff7654e101e4ff755953113dbe74981531cebe73d9131036bf305923000edc764c5300067d54d8d51006bf7159230034ff7058e10004fd764c650006bc7458d1019ebf53592301477554545100367c5059610006be75d9131004ff7159630006bc6458131036de3058e10005df754c530024fc7459530006f960181510077870545500067f6554130024fe74d951001cfc75d8d501e67f51d9531006bd70d9131005bd74981531c7b431d9131006fb70595300067c7558d1007cfd764c110005f771541100967c52d953002f777154550004ff7458630004fd70d953110e7c50d953106edc4358e10006bf7459531006bf20d9131036df3059630004fd74595312067f54d8d510067d5459531004fd70d8d51006be20d9131006bd75d91310eedf3158e50006bc75d9131006bd65d91310c5ec7258d5007cff7158d101c6be71d9131004ff72d8553024fe74d8153036fa6018153004fd72d855309cff7358d1007fd6214c5300567f54d9510006bc72d91311cebd30d913117edf32d8131004ff72596300567c53d951002cfd71d8151167d5214c530006df634c110005ef7258131014fc72d9531024fc7458e50036de3058e50036f77158650014fe72d8553004fe764c550004fd73d8550004fd72d81530967f50d953002cfe76d953013dbc745855302cfc7558e100bef661d85501b5fb705855000cfe76d8550004ff755863000e7e61545500077b7054550014fe72d8d51006df43d8d50006bf7259230006be5259230006bc52d9131057746554510004ff74d815119ebe3159230125bc7458d51004ff72d953016ddd724c530004bf74595310fdec7258131006bc64981310eedf3258e50014fc7258650035dc764c530004ff72d8d50004f
  | 5 => 0x12002000018c0010d80103c160000c5644c0299704012588020280001cbd0200700cbe011670000211c15adc0109800124120040706ac0231173b00907c013c4000400009c00050681bc080e06822c50020040380900007054220180d038130040101c0003c043347f10406000002680000011004010f8000300b0280252c00008050600b010171f4a254a1c000324e4000002a0240400c0e0c0040061a1f8000022d3741a000040c809004790d80604ea98041e01807020eb01c02034b0038050080002c12000080481014173008168a00b040020c0000018b608020180304010000070040b09402001242501002c0079c002f0020b8115642d83c09000162100035d2a3801f000e526c0610cfa1140704c060ac5f0600a0010e1844515c0809000190044fc07004010440a378010547f0001032e0a0501600801834010ed480400d00c100340000016ce006000560180105400008030000002c6d0bc00000040495d0000200015528240003d004011ec0150c5f0001c00c0043000004190000056c000407803f11a24000040200046000104a40000c1484cbe001b104c0d01e11004ff7558e10006bc64d813119ebc5359230014fc72596300ccff7359530076f551d855000cfe7158e500067d54d9510034fc7654e10004ff72d8d10006f96018153004fd72d815100df7755451002cfc75d8530004ff764c65001cfe7358650005bf744c65001edf6054d30005df7354130006f77158d100ce7f535963011dde731815102cfe76d9510034fe7058e10034fd73d853000cfc71d8d50004fc764c550004fd7259630036fa6018151006be65d9131014fc72d8d50036bc7059230004fd73d9510046df3258d10014fe72d815301cfe73d8151004ff7558d10014fc72d8131014fc72d8d1006edf32d853001dde7354530014fe72d8131004ff72d9510007755154110004bf7458d10005bd741
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8bf845d9319400155d0438ac91800297e0d52596300046fc1ae8b2a60008bf845c9634400b0f90aba2c68800e3720d74d81510045fc3acbb226242c9d73192604c40155b04286c89891327dcc6459531006363a8e4b1a20008fb8758060544014bb0ba1ac7280030fdd764581310343e43aa4b2c6000c3c751d1634400187eeb3aac9180021fe157654d100045fc22eca9a200087f855d16344001958e9b92c6880023be09764c6501c54e43265b2262008df835c965440051e90e90ac68800297e153258e500245e422e4b2a20018de87d8d31540051d904ba2ca98056ae60071592300043fc2ae4b1c2000a9d83085648c0014bb07296ca9800387d4c64d953100477c12e8b1a20008bf845c9619400147d0b316c8988028f21570d91311cd5a43243b226200a9d83143644c40176308382a28800317d97735413000656326e4b0262068f487485619400917d093b262a80eb275cc641813102c6ec1ee5b0aa600cac741c963440011df04bb2a6880023de0574595101c54ec18e5b226200a3e85083644c40117b0e286c89880237e0d745953100c6ec1ee5b2a6239ab5811cb644c4011dd0e392c68801a3721d3258e101c55b408e5b226200a5d83947654c00917908b8eca980032b1c864581310346e41ae9b026239a9e831cb644c40b0f90ab92c70800237e0d7258d100347a43ac2a8c600087f855c9654c001d8a6490ec09880297e0d52d953120e4f398c830262028ec825d9538400d1b90eb1a63280022f61e65d91310245f426e2b2c60008bd8798b644c40155b0438ac91801ab6a034358e100243fc3aa9b2a2039a9e83083644c4051dd0fb92c6880022fa1c52d913101c6e41ae8b2c2000a9d83083644c40155d04286c8988022f61c52d913100537414a3b2a6000ec632487634400b0fd0fbaac68800237e0d74d81510045f438c8b0262008ef825d1654c005998e4992c7080023de0574595301c54ec18e1b226200c3c75d91604c40156b02286c898803271d373595310166639264b1a20068de87d0d63840071b906b92ca8800387d9753d91310046fc1ae4b2a6000a3d851c5648c00195ec9b92c09880a3b209764c6501c5cb40ea7b226200c9c74d8d315400987ce8aa6c2a98038755343d8d510051ec2841b226239a9e831c3644c471938edba262980cea7a0e515923020ccf43ee898a60008ef825d1654400117d0e286c8988030fdd77458d100051ec2ce5b2262048be87dd1634406753d0638ac9180061f61772d8d510062eb9ca7b2a20048be86dd1604c40917908b9ec0a88e2ada0450d91311d64eb98c9b2a620487c87551654c409878e8aa2c3280032b1cb64581310045ec26e2b2c60008bf845c7654c00117f08b92ca8800a3b2097654d100043fc2ae4b2a2000aad82997644c40117f08b92ca9880e3720d7459510
  | 1 => 0xd010069050e051cdb0d0f66130100002f06010054410000090100000600070b0224080906db000000de010b000000018e260204011f03b4020a09090e0b040081004094153200071d040014104902000459040f001e2a00032d0800282f1400b4030a0346e43a64b1ca0038dc835c965840018beeab1a63280022fa1c74595310052e41aa9b2a2000a3e851c9648c00147b0b316c89880333dcc7258d1000637ba8e4b2a6002ccc724c963940050ff0ea96ca9881a3e201725953100477438e4b2a600687c87595518c00147b0a392c9180022fa1c525923000477c12ebb0a6006a7486545504400917d0fba2ca9884667211754c530034ba43aa2a8220008fb87580604c47353d06286c898803875534358e5001476412e8b2a20008be87d45648c00156b02106c8988028fa1672d91310045ec38a4b2460048bc845c961940014bf06aa6ca98107279db53d913100c6e41aebb0a6000caf74dc963440711790dba2c09880e3720d72586500346ec1ee9b2a6033a9e83085648c00117b0fa8ac91800237e0d74596100055cc00a2b246000c6f75dc96344001d8a6490ac688107279cc64d95310061e3a8c8b026206aba80145648c001d18c4996c8988022fa1f64581310046fc1ae4b0ca0068dc865d5314c00d1ed0db8a60880063760f74d953101c6f41ee9b2a2021c5c65dd5314c001878ebba2c6880031bdd47258d100045fc3ac5b2262028ec825d1634400187eea3a2c6880e2a7a1b53d91310054ec1ca2b246000f8532487644c48b1bf06ba6c0a990f17dd773595310051f428e2b2460028ec825d1658400d0f90ea92cb080063d20574595300045fc22e7b02a238a9d83dd7644c40153b0638ac9180022f612764c5500245e422eca9a2000aae82997644c40187eea322c0988023be097654e100147743ee4b2a6038ab681083644c40917908b92ca988121fe1d54d95300046ec1ee9b2a20048bc845d93194001b36e838262980029761632d8d500046fc1ae8b2a20028dc874c963440011f70eb00c0a9802aba0a515923000657ba0e4b1a20008ef825d16584001976e1386c89881a3721d6354e1001c6f41ee9b2a6000a5d85d0f63544011f700b92ca988161f2157258d1019d4e41aeab24600087f855c9634400d5750038ac9180e6a7a0f75d91310347a43a42b0c60008be87083644c4011bf06b92cb08002ab60a5159230006363aee4b1a2000a3f855c3644c401938e8b1a63280122f2117258d1001476412ebb0a6000a9f835d5648c00117d0e3a2c68800b331c932d85300045ec3841b226200ccf731c9654c00187aea3aec89881adc2015154110006cc3a6e098a6000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x21cea121932487644c4058c4874c92158d10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x1
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x124d
  | 12 => 0x124b
  | 13 => 0x124c
  | 14 => 0x124e
  | 15 => 0x9ca
  | 16 => 0x9cb
  | 17 => 0x9cd
  | 18 => 0x9ce
  | 19 => 0x12ca
  | 20 => 0x12cb
  | 21 => 0x12cd
  | 22 => 0x12ce
  | 23 => 0xa4a
  | 24 => 0xa4b
  | 25 => 0xa4c
  | 26 => 0xa4d
  | 27 => 0x134a
  | 28 => 0x134b
  | 29 => 0x134c
  | 30 => 0x134d
  | 31 => 0xb4b
  | 32 => 0xb4d
  | 33 => 0xb4e
  | 34 => 0xbcb
  | 35 => 0xbcc
  | 36 => 0xbcd
  | 37 => 0xeca
  | 38 => 0xecb
  | 39 => 0xecd
  | 40 => 0xbc955
  | 41 => 0x94bd3
  | 42 => 0x168a
  | 43 => 0x198a
  | 44 => 0xb49d3
  | 45 => 0x9cb53
  | 46 => 0xb49d5
  | 47 => 0x138c
  | 48 => 0x9ced3
  | 49 => 0xec9d5
  | 50 => 0x198c
  | 51 => 0xa0c
  | 52 => 0xa4bd3
  | 53 => 0xbca55
  | 54 => 0x138e
  | 55 => 0x168e
  | 56 => 0x178a
  | 57 => 0x148c
  | 58 => 0x58a
  | 59 => 0x1a4a
  | 60 => 0x17ca
  | 61 => 0x19cc
  | 62 => 0x14cc
  | 63 => 0x16ce
  | 64 => 0x144e
  | 65 => 0x28c
  | 66 => 0x589d2
  | 67 => 0x1a57d2
  | 68 => 0x59a52
  | 69 => 0x18ce
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 866
  | 6 => 899
  | 5 => 256
  | 4 => 2
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/288+packedAt gbK7 (32042+(h % 288)*10) 10) % 866)
  | 6 => 2*((h/334+packedAt gbK6 (43152+(h % 334)*10) 10) % 899)
  | 5 => 2*((h/99+packedAt gbK5 (15104+(h % 99)*8) 8) % 256)
  | 4 => 2*((h/7+packedAt gbK4 (140+(h % 7)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe0f81e0fe0fe01fffffff14c063c0e73ff
  | 1 => 0xf0e03f001ff0ff0fffe1fe03f2b239d2319e73
  | 2 => 0xff003fffe000fff001fe1ffc0cc3c1e3c1e39c
  | 3 => 0x3fffffff000001ffe0000f03fe03fe03e0
  | 4 => 0x3ffffffffffffe0000000ffc0003fffc00
  | 5 => 0xffffc00000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x12180280a01401210422251400402040630a5
  | 1 => 0x50422300845025048cb1540aa01218d2108652
  | 2 => 0x6a042d52a040b6a0253519a824c2c162c1c318
  | 3 => 0x4008b69cd76a040049d99030cb036e037a03e0
  | 4 => 0x81118e7198cd8c9700000c10fec0001ad7800
  | 5 => 0x8c9e000601081081800001020ff9b5b8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_38005
namespace PEqualNP.Outside.L_meta_38005
open PEqualNP.Outside.L_meta_38005.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 6 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 25 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 90 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 44 := bs1_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 539 := (concat (concat bs2_4_0 (concat bs2_4_96 bs2_4_192)) (concat bs2_4_288 (concat bs2_4_384 bs2_4_480)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 664 := (concat (concat bs2_5_0 (concat bs2_5_96 bs2_5_192)) (concat (concat bs2_5_288 bs2_5_384) (concat bs2_5_480 bs2_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := bs2_6_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 92 := block_range (n:=92) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := bs3_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 6 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 56 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 781 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 bs4_4_288)) (concat (concat bs4_4_384 bs4_4_480) (concat bs4_4_576 (concat bs4_4_672 bs4_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 801 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 (concat bs4_5_672 bs4_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := bs4_6_0
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
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat bs5_4_0 bs5_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := bs5_5_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 2 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 64 := block_range (n:=64) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 256 := (concat bgb_5_0 (concat bgb_5_96 bgb_5_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 35 := block_range (n:=35) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 899 := (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 866 := (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 bgb_7_576) (concat bgb_7_672 (concat bgb_7_768 bgb_7_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := bgb_8_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 34, 42),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8feeefeeafeeca8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276922536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38005.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[5,6]⟩,⟨.or,[1,5]⟩,⟨.or,[0,2]⟩,⟨.and,[3,9]⟩,⟨.or,[1,10]⟩,⟨.or,[4,7]⟩,⟨.and,[11,12]⟩,⟨.or,[2,8]⟩,⟨.and,[0,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276922536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276922536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38005

open PEqualNP.Outside.L_meta_38005 in
theorem PEqualNP.Outside.L_meta_38005 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276922536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276922536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
