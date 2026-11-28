import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37993.Model
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


end PEqualNP.Outside.L_meta_37993.Model

namespace PEqualNP.Outside.L_meta_37993
open PEqualNP.Outside.L_meta_37993.Model
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

def SBf (j : Nat) : Nat := [8, 5, 6, 8, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37993

namespace PEqualNP.Outside.L_meta_37993
open PEqualNP.Outside.L_meta_37993.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x172000c1400010490cb1011821000017000d7fc41fc31ff43fe43fd10fd32fc32fe32fd42ff32fd21fe10fe31fd41ff40ff42bc40fc21fe30fe40ff31fc30fc42fe20fd20ff10fd43fe41fe21dc30fd31be40ff20ff21fd40de30fd30fc43ff30fe42fc20fc40fc10ff41
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xe217f53486faa9186f90c40bf29681bc21103de85215f54a10bea84637f548c33080186f15110f719065bf421037ca3205f54c42ee996637d53087ba85184f55330bf286857f53482fca890f715030bea8c877e53107be87185f94f41f6990657e54882fea688778c010bf298437c5050afaa7a0778c630fb98a637c54c43ee4290df15330ee21c61d8400c3f440105f95031bf288817d5010b7ca818ef95021ef298837c54442fca9086fd0441bfa8287de418c2f8a688778ca30ae29a817e53843ba83185f54242dea1a85bc519037c81905f94743ee29461dd540c3bc84187ec42109f2a6617e5210af8a7906fc8440bea8c81dd328c27ea8887790f31dea1887de30443bc81185f94031eea9e817e519037a62207710a30bf2a265bf4290afaa1195fd4810bf29c437f53842faa710df94331bf28885bc40483f240885f95010de90c817f514caf8a9086e94040bf280437f54082fca810ef0ca40dea00817e528c6fca4886f10130dfa90817f524c6faa990f714630de200617e520c3bca4185f54743bf28485f510042fca898ef50d41eea1a635e5310afaa3995f54432fd104217f54042fca5987715230beaa0617e50c87bc87185f94841bfaa0657d54086f8a4084f95320ee908617e51082faa518df14121efa1461dc218c2f8a8996f95032fb90c43be4250afca421f70c830bfaa241fb304c2fca5a1efcc640dfaa2217d5110bb861905f54343ef28c61dd430c3be62185f94720bea94437e54cc37c81186fd0440fa108217d54082fea9196f90d43de20881bf4390fbe8721df94a32bf29e21fb409037a87a15f14530be2a6637e52082faa5185f94f42de200417f53086faa3a06f88640bfaa641fa10042faa921df55330bfa9c417d540c6f8a710d794f20dfa8c817e530c6f8a2a1df54041bfa8265785050ff480205f14532ef29885bd4210af8a5886fd0d42bea9a41de324cbb8a6905f55130df990817d53906f6a0a1ef10330bfaa2217d53d0bba63185f95320bea8483dd520c37862205f55131bf28c877f5250ef8a2a07e4c030bea9c41de210c27ea8985f94443be29843bf401037c83204f95032bf2a663bf54482f8a6086f55310ef18261de30482fea2a15f15032bfaa6217d52d06fca5885f14d20bea9e417e544c2fca3a17794030bea94837e54ccb7080185f94421de20421df310c6fca520df14d42df29081bc43902fea4a0d794c41bd280437e548c6d8a4885fd5210bea8c857d53c437c81887750230ee29a81de434cbbc8621df94030be28287ef200833881184f15120be29287dc510c2faa3985fd5332fb88421df320cbba87996fd0c43bf280877d5010efea890fb50842bf294613d54c437c811077d0630cf20061dc418c2faa420fb08620fba0c83df308c3f641107e48020b7a9221dc30c42f8a898f7c8630
  | 1 => 0xf540c3be84186fcc440be29221f421842faa6085f54332be28a85bf4210bbea81877d4630bf29485de430c2faa5a05f54610bfaa463df318c6fea8995f94e42bea9087ee4210bbea5187708430bea9221ed21086faa4207e10330bfa8a877f5050bbaa610d7d4d40be2a4617e530cafaa690dfd4910bfaa2617e540cafaa521df94b31bf298877c53c86fea6105f95042df108817d544cafca3185fd4d40eea1e6379500877aa4205f94621be2a665bf21902baa610df94231bea88617c52842bea6886f10230de98c815d53d027aa8197795230df202417c548c6fca5206f15120bfa9e43be400c2fca110dfd5221beaa021df328cbe8a2906f90130dea1683f5310c7f640905f14930beaa4637f548827aa9907750030dfa1e83fb5050fba431857d4d20de20c81dd510c2faa3a17754f20bfaa0437e540c3bc61907754a30ee194615c534437aa5207dd4520bf29081dd310c2faa0196f54c40bf280857c548cafaa018ef90140efa1a87dd438c3b860905f14e20eea98859d4310fee43086f10310dfa0c83dd300c33880185f55220af298437e54083f620886fd0640bea96617d540cafaa5107794430f7994657e54c877ea8986f50441bea9c633c544c2faa7187bc8421beaa4657e51ccafea5087bcc932bf29487be54c83d842105f94041fa908437d520c77ca9886f10c40ef21e657f504877c80107e8c030bf288617e508c37c81987e88110bf28465de53c42faa6886f10220bea9481bc52903bea6a05f94c40be292637c52502faa8905f55240bfa9a83dd310c7bea4185f95221ef10c61be4290378a22077d0430ee20861df53442faa7084f94240ef90861bd43902fca820df94641ee29a217c548837aa2206f54e40f710c41dc30082faa9905fd4141de18c81bd42102fca410f7cc030bea90217c540c27ca9886fd0240dfa1683bf43102f8a0a0df54420bfa9e217c53486faa190df94642bf28665bc544c2fea098f78c310bf28441de528c278a8886f90210df99481f950087f220087750c43df19081bc521037880087bc8220bea9c817d53106fea5885fd4930be2a443ed20082faa5a1df15130ee18861be41102fea6a1778c220bf29c837e53d03be80187dc4010df28081df324c73c811876d0030be28a417d508877a64206fd4e409eaa0637e530c3bca610f754f10df18881bd41102faa790f795030bf28c63bd51903b8a41877cc830ee184217e54102f8a9905f95232bea86855e500c27ca810f794f20bf2a6217e53442b8a690774c832de202217c504caf8a990df94241bf29e437e53043baa3185fd4520de21081bd54086fea990df94010beaa421f621086fca5085f553319eaa043dd434cbf661186fd4c40ee20061df53482baa7905f94432ef29e817d54ccafaa3905f94240be298413f54482fea7906f94c40aea9
  | 2 => 0x2001480183a180100203600800000b40200c0aa2e70000000de2280400036720080a01a0000e010160682404804481ea170020400001000000420602c000200e00802008008000800e4e80000062002ea052520001405800050000507a000d00b00002852460000c8200100406806078283586e0019400814030480019402818010060002604036408009a806020060680205080298640000807800120007e08801176228440c8180001a1b036010360000206800220081d0ce16ae92c8506200202846000060000001900048447d85c0d004058000a0140090e000121593a008000900004000030400080213012088000b806239765d000018580686e02820061a66a004360073280001a740001c100000b854e32020981a0100019002008c2118340400a00818040241689e0000e3b0000580e0f93ed600a0c80a1b02a0a800040081a000000186987c83588008051d800030001a00a018020005602000060c47900e04033bd43d06fca3984f94040ef180417d520c2fca1a1fe14143bea9881dd53106faa598ef14c40be282637451482fea710df15021bf288217f51503de84a17dc8410bea8683f641107be6598df14d40bfaa0637e548c37aa818ef94440bea9841bd42902faa7215f15031f790c437e53882faa8885f54331fda0061bf43903b861106f90840af28461ee21082fca7206f50941bea84877751482fca6105f94243df20a837d5110fb863186fd0d41bf28041df408c3ea8220df54632bf29063f7415077c65206f90010ef994617d548877ea2207d8c431dc20661bd54c83d8a4887dcc631f7a92217c54043f680a07750830fc904217f544c6faa890df94d21de994817c54487bc610877d0c30ee218617d518c2fea4a05f54440f710241bd54cc3f28020770c010beaa485be31902fca6217e94021df2a6617d53d06fea99877d4430bf2a0877f54cc7baa9186fd0f42efaa461de314c77a8320774c931ed28061dc408c3bc64187b88521bf29021de410c2fca3a077cc630fc20061bc4290378a7205f54021ee210617e52d077a86205f94e43beaa621be404437881906f48440ef18861dd320c37864205f94210deaa0657e54483bc80185f94620be2a0417c52506faa3105f94341bf290657e51106bca7a05f14e10be29e21be43903ba82185f15120bf28c655d53106faa5885f94431df29481bf42902f8a6a0df54e32fda0661f610442fca0207790d31bfa9821bc21902fca7906f94e40bf29a41dc304437ea5205fd4530f2908437e544437e84a0df94032beaa483de428c2bca7885754c429f2a0637
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1211023e651512097d954310e5c6354341c7d4e40482b8604c8409758c52043375414520b6982410c32c5290110bc580218425e6394a109e596100437160145209798e54882da6015230ae983531026d6215030a758c21102da60d4a30b6980520c23e6415032cb548521023c6454032b918520082ba63940409d984540c39a4310030a7593300c23f6454021c7951438c25e6394410e6884400c2756508410e658c400c33b6454021cb148404429e6408630f8486500871f531012097996304835753d45209718d500869f6550c43c7152304832f54d49109758c52c425e63145429b994524423e64d4f10ced8154cc27a6014c218f191508c79a6010030c755230c82db6048430e6100308434c528c11097994420c33954103309d58454cca5e650c110b3988510c3995110030d9d4821842d86050830c7152304c25d63152219718d54483355110440b6582410c25e63d50219bd89544c69e6010030e6d88400c2d86050c438f594211031c53901209dd85544ca766195120c714c404829d6394a40ae980531025c6354042cdd46519025f6354221c754f411063d64949108f994404c25e6510a308f992518c3a654484218f980544423f64543329758c54042d86350040c795153c823e650c840e6908400c35863540218f992528c29d6408430d5d44304823f6454231d654e500865e6315032ae181311023f64549108f590530432c5414910da14a204435453d4520e6588400c2b56114c40c7952530863d6414d2197594428c29f644c0308f59053086da60d4630c7151434ca3d650c4408f994404439921100309758e548823e6095032ce952500867461551208f990534863e650ca4097195434c63d6494d20c755153c823d6494c309bd89544431d535044197594430c39b65100308f59353c8398404c030ae582311036765484218fd91534826f6254d10a7990318c33b6414143c795230c831e5390310a7982400c2d86050430b5584520c31d548c310ae982400c33a609404097994418c39b6050c438f593504863e6508640c7151430c2da6014a30a798c521027765440108f994404833651506408f592538833854cc1309b98853042b561148408f994311031f5414d108f19150c865d63145428f99352c425e6394d10a798c41902e96008620c7d50438c398400c020ae98232103396510330c7d5353442da60d44309e181544ca7b6550040ce55150086b9600864097994534439b5110030d314f524435b63141438f592528c23f64543319bd95200827b6548020e64c4400c25e6510430c794e40c82db6050830e6548400c23e65084409798e52442da649403097d95320cb345110120cb949429023e6494910d5d46518c2bb6050c40a798c411031d53d0842a798c51103c5534842197d8d50d079a5410030e6d84400c2b66114c40
  | 1 => 0xc63d650c8409798c54c825d63d4b10e6508400c25f6355110a758c429031d5314c40a7590520c31d43940438f992538831c5450d318f992544c25d6394a108f996404825e6514d209b98a52443986510030e6d04400c23f6454d10cbd50524425e6315021e6594400c31d5494c21c755030c43395494021e6584400c25e6094c41ab988511029d6310840c7550430c2db6510030a798c21102ba6008640ae983511023d6414b108f992528431c548c110d6d0c5050f1e548c310d3149324c71d5310320cd150514829e640c430d694e50086e462440109758c525063e6414f209b58854cc71d5390310aed81211039b5210030c795030c831d5494f20979825310b994110030d5d4c514823f6454221b6982400c23d6494a108f594219029d63d0040c7d50534823f6454032ae980211023c64549108f1815408798400c3208f19150cc63e64946209798c540825c6355110ae59440cc23e64148109758f504879a52100309798c544869e64cc2308f59252082da6008630c754c43102d965d0030ce94c400c23c60550329d584540c32f5294a40b6d81430c25e6394d208f990524c69d640c630ae583431031d53103109718d50c87655108420ae98052902ba60d4e408f99253482ae6214c40c7553310c7a52108640e610c400c3986050c43d514c51482776550441bc185208431f5390140e9551210875853d01409ed81544ca986050c439798e548431f540c1208f593504ca7561951209718d509066f6550842c7d5030442da60144309798c52c439a64100309798f504867b6054d218f590530825e65084309718053442b9608c840ce594400c27b65440108f592510423d64149319d584540825e658c110b618143ccb986210030b6980540c3e021882108f59432902cd62150309dd8553483a521084409b189534425e6394620b6983548c2d661150309bd95210869e640c830e6944400c2d86050f318f99353087645284110d5144304834f520c110c755253c435b6354021a7592518c25d65d0030f1484218c23e649482097d8d50c875b6394021e6148400c25e63149419e983548c798400c0109758f505063e64d4131e698c400c27b6055121e60c8400c25f6354241b9181210874c53149109758c54c82d96090830ae980539025e63951109798c548871d54cc832c715143ccbc653484219dd95310c71e5454f109798c540423c6454d10ad984521027b605513097594420c25e6094c2197d8d500869d640ca309e195204425d63d4142d3d4c524425d6315310c7d52548c2bb604c840ae980511026d62150108f994544423e64d4132e6550400c31d5454c21e6104400c25e6394820a758c219032c52509419798e519023e6414f21aed81311029d6414430c715143cc73454d452097d8d501065d6510430ced92500865d63d5310ae18
  | 2 => 0x649511097d8d544826e62150109758f54c823d6414f209758e544c398400c120c750d5210f1c54d4d20f1484210c32c54d49109718d5090b56514c6309758e520823e6414c10b658f400c29e64946308f592534423e6414b10d5544310c25c6354041d9548210429d631044097d8d52442ba60146408f992530c29e63108408f992510429e6494a308f992534425c6550d328f590514ca5e6314c21b5984520c39940100308f982540865d639462097994218c23e6414f109e980520425c6054c42c714e405029d640c830ae1814350a3d6494e109798f505065e63153218f596540c65e63153109718d50886da60d5030c750d5110f1c5390110b6d81410c31e5494f109e583540879b43100308fd954310e7b654c0309758e548425e63d5310a71814310e5d639441097d8d50d0a5f6355130b6181434c69e6414830a7593308c2766115332b5185324c73864540219b988540c29c63500408f181540c71f5390110a7990210c23f6454232e60c4400c31c5414d20f8485500879842100309b98854cc6b86050d41b6181210c39a6010230b6582430c25f654c431c714c404427965100309718d544863c6454332a7191300c23d6494620c7d4c40442da6410030ae983529039a62100309758e544423d6414f109e580530863d6414f21ce994400c27661150208f592518c39943100309b588530431c5350d41e6984400c39a5090030b6181434ca5e63d4b10e6084400c31c540c1209e983530863f6454d218f191500866d6294d10b958a21086786055121e6d08400c29d6494a308f990514cada60d48309718d50d0a6d6295110d6597400c23e6414c219e980540863d6414e21d3148304433a5454021e610030882e765484218f99350487386494021d3548520c33751901209798c52042b46150941ae983519029d6394640d654d500863d6595032ae1814310e6e6294d10a7590218c23f64540319758e544831e5090030c7d52304c39861100308f590520423d650c6408f994319023d64d4f10a7d8d401034d520c8309d984530831c5414d10e6cc8400c31d544c832e6940400c2d960084309b98a544423c64540318fd95401032d52108409758e529023e6415031e6cc4400c31c54d4d10cdd44404823e6414c20e68c8400c23e6494e10a798c219031d541503097d8d544869e63d02409e583548ca3f65504419798f54c83355114440c7940400c2ba60d4840d5d46304839b2110030e68c4400c25e63d41429dd85544831d540c3209e583530874e524ca30c795253c82786055131da580524423c6454d21b5584540c25e6395120e6103300c29d63148409d185544ca7b605513197596530863d64d4c218f19150886b8644c030a758f409031d53903208f990540871f54d4d20d3d4a528c29e6394a40a798f401023e64951209798c540
  | 3 => 0xa1d004188070100600c01000011d40d3a805050090283f4bc1d02800120000c4530005b26805000430bc440a8044d0082941401c0100005008190100a0500500001084000500000800100224040c0083e0bc0703cbd040a90046b0248e01c0100403000d701000014121c8480180000c07051d5000205c8480180808891248030604d0043c00804014023148204402030160cc0e19c00018330040e0240a008718101100c1c0007906c090002f0140b1540c010010380d01c0a064020702a0040500033004020ac7b3100700007090000181a010090100d000000c80b01401074050b0000140200c212d8000000c24812020870000000022030310580a0040a034007f4020bcae038050040002c0e00505014000e93c010070c4034c00010c18000c400cca07c0316c0006c000180a0001601c17000060000300000080040000c0381a038060040305401cbd4a404431c540c110ae580211023d6595021ab588511031e53103208f994544c34f53d49109e583548c73754d4520b3988540c25d65084309dd95210865c6354910c7d4e539025d6315121b6580218c23e65901308f59352c42786054d219bd95320ca9e64144309dd85524435a6094030d5544510c25d631502097181531079932100308f99353c831e540c310c7d52304823c60151108f982540c65d63150219758e51902ba6014840a75924310eda60084309b189544431f548c110d618e500873a4314143a798e51902746154d20a7993300c3345190120ab588531025d63d50218fd954210a79601502197980534425c6054c21a7590310c2756114c20c794d439025d63949108f191508ca9d6310640a758c51102ba608c440ae18143d0b985110030e610030c42756194d20c755153c431e53103109d986534823c6454d20e6904400c2b86050f41cbd48404425d6508630d9146204831f6550c4397596430c25f654c030d3d4a304431e5454c21b6980518c23e6414e219e983548ca9e640ca309758c54c871d5350842e6100304425e6394a4097594418c31c5350d42d6d8153d025f6354042c7551310c754518c120d694d500863d64d41318fd9150c867a60d502197994304826c625513197d8d5090a5f6550030e6994400c2da6090830a798c42902cd6214430b6594400c29a60900308f996404423e
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x6001101000062410900001000408186002c02c08200022a01985003829a1c084800600b000000003040161c160000101469d46110030c2ac8a88621861b651814310f22b12a228861c2148400c110934ec29080185187050d5210fc09084220061c25485210030c30c831ca010e1965194400c24c3a2c010861895952108440c4ac4a88a22072154485500864c382c6108818354d6214c40b40e0908422061b751814310e8c38286a8887269cf6048440a1ae42a28798e1854181434c64c39ac0108818554d6114c40c4aa4b08a4206186418d5008706b1aa4210818558d5110440a30e0a1ca021d1975184400c30cb288620061649c46510030934ec288801858972194400c28d386a729c818614c6050d41870e0b20a690e9161184400c2c8b88c420061265d82110030b22e2328801859271188400c2c4b90a220061c45445110030932ec288801858a72144400c28cba8c420061629c861100308b0e0b18a890e1854181434cb0aaa2c22a061861506050f31a34ea310801849870590210c306b22a429061435c85450c30c2ac6a88a2206185418143cca8cba84220061c4d44400c120b12e4308801859271148400c28d386a92a461461c0540c110b22e2290801864565484210c30c298c0a1a85469d42110030a2ae22a2861868962188400c30ab22a228861915496114830b80e09084218710511003048306b22a419061455c45450f32c1ac6a90a42074153485500864d3a6c090861265d85210030934ec108801860d54588540c385a908018221629c86510030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x2002051008c09765485210030d01725445110030c09755886210030c81764842110030d01525c45210030c11765445110030c81725846110030a09821506050f31c11755846110030c81625c46210030a11811506050f32c11655c46510030d01754842110030c09655c86510030
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 779
  | 4 => 754
  | 3 => 85
  | 2 => 14
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
  | 7 => 2*((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s0K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/287+packedAt s0K5 (21033+(h % 287)*10) 10) % 779)
  | 4 => 2*((h/265+packedAt s0K4 (28652+(h % 265)*10) 10) % 754)
  | 3 => 2*((h/56+packedAt s0K3 (4165+(h % 56)*7) 7) % 85)
  | 2 => 2*((h/11+packedAt s0K2 (840+(h % 11)*4) 4) % 14)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3ffff01ffffc183fffff07ffc1ffc01f3f3fc
  | 2 => 0xfc0ffffe07fffffc0fc1ff87ffe1fffe8c7c7f
  | 3 => 0xfff03ffff81ffffff001fff87ffe1fff0f8f8f
  | 4 => 0x3fffffe001fffffe00007fffe007f00ff0
  | 5 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x9861811c51448200b2c270089c02243031b1bc
  | 2 => 0x29221224320910940550948525214952845455
  | 3 => 0x5084a44880d22129502129504a5412a50a8a8a
  | 4 => 0x62cb38912483b5ce69b40c44739980c7d00f60
  | 5 => 0x830c30e1c71c39f38e39ce6603110307ef6000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37993
namespace PEqualNP.Outside.L_meta_37993
open PEqualNP.Outside.L_meta_37993.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x9d43
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
  | 4 => 2*((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 2 => 0x87c1ffc3e0fffff8707f8783fc3c1fffd64c9f
  | 3 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x800880400040008090088880444422009131
  | 2 => 0x2112910909522128342485112428894c524486
  | 3 => 0x12a52290d2a406538859502aca8152a2a58b18
  | 4 => 0x5539c42a9836ab9d5d0c4443733380c4f80ec0
  | 5 => 0x663187331cc733e66e6e667062220308ff6000
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37993
namespace PEqualNP.Outside.L_meta_37993
open PEqualNP.Outside.L_meta_37993.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x10000ef20f710ed20ee21f510ec21
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x2d2a010f848110
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
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/9+packedAt s2K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/7+packedAt s2K3 (54+(h % 7)*1) 1) % 2)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x81fffff81ffffc0ff0ff83ffffc1fffd18fe3f
  | 1 => 0xfe07e0ffe07e0ff0ff0ffc1e07fe0f02ef33cc
  | 3 => 0xfff800ffff800fff000fffe007fff0030fc3f0
  | 4 => 0xfffffffffffff0000007fffffff003ff
  | 5 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8c104408c1044401101190aa30c85518085615
  | 1 => 0x14b18511472854b07106948c534a46286b32cc
  | 3 => 0x2862d6a28a1d6d57088b5ac8a5ad64530dc370
  | 4 => 0x714518c414510a6aaaa04201063188e3b001aa
  | 5 => 0x4186108718618b8ccccc6311c0210083d6a800
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37993
namespace PEqualNP.Outside.L_meta_37993
open PEqualNP.Outside.L_meta_37993.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x800020000010000481870020003404800405003c1fc30fe31ff30f710ff32fc21fc20fd32ff43fd41ff20fe21fe32ff10fc10fd21fe41fe30fe10fe40fc43f510ff41ff21fc31fc41fc32ff31fe20fd31fd42fe43fd30ff40fd20fd40fd43fd10fc40ff42fc42fe42
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xe63bd540c2faa7907b50a32bfa9e417c504c7eaa7885f94a30bf290857f54cc7e861887750f30fa98a217e5110ef8a4984f55321fb202217e50042fca1a1df54443ee99463f6511037c80a05b54843bfa9843ee32086faa1195fd5030ef980617e544c6faa7a0df54610fba1e21ee52cc6faa8905f94242ef99065bf41107be86a1df94c40bf2a2417d52d02f8a9995f95043fba02217d5490fee61885fd4e10f699043b754442faa021778c531af298417d53d02fca5985dd4543fba0a217d5210fba6418cf55032bea88817551102fca6217d4c110be28a81de434cbb8a6886fd5110bf28843fb20483a8a6885fd5010fa20e437e53c837aa8107d14f10bea9e21f4514cafca4207d50441faaa221f7318c6f8a8995fd4543de2a2217c53882fca1185f14542da2a2217e51d0fee6210df54e10bea94837f54443f681205f54420bf28087f521442fea8107dcc910bea8043f443c42faa5987d94420bea8665ed42c82f8a6886f10440bea90837c54443e86390fd101109f2a0617c53486fea090dfd5130f7908436d52103ea20087dd4d109f2a643bd4310feaa2205f94c30fbaa621f641442faa018d754f21fa208437d520c6f8a890fd8cb10bf294637e53843bc86985f54840faa8c417d500cbbe6518df54f42be28287f651902faa3a06f50040eea18877f54086e8a2995f15231bfaa065f920082faa3a1fbc8020cea18877e54043e88218db54b31be2a4617d53886fca3205f95320ba28a857d51882faa610dd94640f7212417c53c86fca120fdcc710beaa463de43ccbde85215f15331ef990637d53442eaa3105f94d21bfa9021ed52103da64197d54b10dea14837e548c3e883885bd4910f6a1043fa40102faa021df54730beaa465f432c42faa898fbcca32bea98217f524437ca998df54342bea96637e52d0f7e8621df94321beaa4417c544c7ba64985f14941bf29e835d5310bd842105f94832faa92217e50ccafaa690fb50842be2a0217e530c6f8a810df14a10dfa10837e540cbda84995f14f10bf2a4637f54ccbea40887b94830fb28861be41506fca890fdd0910be2a6417f53887ee6298cf55020fb18863f45150f7e81205f94a10bea8e85ee428867aa998dd54640bf29a21f721c43ea81885f94f21dfa12817e54443da65907d0c421bfa9a857e54086f8a0a0df94c43bf29c81f642442faa5886f50c41fb906217f535077a84215f54430beaa6657c54cc3f621087d84110be29a416e52d06fca5197b08620fba0e63bd43502f8a2905f94032bf280437f54886fea9887e8c030f7904417e51d03eca4885fd4940fb28c617f53c87f620887cd4110faa1a217f548837ca8187d94620bf28c83f420c43eaa6887d8c710be292817f50507ea85885d54430bf29663fb308c37c832077cc230b6a9061f421c42faa8196fd0842
  | 1 => 0x910043ea63885fd4132ef21e61ef324cafaa818dfd4143fb90c43dd434cb7c82205f54e20be29e41f752443eea2a15dd4542bf288857f5050bdc6510fd8c9109f2a6637c53502fca121df94410f790c437f544c67aa8185d94410fba06217e5190ff660987b90b20be2a0657e50cc77e85a05f55132bea9487bd54c87eca6885f14c10bea8687f741c42faa720df95130ef29e43f530c42fca3907dcc510fa19221f521c42faa719778c932bfa9c41f652c43eca8885f54c429f2a0417e54cc2faa1a0df54a10bea9021fb40502faa8105f55331bfa8263de4310fbaa6217b90821f7290817d52d0efaa810df54732be2a0617f544cafca01077d4d10fb29e217e52906fca0206f55032be29c43dd434c3da40107dccb10dfa1e81ed424837a87a07b50a21ee99661f441442fca820df94841ef98c637e508c7de84a15f94221fa20621bf43906fca990d714d10fb88021745150efea690fd90710bf29a41f721442fca8207794c20bf296217e510c3ba60185fd5231be2a4437e520c6fea990f794c42eea1e657e54886fca710d794c40fb18a21bf42906faa7217b54830bf28085f540442faa7187b14910bea80837c504cbbe6218fdc8110f710c41e45244278a8885f148109faa2215e53d06faa8885d54630bea8c617e52d02faa520778c130faa88617e53d02fca018f5d4d10fd100417e530caf8a6107d14910dea1083f554c437a8720df54a21bf298217f524c7dc84217d08510bf28e61f431443dca5a0dfd4530fba9e217f54cc2fca7887b4c920fba0c837d544877a8220fec8220fa2a6217d54842fca5a0dfd4d10beaa641f542442fca720fd95310bfa8a857e50842fca1a0fb54b31bf28481de53103ec60885f94a43dea12817c53506faa6205f54321fba96217e51107dc4290df54442baa8c21df32cc2f8a8907d08110bf28865ee320cbdc4210734c832faa0a21de438c7baa790df55230bfaa421f643443ee6390df14d42fa906217c50486eca2185f95310fa212217f53083dc40905f55310be2a643f742c42baa7a0df95220fb10843dd53d075a84215f95210bea84637e51102faa321774c832f7212657d528c2eaa2105f54242fb216217e5390aeca2205f94a40dfa14857d50887ec40885794f21bfa92877c54c43ee21085f94830deaa6637e54ccafca620d794c42bfaa241de318c2faa3907754c209f2a0657e5190b7a85a05fd4f10bea9c81f543c42dca4185b94843bf2a663f750443bc8618dfd4d20bea94417d540c2f8a8985f95132be2a4657d52442fea5886fd0f42f719641bd43d0afca721d754c20ef29e837e51ccb7ca990fb4ca21de20c817c5150efaa2195f54331be28a65f532442fca818fd14542ef99465f621c42fca8215f94910fca00817e5210fb863185f14931bea8483f551082faa3195f95020fa20
  | 2 => 0x4501003a000080a000940183a378061000008806078044d004028040f80401076698220010603b880239a6280a00801680a00000e02014078860100a03800000220103e0c81a06000019fa00088011082101a1b00602006008040a00655838038040a810028020000400012543ac0204e0a8260002205848fb0580080c048003700200956a389200802038040384c018100095400004038560006a0390291008020109e00a020d2000001f01200936400000080a1280c668280305a0080a000089a04e188000080200012108003c9400d92c180420005a2182c1280e02008028220020c012de0b8340180003018028060680a0a0060d1300005c1f0020f01a0a0060e00e4e802130080480a00008030060302423004000000083a0180e000900084407026020022f02e020005e8040000060000248246c1f8000000303a25800498c003064165f14e10bea84877d5190ef8a818df54c41afa9a21f75150f7ca8105fd4c10bf290437d54043ec42885f55240df212857e51082fea2907750e31fb21e217c54882d8a4887d50710bb28841f431c42f8a9087d0c110b7296637e52083e885885f95232fbaa221df324c2fca3106fd0c41fb18621f741c87eaa3207d14b10fba8a65f730443ee4290dd94620dea1a85be4350ebaa6205f54830bf28465ee5210fe8a8887dd0d10bf298417c52442f8a0a17d14d10bf29c417d51903ba8618df94742bf298437e518cafca218f78c430bfa9421bf401037e86a05fd4540bf280837e540c2faa9217b8c920bfaa4657d52d06fca5217d10d10bf28685bf41906fea2997d4c431ee98863f641106fca310df54e31ee18861f741506fca1105f94030f690843f532c42daa5a0df15020dfa1c877c5250efca318df55241bf28c617f524c3dc85197dd0421bea946377514caf8a5885f55321bb28c61fa10042faa6105f14530beaa4437d53c86fea890dfd4d40bfaa641ed5210efea4a0db94840fba0863ef52442fea818ef95032f3a92217e520437e86a15f54d20f6a96837c53086faa8987d88310fc98061dd53103be8721df55330bf29e857f548c3ea4210fd54630fb20621f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x4410874d53c8020d9d8552cc6f160951109d18554cc2d66310b10ad59030442746155130cd152524427a6014c21ad992544426e62150109798c54482f36054d108f59253c426d6215031b958843c436752d4110cdd91518c3546354640c714d4350a776548421ab593210863d6414e108fd95411072d5494830b598e524427661150309d58753882e76255110d5d8553c874c524c930cb551520c26d62153319d18553d027761553309b98854cc6f1600c910a7593310c7a75414910b5d8d524423c6454d208f19152443676154b41d514f21442b6640c3109dd9532443d053d4110d5544318c27561152309d19532c427661d52209d18552cc2d76150c31cb50d5210f6762546409b58a544c67b6055132ad99253c431d548c430c7553300c27661141439758e524423c64546209bd95200832d52500409d587548831d54cc832cd55251082776155130c7951438c66f6254d10bc580424423f64546309b58853042f160d4f10d999452443a542104219d98453042746155320f1d85320cb5453d4110cd15331442756194342b958b31c42776154f20bc58253443655294440cb552210826d62d4543d954a510c2b464549109d58650cca3d6414c108f592530c72d42944429b988544c34f53d4910c350d5210f1d53500409dd9542c427461548439d19543c425f654c030b998b31c42756194242b958b410876652944308f590534827a60150219d994404423d6494a319b58853843c5320cb10cb5095010b2c54d4910d3549300c3a454d49108f994544434d43548438fd91518831d5454f21b998a54c435663d45429d99731442756115220b558f21c425e63948219dd85544c6d56394910b998840c432c5450a329758c54842e662d07108f993530825e63951219758c525025e63153208f992520867560145328f596540835453149108f99053086e76254d10c754d4210a766588110d394d32886776155121e91854210b555394440e350d424ca7661d5232cbd954210b1d5454c209dd855210e3d6494910c7552530833564d4532bc98043442d66395310ad59252c427561d5230f1d4f524431d5494f218f992528c67661d52309d1855310ae96008420d354d521026e6294910b958840c42b66515110ad59321c431c5350d409ed95401034e4354843d994c524426d6294e41c715053442d663d0421d354d20082b56494d10d9549510c3976150c43ad59331442e56294f10cd95031c874d53948409b988548c23d6494d109798c528426d6215230c794d43906f36054910b598f214425d63d53219d987540826d62951219d5865090e6e62141439dd855348274654c5109798c540c2776154b308f99053482b664c85109d987538834e5354b41bc580434433561d51109b195324826c6255130d5d8553d07565394420d914831442766114810
  | 1 => 0x425d63948219d987530435763546209e58054086f16015310d5d855310a746154f20cb150524427561951329b98a54c42d663951109dd8554c839754d4d10b558e52c426d6590821d594f41c86f36055110f1185320ca776154b408fd954310e5e6394a41c750e5110f4d5350842e394d4210b4e5394b41ab58b411075563d4542dc945100426e6214d40ad18543d0b7265d41109718d54442d66394d10e51854310ecd638c832c715143cc32e5454b31e3551320cad563083108f59252c42f2600c910b958b314425d6314a109798e54c423d6494821d514e52443645288510b958a54c425d6394a41d354e4210a776155132d314d32086e662cc510d9544218826c65509209718d52442d563c85109dd8553d02d663d07109d9865090e746155132cd50c5150ae662d04319d587540825d63141429e580540c6e66210110cd150214426c62546309b58a53c43e12008110b598f41c87c75314910ad59032c42e46150932cdd8554cc72d52d00409d9845050a3d64d4c20d914b414427561940429d98650cca7560d4532b998b41442d56310b10b318d424cba45414910ae580411025e6314142ad5932144276619423297d954310f8e544c832ad99020c427661d5030b998830c42b664cc7218fd9540103954310f10cd191518c2746154d209b189534427661940329758e54c433554544309798c54086e5620c310ad99032c43c5320c9109798f540827761550329dd95310c65e63952219758e544866e62150319bd89544425c6550d30b998843c42f16014f1097d95310c6b664cc710d594d51102e562101109d99430442766508110d958b5150ed46355110bc582524423f6550842cb551320cb4c53d4910d5d4c314431d540c430d550c514caf160d5310b598c20c431d53d0040cd544419025e6514d10cdd50414423e64d45328f59053c823d6414c21a7593318c754538c5108f99252c427661d5010cb15142482d563d07109d19543442756194043d594c41c867661141329d584540c2766114c209798e52c425d6315320c3551320ca3e64951108f593514cae7614c821cd55041cc6e662d0731cd99454442cc6250d32b91895344277654cb10a758f41106d463549108f191518c31e5494f219758f540832d54c8020d3d51320ca6f62546409798e524423e6414e20b358f210872d5290440cd15253442d563101108f990504cb565414d10f8d4b504425e63152209758f5150a5f63549109b58b540c32d5448020d590c514ca3e6414f209e980540c65c6354640c915052442d66514d108f99053082756194032e950842c42776550910d9148414431d544c030cbd50524427661940429d19541443c453d49109b98854cc29d63d0641cd150314423d65950309dd9543c426d629523197d95320ca3f6454d20d994a511036454149109d59
  | 2 => 0x6590110b598f41443545414d108f992530c6d76355110a75924310ee66294d109bd954210a6d6294d10b558c204434d32540328f590504ca756194010cb15142c823e64d4f219798c52502e46255110d9d48214427b65480209798c53082d9600c430d9950524432d5454b319d584504ca6f654c832add91534423d6494e21ad59032442e6620c1109e181544ca5d63951319d5835150e5c6354620d554d511023e6494910ad59331c42b664949109d997414434c534c920d9d89518c2d6630811097d8d51902b66408110d314d32c834c5314910b558c42443c45314910cd951510831e5494c20ecd53504427b6544010cd951510c34d528c430c795153c871d53d0842b9588304438d4394843e51535344335519044097d8d518834d52cc0309b988548436542145329b98b5150fd1300c110d594d51082b6640c9109b588540c2b664cc510b9988434423e6414a10e550c434426e62150309d19542c43556114d109d98753082ad6490842d918951903356115110b558f410c73754d41109b58b54cc71d43548439758c54483565394440b5d85320c63d6494d219d195324433554107219d984548825e6314810d514c214432c5250940b598f21c42756194343b558f414434d53084209798c540cab664c8710cb949429067665c85109d5805150a7461551209d5845050ee562cc4219b58854cc32e5450a219798e544426f6548421f814b504426d62951108f590530832f4354843b358b310c6ac6250d429798f54c866c65509329b994524436462546308f191534433761553219758c54c874e5394840d9d855210f1d43540439d584538827560d45429d99630442b564083109d195424423e6414e10ad992534426e6214c109d586508ca7561150209d9865090b374314542e354d4210a3e6494d219798c54c87576354640e9508424426e6295110d914b50442e56294d10cd185540ca7561d4c20b958b41c42746155032d354e52d072e5494b31ab59321886f160d4b109bd89544c36561d4910b358f218863e6415030d914c524425d63152208f99253c427761551209b58854042f16014b10c7d53534434e5354840d3551320cad66310910b598c40c433454905109dd855310b5561d4d10cb54d4210a6d62141439b58a53486e56295110cb952520c38d4354843ad1915344355530c721add85431066f62546309798e534436642145329b98a544c6e56210d10b999452442796014c21ab58b419073554944309758c54086d46150d32c354d4210a766115010d518d51882e662951109dd9510042776154d219d594410c6766195132cb951520c2e66294f10b358b318c66d658c8219b98a539063d64d4f21add8542106b6640c1109d98754cca6e62150209d98650d0b1c5450d32d3d4c52442746154b409b98b540c2776550d10d114c524
  | 3 => 0x301000801000a600401028010080c0ecd10007501c8f0000000c0106c130000100c05009750e803224020011f00000004040404802002014061f80d1b8050640006c0813801000050543900000004100646604c110147b07c0100c000682500401474181a00300c0e01c0002c09000060083500801008170042f2084c188023541121c0001c15000050140a0f80e0041400004100050a4020000001c0400020054ac0051304c3c00013034060500000c0e004a90c41d000054a4010a8020d00504808000000a82e000910200900400004b70080000c0b0a800000095a8072a4000400b0100a07c230a801000022c402014000a400008152c006110059082f000100080302800030010104306403a54100441e43c001811b50c0a1505002001000040c4000016903000011150e008014010040704014014000041c47c0c0280e1182700c388fd9152443555394420d5d4f504423d6414a108f990524c3d353d4110b558e54c42b564949109d59431086e46150a329758e54442b56408110cd55151082766194043cd19151882d563103109758c540432f54d49109b988538434d5388420d9949510c35453d0510d34ca510cb656114910ec15350442e66294910bc98042442756114c20cb548411031f6550c43e5150534434f654c8329758c540835553544209b98a548c63e6414c10b3d95320ca3d6414810abd954210a3e6494e21cd952510825e6315210d994b41cc6b66494b10ad993310872d548c8329ed95300c27561d5332b958b414431d5310440d998b5150f546154c429b58853502d66310110d5546310c33454d4110b598e52c425f6355110cdd85540cb3664d45329b588544c34d520c430cd150524423e6494d10cdd91518836461548439798f5150b3454c8510d354d52d07c5320c421cd952510c3566514d10cd95331c87a761508429758e52c425d6594c209b58a54c42d56395110d954621083665254440a7d954310f4e524ca31cd15053443b140101109b98a534431d53904409758c52042766114e209d984548c2d46150f32d9549511023d6414e209e596100432c54509329d587540c31c5450c31cb15142086b764549109d98454083a754d491097596430c66c62551108fd9153442b5640c3109718d544825e63150108f59053c863d65950328f99053c876452cc510cb550210826e6294f1097d8d544826c6254640cb55252cc6e761508219d98650d0f1e5454c209798c54082756014543ad1854350a6d6215210d514c414423e64150209b988530831c5450f3297195434cab56494f10d994841cc65d63952219d5845050b145414d109dd95411063d6414930e5d50534427561d5232c7153534426e62d5331c7151434c27661d4810c7551320ca3e6415032c7d50534426e6215032e550c410c67465485108f9905204276
  | 4 => 0xd84102800158010004401c06080050807d0140000008004260043c28482000000fc04260aa05c4e0
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x14204c00081c500060801800002120a301040e00087000039000242800a04191087000000245d847150d424cb14aa2c010841a150d6210d10c52a4b00822050d73149425030ca9ac020881435cc5450821d0ac8990658870553d854210b42b1a8421621499d25314910d8264b006488526749505244342a18c2a12658550c6154843a48eaa108488434755903244286b98a8a1241c150d4214532a1ae829a6410f0554d85320ca8a3aa8621a21c11505314910e0a8630aa421d1970151430c686b94a8a1c63435ca5350e41c28a931ca4886445398b4144382aa0c299065a85912008110a8ce7298a4887047154d4210b122a4c598a214a5c05450821c88c6312a3207077150d5210f50a12c021221435d6544c832a1ae929a6510e146418d5188342a1ac421e21435ce5250a41e0a87b0aa421f047150d5210f48b226018221511c5544c832d0ac899064885467295053442863aa86a1265c1d505314910a92e029a6410e266414b3144324a9ac01084186551600c430a1ae92926518f045414f5244348a1ac021a219198c52d0510d42c4a0080886166414f214429238aa6a1085191d56210d10d22c6a0080886856350842443822a6a629221c1dc55350842e08e2aa2641950d7414d32c8360b12601822192549600c430a1ae42a28618d0d739514288712320c4a8c61831954350932a1ae829264986166414e52442a23aa6419221b058d2008110a1ae42a287986245498a5344286b90a8a1a61435c85350d40c28a931e42884547558c4244286ba0a699241519ce5414910e0ee2aa2641950d7315142c8382a98c2a1085459d25414d10
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x40000000100010000120000009078750f6154843a0485591320c910a0686dc55350842c047558d4210910c0475591320c910a048558d4210910a0686dc5544c8329078754f6150842c047550d6210d1090787553614c832a048550d6210d10a0686dc54354843
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 741
  | 4 => 794
  | 3 => 91
  | 2 => 12
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
  | 7 => 2*((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s3K6 (672+(h % 28)*6) 6) % 42)
  | 5 => 2*((h/261+packedAt s3K5 (20007+(h % 261)*10) 10) % 741)
  | 4 => 2*((h/292+packedAt s3K4 (30172+(h % 292)*10) 10) % 794)
  | 3 => 2*((h/44+packedAt s3K3 (4459+(h % 44)*7) 7) % 91)
  | 2 => 2*((h/32+packedAt s3K2 (720+(h % 32)*4) 4) % 12)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc1ffffe0ffffff81fc3fc3fffc3ffffd11f1ff
  | 1 => 0xfe07c3ff03e1f0fe3fc3fc383fc38382eececc
  | 2 => 0xfff803fffc01ffffc003ffc03ffc03ff0f0f0f
  | 4 => 0x3fffffe00fffffc00003ffffc03f00ff0
  | 5 => 0xfffffc00000000ffffffffffc0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x44100022080000000404404884048888005055
  | 1 => 0x8cb184463942a1161c41c4119c41191866c6cc
  | 2 => 0x1062aa8850d548aac222aa822aa822730b0b0a
  | 4 => 0x39453310a2906acd6aa8220433327023b00da0
  | 5 => 0x2186221cc3198cf1b333332702204043dda000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeaa0a0eeeeeaeaeaeaa0a0eeeeeaeaeaeaa0a0eeeeeaeaeaeaa0a0eeeeeaeaeaeaa0a0eeeeeaeaeaeaa0a0eeeeeaeaeaeaa0a0eeeeeaeaeaeaa0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37993
namespace PEqualNP.Outside.L_meta_37993
open PEqualNP.Outside.L_meta_37993.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x1083140000400340016000015607000a011804437c1dd30f710fc32fe20fe40fe10fc31f741fd10ff40fe43fc10ff42fd31fc30ff20fd41fe32ff21ff43fc43df30fe31f441f510fd32fe30fd30ff41fe42fe21ff30fd21fd42fc21fd40ff10fc42fd20fc40fe41ff31fd43fc20fc41ff32
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x40800001989000802c006000400002000014e011e0800000640000000000000c000060228600001900000080060400300009000a0800400400800000008680071602580006a0020000101001f77514caf4a0195d54432bba8a815c53486eca2106dd0841aea9c217550d06eca321dd14540daa1083d530442f4a018d794c10ea20e615f5350abaa7185d54610f898221755190a7aa990dd14543baa8c815e53102eca3206d95041bb28c4176510c268a8887510530bda82855d53083ae8398744c110baa8c875e53842eaa2207cd41109eaa0653e54082eaa020d7d4d21eb98621d9308436ea8886d10440bb2a6217651906f2a121fc8c1109faa2217454442eca3185d54630baa88615e53882eaa31076d0130ec202617454c427ca990f64c220ea98621b4544436883205754e40bb288815d530427ca8195754c40bca80657651043ae82984f15110bb28865d930482f2a018dd54420ec982217654442dca4205e14142ba28a657654106e8a2a15b54840eb982217a5090eeca32176d4130bba8a875e530c2bca6105714d429eaa0415d53882eea2a15794e40
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x180002ac0050c2310351514c220e4104404c352544c110ac1814210730548c1109658053486c96210130e41513044314544c110c6151304431454cc110cc15130442d1638c110d41513044393544c110b4580414c23664951108d1915188310544c110c954841102d16110130
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x510745453088340b108220261449d2544c110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/36+packedAt s4K5 (736+(h % 36)*6) 6) % 46)
  | 4 => 2*((h/89+packedAt s4K4 (2673+(h % 89)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s4K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/1+packedAt s4K2 (147+(h % 1)*2) 2) % 3)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf87ffff81f87fe0e3e1fe3fffe1e07fc8c7e4f
  | 1 => 0xff81f87fe007c3f03fe1fc781fe00780f3b38c
  | 2 => 0xfffe007fffffffffc001ff801fffffff03c3ff
  | 3 => 0x7ffff803fffffe00001ffff803fc03f0
  | 5 => 0xffffff80000003ffffffffffe0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x49142408c1289202068a20a8cb1224a8841645
  | 1 => 0x532c5491473316701aa8e43157305518b1b38c
  | 2 => 0x200891220a040094400149020444925102c09a
  | 3 => 0x4651664494219b2aaccc002499996422dc0360
  | 5 => 0x84618007184621cd31119247000180436b6800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaf0a0f0a0feeafeeaf0a0f0a0feeafeeaf0a0f0a0feeafeeaf0a0f0a0feeafeeaf0a0f0a0feeafeeaf0a0f0a0feeafeeaf0a0f0a0feeafeeaf0a0f0a0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37993
namespace PEqualNP.Outside.L_meta_37993
open PEqualNP.Outside.L_meta_37993.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x126d10a44c910208001430844a18e044fc20fc10fd31fd10fd32fd20fe10fd41ff10ff40fc41f510ff30fc30ff21fd40ff20fe20fe31ff43dd30fd21fc40df30fe40fe21f441ff41fc32f710ff42fd42fe30fd43fc43ff31fc21fe43fe42fc31f741fe41fc42ff32fe32fd30
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x6b7c404f03733c08916b10001e2010014000000068f807004735002c2bc460c692afb454442baa7085d54341bb28c857551083b261085794c20bb288815d53902eea2a1dd94430ea20a615d53102baa6105e14142eda02615d538c2eaa321cf55321baa8083b742106eca2195794c40bb28c87d5304427aa8195e54243aea9821d741cc2e8a2a1764c2209f2a6435e530436883205d54430ba2a22175510cae8a9885dd4542bba8a657a5090eeca2085d94640da208815f53486baa7105e94031eba0a615e53883ae61885794e10ec202616d52102b8a6a17c4c110ba28a6575518c2e8a2a1dd54620eda826179500caeaa3204f95020bb28c83755190aeca9884fd5110bb28c41b542107a883985d94420afa9a857551102e8a2a06dd5110ae29a433454442f2a018d794c30ec982213d54082eca8885d54610af29c817b5050be460884f15110db2a083d530c42eca820fcd4110ec982413e540cbae6088744c110bd280656e52102eea2a05d94630
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x88e8180000412020330548c110b4584404c2c96210130b458e3044314544c110c515330442366495110cc15130442346454620d454530882b06050841c95484110350544c110c41513044393544c110e4104404c2596014d21c61513044390544c110b4580414c352544c110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x512749513044340b108220261441d1514c220
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
  | 5 => 2*((h/22+packedAt s5K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/40+packedAt s5K4 (2673+(h % 40)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s5K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/8+packedAt s5K2 (147+(h % 8)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf87ffff81f87fe0e3e1fe3fffe1e07fc8c7e4f
  | 1 => 0xff81f87fe007c3f03fe1fc781fe00780f3b38c
  | 2 => 0xfffe007fffffffffc001ff801fffffff03c3ff
  | 3 => 0x7ffff803fffffe00001ffff803fc03f0
  | 4 => 0xffffff80000003ffffffffffe0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x49142408c1289202068a20a8cb1224a8841645
  | 1 => 0x532c5491473316701aa8e43157305518b1b38c
  | 2 => 0x200891220a040094400149020444925102c09a
  | 3 => 0x4651664494219b2aaccc002499996422dc0360
  | 4 => 0x84618007184621cd31119247000180436b6800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0feeaf0a0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37993
namespace PEqualNP.Outside.L_meta_37993
open PEqualNP.Outside.L_meta_37993.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x100110802006005410870240030d50c0049a4049214008204908c017f90c01fd42017f54c03fe50027f14803fc5000ffd0001fd5400ff54009ff5200ff4c003ff30017fd4c03fe2001ffd0805fd3100ff0c001fe4200ff84001fd4100f7cc003fe3000ff90007fe54007fc8401fd51017fcc803ff5000ff10005fc3100ff48003dd3000fd44005fc32017f94c03fd10017fcc405ff43017f14c07fc41017f8c803f71000ffc8005fd4300ffc4001fe5200ff08005fc4301ff15003fd40027f14401fe51007f54803fc1001ff10807ff41027fd4405fe31007f08401fd21007f88401fe41017f4c809ff54
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x84a407ff98c21085fec710843ff438840bfe2084205ff8c6210effe60a881ffd619084dfe8848404fd1455106ff8a69081ffc4294821ff98c420dff58d21037fc201087bfe3154455fea1aa403ffd0d41007fa8210802ff648840fff2904206ffd4021107fa612886bdd30904017a30aa803ff50e4103ffecb90806fc60c840ffeb1c8407efd0a420bff840a0803bd429041bffa1a4213fdc432111ff820a101efc6590807fea028203bf1925103efacb90837ff534840ffe2944200ff58552067fcc090803fd540841bff98a4209ffd0421027f8a7290a77d5054807ff21c842fffcc15413ffa632108ffc305081bff18a4207ff9494209ffa219081ffe325080fff104a417ff8814117ff840aa0bffc6055047feb028411ffd0a21027f8a4a88b3ed2094807fe20a8404ff151520f7fcc6a888fff5050801ffb2a821dff98151027f8a6a881ffc5248441feb04a207ffc8242027faa6a90b7ff439485fff082a82fff8815411ffc20a1013fd5494407feaa2840dbfd8d2101ffa84a082ffd308845ffeb02a81aff4824102ff8c52880afe6390845ff324a205ff18a4103df8c72900afc638843dffa1aa200bfd962106ffe649081eff60c8407dfa1a8406f74c021007fac89081efc6308407ffa0a8405ffd8e410c7f8c6a0843ff328844d7eb048406ff9402103ff88510817fc519440fff906420effd092102ff8c610883df3094407ff2048404df14251007eec2aa00efc645480f7f314a201bf1825101df8c89081eff6408441ff084a20fff19521027fea6a880ffc4250407f7a14841effcc551007fca2a0877fd605440ffeb0ca403df15154165fac129063fc5350447dea02842dff8c65203ff88490852fd63c84077e3244204ffd5152186faa6aa017ff6408429fea1e4207df9495202ffec728876ff6054435fb8848213ff9032101ff8a9210b7ff3194827ffa064203ffd024202ffca31089ffd5390831ff98a8207fb10a42027fea7290c3fd63550377fb1c8204ff14d5411dfac0a101ffe3208431ffa9a8223f74c14203ffa4010863fe3150409ff2a4a223ff94142015b8c69081ffc609482bfe2a6421aff44241067fa6090893fd5350807ffa1aa807ff0c952026fea0a9013ff535501bfe21a4200bf58642027fea4a900fbf4290401fe312a830ffcc5540fffe84a88037d54548317fb1a8210ff10e210cff8a4a0803fe514840ffe294a404ff94551027faa1288c3fe315503ffe212a22aff90d5203ffaa52101ffc65c8429fea9e4201bf98154157fa64a9083f5109440f7fb2e4200ff59641027f8a4aa00ffe4290407fa20a8205ff14621107fc61288a3ff51908537eb02a404ff9415103ffec729077fe30544017fb128207dfd4a5203ffea52106bff2090461dea1aa803ff1024201ffea92101ffd52c840fffb1e4204bf99721
  | 1 => 0xffc41908017fb2a4207df14952137fc21210137f5055009ff29aa801bf98242025fcc328802fd65c843d7fb1aa208ff10c2101ffc84a086bfd5090401feaa64205ff9062109ff82190817fc6008409ff282a405ff0c42103ff8c19084fff50c8409ffa92a813ff0c32101ffe832100fbc409040bffb28420eff99121137fea121003fe4148419fe2824215ff1072101ffca920863fd32504057e31a420dff4c52103ffa652900ffd5490853ff202a40cbf58121005facb10877fc4054401fea14a205ff8842105ffe6110817fc5108427ff0864230ff4c9540bdfec0a082efe61084017eb2a8200bfd8554005fec4a8886ff6394407fe21a841eff90d510bffe20a08c3fc63550017eb284202bf98d2101dfcc8108c2ff6355035fa884822abfd8d520d7f8612080eff6555001ffb12a80cbf58a21005facb21006fe60c842ffe2828200af593210d7fc6120803fd629040f7e31e4206f7cc02103ff8cb21057ff41c8419ffb024229ff48152167f881290bfff105500ffe104a424ff0c542005fec8a900ffc4050401fea8c822bff1915214dfec0a9013ff539440ffe1044203ef10541137ba6121087ff31944077e322a226ff942420cffccaa086ffe3290409fe29ca203ff90d4116ffc872902ffd4088413ff2a04229fdc415201ff880aa01fbe42508037f3028400ff58954027fca72906bfe50904017eb148225ff145420c7fca6a0887ff439440fff324a403ff90d5403ffc65210037d5294407de20aa807ff99021067fa8090893fe6350817ff1044207ff4842103ffaca1080efe648840dfea804207ff5824202ffc6328817fc1090427ee986421eff4c551067fe609084ffe50c8407ff20a8204ff14a51037ea201081ffc2048409bfaa4a207bf18951067fc409080ebe64c840f7e324a404ff1425211fbe60a101eff609080ffe30c8418ff98d41007fca52081bfe3008421fe29c421dff88151007fa8510803ff6155053fe882a42fffd8154007f8c4a0812fd659440bfe20c822aff18d520f5fac6a886bfe109040ffe9048421ff10e51015fcc61088ffd5050831fe98a822cff5025201ffca8a10137f529440fff32c8404ff1415416ffa632906bff5090453feb02a400ff50951007fcc4a080ffd405500ff7904a422ffd0a5102ff86328806fe6088401ff30aa829ffd015203ffa419080fff41904077f30c8200ff5092101ffaa92081fef210840fff1964204df145520bffe60a081ffe63908077eb248230ff4c554027d8a4a908bfc429440fffb064202bf98e2111fea20a1017fc100840fff902a400ff5442102ffec520802fd6488443ff994a200bfd954203ffccb9088ffe305080dfe1804207ff58f210eff8c0a8843ff5388409ffa8aa407ffd8252137ee2121077fc2054447ff3028400bfd91510effa80a880eff6150459ff9
  | 2 => 0x21106fca12884bff5188453ffb02a407fb14a5203ffac929083fe6094425ffaa44207ff99421007fcc2a900fff42904037f3048202bf98d4202ff8c11081ff5210842fff9028200bf986420f7fa86a8823fc53084037e304a428ff14642027fca8a901fff2094811ffa184203ff10a41027f8a128813fd5254409be28aa81bbf58e410effc80a8817fe3108417feb044224bfd8d4200dfcc09081efc64c8401feb12a200ff5492101ffa872101ffd65c840ffe192422dff50e52027faa0a901efe629481fffa8a4220ff10251027f8a8a881ffe6090807ff2028200ffd9152027dea4a90a7f51054859ff204a42bff1055213ff863210a7fe3054807fea1a820fff9952110ffc8728823ff5308443ff31ca203bf99152047fe621080ffc545040bfe32c4207ff0ca210effe80a8843fd3188409bfa8ca207ffd9642007fcc2a104bff52884017eb224224ffd8d42097fccb10813fe539444def9848404bf9964101ffca92101ffe428841fffa924203ff50d5401dfec4a105bfc51c840ffe2904203df951540d7fa6120897fc65508097fb2aa203ff9015417efaa0aa043fd32884097e32a4223fb48142137fc6121003df6348421ff21c422cffd0252127f8a6a100fbf40508017eb0ca404ff1525203ffe431081ffe60c8427ef9864229ff0415214ffc20a900fff435080f7f314841aff5824103dfecb2108ffd305080ffe2928407ff9092101ffe80aa063fd5350409ffa8aa805ff9464103df8c810813ff5154409ffaa2a21cff9964103ffe8410893ff315080bfe3204226ff5424201ff8a8aa017ff10884357eb048229ff0c152067fe209080afe6394843fe98ca224ff8c542167fe2129006fc6050421fb18c421dbf5815109ffaa190837fd324842bff2a64204ff54d540cffea4a0867ff515040fff9904205ffd9251007f8c2aa013ff519485b7eb1ca424ef50d42007faa4a080ffc439040ffe2104207ff94952027f8a0a881fbd64c840fff90a420bff10221027fea4a884ff510c844dfe0848407ff986520f7f864a8813fe535443fff322a200fb8852101ffea8a0813ff5054801fe30a8407bfd955206fec629080fff4250809feaa2a407ff0ca52027fea929003ff6448457ffa0aa402bf98f21107f8412888fef205081bff29a4213ff8c321007fa839081eff639480dfe9804205ff94421087fca71081ffe609481bff21a4218ff58d41067f880908137f535480d7eb00420cff1812101ffea8aa006fc6008401ff212a205ff1464103ffea529077ff105442f7eb028202bf98d5403ffec12101ffc4250817fe2844207bfd942102ff86320812fc655044dfe184841eff18d51127fe64a106bdf309043dfe992a220ff50251027e8a328863fc32504077f324a220ff8825114fba60a901ffe529080ffeb004220ffcc251007faa39080
  | 3 => 0xeb04a407ff18242027fea0aa00efe644840bffb2c8221ff58e51015fcc6a080efe64c8411ff2984203bfd914101ffe82aa09ffc53908017fb2c8223ffc414215ffe84a901ffc529080ffb90c422bff9915210ffa872881fff64c844fff18c8404ff9425203df8c4aa00afe6394453f7902a42fef5015402ff8c72880fff439084df69048420ff9025113ffea721082fd60944197fb02420bff44221027fea528806fe605442fff2828207bf194210efee20a881bfc5008401fa30aa814ffd0f21167ba612907bfd6354407fe2028407bf1894103df8c72101ff7214842fee9828204ff1525103ffcc321033f71048407de20a8423bfd814202ffc8210802ff6550431ffb1a8220ffd025117fba60aa01ffc639481bee31a421dff481510d7fe6120863fe3250429ffa9e4214ff14f21127fca6a1023fd3108401feb2a8407bfd8c2117dfec0aa017ff609440bfe328420cff44121005fac8108127e65c84017fb0aa404ff941540d7f8412086fff3290407fea048226ff4c24201fee8320803bd545080f7f30c4201bf1814211ffc40a1053fe31c8437ff31c8214ffcc72117dfac0aa077ff605440fffa148407ffc822101e78a8aa002fc615085fff902a829ff4c15203ff8c9908abff325480fff194a41aff8824111ff8a0a1006fc605442ffe9028205ffc4251087fac710813fd5294407dfa12a807ff4825203ffac81080fff405040fff192a405ffd8c21027fea3288037e515440ffe2964210fd4c6210bffcc0a081ffc63c8409ffaa4a210ff50e21087faa71080ffd4290407dfa1aa807ffc8121015fcc72080ff44190461ff192a801bf18154127fa62a10aafd6354849ffa9a842fff481540bfee20a0803fd649440bffb048206ff5002102ff8c12086ffc5390417ff2044200ff5952117ffcc0aa01eff64c84057e31a8207ef9932103ff8852106bfe6090459fb884a405ffd822111ffec0a101fff42c843bfe882a200ff9895103ff84010837fd43484077eb248407ff5964206fea62908abff6354809fea9aa207fbc8242005eec2aa01fff32908097e32a8406ffcc02103ffe65908037d54944357fb04820cff9012103ffc401082fff4088423fe2a44221ff0ca5100df8c120803fd62944037e302a402bf98d5103ffcc79088ffc605080fffb0ca407ff5082103ff88590812fe6508409be28aa204ff145520bffa20a0853fc43c8455fe18aa403ffd0e41007fac2a10b3fd1094801ff28e421bffd4e4117fee20aa08fff3050801ff214a20eff15121007fec4a0836fd6348419ffa024207ff08142027faa729037fd53484617eb1aa807fd884210dffe6320887fd3294427fe9864229f7cc1520effe40a8873fc5290407fea028403ff10e42007faa51086bbe409040bff18c8226fd442420dffac72081ffe52c8429fe18e420fffd51
  | 4 => 0x1bff4008401fea8c4213ff1032105ff86110833fc304845bfe18ca400ff98a41107ba612881ffd5208411fea984204ff95151137f8a12100fbe5490409fba8ca204bfd855103dfec8a10ab7d5354849fe31a8407ff5932103ffcc0108b3df309480fffb24a404bf19621027f8a2aa00eff6455009fea82a205ffd8a5101ffc80a1012fe6548419fe082421cffd4a410fff8c8a8817fc41884017eb24a200bf58a5105ffc2110803fd418840f7fb1c841bff4ca41007fcc4aa077f5105440ffeb06420bbf58221125fac6a101eff6008407ff2a2822ff7cc15400dfcc1290a7ff305482ffea82820affd4421007faa890847ff4188407fe2a28400ff59221005facb20813fe5494801feaa4420eff10521067fc209081ffc20548017fb0a840affd5021005bec69080fff4050801fe30aa418bf58d4114ffa80a9087fe3294401fea0a4205ff1825103ffca49085ffe305040ffe31c8413ff1432103ffcc990883fd2094409fea84a403fb10942167ea212900ffe5455019ffa824205ffd8e21027dea52905ff5105040bfe31c8205ffc424102ffec010817ff64884077f322a204dfd4d54007fc839080afc6354401fe312a22cff8c25200dfcc128802fe619481dffa0a4230ff0c9540a7fa63908b3fe1094819ff2824203bf9925217fea20aa00afe6354855fe21aa400bf59542007faa4a101ffc320840fffa90420bff94221107ee212880ffd40908057e31ca207bf988210eff820a880afc635484bffa8a840bf74c22101ffc86a101ffe420840ffe104841fffd05510eff860a885ffc3050407ff21c822eff1065201ff8812080ffc4150407ffaa28400bfd89540bffea0a0893fd6350807df2a28407ff08321027faa8a887ffc41544057e31c8200ff5454114fda40a90a7fc6054801df20a821dff84151167f8612901f7e65c842ffe082822fff04154167f8212906ffe539040ffe9904204ff94951107fa2128833dd304840bfe31c4207ff90942007fec2a1013ff505440bffb2c421bff4c641137fe6121002fd64c84037e3024230ffd8d5403ffe4210806fe605480bff8804204ff14d5203ffc4121003ff6454401deaa48203efd064103ff864a104fff30c8455ffa1aa425ffd494203ff8c92902ffd208841bffb1a4207ff8ca21007fec2a900afc635500fffb0c8400ff949410bffc20a081ffd42c844fff98c8413ff5032117ff860aa07bfe3254435fe2848201bf1824202ff8c91081eff609485ffe882a82affcc55201ff882aa00ffd5450455ff18aa424ff4c9420efba60a8812fe655040dfe2004200bfd9121177fe8329013ff509480fff1924220ffc825103ffc41908137f5454801f69084213bf5832105fee211080fff4150409feaa4a404fdd455103ff884a9023fe4308419fe9024207ff14952077f8c890802fc615480ff
  | 5 => 0xb80012e0000000900e028000a100202c0304e006000000290080c80002a00601c1000200c05c2b80105400c0900009a128000000024640001600006407808002008018070004140d8061640180500f00e2c81d020002004210280000081081201a0342b81312e3e80013f0001ac000060000282700218e2c80100d0101980180700c01c0018548e0000100e0141600000000002c000020000000d01001664c1600006e0248900201001c0983200200401017000028021fd030024738000060000801e1be4ec0581d09805c010fd00004c1b0280aa084000000083440001802c0280680300e05c0005209c050000000b202c0900000203c0a00100c2380a00001421c0081b00609c5780b0580ac0081b14c01019802006014038d20000240e02a0020000381100001c080100523d09981300003017ef9844206fdc4021007fac4a080fff425041ffe28a4206ff4402103ffe8529012fe6550847fe90284009f597210bffa60a08abfe63548017eb24a429ffc415202ff8631085bff51c844f7eb1c8403ffd095403ffec72100fbf405503bfe982a208bf58c2103ffe652907bff32544037f302820cf7cc12103ff865210137f52550217eb1c4207bf98a4111fee20a1003ff655082dffaa64200ff98a51157fac6a9003fd6454807de2a2a804bf9962101fee82a0803ff6548423ff2a44200bf59521007facb10837fc3148407ff204820dff18d21027faa0aa017fc659040bfe084a229ff101520a7fc87908b3fd309483dfe21aa202bf18d4203ffa652105ffc6050441fe184a207ff0cb2101ff884aa012fd6594801feb22a20eff9512103ffcc729033fd6048421ff31c4204ffd4d5217ffa60aa063ff3250401ff10a4207ffd4b2102ff8832881ffd639484bff32a8404bf1964103ffe401080ffc5490447fe8828404ff94d52187fcc6aa037fe6348409ff294a21bff54e4101ffe812082ffd5088461ff992a80bbfd822101ff886a0803fd615502fef982820bfd4422105ffea110833fd504842ffeb028204bfd8952137fe2121013ff509440fff2164208ff50c2103dfec79081fbc4250817ff1844204efd5154027f8a0a9003fd6550419ff1824203ff10d5400dfcc01088bff4194409fe28aa207bf197210f7f862a881ffd6308401f790c4207ff4cb2116ff8872901ffc619480fff294421df7cc151037fc8010847fe6488453ff102a403fbd0942067ea209084fff10c842fffb028200ff54a4100df8c110802fc615503dffb1aa221bf58e51025fccb2100ffd435080bfe084422fff8c154027fca128867fc6550455fe98aa41cffd464114ffcc0a901fff2050837fe194820bff9822101ffea920867fc515040bfe324a204ff54e510c7f862a0803fd51484417fb04a209ff15021187f862aa09ffe5390801ffb12a214ff94f21027f8a329
  | 6 => 0x2201480202c0490080724a0a8048041500004508b01c060000050403800000004c3dc000260060500480a004094030020060080003800041c1088b0240000681a038000000290dc3602d80409205c1400003003c010030323480784c05c0480905b00c17c0002e0060003e00104e0183100700e0700883e00401c4900f0820e401806000088128090002982c00300a0140a05d0020000002603622c010070220840103601800c000860140001580000c2180983204c000000021f601c010020100100300500406423829008258170110000000087d02000c00002010150078060040dc1800901411c420380020000601f1765e86c81500402c0f02d0400000000700e008178060000005a00500001c4c8130f005c4200400003c0c0e614805c2e8020be0d40001618c0883
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf705932124def7259542014fe73d9621006bd64905210057f715525101ebe6150a41006bd6550a41006f632d8554006bf6550a41006f462d85540077553d8554004ff7259541004ff70595420067f735972102fe661c86210b6f651d8552004ff74597210067e4359721004fd75d8542006dc51d8d210f6dc635452103cfc72597210aef641d8542004f570d8554024ff7654721006df6350921006df305952103dec725052102cff745902102dbe719054112e7f505954201cfc745865208cff7259121006f560d85541bf9f3090541014fc7358642006dd30d922102e7c515962102cff7398642004fd71d9152004ff73590211c6f542185542873c5418954004ff75591210067e3059721006f572d855400cfc7059321014fe7359621006f510d92210067e105972120e7d6054a5101cfe745865202e7f7559641006df635052103cff725942102ef4751855400cfc70d855403cbf7650a41006f77159521006f730d855403e7f2059721006f7321855402cfc71592511cef640d8554006df30d9521276ee52d895403cfd71d952102d7e7194551076ed4258a41006bd43d954201fb661552411c6f5411855400cfc70d9541005df7358542004df70d8d21006dd3098652006f52018554205f77159151206f653d8554004ef764842103ebd425964203eae6250a410257e7550a5100cfc70d85421cf7454d85540067f7059721206f651d8554005df73589412077753d8554006bd53593211aede52d8d21004fd7690951006f5321855401f3f7555142005f47154921074fd7690721004fd705902101dbf75552411ccff765464100cfe7059541024fe7559121024fe76d952127ef652185540aebf40593210073d65552411c6f543185541173f4255251014fe73d95212767c51d895403e7c4259721004ff73d89540067d65907210267e65947210aebc41d8542006bd40590211debf6350a41014fe735964203ebc72593210b67f54597211c6f574185541cef740d85540067d6454a51004fd705962101e7e64551520067d3059721005ef725072100cfe7059521174ff755954202cfc73185420057d7550a51006bd405932106edd21d8d212576f2055152006df70d8d2103ebf429864206ddc735912103cfc7259421004ff745942107e7f5458a511cef754d855400cfc705864204ebf4059021006f510d9521156dc6354921006df301855223ebd63551421173f4055251007ac72551420267c655522102e7c5159421006bc505932102cfc729865202cfc715902100cfc70d915212f3c65551422167d6354a510febc415954103ef7215864204cff76506211d7b51050a41006ef205954207e7f51d952102fb441506210073d64552511cef643d855403ebe2159321006bf535932102e7f6194551006f4515864203ebf725932101dbe7494a41
  | 1 => 0x8552005f471553210ce7f51d9541006dd30d9541006df63885211c6f74018554024fe7559221006f710d954203cfe72d91510febf4259641004ff73d89410567f5359421005bd7550a411e73d505524101cfd71d95410b67f505972102df471552210067d5359421006f66318554004fd72d915102cfc7650a212767f53d89541cef654d8554004fd7654a410067d6555321006df42d8d21006f66018554026bc655514203fac425092102cfe715942127f775018554006dc54d8d2103ebc3259321004ff73d9121006dd75d8d21006f510d95411157f7655251006bd435925221e7f60552511c6f7421855412e7f52d954200cfe7059641006dd305912103cfc7259541004ff7458a5114df87059152006f662d85540dedc6390521006df30d9221245bf73551421aedf21d8d2103cfd7259421146bd54d915202eee2158a4103cfd74d954203cfc76553210067d5458a51004fd7655121006dd30d8951206f453d8554007d710d8d21185dc7358954006f5105912102ef41018554014fe73986420047d75d854222f9d305514200cfe70d8954006dc10d8d21004ff7650a5100cfe70d8554006bf64552210076c7255152014fe73590211ef3c415525112e7c65595420067e535972127ef45018554005dd70d8d2102cfc7159642006f510d895103cfd71d9121004fd70d855402ebc415925101dbe7454a4103e7e32597211d7ad2050a41004fd731855201cfe7459421004ff76509510067e745972102ebc415902115e7f54596421e6bd6055241006dc50d8d2101cff715902103cfc76909510e67f52d96411e7b71055241004ff7059421245bd735514202ebd74d96410067d65945412567d60551520aebc715932102def714842101cfc7654942006f510d915103cfe7655321004ff7058a51006bd755932103ef7219865201cfc7458a51007b77150a410067d659472103cfe72d95210067f30597211e6bf6055241006dd74d8d2102cfc76550211d79f3050a41006f53198652004fd73590211c77775185540267e6555321006be505932103cfc725925221f3d4055251014fc7359721007747155251004ff70d915203cfc7650521006dc64d8d21006ed62189541c4fe7694541006f630d8554125dc7358542024fc7559021006be705932102cff7318552006f5311855403dbc7655142006df75d8d210067d71597211cef743d855403f6c5254921005f47159152006f510d915203cff7694a410e73f525524102eec6298a41014fc73d912101cfc7654541014fc73d8542014fc73d8941004fd71d89540057f7154a510267e6554a21206f750d8554014fe7358652004fd70d9121006f430d8554004fd70d8951014dc7359521006dd30d91520c5dc735894103cfc72d9121005f77158954004fd75d9221006bf6590541004ff7359221004f
  | 2 => 0x4fd7358642004fd70d854220f5d3054a5100cfe7018554027776194551004fd75d89410067e545972103cbc7655142005f67198954014fe735912100cfc70d922127fb75418554006df30d9541007b471552410aebf4159321006f710586521cdf67618554006f731d8542004fd73d8954014fe73d91521c4f671d964102ef7731855427ef553185540b67c53597210067f315972103eef2059642007e5514842115f3c5458954006dd3059542004fd70d96410057d759894102eec6258a510267e615525103e7f5259252006df30d89510067f65549421c776541855402ef6419864202cfc71592521cef440d855420f751054a510267c655492102cfc7159621094fd75d962106fd471d8d21006be40d912101ebe6450721006df3059121006f5105954202cfe71d9641006bf10593210cd7e7598941014fe731854203ebe425932100cfe705922103cfe725902102df47154a21004fd705925226d7d735515200cfc7058a41006f74158652004fe7655121004ff70d8554006bd505932103c7c7655152006f710d8941006bd40d954200cfe70d854202cff7098652014fe735864203ebe425902107e7c50d95212077752d8554004df7359521006f573d85540067e4059721004fd7655021006ed20d915210edc6394521014fe7359521004ff735954102cfc7318552004ff73d915122f9f3055142004f770d8554006df30d9151235bf70551420057d7590a5115ebe54d9152176bf40d95421afd421d8d21004ff73d854202ef77018554014fe73d9121005bf71552410267e6594541024bf7655241004fd73d855203ebc6250a41006bf7059321004df735912102ef470185540067f6554a4102ebf7459021006b71059321014fc735865203e7e7259721006dc6359521024fc75d9121024fd7159421005df735895403dec7250721004fd7498652006fb705954202cfc7158a41006df30d915203e7e205972101e7f765525102ef6319864203ebc5259321004fc7650951014fe73d96410257e7590a51004fd735952101ebe6490521004ff7359251006dd40d8d21006dd30d912103ebe7259321116bf42d964108ebe54d9221007b771551420e6bd54d915101cfc74d8951074fd72d9121014fc73d954102cfc7598642006df40d8d21006dc63d952103fe4215492101cfd7518554014fe735972108cfd74d922102cff739865202ef42198642006bc705932127ef753185540273f74551521c6f54018554006f7619854203ebf52593211c6f454185540067f4359721004ff73d91520067d53d89540073d5454a41004ff7059121006f510d91211773c549895402cfe71d8941007b543d855422fb5105514202ef710d964101e7e6455251006f7105964107e7c515952102ef71018542006f731d8554006dd30d9151006de60d8d2103cfd751
  | 3 => 0xd305972102cfe7159641006be74d855227ef75218554005f4715895402cfc7518542006dd70d8d210057d7598a4103e7f7559642004fd7359321006df30595420febc40d9151006bd645472102eec6258a41004fc765494102cfc765522125d7f7055152006dd30d855200675105972119fcd308852102cff73d962107cfd765452107cff75595210967c51d89510ffb4415454102ef4411855203e7e6254a51006f441586520067e75d8542007d530185540067d5059421006f5105972119fe5108852101faf7250a4115f3f43551521ff5d3094551176bc41d95420773c545512108ebf425922115ebe64d9152005bd7498a51006f432185540d6be609054112f3c515514201cfe7459521076be54d91210fe7f54596410067c405972115ebf43595420e67c51d915103e7d5259252006be3159321006de75d8d2102ef64118542006bd4059252007b540d8554006f51058a51014fc7359221006dc65d8d21004fd70d894107df57198951004ff7359721004ff7159642006f71059421006f563185541067e60945510067c7459721026be6555142006f731d855203e7c5259421006f510d8552176bf4059252004fd7358652004fd73d915102ef47418554005b47155142024fe7518542005ef7254521006f562d8554004fd701855202cfc74d962100777715515220f5f3054a51014fe73593211aede72d8d2103cfe72d96410fdbe74989510267c655452102ef710d9621004fd74d9521006f7715954203ebc215932127ef65018554094ff7654421006f71058a411467c51d915203ebd5259321006f7105922103cff7690a5102fe64148421004ff76550210077550d855402ef671d9641007777154a510067f7559541006f7105864222fad2055142006df60d8d2100cfc70d895103fae74c8621006bd43d8954186dc6355121006dc41d8d21004fd7098642004fd73d9221004ff7059521005bf7150a4103ef4215865202ef441986522267d63552511cfb740d855402cfc7159421007cf734842102cff73d9641155dc7358552006f510d855402ef43118542006de50d8d2102def7648421024fd72d9152004ff7059721006f420d8554006d530d855403cfc72590211057e705525126d7f73551521cef475d855402cff70d964100cfe70d962108eee42d89411ff75109455121e7d6055251006df30d912101cfc75d9151006be40d9151006f7105925224cff7259542004ff7358a410263c6555142004ff76551211cf3454d855415e7d5459642006f771591210067c3059721006bd6450a21257751055152006bd659054101e7c64551521cfb454d85541467f50596421cfb742d8554004ff7558642004fe765494103cfe72d912101cfe7418552006bf64551212575d3055152014dc735912100cfc70d96410febe54d915102cfc71d9121
  | 4 => 0x51420067f7159721004ff7059541024fd71d915103ebf745932101cfe74d9521006df3059541005df73585521ce7575d8554014fe7358a41006be73593210d5be70552411ff5f3094551006f74198652006f7601855402cfe71d8954024ff7654a21014fe73d95410067d53d91521cef575d855403d7c7655152005fb7059542004ff70d9521006be305932100cfc70d89410d5bc7050a41004fd7359642005f7715492119fcf3088521006be1059321006df41d8d2103ebf20593211c6f44318554176be5459252006f6315864202e7e5159641006dc63d912100cfe7059021004fd73185421c6f6741855402cfe7159021004fd7359251004fd7690a51176bc415925203ef7715864203cfc725964117df87058954004fd70d95421c6bf4218554006ef6298941006df3058a5101fb66150a41014fe735964101dbe7454641006dd50d8d2127ef550185541c7b74318554006df30d8552014fe73d9151006df735954212d7e75d8542006f773d855402ef47218554004ff73d8552007b47150a41006f520d8554004ff70d8951006bd40d8954004dd70d8d210273f7455251007ae6250a4108ebc41d894124eee42d8954006bd6490721006f77159541024fc7654921076bc40d912103cfc765452102ebe41590211c6b7421855424ebf40d8954004fd735925203ebc4259021006df10d8d211467f53d915200cfe70d9641004ff705902103cfe76d895401e3e6455251005f7715512103ebc425932103cfe729865202ef710986520ce7e65d95411cef443d855402fe65148421004ff76553211ef3e515524102ef710185541aede42d8d21027766154a51006df30d8554006bd305932102fb67190541006ed2059542006bf545932102cff70d922100cfe705912102ebe4159251014fc735932101cfe74d85520067e50d95211c6f64218554005f77018554006d710d8d21006d730d85541c6f57518554006dd3059541207b574d855403e6e6254a5100cfe7098652006dc6359121006bc3159321006dc7359542006f710596211aedc52d8d2101cfe74596211f6bd6355241005bc7155142006dd30d8542006f751d8542006bf7459121006f7631855402cfc75d922100cfe705942127e7f5218554006f710d89540073f6455152006f510d85420267e6555021006dd3058a5127ef4521855401cfe7459721006f5105954103ef42158642026bc6555241004fd70594210067d50d8954004ff70592510076d6254a51006df52d8d210ff3c5458554096ee52d8951004fd7358a51076ee4258a4120f6d2054a5102cff7018542004ff70d85520967f5259621004fd70d954127e7752185540067d10597211cf3c54d85540b67f5159721006bf745954203e7c205972102eef6298a5101cfe74d96211767f54d95420065d305972102cfc71d9521006d
  | 5 => 0x4fd7058a51004fd72d8554006bd6455321206f675d855401cfc7650921004ff73596211cef543d855403e7d325972103e7e52597212667f6355152005f7715092127ef5511855408f3c545522100777715525103eef205925202cfe71d954201e3c64551521d6bf6050a411d6bd6050a412575f305515202ef671d96210e57e7598a41007d7301855401fb7619054101f3f7555241014fc735954202cfc73d964107e7f52d952103ebe42592521cef774d8554074fd76505211d7b71050a4101ebc645512100cfe7058a41006df635452100cfc70d9121006ef20d954200cfc705952103e7d215972103f6e75c8621006ed621895124ebc41d8954006f531d8554006bc7359321006bd6494721096f55198652076be64d9121005bd74d85520567f545942106edc71d8d21006f75198642094ff7259521005df735895100cfc70595420267c6555121006dd3098642006be40593210257f7254a51004ff7558a4102fb4419454102ef6319865201cfc7459621006f710595211cdf771595412067c51d8554004ff735964203ebe32593210067d435972102ef631185540967f54d962102ef4219865203cff74d954203cfc765072123f3d535514201cfc74d9541006f7621855403cfc7259642005f7715954202fb710905410263e65552410ce7c50d9541004f5701855403dbc7255142006be535932103cfe7259252014fe7398652006bf30593211b7cd30c8621006f7411855202ef671d9221004fd70592211057c705525100cfc70592211aedc21d8d2101faf62551420acfe7690521014fc73594211cef542d855400cfc70586520fe7d5459641006f710d95212067675d855400cfc7059642006dd30590211afd771d8d21006f51059021004fd74d962102ebc6459251235bd705514221f5d305525102df4715502101cfc74d95210af3c5455321006f732d855403e7d2059721006dd3059321006dc7359521006bd735932100cfe7018542115be7498a510067c4359721004ff7059221006dd3059251004fd73d9621006df6354921275ef72591520057c715515202ebc415922121f751055251014fc735964100cfe70d912103e7d52986520ce7e655072107ef6515865203cfc7654721006f51059321006f51059251004ff7654a41024fc75d8941004fd71d954202cff7559421004ff7459621006dd30596422576d205515202e7f75596210f5dc735895100cfe70d855202eec2158a410ce7c655954127ef55218554024fe76d954212e7c515954202f767194551004ff735954208cff765042101ebc6450a5107e7c655952100574715515203e7f5298652006df74d8d21006df3059721206f652d85540067d6554a21005ef7254721006be43593210065f305972100cfe70d922100cfe70d95420e73f505524102eef6298a4112f3f535
  | 6 => 0xf70d915100cfe70592511767d54d9542004f77159542006f710d915202ebc64592211e7b51055241004fd74185520067f6554521024fc7559321006bf3159321004ff75593210067d50d915203d7c7255152014fc735925100cfc70986520b67c5059721004fd7398652006f5105964204ebe545902115cfd7654942006f51098642076f64158642006f610185541cef540d8554014fe73d89511c6f64318554006de10d8d2101cfe749865222ebd605514203e7f2159721014fc73d85521aedf20d8d210073f655514200cfe7059642006f473d8554024ff715942103f6d75c862102cfc7654a4102e7e5159421005bf7550a41004ff735865225d7d7055152006f672d8554024fe75d8542006df3098642024ff7654942005df73595420067d3159721006bf6450951006ef6298951006df3059321206f450d8554006f7201855415cff7459542006ed20596422167f6354a510e5bf76552410adf77158941006df72d8d2103ebe20593210067e50d954103e7f7559721014fc7359642206f753d855400cfc7059121006f463d85541c7747518554005f771552210fcff745954103fe761885211cef454d8554004ff73d95411c6f44218554006f660d8554004fd7059121006f663d855402ef710d922106dde76d8d21006bc5359321006f56118542004fd705964203e7f325972102cfc7318554004ff70592522077750d8554026be6555241014fc735962101dbf7555142006dc75d8d211067c60945511b7cf30c862112e7f5359542024fe7558a4121f5f30552510d5be7050a410ce7c51595410b67c51d85521a7cc63885211aedc42d8d2101cfe7458a511cef742d855401cfe7654942005bf74545410b67c715972100cfc7018552006f47159542006df3059021006f73118542006df54d8d21024fc7558a4104ebf4359021006df6390521014fe73d855201cff765922103dbe7255142006bf5059321056f551185520247e75d8542006f670185541c6f75418554006df30d8542006f53018554004ff76552210067d655072102ef641185541a7e5318852101cfc7459721006df3059251006f410d855403e7d4259721074ff74591210067d73597211173f4355251006bc30593210067c7059721024ff7654521006f451d8542005f570d8554004ff7559221005f571989540067f6554921004ff735932100cfe7059542004fb705954202cfc739864200cfc7059252004fd759864202cfc7650a5101dbf7250a4102cfc71596411cef775d8554114ff755954102ef71018552125dc7359542006df30596420aebf4359321006bd645502102cfc7654a210267f6255152006bf7459541006f620d855402ef43118554024fe75d92211cfb674d8554005bf74549420cebd545925106ede71d8d2123ebf6355142004fd73d9641005f77155321
  | 7 => 0x962100cfe70d915203ebc4259252006f53198642006df50d8d21006f710d9121007b7715524102cfe7159251006dd54d8d21014dc7359542006f76198554006bf73593211c6f554185540febe645472102eee61484210067d535954200cfe7018552004ff7058652004ff70d9121026bf765524101ebe645502102cfe7655021004fc76551210067d535972102cfc73d922103fac42549421ccff715954102eed72d9221006f46218554024fe7559021024fe76d9541006f7301855401cff765925102e7f7559421005f770d85540257f7455251005bd7494a4107cfd72d952102ef65198652007755318554005f77150a210267c655494201cff7650721006f7105912112e7e65d95421aedc72d8d211467c515964212f3f5255142207b754d8554006f710d9541004fd7318554014fe7358a51006f56118552006dd30d9542024fe75d912100cfc70d95420aebc405932103d7e72551520b4ff7159521014fe73d95422767f50d89540febf42d915103e7f4259721006f510596410067d4059721004fd74d855203cfe72185541cef574d8554006f510d954203cfe72d9541006f63218554006bf6450921006f56018554004ff735864208ef541986421173c549855403e7c6254a5102ef4519864207eee5258a5102cff7098642006f710d895118fcd30484211cf7654d855403e7e2159721004fd75d91211c6f6401855407e7f54d95212673d4355152006f673d8554006de40d8d21126dc63509210ce7f52d9541006f7511854202ef7751855402ef6511855427fb774185540067e7059721006dd3059641004fd70d85520b67f53597211f6bf635524102e7e5159621006dd30d9641006df6394521004fd7359541006bd74d8552014fe731855402eec6298a51004ff715954222fb71055142006f710d91510567f50594210277661552510d6bc60905410b67c54597211ccf7715954101ebe6450a21004fd73d95210067d705972127f775318554006dd65d8d210067d6555021006df7359521014fc7358a510c6dc6350521006f510d9641006bd435954200cfe70d8941004fd72185540aebe5459321005f77154a21004ff715925200cfc705954101cff7650521007ad6250a41076bc6459121014fe7359251014fe7359421006bd715932102cfc73d9621004fd7059641007d510d8d21004fd70986520067f6555221006df65d8d210d5bc7055241206f553d855401cfc74d855201cbe74d855202ef7721855407cfd7694721014fe7318552004fd73d854200cfc70d855203e7e5259642004fd7398642006bf645052100cfe70d91511e79d30552410057f7255251004fd70586421c774541855415ebf42d9152006f87059542004fd74d8951116be5459251004ff70d894103eee62189410567f54185520067c105972102cfc7398652004f
  | 8 => 0xcfc7059721006f57018554014fe73d8542006dd3058642006de74d8d21014fe73595410076e6254a5100cfc70d952100cfe7098642004fd73d855403cfd7259021007b4715514200cfe7058652006ef6298954006dd305925206ede76d8d2102f771094551024ff765964106edd72d8d21006df7359121014fc7359252004fd73d95410067e5059721006f460d85540067d659452102cfe71d9521006de54d8d21014fc73d9151006f751586420067c4159721004fd7058a410067d5059542004ff73d9542006f71059542004fd7059521006dd30d85540067f7559542004ff705964201cfd7159021004ff7059641005bf7255241006f56118554006df30d954225777105515200cfe7058642006f763d85540067d7459721096ed52d89511d7af2050a41004ff745865203ef76188521206f752d85541467f535964200cfc70d9621006f470d8554014fc7359021086dc6388521004fd73d89511debd6350a41176bf43d9542004fd7018554006f5105925203cfc72d9521006f631586520067d5418552004fd7018542005f47150921006dd3018554004fd735954202cff73d922102cfe71d915201ebe6490721006f67618554006f46318554006df3018542004fd7359621004ff73d8554004df7359542007d530d8554005fb70591520276f7254a51006f66218554006f4601855427ef6531855401c7f765525127ef45318554024fd7418554004ff70d854201ebf62551420067f65549410067f7559521014fc73d9521014fc7359521004ff73596410b4fe769452103ef7219864202ef67198652006f63018554006de20d8d21006b5105932102ef47318554006df3059641006dd30d8941006f563d8554006bc75593210acff715912115ebc64591521aedf71d8d2101cfd75d8954006df30d964115f3c645515202e7c6559641006f6201855402eee2158a510febe64d9151006dd3018542014fc7359541004fd7359721004fd705954200cfc7059021054ff765462102ebe415922103c7f7654a5118fcf3048421014fc73d8951007b54318554006f5101854202cfe7694a41006f43018554026bc7655142004fd70d9621006f441d8552006f51058652076bf42d9121006bf62905411cef674d855420f771054a51006bd541854203ebc205932101cfe74d8951004fd70d9152006bd105932101e7c7655152006f532d8554006bf7559321006f510d894101ebe61552410069d30593212567f6055152206f650d8554006bf515932103cfd75d855202ef43118552006dd305865200cfc709864202ef65118552004fd70d95211c6f7431855400cfc70d9151005bd74989510073d545494222f3d50551421e79f30552410fcfd76545410067f405972127ef75018554006f432d855402ebf6190541006ef725912103dee768852100cfc705
  | 9 => 0x771484210257f7455152024fe75d89411afd721d8d21004fd73d9152024fd74d8954006df3058642014fe73d89541ce7d75d8554014fc7358a410067f10597210057f7454a5101ebe645532103cff72590211c7345418554006f510596210067710597212667d635515201cfe74d9541006bd5458a4104ef541185421c7b454185541167f54d95411c7b74218554006f570d85540067d75d8542006f7105972101ebc645522103e7e4259721006dd60d8d2103ebd2159321006f71059541006bd435902103cfd74d8542004ff7058642006ef20d915222ebf60551421057e7054a510077550185542273d435525115dbe74d85520067c735972101e7c64552510067f745972100cfe7058a51006f510d8954006bd4359321206f552d855403cff7158a41004fd7359121006dd30d8954014fe735925203e7c7259721006bf7159321006dc40d8d2102fe7108852103cfe7298642006df3059252006df64d8d2102e7c5159641004fd7059321116bc41d954101cfe765454102cfc7159221004ff7654941007af7255142006f472d8554006f71058a5100cfe70d895101cff7650a21206f550d8554006f670d855402ef451185421c6f440185542267f635525100cfc70d895424f3c54d8954004fd70d9221114fd74d9541006de65d8d2127f77521855404f3c545502102eef6188521006dc73591212573d4055152024fc755912103dec725452103e7f7259721007d730d85540cf7751945411057c7054a51077b4415052102e7c655962106ddc73595211cef474d85540aebc435932103cfd7418542006f760d8554004fd70d9151004ff73d9521006dd3059421006de70d8d21006f710d8552004ff705962103fe4215092101cfe76d9152005df70d8d21004fd7358a41006f510d962112ebd54592520069f3059321006f7311855203cfe7259421005f7715915202cff70d9621116be64947211cfb743d85540e73e655524103cfc769494115f3f4055152076bc41591211ef3c5155241006bd4059542006f51059421004ff70d9542006dd3059221006dd3058a41014de76d8d211173e6455251006dd30d962103cfd75d9152006ef7648421007e54148421006df30d8941004ff7259251004ff7358a51004fd73d912103cfe7259642006dc74d8d2115ebf405954203e7c3259721005f4715954201cfe76d9121206f452d8554004fd70d89540067f6554541006f51058a41024ff7654541006dd64d8d2103cfc7258642006f710d855400cfc7058a51006f510592211c6f654185540067f65551210276f625515203ebd2059321014fe73d894104ebe5418542004fd70592510067d5359642006f7311855415f3f4255152006df305865202cfc74986521cef642d855400cfc7018542024fc755922111df8705954200cfc7059641014fe73d8554
  | 10 => 0x952103eee6218954014fc73d9542006f530d85540267e6594521075f571989411cef641d8554005df735915200cfe70593210267c655454100cf8705954203fad74c862103ebf2159321004ff70d9541006f431d855202eed72d9621006f51098652004ff7559021006f7105964203e7c5259642004fd73d894103eee62189510ce7f525925103e7c2159721006f67318554155dc73591520e67e6590721014fc73d9152005f57018554004fd7059721006f710d854207eed5258a5100cfc705925102fe63188521024fc7558642004ff73d8951004ff735925202df47150a21006bd7059321007747154a51006bc515932100cee768852103cfc725925107e7e65d9521004fe7650951076be5458a410febc64591510267c65549412077675d855402fe66148421006f51058642006dd301855203df67188521006f770d8554006bd315932103ef72158652006dc70d8d2103ebd4298642006f431d8554024fe755864202cfc729864202cff7018554006f5101855203ef771586520b5f771589510076f7255152006de64d8d2103e7d725972100cfc7018554206bd74d85540febf41d915115f3c41551520067f6494551006ed20d9542005f77155021006f6721855402cff70185520e73f53552410067f6294551014fc73d8954004fd769494100cfc70594210073d5450a511467f50d915224ebf43d8954024fe755932102cff731854200cfe7059621007b54018554006ed2059252006f53158652004bd74d8552006d53018554004fe7694941006dc60d8d21006f5721855415ebc4159542014fe73595421cf7575d855401cfc7459521004fd7650a5103cfc725932103ebd7259321004fd735964101cfc7459421206b574d8554006df305922122faf205514227ef67518554006df305942102cfc7159542004ff7459521004ff7058a4120e7f6054a51004fd7058652004ff735952103ebf3259321006bd64507210067f4159721006f631d855406edd71d8d2103e7c5259721006f5621855403cfe72d8554004fd7694a41014fc73d855400cfe705925203ebe525932101cfe76d915103ebd3259321006d510d8d2101dbc7454942006df30d96210057d75d8542006f42018554006f762d8554004fd7518542006f761985520267e6554721004fd7359221004f47159542006ed6218941006df3058a4101ebc6450921004ff7359421005ef7250521004ff735912100cfe7059721006dd10d8d2102ebf745922103ebf745925202eee76885211aedc20d8d211c7b740185540267c6554a4101cfd75d8554006df51d8d21004fe76909511c73c5418554006f741d8552197cc7348421006dd3059621024ff7659621006f51018554004fd735942102cfc74185520067d5059721004ff70d895401cfd72d954201ebc645052102cfc7158a5103fe
  | 11 => 0x10030170860302300012e014189ed01e194001330000a00406e000080310010200040880405605c0f80b0602380183100a0400601a0040f0098030640247900600400000031006004018050220180382e0004881303c0720ac19013034000318070079000e83911816c152ea0040000112002629c0100303e0040781400ec61f70000100300104a03602405001066140638db02a030039fb0440005e00100602c1781206c0980c80c0220081f809016018030150560142802b0497c80100100c02c000010240040481a02c0240200c01600c060000121502e80d00000c2503b05800c360090b51e80100102615c0100005450c0002d01c0380484f01a0000386400403c0380609e0683980200e040000000360002b00009e0500102c25a0000f00407a1440280209c04c0585900200407e9f02000800005050000148200140380000a0040180000305c0a41184a028398078071700140781d0220040501c03c2240201c00200a0c00600200c0b8060060600682903c19807801238004058050320242a0100d404c1e84801200400013000000000000061140b03104c1040701c01c03806017000019b70020003680001c00c0d8168ee0020000403106204400012000000118000001340084607e02404034004da4008f504a024148040000881808404a02c59825012004078391060000200000805c01805006f720d8554006f431d854202cfe71d91211167d54d9541005df73595211d79d3050a4102ded76c8621007cf63885210fcfd75d964102cff74d954103ebe6250a41005fb7058954006be75593210067c315972102ef710986420077471551521c7b47418554006f610d855402cff7318554006f5315864208eed42d894102ef67198642006bc1059321004fd7655321004fd7655221024fe759864202dee71885210267e6154a51006dd3059521004fd705954120f6f2054a511bf9d309054103cfc72586520ffb74154641004fd72d964103e7e52594211ceb674d85540aebc5459321006f7105932102ef77418554006f51059521005f471551210067e3159721076bf41d9121006ef7259542004ff7259641006f772d8554176bf43592520067d5059642006df301855402cfe7655221004fd72d954101ebc64509511bfb51090541006df309865202eec2158a51024fc75d854203ebf42596420067d6554721006dd30d952121f771055251006f71059021006f71059251006df30d895402cfe7690a5103eed76c8621004f770185541f73d53552410067e735972112f3f5055142006ef7259521005df7359121014fe73d9221014fc7359121024fd74d8554004fd73d9542006f573185541cebc41d855401dbc7454541006dd20d8d21006d73018554014fe735922100cfe70d954103dec72547211cef442d8554006df305962100cfe70d
  | 12 => 0x1004120100030020040e0000500003e04903a0680088c0040000f83409200c038040000001f81200002c1f01000e3540000a23a0540780b13029c708730140040100100400037863000048028040d215c2183202a00c4a80502c0140c80103602c1780100a0000402003809c0684512e3df2eb9e0000040e80c0080319d00101001408001000234378190122e8098133fc03c010000000084680d0000941783d0000381f8530ac098210020300480181900a120070040d60a40500101a0180f06c0080080182f09a0080003500a240000040000582200401a00c0680c0a20ac0000b01c06002002014108050c700c0102d0b10160000c8020001300780f0ac03c04800076728020150160900001900203806016008028198020040c407b0902a00c6381e04c4f01280307e004004e800201400001014070090021c208c1000701e0000004c0060081700300c004000030260400180609a01c040270400000a0100040140293d0040080000000000505002024010298300080585d8c60c2000010341cc1ac0500700202c1380f0022849b80511c0040000509c8040580008c004000010385240f81d0220200180a0420
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa76850cb615500147b0a382c9908032da13715954201d1f426caaa242078ec825cd61908814ed0a386c2aa003365c130586422055a43281b0aa800ed13044361508014eb0ba08c2a90029de15101855427f1a328e2aa284058f4815d954884ab4ed02082cb90803351c730595420051ec28e6b264200a7585cc761550039b4e0982c3290023761e70d8d210066db82c1b1a4200d34549c662550011eb0e196c2aa0032d59071553210047ac3c4030aa835ad5811c36348401d3261082c99080e8fa1b64551520047bc3a21b2c82078ec825cd61948015750018ac99081e1fa1e545972100636b2ee4a8e4200a758194165c84031e90e882c8908029d21510185420054f41c20b264200af1800c7615489f96eec38aa92080336e0170d8d210066bb9ce7b0aa84fc77621c554548019b6e1982caa11a29d616721855402e3a38acaaa04200c9d74cc3615480196908b80c2aa002ad61232185541c65b320e2aa64220c778744165c84bd9ace3986cb20803b4d81301855402c7a40ae030aa800a9d8394164c84cf8baeb986c2aa002b560640d8d210047b43861b0aa800ab5819c164c84b79aee2982caa0802b660063595210053b40c80b2e420387d85dc361550019b6e1306c69080237e0d70595420076498241b2a8400a7585c806155001da700986c2aa00a3720d705952133e4f3a661b0aa400ed0604c361550059a8e698ac329002b660063d912129e6a39a20b224235cce76d8e214847196ec438aa8a1002b9a0b73d85540075898220b264253cd676443634840153b08286c690802bc60031d85420052f41ca0b2e4239a75851cf61550d756f08b00c2aa0073a1c3205954230e2f3aa61b0a84008f7815d9544840f17d0faa2c99098ead61262185540046f43a60b2a84028dc87cc165508015cb04386c2aa003351cf71595210052fc2ac1b1a4200ed13044165908011ef0eb18c2aa00a3720d76551211cd3ac2ee1b0aa873e5675cc36155001da260906c2aa056ada04705932127f1b328e2aa48200a3e851c164c84015e50139ec2aa0023d61c32185540074bc2221b1a4200dd3704436348401da260886c4a08029d61432185540076898221b0aa800cd463dc554484015ab06386c2aa0033c5c110d85520061fba4a8b2e4254cd473c4164484011ed0e882caa10128fa1764552210056b41821b0aa8038be84dc36154801ce700882cb908023da1c20d855431e9ba90e2aa28400d3454dc361550015a906b90c2aa0033c5c130185540052f42e83b1a42018f48744165484090f90ab82c8908e2ad211701855400e6c38260b2a8407aae8214164c84010fb0bb86c2a100a1f21d53595421cd5b420e7b0aa858a5e830c165c84019e2e1b06c2aa003365c130986420052fc1ae2b2e4200da7721c55450801da2e0980c2aa0029de057359721
  | 1 => 0xf0eb2ca290803b4dc130d855403c3f43ecaa948259e5a204c165c840196ae9886c2a9002ad61020d85540046e43a60b2a4200ab584d4461508018ef0ab80c2aa0033c1c470595420069a2a2e030aa800cf170443615080136f0038aa8a11031d99771553210054ec1820b2642009b5801c5545080717908b82ca908034d15170d855400c7c402ecaa24200cd463dc552484014eb0a100c2aa0031d61770d855403d37c32c4a94a2058f68708061550011ef02b82caa0802bce0162d85540076898421b0aa800af2800c761550b7d2ce8986c2aa002ad205735932102e79882e030aa4028df87d8363484011bb0e286c690803351cf71591210076898221b2c8200ccf30dd921084014b906b8acb908e2cd21153185542ef4ba126030aa869e57524c06155001caa61882cb9080e1fa1f65552210047b436e030aa8078be8790d64c8401c6f08882cb908023de0573591210056b41c21b0aa800cf370441619080b1e90f882caa1007369c130d962100c7c402e6b2a8400cd570cc061550019e6e0882caa08e72d19371551210054ec24cbb1a4200af080588615500196ae8886c2a900237e0d70591210066a31ee2a124264c7575443615500b56902a1ac8108034d15370185540054ec1c80b264200ed2704c061550410ff0e882cb90803351cc715954227d9a42a8030aa800c5d751d763484e1c68a9b10c2aa1932d9d110d85520251f42ec8aa24207a6c824c565c848156b09b86c2aa00335dc530595420146f43ee6b224204c3c755506150801da260882cb20803b44c1105925101c9ec2ee2aa48238ab684c8061550015ab02206c690802b560c20185541ce3bbb6e2aa4a26ca77855c061550019aee1980c2aa0033cdc310595422055ac26e7b0aa800cad64dc941c84011bd0db86c690807369c130986420066ab8661b0aa800ad483588615500196ae8b86c2aa003361cf70595420146f436e6b224200c77525c0615500156908884c3290023ee0176551210054fc1ae2b264239b3484543615507156d03b2a8520803a561330185540076898221b0aa44fd67621c554548014db04202cb908038d215105932103c7a43a62b0c8400d34541c5625500187eebaa2c990802a7e1110d8d210055b40ca0b264200cb742dc061550011bf0eb2ec6908023da1d10595410069a2a2e3312a800ab5810c164c847bc6882aa0c2a90034e153705895401e1e3b2a8a928465c7575c43615500196e84b80c2aa1972d9d310d85521cd3a432a7b0aa800ae6821806155001d9260902c929007369c13058642006b2900e2aa2a41f8bd86dc5549049f4ed0a100c2aa0e69d61772d85540076498241b22a400aaf824c564c840917d0fb22a89095e9d60610597210076898220b0c8400c757514761508734e90ca86c2aa0029d6063059721006d2396e2aa28440
  | 2 => 0x110d91210047bc3ac230a8400ad68110363484019aee6882caa100e2fa1373d85522cd2ec1c60b2e4200c3c545d954c84015e500190c2aa002a7e1160d8d2100572c10c1b0aa8028dc835c165508031e90e882c32900317dce73597210052f42ce9b1a420787c85dd954c84815690ca1ec2aa0d6b3a0850d8d2100e6d38260b1482008be8714d64c840b0f90ea9aca10802bc60263d85540053bc2a2130ca400ad58388361550011df0eb10c4a88033c5c110d85540047ac06e2b2a844fb348550c61550030f90ea82cb2100237a1c50d8d210066cb8260b0ca439e3664dc554944039b0e0986c4aa003b44c110d95410052ec2cc9b1a42008be8714164c8401da260886c8a90023761e10d8d210056ac1ee5b0aa8058f4815d95408401cb260882cb9080369c8071551421c6d3b10e2aa284008fa871c1655081f0fb0db8aa52881eaba0b6550a4100679b8220b2a4200ed13044364884039b4e0980c2a10363761c10d8d210047bc3ac030aa80787c8754d65c84e7d2ae9986c2aa00339dca72d85540071bc2a20b2642008f58708361550014ef02ba2cb908063de1d10d854203c7b436e2aa2420d8dd87183634840717908b82c329003b418110d8d212df2abaa61b0aa800ed130443625440117b0fa8ac9908029d604405972100c5e43a80b24a400cd7704c361550019e703b82caa101e79a0b715512102c7a408ecaa242008bd84dc3615480187aea3aac990803b44c1105972101c3fc3acb28a8239a75851c361550015ad07100c2aa13ead2194018554006ca980e2aa28400ad6839c06155001da260886c4aa0122f61373d855403d5741420b264200c7752dc061550019aee6882c89093e9da1632185540046ec06e6b2242048bd84dc36155001d2e60882c99080e2fe1d74d85520054f41c80b264200af1800c8615500f1790ea1ac929003a5cc310593210061fbb2a8a14a200ab484441619480b96882ba0c2a900335dcf10595420046f43881b1a4200ed0704c361550d14eb0b310c2aa0028f61070597210046f43e60b2a4203a3c8459554c84070fb0bb9ec2aa01e2fa1e40593210045fc22e0b224205cf3105c061550039b0e0982caa08034715373589542ef8a2a26030aa840c7661dc55494401ce460882cb908029e60031597210053ac2e63b0aa40387e87d9554484059ace698ec2aa0023da1f10595410cc3ec36e2aa4a200cf3708c361550011bb0f32ec6908023de0573595420072a98220b2e4200aad8214164c84014eb02382cb90802b5a0c20d85540056ac08a1b1a4200ab6810c164c84019e2e1100c2aa002b560c601855400679b8220b2a8400ad58398361550a35ad02386c6908032d5d041d855200c7bc3a21b0aa800a758190165c84734eb0bb9ec2aa017391c972185540066bb9e20b224200a3c8544164c840f0f
  | 3 => 0x1b1a4260cb574c43615507156d09190c2aa002a721160d8d210056ac1ce030aa80787e8794d65c84090fd0bb9ec2a10063de1d10d85520047ac3cc630aa8008bd8714d64c840153d07282c9908024f6137154a510076898220b2042008f5870c061550018eaeb886c2a10033c5c060185540146e41ae0b224200e55310c565c84015b30031eca908029d61432d85540056b40ca1b1a420087f855c164484ab56d02082c990803275d130d855200578c04e7b0aa803a3f86591549440166902aa2a4a10173cc41709865200c7643a40b2a8400e548544363484018eaebb86c2aa002ada06705932100678b80c1b0aa800cd97018363484019aee0886c690802b560670d8d210046fc1ae430aa8568bc8744164c84011bb07bb2a8908029d21510586421cd5b426e1b0aa8008de871cd6550801cb700982cb9080a3721f305912102e6a39ae630aa800cb584dc361550019b6e0982caa10021f61773d85420046f43c81b1a4200d67721c554548090f90ab82c3210023761c40d8d210047ac00e2b2a8400ad58384061550015e501318c2aa0023d61e70d855402e7210ae430aa800ab5840cb6155001da260886caa10e6ada1020d85543364f3a261b0aa4008f5879c0615500153d093aec69080336dc130d85543362ebaa61b0aa800ab584c8061550019b6e1106c6908d637a1e10d8d210076898221b22a200a3f8544164c84738e8edb8aa8a900e3b60b73d85422055ac20e7b0aa8008f487441655080196b09b8acaa100237e1d64d8d210047ac3c41b0aa858a9e830c164c84015ab06086c2aa002ada0450593211cd3ac28e5b0aa838ab6840c861550ad9690e882c9908121fa1770d854200e6d38261b2a4200ad68398361550011eb0e300c2aa0028f617715932100759c0220b264200c5d75cc36150801da260900c2aa01e4f21d54549420051fc2220b2e4200a5d85d0763484655ad03b96c690803b44c11058a510046f43e60b224200cd770c436348401da261100c2aa002ad21110185520d65bc3a20b264201cd8704c3615507bc68a2aa0c2a100237a1c735912102e79882e1b244200e513044165c84011ef0eb08c2a9002b520554d8d210055ac266030aa800ab78444061550014bb0a206c6908062f21d40595420056b418c1b0aa800ad58188363484014bd06082cb9080355cc071551520066cb8261b224200a6d8284165c840b1790eb22a8108062f21d40590212059a42a81b0aa872e56754c361550bdd2d09980c2aa16796481305972100679b8ee0b2a8400c3c54dd954c8401da260882ca9080336dcc70595420053ac2e83b0aa4008f58798061550019b707b82caa10163da0570d96412065a3b6e2aa28400cdb704c362550014bb07082cb909a34dd0871551520053a42a2130c8440a7685dc361550019e2e0900c2aa003b44c
  | 4 => 0x1908019aee6882ca908e2ada1330185540066639eec9084200a5e8384165c840927b09b8aa9288128f21564550210055ac26a330c8462c5e75cc361508014bd0a206c69080e2f21170185420046fc3ac1b1a42038bc845c76550801cb261082cb908029ea0031597212e74b3a661b0aa840ab5841cb61550019e6e0986c2aa00237e0d76551210146e41ae430aa800a9e831c164c84ddc68a9300c2aa003355c130185541ad6a43221b1a4238a748654c61550011ed0f186c2aa002b360850d8d211c71a320e2aa2a40587c8759554084015af06b16c2aa1029da1420d8554006b2396e2aa2a401cda704c1629447ba6ca3b8aa920836b5a0670d8d212a66a39e20b2a8400a5d8394165c8401ba6e0986c2aa01eab209315932100669b8221b1a42008de87cc16550801ce260882cb90803b4d8110d8d210052e42a21b1a4200ab584d45619080b1e902b9aca108036948071551420055bc222030a8401c7870541655080199a61bb2421080237a1d30595210054f41ce0b264205cf3105c3658840947f0cb2aa9209029da1473d85540072ac2e6030aa800ae68218361550015ad06386c2aa00237a1c70d8d2103d96412a8a9284078be87d95429040f0f90eb2aa9909038d19771551420051ec26e2b2e4200a3e85dc564c84018eaca38aa9908029d61730185540052f41ce0b2e42058f6870c8615500153b06282c990803b24c120596420074a42221b1a4200a74854436150801da260880c2a1003b44c1105932100769c026030aa85fcb57444361550014ed02202cb908173cc4170185420051f426e2b2e4200c7685dc5655080147b0839acb9080335dc130185540066a38a60b2a8400cdb704836348401da260884c3290163da1e20185540066cb826030aa400ec930481655082b55b04382c99080336dc110d8d212bd5ac0c20b264200c757544361508019e103b82caa117335dc730595410056cc00c6b224239cb664dc554c841d17b0db8a8520803355c130d855403d57410e0b2642008dd87993634849f4ed0b980c2aa0033518c71551212d63a43a20b2e4239cb776dc554904014ed03182cb90802ad60650593210052f41880b2e4200cdb704c16550473c6ccbb8aa9208173cc4170d964100667bb6e6908420093d85dc54290401da260882c92900335dcf71595420046f43ca1b1a4202cd4734c561908090f90ab80c2a9007369c130d92210043ec3880b2e4200ed0604c061550bb9ace2986cb2080237a1c10d8d210053bc2a2030aa40187c8754165c840156b03182c9908033c5c230185540052ec1880b2e4262c9d74cc361550011bf06b82ca908029760e705972103c77416e7b0aa800ed3604c361550031e90e882c3210023760373595422e78a2a661b0aa800ed1304406155001da260882c52080335dcf10595211ad674108
  | 5 => 0x802bc60032d85540076898220b284200ad683dcb61550010fd0e202cb90802a761351d8d210047bc0ae6b2a820187c8754165508412f100baa8528802a760c70593210071a42220b2e4200a9e8314164c840147d0a39ac990802b560e70d85540047bc0ae0b2a8400c3c415d761508019aee3982caa101e9ba0b6554a4100c7a40ee0b224200a5c8558363484014eb0b190c2aa0031d5d570d85540053b40ce0b2e4200a5e8390165c84051b90f982ca908061f21d50594210061e28ae9b0aa454cd473c416548401c3ea729ac990807369c130986522063a32ee2aa242008dc874c165508014eb0a106c2aa003a64c110593210047ac3c6030aa800ed13044165884019b2e0980c2a1002b5a0450d8d210056ac18c1b0aa85fc767544361508011bb0f306c6908028fa1073597210055ac08e0b2642008dd87943634840156f02baac99080a2f21d43595420052f42cc9b1a4204a3e86d95545080156b09a8ec2a1003b44c110586520052ec1c80b2e4200cd9704c36488401c3ea92a6c690802b520d61185420045ec26e7b0aa400ad683840615507356d09b9ec2aa002ad61020185540074a98620b264200a75819c165c84015a906b08c2a90033c1c770595420047bc3ac430aa800ed130840615509f8ecca38aa990802ad21110d85520054ec24ebb1a42058f4815c165508015cd04386c2aa0025de0071551520045fc22e0b2a4200eb23044164c84019a6e0986c2aa0031da1770d85540046ec3c81b1a420787c8754d65908014eb02182cb908021fa1c435972100e7838220b2a8407a6e8210165c8401caf0a886c690803b44c110d962103c5e426ecaa64200a9c8444363484015730018ac9908163d20573185540046f438e6b2a4201cda704c0615487366908a9ec2aa002a7a1351d8d2138f1a2a4ec30aa8008f6870cb61550c18eceb886c2a1003a54c1105932127d3b40ecaa9482048bf8759641504011ef02b9aca908021f61f415972137f1a2a2c430aa838b3484540615500156b03202c9908033620f70595420d4dc402eaa148200a9d839c164c849f4ed0b900c2aa01e2f21d435932101d1e422caaa04200af08058b61550b3d3440982c990802b960b73d85540066cb826030aa800cd1704c061550014df0498acb90802bce0162185540066a318e2a124200ad48358b61550b50f90e882cb9081eaba0b645095103c5fc3ac920a4200a3e841c165c84019b0e6382caa10030fdd95454a410056b41ce1b0aa804a3c8559154c84718eeec38aa92894f351cd10595420047b43c41b0aa800cd9704c162904014bb0b3a6c690803b44c1105922127d3b4286430aa838a748654061550019e700b86c2aa0039c18150d855400e7838620b2a8400a5e831c165c84039b0e1982caa106a2fe1d10593210045fc22e0b0ca405cf3105c26
  | 6 => 0x53a40ae6b2e4200ad58194363484015cb04300c2aa003365c1309865201e1f3a2a8b14a252ad58184363484010fd0fa0acb908163d20573595420045f43ea2b264200ed0704436348401da260882caa08021fe15705954100679b88e0b2a8400cd473dc565508070f90ab8ec8a900335dcc71595420243fc3aebb0a8401cda704c36590401d3700982c9908022fe1170595410054f420a1b1a4200ab6818c164c8401b2e6038aa8a1003355c310d8d21007689822130c8400cb7845c0615500147908882cb90803b4dc110d8d210055bc0ae6b264200c3d741d165c84019b6e7b82caa10029760c705972103c3f43ca0b2e4200ad683180615500156b08190c2aa0063d21d105954101d1f426caaa44200ad583880615509f4e90ab80c2aa002b5a0620d8d2102e79c02e030aa8008dd80dcd6548401ba2e0980c2aa1b78d15060185540055ac08a0b2642028f7874c76155001da260882caa10e78d19371551520065aba6e1b0aa8008de8788363484014ed02182cb90802a720d71593210261f3aaa8b148240ab5841c361550019b2e0986cb208023da1f105954227d5a4328630aa803c3c7455061548015e30018ec2aa0030fd97745494200578c04c630aa86bab7845c061550816690aa1ec2aa002bca0032d85540046ec3c41b1a4251ad68104363484d94ef0ab00c2aa00336dc210d8d212f78a2a66030aa84fcb4761c5545080155b05082c99080395cc110597211c71b320e2aa4a200d67201c554548031f50fb82caa1002b5a0640d8d210061fb2ee8a8a82058bc8750d64084814ed0bb9ec2aa0023b60b73d85540056bc1ae430aa800cd970d83634840f4790caa2a4a1187275d130d85540056b4184030aa800a9e8304164c8401da260880c2a9002b5e0d62185540074898220b264200a7585d0661948011eb0e186c2aa0038755054d8d210047dc02e6b2a84008ef8758862504019b2e0986ca908063d60570d922103d3741420b2e42048ed82dcf61548018ef02baec2a1002a760e10593210062ebaa61b0a8400ad68398061550011bd0e982c89085a9b60870597210066cb8260b14a200d3454dc5625500b1ed0e180c2aa003b44c110d95210076898220b224259a9d838c164c84039b4e0980c2aa00297e1510d8d210056ac1841b0aa839ab6841c361550e5d2ae8986c2aa00317dce535972129e6a39a20b2a425bf14544c361550014ef0a886c2a90e63de0576550213572ba966030aa8078f4874c561948015ad07106c2aa0030fdd6755932103c5e43ac8aa64200d55301c5545480f4dd04382cb90807369c130d91210065b426e1b0aa80087d8710d65c8401cae61882cb90803b4e0110d8d210146f43ee6b2a8400cdb709c363484bdd2e85980c2aa0025d600715515200679b8220b224259e99204c164c84014bb06082cb9
  | 7 => 0xa0801e168000180002816038060781a0d0a0018120289c03000369341c82a01802000060780c190322100208192000b8048060a01606808270ac1287a0000002048060b60405a05800018100281a01018000001d0120a04a7c86e2b0240900606804038040f0600b006188ca358dc000480206e198080007e00010048040e000000dc258d62104a008141e03a078080807006000010420280a110b60000c0b09a00000000080000000800118c21f8ea4607404158bc8f2050942a8000323625004000403b85200018000020480a000061781402d40390b40000e07806013da0081600070090120000858004320341500801812090000007201838130220380007002070000e00000818068020800e090141080c15a6c190000b01a03804000000900a038120101002830128380303659000020020180a000e00002810814030100181016800048000d81a0000200016058000018409014878000000627018000000400e030021c8000980800848030000c01a0300007000008000aa68028024480828002000002e000000922086201000000a00a9840205c00006038800000c03810be09a1980a000021282c2f0020002c2584c0c800008060f8280000c0180006014080220b026198d8008f78758461550a99aced886c690803355c110d8d210063a42ae030aa838c74761c554548014eb0ba0ac3290172d1c564550210056ac1c21b0aa80087f855c161908011eb0f186c2aa0033c5c360185541c55b4204030aa800cf370441619480b9a862b98c2aa0e72d98771552412055ac26e5b0aa8008bd8714164c840187ee93a2cb908122fa1f645522100c77436e4a0a4200af28098f61550c756b09390c2aa173955d730d85540056bc0aa9b1a4200ab784442619082d4ed02382cb90803b44c220d85540066a318e2a924207aaf8658942904011eb0e100c2aa002a7a1265d8d213572b42e6030aa8058f4815cd64084011b90e982c8908023be1d62189540074a98862b2642028de87dcd65484051bd07bb2a8908021fe15705952100566c1081b1a4200cd770cc3615500b1ed0f180c2aa0062f21d40593211cd5b42065b0aa800ad58398061550019b2e0986cb108023d61e62185540
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x30820580ca000b30000309000000512101871400000001c1030000383000d1801e0000000001141878700040c0000a000800000000109c30200008860068015319015370d855401436a63705836348401d4130480715515200784e113044165c84014d19018f7154921007604c1201c554508018d1874c220185543c7249d13044361548018d2874c110595413bf149d5304436150801951804c071551520050da58545c662550014369615071589540040fa60545d954c84014d2974c110595420d724e1d3044164c840142d9215376553213b60d21c8444165c840103f985d07459721006a26093084164c84018e1825c0601855400714217704436348401c93945c1301855400e3421d3044165504018d0874c110595420053464063dc55448401991804c0715514210714e1d3044165c84adc90874c110593210063460d7088061550014d2974c110595210060d1518718061550e9691938c1105932100436e61701836348401436961537018554007242137044363484f3e1054181301855400d34645704c364884014369615371589543b60d214845c06155001c91744c110d855200658601201c554548014d19018f7150921005b0648704c361550014d19018c71549210050da58545c06155001c50955c1301855400784e153044164c84014c8974c12059542005b0648604c061550014369615370d8554006852148444363484018d383e0770595420050da58549c662550018d181dc270d8d210063460d701806155001a2454608601855400534a5d304416448401c53525c130185542d71421d3044165c84014d2971c110d8d2100534640714c16550801c9174dc130d85540063460770883634840121f9855054d8d2100744151704c061550efc91744c110d855400634dcd809cf6155001a51316003159721005b0648604c361550014d19018c715092100724251704c0615500103f985d4755932100634a1d3044165508eb834872151059321007842113044165c8401c5385dc110d8d2100e3221d304816550801c5295dc130d85540050da58545c3615500103e9815376553210054c640545c061550012d190a0f72d8554007145d7704c361550014d0974c110595420053465e704c06155001c53955c1301855400724e13704436348401a49824c2105972100534640631c554484018d2874c220d8554004b4640835c86155001a3054201621855400634e1d30443659040143a961537058954007145d5304436150801c9194dc130d855400724d09704c06155001c9294dc130d855400668601201c554508f1c51754c110d85543a59464e3044165c8401e10854c110593210053264073dd9210840141e96153735895400744153704c361550014d197181301855400714657704c36155001a91316003159321
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x8802020000e0421484dc110d8d210058254c2a2e0980c2aa002831a01518718061550eda084a928b826030aa875e0421c854c110593213b70210e42260882cb90802c12a6153704c36155001a082a32e3026030aa800d80151921813018554
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x209
  | 7 => 0x3
  | 8 => 0x20c
  | 9 => 0x20d
  | 10 => 0x20e
  | 11 => 0x1409
  | 12 => 0xb09
  | 13 => 0xb0c
  | 14 => 0xb0d
  | 15 => 0xb0e
  | 16 => 0x140c
  | 17 => 0x140d
  | 18 => 0x140e
  | 19 => 0x1549
  | 20 => 0x154c
  | 21 => 0x154d
  | 22 => 0x154e
  | 23 => 0xb89
  | 24 => 0xb8c
  | 25 => 0xb8e
  | 26 => 0x1489
  | 27 => 0x148c
  | 28 => 0x148e
  | 29 => 0xbc9
  | 30 => 0xbcc
  | 31 => 0xbcd
  | 32 => 0x14c9
  | 33 => 0x14cc
  | 34 => 0x14cd
  | 35 => 0xd09
  | 36 => 0xd0c
  | 37 => 0xd0e
  | 38 => 0x1609
  | 39 => 0x160c
  | 40 => 0x160e
  | 41 => 0xd49
  | 42 => 0xd4c
  | 43 => 0xd4d
  | 44 => 0x1649
  | 45 => 0x164c
  | 46 => 0x164d
  | 47 => 0x1049
  | 48 => 0x104c
  | 49 => 0xb0211
  | 50 => 0xb0214
  | 51 => 0x140b11
  | 52 => 0x140b14
  | 53 => 0x144b
  | 54 => 0x155411
  | 55 => 0x148b91
  | 56 => 0x2cd
  | 57 => 0x19cd
  | 58 => 0xd1491
  | 59 => 0xd1494
  | 60 => 0x105491
  | 61 => 0x104a
  | 62 => 0x105494
  | 63 => 0x14cbd1
  | 64 => 0x184e
  | 65 => 0xd54d1
  | 66 => 0xd54d4
  | 67 => 0x1054d1
  | 68 => 0x1054d4
  | 69 => 0x104d11
  | 70 => 0xd1051
  | 71 => 0x104d14
  | 72 => 0xd1054
  | 73 => 0x1a0d
  | 74 => 0x104d51
  | 75 => 0xd5051
  | 76 => 0x104d54
  | 77 => 0xd5054
  | 78 => 0x188e
  | 79 => 0x28e
  | 80 => 0x44d
  | 81 => 0xb1394
  | 82 => 0xb0954
  | 83 => 0x94c
  | 84 => 0x138c
  | 85 => 0x138b
  | 86 => 0x289
  | 87 => 0x94b
  | 88 => 0x168b
  | 89 => 0x9cb
  | 90 => 0x2c9
  | 91 => 0x9d9d5
  | 92 => 0x1699d5
  | 93 => 0x9c2d5
  | 94 => 0x1682d5
  | 95 => 0x94e
  | 96 => 0x138e
  | 97 => 0x9ce
  | 98 => 0x168e
  | 99 => 0x28d16
  | 100 => 0x94d
  | 101 => 0x138d
  | 102 => 0x9cd
  | 103 => 0x168d
  | 104 => 0x2cd55
  | 105 => 0x9c296
  | 106 => 0x168296
  | 107 => 0x29316
  | 108 => 0x2d355
  | 109 => 0x142d5
  | 110 => 0x1342d5
  | 111 => 0xd42d5
  | 112 => 0x1a02d5
  | 113 => 0x19c2d5
  | 114 => 0x9d856
  | 115 => 0x169856
  | 116 => 0x949d3
  | 117 => 0x2c291
  | 118 => 0x282d1
  | 119 => 0x9c956
  | 120 => 0x9c955
  | 121 => 0x149c2dd
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1262
  | 6 => 1964
  | 5 => 1019
  | 4 => 109
  | 3 => 9
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/35+packedAt gbK8 (1664+(h % 35)*6) 6) % 64)
  | 7 => 2*((h/441+packedAt gbK7 (46694+(h % 441)*11) 11) % 1262)
  | 6 => 2*((h/682+packedAt gbK6 (94272+(h % 682)*11) 11) % 1964)
  | 5 => 2*((h/367+packedAt gbK5 (60121+(h % 367)*10) 10) % 1019)
  | 4 => 2*((h/71+packedAt gbK4 (7630+(h % 71)*7) 7) % 109)
  | 3 => 2*((h/10+packedAt gbK3 (729+(h % 10)*4) 4) % 9)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1fffe0e0f83fe1ffffc3c03ff1448c7c8c7e4f
  | 1 => 0xe1e03f00ffc1fe1e03fc003c02b8f3b0f3b38c
  | 2 => 0xfe003fff0001ffe003fffffffcc303c303c3ff
  | 3 => 0x3ffffffe000003ffffc00f03fc03fc03f0
  | 4 => 0x3ffffffffffffc0000000ffc0003fffc00
  | 5 => 0xffffc00000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2a1a020190a202a19624124a0008414841645
  | 1 => 0x20c2a7006948e20c2ae602a86018b1b0b1b38c
  | 2 => 0x54040949000155404088949344c102c102c09a
  | 3 => 0x8932b2b5ac000893332b208b02dc02dc0360
  | 4 => 0x10101cdcc6319991e0000c010fec00036b6800
  | 5 => 0x991e001804201101000030020ff76b68000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37993
namespace PEqualNP.Outside.L_meta_37993
open PEqualNP.Outside.L_meta_37993.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 14 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 85 := block_range (n:=85) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 85 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 82 := block_range (n:=82) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 754 := (concat (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 bs0_4_288)) (concat (concat bs0_4_384 bs0_4_480) (concat bs0_4_576 bs0_4_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 11 := block_range (n:=11) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 779 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 bs0_5_288)) (concat (concat bs0_5_384 bs0_5_480) (concat bs0_5_576 (concat bs0_5_672 bs0_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 44 := bs0_6_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 12 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 91 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 794 := (concat (concat (concat bs3_4_0 bs3_4_96) (concat bs3_4_192 bs3_4_288)) (concat (concat bs3_4_384 bs3_4_480) (concat bs3_4_576 (concat bs3_4_672 bs3_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 69 := block_range (n:=69) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 741 := (concat (concat (concat bs3_5_0 bs3_5_96) (concat bs3_5_192 bs3_5_288)) (concat (concat bs3_5_384 bs3_5_480) (concat bs3_5_576 bs3_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 42 := bs3_6_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat bs4_4_0 bs4_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := bs4_5_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 9 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 109 := (concat bgb_4_0 bgb_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 59 := block_range (n:=59) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1019 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960))))
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
theorem bgb_6_864 : Interval gbAtlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 44 := block_range (n:=44) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1964 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632)) (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)))))
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
theorem bgb_7_864 : Interval gbAtlas 7 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1262 := (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat (concat bgb_7_288 bgb_7_384) (concat bgb_7_480 bgb_7_576))) (concat (concat bgb_7_672 (concat bgb_7_768 bgb_7_864)) (concat (concat bgb_7_960 bgb_7_1056) (concat bgb_7_1152 bgb_7_1248))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 64 := block_range (n:=64) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := bgb_8_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 36, 38),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0feeefeeafeeaf0a0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276809888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37993.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.and,[2,6]⟩,⟨.or,[4,7]⟩,⟨.or,[0,7]⟩,⟨.or,[2,6]⟩,⟨.and,[5,10]⟩,⟨.or,[5,10]⟩,⟨.or,[1,9]⟩,⟨.and,[8,12]⟩,⟨.or,[11,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276809888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276809888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37993

open PEqualNP.Outside.L_meta_37993 in
theorem PEqualNP.Outside.L_meta_37993 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276809888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276809888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
