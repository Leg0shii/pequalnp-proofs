import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37181.Model
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


end PEqualNP.Outside.L_meta_37181.Model

namespace PEqualNP.Outside.L_meta_37181
open PEqualNP.Outside.L_meta_37181.Model
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

def SBf (j : Nat) : Nat := [6, 8, 6, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37181

namespace PEqualNP.Outside.L_meta_37181
open PEqualNP.Outside.L_meta_37181.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4400608030d4090081cf2c314e2802d181bf43de43bd43dd439d43be42bc42de32dc32be41bc41de31dc31bf40bd40df30dd30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1102031400196300409000a70082047552438e292871c5150e3ea0a1c754c428faa4651d540ca3aa620c7d52318eaa0631d53d023aa9984755130
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x500006085987548ca0e62d523183189544c2146155130
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
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 20)*5) 5
  | 2 => packedAt s0K2 (156+((h/1+packedAt s0K2 (152+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3ffff83fffffffc0fffc1fff83fffffe78f1ff
  | 2 => 0xc0ffffc0fff83fff07ffe0fffc1fe07f9f3e73
  | 3 => 0xff03ffff03ffc1fff83fff07ffe0ff81e7cf9c
  | 4 => 0x3fffffc0001ffffc00007ffff0001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4108888209210402948094901292a282850a5
  | 2 => 0x922911064920608b02952092a4124154932652
  | 3 => 0xa4a22121a44031550265204ca409505458b18
  | 4 => 0xacb3c4a49076b5e69cc318c7739c0619f80de0
  | 5 => 0x30c38738e38739f8e73b9ce063181861fef000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37181
namespace PEqualNP.Outside.L_meta_37181
open PEqualNP.Outside.L_meta_37181.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x23004d08d0a54d1f143c5841c304064a401803c00009007401200003802200a00000000048000190004000000002700000002e980182c01002007111b0e00080881e040030200001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683be42d077885a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41efa9a835f53506f8a6a0f714d41ae29a83bf435077a86a0dfd4941be29283be425077884a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077c8620ef10c41bf290837d521077e8420ef50841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f790f31eea1e637e52cc6faa598f78cb31ee196637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63dc438c6fca518df54a31ef99463dd328c6fca318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898f790d31eea1a637f524c6f8a498f78c931ee19263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c7be8618f710c31bf290637d520c7be6418f74c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29c437d52886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0xc0000003d2000000003ee0000024b000000000004b4a600000031e6a0001880000000000005a000d38db52a064229712788fcbf28b4c85380000f000000e28df49e1e84809150e324988242f2170c2951000000640000005986e849000578caa0f4d2000000000008380000000068840825096000ca22623c1394480000029d100e60000001e8004f85d0ec9353e491800000468000a1a5d0621f91b87933e1401f80a270260a58f13aa000690952202c06983b420000af9480001ad429130645ac001552b668c000003ac33501a2e0b24dc0019c0001cc0020d00095c00000376475008220008b45d92f2ec0006d1ef0403f80024c00097c440000009b4108000f80000018600002447015196000759c72e66a472a7146a8a406a781640e09685d1ac3850d14c0003f4fc1b31744686027d13c0ac000f61e0740a99402660011b18c31622c2d8003b804800244000854be0a60008e4f525e24e2703528e0b0890000003002903b0b144a5b40b86c1580000000c0e40094185f0360f03109300c0507c9f409a7985b0003300000010c0e8000000b4424370ab8ab22c314cb8a01d07ece216903a65914086272000089ff24ca1000255256000261ab4a4858c99df53295140a0a12e0dc90a311f60b8299ae3bca493a8573c231000230000000000000001786798451099d0f90034c5690c23341209c2301c1b03088906e13a5a90010a3026dcdc2412ca1d50982619c5fd4126b422728d01cf4841944d80029e734778010040000c09000010b8000000208c11058340080f07c1401400014050080200400000020000100001000000400200004030020140003c19000020040006401008000280c04020000260000001401004020240b00013000000000205c01038000080b014070000203407008030080903c0200c030040a0000b000060000f000010000003001000030840101800070000040200c02000030180101845000040240000004078010100400000000000080102c06010080082a014030000102c210380000000008000000600c0104801010000000b0040000814008130180b0300005c0700008034020000303016000030000100001008070000a0140601c0001400000180080100c0005403000030140000c040000b006fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855
  | 3 => 0x770009d0bd17b4a27886a1b61a01f49a2533c80000000040a0cc00000312445110f40682a40014d18c110e99eb17e2a9249b51424080010524a4f4e600027c0000018a06a76c0019d0000013b800000390ab2070841a07a94422a22834a1700051c219e7230000001d22e04c85286d4e62cd431c92a81843c1f5000580710c3000000ac1d8080001468004284186889f08e5b0f6a3c0000009600038c1200006f4703b09b2593e202cbc0000006652710e0005dc00085000000000000000001792a000a00df800374234000d935e0007c0004de9880023a45821cae87b0001286a80020252910987134000000e717c2dce1a020008700013a21e7748b8f30c613c000a30000792e1b44c02885793b4800a0e09831e4378001ec1d2540b221e4640000721d436001318004e4000b41c207c2640008f02c000000000009fc4926c4a00005e1f03fa51400265000780c68ca06c8f4980073363a8b085a1046a80025b0cc00000261232508dc8230267ccd90000a4380ba95937c304d0a6a518518001b1490a3c94172000000fc9c834a181251f633c0013d1043fc0202880047c2b886a7e48ea41370003c61c43f8f752c1c0b79e80006b4de800000000c11490001053b0102dc000000000002d4000640008212b00000048c001204cc0007fa040003e8d22682a481926883000000f2a7b216224e7000000001060000003b48a003000000000000520e4ae0003f8768b18004768bc8e1c027e1511194100a9e46600045640d4a28a4167441511b24819c1803a52635c540003240000025800075000219100154b100052290c42000322000000fc0082e49709445407c8385652e258eb92931c2f48401a3dc004001bc118424b38001c65f4638003203b8000000302e08f8003587e856a703340011380024472d228000586
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420d954621083655108420d9547200826f6548020b9185200836551480209ed95200825f63553109718d54c425e63153109758c54c423f6454f108f19153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e6394b109758e52c436452487109798f548425d63d52109798e548425d63952108f993538423d64d4e108f992538423d6494e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452442766588510d914a21442746548510d9149214436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109d597210436552c84109d59421043655208410d954b100427965840109dd9510042e46244010d9549100427b6544010
  | 1 => 0xc71c5450d31c7152324c65e650c931a7590324c71c540c931c7152314c63d6595031c718d540c63e64150319798c540c65d65d0c31c7553430c65d6510c31c7550430c71d54cc83197d95320c69c644c831c7551320c71d54cc43197d95310c69c644c431c7551310c677654c4319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f219798f548865d63d52219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e2197d8d544865c63551219ed81544867860551219798c544865d63151218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f990504863d64141219798c504865d631412197d8d540865c63550219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d63948218f992510863d64944219798e510865d6394421b958a210866f65484219dd9521086e76548421d9d9521086e460484218fd91500863c645402197d8d500865c6354021d9485500871d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d029c6350740c754d41d031e53d0e40c794d439031e5390a40a758c429031e5310a40c794e419029d6310640c794c419029d63d0240c794f409023e6510d409798c525025d63149408f997425029c63509409798c515025d63145408f997415029c6350540a798e405023f6550c4097d8d521025c63548408f596421029d631084097d8d511025c63544408f596411029d6310440a758f401023f65500409ed95401031c6355330c755343cc31d5410f30c755332cc29c644cb30c755132cc31d54cc730a719131cc31d544c730c758e548c31e5490e30c7951438c31e548ca30a7590328c31e540ca30c7952318c29d640c630c7950318c29d64cc230c7953308c25d63951309bd89544c26c62551309dd85544c274615513097997434c25e6510d30c7550434c23e64149308f590524c25e65cc930a7191324c23e64145308f590514c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c3097d95430c31c5450c308fd91520c23c645483097596320c29d640c8308fd91510c23c645443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c823f6454f208f19153c823e6414f208f59053c823e64947208f59251c825e63947209758e51c825e63d52209758f548825e63952209758e548823e64d4e208f593538823e6494e208f592538823f64546208f19
  | 2 => 0x4698f2000738001ef2525f4101fe04c7e84507501a275111410ec698f01512c40ecfa0002fc5d87411f3c40b1131f20645c49906b0000ac00000326110d59010000000010c0f8664a90193ce000d78001360000a103000000ac964000524b600019a701098813380005581d3da830128b70c40000000031c0000013d0001dcde8002da000db8002c23a40012717c7e5128e7000000ab2033f63f00003f000248ad0ca1c83102a1380cc0000aa0a0002889f80000004ccd18a3e6870c18942f0300539331f6818468a437e1406597c0802bc8b9572900009280029c000251c128e04c0403002078010080004000000010080a01c0500005010040100a010010040f0200000003030290140101c1700c030180c004010080e01805004040000a00402008000400400806000020040900402008330dc02008050180700400034000280b05012000040080103c03008010180200c01024000040003000000000380a00002000080240b0140905c0003c110080001c0005c000181101000010020000000c0602000004040340000401028050200002800008010000b00c000000000c0d00c0400002040040000500001014000200c00c0000804034000040003c0000800024040129d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9c6150c43a7d814310f1d4354843c750d5110f1d439404397d8d51d0a5c63547429798e50d0a5d63943429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429d98454cca756115332c715143cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f992544ca5f63551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3d6595032c718d540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c83297d8d52d065c6354b41a758c42d065e63943419758e50d065e6394a419758e529069c6350a4197d8d509065c63542418f997435071c53d0d41c714d435071c53909418f994425069d6310941c714c425071c53905418f596431071d5390c41c754c431071d53d08418fd95421069c6350841c754d421071d53d04418fd95411069c6350441c754d411067765504419b98854cc66d6215331c715143cc63f6454b318f19152cc69d640cb318f99250cc63d64943319b98b548c66d62d5231c7d50438c63e6494a318f592528c69c644ca318fd91508c63c64542318f992544c65f63551318f994544c71d631513197996434c71c5490d3197195434
  | 3 => 0x18c001ca3103acaf9d003c3f48101b1b83e06d8a02e60002b8003cc50c0585f3980003c891078060ff9750000003a1823782c000060000000000002a60009b88f0a2578e491000085c0020b2282b8001ea21a48cd707d360474f58b501e00000000346000960c823c8382d0000aa000f61e1000000000bd20c0008b0b6000000001a002e6b0000cf446878c89c41123387089e000000ba0001920003f0823d0000c600031601ca686f10e4480000007204800000100194da81f0e07c0f88d425e65c271a83ee65098000000000001670001b8789722d20b5089502961c4b704742420ceb0fa0000005e17a24c2989b1c2248000000000000e80500007a78cc816a1e8550a10f7010770001cb3ca56c2e0a107c674000001c66147f09911c6f8ea9aa164000001b10962d00e1c52fe03102179256380000c7000000771a723413c6a80040446ce79181a4184000000007680b0a9000424661840000000004520000085a0101c344a293b44083c56a0918c0688789f0f40000002822600013a160006609a067000090001e900030c00186300000109d3000000001a12503645fa05000000002183ea635068bb3ec1a4ca92d000360ae1390003986b02f0000004ba192d6000151b81846e8d68df2f6010d982328086c000e52980c0001b60a6024889ee000470c90330007346f08c28c00000000242294001310007209a9db4002a8518f30702a00000022a744ec9550922686294f09a77c032210ac718bb82e0f6774b0010000000420430001c801000000000000000fe8501880000070c0006a00087400170000000d104c3642c4000002ca87d040ef000000dc800000240c38000000002d8000f04a8000ff0004f0ac000068000780003483405c9082d0790fc0642de414751043122cc4b0483682b00004238e7609009c20e1b50a8001300145d05d1161cca522440e58c6b8f93fa66c000b825c67843000302000e919f0006a47113e1b4178760414206946092221c148441d708c0a4428f52880009d15d3f824c4a9193bc1a0768363a85990d0350001608506c0066586e8370b2000dd8f6022088c780000
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x4110120001540000000893001c018d0483804c02c000a3c300000000402200080003431c94354843a28e2a1aa221d1b7050e5010e8ab88a8a1e65459c75410e32838ecaa2641950d7215143cc687396a821c63075d8540c931838ecaa26418c1c76551310c60e3b2a899661071d9544c73083aed2a0651841d76950318c20ebb4a998461431c95410d30a28e2aa0869850d72151430c28ab88a8a1861191d95244010
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (6+((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s1K6 (731+((h/13+packedAt s1K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s1K5 (20202+((h/222+packedAt s1K5 (17982+(h % 222)*10) 10) % 880)*11) 11
  | 4 => packedAt s1K4 (22768+((h/183+packedAt s1K4 (20938+(h % 183)*10) 10) % 728)*11) 11
  | 3 => packedAt s1K3 (1071+((h/7+packedAt s1K3 (1029+(h % 7)*6) 6) % 39)*6) 6
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 2 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 3 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8104044410480000a5090044802254501850a5
  | 2 => 0x248a48832490612c0a42a429521482a9432652
  | 3 => 0x429291090d2206554084ca8265412a0a858b18
  | 4 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 5 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0faaafaa0faa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37181
namespace PEqualNP.Outside.L_meta_37181
open PEqualNP.Outside.L_meta_37181.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xc11c04023c81492c400e34018000a302204a0df43be43bc43dc439c43bf42bd42df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x4829c6008009300040314b000614794e438ea90871d5110e3ca021c714d428e2a6651c544ca38a6a0c7153318e2a2631e539023ca9184715030
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x68108558454cca0d621533183588540c2156115030
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | 2 => packedAt s2K2 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (297+((h/5+packedAt s2K4 (272+(h % 5)*5) 5) % 21)*6) 6
  | 3 => packedAt s2K3 (371+((h/4+packedAt s2K3 (351+(h % 4)*5) 5) % 18)*5) 5
  | 2 => packedAt s2K2 (155+((h/1+packedAt s2K2 (152+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffff07fffc1ff83ffff07ff07ff07fe7cf3cf
  | 1 => 0xf07fff83fffe1ffc1f07f87ff87ff83fa33cf3
  | 3 => 0xff83fffc1fffe1ffe007ff87ff87ffc1c3cf3c
  | 4 => 0x3ffffe00001fffff80007fff80001fc0fc0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8108111084820000a5090089008902940c5145
  | 1 => 0x24112209091030940a42485248525028a12492
  | 3 => 0x4222442052210329408495049504a501428a28
  | 4 => 0x6b5b894a43b555ce73d0c447e660318df40fc0
  | 5 => 0x8c630e739c3999f39ce7e660c440c631fbf000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaee88ee88ee88eeaaee88ee88ee88eeaaee88ee88ee88eeaaee88ee88ee88eeaaee88ee88ee88eeaaee88ee88ee88eeaaee88ee88ee88eeaaee88ee88ee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37181
namespace PEqualNP.Outside.L_meta_37181
open PEqualNP.Outside.L_meta_37181.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xf38000c00300b00234a00905000020610714121520df43be43bc43dc439c43bf42bd42df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xe00280b01928004a30088060000010404794e438ea90871d5110e3ca021c714d428e2a6651c544ca38a6a0c7153318e2a2631e539023ca9184715030
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xd000808558454cca0d621533183588540c2156115030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (297+((h/5+packedAt s3K4 (272+(h % 5)*5) 5) % 25)*6) 6
  | 3 => packedAt s3K3 (371+((h/4+packedAt s3K3 (351+(h % 4)*5) 5) % 22)*5) 5
  | 2 => packedAt s3K2 (155+((h/1+packedAt s3K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff07fffc1ff83ffff07ff07ff07fe7cf3cf
  | 1 => 0xf07fff83fffe1ffc1f07f87ff87ff83fa33cf3
  | 2 => 0xff83fffc1fffe1ffe007ff87ff87ffc1c3cf3c
  | 4 => 0x3ffffe00001fffff80007fff80001fc0fc0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8108111084820000a5090089008902940c5145
  | 1 => 0x24112209091030940a42485248525028a12492
  | 2 => 0x4222442052210329408495049504a501428a28
  | 4 => 0x6b5b894a43b555ce73d0c447e660318df40fc0
  | 5 => 0x8c630e739c3999f39ce7e660c440c631fbf000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37181
namespace PEqualNP.Outside.L_meta_37181
open PEqualNP.Outside.L_meta_37181.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2c06492263e108151a000004a2518050187af407801d02b8000325cc024400a2b36447082c69085262c0000e2950c5a013a93800010b3c3012340203980000ff43fe43be43fd43fc43bc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x261bc544c278a8986f90d30de21a617f524c2f8a4986f90930de21261df324c3ba64985fd4530be28a61bf414c37a829877cc530ee98a61bf404c37a80987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c37c86186f10c30bf29061ee520c2dca4185f54830f6a90616d520c37c84186f10830bf28861f6510c2eca2185f54430faa886175510c37e82186f50430bf28061bf400c37a801877cc030fd18061dd300c3f260185fd5320dfaa6413f54c82fca9905f55320be2a641bc54c8278a9905fd4f20bf29e417d53c82f8a7906f90f20de21e41be42c837885907b8cb20f6996417e51c82faa3906fd0720dea0e41ef21c83da43906fd0320dea06417f54882fca9106f952209f2a4417d548837aa9104f55220be2a4417f53882fca7105f54e20be29c41be438837887105f54a20df21441bc42882fca3105f54620dfa0c41bd41882fca1106fd0220dea0441ef20883f641105fd5120dfaa2413f54482fca8905f55120be2a241bc5448278a8905fd4d20bf29a417d53482f8a6906f90d20de21a41be424837884907b8c920f6992417f51482f8a2906fd0520dea0a41ef21483da42906fd0120dea0241fb20483dc40905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf29841de53082bca6105f54c20eea98415d53082f8a6106f90c20de218417e520837c84106f10820bf28841f651082eca2105f54420faa884175510837e82106f50420bf28041bf400837a80107bc8020fd10041ed20083f240105fd5310bf2a621be54c427ca9885f55310deaa6213d54c42f8a9885fd4f10bf29e217d53c42f8a7886f90f10de21e217f52c42fca5885f54b10be29621be42c437885886fd0710dea0e21f631c43ea63887d88710fa90e21bf40c437a81885fd5210bf2a421be548427ca9085f55210deaa4213d54842f8a9085fd4e10bf29c217d53842f8a7086f90e10de21c217f52842fca5085f54a10be29421be428437885085f54610dfa0c21bd41842fca1086fd0210dea0421fa30843f261087e88210fc90421f710843f621085fd5110bf2a221be544427ca8885f55110deaa2213d54442f8a8885fd4d10bf29a217d53442f8a6886f90d10de21a217f52442fca4885f54910be29221be424437884886fd0510dea0a21f631443ea62887d88510fa90a21bf404437a80887e8c110fc98221fa20443f240887ec4110fb082217f54042fca8086f950109f2a0217d540437aa8084f55010be2a0217f53042fca6087794c10af298217d53043baa6085754c10be29821be430437886085fd4810bf29021ee52042dca4085f54810f6a90216d52042f8a4086f90810de210217e510437e82086f50410bf28021bf400437a80087dc4010fd08021f510043f220087c44010
  | 1 => 0xd520c77c8418ef10831bf28863bf410c77a8218f7cc431fb18863dd310c7ea6218df94031fd280637a500c6faa018fe54031bca80637f54c877ea990cfd5321bf2a6437d54c86f8a990ef153219e2a6437f53c86fca790df54f21be29e43be43c87788790ef90b21de21643ee32c87da6590efd0721dea0e437e50c86faa190dfd5221bf2a443be548867ca910df55221deaa4433d54886f8a910dfd4e21bf29c437d53886f8a710ef90e21de21c437d528877c8510ef10a21bf28c43bf418877a8310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21bf29a437d53486f8a690ef90d21de21a43be42487788490fb8c921f699243bf414877a8290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610ef90c21de218437e520877c8410ef10821bf28843bf410877a8210fbc8421fb10843ed21087ea4210df94021fd280437a50086faa010fe54021bca80437e53d02faa7a06fd0f40df21e81bd43d037887a05f94b40bea9681bf42d037c85a06f50b40de216817e51d02faa3a06fd0740df20e81bd41d037883a06fd4f40df29e813e53d037aa7a06f14f40dfa9681be52d027ca5a06f54b40de29681bf32d037c65a06f4cb40de19681bf51d037ca3a06f547409ea8e81bc51d037e63a06f8c740de98e81bc31d037e43a06f88740de90e81bc21d02faa9204f55240bf29c817d539037c87206f10e40bf294817d529037c85206f10a40bf28c817d519037e83206f50640bf28481bf40903f681205fd4d40be29a81bf435037c86a06f50d40de21a817f52502f8a4a06fd0940df21281bd425037884a05fd4540be28a81bf415037c82a06f50540de20a81fb405037c80a06fd4d40df29a81bd5350378a6a04f14d40dfa9281be525037aa4a06f149409e29281bf325037c64a06f4c940de19281bf515027ea2a06f94540dea8a81bc515037e62a06f8c540de98a81bc315037e42a06f88540de90a81bc215037ea0a06ed4140bf2a0813e54102fca6205f54c40df21881bc43102fca4205f54840df21081bc42102fca2205f54440dfa0881bd41102fca0206fd0040fd20081bd40103f280205fd5330dfaa6613f54cc2fca9985f55330be2a661bc54cc278a9986f90f30de21e617e52cc2faa5986f90b30de21661df32cc3ba65985f94730bea8e61bf41cc37a839877cc730ee98e61bf40cc37a81985fd5230bf2a461be548c27ca9185f55230deaa4613d548c2f8a9185f54e30df21c61bc438c2fca5185f54a30df21461bc428c2fca3185f54630dfa0c61bd418c2fca1186fd0230dea0461df308c3f661185fd5130dfaa2613f544c2fca8985f55130be2a
  | 2 => 0xafaa6216fd0c42df21885bd4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042dfa9885be5310a7ca6216f54c42de29885be5210a7ca4216b94842dfa8885be5110b7aa2214f54442de28885bf5010b7ca0216f540429ea8085bc5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccbbe87996f90f32de21e65dc43ccb3887996f90b32de216657e51ccafaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cb7c87196f10e32bf29465ef428cb7c85196f10a32f621465ac428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132efa1a65be434cb7886997710d32ce21a65ef424cb7c84996f10932f621265ac424cbde6499778c932bfa8a657c514cafea0995f14132bfaa065bf540ca7ea8195f95032beaa0657c540cb78a8194f15032bf29865be430cb7886195f94832df21065bc420cbbe64197b8c832ee99065ed320cb9a64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077c87a0ef50f41de21e837e52d06faa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0cf94f41dea9e83bc53d077ea5a0ef94b419f29683bd52d0778a5a0efccb41df19683bd32d077865a0efd4341df28683bd50d067aa1a0ef14341beaa4833d54906fca720df54e41df21c83bc43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077c86a0ef50d41de21a837f52506f8a4a0efd0941df21283bd425077884a0fdd0541df20a837f50506f8a0a0efd4d41df29a83bd5350778a6a0cf14d41dfa9283be525077aa4a0ef149419e29283bf325077c64a0ef4c941de19283bf515076ea2a0efd41419fa8283be505077aa0a0ef14141bf2a0833e54106fca620df54c41df21883bc43106fca420df54841df21083bc42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc77ea998cfd5331bf2a6637d54cc6f8a998ef153319e2a663be43cc7788798df94b31bea9663be42cc7788598f7ccb31ee99663bf41cc77a8398df94331bea86637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c77c8718ef10e31bf294637d528c77c8518ef10a31bf28c63bf418c77a8318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898ef90d31de21a637f524c6f8a498ef90931de21263df324c7ba6498efd0531dea0a63f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77c8618ef10c31bf29063ee520c6dca418df54831f6a90636
  | 3 => 0x8c1ae31425a3600000ae0000000000000ac73625c19070600072c70041843e5aa35e17664a5ee7327da00027600000000023430e00007c7400005dc03242a0f800000041a16c6a600077a0004b40005da0001a60820001ca6881245e422a02a00000000000024010000000080100800008c038000040000280000a0180c80000203801801004048008050020040380000200c000000060080180000c0000400801a004038010080040000a01a0040000601a00c0a00000404801804004000028090080040f8060000000000200a0000380400400001804006004080000040000000000000008800000008000000000040080200400c000010120000100200000009004000018068000000000180000800c000030000080d80000000000800000000000220000080500100400804005000024000050120000200000400c0000900001c0380300002400815002034010030020000180000200c00000004010020070000040901301201002002000024008000080000080000000c0b8010040040280b0020080000000600c03800002008018030060140180001200400800000004008010020200200400000c01000006008000170080000600f00000c010070000940000100002c0180000600000000000000008060040080280000c00004800004000008000060040000100c000000040000340200100a010008000020280780200000403006000004000030240100380100402800005004000008090000080400002a0000000b00600800000024008008000180080000200c06800025bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521fb94a43b7294877d5290fdaa521db54a43bf28c877d5190efca121df542439f29c87bf5290f7ca521cf94a43d7294872e5290f7aa521eb54a43de29487bf5190f7ca321ef546439ea8c87bc5190f7ea121ef94243dea84873d5090f78a121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021ef94c439f298879e5310f7ea421ef948439f29087bd5210f78a421efd4443df28887bd5110e7aa221ef14443dfa8087be5010f7aa021cf54043de280877e53d0afaa7a16f90f42de21e857e51d0afaa3a15f94342bea86857d5490afca7217794e42af29c857d5390bbaa7215754e42dfa1c85be4390b7a87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1216fd4e42df29c853e5390b3ca7214794e42dea9c859d5390b78a7214f94a42dfa8c85be5190b7aa3214f54642de28c85bf5090b7ca1216f542429ea8485bc5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e531
  | 4 => 0x80004f000000079a01e5961f41e21b614c0d25d22dc3b035a29c0cc6721d63dc1de5765945b62fa67869811231a0004de04000049c07a00000045a60c77400000004e0005983784f40000007e67580000000000001dc6680000000004e40002940000b05c863639e3741d254e28c1040003980002f000048858e0000000006140004262280000000000000005720000005d00008240000000000005d86d20000e46e834c0000980004a81402e66ac7025040225e035660e48012a0000000004220002646a27fe00052a7b201a0006402662566800000000000007962027a645c00000018824c00000000005a0006706745060000c808a6a45be65000074800000053a53e1d852c0004f612c24e3220005b800000046681e0b428033429a4ec62000000044800000076e0000000002183e00003080000005780704ee5b20a652e0004720007de1500000dc05680000081c42819461c0002f81ee16025e04c07e45400673a0000002f400000035400031e7d875a00006c6020ee75050a23800000000000039a00000020a0000007ac3f248265a3fa75e7ae12e17a2161743265120005f86162581262b03884002880000001f60e200847046c24074a1f83842be0000000000000000003b83ae4405c20001280002ce62e47e0001681345e64fa1724f85f20004520004385241ec0503ea00040c5260000000004aa65474c6b40002603a27c416600062634209c0000100000003cc7d46ca0000007cc0003060002d84fc69000006436e13a0000002920ce4da1fc7186040000000006f065c0000000006285620003b40000760002f20f06622b66180144c00003c463844401c7f83f81980fc72618013015a32a2a64847e44dc5e200419278a00061e3ec8226aa4e22b406a6340a008c4127ca00000053c4622ac75621e0000900000000000007fc00080a6da19a0b281003a6121364a01485841585f02ae2302740004561960f44b25ca0005484083ee33c2ca0000004500ec5e80005c65bc8163320006582064987c84c40000000000003ba6d600000049669c00036200013c0000000000000003e878c08000000039400000000056400039659c75c6ee21c5146960005360fe66c0784d80000a80000000000000000000001fa28a00061a00003400038e0000006ce6a800077866600034e5a80007286220002b857e2365d62240003481cc7ee4145ea0000002a07904366560006ec18c1081620000001546e000000000010c00000001204a09e18412215c1f23fc45866e0c43e645e8143f06602d40001826fe21249244e5925280385703444ac6b67703be49a0000740001560006b80000000002463c20007e232800036804879e5000003bc48c0000001b25907843820d62c87ce1206dc09a7dc1c625433e1e030c76a0007d00000265fe4303a83b65ac3
  | 5 => 0x3b20b60006f60000000006080000000000000fa2e033a68c00072e00071477c6b226c55a0005de6fc00018e0000002d600056a0f20005ec16e0000000000aa0000000005f60000002321327300000004760de03e3ca0000003da0007680007f61ea80e7640628087f011816a0004686c65f450c54400022278e1c81446303000000f640479c2ea0005b023e27281a5a020c00056614e0002707200c00000006f477e6be34a64c00063a00003c19e6420527be37c7d60000005a20003721b80006e435200056002860067671c00000000000063c25259e00e0b869441c5c411c17c02055c7ec00000000a3aa1d00004d400042c4343f47a079400000051a0000000004a655031c6640003206321701061a000065246e1ce57c2a817843a43228235050e7528202440662bc2c054a0002085cc2da8260361aa4206c476c2a200014624871040e2aa0d858c7867a86c810e2260e65345ba6ea3386464e874404667c7b62e81e61ba54000044a4464103d84be01841e60600064e7122d03d648e4a268a39255670e1c204464454273c1a249426e00069e0000000000007e80000002c43e22fc80460a0000000000008060000427b411e7ea0000005862c239055e3d272400079858819c2905a432c0e00301c00003d000055200068436c6de21452000065e11a47822c32e6b03364d200000000000000000057a2b20000547040000000000000007545087e05180000008020000007b027e2680600be3fe81808400078854c7bc71e3767806d42784cc58055402429e1b04ba00000000036453072a00000062400000000002a0007164902622ec35c08e76600047c0000005821640001381a40001160004f268e00070847a56e23c0006820002cc1ac00031228e3a040674e0167460c20000004e00000001a81103de0001c40005320003ac00000006800038635872213e00037e5fc0000004744a45223107820000020e84b60000000006ae0005100000000001be0003a64ce2a40000000c60007767d20000004ae0000007c26e63c00004645ae22e00017e7c63f62844c61867a442e6d00000002de7aa0005b420438a0721da3e40004c844c7f469a0000d451c76000000002c0000002f658a4bc0a251e67e27c4866f80000005fa00011414a4fe66a37a0001f04b800057454600077209621a6480000000000001d40000000002c600000000037000000020000036676223a0586fa1e409400067a00000000056c15200000000000000029600000000000040233055842470c0000000000007342fe4d026a5c03c85384600860008120003247387fa62a7f25ce1026ba00080c62c46a0000000a410020e2e26102982860d01fe71a5a640a7ba2e40006bc6cc7426923186f24ca48a44205c0000bc5166c26a07920002504b06e20ba15e41630a1e
  | 6 => 0x882ba00070a00038002e3d400027a43c0005d400049e1b44c20000da00024a0000005680920000001426d80006c03c624239c2203040002ee00073e00000000036a0007a20000000007b82d20000ea0000003ce0003a40000004ea7c01bc21063e68631634600050234018a4e605e00000c59a4d60003020ca06e00000000010a
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x9544422c62551108fd85544433761551108fd81544433b60551108f993534423d64d4d108fd91534423c6454d109bd89534426c6254d108f990534423d6414d109b988534426d6214d108fd96434423d6590d10ab98a43442b56190d10ae582434423f6510d108f594434431f5310d10c714c43442b56110d10ae580434423e64d49108f593524423f64549108f191524425f63549109718d524423e64149108f590524425e63149109758c524423f65909108f596424429e6390910ad58642442b960909108fd94424423d6510910cbd48424432c5210910ad58442442b96010910ae58341442bb60505109d19531442f0604c5109d19521442f06048510ad587404423f65501108f59540442b761501109e19530442f0614c110f44c530442786548110bc18520443e121481109798f540425d63d50109b98b540426d62d50108f596540423e63950108f98a540423c63550108f189540423f61550108f585540423f60550108f581540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431f6494c10c7192530423f6454c108f191530431e5454c10c7551530431f6454c10c7191530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108fd96430423d6590c10c794e430431d5390c10ab98a430423f6510c108f594430431e5310c10c754c430423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cbd92520432c6494810cb90e520432c43948108fd91520423c6454810cb951520432d5454810d394d520434d5354810cbd91520432c6454810cb90d520432c43548108f990520423d64148109798c520425d63148109b988520427661148109e980520423f65908108f596420429e6390810c794e420431d5390810cb94a420432d52908108fd94420423d6510810c794c420431d5310810cb948420432d52108108f992510423d64944108f597410431e53d0410c754f410432e52d0410cb54b410423f6550410c794d410431d5350410cb949410432d52504108f992500423d64940108f597400431e53d0010c754f400432e52d0010cb54b400423f6550010c794d400431d5350010cb949400432d5250010d554f100436552c40109e59610043595384010da54a10042f161840109dd9510043555344010d954910043b34044010ec501100427b6544010d654d10043695244010ecd0510043b14144010bcd9510043736544010ec99110043b16444010ec95110043b15444010dcd4d10043d25344010dc54d10043d15344010d454d10043b24344010ec10d10043735244010f894910043715244010f854910043615244010ec90910043b04244010
  | 1 => 0x82e8604c9208f990514823d64145209798c514825d63145208f997414823c65d05208f995414823c65505208f99740482ae62d01208f19540482ac62501209798f540825d63d50209d987540827561d50208f596540823e63950208f586540823c63550208fd85540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831f6494c20c7192530823f6454c208f191530831e5454c20c7551530831f6454c20c7191530823e6414c208f590530825e6314c209b98853082766114c209d584530823f6590c208f596430831e5390c20c754e43082ae6290c208fd94430823d6510c20c794c430831d5310c208fd96420823d6590820a798e420831e5390820c754e42082b960908208fd94420823d6510820c794c420831d5310820ae580420823e64944208f59251083365494420cd55251083565394420d554e51083366494420cd59251083364394420cd10e51083364294420cd10a51083365454420cd55151083565354420d554d51083366454420cd59151083364354420cd10d51083364254420cd109510823f65d04208f597410831e53d0420c754f410833651d0420cd547410823f65504208f595410831e5350420c754d41082ac6250420cd945410833551504208f992500823d64940208f597400831e53d0020c754f400833651d0020cd547400823f6550020c794d400831d5350020cd94540083355150020d354f200836551c8020dc546200826f6548020d354d20083655148020ea501200827b6548020ea909200837151480208f98e54c423e62953108f18d54c423c62553108f99353c423d64d4f108fd9153c423c6454f108f99053c423d6414f109b98853c426d6214f108fd9643c423d6590f10ab98a43c42b56190f108fd9443c423d6510f10ad58443c423e64d4b108f59352c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c423f6590b108f59642c429e6390b10ad58642c423f6510b108f59442c42b56110b10ad58740c42b761503108f98e548423e62952108f18d548423c62552108f993538423d64d4e108fd91538423c6454e108f990538423d6414e109b988538426d6214e108fd96438423d6590e10ab98a43842b96090e108fd94438423d6510e10ae580438423e64d4a108f593528423f6454a108f191528423e6414a108f590528425e6314a109758c528423f6590a108f596428429e6390a10ae582428423f6510a108f59442842b96010a10ae58341842bb60506108f98e544423e62951108f586544433561951108f5825444339609511097d8d544425c63551109bd89544426c6255110a718d54442ac6255110c7d8d544423c6355110c718d544421c6355110cbd89544423c6255110cb18
  | 2 => 0x524c930e3109324c2d8604c9308f990514c23d64145309b988514c26d62145308f997414c23c65d05308f995414c23c65505308f997404c29e63d01308f195404c29c63501309b98b540c26d62d50309d987540c27561d50308f596540c23e62950308f586540c23c62550308fd85540c23e64150309b988540c26d62150309d984540c27561150308fd96430c23d6590c30ab98a430c2b96090c308fd94430c23d6510c30ae580430c32e5494830cb552520c32f6494830cb192520c32e4394830cb10e520c23f64548308f191520c32e5454830cb551520c32f6454830cb191520c32e4354830cb10d520c23f65908308f596420c29e6390830cb94a420c32d52908308fd94420c23d6510830cb948420c32d52108308f992510c23d6494430cd952510c3355494430d994a510c3655294430cd992510c3356494430cd90e510c3344394430cd90a510c3344294430cd951510c3355454430d9949510c3655254430cd991510c3356454430cd90d510c3344354430cd909510c33442544308fd97410c23d65d0430cb94b410c32d52d0430cd947410c33551d04308fd95410c23d6550430a718d410c32e5250430cb549410c3365150430cd545410c23e64940308f592500c23d65d0030cb94b400c32d52d0030cd947400c33551d00308fd95400c32e5250030cb549400c3365150030cd545400c34d52cc030d5547300c371518c03097d95300c34d524c030d5545300c399404c0309ed95300c39a434c030dc545300c25e63d53209758f54c829e63d53208f98f54c831e63d53208798f54c831d63d5320cb98b54c823d61d5320ce58354c823e6315320cb98854c823d6115320ce58054c823e64d4f208f59353c823e6494f208f59253c823f6454f208f19153c823e6590f208f19643c82ae6290f208f99443c823c6510f20c794c43c831d5310f20ab98843c829e6390b20ae58242c82b96010b20cb15232c832c544cb20d314d32c838c434cb208f99251c823d64947208fd9151c823c64547208f99741c823c6550720ab98b40c82ac62503208f98e548823d61952208f18d548823f61552208f993538823d64d4e208fd91538823c6454e208f990538823d6414e209d98453882756114e208fd96438823d6590e20ab98a438823f6510e208f59443882b96010e20a798e428823e64946208f592518823f65d06208f597418823f65506208f59541882ac62506208f98f544823d61d51208f992544823e65151208f98c544823e62151208f188544823d61151208f993534823d64d4d208f992534823d6494d208fd91534823c6454d209dd8553482746154d208f996434823c6590d20ab98a434823e6510d208f19443482ae6210d20ae580434823e6590920a798e424823e6510920cb152324826c654c920cb151324834c534c920e310d324
  | 3 => 0xf408f98a53d032e6294f408b98a53d032d6294f408f58653d02b96014f40ae58352d029e6394b40a758e52d023e6394b40c798e52d021e6394b40c758e52d023d6194b40ae58052d023e65ccb408f59732d023e658cb408f59632d023f654cb408f19532d023f650cb40e34c832d02b960d47408f18d51d023c6254740ae58051d023f65cc7408f99631d023d658c7408fd9531d023c654c7408f99431d023d650c740ab98831d02ad620c740ae98031d02b9600c7408fd9721d023e65887408f59621d023f65487408f19521d023e65087408f59421d029e6308740a758c21d02ba6008740ae58021d031e5390e40ab98a439029e6390a40cb94a429033551506408f997435031c5390d40ab98a43502ad6290d408f997425029e6390940a758e425032c5290940cdd45415023e6510540ab98a53502ad6294d40ae58253502bb6054d408f988535023d6114d40a798e525029d6394940ae58252502bb60549408f98c525023d61149408f997325023d65cc940c714f325023e658c9408f596325032c528c9408fd95325023c654c940c714d325032c524c9408f194325038d320c940ae98032502b9600c9408f98f515023e62d4540ae582515029f6354540a718d51502af6254540ab18951502bb60545408f197315023e658c5408f596315031c538c5408fd95315023c654c5408f994315023d650c540c714c31502ae620c540ab58831502ba600c540ae580315023c65c85408f996215023d6588540cb14a215023f65485408f195215023e65085408f594215029e6308540a758c215032c5208540ae98021502b960085408f59643102ae6290c40c794c431023d6590840a798e421032e5210840cd547411023f65504408fd95401027b6550040ce951401026e62d53309b58b54cc2ae62d5330c798f54cc23e62d5330cb98b54cc22e62d5330cb58b54cc23d61d5330ce58354cc31e63153308f98854cc23d6115330ce58054cc2ae6290f30ae58243cc2b96010f308f99252cc23d6494b308fd9152cc23c6454b308f99642cc29e6390b308f99442cc29e6310b30cb94842cc32d5210b30c715332cc31c544cb30e310932cc23e64947308f59251cc23f64547308f19151cc23e65d07308f19541cc29e63d0330a718d40cc23e62952308f586548c23c62552308fd85548c2ae6290e308fd91528c23c6454a308fd96428c23d6590a30a798e428c23f6510a308f594428c2b96010a308f992518c23d64946308fd97418c23d65d06308fd95418c23d6550630a718d418c23e62d51308f587544c23e64951308f994544c23e63151308f18c544c23e62151308f584544c23e6590d30ab98a434c23e6510d308f993524c23d64d49308f996424c23c6590930a798e424c23e65109308f194424c29e6310930ae580424c31c54cc930c7151324c34c
  | 4 => 0xc8c5500c7593154031dc4c5500c65e63d53219758f54c869e63d53218f98f54c871e63d53218798f54c871d63d5321cb98b54c873561d53218f58354c863e6315321cb98854c873561153218f58054c863e64d4f218f59353c863e6494f218f59253c863f6454f218f19153c863e6590f218f19643c86ae6290f218f99443c863c6510f21c794c43c871d5310f21ab98843c869e6390b21ad58642c86b56110b21cb15232c872c544cb21d314d32c878c434cb21ab98b41c86ac62507218f99250c863d64943218fd9150c863c64543218f98e548863d60952218f18d548863f60552218f993538863d64d4e218fd91538863c6454e218f990538863d6414e219e98053886796014e218fd96438863d6590e21ab98a438863f6510e218f59443886b56110e21a798e428863e64942218f592508863e63d51218f583544863e64951218f994544863e63151218f580544863e64d4d218f593534863e6494d218f592534863f6454d218f191534867b6054d219e181534863e6590d218f19643486ae6290d218f994434863c6510d21ab98843486b56110d218f996424869e63909218f994424872c548c9219b195324872c544c921d314d324878c434c921b9185324863e65d0521ab98b414863c6550521ab189414863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f98e540863d60950218f18d540863f60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7d92530871c6494c218fd91530863c6454c21c7951530871d5454c21c7d91530871c6454c218f990530863d6414c219798c530866e6214c219e98053086796014c218fd96430863d6590c21c794e430871d5390c21ab98a430863f6510c218f594430871e5310c21c754c430863f65908218f596420869e6390821c794e420871d5390821ad586420863f65108218f594420871e5310821c754c42086b561108218f992510863d64944218f597410871e53d0421c754f410863f6550421c794d410871d5350421d354f210866f6548421d354d21087a541484219dd9521087a642484218f992500863d6494021ce95250087395494021d694e50087595394021ce99250087396494021ce90e50087384394021ce90a50087384294021ced0650087394194021ce95150087395454021d694d50087595354021ce99150087396454021ce90d50087384354021ce90950087384254021ced0550087394154021dac8550087722154021da485500877121540219b98a53d026d6294f40ab98a43d02ad6290f40c794c43d025e6394b409758e52d029e6390b40a758e42d032e5210b40cd54741d02b960d4f40ab98a53d02ad6294
  | 5 => 0x435071c5390d41ab98a43506ad6290d418f997425069e6390941a758e425072c5290941ab98a53506ad6294d41ad58653506b76154d418f988535063d6014d41a798e525069d6394941ad58652506b761549418f98c525063d60149418f997325063d65cc941c714f325063e658c9418f596325072c528c9418fd95325063c654c941c714d325072c524c9418f194325078d320c941ad98432506b5610c9418f98f505063e62d4141a7d8d505069c6354141abd8950506ac62541418f59643106ae6290c41c794c431063d6590841a798e421072e52108418fd9541106776550441cd951411066e62d53319b58b54cc6ae62d5331c798f54cc63e62d5331cb98b54cc62e62d5331cb58b54cc73561d53318f58354cc71e63153318f98854cc73561153318f58054cc6ae6290f31ad58643cc6b56110f318f99252cc63d6494b318fd9152cc63c6454b318f99642cc69e6390b318f99442cc69e6310b31cb94842cc72d5210b31c715332cc71c544cb31e310932cc69e63d0731a718d41cc63e64943318f59250cc63f64543318f19150cc63e62952318f582548c63c62552318fd81548c6ae6290e318fd91528c63c6454a318fd96428c63d6590a31a798e428c63f6510a318f594428c6b56110a318f992508c63d64942318f98b544c63d60d51318f992544c63e65151318f988544c63d60151318f996434c6ae6290d318f994434c63e64d49318f593524c63e65909318f196424c69e63909318f994424c63c6510931a798c424c6b56110931c7153324c71c544c931d3149324c78c424c931b5185324c63e65d0531a798f414c63c6550531a718d414c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f98a540c63d60950318f189540c63f60550318f990540c66e62150319b588540c67a60150319e580540c63f6590c318f596430c6ae6290c31ad586430c63f6510c318f594430c6b56110c31cb952520c72d5494831cbd92520c72c6494831cb90e520c72c43948318fd91520c63c6454831cb951520c72d5454831cbd91520c72c6454831cb90d520c72c43548318fd96420c63d6590831a798e420c72e5290831cb54a420c63f65108318f594420c72e5210831cb548420c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc43197d95310c74d524c431e5505310c677654c431e590d310c63e64940318f592500c73a5494031ce552500c76a5294031da54a500c73a6494031ce592500c73a4394031ce10e500c73a4294031ce10a500c73b4194031ce506500c73a5454031ce551500c76a5254031da549500c73a6454031ce591500c73a4354031ce10d500c73a4254031ce109500c73b4154031ce505500c75b3154031d
  | 6 => 0xa9e6314442a758c5110aba6014442ae5805110a3c63540428fd855010a9e6314042a758c5010ab66114042ad5845010a3d61953328f58254ccb1c63553328fd8554cca3f6055332c755343ccaae6290f32ab98843ccb1e6510f32c759443cca9e6210f32e398843ccb8d6210f32a758443cca9d6010f32a798e42cca3e64947328f59251cca3e64943328f59250cca3d61952328f582548cb2c62552328fd85548ca3f6055232cb553428ca9e6390a32a798c428cb2e6510a32ab594428cb2d6510a32ab98c428cb8e6310a32e358c428caad6110a32ab580428cb1e54cca32ab993328ca3e64946328f592518ca3e64942328f592508cb1d63d5132cb58b544ca3d61d51328f583544ca3e64951328f994544ca3d61151328f580544ca5e65d0d32b398b434ca3e6590d32a798e434caae6290d328f994434cb1f5410d32a7994434cb1e6510d32e3d88434ca9e6210d32e3188434ca9d6110d32a7580434ca6e65d0932b398f424cb8c43d09328f996424ca9e6390932ab98a424ca3e6510932cbd50424cb8f4310932e310c424caae6510932cb994424cb8f6310932ab98c424cb8c6310932ab584424caad6010932ab993324cb8c43cc932a7992324cb8c428c9328f990514ca3d64145329e980514ca7960145328f990504ca3d64141329d984504ca7561141329798f540ca6e62d50328f98f540cb1e63d50328798f540ca3e62d5032cb98b540ca2e62d50328f587540ca3d60d50329d984540ca7561150329e980540ca796015032ad584540cab960150328f98c540cb1e63150328f988540cb2e6215032cd984540ca3d6115032cd584540ca356115032ce980540ca3d6015032ce580540ca3960150328f992530ca3d6494c32ab98a430cb1e5310c32ab988430ca3e64948328f592520ca9e63908328f994420ca3c6510832a798c420cb2e5210832c7153320cb2c548c832b358e320ca5f654c832c7151320cb8e424c832e3109320ca6f654c832cb151320cb8e434c832e310d320cacf654c832d3d95320cb8f644c832e3191320cb8f544c832d3951320cb4c544c832e3151320cb0c544c8328f992510ca3d64944328fd91510ca3c6454432d34c9510ca3e64940328f592500ca3f64540328f191500cb4d32540329b98a53d066d6294f41ab98a43d06ad6290f41c794c43d065e6394b419758e52d069e6390b41a758e42d072e5210b41ad58753d06ae6294f41ab58a53d063e6294f41cb98a53d062e6294f41cb58a53d063d6094f41ad58453d06b561d4b41a798e52d069d6394b418f98e52d071e6394b418798e52d071d6394b418f58252d06b56114b418f99732d063d65ccb418f99632d063d658cb418fd9532d063c654cb418fd9432d078d320cb418f18d50d063c6254341c794e43906ae6290e41a798e429072e5290a418f997
  | 7 => 0x2807c06c00800c00000400002000000800003013009800004c00000004413800c00000000401000000005000000000c02000c00400c00c00002400c00000401801802800001000400002c00800801400000804c00802000002400400c00000000401001405801000800002000800c00404801001800000c01800000000003402803400802800401000000400000c00804801000000000000405801400c03000401400c02400800003401400400000001806801400000402400001000000801000800004800400003801403c00401402402400001c00800005400400004802400401c00006001c00401001003c02000c0000000000440080180080180080332f6494a43cbd0e5290f4f4354a43cbd4a5290e3d6194a438f5825290f2c6394a43cbd865290f2e6194a43cb5865290f2c6194a43cbd825290f2e6094a43cb5825290f2c6094a43cbd955290eae62d4643ab58b5190f2e52d4643cb54b5190f2e5294643cb9495190f2d52546438f1895190e3f6054643ab9885190ead6214643cb9485190eba6014643ae5805190eae62d4243ab58b5090f2e52d4243cb54b5090f2e5294243cb9495090f2d52542438f1895090e3f6154243ab9885090ead6214243cb9485090eb66114243ad5845090eae6290d43b358a4310e3f6550c4397d954310eae6294c43ab58a5310f1e6394c43cb98a5310f2d6294c43e398a5310e9d6294c43e358a5310e8d6294c438f5865210e3d6094843cb5485210eb66114843ad5845210eba6014843ae5805210e3c62544438fd815110eae6214443ab5885110eba6014443ae5805110e3c62540438fd855010eae6214043ab5885010eb66114043ad5845010eae6290f42c794c43d0b1f6494e42c794f4390b1e5390e42c794d4390b1d5310e42c794f4290b4d53d0a42ab98b5390b1f5394e428f5865390a3d6094e42c798a5390b1c6294e42c7d865390b1e6194e42c75865390b1c6194e42c7d825390b1e6094e42c75825390b1c6094e42c7d955390aae6214e42a798f5190a9d63d4642c794f5190b1d53d4642c794e5190b1e5354642c754d5190a3c63546428fd815190a9e6314642a758c5190b1e5314642ae9805190ab96014642a798f5090a9d63d4242c794f5090b1d53d4242c794e5090b1e5354242c754d5090a3c63542428fd855090a9e6314242a758c5090b1e5314242ad9845090ab56114242c714e4350aae6290d428f9944350a9e6390942ab58a4310a3f6550c42c794c4310b1d5310c42ab5884310acd63908428fd954210a6f6550842ab98b5310b2e6294c428f5865310a3d6094c42c754c5310aae6214c42ad9845310ab56114c42ae9805310ab96014c42a798e5210a9d6394842c798e5210b1d6394842cb98a5210b8e6394842ab58e5210b8d6394842a358e5210a3c63544428fd815110
  | 8 => 0x1498539260000000938000cf00002082f04a299a2203098c9978a48000002f31d0a9b8aca3680016f0ba99980000000f08ab3024d8002ccaa8aa780021c80000007c9371308e0805213ae59108079560b28001d603508e80017f29312a8002a5247272af5abf1783148642fdaa48a1946aa5967a1db09a768a70000000a680000000009307b8b220c1fd88686512f23a0000df1c99918003028000981fd06e1d815480000001da430003390f7800301aa728baf726d2e7a6f1b99d3036a7d83da6c94a30888b1539400110202c2b20229aac03b98c0301fb97608f8f33292902ca9bb1ff8efb1a0f8a682829881eb1728a88318d301524622e1e217e1e2b051392418712149e5b401c20e207d80721f9d6a808699be0c0a22b3d2f514c9ea3041858dd8621208002e180000000d0af18225e1588a39590e694130cac1b1d1a900000000009f0a303a2b880022f26480005fa0d3308c732700032d96a16821ea7320680001b1078002f113f8000628002cd1e18400809f200000010a322a23a8f0000000001bab0e216b160f92180cc0003192aea7e0002ff21300000c09d31d8daafb9c712400a8612962022bb1641748cd9940f1182b19a0e000002000400000800400400802000000000800c01800000400800002c02806000000002c00c00000c0200240040000000080480000140340000100200280940a004c0240040080a800000c00000000004800c03400400c00400c02000001400002000000002000403800002000000401804c00001000001403000400000400000000400800801000400401c00000404802801803800000005000400402804808c04000800c0140040000940180b000001c00804401001402401c00802c00001000002000400007800003400002401000804401000807401800008c02400801001c00401801400000402800400000000400000000801001403407000401c00805000005c00c00001c00400001800800003401c01803001001401805800c01801000c00002001002802000012800400001000c00004800003000801404000000400800000c02002002400804c01800c00401801000000400004c00000000800c03002400801401c01404400400005000801800010c0200500040100140d000402405800404c00801c01c00000000001000400400000000c04800403800c00001000008c00004c0080240000040000dc00401c00c00400800401000800800004001c00000000000401800003400003800001000001c00800400000004402c01c00400c00c00c00402000400801001800403c02800000000003403800c02801000000c03803000c00400c00004001400001801800002801400400000801003400002800001400402804801401000807c01000800c04400001000000c00800c020034018024008088
  | 9 => 0x888000000000002ab128101077a5d3352d49608002c800000000000e0000c42c688caa82aaa1d175ab30cd1b51428001e40e802b094b1a8f280011c9290000ce11a3238f0a86ac9806800136b2e96d8000de014ac400000004f1e49a09a69d4b4123902f99d07e98d9bc0cfb1c262a3fa3a8329871bf1ae13128d9b80001a795b2650428fda40a4c0001f320092213d95286300612ca3509da3130bb3e8002f62441d9a2a1fc800313a9e8ffb318ff0001418000000ad0270670000f98001c01fe00000033da3d83e8000528000d10242d703781aa492eba941669f19d59f60b391512b000266253239b1c8000002d9a2d1d794927c1a10cb800096a0eaa600021e1f68e00002d5326000063981a040000000958480002970003388e58120ee0aa2d02f29072339789af22300012a0000000000001dd00013e00025480000000022ea4a81d30f2052b2ac614e1692702749b599928e0000000002200002620c286f87e3280002dfb130d91798d1800212ae9a4b0ed0000000000000000000002060000000000000002ce8000002a997204e84128123c8000f00002642830d7ae0829b3386e8002b095700019e2cc06d2bc1471cf1ce0119df8dfa7c8db80000000008000031519b14805091125eab4a8a80000001e0be8001c4a78124a3d04c8001a18a529b00000015c9ec0872848b890200000005d998248ad42240000002a095d8001e68002fe80000000000033498085e99a9a425380029fa50a2fb370000002a00000359f48e98a28000bc17c88f11816aa081bd94226082800ea15b11989a341e90001af945227b141632e529d8000000000fa2262018ec9fc10e8002328488000001332ed90627b87531f9121ca0d9b433429a398a99c1518239d40708d2ab7adb02183a96d195906874866a438c1ab519483818a25c339b3f02308db0307c32faba8598bd8fd1a70000000000000992d88001e113532f03b0940dc21a123ae60008fc9730000002668d20002250a415a0ea8002db8d60001c290280000012511912e1839c53181db0000000000002da80015114ea820ad9d5307a2c0000a6148b1b9b1a81ae299528a269a1c0842e49f0b02000209ae92671de2de99e91d800255800000068ab019027faf03072d5b1f1f01438469a5a6c05f13b90f8003219cb8002b607720b83713b1fa16f819285887998a428001da18318797798129582d80000000000d8002c7b2c00025c91b0c7a5b18880b8fa8592632e013d135a9798413c0962580cb164804078b0107b2b919c94f90504f96212bb0a1f99479cd2ef0430000b500025b91c128afb0000001c186c14a8dea468e922900011d2d62028dd00000016c0d6b179908002ec00028432baea0000000438001d20000001a494d00000002298e00000000015f0258000000000000000e180000
  | 10 => 0x76267a1b07a840a45b4098b00005799f2be2949e7b3c8450f389700030d0001ba00010b83480030610a8f611fabd83d3210002281e50000000000000000b125200006a8001e7054afc800000120000000058ab72d82a3a0aafa07694da838e70001b700015c00017a80000000024f0269bfa90931a7b0000000fb8000000000000558a08d48eb9211178b4a0a0791cea14072abea11800000170aee0000b30000001ab0000000000000000000000000e280000000012d2120a208c22a8001b11cc19d80930a8000909b49459e800015784980fa7390c16b8252992950000000002510000f4a30a21ae428d00000000000003c80033c04600000018d0001dc1dd9fe8000000571b691eaea9409868158000a78001faa1980000019a331000228b3b00000027a1fb00000000000005c0001300002d0a370a900005e2ff9d905aa2d83f06c9b794b30826f9c080000000000024bb320000b70000001b60000d724e1610002b829889e31e8001038001f40b18470001f7a208000001c81eb8001b200000000020d8001c900000018e89f81b97929a872138889a05aa180000033800000024119faf404209a3122688e100000026e0000002ec8000738000000000001c41ec800000045a9e1e00a58a10000f227996981300588810dae702488213f04e2d195b992b00251ae31650690000210d50000000002713220001ad80016880007f23184a84c10329f28eb0d8893049852981c32560702ad88b92d80000000009a80000020c9e62110188012a92088002d2934ac58002e228000018fb3b9a51bc8aaaa682cb3327d0a8000000000320aba0b58000001540002919ef8ab9ee80000019105b11a8b68e880023000016725710c8002dd1131b38ccac1235a2692700a2ce04410e0001168003102d6864a382a30858399bb86630e8170e386a0bb9c62cf1a889e8902a217d8140ea000265b2a2f480001f0002de2c919380017714b8c9afa94602880021532305501c986328a8b2fd0000001970002349df0001380083368290fe29105007611705200029d1960000000000338000678eb32b0d40000000002cf80000029c09b2d90000e300018900025aa16303afe1531440e792315590183115502e30b0a00fe9be87a27511ba482b20b81ad002af7a5688504b0e628cb421daa100c51ed2692b58b7adf2c310425f9ff2740331279f81a980015e2922e88fb13e82a1f124d2450001eda6e91604782b8001cf8000001e99e88af8da0608000d00a98002778000000799a28000000000001c10002c21718ae8532b3a3b32d05d0000198ba14f00006da853268002bf88d17a0862070c20b080000028897d0ca1628002d78000c680010000013380000012980028700034180017e95005c89c91393780031680021880024211f0d39058000000000000ceaf8000
  | 11 => 0x6b82781296cb091ccb37ab9a89000000318a6a95f9768001229f50001dc80000026a18f20f10913a0002d38000581ef2e399b9d380caac8f59751c5a25800000121800100b3fa8c0000fc0000001d180023e0001f9258a4a2bb8c00001129430000b6305abcb3a23f15d1f28c804184d1600682d303fa0b1d8aeeaf916e259aab9e0aeb20022104491e1d03361f59ca9bd2efa722b18162aa2602758f18bb0c89db8c62638169a0009b1e0d08321b40b400016600028fadc0000d80101f88003248000002d100000000027891995e8bf1ab838abd00000027a81e8182c3b2e2541b01ac0000002108000000002ca0832a2a9380009102d31717fa2b8951700caac00c4adca70a4481c00b11417c2ed27e9c390988113289c00022b1f39b0a4e89b9aeacd8920c31c6ab6974315910056a9a06587195a8918000002af2cbab11a2075afc00001a23c00000200010d00005ba61a7928610880385a0ef165a048ab0088000000139968601c780000000013aa7f23322716e82623b95980004d80023200019225a0002e68b900008180026b03e2ae0003128000dc80000000000022c97b0000000c90d8ae114483c00000013608e310a1aae800000006f0e41848000000c38f408a111a9c9ee00000000000000180013c9f700002200000000025db1130c1738000001580f70001b8800084af233298b8002c500006b0001521268002578000e50030989aca6b8001e385124980010b056004882ac48db0002d23358bd099a4c950aafaf8a3784b8bf9ea8ac1b295699317b8ec139a0924f97101fa5000012e9188618d58001d1000000238a401341148be33aaf68002170e4b00b342f19322031a82c8925b278492079aa097b240c5a5f0000000001638342881c890f1de94c2a10000000eda361a60f80732528ae161a92adda03a3eb2a8000000b00b980007f81792c0bca17b298362f98838f52cb2ad296a4792f80002c000261000092a55051b3e2718000eea6d80020f8001b31e30000741a300020100016b0c11081cd8391d73068f6b2587d02ab250002f3b2ca8980000011580000021f30fac72c0ab402eaa42da2878001801cb00027721921b9b92590000000541048000000782f0800000010b1b2249d29aaa
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xa0525711482150314292c010a818398d62d5330a1ae5318a99861a6358054cc217394cba0e610b1c9655063086ae2328849850c75109324c2c4b808499261345c4604c93085aeb314861850e73d92520c28739ec8a90610b9da4354830a52e021aa4184997098e420c30731aa521061499ca4394430a2ce7214a21851473591510c29339486a88614c5c24354430a62e021aa21851673909510c24cb80c6a08618318d5250430c28c6a8a821870952501300c388a8a8098061629ca434c030e2486a8a601860d6398b54c8286b9cc42a6418a989601532086ae2328879050c7510d32c820f39ccba0e41071cd655062083ce7310a89042e72196434821ab88ca21a410e1d56010d20a18ea21a64905897010d3248270b88c0992410b9ca6395020a1ce5b24a61050e72d915308216bacc5218418354e6290c20952e1314861041e73d96420820ebacc72104107dda539082083eeca9c84106195358042082933948728841459ce4294420a48e4b22a2105267290d510828b39c84a88414c5c24254420a62e0212a21060d531894108254b80c4a0841891895150420e12a6a0240107215150120082c539c8490041c8909514802085ce531ca98841e7398a54c4217396cb21e21079cf6590b1085ce531ca90841e7398a5484217396cb21c21079cf6590a1085ce531ca88841e7398a544430631ec4aa22183d8c6255110c18c6312a88842c725935344217396cb21a210b1c96510d10a1ae4298868861453584434430c29ac021a21071cd64d491083ce7b2c848841c735944244286b98a421221891496110910c50a4b0084884e1721813144268b98c090a21071cd6550110858e4b2a80884e1721853044268b98c2902210b9ca639501083ce7314a80850e72d925304217396c8a9821439cb6454c1085ce5b2c860842d7598a430430729cc5218218354e6290c10a1ce7b24a40842e7690e520420f39ec8a9021439cf645481085ced21aa40841e73d96420420ebacc72102107dda539081083eeca9c840860e6394a420430731aa521021c454f4044010e42a5a022008711535011004390a928088021c454f4144010e42a5a0a2008711535051004390a9282880214c5d66444010a66eab2220085907359110042d0392c888021585cb5344010aa2eb29a20087125454d1004388aa2a688021c4dd15344010e20e8a9a20087126454d1004388b22a6880214c5d64344010e22a721a20085a27290d1004298ba88688021c454c4344010aa2e7a9220085617594910043a0a9ca488021c89515244010e42a8a9220087425354910043a0a9aa488021c8dd15244010e40e8a922008722645491004390b22a488021c890d5244010e4086a9220085317590910042c939c8488021c454e4244010e42a52122008531751091004388a988488021c85484244010
  | 1 => 0x5290e93388c129487495c46094a43c52c0304a521c2d769485190f15294c028c878a949601464385aed290a121e26529845090f13292c228487895496114843c52a4b00a421c39701895110e1ab88c4a8087459c46294e42a2ae2314a72151a7018a5390a8cb80c529c85439c86194e42c2ac230ca72151a701865390a8cb80c329c85439c86094e42a2ce2304a721515711825390b0cb00c129c85075da5314642c34a7300a32161a535805190a0ebb4a6284858594e6114242c2ca6b08a121615535845310b0ca9ac0298850e5c0635444286ae231aa02150e75188434cac2b88c421a65625c06210d32918e4b08869948c72580434cb0732887a1265439d76310932a1cea31884995857118c424cac4b80c621265231cd6110932918e6b00849961663584540cb13312c22a0658c5866015032c34c6b00a81962a62580540cb1930ac02a0658c5856015032a2ae22a6641951970153320ca92b88a9190654a5c0548c83283cec2a2641951571151320ca8cb80a8990650b9d8544c832a4ae22a2641952970151320ca873a6ca99065239db544c832a1ce92a2641954571151320caa4b80a899065239d8544c832b0ae22a2641958970151320ca873b0a899065839d8544c832e0ce22a2641950d71151320cb82b88a899065415c4544c832e14e02a2641950d70151320cb84b80a899065425c0544c832c18c8992a21960c644c9500ca86b94a621e83435ce5210b41c18a6b1486a0e0d6314a425061cb80ca1928383195320c941d0a64b0864a0c2e7298f505060f39cc5a82838398d62d5331a1ae5318a998e166358454cc61cb80ca21263431d4424c931b0ae22126498cd170185324c616bacc521863439cf6494831a1ce7b22a418c2e7690d520c692b8886a9063255c66390831c1cc6a948418f0552505310c6c339486988634a9ca4394031a34e7214a018d1873591500c69539486a80634c5c64354031a62e221aa018d1a73909500c788a0a62a8063c490d3154031c1ac7316a990d0d7398854c8713312c22a6430e5c06510f21a18ea21a6590c3970194434861a3aac221a43431d4434c921b0ae221a6490ce1701853248617394c72a043439cb6494c21a1ce5b22a610c2d7598a4308706a9cc521843295c66290c2183ce7b2c8410c1d7598e420860fbb4a72104307dd95390821c2aa6b088410f055350521086c339c84908434a9ca4394021a34e7214a010d2872591500869539486a8043469ce4254021a62e3212a010d31711095008790a0a42a8043c89092154021a1ae529887a050d7394842d0217396cb98e81079cf65c8740c18a6b1486a060d6314a425021ab88ca1928183195320c940d1264b0064a042e7298f515020f39cc5a8a810b1c9658c540a2ae229862a060c53588315030c29ac018a81071cd6588540c1ac629042
  | 2 => 0x11e0003b020000002400000000b6328cc28400358e32814f2c50600087244f52611c000e8340d9504000005e550d30a09d4f05637929464c03508e008f214cea4342025c8c444864f82d0f44d4dd04148a91c40c2fcd23554428c00001361000e2cc61194001294a270a55480052c9e4680000127078b20f08b10c152a10e48d07160dd538cf4e4ce06801139481a8cd40c2e0644523cc81d8ac000004d40b545423681f09cec0992c074551d0000012a39556000000002211d121205a00000384001a41b174000007b540005002c2f4a6414752d47019c6d408730e4100011d188ab20cb90d5331e8fa130bc1090f1b000000001b8823ec8039ca20242518c0018134250f70580a3f4130480f050b71e4933d8b0190f1000001f0000c92d0c13d380052e8593607810468514440bc000ac2a199082900054cfc4e89a29cdb1dd4d15d18530df2653000116145210005f034003440413c3e424f3000f01409b00000124fe42c96241140d92046c000012631d380008a4b800308072b86f44cc40d0c52bc3f4bd011f8293bc0032cf4060c61fc4b1acb8044060c4e23252b3985b27d0a4c41700155000b445c00000ed225100013f40003150f9488723053b35d473903843023525280e8bb490922a80000132000002107d000e900088118be070ad30c332152523543000ee00021204eb47cf8255151700000146000003fc000dc0037000018740c140400000080700c18030202802000182c0201068202e00118206e03010142202040148402008001203040000013000000e00038280e02098a802070489c08020604c00020287c1e0f000000603000100e020684c0216078001401070040006000081a00008441c0a000241409008200437030000a000001c0800005267118e5290e92b88c7294874a9c06394a43a52e031ca521d0e731865290f12b08c3294874a9c06194a43a52e030ca521d0e73182
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x240240112731181014001539002e1c381b05070e031d00262f3b1e23322a3625000001332d1f0f3f281a3e343a00350a30170829210b12001304202c000037000c00063d22002b000000090d3c19160006355010218a050604180001c6803204000c21615c06194a43c21715806094a43c11615c06194e42c11715806094e42889801c96110d32885811c96010d32889801cd6110932885811cd6010932d01719c0544c832d02715c0544c832d01715c0544c832a0980195320c941a058298d6115331909801d4424c931a058198d5290831905859ca434c431911819ce4254031b028290d3154031a05839896115321909801d4434cb21909801d4434c921904855c4434c921c05535c66290c21905859ce4248421921819ca4354021b02839092154021a0581195320c940a058114d620c540a118114d600c540c05635c45208540a21811496008540a098298d6015330905811d4424c930a098098d5290830911809ce4254430a098018d5250430a118018d5150430909859ca434c030b028290d514c030a09839896015320905811d4434cb20905811d4434c920908855c0434c920c09535c26290c20921809ca4354420c09535c06250420a21801895150420909859ce4248020b02839095148020a058214d6110d10a098214d6010d10a05831496110910a09831496010910b0282dd15344010910875915344010b00825915344010921859ca4344010d01539ca4344010b0283dd15244010920875915244010b008359152440109228790d5244010911859ce42440109138754e4244010d027354a4244010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1044
  | 4 => 1671
  | 3 => 343
  | 2 => 65
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
  | 6 => packedAt s4K6 (864+((h/16+packedAt s4K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s4K5 (32016+((h/348+packedAt s4K5 (28188+(h % 348)*11) 11) % 1515)*12) 12
  | 4 => packedAt s4K4 (70182+((h/557+packedAt s4K4 (63498+(h % 557)*12) 12) % 2206)*12) 12
  | 3 => packedAt s4K3 (17833+((h/114+packedAt s4K3 (16807+(h % 114)*9) 9) % 412)*10) 10
  | 2 => packedAt s4K2 (4047+((h/21+packedAt s4K2 (3900+(h % 21)*7) 7) % 79)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe1fe1ffc3fe3fc7e1e38fc7f1f87f0fe0cf4cf
  | 1 => 0xfe1fe1ffc3fc7f8fe03f1f8fe3f87f0e333b33
  | 2 => 0x1ffe3ffc007ff1ffc01ff1fc007ff1c3cc3c
  | 3 => 0xffe0003fffff8001ffffe001ffff8001fc0fc0
  | 5 => 0xffffffc000000001fffffffe00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x28028004088410800408241204821044045045
  | 1 => 0x408408088100a0104011088421202408112112
  | 2 => 0x1548449110494802aa40112148114aa0c28c28
  | 3 => 0x844155222240092532a2400192550221680e80
  | 5 => 0x19919983bb927249dd3c9e4800660ccdbff000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee8fee8eee8eee8fee8fee8eee8eee8fee8fee8eee8eee8fee8fee8eee8eee8fee8fee8eee8eee8fee8fee8eee8eee8fee8fee8eee8eee8fee8fee8eee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37181
namespace PEqualNP.Outside.L_meta_37181
open PEqualNP.Outside.L_meta_37181.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x2a28600003e8c4803800b8600450295604f0e4e74d1904b510c4a00016003d7a150b05800a1c5084840dae260090d0610aa60018410c0157c300004000800bff43fe43be43fd43fc43bc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x261bc544c278a8986f90d30de21a617f524c2f8a4986f90930de21261df324c3ba64985fd4530be28a61bf414c37a829877cc530ee98a61bf404c37a80987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c37c86186f10c30bf29061ee520c2dca4185f54830f6a90616d520c37c84186f10830bf28861f6510c2eca2185f54430faa886175510c37e82186f50430bf28061bf400c37a801877cc030fd18061dd300c3f260185fd5320dfaa6413f54c82fca9905f55320be2a641bc54c8278a9905fd4f20bf29e417d53c82f8a7906f90f20de21e41be42c837885907b8cb20f6996417e51c82faa3906fd0720dea0e41ef21c83da43906fd0320dea06417f54882fca9106f952209f2a4417d548837aa9104f55220be2a4417f53882fca7105f54e20be29c41be438837887105f54a20df21441bc42882fca3105f54620dfa0c41bd41882fca1106fd0220dea0441ef20883f641105fd5120dfaa2413f54482fca8905f55120be2a241bc5448278a8905fd4d20bf29a417d53482f8a6906f90d20de21a41be424837884907b8c920f6992417f51482f8a2906fd0520dea0a41ef21483da42906fd0120dea0241fb20483dc40905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf29841de53082bca6105f54c20eea98415d53082f8a6106f90c20de218417e520837c84106f10820bf28841f651082eca2105f54420faa884175510837e82106f50420bf28041bf400837a80107bc8020fd10041ed20083f240105fd5310bf2a621be54c427ca9885f55310deaa6213d54c42f8a9885fd4f10bf29e217d53c42f8a7886f90f10de21e217f52c42fca5885f54b10be29621be42c437885886fd0710dea0e21f631c43ea63887d88710fa90e21bf40c437a81885fd5210bf2a421be548427ca9085f55210deaa4213d54842f8a9085fd4e10bf29c217d53842f8a7086f90e10de21c217f52842fca5085f54a10be29421be428437885085f54610dfa0c21bd41842fca1086fd0210dea0421fa30843f261087e88210fc90421f710843f621085fd5110bf2a221be544427ca8885f55110deaa2213d54442f8a8885fd4d10bf29a217d53442f8a6886f90d10de21a217f52442fca4885f54910be29221be424437884886fd0510dea0a21f631443ea62887d88510fa90a21bf404437a80887e8c110fc98221fa20443f240887ec4110fb082217f54042fca8086f950109f2a0217d540437aa8084f55010be2a0217f53042fca6087794c10af298217d53043baa6085754c10be29821be430437886085fd4810bf29021ee52042dca4085f54810f6a90216d52042f8a4086f90810de210217e510437e82086f50410bf28021bf400437a80087dc4010fd08021f510043f220087c44010
  | 1 => 0xd520c77c8418ef10831bf28863bf410c77a8218f7cc431fb18863dd310c7ea6218df94031fd280637a500c6faa018fe54031bca80637f54c877ea990cfd5321bf2a6437d54c86f8a990ef153219e2a6437f53c86fca790df54f21be29e43be43c87788790ef90b21de21643ee32c87da6590efd0721dea0e437e50c86faa190dfd5221bf2a443be548867ca910df55221deaa4433d54886f8a910dfd4e21bf29c437d53886f8a710ef90e21de21c437d528877c8510ef10a21bf28c43bf418877a8310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21bf29a437d53486f8a690ef90d21de21a43be42487788490fb8c921f699243bf414877a8290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610ef90c21de218437e520877c8410ef10821bf28843bf410877a8210fbc8421fb10843ed21087ea4210df94021fd280437a50086faa010fe54021bca80437e53d02faa7a06fd0f40df21e81bd43d037887a05f94b40bea9681bf42d037c85a06f50b40de216817e51d02faa3a06fd0740df20e81bd41d037883a06fd4f40df29e813e53d037aa7a06f14f40dfa9681be52d027ca5a06f54b40de29681bf32d037c65a06f4cb40de19681bf51d037ca3a06f547409ea8e81bc51d037e63a06f8c740de98e81bc31d037e43a06f88740de90e81bc21d02faa9204f55240bf29c817d539037c87206f10e40bf294817d529037c85206f10a40bf28c817d519037e83206f50640bf28481bf40903f681205fd4d40be29a81bf435037c86a06f50d40de21a817f52502f8a4a06fd0940df21281bd425037884a05fd4540be28a81bf415037c82a06f50540de20a81fb405037c80a06fd4d40df29a81bd5350378a6a04f14d40dfa9281be525037aa4a06f149409e29281bf325037c64a06f4c940de19281bf515027ea2a06f94540dea8a81bc515037e62a06f8c540de98a81bc315037e42a06f88540de90a81bc215037ea0a06ed4140bf2a0813e54102fca6205f54c40df21881bc43102fca4205f54840df21081bc42102fca2205f54440dfa0881bd41102fca0206fd0040fd20081bd40103f280205fd5330dfaa6613f54cc2fca9985f55330be2a661bc54cc278a9986f90f30de21e617e52cc2faa5986f90b30de21661df32cc3ba65985f94730bea8e61bf41cc37a839877cc730ee98e61bf40cc37a81985fd5230bf2a461be548c27ca9185f55230deaa4613d548c2f8a9185f54e30df21c61bc438c2fca5185f54a30df21461bc428c2fca3185f54630dfa0c61bd418c2fca1186fd0230dea0461df308c3f661185fd5130dfaa2613f544c2fca8985f55130be2a
  | 2 => 0xafaa6216fd0c42df21885bd4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042dfa9885be5310a7ca6216f54c42de29885be5210a7ca4216b94842dfa8885be5110b7aa2214f54442de28885bf5010b7ca0216f540429ea8085bc5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccbbe87996f90f32de21e65dc43ccb3887996f90b32de216657e51ccafaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cb7c87196f10e32bf29465ef428cb7c85196f10a32f621465ac428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132efa1a65be434cb7886997710d32ce21a65ef424cb7c84996f10932f621265ac424cbde6499778c932bfa8a657c514cafea0995f14132bfaa065bf540ca7ea8195f95032beaa0657c540cb78a8194f15032bf29865be430cb7886195f94832df21065bc420cbbe64197b8c832ee99065ed320cb9a64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077c87a0ef50f41de21e837e52d06faa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0cf94f41dea9e83bc53d077ea5a0ef94b419f29683bd52d0778a5a0efccb41df19683bd32d077865a0efd4341df28683bd50d067aa1a0ef14341beaa4833d54906fca720df54e41df21c83bc43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077c86a0ef50d41de21a837f52506f8a4a0efd0941df21283bd425077884a0fdd0541df20a837f50506f8a0a0efd4d41df29a83bd5350778a6a0cf14d41dfa9283be525077aa4a0ef149419e29283bf325077c64a0ef4c941de19283bf515076ea2a0efd41419fa8283be505077aa0a0ef14141bf2a0833e54106fca620df54c41df21883bc43106fca420df54841df21083bc42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc77ea998cfd5331bf2a6637d54cc6f8a998ef153319e2a663be43cc7788798df94b31bea9663be42cc7788598f7ccb31ee99663bf41cc77a8398df94331bea86637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c77c8718ef10e31bf294637d528c77c8518ef10a31bf28c63bf418c77a8318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898ef90d31de21a637f524c6f8a498ef90931de21263df324c7ba6498efd0531dea0a63f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77c8618ef10c31bf29063ee520c6dca418df54831f6a90636
  | 3 => 0x29619c00000000000000000000000000000000000000028e0000000000000000000002a00000006ee68000000040423800000900000100400000200500200000000000000100000000000300000200000000100100000300800200000000000400100100000200200000200000200100000200000000800100100100500900100100600300200000000000000100000500000000000200000000000000000500000000300100a00000000100100100100200000800000800300000400800500400100200100000400300100000000600000100000100200000000200100000a00200000000100200000000700200100000c00000100000000300500200100000000200000100000000000000100300400000100700a00200900000000500100100300200000100100100100300000000800000000000000000000000100300100000000500000200b00500300100000700000000000100000300000000100000100600000000000300300900500100400200002600200000800000100100200000500000200000200000700000100000000200000600000100300200100000000700500600000100000000400800100000000000000000000400000200100100200000100000000300000000300000400000000000100000000200000000200300200000200400000000400000100000000100100800500700000a00000a00700000300200100300000100000000001200200100100100000100000100100000500000000100000200100000100100000000000b005002001000002bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521fb94a43b7294877d5290fdaa521db54a43bf28c877d5190efca121df542439f29c87bf5290f7ca521cf94a43d7294872e5290f7aa521eb54a43de29487bf5190f7ca321ef546439ea8c87bc5190f7ea121ef94243dea84873d5090f78a121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021ef94c439f298879e5310f7ea421ef948439f29087bd5210f78a421efd4443df28887bd5110e7aa221ef14443dfa8087be5010f7aa021cf54043de280877e53d0afaa7a16f90f42de21e857e51d0afaa3a15f94342bea86857d5490afca7217794e42af29c857d5390bbaa7215754e42dfa1c85be4390b7a87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1216fd4e42df29c853e5390b3ca7214794e42dea9c859d5390b78a7214f94a42dfa8c85be5190b7aa3214f54642de28c85bf5090b7ca1216f542429ea8485bc5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e531
  | 4 => 0x81be78e49e0006645da0000000005167b00003185fc75429858a3680005224380000006e40160000a800000000050e0003a41d60f408c08e30200000000000007213c6aa78800014a5305560007cc0000000000005541a400050a03a0000007701fe0000000000004d000054a0000000006500000000000006ea0000003aa6466c24480004184a626863a00000074a0000000003a60001a000000000000057829e7ca00000023a0001806300000000000000000000005ee0002f60000000004720000000000140000000fa0000000000000000000000000002560000000000000000000000000008080000004260280004b80003705ec0000000004bc00000000000000000073200000000052c76606a00000000000000000000044c4f40000000000003986a27fe6620006080000004e800069e0000000007bc70844e0006020004e082600079227c0000001660000000000000002f261c00038659e73e4880006206be6fa0005260001720000000002a437a0000000000000000000000000000000000000000000003c21ba16a00048e67e38000000000000030800000034c65a0000004a00000000000000e200000013400000000a6660000005d200000005477a3887620003bc5b00000000007c40001900000000006060000003cc11c63400000000000002a0000000000000000000000000000002a84a814e31e0000000000000004d20001ac00061640000000000011a00058c36c4d463c0000000005a40000003e800058800028c4520000006c400000044a00000000000000000045e4f000032000081c0004e60000000003360005360002922540005ce00053800049477e0000000000000000006847343be76a41215a1de0000000005c02b00004ae81e0000002fc0005a02a20003920006b406440a5820005064be03c00005a3724024300005d000000000000000000056c0003ec1f80006da2c60000000004c80000000001440000000000000007ee2d607681862826e0000000000000000000000004b60000000000000000000001ea0003147460000001cc00059c0007380000000000007740003b200028430a4a271e71c45a3dc0000001561166c631a00000012a0000005b600011800000000072a0000dc0000004ea2025a60000d216469249200000000000065e4640000a635016e0000000000007240006b000000000047a0000000000000000000000000000ee0002aa0000006140000000000006e600079a49633a53400000000000000000000013a7222bc0005c800000000000000000047e00000000030e0000000005980002f400000066c5d60007120000000005ae00000000000051852a0000000d01c40006820000001202de6403ee0007a82906426520000000002d400034e00000000070e2600005f40006fc0e80000000
  | 5 => 0x21e3ca0000000004164e20006f40007f200012800025e5b20000003c600003400004e7f60000003540003d47be00000000063e0000000000002be3ea3e258e1c065c0001bc5cc11000000000000027200006e0004346d80000008160006ba7ea0ae2140c800000000000000000000000e02400000038200044600002c5620000000006ac0000000000000003347a270643200000077c1e40000000000000000000000002f801c4785d41546d60000e64c44b078c3a87603ce56e7564ce09461e2fe10e4fa60a00000056451478a0562dc0000004560000006780008120005d800023c0000000000000000001f07b80463487904f67302b437614c6187726bc00029a2ca2281221960000000005660000006a400000000030666e5400002107c048a0ec3fa75e2c00006360005fa0002ec0000002b600000000047c6d27f40000000000000000004ca00000000045c0000000005520000000aa22600000000051e0000000787c67500007ac23601e0002d20000000000006ec00000000000070a49a00053224c7580ce12c1e236469c6d033e00000000000000034220e28607a1123300000000000000000000000000000004cc6b60364800006c847447600000004817a0000007ce7687a40005f60003268101dc12e5be4dc50251a5600003c835e0021706e85121da00000000039600005e00c6ae66800000000026274e0000000000f02a60000980007640005b821a00082400000000019e0006f01940000000000000007f00000000002880000000001ce00000000033200000000043607400045417400000046a7160001e80002f00000000000000003600000000000002cc1360004600000005dc0006440004fe1d21ae00000007003801a3f00000000002e467c6ca00000008a00011e0d62660000000000007aa0000000005a80000000007d47b200054227a04a00000000000022c0000001b20000000001fa00000000000000000067000000037c00000058400080c28a68a09000079605c2642ee14000069a41e09e00059280e00038c3d60044a44c000000000071a0002203da57600046612605800000064e00027033c24e0000000000b67c20c277600000018a1088060000004227c80000000000000000000003d80003940006325a21e60a272c00000008000005200000000000000000000031c0000007840005281c215874879800010c05000000000000000000000073a0b414600000017e0003840d43d00005100003440000007a60083104de00000070400000000000000000000000079e6b20005fe0000000000000000000000000000000000000000005800000006723fe0000000000003b670c3d200000080a0000000000002ea6f804c66034a0000000003fc00032a1b682246e28238e3744840ea7fc17c00032c0000000007a071
  | 6 => 0x27839e2301a600000016266a0000000000002440000bc00059000041c2e87420000000003f20006a662a43e6480007b67de3f42fa4864d60000003580000000000000000000000000420000003460000000007e600068840c68c5ea30019a76c43c13048257c5c20000003627d80000000000007da7ec5860000001c60000000006861d40000000003400000004fc52000065618e0000007e25460000000000006de0000000000004700c60000fc0000000000004620005440007863b053a42035c1020001a20007b432857a00000000055a0004900000000000000000004080000000000000000003780000000845e00000000be0001f20005de37e0000000005e84c62b20000000000007806fe62400000000000000000009a0000000002e02e63b400025001204407c61a4143c40000002420004240004ac65829c13e00000000000041a7dc4980001820000000000000000000005bc0003127361f400000041000026a00000000032200000032400000000020c6f203000000000039a5e400036e0000000000005580002220000000000006a00000000000004ec0260000ba6540000000b82c400028000000000053e00000000012400000000000000000000062c00026c6101841980cc5044d800072e0002043ba2e23ac0001146944da2ac64c0604aa39c5f000000036600015c59606240602e2d842e6b800046c4b40828040b000000044000000060e00057e06800025c7fa7525000001b000076e24a5ac0005c40000000060000003e622e00000021630c0180000320000005245e20102767820002181ee10a80243a0c06747001004f215200000000000000000000000000025a0005f81420003ae00015000010600081a0000000000000000000000d80002240000000002ba0001603e00da50c0202da0002d017608600008800000000036a0006d40000000000000000e03a20000000c40001320000002460000001d80000000003526f62400000000000006a80000003f822a00079c00070200064a0000000000fe5503a06261aa3de68e7268003f649c61254c55e69000000007e00000048c1fc75a4b282042c4ba1047e44c27100007ba6764500665f206c3e40a016859a1f61923c07f85e64ee0000002346e000000000055c0001ec60000000000000000000000009c3b800025200000000000000074c27e2c80006dc7140000000f82741888142580000002ae67a0007945087400006c00004285ca0006ce59400017800000000000069624800009600000000000000000016c00000020a00003e54e09215e5685ba02256a7ae6380b27d04420007780000000000e400042a0000003900001b40de0000000002080000005480006e20000ca23200052e00021c0f60003560001ca3166cc18600000000000000057000000051c000
  | 7 => 0x5c600018c2946047e840e32e62e0000000000002120006221e000023e00020000035a1380000000000000000000000000000ac0000004580a45741c81480f200075c0000000000007e04f87d20404442c20001b80004e47280000000000000000000005b400000000000000000000000000053c2060000000000003387d65aa00074472000057200000060c2b80000000000000003040000006982ce1a800038a00000000000000000000073c0000000000000000000000000000000000000000000004681d00
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x9544422c62551108fd85544433761551108fd81544433b60551108f993534423d64d4d108fd91534423c6454d109bd89534426c6254d108f990534423d6414d109b988534426d6214d108fd96434423d6590d10ab98a43442b56190d10ae582434423f6510d108f594434431f5310d10c714c43442b56110d10ae580434423e64d49108f593524423f64549108f191524425f63549109718d524423e64149108f590524425e63149109758c524423f65909108f596424429e6390910ad58642442b960909108fd94424423d6510910cbd48424432c5210910ad58442442b96010910ae58341442bb60505109d19531442f0604c5109d19521442f06048510ad587404423f65501108f59540442b761501109e19530442f0614c110f44c530442786548110bc18520443e121481109798f540425d63d50109b98b540426d62d50108f596540423e63950108f98a540423c63550108f189540423f61550108f585540423f60550108f581540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431f6494c10c7192530423f6454c108f191530431e5454c10c7551530431f6454c10c7191530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108fd96430423d6590c10c794e430431d5390c10ab98a430423f6510c108f594430431e5310c10c754c430423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cbd92520432c6494810cb90e520432c43948108fd91520423c6454810cb951520432d5454810d394d520434d5354810cbd91520432c6454810cb90d520432c43548108f990520423d64148109798c520425d63148109b988520427661148109e980520423f65908108f596420429e6390810c794e420431d5390810cb94a420432d52908108fd94420423d6510810c794c420431d5310810cb948420432d52108108f992510423d64944108f597410431e53d0410c754f410432e52d0410cb54b410423f6550410c794d410431d5350410cb949410432d52504108f992500423d64940108f597400431e53d0010c754f400432e52d0010cb54b400423f6550010c794d400431d5350010cb949400432d5250010d554f100436552c40109e59610043595384010da54a10042f161840109dd9510043555344010d954910043b34044010ec501100427b6544010d654d10043695244010ecd0510043b14144010bcd9510043736544010ec99110043b16444010ec95110043b15444010dcd4d10043d25344010dc54d10043d15344010d454d10043b24344010ec10d10043735244010f894910043715244010f854910043615244010ec90910043b04244010
  | 1 => 0x82e8604c9208f990514823d64145209798c514825d63145208f997414823c65d05208f995414823c65505208f99740482ae62d01208f19540482ac62501209798f540825d63d50209d987540827561d50208f596540823e63950208f586540823c63550208fd85540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831f6494c20c7192530823f6454c208f191530831e5454c20c7551530831f6454c20c7191530823e6414c208f590530825e6314c209b98853082766114c209d584530823f6590c208f596430831e5390c20c754e43082ae6290c208fd94430823d6510c20c794c430831d5310c208fd96420823d6590820a798e420831e5390820c754e42082b960908208fd94420823d6510820c794c420831d5310820ae580420823e64944208f59251083365494420cd55251083565394420d554e51083366494420cd59251083364394420cd10e51083364294420cd10a51083365454420cd55151083565354420d554d51083366454420cd59151083364354420cd10d51083364254420cd109510823f65d04208f597410831e53d0420c754f410833651d0420cd547410823f65504208f595410831e5350420c754d41082ac6250420cd945410833551504208f992500823d64940208f597400831e53d0020c754f400833651d0020cd547400823f6550020c794d400831d5350020cd94540083355150020d354f200836551c8020dc546200826f6548020d354d20083655148020ea501200827b6548020ea909200837151480208f98e54c423e62953108f18d54c423c62553108f99353c423d64d4f108fd9153c423c6454f108f99053c423d6414f109b98853c426d6214f108fd9643c423d6590f10ab98a43c42b56190f108fd9443c423d6510f10ad58443c423e64d4b108f59352c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c423f6590b108f59642c429e6390b10ad58642c423f6510b108f59442c42b56110b10ad58740c42b761503108f98e548423e62952108f18d548423c62552108f993538423d64d4e108fd91538423c6454e108f990538423d6414e109b988538426d6214e108fd96438423d6590e10ab98a43842b96090e108fd94438423d6510e10ae580438423e64d4a108f593528423f6454a108f191528423e6414a108f590528425e6314a109758c528423f6590a108f596428429e6390a10ae582428423f6510a108f59442842b96010a10ae58341842bb60506108f98e544423e62951108f586544433561951108f5825444339609511097d8d544425c63551109bd89544426c6255110a718d54442ac6255110c7d8d544423c6355110c718d544421c6355110cbd89544423c6255110cb18
  | 2 => 0x524c930e3109324c2d8604c9308f990514c23d64145309b988514c26d62145308f997414c23c65d05308f995414c23c65505308f997404c29e63d01308f195404c29c63501309b98b540c26d62d50309d987540c27561d50308f596540c23e62950308f586540c23c62550308fd85540c23e64150309b988540c26d62150309d984540c27561150308fd96430c23d6590c30ab98a430c2b96090c308fd94430c23d6510c30ae580430c32e5494830cb552520c32f6494830cb192520c32e4394830cb10e520c23f64548308f191520c32e5454830cb551520c32f6454830cb191520c32e4354830cb10d520c23f65908308f596420c29e6390830cb94a420c32d52908308fd94420c23d6510830cb948420c32d52108308f992510c23d6494430cd952510c3355494430d994a510c3655294430cd992510c3356494430cd90e510c3344394430cd90a510c3344294430cd951510c3355454430d9949510c3655254430cd991510c3356454430cd90d510c3344354430cd909510c33442544308fd97410c23d65d0430cb94b410c32d52d0430cd947410c33551d04308fd95410c23d6550430a718d410c32e5250430cb549410c3365150430cd545410c23e64940308f592500c23d65d0030cb94b400c32d52d0030cd947400c33551d00308fd95400c32e5250030cb549400c3365150030cd545400c34d52cc030d5547300c371518c03097d95300c34d524c030d5545300c399404c0309ed95300c39a434c030dc545300c25e63d53209758f54c829e63d53208f98f54c831e63d53208798f54c831d63d5320cb98b54c823d61d5320ce58354c823e6315320cb98854c823d6115320ce58054c823e64d4f208f59353c823e6494f208f59253c823f6454f208f19153c823e6590f208f19643c82ae6290f208f99443c823c6510f20c794c43c831d5310f20ab98843c829e6390b20ae58242c82b96010b20cb15232c832c544cb20d314d32c838c434cb208f99251c823d64947208fd9151c823c64547208f99741c823c6550720ab98b40c82ac62503208f98e548823d61952208f18d548823f61552208f993538823d64d4e208fd91538823c6454e208f990538823d6414e209d98453882756114e208fd96438823d6590e20ab98a438823f6510e208f59443882b96010e20a798e428823e64946208f592518823f65d06208f597418823f65506208f59541882ac62506208f98f544823d61d51208f992544823e65151208f98c544823e62151208f188544823d61151208f993534823d64d4d208f992534823d6494d208fd91534823c6454d209dd8553482746154d208f996434823c6590d20ab98a434823e6510d208f19443482ae6210d20ae580434823e6590920a798e424823e6510920cb152324826c654c920cb151324834c534c920e310d324
  | 3 => 0xf408f98a53d032e6294f408b98a53d032d6294f408f58653d02b96014f40ae58352d029e6394b40a758e52d023e6394b40c798e52d021e6394b40c758e52d023d6194b40ae58052d023e65ccb408f59732d023e658cb408f59632d023f654cb408f19532d023f650cb40e34c832d02b960d47408f18d51d023c6254740ae58051d023f65cc7408f99631d023d658c7408fd9531d023c654c7408f99431d023d650c740ab98831d02ad620c740ae98031d02b9600c7408fd9721d023e65887408f59621d023f65487408f19521d023e65087408f59421d029e6308740a758c21d02ba6008740ae58021d031e5390e40ab98a439029e6390a40cb94a429033551506408f997435031c5390d40ab98a43502ad6290d408f997425029e6390940a758e425032c5290940cdd45415023e6510540ab98a53502ad6294d40ae58253502bb6054d408f988535023d6114d40a798e525029d6394940ae58252502bb60549408f98c525023d61149408f997325023d65cc940c714f325023e658c9408f596325032c528c9408fd95325023c654c940c714d325032c524c9408f194325038d320c940ae98032502b9600c9408f98f515023e62d4540ae582515029f6354540a718d51502af6254540ab18951502bb60545408f197315023e658c5408f596315031c538c5408fd95315023c654c5408f994315023d650c540c714c31502ae620c540ab58831502ba600c540ae580315023c65c85408f996215023d6588540cb14a215023f65485408f195215023e65085408f594215029e6308540a758c215032c5208540ae98021502b960085408f59643102ae6290c40c794c431023d6590840a798e421032e5210840cd547411023f65504408fd95401027b6550040ce951401026e62d53309b58b54cc2ae62d5330c798f54cc23e62d5330cb98b54cc22e62d5330cb58b54cc23d61d5330ce58354cc31e63153308f98854cc23d6115330ce58054cc2ae6290f30ae58243cc2b96010f308f99252cc23d6494b308fd9152cc23c6454b308f99642cc29e6390b308f99442cc29e6310b30cb94842cc32d5210b30c715332cc31c544cb30e310932cc23e64947308f59251cc23f64547308f19151cc23e65d07308f19541cc29e63d0330a718d40cc23e62952308f586548c23c62552308fd85548c2ae6290e308fd91528c23c6454a308fd96428c23d6590a30a798e428c23f6510a308f594428c2b96010a308f992518c23d64946308fd97418c23d65d06308fd95418c23d6550630a718d418c23e62d51308f587544c23e64951308f994544c23e63151308f18c544c23e62151308f584544c23e6590d30ab98a434c23e6510d308f993524c23d64d49308f996424c23c6590930a798e424c23e65109308f194424c29e6310930ae580424c31c54cc930c7151324c34c
  | 4 => 0xc8c5500c7593154031dc4c5500c65e63d53219758f54c869e63d53218f98f54c871e63d53218798f54c871d63d5321cb98b54c873561d53218f58354c863e6315321cb98854c873561153218f58054c863e64d4f218f59353c863e6494f218f59253c863f6454f218f19153c863e6590f218f19643c86ae6290f218f99443c863c6510f21c794c43c871d5310f21ab98843c869e6390b21ad58642c86b56110b21cb15232c872c544cb21d314d32c878c434cb21ab98b41c86ac62507218f99250c863d64943218fd9150c863c64543218f98e548863d60952218f18d548863f60552218f993538863d64d4e218fd91538863c6454e218f990538863d6414e219e98053886796014e218fd96438863d6590e21ab98a438863f6510e218f59443886b56110e21a798e428863e64942218f592508863e63d51218f583544863e64951218f994544863e63151218f580544863e64d4d218f593534863e6494d218f592534863f6454d218f191534867b6054d219e181534863e6590d218f19643486ae6290d218f994434863c6510d21ab98843486b56110d218f996424869e63909218f994424872c548c9219b195324872c544c921d314d324878c434c921b9185324863e65d0521ab98b414863c6550521ab189414863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f98e540863d60950218f18d540863f60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7d92530871c6494c218fd91530863c6454c21c7951530871d5454c21c7d91530871c6454c218f990530863d6414c219798c530866e6214c219e98053086796014c218fd96430863d6590c21c794e430871d5390c21ab98a430863f6510c218f594430871e5310c21c754c430863f65908218f596420869e6390821c794e420871d5390821ad586420863f65108218f594420871e5310821c754c42086b561108218f992510863d64944218f597410871e53d0421c754f410863f6550421c794d410871d5350421d354f210866f6548421d354d21087a541484219dd9521087a642484218f992500863d6494021ce95250087395494021d694e50087595394021ce99250087396494021ce90e50087384394021ce90a50087384294021ced0650087394194021ce95150087395454021d694d50087595354021ce99150087396454021ce90d50087384354021ce90950087384254021ced0550087394154021dac8550087722154021da485500877121540219b98a53d026d6294f40ab98a43d02ad6290f40c794c43d025e6394b409758e52d029e6390b40a758e42d032e5210b40cd54741d02b960d4f40ab98a53d02ad6294
  | 5 => 0x435071c5390d41ab98a43506ad6290d418f997425069e6390941a758e425072c5290941ab98a53506ad6294d41ad58653506b76154d418f988535063d6014d41a798e525069d6394941ad58652506b761549418f98c525063d60149418f997325063d65cc941c714f325063e658c9418f596325072c528c9418fd95325063c654c941c714d325072c524c9418f194325078d320c941ad98432506b5610c9418f98f505063e62d4141a7d8d505069c6354141abd8950506ac62541418f59643106ae6290c41c794c431063d6590841a798e421072e52108418fd9541106776550441cd951411066e62d53319b58b54cc6ae62d5331c798f54cc63e62d5331cb98b54cc62e62d5331cb58b54cc73561d53318f58354cc71e63153318f98854cc73561153318f58054cc6ae6290f31ad58643cc6b56110f318f99252cc63d6494b318fd9152cc63c6454b318f99642cc69e6390b318f99442cc69e6310b31cb94842cc72d5210b31c715332cc71c544cb31e310932cc69e63d0731a718d41cc63e64943318f59250cc63f64543318f19150cc63e62952318f582548c63c62552318fd81548c6ae6290e318fd91528c63c6454a318fd96428c63d6590a31a798e428c63f6510a318f594428c6b56110a318f992508c63d64942318f98b544c63d60d51318f992544c63e65151318f988544c63d60151318f996434c6ae6290d318f994434c63e64d49318f593524c63e65909318f196424c69e63909318f994424c63c6510931a798c424c6b56110931c7153324c71c544c931d3149324c78c424c931b5185324c63e65d0531a798f414c63c6550531a718d414c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f98a540c63d60950318f189540c63f60550318f990540c66e62150319b588540c67a60150319e580540c63f6590c318f596430c6ae6290c31ad586430c63f6510c318f594430c6b56110c31cb952520c72d5494831cbd92520c72c6494831cb90e520c72c43948318fd91520c63c6454831cb951520c72d5454831cbd91520c72c6454831cb90d520c72c43548318fd96420c63d6590831a798e420c72e5290831cb54a420c63f65108318f594420c72e5210831cb548420c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc43197d95310c74d524c431e5505310c677654c431e590d310c63e64940318f592500c73a5494031ce552500c76a5294031da54a500c73a6494031ce592500c73a4394031ce10e500c73a4294031ce10a500c73b4194031ce506500c73a5454031ce551500c76a5254031da549500c73a6454031ce591500c73a4354031ce10d500c73a4254031ce109500c73b4154031ce505500c75b3154031d
  | 6 => 0xa9e6314442a758c5110aba6014442ae5805110a3c63540428fd855010a9e6314042a758c5010ab66114042ad5845010a3d61953328f58254ccb1c63553328fd8554cca3f6055332c755343ccaae6290f32ab98843ccb1e6510f32c759443cca9e6210f32e398843ccb8d6210f32a758443cca9d6010f32a798e42cca3e64947328f59251cca3e64943328f59250cca3d61952328f582548cb2c62552328fd85548ca3f6055232cb553428ca9e6390a32a798c428cb2e6510a32ab594428cb2d6510a32ab98c428cb8e6310a32e358c428caad6110a32ab580428cb1e54cca32ab993328ca3e64946328f592518ca3e64942328f592508cb1d63d5132cb58b544ca3d61d51328f583544ca3e64951328f994544ca3d61151328f580544ca5e65d0d32b398b434ca3e6590d32a798e434caae6290d328f994434cb1f5410d32a7994434cb1e6510d32e3d88434ca9e6210d32e3188434ca9d6110d32a7580434ca6e65d0932b398f424cb8c43d09328f996424ca9e6390932ab98a424ca3e6510932cbd50424cb8f4310932e310c424caae6510932cb994424cb8f6310932ab98c424cb8c6310932ab584424caad6010932ab993324cb8c43cc932a7992324cb8c428c9328f990514ca3d64145329e980514ca7960145328f990504ca3d64141329d984504ca7561141329798f540ca6e62d50328f98f540cb1e63d50328798f540ca3e62d5032cb98b540ca2e62d50328f587540ca3d60d50329d984540ca7561150329e980540ca796015032ad584540cab960150328f98c540cb1e63150328f988540cb2e6215032cd984540ca3d6115032cd584540ca356115032ce980540ca3d6015032ce580540ca3960150328f992530ca3d6494c32ab98a430cb1e5310c32ab988430ca3e64948328f592520ca9e63908328f994420ca3c6510832a798c420cb2e5210832c7153320cb2c548c832b358e320ca5f654c832c7151320cb8e424c832e3109320ca6f654c832cb151320cb8e434c832e310d320cacf654c832d3d95320cb8f644c832e3191320cb8f544c832d3951320cb4c544c832e3151320cb0c544c8328f992510ca3d64944328fd91510ca3c6454432d34c9510ca3e64940328f592500ca3f64540328f191500cb4d32540329b98a53d066d6294f41ab98a43d06ad6290f41c794c43d065e6394b419758e52d069e6390b41a758e42d072e5210b41ad58753d06ae6294f41ab58a53d063e6294f41cb98a53d062e6294f41cb58a53d063d6094f41ad58453d06b561d4b41a798e52d069d6394b418f98e52d071e6394b418798e52d071d6394b418f58252d06b56114b418f99732d063d65ccb418f99632d063d658cb418fd9532d063c654cb418fd9432d078d320cb418f18d50d063c6254341c794e43906ae6290e41a798e429072e5290a418f997
  | 7 => 0x7c00003c00800400001802c00000002400400000400000000800000000000002c00402000003c00001402000000c00002800c02800000401401400000400000407000007400002000c00000400801000400001803002c00802005000000803800c02c00800400001800000c03c00000402800000000000c00003400800800000801000400c00000400002c00400004801800400c00400401004000000c00001000000000000000001002001400000400400801800400401800400000400400800c01c01800401400800401001c00404000c00c00803c0000040000040180000000fc00002401404009800000400800c00001000000001000c00400c0000032f6494a43cbd0e5290f4f4354a43cbd4a5290e3d6194a438f5825290f2c6394a43cbd865290f2e6194a43cb5865290f2c6194a43cbd825290f2e6094a43cb5825290f2c6094a43cbd955290eae62d4643ab58b5190f2e52d4643cb54b5190f2e5294643cb9495190f2d52546438f1895190e3f6054643ab9885190ead6214643cb9485190eba6014643ae5805190eae62d4243ab58b5090f2e52d4243cb54b5090f2e5294243cb9495090f2d52542438f1895090e3f6154243ab9885090ead6214243cb9485090eb66114243ad5845090eae6290d43b358a4310e3f6550c4397d954310eae6294c43ab58a5310f1e6394c43cb98a5310f2d6294c43e398a5310e9d6294c43e358a5310e8d6294c438f5865210e3d6094843cb5485210eb66114843ad5845210eba6014843ae5805210e3c62544438fd815110eae6214443ab5885110eba6014443ae5805110e3c62540438fd855010eae6214043ab5885010eb66114043ad5845010eae6290f42c794c43d0b1f6494e42c794f4390b1e5390e42c794d4390b1d5310e42c794f4290b4d53d0a42ab98b5390b1f5394e428f5865390a3d6094e42c798a5390b1c6294e42c7d865390b1e6194e42c75865390b1c6194e42c7d825390b1e6094e42c75825390b1c6094e42c7d955390aae6214e42a798f5190a9d63d4642c794f5190b1d53d4642c794e5190b1e5354642c754d5190a3c63546428fd815190a9e6314642a758c5190b1e5314642ae9805190ab96014642a798f5090a9d63d4242c794f5090b1d53d4242c794e5090b1e5354242c754d5090a3c63542428fd855090a9e6314242a758c5090b1e5314242ad9845090ab56114242c714e4350aae6290d428f9944350a9e6390942ab58a4310a3f6550c42c794c4310b1d5310c42ab5884310acd63908428fd954210a6f6550842ab98b5310b2e6294c428f5865310a3d6094c42c754c5310aae6214c42ad9845310ab56114c42ae9805310ab96014c42a798e5210a9d6394842c798e5210b1d6394842cb98a5210b8e6394842ab58e5210b8d6394842a358e5210a3c63544428fd815110
  | 8 => 0xad922a60b2a0002f8ac08003040000000002f689a894000312a07a2912798a0268000000000000000000000a885b2813198001082be8000000000000000000c6800329a722b90002baacd3078df8bfa4128431cb0900019e8d59268000001faa8525a341193272a90ab41718621a83050fb9088353021703302c795302020e2519f7262a060869f20d0acf00018c00000780002f26992388c0000e517087d00680017d9752590000000000ae01e8cc8778b19f98e48002d916880015023f1c08879d603e0002a480000000000017c0000002f289627783f27ea2b25501396e30317608e1eb0580bb0a926d0dd0001dc0002ec8b781187106388d0cf20f93580029ba180100ce09b2e22f327400024e00000029100032000007f80007686807d8970002d809d8f98000b20000e7800144af40000649131d5a4a2c4a9e1bb0fb0001d096587f23b8853139739c1149036afe0ea2b5258242aafa090111e8000000249b3c0b4911000151a4a94724228680f8000578000e69d500000000007c8000000000002600560000000000000000630002eb80000011d0bb800000157b2ba9806f80027daf0895a9a03f81f2bc138ac0000133b1f931aec000002400c00006800001002800400000000003808000400001400803c03c00400000000400400c00801400400002c00401002001c00000801000400801400400800800000000401000800001801402c01401001003400400c01c00000800800000400401400400001401800000400001407800000000801000002c00802805c00400c01c08400c00400000000003c03000001800000404400800001000000c00c00401005400000c0a001801005001c05800000400000001c00000000003803c02400000001c00401000001005c00001002400400001c01c00400000c00c02403c01801002400000400000000400002000000000002400000000001003000006800c02002c02004400001002400800000400000400400000000000000000400000400000000c00001000801001800000402000c01400800001002000401802400c00403004001c06400000002000000000006000800000400c00000800802c01403800400800000402402401800400001801001800407400c06000800802c00401c00000000400400004800000c02801400002000002801000c00001000000000c01400803001001001800803c00001400000801400000401c00c00001003000007401c01400806800000400c00400000000402400000400008800402800400000000c01c01402400000000400000c01000002000c00000002807800000801801801001000002000008000000000801401000000c03003002800000000800801c01800000000003800004400000400400c00003c00000800401404402400801000000000802c
  | 9 => 0x8001a599d0002bb1f6b2800000000018b8000bda9c000000059af0189075b190002a280000000000000014580000016b2352520d2a5c25d898a97b2ead211180005423100004e0f21e433b800073800002b351a91d20ef159800000014a8990300020c89f8000000220000000001f610386c1901cc800000004993a318000f195d9848000409a50002168001198000000002b11ed8000191b90e38fa3260668e280013cadc8169e0a5b80000001780000000022b8978003268a68f10000001f81208be2918002ab18e0e234313d800038a662ac82118c850a93935035a5f01b1150e80f28010938af0da00000020b8740311f0ab2b1a0418000001fba448003241948002fb84b0180001cd80e240a3909c30c8001dd10519100002e0002d080030284aab2295a47b3399ca1eb1519200027a00028d9ee892a468b980033898b2cc0e10000000002ed19c2a200032880012e8c18050001a400000032c8000000000000000001b08001a9a3000000000000000d8001a30002708002ee80000c00031b00030a80000020b2e29ea2430001e63291f10f4044ae6078a23000053000204a2182d1408001f380000023aa9fa9d1ef16e8380cdb0114ca61318a57b3eadc001a1d2d591a9b00702ae90c8330000f69040aaa732f58ca9e117fa3300004ea0180000001b95080015d2d6ac5130340980a1b8ac8d69561d3aa02b6a5e00018fa2d0000d700000900000000006a8000000000000000000000002b58511188000548b2af9adda670000402040859fc9d318d0000000a1add25480000000000000023a00020a8f0a8307800000024c00001aad8aa720d05c87b8c60f80001e48001df0000238002d500006f1a680021300009800000000004f0ba93e95b800250ae18000601450002260000001628002e3a198000001fc11f2ad22000013bafd8000000339a22b78003378002340bc8000b8800053aa79a28000ca12629200008c800155a6b1d28e181a13e0690000c780003e80028e0b310e97a88230f0a58000000000a20000000001292e830388e80016a05fb1d92300024408b1212a3227a4d81425895f8cfa3c263800309acdae00280002d980000000000000000022200000000000000000011cac30001fa00000010900000021c0640001829c500003b8000000000000de8000000000000000000fd0ed0001f00000652700000000000002ce8b90000000001cd0001ec8001c63142251cb8003060c28c398a95127606b91a2140000c101d80019899e10d83918391f8a61a03068000b80001b200019629886a1ada6c800141295000000000067a0d8000000000be9b404d8001fd8ba109b0e8000920000000003368002148001009a48450000000002fd281a239a62492a419296a8000000000000001f30000000001ea98d8660002f73420bd21d80
  | 10 => 0x10709ca598002e59b10000000001100a080033a000000000000000000195a8c8c4a320008a81c2890af499b2618ce9c32c5a7e08f9069c580017480000000f0001d70dc00000007c00000000000005200000022c0000cb00a0000000002f528822a0002d78128001b5a3d0001cc12f0002b094194a80000000020983188d960a1f0ab2758c58dcaea9ce32c23d8e30001e00000002daac68b5a6d9ac868a821c980025280017985192db16a0f191b1aa6780000009316d8001310a400026e8aa20e85507eaccaef00000025702d8000001b893404c8a027d0470000000000001771270003088000b091b1648000000002f18002b009b9489122b99aa8a29da8001a38daa7992999a8719850001572d60c000007300000024f000000274a4b0208000001bd8001e2a282790ea83004f98e94b0000000f71063332bcab332d95a8000d40000001220000000002cf9758861e30002170ae80012c0c980013d0130919f7b002fa80017cb1e9d18001ca800166928124169978aff0002a83342cb0002ac05a94b9108d900003b3428003322971ba0002860002a9a47000061315a1a22d9b299811580a800288a77152aaa2931c700007600024c84b80010f2022fe8000000000000001ae0000360000000000123180000000e9a349de8422101c48d209495e87082f96fb2094f06d29410b0cd0ad2809cfade17e0a301d0e600815490a0a7a459fe9582801aa2058410000ec3318231d89322ca10c1460e0121a7397b1da02916b8f003ca5b1d78002cb83d9b19bc92a2bb8288ed91d96f3308e5943000189805a3830d0d81bd1e50569881c894d800336000149af3a179bb8002649990e900384a0002ef8000ef8d9b118000000002aa80005d9bf000161a109248002f80002af3381f9000235978199b2300002980011282b00000000013c327ae483297e925977855a00ad195e06ea892ea1ee0002718000002f60001e780005e00029680012b8ab80000023e00022cb018a70002082d12d40000001879ec00026b8002b8a0a2b6312283a66ac187228a0151192241870b401f9a796910227689d0f7916ab48c825610a8eb8f39288172ff8c89a10f332506080008300027b212a1e26914a22a9538000752e40c0847aa38891d00000000001160000b700002a84826800024e9a0a8f21a8000000001cb2fc33c8a9a99263000096a4f96c8000000a518600028b800000021b3721600010480000000000030e0000001d10001f402625f80002e8000258001328d300000015f2418bc32d1820000000f90188001ca186aa1a8a8001fe00009f00000012a86c8003178002a58000001e38000f51cea9b0000cc0000000001378000000000000002088dba7c0dd9480c32070002f232f93487b2a09e9a651dd8158ecaa88f626aa5a8af80000008093a0eb203ad2
  | 11 => 0x11b7236a288e88002b38000002a6a7b80005a139a623160fead308f000000032000172ae8a9614f8003248002e7ae132aa158001b4a872bfac62e30488379ac33dabf2c8b3585005f08714d00010ba450030f5845802248865a4d14e28f96100029c8000c200013908880000000006d80000000031c0fd8c520500023627c8000001568000001ab0001c90790000000001d40000000000000000d38000fc00000000000005d16002c225b21000136800311222ae6b2e19700033e1ba94c2c800031d1e8a1fa1c8002f12be15c98119b9b633b2ee2460000f88000000000d8800000285a6a0c431e09980000000000000011422e000000000000000000000000000000292800042a9e9768001b30d188494405731080c93705902c9ed049a8d17910d1182c41dfa271bf808a7523ca002ae22132f3349c21c401600000000000000027f8001ff9f888299a2b821900007719503a8d11680000002db8249f480000000b9058000fa9be0000000000003393398000002998629f580000021385ea87aada38b0480423789e0fc84380027888a800039aed8c72329af000100061a268228d02510001e9000030b0b233b2200012f8000000000001888000b6220b0a00000000000b18427a8fe1dca5d00015b18000003a19f0db00011e3219e5b3aac114003491c0070199b38000000000ac17d0000000001fd0000001e730c30d81c800107ac9b3fb0f80000025009500008400000004c254000000167adb1c78a105ba9a9380911c680012c9420d7ace1b50000000002ba185a6c0001eb8000000000c90000003149b78000bf2a11b680028b0000000000000000000000002fa1830002c71a732700015907a00023980000010f8001fb0000b6a06b130ee1479550a3b3f256b3288bb0ba15081ad495227108a0278000002558000b00ff8000002fcb258061650002011ef83d1e697a25386980000000014399780006b10107e31b8839beb071e231f0002e082521188000012b340229a111f519faa60ff1968460a48588000002c926432b17f0000000000000eeb3d21200e80015a2e92901028001ae8000002f78002372bda249c397b82b8001170000000002530df10e1731d6b058000000000e0889800268a658001cf341af912d01c1bc23b2caae994ea02809b1030092e18f0d61de2d728c0002ab8e71f29c81360e41b9ac2067331000081010b1702725e964218abd1d92b1aa516327f02403704d1d49d81b83239c011e9ad26f13a8b3ada172046a6e0001ab89000024b99d9469db2c3a8e80016728287296393fa6fae727815893f00000d0002df94283c19080010195c2d01178001ff1c18000002df1620001af86e1308000001f180000000000023e80000005c166000000000000000099181a4393b07aafb2a90340000001540000000000000000
  | 12 => 0x29f113a2ea84ac2a032e524022f8cb8000b500016c0d519400022f2de80030800000011b89e8432eb00029d800133000052a5c8441a8ab7000000074800079a4800000023f82a1d9b229200de1e18881148000000002d38001a1a948f480012501e00000000023084909a00000021b0001710001740d4a0c16d1db8b
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xa0525711482150314292c010a818398d62d5330a1ae5318a99861a6358054cc217394cba0e610b1c9655063086ae2328849850c75109324c2c4b808499261345c4604c93085aeb314861850e73d92520c28739ec8a90610b9da4354830a52e021aa4184997098e420c30731aa521061499ca4394430a2ce7214a21851473591510c29339486a88614c5c24354430a62e021aa21851673909510c24cb80c6a08618318d5250430c28c6a8a821870952501300c388a8a8098061629ca434c030e2486a8a601860d6398b54c8286b9cc42a6418a989601532086ae2328879050c7510d32c820f39ccba0e41071cd655062083ce7310a89042e72196434821ab88ca21a410e1d56010d20a18ea21a64905897010d3248270b88c0992410b9ca6395020a1ce5b24a61050e72d915308216bacc5218418354e6290c20952e1314861041e73d96420820ebacc72104107dda539082083eeca9c84106195358042082933948728841459ce4294420a48e4b22a2105267290d510828b39c84a88414c5c24254420a62e0212a21060d531894108254b80c4a0841891895150420e12a6a0240107215150120082c539c8490041c8909514802085ce531ca98841e7398a54c4217396cb21e21079cf6590b1085ce531ca90841e7398a5484217396cb21c21079cf6590a1085ce531ca88841e7398a544430631ec4aa22183d8c6255110c18c6312a88842c725935344217396cb21a210b1c96510d10a1ae4298868861453584434430c29ac021a21071cd64d491083ce7b2c848841c735944244286b98a421221891496110910c50a4b0084884e1721813144268b98c090a21071cd6550110858e4b2a80884e1721853044268b98c2902210b9ca639501083ce7314a80850e72d925304217396c8a9821439cb6454c1085ce5b2c860842d7598a430430729cc5218218354e6290c10a1ce7b24a40842e7690e520420f39ec8a9021439cf645481085ced21aa40841e73d96420420ebacc72102107dda539081083eeca9c840860e6394a420430731aa521021c454f4044010e42a5a022008711535011004390a928088021c454f4144010e42a5a0a2008711535051004390a9282880214c5d66444010a66eab2220085907359110042d0392c888021585cb5344010aa2eb29a20087125454d1004388aa2a688021c4dd15344010e20e8a9a20087126454d1004388b22a6880214c5d64344010e22a721a20085a27290d1004298ba88688021c454c4344010aa2e7a9220085617594910043a0a9ca488021c89515244010e42a8a9220087425354910043a0a9aa488021c8dd15244010e40e8a922008722645491004390b22a488021c890d5244010e4086a9220085317590910042c939c8488021c454e4244010e42a52122008531751091004388a988488021c85484244010
  | 1 => 0x5290e93388c129487495c46094a43c52c0304a521c2d769485190f15294c028c878a949601464385aed290a121e26529845090f13292c228487895496114843c52a4b00a421c39701895110e1ab88c4a8087459c46294e42a2ae2314a72151a7018a5390a8cb80c529c85439c86194e42c2ac230ca72151a701865390a8cb80c329c85439c86094e42a2ce2304a721515711825390b0cb00c129c85075da5314642c34a7300a32161a535805190a0ebb4a6284858594e6114242c2ca6b08a121615535845310b0ca9ac0298850e5c0635444286ae231aa02150e75188434cac2b88c421a65625c06210d32918e4b08869948c72580434cb0732887a1265439d76310932a1cea31884995857118c424cac4b80c621265231cd6110932918e6b00849961663584540cb13312c22a0658c5866015032c34c6b00a81962a62580540cb1930ac02a0658c5856015032a2ae22a6641951970153320ca92b88a9190654a5c0548c83283cec2a2641951571151320ca8cb80a8990650b9d8544c832a4ae22a2641952970151320ca873a6ca99065239db544c832a1ce92a2641954571151320caa4b80a899065239d8544c832b0ae22a2641958970151320ca873b0a899065839d8544c832e0ce22a2641950d71151320cb82b88a899065415c4544c832e14e02a2641950d70151320cb84b80a899065425c0544c832c18c8992a21960c644c9500ca86b94a621e83435ce5210b41c18a6b1486a0e0d6314a425061cb80ca1928383195320c941d0a64b0864a0c2e7298f505060f39cc5a82838398d62d5331a1ae5318a998e166358454cc61cb80ca21263431d4424c931b0ae22126498cd170185324c616bacc521863439cf6494831a1ce7b22a418c2e7690d520c692b8886a9063255c66390831c1cc6a948418f0552505310c6c339486988634a9ca4394031a34e7214a018d1873591500c69539486a80634c5c64354031a62e221aa018d1a73909500c788a0a62a8063c490d3154031c1ac7316a990d0d7398854c8713312c22a6430e5c06510f21a18ea21a6590c3970194434861a3aac221a43431d4434c921b0ae221a6490ce1701853248617394c72a043439cb6494c21a1ce5b22a610c2d7598a4308706a9cc521843295c66290c2183ce7b2c8410c1d7598e420860fbb4a72104307dd95390821c2aa6b088410f055350521086c339c84908434a9ca4394021a34e7214a010d2872591500869539486a8043469ce4254021a62e3212a010d31711095008790a0a42a8043c89092154021a1ae529887a050d7394842d0217396cb98e81079cf65c8740c18a6b1486a060d6314a425021ab88ca1928183195320c940d1264b0064a042e7298f515020f39cc5a8a810b1c9658c540a2ae229862a060c53588315030c29ac018a81071cd6588540c1ac629042
  | 2 => 0x2a0000d8d400000001462c49e00000000002880000000240001f89d0005701087064003193e3b80041c2a000bc0000011000000db08021500002900047c00000002a40000000000fa0000038913554000006d000af40000000d600000538ea00005418002b8130000000148094b54d8003212b0dc422b12400023548f50c93816c002d1530001837c001d54d16000000fc000000003c0000011800001411c0354e4120000043c3a0309f0008f34c00000c2138000004f000880000028000000000000000000000000005a22400000f74a400430da00000000684ec3b528d843800208a7040b24bc8548c265505e1e84d000001240025c003d92742c470007324cbd32c00228bb2608e558064a072344004750118411310a318c383ece5435150ac1f0d07d0c42f340ad17c003c40031d47000aa00131140001dc160080019800128402e86e1300009c22028001f0e01484b254003b00014d1a4500000078001023f4ce0000007800000000000045c00000d203d340012600118000000000000400000bf0012c0003f20c001807900024000004d4fe0000000000458b72c0b60b06207130514ef0354237508000f4000e3000ab000de170e81ec00000001bcf2000ca3fd122706422c280680019c000006b000004940000000204f3000b82441b174e12500040c0007400470924dc0800000000f900000000001d90a325111a454000963a4e71c400440d510c00230000000b0014b00000001330014f298000000000056000e63e0390000000000000004b94c0b8c14641542400364c50007f000c326c0000000000484a8000007400000000e4000cc0015000000000c04793f3ad22000070009a0012d000b31b0171940000000000000008d0003d000f028400000000000000009000300013d001514f000000000000000c29000d7484004100e164b90008646c3300144000ed00000000cd0005100000000000008426549000800002d0013a33c550000000000000a500105000001a800001433700000045050000f932104002f800480000000001e01802008000001800000000020280600802008020000003002008000300000800068000000c0200000000010040080002000080000380000006010000000204810008000600201808000040200201000050260000000800060000080002006000000080601024000000180a0000800004000000080003800010000400200816000160600400800010000000000d267118e5290e92b88c7294874a9c06394a43a52e031ca521d0e731865290f12b08c3294874a9c06194a43a52e030ca521d0e73182
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x27163a393e000d3b1c1a1d34170812191324003821362e31371b4010060b262a2d3d2800002f07293500000c32000500002c2b000022330e2302111f3f0000303c1e180f092014011504250a030000002e1810302000900038001460c2010e94004c21615c06194a43c21715806094a43c11615c06194e42c11715806094e42889801c96110d32885811c96010d32889801cd6110932885811cd6010932d01719c0544c832d02715c0544c832d01715c0544c832a0980195320c941a058298d6115331909801d4424c931a058198d5290831905859ca434c431911819ce4254031b028290d3154031a05839896115321909801d4434cb21909801d4434c921904855c4434c921c05535c66290c21905859ce4248421921819ca4354021b02839092154021a0581195320c940a058114d620c540a118114d600c540c05635c45208540a21811496008540a098298d6015330905811d4424c930a098098d5290830911809ce4254430a098018d5250430a118018d5150430909859ca434c030b028290d514c030a09839896015320905811d4434cb20905811d4434c920908855c0434c920c09535c26290c20921809ca4354420c09535c06250420a21801895150420909859ce4248020b02839095148020a058214d6110d10a098214d6010d10a05831496110910a09831496010910b0282dd15344010910875915344010b00825915344010921859ca4344010d01539ca4344010b0283dd15244010920875915244010b008359152440109228790d5244010911859ce42440109138754e4244010d027354a4244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1044
  | 4 => 1671
  | 3 => 343
  | 2 => 65
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
  | 5 => packedAt s5K5 (32364+((h/348+packedAt s5K5 (28188+(h % 348)*12) 12) % 2216)*12) 12
  | 4 => packedAt s5K4 (70182+((h/557+packedAt s5K4 (63498+(h % 557)*12) 12) % 2426)*12) 12
  | 3 => packedAt s5K3 (17947+((h/114+packedAt s5K3 (16807+(h % 114)*10) 10) % 601)*10) 10
  | 2 => packedAt s5K2 (4047+((h/21+packedAt s5K2 (3900+(h % 21)*7) 7) % 79)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe1fe1ffc3fe3fc7e1e38fc7f1f87f0fe0cf4cf
  | 1 => 0xfe1fe1ffc3fc7f8fe03f1f8fe3f87f0e333b33
  | 2 => 0x1ffe3ffc007ff1ffc01ff1fc007ff1c3cc3c
  | 3 => 0xffe0003fffff8001ffffe001ffff8001fc0fc0
  | 4 => 0xffffffc000000001fffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x28028004088410800408241204821044045045
  | 1 => 0x408408088100a0104011088421202408112112
  | 2 => 0x1548449110494802aa40112148114aa0c28c28
  | 3 => 0x844155222240092532a2400192550221680e80
  | 4 => 0x19919983bb927249dd3c9e4800660ccdbff000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee8eee8fee8eee8fee8eee8fee8eee8fee8eee8fee8eee8fee8eee8fee8eee8fee8eee8fee8eee8fee8eee8fee8eee8fee8eee8fee8eee8fee8eee8fee8eee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37181
namespace PEqualNP.Outside.L_meta_37181
open PEqualNP.Outside.L_meta_37181.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x302418e000062e44a15805e980143e1801600b0925009118400f88026028f370a21c8f2e85e3a7e000b40ed46aa36554bd22b53b30001b1d000001c0001da000005b1700001334c8c800600000800000005120998220080801228b80017fd5005fe54017f55005fc5401ffd4c07fe5301ff54c07fc53017fd0c05fe43017f50c05fc4301ffd4807fe5201ff54807fc52017fd0805fe42017f50805fc42007fcc801fe32007f4c801fc3200ffd44037f5100ff94403fd5100df54403fc5100ffd0403bf4100ff90403fd4100ef50403fc4100ffcc403fe3100ff4c403fc3100ffc8403fe2100ff48403fc2101ffd4007fe5001ff54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a400cff59520065faca90033fc65480077e32a400cdf1952001cf8ca9002fff64480177fb224000efd91200057ec89002ffe64480057f322400bff5912005dfac89002ffc64480057e322400bef1912001578c89002fff5448017ff2a2400bff5512005ff8a890003ff63480017fb1a4000ff98d2004dfcc690003fd63480017eb1a4000ff18d2004df8c690033ff5348019ff29a400cff54d20067f8a69002fff4348017ff21a400bff50d2005ff88690033ff524800bff292400cff5492002ff8a49002fff424800bff212400bff5092002ff88490003ff324800bff1924000fb8c920007fa6490003ed324800bfe192400affd8520055fec29002bfe61480037f30a400aff58520055fac29002bfc61480037e30a400affd4520056fea29002bfe5148015fea8a400adf54520057f8a29002bff4148015dfa0a400aff90520057fa829002bbd4148015fe20a400affcc520057fc629002bfd3148015fe18a4005ffc8520057de429002bfe2148015fe90a400afb4852002ff84290033ff5048009ff282400cff54120027f8a09002fff4048009ff202400bff50120027f88090003ff3048009ff1824000ff4c120027f86090017ff204800bfd9024004ff88120027dc409002bff1048009ff082400afe84120057fa209002bf91048009fe0824004ffd9420025feca10013fe65080077f3284004df9942001cfcca10013fd65080117eb284004df59420004faca10013fc65080097e3284004ffd9020025fec810013fe64080057f3204004ef990200157cc810013fd640800f7eb204004ef590200057ac810013fc64080097e3204007ffd502003ffca81001ffd540800ffe2a04004ffd8c20025fec610013fe63080137f3184004f798c20005bcc610013fd63080017eb184004f758c20005bac610013fc63080097e3184008ffd4c20047fca610023fd5308011fe2984007ffd0c2003ffc861001ffd430800ffe2184005bf9882002ffea410017fe520800bfea904005ff1482002ffe8410017fe420800bfea104005ff1082002ffe6410017fe320800bfe9904005ff0c820027fec210012ff6108009ff3084001bf98420027ecc210006f66108009feb084006bf58420027eac210002f56108009fe3084004bf18420037fea21001b7f510800dff2884006ff54420036faa21001bfc510800dffa084006efd0420037fc821001bfd410800ddea084006ff10420037fe621001bfe310800dfe9884006ff0c42002ffe4210017fe210800bfe9084005ff08420025fcc010013ff5008009ff2804004ff54020027f8a010013ff4008009ff2004004ff50020027f88010013ff3008009ff1804004ff4c020027f86010013ff2008009f79004004ff88020027f44010013fd2008009f69004005fe48020027fe2010013fe1008009fe8804004ff04020
  | 1 => 0xffc210c0097f3006004ffd4030027fca018013fd500c009fe2806004ffd0030027fc8018013fd400c009fe2006004ffcc030027be6018013fe300c009fd1806004ff4c030027ba6018027f9300c009ff8806004ff84030027fa2018013fc100c00bffb2e4005bfd972002ffccb9000efe65c800bfeb2e4012bf5972002ff8cb90016fc65c800bffb264005bfd932002ffcc99000afe64c800bfeb264011bf5932002ff8c990016fc64c8023ffaa64011ff9532008ffaa990047fc54c800bffb1e4005bfd8f2002ffcc790026fe63c800bfeb1e4000bf58f2002ff8c790016fc63c8025ffa9e4012ff94f20097faa79004bfc53c8023ffa1e4011ff90f2008ffa8790047fc43c800bffa964005ff94b2002ffaa590017fc52c800bffa164005ff90b2002ffa8590017fc42c800bff9964005ff8cb2002fdc6590017fd32c8001f69964005ff0cb2002ffec390016ff61c800bff30e4001bf9872002ffac390042fd61c800bfe30e4001bf18720087fea3900437f51c8021ff28e4010ff54720086faa390043fc51c8021ffa0e4010efd0720087fc8390043fd41c8021dea0e4010ff10720087fe6390043fe31c8021fe98e4010ff0c72002ffe4390017ef21c800bff10e4005ff48720087da4390017fc21c8025ffa864004ff94320097faa190013fc50c8023ffa064004ff9032008ffa8190013fc40c8001ff9864004ff8c320007fa6190013fc30c8021ff8864004ff84320087fa2190013fc10c8009ffb2c4004bfd9620027fccb1000efe6588009feb2c400fbf59620027f8cb10012fc6588009ffb244004bfd9220027fcc91000afe6488009feb24400ebf59220027f8c910012fc648801dffaa4400eff95220077faa91003bfc5488009ffb1c4004bfd8e20027fcc710026fe6388009feb1c4000bf58e20027f8c710012fc638801fffa9c400fff94e2007ffaa71003ffc538801dffa1c400eff90e20077fa871003bfc43880157eb14400fffd4a2002ffca51003ffd528800bfe294400effd0a2002ffc851003bfd428800bfe2144000ffcca2002ffc6510003fd328800bfe1944004ffd8620025fec310013fe61880037f30c4004ff5862006dfac310013fc61880097e30c400dffd462006efea310037fe518801bfea8c400ddf5462006ff8a310037ff418801bdfa0c400dff9062006ffa8310037bd418801bfe20c400dffcc62006ffc6310037fd318801bfe18c4005ffc862006ffc4310037fd218800bfe10c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fe9844004ff0c220027fe4110013ef208800bfd9044004ffc4220027fc2110013fa1088009fe884400dfe44220027f82110033ff65480197fb2a4000dfd9520004feca90033fe65480077f3
  | 2 => 0x300cff88318027ff318c033ff18c6019ff4c63004ff86318067ff218c033ff10c6019ff486300cff84318012fe608c009ffa846004ff94230027faa118013fc508c009ffa046004ff90230027fa8118013fc408c009ff9846004f7cc23004ff66118013ff108c009ff0846004fe84230027fa2118067f9108c009fe0846018ffd95300c5feca980037f654c0013fb2a6018ff9953001dfcca98063fd654c0317eb2a6018ff1953001df8ca980637c654c0073e32a6017ffd91300bdfec898003bf644c0015fb226017ff99130015fcc89805ffd644c02f7eb226017ff19130015f8c89805fbc644c0055e3226017ffd51300bffca89805ffd544c02ffe2a26018ffd4d3004ffca698063fd534c013fe29a6017ffd0d3004ffc869805ffd434c013fe21a6000ffd8930005fec498003fe624c001feb126000ff1893002df8c498063ff524c031ff2926018ff549300c7f8a49805fff424c02fff2126017ff509300bff88498027ff324c001ef9926000ff8c930007fa6498003dd324c013fe1926016ffd85300b5fec29805bfe614c0037f30a6016ff585300b5fac29805bfc614c0037e30a6016ffd45300b6fea29805bfe514c02dfea8a6016df545300b7f8a29805bff414c02ddfa0a6016ff905300b7fa829805bbd414c02dfe20a6009ffcc5300b7be629805bfe314c02dfe98a6016f74c53004ff8629805bff214c02dff10a6016ff485300b7f84298063ff504c009ff2826018ff54130027f8a09805fff404c009ff2026017ff50130027f88098027ff304c013fd9826004ff8c130027bc609805bff104c009ff0826016fe841300b7fa209805bf9104c009fe0826004ffd9430025feca18013fe650c0077f3286004df9943001cfcca18013fd650c02b7eb286004df59430004faca18013fc650c0097e3286004ffd9030025fec818013fe640c0057f3206004ef990300157cc818013fd640c0297eb206004ef590300057ac818013fc640c0097e3206014ffd50300a7fca818053fd540c029fe2a06009bf98c3004ffea618027fe530c013fea986009ff14c3004ffe8618027fe430c013fea186009ff10c30027fec418013fe620c00b7f3106004fb98830005dcc418013fd620c0017eb106004fb58830005dac418013fc620c02bffa906015ff948300affaa418057fc520c029ffa106014ff908300a7fa8418053fc420c013ff9906009ff8c83004ffa6418027fc320c009ffb086004bfd8430027fcc218006fe610c009fb3086001bd98430027fac21804efd610c009fab086000bd58430027f8c218012fc610c027ffa886013dfd443009ffca21804ffd510c027bea886013ff1443009ffe821804fbf410c027ff2086013ff5043009f7a821804ffc410c013ff9886009ff8c43004ffa6218027fc310c027ff9086013ff8843009ffa421804
  | 3 => 0xf2186409ff50c3204ff88619016fe620c80bffa906405ff9483202ffaa419017fc520c80bffa106405ff9083202ffa8419017fc420c80bff9906405f7cc83202ffc6419017ee320c80bfe9906405f74c83204fda6419003cd320c80bffb086405bfd843202ffcc219006fe610c80bfeb08641fbf5843202ff8c219006fc610c83fffa88641fdfd44320fffca21907ffd510c83fbea88641fff144320fffe821907fbf410c83fff208641fff504320ff7a821907ffc410c813ff9886409ff8c43204ffa6219027fc310c80bff9086405ff8843202ffa4219017fc210c80bffb006405ff98032025fcc019017fd600c8017eb006405ff1803210ffea019087fe500c843fea806421ff14032107fe8019083fe400c841fea006420ff100320fffe201907ffe100c83ffe880641fff0403204ffecb98026ff65cc013ff32e6003bf9973004ffacb9807afd65cc013fe32e6009bf1973004ffec998026ff64cc013ff3266002bf9933004ffac998076fd64cc013fe3266009bf193300effea998077fe54cc03bfeaa6601dff1533004ffea798027fe53cc013fea9e6009ff14f3004ffe8798027fe43cc013fea1e6009ff10f3004ffec598027fe62cc00b7f3166009ff58b30005fac598027fc62cc03dffa96601eff94b300f7faa59807bfc52cc03bffa16601dff90b300effa8598077fc42cc013ff9966009f7ccb3004ffc6598027fd32cc001ee9966009ff0cb3004ffec398026ff61cc013ff30e6001bf9873004ffac398072fd61cc013fe30e6001bf187300e7fea3980737f51cc039ff28e601cff547300e6faa398073fc51cc039ffa0e601cefd07300e7fc8398073fd41cc039dea0e601cff1073004ffe6398027df31cc013ff18e6009ff4c7300e7ba6398027fc31cc039ff90e601cff887300e7fa4398073fc21cc03dffa866004ff943300f7faa198013fc50cc03bffa066004ff903300effa8198013fc40cc039ff8866004ff843300e7fa2198013fc10cc009ffb2c6004bfd9630027fccb1800efe658c009feb2c601bbf59630027f8cb18012fc658c009ffb246004bfd9230027fcc91800afe648c009feb24601abf59230027f8c918012fc648c035ffaa4601aff952300d7faa91806bfc548c02d7eb1c601bffd4e3004ffca71806ffd538c013fe29c601affd0e3004ffc871806bfd438c013fe21c6004ffd8a30027fcc518016fe628c009feb146000bf58a30027f8c51806fff528c037ff294601bff54a300dff8a51806bff428c035ff214601aff50a300d7f88518027ff328c001ff1946000ff4ca3004ff86518013ff618c0097fb0c6004ff9863000dfcc318013fd618c0337eb0c6004ff18630025f8c318067ff518c033bfa8c6019ff946300cffaa3180677d518c033fe28c6019ffd06300cf7e8318067fe418c033fea0c6019ef506
  | 4 => 0xa7ff40cc853ff2066429ff5033214ff881990a3ff10cc851ff0866428ff44332147f82199017ff658c80b7fb2c6405ff9963201dfccb190177e658c8073f32c6405ff5963213dfacb190177d658c8013eb2c6405ff1963202df8cb19017ff648c80b7fb246405ff99232015fcc919017be648c8055f3246405ff59232135fac919017bd648c8015eb246405ff1923202df8c91909bff548c84dff2a46426ff55232137f8a91908afd638c84fffa9c6409ff94e3213ffaa719027fc538c84dffa1c6409ff90e32137fa8719027fc438c80b7f3146405ffd4a3202ffca519017fd528c80bfe2946405ffd0a3202ffc8519017fd428c80bfe2146405ffcca3202fbe6519027ef328c80bffb0c6405bfd863202ffcc319006fe618c80bfeb0c6425bf5863202ff8c319006fc618c84bffa8c6425dfd463212ffca319097fd518c84bbea8c6425ff1463212ffe8319097bf418c84bff20c6425ff5063212f7a8319097fc418c813ff98c6425ff8c63212ffa6319027fc318c80bff90c6405fbc863202ffc4319017fd218c84bf690c6405ff0863202ffec119017fe608c8097f3046405ff58232005fac119017fc608c84fffa846427ff9423213ffaa11909ffc508c84dffa046426ff90232137fa811909bfc408c84bff8846425ff8423212ffa2119097fc108c849ffb2a6424bfd9532127fcca9900efe654c849feb2a6424bf59532127f8ca9900efc654c847ffb226423bfd913211ffcc89900afe644c847feb226423bf5913211ff8c89900afc644c847ffaa26423ff9513211ffaa89908ffc544c849ffa9a6409ff94d32127faa699027fc534c847ffa1a6409ff90d3211ffa8699027fc434c849ffa926405ff94932127faa499017fc524c847ffa126405ff9093211ffa8499017fc424c813ff9926409fbcc93202ffc6499017de324c845ffb0a6422bfd8532117fcc299006fe614c845feb0a6422bf58532117f8c299006fc614c845ffa8a6422dfd4532117fca29908bfd514c845bea8a6422ff14532117fe829908bbf414c845ff20a6422ff505321177a829908bfc414c813ff98a6422f7cc532117fc629908bfd314c845ee98a6409ff0c53202ffe429908bef214c845ff10a6422ff48532117da4299017fc214c801ffb026400bfd8132007fcc099003fd604c801fe3026404bf18132127fea099093fe504c849fea826424ff1413211ffe809908ffe404c847fea026423ff10132117fe209908bfe104c845fe8826422ff0413202ffeca19016ff650c80bff3286403bf9943202ffaca19086fd650c80bfe3286405bf1943202ffec819016ff640c80bff3206402bf9903202ffac819082fd640c80bfe3206405bf19032107fea819083fe540c841feaa06420ff1503204dfcc619027ff530c813ff2986409ff54c3204ff8a619027ff430c813f
  | 5 => 0x3394109c0ca80000004900e1f080010701f25223ca0e0b91c51080910001808da9bb87d80009a80022d95d0748001d80000001558001cd974a390f10001cc92924c08696b8d0824a4584c1c684b8a117b2170450001ae226214803000004054030470000280700100205c0580f02e00010012036008060170000180880900a0c400806002020040090000000181900002c0b80300400403005000028070040500440280101a01c0200400a0c40180000001c008010060000080d0000c80000300e024080000000780200500801810808000044048250000a00780c01a000000050020300080a04a01800002064044000020560400d01000402c050030000200000d002014010000140140700300800c0002d00617c0001f000000018080061640280000c0040100700e004010070000000400b01a008140100040100000000202c0c80702e02001803000008028020160ac00000000030038020000000080303400002022006040000000060000702a0000000000a0180140180500000c018020000040a00400201c028050060b80380001a008000110320080680000400000000014014050410000000000200002c0000003c04c000060220280001900202c0200500400c0d810004000010000000680300f00800000809002014090000100000100e00c0000100300a01400000006010008030020000f8030360280000300a028058000260380080603c0000000c0500880980601400801004004000070030060540080502e024008040b80080480300000000003008014090000040080181e01e010028040000100800000201c000170000000002100000c028030080040600100001401819028000080020460000381001001c0100503400c00027ff65cc8137fb2e6409ff9973201dfccb990277e65cc8073f32e6409ff59732155facb990277d65cc8013eb2e6409ff1973204df8cb99027ff64cc8137fb266409ff99332015fcc999027be64cc8055f3266409ff5933214dfac999027bd64cc8015eb266409ff1933204df8c9990a7ff54cc853ff2a66429ff5533214ff8a999027ff53cc813ff29e6409ff54f3204ff8a799027ff43cc813ff21e6409ff50f3204ff887990abff52cc80bff296642aff54b3202ff8a5990a7ff42cc80bff2166429ff50b3202ff88599027ff61cc8137fb0e6409ff9873200dfcc399027fd61cc8517eb0e6409ff1873200df8c3990a3ff51cc851bfa8e6428ff94732147faa3990a37d51cc851fe28e6428ffd07321477e83990a3fe41cc851fea0e6428ef50732147f88399027ff31cc813ef98e6409ff8c73204ffa63990a3dd31cc813fe18e6405ffc8732147fc43990a3fd21cc80bfe10e6409ffd833204ffcc199012fe60cc813feb066400bf5833204ff8c1990abff50cc855ff286642aff54332157f8a199
  | 6 => 0x209e15617d00021405d8e78b59a815a0f419f8bc1a88f89f82530d880000011f840a4e83401719e98b0119a981b96b10380b203a128729a101100a15811193c88b8c219421d1d71e001294387c0320c90a38ce22014084aa181768c00f81758990752052000de13a1fb9a28fe0001f894f166247927861a1b06723796e80014803090188f8ca0002380350af9b89cc09b00022124aa430f50160d1a3a8be821a0b9ee89a12f17e1688801c194a13322a8000000cc0000001248439e508e00007080018209224c99a1a30000ea0000002008ad14680000700000c2110001ba00020621e8a80b099492402307594c85994d1e990119c0810791c614581aa4498b8560b205e1650078d200023c0000000c98dc80014e10602293711e0000a880000000012b8998828001b98cb0ee8000001309a40799699bf90b97518617ea5113191f02e23880d0000001e18001288001181fe8000000d50000f980013606680013e0c78b615b00018e00395f1478000db856a2b9eb000037a499dc9b08b320e9ee0d59272168838ad9069990ba92da321c88b893ea0f0e594285000010793f0300b98001e624907687e0a597f1d083b9f60000639f7a270000e50fb05aa0c1d69210000001ec14323111083da069191e803a1fd93997800013c1ff00009c9e495482c00006491aa4f0e984a2228001311710bd0001110591b48e60bfa240ab95e89d05ca019a19ad8e014881da049648bb13288708b19997f9d300a8960a188c8bda1a1cb21e1151bb0c488f03f0f7a4819f1d783e0240f322e1b120423e91ba2d0c884b0a409f9d90429fa9b91cb9519f983308d094a4b1eb8a7a3b1aba3098704c8180640002518478002058b38ac0148738001368789530000d48431c70001c415e13b00024d0371bc8020001ab08424b98e80019801424387d0ec21c02591e9840f590295b8aea121d000000000000018980024f9f19d39b20ed1da135a2513400000000000007f1c28b10059571ac04d8000d10000001041301238550a08150821461280978df0b18480aa86818386c0eb1261f52399259fe0a986307b9601a004017da33a1380f02206e0b299002716d9a61c09020f688807a88182a10d9f700018813b8f019b998a1f80ba1c9d190c9500831209380ea95c1c391016c02819113d96a98a0c59e5a1308911c00191417780007792b00022984614f8c09e31ff961a1921a82e98685a0a68fa0558001679509ea98d0d71c91168d79e3a2209005794020b017a208581af0000002440fe80023f81c05f0001800a30ab1ca8c180020d24da4a0e11d203c9da8c717017887207c9f117a0718000421a500011306791981909196288a0a70b786b8b804e11a00015400013a97084683111219086286d8780000000001d51d881680020a94a86a00000011b0510ac8c11b61fb1
  | 7 => 0x1fa24080680009090aa4680000010b10980000010f00000011380010889f0388faa3300020780000000000012d1379a700016680003580009882aa4280023f1e681000000010fa070001498001fd23a0ff8c80c2a292160288a291785b1ca16803814198786f0bca239589e11d10ee00005092a98318525019e1c812ca2884583b1149321e788c06980023400000003a8000e68410098f600018fa0816f9858aa2359609b71422099f016e09285c2460200fc8d39b31df904a199cf16590301b0418c683388787b21d8ec8a00f20b48000970fd80013517b9d61eca021d29e70700e09738850001a21a09bc00000000003180005b8b416924e0610c40000470250650f09f680014b8f908883e9760cf8000e81b40000000000940000002368848eb8000c52301a68001e20a500021b8000001729921798000349be05306e8b50f712a0d98761252248e18899b38001c10730001cf88581894501d0e31c49ac8001c79719791930cd97a9dd8fc19a92e23d0158fd1390da0f39598049ef9fc06d02c91d0001b8095a2c0af112a01000000a4000018c9890000a481a1889551f39e282100007f8000d01221bf0b723d8000e70ff00006b02d8001811929ed80000006f80f96119d05720f9b6a450000740001ba9e8a3e09e9df12f86081f85402380011c8e40002269cd0000dea1505d1939960ba21f22f22817304488a8002371db80016d0051521f49230000d60002218001a790c0f49a90000ce80000001091d80895680404f00019d9b000020a1de96f20315105e8d69be9819f28121ea1db0cc852a319630ae02d0090ed98c10595297413493f8f19ef11704e8980be09b86c82f0398661dd25295a82f9919009771640601dc0001af88d8fb82b8000000ef07e8c314b04fa2b06a83fa352348ef8a210d03c10a00022a0d41969b19aa0539591bd9f323611615f9a49298d29f90001090000001ad1201970d901301980000009300d8001ce9ed1d58a60691228e48c60dd80014420c80013880000007721080010000294c00604980013d0cb8000000001c980014d9d49c58b024103296c95ca15a231638df9f405492180000000003d0000000001448b68809950000000368520000000000001269b790e9b29f21b52259849de23ba2e9050659ae820a0d9fc9979e0a2c81ca27915a420cf1670e28dc0a905f8e21bd0db01e23280018d9b58e916a0030e380014700007a17200002601e80019b03906214e99ca509c219592e8bf00100c9aa94920898aa090361c022f82b00817ca418000001a3a470002178e88bb88e9f59d401390e0950689e40cd02985882680002912c0489a5a118f28c398f0001ce15d80007117c00000000000000020280021880e89389d9188278000969538001e91c32488518dd0000860d82100001829578d316
  | 8 => 0x1d984400004d000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7458c20024ff7358c20026df7358c20006df5358c20006de5358c20006dd5358c20006dc5358c20006df4358c20006de4358c20006dd4358c20006dc4358c2002cff7258c2002cfe7258c2002cfd7258c2002cfc7258c2002ede3258c2002edc3258c20004ff7158c2000cfe7158c20004fd7158c2000cfc7158c200067f5158c200067d5158c20006bf4158c20006bd4158c20006df3158c20006de3158c20006dd3158c20006dc3158c20024ff7058c20024fe7058c20024fd7058c20024fc7058c20026de3058c20026dc3058c20026ef2058c20026ed2058c20006df7558c20006de7558c20006dd7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c20006de5458c20006dd5458c20006dc5458c2002edf7258c2002ede7258c2002edd7258c2002edc7258c2002edf5258c2002ede5258c2002edd5258c2002edc5258c2002edf4258c2002ede4258c2002edd4258c2002edc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df5158c200065f5158c20006de5158c20006dd5158c200065d5158c20006dc5158c20006df4158c200069f4158c20006de4158c20006dd4158c200069d4158c20006dc4158c2002edf2158c2002ede2158c2002edd2158c2002edc2158c20026df7058c20026de7058c20026dd7058c20026dc7058c20026df5058c20026de5058c20026dd5058c20026dc5058c20026df4058c20026de4058c20026dd4058c20026dc4058c20026df2058c20026cf2058c20026de2058c20026dd2058c20026cd2058c20026dc2058c20026df1058c20026de1058c20026dd1058c20026dc1058c20006f77558420006f67558420006767558420006f57558420006757558420006f47558420006f77458420006f67458420006b67458420006f57458420006b57458420006f47458420006f75458420006f65458420006f55458420006f45458420006f77358420006f67358420006f57358420006f47358420006f75358420006f65358420006f55358420006f45358420006f74358420006f64358420006f54358420006f4435842002ef7725842002ef6725842002ef5725842002ef4725842002ef7525842002ef6525842002ef5525842002ef4525842002ef7425842002ef6425842002ef5425842002ef4425842002ef7325842002ef6325842002ef5325842002ef43258420026f77058420026f67058420026f57058420026f47058420026f75058420026f65058420026f55058420026f45058420026f74058420026f64058420026f54058420026f44058420026f73058420026f63058420026f53058420026f43058420026f72058420026e72058420026f62058420026f22058420026f52058420026e5205842002ef12058420026f42058420
  | 1 => 0x94200067c71594200067f41594200063f41594200067e41594200067d41594200063d41594200067c41594200067f31594200067e31594200067d31594200067c315942002e7f215942002e7e215942002e7d215942002e7c21594200267f70594200267e70594200267d70594200267c70594200267f40594200267e40594200267d40594200267c40594200267f30594200267e30594200267d30594200267c30594200267f20594200267e20594200267d20594200267c20594200267f10594200267e10594200267d10594200267c1059420006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006be5359020006bd5359020006bc535902002ebf725902002ebe725902002ebd725902002ebc725902002ebf525902002ebe525902002ebd525902002ebc525902002ebf325902002ebe325902002ebd325902002ebc3259020006bf7159020004bf7159020006be7159020006bd7159020004bd7159020006bc7159020006bf51590200063f5159020006be5159020006bd51590200063d5159020006bc5159020006bf3159020006be3159020006bd3159020006bc315902002ebf215902002ebe215902002ebd215902002ebc2159020026bf7059020026be7059020026bd7059020026bc7059020026bf5059020026be5059020026bd5059020026bc5059020026bf3059020026be3059020026bd3059020026bc3059020026bf2059020026be2059020026bd2059020026bc2059020026bf1059020026be1059020026bd1059020026bc105902004edf7598c2004ede7598c2004edd7598c2004edc7598c2004edf7498c2004ede7498c2004edd7498c2004edc7498c20006df5498c20006de5498c20006dd5498c20006dc5498c2002edf7298c2002ede7298c2002edd7298c2002edc7298c2002edf5298c2002ede5298c2002edd5298c2002edc5298c2002edf4298c2002ede4298c2002edd4298c2002edc4298c2004edf7198c2004ede7198c2004edd7198c2004edc7198c20006df5198c200065f5198c20006de5198c20006dd5198c200065d5198c20006dc5198c20006df4198c200069f4198c20006de4198c20006dd4198c200069d4198c20006dc4198c2002edf2198c2002ede2198c2002edd2198c2002edc2198c20026df7098c20026de7098c20026dd7098c20026dc7098c20026df5098c20026de5098c20026dd5098c20026dc5098c20026df4098c20026de4098c20026dd4098c20026dc4098c20026df2098c20026de2098c20026dd2098c20026dc2098c20026df1098c20026de1098c20026dd1098c20026dc1098c20004ff7558c2001cfe7558c20004fd7558c2001cfc7558c20004ff7458c20014fe7458c20004fd7458c20014f
  | 2 => 0x4ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2000cfe7158d20004fd7158d2000cfc7158d20006f47158d2000cf47158d200067f5158d200067d5158d20006bf4158d20006bd4158d20006df3158d20006dd3158d20006ef2158d20006ed2158d20004ff7058d20006fb7058d20006fa1058d20006f91058d20004fe7618d200067f6518d200067c6518d20006bf6418d20006bc6418d2004ede6318d20006dd6318d20024fe76cc920024fc76cc9200657e75cc9200057d75cc9200067f65cc9201567c65cc92005dbe74cc920005bd74cc920006bf64cc92014ebc64cc920006df63cc92004edc63cc920025fa70cc920005f970cc92002fe820cc920005ee768c92002eee768c92002f6e758c92002f6d758c9200076f658c9201976c658c92002fae748c92002fad748c920007af648c92018fac648c920165ed738c92004eee638c92004eec638c92002def718c920185ed718c92017eef618c92017eed618c92017f6f518c92017f6d518c92017faf418c92017fad418c920025ee708c920025ec708c92002eef608c92002feb608c92017fea108c92017fe9108c920024fc764c9200067f654c9201267c654c920006bf644c92011ebc644c920006df634c92004edc634c92002fcc324c920005fb704c920025f8704c920025ec764c92004eec764c920024ec764c9200076f654c9201776c654c920007af644c92016fac644c92002def734c92002fcf734c920007cf634c92004eee634c92004eec634c920007cc634c92004ecc634c920165ef714c920165ed714c92015eef614c92015eed614c92015f6f514c92015f6d514c92015faf414c92015fad414c92015fcf314c92015fcd314c920007eb704c920025ee704c920025ec704c920007e8704c920025e8704c92002eef604c92002feb604c92015fea104c92015fe9104c92002cfe76cc12002cfc76cc1200067f65cc1200f67c65cc120006bf64cc1200eebc64cc120006df63cc12004edc63cc12002dee72cc120005ed72cc120007cd32cc120027e820cc12004cff764c120004fd764c12002cfc764c1200057f754c1200657c754c1200067f654c1200c67c654c120005bf744c12005dbc744c120006bf644c1200bebc644c120006df634c12004edc634c120005ef724c12002dec724c120007cd324c1200067f74594200067e74594200067d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067d43594200067c435942002e7f725942002e7e725942002e7d725942002e7c725942002e7f425942002e7e425942002e7d425942002e7c425942002e7f325942002e7e325942002e7d325942002e7c32594200067f71594200047f71594200067e71594200067d71594200047d715
  | 3 => 0xe70d95200667d70d95201ae7c70d95200067f40d95201ae7e40d95200067d40d95201ae7c40d95201ae7e30d95201ae7c30d95201b67f20d95201ae7e20d95200667d20d95201ae7c20d95200067f10d95201ae7e10d95200067d10d95201ae7c10d952005dbe76d912005ebe76d9120014be76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120005bf71d9120005bd71d9120006bf61d9120006be61d9120006bd61d9120006bc61d91200073f51d91200073d51d9120007af21d9120007ad21d91201a7bb20d912019fae20d912019fac20d91201a7b820d9120007ba10d9120007b910d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d912019ebf72d91201a6be72d912005ebd72d91201a6bc72d9120006bf52d91201a6be52d9120006bd52d91201a6bc52d91201a6be32d91201a6bc32d9120006bf71d9120004bf71d9120006be71d9120006bd71d9120004bd71d9120006bc71d9120006bf51d91200063f51d9120006be51d9120006bd51d91200063d51d9120006bc51d9120006bf31d9120006be31d9120006bd31d9120006bc31d91201a6bf21d9120006be21d9120006bd21d91201a6bc21d91201a6bf70d912019ebe70d912005ebd70d912019ebc70d9120006bf50d912019ebe50d9120006bd50d912019ebc50d912019ebe30d912019ebc30d91201a6bf20d912019ebe20d912005ebd20d912019ebc20d9120006bf10d912019ebe10d9120006bd10d912019ebc10d912004cfe76d8d200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d2002cfe72d8d2002cfc72d8d20004ff71d8d2000cfe71d8d20004fd71d8d2000cfc71d8d200067f51d8d200067d51d8d20006bf41d8d20006bd41d8d20006de31d8d20006dc31d8d20006ef21d8d20006ed21d8d20024fe70d8d20024fc70d8d20006fa10d8d20006f910d8d200657e7598d200057d7598d200067f6598d200067c6598d2005dbe7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d200057f7558d200657c7558d200067f6558d200067c6558d20005bf7458d2005dbc7458d20006bf6458d20006bc6458d20005f77158d20055f47158d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d20006df7358d20
  | 4 => 0x8f20004fd7458f20014fc7458f2002edf7358f20024fc7258f2002ede3258f2002edc3258f20004ff7158f2000cfe7158f20004fd7158f2000cfc7158f200067f5158f200067d5158f20006bf4158f20006bd4158f20006df3158f20006dd3158f2002eef2158f20006ed2158f2002def764cb20006ef764cb2002fcf734cb2002fcf634cb2004eee634cb2002eec634cb2002fcc634cb2002ecc634cb201c5ef714cb201c5ed714cb2002eef614cb201beed614cb201bf6f514cb201bf6d514cb201bfaf414cb201bfad414cb201bfcf314cb201bfcd314cb20025ee704cb20025ec704cb2004ede63cc320006dd63cc32002dee72cc320005ed72cc320007cd32cc32004cff764c3200057f754c3200957c754c320005bf744c32008dbc744c32004ede634c320006dd634c320005ef724c32002dec724c320007cd324c320027d8304c320004ff7558e200067f7558e200047f7558e2001cfe7558e20004fd7558e2001cfc7558e200067c7558e2001c7c7558e20004ff7458e20006bf7458e20004bf7458e20014fe7458e20004fd7458e20014fc7458e20006bc7458e20014bc7458e20026df7358e20004ff7158e2000cfe7158e20004fd7158e2000cfc7158e200067f5158e200067d5158e20006bf4158e20006bd4158e20006df3158e20006dd3158e20024fc7058e20026de3058e20026dc3058e20026ef2058e20026ed2058e20026fa1058e20006f91058e2007d7e75cca200057d75cca20075be74cca20005bd74cca2004ede63cca20006dd63cca20025fa70cca20005f970cca2004cff764ca2004ede634ca20006dd634ca2002fcc324ca20005fb704ca20025f8704ca200657e76d95200667e76d952001c7e76d95200067f64d95200067e64d95200067d64d95200067c64d95200073c64d95200063c64d95200057f71d95200057d71d95200067f61d95200067e61d95200067d61d95200067c61d95200073f41d95200073d41d95200076f21d95200076d21d95201b77b20d95201af6e20d95201af6c20d95201b77820d95200077a10d95200077910d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95201ae7f72d95201b67e72d95200667d72d95201b67c72d95200067f42d95201b67e42d95200067d42d95201b67c42d95201b67e32d95201b67c32d95200067f71d95200047f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200063f41d95200067e41d95200067d41d95200063d41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95201b67f21d95200067e21d95200067d21d95201b67c21d95201b67f70d95201ae7
  | 5 => 0x4ff7458830014fe7458830004fd7458830014fc7458830026ef7258830006ef5258830006ee5258830006ed5258830006ec5258830006ef4258830006ee4258830006ed4258830006ec425883004eef325883004eec3258830004ff715883000cfe7158830004fd715883000cfc71588300067f51588300067d5158830006bf4158830006bd4158830006ef2158830006ee2158830006ed2158830006ec2158830024ff7058830024fd7058830026df3058830026dd3058830026ee2058830026ec2058830006ef7558830006ee7558830006ed7558830006ec7558830006ef7458830006ee7458830006ed7458830006ec7458830006ef5458830006ee5458830006ed5458830006ec545883004eef735883004eee735883004eec735883004eef535883004eee535883004eed535883004eec535883004eef435883004eee435883004eed435883004eec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef51588300066f5158830006ee5158830006ed51588300066d5158830006ec5158830006ef4158830006af4158830006ee4158830006ed4158830006ad4158830006ec415883004eef315883004eee315883004eed315883004eec3158830026ef7058830026ee7058830026ec7058830026ef5058830026ee5058830026ed5058830026ec5058830026ef4058830026ee4058830026ed4058830026ec4058830026ef3058830026cf3058830026ee3058830026ed3058830026cd3058830026ec3058830026ef1058830026ee1058830026ed1058830026ec1058830006f77558430006f67558430006767558430006f57558430006757558430006f47558430006f77458430006f67458430006b67458430006f57458430006b57458430006f47458430006f75458430006f65458430006f55458430006f4545843004ef7735843004ef6735843004ef5735843004ef4735843004ef7535843004ef6535843004ef5535843004ef4535843004ef7435843004ef6435843004ef5435843004ef44358430006f77258430006f67258430006f57258430006f47258430006f75258430006f65258430006f55258430006f45258430006f74258430006f64258430006f54258430006f4425843004ef7325843004ef6325843004ef5325843004ef43258430026f77058430026f67058430026f57058430026f47058430026f75058430026f65058430026f55058430026f45058430026f74058430026f64058430026f54058430026f44058430026f73058430026d73058430026f63058430026f23058430026f53058430026d5305843004ef13058430026f43058430026f72058430026f62058430026f52058430026f42058430004ff7558f2001cfe7558f20004fd7558f2001cfc7558f20004ff7458f20014fe745
  | 6 => 0xf71594300067e71594300067d71594300047d71594300067c71594300067f41594300063f41594300067e41594300067d41594300063d41594300067c415943004e7f315943004e7e315943004e7d315943004e7c31594300067f21594300067e21594300067d21594300067c21594300267f70594300267e70594300267d70594300267c70594300267f40594300267e40594300267d40594300267c40594300267f30594300267e30594300267d30594300267c30594300267f20594300267e20594300267d20594300267c20594300267f10594300267e10594300267d10594300267c1059430006bf7559030006be7559030006bd7559030006bc755903004ebf735903004ebe735903004ebd735903004ebc735903004ebf535903004ebe535903004ebd535903004ebc5359030006bf7259030006be7259030006bd7259030006bc7259030006bf5259030006be5259030006bd5259030006bc525903004ebf325903004ebe325903004ebd325903004ebc3259030006bf7159030004bf7159030006be7159030006bd7159030004bd7159030006bc7159030006bf51590300063f5159030006be5159030006bd51590300063d5159030006bc515903004ebf315903004ebe315903004ebd315903004ebc3159030006bf2159030006be2159030006bd2159030006bc2159030026bf7059030026be7059030026bd7059030026bc7059030026bf5059030026be5059030026bd5059030026bc5059030026bf3059030026be3059030026bd3059030026bc3059030026bf2059030026be2059030026bd2059030026bc2059030026bf1059030026be1059030026bd1059030026bc105903002eef759883002eee759883002eed759883002eec759883002eef749883002eee749883002eed749883002eec7498830006ef5498830006ee5498830006ed5498830006ec549883002eef739883002eee739883002eed739883002eec739883004eef539883004eee539883004eed539883004eec539883004eef439883004eee439883004eed439883004eec439883002eef719883002eee719883002eed719883002eec7198830006ef51988300066f5198830006ee5198830006ed51988300066d5198830006ec5198830006ef4198830006af4198830006ee4198830006ed4198830006ad4198830006ec419883004eef319883004eee319883004eed319883004eec3198830026ef7098830026ee7098830026ed7098830026ec7098830026ef5098830026ee5098830026ed5098830026ec5098830026ef4098830026ee4098830026ed4098830026ec4098830026ef3098830026ee3098830026ed3098830026ec3098830026ef1098830026ee1098830026ed1098830026ec1098830004ff755883001cfe7558830004fd755883001cfc7558830
  | 7 => 0x9130216bf30d913020ebe30d91300bebd30d913020ebc30d913020ebe20d913020ebc20d9130006bf10d913020ebe10d9130006bd10d913020ebc10d91300067f65d89300067c65d8930006bf64d8930006bc64d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d8930004ff71d893000cfe71d8930004fd71d893000cfc71d89300067f51d89300067d51d8930006bf41d8930006bd41d8930006df31d8930006dd31d8930006ee21d8930006ec21d8930024fe70d8930024fc70d8930006fa10d8930006f910d89300c57e75989300057d75989300067f65989300067c65989300bdbe7498930005bd7498930006bf6498930006bc6498930006ef62989300057f75589300c57c75589300067f65589300067c6558930005bf74589300bdbc7458930006bf6458930006bc6458930005f771589300b5f471589300067f65189300067c6518930006bf6418930006bc641893002eee6218930006ed6218930005de76cc93004ede76cc93004f5e75cc93004f5d75cc9300075f65cc9302075c65cc93004f9e74cc93004f9d74cc9300079f64cc9301ff9c64cc93002ede62cc93002edc62cc93004ddf71cc9301f5dd71cc9301eedf61cc9301eedd61cc9301ef5f51cc9301ef5d51cc9301ef9f41cc9301ef9d41cc930025de70cc930025dc70cc93004edf60cc93004fdb60cc9301efda10cc9301efd910cc930024fe768c9300c57e758c9300057d758c9300067f658c93013e7c658c9300bdbe748c930005bd748c930006bf648c930136bc648c9301d5dd738c930006ef628c93002eec628c930025fa708c930005f9708c93004fd8308c930024fc764c9300067f654c9301267c654c930006bf644c93011ebc644c930006ef624c93002eec624c93004fcc324c930005fb704c930025f8704c930024dc764c9300075f654c9301e75c654c9300079f644c9301df9c644c93004ddf724c93004fcf724c930007cf624c93002ede624c93002edc624c930007cc624c93002ecc624c9301d5df714c9301d5dd714c9301cedf614c9301cedd614c9301cf5f514c9301cf5d514c9301cf9f414c9301cf9d414c9301cfcf214c9301cfcd214c930007db704c930025de704c930025dc704c930007d8704c930025d8704c93004edf604c93004fdb604c9301cfda104c9301cfd9104c9300067f74594300067e74594300067d74594300067c745943004e7f735943004e7e735943004e7d735943004e7c735943004e7f435943004e7e435943004e7d435943004e7c43594300067f72594300067e72594300067d72594300067c72594300067f42594300067e42594300067d42594300067c425943004e7f325943004e7e325943004e7d325943004e7c32594300067f71594300047
  | 8 => 0x6ed628ca30025fa708ca30005f9708ca3002cff764ca3002eee624ca30006ed624ca3004fcc324ca30005fb704ca30025f8704ca300c57e76d95300c67e76d953001c7e76d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95300057f71d95300057d71d95300067f61d95300067e61d95300067d61d95300067c61d95300073f41d95300073d41d95300075f31d95300075d31d95302277b30d953021f5e30d953021f5c30d95302277830d95300077a10d95300077910d95300067f74d95300067e74d95300067d74d95300067c74d953021e7f73d95302267e73d95300c67d73d95302267c73d95300067f43d95302267e43d95300067d43d95302267c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95302267f32d95302267c32d95300067f71d95300047f71d95300067e71d95300067d71d95300047d71d95300067c71d95300067f41d95300063f41d95300067e41d95300067d41d95300063d41d95300067c41d95302267f31d95300067e31d95300067d31d95302267c31d95300067f21d95300067e21d95300067d21d95300067c21d95302267f70d953021e7e70d95300c67d70d953021e7c70d95300067f40d953021e7e40d95300067d40d953021e7c40d95302267f30d953021e7e30d95300c67d30d953021e7c30d953021e7e20d953021e7c20d95300067f10d953021e7e10d95300067d10d953021e7c10d95300bdbe76d91300bebe76d9130014be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130005bf71d9130005bd71d9130006bf61d9130006be61d9130006bd61d9130006bc61d91300073f51d91300073d51d91300079f31d91300079d31d9130217bb30d913020f9e30d913020f9c30d9130217b830d9130007ba10d9130007b910d9130006bf75d9130006be75d9130006bd75d9130006bc75d913020ebf73d9130216be73d91300bebd73d9130216bc73d9130006bf53d9130216be53d9130006bd53d9130216bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d9130216bf32d9130216bc32d9130006bf71d9130004bf71d9130006be71d9130006bd71d9130004bd71d9130006bc71d9130006bf51d91300063f51d9130006be51d9130006bd51d91300063d51d9130006bc51d9130216bf31d9130006be31d9130006bd31d9130216bc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d9130216bf70d913020ebe70d91300bebd70d913020ebc70d9130006bf50d913020ebe50d9130006bd50d913020ebc50d
  | 9 => 0xe644c83202fcd644c83202fcc644c832247cf544c832247ce544c832247cd544c832247cc544c832257cf714c83223fce714c832257cd714c83223fcc714c83202fcf614c83202ecf614c83202fce614c83202fcd614c83223ecd614c83202fcc614c83223fcf514c83223f4f514c83223fce514c83223fcd514c83223f4d514c83223fcc514c83223fcf414c83223f8f414c83223fce414c83223fcd414c83223f8d414c83223fcc414c832007cf704c832007ce704c832007cd704c832007cc704c83202fcf604c83202fce604c83202fcd604c83202fcc604c83224fcf504c83224fce504c83224fcd504c83224fcc504c832247cf404c832247ce404c832247cd404c832247cc404c83223fcf104c83223fce104c83223fcd104c83223fcc104c832004ff75580320067f75580320047f755803201cfe7558032004fd755803201cfc75580320067c755803201c7c7558032004ff7458032006bf7458032004bf7458032014fe7458032004fd7458032014fc7458032006bc7458032014bc745803202edf325803202eee325803202edd325803204eed3258032006cd3258032004ff715803200cfe7158032004fd715803200cfc71580320067f51580320067d5158032006bf4158032006bd415803202efb7058032006fa5058032006f95058032006fa4058032006f9405803204efb305803204ef8305803202efb205803202ef82058032006fa1058032006f91058032004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b30014fe7458b30004fd7458b30014fc7458b30024fc7358b3004eef7258b3004eef3258b3004eec3258b30004ff7158b3000cfe7158b30004fd7158b3000cfc7158b300067f5158b300067d5158b30006bf4158b30006bd4158b3004edf3158b30006dd3158b30006ef2158b30006ed2158b3004ddf764cb30006df764cb3004fcf724cb3004fcf624cb3002ede624cb3002edc624cb3004fcc624cb30235df714cb30235dd714cb3004edf614cb3022edd614cb3022f5f514cb3022f5d514cb3022f9f414cb3022f9d414cb3022fcf214cb3022fcd214cb30025de704cb30025dc704cb30004ff7558a300067f7558a300047f7558a3001cfe7558a30004fd7558a3001cfc7558a300067c7558a3001c7c7558a30004ff7458a30006bf7458a30004bf7458a30014fe7458a30004fd7458a30014fc7458a30006bc7458a30014bc7458a30026ef7258a30004ff7158a3000cfe7158a30004fd7158a3000cfc7158a300067f5158a300067d5158a30006bf4158a30006bd4158a30006ef2158a30006ed2158a30024fc7058a30026df3058a30026dd3058a30026ee2058a30026ec2058a30026fa1058a30006f91058a300dd7e758ca300057d758ca300d5be748ca30005bd748ca3002eee628ca30
  | 10 => 0x96320063f41596320067e41596320067d41596320063d41596320067c41596322767f31596320067e31596320067d31596322767c315963202e7f215963202e7e215963202e7d215963202e7c21596320067f70596320067e70596320067d70596320067c70596320067f40596320067e40596320067d40596320067c40596322767f30596322767c305963202e7f205963202e7e205963202e7d205963202e7c20596320067f10596320067e10596320067d10596320067c1059632006bf7559232006be7559232006bd7559232006bc7559232136bf735923226ebe7359232006bd735923226ebc7359232006bf535923226ebe5359232006bd535923226ebc535923202ebf725923202ebe725923202ebd725923202ebc725923202ebf525923202ebe525923202ebd525923202ebc525923202ebf325923202ebe325923202ebd325923202ebc3259232006bf7159232004bf7159232006be7159232006bd7159232004bd7159232006bc7159232006bf51592320063f5159232006be5159232006bd51592320063d5159232006bc515923226ebf3159232006be3159232006bd315923226ebc315923202ebf215923202ebe215923202ebd215923202ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232006bc505923226ebf305923226ebc305923202ebf205923202ebe205923202ebd205923202ebc2059232006bf1059232006be1059232006bd1059232006bc1059232004ff755823201cfe7558232004fd755823201cfc7558232004ff7458232014fe7458232004fd7458232014fc745823202cfc725823202edf325823202edd3258232004ff715823200cfe7158232004fd715823200cfc71582320067f51582320067d5158232006bf4158232006bd415823202eef2158232006ed215823202efb705823202efb205823202ef82058232006fa1058232006f91058232004ff75d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d8132004ff71d813200cfe71d8132004fd71d813200cfc71d81320067f51d81320067d51d8132006bf41d8132006bd41d8132006df31d8132006dd31d8132006ef21d8132006ed21d8132006fb60981320057f75581321257c7558132005bf745813211dbc7458132005f77158132115f471581321257e75181320057d751813211dbe7418132005bd7418132115f67118132005f57118132026fa6018132006f9601813202fcf764c83202dcf764c832006cf764c832267cf754c83224fce754c832267cd754c83224fcc754c83202fcf654c83202fce654c83202fcd654c83202fcc654c83225fcf744c832247ce744c83225fcd744c832247cc744c83202fcf644c83202fc
  | 11 => 0x4e7d435973204e7c43597321567f72597322867e72597320067d72597322867c72597320067f42597322867e42597320067d42597322867c425973204e7f325973204e7e325973204e7d325973204e7c32597320067f71597320047f71597320067e71597320067d71597320047d71597320067c71597320067f41597320063f41597320067e41597320067d41597320063d41597320067c415973204e7f315973204e7e315973204e7d315973204e7c31597322867f21597320067e21597320067d21597322867c21597320067f70597320067e70597320067d70597320067c70597320067f40597320067e40597320067d40597320067c405973204e7f305973204e7e305973204e7d305973204e7c30597322867f20597322867c20597320067f10597320067e10597320067d10597320067c1059732006bf7559332006be7559332006bd7559332006bc755933204ebf735933204ebe735933204ebd735933204ebc735933204ebf535933204ebe535933204ebd535933204ebc535933214ebf725933227ebe7259332006bd725933227ebc7259332006bf525933227ebe5259332006bd525933227ebc525933204ebf325933204ebe325933204ebd325933204ebc3259332006bf7159332004bf7159332006be7159332006bd7159332004bd7159332006bc7159332006bf51593320063f5159332006be5159332006bd51593320063d5159332006bc515933204ebf315933204ebe315933204ebd315933204ebc315933227ebf2159332006be2159332006bd215933227ebc2159332006bf7059332006be7059332006bd7059332006bc7059332006bf5059332006be5059332006bd5059332006bc505933204ebf305933204ebe305933204ebd305933204ebc305933227ebf205933227ebc2059332006bf1059332006be1059332006bd1059332006bc1059332004ff755833201cfe7558332004fd755833201cfc7558332004ff7458332014fe7458332004fd7458332014fc745833202cfc735833204eee325833204eed3258332004ff715833200cfe7158332004fd715833200cfc71583320067f51583320067d5158332006bf4158332006bd415833204edf3158332006dd315833204efb705833204efb305833204ef83058332006fa1058332006f910583320067f74596320067e74596320067d74596320067c745963213e7f73596322767e73596320067d73596322767c73596320067f43596322767e43596320067d43596322767c435963202e7f725963202e7e725963202e7d725963202e7c725963202e7f425963202e7e425963202e7d425963202e7c425963202e7f325963202e7e325963202e7d325963202e7c32596320067f71596320047f71596320067e71596320067d71596320047d71596320067c71596320067f415
  | 12 => 0x600100000000300000000000500301500000100300200100000100100700100000300000200100900100000700300c00000000600200000100000600100000000400600500000000500000000800100100400100100100600200300000200000700000000700100000200700200200000400000000100000100300500500100000200000000000400700000300300100200400000000000100100500600000500800200000200200101f00000100000000200300200100100600000000001100301000000000400000300700300100200700100200400000e01100000300400000000b00100700000100600b00100600100100000000200000100000400100400700000500500200f00100000800000000000100000000000200000300700000100000200000100000100000000c00600100200000100900200000200700000400000000500200200000300000100000000500000400000000300000100000200400000100500300000000100200100900100d00700000000000300000000900300000000400200100000000100201200500000000200100000000000600400300200000200000000a00a00100200000100200700000a00000300d00000000000000c00400000000000200300900200100000000100000100900000100200000000300000100500200000200000200300400100000200500100000100000000101600200000a00700100200900200500000300800000300000300500100400700000000200200300200000100a00000000100000200300c01000100100400300800700200000000300200100100100000800100000000100000100200600000300000100800300000000000000000400000000000000300000000100000000300600300200c00200200500000100300000400700600200d00000100700300000300000000200000000100000100a00200100100600200400c00300200000300101700a00100000000100c00000100000f00300300000000100000300000500200300100000000300300000600000000200d00000700200f00000600600300100600400000000000500000500300700000300000000800000000100200000000500200000f00000200c00100000000100400000000100200000000000001b00500000000000600001200200100400100000000000000200100400600400200000700000200000400300400000000000600200200000d0000000030000000000000060020000000080010010000000060250000070040000010000000020030010000020000020000010020030060000030010010040030010010010000010000050020067f74597320067e74597320067d74597320067c745973204e7f735973204e7e735973204e7d735973204e7c735973204e7f435973204e7e4359732
  | 13 => 0x800000000000d0ca800058d000000000000000000000005ba1c080005700002148cb40007f12eb9ca00003920000b580006861da11501e400012d14d8c72000000067400000000000000001183858d9cf140eb06e0bc89084592078b240000000001ad00000003d4800099a000000000000047428609acf581fd35e0b4cc7a0c339006d074e11b27e11b838220500000000f2257000048400036f14e80000001c22569c3445c732174116c40c0980000a7099c2db3f481487e00002ac000045e6cd000006c00009700000006e000020007ac1042ff0260000000000000000000000000000010060013120000d040100d5800000000000000000000001f780000000000a8801800000000000000002fe1f3063800011a36397ac33e00000003fcce84e40d11f9c6c24a8000000000000006f000095800000000007a400015b125400835e39091bce985c202213701900000000d087ae0001f400003f800006c197897c45031b000029e00000003b0e040002cf84a400067a00000000005bf000000000000000000000000003eb92fc9884de0000640000177314071c3e04d503b92c81f600000015d400007535c0000bd80003ed975831800000000000006f41c592340fc08d000000000000000004fc4a600000c8000a08000151800000002318200000007a43e916f4bb0000222125070a5051f900009e25440ef9be07bc20b15e0000000000000000000036300000001de5073258de80f663a00009e0a4810b1d682683ba0863a48ab008275e24e814c4286b909d04dc13870917d9e1cc2e2441a880d498441c3528ae8e3e11e05691b4f386832d69c941d20180cd800000047331d9cc4d9401100015640001083d89d2c59419c3c289f4000000000029c0001873ec87a00007c605d000000049a0001550304070000000000017f0000000270000000050800039f00016a00006cb00000000ae02f161005832800015400004947a11c7000000001e00005f80000000a091580000001fd11b0e3c00000000244c04d138193948a227a0001ed89a412d2e285b00000002a38000c8e0b32211fc0f464aa0d6949cebe6e001c14647fa00000014bc00000000000004ba34d000169c9a80000001dd43260003550000000000047800000072d2178a408f6788000106c6600000001ad4b5e00000013280006a000000004a40001e280009ea00000000000001b60d1913452c00000001c80000000000e581723d429f89e400000000000000b83911a015a47e21ec0100fac9005660b70ce075c6ee056034ca1065a0000d40c360001f61edc0000000000000000027000132400061a0001adc00000000100500000000100000000800100800700200d00000000000000000100000700000000000000200000100300000c0000010030060000000040000010070050
  | 14 => 0x8447a00000000e480001a2000000000000011c83ec2a201f16e40000503b2800000000000000000006c51bb0000dbc29f00000005c610f3228000b3c1cd3938000cd67bc0bc90b80000591b59ac022470634017e801c618000000000047d00013400005b600009ecb3a6892bd00000000000000000000000000002cc5a30315006140001023cd00000000000001590e6662e26e800000000032e8000f880000000f1c0006e103180006005e915f00000002a73548958f723540000000bca0001ed8fe40ec000055859000000000002040001d300000000006933eb17d8c2026a313800067200000000000000001fa0f18bda0002278000c220000001c040002580000f2400000000000000003ea3360000e8c0000e486780004a7000000000055a14004f8834000000005000000000000000002831a080006e80003e40000a40000000000000037e00001940000003e68000000593343800000000019f80000d050d3a20e7400000000015e43c20c734a800000059939a1b9c6a44d80000000cb200000000007560001c01e6cdd054e0000768d3050632e04cc13202427916b06b27261d4195c8f854d29e96600006121c8000000010a1cd8324c9442430580006e600000009346d80000001f4434a0000000000a700003c0909cd8800024e000000000000000006200000000000000000000021c00031c0001184e264ef00000008740000000000a467163b09c643140002d198fc77a46409c889800038a2ed000010022819a80000000003b48de40000000000af43706dd000066066c4381a48d2800000000000cc8ea00035b0d88000243367839453c000000000096831637982bc0000000001dc4f7422900006bc9be80029e070cd7e000000000000000005f0000eec41f1978ca00000000000908ff274708387540007420000588f8a42815a0efc0000000da800000000024c934c000000137000087a60a08e1cfc8801682188bbc7842eb219000000038c0720000dac08e042042495c00017c1a8cfb4161000000000055300014740005170000b708602f51ec107400049b0000000a8c00000000006f628233807fc0000000591808bc43572ae800013c0390e780000000000001d548285881349c200000003579750c882413c011d8e342dd17b89380000000dc80000000003f2148800000030e08905e800000000001c65cd1709e5c87800000018bc81a0000ec80000000002c0838400008508e800000000025797bc00045c0001c380005de0000b3400027600000000001ed0a61aac56600000009bc41c0fe08c816caae0003570808802000000000000000030f9a8800040800005e0376000000000000009b0000c9c00000020a8094ce200033c15d01ce5283ce95203f42f300000004fc05d27d088800000019e0830d8000005f
  | 15 => 0xffcdf62a1223999c64a00025b10e49c47e136a9e2c4c81e52be051cdf46dc2be9a4088c792036800000075b00000000004110000ef02e600000006346aa4b80ae0000182000000089c0000001f480006580000000740af60000a4800000010000000000003e32e78000000000000000000026d25807206280000001f2c00000010190cc00000000000000000000000000b6a11f0001fd40005e80000000000000000102400076b00002240002cc263000087c5311d1000000000000014549f0000000000000000038e0e60e9e000162a01c0002301d097e4ca600000516dc5165dd0fa00000007840c88168000000000000010629400000000000000fa80002ba5fc0000c9000000000000000000001ab0000aa269a1498000a6e0000000c20000000000000000025100009981c000020c82802f434b00000000000002f08c24476000000000000075425a80007f663e110881089c60106d8ee831216a1851f1c20212e01409500001aa3d381b8f9800002a000035861d1f697240000001118000000497159154038c0000001b38e1400035f1ac43c80260c91af403800034201ccb6401222c00000f000000000000000000001fccd760000991aa09dc0001491dbc00069b2970000b0812239c800000000017600000000000109880000000000000000072e0001ce000071d00000008ce0bc3ba19bc000000000000000000027b98a40000000000cc81c40000ad8e980001c0000031400000000005940004c80000000e080002290d1845a0000d000000000000001688a1c00000004c00000000001fc83482e909018a80000001f280000004710000c4ce4625e34680009b6000000179cc180003c880001187520000984128790000048c0aa0cf2c48e4c43409629913ac12a76419b90acbfe43b0001a78d0a3c80ad1b640000001e818349625450a180f100a000144804c0000000001e0c0004d60001fe08186ac00000000004b914099dc5cc3652f80000fa60000000fcc75e00032d80000006d80000000000637000198400000015b80000000000000b7c0003170000000dc616d000079c00000000005800000001fc0000c4a6032e411a01fa0d100004a800053300006201a804009d887cf1820d382914c80a06c2491b900000003189fecefa00000000000000003cf9df8b66000092071034e06b3f1953c00048f2818ad4cda0002ca81d08040000f49d200003750001e7846200000000005a20000000000b9800000000000620000000000ff4000119008807a0000378b4842c60500016a426214b1ee1508fc00003b4000000023820b828400000000000000000003cb0000b2c4a51a190940002a500e80000004ea000000000023a3bc1498c286d3000066876067312c8a44eb076000000a40000000a4000000000000011a4c6a000000000000
  | 16 => 0x15f244156cf5a3533788afcc980d719093a00000000000000000753000059c0001b222b9f70000000000065c0003a300000007c8000000000000065600000007fc2a900019d86c86323ec140400056b3b707ec0001ae00000004726881230c745b20001001280faa30d0ac9d5c4c6298142189800051f2908000ed80002e5891458054c0000000ea243f000000000014010f1e340004da0670000000000000174c7c0000000000000000000000000006d20e506a45dc0000001df000000009e800007600000000000000000f88000d7438311f0eb08307eb00000000000001f08000d667c12f700005880003608ba8b880000001f088d46630001684e820000000c980006eb02c0c146ee0480be01a86da5ae29800000000b500005d0a2600011e15a02a60001c10d80f8000027602d0f6068c39a96ac7886da16a800050e37c0ba843400057700012ec00000039f000037e6c214415e05a056502f000030849f000000000022c0000000e7664e0000000f12000000162c0000000000000000000000000000000034700005620420c089940000002f30000c840000000000b822e736d943c86e57f00000000007180001dc8a3656e00009300000cc0001cf0a520c237e112059008a000000041e0000000000000000157000000000025200000000000000000f280003021d0c000155119800096e1141ca87146742551948000b0e62c000076c000000000000000000000006586dc0c400011aca86000000190c69c0000000000a6a00016f000000000027f800000000000000000000f5000000098012b05180000001e60000000dea09110d80005f200007a121cc78000307800000000011587b80000001d900000000001ef999005631124319504e224f2b18000c660000d4000039827000000000000000000000a0400000014500004cc00000000000000000000bc650a0631eb83de00036609b055641000010a8dae3b80000000ce4000000000000000000000000c400000000000000000000000000207000176c00077000000006fa00014b80008be51a2849fbc4226e63f111fc944692000056000071100017e0b861173348b1cf662a400000003325673bd06f0e3653e0ab8e64ab85d031a1d98b0a37806019a8ad40000000368000000000138c0004c70001efcb1e14a2020000000000023800000007f1c200007ba00000000006045900000000ada00036a00000000df023086046c00014d80000002e533e800002e0002ca082425e2500000000e7400028f19f01f81e211e90d439c52d00017cc0001ea26c80003c64cf1e58cd00000a927f090091c000000000076e00000000000005b81b48000ae03480001f7c00000000000000000003a8041800000000000000002fd000000000036600000000000600001fd1012000000126000000000
  | 17 => 0xbd8e9000000000017ecaaa0002889ac872834516c1fa00000000000ecccaa4ab000000013a0d600017d40003d900000000005a5379171c67c72904800000007402c000007820000000000176000055000000005612480000000002d200000001fe3330540000000000000000000000000000000001df00008263ee0000000d141950000000fba00000000000000000000000000000000000061e000000128ca96000000000000035b11a80fcf7a00037105c000064d05b8000ad875a39b80000001270001f502507101e5010c34c6130001bb00cc00000000000002372df0c300001e025e86ccf043f6034997c64445e27480000000000000dc40001262bb00000000002659a589426603ef03b82de0b809e15bceee4e103e00000005a00001a648820000000000c2a7560000cacc322ed0000ac00000bd17e022ce7a00000018ac0000003530000ffc0360000000a201f83c3000000007a3c785ac6301b00a300003b80f1000040c1b25820000a3c2085710001c50a8231e231000073c0340dd12447a248335215586020003fb11f82cc34c3bf96a80c222530700000000001db1c5c0004650000000f5e00000000005e017121680000003b100000000000fa00000000002fa0001670afc79334880005325df2da000014a15e24603dc14c76a11000000000001c30000000000000000000000000000002ec7ab24480000007630000ab4aa4477000000005a00002f80b80000a4000058c0000000001748000000123800081c7a81e000009ec2c137282a01f07ed0001a3cbe81f713b90d0000000000102c0584f32d81b200002af0001228b8c3c32e50cec20a00010c9380000000000000072e1f313380000002d700000000000001ea80009265d100014b009e6480000c6cac41be23c9caca9400039611e85b400000000009522011972008000000000000000030733f97900005ce3a7003484200000015cc9783d323c0a14b360f02619ca80001d204400000004fd18d0ccc16c55f000000000030b26b800028a1de1b9072c00004a0000000c6039c0000a3400043600000000000001dd8a1847e0000040d1c000597000000000000024b00005541b12c900003a21d700000000060000650a2800058e0259154cdc21000000000000000000f34ffa000332800079c6212118e680007ec2c19bd863e7a60c780000007452929d64d8c426000000000015612e000000000000001447982f13648ee400000500019240006233fe0000e00516000113071a0002858000f6464f0fc80001d40002248000dfa68100785c85340000c0000000080800000000002bb0001fdc0002d40000c380000001ad00000000000000000a92032000188800000014a94ac0007ff00013ec0004c52950ea800044a32c0000f543da3b9800036e5fe0499bf8a0027f00003d80
  | 18 => 0x4588400002480000e6c0003e49e609ce80400000000000d0000000071e0002ec8000e1e69c07691740003cf00000000000000000000d3a00020b0fd4ef22130000000000000000000000000000005f400058c0000000eba0001670e941e621d39111c00007d02fb8000ece0002f01c30000000328116851c18300012144b6000203837400000000000000000000000000160000000000000053900017c47104063c713b40007e600004547126f710a94e800013600000000000000bd8000000000000000000000000000000000001da87c800007d3201668c8c20a00003e470e6f01bf9d7000069f0de9bb40002c63209ed500c6ad000000029c6e9245800009c11135389f006e7bb000000000060600019d47ee00000000004be41e18300005863e71311b4000067e00002c40005a63040030da22cf08714ec00000000000000002cb000000009212c01d00006d022a2b09d88cc40000000000c1200017100000004f030000000000000000000e5e31227c8114b784c10010000c3c0000001ed000000033c88d00000000000000f3200034580000000000928000cf680100012e802a35f1fe1f94dbe0001f10000000319153000000000000000005c80001ae00009660000000000cd0000000034881400031c1db400018b00017c80007c3000129800004d3619ef82d253406a8000e9a000000000000014d00000000004820000000bb80000339a840000000c31e540000e818a8d7400000713a0000000275000150088a6f93f50870b220003750f58abc4430000000b6234f15c9a5ce9436a00000004e600004f8398806064000000000000000000009e810c00008480000002ea90b07520920000000a3049e00000000005bb0a91580a2458634a0000e0e1a10001e940000ae0000000fdc000000000000000005100006b07cf23303348246ff225800000000019e9f283ac32000000000000000a201c40000000001bbc4e47153dc1f3800002a2318c8c00000000000c00000001d01628ca47a200000004105fd000000003e1100aa0000b80135000185800000038900005ec6070000760a384600000000000000089832c00000009a092c4d05720ea000042e65100000009020001701cc00003311240a30bd44e63
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa9e84106630800117f08baac61000a2f2117558c200043fc2ae8b18400387c855d163080091bd0fa9ac6100123721d5358c200054fc22a6b184000a9c8454d630800153d0829ac610002a76105358c200246f43e86b1840048dc8750d63080014bf0aa1ac610002972154358c200052f42886b184000a5d8510d630800b1d904b8ac61001237a1e3158c200052f42c62b184000a5d858c5630800153d0918ac610002a76123158c200246e43a62b184005acc824c563080014bd0a18ac610002976143158c200054f42062b184000a9d840c5630800b59d0418ac610012b6a003158c200054fc22eab184000a9c845d5630800153d083aac610002a76107558c200052fc2ae8b184000a5c855d163080014bd0a3a2c610002976147458c200070faa4a8b184000e1d5415163080014bd0b38ac610002976167158c200054f424e2b184000a9d849c5630800159f04b8ac610016b32097158c200052f428e2b184000a5d851c5630800153d0838ac610002a76107158c2002d67410e2b184000acd821c563080095b50038ac610002b66007158c202b727906a2b184056e4d20d4563080b14bb0b28ac610002a7a125158c200054ec24a2b184000e578154563080b1c9e40a8ac610163934815158c202b52f428a2b184000a9e84145630800153b0828ac61000387d474158c200070ea8e82b184052e8f20d0563080a5d1a41a0ac61000297a164158c200052ec2c82b184054a9d849056308001d2f02a0ac61000387d454158c200070ea8a82b184054e8f2050563080a9d1a40a0ac61000297a144158c200052ec2882b184052a9e84105630800156d09baac210002ad61375584202c53ac3ceab084056e67209d561080adce4413aac21015b9948275584202cf38904eab084000c77875d561080b1cce40baac2101639c88175584202c732902eab084057e71205d561080ad4ed0a3aac210002ada1075584200055ac20eab084000a7685dd161080014eb0bba2c210152ad61e74584200071b3ace8b084000e35759d161080a5d4e413a2c21014bac882745842029752904e8b084055eb1209d1610800196f0eba2c2100038d9d574584200071abaae8b084054ea7205d161080a9d6440ba2c210153a9481745842029f58902e8b084000a76851d161080014eb0a3a2c21014aada1074584200071baa4a8b084000e355415161080014ed0bb9ac2100029d61773584200055b426e6b084000ab584dcd61080a35cf04b9ac210016b920973584200053b428e6b084000a75851cd610800156d0839ac210002ad610735842002d73410e6b084006ae5821cd61080095e50039ac21001abc60073584200055bc22a6b084000ab48454d610800156d0829ac210002ad61053584200053bc2a86b084000a748550d61080014ed0a21ac2100029d6144358420
  | 1 => 0x865b226490016b3a0b634c9201ae363b6ca9924035d6870d953248067958edb2264900cf6a1c3644c92004d67436c69924000e4f6518d3248001c98ca31a6490003a3d90634c92000746320c699240049ea87dc132480017c30238264900273318d72cc12002566432659824005ccc764cb30480097910099660900021fe15764c12001c3e42aec98240008bf845d9304800517908bb260900023de05764c12000c7a40aec982405d87e86dd53048001878c9baa60901721fa1f654c1201b43e43eca9824000c3c74d9530480b717d0dba260900030fd97744c1200061e32ee8982405a8be87d9130480691790fb2260900030fdd7644c1200061e3aec898240048ee86dc930480093990e9926090012b3219324c12002e663b2649824004bc8804c9304800187ee93a2ca100030f5d074594200051fc22e6b284000a3c845cd650800147d0839aca100028f61073594200043fc3a86b28400087c8750d65080010fd0e21aca100021f61c43594202c43ec3ce2b284000a3e849c5650800147b0938aca100031de0571594202b43f438e2b284000a3e841c5650800147b0838aca100030fdc741594200061eb8e82b28400087e8790565080010fb0f20aca101528f61241594200071bc0a82b284000c3f71505650800187ae2a0aca100021fa1c41594200043ec3882b284052a3e8410565080010fd0f18aca100021f61e31594200051f42462b284000a3d848c565080010fd0e18aca100021f61c31594200051f42062b284000a3d840c5650800b4dd0418aca100029b60831594200253d40062b284000a79800c5650800187eeb3aac8100030f5d475590200051fc2ae6b204000a3c855cd640800147d0a39ac8100028f61473590200045fc3aa6b2040008bc8754d640800117d0e29ac8100022f61c53590202a45ec3ce2b204000a3e859c5640800147b0b38ac8100032de0571590202945f438e2b204000a3e851c5640800147b0a38ac8100030fdc751590200061eb8ea2b2040008be87945640800117b0f28ac8101628f61651590200071bc0aa2b204000c3f71545640800187ae2a8ac8100022fa1c51590200045ec38a2b204056a3e85145640800117d0f18ac8100022f61e31590200051f42c62b204000a3d858c5640800117d0e18ac8100022f61c31590200051f42862b204000a3d850c5640800b55d0418ac810002ab60831590200255d40062b204000ab9800c56408001c3ea92a4c610003875505498c202c52ec2ca33184000a9e84946630800153b0928cc61000395e055198c202b52f428a33184000a9e84146630800153b0828cc61000387d474198c200070ea8e833184000a5e8590663080014bb0b20cc610152a76124198c200074bc0a833184000e1f515066308001c3aa2a0cc61000297a144198c200052ec28833184052
  | 2 => 0xf50d91200045ec3ea1b2240348be87c43644800117b0f886c8900028fa1710d91200051ec2e21b224033eb010443644800517d09baec6900022f61375d8d2001c3f42ee9b1a400087d85dd3634800159b0418ec690002b660031d8d2000e7838a21b1a4000ed2314436348001dc242886c6900030f9d36598d200061f3a0cb31a4000c3f655d26348001878caba4c6900030f9d76498d200061ebaec931a4000c3e75192634800187aea324c69000e1fa1b7558d201ac3e436eab1a400087e87d956348001878e9b2ac6900031d1c76558d200043f438cab1a4000c3c7419563480018e8e232ac69000a2fa1b7458d2019c5e436e8b1a4000c3f65dd16348001878cbba2c6900022fa1f6458d200061fbaec8b1a4000c3c75d916348001968e3b22c6900022fa1c6458d200061fba8c8b1a4000c3c751916348001968e2322c6900031dd977158d200063a32ee2b1a4000cb764dc56348001968c9b8ac6900021f6077558d200045fc22eab1a40028bc845d563480011ef02baac6900063d2057558d200061fbaee8b1a4000c3c75dd1634800117b03ba2c6900021fe157458d2001c3e42ae8b1a40008f7815d163480031e902ba2c6900030fdd47458d200061e3a8e8b1a4000c7775dc563480018e8ebb8ac6900032ddd37158d200065a3a6e2b1a4000c7785dc563480018e90bb8ac6900032de137158d200065a426e2b1a400087f855c563480070f90ab8ac6900022fe117158d200145e422e2b1a40008df835c563480011df04b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a400087e87d4563480070f90fa8ac6900030fdd35158d2031e1e3a6a2b1a4000c7771d4563480038e8e3a8ac6900021fa1d5158d200043e43aa2b1a4000c3f7454563480c5878e8a8ac6900031ddc55158d2000e3a38aa2b1a40008be87d0563480051790fa0ac6900030fdd74158d2030e1e3ae82b1a4000cb771d056348003968e3a0ac6900022fa1d4158d200045e43a82b1a4000c3f7550563480c1878eaa0ac6900032ddc54158d2000e5a38a82b1a40008de87cc563480039a8e398ac6900063721d3158d2000e6a38a62b1a40008ee87c8563480039c8e390ac6900063b21d2158d2000e7238a42b1a4001cf07184163480031f10e882c6900073c1c51058d200076898a20b1a4000ee12144163480bf8dae4328c69017b2b5c86418d200046fc3ac631a4000ad48158c63480bf0f90cbae64900030f19175cc920286b4102eb992403587f87d9732480010fb0fb2e64900030f9d365cc9202f45e432e99924000c3f655d33248001878caba6649013f6a08174cc92019c5fc3ec999240008bd87d93324800187cebb2664900030f5d764cc92004e6c31ae19924036e4c32d953248069d1
  | 3 => 0x3b2a4000a3e841c7654800147b0838eca9000297a0c71d95200052ec18e3b2a4036a6e821c7654806b4db0438eca900d69ea0071d95201b53cc00e3b2a4000c3f71d07654800187ae3a0eca900021fa1e41d95200043ec3c83b2a4068a3d849076548001c6f02a0eca900030fdc541d95200061eb8a83b2a400087e8710765480010fb0e20eca9019e8fa1041d95200043f43c63b2a400087d878c7654800147d0918eca900028f61231d95200043f43863b2a400087d870c7654800147d0818eca900028f61031d95201b53741063b2a4000a6d820c7654806b4f50018eca900029e60031d95201ac3f43c43b2a400087d87887654800147d0910eca900028f61221d95201b73210a43b2a403687e87d0365480010fb0fa06ca900da1fa1f10d95200043ec3e21b2a4000a3e84c43654800147b09886ca900d79c04110d95200061f3b6cbb224000a3d81d97644800117b0f32ec8900028fa1665d91200045fc3acbb224000a3e86197644800187cec32ec8900028f60465d91200045f436e3b224000c3f65dc76448001878cbb8ec8900030fd9571d91200061e32ae3b2240028bf87d87644800196ae3b0ec8900022f61e61d91200051f42cc3b224000a3d85987644800117f0eb0ec8900028fe1561d91200051e42ac3b224000a9f83587644800153906b0ec89002e2f61c61d91200051f428c3b224000a3d85187644800153d0630ec890002a760c61d91200065ab88c3b224000a3e86d4764480014790da8ec89018f0f9db51d91200051f432a3b224000a3c8654764480c587ceca8ec8900ceab21921d91200075230a43b224034ab8864436448001d60c2886c890003e848510d91200061fbacebb224000c3d751d7644800147d0bb9ec8900028f61773d91200051f42ce7b224000a3d859cf644806955d0439ec8900ceab60873d91200045fc3aa7b2240008bc8754f644800117d0e29ec8900022f61c53d91203345fc3aa5b2240338bc8754b644800117b0f38ec8900028fa1671d91200051ec2ce3b224000cb7815c7644800117d0e38ec8900028fa1471d91200051ec28e3b224000a9e831c7644800153b0638ec8900d2aba0871d912019d56c10e3b224033aba801c764480695730038ec8900030fdc751d91200061eb8ea3b2240008be87947644800117b0f28ec8901968f61651d91200071bc0aa3b224000c3f71547644800187ae2a8ec8900022fa1c51d91200045ec38a3b224064a3e85147644800117d0f18ec8900022f61e31d91200051f42c63b224000a3d858c7644800117d0e18ec8900022f61c31d91200051f42863b224000a3d850c7644806955d0418ec890002ab60831d912019d5d40063b224000ab9800c7644806717d0f10ec8900022f61e21d91200051f42c43b224000a3d858876448069d484290ec8900d22fa1
  | 4 => 0x10c001c6ceb3a2c2180038d5d674584302974b984e8b086052eb2309d1610c0a5d2a613a2c2181b3ac4c274584300065bc3ae8b086000e36755d1610c001c6aeaba2c218153a5cc174584302a759182e8b086054e95305d1610c0d7d6260ba2c2180029da1474584300053ac28e8b086052ab6841d1610c001c6ea92a2c2180038d55054584300053b42ee4b086000a7585dc9610c00156d09b92c218002ad61372584303556bc1ae4b086009ad4835c9610c0014ed0a392c2180029d61472584300055b420e4b086000ab5841c9610c0135ad06392c21804eb560c725843002579400e4b086013af1801c9610c00156f08a92c218002ad21152584300055b420a4b086000ab584149610c0014ef0aa12c2180029d21542584300053b42884b086000a7585109610c00117f08baac79000a2f2117558f200043fc2ae8b1e400387c855d163c80031b90e98ac790007351c53158f2000e7238a42b1e4005ccc7258d30c80093990e9926190012f2201324c32001c3f43eeab1c400087d81dd5638800117f08baac71000a2f2117558e2021c3f438eab1c40028be87dd1638800187eebba2c7100030f1d77458e200045ec0ee8b1c400087f855d163880070f90aba2c7101062fa1c7458e200061fba8e8b1c4000c3c751d163880010ff0ab8ac71000e1f2157158e200045fc22e2b1c40028bc845c563880010fd0fa8ac71000e1f21f5158e200061fba6a2b1c4063c3c74d4563880010fd0ea8ac7100021f21d5158e200061fba2a2b1c4062c3c74545638800117d0fa0ac71000a2f21f4158e200061fbae82b1c4061c3c75d05638800117d0ea0ac7100022f21d4158e200061fbaa82b1c4060c3c7550563880091b90e98ac7100073c1c51058e200076898a20b1c4004cd87058d32880010fb0f326ca900021fe1d64d95200051ec08c9b2a400087e86dc76548001878c9b8eca900030f19171d952001c3fc3ec3b2a4000c7571d8765480010fb0f30eca900028fa1261d95200051ec24c3b2a400087f87587654800147f08b0eca900028f21161d95200052fc1ac3b2a4000a5c8358765480190fb0e30eca900028fa1061d95200051ec20c3b2a4000a5e8318765480014bb0630eca900031d5c461d95200051f43683b2a4000a3c86d0765480c387ceda0eca900028f21941d95203061f3b283b2a4035a6c864876548001cc8c290eca900da9e21910d95200073830a21b2a4000f6121443654800187ee93a6ca900030f5d074d95200051f426e7b2a4000a3d84dcf654800147d0939eca900028f61273d95201b537410e7b2a4035a6d821cf65480010ff0ea1eca900021f21d43d95200043f43887b2a400087d8710f65480d30ff0ea16ca900d61f21d42d95200043ec3ce3b2a4000a3e849c7654800147b0938eca900031de0571d95200043f438e
  | 5 => 0x80022fa1e51590300045ec3ca2b206058a3d85945640c001c6f02a8ac8180030fdc551590300061eb8aa2b2060008be87145640c00117b0e28ac81815a8fa1451590300045f43c42b2060008bd87885640c00147d0b10ac8180028f61621590300045f43842b2060008bd87085640c00147d0a10ac8180028f614215903004d4f41842b206000a9d83085640c0095750010ac818002ae600215903000717aa4a93106000e2d54152620c0b14db0b28cc418002aba12519883000556c24a33106000e6781546620c0ad4dd0a28cc418002aba10519883000556c20a33106000e2f51d06620c001c5aa3a0cc4180029ba16419883000536c2c833106054aad84906620c001d4f02a0cc4180038bd45419883000716a8a833106000a6e85106620c0014db0a20cc41814aaba1041988300045fc22eab1060028bc845d5620c0010ff0aba2c41800e1f21574588300247743ea4b1060048ec87549620c00155f08a92c418002ab211525883000557420a4b106000aad84149620c0091dd0fa12c4180123b21d425883000537c2a84b106000a6c85509620c0014dd0a212c4180029b614425883004c6e41ae2b1060048ee87885620c0014dd0b10ac4180029b61621588300055742442b106000aad84885620c0091d90e90ac418026b320d21588300053742842b106000a6d85085620c00155d0810ac418002ab610215883004d6741842b106004aea80085620c00155f08baac418002ab211755883000557420eab106000aad841d5620c0014df0aba2c4180029b215745883000537428e8b106000a6d851d1620c001c5ea92a2c4180038b55054588300053742ce2b106000a6d859c5620c00155d0938ac418002ab612715883000567c1ae2b106009acc835c5620c0014dd0a38ac4180029b614715883000557420e2b106000aad841c5620c01359d0638ac418002b360c715883002575400e2b106000ae9801c5620c0adc9e61a8ac41815b934c351588302c536c2ca2b106000aae84945620c00155b0928ac41800399e0551588302c727982a2b106058e4d30545620c0ad4dd0a28ac418002aba10515883000556c20a2b106000e2f51d05620c001c5aa3a0ac41814ba3cc341588302974698682b106000a6e85905620c0014db0b20ac418152ab612415883000753c0a82b106000e2f51505620c001c5aa2a0ac418153a3cc141588302a74698282b106000a6e85105620c0014db0a20ac41814aaba1041588300055b426eab086000ab584dd5610c0b14eb0f3aac21815b95cc275584302b739184eab086056e55309d5610c0ddce2613aac2180031de1d75584302c72b982eab086058e72305d5610c0b1caa60baac2181b79c4c175584302b53b428eab086000ab6841d5610c00156b083aac2180029da1774584300053ac2ee8b086054ab5879d16
  | 6 => 0xd5d40043b226000ab980087644c08517d0fa86c8980022f61f50d91302145f43e21b2260008bd87c43644c00147d0b886c8980028f61710d913020f5808221b2260028be84dd7624c00117b09baec49800e1fa1774d89300043ec2ee9b126000acd83087624c0015d30010ec4980073c1c510d89300076898a21b126000ee221443624c00187ce9b2cc4980030f9d065989300061fb2ae93126000c3c655d2624c00187cebb24c4980030f5d764989300061f3a8c93126000c3d75192624c0070fd0dbaac49810e1f21b75589300043f43ecab126000c3c74d95624c0018e8e3b2ac4980021fa1c65589300061e3a0cab126000c7471195624c00517d0dba2c4981062f21b74589300061fb2ee8b126000c3c65dd1624c00117d0fb22c4980030fdd764589300061e3aec8b126000cb471d91624c00117d0e322c4980030fdd464589300061e3a8c8b126000cb471191624c0018eecbb8ac4980031d19771589300065bb26e2b126000cb464dc5624c0e18bae6328c4981bf275cc641893000477c3ac43126000ae481588624c0e10f90cbac64980030f191758c930276ac182eb192600087d87d96324c00187ce9b2c64981be2f219748c9300061fb2ae91926000c3c655d2324c09bb3060ba464980022f61f648c9300061f3aec91926000c3d75d92324c00b9d0c4b846498113930cb654c93021746196c89926043c5c76d95324c087ab0e1b2a6498107271db644c93020ecc386c89926005ace86d89324c001c9eca312649800393194624c93000747b20c49926000e8c64189324c0093b50fb826498002f4604704c9300061fba4e8b286000c3d741d1650c00147f08b92ca180028f21172594300051f420e4b286000a3d841c9650c0010ff0ea12ca180021f21d42594300043f43884b28600087d87109650c0b10fb0f38aca180028fa1271594300051ec24e2b286000c77815c5650c0ad0fd0e38aca180028fa1071594300051ec20e2b286000c3f71d05650c00187ae3a0aca180021fa1e41594300043ec3c82b286054a3d84905650c001c6f02a0aca180030fdc541594300061eb8a82b28600087e87105650c0010fb0e20aca1814a8fa1041594300043f43c42b28600087d87885650c00147d0910aca180028f61221594300043f43842b28600087d87085650c00147d0810aca180028f610215943004d2f41842b286000a5d83085650c0094f50010aca180029e60021594300061fbaceab206000c3d751d5640c00147f0ab92c8180028f21572590300051f428e4b206000a3d851c9640c00117f0ea92c8180022f21d52590300045f438a4b2060008bd87149640c0a917b0f38ac8180028fa1671590300051ec2ce2b206000cb7815c5640c0a517d0e38ac8180028fa1471590300051ec28e2b206000c3f71d45640c00187ae3a8ac81
  | 7 => 0x3d849c7654c0018ef02b8eca980021fa1c71d95300051f420e3b2a6000a3d841c7654c0894bd0638eca9810e9760c71d953000537410e3b2a6000a6d821c7654c0874f50038eca981129e60071d95300061fb8e83b2a6000c3d71d07654c0010fd0f20eca980021f61e41d95303ad1ec2483b2a6000e3781507654c00187ee2a0eca980030f5c541d95300043f43883b2a600087d87107654c0e947d0820eca9810e1fa1e31d95300043ec3c63b2a6000a3e848c7654c00147b0918eca98113950c531d95300043f43c43b2a600087d87887654c00147d0910eca980028f61221d95300043f43843b2a600087d87087654c00147d0810eca980028f61021d95302252f41843b2a6000a5d83087654c0874f50010eca980029e60021d95302243f43e81b2a600087d87d03654c0890fd0f886ca980021f61f10d95300051f42621b2a6000a3d84c43654c087ce020886ca980030f9db65d91300051ec0ecbb2260008bd87997644c00147d0b32ec8980022fe1d65d91300051f430cbb226000c3e76197644c00147b0232ec8980022fa1b71d91300061fb2ee3b226000c3c65dc7644c00187ecab8ec8980030f19571d91300145fc3ec3b226000cb571d87644c00117b0f30ec8980028fa1661d91300051ec2cc3b2260008bf87587644c00147f0ab0ec8980028f21561d913000557c12c3b226000aac82587644c02f17b0e30ec8980028fa1461d91300051ec28c3b226000aae82187644c00155b0430ec8980032d5c461d91300051f436a3b226000a3c86d47644c0c787ceda8ec8980028fa1951d91300051e432a3b226062c3e76547644c0835390c98ec898003a518531d91302155c43221b226000eb061443644c001f2262886c8980030fdd675d91300061eba8ebb2260738bf8754f644c0831790ea9ec8980028fa1772d91300051ec2ee5b226000a3e859cb644c00147b0b396c89810aa7a0c72d913020d4ec18e5b2260008bf8754b644c0011790ea96c8980022fa1c52d91300045ec38a5b2260008bd879c7644c00147d0b38ec8980028f61671d91300065bc0ae3b2260008be871c7644c00147d0a38ec8980028f61471d91302154f418e3b226041a9d831c7644c00155d0438ec898002ab60871d913020d5d400e3b226042ab9801c7644c00187ee3a8ec8980030f5c751d91300045f43ca3b2260008bd87947644c0e547b0b28ec8980038de0551d91300061fb8aa3b226000c3d71547644c00117d0e28ec8980022f61c51d913038d1f428a3b2260418be878c7644c00117b0f18ec8980028fa1631d91300051ec2c63b226042e94314c7644c00117d0f10ec8980022f61e21d91300051f42c43b226000a3d85887644c00117d0e10ec8980022f61c21d91300051f42843b226000a3d85087644c08553d0610ec898002a760c21d91302
  | 8 => 0xe992c01900393dd53258032007263aa64b006400e8f744c9600c801d18e8992c019003b2e0132580320076440264b006405ecb704c9600c80199a65b8ac0190021fe15715803201c3e42ae2b0064008bf845c5600c80517908b8ac019003334c971580320043f43ea2b00640387c87d45600c80187ee9a8ac01918f0f1d3515803200726996a2b00640087e87545600c8010f90ea8ac0190030fdd151580323161e3a2a2b006400e4d32545600c80117d0fa0ac01900a2f21f41580320061fbae82b006461c3c75d05600c801d1a65a0ac0190022fa1d41580320045e43a82b006400c3f75505600c8c1878eaa0ac019003a34c9415803201e3c3aca0b006400ab984941600c801d9265282c0190163e21d505803200764992a0b006400a7985901600c805970e9202c019003b24ca405803202c7c43a80b006400ec932501600c801d9265082c0190063e21d10580320076499220b006401cf071441600c80117f08baac59800a2f2117558b300043fc2ae8b16600387c855d162cc0039a8e298ac5980063b21d2158b3000e7238a42b16600387e87dd5628c0010fb03baac5180022fe117558a300145e422eab1460028be87dd1628c00187eebba2c5180030f1d77458a300045ec0ee8b14600087f855d1628c0070f90aba2c5180030fdd47458a300061e3a8e8b14600087f855c5628c0070f90ab8ac5180022fe117158a300145e422e2b14600087e87d45628c0070f90fa8ac5180030fdd35158a3031e1e3a6a2b14600087e87545628c0010f90ea8ac5180030fdd15158a303161e3a2a2b1460008be87d05628c0051790fa0ac5180030fdd74158a3030e1e3ae82b1460008be87505628c0011790ea0ac5180030fdd54158a303061e3aa82b1460048ec87485628c0039e0e2882c518003b84851058a3002674382c4994600087d87993654c0010ff0eb26ca980028f60464d95300043f436e3b2a6000c3c64dc7654c001878c8b8eca9800e1fe1f61d95300063ab8ec3b2a600087d87987654c00147d0930eca980028f61261d95300043fc3ac3b2a6000a3f84587654c00147908b0eca980029be0961d953000536412c3b2a601887d87187654c00147d0830eca980028f61061d953000537410c3b2a6000a6d82187654c0018eae230eca980028fa1b41d95300051e43683b2a6061c3e76d07654c0014790ca0eca981830f9d941d953021d2e43263b2a6000e54614c7654c0894f10c886ca980039c18510d9530007a898a21b2a6000c3f749d3654c00187ae83a6ca981da1fe1d43d953021c3e43a87b2a6000a3e84dcb654c00147b09b96ca980028fa1272d95300051ec24e5b2a6044a5e831cb654c0874bb06396ca980021fe1d42d95300043e43a85b2a600087e8710b654c0010fb0e216ca980021f61e71d95300051f424e3b2a6000a
  | 9 => 0x705963202d37414e0b2c6432a6d829c1658c8010fd0fa02cb190021f61f40596320043f43c80b2c640087d87901658c80b4dd04202cb190029b60840596320043f43e20b2c640087d87c41658c80147d09882cb190028f61310596320043f43820b2c640087d87041658c80147d08082cb190028f61010596322752f41820b2c6400a5d83041658c80b4dd04082cb190029b60810596320073888020b2c6400c3f759d5648c8f555f04baac919016ab20975592320061eba8eab246400a3f855cd648c8014790ab9ac9191e6abe0973592323c45fc3aa6b2464738bc8754d648c8a717b0f38ac9190028fa1671592320051ec2ce2b246405aae829c5648c8ef55b0538ac9190032de0571592322ac5f438e2b246400a3e851c5648c80147b0a38ac9190030fdc751592320061eb8ea2b2464008be87945648c80117b0f28ac91915e8f61651592320071bc0aa2b246400c3f71545648c80187ae2a8ac9190022fa1c51592320045ec38a2b246459a3e85145648c80117d0f18ac9190022f61e31592320051f42c62b246400a3d858c5648c89bd286298ac9190028fa1770592320051ec2ee0b246400a3e859c1648c80147b0b382c919016aba0a705923218d56c14e0b2464008be87d41648c80117b0fa82c9190022fa1e50592320045ec3ca0b246405aae82141648c80155b04282c9190022fa1f10592320045ec3e20b246400a3e85c41648c80147b0b882c9190022fa1c10592320045ec3820b246400a3e85041648c80147b0a082c919136a7a0c10592320054ec1820b246405aae82041648c80155b04082c919003ac44010592320145f426eab0464008bd84dd5608c8070fd0bba2c1190021f617745823200c7c43a20b046401cf071441608c801dc242882c1190022fe1175d81320145e422ebb02640087f855d3604c8070f90aba6c099007351c531d813200e7238a43b026404cf2605c4604c8011f70eb00c0990033c5c5601813202e6743eec9906400e4e85dd9320c801c9b0bbb2641900333dd7764c83200666baeec9906400e8e84dd9320c801d1b09bb26419002b3e07764c83200566c0eec9906400e4f51dd9320c801c9aa3bb26419003a3d07764c83200746a0eec9906400acd80dd9320c80159b0d3826419002b3e19704c832005a7c2ae09906449b4c855c1320c80171f08b826419122e3211704c832005e3c0ae09906447bc4815c1320c89369d0a3826419002d3614704c832245c7420e09906400b8d841c1320c88f78d023826419002f1604704c832006e4b80e0990640387e87dd5600c8010fb03baac0190022fe1175580320145e422eab0064028be87dd1600c80187eebba2c0190030f1d774580320045ec0ee8b00640087f855d1600c8070f90aba2c0190030fdd474580320061e3a8e8b006400ccf874c9600c801999
  | 10 => 0xb2e6400c3f7150565cc80187ae2a0acb990021fa1c41597320043ec3882b2e646ca3e8410565cc8010fd0f10acb990021f61e21597320051f42442b2e6400a3d8488565cc8a1cc84290acb990028fa1370597320051ec26e0b2e6400a3e849c165cc80147b09382cb9902697a0e70597322052ec1ce0b2e640087e87d0165cc8010fb0fa02cb990021fa1e40597320043ec3c80b2e6409a5e8310165cc8014bb06202cb990021fa1f10597320043ec3e20b2e6400a3e84c4165cc80147b09882cb990021fa1c10597320043ec3820b2e6400a3e8404165cc80147b08082cb9902697a0c10597320052ec1820b2e6450a6e8204165cc8014db04082cb990039c44010597320061fbaceab266482a9f835d564cc81353906baac9990030f5d475593320051fc2ae4b266400a3c855c964cc90353f06b92c9992022fe1d52593323345e43aa4b26646b8bd879c564cc80147d0b38ac9990028f616715933204d4f41ce2b26647fa9d839c564cc80196f02b8ac9991b22fa1c71593320051f428e2b266400a3d851c564cc80187ee3a8ac9990030f5c751593320045f43ca2b2664008bd8794564cc8db47b0b28ac9990038de0551593320061fb8aa2b266400c3d7154564cc80117d0e28ac9990022f61c51593323751f428a2b2664008be8788564cc80117b0f10ac9990028fa1621593320051ec2c42b26644fea42148564cc80147d0bb82c9990028f61770593320051f42ce0b266400a3d859c164cc81353d07382c9990fea760e70593320045f43ea0b2664008bd87d4164cc80117d0f282c9990022f61e505933204d4f418a0b266400a9d8314164cc80117d0f882c9990022f61f10593320051f42e20b266400a3d85c4164cc80117d0e082c9990022f61c10593320051f42820b266400a3d8504164cc81353d06082c999002a760c105933227d5741020b266400aad8204164cc801d6220082c99900a2fa1375583320045ec26eab06640387e85dd160cc8010fb0bba2c1990063e21d105833200e7838a20b066400ed13144160cc80187ee93a2cb191fa9be09745963202d36412e8b2c6400c3d741d1658c80147f08b9acb190028f21173596323ed37c12e6b2c647c87f8750d658c8ed0f90ea1acb1915e1f61e71596320051f424e2b2c6400a3d849c5658c80b4dd0538acb191ee9b60a71596320063bc0ae2b2c645987e871c5658c80147d0838acb190028f61071596320061fb8e82b2c6400c3d71d05658c8010fd0f20acb190021f61e415963229d1ec2482b2c6400e3781505658c80187ee2a0acb190030f5c541596320043f43882b2c640087d87105658c8ab47d0820acb190021fa1e31596320043ec3c62b2c6400a3e848c5658c80147b0918acb1913b950c531596320051f426e0b2c6400a3d84dc1658c80147d09382cb190028f612
  | 11 => 0x4f1c00000000000088c000af000042c58c0000003202793b00000000016f428800000000109c0ac00135177d55c9c44c8000ca55c8c5400c1ec0000000016b8df42ac83c00155800080c00000000200000000600600000000001400c00000e00000200000400000000400a00000000a00001600a00400800000000800200200001400000600a00000600800800400c00000400400000200200600000000400000000000200000200600800200200400a00400000000000000000000000000000000800200000200200400000400000600200200200200001000400200200000000000000800600200000202200000000600000a00600600000000000000400400200000000600000200400000200000200200000200200800000800000200000200200200400400200200000200000000a00000000800000e00a00000a00000000200400800000000a00601001400200402800200600000001600000000400200400000c00200001c00201200401e00000000600600000000000a00000000200200000000400000200200000000000400c00400600200401a00000000400400000000200001000400000001200000c02200a00400000a00200001403400a00400000000000001400c00000400a00000000200000000000200200200601800800001001603400600400400000800a00400800800e00800000400600000001000400600200200200201400000000000a00000400000000e00001c00000000000600000600c00401200801200000800800200600000000200200200600000000000000000000200600200800200000c00000000000000000000400200400001200000000a01a00600000800000000200000400400200200400000000800800401e00000000400400200200000600c00000000800000200000800a00a01200200400800000400000000a00000000000000001200800e00000200201200601800000200600400000000400000400000600200000400800600600200000400401000000200000600800000400000800001000c00200600200201001400001400a00a00200000000200600200e00000001600000000400e00000000e01400200400400400200000400200000a00000200000400a00401a00801000800000000000400a00600200001200201200200200200400c00000c3f749d165cc90d4bf06ba2cb990269720d74597320061eba0e8b2e6400a3f845c965cc80147908b92cb9921697e0d72597324243fc3a84b2e646987c8750965cc8db0fb0f38acb990028fa1271597320051ec24e2b2e6409a5e839c565cc9074bb0738acb990031de0571597323743f438e2b2e6400a3e841c565cc80147b0838acb990030fdc741597320061eb8e82b2e640087e8790565cc8010fb0f20acb991ae8f61241597320071bc0a82
  | 12 => 0xc600000016a4000000001090000000000000001240000000000000a2c7545a40000000000004840012d400003c82d51c0000000015389900016000000000000000484a1760d690a800091c0014040000000000007903b15dd2e49cc0dcaecd7486400039531c3ad618bc491174050c6d0df025000000049158c6c01cc000000b30dcc6157fcdb8ff157c05472c000850c20dec000574000c04000a1086d25000179c674000064000000000ce40006e0da864d0984743480000000000000000007780000000000010688900015500000000000007c4000000000000000000e2d3580011dd26d1f11280000003a40010140004992b00000016e92a00015650c869182c000000000000000000b7c1b4000000000000fa8000118138000cbd17c00000000000000000000007455000072545cd2119069d718534ff8000000000000000000218fc40000000008b889cda0000000000ef063c54c2c96c533c5a12254380011740000017740005ec000000c50d4c42400000004c7314d00013889f847800000095800000009c434f6000127940c0006b52ec0008ec5e8978190000d540016684f8000000000000f1112c828a0000041d6d00001f4eb546c3180003e520cee000090c7bc0015ecc68254fd40000000014440000008bc0000000000013800001d40000000000c0c1c000b915a80002255d121c0000003d15f4000f480016ad5e40015c00000000006489d4000f5c000308d114300a40000006240000009dc000948d14641530c2cb451256251190e0dfd490001330000f38aa04b4cf42e80005e44380012200009a1738000000000e513dc000000000f3c0007847880000014c968c7456c95747ec1205cd4f4b24000ba4f2c9849180000000013017e40000017f80000002580000000000000008e0268000465000000878000001185798000000000000000d7c3b94c16a0000ecd6340004201e8000c9c0000000014ac971258000000ae80000000009c800173cd180007202280009c0000b1c00000000000000099c4456300006f0acc45000124c0000cc001524c6cb8c2b40000000000000000000000000000010940005706218116606f4bc1764461674b3c0011acc08f6c1845141142083e90785e14a0c3015ccfc000c296085d000002400148c000f94780000000001398000000e980017dcbe40017b83980014e4000380000e4c000000530000ad0000000000e44d980000000016e4ebd0e4000000000000000000000001148abccac9f0001588d28000001648fece48000000a34b492b8000069520b81080001474aa4888c4c4f000000000017cbe00000000003bc00000110d3180008581251ec00169983400019957861c00000000117000000056c5900000000000000000011d13b400078c4180013f8000001830000000000000000d5cfe
  | 13 => 0xf400017b00012040007f80017acbd01b93ec001368000344c340015047a400132800000087c000f1574c044efc0016f04c400153d1144e04f4c983ed4002116813e8a8025cfc0c400000000000000008e54193cd5b00000400000000017108051800000000000010ace400002d40000005c0000508000000000bccdb581cba80000610342a8010a20000b6000043ca1c000000c00bac148b7800000136ce200001dc220000bdc0000c40000000000000013107c80014d4e952091600000008357c0e692e000019c00000167ca94d78000000000000000000b2007d7887951780000000000013d8000e5ca151a4d880000008f1664324a38000748001374000100ce80006040001600000014b40000017c8fe0000001364000000000554000000ec8000000000ae15704540001d811c0a8000000000000b955951c40012011400006347f15094a8000a70f88ee8dc00000011b4000b00ea40340145b80001d15cc00178cfbd42c0018200000015e824000000000000069840176c97d15098c0006a85416540000015989d80000012194ec058000f54c893f4a8d7780013d000000000000084562c4a4764000000b091086d8709339060000fa40008b00000f400000000151000159ceec37800061033c000000000000000ee4000000000ddc0014cd540d58ef8f858181c80006e800000000163800000000073ce14000000000000070bb8000f7c0000007740907e8000000000000000000a9c3c8e34638000000000000e64000000bbc5180000000000007710c002d4fc00068c12c000cd0000000ad8870e30874820000000000000000001304fc9714a60998000000000414a64000d38b680000000015680000001fc00172c44ccc000000000105c00095400088000000000000000000076c0011d8000000001284a440011bc000e90b1453ce84314000001048c14cc51c8000b28add0d80bccb52dc9fced8000001044768000f305dc0017546586ecf24bd48cc538e8c0014880000000012150300000000000000005ac000000000000000594000000c8d65c5d80006700e43c4001470000000b9c000868684eb00000017ec000260000d945a89b8d7000139c000000001708b88000bb00011fc9b513c00108c7a86ac1a80000000015d80000000000000000000017d8000840ac16fc28507cde43f4000000b84a0800000161123c2bc000ce000070d3f0108fd8f5000000130c3b4e9c36d3782f4000e881800008ad164a9154c4400009e515c000000000824ced3b85d53e1690b7400129c2b9650a412c57b4000c907f57840a0608000de047d32c00029103d2e8ca054800115845d5c4d08760f080000011b8cdc0000000009ace60b3400000170c3700000007180016a86a00000015b91d46c4001460000000000000000000000000000000
  | 14 => 0x8ae4000000000860001074000bec0000000000003fce114b125d038bb40009b08a118c0009f4dd8244c7000029400095d448a289340b40016cc4d42cccb01588d000046c0000000001a4000000000e00ead7684d85fc00000000128000002064418cc8505052cc3d1c0000d8492822c55c00000139534c000000000000000000001629084628bf12f0c440005b00000002f8000cd88080014f972800161d6e0000a75008000469828000000000000a503f0001434000000d487b067c6a4458000000000650c5c0000006dc7b800009569c00000182400138c000d80000000000a78d6d0d4a0400128c81959000074c000001560000d30988000000f98f050a475020ca7c000000000de90f814400083000023c000000944000270000000000f000000000000000014bcc58000b7073400101c00000147c0008fc000000000000334a68000000000000c3800000000177033800000180caad6dc00075c000000050000c240000000010b1188960c94b10fa15a03d80008d800000000000000000000126857849d010000ab86680000000001b00006d54580000000000002480000000017cd5b57d516c17400152c00059caf800169409966c00119400167877c0d4000000909138000000000000000000bf40014dd2481703d479c00119ce540000009409a8000a996145f14940000000000000000000000004ec00000000970522c000000201838000000000000000000355535144000000df860d75000010d7d0904b6c57c0000010ec0011f4cf85216b0000a0c000000b4d7f400000000000021c0000012bc2fc0007d54d95f88c06f8e189011cc000000000000f8c000000e1c6791b156c0000000ec00000000000000000006ce296c0358000000b580001bc3dc0000008e800014d6d80007a0d1ccf00012982e4000000c7881c3400002ed3c914c7e40012300013e4f187dc0014e04b071d00c5f40003300000000014b97a802893d7a0000404000000e08000000e580c8ed42053bc00000000000008c0012380016851a005cedd81508800015400029c0000002a1641414000cb89a5024164e7130830c568d502383a87d8dd4700188000104528449100ef4000030c4941c5613840006300b86e40006540005bc0000001e02e12f400031172424d3492a93540000000000b000038c3e0d90000360e393a11300000008f80000011e94e80000005000000008a80007fd370b0c838084000298e24db0000000000000000001110000f4c01c0004ccd3d580a584fc5f84bd720110000001264aa90bc001274000ec400000000000146800000000000000037c0f8894000000dc9484e0cf440011a94782f00004a94404ac00143cda4168000000b5c00066400000000000000000107000000084d360000f90488924fad104ba0fe8078af4f64f280013340
  | 15 => 0x6bd75d3ad6b5544000000000000000000000000d60fcd254c0c504eb8950e049ed2a466c4b94980010f41ad04c0d88140007ac1292d0f58000000000140000000000000000000000000000000a5d7bc0009200000000010280002300017f11349740000800005450c46cd7c56ec62c93164c660688848a4c000b2c00149d7800e9644000ff46b848c2d0f35548e6cd0571d5e0000000ac8000680a5506d020f753400000011e4000000000d9c0005580000005c5734000001420001514000000b387b49bc8008544c0000001480000000d40000ad4c100005812700007996bc8f400034c8dc000000ed137cb5400144d730000000000000000000c7c000134714000000000428b18000f680012900000000e08b40010b8bf80000003500000014540009e872831d390000000000000ea096c374000000ea8000000000000000c642641a1805320bfca243645b4be83007e0000fb8600a4899540852555400001905400000000160ca6cb05019450cc83cd2f8408a3cd655bd3c5528d0cffc28c2347581505100012601c0000000000000fdc0006c80012c800065cb50dbc4e93c0000000738000c18d3400102cf800014282a542488563c3c0000618001294000001058000000000a196204e40007cc0016d40012894110dc0015007c04d0001700000001324494ca8c750e9228001065210f216f80009d0000b640012c10b40000000007400000000012cc000000000275120d8c32c000000000000000001244000000001605464000e800006957940002800000015f111c0d0968a300000014f00f05880011557a4000ccc001198000711748000000000fd094c5980008c4c80390e7c8c8f0c3f8f790f05855a40380044311e04dc17838974400000092c0000013fc85d3d4fb4fb000070400135d7580000000000000000000000003040007d17e80002d800035c4800000000000000000000012fc0000010a02b026c964000d2c0000000010cc000000000e74000000001671041658a840000000000008995d4ac44100002dc000bd89143a08a5168ab0d242c00881e4f7000000000000180816cdd13a86b0000e7881013000040cbc80000005640010fd5fc001344000000e3c000000b412d89e00000001f0000000f9c0000000001c400013d2b40010d14c45c92ac0002c447000127d004afcdc55acdad4a57e150d234938194d0000000000021400051c39d584000981800ec0cd5790000a88ab40fc00000000000036827c0000000000000011f80000008d5688000b98000000d443840013140000006fc3280013a55181f
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x5e35cae02000002ab08a82088d971c98035002c032004c1070091a38660001d320182a40514b612ad3863085b96002879e4a7d6802414431460cd1c0830a00921a18b82000068308302821a0c3030040fe61741d165cc91141c935d074597320069460d1004165cc801a618244010597320040fe61751d564cc91141c935d47559332006a460d1004164cc801aa18244010593320040fe61741d1658c90f42c925d074596320069460d10041658c801a618244010596320040fe61751d5648c90f42c925d47559232006a460d10041648c801aa182440105923200683a1684dd9320c8019c1815c0704c832007031d4744c9600c801649952013258032005a2650804c9600c8016c191201325803200433261325c5600c801a89844ca50580320069261532901600c8012c8984c910580320253825d21441628c0016619218510d953021d9425931443654c089a50864c510d95300040fe61741d3654c0016a19218510d913020da425931443644c085a90864c510d91300040fe61751d7644c00103f985d074594300040fe61751d5640c00122f9855054988300048be6154151620c0012379855054584300253425d3144163880016519318510d95201ad9825921443654806da608648510d95200040fe61741d365480016919318510d912019da8259214436448069aa08648510d91200040fe61751d764480034d0974c51058d2000e3421d3144163480034e0974851058d2000e3821d21441634800103f985d074594200040fe61751d5640800121f985505498c2000487e61541516308001237985505458420
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x3
  | 6 => 0x8a
  | 7 => 0x8d
  | 8 => 0x8e
  | 9 => 0x4
  | 10 => 0x98a
  | 11 => 0x98d
  | 12 => 0x98e
  | 13 => 0x128a
  | 14 => 0x128d
  | 15 => 0x128e
  | 16 => 0x150a
  | 17 => 0x150d
  | 18 => 0x150e
  | 19 => 0xca
  | 20 => 0xcd
  | 21 => 0xce
  | 22 => 0x9ca
  | 23 => 0x9cd
  | 24 => 0x9ce
  | 25 => 0x12ca
  | 26 => 0x12cd
  | 27 => 0x12ce
  | 28 => 0x168a
  | 29 => 0x168d
  | 30 => 0x168e
  | 31 => 0x3ca
  | 32 => 0x3cd
  | 33 => 0x3ce
  | 34 => 0xcca
  | 35 => 0xccd
  | 36 => 0xcce
  | 37 => 0x15ca
  | 38 => 0x15cd
  | 39 => 0x15ce
  | 40 => 0x170a
  | 41 => 0x170d
  | 42 => 0x170e
  | 43 => 0xcc992
  | 44 => 0x98cd2
  | 45 => 0xcc995
  | 46 => 0xcc996
  | 47 => 0x15c992
  | 48 => 0x995d2
  | 49 => 0x15c995
  | 50 => 0x15c996
  | 51 => 0x1609
  | 52 => 0x130b
  | 53 => 0x1649
  | 54 => 0x134b
  | 55 => 0xcd512
  | 56 => 0x150cd2
  | 57 => 0xcc9d2
  | 58 => 0x9ccd2
  | 59 => 0xcc9d5
  | 60 => 0xcc9d6
  | 61 => 0x1709d2
  | 62 => 0x9d712
  | 63 => 0x1709d5
  | 64 => 0x1709d6
  | 65 => 0x1789
  | 66 => 0x130c
  | 67 => 0x17c9
  | 68 => 0x134c
  | 69 => 0xcd692
  | 70 => 0x168cd2
  | 71 => 0xcc3d2
  | 72 => 0xcc3d5
  | 73 => 0xcc3d6
  | 74 => 0x3ccd2
  | 75 => 0x3ccd5
  | 76 => 0x3ccd6
  | 77 => 0xd0c
  | 78 => 0xd4c
  | 79 => 0xe8b
  | 80 => 0xecb
  | 81 => 0x9712
  | 82 => 0x1849
  | 83 => 0xb8b
  | 84 => 0xb89
  | 85 => 0x184b
  | 86 => 0x19c9
  | 87 => 0xbcb
  | 88 => 0xbc9
  | 89 => 0x19cb
  | 90 => 0x10c
  | 91 => 0x10b
  | 92 => 0x14c
  | 93 => 0x14b
  | 94 => 0x409
  | 95 => 0x449
  | 96 => 0xb8e
  | 97 => 0x184e
  | 98 => 0xbcd
  | 99 => 0x19cd
  | 100 => 0x999d5
  | 101 => 0x98bd5
  | 102 => 0x40e
  | 103 => 0x99856
  | 104 => 0x98b96
  | 105 => 0x44d
  | 106 => 0xd5d2
  | 107 => 0xb8c
  | 108 => 0x184c
  | 109 => 0xbcc
  | 110 => 0x19cc
  | 111 => 0x589
  | 112 => 0x5c9
  | 113 => 0x9d9d5
  | 114 => 0x9cbd5
  | 115 => 0x58e
  | 116 => 0x9d856
  | 117 => 0x9cb96
  | 118 => 0x5cd
  | 119 => 0x15cb15
  | 120 => 0x178e
  | 121 => 0x15d715
  | 122 => 0x15da15
  | 123 => 0x15cb16
  | 124 => 0x17cd
  | 125 => 0x15d716
  | 126 => 0x15d896
  | 127 => 0x170b55
  | 128 => 0x160e
  | 129 => 0x1715d5
  | 130 => 0x171a55
  | 131 => 0x170b56
  | 132 => 0x164d
  | 133 => 0x1715d6
  | 134 => 0x1718d6
  | 135 => 0x74b
  | 136 => 0x74c
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1191
  | 6 => 2058
  | 5 => 1551
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (48434+((h/397+packedAt gbK7 (44067+(h % 397)*11) 11) % 1430)*12) 12
  | 6 => packedAt gbK6 (107016+((h/686+packedAt gbK6 (98784+(h % 686)*12) 12) % 3614)*13) 13
  | 5 => packedAt gbK5 (97713+((h/517+packedAt gbK5 (91509+(h % 517)*12) 12) % 2724)*12) 12
  | 4 => packedAt gbK4 (4193+((h/19+packedAt gbK4 (4060+(h % 19)*7) 7) % 70)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc1fe1e0e0fe0ff8fc0ff81ffc27c19e0cf4cf
  | 1 => 0x1fe1fe00ff0ff0ff1ff03fe07cda0666333b33
  | 2 => 0x1ffe1fff000fff0fe0003fff831c3879c3cc3c
  | 3 => 0xe0001ffffff0000fffffc00003e03f81fc0fc0
  | 4 => 0x1ffffffffff00000000003ffc001fff000
  | 5 => 0xffffe000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x24022040201201102405080a2800c08a045045
  | 1 => 0x9214400490490a109401280504a0224112112
  | 2 => 0x12540aa900092a0a4020a55501141850c28c28
  | 3 => 0x4000133292a0000c92aa804102a02d01680e80
  | 4 => 0x3111ddcfccfccc000c301861bff4001bff000
  | 5 => 0x9f99801818818880030c061863ffb7fe000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37181
namespace PEqualNP.Outside.L_meta_37181
open PEqualNP.Outside.L_meta_37181.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
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
theorem bs1_4_544 : Interval s1Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 551 := (concat (concat (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 bs1_4_96)) (concat (concat bs1_4_128 bs1_4_160) (concat bs1_4_192 (concat bs1_4_224 bs1_4_256)))) (concat (concat (concat bs1_4_288 bs1_4_320) (concat bs1_4_352 bs1_4_384)) (concat (concat bs1_4_416 bs1_4_448) (concat bs1_4_480 (concat bs1_4_512 bs1_4_544)))))
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
theorem bs1_5_640 : Interval s1Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 666 := (concat (concat (concat (concat bs1_5_0 bs1_5_32) (concat bs1_5_64 (concat bs1_5_96 bs1_5_128))) (concat (concat bs1_5_160 bs1_5_192) (concat bs1_5_224 (concat bs1_5_256 bs1_5_288)))) (concat (concat (concat bs1_5_320 bs1_5_352) (concat bs1_5_384 (concat bs1_5_416 bs1_5_448))) (concat (concat bs1_5_480 (concat bs1_5_512 bs1_5_544)) (concat bs1_5_576 (concat bs1_5_608 bs1_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_32 : Interval s1Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 40 := (concat bs1_6_0 bs1_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 13 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 17 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 13 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 17 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_32 : Interval s4Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_64 : Interval s4Atlas 2 64 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 65 := (concat bs4_2_0 (concat bs4_2_32 bs4_2_64))
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
theorem bs4_3_320 : Interval s4Atlas 3 320 23 := block_range (n:=23) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 343 := (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 (concat bs4_3_96 bs4_3_128))) (concat (concat bs4_3_160 (concat bs4_3_192 bs4_3_224)) (concat bs4_3_256 (concat bs4_3_288 bs4_3_320))))
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
theorem bs4_4_1664 : Interval s4Atlas 4 1664 7 := block_range (n:=7) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1671 := (concat (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384)))) (concat (concat (concat bs4_4_416 (concat bs4_4_448 bs4_4_480)) (concat bs4_4_512 (concat bs4_4_544 bs4_4_576))) (concat (concat bs4_4_608 (concat bs4_4_640 bs4_4_672)) (concat (concat bs4_4_704 bs4_4_736) (concat bs4_4_768 bs4_4_800))))) (concat (concat (concat (concat bs4_4_832 (concat bs4_4_864 bs4_4_896)) (concat bs4_4_928 (concat bs4_4_960 bs4_4_992))) (concat (concat bs4_4_1024 (concat bs4_4_1056 bs4_4_1088)) (concat (concat bs4_4_1120 bs4_4_1152) (concat bs4_4_1184 bs4_4_1216)))) (concat (concat (concat bs4_4_1248 (concat bs4_4_1280 bs4_4_1312)) (concat (concat bs4_4_1344 bs4_4_1376) (concat bs4_4_1408 bs4_4_1440))) (concat (concat bs4_4_1472 (concat bs4_4_1504 bs4_4_1536)) (concat (concat bs4_4_1568 bs4_4_1600) (concat bs4_4_1632 bs4_4_1664))))))
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
theorem bs4_5_1024 : Interval s4Atlas 5 1024 20 := block_range (n:=20) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1044 := (concat (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 bs4_5_224))) (concat (concat (concat bs4_5_256 bs4_5_288) (concat bs4_5_320 bs4_5_352)) (concat (concat bs4_5_384 bs4_5_416) (concat bs4_5_448 bs4_5_480)))) (concat (concat (concat (concat bs4_5_512 bs4_5_544) (concat bs4_5_576 bs4_5_608)) (concat (concat bs4_5_640 bs4_5_672) (concat bs4_5_704 bs4_5_736))) (concat (concat (concat bs4_5_768 bs4_5_800) (concat bs4_5_832 bs4_5_864)) (concat (concat bs4_5_896 bs4_5_928) (concat bs4_5_960 (concat bs4_5_992 bs4_5_1024))))))
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
theorem bs5_2_64 : Interval s5Atlas 2 64 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 65 := (concat bs5_2_0 (concat bs5_2_32 bs5_2_64))
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
theorem bs5_3_320 : Interval s5Atlas 3 320 23 := block_range (n:=23) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 343 := (concat (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 (concat bs5_3_96 bs5_3_128))) (concat (concat bs5_3_160 (concat bs5_3_192 bs5_3_224)) (concat bs5_3_256 (concat bs5_3_288 bs5_3_320))))
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
theorem bs5_4_1664 : Interval s5Atlas 4 1664 7 := block_range (n:=7) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1671 := (concat (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384)))) (concat (concat (concat bs5_4_416 (concat bs5_4_448 bs5_4_480)) (concat bs5_4_512 (concat bs5_4_544 bs5_4_576))) (concat (concat bs5_4_608 (concat bs5_4_640 bs5_4_672)) (concat (concat bs5_4_704 bs5_4_736) (concat bs5_4_768 bs5_4_800))))) (concat (concat (concat (concat bs5_4_832 (concat bs5_4_864 bs5_4_896)) (concat bs5_4_928 (concat bs5_4_960 bs5_4_992))) (concat (concat bs5_4_1024 (concat bs5_4_1056 bs5_4_1088)) (concat (concat bs5_4_1120 bs5_4_1152) (concat bs5_4_1184 bs5_4_1216)))) (concat (concat (concat bs5_4_1248 (concat bs5_4_1280 bs5_4_1312)) (concat (concat bs5_4_1344 bs5_4_1376) (concat bs5_4_1408 bs5_4_1440))) (concat (concat bs5_4_1472 (concat bs5_4_1504 bs5_4_1536)) (concat (concat bs5_4_1568 bs5_4_1600) (concat bs5_4_1632 bs5_4_1664))))))
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
theorem bs5_5_1024 : Interval s5Atlas 5 1024 20 := block_range (n:=20) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1044 := (concat (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 bs5_5_224))) (concat (concat (concat bs5_5_256 bs5_5_288) (concat bs5_5_320 bs5_5_352)) (concat (concat bs5_5_384 bs5_5_416) (concat bs5_5_448 bs5_5_480)))) (concat (concat (concat (concat bs5_5_512 bs5_5_544) (concat bs5_5_576 bs5_5_608)) (concat (concat bs5_5_640 bs5_5_672) (concat bs5_5_704 bs5_5_736))) (concat (concat (concat bs5_5_768 bs5_5_800) (concat bs5_5_832 bs5_5_864)) (concat (concat bs5_5_896 bs5_5_928) (concat bs5_5_960 (concat bs5_5_992 bs5_5_1024))))))
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
theorem bgb_5_1536 : Interval gbAtlas 5 1536 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1551 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536))))))
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
theorem bgb_6_2048 : Interval gbAtlas 6 2048 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2058 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992))))) (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248))) (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))) (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)))))))
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
theorem bgb_7_1184 : Interval gbAtlas 7 1184 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1191 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 (concat bgb_7_384 bgb_7_416))) (concat (concat bgb_7_448 bgb_7_480) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))))) (concat (concat (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 (concat bgb_7_832 bgb_7_864)))) (concat (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024))) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8feeafee8fee8eee8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813544 * 2 ^ 32 + 4276678376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37181.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[2,3]⟩,⟨.or,[4,5]⟩,⟨.and,[1,7]⟩,⟨.or,[0,9]⟩,⟨.or,[1,7]⟩,⟨.and,[2,3]⟩,⟨.or,[6,11]⟩,⟨.and,[8,12]⟩,⟨.or,[10,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276678376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276678376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37181

open PEqualNP.Outside.L_meta_37181 in
theorem PEqualNP.Outside.L_meta_37181 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276678376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276678376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
