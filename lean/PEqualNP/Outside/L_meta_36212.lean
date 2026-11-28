import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36212.Model
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


end PEqualNP.Outside.L_meta_36212.Model

namespace PEqualNP.Outside.L_meta_36212
open PEqualNP.Outside.L_meta_36212.Model
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

def SBf (j : Nat) : Nat := [6, 8, 6, 6, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36212

namespace PEqualNP.Outside.L_meta_36212
open PEqualNP.Outside.L_meta_36212.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x110034a0c052ce500020627bf43bd43be42bc42be41bc41ee21ec21bf40bd40ef20ed20
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1098096292871d531063aa7a05914520
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => packedAt s0K4 (208+((h/4+packedAt s0K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s0K3 (111+((h/1+packedAt s0K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x7ffc1ffffffff03ffffc0ff83fffffe7e31ff
  | 2 => 0xfffffe07f03ffffc1e07fffffc1e07ff93fe4f
  | 3 => 0xf81ffff8003f07ffe007ff07ffe00781e3cf8c
  | 4 => 0x1fffffffc007fffff80007fffff801fc0ff0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x9044444122084100a4494848812294a4261095
  | 2 => 0x218888324452822c0a8291932414215890e64a
  | 3 => 0x52d51490eaa44d556144ea45cb40560d634b8c
  | 4 => 0x651a21248c06969a5390308672996011d80d60
  | 5 => 0x861c39c70f38e7e39de73ce063118461ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcccc0c0fcccf0c0fcccc0c0fcccf0c0fcccc0c0fcccf0c0fcccc0c0fcccf0c0fcccc0c0fcccf0c0fcccc0c0fcccf0c0fcccc0c0fcccf0c0fcccc0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36212
namespace PEqualNP.Outside.L_meta_36212
open PEqualNP.Outside.L_meta_36212.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x23004d08d0a54d1f143c5841c304064a401803c00009007401200003802200a00000000048000190004000000002700000002e980182c01002007111b0e00080881e040030200001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51903eca3205d94640bea8c81f551902eaa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a05f14540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f681907e10320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2107b88420f6108417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fba0e21f441c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fba0a21f441443ec62887d4c510fb10a21f521443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5090afea6a177d4d42afa9a857c5350bb8a6a15714d42dfa1a85bd4350bde84a16f90942bfa8a85f75150aeea2a15f14542fa28a85745150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3997d94732bb28e657d51ccbeaa3995d54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c53506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f7cca31ee994637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c7bc8698f750d31bfa92637c524c7bc6498f70c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863df430c7b88618df94831bea9063df320c7ba6418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21fba0e43f441c87ec6390fd4c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087ee8210fd10421fb18843f531087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa
  | 2 => 0xa0005680015e0ee2a0bf9503b65e8aa80005a1b8e422130ea20000003600380792a000000002674686103e00037e168e100946e8b5461981a800031a25000200bf2664407acd3129356310d400035a52c0a1263de148352644b013c8f800000a180019b00093400000378a2800000142428059b64360011607300000000000000220b08001f2000ca0003da5094807b000000a202a0001c89400000000000069000000ab2703960000025c0620006f00028c84c411ae000000000000001280000000098897000000a0d210002ba949228000007c400000270460002713728fc0000029e7fc8600016a000fe9654f6000bc2150001e50e89701a5c8b81101cc40425a944a8000000d12d8410000001fc000e600000004876218032000000003ac840b707626e00127805022340000000300008d8002ee000000003b80f50f0002d67dcc1a820000000027e0008d50918e0000013e10700000126000000000358d93105a0001890005e4891c50000000000025a1c07a0280d80004083500014cbd8004da195171b5000000001035244b1151f4000a4d078002da9589f80000c7b0050000000000028b146358000000004f0eb9361ba0dc0000000031401000000280d38001c82a40001646c000000000002502118b52c000060ee3e02893713d2c68087aa8f098138c281d4329dcb48ff000001159f60001206f800000040641fb352000000001da0002c9d900000000190000098ca8904aa830f091915c3dc2e1d04de5d44f8e3000000af8000000a020040140101c0500c050000000804000000040201801008020000003c0401c0b01011000120080102001010070100801c0300008008070080004c0701c0f000010000003400008040080200400000000140200c0c004080141001005054010140600400000040681105801000210000900802004010000005406004030140000c00004000080f01801020010100009c0000c0300400000010280103c05020000000002003004060080000c05008000240400c0a004010081b0040203400004220000000000000000000a018000140001000000010281202c000340600c0000c0f03800004020080002002000060000d020000380500c0000000000030440000000014070040201402000030000500c04bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857
  | 3 => 0x4e8000000000003c84d8e00000e80026b4be0004e00016085cba0002cc65c0002107e7d4738dc000000908004223540f8000001854020e0009806d000000000001a321a0011ea3e13a3384d1d40608050e2780069210d1343d04d4001203aa20c000002ec524301de0ce90c878154289747b00048c10c7980033c001391aa4008a4fc9da000858190000ac0b08d0411643a1038004d00ccb5259376001028d24101c44f0fc0a809cd79930340011327d29c000332273920008025e1709fc78000000000f38003000005fa6a00000092a76076a388107426606d119600001bd32a28000088630003cc000430000c87e85d8000000000000010a470000003667cc0025700060800000000000000ea0464450300022e34c4680000000000000000000000004c2a540002b4b600000000000618a521f4f290445800314605121c107c77c6d95c3420b845251078a1ce71d828e14055a44380000be1cd41a000560573fc090001223582dcb11060fe780da0000000005d00026000000269000000e92850007e0a8800412550648510be000a19e938e0002492447035cb795839e8c04909848e794538c3478094ce000194020d101331a1b48b1ee370938ada842980701c23b108078599bd32c2b4f204014c16c9da0b494000639dd45e3c42a804000674461a03a63f4000000400008484402e92cf18e90000d0b89450006c400000480668d91271b06904790e1f61193d000000000c887d112000000c00000000008e0004780007e0004e82c10822a63c00039000308db80005e7446609613201ca90001de3944aa2233e1a0f900019a4513a91d0000000000014a00075800000004a0a97000000000910004c4f513e2e621c95a044a62f4979fc162a442e9ba17298cc923a264968000a438c0000016451a000001c34722bcc60aa0004e4228002800a5199a50f02f13980017c304f10e112655c0014806c564a68000003e140a49168000e52500000002f0e23324143a9c42fa2d80007a00000000000000001018cf000000000002ce18826a0a46248c2380000054d191132166f8000cb4d8001448f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xc54c82766194f209d58653c823e6414f208f59053c825e63947209758e51c825e63d52209758f548827661d52209d587548825e63952209758e548823e6494e208f59253882766114e209d584538823f64546208f191518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551209ed81544823e6515120c7d53534831c54d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520ce153204836451881209798f540825d63d50209d987540827561d50208f596540833860550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083655188420ce553400827965100209bd9520082e461480209ed9520082b8644802097d8d54c425c63553109798c54c425d63153108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798e52c425d6394b10b558c41c42b4644c710b558e21c425e63d52109758f548425e63952109758e548423e64d4e108f593538425f6354a109718d528423e6414a108f590528425e6314a109758c528433561d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d9584524427665d0510d514f414436452d0510cdd5041442d56310510d514c41443645210510d514e3144364528c5109d19531442b4644c510d914931442766588510b558e214436452885109d19521443645248510d914a104425e63d50109758f540427661d50109798c540425d63150109b988540426d621501097596530425e6314c109d984530425e63d48109758f520423e64148108f590520425e63148109758c520427661148109d597210435553c84109d59421043555308410d554f100427965840109dd9510043555344010b9189100427b6544010
  | 1 => 0x69c63504419dd9541106d463504419b98854cc66d6215331b518543cc69d640cb31b558c41cc79643107318f992528c63d6494a31b5587328c63f64542318f191508c63e649513197d8d544c67761551318f994544c71d631513197996434c71c5490d3197195434c71c5450d31b5185434c71c548c93197994324c69d640c931c7150324c73454cc531c7152314c67a60d50319e583540c65e631503197597430c65d6510c31b5587320c65f654c8319d594410c794431043197d95310c69c644c4319dd95310c6b4644c4319798f54c865d63d5321cdd8554c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c87556194f21c795153c871d5454f218f99053c863d6414f21d594f41c87355410721b558c41c87565310721d594e31c86b4644c7219798f548865d63d52219e983548867960d52219798c548865d6315221d554f218865f63551219718d544867761551219ed81544867860551219798c544865d63151219d586534863f6454d218f191534867b6054d219e181534865e63141219758c504865f63550219718d540865e63150219758c540867a60150219e580540863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520865e63944219758e51086756510421b558c41086e562104219d59631086b4644c421b558e210866f65484219dd95210863f64540218f191500865f63540219718d500871d53d0b40c754d42d02b86050b40c794f43902b46150e40a758c42903565394640d554e51903565354640d554d519031e5390640a758c419031e5310640cd544419029d63d02409798c525025d63149408f99742502b860509409798c515025d6314540ad185431025f63548409718d521027761548409d185521023d6590840a758c421025f63544409718d511029d6310440ae580411029d63d00408fd95401027b65500409dd8554cc2746155330c718d54cc3376155330cd18554cc31d54d0f30c755043cc31d54ccb30b558732cc31d544cb30c755331cc29c644c730c755131cc27661d52309d587548c2d46150e309dd85528c2746154a30a7590328c29d64cc2309758e544c26f62551309b189544c27761551309d185544c25e65d0d3097994434c23e64149308f590524c25e65cc930b5587324c25e65cc530a7191314c25e63d50309d987540c27561d50309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c25f6550c30b5185430c25d658c830a7590320c23f64544308f191510c3376454430cd191510c3564354430d550d510c3563254430d50c9510c25d658c430d5546310c355510c430a7593300c35551cc03097d95300c355514c0309ed95300c25f63553209718d54c827761553209d18554c825e63153209758
  | 2 => 0x536000046106000000cf00022a670000621de70419800000000888cd1e20000000c01c000000000005c87096c0c842cad1fd0002549792400050c499b83c07a8c51af000070e3a050004303c86d3d84b029a0c2d23a8f798317e18ca5113238228e885017200018a1a2c2604cb86907422c1083d1d80649007d20a0a0000000005205202c010024492012fe23454a092fa72cbc1080aa2cca59ff00080d0b0d60c043c0006c28c53c421b7000000e180022c4ec00160000000001d51680000980007e714000000400006a9a43ee1084021326a2d87da002326f40510a20e33c8b9582f44f8a10ce2e62ec951b5326474331cc0726b8449900765990b9400003d425000208570e70ab000000008ae06e1d07015704e0445397b03a3d0730bc05a034080001d0041103801004010680700801030090000e0040a00007004000500b024030101a0000a02c00000070e81209c020000d00009004080042c0540a004100040a0100501008000000000501809018090040101c050f4000080e0080004c000080702802004060000100827018000000b008000842a010100d8001a8010040901401000010ec130100501000060010002200000014000540e00000000120040701408000000040f074000000000801000180180302401030000a40700c0402800000040000201c02024000140000401108010240c0004804c0200403002776154b439d18552d0e7661943439d58650d0f574314543cd90c5150e3f6550c43ad1854310e5f6550c43b51854310eb46150f4297d8d51d0a5c63547429798e50d0a5d63943429d98650d0a7561943429798e5190a5d639464297d8d5090a5c6354242c714f4350ab46150d42d5d4f5150b5453d4542d5d4c5150b545314542d6d4f5050b5853d4142dcd475050b7051d4142d6d4c5050b585314142dcd445050b705114142ced0c5050b394314142ce9085050b1d53d08428fd954210b1d5350842ae1814210a6f65508429d98754cca7561d53329e98354cca7960d53329d98454cca756115332b518543cca3f64547328f19151ccb376454732cd19151ccb564354732d550d51cca7661d52329d587548cad561cca328fd91508ca3c645423297d8d544ca7761551329d185544ca7b60551329e181544ca5e6590d3297195434cad46150d329d984504ca7561141328f596540ca7761550329d185540cb1c6355032cdd85540cb3461550328f990540ca5e631503297597430cb1d54d0c3297594430cb1d5410c32c7553320cad561cc83297d95320cb1d544c8329bd95320ca5f6354b419718d52d065e63943419758e50d065e6394a419758e529069c6350a41ae181429065f63542419718d509075453d0541c714e41507546154c41c754e431071d53d0841a718d421071d5350841add8542106b860508418fd95411
  | 3 => 0xff0702740006c9ad046000941bf29a578938a22b65b81213c0708482f0042720f81e0001be654fa9770285140d000000000cc8fd0006d0f59862c61e02607e17c000a8918374280030003ba83c269f62da5a90702a18e7c4c38dd330554001c22623d824897000718eca0b000760230003ca408e2191006174d080026c7a4fc14e13c000000bd1700002017109c8106a141000001010003a44503a8000000007f0003e4438379de0865ac6919b316324a21263a8214391d30a200000000000000e4818000148228351dc6a803964358000ba8003c6674000b00003ac001a30ac6c4470572525246f2063003404b0000ca3a44085f3241c4e40124287847980000020c0b00035000054000000634001882ba000cd09b1da3e056123130000000003f20007280026e3188d0290000006d93010c3907b8001f4370910a5000000f38004105d03f86e0007c0ab034188788e7a180823886c11f1a623c8d8ba3a01a06d14c0d61f0190d7122240258540ec320279da154208128002a6790110e72b2424588e300057d06a0705c2dc7f89f4327ecee0000906500a899000728f317611032c3b9543444ccde0870004b89e9db42a67cd292d2f211c518c02e00ac0b8d11386ccf68ca3ac0000000f12806c53150356164ef8c321a548308303803f0081d722459cfe1031824c8a387a1f25949c1ee000000c205a2f868059100256274d30f014202c928260ce624b79b624263057a10268588df1fa20207d0505c05e034740f21986a4bf1f400a2d4010730b06c8e686a0b64fc1b0c20004403d98515a1100001e376000f4211304000c71f323c69ccb16813463cdc8c
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x160066000000000c230b5132054000090000000003400170120003ce4551c1100282883840001834c1c54314142c32a6302842161463185540ca8a38aa8218658555161cc832c32a63028420e1454185434c60ebb0a819263251d161cc831a28e8b0ca790c557694c41c870ca98c0a16818518c6155330a28e2aa087986155458732cc20e3b2a898e61455d03254430a28e8a88621861564547300c28a3a2c229a21155d85310510c8ac62908288624641493144322b18a510a219154c6244010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x210600008148755161cc8328148755161ccb30814865d032544308148759151cc030
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 6 => packedAt s1K6 (731+((h/13+packedAt s1K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s1K5 (20138+((h/221+packedAt s1K5 (17928+(h % 221)*10) 10) % 963)*11) 11
  | 4 => packedAt s1K4 (22272+((h/179+packedAt s1K4 (20482+(h % 179)*10) 10) % 647)*11) 11
  | 3 => packedAt s1K3 (1273+((h/8+packedAt s1K3 (1225+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s1K2 (244+((h/1+packedAt s1K2 (240+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf03ffff81fffff81fffff83fff03fffcfc7e3f
  | 2 => 0xffc07fffe03f83fe0fc0ffc3fffc1e03639fcc
  | 3 => 0xffff81fffffffffff000fffc1fffffff83e3ff
  | 4 => 0x1ffffc003ffffff00001fffe003fc03f0
  | 5 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x94850808c489108052c52804a52132a82c2e15
  | 2 => 0xa19314914392159605545a42cb6514196196cc
  | 3 => 0x420a25220924422aa02094a8128a495282c16a
  | 4 => 0x8b2c59c492075bcd39b606229cf39063f403b0
  | 5 => 0xc3061871c386371ce38e73300c20183db7800
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0fa00aa00faaafaa0fa00aa00faaafaa0fa00aa00faaafaa0fa00aa00faaafaa0fa00aa00faaafaa0fa00aa00faaafaa0fa00aa00faaafaa0fa00aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36212
namespace PEqualNP.Outside.L_meta_36212
open PEqualNP.Outside.L_meta_36212.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xe00156900046228030a0001c62be43bc43bf42bd42bf41bd41ef21ed21be40bc40ee20ec20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x58010096a90871c535063ca7205954420
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
  | 4 => packedAt s2K4 (212+((h/4+packedAt s2K4 (192+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s2K3 (111+((h/1+packedAt s2K3 (108+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffff83ff83fffe0ff83ffffc1fc0fffe4ff39f
  | 1 => 0x3fffc1ffff07ff07fc3c1ffe1fff03fb13cf3
  | 3 => 0xfc1fffe003ff87ff8003fe1ffe00ffc1c1cf1c
  | 4 => 0x1ffffffc0007fffffc001fffff0001fe0fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1080888404a000029804822802441518065185
  | 1 => 0x484910492104c250224151452092a0a4912432
  | 3 => 0x295a21436a4c4eb506227517540aca85c18e18
  | 4 => 0xb2944a1240691529cca8201a992c03096a0bc0
  | 5 => 0xc318739c738e67ce7733b98310308c31fdf000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36212
namespace PEqualNP.Outside.L_meta_36212
open PEqualNP.Outside.L_meta_36212.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x4088a71a0c201df32ee32dd32ed32cd32bf41bd41be40bc40
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x26080c0ea420a6a9c658f544cb18a899634cb41c69928338505071a6520634c840
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xd10a2983544ca0c654c941c24c8505060f654ca40
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
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
  | 4 => packedAt s3K4 (156+((h/3+packedAt s3K4 (144+(h % 3)*4) 4) % 11)*5) 5
  | 3 => packedAt s3K3 (224+((h/2+packedAt s3K3 (216+(h % 2)*4) 4) % 12)*4) 4
  | 2 => packedAt s3K2 (155+((h/1+packedAt s3K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xe0fffe07e0fc1f87fe1ff0ffe0f0783ece7e93
  | 1 => 0xff07fffffffffff81fe0ff07ffffffff318fff
  | 2 => 0xfff83ff800ffe1ffe000fff8ff007fc1c1f31c
  | 4 => 0x3fffff0001ffffff0000ffff8001fe03e0
  | 5 => 0xffffc000000001ffffffffff00000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2a1182314528a881660530296891489c463691
  | 1 => 0x40400442004000100820410201241220108826
  | 2 => 0x8622a890d6928baaa1149ab0ba826585c15318
  | 4 => 0x14b53124941acdccd35608a0dccb4109ea03c0
  | 5 => 0x18c621c718e311771d98ecc4100c0631bdec00
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeee8e8ccccc8c8eeeee8e8ccccc8c8eeeee8e8ccccc8c8eeeee8e8ccccc8c8eeeee8e8ccccc8c8eeeee8e8ccccc8c8eeeee8e8ccccc8c8eeeee8e8ccccc8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36212
namespace PEqualNP.Outside.L_meta_36212
open PEqualNP.Outside.L_meta_36212.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xb000e4c000080044a1318000002a0030000a41a3080859b406850732706a11274c175a4029e2c05522487d392563d28050000000c20170000410406e1240ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x30e064284d3c6c240100f05498b8f4412d2904002c0000000c016cac854c68907800155d1800a41c7cdc01416874d160f800e56404111080d97c20c120385c00b4193948a000891ccc60c934e845303524ec0000a8010974d5800000b0fc010c9c0001880144080170003d1401580000500000018470940000c578480155508cbc5806400006103418140a0818180400020800000008040e000e18000c00001a000601765110eeaa221cf94a429ea8c853e5210b5ca4214f544429f2a6653d54ccaeca3995d547329faa2653c544ca7ca5a0cf55241af29c835d53906dea4a0db14941d7a92833c5250758a4a0cb14941dba8a833e54106bca620d754c41cf216639c42cc73e8398e7507319f2a4633d548c6baa718ed50631daa0a639e424c7388498f5d4531cfa0a63d6414c73a8298f550531caa0a633e540c67aa818d794c319faa6433c54c87aa6390cf952219eaa4435e53886baa710eb10a219faa2433c544867ca810cf55021af298435d53087588410f54c421bd280437950086dca5205b54a40afa9a815c535027ea8984f151309f2a0613d540c2dca4185b54830bb2886175510c35885904f952209eaa4413f5448278a89057d4d20ae29a41ac42482eea2905d145209f2a6213d54c42bca7885754f10ea98e21d5314427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x70023ce3000541064404c024300548020d00b400281180013228c6250731a9189418c6a46250531a5584424c6956490531a3189414c6c46250531e1d89414c6946250531e1189414c6846250531c5d5131c862d6510821c55513108784424c421ca1095008751315402195584535032442145208b18954c4315544c710
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x204050575109310878021262a8043411c9544c710
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
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (826+((h/15+packedAt s4K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s4K4 (2937+((h/33+packedAt s4K4 (2673+(h % 33)*8) 8) % 130)*8) 8
  | 3 => packedAt s4K3 (833+((h/7+packedAt s4K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s4K2 (150+((h/1+packedAt s4K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3fff07ffffc3e0f87ff87fe1fffe07c39f3f3
  | 1 => 0xfc3fff83f0fffff00787f8ffe3c0fffe263c9f
  | 2 => 0xffc1fffc00ffc3fff807ff0ffc00ff83c7cf1c
  | 3 => 0x1ffffff0003fffff8000fffff0003f80fe0
  | 5 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x48041110a0204002810981120452212808d131
  | 1 => 0x11092209094a225042c248a522844a52222486
  | 2 => 0x28944520629004a58804920a480a9508c54b18
  | 3 => 0xb2a9884a481aab3954d0408d932c0613700ec0
  | 5 => 0xc3310e738ce333ce676764c102301863bfb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfae8fae8eac8eac8fae8fae8eac8eac8fae8fae8eac8eac8fae8fae8eac8eac8fae8fae8eac8eac8fae8fae8eac8eac8fae8fae8eac8eac8fae8fae8eac8eac8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36212
namespace PEqualNP.Outside.L_meta_36212
open PEqualNP.Outside.L_meta_36212.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x1b3a000001e2421844000000a0929a005d30d1c9cf2a009030722b5003002909600acf940255188164ce0c586482800a49100074c200e14048330b044ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5d00260d006f30363e5b18004d3f0045402b346d00410000070000734424060054190e46003704582f2511382743652e470b02001300001650003500000a006a00034f0956705a0000007461390862105714550072016c64286968004c3b2159004e3c710000126e66320f00606b001a00000000002d1b003a1d5f67000c4a0000003d000000000000492c00004b331e15515e00000000000053001763000000001c000005000000000000231f5c225229000000002a4842003120020104008001000001000000000000010300000000000380800181838000800308800600808180db94b43b6a96877a50d0ef2a1a1eb50842bd28085795010a7ca9194f55232bd2846579508cabca720d754e41b7a92836c52506bca620d754c41b7290836d52106f4a020de54041aea9c633f544c678a898dbd4931b6292637b504c6f0a098e7d5131ce2a263cf524c798a498f5d4531eda8263d8504c6bca618d794e21aea9c433f5448678a890cf950219eaa0435e53086baa610de94021bca80439f31d033a63a04f55240b7294816d52902bea6a05714d40cfa9a819c535033e62a0674c540dda82813e54102dca4205b54840dca06613e548c27aa9185b94a30b6a94613e540c27aa8185b94830b6a906176510c2eaa2186e50030e798e41cd31c835e81906b503209f2a4413d54882daa5106e50220afa9a415c5348372809073d4d20e629a41cf314839a62907ad4120d7a0241ea404835a80907a50120d4a0241eb30483d060904f950209eaa0416e52082bca7885754f10ea98e213e548427aa9085b94a10b6a9421b940843d24108754c510dca0221e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2cba018031a00200059c12891e000a9849400a99000e8881ae0f100c2ca5095010a696014941c6150504c74852141318e580544861c654c540ca549400c3315150030c614d404824c654c520aa59240482c86350120e2d8d40483886350120e2d4d40483885350120e2cc540483893150120aa59030482e1610c120ca54940843295448210e44c540443c13148110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xd10000a14ebb1a809048a76d4d40482443b262a0241421d53150120
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s5K5 (826+((h/15+packedAt s5K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s5K4 (3471+((h/39+packedAt s5K4 (3159+(h % 39)*8) 8) % 187)*8) 8
  | 3 => packedAt s5K3 (952+((h/8+packedAt s5K3 (912+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf03e1f0ffffe1f0f871fc3c1c7fffc1f0743f3
  | 1 => 0xfffffff07c3ffff007e1fffff8703ffe19fc9f
  | 2 => 0xffc01fff803fe1fff801fc01ff803fe1e18f1c
  | 3 => 0x1fffffc001fffffe0001ffffc001fe0fe0
  | 4 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x148531222a113102c212e2484494a455034131
  | 1 => 0x21080201004400100120048488210888081486
  | 2 => 0x429554641aa91365c8116a115502b345618b18
  | 3 => 0xb288889500c44b915440025a24b0188bc0ec0
  | 4 => 0x8c3110ce633199ce6699b338040c2211d7e000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfecceac8fecceac8fecceac8fecceac8fecceac8fecceac8fecceac8fecceac8fecceac8fecceac8fecceac8fecceac8fecceac8fecceac8fecceac8fecceac8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36212
namespace PEqualNP.Outside.L_meta_36212
open PEqualNP.Outside.L_meta_36212.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12ac72f000c62838880004a98a0040b0f86005892e36011807e41f0260dc52a0a2079778e508474a40a768343803a90a917a019805a01b0000d401e76000190001c0b6200d0026c801811000800112000821204b8000048801428d8001ffd5005fe54007f55005fc5401ffd4c01fe53007f54c07fc53017fd0c01fe43007f50c05fc4301ffd4801fe52007f54807fc52017fd0801fe42007f50805fc42007fcc801fe32007f4c801fc3200ffd44037f5100ff94403fd5100df54403fc5100ffd0403fe4100ff50403fc4100ffcc403df3100ff8c403fd3100f74c403fc3100ffc8403fe2100ff48403fc2101ffd4001fe50007f54007fc50017fd0001fe40007f50005fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x84400dfe44220027f82110003ff65480017fb2a4000dfd9520004feca90033fe65480077f32a4000ff59520005faca90033fc65480077e32a4000df1952001cf8ca90003ff64480017fb22400bff99120015fcc890003fd64480017eb22400bff19120015f8c890033ff5448017ff2a24000ff5512005ff8a890003ff63480017fb1a4000f7d8d20005bec690003fe63480137f31a4000ff58d20005fac690003fc63480137e31a4000f718d20005b8c690033ff5348001ff29a4000ff54d20067f8a69002fff4348001ff21a4000ff50d2005ff88690033ff5248019f7a924005ff94920007faa490017fc5248019f6292400bffd092002ffc8490003ee4248001fea124000fb5092002ff88490003ff324800bff1924000fb8c920007fa6490003ed324800bfe192400affd8520055fec29002bfe61480037f30a400aff58520055fac29002bfc61480037e30a400affd4520056fea29002bfe5148015fea8a400adf54520057f8a29002bff4148015ff20a400aff50520057f8829002bff3148015ef98a400aff8c520057fa629002bdd3148015fe18a4005ffc8520057de429002bfe2148015fe90a400afb4852002ff84290033ff5048009ff2824000ff54120027f8a09002fff4048009ff2024000ff50120027f88090003ff3048009ff1824000ff4c120027f86090017ff204800bfd9024004ff88120027dc409002bff1048009ff082400afe84120057fa209002bf91048009fe0824004ffd9420025feca10013fe65080077f3284004ff59420005faca10013fc65080097e3284004ffd9020025fec810013fe64080057f3204004ef990200157cc810013fd64080017eb204004ef590200057ac810013fc64080097e3204008ffd502003ffca810003fd540800ffe2a04004ffd8c20025fec610013fe63080137f3184004ff58c20005fac610013fc63080097e3184008ffd4c20007fca610003fd5308011fe2984007ffd0c20007fc8610003fd430800ffe2184005bf9882002ffea410017fe520800bfea904005ff1482002ffe8410017fe420800bfea104005ff1082002ffe6410017fe320800bfe9904005ff0c820027fec210012ff6108009ff3084001bf98420027fac21001afd6108009fe3084004bf18420037fea21001b7f510800dff2884006ff54420036faa21001bfc510800dffa084006ff90420037fa821001bfc410800dff9884006f7cc420037fc621001bfd310800dee9884006ff0c42002ffe4210017fe210800bfe9084005ff08420025fcc010013ff5008009ff2804004ff54020027f8a010013ff4008009ff2004004ff50020027f88010013ff3008009ff1804004ff4c020027f86010013ff2008009f79004004ff88020027f44010013fd2008009f69004005fe48020027fe2010013fe1008009fe8804004ff04020
  | 1 => 0x7fc310c027ff9086013ff8843009ffa421804ffc210c0097f3006004ffd4030027fca018013fd500c009fe2806004ffd0030027fc8018013fd400c009fe2006004ffcc030027be6018013fe300c009fd1806004ff4c030027ba6018027f9300c009ff8806004ff84030027fa2018013fc100c00bffb2e4005bfd972002ffccb9000efe65c800bfeb2e4000bf5972002ff8cb90016fc65c800bffb264005bfd932002ffcc99000afe64c800bfeb264000bf5932002ff8c990016fc64c8025ffaa64011ff95320007faa990047fc54c800bffb1e4005bfd8f2002ffcc790026fe63c800bfeb1e4000bf58f2002ff8c790016fc63c8025ffa9e4000ff94f20007faa79004bfc53c8023ffa1e4000ff90f20007fa8790047fc43c800bffa964012fbd4b2002ffca590017fd52c800bfe2964005fb14b2002ffe8590017fe42c800bf72164005ff50b20007da8590017fc42c800bff9964005ff8cb2002fdc6590017fd32c8001f69964005ff0cb2002ffec390016ff61c800bff30e4001bf9872002ffac390042fd61c800bfe30e4001bf18720087fea3900437f51c8021ff28e4010ff54720086faa390043fc51c8021ffa0e4010ff90720087fa8390043fc41c8021ff98e4010f7cc720087fc6390043fd31c8021ee98e4010ff0c72002ffe4390017ef21c800bff10e4005ff48720087da4390017fc21c8025ffa864004ff94320007faa190013fc50c8023ffa064004ff90320007fa8190013fc40c8001ff9864004ff8c320007fa6190013fc30c8021ff8864004ff84320087fa2190013fc10c8009ffb2c4004bfd9620027fccb1000efe6588009feb2c4000bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc91000afe6488009feb244000bf59220027f8c910012fc648801fffaa4400eff95220007faa91003bfc5488009ffb1c4004bfd8e20027fcc710026fe6388009feb1c4000bf58e20027f8c710012fc638801fffa9c4000ff94e20007faa71003ffc538801dffa1c4000ff90e20007fa871003bfc43880157eb14400fffd4a2002ffca510003fd528800bfe294400effd0a2002ffc8510003fd428800bfe2144000ffcca2002ffc6510003fd328800bfe1944004ffd8620025fec310013fe61880037f30c4004ff5862006dfac310013fc61880097e30c400dffd462006efea310037fe518801bfea8c400ddf5462006ff8a310037ff418801bff20c400dff5062006ff88310037ff318801bef98c400dff8c62006ffa6310037dd318801bfe18c4005ffc862006ffc4310037fd218800bfe10c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fe9844004ff0c220027fe4110013ef208800bfd9044004ffc4220027fc2110013fa1088009fe8
  | 2 => 0x300cdfac318013fc618c0097e30c6019ffd46300cefea318067fe518c033fea8c6019df546300cff8a318067ff418c033ff20c6019ff506300cff88318027ff318c033ef98c6019ff8c6300cffa6318067dd318c013fe18c6019ffc86300cffc4318067fd218c033fe10c6004bf98230027fea118013fe508c009fea846004ff14230027fe8118013fe408c009fea046004ff10230027fe6118013df308c013fd9846004ffc4230027fc2118013fd108c009fe0846000ffd9530005feca980037f654c0013fb2a6018ff9953001dfcca98003fd654c0017eb2a6018ff1953001df8ca980037c654c0073e32a6000ffd9130005fec89805ffe644c0057f3226000ff59130005fac89805ffc644c0057e3226018ffd51300bffca898003fd544c02ffe2a26018ffd4d3004ffca698003fd534c013fe29a6017ffd0d3004ffc8698003fd434c013fe21a6000ffd8930005fec498003fe624c001feb126000ff1893002df8c498063ff524c001ff2926000ff549300c7f8a49805fff424c001ff2126000ff509300bff88498027ff324c001ff1926000ff4c93004ff8649805bff614c02d7fb0a6016ff9853000dfcc29805bfd614c02d7eb0a6016ff1853000df8c29805bff514c02dbfa8a6016ff945300b7faa29805b7d514c02dfe28a6016ffd05300b7fc829805bfd414c02dfe20a6009ffcc5300b7be629805bfe314c02dfe98a6016f74c53004ff8629805bff214c02dff10a6016ff485300b7f84298063ff504c009ff2826000ff54130027f8a09805fff404c009ff2026000ff50130027f88098027ff304c013fd9826004ff8c130027bc609805bff104c009ff0826016ff44130027f82098013ff650c0097fb286004ff9943001dfcca180137e650c0073f3286004ff59430005faca180137d650c0013eb286004ff19430025f8ca18013ff640c0097fb206004ff99030015fcc818013be640c0055f3206004ff59030005fac818013bd640c0015eb206004ff19030025f8c818057ff540c029ff2a06000ff550300a7f8a818026fe630c013ffa986009ff94c3004ffaa618027fc530c013ffa186009ff90c3004ffa8618027fc430c009ffb106004ff9883002dfcc418013ee620c001773106004ff58830005fac418013ed620c00176b106004ff188300affea418003fe520c001fea906015ff148300a7fe8418003fe420c001fea106014ff1083004ffe6418027fe320c001ef1906009ff4c83004ff86418027dc320c009ffb086004bfd8430027fcc218006fe610c009fb3086001bd98430027fac21804efd610c009fab086000bd58430027f8c218012fc610c027ffa886013dfd443009ffca21804ffd510c027bea886013ff1443009ffe821804ffe410c027fea086013ff1043004ffe6218027df310c013ff1886009ff4c43009fba621802
  | 3 => 0xf31a8000ff58d40007f8c6a0026fc6350041ffa9a8000ff94d40007faa6a0083fc5350005ffa1a8002efd0d40017fc86a000bfd4350001dea1a8002ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0016fc6250041ffa928000ff94940007faa4a0083fc5250005ffa128002efd0940017fc84a000bfd4250001dea128002ff10940007fe64a0003fe3250001fe9928000ff0c9400fffec2a007eff615003fff30a8001bf985400fffac2a007efd615003ffe30a8001bf185400fffea2a007f7f515003fff28a801fff545400fefaa2a007ffc5150005ffa0a8002efd0540017fc82a000bfd415003fdea0a8002ff105400fffe62a007fdf315003fff18a801fff4c5400ffba62a007ffc315003fff90a801fff885400fffa42a007ffc21500057fb028020ffd4140027fca0a0003fd5050009fe2828002ffd0140017f680a0013fe4050009df2028004ff101400277880a000bf8405003fff8828004ff841400fff420a007ffd105003ffc8828004ff0414004ffecb98026ff65cc013ff32e6003bf9973004ffacb98002fd65cc013fe32e6009bf1973004ffec998026ff64cc013ff3266002bf9933004ffac998002fd64cc013fe3266009bf193300f7fea998077fe54cc001feaa6601dff1533004ffea798027fe53cc013fea9e6009ff14f3004ffe8798027fe43cc013fea1e6009ff10f3004ffec598027fe62cc00b7f3166009ff58b30005fac598027fc62cc03dffa966000ff94b30007faa59807bfc52cc03bffa166000ff90b30007fa8598077fc42cc013ff9966009ff8cb3004ffa6598027fc32cc013ffb0e6009bfd873004ffcc398006fe61cc013feb0e601cbf5873004ff8c398006fc61cc039ffa8e601cdfd47300e7fca398073fd51cc039bea8e601cff147300e7fe8398073fe41cc039fea0e601cff1073004ffe6398027df31cc013ff18e6009ff4c7300e7ba6398027fc31cc039ff90e601cff887300e7fa4398073fc21cc03dffa866004ff94330007faa198013fc50cc03bffa066004ff90330007fa8198013fc40cc039ff8866004ff843300e7fa2198013fc10cc009ffb2c6004bfd9630027fccb1800efe658c009feb2c6000bf59630027f8cb18012fc658c009ffb246004bfd9230027fcc91800afe648c009feb246000bf59230027f8c918012fc648c037ffaa4601aff95230007faa91806bfc548c02d7eb1c601bffd4e3004ffca718003fd538c013fe29c601affd0e3004ffc8718003fd438c013fe21c6004ffd8a30027fcc518016fe628c009feb146000bf58a30027f8c51806fff528c001ff2946000ff54a300dff8a51806bff428c001ff2146000ff50a300d7f88518027ff328c001ff1946000f78ca30007fa6518027fc328c001ee1946004ffd8630025fec318013fe618c0037f30c6004ff586
  | 4 => 0xffc519404bffa0ca025ff9065012ffa8328097fc419404bff98ca025f7cc65012ffc6328097fd319404bee98ca025ff0c65012ffe4328097fe219404bfe90ca025ff08650025fcc128013ff5094009bfa84a003fed4250027f8a128013f85094009ffa04a004ff10250027fe2128013fe1094009fe884a004ff04250025fecaa8003ff64540017fb22a024ff99150015fcc8a8003fd6454049fe322a002bf1915001ffea8a800ffe5454007feaa2a003ff15150007fec6a8002ff6354001ff31aa000ff58d50007f8c6a8026fc6354007ffa9aa003dfd4d5001ffca6a800ffd5354001bea9aa003ff14d50127fe86a8003fe4354001fea1aa024ff10d50007fec4a8002ff6254001ff312a000ff58950007f8c4a8016fc6254007ffa92a003ff9495001ffaa4a800ffc5254049ffa12a000ff90950007fa84a8093fc4254001ff992a000ff8c950007fa64a8003fc3254047ffb0aa023bfd855011ffcc2a8006fe6154047feb0aa023bf5855011ff8c2a8006fc6154007ffa8aa003dfd455001ffca2a800ffd5154047bea8aa003ff1455011ffe82a808ffe4154047fea0aa023ff1055011ffe62a808fdf3154047ff18aa023ff4c55011fba62a808ffc3154047ff90aa023ff8855011ffa42a808ffc21540077fb02a003ffd415001ff6a0a8013fe5054009bf282a004ff14150026f8a0a800ff85054049ffa02a004ff1015011ffe20a8013fe1054047fe882a004ff04150027fecb20012ff6590009ff32c8003bf99640027facb20002fd6590009fe32c8004bf19640015fac92000bff5490005ff2a48002ff55240017f8a920013ff6390009ff31c8009bf98e40027fac720002fd6390009fe31c8022ffd4e40007fca720003fd5390045fe29c8002ffd0e40017fc872000bfd4390005fe21c8004ffd8a40027fcc520016fe6290009feb148000bf58a40027f8c52008bff5290001ff2948000ff54a40117f8a52000bff4290005ff2148002ff50a40017f88520003ff3290001ff1948000ff4ca40007f86520013ff61900097fb0c8004ff9864000dfcc320013fd61900437eb0c8004ff18640025f8c320087ff5190043bfa8c8021ff9464010ffaa3200877d5190043fe28c8002ffd0640017fc832000bfd4190005fe20c8021ffcc64010fbe6320087fe3190043fe98c8021f74c64010ff86320087ff2190043ff10c8021ff4864010ff84320012fe6090009ffa848004ff94240027faa120013fc5090009ffa048004efd0240017f68120013fc4090009fc2048004ffc4240027fc2120013fa1090009fe8848021fe44240027f82120003ff65500017fb2a8020ff9954001dfccaa0003fd65500017eb2a8020ff1954001df8caa0012ff6450005ffaa28020efd5140017fca8a000bfd5450005fe2a28002ef15140007fec6a0002ff6350001f
  | 5 => 0x4d3204ffca699003fd534c813fe29a642bffd0d3204ffc8699003fd434c813fe21a642cffd493202ffca499003fd524c80bfe292642bffd093202ffc8499003fd424c80bfe2126409ffcc93204fde6499017fe324c80bef192642affd8532155fec2990abfe614c8037f30a642aff58532155fac2990abfc614c8037e30a642affd4532156fea2990abfe514c855fea8a642adf54532157f8a2990abff414c855ff20a642aff50532157f88299027ff314c855ef98a642aff8c532157fa62990abdd314c813fe18a6405ffc8532157fc42990abfd214c80bfe10a6400ffd8132005fec099003fe604c801feb026400ff18132025f8c0990b3ff504c859fe282642bffd013215ff880990abff104c855ff082642aff44132157f82099017ff650c80b7fb286405ff9943201dfcca19017fd650c8017eb286405ff1943202df8ca19017ff640c80b7fb206405ff99032015fcc819017fd640c8017eb206405ff1903202df8c8190a7ff540c851ff2a06400ff55032147f8a819026fe630c813ffa986409ff94c3204ffaa619027fc530c813ffa186409ff90c3204ffa8619027fc430c80b7f3106405ffd483202ffca419017fd520c80bfe2906405ffd083202ffc8419017ee420c80bfea106400fb5083202ff88419017ff320c80bef9906405ff8c83202fdc6419017fd320c80bee9906409fb4c83202ffec219016ff610c80bff3086401bf9843202ffac21909efd610c80bfe3086401bf1843213ffea21909f7f510c84fff2886427ff5443213efaa21909ffc510c84fffa086427ff9043213ffa821909ffc410c813ff9886409f7cc43204ffc6219027fd310c84fee9886409ff0c43202ffe4219017fe210c80bfe9086405ff0843202ffec019017fe600c8097f3006405ff58032005fac019017fc600c853ffa806429ff14032147fe80190a3fc400c84fff8806427ff8403213ffa201909ffc100c8077eb2ca004ffd9250027fcc92800afe6494009df324a002af99250027fac928002fd6494009deb24a000af59250027f8c928012fc6494007ffaa4a003dfd525001ffca92800ffd5494001beaa4a003ff15250027fec728013fe63940137f31ca004ff58e50005fac728013fc6394007ffa9ca003ff94e50006fca72800ffd5394007fe29ca003df14e50137fe8728003fe4394001fea1ca026ff10e50027fec528013fe629400b7f314a004fb98a50005dcc528013fd62940017eb14a004fb58a50005dac528013fc6294007ffa94a003ff94a50006fca52800ffd5294007fe294a003df14a50137fe8528003fe4294001fea14a026ff10a50007fe6528003fe3294001fe994a000ff0ca50027fec328012ff6194009ff30ca001bf98650027fac328096fd6194009fe30ca004bf1865001ffea32800f7f5194007ff28ca003ff5465012efaa328
  | 6 => 0x5fea0a8433ef50542017f882a10cfff3150867ef98a8433ff8c54219ffa62a10cfdd3150867fe18a8405ffc854219fde42a10cffe2150867fe90a8433fb4854202ff842a1003ff60508017fb028400ff98142007fac0a1003fc60508097e3028434ffd41421a7f8a0a100bff4050805dfa028402ff1014219ffe20a10cffe1050867fe8828433ff0414204ffecb99026ff65cc813ff32e6403bf9973204efccb9900e7e65cc813feb2e6400bf5973204efacb990027d65cc813fe32e6409bf1973204ffec999026ff64cc813ff3266402bf9933204ffac999002fd64cc813fe3266409bf19332197fea9990c7fe54cc801feaa66431ff1533204ffea799027fe53cc813fea9e6409ff14f3204ffe8799027fe43cc813fea1e6409ff10f32197fea599017fe52cc801fea966405ff14b3218ffe8599017fe42cc801f72166400ff50b32007da8599017fc42cc813ffb0e6409bfd873204ffcc399006fe61cc813feb0e6430bf5873204ff8c399006fc61cc861ffa8e6430dfd4732187fca3990c3fd51cc861bea8e6430ff14732187fe83990c3fe41cc861fea0e6430ff1073204ffe6399027df31cc813ff18e6409ff4c732187ba6399027fc31cc80bff90e6430ff88732187fa4399017fc21cc813ffb066409ff98332025fcc199027fd60cc8017eb066409ff18332197fea1990cbfc50cc863ffa066431ff10332187fe21990c3fe10cc861fe8866430ff0433202ffecb19016ff658c80bff32c6403bf9963202ffacb19002fd658c80bfe32c6405bf1963202ffec919016ff648c80bff3246402bf9923202f7cc91900abe648c80bfeb246400bf5923202f7ac919002bd648c80bfe3246405bf1923217ffea9190bbfe548c801feaa4642eff15232155fac7190bfff538c813ff29c6400ff54e3204ff8a7190bbff438c813ff21c6400ff50e3204ff88719016fe628c80bffa946405ff94a3202ffaa519017fc528c80bffa146405ff90a3202ffa8519017fc428c80bff9946405f7cca3204fde6519017ff618c80b7fb0c6405ff9863200dfcc319017fd618c85b7eb0c6405ff1863200df8c3190b7ff518c85bbfa8c642dff9463216ffaa3190b77d518c85bfe28c642dffd063216ffc83190b7fd418c85bfe20c6409ffcc63216fbe63190b7fe318c85bfe98c642df74c63204ff86319017ff218c80bff10c6405ff4863202ff84319017ff608c80bff3046404bf9823202ffac119002fd608c80bfe304642fffd423217ff8a1190bbff408c85dfe204642dffc423216ffc21190b7fd108c85bfe0846400ffd9532005feca990b3fe654c8077f32a6400ff59532005faca990b3fc654c8077e32a6400ffd9132005fec8990affe644c8057f3226400ff59132005fac8990affc644c8057e322642cffd513215ffca899003fd544c857fe2a2642cffd
  | 7 => 0xa90e3fe64548057f322a400ff591521c7f8c8a900afc6454807ffaa2a403ff9515201ffaa8a900ffc5454801ffb1aa400bfd8d52007fcc6a9003fd6354801fe31aa409bf18d5201ffea6a900ffe5354807fea9aa403ff14d521c7fe86a9003fe4354801fea1aa438ff10d5201dfec4a900fff5254807f7a92a405ff9495202efca4a9017fc525480bbe292a403fb149521c7fe84a9017fc425486fffb0aa437bfd85521bffcc2a9006fe615486ffeb0aa437bf585521bff8c2a9006fc6154807ffa8aa403dfd455201ffca2a900ffd515486fbea8aa403ff145521bffe82a90dffe415486ffea0aa437ff105521bffe62a90dfdf315486fff18aa437ff4c5521bfba62a90dffc315480bff90aa437ff885521bffa42a9017fc2154801ffb02a400bfd8152007fcc0a9003fd6054801fe302a404bf1815201ffea0a900ffc5054871ffa02a438ff101521bffe20a90dffe105486ffe882a437ff0415202ffecb21016ff659080bff32c8403bf9964202ffacb21002fd659080bfe32c8405bf19642015fac92100bff5490805ff2a48402ff55242017f8a921017ff639080bff31c8409bf98e4202ffac721002fd639080bfe31c8436ffd4e42007fca721003fd539086dfe29c8402ffd0e42017fc872100bfd4390805fe21c8405bf98a4202ffea521017fe529080bfea948405ff14a4202ffe8521017bf4290805f7a148405ff10a4202fd88521017ff619080b7fb0c8405ff9864200dfcc321017fd619086b7eb0c8405ff1864200df8c3210d7ff519086bbfa8c8435ff946421affaa3210d77d519086bfe28c8402ffd0642017fc832100bfd4190805fe20c8435ffcc6421afbe63210d7fe319086bfe98c8435f74c6421aff86321017ff219080bf790c8405ff8864202ffa43210d7ed219080bfe10c8405ffd824202ffcc121012fe609080bfeb048400bf5824202ff8c1210dbff509086dfe2848402ffd0242017f881210d7ff109086bff0848435ff442421aff82121003ff65508017fb2a8400dfd9542004fecaa10d3fe65508077f32a8400ff59542005facaa10d3fc65508077e32a8400df1954201cf8caa1016ff6450805ffaa28402ff951420177ca8a100bfd5450801deaa28402ff15142007fec6a1002ff6350801ff31a8400ff58d42007f8c6a1026fc6350869ffa9a8400ff94d42007faa6a10d3fc5350805ffa1a8402ff90d420077c86a100bfd4350805fe21a8402ef10d42015fec4a10d3ff525080bff2928400ff5494202ff8a4a100bff4250805f7a128405ff9094202f7c84a1017fc425080bde2128402fb109420175884a10cfff61508677fb0a8433ff9854200dfcc2a10cffd61508677eb0a8433ff1854200df8c2a10cfff5150867bfa8a8433ff9454219ffaa2a10cf7d5150867fe28a8402ffd05420177e82a100bfe415080
  | 8 => 0xf54e4304ff8a721827ff4390c13dfa1c8602f7d0e4304ff88721827dc4390c13ffb148609ff98a4302dfcc521827fd6290c017eb148609ff18a431f7fea5218fbfc5290c05ffa148602efd0a43017f88521827ff6190c137fb0c8609ff9864300dfcc321827fd6190c7b7eb0c8609ff1864300df8c3218f7ff5190c7bbfa8c863dff946431effaa3218f77d5190c7bfe28c8602ffd0643017fc832180bfd4190c05fe20c8609ffcc64304fbe6321827fe3190c13fe98c863df74c64304ff863218f7ff2190c7bff10c863dff486431eff84321827ff6090c13ff3048604bf9824304ffac121802fd6090c13fe304863effd42431f7f8a12180bff4090c05fe204863dffc42431effc21218f7fd1090c7bfe0848600ffd9543005fecaa18f3fe6550c077f32a8600ff59543005facaa18f3fc6550c077e32a8609bfd9143017fea8a180bfe5450c05feaa28602ff15143015fec6a18f3ff5350c13ff29a8600ff54d4304ff8a6a180bff4350c05efa1a8609ff90d4304f7c86a1827fc4350c13de21a8602f710d43007fec4a1802ff6250c01ff3128600ff58943007f8c4a1816fc6250c79ffa92863cff14943017fe84a180bfc4250c77ffb0a863bbfd85431dffcc2a1806fe6150c77feb0a863bbf585431dff8c2a1806fc6150c77ffa8a863bdfd45431dffca2a18effd5150c77bea8a863bff14543017fe82a180bfe4150c05fea0a8602ff1054304ffe62a18efdf3150c77ff18a863bff4c5431dfba62a1827fc3150c77ff90a863bff885431dffa42a18effc2150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028604bf181431e7fea0a18f3fc5050c05ffa028602efd0143017f880a18efff1050c77ff082863bff441431dff820a180efd659480bffb24a405ff99252015fcc929017fd64948017eb24a405ff1925202df8c92900fff5494807ff2a4a43adf9525201ffaa92900ffc5494807be2a4a405ffd8e5202ffcc729026fe639480bfeb1ca400bf58e5202ff8c72900fff5394807bfa9ca403ff94e5201ffaa7290037d5394807fe29ca43affd0e52007fc8729003fd4394875fe21ca405bf98a5202ffea5290177f5294807f7a94a405ff14a5202fd8a529017ff429480bfe214a405ffd865202dfec329017fe61948037f30ca405ff586521cdfac329017fc61948037e30ca403ffd465201efea32900ffe5194807fea8ca439df5465201ff8a3290e7ff4194873ff20ca439ff506521cff883290e7ff3194873ef98ca439ff8c6521cffa63290e7dd3194873fe18ca405ffc865202ffc4329017fd219480bfe10ca405ffd825202ffcc129012fe609480bfeb04a400bf5825202ff8c12900fff5094807fe284a403df142521d7fe81290ebfc4094873ff884a439ff842521cffa21290e7fc109480b7fb2aa400ffd9152005fec8
  | 9 => 0x17fb12a800ff98954007fac4aa003fc625500b7e312a803ffd495401ff8a4aa00bff4255005dfa12a802ff1095421ffec2aa10eff6155087ff30aa801bf9855421ffac2aa10efd6155087fe30aa801bf1855401ffea2aa00f7f5155007ff28aa803ff5455421efaa2aa00ffc5155005ffa0aa802ff90554017fa82aa00bfc4155087ff98aa843f7cc55421ffc62aa10ffd3155087ee98aa843ff0c55421ffe42aa10ffe2155087fe90aa843ff08554007fec0aa002ff6055001ff302a800ff58154007f8c0aa012fc6055007ffa82a803ff1415401ef8a0aa00bff4055005fe202a843ffc415421ffc20aa10ffd1055087fe082a803bf5965304ffec929827fe6494c057f324a609ff59253005fac929827fc6494c137e324a603ffd525301ffca92980ffd5494c07fe2a4a609bf98e5304ffea7298277f5394c07efa9ca603d7d4e5304ff8a729827dc5394c13ffa1ca609ff10e5304ffec529827fe6294c0b7f314a609ff58a53005fac529827fc6294c07ffa94a603ff14a53217fe852990bfc4294c13ffb0ca609bfd865304ffcc329806fe6194c13feb0ca641bf5865304ff8c329806fc6194c07ffa8ca603dfd465301ffca32980ffd5194c83bea8ca603ff1465320ffe8329907fe4194c83fea0ca641ff1065304ffe6329827df3194c13ff18ca609ff4c65320fba6329827fc3194c83ff90ca641ff8865320ffa4329907fc2194c13ffb04a609ff98253025fcc129827fd6094c017eb04a609ff1825301ffea12980ffc5094c07be284a642ffd0253217f88129907ff1094c83ff084a641ff4425320ff82129826ff6554c01ffb22a600bfd9153207fcc8a980afe6454c01feb22a640ff19153015f8c8a980fff5454c07bfaa2a603ff9515301ffaa8a98037d5454c07fe2a2a603bfd8d5301ffea6a980fdf5354c13ff29aa609df94d5304ff8a6a98277c5354c07ee29aa640ffd0d5304ff886a9803ff6254c017fb12a600ff98953007fac4a9803fc6254c0b7e312a603ffd495301ff8a4a980f7c5254c81ffa12a640ff109531fffec2a98feff6154c7fff30aa601bf985531fffac2a98fefd6154c7ffe30aa601bf1855301ffea2a980f7f5154c07ff28aa603ff545531fefaa2a980ffc5154c7fffa0aa63fff905531fffa82a98fffc4154c13ff98aa63ff7cc5531fffc62a98fffd3154c7fee98aa609ff0c5531fffe42a98fffe2154c7ffe90aa63fff08553007fec0a9802ff6054c01ff302a600ff58153007f8c0a9812fc6054c07ffa82a603dfd415301ff8a0a9903ff4054c81fe202a63fffc41531fffc20a98fffd1054c7ffe082a609ffd964304dfecb21827fe6590c077f32c8609ff59643005facb21827fc6590c137e32c8602bf59243017fea92180bfe5490c05feaa48602ff1524304dfcc721827ff5390c13ff29c8609f
  | 10 => 0x100100700380080000000200580000000400100000580800080600380300280180400380400080200080a00400000a80480000600700500680480080000381b00200180200000680080000180180000000101200080100680c80100900280000000080480080400400a00080080680500400100000900480080400200400280100000300000680800180200000200000000000280100000300080b00100001e80080380280001900180200100480780001880000300200100000400d00180000180102580080300000780480000000100000380100780c80000f00280000280680100000080c80080200001380100080000080300280000580080000280000000280800000400480000000100101100080100380000100580880080180000580000000180b80800100000180380300280000700001080200000000300100080080280200100080180000a80100100800000500380080000080000000080880000680000800100880000480100000200300280280000080480180000080180d00280080200001500280180380080000500100000b00900600100080080700000800080a00180080300000100100300000100000000080100100180500200200000d80100180000280100080000000080000300000280280000080180100300080300080380000080480180380100080000000700180080100000400881480580080000080000000000080800000280780800680180000000d80180180000300100600000080000180180380000180000700000080300180300000400180000080000480000680080080b00100800800400180600481200980180900000080400000400100100000180080480380200000000000880600100000480300380080000600000000000000980480000500100480180d00300000000280500280080480000101400480000200600200000480f80080700280000000700180000300000700000280400080880502300180180000100500400000300e01580380200200380380300180080380580280380680700400580680000380080a00100400000080080580080e80900080000000000080080000280100080700380680580000301180000080100000000d80080080280580000080200000380000b00180280000080000380001100000300d00180100000700100480580700200000000280000000100080200080080080280382280400600000580000280280000000080300281000480a80000080080280400600000000380480200281280780500600200200aff65550057fb22a802ffd515401f7ea8aa00bfe5455005bf2a2a802ff15154016f8a8aa00bbc5455001ffb1aa800bfd8d54007fcc6aa003fd6355001fe31aa809bf18d5401ffea6aa00f7f5355007fe29aa802ffd0d54017f886aa003ff6255
  | 11 => 0x71c138067ca740df022004491200039f162cedc74a0000158ba65b04451d60fe818e00000006343b6000000086a0db16500000000000930ce0ece824303066400010520a89f0c521da1d2000000029e00014109ac72e3c300000000000001eb4a1079c04f067002000023d02c000026634080045223e3000089c0000c444e0f751366da1ab816400010e1b49da8c6a59d2110000b4e6a01800b7caba00002010c4fc65401648d1432c1342f11dc037213a00013b47ca67226a15385066a43d180000121bd35100000007ba1d900010923ff020a07001a4a42c61fcc0005e606c8000000597000039061e49d151025c0000003270320eea6302e80f4c00022f0bb13fc00055200000003da7810000284408812147136c3086612b90000fbe45f000000039a00037b000000000022900000002be00000000000000000000000409389127ca4c44407d893407e1460000000ae04b90a01bec0007723fc0c28ad60001770de40005cf00020b44ec0003959b081080000000d9400677f1bf04f8cdc81d2be20cc4400550442114a2800001880000007ea2101bdcb3e54d00004ccb0a00012d9e643c222e21780000e071b000011800011100000008ee0004048d34baa61137619950687d434418d83920120310ae82525df27405b88ce3d73ca05a4bfe2111dc80a447e7442d09d44e0200004d1fd50783cb10f859800085d1fba20cb768a50001ae05980004438000e3c00000018fc9b400008d8000eaa00011b8ba0d882330001b7c6cc60c3c5001000038e0a10000a0038b4280000ada12b0000d6c5b473c0da9f2c8ac62623a994064229c3669d2d0603702228000a200001838e1c05e00041400000000ab000000000022500000006587093650824e4c15a258800032486b18e00000003b4006138865073d1210000aac4980ba800008a000226000064887e0500a9503255a1338250a7a5073cf8000ba868542891a4a5885c1181f9038a6d317e861c56e0000878c540000000000000bbc0000000000f2e7613009854a2e1380c690640cc60923289ccede2c120a01c87e66483719b544f023927a21b10aa02125185c875e1f10de020cc1e1af219224c6aa87002a00c04e27082d99a0c2487a739a923892c43007a176c5b07b645b99480de3354188bb10980da00600200180080380180200c80080000080000180400180000100580100180280000b80100400a00600080000180300000680000180380280000200000080100080380000100580500780200000380580280280300000280000700080200280200000600400c00180000080000000500400800000080001100181b00000180400080380000000180180100100100000000380080100800100100500400000000100000180080500080980000900480100400700000800180100c803800002
  | 12 => 0xf68000178120882e4c43a31a2cbf225d19b9cd800087821c801800020c00000009c04d700000000700003fb1d78b8c40c243994c14482b0602240d987c702b83f4c0e6311298ee042e55e17487dcca22f20a69fa055c08e19f1618e9a2611a9853c68800000020a4b0664f0000a4c0000001af09f80004760b41d400922d414100005de4783e9209c7e26b21e0800110400000020047ea58a1c300000002e02a58c2c6b4000375132101c052021147cbe200002800007cc00000022b4c5e1731c19e90ba217807697651421ff1400808a466370000a240008050001f3cbd852f2b18a9c0000003ad8e3d11a2d338a91b40bc6eb37e00002580fc4101c084620d400000000001e614b1ae89562cf316830c9ee4f50aa0a906c82231978000aaa37800010ec95e25f00007780000002ee91601d85711ca80000000363fd125c0001f4252a0449e60003b31ca8bdc000086800000000000009dcfd247e20310f439448f3c28c2041e4ea2b01658000186000007c9f613200006b4c5433406584040001a43c011546446692099d8c318679000046513415c18e97cc3448b4455006c3a40f3342192486c84023f9fc063c008123201c00a5ad35c9e80dc872330d9f10000000000000092600042d94dcb62000200800000000000000002500000000000000000180829c0000000001a98c6611033d00000004ec06819f073683500000003b027f3e5134816a5f611e00000000fe23a0b443c8000429000000014b2d21850b082350369f4044800000011f4d52221000013cf5e67726281dc98e6be0ad80000000000c8000065651530f0c3432a4bb44c8000f800003980ce80002d500000004003622859c2c00006900000007ce05d0001a18d600001fe8e8c5d60001ed1058d2822b1239f083346fd33c00f4bb814a411a1985e80000b60000efa675063935400000012793f09dc49422697340001d63f08700532543142800025448d000027cc6474312214e4a421602b521d43966bb1a1a1cce8202b00012dc00026c39f8000b7a81642c9b987a00002b78840cb053820f88f47e86761c99ff80b487100000000000000a8800000000000001cc4da5742a280009fc0000e98000f645810050868e343a21ea94c8a9210800016a03b87a93c48c300006e000021802e27182f18a34c146413ca80000006e200b9964f7c3322a39240d9e52a42d0f84f362c40ae8488cc45e709814589d24d90000e4907212f29f92b877e7d81d9880cd5467b04584dc68437b333000014c1090e60b8c0003a7189800107a0000000264e1e7372249fb000000037f11b000011311107e004e0000f780008388a2000000000068d00000004fa12040196e46620001a4191819835400000009360003dc8c6462c00028f000000016b1cc828c00048115e1510e0a01e2758a301d0
  | 13 => 0x1e580000000e883840003a000005548506630d0862c1124fa00010607ac2380bd82a8fb883a00d1cd0d3242c44a0000f6a00034f00006b289225f95d4b5874f0611d8067e6d624500948482e423c89441b04bd07fa20414a58910c15a114647101b9fe4c442b5078992830a5e0000000055a79a30e0000fbc6f4444000036837d0fe800000030200000010fa69f33582ec0007ae31c07f0000000000227d0285b700001d80003233ab21080000003f11264e1805c000137ced82fa134000000000000009288660ca31615945141ea2aa0000eca44129b00000001803171188a0a1a618fa2e884c63e1de84f43280002730af400023a10b1c0c7381143e08750d785e8000106cb8a00039200000000000321be000000024a90400000000000c4488e57a0000f304ac42322180cc9c86ad02f8d442ca6ae2ad80000a281334a86e80fc66a18495d889633b0000f640006ef04008790ce50d1b98370bb06a84208d800008b21f208d07c400021f1d30f540002b98a6020600000000001dc00000003c80003ae2488f8000000032a8000704657241800099e4dc0000dc505c0d60af03c04c84020000b203ce0000001aac0002f80001fc40000000a702a4f426cb3e30f1c3844fd337a078bea0f93a38a191582a926f12150f2721000045400060442312788de74900012704982f52059820000000052000017e3030001880e6273904299802240001618000c8600041c0b749342b83c70d3ca6650c1b589540741fe00010a875800000000007b80960239b000b654c02711a80003cf2e51abc97c0002a885dc5c200038f9e303646e82eb0000cd8305000000076200000113e474a4bc31d0000b8859e000003c98c6f1073a10c0004a20fc8fac38277100005a88ae72c3a90f3411a5a03e188b0d6c2b30318754ec47fd0698678b220004421444d9c25c2ce0e5c0640000001fb43623f81f49c9c416000000000000000000018a02c41500001b240b01d70001bcc2982690000d186ee1982038000a060000000000e1c00000002f0d8e1c6000000000000001a81f09ca000083800102e6dd2149eec66c0ef18b964c0944e31a612c8c2c5203ad20840008952071a4d03488c00000002b05573c813385fe1794520ee90c48650dc1438cb829b000023018a20125300000000003258000682000000000001628f00000006361e52b4986425c4530000a043b6174000129cc061e83e40000bf835d09b1eb05da8983c917b445063900000000f641a0000274492388000132c3867140000ea4e4a642067800085a7b82e4907472855f413000089402202691ecc2e3980000000eb2000048800028a00035380009920003f3222d16c0f53c116d058e258000000073e0001600f0c00032538e8e5854c1ab1ef8000c243334061f54a625ef0410d28e0c3bb000
  | 14 => 0x697909802e5000159041c3121be0f10f62000000166800045e3c884601143750a4114418c5c30ab1884ffe47012d0604c2678f00009486966c53f583806ec1390101e34a608a90000b5800000000008143760000f100f000000017b1ab0b64000000173023e0003f78aa0f7a60236a0fb00007d70000c800000bd000000024a716000051c5960ce01c859c000000175000000063d09f800108870700007d4cda00000003acb90000128130852880b3aba2248d61022958b7100080d1208e98a322c645c19740006102a08000f0600000015fc21813c2c400000008360071b480006440000c50c56000000122094200000005100000002b39a8c0000004378e742fc2f91e407c000000011f1c5cd200001a380000000860000000158304137000103e0001739c64326226279000000063b00000007e40002ae000000000011500000000000001b6400067f2d308ecd4a00000000000004372c39afd0a60e500002d86782902df8db504a17d3238cb823c3062879e9402c38900018f095809c1c68afc0006913e297087140003fd8000e660002d180009980000e794042820b744290843d60000000000ea60003911de478a4660000fe87bc671000197c40e35215a0a1c00061f0000c987848ab4242178e400fa0e2060c16268e18801a04f47b710320dc64e480195213880877e36405250f854209686d852a64c28d035c0000c134b8000000161000000000043c00000004d6367000199c8746c644b8920a48680000156070a61a00012d107c76436c1b701a48ae3c409e46d068f00e15e00005c700021504e442e21c00008680712c78ef878018900016b80003f94279b443ec2363121fdc3be7cd3bc0b340004270001860c680c90e800000000001c61608f608573ba023ce0869a4349184b4a5f41d819cc8b451338016547946b71b0800081450243d97c80006e50000ac42863e83f72040cfa0243cc0bf104407f3e98608aa000000016d80000f60000ca47221a70e417e861c5f005f045cb7c0001d400009660002708000d363fe3b4a1b47da7113ed1424afa4f142c1d202f81b716806cca4a6fa4470b4854080a2f087ec81a3493ae0dbc8061e915519d00002f10000484b202321f80cc02b244025002a01aa73800a14883d81a92cc8b38cac274417882032286a2fe9f94ac28801378d70e9c79e0df07800ce65e000000000000022ca2bc89c4b82ed1e2c8b80230298bcc00086e3d1000000000000021840002b61fd80003ba80f2da964843a22908e166cd6600012a0bdc0006d013d800000006a0000f2495485600010acf7800000001f40000930098a48bd226504080d0ed6000030000000046800000000006e904a9a60b4489e2321cbce206db265154c35800000012d50048081b714d470002810e085000000034902e0c165ba0001cec00
  | 15 => 0x189c00009821283e0bd62db000000000000000001840006f9000000000000000000009a62af000102035c2124150e102da6f5256868c2fe3a122d896431e13104815dc21627514f9a28a5261d0001f6c5fc12345812484c68b513500000002e232a1c3502a000000213431067e3ee9078ce056641920b02144dd278000065a36c3d9a11c6e887728e8d00dce0b22211f9c05c4e70438bec0f23b71259ac4f4c1aa29f1f38a5047337f87b833600000380000005fb0000dfc00003e00e9894fb25af0001ad4572000000000000020a0000000eba1704321b8455888f08b0000b9c4d83c980000005182a793d800000039d01e0ee646e1ac1b78e1406b0260a743b21e30240a2ce267d1000049cf567542fc16348ba0001fe01b048a88628d82e515052e0329de878c5d708204187a869c12b9a240000002e080000004f8000054c00002d000180034a51242f80000000000ab80000008b91f711200000000001e740000002b117a80ea53b10d800015e1f30000a8cd3a0e310a93040000000218f6c26a00009d9cb45b237a1b51748e803182ff21c80001b02b6188ccd0000000084ceee00000022984bc0cd25b071cab20002bf000107e6961580ed4f5065a39900000000003228000e52363453a1a0000000000000015c0002541b048a02973f900000000002088000000000000181441a2621e880005562b215d89004323503bb000000006e08014b4dda390239000000000000000000003561cd1794ff8546000000034039e459800000065b26180002f418a1b91470000534000201800002600002d00001a820000010fe11d07b80010082de1f501e81d43ef2c716e09a00003b680603e42c20b782487a48a03e6183867250a277812c2c66821c095ec0005aa000113d0302a104d8674b8029a1ec0cf491600033216510e85a92b71d08a78000000000000000000020ecaf22603940fd81d20dd40d88b48f86bd00000b09528962091e1c9741973be00005cc00000006fc0007bf1d690fc2a40de37900008c068c20287e800064d43b00ec5086f04251d14ebe0003c20a2112240f000218c00034e0001b0c0e85cb44e9ad0000000071115049c3bc3771b5c00000008d0000c802432a40398c1a0b300021e89a20001d5000000048c2580b140000002cc22c40001640af9decfac5ab2231a1c90c54a23197dc9082d70689600d4202a2939f2400084b3f016f003250600a8eac79c7681af82b41741ce26
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe50594200267c5059420004ff755902001cfe755902001cfc7559020024ff7459020026bf7459020006bf545902003ebe545902003ebc5459020004ff735902004cfc735902003ebf435902003ebc435902002cff725902002cfe725902002cfd725902002cfc725902002ebe425902002ebc4259020004ff715902000cfe7159020004fd715902000cfc71590200067f51590200067d515902003ebf4159020006be4159020006bd415902003ebc4159020006df3159020006dd3159020024ff7059020024fe7059020024fd7059020024fc7059020026be4059020026bc4059020026ef2059020026ed2059020006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006bc535902002ebf725902002ebe725902002ebd725902002ebc725902002ebf525902002ebe525902002ebd525902002ebc525902002ebf325902002ebe325902002ebd325902002ebc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf51590200063f5159020006be5159020006bd51590200063d5159020006bc5159020006bf31590200069f3159020006be3159020006bd31590200069d3159020006bc315902002ebf215902002ebe215902002ebd215902002ebc2159020026bf7059020026be7059020026bd7059020026bc7059020026bf5059020026be5059020026bd5059020026bc5059020026bf3059020026be3059020026bd3059020026bc3059020026bf2059020026af2059020026be2059020026bd2059020026ad2059020026bc2059020026bf1059020026be1059020026bd1059020026bc1059020004ff7655020024fe7655020004fd7655020024fc7655020016be6455020006bd6455020004ff7558c2001cfe7558c2001cfc7558c20004ff7458c20014fe7458c20014fc7458c20024ff7358c20026df7358c2002cff7258c2002cfe7258c2002cfd7258c2002cfc7258c2002ede3258c2002edc3258c20004ff7158c2000cfe7158c20004fd7158c2000cfc7158c200067f5158c200067d5158c20006df3158c20006dd3158c20024ff7058c20024fe7058c20024fd7058c20024fc7058c20026de3058c20026dc3058c20026ef2058c20026ed2058c2004cff7694c20024fe7694c20004fd7694c20024fc7694c20216be6494c20006bd6494c2004ede6394c20006dd6394c200475f5394c20004ff7654c20024fe7654c20004fd7654c20024fc7654c2001e7e6554c200067d6554c20206be6454c20006bd6454c2004ede6354c20006dd6354c2004cff7690c20024fe7690c20004fd7690c20024fc7690c20016be6490c20006bd6490c20004ff7650c20024fe7650c20004fd7650c20024fc7650c20016be6450c20006bd6450c20
  | 1 => 0x920007ae435092005fac4350920255ef7150920255ed715092024eef615092024eed615092024f6f515092024f6d515092005faf415092024fad415092024fcf315092024fcd3150920007eb7050920025ee7050920025ec7050920007e8705092002eef605092002feb605092005faf405092024fea105092024fe91050920024fe76cc920024fc76cc9200657e75cc9200057d75cc9200067f65cc9201967c65cc920006df63cc92004edc63cc920025fa70cc920005f970cc92002fe820cc920005ee768c92002eee768c920065ee758c92002dec758c9200076f658c9200076c658c92002def748c92002fae748c920005ed748c92002fad748c920005ad748c92022ded738c920007cf638c92004eee638c92004eec638c920007cc638c92004ecc638c92002def718c920245ed718c9202376f518c9202376d518c920237cf318c920237cd318c920025ee708c920025ec708c92002eef608c92002feb608c92023fce308c92023fcc308c920237ea108c920237e9108c920024fc764c9200067f654c9201667c654c920006df634c92004edc634c920005fb704c920025f8704c920025ec764c92004eec764c920024ec764c920065ee754c920065ec754c9200076f654c9200076c654c920005ef744c920005ed744c92002def734c92002fcf734c920007cf634c92004eee634c92004eec634c920007cc634c92022def714c92022ded714c9202276f514c9202276d514c920227cf314c920227cd314c920007eb704c920025ee704c920025ec704c920007e8704c920025e8704c92002eef604c92002feb604c920227ea104c920227e9104c92001cff7654120064fd765412002cfc76541200067f655412001e7c6554120006df6354120006dc6354120005ef725412002dec7254120027785054120027e82054120014ff765012005cfd765012002cfc76501200067f65501201067c6550120006bf6450120016bc6450120006df6350120006dc6350120005ef725012002dec7250120007ad4250120027e8205012002cfe76cc12002cfc76cc1200067f65cc1200f67c65cc120006df63cc12004edc63cc12002dee72cc120005ed72cc120027e820cc12004cff764c120004fd764c12002cfc764c1200057f754c1200657c754c1200067f654c1200c67c654c120006df634c12004edc634c120005ef724c12002dec724c120024ff75594200267f7559420004ff7459420014fe7459420014fc7459420004ff735942004cfc73594200467f535942002cff725942002cfe725942002cfd725942002cfc725942002e7e525942002e7c5259420004ff715942000cfe7159420004fd715942000cfc71594200467f51594200067d5159420006df3159420006dd3159420024ff7059420024fe7059420024fd7059420024fc70594200267
  | 2 => 0x6de5418d20006dd5418d20006dc5418d2004edf7218d2004ede7218d2004edd7218d2004ecd7218d2004edc7218d20006df5218d20286de5218d20286dc5218d20006df4218d20286de4218d20286dc4218d2004edf7118d2004cdf7118d2004ede7118d2004edd7118d20004dd7118d2004edc7118d20006df5118d200065f5118d20006de5118d20006dd5118d200065d5118d20006dc5118d20006df4118d20006de4118d20006dd4118d20006dc4118d20286df2118d20006de2118d20006dd2118d20286dc2118d2004edf7018d2004ede7018d2004edd7018d2004edc7018d20006df5018d2027ede5018d2027edc5018d20006df4018d2027ede4018d2027edc4018d20286df2018d2027ede2018d20006dd2018d2027edc2018d20006df1018d2027ede1018d20006dd1018d2027edc1018d2004cff7694d20004fe7694d20004fd7694d2004cfc7694d200067f6594d2001e7c6594d20006df6394d2004edc6394d200675f5394d2002dee7294d20005ed7294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d2001e7c6554d20006df6354d2004edc6354d20005ef7254d2002dec7254d200676c5254d20005fb7054d20025f87054d2004cff7690d20004fe7690d20004fd7690d2004cfc7690d200067f6590d201f67c6590d20006df6390d2004edc6390d2002dee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d201e67c6550d20006df6350d2004edc6350d20024fc76549200067f655492001e7c6554920006df6354920006dc6354920065ef725492002f6c5254920005fb7054920025f8705492002fe82054920005ee769092002eee7690920065ee759092002dec75909200076f65909200076c659092005ded7490920016ee6490920016ec6490920005ed7390920007cf6390920276ee6390920276ec6390920007cc6390920006cc639092002def719092026ded7190920266ef6190920266ed61909202676f51909202676d5190920267cf3190920267cd3190920025ee7090920025ec709092002eef609092002feb6090920267ea1090920267e91090920024fc76509200057f75509200657c75509200067f65509201a67c6550920006bf6450920016bc6450920006df6350920006dc635092002fac4250920005fb7050920025f8705092002fe82050920025ec7650920016ec7650920024ec76509200076f7550920065ee7550920065ec75509200076c75509200656c75509200076f65509200076c655092002def745092002faf7450920007af6450920016ee6450920016ec645092005fac6450920016ac645092005fae5450920007ad5450920005ef7350920007cf635092025eee635092025eec6350920007cc6350920006cc635
  | 3 => 0xe76d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d20006de64d8d20006dd64d8d20006dc64d8d2023fcf72d8d20007cf52d8d20007cc52d8d20005df71d8d20005dd71d8d20006df61d8d20006de61d8d20006dd61d8d20006dc61d8d200075f51d8d200075d51d8d20007cf21d8d20007cd21d8d2028fdb20d8d2023fce20d8d2023fcc20d8d2028fd820d8d20007da10d8d20007d910d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d2023edf72d8d2028ede72d8d20006dd72d8d2028edc72d8d20006df52d8d2028ede52d8d2028edc52d8d20006df42d8d2028ede42d8d2028edc42d8d20006df71d8d20004df71d8d20006de71d8d20006dd71d8d20004dd71d8d20006dc71d8d20006df51d8d200065f51d8d20006de51d8d20006dd51d8d200065d51d8d20006dc51d8d20006df41d8d20006de41d8d20006dd41d8d20006dc41d8d2028edf21d8d20006de21d8d20006dd21d8d2028edc21d8d2028edf70d8d2023ede70d8d20006dd70d8d2023edc70d8d20006df50d8d2023ede50d8d2023edc50d8d20006df40d8d2023ede40d8d2023edc40d8d2028edf20d8d2023ede20d8d2023edc20d8d20006df10d8d2023ede10d8d20006dd10d8d2023edc10d8d200657e7598d200057d7598d200067f6598d200067c6598d20006df6398d200057f7558d200657c7558d200067f6558d200067c6558d20004ff7558d200067f7558d200047f7558d2001cfe7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20014fe7458d20014fc7458d20006df7358d20004ff7258d20006ef7258d20004ff7158d2000cfe7158d20004fd7158d2000cfc7158d200067f5158d200067d5158d20006df3158d20006dd3158d20004ff7058d20006fb7058d20004fe7618d200067f6518d200067c6518d2004ede6318d20006dd6318d20005de7618d20006de7618d20004de7618d20006df6518d200075f6518d200065f6518d20006de6518d20006dd6518d20006dc6518d200075c6518d200065c6518d20006df6418d20006de6418d20006dd6418d20006dc6418d20007cd7218d20007cf5218d20007cc5218d20005df7118d20005dd7118d20006df6118d20006de6118d20006dd6118d20006dc6118d200075f5118d200075d5118d20007cf2118d20007cd2118d20287db2018d2027fce2018d2027fcc2018d20287d82018d20007da1018d20007d91018d2004edf7518d2004ede7518d2004edd7518d2004edc7518d2004edf7418d2004ede7418d2004edd7418d2004edc7418d20006df5418d20
  | 4 => 0x95202a67c20d95200067f10d95202a67e10d95200067d10d95202a67c10d95200667c6559520005df7359520005dc7359520064ff75595200067f7559520004ff7459520014fe7459520014fc7459520004ff7359520006df7359520004df735952004cfc7359520006dc735952004cdc735952007cff7259520006ef7259520066ef5259520066ec5259520004ff715952000cfe7159520004fd715952000cfc71595200667f51595200067d5159520006df3159520006dd3159520094ff7059520006fb70595200057e76195200667e76195200047e76195200067e64195200067c641952029f6f72195200676c721952029e7f62195200657f71195200057d71195200067f61195200067e61195200067d61195200067c61195200075f31195200075d31195200076f21195200076d21195202967f60195202977b201952029f6e201952029f6c20195202977820195200077a1019520007791019520014fe76d91200067f65d91200067c65d912005ebe64d912001cfe75d9120004fd75d912001cfc75d912004cfe73d9120004fd73d912002cfe72d9120024fd72d912002cfc72d912005ebf42d9120004ff71d912000cfe71d9120004fd71d912000cfc71d91200067f51d91200067d51d9120006be41d912005ebc41d9120006df31d9120006dd31d9120006ef21d9120006ed21d9120024fe70d912002cfd70d9120024fc70d912005ebf40d9120006fa10d9120006f910d91200057f75591200657c75591200067f65591200067c655912005ebc6459120005df7359120005dc7359120005f77159120055f47159120004ff75591200067f75591200047f755912001cfe755912001cfc75591200067c755912001c7c755912005cff7459120006bf7459120004ff7359120006df7359120004df735912004cfc7359120006dc735912004cdc7359120074ff7259120006ef7259120004ff7159120006f77159120004f7715912000cfe7159120004fd715912000cfc7159120006f4715912000cf471591200067f51591200067d515912005ebf4159120006bd4159120006df3159120006dd3159120006ef2159120006ed215912008cff7059120006fb7059120006fa1059120006f91059120004ff7655120004fe7655120004fd7655120004fc76551200067f655512001e7c6555120005ef725512002dec725512004cfe76d8d200067f65d8d200067c65d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20014fe74d8d20004fd74d8d20014fc74d8d20006df53d8d20006dc53d8d20006df43d8d20006dc43d8d2002cfe72d8d2002cfc72d8d20004ff71d8d2000cfe71d8d20004fd71d8d2000cfc71d8d200067f51d8d200067d51d8d20006df31d8d20006de31d8d20006dd31d8d20006dc31d8d20024fe70d8d20024fc70d8d2004cd
  | 5 => 0x4fd7158e2000cfc7158e200067f5158e200067d5158e20006df3158e20006dd3158e20024fc7058e20026de3058e20026dc3058e20026ef2058e20026ed2058e2004cff7694e20024fe7694e20004fd7694e20024fc7694e2007f5f5394e20004ff7654e20024fe7654e20004fd7654e20024fc7654e2001e7e6554e200067d6554e20005fb7054e20025f87054e2004cff7690e20024fe7690e20004fd7690e20024fc7690e20004ff7650e20024fe7650e20004fd7650e20024fc7650e20016be6450e20006bd6450e2001cff7654a20024fc7654a2001e7e6554a200067d6554a20005fb7054a20025f87054a20014ff7650a20024fc7650a200057f7550a2007d7c7550a20016be6450a20006bd6450a2002fac4250a20005fb7050a20025f87050a2007d7e75cca200057d75cca2004ede63cca20006dd63cca20025fa70cca20005f970cca2004cff764ca2004ede634ca20006dd634ca20005fb704ca20025f8704ca2001cfe76d95200667e65d952002dee72d9520025ed72d95200676f52d9520014fe74d9520004fd74d9520014fc74d95200667f54d95200067e54d95200667c54d952004cfe73d9520004fd73d95200667f53d95200667c53d952002cfe72d9520024fd72d9520066ed72d9520024ed72d952002cfc72d95200667f52d9520066ef52d9520066ec52d9520004ff71d952000cfe71d9520004fd71d952000cfc71d95200667f51d95200067e51d95200067d51d95200667c51d9520006df31d9520006dd31d9520024fe70d952002cfd70d9520024fc70d95200667f50d95200657e76d952001c7e76d95200067e64d95200067c64d95200676e72d95200076d72d95200057f71d95200057d71d95200067f61d95200067e61d95200067d61d95200067c61d95200075f31d95200075d31d95200076f21d95200076d21d95202af7b20d95202a76e20d95202a76c20d95202af7820d95200077a10d95200077910d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067c43d95202a67f72d95202ae7e72d95200666e72d95200067d72d95200066d72d95202ae7c72d95200067f42d95202ae7e42d95202ae7c42d95202ae7e32d95202ae7c32d95200067f71d95200047f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067f31d95200065f31d95200067e31d95200067d31d95200065d31d95200067c31d95202ae7f21d95200067e21d95200067d21d95202ae7c21d95202ae7f70d95202a67e70d95200067d70d95202a67c70d95200067f40d95202a67e40d95202a67c40d95202a67e30d95202a67c30d95202ae7f20d95202a67e20d
  | 6 => 0xc7158f200067f5158f200067d5158f20006df3158f20006dd3158f2004cff7694f2002cfe7694f20004fd7694f2002cfc7694f2001e7e6594f200067d6594f200975f5394f2002dee7294f20005ed7294f20004ff7654f2002cfe7654f20004fd7654f2002cfc7654f202d67f6554f2001e7c6554f20005ef7254f2002dec7254f202d76c5254f2004cff7690f2002cfe7690f20004fd7690f2002cfc7690f20016be6490f20006bd6490f2002dee7290f20005ed7290f20004ff7650f2002cfe7650f20004fd7650f2002cfc7650f2002dee7250f2002def7650b2003eef7650b200076f7550b20095ee7550b20095ec7550b200076c7550b200956c7550b2002faf7450b2002faf6450b20016ee6450b2002eec6450b2002fac6450b2002eac6450b2008fae5450b20007ad5450b20005ef7350b2025eee6350b2002eec6350b20007ae4350b2008fac4350b202cdef7150b202cded7150b2002eef6150b202c6ed6150b202c76f5150b202c76d5150b2008faf4150b202c7ad4150b202c7cf3150b202c7cd3150b20025ee7050b20025ec7050b2008faf4050b2002def764cb20006ef764cb20095ee754cb20095ec754cb20005ef744cb20005ed744cb2002fcf734cb2004eee634cb2002eec634cb202bdef714cb202bded714cb202b76f514cb202b76d514cb202b7cf314cb202b7cd314cb20025ee704cb20025ec704cb2001cff765432002cfc765432001e7e65543200067d6554320005ef725432002dec7254320014ff765032002cfc7650320016be6450320006bd6450320005ef725032002dec7250320007ad425032004ede63cc320006dd63cc32002dee72cc320005ed72cc32004cff764c3200057f754c3200957c754c32004ede634c320006dd634c320005ef724c32002dec724c3200267f7559620004ff7459620014fe7459620014fc74596200067e545962007e7c5459620004ff735962004cfc735962007e7f535962007e7f5259620004ff715962000cfe7159620004fd715962000cfc715962007e7f51596200067d5159620006df3159620006dd3159620024fc70596200267e50596200267c5059620004ff755922001cfe755922001cfc7559220026bf7459220006bf5459220076bc5459220004ff735922004cfc7359220076bf4359220076bf4259220004ff715922000cfe7159220004fd715922000cfc71592200067f51592200067d5159220076bf4159220006bd4159220006df3159220006dd3159220024fc7059220026be4059220026bc4059220026ef2059220026ed2059220026fa1059220006f91059220004ff7655220024fe7655220004fd7655220024fc7655220004ff7558e2001cfe7558e2001cfc7558e20004ff7458e20014fe7458e20014fc7458e20026df7358e20004ff7158e2000cfe7158e20
  | 7 => 0x8300a7ac425083025fcc325083019ef6615083004ddd768c830286dd768c83004f5e658c83004f5d658c8302879e748c8302879d748c83004f9e648c83004f9d648c83004dde728c83004fce728c83004edf628c83004fce628c830286dd628c83004fcd628c830006cd628c830285df718c8302e5dd718c83004edf618c83004fd6618c8302dedd618c83004fd5618c8302df5f518c8302df5d518c83023ddf708c83023ddd708c83023ede608c83004fda608c83023fcf208c830006f77558430006f67558430006767558430006f57558430006757558430006f47558430006f77458430006f67458430006f57458430006f47458430006f75458430006f65458430006f55458430006f4545843004ef7735843004ef6735843004ed6735843004ef5735843009ed5735843004ef4735843004ef7535843004ef6535843004ef5535843004ef4535843004ef7435843004ef6435843004ef5435843004ef44358430006f77258430006f67258430006f57258430006f47258430006f75258430006f65258430006f55258430006f45258430006f74258430006f64258430006f54258430006f4425843004ef7325843004ef63258430006d6325843004ef5325843004ef4325843004ed43258430026f77058430026f67058430026f57058430026f47058430026f75058430026f65058430026f55058430026f45058430026f74058430026f64058430026f54058430026f44058430026f73058430026d73058430026f63058430026f53058430026d53058430026f43058430026f72058430026f62058430026f52058430026f4205843002e7f7559720004ff7459720014fe7459720014fc74597200967f5459720004ff735972004cfc73597200967c5359720024fc725972002eec7259720024ec7259720096ef525972002e7e525972002e7c525972002eec5259720004ff715972000cfe7159720004fd715972000cfc71597200967f51597200067d5159720006df3159720006dd31597200967f5059720004ff755932001cfe755932001cfc755932002ebf745932008ebe5459320004ff735932004cfc735932008ebc4359320024fc725932002ebe425932002ebc4259320004ff715932000cfe7159320004fd715932000cfc71593200067f51593200067d515932008ebf4159320006bd4159320006df3159320006dd315932002eef2159320006ed215932008ebf4059320004ff765532002cfe7655320004fd765532002cfc765532001e7e65553200067d6555320016be6455320006bd6455320005ef725532002dec7255320004ff7558f2001cfe7558f2001cfc7558f20004ff7458f20014fe7458f20014fc7458f2002edf7358f20024fc7258f2002ede3258f2002edc3258f20004ff7158f2000cfe7158f20004fd7158f2000cf
  | 8 => 0x6ec5198830006ef4198830006ee4198830006ed4198830006ec419883004eef319883004ecf319883004eee319883004eed3198830006cd319883004eec3198830026ef7098830026ee7098830026ed7098830026ec7098830026ef5098830026ee5098830026ed5098830026ec5098830026ef4098830026ee4098830026ed4098830026ec4098830026ef3098830026ee3098830026ed3098830026ec3098830026ef1098830026ee1098830026ed1098830026ec1098830004ff755883001cfe755883001cfc7558830004ff7458830014fe7458830014fc7458830026ef7258830006ef5258830006ec5258830006ef4258830006ec425883004eef325883004edc325883004eec3258830004ff715883000cfe7158830004fd715883000cfc71588300067f51588300067d515883004edf3158830006dd3158830006ef2158830006ee2158830006ed2158830006ec2158830024ff7058830024fd7058830026ee2058830026ec2058830006ef7558830006ee7558830006ed7558830006ec7558830006ef7458830006ee7458830006ed7458830006ec7458830006ef5458830006ee5458830006ed5458830006ec545883004eef735883004eee735883004eec735883004eef535883004eee535883004eed535883004eec535883004eef435883004eee435883004eed435883004eec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef51588300066f5158830006ee5158830006ed51588300066d5158830006ec5158830006ef4158830006ee4158830006ed4158830006ec415883004eef315883004ecf315883004eee315883004eed3158830006cd315883004eec3158830026ef7058830026ee7058830026ec7058830026ef5058830026ee5058830026ed5058830026ec5058830026ef4058830026ee4058830026ed4058830026ec4058830026ef3058830026ee3058830026ed3058830026ec3058830026ef1058830026ee1058830026ed1058830026ec105883002cff7694830024fe7694830004fd769483001e7e65948300067d65948301d6be6494830006bd649483002eee6294830006ed62948301cef66194830025fa7094830005f97094830004ff7654830004fd7654830024fc765483001e7e65548300067d65548301c6be6454830006bd6454830005df735483004ddc735483002eee6254830006ed62548301bef6615483002cff7690830024fe7690830004fd76908301b67e65908300067d6590830016be6490830006bd649083002eee6290830006ed6290830287cc32908301aef66190830004ff7650830004fd7650830024fc76508300057f75508300ad7c75508301a67e65508300067d6550830016be6450830006bd6450830005df735083004ddc735083002eee6250830006ed625
  | 9 => 0xc415943004e7f315943004e5f315943004e7e315943004e7d31594300065d315943004e7c31594300067f21594300067e21594300067d21594300067c21594300267f70594300267e70594300267d70594300267c70594300267f40594300267e40594300267d40594300267c40594300267f30594300267e30594300267d30594300267c30594300267f20594300267e20594300267d20594300267c20594300267f10594300267e10594300267d10594300267c1059430004ff755903001cfe755903001cfc7559030024ff7459030026bf7459030006bf54590300a6be54590300a6bc545903004cff735903004cfe735903004cfd735903004cfc735903004ebe435903004ebc4359030004ff725903002cfc72590300a6bf42590300a6bc4259030004ff715903000cfe7159030004fd715903000cfc71590300067f51590300067d51590300a6bf4159030006be4159030006bd41590300a6bc415903004edf3159030006dd3159030024fe7059030024fc7059030026be4059030026bc4059030006bf7559030006be7559030006bd7559030006bc755903004ebf735903004ebe735903004ebd735903004ebc735903004ebf535903004ebe535903004ebd535903004ebc5359030006bf7259030006be7259030006bd7259030006bc7259030006bf5259030006bc525903004ebf325903004ebe325903004ebd325903004ebc3259030006bf7159030006be7159030006bd7159030006bc7159030006bf51590300063f5159030006be5159030006bd51590300063d5159030006bc515903004ebf315903004e9f315903004ebe315903004ebd31590300069d315903004ebc3159030006bf2159030006be2159030006bd2159030006bc2159030026bf7059030026be7059030026bd7059030026bc7059030026bf5059030026be5059030026bd5059030026bc5059030026bf3059030026be3059030026bd3059030026bc3059030026bf2059030026be2059030026bd2059030026bc2059030026bf1059030026be1059030026bd1059030026bc1059030004ff7655030024fe7655030004fd7655030024fc765503001e7e65550300067d6555030016be6455030006bd6455030005df735503004ddc735503021ef6615503002eef759883002eee759883002eed759883002eec759883002eef749883002eee749883002eed749883002eec7498830006ef5498830006ee5498830006ed5498830006ec549883002eef739883002eee739883002eed739883002eec739883004eef539883004eee539883004eed539883004eec539883004eef439883004eee439883004eed439883004eec439883002eef719883002eee719883002eed719883002eec7198830006ef51988300066f5198830006ee5198830006ed51988300066d5198830
  | 10 => 0x4d30005fb7054d30025f87054d30024fc7650d300067f6550d301e67c6550d30006bf6450d30016bc6450d30005fb7050d30025f87050d300067f65d89300067c65d893001cfe75d8930004fd75d893001cfc75d8930014fe74d8930004fd74d8930014fc74d8930004ff71d893000cfe71d8930004fd71d893000cfc71d89300067f51d89300067d51d8930006df31d8930006dd31d8930006ee21d8930006ec21d8930024fe70d8930024fc70d89300c57e75989300057d75989300067f65989300067c65989300bdbe7498930005bd749893023edf6398930006ef62989300057f75589300c57c75589300067f65589300067c65589300067f65189300067c651893027edf631893002eee6218930006ed6218930004fe7694930004fd769493002cfc76949300067f659493001e7c6594930004ff7654930004fe7654930004fc76549300067f655493001e7c6554930004fe7690930004fd769093002cfc76909300067f65909301b67c6590930006ef629093002eec6290930004ff7650930004fe7650930004fc76509300057f75509300c57c75509300067f65509301a67c6550930006bf6450930016bc6450930006ef625093002eec62509300bfac4250930024fe768c9300067f658c93017e7c658c9300bdbe748c930005bd748c930006ef628c93002eec628c930025fa708c930005f9708c930024fc764c9300067f654c9301667c654c930006ef624c93002eec624c930005fb704c930025f8704c93001cff76541300c4fd765413004cfc76541300067f655413001e7c6554130005df735413004ddc7354130014ff76501300bcfd765013004cfc76501300067f65501301067c6550130006bf6450130016bc6450130005df735013004ddc7350130024ff75594300267f7559430004ff7459430014fe7459430014fc74594300ae7f54594300067e54594300ae7c545943004cff735943004cfe735943004cfd735943004cfc735943004e7e535943004e7c5359430004ff725943002cfc72594300ae7f52594300ae7c5259430004ff715943000cfe7159430004fd715943000cfc71594300ae7f51594300067e51594300067d51594300ae7c515943004edf3159430006dd3159430024fe7059430024fc70594300267e50594300267c50594300067f74594300067e74594300067d74594300067c745943004e7f735943004e7e735943004e7d735943004e7c735943004e7f435943004e7e435943004e7d435943004e7c43594300067f72594300067e72594300067d72594300067c72594300067f42594300067c425943004e7f325943004e7e325943004e7d325943004e7c32594300067f71594300047f71594300067e71594300067d71594300047d71594300067c71594300067f41594300067e41594300067d41594300067
  | 11 => 0x67e64d95300067c64d95300057f71d95300057d71d95300067f61d95300067e61d95300067d61d95300067c61d95300075f31d95300075d31d95303077b30d95302ff5e30d95302ff5c30d95303077830d95300067f74d95300067e74d95300067d74d95300067c74d95302fe7f73d95303067e73d95300067d73d95303067c73d95300067f43d95303067e43d95303067c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067c42d95303067f32d95303067c32d95300067f71d95300047f71d95300067e71d95300067d71d95300047d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95303067f31d95300065f31d95300067e31d95300067d31d95300065d31d95303067c31d95300067f21d95300067e21d95300067d21d95300067c21d95303067f70d95302fe7e70d95300067d70d95302fe7c70d95300067f40d95302fe7e40d95302fe7c40d95303067f30d95302fe7e30d95302fe7c30d95302fe7e20d95302fe7c20d95300067f10d95302fe7e10d95300067d10d95302fe7c10d95300c67c65595300c4ff75595300067f7559530004ff7459530014fe7459530014fc74595300dcff7359530006df7359530004ff725953002cfc7259530004ff715953000cfe7159530004fd715953000cfc71595300c67f51595300067d5159530006df3159530006dd31595300f4ff7059530006fb70595300057e76195300c67e76195300047e76195300067e64195300067c64195302f67f63195300c57f71195300057d71195300067f61195300067e61195300067d61195300067c61195300075f31195300075d31195302ee7f60195302ef7b30195302f75e30195302f75c30195302ef783019530014fe76d91300067f65d91300067c65d91300bebe64d913001cfe75d9130004fd75d913001cfc75d913004cfe73d9130024fd73d913004cfc73d91300bebf43d913002cfe72d9130004fd72d91300bebf42d9130004ff71d913000cfe71d9130004fd71d913000cfc71d91300067f51d91300067d51d9130006be41d91300bebc41d9130006df31d9130006dd31d913004cfd70d91300bebf40d91300057f75591300c57c75591300067f65591300067c65591300bebc6459130004ff75591300067f75591300047f755913001cfe755913001cfc75591300067c755913001c7c75591300bcff7459130006bf74591300d4ff7359130006df7359130004ff725913002cfc7259130004ff715913000cfe7159130004fd715913000cfc71591300067f51591300067d5159130006df3159130006dd31591300ecff7059130006fb7059130004ff7655130004fe7655130004fd7655130004fc76551300067f655513001e7c6555130024fc7654d300067f6554d3001e7c655
  | 12 => 0xe755923001cfc7559230026bf7459230006bf54592300d6bc54592300d6bf4359230004ff725923002cfc72592300d6bf4259230004ff715923000cfe7159230004fd715923000cfc71592300067f51592300067d51592300d6bf4159230006bd4159230006df3159230006dd3159230024fc7059230026be4059230026bc4059230004ff7655230024fe7655230004fd7655230024fc765523032e7f655523001e7c6555230005df735523004ddc735523001cff7654e30024fc7654e3001e7e6554e300067d6554e30005fb7054e30025f87054e3004fdb3054e30014ff7650e30024fc7650e30016be6450e30006bd6450e30005fb7050e30025f87050e30004ff7558a300067f7558a300047f7558a3001cfe7558a3001cfc7558a300067c7558a3001c7c7558a30004ff7458a30014fe7458a30014fc7458a30026ef7258a30006ef5258a30006ec5258a30004ff7158a3000cfe7158a30004fd7158a3000cfc7158a300067f5158a300067d5158a30006df3158a30006dd3158a30006ef2158a30006ed2158a30024fc7058a30026ee2058a30026ec2058a3002cff7694a30024fe7694a30004fd7694a302a67f6594a3001e7c6594a30004ff7654a30004fd7654a30024fc7654a30005df7354a3004ddc7354a3002cff7690a30024fe7690a30004fd7690a3002eee6290a30006ed6290a30004ff7650a30004fd7650a30024fc7650a300057f7550a300dd7c7550a30016be6450a30006bd6450a30005df7350a3004ddc7350a3002eee6250a30006ed6250a300d7ac4250a300d5be748ca30005bd748ca3002eee628ca30006ed628ca30025fa708ca30005f9708ca3028f9e748ca3028f9d748ca3004dde728ca3023edf628ca3023fce628ca3028edd628ca3023fcd628ca3028ddf718ca30325dd718ca3023edf618ca3031edd618ca3031f5f518ca3031f5d518ca3023fda708ca3023ddd708ca3028fd9708ca3004ede608ca3023fcf208ca3002cff764ca3002eee624ca30006ed624ca30005fb704ca30025f8704ca3027ddd760ca3004edd760ca3004fce720ca3027edf620ca3028edd620ca3028fce420ca30007cd420ca3004ddf710ca30315dd710ca3027edf610ca3030edd610ca3030f5f510ca3030f5d510ca3004ddf700ca3027ddd700ca3004fda600ca3001cfe76d95300c67e65d9530014fe74d9530004fd74d9530014fc74d95300c67f54d95300067e54d95300c67c54d953004cfe73d9530024fd73d953004cfc73d95300c67f53d953002cfe72d9530004fd72d95300c67f52d95300c67c52d9530004ff71d953000cfe71d9530004fd71d953000cfc71d95300c67f51d95300067e51d95300067d51d95300c67c51d9530006df31d9530006dd31d953004cfd70d95300c67f50d95300c57e76d953001c7e76d9530
  | 13 => 0x940336bf6150940336bd61509403373f51509403373d51509403379f31509403379d3150940337af2150940337ad2150940007bb7050940025be7050940025bc7050940007b87050940016bf6050940017bb6050940337ba1050940337b91050940004fe76cc940004fd76cc94004cfc76cc9401057e75cc9400057d75cc940015be74cc940005bd74cc940007ad42cc940004fe768c940004fd768c94002cfc768c940015be748c940005bd748c940006df638c94004edc638c940004ff764c940004fe764c940004fc764c940015be744c940005bd744c940004fe760c940004fd760c94002cfc760c940015be740c940005bd740c940006df630c94004edc630c940007ad420c940025fa700c940005f9700c94001cff7654140014fe7654140124fd7654140014fc76541400067f655414001e7c6554140005bf7454140015bc745414004e7f7559730004ff7459730014fe7459730014fc74597300f67f5459730024fc735973004e7e535973004e7c5359730004ff725973002cfc72597300f67c5259730004ff715973000cfe7159730004fd715973000cfc71597300f67f51597300067d515973004edf3159730006dd31597300f67f5059730004ff755933001cfe755933001cfc755933004ebf7459330024fc735933004ebe435933004ebc4359330004ff725933002cfc7259330004ff715933000cfe7159330004fd715933000cfc71593300067f51593300067d515933004edf3159330006dd31593300eebf4059330004ff765533004cfe7655330004fd765533004cfc765533001e7e65553300067d6555330004ff7558b3001cfe7558b3001cfc7558b30004ff7458b30014fe7458b30014fc7458b30024fc7358b3004eef7258b3004eef3258b3004eec3258b30004ff7158b3000cfe7158b30004fd7158b3000cfc7158b300067f5158b300067d5158b3004edf3158b30006dd3158b3002cff7694b3004cfe7694b30004fd7694b3001e7e6594b300067d6594b30025fa7094b30005f97094b30004ff7654b30004fd7654b3004cfc7654b3002cff7690b3004cfe7690b30004fd7690b3002eec6290b30004ff7650b30004fd7650b3004cfc7650b300057f7550b300f57c7550b3025ebf6450b30016bc6450b300efac4250b3001cff765433004cfc765433001e7e65543300067d6554330005df735433004ddc7354330027da3054330014ff765033004cfc7650330016be6450330006bd6450330005df735033004ddc73503300267f7559630004ff7459630014fe7459630014fc74596300de7f5359630004ff725963002cfc7259630004ff715963000cfe7159630004fd715963000cfc71596300de7f51596300067d5159630006df3159630006dd3159630024fc70596300267e50596300267c5059630004ff755923001cf
  | 14 => 0x67d51d9540006df31d9540006dd31d9540014fd70d95401067f50d95401067c6559540005df7359540005dc7359540355fb7059540134ff75595400067f7559540124ff7459540006bf7459540106bf5459540126bc5459540004ff7359540006df7359540004df735954004cfc7359540006dc735954004cdc73595401067f5359540004ff725954002cfc7259540126bf4259540004ff715954000cfe7159540004fd715954000cfc71595401067f51595400067d5159540006df3159540006dd3159540354ff7059540006fb705954032e7e505954032e7c505954001cfe75d8d40004fd75d8d4001cfc75d8d40024fd74d8d40006df53d8d40006dc53d8d400d6de43d8d400d6dd43d8d4002cfe72d8d40004fd72d8d40004ff71d8d4000cfe71d8d40004fd71d8d4000cfc71d8d400067f51d8d400067d51d8d40006df31d8d40006dd31d8d40006df6398d400bdf97098d400057f7558d401057c7558d400edfb7058d401057e7518d400057d7518d4004ede6318d40006dd6318d40004fe7694d40004fd7694d4004cfc7694d400067f6594d4001e7c6594d40015be7494d40005bd7494d401075f5394d40004ff7654d40004fe7654d40004fc7654d4001e7e6554d400067d6554d40005bf7454d40015bc7454d401073f5454d40005fb7054d40025f87054d40024bc7650d40105be7550d40105bc7550d40015bf7350d400179f7350d400079f6350d4004ebe6350d4004ebc6350d400079c6350d40005bf7250d4034dbf7150d4034dbd7150d403473f5150d403473d5150d403479f3150d403479d3150d40007bb7050d40025be7050d40025bc7050d40007b87050d40016bf6050d40017bb6050d40347ba1050d40347b91050d4001cfe75d8940004fd75d894001cfc75d8940024fd74d894004cfe73d8940004fd73d8940076ee42d8940076ed42d8940004ff71d894000cfe71d8940004fd71d894000cfc71d89400067f51d89400067d51d8940076bf41d8940006bd41d8940006df31d8940006dd31d8940006fa10d8940006f910d8940006ef629894005df970989400057f75589401057c7558940005df7358940005dc7358940005f771589400fdf4715894008dfb705894002eee6218940006ed6218940004fe7694940004fd769494002cfc76949400067f659494001e7c6594940015be7494940005bd74949401d73c5494940025fa7094940005f97094940004ff7654940004fe7654940004fc7654940005bf7454940015bc7454940024bc76509400073f7550940105be7550940105bc75509400073c75509401053c7550940006bf6550940006bd6550940005bf735094025ebc6350940015bf7250940017af7250940007af625094002ebe625094002ebc6250940007ac625094002eac625094033dbf715094033dbd715
  | 15 => 0xf7650950004fe7650950004fc76509500057f755095001d7c7550950016be6450950127ac4250950004fe76cc950004fd76cc95004cfc76cc95001d7e75cc9500057d75cc950004fe768c950004fd768c95002cfc768c950125be748c950005bd748c950006df638c95004edc638c950004ff764c950004fe764c950004fc764c950004fe760c950004fd760c95002cfc760c95001d7e750c9500057d750c950006df630c95004edc630c950025fa700c950005f9700c9500267f75596401267f54596401267d5459640004ff735964004cfc73596401167f5359640004ff725964002cfc72596401167c5259640004ff715964000cfe7159640004fd715964000cfc71596401167f51596400067d5159640006df3159640006dd3159640024fe7059640024fc70596400267e50596400267c5059640004ff7558e4001cfe7558e4001cfc7558e40026df7358e400bede4358e400bedd4358e40004ff7258e4002cfc7258e40004ff7158e4000cfe7158e40004fd7158e4000cfc7158e400067f5158e400067d5158e40006df3158e40006dd3158e40024fc7058e40026bf4058e40026bd4058e40026de3058e40026dc3058e4004cff7694e40024fe7694e40004fd7694e401175f5394e40004ff7654e40004fd7654e40024fc7654e4001e7e6554e400067d6554e40005fb7054e40025f87054e40004ff7558a4001cfe7558a4001cfc7558a40004ff7358a4004cfc7358a40026ef7258a40006ef5258a40006ec5258a4005eee4258a4005eed4258a40004ff7158a4000cfe7158a40004fd7158a4000cfc7158a400067f5158a400067d5158a40006df3158a40006dd3158a40006ef2158a40006ed2158a40024fc7058a40026bf4058a40026bd4058a40026ee2058a40026ec2058a40026fa1058a40006f91058a4002cff7694a40024fe7694a40004fd7694a4001e7e6594a400067d6594a40025fa7094a40005f97094a40004ff7654a40004fd7654a40024fc7654a4004cff76cca40024fe76cca40004fd76cca401157e75cca400057d75cca4002cff768ca40024fe768ca40004fd768ca40015be748ca40005bd748ca4002eee628ca40006ed628ca40004ff764ca40004fd764ca40024fc764ca4002eee624ca40006ed624ca4002cff760ca40024fe760ca40004fd760ca40025fa700ca40005f9700ca4001cfe76d95401067e65d9540015be74d9540025bd74d95401073f54d9540024ff74d9540014fe74d9540024fd74d9540106bd74d9540024bd74d9540014fc74d95401367f54d9540106bf54d95401063f54d95401367d54d9540136bc54d954004cfe73d9540004fd73d95401067c53d954002cfe72d9540004fd72d95401067c52d9540136bf42d9540004ff71d954000cfe71d9540004fd71d954000cfc71d95401067f51d9540
  | 16 => 0xa50024fe7690a50004fd7690a502ad7f7590a5001d7c7590a50016be6490a50006bd6490a5002eee6290a50006ed6290a50004ff7650a50004fd7650a50024fc7650a500057f7550a5001d7c7550a50016be6450a50006bd6450a500073d5450a5002eee6250a50006ed6250a50137ac4250a5004cff76cca50024fe76cca50004fd76cca5001d7e75cca500057d75cca5018ebe64cca50006bd64cca5002eee62cca50006ed62cca5002cff768ca50024fe768ca50004fd768ca5001d7e758ca500057d758ca50135be748ca50005bd748ca50176be648ca50006bd648ca5002eee628ca50006ed628ca50004ff764ca50004fd764ca50024fc764ca500057f754ca5001d7c754ca5015ebe644ca50006bd644ca5002eee624ca50006ed624ca5002cff760ca50024fe760ca50004fd760ca502ad7f750ca5001d7c750ca50146be640ca50006bd640ca5002eee620ca50006ed620ca50025fa700ca50005f9700ca50014fe76d9150126be64d9150024fd75d9150014fc75d9150126be54d9150116bd54d915004cfe73d9150004fd73d91501167f53d915002cfe72d9150004fd72d9150004ff71d915000cfe71d9150004fd71d915000cfc71d91501167f51d91500067d51d9150006df31d9150006dd31d915001cfd70d91503767e50d91503767c50d9150126bf40d9150126bc6459150005df7359150005dc735915036dfb7059150024fd75d8d50014fe74d8d50004fd74d8d50014fc74d8d500dede53d8d500dedd53d8d50006df43d8d50006dc43d8d5002cfe72d8d50004fd72d8d50004ff71d8d5000cfe71d8d50004fd71d8d5000cfc71d8d500de7f51d8d500067d51d8d50006df31d8d50006dd31d8d502fe7f6598d50006df6398d500c5f97098d500f5fb7058d502f67f6518d5004ede6318d50006dd6318d500247c7654d500067f6454d5001d7f7354d5001f5f7354d500075f6354d5004e7e6354d5004e7c6354d500075c6354d502d67c6254d503657f7154d503657d7154d5035e7f6154d5035e7d6154d5035f5f3154d5035f5d3154d500077b7054d500257e7054d500257c7054d50007787054d5001e7f6054d5001f7b6054d50004fe7690d50004fd7690d5004cfc7690d5001d7e7590d500057d7590d50004ff7650d50004fe7650d50004fc7650d50024fd75d8950014fe74d8950004fd74d8950014fc74d895004cfe73d8950004fd73d895007eee52d895007eed52d8950004ff71d895000cfe71d8950004fd71d895000cfc71d895007e7f51d89500067d51d8950006df31d8950006dd31d89502a67f6598950006ef6298950065f97098950005df7358950005dc7358950095fb705895029e7f6518950125be7418950005bd741895002eee6218950006ed6218950004fe7690950004fd769095002cfc7690950004f
  | 17 => 0x96ef5498a50096ee5498a50096ed5498a50096ec5498a5002eef7398a5002eee7398a5002eed7398a5002eec7398a50096ef5398a50096ee5398a50096ed5398a50096ec5398a50006ef4398a50006ee4398a50006ed4398a50006ec4398a5002eef7198a5002eee7198a5002eed7198a5002eec7198a50096ef5198a500966f5198a50096ee5198a50096ed5198a500066d5198a50096ec5198a50006ef4198a50006ee4198a50006ed4198a50006ec4198a50006ef3198a50006cf3198a50006ee3198a50006ed3198a50006cd3198a50006ec3198a50026ef7098a50026ee7098a50026ed7098a50026ec7098a50026ef5098a50026ee5098a50026ed5098a50026ec5098a50026ef4098a50026ee4098a50026ed4098a50026ec4098a50026ef3098a50026ee3098a50026ed3098a50026ec3098a50026ef1098a50026ee1098a50026ed1098a50026ec1098a50004ff7458a50014fe7458a50014fc7458a50004ff7358a5004cfc7358a50026ef7258a50066ee5258a50066ed5258a502ae7c5258a50006ef4258a50006ec4258a50004ff7158a5000cfe7158a50004fd7158a5000cfc7158a500667f5158a500067d5158a50006df3158a50006dd3158a50006ef2158a50006ee2158a50006ed2158a50006ec2158a50024fc7058a50026ee2058a50026ec2058a50066ee7558a50066ed7558a50066ec7558a500666c7558a50006ef7458a50006ee7458a50006ed7458a50006ec7458a50066ef5458a50066ee5458a50066ed5458a50066ec5458a50006ef7358a50006ee7358a50006ed7358a50006ec7358a50066ef5358a50066ee5358a50066ed5358a50066ec5358a50006ef4358a50006ee4358a50006ed4358a50006ec4358a50006ef7158a50006ee7158a50006ed7158a50006ec7158a50066ef5158a500666f5158a50066ee5158a50066ed5158a500066d5158a50066ec5158a50006ef4158a50006ee4158a50006ed4158a50006ec4158a50006ef3158a50006cf3158a50006ee3158a50006ed3158a50006cd3158a50006ec3158a50026ef7058a50026ee7058a50026ec7058a50026ef5058a50026ee5058a50026ed5058a50026ec5058a50026ef4058a50026ee4058a50026ed4058a50026ec4058a50026ef3058a50026ee3058a50026ed3058a50026ec3058a50026ef1058a50026ee1058a50026ed1058a50026ec1058a500057d7494a501d67e6494a502a73e6494a501d63e6494a502a73d6494a502a67c6494a503057e7394a500067d6394a5001d7e7294a5001f6e7294a502a67f6294a502a76e6294a502ae7d6294a502a76d6294a502ad7f7194a503857d7194a502a67f6194a5037e7d6194a5037f5f3194a5037f5d3194a502a77a7094a502a57d7094a502af797094a5001e7e6094a5001f7a6094a5002cff769
  | 18 => 0xc4259250004ff715925000cfe7159250004fd715925000cfc71592501067f51592500067d5159250136bf4159250006be4159250006bd4159250136bc4159250006df3159250006dd3159250024fe7059250024fc7059250026be4059250026bc4059250106be7559250106bd7559250136bc7559250006bf7359250006be7359250006bd7359250006bc7359250106bf5359250106be5359250106bd5359250106bc5359250006bf7259250006be7259250006bd7259250006bc7259250106bf5259250106be5259250106bd5259250106bc5259250006bf7159250006be7159250006bd7159250006bc7159250106bf51592501063f5159250106be5159250106bd51592500063d5159250106bc5159250006bf31592500069f3159250006be3159250006bd31592500069d3159250006bc3159250006bf2159250006be2159250006bd2159250006bc2159250026bf7059250026be7059250026bc7059250026bf5059250026be5059250026bd5059250026bc5059250026bf3059250026be3059250026bd3059250026bc3059250026bf2059250026be2059250026bd2059250026bc2059250026bf1059250026be1059250026bd1059250026bc105925032d7f76552500167f76552500147f765525001d7f745525001f3f74552500167e645525032f3e645525032f3d64552500167c64552503057c73552502ad7c725525032f6e625525032f6d62552501373f42552503a57f71552503a57d715525032e7f615525039e7d615525039f5f315525039f5d315525032d7f70552500077b705525032f78705525001e7e605525001f7a6055250004ff7458e50014fe7458e50014fc7458e500c67f5458e500067d5458e50026df7358e500c6de5358e500c6dd5358e503067c5358e50004ff7258e5002cfc7258e500c67c5258e50004ff7158e5000cfe7158e50004fd7158e5000cfc7158e500c67f5158e500067d5158e50006df3158e50006dd3158e50024fc7058e500267f5058e500267d5058e50026de3058e50026dc3058e500057d7494e502ff3e6494e502ff3d6494e5001d7e7394e5001f5e7394e502fe7f6394e502ff5e6394e503067d6394e502ff5d6394e500065d6394e502ad7e7294e502ff6e6294e502ff6d6294e503057f7194e503957d7194e502fe7f6194e5038e7d6194e503075f3194e5038f5d3194e502ff7a7094e502fd7d7094e50307797094e50005797094e5001e7e6094e5001f7a6094e5004cff7690e50024fe7690e50004fd7690e503057f7590e5001d7c7590e50016be6490e50006bd6490e50004ff7650e50004fd7650e50024fc7650e500057f7550e5001d7c7550e50016be6450e50006bd6450e5002eef7598a5002eee7598a5002eec7598a5002eef7498a5002eee7498a5002eed7498a5002eec7498a50
  | 19 => 0xd32005ef7250d3202dec7250d3201cff7654932164fd765493204cfc76549320067f655493201e7c6554932005df735493204ddc735493202fcc3254932014ff765093215cfd765093204cfc76509320057f75509321657c7550932006bf6450932016bc6450932005df735093204ddc735093202fac425093201cfe75d8132004fd75d813201cfc75d8132014fe74d8132004fd74d8132014fc74d8132004ff71d813200cfe71d8132004fd71d813200cfc71d81320067f51d81320067d51d8132006df31d8132006dd31d8132006fb60981320057f75581321657c755813215dbe7418132005bd741813223edf6318132026fa6018132006f9601813202cff755943202e7f7559432004ff7459432014fe7459432014fc745943214e7f545943204cfe735943204cfc735943204e7e535943204e7c535943202cfe725943202cfc725943202e7e525943202e7c5259432004ff715943200cfe7159432004fd715943200cfc715943214e7f51594320067d515943204edf3159432006dd3159432004ff7059432024fc705943214e7f5059432004ff755903201cfe755903201cfc755903202cff745903202ebf7459032146be545903204cfe735903204cfc735903204ebe435903204ebc435903202cfe725903202cfc725903202ebe425903202ebc4259032004ff715903200cfe7159032004fd715903200cfc71590320067f51590320067d5159032146bf4159032006bd415903204edf3159032006dd3159032004ff7059032024fc7059032146bf4059032004ff765503202cfe7655032004fd765503202cfc765503201e7e65550320067d6555032016be6455032006bd645503202def7650832176ef76508320076f75508320076c755083202def745083202faf745083202faf6450832016ee645083202eec645083202fac645083202eac6450832147ae5450832007ad545083225def735083225ded735083225eee635083202fce635083225fae435083225fac435083202eef61508323aeed61508323af6f51508323af6d5150832147af41508323afad415083225fcf31508323afcd3150832147af4050832004ff75580320067f75580320047f755803201cfe755803201cfc75580320067c755803201c7c7558032004ff7458032014fe7458032014fc745803202eee4258032006ed425803202eee325803204eed3258032004ff715803200cfe7158032004fd715803200cfc71580320067f51580320067d515803204edf3158032006dd315803202efb705803204efb305803204edc305803204ef8305803202efb205803202ef82058032006fa1058032006f91058032026bf7459250136be5459250106bd5459250004ff735925004cfc7359250136bf4359250136bc4359250004ff725925002cfc7259250136bf4259250136b
  | 20 => 0x2ebe215923202ebd215923202ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006bc505923225ebf305923225ebc305923202ebf205923202eaf205923202ebe205923202ebd205923202ebc2059232006bf1059232006be1059232006bd1059232006bc1059232004ff765523202cfe7655232004fd765523202cfc7655232016be6455232006bd645523201cff7654e3202cfc7654e3201e7e6554e320067d6554e32206be6454e32006bd6454e32005ef7254e3202dec7254e3204fcf3254e32014ff7650e3202cfc7650e32016be6450e32006bd6450e32005ef7250e3202dec7250e32004ff755823201cfe755823201cfc7558232004ff7458232014fe7458232014fc745823202cfc7258232004ff715823200cfe7158232004fd715823200cfc71582320067f51582320067d5158232006df3158232006dd315823202efb7058232006fb5058232006f8505823202efb205823202ef82058232006fa1058232006f9105823201cfe76d95321667e65d9532014fe74d9532004fd74d9532014fc74d95320067e54d95321667c54d953202cfd73d95321667f53d953204cfd72d95321667f52d9532004ff71d953200cfe71d9532004fd71d953200cfc71d95321667f51d95320067d51d9532006df31d9532006dd31d9532024fe70d9532004fd70d95321667c50d95321667c6559532164ff75595320067f7559532004ff7459532014fe7459532014fc745953217cff7359532006df7359532194ff7259532006ef72595322d67e52595322d67c5259532004ff715953200cfe7159532004fd715953200cfc71595321667f51595320067d5159532006df3159532006dd3159532004ff7059532024fc7059532014fe76d913215ebe64d913201cfe75d9132004fd75d913201cfc75d913202cfd73d913215ebf43d913204cfd72d913215ebf42d9132276ef32d9132276ec32d9132004ff71d913200cfe71d9132004fd71d913200cfc71d91320067f51d91320067d51d9132006df31d9132006dd31d9132024fe70d9132004fd70d91320057f75591321657c755913215ebc6459132004ff75591320067f75591320047f755913201cfe755913201cfc75591320067c755913201c7c755913215cff7459132006bf7459132174ff7359132006df735913225ebe435913225ebc435913218cff7259132006ef725913225eef3259132004ff715913200cfe7159132004fd715913200cfc71591320067f51591320067d5159132006df3159132006dd3159132004ff7059132024fc705913215ebf4059132004ff7655132004fe7655132004fd7655132004fc765513202cfc7654d320067f6554d3201e7c6554d32005ef7254d3202dec7254d3204fcc3254d3202cfc7650d32006bf6450d32016bc645
  | 21 => 0xe3254b32275ed7690b3202eed7690b322776e6590b322776d6590b32016ee6490b32016ec6490b3202def7390b32275ed7390b3202fce6390b32276ef6190b323beed6190b323bf6f5190b323bf6d5190b32277cf3190b323bfcd3190b32014ff7650b3204cfc7650b320057f7550b321957c7550b321a67e6550b320067d6550b32016be6450b32006bd6450b32005df7350b3204ddc7350b3202fac4250b3225def7650b32016ef7650b32014ef7650b320076f7550b320076c7550b3225f6e6550b3225f6d6550b3202def7450b3202faf7450b32016ee6450b3225fae6450b32016ae6450b3225fad6450b32016ec6450b3218fae5450b32007ad5450b3225def7350b32007cf7350b3225fcc7350b3202eee6350b3225fae4350b3225fac4350b3225eef6150b323b6ed6150b323b76f5150b323b76d5150b3218faf4150b323b7ad4150b3225fcf3150b323b7cd3150b3218faf4050b32004ff755833201cfe755833201cfc7558332004ff7458332014fe7458332014fc745833202cfc7358332006ee4258332006ed425833204eee325833204eed3258332004ff715833200cfe7158332004fd715833200cfc71583320067f51583320067d515833204edf3158332006dd315833204efb705833204efb305833204ef8305833202e7f7559632004ff7459632014fe7459632014fc745963217e7f535963202cfc725963202e7e525963202e7c5259632004ff715963200cfe7159632004fd715963200cfc715963217e7f51596320067d5159632006df3159632006dd3159632004ff7059632024fc705963217e7c5059632004ff755923201cfe755923201cfc755923202ebf7459232006bf5459232176be5459232176bc5459232176bf435923202cfc725923202ebe425923202ebc425923225eef325923202eec3259232004ff715923200cfe7159232004fd715923200cfc71592320067f51592320067d5159232176bf4159232006be4159232006bd4159232176bc4159232006df3159232006dd3159232004ff7059232024fc7059232176bf4059232176bc405923202eef2059232006bf7559232006be7559232006bd7559232006bc7559232006bf735923225ebe7359232006bd735923225ebc7359232006bf535923225ebe535923225ebc535923202ebf725923202ebe725923202ebd725923202ebc725923202ebf525923202ebe525923202ebd525923202ebc525923202ebf325923225eaf325923202ebe325923202ebd325923202ebc325923202eac3259232006bf7159232006be7159232006bd7159232006bc7159232006bf51592320063f5159232006be5159232006bd51592320063d5159232006bc515923225ebf31592320069f3159232006be3159232006bd31592320069d315923225ebc315923202ebf2159232
  | 22 => 0xd423c7ad2190d42005bd7090d4201cff7654942014fe76549421c4fd7654942014fc76549420067f655494201e7c6554942005bf7454942015bc745494202fac42549420067f65d81420067c65d814208fac42d814201cfe75d8142004fd75d814201cfc75d814202cfd74d814204cfe73d8142004fd73d8142004ff71d814200cfe71d8142004fd71d814200cfc71d81420067f51d81420067d51d814208ebf41d8142006bd41d8142006df31d8142006dd31d8142006ef21d8142006ed21d814208efa40d81421a57e75981420057d75981420067f65981420067c6598142077ac4298142006fb60981420057f75581421a57c75581420067f65581420067c6558142005df7358142005dc735814205fac4258142005f7715814219df471581420067f65181420067c651814203fac4218142026fa6018142006f9601814204e7f7559732004ff7459732014fe7459732014fc74597321967f54597320067e54597321967c545973202cfc735973204e7e535973204e7c53597321967f5259732004ff715973200cfe7159732004fd715973200cfc71597321967f51597320067e51597320067d51597321967c515973204edf3159732006dd3159732004ff7059732024fc70597321967f50597321967c50597320067f74597320067e74597320067d74597320067c745973204e7f735973204e7e735973204e7d735973204e7c735973204e7f435973204e7e435973204e7d435973204e7c43597320067f72597322d67e72597320067d72597322d67c72597320067f42597322d67e42597322d67c425973204e7f325973204e7e325973204e7d325973204e7c32597320067f71597320047f71597320067e71597320067d71597320047d71597320067c71597320067f41597320067e41597320067d41597320067c415973204e7f315973204e5f315973204e7e315973204e7d31597320065d315973204e7c31597322d67f21597320067e21597320067d21597322d67c21597320067f70597320067e70597320067d70597320067c70597320067f40597320067c405973204e7f305973204e7e305973204e7d305973204e7c30597322d67f20597322d67c20597320067f10597320067e10597320067d10597320067c1059732004ff755933201cfe755933201cfc755933204ebf745933202cfc735933204ebe435933204ebc435933218ebf4259332004ff715933200cfe7159332004fd715933200cfc71593320067f51593320067d5159332006be415933218ebc415933204edf3159332006dd3159332004ff7059332024fc705933218ebf4059332004ff765533204cfe7655332004fd765533204cfc765533201e7e65553320067d655533201cff7654b3204cfc7654b3201e7e6554b320067d6554b32005df7354b3204ddc7354b3202fc
  | 23 => 0x67c70d95421d67f40d95421d67e40d95421d67d40d95421d67c40d95423fe7f20d95423fe7c20d95420067f10d95420067e10d95420067d10d95420067c10d95421a67c65595423f5ef72595421c7ac42595421d4ff75595420067f75595421c4ff7459542006bf7459542004ff735954204cfc73595423f4ff7259542006ef7259542004ff715954200cfe7159542004fd715954200cfc71595421a67f51595420067d5159542006df3159542006dd3159542004ff7059542024fc70595421d57e76195421a67e76195421d47e76195423e73e74195421a73d74195423ee7f64195423e73c43195423e67f62195423e76f42195423ef3e42195423ef3c42195423e76c42195423e72c42195421a57f71195420057d71195420067f61195420067e61195420067d61195420067c61195423e73f41195420073d41195420075f31195420075d31195420076f21195420076d21195423e73f401954202dbc765514201ebc765514202cbc7655142015bf75551420173f75551420073f655514201ebe655514201ebc65551421a73c655514225dbc73551421a73f5355142007af725514202dbe725514202dbc7255142007ac725514202dac7255142016bf6255142017af62551423ddbf71551423ddbd71551421a73f51551423d73d51551423d79f31551423d79d31551423d7af21551423d7ad2155142005bf70551421a73c50551420067f65d8d420067c65d8d42177ac42d8d4201cfe75d8d42004fd75d8d4201cfc75d8d4202cfd74d8d42176de43d8d42176dd43d8d4225ebc43d8d42176ed72d8d42004ff71d8d4200cfe71d8d42004fd71d8d4200cfc71d8d420067f51d8d420067d51d8d42006df31d8d42006dd31d8d42024fe70d8d42004fd70d8d42176bf40d8d421a57e7598d420057d7598d420067f6598d420067c6598d42006df6398d4215ded7298d4218fac4298d4219df67198d42005f57198d420057f7558d421a57c7558d420067f6558d420067c6558d4218def7258d4215fac4258d420067f6518d420067c6518d4204ede6318d42006dd6318d42147ac4218d42004fe7694d42004fd7694d4204cfc7694d420067f6594d4201e7c6594d42015bc7494d421a75f5394d42217ac4294d42004ff7654d42004fe7654d42004fc7654d420067f6554d4201e7c6554d42005bf7454d42015bc7454d420073d5454d42005ef7254d4202dec7254d42207ac4254d4202cbe7690d4225dbf7590d42005bd7590d420073f6590d420073c6590d42015be7390d420179e7390d4225ebf6390d420079f6390d4225f9c6390d4202dbe7290d4225fae7290d4202dae7290d4225fad7290d4202dbc7290d42016bf6290d42017af6290d4225dbf7190d423cdbd7190d423c73f5190d423c73d5190d4225f9f3190d423c79d3190d423c7af219
  | 24 => 0xc725964202e7e525964202e7c525964202ebf425964202ebd4259642004ff715964200cfe7159642004fd715964200cfc71596421b67f51596420067d5159642006df3159642006dd3159642004ff7059642024fc7059642004ff7558e4201cfe7558e4201cfc7558e4202edf7358e4215ede4358e4215edd4358e4202cfc7258e4202eec7258e4202cec7258e4202ede3258e4202edc3258e4202eec3258e42004ff7158e4200cfe7158e42004fd7158e4200cfc7158e420067f5158e420067d5158e42006df3158e42006dd3158e42004ff7058e42024fc7058e4202eef2058e4204cff7694e4202cfe7694e42004fd7694e421b75f5394e42004ff7654e42004fd7654e4202cfc7654e422d67f6554e4201e7c6554e42005ef7254e4202dec7254e42004ff75582420067f75582420047f755824201cfe755824201cfc75582420067c755824201c7c7558242004ff735824204cfc735824202cfc725824202ebf425824202ebd4258242004ff715824200cfe7158242004fd715824200cfc71582420067f51582420067d5158242006df3158242006dd315824202eef2158242006ed215824202efb705824205efa405824202efb205824202ef82058242006fa1058242006f9105824201cfe76d95421a67e65d95421d7ac42d954202cff74d954202cfd74d95421d67f54d95421d67d54d954204cfe73d9542004fd73d95421a67f53d95421a67c53d9542014fd72d95421a67f52d9542004ff71d954200cfe71d9542004fd71d954200cfc71d95421a67f51d95420067e51d95420067d51d95421a67c51d9542006df31d9542006dd31d9542024fe70d9542004fd70d95421a67f50d95421a67c50d95423e57e76d954201c7e76d95423ff3f74d95421d73c74d95421d73c43d95421d76f42d95423ff3e42d95423ff3c42d95421d76c42d95421d72c42d95420057f71d95420057d71d95420067f61d95420067e61d95420067d61d95420067c61d95421d73f41d95420073d41d95420075f31d95420075d31d95420076f21d95420076d21d95421d73f40d95423fe7f74d95421d67e74d95421d67d74d95421d67c74d95420067f73d95420067e73d95420067d73d95420067c73d95421d67f43d95421d67e43d95421d67d43d95421d67c43d95421d67f72d95423fe7e72d95421d67d72d95423fe7c72d95421d67f42d95423fe7e42d95423fe7c42d95423fe7e32d95423fe7c32d95420067f71d95420047f71d95420067e71d95420067d71d95420047d71d95420067c71d95421d67f41d95421d67e41d95421d67d41d95421d67c41d95420067f31d95420065f31d95420067e31d95420067d31d95420065d31d95420067c31d95423fe7f21d95420067e21d95420067d21d95423fe7c21d95420067f70d95420067e70d95420067d70d9542
  | 25 => 0x92521d6bf4159252006bd4159252006df3159252006dd3159252004ff7059252024fc70592521a67c50592521d6bf4059252004ff7458e52014fe7458e52014fc7458e5202edf7358e52166de5358e52166dd5358e5202cfc7258e5202ede3258e5202edc3258e52004ff7158e5200cfe7158e52004fd7158e5200cfc7158e521667f5158e520067d5158e52006df3158e52006dd3158e52004ff7058e52024fc7058e5204c7f7654e521d57e7454e521d57c7454e520067d6454e5201d7f7354e5201f5f7354e5204e7e6354e522d75e6354e522d75d6354e5204e7c6354e522d57f7254e520076f7254e522d76c7254e5201e7e6254e5201f6e6254e5241d7f7154e5241d7d7154e522d67f6154e524167d6154e524175f3154e524175d3154e522a57c7054e5204cff7690e5202cfe7690e52004fd7690e5201d7e7590e520057d7590e52016be6490e52006bd6490e52004ff7650e52004fd7650e5202cfc7650e520057f7550e5201d7c7550e52004ff7458252014fe7458252014fc7458252004ff735825204cfc73582520667f53582520067d535825202cfc7258252066ef525825202eec5258252004ff715825200cfe7158252004fd715825200cfc71582520667f51582520067d5158252006df3158252006dd315825202efb7058252066fa50582522a67c505825202efb205825202ef82058252006fa1058252006f91058252014fe76d91521c6be64d915202cfd75d91521c6be54d91521b6bd54d915204cfe73d9152004fd73d915201cfd72d91521c6bf42d9152004ff71d915200cfe71d9152004fd71d915200cfc71d91521b67f51d91520067d51d9152006be41d91521c6bc41d9152006df31d9152006dd31d9152024fe70d9152004fd70d91521c6bf40d91521c6bc645915240def725915202cfd75d8d52014fe74d8d52004fd74d8d52014fc74d8d5217ede53d8d5217edd53d8d524067e52d8d524067c52d8d52004ff71d8d5200cfe71d8d52004fd71d8d5200cfc71d8d5217e7f51d8d520067d51d8d52006df31d8d52006dd31d8d52024fe70d8d52004fd70d8d52006df6398d52165ed7298d52195ef7258d5204ede6318d52006dd6318d52004fe7690d52004fd7690d5204cfc7690d52004ff7650d52004fe7650d52004fc7650d5202cfd75d8152014fe74d8152004fd74d8152014fc74d815204cfe73d8152004fd73d8152096ef52d8152096ec52d8152004ff71d815200cfe71d8152004fd71d815200cfc71d81520967f51d81520067d51d8152006df31d8152006dd31d8152096fa50d81521c5be7498152005bd7498152006fb6098152005df7358152005dc73581522a67f6518152026fa6018152006f9601815202e7f75596421c67f54596421c67d5459642004ff735964204cfc735964202cfe725964202cf
  | 26 => 0x206bf4259643004ff715964300cfe7159643004fd715964300cfc71596431f67f51596430067d515964304edf3159643006dd3159643004ff7059643024fc70596431f67f5059643004ff7558a4301cfe7558a4301cfc7558a4304cfc7358a4304eef7258a4315eee4258a4304eef3258a4304eec3258a43004ff7158a4300cfe7158a43004fd7158a4300cfc7158a430067f5158a430067d5158a4304edf3158a43006dd3158a43004ff7058a43024fc7058a43004ff75582430067f75582430047f755824301cfe755824301cfc75582430067c755824301c7c755824304cfc735824304ebf435824304ebd4358243004ff725824302cfc72582430bebf4258243004ff715824300cfe7158243004fd715824300cfc71582430067f51582430067d515824304edf3158243006dd315824304efb70582430befa405824304efb305824304ef8305824301cfe76d95431e67e65d954304cff74d954304cfd74d95432167f54d95432167d54d9543014fd73d95431e67f53d954302cfe72d9543004fd72d95431e67c52d9543004ff71d954300cfe71d9543004fd71d954300cfc71d95431e67f51d95430067d51d9543006df31d9543006dd31d9543024fe70d9543004fd70d95431e67c50d95431e67c655954342ddf7359543214ff75595430067f7559543204ff7459543006bf745954342cff7359543006df7359543004ff725954302cfc7259543004ff715954300cfe7159543004fd715954300cfc71595431e67f51595430067d5159543006df3159543006dd3159543004ff7059543024fc705954301cff7654d43014fe7654d43204fd7654d43014fc7654d430067f6554d4301e7c6554d43005bf7454d43015bc7454d4304f9c4354d4301cfe75d8943004fd75d894301cfc75d894304cfd74d8943426be43d8943426bc43d894318eee42d8943004ff71d894300cfe71d8943004fd71d894300cfc71d89430067f51d89430067d51d8943006df31d8943006dd31d8943024fe70d8943004fd70d894318ebf40d8943006ef62989430057f75589431e57c755894302eee6218943006ed621894301cfe75d8143004fd75d814301cfc75d814304cfd74d814302cfe72d8143004fd72d8143004ff71d814300cfe71d8143004fd71d814300cfc71d81430067f51d81430067d51d8143006df31d8143006dd31d81430eefa40d8143006fb60981430057f75581431e57c7558143005ee7218143005ed7218143026fa6018143006f9601814302ebf74592521d67e54592521d6be54592521d63e54592521a6bd54592521d67c5459252004ff735925204cfc73592521a67f53592521d6bc435925202cfe725925202cfc725925202ebe425925202ebc4259252004ff715925200cfe7159252004fd715925200cfc71592521a67f51592520067d515
  | 27 => 0xe54592531e6bd545925304cfe735925304cfc735925304e7f535925304e7d535925304ebe435925304ebc4359253004ff725925302cfc7259253004ff715925300cfe7159253004fd715925300cfc71592531e67f51592530067d515925304edf3159253006dd3159253004ff7059253024fc70592531e67c5059253216bf4059253004ff7458a53014fe7458a53014fc7458a5304cfc7358a5304eef7258a53166ee5258a5304eef3258a5304eec3258a53004ff7158a5300cfe7158a53004fd7158a5300cfc7158a531667f5158a530067d5158a5304edf3158a53006dd3158a53004ff7058a53024fc7058a53004ff7458253014fe7458253014fc745825304cfc735825304e7f535825304e7d5358253004ff725825302cfc7258253004ff715825300cfe7158253004fd715825300cfc71582530c67f51582530067d515825304edf3158253006dd315825304efb70582530c6fa50582532fe7c505825304efb305825304ef83058253014fe76d9153206be64d915304cfd75d9153206be54d91531f6bd54d915301cfd73d9153206bf43d915302cfe72d9153004fd72d9153206bf42d9153004ff71d915300cfe71d9153004fd71d915300cfc71d91531f67f51d91530067d51d9153006be41d9153206bc41d9153006df31d9153006dd31d9153024fe70d9153004fd70d9153206bf40d9153206bc6459153445df735915304d7c76551530167c765515304c7c765515301d7f745515301f3f74551530073f64551530167e64551530167c64551532073c64551530075f735515304d7e735515304d7c73551530075c735515301e7f635515301f5f63551532d57c72551532073f425515343d7f715515343d7d71551534367f61551534367d61551534375f31551534375d31551530057f705515332e7c605515304cfd75d8953014fe74d8953004fd74d8953014fc74d8953196ee52d89532d67c52d8953004ff71d895300cfe71d8953004fd71d895300cfc71d89531967f51d89530067d51d8953006df31d8953006dd31d8953006ee21d8953006ec21d8953024fe70d8953004fd70d8953205be7498953005bd7498953006ef6298953005fa7098953005f9709895302eee6218953006ed621895304cfd75d8153014fe74d8153004fd74d8153014fc74d815302cfe72d8153004fd72d8153004ff71d815300cfe71d8153004fd71d815300cfc71d81530f67f51d81530067d51d8153006df31d8153006dd31d81530f6fa50d8153006fb10d8153006f810d8153205be7498153005bd7498153005ee7298153005ed7298153006fb60981532fe7f6518153026fa6018153006f9601815304e7f75596432067f54596432067d545964304cfe735964304cfc735964304e7e535964304e7c5359643004ff725964302cfc72596431f67c5259643
  | 28 => 0x1801001600000b000c0000010000000034001001000807a001006802c02400e000000800200800300080020000038000000000001004400401a0000008000002004800000e003001800402c00400b800806c00300b814001000100100040000060078018000019001800c034001008808801600b006005402a01d000800000200100080000060050088008006017000802c00600001100080140000028020012008000802400e001000000400000500000080d0001016800000c004008001c0300000018008000000004000c01c04d00880a00160100170024014003001002001601d009000c00001e00b00100700050058048002000001800c006000000007402e00a00900140180020028000000004008800c01200800d8004000001001002c01800d002000000000400c004c004003002802801400000700040000050000024000005000000c00c018000004002600101c0000016065000800801a002000000000000b00880440000000048020000007003000400e000014002c03200a00600500120040000000002000003806400200e0010004004004005000001a00c008800c01e001000002c00200d0000018004000000007000e01b00c000801e010005000c0000080020000026005007001001e00400b002000000701c00000040030000000008021004804803c00600600000060030008020004032005000000000e008000800a003000004c00201d0100014000000006800800c00c00e800c002000005800002c05700180000000290060008014002000000000c00804cfe76d8d54014fd75d8d5401cfd74d8d54446de53d8d5442ede43d8d5402cfe72d8d54004fd72d8d54004ff71d8d5400cfe71d8d54004fd71d8d5400cfc71d8d544467f51d8d540067d51d8d54006df31d8d54006dd31d8d54024fe70d8d54004fd70d8d54006df6398d5404ede6318d54006dd6318d5402cfe76d8954014fd75d895401cfd74d895404cfe73d8954004fd73d895440eee52d89543f6ee42d8954004ff71d895400cfe71d8954004fd71d895400cfc71d895440e7f51d89540067d51d8954006df31d8954006dd31d8954006ee21d8954006ec21d8954024fe70d8954004fd70d89543fe7f6598954006ef62989543fe7f651895402eee6218954006ed6218954024fe76d8154014fd75d81543567d75d815401cfd74d815436ebf54d8154356bc54d815404cfe73d8154004fd73d815436e7f53d815402cfe72d8154004fd72d8154356bf42d8154004ff71d815400cfe71d8154004fd71d815400cfc71d815436e7f51d81540067d51d8154006df31d8154006dd31d815436efa50d815432e7c50d8154356fa40d8154005ee7298154005ed7298154006fb6098154005df7358154005dc7358154026fa6018154006f9601815404ebf7459253216b
  | 29 => 0x3002001400400502100040380050008070002005021804400000d000802000600102b800004c009007002000c026000003000002400a80180160000038000068000004005400800200c002000000500f00040000100060050000001003805c0180130050000000009005000000400500a8014040010000002000000a0000068014005000004c07a0000040018012000001002001000901d8010002000003801400e00800080080000010020008004001000800001c01200b004401e004000800001200800c0014004006000806400a012000003000200b008800800001b005802006400b001800c068000004800800401d000801000c001001804c02e00f0010008000000001800001002c000000000800000000280260040040004000001003003c030004000000c00000a0010050000015000002000001a000002c0000050000014018002005800800a00b00c0000000001008800c012015011802c00a000015002401000900700640c60050040018018003004000400000f000003c00801b0020004008001019800c0040020010024004001000000c0020020000020000000005800800200201600e00020110000004008009001000c036009002802004800400400040000080010038000000000800000a000007800001800c00000780000000058008002004006000400200c0000020016001019800400605900200080020000000000012001001800000200900000000020010030008002000007003c000002000001c00000c005800009c002000808c02000500380280000000218008032000001803c00c000007800c0220000028024020001000000c01000f001801400600100e007401a00c0110004002001027800002800000500100020120098024026000000800000c002009801c00e01e007000407600300300140020000030000000035001802400e024003801002800700280a00020150148010012000000001002402a009002c002006000002c01c018001000c006000000000000800600100ec00c01000a000000202500400440720120090058000002006800800e01d007800001c01200000000460020088034000002000003800e00000d0010000000002000400000100d8008000008010003800a00c002804402200000000000380190080000010000006800c002013007800400400c0008014000002000803400a00000d801800600000080080100000028018006000001801c002000000801c0060000008004016000003000800200002980040020000000044008007000002001800b00480000000070030014008007002000001600400200000400000010000014003006001800000200b8024000001001800c000003000800803a00d00d801004c000002800c0720020048050000000000805c0080110350004002000
  | 30 => 0x200700000000030000018003001800400a069003000400e00800480ec030001002803000800200000140000020058020002009003002c004000000000c00a001018004400000a00380100000120040038010001006003401c00c0058020008005004803000400200200040000000000014002009001003001600000100180000000048010002001001001400a000000002c05c00a00380040020060000028000094001800000000c005801000000000000000220000010004000002000801400000b000800400000000c00300100010000000034003001001c02e0010038008036004012000002c0000000004026010000802002a00700f8008020000000800c000002001001c01400b0008018000014001800001001b000800400404f001001400200c000800001000000000040000020018014020000003003800a034006003c006005002800000c0000060004016006003004400004900481240180010060010000000000000800601c0050018006001000001800e00c00200080000030248018010004000000400c00a000000c00204000080000340000008004020005000800800002800b8020030000001801c0000020050004010000003000000800500b800800e000001804000000200b801401000100680440000030058014016004004805400e003005000400a01b004000000000a00300fc000001001000801a000000001800002300080d4006003004800008a001008000402a001002016801e009001000c0040110120004008007006802802000000e0024006000000801000600a00b80000de003000000006a00b002001003c003000000000000000080040220150018004008006001006c00a00f00b8004000000000002001800a00000000040030000004000003006800402001a015801800800b0008000004003001802c0040330050034004000000007c00000e0000000002006018800000c01a005800c004003000000000e007001001400a003009800c0040000138050002001002009800c000000804412a039003001004a001005000000a0090128010008000007803001600100f802000c0230000000006001000000c00000000080240040010010038000000002000001c003009000000200f000004008a0020298004028001000004800200a001800801c001000801000000c00d800800001c000000000000900a8004022008015800400600c00100080a8000005000400000a00300000000000040000000003000001800a00d000800004800000080c000401900200280900120068000054002011806400c005004002800601000080140020170070010002000007000400000c00000080060000068040000000001002000000000380300000190110008008000009801400200000f8000004033003001000a003000000
  | 31 => 0x3a6638863a00000da1d088f87bc98aa4fb9c665b8160a6f78d9003d117632e981489e17b40009bc05e98cd287a152a4a4100047ea0a06d2138e5988c964d08a7e8120e9e0ef131c64a808074113704a78772800a3665068000000000010f800055000000000c2a931158658204245e413503d2941e558832687508b43a5970000003fc86880006e28d0200001de718800008202822b488bc59f03e842b93cc7dd804e53699e062500001b818623ee800033f09e82340bbe00000000000f024b1800068622ca000000027680007de0000000000000009e27d980000df8be600000000eaa2d40120000000058400014e212e1ca291a8b0006d9a7e00012ee05400007939c7a820238e747841c74ca48c1341620219825661497e827312ca05506448da91d4226843036719ca450984e1388a4a0aca21664c90fc975a0388be0f04520a21a1501c5c48c1c523ef03c61e311225550c921f49df21f11a7821f99843788d103b61b0e6a822fa823815295b03446ae0f5c1119f0c66d15241719f4a63d87561c6039c2839d3828f91a44df22fe28596f051d19da2221686954986e78585240481404156119893e8b24713a55025182e202a25c87b7224e39f874c4bc8dd28d085322c98b305198d4e8e6960606398c2840085c201059e0000c0297322c87e900004a810cc2d322545e190c066e1fbc3ee160c94881d80001e3a09d80002ee124a89e8f4200023b65311034372a5ae29691207c213543af917c2c8a45613b1af8466800053f17e635317a006b21ca9259086909862a2180dae5da081c21d0a6c0168bd04eb8a1c860a4928050050261a2027cb845400009440e00000921980448798ae00000006298ff480486ac3e3853e8fb1dc6956888a46f046437b00002fa03b465d1ea853a9c3251f8db090e15ea8fd92c2771180093b8f6451c8f9e67006321f280003c6932e0001ade000000090f922239c06c08bd04e610521d01a2028a177010e8a991ba09a0d9e6d086e4627a03c90c9d4c153256e7349a3e85e20ea136068c7d421d21d981301649a8494e1eb44370cfe4b30f9277ba22821e0c2c2e123c21bc001e89d82a03d1850218120900000c7c00010ca8ab000079b800053006b40248d744ca8f3e0000d7c000181a21a0ffc751000078616420001678943800008e0efe36f8000945000032a80004148a0c1ae968c3fb22868e700002f5800000014c88d10000000000095600003b720408ed0df412a15ec000221e000182c00012a60e914306ee93440001e9017219880001c086ef9df684217dc1c717ba3bf000070b94dc0000d5296197786de210a6560ae414a9a8c9071c061b59112000150c000034a34480cc6c117262fe0cee1a59c102b981fc0510a286d715e48da0bc607306a4545a51e37508ca8cd95a883c0026022000800001000
  | 32 => 0x8071e462439fc081080ae7d098088f90d2a36f235c2d088440521e526c203209278ce48b705487fb97ce5a918925f81df855c0c5e32f9bfa76701da09e9fa8557214417a13983891c3c97020f663a92fa0fd86c896d98021700bdc19822641af06b8338002423f8ef27bc113c6f30eb64188bea4fc25986301b604470bde6991c362eda2e45cc82c82490e2a3f595e26a69da63288ccc5bb8e1e830215a495886440122d853b11ca7bb9ea07b3858e7b98c061a093ac93a8a1a220145044f80000dc11322de11e86179d8e79080000000ddc2f680007990000000251c46f8d284b38ee650a9a327409b868a38abc33d0dd06a49a763ec184c0b0a59480109f613d0000191800000010967c68d1447309d48c405860ad977e18b823c26824304a2a4702ac06e66e020d868f038a52b8ac87191f880b1801889b9bb200009ea5f08d8c00004c4000000054881160001f567690a645db07541259a2a23c8000000093a00000000ba07f266f80006f7056a60e021c97600000000d668bca258665073c97520d645595b64771f9a6f5896849a8000510084e06f9220864991e00000007a780000001b2471b00007c582a43829ea6782964017c0f0e96c06dc29487f40a2186c3b425404f10c1084116a2888081e34903fa2888000000000024b84ba69a82960000be270a84dc3a999c800000e800c87c830f8000000252600000000001f2426217da0000e4e2d280b41e9a0c838c9bf827f0fe60c50e2800018e000000003b3800000023da00016b05c189aa2dc87aa0660000175000000011a6277800000000003ae00000a723a47aa800065799341ed9d4079204366f9879a0000000000000046804d20000000000027c000257e000144a81d12be6fa925000012b47af8b862bf0a84727003a52c24482bf809e2910d588551a4c01a1b665118d1e3619d0c24604427a199fa08f98be28da01e8c713861fa1a3a034116291e8a2c49b01ee64300002ca942620f0606440a5ac5fd23c09189010000004c1ba930e7fc01180920df815900007ba000000017e456600003551d9e0000c28000102e57c1dd00001a2c19309f02e323240000b7c4ff87fe78014926bc828646508240001e1487213d4093936c4ec0494031800036a9f624ce05ac01f0000593201a73200000000a802ef00000f42488000088c13e800000003f81fd85788d380003df8e2e0001dcc1061b2035c05d661c854e97690400000f240001a8a4b88c443c301dc6bf80005d28b9c6f9175409c05b220b1bac25c00001ef0cb0017018c3238af085a0b9e60f9a80605876480c8f6871f90bc04e1a348c18c8c3aa09ec0699ebc81991365c313e01738fe025414d200018f01f41a0a0ae9de879424a84309f0665fa47200013d6000150e20c9cac000194800000006f50ba84be1d364e29bae17f8
  | 33 => 0x98a247385f256522d25a983f21928be400000008e2827e2ec97c80ce17ea6a6119c06904827f81c720c621ac2d90000681990e320207c04c8dc42e4049c0001ed040620b2059059863f17c418205a423521e23120000110000074e9c2800007ee58c8c4a0d987ae2da9c7681500f858c25280b98a3023d1ee21e1038c6af15da1d39f106b91ba433d80005920ec86150000420800000014c207923b258880008de800006f000078ca3822128db6000134a0000498886000000012a287007743011ecc93e00006d4220c29d0cd664280002979a5c6571214122258c30ba27c51e844c2c586a805623ba8351a6074607b273f1cde7ec118633a8c0c1320b4e19b1d9029300f675d901e86b8fd41d01d8026c259c10d014e6ea8c227448ce24391cdc26316a0014841e3e615e843c02067340f2867b23e803b11c80b689e01c99730392952884d031c6531abe3171a901a518f855b97760d88f4e4450cc67ca80ac456957c7ab9f8c20089086aa07441a40b4400000000c400b80000000000150a00000004e20000000000001b8f2657b8010728017a0000cec368800095c1012286124465681ea8d2800018b136269f164a11f800024f1ab21d60c6a456000014e830000000000751c823e11464711a0ca000111e3941aec54b80000dea09408b060a04a000035ba3784f899c41421b4c00003b0000000029e00006ce0000457000081e83522f005ba00017520001a207870e22675108c3438d2e5771d2467d22502ab97800f500006d3904e8e79d3000000006f1955a8d18000000075286f18460eba1be8a5071647614484030b668f81de64c211744678ba63498ec03581b8c3b89ff446b847222180362a680003b8083831a1ec8883a39000015c41801ed237c1daa797a33c01b175000021f000025045b423fc35001b0914850c00000005d996f486c088e6a880006c7056c00000000f800005450dc00000e665c90c4c73aa418768800076d80003ff923400000008778900000000000020066a719ac5b791067cc943635ca2e282b889e2aea19800000000000000000066e00004686dd000000000000000e40000000076e000000004602a7a3bc77b00008e625dc294181c8770fbe431956a23613d09048d3496280003a3159e44c102480d9c1266c97407588000197000000000003ec80000001e765858ba21731e7c21c92c856aa158513230e593973e84595643d8108466600421df97be1381360186825870b1ffa5b10c64000017e000056e751800077384841c794b85ef109443a0c3409b00006fb018051699f64f493ce1c400007dd24d4434976a7439a468160d5680b159c35f82a2848a5e462e21fc92092e82a904508279910255889834714ca4ca1192264173430287a842d042e929930a6fa09c243d050e94901fe3b098362ca18e42579880
  | 34 => 0xc00009642e505a6000253a44a078a00010c800008626be80000ec934c32b0d3a19f010a667813c3659fdc9031d725dba5ba0ba83ca000035435200006318cf865119208d5017c6a5149c0ab17fa1418f3801a8000833954e388000007008ea000196c5a4821085f061e620800081d80007b100000000022000043c73f9e885919cf2000200e6258b8a3779d284b6153e97a07ce85e9dd637f1fa61bf20aa88d12ba79f9940645a5bc7700d9408a8af40001352072167a5e90a9000000000001cbe8f49d68892800049fa58400000001ed211e10812545e09b3e3cb0f9c114a3b8185914e95a06e87db876c3d5122682180006ae85f865517c656e164494408ee38e9e0e43415f26e4a28a92110f85360c203c424b44c91c1e4ad98a4000096e8ff976047881e0882a2b46cc2296529868691980000000000163214e00017e200016040000000000000052e83e600022f6244000001821481f79794000238c9011108000000065ca188508a40854121c289887965a508a87231f02497230419d9fc451f157204a800093d03f409003a2000000000000000f680bc000043a00022a8000179a38600006c5953487f80000000e7200001ae513800004882dc67a00000000d08334000000000006ab99ce7009aca72d1a2e59913b400000003b681e86218c52000000006c80005c29cfa36200001121fe8011800014d96287eca3c616f9c160c0800054e00007b293260000000000000000011900001708503a1420002120000000000009ca00022400f487f858f828e07e8ad66fb9ce449c826e49323f42ee9f0e230850449623ce0ffa2225b600000bf80003cb80008d9000077c1798644a0e21f6855289309b674f816c52d9cae00003a000008ac609903672e92981cf975620211fc0000be092d800000006480000f6c000000036b03ba5c68ecc8c9a4d852406da41c050a8ae1f120001b0211d9c920531d1623482ca2ff09540000d6c658154a1e39fc6093198c47900001f584a283904de2ae1ec042619f0000042692c048681c86681ce000087d1d08564153c7f6800080c249a55d069c7bfa11c7f4143411f223c28099e2217862405181e60001654779172c8c31ad274890a08dc82184c101a22408a0400021ec00020fc4201d84326021e40e922c030922e585000000025541c8108a7ca25420000d8400016be8dd167016224e060c800000015884351acc1ce8eae80a00002659d606d59ec632b8e984b680d27eb8a00252962e905128e8fe2556241a0ec406898a00025744c096ac02212944d2030418a00006aaa4440000c6e5c390fa00018f475d05d28e115d21bb8a106df22cc00000262a209c831998f200003127ab13da3f1841608c20ee6111ce690a188826e00000000aca000198674b979600018ac000000082680007d606661458f48564
  | 35 => 0x6859bf00000000000000091f800071a16e825f06928129b8277a835a4de1d7c82f16a846085567a502f286798b211680fa48108b01f81e567ac0efa46e20e88ce965e1fb1b646399e0865914f60e20e840fb827854800008c21cf865582cc00524c20ef8410463045808924ca486040a0e4953a563152c4d3a44c683090c10214c63691b1e0741d1a00011640000000371896c03b82f40000fdc0000000000083459580008cc800036601660cf068a30c840c4f1903e8a88610818a0e07089d581959066000034c60620961c882983e821945b9a0503f9193644300008fe9e1e7ff8000435800c00015de11e80005000f367b915c094c8d203ad0d8e78d00004e4259a13f1ad62098f2000003b800025b27fc80004c8800000003d65cf23d837922de48e9b6a73309c6979800000000dc4d92502000000000000008a1255e7a5865a39e9c7c14422106bc00002dd1a1e0568a061c1994200004c612c851e2c121623b59da086c8e9214b8000216180e3f692d062380000001be2000000091a1d825e2857003918c40000b3819883cc660978843b14d44050dc24c0095275c224631c84a01e810be3ed15063d8825c000142c5fe00001eb194a19915f800000009370c8801c8966241122863486705d790d87771cd853e00000da0c742c311b600000006bd98502448f6a45c921a50c926225e82c494b8d625aba5002571212452912a933032a765245405a8c9c16b91d637d87fc660080e70500b61f19c8402c103027400007368c7055310f20cb00002a30a609081faa1018e5474b02c060ba3ea45b0fb60cb8f506230724610927a5a41e4c4a09c501f095be76580862000fa603f000032812d40fc000085c19fc206082e1899eb640e25b461f044a66718d06c48de894d10764bd97365c51be05b919767bb0a2041700007b78000000235800005768a90000000197060f13101d780003de00004921fe693c838e5ae9f4675994ac3a420da0ae003083f89e63b108901b08c1e0ca00780bd8e345c4172a0e08000126800040a070200000000000000000000051b0c3c00000000000a7c00008c6910223000016da8bf14cc53782d6000000020300005de8000000000000017d0000000083300006e421308b9994e057230a5b31cbc7d68000000004060c000000024fe00000007e8a5c652a80006d00f5261e9e8a00004ae15d16744ae1b7618d8aaa93c1ab62a080f24b903221798a5415a06b00daa02216d800000000006cb87507d9087a5e7a21c1ec091e00001ca90f218a00000002f398cc814a1cc4fa9138000052630203e247b0b1c22580002ff91a801d00007d01438204a4900001f4c2b882ec749800000013169678e585ed8ada00016180951fd600015822790d7a07093f6474999a1178000615a312000127c62e80001d29b442b023d
  | 36 => 0xd030c23a04cd0ce61659ca82cb07be15f01f05fd80002381d5672c06d07ae8f660f0800048017441d71f3a0002092000033e7e7220670d000000021282fc8dfe710024614b0292000131a8d815d60001bfc78682004d180002f100005698b2000013e82e48984000048a0398000000166091706a200025c20001c96000000022e8000201861895380008ca863e8e50b0a3fa112e897904236280004da0000910884884b951875b9a267cd1596627163424fa42c000000032d055e00002ce60906504aca5a638f126811a9ea24a30cb635a055c00008946d18474290232000000006c61a7287d8654424918a73c1c600d4187655190e22700e426ca2582474000a6f29b9e79ca02e7060a7a9741ce05fc05fc50622b25dd18b44dca0a87d71a620b49d1c16d15321f904f02e587d40000acc2b39e7800012e06848f907780f8c68e0f9a78118684438000861923e4f0107a92f14a2658a56675480d8135080a8d417de4ea0c6285f8e8616a11e059f9fde5381c0e55a20a402f9b6c03010903aa80008c001120001f7a3dd90b65eaa35628a94bc489014a5c7071238f9fb437e9b0a579a4640000ac600018208e59e542d81eea500800000017b800019ae2e014b26ab16728f897ac0000000000000072993f88b6992e589000000015ac15c829482d8000000000020a157651c02f00001fc85f500e2000077041696ec3c181ec0001f7e6800aac0aa82ee3429ba695e9c985ea21ba3fa911a326a04e0320ef091b033047d00287e80186233a50829ca2420001332392058007109f26b3800074d133c6d880002c697020ac0000000092a38680002d78bd4904079096a12f091787e27090560710878695280000f70d3e73b19920c18fd881a15b43d68dd84150000356a4ec7e5800014f226c3180e7679986c65d894626868c36000000004e80008d310fe6bf08ae3be215e3339584000247c9789f4e82209260000ede000000000000000849f5e5d180002e61e1041820f2852987480815a226e99ee67495505df21ea3dc8cf2205107445411105a5a37637980006da000077482d400014766ee000079a129224524de01580340000000409a3222bd906871685aa5bc9566000216000023ae00008da788800000000007f600c42b800004a1a0dc52800000b60fd21550f882ba800011121c663f94860e58e5c4502392000038400000004d5968e6e8017885c80004ab9cd641600004d6000000016e281b082a43aa3de39a00007a38000000000069511f659d839047022560d8097e6a09b7091384788b12388067800039e1df42849a6c5c48f402b418d65d61e380c58a425cb885659a99905b014be4cf800023799c616f0e441232518042140a946899293f09c47e000007f38e06000000034898642da00002cc946e00024ac00013aa80d18ce1f6097800
  | 37 => 0x899e447df0e385f287786681c0000003b622808e639f09485740bb07ce22c608d203e3301704000216e2a888c053d10ee32c800006d0ebc81b987e5be876a025885a1e091da32089343069efc69c0ca68d797200001a3602680000000000000139a2d1a1a0000000000024d0000222e41ca4b292813a011c1d86231017624e1f045bd972890d0e60000162c405800078f15cc1a393a27bd8fa412a840e42706987b680008eb000079e90485a00ff00001b3600014fa58713e63e889a447115d400f8a0837c8000085800031b15ce3cc0a1e6c506b22d61e6289c0e2c912897687ba29082d146015f89287bd206a48707006838e4c04999f20049088000000080ea5063108c9e594a2f000009fa4980c180a022482f4a0c6062a1f250f9366436904c4071e284e08432337a4e25a7037466a088296f802e76290b212988a2133926421b07b843d94204029f2030e22d694800009571b2c0c7a11000000005eca2ea1a695a4025253642900006b8800032500001a004001139e4a2ce997865b8d00965a2aa02a959a45e0000000000000015b0000000057280003ac06147f3022e49d9530675a38013292f43cf000015980004d7800000013840001cf641f0cf047799023f3800091d205a3f298da5b2000019a955800007a400022723a21fba0019bc419792ac63b800092b98dc5f49ed601115123b924460e698a0395a1260000cd8000232823f11e62c0920274f145604784ea8af008c0001ba248a801c5ff1ee046002507e1000042aa26a3949a5e6db85300001ae84e49906693991c0001f1c17d079e32a18d8000000000024a40000fa82a705da25608e8000169816700008bb00003a81a243f20cc2046800000016b6879257695f1bb004f845c750949a46c12de46b06ca4a9059400000000ad00000000db200016020001ac43508e1c66a8e8236e80042fb227e09881340001b9a0000916757081a597000000000006ef1b546ad0dda2669dd40001ec200013740001ac626b000084180008449ef811b812e7ae0110400a4e401523aa82895f6000079890180009640000123a00878080000cd0000000091a0001b7a8a21ce226b9e2a78b94888968000000242a0001ed84cb1dba7898dce104a1ce2d7091c00007c08b4000000021a40001a48229000037b989000000004919ac8000000024d870a01784c00001da8781941434b24d63fea34883425ce00008426c6821a5b3825236988cc3bb035c87e1f1e763253c0000de051a1a107c882e439691f018807348ec11aa42a0b5271790a692506be5b594b4916a5a413c9cc078910e64279cc695c822606ea0244efa0984e518665ac943a3d59e802a60a6e0839f0017885f66fc8c76529162a933a40a2a38da078807766761b942b70d386b71a7a7e18b0600000004ac00006cc96aa3fc925a5ae0f
  | 38 => 0xd5078d85d80ce985a1b4919632199f862617725fb16dc642130c4f09e0c375980a6ed20e61cd96fe2fd168207d1f3e1df25784c4a3c8651a30297aa1768ac15603b50b6284f12323a2a3be87e81562d00b1088511441358000346a29c00023a84f7965814719fe46ca52c772116a5578c0e4f225484e91a563e003c088903ac5d21db48158e0c9430b3c522841a75e8a8610a82723dd112c546800051a95fa3b1830e7fb16b400003760020000777800088e800081e08220a6904a41a883e6e3902a4e7000006a1d9a58d80000e60000118800017e8000000179c1cb82645d7155672680006c880000c3104684ca3625f5a41675e1a6e4288aee00022324c80000461000072504ac583a5aa0328000267860e550a2e83eb80004b5800044d0a926a58bac48f16ca3ab110441f936e0380f7c8db145e1778490000246082292520000562256920e1be242288d913a2919c86130a43a64e136a0f7969e621000088017cc150810626c8f34140060c260000090005281780e0e0cca05c85a8f1218093e4309a58019498ca09780a03ea8d0657f12ec4cc000088b1c0a13b9f60907a31885414128c5035e5058038000207e00022604ba90de8a680988a0a3f000f1c884fb1a582e68ad867a9a28626a13e0df252a6f6a2803058b5607d87ea8f288104f2800034105b012c25b80ab97702ad998e0000c400000fc2088017091b822857f920c654800002c8e140cd8af255f916e2689fd279a81880000c467ef80002759cb234c8c2487600005230340640000042c015e9639966148020413311885fb88301f7219058ea2ae7fe007a1f30232129188a8bb8d925b198125841d2a073985c7a1256a02080f07310ed2000000021500000d18f0a6fd054a351938c15e9a222afa2ba0ea010c57611f84401caa4a00ade000237c2be08b600018c800000009069242851a00c78f9f9e0000f16295800000001c6419086e79817b04d00512000000014522e07768c5075384224c19428064236e000000078c0aa86911bf6000000008d800076fa5306e606c41ad9a521c68f6e21307f004000005409032162872a6079b3c6f0867a0c2937e433800069d0bd822c8f00000135a879937a00007320000e6a04700000669ae0470800000000008911e8200006a000000006a9800028285c2000000064e80000001dd8000000002299c209092882f082d059400000f6000036a00000000000690000060a00003989c388cb9a0812fa31623221b650f070e8d6812441b9f8e3918000027016e193889c33725de00000006499cf482092c084aa16c68c08460000b3693d8000000000000012703a68a6600001043668000146016005c80007cb1008000237e00017ae2cd25887cda1da00015ae61280000968a946b687a2000117a7e2a3d400024aa4aa96f888a8a961fe935c5
  | 39 => 0x6a901aa6161bd070ea32c716195084e10ac3f89b4a88e116000a8db402898a80000f180001d6c36e14e84038b7e5a29c9e29a90c485322c20000d76380940c2e393ba0c21b00694102201893f459688e46489f6883e0a7620d9e58190954478b0d5e73b9552442a0a60fa98e80001bfe8180b70208211a3f017844ff0a3867703ce13a097494584bc752a2ce035063027492fc60a8bae2d403562489d6a2358f867d516c26f617f226f1cb6865958e52a18065b4974c520173a64122928000634360963857098784ef0a140161b5a3ae88847f888ec000024428b859034c00001bd000000011544081c7466f15a03ba0b1e3a5000023712387621aee6ea24766b09314959000068082fa57d18d40a100005af00848119318078a33e25399a27fd94d000000003e58ef6000000077f25126a785347dc06f201c233800000002899822000193e1cc000076b124084e916680a861c3431f988438b3e22aa1a62be800051e00008c68ff623d8eb226384f671c000086a9b26267074645300000000b5a417800000000003f121c47da98fa0e506407ed89fe2c38c90000197c66c0000000229e1a78438507000092ea43656ca1146d60f5e8559c3e79b103c6a200160998f8a48289941e483481ca1e126b99e5a2e0a10231680002508b147f9092009a800095880006f2019c4a119288759c8a000000085910780000000000158089d05ca000000e0001eb206812fe17a870c2a8183404d9cd406e1d7e00000000648a8a45f80000379f0a0001cce26a1e9892e131e7c610ba860087c6c303865bf096a352800045a079c95186ce7520fac0000f143a89c563311ca47a300008af963c5c592d21848cda16886cc39d0f7a71b8bf072005c40a400004a59fac6490b0800002f851096d477fa13600015c83a38e262fb8b125150d5c4e58ca4894960085d19688f980000000eca0190ba08cd0f4c3c7201090904fe1c1248a0000f3a11595e09270000000000028f000073294840000c7853906fa0001dc253f800037aa09c000199621480765398e04535978e000250a84b19e647c80005f6086a00000001d20b7a000139e7648d3c1a114f22738c000c68492884863805d2478000151e000157a20599de6ba905688994f0687000000015106f38000754000024c929a2140c5475521b46d4835822f9f487e4004a00b1af4000118e000000000004e43bb800049e231e3979fb82bb0f086968d640000ef41bf8f825868998224a0f4401a28c2aca42e49991b4160978c5a6811481902224aa0c125148ab419c8b8863789b415185a03d102e07db014200822044e98000748000031e94ee000000028e828c80589f83c78dc8060a5d264c0f3228ca0b07a9036e1e020ac5c780000000aa6050248e8548c4e54222a03f7986a88f86581669c6a8fb8e6e8f420847010
  | 40 => 0x63b105079004660f20c1403582de19fa0183fe1f301d6a592897090a32118b02d507ba438133a7728f706ed86229399a421c219e43a71db231f9ad40e783727a685e43e5008e06520de54d8a5c2db22c01e52340082a4800000000953183a0001e5c86e0bcc7c98e6c00000007e092c486300004fc80004f61666426a3f2723a5ca07e1210850106c2100c5800000007e4a3cc0000000000051a00019ba07c848065a961e00000006b624980f11444000219c3f32166540191a9369e7000012067f500007451efa0000000000000071113b261c000000013808230000000148e00006e26f486ae000211889981682e90fee47a8a4e3848c3a6810dcc00005440001408000137686380008a60000468800000003e45718e6427d0a4856f18485ff980c01f9f522f2925e092829e00018bc86a2184384071410b0eea00000006999810730800003f80006741170000078828916120749b0670312365f0000076c00006ac000083487620000f582dd806629c1cb84460674360210c55b00900a99b965259f7261023704859c7832f1494673000027617926d78d780001458882207042e1124000114800007606cd240e849000083092dc2580ac47a4820c21d99b635a9f44857204415402029348b6e1278ac2000198a1008214000096213e000059b94066699dfa00015ba6b024e823e9b7e62d800014e15485d380003158a347151684260852293223c46a385ec0001a86708142e1aa992c2ba202659b05d0707067829602bc4af00000000000000000016e023a77887e6238800000000000001f94335175a8e986f67578cca0c91b881b797644110000930115e3ca836c38c0000298973820e800029a1a1486680004b9800071289a682e88b86180e081011b9c7a7124e05880008781f3c47ba2b67418cc832e1b3a71314984ee00000658d4404b03ec756877a24c102c075a4a249b8d364fe929c8e1a4c600006a647f86d88d480ea26f855a0de00000000000006933600004b600009dc7f080008cc0c1c2fe80002f20000817800000004da00000000001ffc0d3a560000200a3858d1874000004eda5c400000000001c4883119a483e9b1069a06d476f204c5091dae2d2087025c91465c889ee92f9d6452796ea2ed1d1012d1c1a24b0e362fd9c267fa876e5a21ce82b5046c10a00007b524028e8a4583a00cfa89a07684821d0a17b9668766151c34594ce445894c0af80a449d0baa517115296897a28f581841bb08a665e94107c511c63a9193c0bf00ba0409fca0d908f055e063c0299e745d0a5446dca45082e072c2c602606ca894082f99185c611260aa25a094fa5e04238b2e72402743c880ce5498342562991470c1b843800ce83229ad04f71a4a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe8c6390d4248001ad0ebb8284900035add4705092029c3e432eb9924009c5c635d732480b5ad040bae64901521fe1f65cc9200043ec3ecb9924000c5e75d8f32480018baebb1e649012f3318d748c92000697b2ae91924000d2c655d2324809795cc6ba4649012f2b18d748c92025e4631ae91924000d2f515d23248001a5aa2ba4649000363cc5748c920006c698ae91924005caf605d2324800bb56c0ba464900036a841748c920006d4882e91924009ace86d8e324800199cedb1c6490003635d3638c92000727b28c71924000e4c6518e3248001b1ae831c649011f361c3634c9202a6363b6ca9924054d6870d9532480a78d8ec32a649014f5a1c0654c92002476432e8992400c96c855d132480093d100ba2649011f331db634c92023ee4386c69924009ccc7618d3248001c9eca31a649013f721c0634c920024f543ee09924047dcb731c132480ab8d8e5b2aa0900126b21d42501200255643284a024005cac76509404811d6590aa128090003a318d4250120025d440284a02400087f855d930480070f90abb2609011e37e0d764c1202943f436ea9824060c5c63dd530480bb0fd0fb2a60901561f21f654c1200062fbaec69824000c5c75d8d30480a3998e5b1a60900123ba1b724c12000c3e42ee2b28400487c8754565080018eee2a8aca100122fa1f54590200061fbaea8b2040028ed82dcd640800917d0f20ac8100028fa1641590200051ec2c82b204000a9e83905640800153b0720ac8100122f21d41590200061fbaceab204005aae82dcd640800f55b05b9ac8100028fe1573590200051e42ae6b204000a3e851cd640800147b0a39ac8100028fa1671590200051ec2ce2b204000a9e839c5640800153b0738ac8100028fa1471590200051ec28e2b204000a9e831c5640800153b0638ac810016aba08715902003d56c10e2b204004aba801c5640800f5730038ac8102338bc83515902046716906a2b20408da3d85945640800153d0728ac810002a760e51590200071bc0aa2b20408de2f20545640811bc5a40a8ac8102328fa1451590200054f418a2b204000a9d831456408001c3ea398ac81000387547315902044f4790662b204089e8d20cc5640800147d0b18ac8100028f61631590204554ec1c62b204000aaf824c5640800b5590498ac810003a3e09315902045f4641262b204000e97814c56408001c3ea298ac8100038754531590204574790262b20408ae8d204c56408115d2e2098ac81022ba544131590200051f42862b204000a3d850c5640811353d0618ac8100122f21d645502000c6e41ee2b1840058ec825c563080091b90e98ac61000335dc53158c200070fa9ac9298400487c8759553080091b90eb1aa6100122fe1d6490c200245e426eca18400087f855d943080070f90abb286100122f21d6450c20
  | 1 => 0xd0e288c6900023761c5118d204852f428a231a4050ace82d04634800159b05a08c69002637a1e4118d200046ec3c8231a4000a5e8590463480014bb0b208c690003355c64118d200066ab8a8231a40098de8710463480011bb0e208c69000297a144118d200052ec288231a4050ace82104634800159b04208c69013eb6a004118d200056cc008231a40098de8788463480011bb0f108c69000297a162118d200052ec2c4231a4000a5e85d0063480014bb0ba00c690142b3a0b4018d2000566c168031a4000a5f8548063480014b90a900c69002637a1f1018d200046ec3e2031a4000a5e85c4063480014bb0b880c690003355c71018d2000567c122031a4050acc8244063480019aae2880c69000317d4e7694d2004c6e41aed29a4000a5d83d9653480ab8dce5b2ca69000e972176394d2002476432e529a4000c6f655ca53480093d100b94a69000a2fa127654d200045ec24eca9a40008df835d953480070f90a3b2a6900261fa1f6554d202ae36396caa9a4054c7870d9553480071bd0fb1aa690147331cb6354d2023e6c386c6a9a40048ee86dc9534800b1f50db82a6900021fe157690d2001c3e42aed21a40098dc835da43480091d90cb9486900127a2017290d2001c3f42eeca1a400087d85dd943480010ff0abb2869000e1f2157650d200046fc1aeca1a40008f7815d943480031e902bb286900263720c7650d200146f43ec6a1a4054c7870d95524809d1d90cb9c849000393d94639092000726328c72124050cce8718e424809d99b0e31c849013ba3a10639092027746c20c7212404eacf8118e424800159b0231c849000393d44639092000726a88c7212405387e86dd542480ffad041baa84901f21fa1f65509202a43e43ecaa124055e2c42d95424800b55d05b22849000317dd763509200062e3aec6a124051e8c42d8d42480018beea31a8490003171d4635092028746210c6a12400c96e87dd542480758d8edbaa84900eb8b19375509203e6363b0eaa12407ce2c641d5424811f2dd0fb2a84901531b1db655092000716326caa12405396c8719542480a78d8ec32a84900038b190655092001557436c8a1240059ac8755142480015590caa2849012f3318f735092025d67436c6a124047ccc76d8d4248001a98ebb1a8490003a3193635092027e663b0c6a124000d4c7518d4248001c9eca31a849000393194635092000747b20c6a124000e8c6418d424809799d0e31a849012f3361c635092000727ba8c6a124000e4c7518d4248097d1f0831a849012fa3210635092028667ba0c6a124050e8f7418d4248001d1ca831a8490003a3550635092025d67c08c6a124000acd8118d4248001c9ea231a849000393544635092000747a08c6a124000e8d4118d4248001d1e8031a84900166ba1e43509200055743486a12404b
  | 2 => 0xe41d8d200052f42c83b1a4000a5d8590763480011bd0e20ec6900023761c41d8d200052f42883b1a4000a5d8510763480a359d0420ec690002b360841d8d2023d6d40083b1a4000ad980107634808f1bd0f10ec6900023761e21d8d200052f42c43b1a4000a5d8588763480014bd0ba06c6900029761740d8d2028c6f43e21b1a40008dd87c4363480014bd0b886c6900029761710d8d200066bb8e21b1a4000cd77144363480138b8c6bacc690003179d76398d200062ebaec731a405487c86dd563480010fd0fb2ac6900021fa1c6558d200043ec0eeab1a4000c5f75dcd63480018b8ebb9ac6900021fe157158d2001c3e42ae2b1a40008bf845c5634800517908b8ac69000237e0d7158d2000477c12e2b1a400087e87d4563480070f90fa8ac6900021fa1d5158d200043e43aa2b1a40008de87cc563480018beeb98ac69024f171d73158d2000c6e43a62b1a4000c5f754c563481258b8ea98ac69000335dc53158d200046fc3ac631a4000a5f8558c63480014b90ab18c690002376067618d200062f3b6ca31a4000e4d82d9463480014bb03b28c6900023761e6518d200046fc3aca31a4000c5e7619463480014bb02328c6900023761e6418d200052f42cc831a4000a5d8599063480011bf0eb20c69000297e156418d200052e42ac831a4000ad78159063480015a902b20c69000393d957218d200072632ae431a404face86d48634809f79501a90c69000393d945218d20005c6c20a431a40008de86dc463480018becbb88c690003171977118d200062fb2ae231a4000c5c655c463480011bf0fb08c690003355c76118d200046ec3cc231a4000a5e8598463480014bb0b308c69000237e1d6118d200052fc2ac231a4000a5c85584634800153f08b08c690002a72116118d200046ec38c231a4000a5e8518463480014bb0a308c690002a7a106118d200054ec20c231a4000cd57118463480014bd0da88c6900029721b5118d200062f3b6a231a4000a5e8654463480014b90ca88c690003179d95118d20006aab8aa231a4000ace86c846348001b8ae3908c69013eb32192118d202856c4322031a4000dd1714406348001c3ea92a0c690142b3a0a5418d2000566c14a831a404fada8095063480015b3012a0c690142b3a085418d2000566c10a831a40098df815c463480139af02b88c69000335c857118d200066a10ae231a4090e4e72d446348121c9ae5a88c69024317dc75118d200062eb8ea231a40098de8794463480011bb0f288c690246976165118d200066ab8ca231a4000acf8254463480a159904a88c690003355c55118d2000727c12a231a4000e4c825446348123c9ce4a88c690247935c95118d200072bc0aa231a4091c5f715446348123cace2a88c690003175c55118d2048f2ab8aa231a4000c557154463480131b
  | 3 => 0x2b224000c7785dc564480018e90bb8ac89000335e0f71591200066a41ee2b22400087f855c564480070f90ab8ac8900022fe1171591200046fc1ae2b2240098dc835c564480011ed0e38ac8900031ddd471591200063a3a8e2b224000cb7741c564480019aee638ac890003351cc71591200043f43ea2b22400387c87d4564480018bee7a8ac890243171cf51591200063bb8ea2b224001c7471d4564480010fd0ea8ac8900021f21d51591200062fb9aa2b224091c5c7354564480018eee2a8ac8900071d1c5515912000c5e43a82b224001cb47150564480011bd0f98ac8900263721f31591200062fbae62b224093c5c75cc564480019aee398ac890007351c731591200046f43a62b2240008dc874c564480018beea98ac89024b171d531591200066bb8a62b224001cd4714c564480039c8e390ac8900063b21d215912000e7238a42b224001cf07184164480031f10e882c890003b44c5105912004c6f41eecaa240008dd83dd954480010ff0abb2a89000237e0d765512004c6e41aecaa240008f7815d954480031e902bb2a89000a1fa1f65551202ae36396caaa240048ee86dc954480093d501b92a890003175d753d8d200052f42887b1a4000a5d8510f63480014bd0b18ec6900029761631d8d2000c6fc3a63b1a4000cd5714c763480014bd0a18ec6900029761431d8d2000726c16cbb1a4000a5d81d9763480014bb0232ec69000297a1664d8d200052ec2cc9b1a4000a5f8559363480014b90ab26c690002b5e0564d8d200056a40ac9b1a4047ace86d4b6348001c9ecba96c69011ef2a0352d8d2000727b28a5b1a4000b8d8414b63480018becbb8ec6900031719771d8d200062fb2ae3b1a4000c5c655c763480019aae3b0ec69000297a1661d8d200052ec2cc3b1a4000a5f8558763480014b90ab0ec690002a7e1161d8d200054e422c3b1a4000a5e8518763480014bb0a30ec690002a7a1061d8d200054ec20c3b1a4000cd57118763480014bd0da8ec6900029721b51d8d200052f432a3b1a4000a5c86547634808f5990c90ec690003b118521d8d2028d6c43221b1a4000dd371443634800153d09baec690002a761375d8d2023d66c16ebb1a4051ad980dd763480018baea3aec69000297a1674d8d200052ec2ce9b1a4051ace821d3634808f59b043a6c69000387d5254d8d200052fc2ae5b1a4000a5c855cb63480014bd0b38ec6900029761671d8d200066bc0ae3b1a4000a5e851c763480014bb0a38ec690002a7a1071d8d200054ec20e3b1a4051ace821c7634808f59b0438ec69011eb6a0071d8d2028d6cc00e3b1a4000c5f71d4763480018bae3a8ec69000237a1e51d8d200046ec3ca3b1a4000e578154763480018bee2a8ec690003175c551d8d200046f438a3b1a40008dd8714763480011bd0f20ec6900023761
  | 4 => 0x5480a94db05b9eca901569e60373d95200062eb98e7b2a4054a6d821cf65480ab4dd05a1eca900029b60b43d95200043f43887b2a400087d8710f65480a78df0eb96ca901578b90b42d95202ad37416e3b2a4054a6d82dc765480018dae5b8eca900031ba0b71d952000636c16e3b2a4000a5e839c765480014bb0738eca900031b5c971d95200063bc0ae3b2a4000a3e841c7654800147b0838eca9000297a0c71d95200052ec18e3b2a4055a6e821c765480a94db0438eca901529ea0071d95202ad3cc00e3b2a400087e8790765480010fb0f20eca9000297a0e41d95200052ec1c83b2a400087e8710765480010fb0e20eca9000297a0c41d95200052ec1883b2a4055a6e8210765480014db0420eca901529ea0041d95200053cc0083b2a4095e4e72cc76548001c9ae598eca9000317dc731d95200062eb8e63b2a400087e878c765480010fb0f18eca90253939c931d952000726b9263b2a4000e57814c765480018bee298eca90003175c531d95200043f43863b2a400087d870c765480a90fd0f10eca900021f61e21d95200052f41c43b2a4000a5d8388765480ab0fd0fa06ca900021f61f40d95202ac3f43e21b2a400087d87c4365480014bd07886ca900029760f10d95200072a98e21b2a4000e553144365480018b8cbb9aca9000317194735952004c6f43ee6b2a4000c5f75dcd65480011bb03b9aca9000317d4773595200062fba8e6b2a400087f855c5654800117f08b8aca9000a2f21171595200046fc1ae2b2a40098dc835c565480030f90ea8aca9000317dcd515952048e2e39aa2b2a4000c777154565480011bd0f98aca900263721f31595200046f43a62b2a40008dc874c565480ab8dd053b0ca901531b60a76195200043ec0cec32a4000a5e8399065480014bb07320ca900021fe1f61195200063ab8ec232a400087d8798465480014bd07308ca900029760e61195200043fc3ac232a4000a3f84584654800147908b08ca9000297e0d61195200052e41ac232a400387e8718465480010fb0e308ca900028fa1061195200051ec20c232a4000a5e8318465480014bb06308ca900031d5c461195200052f4366232a4000c5e76cc465480014b90c988ca90003179d93119520006aab8a6232a4053a6c8648465480a54f10c880ca90003d44c5101952002c76412e7b224000ed13144364480010fd0fb2ac8900031d1c765591200043f438cab224000c747119564480018becbb9ac8900031719773591200062fb28e6b224000c5c651cd64480018eecbb8ac8900031d197715912001c3f43eeab22400087d81dd564480131bd0fb9ac89000317dd773591200062e3aee6b2240008dd81dcd64480018beea39ac890003171d4735912000c7b43ee2b224000c7775dc564480018e8ebb8ac89000335dcf71591200066a39ee
  | 5 => 0x8172b5e0d725843004d6a41ae4b086000a76851c9610c0014eb0a392c218002ada1072584300055ac20e4b086009ad6831c9610c0275ab06392c218012bca00725843009d78c00e4b086009ad683d49610c0015ab07a92c218012bca02525843000578c04a4b086000ad783549610c0135a906a92c218002ada1052584300055ac20a4b086009ad683d09610c0015ab07a12c21813bb10ca42584300053bc2a84b086000a7485509610c0015af06a12c218026b520d425843025f6219284b086000ea542109610c0b95af0f192c218002b561e32584300072b3ac64b086000e55758c9610c001d2d09192c218003a5612325843004d6b41464b086009ec6828c9610c08f5af01192c21811eb5602325843023f6390464b086047ec5208c9610c00117f08b8acb9000a2f211715972002476412e2b2e400187c8754565c811b8d8e4a8acb900031ddc5515972044e6639662b2e408accc724c565c80031790ea0ac99000335dc5315932000e6a38a62b2640048ec825d954c800b0f90eb2aa9900162f21d645532002e56392c8aa640018dc874c563c80019aee298ac7900161fe1d6594f200052fc1acb29e400987d85dd953c80091d904bb2a7900162fe1d6490f2002e57392c921e40048ee82dd943c80fb2dd0fbaa85901ff8b1937550b203ef16320eaa1640059ac8755142c800b5590caa2859012e3b61b7350b2002d5743486a16401296c855d132c800b958e4b2281900126b21d425032002e563b284a064096b2c8550940c808f1bf0eb1e61900121fa1e54596200061fba4a8b2c400487c8754565880018eee2a8acb100122fa1f54592200061fbaea8b2440048bc875056488001da262882c9100022fe117158e200145e422e2b1c40048dc874c563880019aee298ac7100123e2017654e200243e43acaa9c40048bc875914388001878eab22851013e37e1d63cca200061eba4a9b2a4000a6d8295365480014f3012a6ca900123b60b71d95200052f41ca3b2a4000a5d8394765480030ff0ea8eca900029be0951d952046e36b92a3b2a4000c7571547654811399ae598eca9022b335c931d95200052f41cc9b2a4000a5d8399365480a78dcecb96ca90152da20172d95200063ab8ec3b2a4000a5e8398765480014bb0730eca900028fe1161d95200051e422c3b2a4000a5f8358765480014b906b0eca900321f61c61d95200051f420c3b2a4000a3d8418765480014bd0630eca900029760c61d95200063ab88c3b2a4000a5e86cc765481278bced98eca900029721931d95204962f3b263b2a4054a6c864876548001cc8c290eca901569e21910d95200073830a21b2a4000f513144365480a94db05ba6ca900030f5d074d95202ad37410e9b2a4054a6d821d365480a94f5003a6ca901569e60074d95200051f426e7b2a4000a3d84dcf6
  | 6 => 0x566c1ceab106009acc835d5620c00155d083aac418002ab61075588302766639ee8b106009ace839d1620c00159b073a2c4180029be1574588300053642ae8b106009acc835d1620c00195ae83a2c4180038bd52545883002575404a8b106000ae980951620c01359907b8ac4180029ba16715883000536c2ce2b106009ace839c5620c00159b0738ac418002b3e0d715883004d6641ae2b106000a6e851c5620c0014db0a38ac418002aba10715883000556c20e2b106009ace831c5620c00159b0638ac418012baa00715883000574c00e2b106090e4f31d45620c11b4db0b28ac418026b3a0e515883000566c1ca2b106000e6781545620c123c9e62a8ac4182329ba14515883004d67418a2b106000acd83145620c0014dd0b20ac4180029b616415883004d6741c82b106000acd83905620c0011dd0e20ac4180023b61c41588300053742882b106000a6d85105620c01359d0620ac418002b360c41588300257540082b106000ae980105620c0015990e98ac418026b3e05315883004f63c0a62b106000e4f514c5620c001c9aa298ac41822bb1c4131588304576288262b106004c7a70596520c009974e0b24a4180031e59570948300065cb22e12906005cea625c2520c0090f90bbb2a4180031759773548300247643ac4a906000ccf73589520c0091db04bb4841800e1f21776508300245e426eca1060048ec82dd9420c00195885bb284180021fe15765083001c3e42aeca106000cac425d9420c0010fb0dbaa84180eb0f99375508303fe37316eaa106000c7661dd5420c0010fd0eb2a84180021f21d655083000716212caa106000c3f75591420c001878eab228418016ab20964508300064eb26e6a1060048ec87589420c0018deeab1284180031b1d5625083001556422c4a106000ccf73589420c0a1d1ce8b146418143a35d1628c83028667b8ac51906000ccd7158a320c001c9ea2b14641800393545628c83004d6b41eeab086013ad583dd5610c11b4eb0f3aac218243959ce75584300072ab9ceab086090e54329d5610c119cae613aac218233954c275584304bd79c02eab086004af0805d5610c0018ef0ebaac218247959cd75584300072ab9aeab086091e54325d5610c001ce700baac2182379c201755843046f2b982eab08608de55305d5610c1194ed0a3aac218026b5a0c755843009d6ac18eab086000a7685dd1610c0014eb0bba2c218026b5a0f745843009d6ac1ee8b086000a76851d1610c0014eb0a3a2c218026b5a0c745843009d6ac18e8b086000ae6821d1610c0015cb043a2c218012bca00745843009d78c00e8b086000e3754951610c0095e5012a2c218002bc60254584300056bc1aa8b086009ad483551610c0014ed0bb92c2180029d617725843004d6b41ee4b086013ad583dc9610c0135a907392c21
  | 7 => 0x7e871c5650c0134bd0638aca180569760c71594300043f43c82b28600087d87905650c0134bd0720aca180029760e41594300043f43882b28600087d87105650c0134bd0620aca180029760c41594300053741082b286000a6d82105650c0094f50020aca180029e600415943004d2fc0a62b286009e57814c5650c0018bee298aca18003175c531594304572b88262b28608ae55104c5650c0010fd0f10aca180021f61e215943004d2f41c42b286000a5d83885650c0010fd0e10aca180021f61c21594300051f42042b286000a3d84085650c0134bd0610aca180029760c21594300253d40042b286000a7980085650c00917d0faa2c8180030fdd754590300245f43c82b206000a3e85905640c00147b0b20ac818026a7a0e41590300245e43a82b206000c3f759d5640c01353906baac8180028fe1572590300051e42ae4b206009a9c835c9640c00195ae4392c818026a7a0f52590300054ec1ea4b2060008be87149640c00117b0e292c8180028fa1671590300051ec2ce2b206009a9e839c5640c00153b0738ac8180028fa1471590300051ec28e2b206009a9e831c5640c02953b0638ac818002aba08715903000556c10e2b206004aba801c5640c0295730038ac81824387cc7515903046d1ec2ca2b206009a9e83945640c00153b0728ac8180038de05515903048f0f98aa2b20608ca3e85145640c01353d0628ac818002a760c515903004d4fc0a62b206009e97814c5640c001c3ea298ac8180038754531590304574b88262b20608ae95104c5640c00147d0b10ac8180028f616215903004d4f41c42b206000a9d83885640c00117d0e10ac8180022f61c21590300051f42842b206000a3d85085640c01353d0610ac818002a760c21590300255d40042b206000ab980085640c0131b906bb2a8180121f21d65550300245e43ac8aa06000c5d65dcd540c00193ac9b9aa8180038bd5254988304872798ea3310608da6d85946620c01359d0728cc418002b360e519883000733c0aa33106091e4f31546620c1194dd0a28cc418026b3a0c519883000566c18a33106000a6e85906620c0014db0b20cc418026b3a0e419883000566c1c8331060058ee87106620c0011db0e20cc4180029ba14419883000536c28833106009ace83106620c00159b0620cc418012baa00419883000574c00833106009acf814c6620c013d8f0298cc41800393d45319883000726a8a63310608aec7104c6620c115d8a2098cc418026b3a0f525883000557420a4b106000aad84149620c0131b906b8ac4181423721d31588300247743c42b106000a6e85885620c0014db0b10ac418026b3a0e21588300247643a42b106000a6e85085620c0014db0a10ac418002aba10215883000556c2042b106009ace83085620c0095d50010ac418026b3a0e75588300
  | 8 => 0xe10eca980028fa1021d95300051ec2043b2a6060a5e83087654c0014bb0610eca9817e9ea0021d95300053cc0043b2a605fc78705c3654c0c10fd0fa06ca980021f61f40d95303043f43e21b2a600087d87c43654c0c14bd07886ca980029760f10d95300072a98e21b2a6000e5531443654c0010ff0ab8aca980022fe1171595300145e422e2b2a60008ef825c5654c00b1d904b8aca980023ee01715953000c3e43aa2b2a6000c7771545654c0031b90e98aca9800335dc531595300043ec0cec32a6000a6e82990654c0014db05320ca980029e60264195300043fc3ec232a6000c7571d84654c0010fb0f308ca980029760e61195300043fc3ac232a6000a3f84584654c00147908b08ca980029be09611953000536412c232a6000a7b80584654c0070fd0e308ca980021f61c61195302ed2f418c232a6000c7571184654c0c18bced988ca9817a9721931195300062f3b26232a6000e57614c4654c0010fd0fb2ac8980021fa1c655913001c3f43eeab22600087d81dd5644c0018b8ebb9ac8980021fe15715913001c3e42ae2b2260008bf845c5644c0011df04b8ac8980163b20971591300043f43ea2b22600387c87d45644c0010fd0ea8ac8980021f21d51591300062fbae62b226093c5c75cc5644c0031b90e98ac89800317dd531591304962e3aa62b226000cd7714c5644c0010ff0abb2a89800237e0d76551300143f43ecaaa2605fc7870d95534c00155b0810ec498002b360c21d893000574c0043b126000c3e74d96624c00187ce832cc4980030fd9574989300061e32ae93126005cac625d2624c00195ae9b14c49817e1f21b75589300043f43ecab12600087e87195624c0011df0eb10c49800e1f21476549300043fc2aed212600387c855da424c00b1d904bb4849800e1fa1776509300043ec2eeca12600387e859d9424c0010fb0b3b2849800e1f21476509300043f436eaa12600087e87d95424c0010f90fb2a84980038b10b655093002d57416c8a1260028ee87d89424c00555d09b1284980030f9d3658c9300061fb2ae91926000c3c655d2324c00b958c4ba464980032b5d3628c9300063c32ae11926005ce8625c2324c0c18b8e7b2aa09800317d9773541300062e32ee6a02600487e87951650c00187ee92a2ca180031dd4571594300247c402e2b28600487e87945650c0134bd0728aca180121f21d51594300063bb8aa2b286000c3f749d1650c0094f5013a2ca180029e602745943004d2e41ae8b286004a7a809c9650c0134b906b92ca180028fa1072594300051ec20e4b286009a5e83d09650c0014bb07a12ca1824317cc7715943046c3ec3ce2b286009a5e839c5650c0014bb0738aca180029ee0171594300253c402e2b286000c77815c5650c1238be62b8aca180031ee01715943046e3c402e2b28608c8
  | 9 => 0x75509403ff16316eaa12807dc3c761d542500fbc58c43aa84a00830f1d7655094002c5e43acaa12804ba9c83595425000b55904b2a84a012f2718f735094002d57436c4a128000d3875dc14250001a76ea38284a000a6be1d42cc940006573b28599280058bc849da3250097938c6ba464a00122f219744c9401049e42ae899280049b8805d132500010ff0abb064a000e1f215760c94004e4e31ae81928005cac765083250097d18c6a1064a00163e219700c94004e6c31ae01928000da9425c0325000187ecbba2a0a00022fe1171597300145e422e2b2e60008ef825c565cc00b1d904b8acb980061f21d51597300063bb8aa2b2e6000a7b8054565cc0019aee298acb9800335dc5315933004c3e43acaaa66000cd7714c562cc0018f2cab84a5980163b2097690b3002c5ec26eca1660028ed82dd942cc0010ff0abb2859800e1f2157650b300243e43aa2b2c6000c7771545658c00917d0faa2c9180030fdd754592300245e43a82b24600287d85dd9548c0070fd0fbaac5181531b60b7558a300043ec0eeab146000acd83d49628c0018deea292c518002ab6105258a300043fc2ae2b14600387c855c5628c00117f08b8ac51800a2f2117158a300043f43ea2b14600387c87d45628c0010fd0ea8ac5180021f21d5158a3028c6f43e62b146000c5f75cc5628c1278b8eb98ac51800317dd53158a304962e3aa62b1460048ec87485628c0010ff0abb4851800e1f2157690a300043fc2aeca14600387c855d9428c0011ef02bb285180063d2057650a300061e3aac8a146005aac82591428c0091d90eb1285180031b1d56250a3001556422c4a146005cae625d2328c0a3b1864ba465180032b5d1628ca3002674382c49946000c3d74953654c0014bb0728eca980061fe1d51d95300063ab8aa3b2a6000a6e82993654c0014db05326ca980031d5c761d95300051fc22c3b2a6000a3c84587654c0014df04b0eca980029b20961d95300c43ec38c3b2a6000c7571187654c0bf4b90c98eca9824b179d931d95300072bb0a63b2a6000e54614c7654c00187ae83a6ca9817f171cd73d95300053741687b2a6000a6d82d0f654c00147d09396ca980028f61272d95303052f41ce3b2a6000a5d839c7654c0018ef02b8eca9818297a0c71d95302fd2ec18e3b2a600087e87907654c0010fb0f20eca9818297a0e41d95300052ec1c83b2a600087e87107654c0010fb0e20eca9818297a0c41d95300052ec1883b2a6000a6e82107654c0014db0420eca9817e9ea0041d95300053cc0083b2a6000c5f71cc7654c0018bae398eca9817e1fa1e31d95300043ec3c63b2a6060e54314c7654c0c1caf0298eca9800317dc531d95300062eb8a63b2a600087e87887654c0010fb0f10eca9818297a0e21d95300052ec1c43b2a600087e87087654c0010fb
  | 10 => 0xb14a00ca6e8590562940014db0b20ac528002b3a0e4158a5000566c1c82b14a0008ee8710562940011db0e20ac5280329ba144158a5000536c2882b14a000ace83105629400159b0620ac528012baa004158a5000574c0082b14a095e4c75cc5629412bc9ea398ac528003935473158a500653742c62b14a000a6d858c56294129c98ea98ac528003b1e053158a504a727a8a62b14a000e4d514c56294115d8e2098ac52822bb14413158a500653742862b14a000a6d850c5629407587cc8ba4a5280122f2137650a5000656216eca14a000cac425d9429407587cc9baa85281ff1b98b7550a500061fbaac8a14a020c3c75591429400b55904b22852800e4f21d5450a500151fc32a8a14a000c3f7655142940ab65904aa285280123b21d6250a50066363aac4a14a002aac84589429400187cc8bae652816b1b98975cca501061f3aac9994a000c3d7559332940198dceab1665280031b5d562cca500145f422ed194a005c6e625d6329400117f0cba465280172b989748ca500045fc3ac9194a0008bd87592329400195ce8b1465280032b5d1628ca5002476416ec994a000c3e64dd532940198d8eab1265280123b609760ca500265d382c8194a003978855c03294001972c8b8065280173a989700ca5000e6b38a63b22a000cd5714c764540c18beca39ac8a8002b3a0b43d8d500052ec2887b1aa0018df874c763540039ace298ec6a8003355c531d8d500046fc3ac631aa055c3f655d062540011df0eb10c4a800e1f214765095004c3e42ced992a000c9e74d8e325400b1f10cb8064a80121f21d51596400063bb8aa2b2c800387e85dc963900010fb0bb92c7200023be097158e4002c76412e2b1c80048dc874c563900019aee298ac7200123e2017654e4000556c20a4b1480048ec87485629000155f0890ac520003b44c51058a400263d382cb2948005cae625d2329000195ae8b1465200122f61371d954000c3fc3aa3b2a8000a3f84547655011b87ae8a8ecaa00031d5c551d954044e4eba663b2a8099e1f54cc7655011593ae898ecaa026387d5131d95400062e328e6b2a80008dd81dcd65500018bea3b9acaa000317dd473595400046fc1ae2b2a80098dc835c565500011df04b8acaa00163b209715954000c3e43aa2b2a8000c5f7354565501238b8e6a8acaa00031ddc551595400046f43e62b2a80098dc87cc565500011bd0e98acaa00023721d31595400062ebaea7b1a800087f855cb63500070f90ab96c6a000637e1d31d8d400066ab8a63b1a80008df8758c63500014b90ab18c6a00029760f6594d400061fb2ae929a80058ee829d953500011db053b2a6a00261f21d6554d4004d2e41acaa9a80028fa86dc15350001da262886c4a00023be1d62189400061fb2ae929280058f8865c252500f927d0fbaa84a01ff0f1db
  | 11 => 0x9404d47d0a39ac9280028f61473592500051fc2ae4b24a000cad721c9649404147d0b38ac9280028f61671592500054f41ce2b24a000a9d839c5649404d47d0a38ac9280028f61471592500054f418e2b24a000a9d831c5649400155d0438ac928002ab60871592500255d400e2b24a026ab9801c5649411947f02a8ac9280838de0551592504cf0fa8e62b24a000e1d51cc5649404147d0b18ac9280028f61631592500074bc0a62b24a098e1f514c56494001c3aa298ac92822ba5c4131592504574a88262b24a020a3e850c5649400147b0a18ac9280828fa1621592500051ec2c42b24a000a9e83885649400153b0710ac9280022fa1c21592500045ec3842b24a020a3e85085649400147b0a10ac928002a7a0c21592500054ec1842b24a004aba8008564940015730010ac9281b74edd370552500246e43a62b1ca000a5f854c563940019aee298ac72818297e1d6394e502f62fc3ac729ca000a5f8158e53940014bb02b1ca72818317dc56394e500062eb8ac729ca05f97b865c253940bb8f70cb84a72817f4e9917094e502fe9cb22e129ca05fd6a625c253940bfad2c4b84a72818356cc57094e50006ac98ae129ca00097980dd5439400187eeab2287280830f1d56450e5002c7743e87314a0008ed87d0e62940014df0aa1cc52804a9b2154398a500953742887314a000a6d8510e62941194df02a8cc52804b99e055198a500953742c83314a000a6d85906629400159d0720cc528002b360e4198a5002c7743883314a0008ed8710662940254dd0a20cc5280029b6144198a500056741883314a000acd8310662940095d50020cc528002ba6004198a504df27a8e63314a000e4d51cc662940254dd0b18cc5280029b6163198a5000763c0a63314a09ae4f514c66294001c9aa298cc52822bb1c413198a504576288263314a012a6e850c662940014db0a18cc52800a2fa137358a500045ec26e6b14a000a6d85d0962940ab4d904a8ac5280029b6162158a500056741c42b14a000acd8388562940091d90e90ac5280029b6142158a500055742042b14a000aad84085629400159d0610ac528002b360c2158a500257540042b14a00ca6e859d162940014db0b3a2c528002b3a0e7458a5000566c1ce8b14a000a6f855d1629400195ae83a2c528002aba137358a5000556c26e6b14a000a6d859cd62940014df0ab9ac5280023ba1f4358a5000476c3e86b14a00ca6e8510d62940014db0a21ac5281569b2177158a500653742ce2b14a000a6d859c5629400159d0738ac528002b360e7158a5000537c2ae2b14a00ca6c855c562940194dd0a38ac5280029b6147158a5000557420e2b14a000aad841c5629400159d0638ac528002b360c7158a5002575400e2b14a000ae9801c562940014d90ea8ac5282329be055158a5006733c0aa2
  | 12 => 0x38de0551592324f717902a2b24649da3e85145648c89753d0628ac919002a760c51592320070fa8e62b246400e1d51cc5648c939d1e4198ac9190028fa1631592320051ec2c62b24648ba9d838c5648c80b55d0518ac919002ab60a315923200557c1262b246405aac824c5648c917d186498ac919003a3e09315923245f4641262b24649ca9f814c5648c897d2f0298ac91900387d4531592320070ea8a62b24648be8f204c5648c80147d0bb82c9190028f61770592320051f42ce0b246400a3d859c1648c80b55d05382c919002a7e0d705923202d57410e0b24642eaad821c1648c80b55d04282c919002ab60850592320051f42e20b246400a3d85c41648c89753d07882c919002a760f10592320074a98e20b246405aae82841648c80155b05082c919003a54c510592320045f43820b2464008bd87041648c80147d0a082c9190028f614105923225d4f41820b246400a9d83041648c80b55d04082c919002ab608105923202c5e43ac8aa46405cac72591538c80195ac9b92a7190172b1c96450e3225c76c36e4a1c6400cad64dc9438c80517d09baac1190022f613755823223c6f43e62b046400cd5714c5608c8015b307a82c1190063e21d10582320076898a20b046400c3d74953654c8030ff0ea8eca990031d5c551d95320045fc22e2b2a64028bc845c5654c8011df04b8aca990023ee0171595320247c402e2b2a640187c87545654c8018eee2a8aca990063721d31595320066bb8a62b2a640087f855c3644c8070f90ab86c89900e1fa1f75591320043ec0eeab22640087f855c5644c8070f90ab8ac8990023ee0171591320247c402e2b22640087e87d45644c8070f90fa8ac8990021fa1d51591320043e43aa2b226400c5f75cc5644c9278b8eb98ac8990063721d31591320062fbaa62b226492c5c754c5644c8019aee298ac899007351c531591320043fc2aecaa26400c5f65dcd524c8019aee298ec0990023ee1d60181320045fc22e2b2864028bc845c5650c80b1d904b8aca190061f21d51594320063bb8aa2b2864018bc87505640c8019aee298ac8190161f21d655503202c5e43ac8aa0647fe2c64dd5420c8fbc58c83aa8419016ab219545083201c3f43eeab006460c5c73dd5600c8ab8dd05baac0190031b60b75580320043ec0eeab006460c5f31dd5600c8bb8b8e63aac01900b2b1d142580320043fc2ae2b00640387c855c5600c80117f08b8ac01900a2f21171580320043f43ea2b00640387c87d45600c8010fd0ea8ac0190021f21d515803227c6e43a62b006400c5f754c5600c9258b8ea98ac0190063e21d10580320076898a20b0064058ee82dcd64940011db05b9ac9280028f61641592500054f41c82b24a000a9d8390564940091790ea0ac928002aba0b735925000556c16e6b24a000a3f855cd64
  | 13 => 0x63a38ecab02840087e871956050943c588432ac0a10031d1c465581420062fb2ee6b028400c5c65dcd6050801b1885b9ac0a100317d9473581420062e328e6b028400d8c421cd60508018eecbb8ac0a10031d1977158142006d2216e2b02847cc3e7419460508011f70eb00c0a10261fa1e54597320061fba4a8b2e6400a6d8295165cc8130fd0f28acb9902697a0e515973200c3e43aa2b2e6400a6f8254565cc8018eee2a8acb990030fdd274597322d537414e8b2e6400a6d829d165cc8014f5013a2cb990029e602745973204d2f41e84b2e6400a5d83d0965cc9218be63b8acb992461f61e715973204d2f41ce2b2e6400a5d839c565cc8014df04b8acb9916a9b209715973200637c12e2b2e6400c6c825c565cc8018ef02b8acb9924717cc571597324843f438e2b2e6409a5e831c565cc8654bb0638acb990021fa1e41597320043ec3c82b2e6409a5e8390565cc8014bb0720acb990021fa1c41597320043ec3882b2e6409a5e8310565cc8014bb0620acb9916a9ba08415973200536c1082b2e6400a7a8010565cc8014f30020acb9902697e05315973204f2bc0a62b2e6400c5f714c565cc8018bae298acb990021fa1e21597320043ec3c42b2e6409a5e8388565cc8014bb0710acb990028fa1270597320051ec24e0b2e6400a6d829c165cc8010fd0fa02cb990021f61f40597322d53741080b2e6400a6d8210165cc8010fd0f882cb990021f61f105973204d2f41e20b2e6400a5d83c4165cc801caa63882cb99003954c510597320043f43820b2e640087d8704165cc80147d08082cb990028f610105973204d2f41820b2e6400a5d8304165cc8b54dd04082cb990029b608105973204c5f43c82b26640387e85dc164cc8010fb0bb82c9990261f21d65553320062eb2ee6a96640087d86dd542cc8750fd0eb2a85991f21f21d6550b322d716212caa16643ac6f76dd542cc875c5cc9baa85991f31bdd87550b323e717320eaa166400aaf8655142cc801a9eebb9a859900b2b9d1425833200c3e43aa2b2c6400c7771545658c80b17d0faa2c9190030fdd7545923202c5f43c82b246400a3e85905648c80147b0b20ac919002a760e415923200c5e43a82b24640387e85dc1648c8010fb0bb82c9190030fdd6755923202d57416e6b24644baad82dcd648c80147f0ab9ac9190028f215735923225f0f29ea6b246405aae82d4d648c80155b05a9ac9190028fa1671592320051ec2ce2b24644ba9e839c5648c80153b0738ac9190028fa1471592320051ec28e2b24644ba9e831c5648c80153b0638ac919016aba08715923217556c10e2b246400aba801c5648c8015730038ac9192838bccb51592324ef16196a2b24649de2f20d45648c93d47b0b28ac91912ea7a0e51592320054ec1ca2b24649fe2f32545648c93dc5864a8ac919
  | 14 => 0xc84c8765508754d90c90ecaa10eacb21121d95420073230a43b2a847fa3d84dcf65508754db05b9ecaa10029ea0373d95420053cc06e7b2a8400c5d731cf65508010fb0f38ecaa100297a0e71d95420052ec1ce3b2a8400c77815c7655087547d0838ecaa11fe8f61071d95420052f418e3b2a8400a5d831c765508ff4dd0438ecaa10ea9b60871d95420053d400e3b2a8400a79801c765508018bee398ecaa1003175c731d95420043f43c63b2a840087d878c76550801caf0298ecaa100317dc531d95420062eb8a63b2a840087e870c765508010fb0e18ecaa10ea1fa1e21d95420043ec3c43b2a8400a5e8388765508014bb0710ecaa11fe8f61070d95421d536c10e1b2a840087e87c4365508010fb0f886caa100297a0f10d95420052ec1e21b2a8400e5531c436550801caa62886caa10021fa1c10d95420043ec3821b2a843aa3e84043655080147b08086caa100297a0c10d95420052ec1821b2a847fa6e8204365508014db04086caa10021fe1571595420045fc22e2b2a84008ef825c565508030f90ea8acaa10031ddc551595420066bb8a62b2a8401cd4714c56550801a5884b88caa10021fe1f61195420063ab8ec232a840087d8798465508014bd07308caa10029760e611954256f16214c232a840087f87584655080147f08b08caa12b29be09611954201c3f438c232a840087d8718465508014bd06308caa10029760c611954255f16210c232a8400c757118465508014f500308caa10029e60061195423ed1e4328232a847db2c8250465509558bced988caa12a7c310b31195425462f3b26232a84a7f0c424c46550801caec2988caa1003951853119542535374364232a847db2c84c8465508f94d90c908caa11f2cb21121195423fe1e3b6caaa2847fd2c72d95545080b35d0fb92a8a11ff4bdd4725514201476c16e3b1a84a5c6d72d4763509498dae4a8ec6a112f335cb31d8d4200c6fc3a63b1a84a3ccd724c763508019aae298ec6a10034b1097598d420063b38ecb31a8400c767119663508018eecab8cc6a10031d1957198d420066bb1ae331a8409cd4635c66350801b4884b8cc6a10034b10b7558d420043f43ecab1a840087e8719563508011bf0eb18c6a10162f6127694d420052ec1ecb29a84048fa809d953508011f3013b2a6a10eb0f1d36554d423fe36396caa9a8400c3f65dd1535080b35d05ba2a6a100a4f21d5454d4201d1e432a8a9a845ab2c8255153508051dd0db92a6a100a6ba137254d423fe1f3b6cb21a847fd2e72d9643508fb87cec32c86a11f74b9c86590d420070fb2ec721a840093f855c24350875878e9b2aa4a10030fd97745494251716210cbb028400cd7714c760508039a8e298ec0a10034b109759814250e36b90cb302847f87c86dd56050801a5885baac0a10021fa1f655814200
  | 15 => 0xb20ec8a99761fa1b70551532d536412a3b12a609c5d754c76254c014db0a10ec4a9802ab61021d895300566c1843b12a600ae9800876254c0b958c4ba4c4a98032b5d3629895300675b12e1312a605ce8625c26254c011df0eb10c4a980335dc531d81530076898e21b02a600a79850436054c0157308086c0a9802b660c10d815300574c1021b02a604cb8605d26054c099d0c0b94c0a98032e5d3609815300674b96c1302a6008fb875806054c030f90ea8acb218028fe1151596430063bb8aa2b2c860387e87dd56090c0187d09baac1218030f61375582430061fa16eab04860087d81dd56090cc18be63baac1218021fe15715824301c3e42ae2b04860087e87d456090c070f90fa8ac1218021fa1d51582430043e43aa2b048600c5f754c56090d258b8ea98ac1218061fe1d51d95430063ab8aa3b2a86afc5f75dcd6550c0117f08b8acaa18023be09715954302c76412e2b2a86008fb805c56550c091f100b8acaa18061f21d51595430063bb8aa2b2a86018dc874c56550c019aee298acaa18030fd977454d4300477c3ac43128600cd7714c76050c011f70eb00c0a18ea8fa11515925200c5e43a82b24a400a3f855056494955c3ca998ac9292a38795131592520066bb8a62b24a401cd4714c564948031b90e98ac72900335dc53158e521d61e3a2c8a9ca400c3d7559243948012db05baa87291761f21d53582522a53c402a6b04a4008bf845c5609480517908b8ac1290063e21d10582520076898a20b04a400a3d8590764548050f90ab86c8a900637e1d31d8d520066ab8a63b1aa4008df8758c635495d9d2e5b04c0a90023ee1d601815200c3e43aa2b2c8400a3f8454565908018eee2a8acb210163b2097158e424ee36396a2b1c849ec6c725456390939998e598ac7210063721d3158e4245e6639262b1c8400cd7714c563908130fb0bbb2a7210163b2097654e4201c3f43eeab048400c3e84dd5609080187b09baac1211571ba0b755824200636c16eab048455c3f42dd560908ab87a85baac1210021f60775582420043fc2ae2b04840387c855c560908010fd0fa8ac12100e1f21f51582420043f43aa2b04840087c8754560908018beeb98ac12124f171d731582420062fbaa62b048492c5c754c560908031f10e882c121003b44c510582420051ec24a3b2a8400a5e8394765508014bb0728ecaa10061fe1d51d95420063ab8aa3b2a8400d2c42dc76550801a5884b8ecaa10031d5c761d95420052f41cc3b2a8400a5d8398765508690fb0e30ecaa100297a0c61d95420052ec18c3b2a8400c757118765508014f50030ecaa10029e60061d95423fd1e43283b2a847fb2c825076550801c68c2a0ecaa124f179db31d95425578621663b2a8492c5e764c76550951e188498ecaa100395d8531d95420072a30a63b2a847fb2
  | 16 => 0x400902600200000200100b00000001700001200200401100200000601500600800101700000000000100000002701b00000e00000201500900a01400c00100600300b00300b00203e00000000401c02e00001200000100000e00200200200300801800000100100100800a00600300d00c00a00000002f00000000003100000100f00005200200001602200800900500700000000500300100100200700200000300100000000002d00800c00200400701d00000300a01d00201800200000800a00c02600000700500000000400100100800703800200000000400400900502500700000001700200200601500100601900001600200600a00200300000000200300600900200900401000000300402c00000100600400600000800100100400200002900500100000600801000600302e01d00100301d00600000200000600000600300400101100000800003000600000200201a00302f00600a00500200500400a00200200b00200000000900602200e00700003600300900600101100300001900000000100002a00201900e01500000101100e01801401001700000700b00c00301d00100400f00400e0060ab01000800101800c00300000b00203500000700000000000a06a01900300700c00100404e00601100500700900202700600000000201e01a00101100200c00400000503300000001000e00100004b01c00602200200700100000e00200002700101600200400800100200400100200c00000000800200001000000200a00500e00300400b00001200300100001700600000000c00500000403600c01c00101900d00202400100000000000001c00c00000b00701a00200200301900400500900100200700301000600d01500100000d00c00302100600e01a03400000601100000000200a00900200100200200400400500001d00e00b00201100501301f00302100000300100004300700600800000f00b00100b00100800200800100000400100800c00403d00c00404000c00600600000100900300004001100201000200700b00900100100d00503001801d00a00a00200100800000000904102500200300202200502c00100100000000501200000700000600000402f00e00000000100204d00a00000c00003400400600001100300300000000400100700900200000000c00000000000000000b00300a00601000500100000000200000b00001200c00000b00300401601900c6fc3a63b1aa800cd5714c763550011bf0eb18c6aa0029b61421d895400556c2043b12a800ae98008762550011df0eb10c4aa1fe9be1562189540143ec2ee3b02a8038bd84dc760551490fb0ea8ec0aa2c7175d731d815451e2ebaa63b02a8b0cb974d8260550011f70eb00c0aa00335dc531592530045fc22e2b04a6028bc845c56094c0147b0
  | 17 => 0x3fa33a97ac7002f63bca10d1685151fb1ee83fe746423807c88066c38018fc5543071c4809500250f219152cbba6be45e8f506d259d333908c8e055740e03bcfc03bb40995945306082ffa1f82a4825115958022e6f92d38bcc9e217c3249ef4b560af0a401c4ea62ba12c94d85be0ba3fc0ddccd228009917d91465e63890d98a8a1682b584c04b873802292d42e65ef3f41f0879a0000000168bc440c3128c0cd9440a02b0af0a3e0001101bd42020e415717c43106de000146c0000000e90328ea800022b0010000371000209cca8245388a24800063819094bc0000003371c10f1e85c15f0d8447435029c97800005371f79284b20655320a1bc02a2ce39204e85d206b1cd8000dd62862d11f1083405d0f7127c1324f80000454eda0001c800003964bb2098c380008ae1641ca88e823002a96489f8000000201d17c0c72a3868809a5af000130d15e82d17c90d0fba07324ea1845c858f27f85100304891ef0000d2a03036022282c07a80448084b361e0456118c0c042c0d31b94bd02d300000003360e0000037848e00000020a80004a2417090c00074d00006a86a421606200000000000fe94c82ba00000000010668760001c2000019334c00000000000000000000000049800101800000000000002613cb80000007bb2e106a0000000000124400011401a80000006420780000e60000401944036a4640f483d40000bb2d4859856a6910f28000c0600043996a8000000357208c4648b50000000e726e7274a28856248f26710907748513e79a780000000000b30daa0003f1809833069f25f9b382841f03ad0000ce00000f08cd831e89533c875070c4dd1ae1bd01f833e1ce135cc1209d08990506dc5091a78e487602c92290f700000000da06c4d364692d818408aa58c12d0ebc00077f02e0000cc80b914e00000003374051d6078485234a0d880002a50c18000bb40002521dc87ae4df096000000053f2c8944800474e2fb8e640ee4092eb11200fc4e22f81ca40001ab4351ee4af666608c14605d43ce2ce203826a0f14100678d905894000de4a0608820a80004923640b4859c0003e406c09d09a2000000000000000000020c86ca00000300000300402500201500400000c00400000200700400301400200000202400400100200500e00000000600000001200000300600105e00e00800600b00a00000000605003700900400300d00000200d03900500200500900000300400200800000e00402100700000a01f00800000600900400001702f00200101300600101100000400801200300000002000900401400c00000100000000000600500200000200000000000000403702600100700100300600004800001301900400200000800300901105900e02500b00a00102900400000900400d000001020020000032002001006
  | 18 => 0x11308b68840bd85d40021272462034cca6d406c8cc09f22b82641ae84268982bc839c6d83db03784684ae73b21b0de05187982600000a467862ba00000001713289d2000000343a9a188c00003a2800058c000322800024a613000000103e7c600004411487d72501934ca61f20000b5862c5d935c00000003a4359119d12843916a10844f609c42993a04480221538e8ce745d20bf00000004cd3ec0000a8813724a1778e9e5220b114a443007519e811c56c17427787309587882c122e01303ac1709b74c3c0003fa14b40000000f1018c53265728997cc0001400000fe4efc7901f98a990aa24e008928c4ec3a720e223caa63cc35a8000f941df1ec8fa0e3e0e108c901485c4ee15ea2b47084fd36091d410073f3e081940f81c128c82f421243c2310b400786e928898c81b400021d87c40002631741e8cca00002ca000089a000455983c51089117f0b94a1a18032620c00000000001a4c5da0003ba89c4d1a18c000212c00058135209b800018e0fd00007e829623602f80005492e891e4796727060800091c2e22c316d4ef43351cb8b34fb65b4147004841e18b34617eceec7b428521f0f7067f16b848517e8aa0ea8f1ce180a714183189a43b141e946806843500003986166da09f83a4f528833420000c4800019c9ff8f9c55c003167c9ea8663610cf0dc600022f000000000006d80007c47ac000000071e7634529e94f040bc02c95180003023781ec43f83ad4300a8c44237000403c800000000f0f3c00032013c8fa4c2465838107980001f63151d8112c89327d8000b5c3ec0509c3c46c4fa0dc0c8800058b18a00010f651c0001b2444a00033e0000000444139000059446500002fc00063303d034c1da12e38b92007da1840d81e250fa81a1de03944463d20ff08e4a083f52651ab0a941da1001cd0ce25162d316e037688003696b084c3b208b0658ef84fe4530ee0c5e34007f9be89d488216d06dc9547a0000000011a4122eb9c641c64880001da800000000017946747cb22c99e80003f0243800038a0000ee800060c7400001a709aa3571d31a14f080002bb16d844c1550000de846e00021f15d46c01ce3a4800047a7ee00000003528560de8000e5a19f25e86f02b400b2fc000033445c3278920ce63550949ad00006b3000125838c2de0f60ed80003943c70000d4439131b9db809c0002d68000ebc71e0001e70c445ea0ee0370a5c8112ea00fc0941110e01c5001877814889a8ce44b03059c40da03e1459820c5c07ef11f9740c2255f00022c40003810099e740000000000c00b3c4503c5005c5b841904a9c24a280a32ac1a2c85e24a4549b80fce7b31521ad8ebe00041a85a800064b00012cc3a00003481e9800000001e8000eee0001e992701560003ab00000000b50001ac0dae67d4581a00964000000216c000
  | 19 => 0x41c33c88a780006c73000868aa07ae23b894c58e00020f05b41be12442280000004f60000d2c00075c00000010da81600021107340fe04780000d82e30e4083105658412f03d913c5be3699808c566060d720f0000000367a1fcc8604900013401600000ca9ec90ae0000000000ac60000588e38fe686b0000430b4800000000000000271c280000000000000000000058292915000027e0001bf473c0001a18e940007353f800009140a900019e0de600003b188cdfc7b74408a5c8f00002cd20b0de200013e87a80000a000015f400020332c881c1347aa1b91d0465241d0d789d50288371279bb062a6e1356a1242b03be3f610a000022c18f15cc2c862d45d110c59e41f2e314ec7fc3483df1e30a182b900d931cad40280a090a872a56110a803c97265c0f59f6872655402000000002382f687108e66990001e487e286508e956400055d0890ed410e02f3da9cf8b325382bd0c603f042d1e41004ada5fa3061a98b8284630a9c589c637f01594d4e6422d42e80000006e20001ba800005f0fc9e008a675b27b80007520860001a2801a23c04b8550cd42091fc225c6767fa0bb1c8d1380ae18612e800061923e93ac96815141308bc3402c345b0b446fc0001db86f891600035fa19c87e3081be103400065d26303a114e3c619f9f7cb9c6163e383542764761198b2d0440962d99530db07cd038212864c5b91e21c286387ad43209ac0d426510222f106c77300010080861921320d68b000a22e38000a745e338a99bc86e6b13fe8f8c2f062804f8b140848283b08000b2e7a720207640a024045c9f7115035b2e6033062e67430d906110e029437023902a80209a1a3cae27552b79870d4a3584360e84bf22b701897b8aac04b3ae9bfd09c14c0001c741a081e2c415a00460000ef21a01a820a3f50fb80000003a5908868c8423a215dca583e718e91245362bf0000000f3407d2a01218bd200000000000008170a807bcf56009000000113e743000000035a7fb2e21aa40900000c290ad03038a0fd8ea82c60003318cc8c803dd0001a740000b20001f0c000000056000095c39f13697f485277000000006625a012f8c9c1f400020414807be0a632304104d880439e9b700000161e2879c00087024f1c3419237408f0e2c5d83d60f40d7c9d80942df89300e88500a282a848430424b98751423bd0b915e09b04810e11cb87e432d04203f448874c2c702400588080349c0c4d043331018c47565bb12a1508dac14f26c8ca803a6811188c64b8614d1b50000ea203322595b8e3807223d13941ee28540300a8fa24da3658dd849a85f00005dd0f215636c91f916e7a233f084439e6611c1094510a812399a160d564451cc1a9c19e0052ad85280a434e2549bdcb74706147949c80c83b10e1b90f422fc30521345f629d44621c420c614161
  | 20 => 0x3150cf7e27c2ee0d14b9289020713c0a9e65b26a000063665610a00000004dc15016580004e71808960fcc0512629544dbe1f5382a1e8f363733ec852c6ba46e3fa81e41f660d154955491a1db1f02104c1c7f226616548ae3633171790da27e10e481190983b311a19b4ef61532ff197c5dc80538992f010a7661338940cbc38c3410814d503e61880690e6e21d20b8244b0e46f00381a0f9251736609c0b8a61845d99d804857c3d81ff09da7e5380850c5241f43c39fb44040cb0af0d583b03f711f08d4f2855e2659c6cc347741580bd04a409b3fb8d4cfc42db0bc95387722d21a120742384610408198e443a21ec0f2442e11b00012bce565e72b60a087fa10831b1f4041600014511748066f83d7968c1a4293000206cf1a21f23fa268b62208067216877e06136295983e60ea1758b0103271a0001c380005410b09cbc00001a3470c14476000447038889e21900004001167680941dc4dda44a1b69358c7c000300800088e5011a48000db64100001168c9c00044e80009e40a53c99bf00000000d38daceae165383960c17056739097281f20003ef124825a00000021e00ae00000019a03285a52b90000d6e0000001af00007d3290800020a718000000107279e02a00b4d3463c029989826c6353b61534fc85022531f30a1640b17a8d1c9e6000000057c0000000000000d7a13933d800000064409105384f44db41090801506b91f51810d9a0003b58c8d1120000000bc09342840f2222c55e21e22716608f84c93c28c280885d528016f40004c42f09f000004513ea8c48a5000000003ac90882f1070a505565c83859490dde00024a80dc8da0000001fac0384de0000000cc45340001df40004983a519801ba38341885ac1f0341443065c0002f11608000b80368046083421e00019984350b228b32380ec61e000151091839a03240580e040c0142038acc0dc12b2c699480000000000000a66000008097411400004f019c3720000c80c4c4960000ce93043a66973a916dc1ac2b207995209842730a38fac9327ff2950be8eb20ec32d0000168000133000000083a0000d44d0661f1ff90e0a1c88d1868ad07682f23c081fc6584f428405b0a628340ce0c449c000034912f8c901020640a7c88c1233b49e5452a3880100ea01a204f0e88dd4b784833e41aa865063a0311094de445813797c909e7e90d29bb84200c3049062902005e0859aec00000000006646de61700018e45883252d4068400000000000005ee16e09f0000a4c32b000000031235e3fb0c9096e03e0051e2c00000000015884ac4cf2388e3504800039605e80004a53a10000a7800009000004823091778f003ae43a000000000034a2ed8ce04c080919a000000050742a17b00000002588c7c2b80001c3800000000014d00001e800031080e4000359000078c4c
  | 21 => 0x31a36921a44ee157173181c0000b64318d34f8a63d2568308bf800011103b89c20a42c291c8ae05640819d880f00003508b6000045f2c980000001d62079ba072c2812ec05f4b9e0002ef92a05aa731114a17801c83e0d90bf40f615b0260848f2c000450000000039d0950f440001381970000ece4ab000000043652b0208f410ee4b60000bfcd8628909791a00b61ac41482084fe14600014c101e5a108700000c87f1253a264d403fc22100010c47253519a2020e22715d80005b257e1568aa015a7363d20eb827a000000042850e0b32699a1d070689424071d0800000c114f400000031805648621871e090f4688000242926cd880002410000f324b809880000000361a60a34d8c7831b390c030c7640bf94f800000000007dcad26af2351f480000cd09e0a84f6c51e20b00007ca5b233b8b9cc9472813c0f28be841b3de17350e863439e17d44d23c32ad08a036c51d3b79b98ff20c544418b08d658a20898ec3023d50a4868c2e02dd28280645f05cb2bf91eca0c2551aa1d9424c8720c88dec2de3da0171d400004e608f88a80001ed19791984020003cf800031a0000001d1c8820002e980009c86963ea124c5206fb37b22c8000000156000000083f0df86cc00000001d00001ae66b12d86e91360c01fd8000c0a40000000000007d61d01240e4037d2a918a445c1330e502dc84e62739
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x154175e407300e540004801503309c10068d4980160060014a53013c80d2c005002d32006ae12018884a0000036cce9f468479c445890600ac88400c800682000c001061400000002290c0010100594640614c7655080182c4261c611954200709109711846550801a284260061195420061c5c5801846550965e0442185311954200594640614c4655080103e96e157090d420050ba5842dd56050801c24421c4655814225ca324d82841648c801857815c56394e503e40f26376551429400182c82dd95450a5002e2a219425c03250097c8863509700c94025ea1a09848c9610c001650964c510d95200061560d711846548001854865c531195200053425d3144164480038d0874c510591200051564465dc76348001a0f656105218d2000515644655c46348001855855c46118d2000625611711846348001856865c55118d20006152197154463480018c6865c72118d2000515654215c46348001495940857118d2000534640215c46348123855855c65118d200063120971544634800160d942095118d2000711e09715446348001c44825c55118d2000615615719046348001855855c71018d2000631209714406348001a45815446390920005a26425418d424800144c975446350920006916055118d4248001a85815046350920005836574018d4248141c0c63d45748c9204ff0318d515d2324800148c964c5748c920007604c5105d232480a188e865d3638c92000703d957418e3248001c0c655d0638c920
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x80000201a904001c10212e2c00c232a8400d8010990185311954200510b48412e2a88c690002c05a4209715446348001442d2104b8a2031a4000c1125d815446350920
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
  | 31 => 0xa0a
  | 32 => 0xa0e
  | 33 => 0x130a
  | 34 => 0x130e
  | 35 => 0xa4a
  | 36 => 0xa4d
  | 37 => 0x134a
  | 38 => 0x134d
  | 39 => 0x3ca
  | 40 => 0x3cd
  | 41 => 0x3ce
  | 42 => 0xcca
  | 43 => 0xccd
  | 44 => 0xcce
  | 45 => 0x15ca
  | 46 => 0x15cd
  | 47 => 0x15ce
  | 48 => 0x170a
  | 49 => 0x170d
  | 50 => 0x170e
  | 51 => 0xd0a
  | 52 => 0xd0e
  | 53 => 0x160a
  | 54 => 0x160e
  | 55 => 0xd4a
  | 56 => 0xd4d
  | 57 => 0x164a
  | 58 => 0x164d
  | 59 => 0xe8a
  | 60 => 0xe8e
  | 61 => 0x178a
  | 62 => 0x178e
  | 63 => 0xeca
  | 64 => 0xecd
  | 65 => 0x17ca
  | 66 => 0x17cd
  | 67 => 0x104a
  | 68 => 0xcc992
  | 69 => 0x98cd2
  | 70 => 0x15c992
  | 71 => 0x15c9
  | 72 => 0x995d2
  | 73 => 0xd0992
  | 74 => 0x98d12
  | 75 => 0xd0c
  | 76 => 0x160992
  | 77 => 0x99612
  | 78 => 0x160c
  | 79 => 0x3c9
  | 80 => 0xcb
  | 81 => 0x12cb
  | 82 => 0x14b
  | 83 => 0x449
  | 84 => 0x1649
  | 85 => 0x134b
  | 86 => 0xcd512
  | 87 => 0x150cd2
  | 88 => 0xd1512
  | 89 => 0x150d12
  | 90 => 0xecb
  | 91 => 0x15c0d2
  | 92 => 0xd5d2
  | 93 => 0x14c
  | 94 => 0x5c9
  | 95 => 0x17c9
  | 96 => 0x134c
  | 97 => 0x3d2d2
  | 98 => 0x12c3d2
  | 99 => 0x15d2d2
  | 100 => 0x12d5d2
  | 101 => 0x1049
  | 102 => 0xd0a12
  | 103 => 0xa0d12
  | 104 => 0xe8a12
  | 105 => 0xa0e92
  | 106 => 0x198d
  | 107 => 0xeca52
  | 108 => 0xa4ed2
  | 109 => 0x180e
  | 110 => 0x1a89
  | 111 => 0x165352
  | 112 => 0x135652
  | 113 => 0x17d352
  | 114 => 0x1357d2
  | 115 => 0x105352
  | 116 => 0x135052
  | 117 => 0xd03d2
  | 118 => 0xd1712
  | 119 => 0x161712
  | 120 => 0x178d12
  | 121 => 0xd1792
  | 122 => 0x104d12
  | 123 => 0xd1052
  | 124 => 0x44d
  | 125 => 0x74b
  | 126 => 0x1a0d
  | 127 => 0x194b
  | 128 => 0x1a4b
  | 129 => 0x188e
  | 130 => 0xed652
  | 131 => 0x164ed2
  | 132 => 0x188c
  | 133 => 0x1a4d
  | 134 => 0x104ed2
  | 135 => 0xed052
  | 136 => 0x18ce
  | 137 => 0x16c9
  | 138 => 0xb49
  | 139 => 0xb4b
  | 140 => 0x19c9
  | 141 => 0xbc9
  | 142 => 0xa0996
  | 143 => 0x98455
  | 144 => 0x19cc
  | 145 => 0xbcc
  | 146 => 0xb4e
  | 147 => 0x16ce
  | 148 => 0xb4996
  | 149 => 0x16c996
  | 150 => 0xa1516
  | 151 => 0xd992
  | 152 => 0xb4a16
  | 153 => 0x16ca16
  | 154 => 0xb5516
  | 155 => 0x16d516
  | 156 => 0x16cb
  | 157 => 0x19cb
  | 158 => 0xbcb
  | 159 => 0xbcd14
  | 160 => 0x19cd14
  | 161 => 0x44995
  | 162 => 0x45515
  | 163 => 0xb4d
  | 164 => 0xbcd
  | 165 => 0x19cd
  | 166 => 0x44215
  | 167 => 0xb4455
  | 168 => 0xb5655
  | 169 => 0x16c455
  | 170 => 0x16d655
  | 171 => 0x20455
  | 172 => 0x45415
  | 173 => 0x140455
  | 174 => 0x150996
  | 175 => 0x1a57d5
  | 176 => 0x180a16
  | 177 => 0x16cd
  | 178 => 0x20b445d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 2235
  | 6 => 4854
  | 5 => 2240
  | 4 => 54
  | 3 => 6
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (91635+((h/745+packedAt gbK7 (82695+(h % 745)*12) 12) % 2951)*13) 13
  | 6 => packedAt gbK6 (254026+((h/1618+packedAt gbK6 (232992+(h % 1618)*13) 13) % 5825)*14) 14
  | 5 => packedAt gbK5 (141112+((h/746+packedAt gbK5 (132160+(h % 746)*12) 12) % 2689)*13) 13
  | 4 => packedAt gbK4 (3906+((h/18+packedAt gbK4 (3780+(h % 18)*7) 7) % 71)*7) 7
  | 3 => packedAt gbK3 (494+((h/2+packedAt gbK3 (486+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1ff87c0e0ff0780e1ffffe03f0b3873f0743f3
  | 1 => 0xe0ff800ff07fffffe1e01ffff34c44c619fc9f
  | 2 => 0xff0ffff0007f800ffe001ffc0c7078f9e18f1c
  | 3 => 0xfffffff80000fffffe0000f807f01fe0fe0
  | 4 => 0xffffffffffff0000000000fff8001fff000
  | 5 => 0xfff0000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x518148404b44842122a5209a011811b034131
  | 1 => 0x20a08002900092252140849241044444081486
  | 2 => 0x560b2d90045d408a54015968247018a9618b18
  | 3 => 0x85ca2ba900012d899580304b806e00bc0ec0
  | 4 => 0x140e73cd4e6e65c0100610408efa8001d7e000
  | 5 => 0x98c0030188080601011801830fef77f6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefae8fecceac8feeefae8fecceac8feeefae8fecceac8feeefae8fecceac8feeefae8fecceac8feeefae8fecceac8feeefae8fecceac8feeefae8fecceac8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36212
namespace PEqualNP.Outside.L_meta_36212
open PEqualNP.Outside.L_meta_36212.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 4 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 12 := bs0_4_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 25 := bs1_3_0
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
theorem bs1_4_512 : Interval s1Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 539 := (concat (concat (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 bs1_4_96)) (concat (concat bs1_4_128 bs1_4_160) (concat bs1_4_192 bs1_4_224))) (concat (concat (concat bs1_4_256 bs1_4_288) (concat bs1_4_320 bs1_4_352)) (concat (concat bs1_4_384 bs1_4_416) (concat bs1_4_448 (concat bs1_4_480 bs1_4_512)))))
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
theorem bs1_5_640 : Interval s1Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 664 := (concat (concat (concat (concat bs1_5_0 bs1_5_32) (concat bs1_5_64 (concat bs1_5_96 bs1_5_128))) (concat (concat bs1_5_160 bs1_5_192) (concat bs1_5_224 (concat bs1_5_256 bs1_5_288)))) (concat (concat (concat bs1_5_320 bs1_5_352) (concat bs1_5_384 (concat bs1_5_416 bs1_5_448))) (concat (concat bs1_5_480 (concat bs1_5_512 bs1_5_544)) (concat bs1_5_576 (concat bs1_5_608 bs1_5_640)))))
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
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 9 := bs3_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 24 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 117 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 6 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 54 := (concat bgb_4_0 bgb_4_32)
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
theorem allgb_5 : Interval gbAtlas 5 0 2240 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))))) (concat (concat (concat (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344))) (concat (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))))) (concat (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))))))
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
theorem bgb_6_4832 : Interval gbAtlas 6 4832 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4854 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)))) (concat (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)))))) (concat (concat (concat (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)))) (concat (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632))) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))))) (concat (concat (concat (concat bgb_6_1824 bgb_6_1856) (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)))) (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400))))))) (concat (concat (concat (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)))) (concat (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))))) (concat (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136)) (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)))) (concat (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456))) (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616)))))) (concat (concat (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)))) (concat (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064))) (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224))))) (concat (concat (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 bgb_6_4352)) (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)))) (concat (concat (concat bgb_6_4544 bgb_6_4576) (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672))) (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832))))))))
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
theorem bgb_7_2208 : Interval gbAtlas 7 2208 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2235 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)))))) (concat (concat (concat (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 bgb_7_1344))) (concat (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472)) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632))))) (concat (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 (concat bgb_7_1888 bgb_7_1920)))) (concat (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 bgb_7_2048)) (concat (concat bgb_7_2080 bgb_7_2112) (concat bgb_7_2144 (concat bgb_7_2176 bgb_7_2208)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefae8fecceac8feeefae8fecceac8feeefae8fecceac8feeefae8fecceac8feeefae8fecceac8feeefae8fecceac8feeefae8fecceac8feeefae8fecceac8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074664 * 2 ^ 32 + 4274842312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36212.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,3]⟩,⟨.and,[2,6]⟩,⟨.and,[0,5]⟩,⟨.or,[2,4]⟩,⟨.or,[4,5]⟩,⟨.and,[7,10]⟩,⟨.or,[1,8]⟩,⟨.and,[0,6]⟩,⟨.and,[9,12]⟩,⟨.or,[13,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4274842312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4274842312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36212

open PEqualNP.Outside.L_meta_36212 in
theorem PEqualNP.Outside.L_meta_36212 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4274842312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4274842312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
