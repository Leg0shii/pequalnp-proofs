import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36693.Model
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


end PEqualNP.Outside.L_meta_36693.Model

namespace PEqualNP.Outside.L_meta_36693
open PEqualNP.Outside.L_meta_36693.Model
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

def SBf (j : Nat) : Nat := [6, 4, 5, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36693

namespace PEqualNP.Outside.L_meta_36693
open PEqualNP.Outside.L_meta_36693.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x284c1a40128080018076a1601806bf43bd43bf42bd42be41bc41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x180028810020025aa5a1c754f428ea98832d52107a060087808010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
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
  | 4 => packedAt s0K4 (244+((h/4+packedAt s0K4 (224+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s0K3 (170+((h/2+packedAt s0K3 (162+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfe03fffffffe01fffff80fffffff01fff1fe3f
  | 3 => 0xfffc03fc03fffe01fffff01fc07ffe07fe63c7
  | 4 => 0xfffffc0003fffffe01ffffe0007ffff81f83f8
  | 5 => 0xfffffffffc00000001ffffffff8000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x9604848428a224242450b162d48b628a26acdb
  | 2 => 0x2ba1292a51451d4948ac0ab56955115551562d
  | 3 => 0x4caba2329a69491d913d58198c66b4479a6346
  | 4 => 0x713233a3639191911dce6cd03078d9e11d83b0
  | 5 => 0x81c3c3c383e1e1e1e1f78f1e3e40e1861ff800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36693
namespace PEqualNP.Outside.L_meta_36693
open PEqualNP.Outside.L_meta_36693.Model
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
  | 2 => 0x3f80fff807f03f81e0fc1f83ff07c0f8149ecc
  | 3 => 0x3fff03fff8003fffff001ffc1ff800fff8e30f
  | 4 => 0xc00003ffffffc001ffffe0001fffff001f03f0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8082000890800400021422842108520a412c55
  | 2 => 0x955699947525692af0ad15a3574686d0d496cc
  | 3 => 0x264caaa52469b269758219691ad208e598c30a
  | 4 => 0x3468d346464d234db9cb50421ce72c411e03a0
  | 5 => 0x3870e387878e3c71def39e73908430861ff800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36693
namespace PEqualNP.Outside.L_meta_36693
open PEqualNP.Outside.L_meta_36693.Model
def s2K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1a802100883b98f431ee43d087b887510
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x810c00a642cc6590f219443442910910
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*4) 4
  | 3 => packedAt s2K3 (i*15) 15
  | 2 => packedAt s2K2 (i*26) 26
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (5+((h/1+packedAt s2K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s2K3 (98+((h/2+packedAt s2K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt s2K2 (107+((h/1+packedAt s2K2 (104+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0x6afc39cfe3870ecc
  | 3 => 0xfffffffffffffffffffffff3ffc1fffc07ff0f
  | 4 => 0x7cfffe0ffff80ff0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018800104912055
  | 1 => 0x152b9297213266cc
  | 3 => 0xc41350a4844cb0a
  | 4 => 0x38221ac92608da0
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 27 s2Pos s2Neg, 0xeeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36693
namespace PEqualNP.Outside.L_meta_36693
open PEqualNP.Outside.L_meta_36693.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x39c26013950a294812280b9d20a80221294a001e8c4263ea06800084024000002c180091a0018f2d060800b5600000085801b1c60c810c844c185000047144180ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1c964a2e0a140040c26c5e7824728e944438040086c422ae0c00000052be00101e36b462000000925868ac0e60008a48aa50284e2c26009a9e00a60030909c98a2465666008cb0345aa01216c002a43a3e7e2a7ca80000bab27a4c76bc6a20645c84b8000088000032186e06b60854001a4274703c8082240019c020000116b0427006418206083af0e0c40304100811200400013e52d0e7aa921e7d4d439e292873e5410eeca3a15d547429ea9c853e5290aeea2a15d14542af298855d5310b3ca6214f54c42cea98851d5310a7ca4216b948429f2a6653d54ccb3a87995d94732baa8e653f548ca78a9194fd51329e2a2659d434caeea2995d14532bda826578504ca7ca8194f55032b7a92836c525067ca998cf55331b7296636d52cc67ca818cf55031dba1e43b543c876c8590ed10b219f2a4433d54887588510dd946219faa2433c54487588410edd0c21daa18437652087cca410f9d0821db21043b442087c88410e910821f319043e532086bca7a05754f40bb2888175511027ca9984f55330cea1c613e540c27aa8186750c30b7290616d520c2eca2185d544309f2a4413d54882eca3105d54620f210c413f5448278a89057d4d20ae29a417751482e8a29079084209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x140ce40c0001cd1401880000803c101310a44024b48b500400821c6550d32c650c504ca956310b21a358c428868d6310821a918943086a66290821a558c42086c56310821e198c42086a56310821e158c42086856310821a919232086a4644c821e150d32086e0604c82199189511030d43548308758e54883265408620
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x80104847650d3208740a18c099043415ce5408620
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
  | 3 => packedAt s3K3 (833+((h/7+packedAt s3K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s3K2 (150+((h/1+packedAt s3K2 (147+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc07ffc0fffffff81fffff81ff83ffffcfc71ff
  | 1 => 0xff81fff01fc0fffe0f81ffe0ffc3e03f678e67
  | 2 => 0xffffffffe000fffff001fffffffc003f87ff87
  | 4 => 0x1ffffffff03fffffe0000ffffffc3f80ff8
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x530444624488208052925909180529a42c30ab
  | 1 => 0x852cc8a1c919499605b0ab286a4342a9658665
  | 2 => 0xa19114483a2922ab0413452b4a8051282db86
  | 4 => 0x2c51a20912301b4d29640610c7329603d00d50
  | 5 => 0x3061c38e1c3ce3f1ce79c79c06231823ff6000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0eaea8080eaeae0e0eaea8080eaeae0e0eaea8080eaeae0e0eaea8080eaeae0e0eaea8080eaeae0e0eaea8080eaeae0e0eaea8080eaeae0e0eaea8080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36693
namespace PEqualNP.Outside.L_meta_36693
open PEqualNP.Outside.L_meta_36693.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xac0002a000002c0040c240d087005c31a14002273608f8d5238c2d32016143c711914c4c2aa12051204a7480f1601400480000001205529b2810c9068040ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2cb46e5e24a41416047a94767890482662000c224032aa00bc1e3682106872964e0e0060c2441850703a006c00009846809c8400c00066007e74008aa0925abe9e1200000034b65c3eba0a0238088e28ac7c20582e4c88c400b81aae006456b28ca206009a54428600b030006a1c003ca64a5200a82a0800b190200581001c00002100050600285040040f0044f03023c181033e52d0e7aa921e7d4d439e292873e5410eeca3a15d547429ea9c853e5290aeea2a15d14542af298855d5310b3ca6214f54c42cea98851d5310a7ca4216b948429f2a6653d54ccb3a87995d94732baa8e653f548ca78a9194fd51329e2a2659d434caeea2995d14532bda826578504ca7ca8194f55032b7a92836c525067ca998cf55331b7296636d52cc67ca818cf55031dba1e43b543c876c8590ed10b219f2a4433d54887588510dd946219faa2433c54487588410edd0c21daa18437652087cca410f9d0821db21043b442087c88410e910821f319043e532086bca7a05754f40bb2888175511027ca9984f55330cea1c613e540c27aa8186750c30b7290616d520c2eca2185d544309f2a4413d54882eca3105d54620f210c413f5448278a89057d4d20ae29a417751482e8a29079084209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x14400874800143c640c24d00028b0033800044c8141480a008e1c6550d32c650c504ca956310b21a358c428868d6310821a918943086a66290821a558c42086c56310821e198c42086a56310821e158c42086856310821a919232086a4644c821e150d32086e0604c82199189511030d43548308758e54883265408620
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8100004847650d3208740a18c099043415ce5408620
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
  | 4 => packedAt s4K4 (2904+((h/33+packedAt s4K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s4K3 (833+((h/7+packedAt s4K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s4K2 (151+((h/1+packedAt s4K2 (147+(h % 1)*4) 4) % 12)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc07ffc0fffffff81fffff81ff83ffffcfc71ff
  | 1 => 0xff81fff01fc0fffe0f81ffe0ffc3e03f678e67
  | 2 => 0xffffffffe000fffff001fffffffc003f87ff87
  | 3 => 0x1ffffffff03fffffe0000ffffffc3f80ff8
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x530444624488208052925909180529a42c30ab
  | 1 => 0x852cc8a1c919499605b0ab286a4342a9658665
  | 2 => 0xa19114483a2922ab0413452b4a8051282db86
  | 3 => 0x2c51a20912301b4d29640610c7329603d00d50
  | 5 => 0x3061c38e1c3ce3f1ce79c79c06231823ff6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36693
namespace PEqualNP.Outside.L_meta_36693
open PEqualNP.Outside.L_meta_36693.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x8c89c0a59400029938034503a0149001e1800009420800000014833210f801620815005ce80006c900444cc0f0c386a5000401601020810430c3082ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe81bd43d02fca5a05f54b40bf28e817d51d03dc43a07b08740beaa4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c81ee21903d843205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940bfa8a817c51503dc42a07b08540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa8881be411037882207b88440f6108817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3bc87987750f30bf296617d52cc2fca3985f54730f710e61ec21cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c61ee218c3d843185f94230ef98461fb308c2fea8985f95130beaa2617c544c3bc86987750d30bfa92617c524c2fea2985f14530f710a61ec214c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861de310c3b862187b88430f6108617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83dc85907b50b20f719641ed32c82fca3905f54720f710e41ec21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620fb28c417651882faa3107d54620baa8c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920f719241ed32482fea2905f14520f710a41ec21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2107b88420f6108417e50083de40107e88020f690041f920082fea9885f95310beaa6217c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c43ec83887d50710fb18e21f531c43ee43887b88710f610e21f421c43c843885fd5210bf2a4217d54842f8a9085fd4e10bf29c217d53842f8a7085fd4a10bf29421ee52842dca5085f54a10f6a94216d52842f8a5085f54610f710c21ec21842fca1087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53443bea68857d4d10bf29a217d53442f8a6887714d10ae29a217f52443dea4885bd4910bf292217d52442f8a4887b14910b629221f641443ea82887d8c510fa98a21f721443dc42887b08510fa10a21e421443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821ee21043d842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc54ccbbc87997750f32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbc86997750d32f721265ed424cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cafca2195f54432bf280657d500cafca7a0f794f41af29e837d53d07baa7a0d754f41bf29683ee52d06dca5a0df54b41f6a96836d52d06fca1a0df54341beaa4837e53906faa720efd0e41dea1c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0fbd4941b7a92837c52507d8a4a0db14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598fb94b31b7296637d52cc7daa598db54b31bf286637d50cc6fea918df95231beaa4637c548c6faa718f790e31eea1c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f790c31eea18637e520c6faa418df94431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87ee8390fd10721fb98e43f431c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef42887dc8510fb50a21f621443ef32887dc6510fb4ca21f6194437e51887de4310fdc8621bf284437d50887dea910fb95221f6aa443ec54887dea710fb94e21f6a9c43ec53887de8710fb90e21f6a1c43ec43886dca310fbd0621f720c43ed41887d88310fbcc621f718c43ed31887d86310fbd4221f728443ed50887d8a110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821f7a1043ee42087da8410fb10821f799043ee32087da6410fb0c821bf28843f741087e88210fdcc421fa18843ef21087ec4210fb48421fa908437e50086faa010fbd5021f72a043ed54087d8a810fbd4c21f729843ed53087d8a610fbd0c21f721843ed43087d88610fb94421b728843e651087de8210f9d0421f720843ed41087d88210f910421f798843e731087dc6210fb4c421f618843e431087dea010fb94021f6a8043ec50086fca7a05f54f40dfa1
  | 2 => 0xa44c28b00094cda80000024c9f9b0536000299140005fc5080054c57c0000010e0010980000079d4509619e00053800346244002ac08c0f51d0e100015c6e8000fe364a50ad1901380001229080ca216039a240281412a878c0007847c564502b3206605289ea000ae4d20730306f93b00006a07430a640920001f9f80009b40025a000448850000000012411f32e028fc9cb0008bc002383cc53c0026e4ae4e477a6c472a44572b84a04cd1d94e1da0c4468f5340000a800036813c5f1664ac7e9510241caa34c119f3fe1b8ad80050c2945aa041c84f42a02f000a10e808f0002e4552464560f11420a08aa9cbd26138c764fa1fb2f00080fa1123288943a7f0000010f16b00008cb695c000000b70a62f20b0e99bc000a3c002210000008326900037000000000324a89e104e5d8b62b500090c0000020e9ec000003da001090000b8000f88101d06584a0095740013a8071e05a8619362646a83e88c36252c670743768c8002963d68409f000000710000000001e5168002522b0000000009e800000106305518004a490926000372000198e31622d0c60000caa0c000001d86448605b00802000000000380a0000c0a81404804010060600205000038040480601004000200101c0000e000000100001800038060280200008020220a0140580602802000000080c010000000203000000000700c008480380e01840000000180a020060000000814000060300c00056000020100c0900c010040000a0180a00000018020c00404000050040100a0080000000040000100c00804010060180000802050020001000800038040001200000000000080e0000a00000048060180a010000102000000020020100a02002048000381601810000040001204800030100000a0100400004030000781c0080a0000600000048000180a0000003002018000002800800040040c806010000000400814000000000c0880e0000002004010000000e0003d7e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621e750c43bf29087ee5210edca421df54843f6a90876d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a17dd4542bba8a857c5150be8a2a15d14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657
  | 3 => 0xd9d6236000001020002d8002700001f83e0003e4359400950bc0004f800000498000fe01e788f2800000021501c0028000000992449bc6016732485c909585286d8c020f4283f400000510000710c54d00000019d1d610d2c80000096c450005607bc5e92843e000000f80a45f80000b160000408f3000001578250000000012e088960000000001d40002e0000f925a791240c0002970001c53f0a80560e0068290760dc0019c4be39c00109000001330000008dc310d310418000000000080001e90004ec0000005a00096000000000bd8003944c4829880002241410d556834b128c3649246f9cf40e278000001986894914938e3dc4e13834e2bc55a36000000c780009800000000000934002b6000461540000008fc000841f8000fe14d0006410b0000000e8f01f74685f122a1a38a398b0aa54e6000b28000000c83180012e0015b9c10009f0889bf23c000a0000478508d688e4d4650b81471a21ec332022e899400026238360241dd2e43800b10e0348193a00000028c002a952a44c0000040a2ec000000009e000000000000000002d20014f80053200000000512010eb82117e6a00008b01c8a542a5e3be0004d9ba460000000004ba17c6b800094354ea98749c4f0061930847206a0ee5421a026910166474000de000654590000a2000f421840089c0009d202000ab9162fa000c59ac530001588002ee6bd059c9332694000c60000009280029800156800254000ed0000000000000055c00148000000001220000f4164001a6000268000001880009680039c2f0b99e400077054a4a28c4bcf81f50000010d80024e88c7b0001a031d061430ce900000013dc3480000014400085800000558000003faa6887a60256000001370006788d000000000000002d00000029d2bc000ef000000000000fa4820000000000000000047000000e10000000000000000000035800000a70920364b80010722c208000088000001bc002b403c01801840174590cc1bd000000381b7000000440003fc000c28340000005c1c349e401551d22c66a4c68853b0a39198cb0ee36cd0813000989170fb268160840f20009502d2a435c9547a04b3989f49aa813a898d33a190e47b0150002e2000368004d68d4c31234620013ba0926076c000a41d40000018e5268055908000060c2aa08000000f995d00000000000000015410003ec190cd00010c308348002740010a98a44a174001ab03848036175438001392711f2744000000ec3680000008291d12155194001150562b4624a99842de66d0e800000000350b7000334002264406cca90171fe064111b802a0000000022e8f4000000005140011553c0001c8001e23
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x310c2d9600c4309bd96210c26d6588430cb952210c32d5488430d9946210c36551884309bd94210c26d6508430cb950210c32d5408430d9944210c3655108430f10c4210c31d54cc03097d95300c31d544c0309ed95300c25e63153209758c54c823e6414f208f59053c82e46150b20b918532c836651087209d987548827561d52209798c548825d63152209d984548827561152209d987538827561d4e208f990538823d6414e209d98453882756114e20d9d8a51883665188620d9544218836651c822097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d209b195424832c5450920b9185424826c654c920d314d32482e4614c920d914621482ea6088520b9986204825e63150209758c540826e62150209d984540827561150208f990530823d6414c209b98853082766114c209d58453083665108420d954421082e960084209bd95200827b65480209798e54c425d63953109b98a54c426d62953108f99253c423d6494f109b98a53c426d6294f10b918941c42e4624c710d999421c43656508710d995021c43645408710d994c21c43645308710f898021c43e160087109b98b548426d62d52109798c548425d63152109b988548426d62152109b98b538426d62d4e108f990538423d6414e109b988538426d6214e10d994b108423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524436561d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c53149109b984524426c6114910cd15241442746550510b91894144354538c5109d19531442e4624c5109d997214433454c8510d514f21442f260c85109b996214432f5488510cb152214434f5388510d314e21442e661885109b994214432f5408510cb150214434f5308510d314c21443345408510d514c21443675208510b999421443666508510e9d5021443665408510d915021443a45408510c915021443c75308510d994c21443645308510f114c21443445308510f808710442e662841109798c540425d63150109b988540426d62150109d984540423e6414c108f590530426e6214c109b58853042766114c109d987520423e64148108f590520425e63148109758c520436651084109b98a500426d62940109e596100427765440109ed9510043e22144010
  | 1 => 0x86e7614c8219b59432086ae640c821ab590320874d530c821b598f41086e562d04219d59441086b664cc421b958b3108675650c4219bd9521086776548421b9987540872d5415021b398c54086cd6315021b998454086ea6015021ba58054086e661d4c21ab99053086ad6414c21d354c53086e66114c21ba98053086e96014c21b998743086e561d0c21b998643086e56190c21b9d8543086e46150c219b994430866d6510c21e350c43087666194421b999251086e66394421b9582510866d65d0421b398f41086cd63d0421b9597410876565d0421b998f41087c663d0421b198f41087c563d0421b958341086e661904219bd9541086e76510421b959441086e66410421e999041087a65410421e955041086e66310421e9d0c41087a54310421b9580410866d65cc421ab99331086ad64cc421b9597310876565cc421b999331087a664cc421a999331087a564cc421b919331086e560cc421b9986310866f654c421b9d9431086e5650c421b999031086e4640c421b998c31087c6630c421f194c31087c5530c421f190c31087c5430c421b958031086ae6414021ab59050086ce6314021b358c500876950140219dd8552d02746154b409bd8951d026c625474097d8d519025c63546409bd89519026c6254640d994421903655108640e9104219026e6214d409b588535031c5350d40ae181435026e62d45409b58b51503675108540d9144215034e5394840d354e521026e6194840d394d521034d53548409b18552103565394440d554e51103665294440d954a51103676294440d918a511026f62544409b18951103565354440d554d51103665254440d954951103676254440d9189511031d5390440cd546411031d5310440ae580411026f65884409b596211034e5388440d354e21103665188440d9546211026f65084409b594211034e5308440d354c21103665108440d954421103a44108440c754f401023f6550040c754d401027b65500409b98854cc26d6215330c715143cc2776154b309d18552cc26f62547309b18951cc26e62152309b588548c27661152309d584548c23f64546308f191518c26f62546309b189518c3665108630d9544218c3c431086309bd89544c26c62551309dd85544c27461551309b988544c26d621513097195434c31c5450d30b6181434c26e62d45309b58b514c3675108530d9144214c26e62d50309b58b540c27661d50309d587540c23d65950308f990540c25e63150309b988540c26d62150309d984540c2756115030cb952520c32d54948309b986520c32e5454830cb551520c26c6154830cd952510c3355494430d994a510c3655294430d9d8a510c36462944309bd89510c26c6254430cd951510c3355454430d9949510c3655254430d9d89510c3646254430c7552310c355518c430c755
  | 2 => 0x8070080e0200100800004000000b00c0100c1001c010700202c0600c000040200c0403006010000000100800004010000001006000000340000003018000040100002000010080000000018060000000c050040000008000090140100c010100e9bd8951d0e6c62547439bd895190e6c62546439b98b5150e6d62d45439b9885050e6d62141439d9845050e756114143a75924310e3f6550c4397d954310e9f6550c43c7d954310f8d43948439b9865210f1d43548439dd855210e746154843e350d5210ee46154843cbd0d5210f4e4354843cb50d5210f4d4354843c350d5210f6761548439b1855210f646154843991855210f1d43944439bd895110e6c6254443c750d5010e7661942429d5865090b1c5350d42cdd0c5150b354314542d9d885150b674214542c754f4210b4d53908428fd954210b1d53508429bd954210b4d5350842b91854210a7661d53329d58754ccb1c5450f32b9185428ca7661942329d586508ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca5c6550d32c7151434ca6c6550932e350d424cae46150932d590c514cb554314532d9d88514cb664214532d9508514cb6732145328f596540ca3e64150329798c540ca6e6215032c7553320cb2d548c83297d95320cb1d544c8329bd95320cb2d544c832b9185320cb4e5394b41d354e52d074e5354b41d354d52d07676154b419b98a539066d6294e41c794d439069d63d06419b98a509066d6294241d914b415069d63d04418fd9541106776550441b9189411066e62d53319b58b54cc66e62153319b58854cc72e5494b31cb55252cc72e5454b31cb55152cc7676154b319b98a548c66d6295231c7951438c69d64cc6319b98a508c66d62942319758e544c66e62951319b58a544c66f62551319b189544c67b60551319e181544c76452cc5319b988540c66d62150319e980540c67960150318f992530c63d6494c3197596430c71c5450c31a7593310c65f654c4319dd95310c6e4624c4319798c54c865d63153218f99053c863d6414f21b598f41c86b664cc7219798e548865d63952218f992538863d6494e21cb95142886ce6310a21b358c428874e534ca21ab99032886ad640ca21b9987548872f5495221b398e54886cd6395221b998454886e661d4e21ab99253886ad6494e21d3d4e53886e66114e219b994438866d6510e21e350c43886ce63d0621b358f41886ae64cc621ab593318876b50942219798e544865d63951219b58a544866f62551219dd85544863e6494d218f592534866d6294d219bd8953486776154d219798c540865d63150219e980540867960150218f990530863d6414c219e98053086796014c219b59642086e56190821b9d85420866d6510821cb55042086ce6310821b358c420866d658c821b9586320
  | 3 => 0xc00122000204001ea2c00001c9191fa001258353661751a1d90000011d069166000fca421e6000c400021a000001141a40005880013c000499bf4583d8001eb2e8578531d828217c451321a28f0fba3f0006b42918f312001248c000000016a2940a5e0e416300070c1b80024a0000022843e99cc91ff000384000000005f0000c8248000002701dc0012ca08000000001cb0003102a02307e6a0f182615c000c3a6437a5841500748e4b07e18a000294b3912000000001be09a00076000112070b11053e828c711fb4a8000000850e27d85c8001ca9b0000000002840014e2e63d4002093a0000538b7472000e0800182360001c50009ac000000000001e0001100000697b00084c000240000009fa571483a8000000000c8000600008380000027083c298703d848c001e524c65522950000000000004381dc000002e2001241420005a0e72501be3d00000000025c6317d3c03700024e0ca010f22460004205d256018850001793cc000000000004a42d8e325a0f85c1580000e0070ff026000958004709a45906b0001d80016d02c54ceb8112fc36c0f8001301f00c8004d06d0379b716a024f916f0001703f11a0b221c0000031c02000241000048e20731d0594e022115e1b8551b1260364b49e14c06e0002551e0334a00002383e89707400085c0000000000000000000000de00022667c1796c0fe5190a80000094cf814810c0004ea31000008001ba0003c5069ac40e6acfd1bb3164d8f6a01486328ea0780560000026f000808c205646c818ef2110003a51b8e72aa0e83607946413cc694444a6949a95a1e40801423e1c8001059f10000003419e206254ce0ef0005900004b2f43791e80002060c000b434c000000bb000000a6000000000bb227000000a49100000000000017c0006a22d00035c002660c4000288000020012f0833a2528d50001ac000ad95111c5640d25b3dc80000000000000000004800c12515249a9b4000004b06d4240000000010e8573920008000049e000eb000000428000002040cc510c900068c001430008ec461ef4601e88b1fd02a3dc661c70d488c1e8ce11e100820001968cc00263278890bb9d33226840000522e000000000e48491a8500004dd1302703c05cfc00000047d2fa52432788000e0000000000583f8060a589c0949688f11518e9c50616e000000a78002ae1b4000002ac0040000000008050080100400008000000300c000000106c12010130001800803014050240000c0000c02008050040100406038000000002c1d0140000c08004040000105405000020000603c00004030100400005020030580401400000010040200403004010500802c04008000200201408008030000301010004040600100c000000700c0002000004040040700005000000000d02802000010380700000004
  | 4 => 0x3603984d8c50844cc001800005ac000000004382200000019c839ae0000000025d00064ced800328000000000000005480019e24000145186200c088d4400004890c4dc66c5e1723ea0d84d15c236534540003300004226a27c258cc8f925e688cd000272680218ac1607302d1013ce22c61000268104c815f1561849e800000000c6000128118ef9663480943d8004068408e8d34c2460b809f45641800120042000000ad43000000000000910ed03b16c614f49fe32c000f413b0001d5050001d649cd90000005d4239af254444018d52fe574ee21b38c340260990623f8ee800372734e798200c0000000017a97000000058114002620002490205e32e0006d0000360000022e0000b8001210c803cea8142620d0aa19d1da0000000000072800216092000e916a2746d87d80021e2fc0022a00069c00000000001288000001f41100000000031800000000410000004a0000000004250f00a0000a5261c2000374001470001387c10b000000000004449940021a3527ccc300b0cc1540e8a00008b
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x131b8d8c00110b800f001207828f8004000d1e038688001b0023800000181506000300001f80251f0e0022a315a00b249c9c19801785a4219a01900e89848a8717168a1e800c889d001498a100139a9916109d851420928901021180800000220000188d041019004004800a04083162c1801624a8028043e15431855210f42a18c2a9087c150f6154843c1a8630aa421f05431855210f13a18c2a90879190c6154843c4a8630aa421e45431855210f02a18c2a90879154c6150842c18caa1a849968543185424cb82a1a8428a6589550614c832a1ae529a8720d0d72951438c686b90a8a1863465c05450c31a1ae72a28510d0d7494d328869338ea92a44383d516395221c1ac9a9ca710d4671d4e538870732a8621c43835516310821c1ac8a986410e0d5458c5408714aa2c02a043835915314c21c92a6b00a610e0d6550c430866339cc928843299d26394421b0ae73208210c65751903108670b80c818843299d2630c421b0ae93186210cc57690c310874232286188438a5915014021c92c6a80a010d4473544219023238ac429a81435c85350d40c32a6b008220625651042110382a988210881685c041084408c8e2b10a99850d7215143cc2923a2a210c61191c56215130a1ae42a2869861954580310c322b286210861c15503108430b82e0188421850d7315142483122a0c2a1241435d0534c920c88a630a64905467395021c42933a4a610e21491c96115110a88e4b08a6885267495021442a339ca810a21c11535308510a4ce929842885467394c2144383aa0a610a21c11505308510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xa410465840748000015800006004c3a0681d516395221c05649c75394e21a0585191430c421a8180191430c421904815c85350d40c21655c04108440d01535c04108440904815c85450f30904815c85450d30c41655c03108430d01545c03108430a05831506150920a058414c614c920
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
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
  | 6 => packedAt s5K6 (756+((h/14+packedAt s5K6 (672+(h % 14)*6) 6) % 56)*7) 7
  | 5 => packedAt s5K5 (21203+((h/233+packedAt s5K5 (18873+(h % 233)*10) 10) % 1014)*11) 11
  | 4 => packedAt s5K4 (25868+((h/208+packedAt s5K4 (23788+(h % 208)*10) 10) % 909)*11) 11
  | 3 => packedAt s5K3 (3850+((h/25+packedAt s5K3 (3675+(h % 25)*7) 7) % 100)*8) 8
  | 2 => packedAt s5K2 (800+((h/4+packedAt s5K2 (780+(h % 4)*5) 5) % 20)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x81fffff03fffff03fc3fe1ffff87fffa23f1ff
  | 1 => 0xfe07e1ffc0fc3ffc3fc3fe1c0ff8703ddcce67
  | 2 => 0xfff801ffff003fffc003ffe00fff803e1f0f87
  | 3 => 0x1ffffffc1fffffc00000fffffc7e00ff8
  | 4 => 0xfffffe00000001fffffffffff0000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8c1040118208000044046024618091880150ab
  | 1 => 0x14b182228e50542c1c41a208a6882290ccc665
  | 2 => 0x2862d545143aa955c222d5414b550526170b86
  | 3 => 0x7145198828a20d9aaaa811020c664e07600d50
  | 4 => 0x4186110e30c331e33333199380440807baa000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36693
namespace PEqualNP.Outside.L_meta_36693
open PEqualNP.Outside.L_meta_36693.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2aec35a58c0e0056fc25c73010460020b9ab138f5184d9c120009d48a44002eaa2add3a150b0c015ca24ac0072d9400c00bafa62264f54a879648b426bc02a00013000002200061c0020200080080c40510280010004606060405ff53015fd4c03fe53017f54c017d5300ff14c03fe43007f50c03fc43017fd4805fe52005f94805fd52017f148057c5200ffcc801fe32007f4c803fc32017fd4405fe51017f54405fc5100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc5000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x9c2000df54e1004ff8a708027fe4384001fea1c2009ff10e1001ffec50800eff6284007ff3142000bf98a1001ffac508002fd6284007fe3142003bf18a10057fea50802bfe5284001bf294200aff54a10057f8a50802b7c5284013ff9942000ff8ca10007fa6508027fc32840117eb0c200affd4610057fca30802bfd5184015fe28c2009ffcc610007fc6308003fd3184013fe18c2000ffc8610007fc4308003fd2184001fe10c2003bf9821001ffea10800ffe5084007fea842003ff1421001ffe610800ffe3084007fe9842003ff0c21001ffe410800ffe2084007fe9042003ff0821001ffe210800ff71084001fd8842008ffd9510045feca880037f65440013fb2a2008ff99510015fcca88023fd65440117eb2a2008ff19510015f8ca880237c65440053e32a2000ffd8d10005fec688003df63440016fb1a2007ff98d1000dfcc688003fd63440017eb1a2007ff18d1000df8c688003dc63440036e31a2008ffd4d10046fea68801ffe5344011fea9a2000df54d1003ff8a68801ffe4344001fea1a2007ff10d10007fec488002ff6244001f7b122000bbd8910007fcc488002fe6244001feb122000bf58910007f8c488002fc6244001f63122000bb18910047fea488023fe5244001bf2922008ff54910047f8a4880237c524400fff9922000ff8c910007fa648801ffc3244011ffa8a2008ff94510047eca288023fd5144011faa8a2008ff1451003ffe6288003fe3144001fb18a2000ff4c510007ea628801ffc3144001ff90a2000fdc8510007fc4288003fd2144001fe10a2000fd08510047fea08800ffe5044011fea822003ff1411003ffe608800ffe3044001fe9822003ff0c110007fe408800ffe2044001fe9022003ff08110007fe2088003fb1044007ff0822003fd8411001ffeca0800eff6504007ff3282002bf9941001efcca0800a7e6504007feb282005bf5941001efaca080027d6504007fe3282003bf1941001ffec60800eff6304007ff3182001bf98c1001ffac608002fd6304007fe3182003bf18c1002ffea6080177f5304009ff2982005ff54c10006faa608013fc5304009ff2182000ff50c10027f8860800fff62040077fb102003ff98810005fcc40800ffd62040017eb102003ff1881001df8c408017ff520400bff2902000df9481002ffaa408017fc520400bbe2902004ffcc810007fc6408003fd3204009fe1902006bf9841002ffea208017fe510400bfea882005ff14410027fe6208003fe3104001fe9882004ff0c410007fe4208003fe2104001fe9082000ff0841001dfcc00800fff5004007ff2802003ff5401001ff8a00800fff3004007ff1802003ff4c01001ff8600800fff2004007ff1002003ff4801001ff8400800fff1004007fb8802003ff8401001ff4200800ffd1004007fa8802000fe44010
  | 1 => 0x3fe63480037f31a4000ff58d20005fac690043fc63480037e31a4011ffd4d2008efea690043fe5348023fea9a4000df54d20087f8a690043fe4348001fea1a4010ff10d2008ffea490047fe5248001bf2924011ff5492008ff8a4900477c5248021ff9924000ff8c920007dc6490003fd3248001f69924010ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148023ffa8a4011ff9452008ffaa290047fc5148021ff98a4000ff8c520007fa6290043fc3148001ff90a4000ff88520007fa4290003fc2148023ffa824003ff9412008ffaa09000ffc5048021ff9824003ff8c120007fa609000ffc3048001ff9024000fec812001ffc409000fee2048007ffb284003bfd942001ffcca1000afe6508007feb28400ebf5942001ff8ca1000efc6508007ffb184003bfd8c2001ffcc610006fe6308007feb184000bf58c2001ff8c61000efc630801dffa98400edfd4c2006ffca61003bfd5308001bea98400dff14c2006ffc8610003fd430801bfe218400fbf98820077fea410033fe5208019bf290400eff54820067f8a4100337c520801bff990400cff8c820007fa6410033fc3208007ffb084003ff98420005fcc21000ffd61080017eb084003ff18420077fea21003bfe510801dfea88400eff1442006ffe6210003fe3108001fe988400dff0c420067fe4210003fe2108001f71084000ff48420067f84210003ec21080077f3004003ffd402001ffca01000ffd5008007fe2804003ffcc02001ffc601000ffd3008007fe1804003ffc802001fde401000ffe2008007fd1004003ff4802001fda4010003f9200800dffb2e2006bfd9710037fccb8800afe65c400dfeb2e2006bf59710037f8cb8800afc65c4001ffb1e2000bfd8f1005ffcc788006fe63c4001feb1e2000bf58f1005ff8c788006fc63c400dffa9e2006dfd4f1005ffca78801bfd53c4001bea9e200bff14f1005ffc8788003fd43c4017fe21e2000ffd8b10005fec588003fe62c40017f3162000ff58b10005fac588003fc62c40017e3162006ffd4b10037fca5880037e52c400dfea962006ff14b10036f8a58802fff32c4001ff1962000ff4cb1005ff8658801bff51c400dff28e2006fd94710037faa38801bf551c400dfe28e200bffcc710007fc6388003f631c4001fe98e2000fd4c71005ff86388003ff21c4001fb90e2000ff88710007fa4388003fc21c4001fa10e2006ffd431001ffca18801bfd50c4007fe286200bffcc31001ffc6188003fd30c4007fe1862000ffc831001ffc4188003fd20c4007fe1062003ffd961001dfecb0800ffe65840057f32c2003ff59610055facb0800ffc65840077e32c2003ffd8e1001dfec70800ffe63840037f31c2003ff58e10005fac70800ffc63840077e31c200affd4e10056fea708027fe5384015fea
  | 2 => 0x3000ffca698007fd534c003bea9a6001ff14d3000ffe8698007fe434c003ef21a6001ff50d30007ba8698007fc434c001ffb126000bfd8930007fcc498003fd624c001fe3126000bf189300b7fea49805bfe524c001bf2926016ff549300b7f8a49805b7c524c02bffa126000ff90930007fa8498057fc424c003ff9926001ff8c93000ffa6498007fc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6000bf185300b7fea29805bfe514c02dfea8a6016ff145300affe8298003fe414c001fea0a6015ff1053000ffe6298007fe314c003fe98a6001ff0c530007fe4298003fe214c001fe90a6000ff0853000dfec09805bff504c007ff2826016ff5413001ff8a098057ff404c007ff2026000ff5013001ff88098007ff304c003fd9826003ff8c13001fbc609800ffc304c007ee1826001fe0c130067fecb9003eff65c801fff32e4002bf9972007ffacb9003efd65c8019fe32e4002bf19720067fec790002ff63c8029ff31e4001bf98f20007fac790002fd63c8019fe31e4001bf18f2007ffea79003f7f53c8029ff29e400fff54f20006faa790053fc53c8029ff21e4000ff50f200a7f8879003fff52c8019ff296400cdf94b2007ffaa590033fc52c8019be2964014ffccb20067fc6590003ee32c8001fe9964000fb4cb20067f86590033ff61c8001ff30e4000bf98720007fac390002fd61c8019fe30e400fffd472007ffca39003ffd51c801ffe28e4014ffcc720007fc6390003fd31c8029fe18e400cffc8720007fc4390003fd21c8019fe10e400fffd432001ffca19003ffd50c8007fe2864014ffcc32001ffc6190003fd30c8007fe1864003ffd962001dfecb1000ffe65880057f32c4003df99620014fccb1000ffd65880277eb2c4003df59620004facb1000ffc65880077e32c4003ffd8e2001dfec71000ffe63880037f31c4003ff58e20005fac71000ffc63880077e31c4013ffd4e2009efea71004bfe5388027fea9c4000df54e20097f8a71004bfe4388001fea1c4012ff10e2008dfac51004fff5288027ff2944000df94a2009ffaa51004ffc5288027be2944012ffcca20007fc6510003fd3288025fe1944003ffd862001ffcc310002fe6188007fb30c4000bd9862001ffac310002fd6188007fab0c4000bd5862001ff8c31004fff5188027ff28c4013ff5462009ff8a31004bff3188001ff18c4000ff4c620097f86310003ff2188001ff10c4000fb88620007fa4310003fc2188001f610c4003bf9822001ffea11000ffe5088007fea844003ff1422001ffe611000ffe3088007fe9844003ff0c22001ffe411000fef2088001fd9044011ffd952008dfeca900037f65480013fb2a4011ff99520015fcca90047fd65480237eb2a4011ff19520015f8ca900477c65480053e32a4000ffd8d20005fec69004
  | 3 => 0xea1a421eff10d210fffea49087ffe5248401bf292421fff549210fff8a49087f7c524843dff9924200ff8c921007fa649087bfc324843fffa8a421fff945210fffaa29087ffc514843dff98a4200ff8c521007fa629087bfc3148401ff90a4200fdc8521007fc4290803ee2148401ffb024200bfd8121007fcc090803fd6048401fe3024203bf181210fffea09087ffe504843ffea82421fff141210f7fe609087bfc3048419ffb28421bbfd94210dffcca1080afe6508437feb28421bbf59421067f8ca1080afc6508419ffb184200bfd8c210d7fcc610806fe6308401feb184200bf58c21067f8c610806fc6308437ffa98421bdfd4c210d7fca61086ffd5308401bea98421aff14c210d7fc8610803fd4308435fe218421dbf988210dffea41086fef5208419ff290420cdf948210dffaa410833fc5208419be290421bfb148210ded8a41086bff3208419ff1904200fb8c821007fa6410803ed3208419fe190421cbf984210dffea21086ffe5108437fea88421bff144210d7fe621086bf73108401ff1884200ff4c4210d7f8621086bf43108419ff9084200fbc8421007fc4210803f62108401fe9084200fb48421007ea4210833ff6008401ff3004203bf98021007fac010802fd6008419fe300421bffd40210dffca01086ffd5008437fe280421affcc0210d7f8601080fff658c0077fb2c6003ff99630015fccb1800ffd658c0337eb2c6003ff1963001df8cb1800fff648c0077fb246003ff992300bdfcc91800ffd648c0017eb246003ff1923001df8c918067ff548c033bfaa46018ff952300cffaa9180037d548c031fe2a46001bf58e3000ffea7180077f538c003ff29c6001ff54e3000efaa718007fc538c003ffa1c6001ff90e3000ffa8718007fc438c007ffb146003ff98a30005fcc51800ffd628c0017eb146003ff18a300cffea518067fe528c001bf2946019ff54a300cff8a5180677c528c031ffa146000ff90a30007fa8518063fc428c003ff9946001ff8ca3000ffa6518007fc328c007ffb0c6003ff98630005fcc31800ffd618c0017eb0c6003ff186300cffea318067fe518c033fea8c6019ff146300c7fe8318003fe418c001fea0c6018ff1063000ffe6318007fe318c001ef18c6001ff4c63000ff86318007dc318c001ff90c6000ff88630007fa4318003fc218c0077f3046003ffd423001ffca11800ffd508c007fe2846003ffd023001ffc811800ffc408c007ff9846003f7cc23000ff6611800ffc308c007fc1846016ffd95300b5feca9805bfe654c0057f32a6016ff595300b5faca9805bfc654c0057e32a6000ffd9130005fec898057fe644c02f7f3226000ff59130005fac898057fc644c02f7e3226016ffd51300b6fea898057fe544c02dfeaa26000df551300aff8a89800eff634c003ffa9a6001dfd4d
  | 4 => 0x85efc644c447ffaa26223dfd5131117fca89888ffd544c401beaa26222ff1513100dfec698807ff534c403bfa9a6201ff94d3100ffaa6988077d534c403fe29a6201ffd0d3100ffc8698807fd434c403fe21a6200ffd8931005fec498803fe624c401feb126200ff18931005f8c49888fff524c447ff2926200df9493111ffaa49888ffc524c447be2926222ffd0931007fc8498803fd424c445fe2126201ffcc93100ffc6498807fd324c403fe1926201bfd853111ffea29888ffe514c447fea8a6223ff14531117fe8298803fe414c401fea0a6222ff1053100ffe6298807f7314c403ff18a6200f78c53100ff86298807dc314c403fa18a6200ffd8131005fec098803fe604c401feb026200ff1813101df8c09888fff504c447ff2826223ff5413111ff8a09888bff404c445fe2026201ffcc13100ff86098833ff65c843b7fb2e421dff99721015fccb90877fd65c843b7eb2e420cff19721015f8cb90833ff63c84017fb1e4221ff98f2100dfcc790803fd63c84017eb1e420cff18f2100df8c790877ff53c843bbfa9e4221ff94f210effaa7908037d53c8443fe29e4221ff90f21007fa8790887fc43c843bffa96420cff94b21066fca590877fd52c8419fe296420cdf14b2110ffe6590833fe32c8401fe996420cff0cb210effea390877fe51c843bfea8e421dff1472110ffe6390887f731c8401ff18e4200ff4c72110ff86390887f431c8419ffb064200ff9832101dfcc190803fd60c84017eb06420cff183210effea190877fe50c843bfea86421dff1432110ffe6190887fc30c8439ffb2c421cbfd96210e7fccb1080afe6588439bf32c42029f996210e7facb10872fd6588401beb2c42009f596210e7f8cb1080afc6588401ffb1c4200bfd8e21107fcc710806fe6388401feb1c4200bf58e21107f8c710806fc6388439ffa9c421cdfd4e21107fca710873fd5388401bea9c4220ff14e21107fc8710803fd4388441fe21c421fbf58a210e7fea510873ef5288439ff2944200df94a210e7faa510873fc5288439be294421cfb14a210e6d8a510883ff3288401ff1944200fb8ca21007fa6510803ed3288441fe194421bbf986210e7fea310873fe5188439fea8c421cff14621107fe6310803fe3188401fe98c4220ff0c621007fe4310803ef2188401fb90c4200ffd8221007fcc11080efe6088401feb044200bf58221007f8c110873ff5088439ff284421cff542210e7f8a110883ff3088441fe184421fffd95210fdfeca908037f65484013fb2a421fff99521015fcca9087ffd654843f7eb2a421fff19521015f8ca9087f7c65484053e32a4200ffd8d21005fec69087bfe63484037f31a4200ff58d21005fac69087bfc63484037e31a421fffd4d210fefea69087bfe534843ffea9a4200df54d210f7f8a69087bfe4348401f
  | 5 => 0xca3200fd86519033ff618c801ff30c6400bf98632007fac319002fd618c819fe30c6429ffd463214ffca3190a7fd518c853fe28c6428ffd0632147f88319007ff318c803fe18c640cffd8232007fcc11900efe608c801feb046400bf58232067f8c1190a7ff508c853ff2846429ff5423214ff8a1190a3ff408c851fe2046401ffcc23200ff8611909fff654c84f7fb2a6400dfd9532004feca9909ffe654c8057f32a6427ff5953213dfaca9909ffc654c8057e32a6427df19532014f8ca99003ff644c8017fb226426ff991320bdfcc899003fd644c8017eb226426ff191320bdf8c89909fff544c84fbfaa26426ff9513213ffaa8990037d544c84dfe2a26401bfd8d3200ffea6990077f534c803ff29a6401f794d3200ffaa6990077d534c84feea9a6400d754d3200ff8a699007ff434c803ff21a6401f790d3200ffa8699003dd434c803fe21a6401bfd893213ffea49909ffe524c801bf2926427ff5493213ff8a49909f7c524c84dffa126400ff90932007dc8499003fd424c801f6a126426ff1093200ffe6499007ef324c803ff1926400f78c93200ff86499007dc324c803f61926400ffd8532005fec299003f7614c8017bb0a6400ff98532007fac299003fc614c8017e30a6400fd18532005e8c29909fff514c84fff28a6427ff5453213ff8a29909bff414c84dfe20a6401ffcc53200ff86299003ff604c8017fb026400ff98132007fac099003fc604c8077e3026427ffd413213ffca09909ffd504c84ffe2826426ffd0132137f88099007ff304c803fe1826425ffd963112dfecb18897fe658c4057f32c6225ff5963112dfacb18897fc658c4057e32c6200ffd9231005fec918893fe648c42f7f3246200ff59231005fac918893fc648c42f7e3246225ffd523112efea918893fe548c44bfeaa46200df55231127f8a918806fd638c403ffa9c6201dfd4e3100ffca718807fd538c403bea9c6201ff14e3100ffe8718807fe438c403ef21c6201ff50e31007ba8718807fc438c401ffb146200ff98a31005fcc518803fd628c4017eb146200ff18a3112ffea518897fe528c401bf2946225ff54a3112ff8a5188977c528c449ffa146200ff90a31007fa8518893fc428c403ff9946201ff8ca3100ffa6518807fc328c4037f30c6225ffd463112ffca318897fd518c44bfe28c6224ffd0631007fc8318893fc418c403ff98c6201f7cc63100fee6318807fc318c403fa18c6200ffd8231007fcc11880efe608c401feb046200bf58231007f8c118897ff508c44bff2846225ff5423112ff8a118893ff408c449fe2046201ffcc23100ff86118807dc308c447ffb2a6223bfd953111ffcca9880afe654c447feb2a6223bf5953111ff8ca9880afc654c401ffb226200bfd9131117fcc89885efe644c401feb226200bf59131117f8c898
  | 6 => 0x800002801400800c00001000c00403000000800c00000000001401c00400800003400401400000402000001000400800000000400001002407000000800800401802800000400000800000000c00001000000000400000001800800001001c01800401c00000001400400801000000000000400000c00400400000000800000001001801800000400c02c00400000001400000800000000001400800800005000403000000000400400000003801000000800400000000400001403c01800002400000000800000000400001bfb22a6009fd9153166fcc8a98037d6454c59be322a601dfd8d5300cfec6a980b5f6354c03bfa1aa601df90d5300ef886a98037f6254c01bf312a600df58953006f8c4a98027c6254c59bfa12a62cdf1095300efe64a98075f3254c03be192a600dfd8553006fcc2a98037d6154c01be30aa62cdfd0553166f882a98077f3154c03be18aa600dfd8153006fcc0a98037d6054c01be302a62cdfd0153166f880a98077f3054c03be182a62bffd954315dfecaa18affe6550c057f32a862bdf99543014fccaa18affd6550c577eb2a8600df59543004facaa18affc6550c057e32a8601bfd8d4300ffea6a18077f5350c03ff29a8601ff54d4300efaa6a1807fc5350c03ff21a8601ef90d4300ff886a1807dc4350c03ce21a8600ffd8943005fec4a1803fe6250c01feb128600ff18943005f8c4a18afff5250c57ff292862bff5494315ff8a4a18af7c5250c03ff9928601f7cc94300ff864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c017e30a862bffd454315ffca2a18affd5150c57fe28a8601ffcc54300ff862a1807dc3150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028603bf1814315ffea0a18affe5050c57fea82862bff1414300ffe60a1807df3050c03fe182860cdfd8e52156fcc7290037d63948013eb1ca40cdf18e52156fc87290037d4394855be21ca40cdf98a52014fcc52900b6e6294855bf994a40cdf0ca52066fec3290037e6194801beb0ca40cdf18652156fe63290ab7c3194819bfb04a400df98252006fac1290337c6094855bf984a42adf0c252067fecb190a6ff658c819bfb2c64009fd963214ffccb1900afe658c853feb2c6429bf59632067f8cb1900afc658c819be32c64029f19632067fec919002ff648c851ff3246417bf99232007fac919002fd648c819fe3246417bf1923214ffea9190a77f548c851ff2a46429ff55232006faa9190a3fc548c8037eb1c6401ffd4e3200efea719007fe538c803fea9c6401df54e3200ff8a719007ff438c803ff21c6401ff50e3200ff88719006fe628c853ffa94640cff94a32066fca5190a7fd528c819fe294640cdf14a32147fe8519033fe428c801f7214640cff10a3200ffe6519007df328c803f7994640cff0
  | 7 => 0x1050000001dfed500000000000000001b439400224830ac79a92ad8976738e98000001d105ba5380016d0001a1a1cacd8002670000da0064e09a0d5f0001114d84ac84dddf4002e09510000271360378cdaec93896a9fc4d0cc289264e00027890180d8c100dc000000002678df12ca298002451150000ad8000000b5ce387b40000000004f0001b520e9270002869528002070001aca49800000121800000195c8440012dad601f6b54724842ce18291fda59030f6ee28e50635f196dc001184002700000002aa1a48eb0002b685c80000000029ea7100000020c8002eb0002388cc8000000002968a80000000000740db5ebadf0002e780000000000014d9f780000000020a000000000000001402800000000000400003c01001400c00800800c00000c02000000000000000c00801000800000c00000400401000400000800401001000c00000000800001000c00801800002800401000000000005800000400400400400c00001400c01000800400000c00000000000801800000c00400c00c00000400000001401003403c00000000c04400000400800c00800400400800000801401000400000800000401004000000001c00801800401c00400002000402801802c00400001800000800000000002c00000400000000800800000402000c00000800000800400000000402000000000c00400000000000000400000000c00000000800000400000000c03800401000400000000000000001000000000002800400400000c00000801400401400401400000001400400800802000800000c00400001c00400800400c00400c01001400000001401800000400800400000000400001402400400400c00000001800800400400401c01c01800400000000800400000400400000000801000400801001002c00000000c00003000800400000000400800402400000800800001800800000000400800003c00003400000000000002800400000000400801801400800800402c00000400000800000000400801403400800800000003800800000400400400403800000000000c00800c00000002400000800400000000000000000000001401004000001000800400c00001003c00001000400800000001000c01002000001000000000400000c05802806003404000402800001000c00001000000000000c01000401401801800000c00400001000000000401c00003801004800401c00000c00c00000800801c00402400800001000000400000000400400000400000801000400c00000000400800c01400000800403c00000000800800000003c00803000000800800000800000000400000000801800400400005401000001000806000000000400000401800800c02001003c01000001800000000c00000001800801000c00000c02000800
  | 8 => 0x30f928b97029d8000af4659b6c002320000001950000000a5a4089fa171f01a700022c0000001888000000000000001021e4c000000000000368000e180000008c00000000027e00000000023b8001c600000000023c8000000000000002bec0000000023f8001221c0c344000000000000000fe8002282b398a00000000006e9649d4c2a8000660000f9800283806e7d8001ba000011cc40002028da40018d8002d5400012a610000498000000000dbc000002050000000001e2e5199600000022a000217ac98481486a800014380022f0000000001bb84647bc001798899a0088eda8001b420a8000002db02b97b0002162a680019aac62c64001b780000028910b800121c000000002400001ee0000ee4000d145f56105381b8001ce00000b8000002ec0000c180018b000056a902349fc0002a60000820001e50000001820ae8000162560001e4a770b98038000001cd8000001ae0000000000000000b598f00015a0928000000000811bc80000010000003892e8700000000fe40014023086e552118c00167aab1411080e58831b82d11a3478857a658000000000000c4c00000096c002755098001c094497326183e0000002be4172000000bf00000000027fa004000001870bac000000000002e9000000170c0b0d2c000000bb5dda9dc00062800044a5b1a1000095c001cc00000000000000026d94d2a1133975a1d2d7c0010c59b14a8000000001b1c1d0241068000f104380008006200017f0c78000715be902c14a59abf400241c0026398fc000000001e30000a119280009d21e91a5720001688002458000002568000000002cf9eea908779788942d00470d62059a7acc5ec1f99be06b00008ba0e04b6950000001a500002c1bc400000275e8f00010f00028a0000a48fc8a280995906c985d64c000b28001a419648d21980000027ea998d780000000000021a80023784c0cc19798a80017d8000002d1983a5501913322d2d20b9d1d8280250d38000001c78002425654000000002bd99e5742d3692ab424203900000013c8000e100026c80016b24314c11f1c40ff0508080000002bfc6f1325c9a5d80000000000000016a1b48e4143113a230e61da0000000000580bcc001f200000014798e099191ab1991e8611b0000000000002ccda24d8abc80000000000007d1801462a708344d8001fe4a88000000a50d400000000c40000000002180e80024c84cc002601f280000002f8000001c58000001158000000b7ddc0001ba8000f687500015e0000000630001278000000000000a91fdc00247800000000000120081c0000009a00000028ca698858000002ee80011b80012a8002d38b740013b000005c00100cc9c000001a3c0000004180020c1d080000000000000000013000000007ac000000000000000000000000000001bd0
  | 9 => 0x1c3202ea992ec1cc0000000023000000000012f800142800119ce31e1035a26c35d0bc0001e9f26b08002980e640000000d058482a5e11a9639658000000000000d800024b0c88540001df1a898f8000000000000000000000a8daa81c400000000093c000000000001d98000000002580fdc0006dc0009e0000838d08002960000000002cf0000002ee1862668001971ff0000000000000e6c00058c0004f8001fd40000000000011f8000934002691b38001100000000000001b14b88000000b6cef190cef5bf86012606066e000134992101c0003e923d958000000a000028d0002009181809d0c002370002c380007280020d8000000001f31f36548000c800000014f000000000000000000000000000000175c000002e715181aeac93502d2a04d19a962bac32cd04861c2098002b99e3c002c91c15f5ac88d994597d1a05440000000001e080000000000014e81f8d50002811dedd54000000000000000001bbe780ab891d0f8000c080024480000029a0ec0002338001a450a00c21e0e2a02000116a68000196969000000000021d19000132c0000000000000019c048c001210000002d58001fb839d8780000009692a02b00700011c8001005b28289b2d6d9bfc000120e70818000000000000ea1248704591234000000b50964000159070320518000000001148001d380000000000000000000d40017e10340000014980e00007c00008900007e8000959840110000000955ae8c5800189a278bc82ddfe276800000103c00000083c780510002de8000000002108ba8f606b9eb253016a2015c0768000b78880000848000f7651063c0028e83ad581e685720b9940a0a272bbddd1239342e50001af03f00001d68212b9e88000000001161c116e849c0000002380013c04e0c940010d0000002b78000cb80000000004d6ed8002d70944000002e693a80012d0001f62cea5093e83115f8000000000000119eaab519b8000000002b60001be6a080000023a0e7d241df8af059c000e2110c08a6a93700000008c8001382290f20000001bf0440bd9c88000c34d1ee100000011313d8000002b28f85750000888000000002b8864c000002c54000001d80000000000002220000001ad87d8000000000000000000000028458001c28d7e44d194000001ed83800016701edb5d771230dc596c9b95f45d272a5c8eb83b81894f90add48c3c0004a89ca4ba368001989228a400009ea8280016f84e40000000000000000000000000020f8002978ca9b02c08be8cacfc1e280011f40006c0bb8002be1f090140020800000000008e13e00000000009d90b4000000000001a9c000000000002e98000001c8000218130a39000000162846ae82590fd9f64001a4c0019e86dac5d781508f086183c2ca947d8e9120000211124152cb1cb2c721421318
  | 10 => 0x91c8c001d661da398018000000000dd8a98000a9e719b61a1dd78000000000000000000000000000000000000001810000000000001ab0000000d74000001de42d400020eb20bc69fa3e07e2e603a4000fb15505480000006793d15b83b0001a380000016e0000002b9133400124400098e4f00016f2212870002528001cf0000000000000718000002798000000000000002a19561d1810c002d6dd1d1ed026938002720c92b800000001e00a21fa25800033848a4a000000122c4959d8a680000029c8001c7000000000000000073046072c000758329250bf9e59778000000000c4887cd28e76241609ff6d65310f7c5966090887f0644002078348bbc2a0f88000000000000000650001108520df8000000000000000000400a18b8d540ca6194000860000000cb04bee5aef8000002a2a4dabc22e8000d100000000000010c000000000000000000128a319b980029d00011a2060002aa9ef00028880000000000000000000027d4900001c19f6c000002168fe0ed05e00006e27b9bec2680013f000111da600003180027d0001129c00afdcc9320d9d1880003f89f23626ead81601e0c002d4c00249c4a6e205612240000000000000023f000000000000000000073c000000478000001b6619c000000001e383d01f2b84f32068209790002d98d215feda2e010441a9e719a1869ebebcd71157adda3e8001b71214960c62de1e90001a82c5a0b2880708000000002588000528214a25570771d5ccf8000000002652e88030001f7c002a42c40ec85d8000000000919c48000826a59281e153193a247119abfacc89526fe7423508f2c48000000b0c000000000000000000001ce8000ff80000000000010d8000001bc06f9b0800000000201cfa8000000001c064a4670000000002c680000000000004b0000000002a4a758000000002188000000a60001c96eb9900000000001fb00000002e800000299000034c000000f280000000006900000600015d2afa0d0b4800000203a942b11d754900000019fc000000002410000000000000000000000000000001fcab4a5f990ad76d2800000200e6c1f50001af800023105a7a8f187b0000334000000370d58000001f88079640b601400000019f65a8001668000ab0002bbaae9680000002bd0000000000002a000027c0000000000000000b1959a5f0000001bd8ad0e880000000000005a8001dc800100ac100007c84c80008b2850f400025580000000011d2ca0001b902c6dc800000000285a8d98489b2dd1fd8cf0000ae15b24880026b80000009c0000000000000000000001f91de0000001038c44edc002a31d30d24f02ad00005ecb70000b2045cd31a692686101e5d918904a2d317aa898000000002c20002b72c299dc0c88d80000002cc000001f15c6a21800000000000000
  | 11 => 0x21630000279ac092046d7b4bd000160d69aa5c868001f75a0800097c0000028c0001f81e20000a1c001db932917c8a19ed7b80000017f95585f2b8e1925b80010e9954b040026f8ee25a0000b10ea84084c4ce80000001c25724a80000000000000007200000014700000000000027ca841910ff4139048002db86f41fc001aa246a918002419b8ac199162d8002930000eeadc09300015885f9fd0734000000002ed2460000bb00014a0000be13fc000fec985d6e090761391606ba86eeac08a9539e45938b68dc9090000a7800000000020541a620454000002631d88000002f080000028a80000017684100000000cc0000000000029aa1a0000000000000000180040ac2330002688850000000000000000000000d7000071c000000000000000000000000002cbd02aba2a5242a970000000001530331d400019d082dcf8000001299b185314b00018c1de87916181d8000000000000738001405e25422a881bc000000000001ef8000000000db0001bd40502d83a8300fd46d620a910a702291ea660002921d500000015a9b20000001fe894ae480016c80007440004e892e482d40000002801fa1c1ed0a8099f88f8f383540007a036156a229bccb80000988398000000001652490001661858de4b32151a14000000000ed8001e405e93696b87127f1cd00000021b0000001ad198097ab040f8c380000000000020480028e00000000023d80002624c1f10000000000000000000000000e78598001a30f80002ab800000000047c000648002540001e01d6243a7621c54c99480012926f13b97c9c20870c50000ef80014e2101da8d48eed0b05fc000f50c21bf4680b922380001a06085c0000420000000f70200000001bb43a063a1b8002d86d49ec8000000000000000000000000002bdd6c2a788e8000dd42f00000000000000004d069a4d00000015da578008a30000de10c80000001009100000011c0000000000000000002440000000000002818000ffd881850da80006fc001b12e38000ba5f1c1c80010625c1398002f01f480000000000000000000000000021286a0058000001ff9cb8c99748000a84002958000002705ffcddda9a8f8aa8f798b9b6a708641c50000000000000000000000938002949ca0000000002134d94e91b250100000005b0f48002df87a9eb6b300000000000000000022517a0000ca1481b3000000000000000226994ddb1b5810800000000000000124ca0d110000d8c000000000000000000000001fcc0000020300028b0000001d066a00010400020f24e8551d2800087a74920c2925022b03d8e014e6c0000000133ebb1450b64ce14b80021111197180029b8502380001bdc000000002ef0000000000000000002e32e41258001f38a15f3cb940021592b2778001204000000000000dce648000000
  | 12 => 0x1ddc000000002b24000000001ab80000000000012e2310000000a20000002504002024000b08000001f2e6d0000001f4137a215864002340000000fba791141a20001f68011358d68428178000000001e78001760001d00a96120af8450068aa16e61481dda2e9b1e980000019769c033c24ad4542de34000000000000000002eaa040002bd4000000002d88002d7ad91e1ed5d078299fee3d22cab58cd20163b0dc1c92b5d8d07b9b54b4094dd700023580011e09800018c8220000d90000000de8000000000002088000000000000b8400298ac50000000000c30971d14114002a21819d20000688f580000019c8049f70000000020000001d58000000000fd00022600000006d21f0001ed2328002cc0002bf0b000028780000000000000012080002c9c248867b1c38a3aea136e2a82599e2e18002c8079870cc02af22f855925d0a8001500d01930002730dad2c00000024f9e0572800000000007400213a11a7500019900000000000008080000000000000000000000013740020180000000000000006a80000000000002e00003caae0000000000000000001e60000125d6a0355ca3a94897080023c07c40011780000000000000027a0001ca9e800000000000000017e80000000000000000013f8430000c68e699f0588000000000000bc2a380000000000a88959980000009980000000000000029e0000db9bb0000001ea0000000000000002830000000000000000dd0ba0002bc40000025d1faad6800000019800000000000272c4ac000e818f4fa07f86695e85a0002be92540000000000010e0e480000000000000012f0b38340000000000000000002a909a96200025ea6b2b0228a2e00001b04b9904908000d05e19a280f000000047662a84800201173a640c714084900000000001300000015497c0000350000748001171468000002cb80029f0000002b2e5
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd7650c1001cfc7650c1002d7e7550c100057d7550c1015e7e6550c100067d6550c1000ede6350c10006dd6350c100279c4350c10064ff75988100667f7598810014fe7598810004fd7598810064fc75988100667c75988100647c759881000cfe7398810004fd7398810064fc73988100067f53988100067d539881001eee72988100667c529881001cfe709881001cfc709881001eee209881001eec209881001ef7109881001ef51098810004ff75588100067f75588100047f7558810014fe7558810004fd7558810014fc75588100067c75588100147c7558810004ff735881000cfe735881000cfc73588100067f53588100067d535881001eef72588100067c5258810064ff71588100f4fd715881001cff705881001cfe705881001cfd705881001cfc705881001eee205881001eec205881019d7f76948100667f76948100647f769481019e7e769481019d7d76948100067d76948100047d76948100667c76948100057d739481019e7f63948101567e63948100067d639481019e7c63948101a57e729481002f6e729481019e7f62948100667e62948100067d62948100667c62948100367e619481019e7e609481019f77109481019f7a109481019f751094810064ff768c81001cfe768c810004fd768c81001cfc768c8100057f758c81002d7c758c81014e7e658c8100067d658c810066ee628c810006ed628c810004ff764c81001cfe764c810004fd764c81001cfc764c8100057f754c81002d7c754c81013e7e654c8100067d654c81000ede634c810006dd634c8100075d534c810006ee624c810006ed624c810005f7714c810005f4714c81005cff768c41001cfe768c41000cfd768c41001cfc768c41012e7e658c4100067d658c41000ede638c410006dd638c41005ef6618c41001dfa708c410005f9708c41005cff764c41011e7e654c4100067d654c41005ef6614c410004fd76c84100ee7e65c84100067d65c8410196f661c8410004ff7688410004fd768841002d7e75884100057d75884100e67e65884100067d6588410006ee6288410006ed628841018f6c528841001dfa7088410005f97088410004ff76484100057f754841002d7c75484100fe7e65484100067d6548410064ff760841001cfe7608410004fd760841001cfc76084100de7e65084100067d6508410066ee6208410006ed62084101876c520841017ef6610841001dfa7008410005f9700841001dfb7644010006fb7644010004fb76440100077b754401016f78754401001f7a654401001f796544010007db7344010007d8734401016f7b5344010007795344010007eb7244010007e872440100077a524401016f78524401001dfb714401001ff37144010176fa614401001ff2614401016ff2514401016ff15144010007f22144010007f12144010
  | 1 => 0x851001df6700851001df470085101c7e620085101c7e4200851000cff764c11003cfd764c11000cfc764c1100067f654c1100b67c654c110006bf644c1100aebc644c110006df634c11000edc634c110006ef624c110006ec624c110005f7714c110005f4714c11001fd8304c110004fe76c81100067f65c811007e7c65c8110006df63c81100a6dc63c8110006ef62c8110066ec62c8110005f671c8110005f571c8110064ff7648110004fd7648110004fc76481100057f75481100457c75481100067f654811008e7c6548110006df6348110086dc6348110006ef6248110006ec6248110005f77148110005f4714811001fe8204811001ff010481100067f65c41100367c65c4110006df63c411005edc63c4110006ef62c4110006ec62c411001df671c411001ef761c411001dfa76c411001efa76c411001cfa76c41100077b65c41101bf7865c4110007db63c4110007d863c41101bf7b53c41100077953c4110007eb62c4110007e862c41100077a52c41101bf7852c411001dfa71c411001efb61c411001ff361c41101bff251c41101bff151c4110007f231c4110007f131c4110007f321c4110007f021c41100067f73594100047f73594100067e73594100067d73594100067c73594100067e43594100067c43594100067f72594100067e72594100067d72594100067c72594100647c72594100067f32594100067c325941002e7f71594100067e715941002e7d715941002e7c71594100067f31594100067c315941001e7f705941001e7e705941001e7d705941001e7c705941001e7f305941001e7e305941001e7d305941001e7c305941001e7f205941001e7e205941001e7d205941001e7c205941001e7f105941001e77105941001e7e105941001e7d105941001e75105941001e7c1059410004ff7558c10014fe7558c100067e7558c100147e7558c10004fd7558c100067d7558c10014fc7558c10004ff7458c100bcfe7458c100bcfc7458c100067f5458c1001edf7358c100267f5358c10026de4358c10004ff7258c10064fc7258c100067c5258c10026df3258c1000cff7158c1000cfd7158c10024fc7158c10026dc3158c1001cff7058c1001cfe7058c1001cfd7058c1001cfc7058c1001ede3058c1001edc3058c1001ef71058c1001ef51058c101ad7f7654c100067f7654c100047f7654c101ae7e7654c101ad7d7654c100067d7654c100047d7654c101ae7c7654c100057f7454c101ae7f6454c101667e6454c100067d6454c101ae7c6454c101b57f7354c1002f5f7354c101ae7f6354c1000e7e6354c100267d6354c1000e7c6354c100057c7254c101ae7f6254c101ae7c6254c100275f3254c1005e7e6154c101ae7e6054c101af771054c101af7a1054c101af751054c10004ff7650c1001cfe7650c10004f
  | 2 => 0x6df638c51000edc638c510006ef628c510006ec628c510005f6768c51004ef6768c51021df7758c51021df5758c51000777658c51021774658c510005f7748c510005f5748c510007b7648c510007b4648c51021777548c51000775548c51003df5738c510007d7638c51000ef6638c51000ef4638c51003fd4638c51000ed4638c51003f77538c51003f75538c51003fd6438c510007d5438c510005f6728c510007e7628c510007e4628c51000776528c51021774528c51001df6708c51001df4708c51020fd6308c51020fd4308c51001cfc764c5100067f654c51011e7c654c510006bf644c510116bc644c510006df634c51000edc634c510006ef624c510006ec624c510005fb704c51001df8704c51001df4764c51000ef4764c51001cf4764c510205f7754c510205f5754c51000777654c5101ff74654c510005f7744c510005f5744c510007b7644c510007b4644c5101ff77544c51000775544c51003df7734c510007d7734c510007d7634c51000ef6634c51000ef4634c51003fd4634c51003f77534c51003f75534c510005f4724c510007e7624c510007e4624c51000776524c5101ff74524c510007f3704c51001df6704c51001df4704c510007f0704c51001cfe76c85100067f65c85100ee7c65c8510006df63c851010edc63c8510006ef62c8510066ec62c851001dfa70c8510005f970c851001df676c8510006f676c851001cf676c85101ddf775c85101ddf575c85100077765c85101f77465c8510005f773c8510005f573c8510007d763c851010ef663c851010ef463c8510007d463c851010ed463c85101f77753c85100077553c8510006f762c8510007e762c8510006f562c8510007e462c85101d77652c85101d77452c851001df670c8510007f270c851001df270c8510007f170c851001df470c8510004fe76885100457e75885100057d75885100067f65885100e67c6588510006df6388510106dc6388510006ef6288510006ec62885101ef6c52885101e5f6718851001cfc76485100057f75485100457c75485100067f65485100fe7c6548510006df63485100f6dc6348510006ef6248510006ec6248510005fb704851001df87048510004fe76085100067f65085100de7c6508510006df63085100d6dc6308510006ef6208510066ec62085101cf6c5208510005f67608510006f676085101e5f775085101e5f575085100077765085101cf746508510005f77308510005f57308510007d763085100d6f663085100d6f46308510007d463085100d6d463085101cf7753085100077553085101ddf67208510007e67208510006f76208510007e76208510006e76208510006f56208510007e462085101cfe752085101d77652085101d77452085101cfe452085101cf645208510007e63208510007e5320
  | 3 => 0x77158910004ff7058910006fb7058910004fe76189100457c75189100067f65189100067c6518910006df6318910006dc6318910006ed62189100076c5218910064ff75189100667f7518910014fe7518910004fd7518910064fc75189100667c75189100647c751891000cfe7318910004fd7318910064fc73189100067f53189100067d5318910066ee7218910006ef5218910066ee5218910006ed52189100667c5218910066ec52189100666c5218910006ef3218910066ec3218910104fe7118910064fc711891001cfe701891001cfc7018910005ee7618910006ee7618910004ee76189100076f75189100076c7518910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d53189101c7e77118910007e65118910007e551189101c7e610189101c7e41018910066ef75189100666f7518910006ee7518910006ed7518910066ec75189100666c7518910066ef7318910006ee7318910006ed7318910066ec7318910006ef53189100066f5318910006ee5318910006ed53189100066d5318910006ec5318910006ee4318910006ed4318910006ec4318910066ef7118910006ed7118910006ef5118910006ee5118910006ed5118910006ec5118910006ef3118910006ec3118910066ef70189101c6ee7018910006ed7018910066ec7018910006ef50189101c6ee5018910006ed50189101c6ec5018910006ef30189101c6ee30189101c6ec30189101c6ee1018910006ed10189101c6ec10189100667f76949100057e76949100067e76949100047e76949100067d76949100057c76949100667c76949100647c76949100057d73949100067f63949100075f63949100065f63949101567e63949100067d63949101567c63949100075c63949101565c63949100457e72949100476e72949100067f62949100076f62949100066f62949100667e62949100067d62949100667c62949100076c62949100666c62949101d77771949101d774719491019f761094910064ff768c910004fe768c910004fd768c910064fc768c9100057f758c9100457c758c9100067f658c91014e7c658c910006bf648c910146bc648c910006df638c91000edc638c910006ef628c910066ec628c910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100457c754c9100067f654c91013e7c654c910006bf644c910136bc644c910006df634c91000edc634c9100075d534c910006ef624c910006ec624c910005f7714c910005f4714c91004cfe768c5100067f658c51012e7c658c510006bf648c510126bc648c510
  | 4 => 0x4d10007767154d10007757154d101af761054d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100457e7550d100057d7550d100067f6550d1015e7c6550d10006df6350d1000edc6350d1003f9c4350d100457e75d89100057d75d89100067f65d89100067c65d8910006df63d8910006dc63d89100076c52d8910004ff75d8910014fe75d89100067e75d89100147e75d8910004fd75d89100067d75d89100047d75d8910014fc75d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006ef52d8910006ee52d8910006ed52d89100067c52d8910006ec52d89100066c52d8910006ef32d8910006ec32d8910006f571d89100076e75d89100076d75d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d8910007e571d8910007e651d8910007e551d8910227e610d8910227e410d8910006ef75d8910006ee75d89100066e75d8910006ed75d89100066d75d8910006ec75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d8910226ef71d8910006ed71d8910006e571d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef31d8910006ec31d8910006ef70d8910226ee70d8910006ed70d8910226ec70d8910006ef50d8910226ee50d8910006ed50d8910226ec50d8910006ef30d8910226ee30d8910226ec30d8910226ee10d8910226ec10d89100457e75989100057d75989100067f65989100067c659891003dde7398910005dd7398910006df6398910006dc6398910006ef6298910064ff7598910014fe75989100667e75989100147e7598910004fd75989100667d75989100047d7598910064fc759891000cfe7398910066de739891000cde7398910004fd7398910066dd7398910004dd7398910064fc73989100067f53989100067d5398910064fe7298910004ee72989100667c5298910004fd7198910066f57198910004fd7098910066f970989100057f75589100457c75589100067f65589100067c6558910005df735891003ddc7358910006df6358910006dc6358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7358910006df7358910004df735891000cfe735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006ef72589100067c5258910004ff7158910006f
  | 5 => 0xcde76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dc64d8d100075f54d8d100075c52d8d1020fd771d8d10007d651d8d10007d551d8d1020fd610d8d1020fd410d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d100065f54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d100065c52d8d10006df42d8d10006dc42d8d1020edf71d8d1003ede71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df70d8d1020ede70d8d10006dd70d8d1020edc70d8d10006df50d8d1020ede50d8d10006dd50d8d1020edc50d8d10006df40d8d1020ede40d8d1020edc40d8d1020ede20d8d1020edc20d8d1020ede10d8d1020edc10d8d100057f7558d100457c7558d100067f6558d100067c6558d10005bf7458d10235bc7458d10006bf6458d1003edc6358d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d100bcfe7458d100bcfc7458d10006bc7458d100bcbc7458d100067f5458d1003cff7358d10006df7358d1003e7f5358d10004ff7258d10006ef7258d10004ef7258d10064fc7258d10006ec7258d10004ec7258d100067c5258d1004cff7158d10006f77158d1005cff7058d10006fb7058d10005de7618d1003ede7618d10004de7618d1003f5e7518d1003f5d7518d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d100075f5418d100075c5218d1003fd57118d1022edf6118d10007d65118d10007d55118d1022fd61018d1022fd41018d100067f7654d100057e7654d100067e7654d100047e7654d100067d7654d100057c7654d100067c7654d100047c7654d100057f7454d100067f6454d100073f6454d100063f6454d101667e6454d100067d6454d101667c6454d100073c6454d101663c6454d1003d7f7354d100475f7354d1003e7f6354d100075f6354d100065f6354d1000e7e6354d1003e7d6354d1000e7c6354d1003f5c6354d1000e5c6354d100057c7254d1003f5f325
  | 6 => 0xc7558a100147c7558a10004ff7358a1000cfe7358a1000cfc7358a100067f5358a100067d5358a1001eef7258a10006ef5258a100067c5258a10006ec5258a100066c5258a1001cfc7058a1001eee2058a1001eec2058a100667f7694a1019e7e7694a100067d7694a100667c7694a100057d7394a1019e7f6394a101567e6394a100067d6394a1019e7c6394a101a57e7294a100576e7294a1019e7f6294a100667e6294a100067d6294a100667c6294a100467d6194a1019e7e6094a1019f771094a10064ff768ca1001cfe768ca10004fd768ca1001cfc768ca100057f758ca100557c758ca10066ee628ca10006ed628ca10004ff764ca1001cfe764ca10004fd764ca1001cfc764ca100057f754ca100557c754ca100075d534ca10006ee624ca10006ed624ca10005f7714ca10005f4714ca1003cfd768c61020edf638c61000edc638c61000cff764c61001cfc764c61000ede634c610006dd634c610005fb704c61001df8704c610066ee62c8610006ed62c861001dfa70c8610005f970c86100557e75886100057d7588610226ef6288610226ec62886102576c52886100057f75486100557c7548610006ee6248610006ed6248610005fb704861001df870486101c6ef6208610066ec620861024f6c520861001df976c4210006f976c42102477b53c42100077953c42100077a52c42102477852c421001ff271c4210247f251c4210247f151c42100457e76d95100467e76d95100147e76d95100057d73d95100067e63d95100067c63d95100057e72d951023f7771d95100477471d951023f7610d951023f7410d95100067f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100647e72d95100067d72d95100067c72d95100067f32d95100067c32d951023e7f71d95100467e71d95100467d71d95100467c71d95100067f31d95100067c31d95100067f70d951023e7e70d95100467d70d951023e7c70d95100067f30d951023e7e30d951023e7c30d951023e7e20d951023e7c20d951023e7e10d95100467d10d951023e7c10d951000cfe76d8d100457c75d8d100067f65d8d100067c65d8d1003ede63d8d100075f53d8d10004ff75d8d100067f75d8d10014fe75d8d10004fd75d8d10014fc75d8d100067c75d8d100147c75d8d100bcfe74d8d10004fd74d8d100bcfc74d8d100067f54d8d1003e7f53d8d10006df53d8d100065f53d8d1003ede53d8d10006dd53d8d1003edc53d8d10006df43d8d1003ede43d8d1003edc43d8d10064fe72d8d10004fd72d8d100067c52d8d1003edf32d8d1003edc32d8d1000cfe71d8d1001cfd71d8d1000cfc71d8d1003edf31d8d1001cfe70d8d1003cfd70d8d1001cfc70d8d1003edf30d8d1003dde76d8d10
  | 7 => 0xc710026f7764c710285f7754c710285f5754c710005f7744c710005f5744c71027f77544c71000775544c710007d7734c71000ef6634c71000ef4634c71005f77534c71005f75534c710005f4724c71000776524c71027f74524c71001df6704c71001df4704c710005f576c8710006f576c8710275f775c8710275f575c8710005f773c8710005f573c871010ef663c871010ef463c87101977753c87100077553c8710006f762c8710006f562c871025f7652c871025f7452c871001df670c871001df470c871001cfd76887100357e75887100057d7588710006ee6288710006ed628871026f6c528871001dfa7088710005f970887100057f75487100357c754871001cfd7608710066ee6208710006ed620871017f6c520871001dfa7008710005f9700871001df57608710006f5760871001cf57608710265f77508710265f57508710005f77308710005f573087100d6f663087100d6f4630871017f775308710007755308710007e67208710006f76208710007e66208710006f56208710007e5620871017fe7520871025f76520871025f74520871017fe4520871017f645208710007e63208710007e5320871001df67008710007f27008710007f1700871001df470087101c7e620087101c7e4200871000cff764c31000cfc764c31000ede634c310006dd634c310005f7714c310005f4714c310066ee62c8310006ed62c8310005f671c8310005f571c83100057f75483100357c7548310006ee6248310006ed6248310005f77148310005f47148310004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e100bcfe7458e100bcfc7458e100067f5458e1001edf7358e1004e7f5358e1004ede4358e10004ff7258e10064fc7258e100067c5258e1004edf3158e1001cfc7058e1001ede3058e1001edc3058e1001ef71058e1001ef51058e100067f7654e101ae7e7654e100067d7654e101ae7c7654e100057f7454e101ae7f6454e101667e6454e100067d6454e101ae7c6454e101b57f7354e100575f7354e101ae7f6354e1000e7e6354e1004e7d6354e1000e7c6354e100057c7254e101ae7f6254e101ae7c6254e1004f5f3254e1003e7d6154e101ae7e6054e101af771054e10004ff7650e1001cfe7650e10004fd7650e1001cfc7650e100557e7550e100057d7550e1000ede6350e10006dd6350e1004f9c4350e10064ff7598a10014fe7598a10004fd7598a10064fc7598a1000cfe7398a10004fd7398a10064fc7398a100067f5398a100067d5398a1001eee7298a10006ef5298a100667c5298a10066ec5298a100666c5298a1001cfe7098a1001eee2098a1001eec2098a1001ef71098a1001ef51098a10004ff7558a100067f7558a100047f7558a10014fe7558a10004fd7558a10014fc7558a100067
  | 8 => 0x5e7f5358f10004ff7258f10064fc7258f100067c5258f1001cfc7158f1005edc3158f1005edf3058f100067f7654f100067e7654f100067d7654f100067c7654f100057f7454f100067f6454f101667e6454f100067d6454f101667c6454f1005d7f7354f100375f7354f1005e7f6354f1000e7e6354f1005e7d6354f1000e7c6354f100057c7254f1005f5f3254f10007767154f10007757154f10004ff7650f10004fe7650f10004fd7650f10004fc7650f100357e7550f100057d7550f10006df6350f1000edc6350f1005f9c4350f100357e75d8b100057d75d8b10004ff75d8b10014fe75d8b100067e75d8b100147e75d8b10004fd75d8b100067d75d8b100047d75d8b10014fc75d8b1000cfe73d8b10004fd73d8b1000cfc73d8b100067f53d8b100067d53d8b100067c52d8b10006f671d8b10006f970d8b10226ee20d8b10226ec20d8b10004fd7698b10006ef6298b10064ff7598b10014fe7598b10004fd7598b10064fc7598b1000cfe7398b10004fd7398b10064fc7398b100067f5398b100067d5398b100667c5298b100057f7558b100357c7558b10004ff7558b100067f7558b100047f7558b10014fe7558b10004fd7558b10014fc7558b100067c7558b100147c7558b10004ff7358b1000cfe7358b1000cfc7358b100067f5358b100067d5358b10006ef7258b100067c5258b10006f47158b10006ed6218b10064ff7518b10014fe7518b10004fd7518b10064fc7518b1000cfe7318b10004fd7318b10064fc7318b100067f5318b100067d5318b10064fe7218b10066ee7218b100667c5218b10066f67118b10066f97018b101c6ee2018b10066ec2018b100667f7694b100067e7694b100067d7694b100667c7694b100057d7394b100067f6394b101567e6394b100067d6394b101567c6394b100357e7294b100376e7294b100067f6294b100667e6294b100067d6294b100667c6294b1025f777194b1025f747194b10064ff768cb10004fe768cb10004fd768cb10064fc768cb100057f758cb100357c758cb10006ef628cb10066ec628cb10004ff764cb10004fe764cb10004fd764cb10004fc764cb100057f754cb100357c754cb100075d534cb10006ef624cb10006ec624cb10005f7714cb10005f4714cb1001cfd768c71000ede638c710006dd638c71001dfa708c710005f9708c71001df5768c71000ef5768c71001cf5768c710295f7758c710295f5758c710005f7748c710005f5748c71028f77548c71000775548c71000ef6638c71005fd6638c710007d5638c71000ef4638c71005f77538c71005f75538c71005fd6438c710007d5438c710005f6728c71000776528c71028f74528c71001df6708c710007f2708c710007f1708c71001df4708c71020fd6308c71020fd4308c710024ff764c710005f7764
  | 9 => 0xe7254c200657c7254c200a67e6254c2006f5f3254c201ae7e6054c201af6f2054c201af7a2054c201af6d2054c20004ff7650c2001cfe7650c20004fd7650c2001cfc7650c200757e7550c200057d7550c2000ede6350c20006dd6350c2006f9c4350c20005fb7050c2001df87050c200a4ff764c8200057f754c8200757c754c8200075d534c8200a6ee624c820067cc324c820005f7714c820005f4714c820004ff7598420014fe7598420004fd7598420014fc759842000cfe7398420004fd739842000cfc73984200067f53984200067d53984200667e52984200667c529842001ef67198420006f65198420006f55198420066f72198420066f4219842001ef6109842001ef41098420004ff75584200067f75584200047f7558420014fe7558420004fd7558420014fc75584200067c75584200147c7558420004ff735842000cfe735842000cfc73584200067f53584200067d53584200667e52584200667c525842001ef77158420006f65158420006f55158420066f72158420066f4215842001ef6105842001ef41058420004ff768c42001cfe768c420004fd768c420006f6618c420006f5618c420004ff764c420004fd764c42001cfc764c42000ede634c420006dd634c420005ef724c420065ec724c420006f6614c420006f5614c420004fd76884200757e75884200057d75884200676e52884200676c5288420225ed7688420006ed76884202b76e75884200076d75884200e6ee6588420226ec6588420226ef6388420006ed63884202b76f53884200076d5388420065ee7188420006ed6188420225ed7088420226ee6088420227ea6088420004ff76484200057f75484200757c75484200deee6508420066ec6508420066ef6308420006ed63084202af6f53084200076d5308420225ee7108420067e67108420067e66108420006ed6108420067e561084202a7e731084202a7e43108420067ea70084201c5ed7008420067e97008420005e970084201c6ee6008420067ea600842001dfb7648020006fb7648020004fb76480200077b754802029f78754802029f7b534802000779534802001dfb724802001feb7248020066fa624802001fea62480200677a5248020067ea52480200676a524802029fe95248020067785248020067eb2148020007e9214802005ede63d8f10004ff75d8f10014fe75d8f10004fd75d8f10014fc75d8f100bcfe74d8f10004fd74d8f100bcfc74d8f100067f54d8f1005cfd73d8f1005e7f53d8f1005ede43d8f10064fe72d8f10004fd72d8f100067c52d8f10006f671d8f10006f970d8f1020ede30d8f1020edc30d8f1000cff7658f1005edc6358f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f100bcfe7458f100bcfc7458f100067f5458f10006df7358f10
  | 10 => 0xc9202cfcd534c9200074d534c920087ce434c920007cd434c920007e7714c920007e4714c920007eb704c92001dee704c92001dec704c920007e8704c9200067f65d85200067c65d8520004ff75d8520014fe75d8520004fd75d8520014fc75d852000cfe73d8520004fd73d852000cfc73d85200067f53d85200067d53d85200067e52d85200067c52d8520006f731d8520006f431d852008d7e75985200057d75985200067f65985200067c6598520006f761985200057f755852008d7c75585200067f65585200067c6558520005df7358520085dc73585200067f65185200067c6518520006f56118520004ff7518520014fe7518520004fd7518520014fc751852000cfe7318520004fd731852000cfc73185200067f53185200067d53185200067e52185200067c5218520006ee3218520006ed3218520006f73118520006f4311852001cfe701852001cfc70185201c6ee20185201c6ec2018520004fe768c520004fd768c520004fc768c5200067f658c52012e7c658c520006df638c52000edc638c520004ff764c520004fe764c520004fc764c5200067f654c52011e7c654c520004fe76c85200067f65c85200ee7c65c852001cfe768852008d7e75885200057d75885200067f65885200e67c65885202c76c5288520006f76188520006f4618852001dfa7088520005f9708852001cfc76485200057f754852008d7c75485200067f65485200fe7c6548520006f76148520006f46148520005fb704852001df87048520004fe76085200067f65085200de7c65085200676c520852000cff764c120084fd764c12000cfc764c1200067f654c1200b67c654c120006df634c12000edc634c120005ef724c120005ec724c1200067f65c812007e7c65c812001dee72c812001eef62c81200077b65c81202bf7865c81202bf7b53c81200077953c812001dfa72c812001efb62c812001feb62c81200677a52c81200677852c8120067ea32c8120007e932c8120004ff7558c20014fe7558c20004fd7558c20014fc7558c20004ff7458c200bcfe7458c200bcfc7458c200067f5458c2001cff7358c2001edf7358c2006e7f5358c2006ede5358c20006dd5358c2006ede4358c2000cff7258c20064fe7258c2000cfd7258c20064fc7258c200667e5258c200667c5258c20066de3258c20066dc3258c20004ff7158c20004fc7158c2006edf3158c2001cfe7058c2001cfc7058c2001ede3058c2001edc3058c2001eef2058c2001eed2058c200067f7654c201ae7e7654c200067d7654c201ae7c7654c200057f7454c201ae7f6454c201667e6454c200067d6454c201ae7c6454c201b57f7354c200775f7354c201ae7f6354c2000e7e6354c201af5e6354c2000e5e6354c2006e7d6354c201af5d6354c200065d6354c2000e7c6354c200657
  | 11 => 0x14fc75d8d200067c75d8d200147c75d8d200bcfe74d8d20004fd74d8d200bcfc74d8d200067f54d8d200867f53d8d20006df43d8d20086dc43d8d20064fe72d8d2001cfd72d8d20064fc72d8d200067c52d8d20086df32d8d20004fe71d8d20004fd71d8d20086dc31d8d20084fd70d8d20086df30d8d200057f7558d2008d7c7558d200067f6558d200067c6558d20005bf7458d202ddbc7458d20086dc6358d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d200bcfe7458d200bcfc7458d20006bc7458d200bcbc7458d200067f5458d20084ff7358d20006df7358d200867f5358d20086de4358d20094ff7258d20006ef7258d200067c5258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d200a4ff7058d20006fb7058d200067f7654d200057e7654d200067e7654d200047e7654d200067d7654d200057c7654d200067c7654d200047c7654d200057f7454d200067f6454d201667e6454d200067d6454d201667c6454d200857f7354d2008f5f7354d200867f6354d2000e7e6354d200867d6354d2000e7c6354d200657c7254d200875f3254d201af6e2054d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2008d7e7550d200057d7550d200067f6550d2015e7c6550d2000ede6350d20006dd6350d200879c4350d200057e76949200667e769492009c7e76949200057d73949200067f63949201567e63949200067d63949201567c63949200657e72949200676e72949200667f62949200667f609492019f6e20949200676c2094920094fe768c9200657f758c9200657c758c9200067f658c92014e7c658c9200676e528c9200676c528c920005ee768c920096ee768c9200676f758c9200676c758c9200076f658c9202d76c658c920005ef748c920005ed748c920006ef648c920006ed648c9202d76f548c9200076d548c920085ed738c92000eee638c92000eec638c9200876f538c9200876d538c92001dee708c92001dec708c920066ef608c92001cfc764c9200057f754c92008d7c754c9200067f654c92013e7c654c920006df634c92000edc634c9200075d534c9200076e524c9202cf6c524c920005f7714c920005f4714c920005fb704c92001df8704c92001dec764c92000eec764c92001cec764c9200076f754c9202cf6c754c9200076f654c9202cf6c654c920005ef744c920005ed744c920006ef644c920006ed644c9202cf6f544c9200076d544c920085ef734c920007cf734c920007cf634c92000eee634c92000eec634c920087cc634c92000ecc634c9200876f534c920087ce534c9200876d534
  | 12 => 0x55358620006f45358620006f64358620006f54358620006f44358620006f57258620006f75258620006f65258620006765258620006f55258620006f45258620006745258620006f73258620006f63258620006f53258620006f4325862001ef7705862001ef6705862001ef4705862001ef7505862001ef6505862001ef5505862001ef4505862001ef7305862001ef6305862001ef5305862001ef4305862001ef7205862001ef6205862001ef5205862001ef42058620004ff768c62001cfe768c620004fd768c62012e7e658c6200067d658c620006f6618c620006f5618c620004ff764c620004fd764c62001cfc764c62011e7e654c6200067d654c620005ef724c620005ec724c620006f6614c620006f5614c6200ee7e65c86200067d65c8620006f661c862009d7e75886200057d75886200e67e65886200067d65886200076e52886202ff6c5288620006f66188620006f5618862001dfa7088620005f970886202ff6e75886200076d75886200e6ee65886202276e65886200e66e65886202276d6588620226ec6588620226ef6388620006ed63886202ff6f53886200076d5388620227e66188620006ed6188620227e56188620227ea7088620225ed7088620007e970886200057f754862009d7c75486200fe7e65486200067d6548620006f66148620006f56148620005fb704862001df870486200de7e65086200067d65086200676e52086200676c5208620006f561086201c5ed7608620006ed76086200deee65086201c76e65086200de6e65086201c76d65086201c6ec65086201c6ef6308620006ed63086202f76f53086200076d5308620007e671086201c7e66108620006ed61086201c7e56108620006e561086202efe731086202efe431086201c5ed700862001df976c8220066f976c822001f7a65c822001f7965c82202e77b53c82200077953c822001fea72c82200677a52c82200677852c822001ff261c822001ff161c822008d7e76d952008e7e76d95200147e76d95200057d73d95200067e63d95200067c63d95200657c72d952019f6e20d952019f6c20d95200067f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067e43d95200067c43d952019e7f72d952008e7e72d95200647e72d952008e7d72d952008e7c72d95200647c72d95200067f32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067c31d95200067f70d952019e7e70d952008e7d70d952019e7c70d95200067f30d952019e7e30d952019e7c30d952019e7e20d952008e7d20d952019e7c20d952019e7e10d952019e7c10d952000cfe76d8d2008d7c75d8d200067f65d8d200067c65d8d20086de63d8d20004ff75d8d200067f75d8d20014fe75d8d20004fd75d8d20
  | 13 => 0x8e2001ede3058e2001edc3058e2001eef2058e2001eed2058e201ad7f7654e200067f7654e200047f7654e201ae7e7654e201ad7d7654e200067d7654e200047d7654e201ae7c7654e200057f7454e201ae7f6454e201667e6454e200067d6454e201ae7c6454e201b57f7354e2009f5f7354e201ae7f6354e2000e7e6354e200967d6354e2000e7c6354e200657c7254e200867d6254e200975f3254e201af766154e201af756154e201ae7e6054e201af6f2054e20004ff7650e2001cfe7650e20004fd7650e2001cfc7650e2009d7e7550e200057d7550e2015e7e6550e200067d6550e2000ede6350e20006dd6350e200979c4350e2019d7d7694a200667d7694a2008c7d7694a200057d7394a2019e7f6394a201567e6394a200067d6394a2019e7c6394a200657e7294a200676e7294a2019f766194a2019f756194a200667e6094a200676f2094a20067782094a20084fd768ca200657f758ca200657c758ca2014e7e658ca200067d658ca2000cff764ca2001cfc764ca200057f754ca2009d7c754ca2013e7e654ca200067d654ca2000ede634ca20006dd634ca200075d534ca20097cc324ca20005f7714ca20005f4714ca20005fb704ca2001df8704ca20004ff7598620014fe7598620004fd7598620014fc759862000cfe7398620004fd739862000cfc73986200067f53986200067d53986200067e52986200067c529862001ef67198620006f75198620006f65198620006f55198620006f45198620006f73198620006f4319862001ef6109862001ef41098620006f77598620006f67598620006f57598620006f47598620006f77398620006f67398620006f57398620006f47398620006f75398620006775398620006f65398620006f55398620006755398620006f45398620006f64398620006f54398620006f44398620006f77298620006f75298620006f65298620006765298620006f55298620006f45298620006745298620006f73298620006f63298620006f53298620006f4329862001ef6709862001ef5709862001ef4709862001ef7509862001ef6509862001ef5509862001ef4509862001ef7309862001ef6309862001ef5309862001ef4309862001ef7209862001ef6209862001ef5209862001ef42098620004ff7558620014fe7558620004fd7558620014fc7558620004ff735862000cfe735862000cfc73586200067f53586200067d53586200067e52586200067c525862001ef77158620006f75158620006f65158620006f55158620006f45158620006f73158620006f4315862001ef6105862001ef41058620006f77558620006f67558620006f57558620006f47558620006f77358620006f67358620006f57358620006f47358620006f75358620006775358620006f65358620006f553586200067
  | 14 => 0xede6350f20006dd6350f200a79c4350f20005fb7050f2001df87050f2001ded768cb20066ed768cb2001ced768cb200676f758cb200676c758cb20065ef748cb20005ed748cb20066ef648cb20006ed648cb2030f6f548cb200076d548cb2000eee638cb20067ce638cb20067cd638cb20066ec638cb200a76f538cb200a76d538cb2001dee708cb20067ea708cb20067e9708cb2001dec708cb2006cff764cb200057f754cb2007d7c754cb200075d534cb200676e524cb200676c524cb20005f7714cb20005f4714cb20005ef764cb2006eef764cb200076f754cb203076c754cb20005ef744cb20005ed744cb20006ef644cb20006ed644cb203076f544cb200076d544cb20067cf734cb2000eee634cb2000eec634cb200a76f534cb200a7ce534cb200a76d534cb20307cd534cb200074d534cb200a7ce434cb20007cd434cb20007e7714cb20007e4714cb2001dee704cb2001dec704cb2007d7e75987200057d7598720066f76198720004ff7598720014fe75987200067e75987200147e7598720004fd75987200067d75987200047d7598720014fc759872000cfe7398720004fd739872000cfc73987200067f53987200067d539872001cfe72987200667e52987200667c5298720006ee3298720006ed3298720066f72198720066f42198720226ee2098720226ec2098720066f46158720004ff7558720014fe7558720004fd7558720014fc7558720004ff735872000cfe735872000cfc73587200067f53587200067d535872001cfc72587200667e52587200667c5258720066f72158720066f42158720004ff768c720064fe768c720004fd768c72000ede638c720006dd638c720004ff764c720004fd764c720064fc764c72007d7e75887200057d75887200676c52887200057f754872007d7c754872000cff764c320064fc764c32000ede634c320006dd634c320005ef724c320065ec724c3200067f73596200047f73596200067e73596200067d73596200067c73596200067e43596200067c435962009e7f725962009e7e72596200067d725962009e7c72596200067f32596200067c32596200067f71596200067e71596200067d71596200067c71596200067f31596200067c315962001e7f705962001e7e705962001e7d705962001e7c705962001e7f305962001e7e305962001e7d305962001e7c305962001e7f205962001e7e205962001e7d205962001e7c205962001e7f105962001e7e105962001e7d105962001e7c1059620004ff7558e20014fe7558e200067e7558e200147e7558e20004fd7558e200067d7558e20014fc7558e20004ff7458e200bcfe7458e200bcfc7458e200067f5458e2001edf7358e200967f5358e20096de4358e200067c5258e20096df3258e20004ff7158e20004fc7158e2001cfc705
  | 15 => 0x77150930005f47150930004ff75d8530014fe75d8530004fd75d8530014fc75d85300bcfe74d8530004fd74d85300bcfc74d85300067f54d85300067d54d853001cfd73d853004e7f53d853004e7d53d8530064fe72d8530004fd72d85300067e52d85300067c52d853004ef631d853004ef531d8530006f7619853003df970985300057f75585300b57c7558530005bf74585300adbc7458530005ef7258530005ec725853005dfb70585300b57e75185300057d7518530006f56118530004ff7518530014fe75185300067e75185300147e7518530004fd75185300067d75185300047d7518530014fc75185300bcfe7418530004fd74185300bcfc74185300067f54185300067d541853001cfd73185300267f53185300267d5318530026de4318530006dd4318530064fe7218530004fd72185300067e52185300067c5218530026f63118530026f5311853022ede301853022edc3018530004fe7690530004fd7690530004fc7690530006bf64905300bebc64905300079d4390530004ff7650530004fe7650530004fc7650530004fe76c8530004fd76c8530064fc76c8530006f761c8530006f461c8530004fe7688530004fd7688530004fc76885300b57e75885300057d7588530006ef6288530006ec62885303276c5288530004ff7648530004fe7648530004fc76485300057f75485300b57c7548530004fe7608530004fd7608530064fc760853000dde7308530005dd7308530006ef6208530066ec620853031f6c5208530006f76108530006f4610853001dfa7008530005f9700853000cfe7650130314fd765013000cfc7650130005df735013000ddc73501300079d4350130064ff75d8f20014fe75d8f20004fd75d8f20064fc75d8f200bcfe74d8f20004fd74d8f20064fc74d8f200067f54d8f200a4fd73d8f200a67f53d8f20066ee72d8f200667e52d8f200667c52d8f20004fe71d8f20004fd71d8f20066f970d8f2000cff7658f20066dc6358f20004ff7558f20014fe7558f20004fd7558f20014fc7558f20004ff7458f200bcfe7458f200bcfc7458f200067f5458f20066df7358f200a67f5358f200a6de5358f20006dd5358f200a6de4358f2001cfc7258f200667e5258f200667c5258f20066de3258f20066dc3258f20004ff7158f20004fc7158f200a6dc3158f200a6df3058f200067f7654f200067e7654f200067d7654f200067c7654f200057f7454f200067f6454f201667e6454f200067d6454f201667c6454f200a57f7354f2007f5f7354f200a67f6354f2000e7e6354f200a75e6354f2000e5e6354f200a67d6354f200075d6354f200065d6354f2000e7c6354f200657e7254f200657c7254f200a75f3254f20004ff7650f20064fe7650f20004fd7650f20064fc7650f2007d7e7550f200057d7550f20
  | 16 => 0x913000cfe73d913001cfd73d913000cfc73d91303667f53d91303667d53d9130366bf43d9130366bd43d9130064fe72d9130004fd72d91300067c52d91300aebc42d9130004fe71d9130004fd71d91300aebc41d913000cfd70d91300aebf40d91300aebc645913035dfb7059130004ff7559130014fe7559130004fd7559130014fc7559130314ff7359130006df73591303167f5359130004ff7259130064fc72591300067c5259130004ff7159130004fc715913035cff7059130006fb70591300067f76551300067e76551300067d76551300067c76551303557f74551300b73f74551300ae7f64551300073f64551300063f64551300be7e64551300ae7d64551300be7c64551300af3c64551300be3c64551303457f73551303457d735513034e7f63551303475e43551300057c72551300af3f42551303467f60551303477b305513034f5e305513034f5c305513034778305513001ddc7650d300bedc7650d3001cdc7650d3033f5e7550d300075d7550d3000ddf7450d3000f9f7450d300079f6450d300bede6450d300bedc6450d300af9c6450d300be9c6450d300af5f5450d300af5d5450d3033f5c5250d300af9f4250d300af9c4150d30007db7050d3001dde7050d3001ddc7050d30007d87050d3000edf6050d3000fdb6050d300af9f4050d300b57e75d89300057d75d8930004ff75d8930014fe75d89300067e75d89300147e75d8930004fd75d89300067d75d89300047d75d8930014fc75d89300bcfe74d8930004fd74d89300bcfc74d89300067f54d89300067d54d893001cfd73d89300967f53d89300967d53d8930096de43d8930006dd43d89300067c52d8930096ee32d8930096ed32d8930004fe71d8930004fd71d8930006ef6298930085f970989300057f75589300b57c7558930005bf74589300adbc7458930005f77158930005f471589300a5fb7058930006ed6218930064ff7518930014fe7518930004fd7518930064fc75189300bcfe7418930004fd7418930064fc74189300067f54189300067d541893001cfd731893006e7f531893006e7d53189300667c5218930066ee321893006eed3218930004fe7118930004fd71189300667f76949300067e76949300067d76949300667c76949300057d74949300067f64949303367e64949300067d64949303367c64949301557f73949301557d739493019e7f63949301575e43949300075d439493032d7e72949300b76e72949300067f62949300667c62949301567f60949301577b309493019f5e309493019f5c3094930157783094930004fe7690930004fd7690930064fc76909300057f75909300b57c7590930006bf64909300bebc6490930004ff7650930004fe7650930004fc76509300057f75509300b57c75509300073d54509300079d4350930005f
  | 17 => 0x1eee2058a3001eec2058a300667f7694a3019e7e7694a300067d7694a300667c7694a300057d7494a3019e7f6494a303367e6494a300067d6494a3019e7c6494a301557f7394a301557d7394a301567d6394a301a57e7294a300cf6e7294a300667e6294a300067d6294a300667c6294a301575c3194a3019e7e6094a3019f5f3094a301577b3094a3019f783094a30064ff7690a3001cfe7690a30004fd7690a300057f7590a300cd7c7590a30066ee6290a30006ed6290a30004ff7650a30004fd7650a3001cfc7650a300057f7550a300cd7c7550a300073d5450a30005df7350a3000ddc7350a30006ee6250a30006ed6250a30005f77150a30005f47150a30004ff7598630014fe7598630004fd7598630014fc75986300bcfe7498630004fd74986300bcfc74986300067f54986300067d549863005e7f539863005e7d5398630064fe7298630004fd72986300067e52986300067c529863001ef67198630006f65198630006f5519863005ef6319863005ef5319863001cfe709863001ef6109863001ef41098630004ff75586300067f75586300047f7558630014fe7558630004fd7558630014fc75586300067c75586300147c7558630004ff7458630006bf7458630004bf74586300bcfe74586300bcfc7458630006bc74586300bcbc74586300067f54586300067d545863003e7f535863003e7d5358630004ff7258630006ef7258630004ef7258630064fc7258630006ec7258630004ec72586300067e52586300067c525863001ef77158630006f65158630006f5515863003ef6315863003ef5315863003edc315863001cfc705863001ef6105863001ef41058630004ff769063001cfe7690630004fd76906300bebc6490630006f66190630006f56190630004ff7650630004fd765063001cfc7650630005df735063000ddc7350630006f66150630006f5615063020edf648c630006dd648c63037f5f548c6300075d548c6300075e528c63037f5c528c63000dde718c63000fd6718c63020fd6618c630006dd618c63020fd5618c63020fda708c63020ddd708c630007d9708c63000ede608c63000fda608c630064ff76c863001cfe76c8630004fd76c863000dde73c8630005dd73c8630006f661c8630006f561c863010fd431c8630004ff768863001cfe7688630004fd76886300cd7e75886300057d75886303776c5288630004ff7648630004fd764863001cfc76486300057f75486300cd7c7548630005df734863000ddc7348630064ff760863001cfe7608630004fd760863036f6c5208630006f66108630006f561086300d7d4310863001dfa7008630005f970086300bcfe76d91300aebe64d9130004ff75d9130014fe75d9130004fd75d9130014fc75d91300ae7f54d91300aebe54d9130006bd54d913001cff73d
  | 18 => 0xe75884210057d75884213aded72884213a6ee62884210676c528842139f7675884210077575884210d5f673884210d5f4738842139f775388421007755388421065f57288421066f66288421067e6628842139fe75288421067765288421067745288421067e45288421067645288421067e63288421007e53288421005f57088421004ff76484210057f75484210dd7c75484210676e52484210676c5248421005ef7648421006ef7648421004ef76484210076f75484210ddee75484210ddec754842138f6c75484210dd6c7548421005ef7348421005ed734842138f6f53484210076d5348421065ef7148421396ee61484211c5ec7048421065f77648421006f77648421004f7764842100777754842138f7475484210d5f673484210d5f4734842138f775348421007755348421065f77248421007e77248421066f66248421067e66248421067765248421067745248421005f770484210676c5298021066fb609802101ef860980210057f75580210dd7c75580210676c5258021066f86058021004ff75580210067f75580210047f7558021014fe7558021004fd7558021014fc75580210067c75580210147c7558021004ff735802100cfe735802100cfc73580210067f53580210067d53580210667e52580210667c5258021006ee3258021006ed3258021006fa5058021006f95058021066fb2058021066f82058021004ff7559230014fe7559230004fd7559230014fc755923001ebf74592300c67f54592303167f53592303167d5359230316bf4359230316bd4359230004ff7259230064fc72592300067c5259230004ff7159230004fc7159230316dc315923001cfe705923001cfc705923001ebe405923001ebc405923001edf305923001edd30592300067f765523034e7e76552300067d765523034e7c76552303857f74552300cf3f745523034e7f64552300be7e64552300c67d64552300be7c64552303457f73552303457d73552303467d63552300057c72552300c73f42552303475c315523034e7e605523034f5f30552303477b305523034f783055230064ff7598a30014fe7598a30004fd7598a30064fc7598a300bcfe7498a30004fd7498a30064fc7498a300067f5498a300067d5498a300a67f5398a300a67d5398a3001eee7298a300667c5298a30066ee3298a300a6ed3298a30004fe7198a30004fd7198a3001cfe7098a3001cfc7098a3001eee2098a3001eec2098a30004ff7558a300067f7558a300047f7558a30014fe7558a30004fd7558a30014fc7558a300067c7558a300147c7558a30004ff7458a300bcfe7458a300bcfc7458a300067f5458a300067d5458a300867f5358a300867d5358a3001eef7258a300067c5258a30086ee3258a30086ed3258a30004ff7158a30004fc7158a3001cfc7058a30
  | 19 => 0x8c210d7d43158c21004ff7558c21014fe7558c21004fd7558c21014fc7558c21004ff7458c210bcfe7458c210bcfc7458c210067f5458c21066df7358c210d67f5358c210d6de5358c21006dd5358c210d6de4358c21064fe7258c21064fc7258c210667e5258c210667c5258c21066de3258c21066dc3258c210d4fc7158c210d6f47158c210d4f47158c210d6f73158c210d6dc3158c210d6f43158c21004ff7058c2101cfc7058c210d6df3058c210067f7654c210067e7654c210067d7654c210067c7654c210057f7454c210067f6454c211667e6454c210067d6454c211667c6454c210d57f7354c210df5f7354c210d67f6354c2100e7e6354c210d75e6354c2100e5e6354c210d67d6354c210075d6354c210065d6354c2100e7c6354c210076f7254c210657e7254c210657c7254c210076c7254c210656c7254c2110e7e6254c210d75f3254c21007777154c21007747154c211067e6154c213ff774154c213ff744154c210d7773154c210d7743154c211ae7e6054c21004ff7650c21064fe7650c21004fd7650c21064fc7650c210dd7e7550c210057d7550c2100ede6350c21006dd6350c210d79c4350c213f76c5250c21005f77150c21005f47150c210d7d43150c21065ed768c821066ed768c82100ced768c8210676f758c8210ddee758c821065ec758c8210676c758c8210656c758c821065ef748c821005ed748c821066ef648c821006ed648c8213ef6f548c8210076d548c8210d5ed738c82100eee638c821067ce638c821067cd638c821066ec638c8210d76f538c8210d76d538c821067e6718c821005ed718c821067e5718c821106ee618c8213e7e7418c8213e7e4418c8210d7e7318c8210d7e4318c8211c5ee708c82110cff764c8210057f754c8210dd7c754c8210075d534c8210676e524c8210676c524c821005f7714c8210d5f4714c821005ef764c82110eef764c8210076f754c8210ddee754c8210ddec754c8213df6c754c8210dd6c754c821005ef744c821005ed744c821006ef644c821006ed644c8213df6f544c8210076d544c821065ef734c821067cf734c82100eee634c82100eec634c8210d76f534c8210d7ce534c8210d76d534c8213dfcd534c8210074d534c8210d7ce434c821007cd434c821005ef714c821007e7714c821005e7714c8210d7e4714c821106ee614c8213d7e7414c8213d7e4414c8210d7e7314c8210d7e4314c8211c5ec704c821104ff768c421064fe768c42100cfd768c421064fc768c42100ede638c421006dd638c421065ee728c421005ed728c4213cf6c528c4210d5f6718c421104ff764c4213c76c524c4210d5f7714c4210ddee75c8421065ec75c8421065ef73c8421005ed73c84213bf6f53c84210076d53c84213b7e731c84213b7e431c84211c5ee70c84210dd7
  | 20 => 0x147c7558d21004ff7458d210bcfe7458d210bcfc7458d210067f5458d210f4ff7358d21006df7358d210f67f5358d21104ff7258d21006ef7258d210067c5258d2110cff7158d21006f77158d2110cf77158d21004ff7058d2101cfc7058d210067f7654d210057e7654d210067e7654d210047e7654d210067d7654d210057c7654d210067c7654d210047c7654d210057f7454d210067f6454d211667e6454d210067d6454d211667c6454d210f57f7354d210ff5f7354d210f67f6354d2100e7e6354d210f67d6354d2100e7c6354d210657c7254d210f75f3254d211ae7c6054d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210fd7e7550d210057d7550d210067f6550d2115e7c6550d21006df6350d2100edc6350d210f79c4350d210057e76949210667e76949210e47e76949210057d73949210067f63949211567e63949210067d63949211567c63949210657e72949210676e72949210667f62949210667f619492119e7c6094921104fe768c9210657f758c9210657c758c9210067f658c92114e7c658c92100cfc764c9210057f754c9210fd7c754c9210067f654c92113e7c654c921006df634c92100edc634c9210075d534c9210f7cc324c921005f7714c921005f4714c92110cfe768c5210067f658c52112e7c658c52100cff764c5210f4fd764c52100cfc764c5210067f654c52111e7c654c521006df634c52100edc634c521005ef724c521005ec724c5210067f65c85210ee7c65c85210077765c852140f7465c852110ef663c852110ef463c852140f7753c85210077553c85210677652c85210677452c85210fd7e75885210057d75885210067f65885210e67c65885210076e52885214076c52885214076e75885210076d75885210076f65885210e6ee65885210e6ec65885214076c65885210e66c6588521006ef6388521006ed63885214076f53885210076d5388521007e761885210067f65d81210067c65d8121004ff75d8121014fe75d8121004fd75d8121014fc75d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d81210067e52d81210067c52d8121006f721d81210fd7e75981210057d75981210067f65981210067c6598121006fb60981210057f75581210fd7c75581210067f65581210067c6558121005df73581210f5dc73581210067f65181210067c6518121226ef621812101efa6018121006f96018121064ff75d8c21014fe75d8c21004fd75d8c21064fc75d8c210bcfe74d8c21004fd74d8c21064fc74d8c210067f54d8c210d4fd73d8c210d67f53d8c21064fe72d8c21066ee72d8c210667e52d8c210667c52d8c21104fe71d8c21066f671d8c210d6f731d8c210d6f431d8c2101cfe70d8c21004fd70d8c2100cff7658c21066dc6358c210676c525
  | 21 => 0xd654ca21005ef744ca21005ed744ca21006ef644ca21006ed644ca2142f6f544ca210076d544ca21007cf734ca2100eee634ca21107ce634ca2100ece634ca21007cd634ca2100eec634ca211076f534ca21107ce534ca211076d534ca2142fcd534ca210074d534ca21107ce434ca21007cd434ca21005ef714ca21007e7714ca21007e4714ca21225ec704ca2100cfe768c62100cfd768c62112e7e658c6210067d658c62100ede638c621006dd638c621005ee728c621005ed728c6214276c528c6210d4ff764c62111e7e654c6210067d654c62141f6c524c6210ee7e65c86210067d65c86210676e52c86210676c52c8621005ed76c8621006ed76c86210e5ee75c86210e5ec75c86214176e65c86210076d65c8621005ef73c8621005ed73c86214176f53c86210076d53c8621417e651c8621417e551c8621225ee70c8621005f576c8621066f576c86214177665c86210077565c862110ef663c862110ef463c86214177753c86210077553c86210677652c8621067e652c86210676652c8621417e552c86210677452c86210e57e75d82210057d75d82210067e65d82210067d65d82210076c52d82210067e65982210067d65982210076c5298221006fb60982210067e65582210067d65582210076c5258221004ff7558221014fe7558221004fd7558221014fc7558221004ff735822100cfe735822100cfc73582210067f53582210067d53582210067e52582210067c5258221006ee3258221006ed3258221006f721582210e57e75182210057d75182210067e65182210067d65182210076c521822101efa6018221006f960182210fd7e76d95210fe7e76d95210147e76d95210057d73d95210067e63d95210067c63d95210657c72d95210067f73d95210067e73d95210067d73d95210047d73d95210067c73d95210067e43d95210067c43d95210067f72d95210fe7e72d95210fe7d72d95210fe7c72d95210067f32d95210067c32d95210067f71d95210fe7e71d95210fe7d71d95210fe7c71d95210067f31d95210067c31d95210fe7d21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f30d95210067c30d952100cfe76d8d210fd7c75d8d210067f65d8d210067c65d8d210f6de63d8d21004ff75d8d210067f75d8d21014fe75d8d21004fd75d8d21014fc75d8d210067c75d8d210147c75d8d210bcfe74d8d21004fd74d8d210bcfc74d8d210067f54d8d210f67f53d8d210f6de43d8d210f4fd72d8d210067c52d8d210f6df32d8d210f4fd71d8d210f6df31d8d2101cfe70d8d21004fd70d8d210f6dc30d8d210057f7558d210fd7c7558d210067f6558d210067c6558d210f6dc6358d21004ff7558d210067f7558d210047f7558d21014fe7558d21004fd7558d21014fc7558d210067c7558d21
  | 22 => 0x96210e67e72596210067d72596210e67c72596210e66c72596210067f32596210067c32596210e67f71596210067e71596210e67d71596210e67c71596210067f31596210067c31596210e67e21596210067f70596210067e70596210067d70596210067c70596210067f30596210067c30596210e57e75d8e210057d75d8e210067e65d8e210067d65d8e21106de63d8e210076c52d8e21004ff75d8e21014fe75d8e210067e75d8e210147e75d8e21004fd75d8e210067d75d8e210047d75d8e21014fc75d8e210bcfe74d8e21004fd74d8e210bcfc74d8e210067f54d8e21104fd73d8e211067f53d8e21106de43d8e21006ed72d8e210067c52d8e21006f671d8e2101cfe70d8e21004fd70d8e2100cff7658e210e57e7558e210067e6558e210067d6558e21106dc6358e210076c5258e21004ff7558e21014fe7558e210067e7558e210147e7558e21004fd7558e210067d7558e21014fc7558e21004ff7458e210bcfe7458e210bcfc7458e210067f5458e21006df7358e211067f5358e210067c5258e21106df3258e21106dc3158e21004ff7058e2101cfc7058e210057f7654e210067f7654e210047f7654e210067e7654e210057d7654e210067d7654e210047d7654e210067c7654e210057f7454e210067f6454e211667e6454e210067d6454e211667c6454e211057f7354e210e75f7354e211067f6354e2100e7e6354e211067d6354e2100e7c6354e210076f7254e210657c7254e210076c7254e210056c7254e210f67d6254e211075f3254e210d67e6154e211ae7e6054e21004ff7650e21004fe7650e21004fd7650e21004fc7650e210e57e7550e210057d7550e2115e7e6550e210067d6550e21006df6350e2100edc6350e211079c4350e2143f6c5250e210057d7694a210667d7694a210fc7d7694a210057d7394a210067f6394a211567e6394a210067d6394a211567c6394a210657e7294a210676e7294a210e56e7294a210667e6194a2119e7e6094a210f4fd768ca210657f758ca210657c758ca2114e7e658ca210067d658ca210676e528ca210676c528ca21005ed768ca210f6ed768ca210676f758ca210e5ee758ca210e5ec758ca210676c758ca210e56c758ca214376e658ca210076d658ca21005ef748ca21005ed748ca21006ef648ca21006ed648ca214376f548ca210076d548ca2100eee638ca2100eec638ca211076f538ca211076d538ca21005ed718ca21225ee708ca2100cff764ca210057f754ca210e57c754ca2113e7e654ca210067d654ca2100ede634ca21006dd634ca210075d534ca210076e524ca2142f6c524ca21005f7714ca21005f4714ca21105ef764ca2100eef764ca2100cef764ca210076f754ca210e5ee754ca210e5ec754ca2142f6c754ca210e56c754ca2142f6e654ca210076
  | 23 => 0x75e528c53144f5c528c53100dde718c53100fd6718c53100edf618c53100fd7618c531004ff75d8131014fe75d8131004fd75d8131014fc75d81310bcfe74d8131004fd74d81310bcfc74d81310067f54d81310067d54d813105e7f53d813105e7d53d8131064fe72d8131004fd72d81310067e52d81310067c52d813105efa30d8131006fb60981310057f755813111d7c7558131005bf7458131115bc7458131005ef7258131005ec725813111d7e75181310057d751813120edf631813101efa6018131006f96018131064ff75d8f21014fe75d8f21004fd75d8f21064fc75d8f210bcfe74d8f21004fd74d8f21064fc74d8f210067f54d8f2110cfd73d8f2110e7f53d8f21066ee72d8f210667e52d8f210667c52d8f21066f571d8f2110ef731d8f2110ef431d8f2101cfe70d8f21004fd70d8f2100cff7658f21066dc6358f2110fd73158f21004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f210bcfe7458f210bcfc7458f210067f5458f21066df7358f2110e7f5358f2110ede5358f21006dd5358f2110ede4358f210667e5258f210667c5258f21066de3258f21066dc3258f2110ef77158f2110edf3158f2110ef73158f2110ef43158f21004ff7058f2101cfc7058f2110edc3058f210067f7654f210067e7654f210067d7654f210067c7654f210057f7454f210067f6454f211667e6454f210067d6454f211667c6454f2110d7f7354f210ef5f7354f2110e7f6354f2100e7e6354f2110f5e6354f2100e5e6354f2110e7d6354f210075d6354f210065d6354f2100e7c6354f210657e7254f210657c7254f2110f5f3254f21007777154f21007747154f21447774154f21447744154f2110f773154f2110f743154f211ae7e6054f21004ff7650f21064fe7650f21004fd7650f21064fc7650f210ed7e7550f210057d7550f2100ede6350f21006dd6350f2110f9c4350f21005f77150f21005f47150f2110fd43150f210d4ff764cb210057f754cb210ed7c754cb210075d534cb21067cc324cb2110df7714cb21005f4714cb210f4fd768c72110df6718c72100cff764c721064fc764c72100ede634c721006dd634c721005ef724c721065ec724c72110df7714c7210ed7e75983210057d7598321066fb609832101ef86098321066f86058321004ff7558321014fe7558321004fd7558321014fc7558321004ff735832100cfe735832100cfc73583210067f53583210067d53583210667e52583210667c5258321066fb2058321066f820583210e57f76596210e67f76596210147f76596210057f73596210067e63596210067c63596210e76f72596210e76c72596210067f73596210047f73596210067e73596210067d73596210067c73596210067e43596210067c43596210e67f72596210e66f725
  | 24 => 0xc72582310067e52582310067c525823103efa305823120edc305823112d7e75182310057d751823101efa6018231006f960182310bcfe76d9131116be64d9131004ff75d9131014fe75d9131004fd75d9131014fc75d91311167f54d913146cff73d913146cfd73d913146e7f53d913146e7d53d913146ebf43d913146ebd43d9131064fe72d9131004fd72d91310067c52d913100cfd71d9131116bf41d913146edc31d913101cfe70d9131004fd70d9131116bc40d9131116bc6459131465f77159131004ff7559131014fe7559131004fd7559131014fc7559131454ff7359131006df73591314567f5359131004ff7259131064fc72591310067c5259131464ff7159131006f77159131456dc3159131004ff705913101cfc70591310067f76551310067e76551310067d76551310067c76551313557f745513111f3f74551311167f64551310be7e64551311167d64551310be7c64551313457f73551313457d73551313467f63551310057c72551311173f42551313467f61551313477731551313475c315513134774315513134e7c605513111d7e75d89310057d75d89310076c52d8931004ff75d8931014fe75d89310067e75d89310147e75d8931004fd75d89310067d75d89310047d75d8931014fc75d89310bcfe74d8931004fd74d89310bcfc74d89310067f54d89310067d54d89311067f53d89311067d53d8931006ef52d89310067c52d8931006ec52d89310066c52d8931106ee32d8931106ed32d893101cfe70d8931004fd70d8931006ef62989310f5f571989310057f755893111d7c755893110df77158931006ed62189310076c5218931064ff7518931014fe7518931004fd7518931064fc75189310bcfe7418931004fd7418931064fc74189310067f54189310067d54189310d67f53189310d67d5318931006ef52189310667c5218931066ec52189310666c5218931066ee32189310d6ed32189310d6f731189310d6f4311893101cfe7018931004fd70189310667f76949310067e76949310067d76949310667c76949310057d74949310067f64949313367e64949310067d64949313367c64949311557f73949311557d73949311567f639493132d7e729493111f6e72949310067f62949310667c62949311567f61949311577731949311575c319493115774319493119e7c6094931004fe7690931004fd7690931064fc76909310057f759093111d7c7590931006ef6290931066ec6290931004ff7650931004fe7650931004fc76509310057f755093111d7c75509310073d5450931006ef6250931006ec6250931005f77150931005f4715093145cfe76905310bebe649053100cfe7650531454fd765053100cfc7650531005df735053100ddc7350531006df648c531006dd648c53144f5f548c5310075d548c531
  | 25 => 0x92311267f54592314567f53592314567d5359231456bf4359231456bd4359231004ff7259231064fc72592310067c525923100cfc7159231126bc4159231004ff705923101cfc70592310067f76552310067e76552310067d76552310067c76552313557f745523112f3f74552311267f64552310be7e64552311267d64552310be7c64552313457f73552313457d73552313467d63552313475e43552310057c72552311273f42552313467e61552313475f315523134777315523134774315523134e7e60552313475c3055231125df7650e310bedf7650e310bcdf7650e314775e7550e310075d7550e3100ddf7450e3100f9f7450e310bede6450e311279e6450e310be9e6450e310079d6450e310bedc6450e311275f5450e311275d5450e314775c5250e311279f4250e31005df7150e31007d77150e31007d47150e3100ede6150e3100fd66150e311279c4150e3120ddc7050e311279f4050e3112d7e75d8a310057d75d8a310d5f671d8a31006ef6298a31064ff7598a31014fe7598a31004fd7598a31064fc7598a310bcfe7498a31004fd7498a31064fc7498a310067f5498a310067d5498a3110e7f5398a3110e7d5398a310667c5298a31066ee3298a3110eed3298a3110ef73198a3110ef43198a3101cfe7098a31004fd7098a310057f7558a3112d7c7558a31004ff7558a310067f7558a310047f7558a31014fe7558a31004fd7558a31014fc7558a310067c7558a310147c7558a31004ff7458a310bcfe7458a310bcfc7458a310067f5458a310067d5458a310f67f5358a310f67d5358a310f6de4358a31006dd4358a310067c5258a310f6ee3258a310f6ed3258a31004ff7058a3101cfc7058a31006ed6218a31105f67118a310667f7694a310067e7694a310067d7694a310667c7694a310057d7494a310067f6494a313367e6494a310067d6494a313367c6494a311557f7394a311557d7394a311567d6394a311575e4394a310075d4394a3132d7e7294a3112f6e7294a310667e6294a310067d6294a311567e6194a311575f3194a31157773194a31157743194a3119e7e6094a311575c3094a31064ff7690a31004fe7690a31004fd7690a310057f7590a3112d7c7590a31004ff7650a31004fd7650a31004fc7650a310057f7550a3112d7c7550a310073d5450a310079d4350a31005f77150a31005f47150a310bcfe769063100cfd769063100dde7390631005dd73906310079d4390631006fb60982310057f755823112d7c7558231004ff75582310067f75582310047f7558231014fe7558231004fd7558231014fc75582310067c75582310147c7558231004ff74582310bcfe74582310bcfc74582310067f54582310067d545823103e7f535823103e7d535823103ede4358231006dd4358231004ff7258231064f
  | 26 => 0x1cfe7018532004fd701853210df67618532006f67618532006f76518532007776518532006776518532006f66518532006f56518532006f46518532007746518532006746518532006f76418532006f66418532006f56418532006f464185320077754185320077554185320d77753185320d7d653185320d7755318532007d553185320075553185320d7d64318532007d543185320d7e77218532007765218532007745218532007e64218532007e542185320d7e73218532007d632185320d7d432185320d7e43218532006f77518532006f67518532006f57518532006f47518532006f77418532006f67418532006f57418532006f47418532006f75418532006775418532006f65418532006f55418532006755418532006f454185320d6f773185320d6f673185320d6f473185320d6f753185320d67753185320d6f653185320d6f553185320d67553185320d6f453185320d6f743185320d6f643185320d6d643185320d6f54318532006d543185320d6f443185320d6f772185320d6f57218532006f75218532006f65218532006765218532006f55218532006f45218532006745218532006f74218532006f64218532006e64218532006f54218532006e54218532006f442185320d6f732185320d6f632185320d6f532185320d6f43218532006f77018532006f67018532006f57018532006f47018532006f75018532006f65018532006f55018532006f45018532006f74018532006f440185320d6f730185320d6f630185320d6f530185320d6f430185320067f65d81320067c65d81320075d53d8132006f761d8132006f461d8132004ff75d8132014fe75d8132004fd75d8132014fc75d81320bcfe74d8132004fd74d81320bcfc74d81320067f54d81320067d54d81320a67f53d81320a67d53d81320a6de43d8132006dd43d81320067e52d81320067c52d8132006ee42d8132006ed42d8132004fe71d8132004fd71d8132006fb40d8132006f840d81320a6fa30d813213d7e75981320057d75981320067f65981320067c65981320075d5398132005f67198132005f57198132006f76198132006f46198132006fb60981320057f755813213d7c75581320067f65581320067c6558132005bf7458132135bc74581320075d5358132005f77158132005f47158132006f76158132006f461581320067f65181320067c65181320075d5318132006f76118132006f4611813201efa6018132006f96018132126be64d923145df671d9231004ff75d9231014fe75d9231004fd75d9231014fc75d923146e7f53d9231064fe72d9231004fd72d92310067c52d923145cfe71d9231006f671d923101cfe70d9231004fd70d92310bcff7659231126bc6459231004ff7559231014fe7559231004fd7559231014fc7559231006bf745
  | 27 => 0xf758c9320675f758c9320655f758c932485dd758c9320675c758c9320075f658c93247f5c658c932065df748c932005dd748c93247f5f548c9320075d548c932065de728c932067ce728c932066df628c93200fcf628c9320675e528c9320675c528c932067ce428c932007cd428c9320067f65d85320067c65d85320075d53d8532004ff75d8532014fe75d8532004fd75d8532014fc75d85320bcfe74d8532004fd74d85320bcfc74d85320067f54d85320067d54d853210e7f53d853210e7d53d853210eed72d85320067e52d85320067c52d8532006f751d8532006f651d8532006f551d8532006f451d8532006f741d8532006f441d853210ef631d853201cfe70d8532004fd70d8532006f765d85320077765d85320067765d8532006f665d8532006f565d8532006f465d85320077465d85320067465d8532006f764d8532006f664d8532006f564d8532006f464d85320077754d85320077554d853210f7753d853210fd653d853210f7553d8532007d553d85320075553d853210fd643d8532007d543d853210fe572d85320077652d85320077452d8532007e642d8532007e542d853210fe732d8532007d632d853210fd432d853210fe432d8532006f775d8532006f675d8532006f575d8532006f475d8532006f774d8532006f674d8532006f574d8532006f474d8532006f754d85320067754d8532006f654d8532006f554d85320067554d8532006f454d853210ef773d853210ef673d853210ef473d853210ef753d853210e7753d853210ef653d853210ef553d853210e7553d853210ef453d853210ef743d853210ef643d853210ef543d853210ef443d853210ef772d853210ef572d853210ee572d8532006f752d8532006f652d85320067652d8532006f552d8532006f452d85320067452d8532006f742d8532006f642d8532006f542d8532006f442d853210ef732d853210ef632d853210ef432d8532006f770d8532006f670d8532006f570d8532006f470d8532006f750d8532006f650d8532006f550d8532006f450d8532006f740d8532006f440d853210ef730d853210ef630d853210ef530d853210ef430d853213d7e75985320057d75985320067f65985320067c65985320075d5398532006f761985320057f755853213d7c75585320067f65585320067c65585320075d53585320067f65185320067c65185320075d5318532006f56118532004ff7518532014fe7518532004fd7518532014fc75185320bcfe7418532004fd74185320bcfc74185320067f54185320067d54185320d67f53185320d67d53185320d6de4318532006dd43185320067e52185320067c5218532006ee4218532006ed4218532006f75118532006f65118532006f55118532006f45118532006f74118532006f441185320d6f53118532
  | 28 => 0x51320be7e64551321367d64551320be7c64551323457f73551323475e73551323457d73551320075d73551323467f63551323475e43551320657c72551323467f62551321373f42551323476f32551323475c32551323476c325513234e7c605513213f5f7654d320165f7654d3213f5c7654d3213d5c7654d320165c7654d320145c7654d320075f7454d320055f7454d324df5e7454d320075d7454d324df5c7454d320075f6454d324df5e6454d320075d6454d324df5c6454d320075f7254d320074f7254d320075e7254d3213f5d7254d320075c7254d320655c7254d320074c7254d3200f5f6254d3200e5f6254d3200f4f6254d324df5f4254d324df5c4254d320075f7154d320075e7154d320075d7154d320075c7154d324df5f4154d324df5c4154d320075f7054d320075e7054d320075d7054d320075c7054d324df5f4054d324df5c4054d32135dc7650d320bedc7650d320bcdc7650d324d5df7550d324cf5e7550d324d5dd7550d320075d7550d320055d7550d320075f6550d324cf5c6550d3200ddf7450d3200f9f7450d320079f6450d320bede6450d320bedc6450d321379c6450d320be9c6450d321375f5450d321375d5450d32007cf7250d32065dc7250d32007cc7250d3200edf6250d3200fcf6250d324cf5c5250d321379f4250d321379c4150d321379f4050d3232d7e76949320667e769493232c7e76949320057d74949320067f64949323367e64949320067d64949323367c64949320657f73949320675f73949321557d73949320675c73949320667f63949321575e43949320075d43949320657e72949320676e72949320667f62949321576f32949320675c32949320676c32949320674c329493219e7c60949324bcfe76909320657f75909320657c75909320067f65909324c67c6590932065dc73909320075d53909320676e52909320676c5290932067cc32909324bdee76909324b6ee76909320676f75909320676c75909320076f65909324af6c659093248ded74909320beee64909320beec64909321376f54909321376d5490932067cf739093200dee739093200dec7390932067cc7390932066ef63909324a76f53909324a7ce53909324a76d53909324afcd53909320074d53909324a7ce4390932137cd4390932005ee7190932005ed709093200cfe765093248cfd765093200cfc76509320067f655093249e7c6550932005df735093200ddc73509320075d53509320079d43509320076e52509324976c525093248fcc32509320beec765093200cec76509320076f65509324976c6550932007cf735093200dee735093200dec735093248fcc735093248eef635093248f6f535093248fce535093248f6d5350932497cd53509320074d535093248fce4350932137cd43509320078d4350932065d
  | 29 => 0x4ff705863201cfc705863214d7e75982320057d75982320667f65982320667c6598232005f67198232005f57198232066fb609823201ef860982320057f755823214d7c75582320667f65582320667c6558232066f86058232004ff75582320067f75582320047f7558232014fe7558232004fd7558232014fc75582320067c75582320147c7558232004ff74582320bcfe74582320bcfc74582320067f54582320067d54582320867f53582320867d5358232064fc72582320667e52582320667c5258232006ee4258232004ff7158232004fc7158232086fa3058232066fb2058232066f8205823232d7e76d953213e7e76d95320147e76d95320057d74d95320067e64d95320067c64d95320075f73d95321575c73d95321575e43d95320657c72d95321576f32d95321575c32d95321576c32d95320067f74d95320067e74d95320067d74d95320047d74d95320067c74d95321567f73d95320647f73d95321567e73d95321567d73d95321547d73d95321567c73d95321567f43d95321567e43d95321567d43d95321567c43d95321567f72d953213e7e72d95321567d72d95321567c72d95320067f42d95320067c42d95321567f32d95321567e32d95321567d32d95321567c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067c41d95321567f31d95321567e31d95321567d31d95321567c31d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067c40d95321567f30d95321567e30d95321567d30d95321567c30d95320bcfe76d913213d7c75d91320067f65d91320067c65d9132136be64d9132004ff75d91320067f75d9132014fe75d9132004fd75d9132014fc75d91320067c75d91320147c75d91321367f54d9132064ff73d91324a4fd73d91324a67f53d91324a67d53d91324a6bf43d91324a6bd43d913200cfd72d91320067c52d9132136bf42d9132004fe71d9132004fd71d913201cfe70d9132004fd70d9132136bc40d91320057f755913213d7c75591320067f65591320067c6559132136bc64591324e5ef7259132005f77159132005f47159132005fb7059132005f87059132004ff75591320067f75591320047f7559132014fe7559132004fd7559132014fc75591320067c75591320147c755913248cff7359132006df735913248e7f53591324e4ff7259132006ef72591320067c5259132004ff7159132006f77159132004f77159132004fc7159132006f47159132004f47159132004ff7059132006fb7059132004fb705913201cfc7059132006f8705913201cf870591320067f76551320057e76551320067e76551320047e76551320067d76551320057c76551320067c76551320047c76551323557f745513213f3f74551321367f645
  | 30 => 0xc43d96320667e72d96320647e72d96320666e72d96320667f42d96320667c42d96320667f32d96320665f32d96320667e32d96320667c32d96320667f71d96320667e71d96320667d71d96320667c71d96320067f41d96320067c41d96321567f31d96321567c31d96320667f70d96320667e70d96320667d70d96320667c70d96320067f40d96320067c40d96321567f30d96321567c30d9632064ff75d92320667f75d9232014fe75d9232004fd75d9232064fc75d92320667c75d92320647c75d92324a67f53d9232064fe72d9232066ee72d92320667e52d92320667c52d9232066df32d9232004fe71d9232004fd71d923201cfe70d9232004fd70d92320bcff76592320057f755923214d7c75592320667f65592320667c6559232066bc6459232004ff75592320067f75592320047f7559232014fe7559232004fd7559232014fc75592320067c75592320147c7559232066bf74592321467f5459232146be5459232006bd545923248e7f535923248e7d535923248ebf435923248ebd4359232064fe7259232064fc72592320667e52592320667c5259232066be4259232066bc425923248edf3259232004ff7159232004fc7159232004ff705923201cfc70592320067f76552320657e76552320067e76552320647e76552320067d76552320657c76552320067c76552320647c76552323557f745523214f3f74552321467f64552320be7e64552321473e64552320be3e64552321467d64552320073d64552320063d64552320be7c64552323457f73552323457d73552323467d63552320657e72552320657c72552323467e62552321473f42552323475f32552323476f32552323476c325523234e7e6055232066ed7690a3200ced7690a320676f6590a320676c6590a3200dee7390a32067ce7390a32067cd7390a32065ec7390a324a76f5390a324a76d5390a3214d7e75986320057d75986320667f65986320667c6598632066f76198632004ff7598632014fe75986320067e75986320147e7598632004fd75986320067d75986320047d7598632014fc75986320bcfe7498632004fd74986320bcfc74986320067f54986320067d54986321067f53986321067d5398632064fe72986320667e52986320667c5298632006ee4298632106f53198632066f72198632066f4219863201cfe7098632004fd70986320057f755863214d7c75586320667f65586320667c6558632066f46158632004ff75586320067f75586320047f7558632014fe7558632004fd7558632014fc75586320067c75586320147c7558632004ff74586320bcfe74586320bcfc74586320067f54586320067d54586320f67f53586320f67d5358632064fc72586320f6ec72586320667e52586320667c52586320f6f63158632066f72158632066f42158632
  | 31 => 0x8e520057c7158e520667f6158e520667c6158e520057f7058e5219d7c7058e520667f6058e520667c6058e520067f7458e520047f7458e520067e7458e520067d7458e520067c7458e521567f4358e521567e4358e521565e4358e521567c4358e520667e7258e520647e7258e520667c7258e520647c7258e520067f4258e520667e4258e520667c4258e521567f3258e520667e3258e520665e3258e520667c3258e520665c3258e520067f7158e520067e7158e520067d7158e520067c7158e520067f4158e520067c4158e521567f3158e521567c3158e520667f2158e520667c2158e520067f7058e520067e7058e520067d7058e520067c7058e520067f4058e520067c4058e521567f3058e521567c3058e520667f2058e520667c2058e520057f7650e520657e7650e520067e7650e520057d7650e520067d7650e520047d7650e520657c7650e521557f7350e521575e6350e521567d6350e520075d6350e520065d6350e521573e4350e521575c4350e521571c4350e520057f7250e520657c7250e5232e7e6250e5215f6e6250e521575f3250e520057f7150e520057c7150e521575c3150e520057f7050e5219d7c7050e521575f3050e520657d76986521557e73986520057d73986521557c73986520667f63986520067d63986520657e72986520657c72986520667e62986520676e62986520e66e62986520657e71986520667f619865206777619865206774619865206777219865206774219865219d7e70986520057d70986520667c60986520657f76586520057f73586521557e73586521557c73586520667f63586520067d63586520657e72586520657c72586520667e62586520676e62586520657f71586520677761586520067e61586520667c61586520677461586520667461586520677721586520677421586520057f705865219d7c70586520667f60586520657d76982521557e73982520057d739825219d7c73982520667f63982520067d63982520657e72982520657c72982520667e62982520676e62982520057e719825219f7671982520057671982520057d719825219f7571982520057571982520067e61982520667c61982520657e70982520667f60982520677b60982520677860982520677b20982520677820982520657f76582520057f73582521557e73582521557c73582520667f63582520067d63582520657e72582520657c72582520667e62582520676e62582520057f71582520057c71582520667f61582520067d61582520657f70582520677b605825219e7e60582520667c60582520677860582520677b20582520677820582520667f74d96320667e74d96320667d74d96320047d74d96320667c74d96320667d73d96320665d73d96321567f43d96321567e43d96321567d43d96321567
  | 32 => 0x4e67f53d89434e67d53d89430067c52d89434e6ee32d8943004fe71d8943004fd71d894301cfe70d8943004fd70d894315d7c75989430067e65989430067d65989434a79c4398943006ef62989430057f755894315d7c75589430067e65589430067d655894348f9c4358943005f77158943005f47158943005fb7058943005f8705894315d7e75189430057d75189430067e65189430067d65189434bf9c4318943006ed6218943064ff7518943014fe75189430667e75189430147e7518943004fd75189430667d75189430047d7518943064fc75189430bcfd7318943066dd73189434be7f53189434be7d53189430667c5218943066df3218943066ee32189434beed3218943004fe7118943004fd711894301cfe7018943004fd701894315d7e75d85430057d75d85430067e65d85430067d65d85434679c43d8543005ee72d8543005ed72d8543004ff75d8543014fe75d85430067e75d85430147e75d8543004fd75d85430067d75d85430047d75d8543014fc75d85430bcfd73d85434f6dd73d85434667f53d85434667d53d8543064fe72d8543006ee72d8543004ee72d8543004fd72d8543006ed72d8543004ed72d85430067c52d8543466f631d8543466dc31d854301cfe70d8543004fd70d85430067e65985430067d659854346f9c4398543006f761985430067e65585430067d65585434579c435854315d7e75185430057d75185430067e65185430067d651854345f9c4318543006f56118543004ff7518543014fe75185430067e75185430147e7518543004fd75185430067d75185430047d7518543014fc75185430bcfd731854345e7f531854345e7d5318543064fe7218543004fd72185430067c521854345ef5311854301cfe7018543004fd701854301cfe76d814315d7e75d81430057d75d81430067e65d81430067d65d814335f9c43d8143004ff75d8143014fe75d81430067e75d81430147e75d8143004fd75d81430067d75d81430047d75d8143014fc75d81430bcfd73d814335e7f53d814335e7d53d8143064fe72d8143004fd72d81430067c52d8143004fe71d8143004fd71d814335efa30d81430067e65981430067d65981433679c4398143006fb60981430067e65581430067d65581433179c435814315d7e75181430057d75181430067e65181430067d65181434ef9c4318143005ee7218143005ed7218143005f67118143005f5711814301efa6018143006f960181430657f7658e520057f7458e523357e7458e523357c7458e520667f6458e520067e6458e520067d6458e520667c6458e520657f7358e520675f6358e521567e6358e520667c6358e520675c6358e520665c6358e521575e4358e520657e7258e520657c7258e520667e6258e520676e6258e520675e3258e520675c3258e520057f715
  | 33 => 0xf64185530067d64185530157f731855300d7e73185530157d731855300d7c73185535367f63185535475f63185530057e72185530057d72185530067e62185530067c62185535375f321855353d7e71185530067f61185530077661185530067d61185530077561185535377631185535377531185531ad7e70185530057d70185531657e74d81530057d74d81531657c74d81530067f64d81530067d64d81530157f73d81530157d73d81535167f63d815352f5f63d81530057e72d81530057d72d81530067e62d81530067c62d81535175f32d81530057e71d81530057d71d81530067f61d81530067d61d81535177a30d81535177930d815351d7d76981531657e74981530057d74981531ad7c74981530067f64981530067d64981535257d73981531af5d73981530b55d73981531b67f63981530cf5f63981530057e72981530057d72981530067e62981530067c62981535275f32981530057e71981530057d71981530067e61981530067c61981531ad7e70981531ae7f60981530077b60981530057f74581531657e74581531657c74581530067f64581530067d645815351d7f73581530075f73581530cd5f735815351e7f63581530b75f63581530057f72581530057c72581530067e62581530067c625815351f5f32581530057f71581530057c71581530067f61581530067d61581530077b60581531ae7e60581535157e76181531657e74181530057d74181531ad7c74181530067f64181530067d64181530157f731815300d7e73181530157d731815300d7c73181531b67f631815350f5f63181530057e72181530057d72181530067e62181530067c62181535075f32181530057e71181531af7671181530057671181530057d71181531af7571181530057571181530067e61181530067c61181531ad7e70181531ae7f60181531af7a60181531ae7d60181530077960181531af7a30181535077930181533557f765954315e7f76595430147f76595433457f73595430075f73595434fd5f73595433473e43595433475c43595433471c43595430057c72595433475f32595433475c31595433475f30595433467f73595433447f73595430065f73595433467e43595433467d43595433467c43595430067f72595430067e72595430067d72595430067c72595430647c72595433467f32595433465f32595433467c32595430067f71595430067e71595430067d71595430067c71595433467f31595433467c31595430067f70595430067e70595430067d70595430067c70595433467f30595433467c305954315d7e75d89430057d75d89430067e65d89430067d65d89434e79c43d8943004ff75d8943014fe75d89430067e75d89430147e75d8943004fd75d89430067d75d89430047d75d8943014fc75d89430bcfd73d8943
  | 34 => 0x89530076f62989531575f32989530057e71989530057d71989531ad7e70989530057d70989530057f74589531657e74589531657c74589530067f64589530067d64589535757f73589530075f735895314d5f73589535767f635895313f5f63589530076f62589530067e62589535775f32589530057f71589530077771589530057771589530057c71589530077471589530057471589530057f70589531ad7c705895356d7e76189531657e74189530073e74189531653e74189530057d74189530073d74189530053d74189531657c74189530067f64189530067e64189530067d64189530067c64189530157f731895300d7e73189530157d73189535675d731895300d7c731895332e7f63189535675f63189531557e72189530067f62189530076e62189530067d62189530076d621895332f5f321895332f6e321895332f6d32189530057e71189530057d71189531ad7e70189530057d70189530667f74189530667e74189530663e74189530667d74189530047d74189530663d74189530043d74189530667c74189530667f73189530667d73189530147d73189530665d731895332e7f431895332e7e431895332e7d431895332e7c43189530667f42189530667c42189530667f32189530665f32189530667e32189530666e32189530667d321895332e6d32189530667c32189530667f71189530667e71189530667d71189530667c71189530067f41189530067c411895332e7f311895332e7e311895332e7d311895332e7c31189530667f70189530667e70189530667d70189530667c70189530067f40189530067c401895332e7f301895332e7e301895332e7d301895332e7c30189531657e74d85530057d74d85531657c74d85530067f64d85530067d64d85530157f73d85530157d73d855354e7f63d855355f5f63d85530057e72d85530057d72d85530067e62d85530067c62d855354f5f32d855354f7631d855354f7531d85531ad7e70d85530057d70d85535557d76985531657e74985530057d74985531657c74985530067f64985530067d649855353d7d73985530075d739855311d5d739855353e7f639855312f5f63985530057e72985530057d72985530067e62985530067c629855353f5f32985535357e71985530067f61985530077761985530067761985531ad7e70985530057d70985530057f74585531657e74585531657c74585530067f64585530067d64585535557f73585530075f735855312d5f73585535567f635855311f5f63585530057f72585530076f72585530056f72585530057c72585530076c72585530056c72585530067e62585530067c62585535575f32585530077761585530067e61585530057f70585531ad7c705855354d7e76185531657e74185530057d74185531657c74185530067
  | 35 => 0xe8003000c01700d000a00040010054001004c03100080370000003005c00b00140070004008001c0020044006000000e000800000400000000005002400900d40000010006004800c0010001001c00300240320008000002800e00480010030004000005e0000003000000000040080040007001000a00240010020018001c03200140010004005000004f007c00900240070004000003c006001003b000001f000002a007c0090030001002800100080000038005000000100000060010000004800000500100004015003c00000d4005000400000040040010000001c002007001600040000038000001c000005c02d00b40000024010000c00d00180010000006001400100140020000000002c0030004000006000300000030008004000000b00e400600080060048000000400000a400100a001b000400300080120074011001000100000100000008000400000ac001001400d00000070060008001c02159d7e76d91533457d74d91531667e64d91531673e64d91531663e64d91531667c64d91530157f73d915300d7e73d91530157d73d915300d7c73d91533567f63d91535975f63d91533573f43d91533573d43d91530057e72d91530057d72d91533575f32d91530057e71d91530057d71d91531ad7e70d91530057d70d91533447d74d91533567f73d91533567d73d91530147d73d91533567f43d91533563f43d91533567e43d91533567c43d91530067f72d91530067e72d91530647e72d91530067d72d91530067c72d91531667f42d91531667c42d91533567f32d91533565f32d91533567e32d91533567d32d91533567c32d91530067f71d91530067e71d91530067d71d91530067c71d91531667f41d91531667c41d91533567f31d91533567e31d91533567d31d91533567c31d91530067f70d91530067e70d91530067d70d91530067c70d91531667f40d91531667c40d91533567f30d91533567e30d91533567d30d91533567c30d915358d7f76591533557f74591530073f64591531667e64591531667c64591531673c64591533457f73591530075f73591535855f73591533467f635915315f5f63591530057f72591530057c72591531673f42591533475f32591530057f71591530057c71591530057f70591531ad7c70591531657e74d89530057d74d89531657c74d89530067f64d89530067d64d89530157f73d895357f5f73d89530157d73d895356e7f63d895357f5f63d895356f5f32d895356f6e32d895356f6d32d89530057e71d89530057d71d89531ad7e70d89530057d70d89535757d76989531657e74989530057d74989531657c74989530067f64989530067e64989530067d64989530067c64989531557d73989530075d739895313d5d73989531567f639895314f5f639895332d7e72989530067f629
  | 36 => 0x80000000000000080010010007004006a0000007001c037002400000640060008001000c018000000c0008000002c001000c00000040030018017004c0000004000001400800000030000007000400500000020004006003801e0080007001c00200000020058001006c00000040000008000002c0070000033000400d000000200200010000000000000000100020000000003c0000010015000400100100060054019001800000d4001009c0060018012002400d00000030080001000c000001c007000002300000070004001002000600300060008000009800e006400a000800b00180030014000002c02d000c000000800900000000018000000000000040010044000002800c000c025000000200180010024009000c01a000000100000000004002005001d002800c00000020008000000c0080000000004800c002401900d8000001000600000000004000000000000000070024000006800c0020001000000200080040020003006000001ec012003c004000803b00000000010009004801100040000000000001c0220000003000400100080060000016000407600080040040000000c004000000b00000040010008007400800f00000010003018402e00140020018005012000f0010000000000100080690000005000801900400000014004007800100040010000000001000800000040010015000001a000c000001000300200000000000003c000001000200000000064007002c000002c00000040100000000003801a001c00000cc000000000000c4000002800100000070000025000c004004c0150094003000401e0000007000000000200240018006001401d000c005000800100000000038000005c008000400600000010018003000000b0010005001000100040230024017000402d00100000014007000402700300030038000004c00b0014000012801c000400200000000010000000c0020000005004c000010c0020048003000800c001c00d0044003001400200700000008000000000200900050000000000000100000000054000001400500a001a0008000001000e005400e0000009000000400380020000004003000900080200030000006800e0054001000c018002c007003403f0000000001c001004400000040070004004000400000300020010047002400000780000034000000800e0134001000000a005800000000080000000002800900180090010003007c00000000040040004001000000000070004004003c0130000004001000500100020010006001801300ac019000400c000000700080140098000000000a00d400b00100100000044000400200cc0000010005002c0050000083000000a002c008008c0000000011004c00500680190034004002400000000030010009001c00a002c00200ac00
  | 37 => 0x110000001014c00a005c00000100010090004000000000600020004002001801301b40040014000002c0040014006000c000009c00c000001e003c000001001700100010058015001c0040000000003000200280090040003000801f0004008000c0030000000000000b000000000000580018000001803d000401e001800800280000000001000c000001400100000000008000002800a0064000002c0010000064000400b000400500080000028000005000a0010026003c02000000020014000000c003001803a000404900140010000001003c022000800100000000000000003c03d0000008000c00100100000000012000c00002240030004000001007f000400000040000068002002c00200440190014013000800e0044003007800200040000064000000400000140050000004003000100480090004000000c00000dc001000000a002c020006800c0114004002000b0004024000000c0000006000801000100010010000002000500100000030001003c029000400c01e00030000001000c01500040000000002000000900480010158009001c0000018000000c074001000a009000200240110034007004000a00000000018000001c00100000060030001000c00a0000004007403700540000018008006804100000040018007001c00f00240170058003001800900000000010007000000000000060010005005800b000002700900020000000010800000000050014000000000200bc0190000001004000a00080000008002000400e0000000001400500440010004019000000100000020000002000c00000000000090001002c001001c00400000000008000000c00500040030004015000000600100070000001002c0070010029003003b009c020001403a000403300ac00400140060004005004800f0018001002000e006c0000000009000001e006c00700040010004002000c00b00000070000009000000000140010000000000400c0004000006c01300000020228006000000000240030008018005c00900340060008000000c0600028004000000400240040000003000000b000001900200000000010001000700080050090002000805e001800400b80000040009000000500000000020040000c000000001600000520000000001c00000000440014036006800e0008004000c0010020003003c04d00040030028010000000b0000001007800400000120028000000800e00000000018005000000b000c006000c0000030002000000000740090000012000400100000080010002002c00300500080024080004c00f0008012002c00500080180098005002001d0004001002c074000000800100140000001000000400000020010000009c00000140010020000000801000000000028000007800f001c007003401000
  | 38 => 0x4000003d00300060024000006400700240040028008000c00000200390000003001c0000034001000400100080110000000006c07900000020010039001000600140110044004001c00b000000900040010000006003401c0044027005000e0014001007800000100000038001000000300d000a001c00000000070010005002800200100070018002006400400140000000001000400000040000060017000c016000000000600030014012000400100440060124004002000f00000060000011000400a002400000140000004002000000601e40070054009001400d00280010008015000c00800ac0010000002000000b000c00a001000800080000008001005800000b4001002c0010010000000000a0070019000c00100280000000007000c0170018003000000100080070000067001c000000000f00480010028002000804f001000b006c001004400600280160018007000400e001000f001800a00100050004004000400c0000026000c00d0010000001402e00000280004000002000100000010070000002c0220014000001400d00380000068000004c0190034001000000801ec0040008001002400000500030044000001000e002c00200140000014000000c0030004004000000d000000900100020004003001400a009400100bc001000401b000400800700020018003006c022002000000940030000000006800b004400800040040000001009000400bc00b00b800100440020008003001400100800080020001000000a002400700480000000001000400200a80070004001000800000340020014003000401401c401f000400b000c0010004001000400000100080034001000401e000003c000801b0000001005400000100070054009007c005000001000180010040000014c00000240000004004000c02b0008001003800100a00000060000002c007007c0010000004007400500000130004000001000c00bc00300040060014018000400200dc000000c016005000a0048014001c0000020003002808900000000034004000400400000260000001000000f000c00c002c0000040004000000100a400000c4002000000600f801d0028004003c02c003800a0008015003800a000c00100440090014044000400f0014018000c0000000000000c007001c02800580050000001000400c001400000180090000049001c00500100000030008000400500040000024005001800b000000200000110004001006000e0000005001000000140090028002000400000000000010006003c0030004007000002e003c006000800200140000000001003c0010008024000400600000020014001003800100000000034000000400000000030004006000c004000c0010040000001c000000400100280000008003004800000240
  | 39 => 0xcf58230b086941dc520ba61c42480ad64a2bb865021dc0369635935a246a7212c452f0bec9d72be81092b282c70408787ab2aa0914d02cf9bd24c6ad0873dc1479f4801941aaa1eb60a28a5df9ce09df8ee898ba324a0e8bd877629148fc11e1764c58239dacc81d5267e31ec55454b00007a300160ad22fe00017e07f09c1c28619b25788c1c690a0c2b0e162fabf01cc50b50da4f7aa029664cf000000001c6000025a977a6b6800039f9418937addc0fbed76b7000001045262b2f80006c60a1a3f5206c000000063488b379b06f8151e7e220499f457e93eab041b4e1a10c4640ca60c1908c4005380008da11b20002d509d48a343542cb49372780b13800095bddf06bfad5695a111604493840a7000029aa6a4697198e49fad8039600000f3817e523012696b95c6001c00500140010008000004c02e0008006001c0000028000000c00b00000440000014000400100440020004003000000a00280310000003007c01a000003d0008003001800a007c026004000800f800400ac0000000001003c000004800300180130024013000800000180060004001002c00100080030004010009c010007c019000001200680050084004000809800540070000002000000100d40010010000008804400000010000004001401800a80060010000000800b004400000040020008003000c02a005000900200060044009005400000000010000002008000a001001d001800c0000000000001c000000f008800000040120000009001c029000800a0020000000000c00000050044000000c008002800c00180050000002004c013002c005000c0010130008001801a0024035000803c000800000280000000000003c0020014001000004f0010000000c001000400d00040010000000001400800140000038001000801800780040008001006c0000000007002000101280030034000004000000200160020000002c0000034022002c005000000a001000000080040004002000000a0010006001800000140020000000000800c000000100480130010002002c00b0054001002c00001a000d0020001000c0000018000000400c000000e003800200200050008000007800e007800600000030014015000002000c0013001000200bc025001c03c00040000024001000000e00440000000014003400500040000008022008c000000001200080030008004000000400200020018010006000a001c024000800b00100010034002008c00800080010164000000c0090004001000c016002800a000800100000040024016006c00c000000900000200018007000c02b000c00f000001700140020004005001000000040000000005002c00300040000018007005800700000000048021003000300000010018014002000000000010004001005c00000100010
  | 40 => 0x9f5019d0b5cab254c8674632878a000000000000006f74e220002e6800000000211790000282e0ca9c4d00006be00014ea5b8555360e922a173000075410a201900d9a1411a15ee82cc8af85a274298f35768ea052a8cc612fa76cac78d2a2d707e8964425600000a0adf468562a0e2f000113e0001b945b5830a0001053503a9aca6711c80000af69171bb80000000ad0000050a15e60000000000170400009f0000000000028be55e048b9e08bc400000000001cbe0000761b8d055663325e6000171600016a29719a6599129ce35b216a24cab9c05489ba52d201a7311af61600000000069a90d15855e5a6761d100004db5ec600008881bfd9bc7519194b4313701230198bbaa098b5013b8347196172320a400003eab788100b0484417fb1f4a7591e4c04c59483cc00c233eac98ac26a110f480003ad8d9e36f5d720001963bd51322b1b092424596a467725e07fa8352a908e64a84acfe0cf21e22778a0427d9b3f4fe14de7719a6a59552422cf1b57703800000001a990105281c90b8e0690a028e2a1900b115044b183156470f783c4c60c47cd3be47380000002b8e00012540001b665932954085800007daa4e00000005e2a6a05ed4cca887a89372e01ee00000000001cab518924f00002686c4000062ed3490000000aa7800005a2d440d42eec100039100029e856d97fe3afdca71a443a92042ee400002190000e630001225a95adde304a6386052d647c6190a0000b700c785e4b5e28443d0113600000008644da0be08654bdf869c93e80001a62a308e68c268c582e0000042a3dd51f00001b9c7852454713e5507b2887a40357806cd0e0c0e706b4b469644506800000015dc1eb13a4589ccb200000008011f9e055800000000004ca27c600006ec393d114957424637c00007048000000000069c2d22932134e19c22b24a124ac86d84d4ba300005801e13b0b0000000034c738ae4438f206a9844260ad51ba3719ddb6a892cfc23bab10a1b967b70984c4123dfe605d000074bd1d48e49e1a4c52464286c00000018c37b55a260002d02485055e81e2a64011258e0bb0bea98c91ee55746ca032000050d8548171692e8e31e761e891cf31798a2651800052b1cafafe8cb55a1800044ba480145c0008a92dc89f69c76a3090e2345ef68799000000000003c000003128842009ac370001ffe55a17b6ba5ac6e30f14a250e03d84992450000200690619ca8648a167a1800009b000011d0000a83c62c83293a8461c000522905471fa0620002e4e84101501c50962bd306f200022b856e1c640002e4ab6609e024be7b60001b0828f890b5d58b0b873694c9b702f695f80005bc28e01d986e200022b41c20eaa0001b9a000253186e1e1755c920b355297e11b5ea83d7ac5f4890360a7e2a2675701c22820aba0639612107c4464231
  | 41 => 0x2ee04aaaefabd21e5c8139294a0e188479e93c4ab300004cbaac80000212ae29b6a00026b06560740478c08224a0000817814c12e8000b1003da89756de29d22b01605b3aa2907d406f8488598010337685d5a3f80005309ef48662a0e2daa5e87da000012d6d4873ca9c668f8000592000065a11900bc8000000000024a83b7000049e432c0007f38a3b6fd1157000000035600006f5a86486d17b093d8000175ab7020f0b88a2a01104d091921ab9fe83c7eb8216a28ae530caa4b19806c6238e450bb81fc959c0006432daa7520f3da8682370b36b4c1e8252a569800024b15fc7b91dea9e585314d401f88bd942a1dca6588a5a5a83eaad5408302507f122247f1a7aa00020ae4f997f48f184d210a6c1c84580000000f928f3a8420000be300015637f01a16622a6be5f727ea15959b435c4510b9480af8df11d29b203ab199a3901fe8d9c912aa6abd40da491188784718e3a981165a62fcb00ad1247e7938da22b20ca091e84e347b008c89492183444cd27de240e5e8ab9a466aa4c32fa364217def063699a802b00566e5a8993968a4a6e806dc43819c485584f8072a5bc4be11baac60fde108acf68562992928a74e58e80003b9877c62809269978000000036280e9aa4ad71dfaaa1ac3c00023324578875a21805221f0fd2000000000023947ff0210aeb433d00000000000910b4e0000475800059a8cce00000000002f0e54000000821bf86b940000002189000123c000290e0001863000114a2561eba1c1278648dc000aec0000765934f494662000013309c780003e984ee7c525b292f2c2a000000068daa50000101cb63267a0de15d44cf1d5802d40dd0000000b01a5cc228118286510282ad9df87bf05d960e046400000001a180000001e8e6f24976a4d87f86ae8000000219a8658000b7584e92dfc2ed1a818d66d828ce0000657610aabc4c3491800004267a900002f20f2a6e98000a1e0e364018b9a06409c0a4b0000109ea7236c97218b69249ae61c4700020fa32724ba6bba23ab4a06a89689db2036000033b000072684d06339d8c7de8a12acba5469a991655df1e72a1e977635a210e57d9a742e042b2ac8000000f8e5208049885b400000f7000059faafb0001ee607683f82f7a66a6551e4489eca9a311047037a80005be9988000158a8ab1b2a1ed8e7c5eb44b25a20000a0391ae00029bf725200c076170091994800000000782400048280006f80000400007cbd127367882bd2b06000015d00000000000744a1d435c92040518361700241cb1d0000478000012d80004cf902c0c59dd9000058a00008ae80f00002ef0be869b800000004ca0000922ab386726c6a54000022ea00015a2b2d89e478f262a7ad12da96e167a000253c9fc287f000000000000008479e5a7d829d6b222bc85adaaf2665cf4b1bfa621
  | 42 => 0x962d460135b8b43ac5086e000117841d22f244ee8aa02f525ea6c92521ba0cd07c6d4c400000000002478aac09c8728400064213ee68a8000acb15d6aaba25c1142998aa10428000153e22895f4bb0a7ce38a98ea0002af63430cc0000262600011db9cfaca800000008ea8000643cf5aa5422dc2d30db497c8f0b3bca7c4655abd62f6a0845d70abe7ee094c71dda0e9b10b5a627188868e131c3728dba244c9faa3f298c6b08f2086edb48898a3d01652e047d0025183a86d08aa14729558e266be2c9ca91862f6a61f04899195259b0ca66ca2f6c8986b12a628d1a21127e431983ec2a2883230c94001fd21461e51da86ab86f0740141e35f1ba846015183b306c89b01938bb1819ea355d163b005ad52bd3d25b2935a3ce28cc57e1076ba209a03f597544442b7632c0fe85b2052c62916ac15720766c0cf804d2c64459404601b09da07cf908a8569260052552e5ca889b722000000017d67eba9d2229a9062d940003878a64000217c00003ba742246a4b84ba6657908f00012be08694e6b9b17b7b642e601e4191a7e39b02159d31e25f01f30ac23c5024dbe40a34ce7b5ca12649619437cca9fa00008161b365697dfaab2aff4b1aadc88fc4e5040668744efa5d839eb1e12e4ab82ec0051122277d88e40002c1e36b863a66b2aa0a38a75800000000000696753e24c7b6945455ba7323b200008f5123a23fda8206d800033900002480c687df2ed6000207e270913d374000032402b82da1f920000d0000000006e60dd6a63577025f9118bcb2cea37f186e0002ecca2006350000000000210622b12440e2c000aedcc307578000000000044d0e798b51c745ef879625420686b88b7873085a574500d00d9a89e55485863058b0a2b408002b70bca77a232200d9c5dbd38c84510021c7748c64b620000a1b081c186a08e83700009c852ba374a9bb592a9b90f00c3e0911e9e6cc03e680a219541c66e873744c94405d020fea0401e4a14058415a4b3ca46022293e736f112800013ae10298b0afca61e46c04b417f80e234b95caacf29c19369ec02511d6a1195b0110dda6400015ac71696b20002a001c68f12721452d128ee20893c32eaa69c240001c3c40801b200021c824e8000266000084c260aba698e637325b05fcda0028c8000340a51aa38d26a15d8b545db8738ad29b161808000a881dec4858000167cf0666e085b000294400000009e825c4314c00000000006922cde8289b84a8e5560959409273a894b590800004268c82af4000b3b04a03e300005c50bee656d2e70000000000000088b2578000043f33d9c70000085c7a4038c11cc22804b88c84919c7540f08fe0001f887fe80009a32082445c1a2583c000b1f21825c8cc8000000000000e31b209b1d000228500029ee7a2ae78ae98de203499f618292fd00022a1000
  | 43 => 0x2af0251ae48000130e000097900000009fa1f1000026685d20f901399d9c3909708433ed1000015063b88000000159604c9044921a71000000000a6e7120000000393048692a1cb64bc000059d00000001b760002c8603b8b7a8f49a886b62c80130e000299ae3e4f222ba9ae07f53b0a56610c90a60002e7c19b671c0000c6f5db000064d8000b908c5c22e1e061a91d74baf8000ba800002b04000b91800000000005b0800016d0ab4644809aa9604478f6800030117f061eec522c9a8d60b08fdc45ce0f00b6a1ba00004f21ed29206068baca0529bc7f40000000150c20624265d48000aae8d128c121288f60c6c6102a6035696387af133a05fed9c1861566bce95b40eb92d4731a874b12e678511a52eb8c02d152c800037989545a0ad8632e828f00023b00d1130b9b910820001d70000000000000000001270a0d9b227468b9d8579c80b082b1c3c9af320000c983cb9e104e59fb295ca7440000db62e6241a17a183e9e126248b88000058924aacd463b49f2aee036c00000028343602aa8a5e2c5d22127cc0b1c0000030fee0001c4600008087361ae6764400000000000e4a5203e5800000029e47e58c3a327631293c886b68c82be8d0888ca9d000004f8e819ec2ac25baa77263900000001afc2d000004809fe00d2ac26bd68c504679aeab4a924b0000b5f12016c4adb26ac5ea251006e800000000003a5a532b562dc4000181600000000001f245bd00f68fa8000b738000000000065caf34000000033d29a4980a7402a11e7e000045642ea29400018e021a117a19acf1e6120e4400000002c1abbe4108000ade157a0000341131c569163257c6d49c68247283e0000cea7ba007800017100130000868ee401ba86000dc954034604b853f253a608a99468180002d980007728e414e6935217b5fac28e214e3c20e5e0cdc52438f8eea619d0e873e94cc0e51f2e9caa2b67bb0dd8b7680ae35a87f012709d23621c7f1a3888db2983325fda9b006a16799ac86f6579290250882526911b3812107d25ce05a636edbc24556af857fa5d314611f222163a689c0ecdbcf085489791765bb011c9c5a21604311d7b9517e4260a3302a51cac7f505f6381193e4d941b45a8239c2ec1794112852b17aad4c8ce800006a80000000000000134098e60bca5025be12f19be7fc1426000159e7e8104e1b500700001336afd800083f9c98000000000000001e3000065c151a4fd2b0091303d07d7000000028b0000000003c88ca07e888e68607039e8a09c67f5b2050093e80001baa000192485c15707ce18e2000183608ba8d448b88a81818a7a2036f265171d3e45f2d2c3d9873aa8f845e21f99c86c1580a443501f86386162ff00009ffaf8887b218b16c8000b130000647a6e2443a62d5648ad8b9e85d200000a526d84f4722914c0719bd
  | 44 => 0xdc7d098fa2038fe251aaafeb1c8c8a10d9e9c00793f624492b28ca1cd0ac0ac54aad2031b181b62735a664b690a26ba780004f840002cd158078097723c08000931a6bf2710000000000035080001b461bc00013af7c7015c28e84bd00025712840d060da94060002bba9dd9afab0ea4e273315cc6b1abce3db04a2106c7ec3a78c62839463e4310dee63b8334139de986b8288269f9eae450936430323506eb81dc46a250e5be2dc6413dcde8348c142b02232b6b83b228d48b1b852ce01658b186d85db08ff0c6a33a687742216aa3549b197b5a8849b31daf7780f1c5e8021595ac00000009421b685ae7650000a4a2f5e93096be000257a2f48f76a8d539893aadcc000155a00023585c3995a00029f0680a7267da83e70001476424c89609f1564b0d06aaa3983700000cf2a870000b2ea9b6a40000003e092db7502fc7e90c2e56a96e6a52969a64f2dd091cc3f9038223692c0fa8b2328a650b02226d195c42160000000000074413a07f307c80002db203ea33c57a1c868b1cc86bb708766f22e2c46708dc5a3a58a62d28005ba26133eba12e8b81bcd58613bc386913a1d0885042c894f7281b6424d1da44e7abbc414066a13057a638a0d3258f8afc560a544bdaa4763bb9b8178289562951ab4136a034789205029dcf816eb261696b09361548d2280f809867385a31efaac056429c07d8812c033af08bc82a317b0567c114878043991533af0d041702d945b68aee4c808e00680e436e5dbe818117bb777a3f69a09106af3001a60090f8352837e31f191409c81861990e1601503b88091e0092ca876185422c2ce8ab0008100a3b8e97a83f095a33b92e31f9a694975841696d08de40d85e20000cc7954800076023f8000147444cab86000013015ae879bc706581f680ab7fc8cae00000003ec819217407b00f7a3c428a80008d2280200025a4469245a41908e23ac000093f1ea173c233428023a84ed04683205eb3b65809b000000019a4d56476432000004c20001b1c00017d80000540b41860887ea9e741b8aea298adb0000118e00021fc342aad22b81792984090e0a40106684800000025a60002f7a2b2894e80b0000000056074b80009a8c00000000006f51512000220a00000003b40ae6000019c000078600002de00011c47db0000b59a37ab3a000000000000002b0e0000f884a700001e985ac95e63444f58000521acc600006b2000023800000000002e5c9f60000a410fe011acc8e468000025c9f080000e10357284c00000007a8800057c000000000000000000871864058a00000001b6e49d80004c296583e6096829c0000aecc0002d2400a000000000000000c19493431a56d48e0000ae597624bcc00000002ae0590000a9790c03df8846116800055a9557a6d1f500002018961a8717c38b6415c903ebac000000
  | 45 => 0x28afa342eca7569fa271a841c0d16d6e4ba2b4618cc4bf55705eca570a6063c400000022c83232cd6000090c0dd033b2548322afd0d28000034752b9616aba01e98a086b6acb400032d8e252b0a656000110835d08ce7d6a1ca00010a0aded5ec9408fb8b30a25a59c84de8caa9666fc2ce2502179a67600002ce255bb250ceba644330566a1096132bf02bd2a2201dad200b905227db915f0000000828276614796b0518191002daf1aab5aca08a8000000023f229b8e504d8c000a2c80000001e426e19e880002cd24df01ff0a30b9053c800000000007618000846accc90ca6de664210c1132ed241700000fee7f200018c0bbc800000021c200003e2000199c7960188ba50000670ad3466cef42000000022d92d2b1a9aec4ab26ec2d58726852882a0002d16118af005dd02300001e6268ea9e088f9e264bd1a5a87dac58000128c0fd181e76e0b2c66908d478aaaf426dc60d2a480007739b3d40ea036b1e8ed27a4c000620184aa6fa95629f988618526982c3000052993822e4800005b9a8c49a18ec00009be0002630853150e0000626333c0000000f2811709a22f518b344e63780a88000727d1c29ed221c0001086a18075c0bf427daa01d7c90e8000a9280004d1df22261974070e9adc642c5448dd13fab9d96344971b9eab9855f00011be6a88000ac1da22000070c0000c2a2ca888667faf365f354900001f341069edc00025260000b2e00009bba4ea1e41668ec5000000000021d38025c160002cf05d40762000250a0000b0310e2074604847e9c01dc28a680000000000b2c27ca0000c2cb032d3e25458785996a287d300426ae10fc000000015b826478d058361f96143a700005d180001d78e684a92142a5191fc1a0097f68286a66e28584a9dac1a7241b14ad894e481697687131cae0000d84b8580004d8a70c170613c537c00074c24a6a06ab6e1542926970207c78e9d786e20000a6a25065f2829e92da8a0949071002f1df23b81d184bd989a429136e49ca8b6a2443b4247a0d0bb9a4428b617e803b170c952038e278ad8a214a9e633e05b06321f1e0b2a6f28a3da86000267481518b2000125b1ae80e69aea584a6f6114201593453ba1aa6bca4fe3a68a864e21444556048a67b2ae434e0b762f891a36b10ba85420dc800d2a0c9cb99d61bf015a8c5da2000000008511ec300008c2158804e5eadb1e9564000892112c3d70b86b1913f00002a9c0000196943159b85b1ef80b0118500015d217e029484cdc9e32906c52128bf40c312dca61a48a2b516dc4bf9138998000000018bcb6e0ccc0001ca8588a646000195cab6022418ca808b6a000079f1a9e1ff12d032a20864e2825abdd164e283209a942000064380000001944000050c0ceab60710890208e5c5c338a474a6a9b8cafe63083fc1c3673e1d3466584
  | 46 => 0xc38099820a0120bc273cd73c02459c630d815429119a09652ada5b5c00045907843ce98d008191bc7c9a47c77918774dd904604d4662458dc7a842237261900001979d760001051b830ad600000000000000bbe201c880a0e034f8ac684d1302a2409290a384eaaf1001843367ee53d2a6631e800069a1cb074b000041c9bfca4580006c28f23747000043241c87b600000d7a60e330c5009ca18d455400003b180005ae12200002c247d7808064895985081fd2a378a98a7f048d7b11209a6b806605282355b024e82ed066c413000000000fcb020d1500000000000000000000008c800040c187c0002bae1b84b280002df2000034e294012a28b15483289656be02f28344e958477df0283684eda9b000036a99e6000000011c5208b0e59ba9f0000043c9e126deac630ece484a640d3a00007fe00018c400029388b991b44bc80000000eba5b188bc2f00c549b40c603ad093c7701a8413842409bba4442d4aa98477abf8343e258000246c2a983a40f8521c11513d0b1c046996746825b49d403639c7825c284082d000015394d55256a5a810ae648b42aec5ef5d8d18462863fa8564118e1e67012e7e64caa5c0001a7ca4c8a4204613d4a2e2a2c27fa7625fa800092922a205e000031b80006d521d0a20c024993270e67a8c422a0085a960a02e1248b96ab512829ad235e7e01692000198a0240000099400074900006a9910f9c927fa8d02f224ff5cbcbcf877a8241c6c96a800060b8000a018000ae2208000001e3000000000009b80000f7104100004fb00000000afe0e8027600015ce5108d3700019841a31ad00001dae7aec6a28a7aa34b9324f806142181515d320e9903938c25c8405956c45706ce5bb98464c92d18baa1e16242831273501e6716208aa56879e8e002d6bc6197c54c09f838b2a3cadfa9102250e140dcc570084585c15f1f0085a2d2ebb40e4a8278b7d000000000005a1bb500000632ee874e94e814529086749cb28ba05d43d305ce2590f6ebc519027508000a4480008d50f7041fee8a2d1800075a20ac5f01b128c713447438bfa8f5827883ed1ac04e8bfe0002f6400005c70be00009add0e40001d3800020116f406fb88211620002573000086a9b4800000000009cd000027a00000001d4db9980003df0000908000040988341c464ce00005faa22894000000004815bba84298e8bb38ea3add0efebde0b5814be4be6fc9c4e848a0c452a407188d02ba3a1edf8bd9821e85700862cc0c562c14c964e302cb183c7cc99ca530221de9a44683f25c0aa8aaaf8a240000000a860be6000293e007ddb56661b2e5335c2070300000001dba7b89dcb000218f0ab4000182547c8384f440001a4000014b07c320f667798720002a7e1498628bc18e4002aa0d67f797429cc29d465d20c865b048e1f1840700012fa0
  | 47 => 0x18d909a651ce8486b064c5ef19785e91bda59d896e55dae3c0c902eb23aa6d6ab891521f4098c41e800081c98c137a1a1aba38e1271422ca000000000000001560000000000000018de00013921258dc200023a400005d7475589e1c5830eaf0800000020ee373820e000269754f02bc00000000000338415ab58869ad4600027705f09b0eae107de03a81f55a514f85b888d6a30000071215c039ba93c58c12e6b452d6a11f00005a125fa400af52977000034b00008a006391c0a8549531950b3380004568dcb7498000b3d00000001d904242b5e1fba42423a15382c1189414c0af83f61ce1a682f2e7fe10b6770d93a75597b418b408a48d80009668448131400052700009ff000000001f27740578000136c00aac5040ac000a5201077009a6202d1f3c5d6a00a0000fda448435fb89a4366b909cc0ab195f1be81d04490ebe7c580008eb8000a9e00000000fc65f79f2039c13048631d4e665000004daade67c0356bc91091a169a6115fa31a555aa0651980009bf61de6960b102a422261bd247200000001771f8242368bc48f92e26506c022aaa6a20a09a8a000000011080006b8c2ce26c8ce52bc000009c28e895b0aac0c0a1ae434800087aaf043a49248462263607529528fb80004ea6a7039ec748031a4e4bc7a1a872aa24a2d107e024f820f5149f7061c2ab88130d7a933210762e847a377ae8058ba0c01a0cbb226d1cad90500005882f0c26f007eb154000729800070200008a62d520000000000000050a400000000004c980000000148000152086152002889161bd5ae0800020083ee9b2cafba696ad9286a6ac2cda39e0bce87122450ff9e3e0001f663da0000b8e9d7700000000000e8cb4e97fc2d8d0f9000000000000000000d5e0e3eb4295d0f0e788928b1a4aa8217293ff8bf0df609ea686af1aaa467de87e21780005489c6e00000000be833e6f19cdb00015a00001278000000065140006ad8b6c6bfcb829178c9e00008d856c90de0850fc800026480000fb00e60000b8a800077526f47d4882246362c06b29bbe00b80006b4844e876860e23e0313aed10d6666a62c766ac443e280500489d9906b89495c9abca7d593da6dc1ed484da1e000004400001f9a5e717ac3599e4a55fa51814713787b7ad5ca8ce6fc3bd96400a6a338a678f0497428978cb8a3d449ca6c5e7818a1674bdc3958c74bd8a3fa7efa1977ae2d7e2535d923c915945b61c149584c085c489840001cb41cc812f9b805be3ff9da6bbc18d85e3882858782eaa1ed56b1762c00aff802c0e28bb613f00324e72974a2619a204212e0737d137ac9860b4ae21d662999042c085128ec89d40dd80000001e604dc9ba2000140c76f90cc36317660f10d3c535d37e3a3955e6ed88c40000e869616de83e88776b8081ea582800000014b641021a408f8
  | 48 => 0xca288dbaf4abbfa6ae000000075128f04a1a59ea390a4e39959e800000000a1af7000020e600029f210100004c60fd30000f860f9226a39340000002a138762d8434501de32dee908f0837505d86943ef0b20000000099b00000000f7a7a7da342eb9f763d2256305e98dc3c25af40408200073aa2f53701429310c7f4558d304546b6a553810a4a41f1a2d2e3de23b0aae5a70000a425aac7661bb0a25800027aa0f45bf06e60000fb645c2d6200000002880ce064992ca8ef9a2e3f084c8030253ea04a412a8caf400001b260a5ca06658a92a00001808c091fe814ac5300013ba0001a049b8e05c000000029e1c54000000000000006c3000000000005b928a91f90000000000074d9e48a080c990002e5000026282bcc000805a5b625f4000481ddee000216282a8000abaa51c4b940008f98000000144800000000000bd65e18d395ad20de00015bc00016a60aac2e63f2857a0b48000a5ca5fd7ab129589d91dd000005ca468368676a84a262e6660000a9d00012285fe29ba9fb1f300002010000000092e051ab988000a232a160000000093aaa278715445bfac8467e809e3675fe49122c7e000157c0000f5635900002e1050e00026123939cce944800037c8000000000000000001cc13866d29982a1c95de2ae0000000084c2d7522c090a0566e444028dc11bb0002148b7f978c2738f2215fed9a5bd9ff6348000011111967ca8ffa000251e0000000760800033a069300000002078be076282dc5a5a0d89af249c2bb26e1291873e00000000000000771c0000001a960000f602949a80413478eb088000296836e0001aaa301a8ac561277a15280cc70e28f8ba0982854a85b886222440d0800033503f60d6843e0f0889f0002615479a256ba700005a6172e7d5c0000001b4c00005ab0002d00a88d602116132f85e96f25329bec4998e2020e10047721c666ef15d84baa69c483800074825ce753151c50c8000b360cc21e6a34e2c244e44698af2777065c7ec298800027044258a9e2cae22eb0c295e08080b80aa0000000217883b0000bdb8f84b70a1860794eb8bbd279c9e50598ad6adba59500000aa876806e0dfe1c4a680761114e9a9dd06b178a5e14a6c041da8516af00b9e000050a72480006d626706080000192016ca5b00003e711305f5271900025ee000211583899203b7ab36000164d00000000001c28000000000020b821742c80002ac620924f01d6800075f8c1e52a1c87442800000000000c98770326c98a208032877f0000000167d2fd9cba3871c3200024883a0a0965638cd6b4d80009a2947e9e6a0f50f5a596b5c046642d27be0001f8cb4920d400012de0e217306928af122750667730c826cc80001b240000001cf6b0a40009fd80009778be46879430767a7383e68d9459b93ca6178000b16edfc64c168a
  | 49 => 0x4bf2326854ac425fe4a3000018628b599062d89ece2d09810a6384900002de000003482ca59ad5c68f7237d2eae7eaa76a000000002893320000adeaed5e1856a0000747800000022c400013fcaa313a2baa8a7c1cbaaa69ee881193813e5776a1188cb2d423ac8ec4303a72caed80008d5a4c043d86de79a00007f626ca97e000000000000002968000249a39880000002e5a6c5e1245252260817450247c594c2421ed7960e4025388358b412a96755446a1cf196428cc0000000308567291c22a9cec2a8058e0ba125a645a4560002ba470d269f24c2b525b5000e6598d7e51627540002cae67b82d308810620000000000200e0000128000000000000003588000000161aabe940aba912ee0d9000000000009b1a0dbb68231499f000043a97c615310bc15a2b48bcc13aa196a5ea914872c0000000b8280007959ec8000169d00029cabb7a174583890500000000001404a8742a68a1075000029229940e3446198f48851cca85c9c3e5f41e85701800000006c01c387ca9e4897aace56660f198502aa28da3658cc8a319fbc624981c0008ff85830386ad9aeb27ed9c5695619f25a79d0474a84bb6da200ba106ec47e6124daf98c762a380006ec9cc06aa281e158591868b0ee429d41d21ae00d6aff21be4ec96ce1ea90ec602000093b000084091239c60aa2b398874006c343b7987741a2210b1842b81775eb9e5618b229ec80005b8199e246a17e3bb52cc205035c0000c7d093e40a78c000068f2764b2e2a6e34d06d280646c620b286247e1478a149e961db9668000220ea73000076f00002ee811eb22ac9082f80000002eba56e80002c480007ca0f0aae895c200f13d84aa136a18c236bb8484c6a7f83be000096cb9c00001c7aaaa8aac8261f382d00000d92994ad1e0001d548e898be00026f82b10d441422934000067c2d2260f81c0000860c1c422caec880a669ea239980b87803013cdae87e9866757411d30002708b2b000047d00001958000358240600000009ce8000000134a085eb686d02b0a00010702c79eb5589a4580001bcc5820420704025c7950000b0f8000a2e8000a5f031867900000002254ac2dd0f8bb2cfa13ad94e444a9624dd09d87e4000045b05ba684dd494900f3e40900001fa97ecb6d000060c00006f993e2150a6c29d6adbc3a1622a4fc91507cd89e6236a8d3139410b73f9358661a598964cddc1a7a47030821f49c511fabb69c2201a96a8b7ba19f70aa40c71f446e1f111751949bfe9a48c527c4566969b084e24e17880002e0066c0340a7880004088dc046e421f2c966da5af0e6002fabb14729cfc0000fe700017b29022d7a9399b248e08f623cb25a086027f8996828a36c08d209a8a3638e1b825c640004c011720000977382203260f05e047d9e873bb028856b8bf200018760c42580416
  | 50 => 0xe0fa040dcd4e4f08000a1c0806ae404b90000000000000039aa12c000170a7a565fc91a04a4b891bf697480000fb80007d109660001896059a42c231a58f812000060a80005c8192a0002da22f412b4b64a58837800002a326df8dd80003aa1a90b03a4964d81078b2c933804cde364701c72000165c5afed6c06b12c8a1a064e8ee08f060c84034dcc7203da94d4924143a9f80872a179034763a01f0000c0a35c17985348000bd71e92a3127a682e81e200000000000fbe89042a0000000033680002df835400480006df40000002a5200000000000ed80000bb88f9173243604aa7078000000000063d687c0000e7400003e000007bc4c3e0f1758800019e000010c0000bc4255a0612cee8181470364144c1ec9e2e50403c85f984b09f08000000000081b8fe6a82a6fa00000001f5876994e18f66e020881298000782060784ea3065cfaca219e8f5205c971e1b32dca10b4e513c314c079f6b56060a23f7272822212e2f0234280c2e704e8950a63e0002362000056a19b8000bbf1eb100011b8000000052e800016d98fea840000acd25d80eb227cb3e00005c8a5f44a4806e8e8188252100000b18996a9018f258b2e3298bec6200024f499087c000005a9642576469524387598cbc1e7278c065189099000002e95ff47bcae5662b81a62b391d10000e800f15be20002cdc9950a6816214fa07d070f6d0456376b6b24b13cbe7000022684401243c597ae282a012816400090000001f7292471ede468aba76842a10fa99bae3600000d50000ff448328929f22f2a6d09f8a36f935c000124e0000fd0b7d29c443c0000adf0cd8000000089d013811e0000609063f2651b042902dac00000009ee2e1819bc00000023f47e1af765f4a10045a010e4790000157492b018255e8c0000000000000000f5097b000033f936fab10ba413619924c5800081e8fc445a953a322248c71a69c20b894f63be033690a9e6e18dd2965a02e92412e528a53984e397008180c111c84e0000000186a000205898dd48d0002a541568b472b90a56af51f745b318ac92480e8563063189f43995d823b69c69ac884a8519b290fcc0b61154898d148392279e73b9b5e9b9846f6031ba441f2d4a126293042f8a1e0e68ed415b6e0639e9bca27690f42d402d56cf8f395c18f3786722ce2401b78337871c1db230a884800065dae0e58dadd261a25007f710aa5a4113c2ccad0e8f2a184a9f000071e46e45e09a5245ba37e0928ea2b0c98bda07254e4f7000000017fa00027a80002f6088680005059ca9689100c80e070a964952666980000000d8a3130248000282c4d21a1c00022d100019fb45600007830000000099a3e149ec2b30000b792b08000180664bd0184a0151e523800005800002ba1c3084f83779869b8e5c62d303fc8f9e32b2e84558a1e830882f
  | 51 => 0xb83c9c0000179ea04a214508a2117e8d70d2688100003d3acd02b48a373cfdec2b5f0170226a7500000000306a9d873c65e279419b6a7a635a6f12c1d6c6deea4b5944e5eaa57700025362c9c0005091f54bada75e6168000bbb8ece2e8504a4e42688000001ca78c92e41cd2b01af29e54ada8f20780f49945a2ee27d175e17d2a90a26a547b30000061980468be023aab41cdc00014961b80a79000287d3500c55a3d80003138cb4b2497cc10f21a201609d0000000059169eb17f16520020c580001159000172c2261b0068200009e400009cf255c50b822a17c2240337236c45d1bce0000a0e22c0000481a6223251e748e1105aa01042f6c19ec5a8e2bea3f02a888a49e6635b4eca4d5226c36687069a42f4618d1ad423c80007eeab2279aa5877c184f000011dc00008406308bbf58f059e00025c93bf192ea5b8000000000095a84d6366489222929829591cd20001898618101d809894a0000000716ee22b23943c837ccfc3a240004da129877584fa07a00006a80d1605f000000010d086819f80001f720df0000533800010d0000979236a42040f046dd09cb7aa5624f196878999b74b4f110b0000e466f02778120800040787aeaf82f16982148868c0000ba8a68e5554df8a3712ecb58000021203e59aa8a392f300009671abeaead3118f208774c1a01ea7aa3e00001eb604161f212868d2a170ec321586d62e0ee1a874987a6b02db60001a7661d0d869fd1a603bc000041f99e290a09073bd1c5282a20140952caa0ec2dfa3eb23b400004ac457400018928ea00027ae7bdaf0207925e73269eaa95c29130fc21200290db843fac1f84c8d4c7a998b820e8bf0249c788000223cb96184443285a094b20cc267015e72920947a017369bfa2902c39d4a3751274516ac016564caa7e114bd5280dfa8542cca84ac9c64d308648be9dfe4c4ef1208da69d8832df01a2974e82c050429715f2b279e494975fd63885a8e52d483030085e65f26c613cf162a1052c35277109e00006597cb070088a29f4907a74a811a2d2732095e89a24d009d10089b39c5e169c3ca754a26e522c9ee4a388be923a63c79490583a913b6af8824caf78d08704c0406e3d2aea220a7b36600003b5a706241000046a85c4bab000048d23521d304e20001f64000000000021c09410d105a304fe2d8535e00012032068000000072a0db07e989f9b92a8d800002c89a62a20f10b8700004d36a148d826ea46d874eacf80002e31ed20002ed871887d859780003d6000054504a89801ebe1ee27d040845da2028000339973a1b75f460002b32066a020706000019f8000a12298b2758380a6240000001da200024a07ac000089400000002b0c00029a2000089e00007640c700001c05c8e0001c4a00000003d515eabdc80003e0944a69e29f6bb89854000053831
  | 52 => 0x242d4e9d080000000000962400061b2d5e779936600012a208ed10453f8a82a1600006e85f1985920351b100003cd8f3265f929a5508bbe9ef1b720c1299a03791600ce546455647e263c013cb9a9098976800052f952440a9d602331eb714d1abca27115b20f98001bb8c5a7ea1126b058cc40b3c072981800051b228e8e21312103000025d1c401251334adeab9200009920e08fce1b3df3a8f000000002dbe0000e8a437086913c53710e89bb47a08000ba60000a0280004ff8dc92b44836000098018f00001038000035c0000000000032800600003bc00000007208000000282a62da02a59e26849e90000a1592121888b8083c879856214e0808c52a000149ea9100004598000739a0f819180964519ca22b89014a7b22cc00000000001a4e222504900017341dfa78a007595d811000028500000001de247a800000000000000b36448992d7f699b13b6990d3d0831a230130c90b89fc948a7bd3a2007441749aa75b853638fe9423f914686cf290c223e8f4b1a125642b1f538eead6887b8c3401885eb0cfc5207b65efa63f10c258caa089b504ce97523365ab8b2406f0d7616f011a2d1572400e0afd52900001cd28ca3cd15974b025f09928000000000065e8000338ca3cab72c1449ea2181d29b504f90a8f00000009d200000001308a060f05ac18c18000134600021f04eb40002a59ed08390000b7600000000000b8400007111231000284600028a2000243c26b29dc05a80005f6ac5a6958728baf12ce8e79615079c0008c7a4c926bae28476929e096239821b027e55d000035e23187b81b7c0bfa0643fb1869862a76e000000013b00003c600000f50b4ebd6180e8a2e576000026e000000000018c600013ce00000000a11554000097baf400045d31094b159db496e8b23536918a9c09cf430024d211d8000adae2a698524223a9982693293c0000105e89e90b83fda494af615b0920ad7488e00002b68000b8e2022504800000000008da400021c0fa410b03cdb11862e0701a4c8b78cb8b02864a3dd1bdc084dce86d5804a098a3ac28752bc06c1edb9f709a8b1448f64868000aa39758ac6ad5a324a0e86e42bff3b71a9c23ce54a82da46e2e885c29e380f48841f9c12dceae64b2a6820085f2023a5814c410d48fb2d9e49b8ba351b8a7dae0138e31fad32000119804b691e07b296a5052cc41ee89ca3ab2bec6d701346a5133b36b00109c8108ea0c038429fc3a879e188c76b2498a921942587041897d800089ca63a1641e0d66b85c62582a6246100006a4898d38191207ae40d4b4700006fe800018146b04b604ae00000000000722395000029300000000028b0d85ee220952800002921ea2980a3600002be861e9100000b9b856c38b899ebc2951643b92ff7710e5300013561419e3235180008ff8b1410eec4a46254
  | 53 => 0xbdc00025c275b219e00003009ad80000001c84000290abae29a61f0a0a67a10e002e16b50392c5de22d1c8324519fc0000000ab28f1a7724bf83041662440101056f84107d6124c87e00c43c50000a55c000a8dc00089d6a3a00021b298d063d000215411c9ecc3cec1d68af0a1c57200006b300004cb239600013b06f78b168f70000581943466aa3bc71810c892a91d819a276000017c4000000055292a6a59249e0001ab243388097ed2816b449a1038098977c4a0c6833825e29c81fe00018f8adfd7845daab04045298f5d11232b1352a0ae827e670680ba7f2149a17222c23e382341880dec3608000b0ba74c74f2310467c000000089c542a34a0001498aad880470b94567b74c976978000000000000025ca6b7af388582e867c2964bac5a64e0000000b9d00000000396468905244964168f318181614ba0ba9a84e4e9a43eae505662dd0e988d180007f2996e63dc6600000000aea000000008ba60d2a92663000067014d6000000044084e0652a828af6a873863521e10e80000002722aeb1fe2aec80009042b4e5fc8d0e77d1e946fb81f030a185223d265c893a6a800027ac0251eee6fa8000781053c74a000000000004dd5b4451ead260a609b0b9ca55f8a711070270b6e844800002a0978000027f369ab38b42895c016a3207e502ff955000038caf845f2000092b863838623e853201a7a2e48e63490f64a58062a0fa25fe00000005cc55ee0ed9daa000000080094c69352aaca8367569b62a0b9dd0da8000061c1b62b3a0000000000269a11b1e0e0002a2a000201787f80000002dec43ec17b2198bc600029de08f277cb12298444a9d1f6830f946dcdb43378ef7c8bd1ce499887a47bf99cc00527de10b80000001a28418000078a15e00000990119d60442114d84ca92f114b8b94b0ada9a69c9e2c6cd982c39c80000ad8000184aa2e615931514f9a1f164a220a042788170cb1174317ee6d6ac960b516ba39b05a489e12100a90a9c088460360128ee7d201a1000000021880000bd04f62d825344940546103ea7a2e2a2004de8b9f6db12c21fc9b958818abc2df11a57621d7a0e41646b0a156f8d30e942d29ace0eaab37aa500dcb638e0a00002c981294f00f327d6000000047a228c797800000000000000d484e549a4964145e0002c760002baa41b0c700000feb9630f4a79c00006780c6d90c27988aa86ac1d596703a0c0002bfc1581d48f46bbd911e00010b04120263748800093607366919664a3b246200026f05c7000075bc00000011b58d9800078e29185f383c71d622430a5a9d0ae30b5e0220cc946327465530906be1861365828660000000888918b4eb0e241de00b0a3eaa1752087f640b63e25518e0e2639fee00000000000140507211cb125c7c8738e90a7693806750c4895b8c72000209264000002
  | 54 => 0xa1d522669ea8b13999cda9bd8000a8eec5c3792ce46f6067600ea30e89083fc5f8ab69222c0e4589230c8b91b0749b11e253b053a52484125ee1080029a83c0cb2b3054d2eb479013cc133007aa6e256050f8b728e19c2c1a429964a2a9701fddb7eb9785aa92d080c1d813e06998860819a33e34d8ffcaf90dc462a83c91d1a2c6986283282c80225de244ea2d282623ea230a8125141670efa4a3ca589c2a53348c00fe292110c4511728b26841e5441068725aba927ca166b350d1e1e0820486c0314473101a1301858b7d8bbd2521b930000a766bc1eb200024ee0480a2e00010ae4500baa65a953640e00003ed037a7d38000702a16e5d2901240b9a144038000000238e23d560d3090000b8b85320d18000a252cbc674240f54080000000650b69905f371a005873217601a049a2201ad604591d00a02
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa3e840c9650400147b08192ca082d69e602715941002c3f43e62b28200087d87cc5650400147d0998aca080028f61331594100053741662b282000a6d82cc565040010fd0e18aca080021f61c31594101ac3ec3ceab182035a5d839d5630406d4bf06baac60800a1fa177458c100043ec2ee8b18200087d87d5163040050fd0bb92c6080021f6177258c100043ec38a4b182000a3d8414963040014bb06292c6080021f6137654c100143fc1eeca98200287d83dd953040190fd05bb2a60800317ccb7654c100052fc1aeca98200087f845d9530406d0ff06bb2a60800317e0d7654c100643e412eca982000c5f325d9530406b8ee20bb2a6080d71d4417654c100043ec36e8a98200087e8759153040010fb0c392a6080024f6107254c100143f42eeca18200087d85dd943040050fd0abb286080021fe197550c100043fc3acaa18200087d875954304001c3886b2a860800e3721d6350c100bd4e422c6a18200c87f855d662040010ff0ab9cc40800a1f21573988100643f43ea7310200c87c87d4e62040190f90ea9cc408007179cd53988100062eb9aa7310200287e87dd562040010fb07baac4080321fa0b75588100643e416eab10203387e871d562040010fd0fa9ac40800a1f21f53588100043f43aa6b10200087c8754d62040670fd0e292c4080029760c52588100043fc1aed290200c87e825da52040190f904bb4a4080021fe1973948101562f31ae7290200087d8758e52040018bae6b1ca4080d21fe1d62948100043fc2aed190200287c855da32040010fb0dbac64080321fa1d658c8100643e43acb190200287c85dd932040010ff0abb2640800a1f215764c81010c7bc0aec990200087d86dd532040010fd0eb2a64080021f21d654c81001c6e43ac6990200595c8754d32040014bf0ca9a640800297619534c81000726a9cc499020038ec875893204001c9aa6b1264080031d997714c8100063ab2ee299020008f5861c532040018ecca38a64080031d594714c8100d66b318e29902000ce6621c532040079b4e0b1c620800a1fa1776884100043ec2eed108200287e855da21040010ff0cbac42080021fe1d65884100043ec3acb108200ca6c8259621040194d90b314420800e3be1d62884100e53642ac51082003cea7058a21040050f90bbb2420807e1f61b75484100043f43aca908200587c8759521040194d904b28420800f1e9c165084100dd3642ac41082000c79655c021040018f0ebbb220080031ee1776440100063c42eec8802000c7b53dd910040018f0a5bb220080033c947764401000678a8eec8802000c7b76dd510040019b6edb9a200800336dd873440100063dbb2a68802000ceb76dc910040019d6ec39220080031edda5244010005b8c2c4288020b4f605288510040015e70c90a2008002dce152144010
  | 1 => 0x4e1b164288086b520d62c85101c6733b0c590a2000ec46318b2144071bc4e0316428800e7ce1d70c85100143e42ced10a2000c6c529da21440390f90cbac42880031718d75885100043fc3ecb10a200887d87d9621440194dd05b2c4288003179d763885100062ebaec710a2000e4c52d8e21440394dd0bb1442880031b9d7628851000636baec510a200ca6c8518a21440018dcea31442880031b5d462885105bc3f436ea90a2000c5c63dd521440010fd0fb2a428811e1f21f65485100062fbaec690a2000c5c75d8d21440018deebb1242880031b1d7624851022674386c490a2000c6f7518921440018d8ea31242880031b14a760851006537416ca10a2000e4c52d8c21440374dd0bb1042880035914a76085101d732294ec10a203ab6682d9421440359a8c7b98428806a3d21973085100d56b436c610a2000f4452d8c2144001caeca31842880039519463085100074bb20c610a2000e946418c2144001e88a431842880029d21953085103ff1a322a610a2000d557354c2144035ca8c6a9842880ead920953085103b76231ce410a2038be2809c821440071eb0fb1042880eb9994b62085101d732296c410a2039b6685d882144001ccecbb10428800399197620851000763b1ec410a2000ec463d8821440715cb0fb1042881133961f62085100073342ec410a2000e6585d882144001ccea7b1042880039954f62085100047bc3ac410a201aad48358821440015cd0c3104288003399d862085101d5b2428c410a2000ec46318821440015cd0d19042880ead921632085103e7523246410a201aec4638c821440015c90c99042880e6d921532085103d7523226410a201aec4634c82144001e8aa699042880033918b714c110004bac28e29822000cd7631c530440019c8c438a60880025d61671c811006672314e3902200087f855d920440050f90abb2408800237e0d764811000c6e41aec902200287c851d920440199d0403b240880021fa1b75481100062e31eea9022033d7010dd520440010fd0fb2a40880021f21f654811023f34106ca9022000c5f75d8d20440018b8ebb1a40880031bdd76248110006363aec49022000c6f7518920440018d8ea31240880033518f71481100066a318e29022000ce7621c5204408f8f4edb2e208811f9cd8765c411020e6d3b6c78822001cda7618f10440038f4eca9e20881133a9db62c4110066753b0c588220b6f605208710440010fb09b9aca080321fa0b73594101b63b886e6b282036c7510dcd65040018bee739aca080021fa1e43594100043ec3c86b28200087e8710d65040010fb0e21aca080029ba08435941000536c1086b28200c87e87dc965040014bd06392ca080029760c725941006637390e4b28200087e87cc965040010fb0f992ca080021fa1c32594100043ec3864b282000
  | 2 => 0xf629491000536c3ec52922000c6d87d8a52440018dae7b14a4880039960762949100043fc3ac52922000a5f8358a52440554b906b14a4880029ba186294910006373b0c5292200cc6c7618a5244001c9ec6314a4880039318c62949100143f42ced192200087d859da32440010ff0abb4648800a1f215768c9100045fc22ed19220178bc845da32440191d904bb464880021fa1b758c9100061e326eb192202ac5c63dd632440198d8c5bac64880321fa1f658c9100643e43ecb1922000c3f75d923244001878ebb24648800317dd7638c9100062e3aec71922000c6f75d8a32440018d8ebb14648800a1fa17764c9100043ec2eec99220178be84dd9324400117b09bb2648800a1fa16764c9100043ec2cec992200087f855d932440050f90abb264880022fe11764c9100bc5e422ec99220008ef825d932440011ef02bb2648800a1f214764c9100d47a408ec992200087e86dd53244001878c9baa64880ab1718f754c9100043f43eca992200087c87d95324400187eebb2264880030f1d7644c9100646f43ec69922000c5f75d8d32440018b8ebb1a64880225721d534c9100052f432a69922000a5c8654d32440018bceca9a6488003171d9534c9100070fb22a6992209be1c6454d32440031dd0fb1264880031bdd7624c910006363aec49922000e4d53d8932440018deea31264880031b1d4624c91000726a98c499220038f686dc532440018eecbb8a64880031d197714c9100065bb26e29922000cb464dc532440439a8c7b8a64880033918b714c9100063bb28e29922000c74651c5324400196ec838a64880032d190714c9100066bb18e2992201acd4631c532440019cec438a648800339188714c9100072a31ecb18a2000e9463d923144001d28c632462881a39518d548c51000d6b436c718a2000cd676d8e31440015a90ca1c62880873518e728c51001cf9404e518a2000ec463d8a31440019ccec3146288003a9190628c51000762318c518a202ae546394a31440839b0e1b1a628811f1d1db654c5100072a31eca98a20038f4865d131440073e100ba262882e72d1db644c5105c65a3b0c898a2000e946319131440d38e8ecaa26288007351db734c51020e6a3b6c698a203ad64521c931440899c8edb1262880e3391d8624c51000752320c498a2000ec46318931440678e8ed292628810774dcc704c51023e3b3b6cb90a2047d7270d9721440071ed0db9e428800e7ca0373c851010e6a31ae790a2021ad686d8f21440839acedb1e4288107749c363c851022e6b3b0c790a2000e576518f2144001ca8ca31e4288003a5d9063c85100074a320c790a2045dd27018f21440014e90ca9e42880d71d9d953c85104471a322a790a2000d557354f2144043ca8c6a9e42880d75c9c153c85101d733296c590a2000e6765d8b2144089bc
  | 3 => 0x63122000a6e8518c62440014db0a318c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891000727428c63122000e4d8518c6244001c9eea318c488003931d4631891000762c08c631220baec77118c6244175d8c20318c4882ebb1040631891000537436a63122000a6c86d4c62440018dceda98c4880038bd93531891000716326a63122000e4f63d4c6244001c98c7a98c4880029ba19531891000536432a63122000c6e7654c6244001c5ec8a98c4880038b191531891000727b1aa63122000e4c6354c6244001cc8cb288c488003b118e51189101c4f243aa23122038ae4865446244001d88c6a88c4880329ba1675189100053742ce63122000a6d859cc62440014df0ab98c4880029b215731891000573c0ae63122000ae681d4c62440015cb03a98c4880329ba1f53189100653643ea63122000a6d84d4c6244001ccd03a98c48800399607531891000536c2ca63122000e4f5394c62440194dd0ea98c4880329b21d531891000537c22a63122000e4f8354c6244001c9ce6a98c488003935cd531891000537428a63122000a6e8590c62440014db0b218c488002b9a06431891000572c0c863122000a6e8550c62440014db0aa18c4880323ba1c431891000476c38863122000a6e8510c62440014db0a218c488003a350c431891000537c2ae23122000a6c855c46244001ccea3288c4880723be1d51189100647643aa2312200c8ee87cc462440011db0f988c4880029ba17311891000536c2e623122000aae84cc4624400155b09988c4880029ba14311891000536c28623122000a6f855c062440014d90ab80c4880e39a94350189100053742e603122000a6d85cc062440014df0a880c4880029b215101891000567c1a203122000acc8344062440190fd0d3b4a4880329b20a769491000637394ed2922033a75819da52440010fb073b4a4880321fa0a76949100643e414ed2922000c6c829da52440758ed033b4a4880031d60676949101d63b90ced292203ac74219da52440014bf06bb4a4880aa9720d769491006536412ed292200087e861da52440010f90cb9ca4880030f19173949101562e31ae7292200cc6c625ce52440010ff0fb1ca488003175cf63949101552f436c72922000c5e76d8e52440018b8edb1ca48800387d9363949100062fc3ec72922000c5c87d8e52440018bae9b1ca488003179cb639491000727396c7292200087f8758e52440190f90eb1ca4880028fe1163949103351e422c72922000a6f8258e52440194d904b1ca48800297a1863949100062f3b0c72922000c5c7618e5244001c3ec831ca4880038719063949100043ec3ec52922000c6e72d8a52440674eb03b14a4880329ba1b6294910006373b6c52922000c6c76d8a5244001c9ec7b14a4880039318
  | 4 => 0x2440018dcebb14c4880031b5d762989100066739ec53122000ccd73d8a62440010ff06bacc4880321f20975989100062f42ae73122000c5d855ce62440198bca4b9cc4880331714973989100143fc3ea7312200087d87d4e624413f87ce9a9cc4880030f5d3539891000e2f39ea73122000c5d73d4e62440010ff0ea9cc4880021f61d53989101661f3a2a73122000c3d7454e62440038bce6a9cc488003175cd53989100143f436eab12200087e87d9562440018b8e7b2ac4880021fa1c65589100062e398cab122000c5f65dcd62440018b8cbb9ac48800237a1f63589100062fbaec6b122000c5c75d8d624400193ee9b1ac488003271d363589100046f438c6b122000c5f7518d62440018b8ea31ac48800327dd063589100064e3a0c6b12200087d83dd562440011bf06baac4880063720d755891000477c12eab122000c5f75dcd62440018b8ebb9ac48800327dd373589100062fc2ee6b122000c5c85dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd62440010fd0fa9ac48800a1f21f53589100061fba6a6b12209fc3c74d4d62440018bee7a9ac488007171cf53589100043f43aa6b12200087c8754d624400187ee8a9ac4880b30f1d153589100062fb9aa6b122001c5c7354d62440018deebb92c4880031b1d7725891000667b9ee4b122000ccc73dc962440014bb06292c48800317dcc525891032e2e398a4b122000cd473dc562440050fd0b3b0c4880021f616761891006537416ca312200ca6e8219462440018b8ebb18c488003171d4631891000477c3ac43122000a6f8558862440014d90ab10c488002b3e0d62189100056641ac43122000b4d831486244001c9ec6290c4880039318c52189101d6b2388a4312200c8ec825d462440010ff0ab98c48800a1f215731891006476412e6312200c87e87d4c62440190f90fa98c4880329ba0b531891006536416a6312200c87c8754c62440038bce6a98c488003175cd531891006536412a6312200ca6e85d4862440014dd0b990c4880029b617321891000726a9e643122000a6e859d862440014db0b3b0c4880031ba16761891000636c2cec3122000a6e861d462440018dcec3a8c488002d360c7518910006373b6ca3122000a6d83d9462440011db0f328c488002b3a0e651891000566c1cca31220008ef87594624400159f06b28c488002b320d6518910006373b0ca3122000a6d831946244001ccb02328c488003339db631891000727b2ec63122000e4c65d8c6244001d1ec9b18c48800393e1763189100072642ec63122000e4f75d8c6244001c98ebb18c4880023b61e63189100053742cc63122000a6d8598c624400155d09318c488002ab612631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c
  | 5 => 0x80029ba1732d891000536c2e65b122000e4d53ccb62440014dd0a196c4880029b61432d89100055742065b122000aad840cb62440018eceab8ec4880031d5d571d891000732292e3b122000b4d839d762440014db0fb2ec4880029b60f65d89100056741ccbb122000acd83997624400159f06b2ec488002b320d65d891000536c18cbb122000e65811976244001c9ecbb1ec4880039319763d891000747b26c7b122000e4f85d8f6244001c990bb1ec488003939d763d891000726baec7b122000a6e8598f62440014db0b31ec488002aba1263d891000556c24c7b122000a6f8558f62440014d90ab1ec488002abe1163d891000556422c7b122000a6e8518f62440014db0a31ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec48800393a1463d891000726c28c7b122000e4e7518f6244001c9aea31ec488003b160463d891000537436a7b122000a6c86d4f6244001c5ec9a9ec4880038b19353d891000727b1ea7b122000e4c63d4f62440014dd0ca9ec4880029b21953d891000717b22a7b122000e2c6454f6244001c9ec6a9ec4880039318d53d891000733b2ae3b122000e64655c76244001d8ec6b8ec488003b118d71d89100073232ca3b12203c9e78754762440895c90ca8ec488002b9a0775d891022572c0eebb122000ace839d7624400159b073aec48800393a0e75d891000536c1cebb122000e4d839d7624400149b073aec4880031be1d75d891000537c1aebb122000ae6811d762440895cb023aec4880029ba1773d891000536c2ee7b122044ae581dcf62440014dd0b39ec4880029b61673d891000557424e7b122000aad849cf62440014dd0a39ec4880029b61473d891000573408e7b122044ae5811cf62440014df0fa9ec4880029b61f53d891000536c26a7b122000e4f5394f62440014df0ea9ec4880029b61d53d891000537c22a7b122000e4f8354f6244001c9ee6a9ec488003931cd53d89100053742c87b122000a6d8590f62440014dd0aa1ec4880029b61543d89100047743887b1220008ed8710f62440014dd0a21ec4880029b61443d891000746a1887b122000e66755c76244001ccaeab8ec48800399d4d71d891000732a9ae3b122000e675194762440371df0ea8ec4881123b21d51d89102247743e63b1220008ed87cc762440014dd0b98ec4880029b61731d89100055742663b122000aad84cc762440014dd0a18ec4880029b61431d89100053742ee1b122000a6d85dc362440014dd0b986c4880029b61730d891006636312eb3122000c5e73d9662440018bce632cc48800317d9573989100062e32ae7312200cccc625ce62440018bcebb1cc488003175d763989100064f3a6c73122000c9d74d8e62440018bcea31cc488003175d463989100064f3a0c73122000c9d7418e6
  | 6 => 0x2d6a432a231a2000bc482544634405947d09bb2a6880028f6137654d1000537416eca9a2000a6d82dd953440010fd0d3b2a6880031718e7654d100052ec1ceca9a2000c5f739d953440010fb093b2a6880021f60e7654d100062ec1ceca9a200c87e829d953440018be653b2a6880028fe117654d101651e422eca9a2000a5f835d953440014df04bb2a6880029b2097654d100043f430eca9a2000c5f731d953440010fb083b2a68800a1fe0c7654d100062fc18eca9a200287d831d953440018b9063b2a6880321fa087654d100062f990eca9a2000c75811d953440018ec623b2a6880031d4c47654d100043f436e8a9a202cc3c64dd153440d58b8c7ba2a6880021f21f6454d100061fba6c8a9a202ca3e86d91534400187cedb22a6880030f1db6454d100070e31ec8a9a2000c3f87d9153440018790fb22a6880030fdcf6454d100070fb9ec8a9a2000e1f32d9153440010ff0eb22a6880021f21d6454d100052fc1ac8a9a2001a5c8359153440014df04b22a6880029b2096454d100051f430c8a9a2000c3e761915344001878ec322a6880038718c6454d1000d2f436c6a9a2000c5c76d8d5344001c3ec9b1aa688003871936354d100062fc3ec6a9a2002a5e87d8d53440054b90fb1aa6880031721f6354d100062fba6c6a9a2000a5d82d8d53440010fd0c392a6880024f6107254d100061fb20e4a9a2000c3c641c953440018bec6392a6881971718c7254d100063a3b4e2a9a2040b55839c5534406b4e90cb8aa68810ed5e0d7154d10005b2412e2a9a200287e85dd943440010fb0bbb286880323ba0b7650d1000476c16eca1a200287c859d94344001938873b286880021fe157650d100143e42aeca1a20008df835d943440011df04bb286880323b2097650d100143f428eca1a200087d851d94344001938863b286880021f2197550d103462e31aeaa1a200087f87d9543440010fb0fb2a86880038710f6550d100bc6f43ec6a1a2000c5e75d8d43440018baebb1a868805ea7a136350d100443ec3ecbb122000a6e82d9762440014dd0432ec4882df1d5c465d89100062f3aec7b122000c5d75d8f62440018bcea31ec488003175d463d8910005a6c18a5b122000e4f6314b6244001c98c6296c48800e3d60775d89100052ec1cebb12200087f835d762440018df04baec48800a1fe1f53d89100043ec3ea7b122000a6e82d4f624406d8eae3a9ec4880021fe1d53d89100043ec3aa7b122001c5c7354f62440014d904a9ec488002b960752d8910016373aca5b1220028ef8754b62440014bb06296c4880d31d5c452d891000636ba8a5b122000ace8314b624400159b06296c4880029b61c52d891000636c38a5b122000e4e8314b62440014db06296c4880039360c52d891000526c18a5b12200cc6e7114b62440198d8e2296c48
  | 7 => 0x5a50d4363440014bd0ba06c6880029761740d8d100062e31eeab1a200087e87d956344001878e9b2ac6880021fa1c6558d100061e3a0cab1a2000c3f65dd16344001878cbba2c6880032718f7458d100061fbaec8b1a2000c3c75d9163440018decbb92c6880031b1977258d1000657b26e4b1a2000ccc63dc963440018deca392c6880031b1947258d1000657b20e4b1a2000ccc631c963440050fd0fbaac6880021f6137558d100643f416eab1a20008bf845d5634402f17908baac68800237e0d7558d1000477c12eab1a200c8ec825d563440010fd0e3aac68805e2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187f0bba2c6880030f2177458d100061fa9ee8b1a2000c3d53dd1634400187eea3a2c6880030f1d47458d100043f43ea8b1a200287c87d51634400187ee9aa2c68805f0f1d35458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d100143f42ee4b1a200087d85dc963440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc9634400199ee7b92c6880031ba177258d1000636c2ee4b1a2000c6f54dc963440018dea7b92c6880031b54f7258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a200cc6f851c963440198d90a392c6880031bd507258d1000637a98e4b1a2000c6d531c963440010fd0e292c6880321f21c5258d100051ec20a4b1a2000c3f741496344177878e8292c6880029760c5258d1000637b90a4b1a200cc6c7214963440019c8e5b8ac688003179db6518d100052ec3eca31a2000a5d84d9463440014bd05b28c688003955c76518d100046ec3cca31a2000a5e85994634400153d09328c688002a76126518d1000567414ca31a2000acd8299463440011bf0eb28c688002a7e116518d100054e422ca31a2000acf82594634400159904b28c68800297a186518d100062f3b0ca31a2000a5f8719463440014bb08328c68800297a086518d100072ac08ca31a2000e56711946344001caae2328c688003279db6418d100070fb2ec831a2000e1c65d906344001c3f0bb20c688003872176418d100070f3aec831a2000e1d75d906344001d2ae3b20c6880023761e6418d100052f42cc831a2000a5d85990634400153d09320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc8259063440014bd0a320c688002976146418d100064f3b0c831a2000e1f651906344001c38ca320c688003879d46418d100070eba8c831a2000e957119063440014bd0daa0c6880029721b5418d100070fb26a831a2000e1c64d5063440012bb0e290c68800297a185218d100058ec20a431a2000e1f641486344001c38c8290c688003951965118d102
  | 8 => 0x598eca880021fa1c31d95100443ec3863b2a202da7681dc365440010fd0f986ca880021f61f30d951000e2f3b6a7b1a2000a5d83dd763440014bb063aec6880021fe1574d8d100143e42ae9b1a200087e87d5363440014bb07aa6c688003175d753d8d100056ac0ea7b1a2000c5d87d4f63440014bb09a9ec68800297a0b53d8d100072b40ea7b1a2000e5581d4f63440051bf0ea9ec68800297a1743d8d100052ec2e87b1a200087f855cb63440050f90ab96c6880021fa1c52d8d100051ec20a5b1a2000a5d8314b63440014bd0c3aec6880029761365d8d100052f416cbb1a2000a9e84997634400153b0932ec688002b3a0a65d8d1000566c14cbb1a2000a9f84597634400153908b2ec688002b3e0965d8d1000566412cbb1a2000a5d8419763440014bd0432ec6880039560465d8d100070fb2ec9b1a2000e1c65d936344001c3eebb26c688003871d764d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052f428c9b1a2000a5d8519363440014bd0daa6c6880029721b54d8d103562f3b6a9b1a2000e1f64d536344001c38c9aa6c68800257a1c52d8d100052f430a5b1a2065c5e7614b634400163b08296c68800387d9052d8d100072a32ca3b1a2041ad486547634400178904a8ec6880029761375d8d100052f416ebb1a2000c5d751d763440015ad023aec688106b560475d8d100062f438ebb1a2000a5d841d763440014bd043aec68800395a0475d8d100072ac08ebb1a2000a5e859d363440014bb0b3a6c68800327dd274d8d1000567414e9b1a2000acd829d363440014bf0aba6c6880029721574d8d100052f428e9b1a2000a5d851d363440015ad023a6c688106b560474d8d100052f43ea9b1a2000a5c87d5363440014bd05aa6c68800387d5254d8d100052f42ee5b1a2000a5d85dcb63440018beebb96c688106b560772d8d100052f42ce5b1a2000a5d859cb634400153d09396c688002a761272d8d100052fc2ae5b1a2000a5c855cb63440018beeab96c68800237a1c52d8d100046ec38a5b1a2000a9e8414b634400153b08296c68800297a1c52d8d100062f438a5b1a200085e8714b63440018bb0e296c6880029721c52d8d100070f420a5b1a2000a5d8414b6344001c3b08296c6880028761052d8d100052f42e85b1a2000a5d85d0b63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b63440014bf0ab8ec6880029721571d8d100054fc22e3b1a2000a9c845c7634400159f04b8ec688002b320971d8d100072ba8ca3b1a2000acf82547634400159904a8ec68810637a1f41d8d100046ec3e83b1a2000a5e85d0763440014bb0ba0ec688002b3a0b41d8d1000566c1683b1a2000a5e8510763440014bb0a20ec68800297e1570d8d100052e42ae1b1a2041e
  | 9 => 0x768cb100043ec2ced196200087f855da32c40050f90abb465880323b209768cb100143f42cec996200087d859d932c402f17d093b265880022f612764cb100043fc2aec996200287c855d932c400d2b90ea9a65880063ba1f624cb1000d6741ec49962000e4d53d8932c4001c9aa6312658800e3d618714cb1001c7ac36e918e2069c757655231c40678eaed29463880025d617764c71025eb2290e498e2000977855db21c40431ef0cb9e4388003555cd53c87100e53642ac510e201ba6c8558821c40199d4c4b80438812f99149760871001c7ac36e610e2035c757654c21c4001aaae6a98438812ed9209530871001c7ac3ec410e204be6452d8821c40011ef0eb10438812f99949620871017db242ac410e2000ae5868c821c40976c90b1904388002b9e19320871017db242a6410e2000f45534c821c4097ec0a5380438812fd81497008710004bac28e298620448ef8758b20c40012eb0b38e41880e23ba1e62483100143f42ee4b1c200087d85dc9638400147b08292c7080029760c5258e100052fc1aeca9c200093d841c953840050fd0bbb287080021f6177650e1001c6e43ac6a1c2017a9c8458d43840071d904bacc5080329b20b5398a1000e2f39aa73142000c5d7354e62840194d904a9cc5080329ba175298a100143f43eeab14200087d83dd562840678db05baac5080ce1fa1c7558a100043f43ea6b14200287c87d4d62840010fd0ea9ac5080021f21d5358a1000536412a6b1420038ee87d4962840670fd0e292c5080029760c5258a1000637ba8a4b142000acd8314962840674dd0e292c5080031ba1c5258a1000727418a4b142000a6d831496284001c9b06292c5080029360c5258a1000637392ed294203487f8758a52840698dce4b14a5080021fe15768ca100143e42aed1942000c6c7558a32840010ff0abb2650800a1f215764ca10054ae43aa69942000c6c759893284001c9aa7312650800e3b21d624ca10006363aac49942001acc835893284001c9aa6b1265080033998b714ca101c477c3ac590c20448ee8798921840018d8eb31243080031b1d562486100051f424c7b2a2000a3d8498f65440014dd0531eca880029b60a63d95100443ec38c7b2a2000c5d7318f65440012bb07396ca880021fe1173d95100643e412e7b2a2000c5d731cf65440874ed0239eca8811e9d60473d95100043f43c87b2a200087d8790f65440010fd0e21eca880021f61c43d95100053741087b2a2000a6d8210f65440794ed03b96ca8811e9d60772d95100052f41ce5b2a2000a5d839cb65440198dce4396ca880021fa1f32d95100043ec3e65b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a204787e87cc765440010fb0f98eca880028fa1331d95100051ec2663b2a2000a6e82cc765440014db
  | 10 => 0x18a400287c855da31480050fd0bbb262900021f617764c52006674104ed90a403487c865d621480010fb0fb2c42900039914861885201a43f436ea90a400087e87d9521480678f4edb2e4090003d254d32c81200052ec1ea8b1840038dc8754d63080031db05b8ac61000a1fa147158c200043ec28e2b184001a5c83dd953080014bf06bb2a6101ab1798f7454c200152f43ac6a984002a5c8758d53080018bee8b1aa61000697e096354c2000d2ec12c6a98400cc5e7258d53080198b8e4b1aa6100d793c816354c201af26902c6a98400287e85dd943080010fb0bbb2861000e3e2017650c203462f31aeaa18400c96c825d543080071b90eb1a8610003175d56350c200bd4e422c6a18400c95c8754d32080298beeca9a6410032d3209534c8200a727312a699040038f58794661080058eceb28cc210032b920951984200143f43eeab08400087d83dd561080391df04baac2100021fa1f53584200143e43ea6b08400087e8754d61080010f90ea9ac21000b1d1d6515842001c7a43aa2b08400cae48254561080010ff0abb4621000a1f215768c42001c7ac3cc3188400087f855d931080050f90abb2621000e3d21d614c42000726b1aa7108401ca6c8558621080015cf02b1842102f3b1cc5630842000726b1aa6108401ba6c8558421080193d70cb8042100033ae197008420006b5c2ae01084000d68855c021080199d6c6b8042100033a58d7008420006b5a9ae01084000d69535c021080018f0ebbb240100339a94b76480200063da9eec900400cc7a52dd920080198f0a5bb240100031eddb7548020065b4416ea9004000c7b7654d20080016d70a90a40100021fe1572d8f100143e42ae5b1e2000a3d8414b63c40014bb06296c7880029760f5458f100143f42ee4b1e200087d85dc963c400147b08292c7880029760c5258f100052ec1ceca9e2000a5f835d953c40034bd07b22a7880029760f6454f100049ec20e4a9e2035a75869c553c40018eeed38aa788142d560e7154f10295abc1ae2a9e2000b64825c553c40050fd0bbb287880021f6177650f1006477416eca1e20008ed82dd943c40050fd0a3b287880021f6147650f100bc6f43ec6a1e2017a9e84d8d43c40010ff06baec58800a1fe1f53d8b100043ec3ea7b16200087f8754f62c40010fb0ea9ec5880029760c52d8b1000e2f39aa73162000c5d7354e62c40050fd0fbaac5880021f60f7558b1001c7a40aeab16200087e871d562c40010fd0fa9ac58800a1f21f5358b101b63a38ea6b16200087e8754d62c40010f90ea9ac5880029760c5258b101a63a388a4b162000c77751c562c40018e8ea38ac5880023be1d6218b1000e2f39aa63162000c5d7354c62c40674e902bb4a58812f1d1c57694b100043ec3ec5296200087f8758a52c40674e902b14a58800a1fa16
  | 11 => 0x480010fb093b2a6900021f60e7654d200062ec1ceca9a4000c5f329d9534800147f08bb2a6900b28f2117654d200052fc1aeca9a4000a77815d953480014e902bb2a6900021fa187654d200043ec20eca9a400287f831d953480050fb063b2a6900321f2087654d200062f990eca9a4000c6e321d953480018da643b2a6900021fa1b7454d201661e326e8a9a400087c87d91534800187ee9b22a6900021fe1d6454d200043e43ac8a9a4000a5f8359153480034b906b22a6900029de056454d200053a40ac8a9a400287e85dd943480010fb0bbb2869000a1f2167650d200064e21ceca1a400087f855d943480050f90abb2869000237e0d7650d200047bc0aeca1a40008f4815d943480011f700bb2869000a1fa147650d200043ec28eca1a4000c9c431d943480010f90cbaa86900021fe1f6550d200043ec3ecaa1a4000a5d83d954348001c3887b2a869005e3721d6350d200bd4e422c6a1a4000ad48158d43480198f6c13b4a4900335a08276949201543e432e7292402ac5c635ce5248019a9c64b9ca4900021fe1f63949200062eb9ec7292400087f8758e524800147f08b1ca49019a8f21163949200053bc0ac72924000a748158e52480190fd0fb2c64900321f21f658c92000d6641ac91924000ae4815923248001a5ae8aa464900d21fa1b754c92032c3f43eca992403387c87d9532480192b90ea9a649000297a19534c9200052e432a69924033c6c769493248055c98c729264900cf5a1c2524c9200063bb2ee29924000c7465dc532480018eeca38a64900031d194714c9200066bb18e2992401acd4631c53248001ac8a438a64900ab1b1db754c9201572631eea9924033c6c76d953248001c98c7b2a649000e3b219744c92001cf4402e89924001acc83d913248001d1c87b2264900063b21d644c92000d6641ac89924000ae48159132480d38d8ecaa264901a39318d544c92009567436e69924001ace86d8d324801969d0ea9a6490166d321d534c92000727c32a69924000b4e8654d32480016990ca9a649000393219534c92000526432a69924001e4f7654d3248003c98eca9a6490002d3e11534c92000727b22a69924000e4d6454d32480015990ca1a6490002d3615434c92000746b22869924021ce476dc53248043d88c7b8a6490003d154f714c9200d6723b0e29924000d64751c53248035d88c638a6490003d154c714c920007a4a9ee09924000d6b751c13248001e92a6382649000378dc4704c9200052ec18a5b0a4000ab684cc761480050fd0dbaac2900021fa1f65585200062e39ecab0a400087e8719561480018b8e632ac29000317d9773585200062e32ee6b0a40008f78758461480015a906b08c2900323b20975185200052ec18a430a4000e4d534c8614800156d09988c290002b960b31185200043fc2aed
  | 12 => 0x31d5d6618862000732294c310c4000c767558621880018eaeab0c4310003999496188620006b5292e110c4000cf2615c221880014df0cbac43100729ba15638862000537c32a710c4000d69755c221880010fb0dbaa43100021f21d65486200063bbacc290c4000c747598521880018eeeab0a43100031d1d5614862000678b0ee090c403ae66525842188075cc8a4b08431006e9ba15630862000537c32a610c4073e66659c421880017c301388431000399d4d610862000732a9ac210c401187d8718f654800147d0831eca900028f61063d95200062eb98c7b2a400087f845cf65480190f904b9eca900028fa1073d95200051ec20e7b2a4000c5d731cf654817d4dd0439eca900ce9b60873d95200043f43c87b2a400087d8790f65480018bae721eca900021fa1c43d95200043ec3887b2a4000a6e8210f65480014db0421eca900ce1fa1f32d95200043ec3e65b2a400087e870cb65480230fb0e196ca900028fa1032d95200051ec2065b2a40bda6e82dc765480674db05b8eca900031d5c471d95200043f43e63b2a400087d87cc7654800147d0998eca900028f61331d95200053741663b2a4000a6d82cc765480010fd0e18eca900021f61c31d952029d37416e1b2a400087e87cc365480010fb0f986ca900029760f75d8d200052ec18ebb1a400087f855d363480050f90aba6c6900021fa1f54d8d200052ec1ea9b1a400087e8714b634800147b08296c6900029760c52d8d200143f42ce3b1a400087d859c763480010ff0ab8ec69000a1f21571d8d200045fc22e3b1a40178bc845c763480191d904b8ec6900021fa1f6558d200061e3a6cab1a400087e871956348001878e832ac6900030fd977458d200061e32ee8b1a4000c7765dc563480018e8cbb8ac6900031dd947158d200063a328e2b1a4000cd4631c563480050fd0fbaac6900021f6137558d200045fc22eab1a40178bc845d563480011ef02baac6900023d2057558d200043f438eab1a40178be87dd1634800187eebba2c6900030f1d77458d200061fc2ee8b1a4000c3c85dd1634800187ea7ba2c6900030f54f7458d200061fba8e8b1a4000c3c751d163480010fd0faa2c69000a1f21f5458d200061fba6a8b1a4017c3c74d516348001938e9b9ac6900021fa1c5258d200051ec20a4b1a4000c3f741496348177878e8292c6900029760c5258d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200063baa6e2b1a4000c7753dc563480018eaa7b8ac6900031d14b7158d200063bba8e2b1a4000c74751c5634800196ee838ac6900032d1d07158d200066bb98e2b1a4000ce7721c563480018eea838ac6900031dd4c7158d200063aa98e2b1a4000cd6431c563480018e8a438ac6900032e1d37058d200043f434eca9a4000a5d839d953
  | 13 => 0x573c12eb30c4000ae4825d661880075e5003acc310002bc60075986200053b42ce730c4000a75859ce618800156d0939cc310002ad612739862000573414e730c4000ae5829ce61880014ed0a39cc3100029d614739862001d79400e730c4000af1801ce61880014eb09a9cc31012e9da0b53986200072ba9ca730c4000a778454e6188001caf06a9cc31012e9d20953986200053b42c8730c4000a758590e61880014ed0aa1cc3100029d61543986200053b4288730c4000a758510e6188001d2a8621cc310002b9a08439862000572c108730c4000a7685dca61880014eb0bb94c3100029d60e52986200056b418a530c4000ad58314a6188097cad06294c3100029d60c529862025f2ac18a530c4000a558314a6188097ccd04294c31000399dc852986201a733900a530c4034e652014a61880014ed0b994c3100029d61732986200072aa9e6530c404ba77858ca61880974e90b194c3100863de1d32986200d47a43a6530c4000a77854ca61880014e90a994c3100039554d32986200053b4286530c4000a75850ca618800156d08194c310002ad61032986200062fb9aa6b0c4001c5c7354d61880014bb06292c3100031ddd7515862000572c16a2b0c4002c767594561880071e90ea8ac3100029da1731586200053ac2e62b0c4000ab684cc5618800156b0998ac310002b960b31586200053b42862b0c4000a75850c561880018eeeb3aac310002b5a0e75586200056ac1ceab0c4000ae6829d561880015cb053aac310002b9e09755862000572412eab0c4000a76859cd61880014eb0b39ac310002ada1273586200055ac24e6b0c4000ae6829cd61880015cb0539ac310002b9e0973586200053b428e6b0c4000a75851cd61880014eb09a9ac3100ea9da0b53586200072ba9ca6b0c4000a778454d6188001caf06a9ac31000395dcd53586200072a39aa6b0c403aa748254d61880014ed0b21ac3100029d61643586200053b42a86b0c4000a758550d61880014ed0a21ac3100029d61443586200074aa1886b0c4000ae68210d61880015cb0421ac3100029de1572586200053a42ae4b0c4000ad7835c961880015a906b92c3100029d60e52586200056b418a4b0c4000ad5831496188075cad06292c3100029d60c52586201d72ac18a4b0c4000a55831496188075ccd04292c3100029da1732586200053ac2e64b0c4000e5553cc961880754ef0b192c3100ea9d216325862010c7bc3a64b0c401a8f4874c961880014ef0a992c3100029d21532586200072aa9a64b0c4000a76850c961880014eb0a192c310002ada1032586200055ac2064b0c4000ec5320c961880071eb0f30c63100031b997724c62000637328e498c40038f48758531880019c8e4b0a63100021fe1975886200043fc3acb10c4058a6d8694a21880018eceb30c4310
  | 14 => 0xe635d543c80191b90eb1a8790003175d56350f200bd4e422c6a1e4069c6d7655232c8001a5ae8aa465900038b591548cb20064ae43aa6996400dc5f7654d32c8183ac8a438a659000e7a201744cb2000716b22a8996400cb4e8754d32c80196990ea9a659000393e19534cb2000726432a69964000d4f7654d32c801bc9eeca9a6590002d3e11534cb2000727b22a69964000e4d6454d32c800169b0aa1a6590003a3591434cb20007a2a9ee29964054ce7761c532c8001ac8ea38a6590003d154c714cb20064b6412eb30e400ca6c825d661c80010ff06bacc3900031be09759872000636412eb30e400287f87d4e61c80010fb0fa9cc3900021fe1d53987200043ec3aa730e4001cce734ca61c8001c9aa6994c39000a1fa17768c7200043ec2eed18e400287e85dd931c80010fb0bbb26390033331c9634c3200043ec26e6b2c4000c5f739cd65880010fd0f21acb100021f61e43596200043f43886b2c400087d8710d65880014dd0421acb100029b60843596206053dc02e4b2c400087e87cc965880010fb0f992cb1004e1fa1c32596200043ec3864b2c4000a3e840c9658800147b08192cb100031ddc6715962000537c12e2b2c40bfa6c825c565880010fd0f98acb100021f61f31596200051f42662b2c4000a3d84cc565880014dd0598acb100029b60b31596200043f43862b2c400087d870c5658806b0fb0f3aac7100028f6127558e201ad2ec1ceab1c4036a5f835d563880050fd0bba2c7100021f6177458e200043ec3ea8b1c400087d87149638800147b08292c7100029760c5258e200143f42ee2b1c400087d85dc563880050fd0a38ac7100021f6147158e200043ec26eca9c400287f83dd953880050fb07bb2a71000317ccb7654e200052fc1aeca9c400087f845d9538806d0ff06bb2a71000317e0d7654e200062f992eca9c400087d86dd153880010fd0eb22a71000297e0d6454e2000d2e41ac8a9c400287e85dd943880010fb0bbb2871000a1fa157650e200043fc32eaa1c400c96c825d543880010ff0eb2a87100021f61d6550e200070e21acaa1c40038dc8758d438802f53908b1a87100aa1fe197394a201562f31ae7294400087d8758e52880018bae6b1ca5100021f61b754ca201543f43aca994406587c875953288001c9864b2a65100325721d534ca200052fc32a69944000a5d8654d328801969904a9a651004393589534ca200047ac36e29944000c7665dc532880018eacbb8a65100023d618714ca200063b328e29944000c75651c532880014bb06294c3100031ddd7519862001c7ac3ca330c4002c767594661880015cf04a8cc31000ebca0051986200053b42e6330c4000a7585cc6618800156d0998cc310002ad613319862000572c166330c4000a76850c661880014eb0a18cc3100031ddd6759862000
  | 15 => 0x8bb2a8980029be09765513000536412ecaa26000a77815d9544c0014e902bb2a89805e8fa1b64551300151f43ec8aa26002a3c87d91544c18587ee7b22a89830b0f5cf64551300051ec16c8aa26000c3f641c9544c177878c8392a8980025760c72551301662e3b2eaa1a606ab1f845d5434c059c38c8baa869805ea7a1b6450d30006ad3a8e0a1a6000a3d849d7624c0014bb073aec49800a1fe1d75d89300043fc22ebb12600287f87d53624c0010fb0faa6c4980021fe1d54d89300043ec3aa9b126017c3c74553624c0014d904aa6c49805f271d143d89300051ec20a5b126000a5d8314b624c0011df0eb10c498002b920562189300be1f3a2a83126000c3d74550624c0194d904aa0c4980021fe1571189300143e42ae23126000a3f845da524c0cd47908bb4a4980ce9721943949300068eba2872926066e1c6450e524c0050fd0b3b484980021f616769093006477414ed212600087f855da424c0050f90abb4849819b0f19375909300061fbaec9212600287e859d9424c0010fb0b3b284980023da0676509300047ac0ceca12601693c87551424c00187cecaa284980030f1d954509300064e3b286a126000d95431c5424c0191dd05baec2980023b60b75d85300043fc2ae5b0a600287c855cb614c00147b08296c2980029760c52d853006637390a5b0a6000c6d7214b614c0011ef0eb08c298002b920961185300143fc3aea30a600087f845d4614c0190f904ba8c29800a1fe1f54185300043ec3ea830a600087f87550614c0010fb0eaa0c29805f271d143185300043fc2ae430a600287c855c8614c0190ff0f290c2980021f61e52185300643fc38a430a600087d87148614c00147b08290c2980029760c52185300043fc2aed20a600287c855da414c0050fd0a3b482980021f61476905300bd4e4328720a6000c9e7650e414c0050fd0a3b282980021f61476505300143f42ced90a600087d859db214c0050fd0a3b442980021f61476885300e53742ec510a600287e859d9214c0010fb0b3b242980021fe1576085300143e42aec10a60008bf845d8214c02f17908bb042980333318973085300dd3742ec410a6000e6452d84214c001cc8a430842980323e219700853006674312e010a6000cf0615c0214c0075390ca1a8098007271d9435013001dcc40286a02600287e859c763c80010fb0b38ec7900029760f5458f200646e43aa6b1e400287e85dc563c80010fb0bb8ac79005e2fa137158f200045ec26e2b1e4000a5d839d953c80014bf06bb2a7900b28fa107654f200051ec20eca9e406ac5e63dd153c80034bd07b22a7900029760f6454f2000d2fc32c6a9e4002a5e8758d53c80054b90eb1aa79000317dd16354f200662f392c6a9e400cc5c7258d53c80050fd0bbb287900021f6177650f2001c77416eca1e4068c5
  | 16 => 0x458a300143e43ea8b146000a5d83d51628c0010fd0eaa2c5180021f21d5458a3019c3f438a4b146000a3d84149628c0014bb06292c51800257e0d7494a301a43fc3ac5294600087f855da428c0050f90abb485180021fe157650a300143e42aeca1460008f7815d9428c0011e902bb285180664f21d5450a3000716aa4c4a1460038ec87589428c02f55908b1285180038b5516250a300043fc2ae530c600287c855ca618c00147b08294c3180029760c529863001c7ac3ca330c6002c7675946618c0015c904a8cc31800a1fa1f75586300043ec26eab0c600c87e82dd5618c00117f08baac31805e2f211755863000477c12eab0c600c8ec825d5618c02f17d0fba2c3180030fdd774586300061e3aee8b0c6000c3f85dd1618c0018790bba2c3180030fd4f74586300061ea9ee8b0c6000c9c31dd1618c00187eea3a2c3180030f1d474586300043f43ea8b0c600287c87d51618c00187ee9aa2c31805f0f1d354586300043f43aa8b0c600087c87551618c00187ee8aa2c31805f0f1d154586300143f42ee4b0c600087d85dc9618c0018deebb92c3180031b1d7725863000657ba6e4b0c6000cac74dc9618c0018dd0bb92c3180031b617725863000637aa6e4b0c6000c6d54dc9618c0018dea7b92c3180031b54f725863022672c0ee4b0c6000c6f751c9618c0018d8ea392c3180032bdd07258630006563a0e4b0c600cc6f851c9618c0198d90a392c3180031bd50725863000636aa0e4b0c6000c6f531c9618c0018daa6392c3180021fa1e52586300643e43ca4b0c6000c3f74949618c0cd878e9292c3180031bdca525863006636394a4b0c600087e87149618c0190f90e292c3180028f61052586300061fba0a4b0c60bbc3c74149618c0014bb06292c3180031bdc8525863006636390a4b0c6002c7475945618c0071e90ea8ac318002b920951586300043fc2aed20c600287c855da418c0071eb0f30c831805ead21161906300043fc2aeca0c600287c855d9418c0011df04bb283180323b209765063001c7a43ac2a0c60458df87586318c00153f08b0c6318312ad21161c86300143f42eed10c600087d85dda218c0010ff0abb2431800a1f21576486300045fc22ec90c60178bc845d9218c0010ff0abb0431800a1f215760863000732294c210c60c3ab484584218c0015cf04b0843180039914961086300145fc3aa9b22600087f855cb644c0050f90ab96c8980028f61052d91300052ec18a5b22600087f855c7644c0050f90ab8ec8980063720d71d913000477c12e3b22600c8ec825c7644c0011df04baac8980323b20975591300047bc0aeab2260008f4815d5644c0050fd0bb92c8980021f61772591300052ec18a4b226000c6f72149644c0198d8e4292c89800a1fa1471591300043ec28e2b226000a3d849d9544c00147f0
  | 17 => 0x98421ae548158d53084192dd0fb92a6108039358f7254c2100536c30e4a98420cc6e761c9530840165b08392a6108039358c7254c210063b3b6e2a984200e5563dc55308401ac8e5b8aa6108029d6187154c210072ab18e2a984200d64721c553084050fd0bbb286108021f6177650c2106477416eca184268c5e635d543084192d904baa86108323721d6350c210062ebaac6a184217a9c8458d43084355a902b1a86108027960b7150c21006b2296e2a1842008f5861c543084019aac638a8610803591487150c210dcb642ae919042009e7815d232084f95c902b2464108325b21d548c82134636bb2a91904200d2d745523208401c5ac8aa464108023be19718c8210dcb642ae3190420c95c8754d32084438beeca9a6410b1f5994b714c82163eb2296e2990421b96e87dd532084372d90bba2641086e5b215744c821004f3c0ae899042389e8805d132084f55c902b2264108025b21d544c82100716b22a8990421bd4f8754d320841969d0ea9a6410832d321d534c8210dea643aa6990420c94c8754d3208401c9f0ca9a641080393219534c821006a7bb2a69904221e4f7654d320840169f08a9a641080393d91534c82100726b22a69904200f478154d3208401e8902a9a641086bd11c5534c8211072730aa699042c6f474154d320858de8882a9a6410802d3615434c82100746b2286990427af844150d3208401aceebb8a6410803591d7714c821007a2a9ee29904221ce586dc53208401acea9b8a641080359553714c8213b6b3a9ee29904276d6553dc5320841999ce4b1c621086e5b215728c4213b6e398ae79084200d4d7354f21084398eaecbac4210832d92097588421004bbc3aa7108420cb648254e21084353cf0e99442109ced921532884210d6e339a651084200f45534ca2108475ac8a4b8442108331b94b764842106636296ec9084200c6c75dd921084018dea7bb2421086e5ba1f754842100637bb6ea908421b96c85dcd21084011df0cb9a421086e5b215734842162cf3c0ae6908420096c8754d21084018deeca9a42108031d1d776484210063ba9eec908420cc7652dd921084198e8a5bb242108031dddb7548421004ba43aa69084200c777654d21084196c904a9a42109cf591d772484210043ec1eeab00420087e87d4d60084050f90fa9ac0108021fa1d53580210043e43aa6b0042388ec874c96008403998e6992c0108039354d32580211c57440264b004202c787594160084191f10ea82c010832ba20950580210143f42ee4b24600087d85dc9648c00147b08292c9180029760c52592300143f428e2b24600087d851c5648c00147f08bb2a9180025760c72552300be1f3a2a93146000c3d74552628c0050fd0b38cc5180021f6167198a300143f43eeab14600087d84dd5628c0014bb063aac5180021fa1f5
  | 18 => 0x840147b08186ca908029ba0830d952100536c1061b2a4200a76810c365484014eb02186ca908029760f75d8d210052ec18ebb1a420087f855d363484050f90aba6c6908021fa1f54d8d210043f438a5b1a4200a3d8414b63484014bb06296c6908021fe1570d8d210143e42ae1b1a420087e87d9563484010fd0e32ac69080a1fa1f7558d210043ec26eab1a42008ef825d563484011ef02baac6908021fa1c7558d210043f43ea8b1a420287c87d5163485958eee3aa2c6908031b1d77258d210043f438a4b1a4200a3d8414963484014bb06292c690b271bdc85258d2163e3bb88a4b1a4200c7775dc563484018e8ebb8ac6908021fa1a7654d210052ec1ceca9a420087d849d953484010fb073b2a6908031760e7654d210062f994eca9a4200a5f835d953484014df04bb2a6908029de057654d210043f430eca9a420087d841d953484050ff063b2a69080a1f60c7654d210062f990eca9a420087e86dd153484010f90fb22a6908021fe1d6454d210043e43ac8a9a4288a778159153484050fd0bbb286908021f6177650d2100476c16eca1a420287c859d943484010ff0abb2869080a1f2157650d210047bc0aeca1a42008fb805d943484071f100bb2869080a1fa147650d210043ec28eca1a420087c865d543484010ff0fb2a86908021f61f6550d210070e21ecaa1a42178de87d8d434842f53d09b1a86908331dd8676949211543e432e7292422ac5c635ce52484010ff0fb1ca490803175cf63949210043fc3ac729242c7a778158e52484010fd0dbaa64909961fa1f654c9211543e43eca9924200e4c32d9532484192b90ea9a649080297a19534c9210052e432a6992420cb4c8254d32484018eecbb8a64908031d197714c92110e6a31ee29924200c77651c532484018e8ca38a64908031b197724c52100636328e498a4200a748654f21484190f90cbac42908321f61f658852106733b0ca510a421ca6c865d621484394dd0db2c42908729b21763885210e53642ac710a4200a6c8654e2148401ccecbb0c42908029760c52d81210143f436eab02421f87c86dd560484010fd0fb2ac090803171cf65581210043f438cab024200c5c7319560484018becbb9ac0908031719773581210047dc3ac0302420087f855c363084050f90ab86c6108323b2097558c210047a40aeab184200a5d83d5163085918e8e3aa2c6108323721d5358c2106566412a6b184200a5d839d953084014bf06bb2a6108b28fa107654c210051ec20eca984235a7a801d953084014f3003b2a6109ab1798f7454c2100d2f41ec8a984200a5d83d9153084ff4e902b22a61080697e196354c210d5a6c12c6a98420cd4c7258d53084054bd0eb1aa61080a9721d6354c210062fba2c6a98420cc5e7258d53084198b8e4b1aa610833131c96354c210d72bc0ac6a
  | 19 => 0x21fe1d6550e210043ec3acaa1c4200a5f835954388401c3886b2a871085e37a1f6350e210bd4f426c6a1c420cc76615da5288419ace42bb4a5108aa1fe197394a211562f31ae7294420cd4e325ce52884010fb0fb1ca510b069da076394a210043ec3ac72944200c5d7358e52884392d90abb465108325b21d658ca21064b642ee9194421c96c855d232884192d90eaa465108034b5d1548ca210e4b642ae3194420087d86dd532884550fd0eb2a65109961f21d654ca21064ae43aa69944200a5f8654d32884014bb0ca9a6510b2e5ba1e524ca2115637bb4a4994422ae4e6394932884018eccbb8a65108031d597714ca21006b3296e29944200c76651c532884018eaca38a651086b3598c714ca21006b2290e2994421c96e87dd532884558deedbaa65108ab9398f754ca2165cb643aca9944200c6f765953288401c9cc6b2a65108725b217744ca210e4b642ae899442449e8805d132884031dd0fb226510806b3a0f644ca2100d6741ac8994420096c8755132884d18deecaa265109a39398d544ca210f566c36e69944201acf8658d3288439a9f0ea9a6510832d3a1d534ca2142da643aa6994421cd4c8754d32884392990ea9a6510802d3e19534ca2100727c32a69944200a4f8654d328840169b0ca9a651080393219534ca2100f27bb2a69944201e4c7654d328840169f08a9a651080393d91534ca2100726b22a69944200acf8650d328840169b0aa1a6510803a3d91434ca21006b3baee29944221ec663dc53288401e8aa7b8a651086b39dd8714ca21006b23a8e2994421aec6631c53288401e8aa638a65108725b215728c6210063732aed90c4200c6d765972188401a9ae6a9e43108031d99576c8621066b3292ed90c4200c757659721884014ef0ca9e43108025b61c52d8221005a6c18a5b044200b4d8314a6088401cd0a5b04c110802d360c52582210062fb9aa6b044201c5c7354d60884014bb06292c1109123ba1e325822100726a9a64b04420287f865d460884010fb0f328c1108021fe1d6518221004b6c38a43044200b4d8314860884011f70eb00c1108028fa1263d95210051ec24c7b2a421f87d8718f65484018bae631eca908021fe1173d95210062eb98e7b2a420087e8790f65484010fb0f21eca908021fa1c43d95210043ec3887b2a4200a6e8210f65484014db0421eca909c69da0772d95210043f43e65b2a420087d87ccb65484010fd0e196ca9087e1f61c32d95210051f42065b2a4200a3d840cb65484e34dd05b8eca908021fa1f31d95210043ec3e63b2a4200a3e84cc7654840147b0998eca908029ba0b31d952100536c1663b2a420087e870c7654843f0fb0e18eca9087e9da0670d95210053ac0ce1b2a420087e87cc365484010fb0f986ca908021fa1c30d95210043ec3861b2a4200a3e840c3654
  | 20 => 0x2ab1ee2a9e4200e55631c553c84050fd0bbb287908021f6177650f213462f31aeaa1e420c8dc8758d43c84018baeab1a879085ea72116350f21064ae43aa6996421ac5f7654d32c841969904a9a65908721fa1e63596210051f424c6b2c4200a3d8498d65884018bee731acb108031bdcb73596210043ec26e6b2c4200a3e849cd658840147b0939acb1080317dce735962167537414e6b2c4200a6d829cd65884014df04b9acb10b369b209735962100637b92e6b2c420087e8790d65884010fb0f21acb1080317dce43596210043f43886b2c420087d8710d65884014dd0421acb108029b60843596210e537c12e4b2c4274a77815c965884010fd0f992cb108021f61f32596210e43f43864b2c420087d870c9658840147d08192cb108028f61032596213a537414e2b2c420cc6c729c565884390fd0f98acb108021f61f31596210051f42662b2c4200a3d84cc565884014dd0598acb108021fa1c31596210043ec3862b2c42cca6e829c165884014db05382cb108029be0970596212b536412e0b2c4200a76811c165884394eb02382cb108021fa1f30596210043ec3e60b2c420087e870c165884010fb0e182cb108028fa1030596210051ec2060b2c4200a6e820c165884014db04182cb108029da0430596210053ac0860b2c420087d8799763884010ff0eb2ec7108025b61c52d8e2100596c20a5b1c4200b4d8314b6388593c9cc6296c7108021f61e75d8e210143fc3aebb1c420087f845d763884050ff0faa6c7108021f61f54d8e210043ec38a5b1c4200a3d8414b63884014bb06296c710b071d9c452d8e210063b3ace3b1c4200c75759c763884012db0e292c710802cb6105258e21005a6c18a4b1c4200a5d839d563884014bf06baac71080a1fa177458e210043ec2ee8b1c420087d87d5163884010fb0e292c7108028f6105258e210052ec18a4b1c420287e85dc163884010fb0bb82c7108021f6137654e210143fc1eeca9c420287d83dd953884018be65bb2a7108031b8cb7654e2100636996eca9c420087d879d953884014bb073b2a71080297e0d7654e210043fc22eca9c420087f835d953884018bf06bb2a7108031be097654e210062f992eca9c420087e871d953884010fb0dba2a7108021fa1f6454e210043ec3ec8a9c420087e8759153884192dd0fb92a7108031b5d87254e2100596c20e4a9c420096d861c953884198db0c392a7108334ba107254e21004b6c20e4a9c420cd2d841c9538840125b08392a71083353a0c7254e210e4b6c18e4a9c420cd4d831c953885938dec6392a710b271b58c7254e210143f42eeca1c420087d85dd943884050fd0b3b287108021f6167650e2101c7d404eca1c42008f9809d943884050fd0abb2871080a1fa147650e210043ec28eca1c420087f865d543884192d904baa87108
  | 21 => 0x7450e528c4cdc3cc8a1ca51880a1fa167690a310043ec2ced214620087f855da428c4050f90abb485188323b2097690a310043fc2aeca14620287c855d9428c44b2790eaa2851880327dd94350a3100c7ac30e2a146200d95431c5428c42f53f0ca1c8318807275d94390631005cbc0a8720c620287e87dd5608c4010fb09baac1188321fa0b75582310043f43ea8b04620287c87d51608c4010fd0eaa2c1188021f21d54582310be4f3a286b04620287e85dc9608c4010fb0bb92c1188021fa1e52582310643e43ca4b04620087e87149608c4190f90e292c1188028f61052582310052ec18a4b0462008fb87580608c4010ff0ab96c89880a1f21572d91310051ec20a5b226200a5d8314b644c4010ff0ab86c89880a1f21570d913100477c12eab22620c8ec825d5644c4011f700baac89880e3e20175591310143f42ee4b22620087d85dc9644c4014bb06292c8988031bdc8525913106636390a4b226200a3d849d9544c40147f08bb2a8988029be09765513100536412ecaa26200a7b805d9544c4d34f100bb2a8988025760c725513100596c20a5b126200b4d8314b624c4014bb073aec49880a1fe1d75d89310043fc22ebb126200c6f825d7624c4050ff0faa6c4988021f61f54d89310043fc3aa9b12620087d87553624c4014d904aa6c4988028f61052d89310052ec18a5b126200c6d7514b624c40155b08296c498802b360c52d893100536c38a5b126200c6d8714b624c401c5d08296c4988029b61052d893100716c20a5b126200a2d8414b624c5974df06296c498b2793a0c52d893165d36c18a5b126200e4d8314b624c40149b06296c4988023be1d62189310053642ac431262c5ae781588624c40165b08290c498802d360c521893163f33b08a4312620ca6c82d50624c42f87ce8aa0c4988030f5d1541893106536412a8312620ca6e85d48624c4010ff0ab80c49880a1f215701893100637394ed292620287e859da424c4010fb0b3b484988021fe1576909310143e42aed212620c8ec825da424c4018d8ebb14849880a1fa1676509310043ec2ceca12622393c87551424c42f1dd0fb1284988031b1d762509310bd57426c4a126200e2d54d89424c4018d8ea31284988038b550625093100c7b436e2a126200ce462dc5424c42f1bf0eb2462988021fe1572d81310143e42ae5b026200a3d8414b604c4014bb06296c0988023ee1d60181310052ec1ea8b1e420c8dc8754d63c84050fd0bb82c7908021f6177058f210052ec1ceca9e4200a5f835d953c845947d083b2a7908028f6107654f213562f31ee8a9e4201a5e83d9153c84014bb07b22a79080697e196354f210152f43ac6a9e4202a5c8758d53c84018bee8b1aa790833179c96354f210662e392c6a9e4221e578158d53c8443ca902b1aa7908031d5db7154f21007
  | 22 => 0xa10c29900389551421853267f33a9a8430a64cfe6553508614c99fd4e86a10c29933fb190d421853267f52a1a8430a6400ec543508614c801d0a86a10c2990029da1442185320053ac288430a641aad683108614c8015ab06210c2990029de1570185320053a42ae030a6400ab7845c0614c80156908b80c299002b5e0d70185322ed73c12e030a6400a76851c0614c8014eb0a380c299002ada1070185320055ac20e030a6400ad5831c0614c8355cb04380c29906ab5a0f50185320056ac1ea030a6400ae682940614c8015cb05280c2990023da1c50185320047ac38a030a6400a7685d00614c8014eb0ba00c29906ab5a0f40185320056ac1e8030a6400e9543d00614c8015cd05a00c299002b960b40185320047b4388030a64008f587100614c8014ed0a200c2990029d61440185320d56b4188030a6400ad583100614c8015cd04200c299002b960840185320be4e3a287b026400a3d8414b604c8014bb06296c0990038b55142d813200746a1a85b02640287e859c7604c8010fb0b38ec099003a650f40d81320056cc1881b026400ae982103604c84f2bf0ea9cc099002972195398132086a6b92a73026400c77659c6604c8018e8cb38cc0990035554e71981320063bb2ae33026400c74655c6604c801aaaa6b8cc0990031d9d761981320063abaec33026400c7675186604c8018eaea30cc0990039554c61981320072ca9ec1302640287e86dd5604c8550f90dbaac0990021fa1f65581320061e3a6cab02640087e87195604c801878e832ac0990030fd9774581320061e32ee8b02642795c8754d604c801a3ee8a9ac09926f471d15358132096a7b92a6b026400c7765dc5604c8018e8cbb8ac0990035554f71581320063bb28e2b026400c74651c5604c801aaaa638ac0990023da1f61581320063bbaec2b026400c7475d85604c80196ee9b0ac0990032d1d361581320047b438c2b026400c7775185604c8018e8ea30ac0990032ddd061581320065a3a0c2b02645dce772185604c8cb8dae4328c0990029721953181320072aa98c230264008fb87580604c80157108b00c0990039654d60181320043fc2ae5b24620287c855cb648c4014bb06296c9188021fe1570d92310143e42ae1b24620287e85dc9648c4010fb0bb92c9188028f61052592310052ec18a4b246200a3d849d9548c40147f08bb2a9188025760c72552311662fbb2eaa1c626ab1f845d5438c459c3cc8baa871885ea7e196450e314546ec36e2a1c6200d5575dc5438c4ed5cd03b14c51885f0f9d15498a310061eba2a9314620287e87dd5628c4010fb09baac5188029760c7558a310043f43ea8b14620287c87d51628c4010fd0eaa2c5188021f21d5458a310be4f3a286b146200a3d84149628c4014bb06292c5188023be1d6218a313352fc32872946200d1d
  | 23 => 0x185320072bc32a630a6400e548654c614c843aaceca98c299003959d95318532005abc22a630a6400e576454c614c801caac8a98c299003d1e09531853260daa412a630a6400f448254c614c835e8ee4a98c29906b95d8953185320d7a3b12a630a6400b558550c614c801caecaa18c2990039519543185320074bb228630a6400e946450c614c9a54ed0d290c299307d10ca52185326a53b430a430a6400b3584148614c8016ab06290c29900399d9642185320073232c8430a6400f4553908614c8355c90ca10c29900399d9542185320073232a8430a6400ea764508614c801e4aa8a10c299003d154d4218532007c2a1a8430a64c1b57858c8614c8018eeeb3a8c299366b9e09751853200572412ea30a641aad6831d4614c8015ab063a8c2990029da1674185320053ac2ce830a641aad6839d0614c8015ab073a0c299002b9a0a74185326c572c14e830a6400a76851d0614c8014eb0a3a0c29906ab5a0c74185320056ac18e830a6400ae6821d0614c8355cb043a0c299002bca00741853200578c00e830a64d7a7783d50614c9af4eb07aa0c2993239590f541853260d3b416a830a6400e3754950614c8355ad072a0c299002b560e541853200573414a830a6400ae582950614c801c6f08aa0c29935a9de0d54185326b53ac1aa830a64d5e5643550614c9834e904aa0c29906ab5a0c54185320056ac18a830a6400ae682150614c8015cb042a0c29900395a1543185320072ac2a8630a641aad78450c614c835d2f08a18c299003a5dd143185320074a3a28630a6400e575450c614c801caaa8a18c2990029d612521853260d3bc1ca430a64d4a7583948614c9a7cac87290c2990039550e52185320055b420a430a6400ab584148614c8355ad06290c299002b560c521853260f1b420a430a6400a7584148614c983c6b08290c2990028d610521853260d3bc18a430a64c1e5683148614c9a54eb06290c2993079560c52185320052ac18a430a64d1e5643148614c801caa86290c29930799a08521853268f33b90a430a64c1e6472148614c9a3cce64290c299307990c852185320053b42e8430a6400a7585d08614c801c6aa9a10c29906ab5a0f42185320056ac1e8430a6400e9543d08614c9834ef0b210c2993069d216421853260f332948430a64c1e6452908614c983ccf0b210c29930799216421853200733aa48430a6400e6554908614c9a1ccea7210c2993439954e42185326876321c8430a6400ec543908614c9891ef0ea10c29906a3d21d42185320053bc2a8430a6400a7485508614c801c6aa8a10c299003a550d4218532007332928430a6400e6452508614c9899cf0ea10c29930f3921d421853200733c2a8430a6400e6485508614c801d4f08a10c29900399d514218532007532a28430a6400e6554508614c801d4aa8
  | 24 => 0xa6421ae5821d3614c9c14ef07aa6c2993829d60f54d853263d3b416a9b0a64cae6572d53614c801c6ea92a6c2990038de1154d85320071b3a2a9b0a6400e3574553614c9bf4ef06aa6c29937e9d60d54d853263d3a412a9b0a64dee6572553614c8014eb09296c29931e9de0e52d85326ed3ac1ca5b0a64dbe657294b614c80156d08296c299002ad61052d853210d6b418a5b0a6400ad58314b614c98fc6d08296c2990029d61052d853263f1ac20a5b0a6400a358414b614c98f4ef06296c29931f95a0c52d85326e53ac18a5b0a64c7e558314b614c8014ab06296c29931f99a0852d85326d732b90a5b0a6400a7685d0b614c8014eb0ba16c2990038d55342d853263d3bc2c85b0a64c7a748590b614c9871ef0ea16c2990863d21d42d85320053bc2a85b0a6400a748550b614c801c6aa8a16c2990029da1442d85320053ac2885b0a6421ad68310b614c8015ab06216c299003a950842d85320053b42ee1b0a6400a7585dc3614c80156d09b86c299002ad61370d85320056ac1ee1b0a6421ae582dc3614c8014ed0b386c2990029d61670d853210d72c10e1b0a64008f687143614c8011eb0e286c2990029da1740d85320053ac2e81b0a64008f687103614c8011eb0e206c2990029da1440d85320053ac2881b0a6421ad683103614c8015ab06206c299002b9a0840d853200572c1081b0a642795f8754e614c83da9ae4a9cc29906b559c553985320063b3aec330a6400c7575d86614c801caaa7b0cc2990021fa1f65585320043f438cab0a64c9c6f72195614c84f2b90ea9ac29908353dc953585320047bc3ac230a6400a7785584614c8014e90ab08c2990039554d61185320be4e3a28630a6400a3d84148614c8014bb06290c2990038b551421853200746a1a8430a6400c7775d44614c8051eb0f288c29900b1d9d6511853200573c12a230a6400ad583144614c8014ed0ba08c2990029d61741185320056ac1e8230a6400ae582d04614c8014ed0a208c2990029d61441185320056ac188230a6400e9543104614c8015cb04208c2990021fe1570185320143e42ae030a64008bf845c0614c82f17908b80c29936f1d9db65185320053ac26ca30a64d3e5643d94614c8011eb0f328c29934a9da1665185320047bc3aca30a64d9ae782594614c9a94ed0c328c29936b1d9d865185320053ac20ca30a64d1e5683194614c801cab06328c2993479590c651853268f33b90ca30a64d1e6472194614c9a3cce64328c299347990c865185320047ac3cc830a6400a7685990614c8014eb0b320c299362b960a64185320047bc3ac830a6400a7785590614c8014e90ab20c299002bce01641853200578402c830a6400a7685190614c8014eb0a320c2990029da1b54185320053a436a830a6400b5583d50614c8014ed0caa0c2990029d21954
  | 25 => 0x92fa9ceca9c8499393939d9539093271da7c22a721264e3b4d8454e424c923a9ae8a9c849900673a0e7190932006a6a9ce321264019cc835c2424c801a9aa6b8484992ee1fa1f65509321543e43ecaa126400e2c42d95424c8012bd0ea9a84990025721d53509320652e432a6a12640cb4c8254d424c937e1884a9a8499032a7219435093200e4e3b286a126400b1d8550d424c81971904a1a8499387c31494350932156363b4a4a12642ad4c73949424c801e1a8729284990ab1b1db655093200716326caa126400d4f8754d424c80169d0ea9a8499002d321d5350932006a643aa6a126492b4c8654d424c803a9ceca9a8499007531d9535093271da7c22a6a12649bf0e8454d424c9c769b08a9a8499003c361153509324a6a7ba2a6a126400f0f6454d424c937e18c8a9a849909ae321943509320bf4643286a126401d8e7650d424c82fd18eca1a8499007231d94350932715c7c2a86a1264e1f0e8550d424c9c571b0aa1a8499003c3615435093200586c2a86a126400f0f6550d424c9c3e18caa1a84990325721f658c93215727b16cb192640095f855d2324c819b1c84ba4649903257a1d548c9320068eba2a9192640cd4f7550a324c819b1ee8a146499003c3551428c93232e36b90cbb0a64018ed82dd7614c8d58dae5aa6c29905f0f9d154d85320061eba2a9b0a6400a3d8414b614c8014bb06296c2991971b5c852d85320063abaea3b0a6400ad583d47614c8015cb05a8ec29900b1d1d651d85320147bc3aa3b0a6400a7685d07614c8014eb0ba0ec2990029da1441d85320053ac2883b0a6400a7584d97614c9b7ccae5b2ec2990029d61065d85326d72b418cbb0a6400e5583197614c9b5ccae432ec2990029da1664d85320053ac2cc9b0a6400a7785593614c8014e90ab26c299002bce0164d853200578402c9b0a6400a7685193614c8014eb0a326c2990029da1b54d85320053a436a9b0a6400b5583d53614c8014ed0caa6c2990029d21954d85320072bc32a7b0a6400e548654f614c8016af08a9ec299003d1e0953d853263daa412a7b0a6400f448254f614c843e8ae4a9ec29908795d8953d853210fa3b12a7b0a6400b558550f614c801d28c8a1ec2993729da1a52d853263fa2194a5b0a64dda768614b614c80166b08296c299002d560c52d8532007a2a9c85b0a647a9e78750b614c8435c90ca16c299003a919142d853200792aa285b0a6400f455350b614c801f0a86a16c29931ed5e1632d853200573416ebb0a6421ae582dd7614c8018eaea3aec299002ada1075d85320055ac20ebb0a6421ad6831d7614c8015ab063aec299002b9a0875d853210d72c10ebb0a6421ae582dd3614c8014ed0b3a6c2990029d61674d85320053b428e9b0a6400a75851d3614c8435ad063a6c299002b560c74d853200573410e9b0
  | 26 => 0xb171db7454d32004af436e8a9a646895d84dd1534c801a9f05ba2a69903257a0b7454d32006a6416e8a9a646ac5f62dd1534c8d5a9ec5ba2a69900297e197454d320052e432e8a9a642bc5c765d1534c80169f04ba2a699002d32097454d32734ae43ec8a9a6400c5c76d91534c9c7c3cc9b22a69909e5721d6454d320062e3b2c8a9a64e3e1c64591534c93969f04b22a699002d5e056454d32005aa40ac8a9a6400b5b80591534c8016b100b22a69903257a1f7254d320152fc36e4a9a64afc5c76dc9534c8036990db92a699397531db7254d32005a6c26e4a9a6400d4f74dc9534c801a9ae9b92a699002d3a077254d32005a6c06e4a9a6402a5e869c9534c8198b8ed392a699196d3a0a7254d32006a7b94e4a9a642aa5e861c9534c8198b8ec392a69926ec7a107254d320058ec20e4a9a64adb4e871c9534c801a9d0e392a6990aad3a187254d3200727430e4a9a640cd4e761c9534c819a98ec392a699003c3a107254d32005a6c20e4a9a6400f0d841c9534c80161b08392a69900353dd07254d32006a6ba0e4a9a6400b4e811c9534c80169b00392a6992af171db7154d32005a7416e2a9a6400b4d82dc5534c801a98e5b8aa69900297a1a7154d320052ec34e2a9a6425c5c769c5534c80169d0538aa699002d360a7154d320052fc32e2a9a6400a5c865c5534c8478b8ecb8aa699002d3e097154d32005a6412e2a9a6400d4c725c5534c9518b8ec38aa699297171db7054d320052f434e0a9a6400a5d869c1534c8338b8ed382a699002d3a0a7054d32005a6c14e0a9a6400d4c729c1534c8014bf0cb82a699002972197054d320b62e3b2e0a9a6400b4f825c1534c80169904b82a699287171d87054d32005a7410e0a9a6400b4d821c1534c801a98e4382a699002d5a047054d32005aac08e0a9a6400a5c865d5434c8598b8ecbaa86991aac7e117550d321670e322eaa1a6400b4c825d5434c8018bf0cbaa8699032572197550d320062e432eaa1a640c85c865d5434c8d52bf08baa869900347e117550d32006a7c12eaa1a640c95c825d5434c801a9904baa86991a317d897550d32346a7b12eaa1a649bd1f425d5434c8018b8edb2a8699003871936550d320bd4f436c8a1a6400d4d75dc9434c801a9aea392869919a1f21974949323361e322e9292640095f835d2524c819a5c84ba4a499033530c974949320043fc3ec92926400c3d74d92524c8010ff0eb24a4990029de0564949320053a40ac92926400a7b80592524c8674f100b24a49903297219439493232e2f3b2872926400d1d7450e524c8cdc38c8a1ca499032d32094394932064ae43aa7212640ca5c8654e424c92f8bceca9c8499032d32095390932006a7c3aa7212640cb4e8754e424c8196990ea9c84990035321d5390932065a7432a7212640cb4c8654e424c
  | 27 => 0x6396a8b0c640087e87551618c8010f90eaa2c31912f1dd96719823225e3a32ce3304643ac77655c6608c8758e8cab8cc1190325ba0b75582320143f43eeab04640087d84dd5608c8190fd05baac1190321f20b75582320043f43ea8b04640287c87d51608c8010fd0eaa2c1190021f21d54582320053b40cc9b2a6400a7581993654c84f0fb0e326ca990030f5d064d953213d2f436e7b2a640087f835d3654c8010fb06ba6ca990030f5d074d95321552f418e9b2a6400a5d831d3654c9cf4dd043a6ca990aa9b60874d95321543f43e85b2a640087d87d0b654c8010fd0e216ca9909e1f61c42d95321552f41885b2a647ba6e82dc7654c8554db05b8eca990031d5c471d95320043f43e83b2a640087d87d07654c8554bd07a0eca990029760f41d95320053741683b2a6400a6d82d07654c8010fd0e20eca990021f61c41d95320053b40ce1b2a6400a75819c3654c8c14dd04386ca990aa9b60870d95320043f43e81b2a640087d87d03654c8010fd0e206ca990021f61c40d95321552f41881b2a6400a5d83103654c8014dd04206ca990029b60840d95320053b40881b2a6400a7581103654c80147b09baec8990028f61075d91320052ec18ebb22640087e8714b644c80147b08296c89900a1fa1671d91320043ec2ce3b22640087f855c7644c8050f90ab8ec8990021fe1570d91320143e42ae1b22640087e87d95644c8010fd0e32ac8990031dd9771591320063a32ee2b226400c77651c5644c8018e8ca38ac8990031ed9770591320063c32ee0b226400c7b651c1644c8018f0ca382c8990032e19070591320143f43eeab2264008f7815d5644c8011e902baac8990023ee01755913201c7c402eab22640087e871d5644c8010fd0e292c8990d31e1c052591320063bbaee2b226400c7475dc5644c8018eea7b8ac8990031d54f715913200672c16e2b226400c7452dc5644c8018eeea38ac8990031d1d471591320063ba98e2b226400c75531c5644c8018e8a438ac8990031edd770591320063c3aee0b226400cf371dc1644c8019e0e3b82c8990031ed4f70591320063ca9ee0b226400c7852dc1644c8018f6ea382c8990031e1d470591320066db98e0b226400cf3711c1644c8019e0e2382c8990029da0776551320053ac0eecaa2640087e869d9544c80147b093b2a8990021f61276551320061ec24ecaa2640c87f839d9544c8190fb073b2a8990030fd0a76551320051fc22ecaa26400a77815d9544c8014e902bb2a8990029ee01765513234d3c402ecaa2640087e861d9544c8050ff083b2a89900a1f61076551320643fc18ecaa26400c5e831d9544c8190fb063b2a8990031760c76551320062f218ecaa26400c5d431d9544c80187e843b2a8990031b908765513200636a10ecaa26400a5c865cd544c9cd63f08b9aa8992c
  | 28 => 0x11016394801c38873b2872900297e0d7650e520070e21aeca1ca400c5f835d943948190fd04bb287290321f2097650e52064ae43ac6a1ca40cc5c7658d43948cd63908b1a8729003879916350e520070eb22c6a1ca40cc5f8758d43948198b90eb1a872900387e116350e520070e422c6a1ca42ac5f7458d4394855c3ee8b1a8729033179c96350e520662e392c6a1ca400e1f4258d4394801c3882b1a872900387d016350e520643f436e2a1ca40087d86dc543948192dd05b8a87290025b60b7150e520643f430e2a1ca40087d861c543948190fd0db8287290021f61b7050e521543fc3ac730ca42ac5e7358e61948018bae6b1cc3290325b20970986521543e43ac6b0ca400c5f7358d61948558b8e6b1ac3290029d20563586520653b40cc2b0ca42a87f8758e60948558bce6b1cc129003175cd639825225e3bb1ce3304a400c75639c660948698ecc538cc12912f5998a7198252064b6412e3304a43ac74865c660948758eec6b8cc1290031d58d7198252006b3c12e3304a43ad64825c660948698ecc4b8cc1290eb59989719825219e3bb02e3304a433c75605c660948018eae330cc1290029e602619825219c3e43ac6b04a400c5f7358d60948558b8e6b1ac1290ce1f21d61582520063a38ac2b04a40cc3f845d3658c80187e86ba6cb190030f50d74d96320643e412e9b2c640cc3e425d3658c81987884ba6cb1903317cc974d96320662e992e9b2c640c87e87d07658c8010fb0fa0ecb190aa97a0f41d96320052ec1e83b2c640ca6e82d07658c8014db05a0ecb190321fa1c41d96320043ec3883b2c640c87e87d03658c8010fb0fa06cb190321fa1c40d96320043ec3881b2c642aa5e83103658c8014bb06206cb190329ba0840d963200536c1081b2c6400a7681103658c8014eb02206cb1900a1fa1671d92320043ec2ce3b24640087f855c7648c8050f90ab8ec9190021fe1570d92320143e42ae1b24640c96e82dd5648c8050fd0fbaac9190321fa0b75592320643e416eab246400c5f32dd5648c8010fd0e3aac9190322f21d54592320051ec24ecaa46400a3f845d9548c8192790eb22a91905e8fe1964552320661e3b2c8aa4640cc3f87591548c80547d0eb22a91900a8f21d64552320661e43ac8aa4640c83c87591548c9d187ee6b22a9193a30f5cd64552320661f392c8aa4640cc3c72591548c9d1c3e64b22a9190325b20975986320143fc3aeb30c640ca6c825d6618c8010ff08bacc3190031be0975986320643f412eb30c640c87c825d6618c8018d904bacc31900a1fe1f54986320043ec3ea930c640087f87552618c8010fb0eaa4c31900a1fa1f755863200636396eab0c640087d84dd5618c8190fd05baac3190321f20b755863206476412eab0c6400c6c721d5618c8010fd0faa2c31900a1f21f54586323563
  | 29 => 0x96c2a18031b99572d854300636b2ae5b0a8600d8c435cb6150c2f1bb07baec2a18323ba0b75d854300476c16ebb0a860087d879d76150c018bae73aec2a180a1fe1d75d85430062eb9aebb0a869f87f835d76150c590fb06baec2a18321f20975d8543006373ace5b0a8600c6d759cb6150c0199ae7396c2a18331be1672d85430663642ce5b0a8600c6f539cb6150c018daa7396c2a18021fe1572d85430143e42ae5b0a8600c6e755cb6150c018daeab96c2a1803335cd72d854300637c2ae5b0a8600c6c855cb6150c018dea6b96c2a18031b54d72d85430643fc38a5b0a860087d8714b6150c014bb06296c2a1aef175cc52d854306637390a5b0a8600c6d7214b6150d3f2bf06ba8c2a18034710d75185430043ec3cca30a860087f875946150c011ef0eb08c2a18021f61e75185430143fc3aea30a869f87f835d46150c590fb06ba8c2a18321f20975185430043fc2ae430a860287c855c86150c190ff0e290c2a18021f61c52185430052ec18a430a869f95f835d76050c01a3886baec0a18021f61e75d81430143fc3aebb02869f87f835d76050c590fb06baec0a18321f20975d81430043fc2ae5b02860287c855cb6050c011ef02b96c0a18023d20572d81430643fc38a5b02860087d8714b6050c014bb06296c0a1bb29760e659814375f0e21acb302860287f865d46050cd10fb0cba8c0a18034710d75181430043ec3cca30286eaa5d839946050d3f8bae7328c0a18021fe1d651814374f0e21aca3028600c6e659c86050c018dacb390c0a18036310e72181430063732ae43028600c6d655c86050c01b1886b90c0a18031d99671181430063ab2ce23028600d94439c46050c018eccab88c0a18031d5957118143006ca21ae230286008fb875806050c550fd0f322c7290030fdd26458e521552f41cc8b1ca42a87c8759163948554b906b22c7290325ba0b7158e520061fa1ee8b1ca40c87e82dd163948190f905ba2c7290030fdd27458e520052ec1ce8b1ca400a5f835d1639480187ae83a2c7290329ba087458e5215536c10e8b1ca42a87e87d0963948010fb0fa12c7290030fdd34258e521552f41e84b1ca400a5d83d0963948194dd05b8ac7290aa9b60b7158e520063ab88e2b1ca40087e87d0563948010fb0fa0ac7290aa97a0f4158e520052ec1e82b1ca40ca6e82d0563948014db05a0ac7290021fa1c4158e520043ec3882b1ca42aa5e8310563948014bb0620ac7290029da067058e520053ac0ce0b1ca400a3f845c1639480147908b82c7290329ba087058e5215536c10e0b1ca40087e87d0163948010fb0fa02c7290aa97a0f4058e520052ec1e80b1ca40087e8710163948010fb0e202c7290030fdd04058e521552f41880b1ca400a5d8310163948194dd04202c7290029b6084058e520053b40880b1ca400a758
  | 30 => 0x81531661f3a6c9b02a600c3d74d936054c4f2bb07396c0a98025de0572d8153004ba40ae5b02a63587d8718b6054c0147b08316c0a98331b9c862d81531ac3ec3ec3b02a600c7671d876054c014d904b0ec0a9bd3175cf649815333e2eb9ac9302a60cc6e7298a6054c0147b08314c0a98031d5c661981530053cc04c3302a6f3d5973d826054c6b0f90eb22c0a98b30f1d164581531ad3c402c8b02a60cc6c729896054c0147b08312c0a98021fa1f615815300536412c2b02a6f2d5b73d816054d612bf06ba0c0a98b21f61f64181531661f3a6c8302a600c3d74d906054c014f301b20c0a989e5760e72181530051ec20c4302a60cc6e721886054c018eec9388c0a98031d59271181531b63bb1ce2302a600d57639c46054c018ecc5388c0a98031d18a7118153006ab994e2302a62595f835c46054c012df04b88c0a98025b20971181530063bb22e2302a600c75645c46054c01aaf06b88c0a98035520d71181531b63bb1ae2302a600d57635c46054c01acf04b88c0a98035920971181530063b312e2302a600c74625c46054c01aae64b88c0a98d71dd8171181531ae3ab02e2302a60087d879846054c018eae3308c0a98031d5c46118153004bdc3ac0302a6f1b5b835806054cd163d09b9acaa180347dd373595430068e218e4b2a8668c5e87dcd6550de18bee9b9acaa180387dd373595430052ec16e6b2a86f0e1f42dcd6550c014bb07392caa180297e0d72595430053bc0ae4b2a8600a74815c96550c014f700b92caa18029e201725954306637390e4b2a8600a5d839c56550c018eee338acaa180297e0d715954300537c12e2b2a8600a6c825c56550c014f700b8acaa18029e20171595430063ab88e2b2a8600a5d839c16550c014bf06b82caa18029be09705954300536412e0b2a8600a77815c16550c014e902b82caa18029da0470595430053ac08e0b2a8600c79701c16550d3f2bf06baec4a18034710d75d89437752ec1ccbb1286efe1c435976250c010fb0f3aec4a1bba9760e75d89430143fc3aebb12869f87f835d76250c590fb06baec4a18029760c52d894306537414cb312860ca6c825966250c01a3887baac4a1b8e9760e655894300537414cab12862b87c875956250ddbc3886b2ac4a18029b20965589430063b32ee2b128600c7565dc56250c01b2887b8ac4a18031d99471589430063ab28e2b128600d94431c56250c018f4cbb82c4a18031e5977058943006cc21ee0b128600c7a651c16250c018f2ca382c4a18036610c70589430068e21aea312860087d879946250d3f8bae7328c4a18021fe1d651894300477c3ac4312869f87f835d46250c590fb06ba8c4a18321f20975189430662f992ea312860cc5d325d46250c01a3886baec2a1a7f175ce65d85430063732ce5b0a8600c6d659cb6150c01b18873
  | 31 => 0xa6b087f835d06254c0187e86ba0c4a98030f90d74189530061e21ae8312a60cc3e425d06254c1987884ba0c4a983317cc9741895306637192e8312a60cc5d325d06254c018da64ba0c4a98331b08574189530061fc1ae8312a600c3e835d06254c0187b06ba0c4a98030f20d74189530661fc12e8312a60cc3e825d06254c1987904ba0c4a98330fcc974189530660f992e8312a60cc3e325d06254c1985c64ba0c4a98330f4c974189530660e992e8312a600c2d325d06254c1987864ba0c4a98030fe0574189530061f40ae8312a600c3d815d06254c0187902ba0c4a98030fcc574189530061f18ae8312a600c3d315d06254c0187862ba0c4a98330fc8574189530661f10ae8312a60cc3d215d06254c1987842ba0c4a98330b08574189530061fc02e8312a600c3e805d06254c0187b00ba0c4a98030f20174189530061f982e8312a600c3e305d06254c0187a60ba0c4a98030f0c174189530661f902e8312a60cc3e205d06254c1987a40ba0c4a98330f08174189530643f43e82312a60087d87d046254c0187ae9a08c4a999697a0f41189530052ec1e82312a701c5d73d046254c194dd05a08c4a98029b60b41189538073210e82312a60c87e871046254c010fb0e208c4a98030f5d041189537fe2eb9882312a6fee64211046254c190fd0fa00c4a98021f61f40189530061eba680312a6fdc5d73d006254c190fd0e200c4a98021f61c40189530061eba080312a665a5e831006254c014bb06200c4a9bf3175cc40189530653741080312a600a6d821006254c014ed02200c4a98029d60440189531643ec3ec9b0aa62cc3e74d936154c0187ae9b26c2a98029da0764d855313caec1ce5b0aa600a3d8418b6154c198dce4316c2a98031b5c862d85530053b408c5b0aa600a77815926154c198dce5314c2a98029d60662985530051ec20c530aa6fbd5573d866154c014eb0fb0cc2a98031d61f61985537d63ab9ec330aa600e5573d866154c018ece5b0cc2a9be717dcf64585534762fb9ac8b0aa600a74815916154c01a9ee7b92c2a98031bd93725855300636b26e4b0aa600d4f83dc96154c01a9907b92c2a98031bd8f7258553006a7b1ee4b0aa600d4f731c96154c198df0c392c2a98031bd90725855300636b20e4b0aa600d4e831c96154c01a9b06392c2a98031bd8c7258553006a7b18e4b0aa60cc6c729896154c0147b08312c2a98031bdc8625855306636390c4b0aa6f8d5773d856154c01ac8e5b0ac2a98031b1ca61585531643ec3ec830aa62cc3e74d906154c0187ae9b20c2a98029d607641855313caec1ce430aa600a3d841886154c198dce4310c2a9bdf1d9da61185537b5aac1cc230aa60087f875846154c014d904b08c2a98025de1d61185537adabc1ac230aa600b64825846154c332bf06b80c2a98d61f61f64d
  | 32 => 0x801d000000c00000200c8000006003003800c000013000800003200e001800402c015009800001800000e8000006000000000002e0000068000002012004001000e001001000400000a000000401e00000080000ba002000000c008000001005401a004000001402c00600280180000060010018002013000000c00000c004801c028000005000c00602e000000c00800c0000010034006000000003c006002003400a000000001800a026000001000200d0008008002002004000400e004002801000a00900380440080090000074004001002000000400c0000014000024001001800000900300040240070008000004009000007c00200000000e400000300180000020020028000032bd07396c8a989e5760e72d915312cafc1ae3b22a60195c835c76454c012df04b8ec8a98025b20971d91530053b40ee5b22a600a7581dcb6454cd54bd07396c8a9c1a9760e72d91533552f418e5b22a6b2a5d831cb6454c198dce4396c8a98031ddc671d91537cd2fc1ae3b22a66aa5c835c76454c014df04b8ec8a98029b20971d91530063ab88e3b22a66aa5e83dc36454d654bb07b86c8a99aa97a0e70d91537a52ec1ce1b22a600a76811c36454c014eb02386c8a98031e5c070d91531661fbb6c8b22a707d1f74dcd6454d612bf06ba6c4a98b21f61f64d89531661f3a6c9b12a600c3d74d936254c472bb0738ec4a989657e0d71d89530ccafc1ae1b12a706c5d73d926254c0187ae9324c4a98329ba0a649895300536c14c9312a62cc3e745926254d338bae6b24c4a98329b209649895306726312e7312a60ca5c83d8a6254dcba9ae7b14c4a98331b18a71989530043f43ec8b12a705d4f73d896254c01aaee7b8ac4a98031dd9371589530063ab26e2b12a600c7763dc56254c01aaec7b8ac4a98031d98b7158953006ab996e2b12a600d5532dc56254c01aaee638ac4a98031dd9071589530063ab20e2b12a600c77631c56254c01aaec638ac4a980359d8871589530063b310e2b12a600d57321c56254c01aaa6438ac4a9b93479ce74189530068eb9ce8312a60ce2e629d06254c5927f0eba0c4a9803475cd741895306717312e8312a600c3e865d06254c0187ec6ba0c4a980347d8d74189530661f312e8312a60cc3c625d06254c01a3e64ba0c4a98034b8c9741895300696992e8312a62c87d87d906254c5987ce9b20c4a98030f5d3641895306537416c8312a60087d879906254c0187ae9320c4a9ac3175ce64189531661f3a2c8312a600c3d741906254e098bae6320c4a98329ba0864189530061eba6c4312a60ca5c83d886254e0769b07310c4a98021fe1d62189530061eba2c4312a627c5d735886254c014ef02b10c4a98029d2056218953004b7c3ac4312a60ca6f865886254e0569f06b10c4a9802d920562189530661fc22e8312
  | 33 => 0x500000000020080004024010006800000c00a00280140260000018004006003002001c02e000004800001800b000000804a00900b002c0000170010004008001003800c0000080000008008004006001800600000100000000020020048002000000003000000300a001000c013006004000800500280080000080010000018001013801c0000020000008006005000002400000b0018000006000002001c00c0170000004008000003803c02c001002801c00200600080180060000008004000000001801001c0000038004022012002005801000d006800000e000003800000e002002800001000200080300040090048004010000000803401000a0000004008003002000000402600100100060000040000008001003004c026004002000400200b00080b0004005001000007a001000000000003400d0004010000003001000e00300a0000010003000000001c00101700180060080018010010004006000400600000000000160000020030002004002000c002025003002c00a0040018060000006000800800000400600180b6001002802005e02400280180000000028004004000013000000000f008000800401000a001c00000a0000020000000002000000002100000000140030010004006062000802800400a0020010028000001008c000001005000c0280050028004014003002000000001100000000040040008024004000005004c00600b002001000800400380a8002019001000c0060010138004008018002800000a007000800002800000080000000020280004004000004000000600a0030000006000001000000000c007800000c001005805800c002001000002a00b001003400000900e00200000010000014008002000001c03c00000280280240010008008014007000802400e00100580080060060000090010000001801009c00100000440040000000010000000000000c0080010048014024001006801801000b0008008012001004800c00c0030108024000000000801c00c0020058014000002004003000200000180000120000000000004001000006000600400000340060050020008028002000000000200400e0000006002001000000c0060008108004000001800000000900c803000e0020028004002005001801400e0020000000000000000000402c00100300300100190030074006001000000401c00100e0004002009000000000800300a800400c00b0010030006001000000000a01600080000660050080044000000009001c00000600400480000090078014000030001000400c000000000000600000100140040070030024038000001007800c0000020000004003004000802200200e801c02600200080c400200800180040000110000028008001000000800200700f000c000004000001400
  | 34 => 0x24004004000001a001000000002600000180540020000000010000000000801c006006001800400a0010000004008021002001c00e0020078020018002001800000e001004004400000000600040000110008008004004000800001a000002000004c004001800001200000200000020040000000000003000804c00e000006800000c0010000048044001001801400c0010038008008000000002801002501280b80260020020020000002000000800000100300440000010018000000003007000400600000100000000000010000006001007805c010001005002c00801d000002c00c00000080140020100030054000000000800400c025000801404800000200340200060028004002000000001803e000007000c0000000030004000000000000c036000000000000200800200400060010000008006004001000000000800080000000050008010006003000800c00c00200000200020030040000004002003000800600e0000020004005008009400600a000000c0000030000018002000001000c00200700e805c000000002800000200f000800002200100c800000000200100540000000008010010000004801400401d00a802000600e0058018002001001802401400e0018000004008003800c00002f00000140000000000018014000001801c00400d0008008002003005001c00c006002801400a00401a0000004012000000804600300280140100090028010006000003800400c00001600280080000010044008000000002800e004000000004c000002000c002005002000004a00200400140120100040000024003002800000000d000001801c006000000400a008000000c00200100300000000020008008002000000800803600300000140160050008000000006012800000a00300200040040110030008000010000001c01c00400000000000020000004000003000000800c00000380300100000010004014008001800003600100100100300270050000014003000000800800000e000001600600a8004000001009003000c008003000800200001d8000006014001802000200b0000010000008000800800c0000000000000003002000800200000000080080040028008000001003000c014003002800c00400000280000000000070008000003000002c0020110008004004011001008c0040050010000000000002801c0080080028010000002000800400000a003000800e00400000440140050000008036024000000400e00e002800002600001380000040040018000006004003800c000000001002800000000500100040040038000004000000001400a003006800800000c0068010012001005802400000300d00c403c00200280e400c00e00380080560000000044000001000002c016005002800c00600f00
  | 35 => 0x1dc0000c4cb830c1710b00010f922ccb9012d424f309834984951912f0d0cf389ceb417200b500e10242630374095876711103ad0af24f709851a60e8c21297a49b12dec5dd2e18da300001f6461d066280cb2900000003054b670000de429c91040934d223484cd81c5c62e284506c432082cbeccae4097480d9848d2c38ac64c0b646a92c610d113b800013f86c8000059a28a80890ddb1993f88000000000026181173af27a58a4a3be3be85e340d8f4711844933d8026380000931ca073138dce8205a0000203c0001b9891300f89e83e7c65482f49be40806721e681b53aacacf2b04b001320c6d0990f1400000000e90b8e000000019186a10000dd123285063a70a6745cd0a826485b51b244550ae49802bf800029e0000293c4be02486e9054006400009a4c0a0e8424f001320640ad25ec3ea000000024c40000000a0a4008000422800000000000c6e7ef2e68e40b66c0002cd42ae2c283d5114c7193f484060000e56000055000004ee80000000b600003f90b110df8d7e00000000ec8773000104821f0f2c15d400021851442ae47b944b06d700005b30f9407c0691176377a10910a10ba39162a1412ea4c412a3353c9cddc3fb8fb20818de941c0f822ab80610fc00d400505ba0230cf62668a380af89161d54288134d04240c4000021000000005fe3c44bc241e838f0000a300000000409c2fc340c00007f02182e547698000cab00006530000000290800043002cd1214de008b4bdb000cd83257c000000000001c43932b4c0000000fab070090f2edc0000000d7a000095937ac47400000000000be100000010038004002005000003c0020000120080000005005000800000a0060000000005006801000a00400c803400400100080540000000040010000000001000401600500080040220010228000006000000801400400000080cc006000000000400200b00080180000000068008000003000805801200000c0000000000000004c00600b0028030000008004000003a022008804406e00f001000800a017007806400e005000800001c005000802c046018006001003a00001500000000020000014016000006801000e0020050000010000006001c006019000802000a00400e0004004000010000800e000000002c0020000010000008006002005c0080080048014006002000801c002001005800000001100000000120000000000000006000000001a000000005400201d0050028008003000005001a020001000c0020030018000004003001800400000001000040a4003001800c00200400180100020020008000010001000001400400100b000c02a007003805400401d000000000201600000a000c006004003400000d0000018006006004800000a00f005004c02200000000040020110008054004000000802c0
  | 36 => 0xef20000985000102611c80002f68e4f0000000000000029a83433a943ff0e702910aa8fa43b3efdc38ca7f30000eb2000000000000003fc40000f8038706f62822a180000f9c00000010a200007460d300004204000043400000000000001007130cd4603b494345fc0831c3400018c80002be8000069ca02132400000000000e52d5b03249521a243683c64d4002c05701f9405b0154d0d17c8fe908ea9af96ec29539a8248321e0feace005c44c0eaf0370007826d0172a14391b7d208d181069126802d39d504251280971000000024906080000d5d2e345dfae8c5e089a808205f0d6e2f86d0c2ab40000000000367077615551471a3818210d49782b443df94fca0f3f2c3cf255107d0000d8a050503c1b402278000665000000006c4beb223000000000000f3000000000001bccf8507ce000000000029581993cf050a00000000dac97f000078d00000000000e5e393056c0c389d70000484000000044f0ec3282064e1f2038032bc1dd40f4d4712a06b941bc18345b4e933ccc4173d0000037200000000bf000000003d98000000000000000001070a321260f43070868023d445a419c5ce1cdc00000003e9000066c0ec000027f412623483458b029fe00000e50000c4b000000036c800021ca00000002ee1140829099d0cb3564bf40000a0b39bca7e323c465325cdbc10341f9404e7e60000c25000000000000000000a800000a3e0e6006819d00001d291ab00003663925069000000039ec5272efc0000000aef02f06b636140003db4a7f00009d100011231c488383fdc00009ce0000e087990dbe81531989ba1314db33068000253c17907364a939480f5435097e2d181d40000f6131f0ef106a809626a013911e4ea1438c6d80e5e2ec050c8fd43287ac0c6a88f20bce9f3460ed4a6bc8563d440003e3c50e021cc082fdd1862f9051e3c711372e60ad6071660a1d1c0003904000072800013bd03032b4a7d27e50921ce45d73aec812142100d2ffc0d13a98d4d02283dd1c60c0609048b9275000045b8f9730a07783858a2d44bc00036f40000b303520000f721050da73f68000220ea82171800039185fd8bc8bea00000002e08000000030905246e22c9004e269494800000661b54112a0f003f206000006048ed000096200000000a660002a5c0000b8427c241cce6259ceda43e0df545f8da2317c00000001050000000278200004bcec4003cc95000058a23ec578196839900011bc32f89e43d7477a436000000000000000d5230300000000db400010912538cf746943ee926800000000002c78f4d2a74aac0000e851be000026d80b439541182f4800042b86bd38989c80140c8731c6d5a1aa867842dcb852b60ab42bcc00001b019599580000000221810000000005e50000000252c0002944009800102d00004a736100000
  | 37 => 0x57cb482ed4075282aa3522dc50000000ac3be40003cdc7dc3c94f86303600041dcafd2f002f136e0e46c3150392c40a1a18b118919ecba90ee91681e4105c3ba05fc0346dc32c3812d45281f815045893920d172dbcbf10b588330c945140d1816a0924ec80000cb223d8ccd00980003078000453cc420000f3a23c80003260eb7058c67610f90412285169156828d1b3411b00000002a400000000fe32b7905020742051e240003248000255a00008b045641380000000b021a2c79718150112d2cd4e0d4c9ac226c0ef1f909ec30581bf3af4c8389c316115e457f0cb49960000ead467c2720988000227400016620003d58ced37a00002bf07c73d703d40f3ae00000000000000000000000000000000000002f88c822c2cc4c000059b2ba0c9c28800b100000a80000e340560000000048004f49f810ec360984e48d0ff8a4e00005e71b947090000000000057b00000003a6058000001ee0000704052c9cd10e00001bfc0000000c52000066a2da838b1a5cc18028e0d83eda724398c12a000000026dc00000005ee0000fdb30f0000000028608f8d760000e1900003b72d090c61028c6100000001af103f21800001288fde15d822426031bb0a420000000ffd83ace3e00003151d704950644f583d14b960e848ac342c00509640003740ad92380f8c00009e208e490c1df07c10ddc00040110581fa0670175429b446879d163c4fb00002b642c4e1415485f40ca21603d642380fbc0510d8c27820802c33ef0d3a436c44028b05df37f91631a08b7e80000000000000208ae282d70000000009716e4e1c08383f609dc7f400005e8000000030fc5a20000000031c00000000001a041f2000000028100000000e3f000000000000003ec437910648de15700002f8c0004220000000073a0000c44406a00000010f4292509f0a32efb32fcbe9000000030002b688c00003da8a912a8464a00009a3388c0001d74d993d90e5f33f43f93278099437443a000035d96c6e3c3e2cac5b1f421300005ae806cd934334a8d31700393860000381c0000000000000118236c0ca400000001c2c0001e00107bb7400007208a3100410e13e0e69000000000004f50888adc2a9404c392800000002e34614c560b9200000000980680462032a01c07342a01150f4b325007b3ff022a0610c5e2a88f061898ebc38340003624d452d80d9743b800011b4c090c04d678348000054c28c2fe42c224509403c546038ea0d980514ef62bc860781150c90dec48946b0cd70e6e4ef8000a7c0000ab22df460001fc33d41926ca00009dc00000001c8c1d3000000042c0585c530b2a202099840660a629a401f172a8e14358f7f38ccce306ea24c2d7e7508242e5015f0f521e300000fe0220048100a0000b0d00002f90000000023908900007a0040912744f84e04254
  | 38 => 0x429a089ce020aacedb2e2ccfc1efc4102d51087320028484c44f00000fbe000091e0000df380005860f780001379021972c0002696d8d02e200000000000000b9d12b4dd20a8c0000000289000042b00000000000dda00007728000000225c4c41f0c000000000001b40002504b430b9451f0f040de3394eba060a3bf1654cc30ba43db3e04fa8396823d0d5890d1d600002accb970000695265712530bcc3005dc000038cb930000000411915a00002170000a908200a2239d497c000060f1f543969d2c5fb25b8b3b4250dc628b88d4076900d8c60d2718186be08c494c0710974200052f195a100365517000002c01a9436f380405a3478000000030b194837031248f40000811070cab13e48251056886b462872c82bc8820290ed40aa025b00000001b7064517785c13a6c98741f03343cecb6d000000000010dc44a4b2705940003f8afc81c50d692840b6800007b717404731614c631258bfe19b830238e0ef33344ff8337428daf062712a9c9843620aab000107114e059242583df0000f1aa16911616784e545008ad0000c0e00006590b3c00027f09d01dac06037745ab40ee5070452f392cb059f00005042d642b544d095d8164f480000000000000000005c035b41973e22fc713a48222dd48dc386811e417411240a8b4e1e147de1626ac90080ba42ad808139f0a1c2a610a90000df093fc0000000a393ad4e4aa64c32224d012e146309330a80001278334800000044240000000228a4843fa3e3e83e09866ee0286281094ce4e37e8dfc1c18afb04e8e2a15e8a25353046a246c48e26049353b45069a6ca1693180400165ccd03304ee7000000014410a52a90000000000014840001a6000002b8c8a29c4cac000071b0000e8800000003eed12e00009700000000418422124e021197e01b30000fc10000b841ea00000000a9309a4000000000000008b21d080000000cbb45dc0000c42a81000098816f8000035c66224444cf0000245233000031c821214f06db2340ecd14987c601c08c702686c101468943ded197000097d2110f71000109929d4bc600000000000b0134fc416306c0001178baa2a7034694d4000000000019cc6e100007f530dc00028540bf4154000427904daf983ec15b4da50be60001c9ed730000a480940d28396429221c8940955032944644493ffc93b00846850900000000068c23c41ec2e840000000cd30ecc00044a883d00000003144000000000000002d7236800013cc00024b40000000000383c4e43c6031d00005d1087cf460000875314c0002ebc0000e7662980003670a3838331e2000000066d00000000000000000000000005ac22440dd35bcff337bc000007400034c014e00009532418c470e9497fa24c8573d286d442c8df2b1ec0001e482521bd4f240c6c5293a509904024622039cf74
  | 39 => 0x116c8ed60eb0c3138285f32c643440000bd81558a1203b03af0e62f892f3d149247c1e03e805cd0000047a27c9308000ab00000d4200001408a3c0000000c7400000000c3c8ee3a8d068264e0003b28f080000cd50ed80000000a4b00000000000e791acce2f00000000f5856e00002472700a94160d124000003b14dcea6c57111000003883c8d0ed138cc040000a8f3120b1223e8ba001080000606000000000000000000cc8d6400000002c686c52b30520277858436b100c03a8b88382452439b07fc09d0bfc4594548316cfc43bbc643246472ec3f44340000fa1193c9450922000000047a45e8241800000000000a900007ff2134f30011000032f4000458006f0000000456c000000000025a80c6000000000011032ef4f5a423ac9b09ba1bb428074f8d4edd50000000061888b158086f06e429323a8e0281231392730000000000014d0e8f00008d810dc0002872f7d0000d49422600000005670000000000000000006140b980000000000000075708ac35d43b0b9b0e8afca00002c6087470e000011a24cc00000000002c4c1c4a4ac000074e2010000610000106536d51af16b87602a7c35f8eb872000000ce800076e28d8000346c81c19782140c0cc2109b400032250fb00004af000000041ccec880000002d048392eec2de000077b2b987950328616ad440001dd05ff8000c644298350441d12600000000d36c7946610510000000469c00007fc000000114d00004df05904320000eb12c5400034209602f28587000000000011420000da18000deec0a4eed00006150064b6533e84c3b6c412295c89aa37080004610c80c2d433304cc0001fe0000000000000000000000c4314cc15b081c00030b40001d880000000e080000f931574c450f90cc41560000127000046545680000000230c9a200001948d2a7be000072a8000aaa00006d32a486bb32c08590022b260000000192496f0000a2f33ed19c0c1207300a8bce30700001ec400000000000000186c2304d00a9d01e0a9064423190b41724b2d19dc3ed94045b827082d10ae30f644cc624036c9f61cd50321e70ddb25cc83f19700002354e6622a8c4e068800033180002f509101b48d3d0fb425a178452a8e50d0908fa97a44c44db21046ed9d408733454e6143787bb0b4cdf4001c1852b805db33a84181ac03fb38a50753dbc0000e4409f210c804110c84e2f1d0e641a80fe3bac000131c0b20000c622da4ce3b8fe4da36806af1d7cb4709bc5aa000020c8000000000108307951a20000000146806e25d87ba3a6806b2970e3a0a70395070400011a00002518ce411180003e28dad2c2455336d8f940a76ac23fb00003d246f0117000038180000000376000080caa462ce20c034a454c953b4ec7a90af48a49cd0459011cc39410c21e2db03d70ac10ad21286fe391
  | 40 => 0x684d5000119b1e9428016c2e3d23000a2bb30bd539745442d5481e377c4bf09acaf41f483ee2df858b41308bb23046fa3ed816c2b100000b149d9000000000000000a9895d3e982648dc80000798e2682ba0000ee0cb119c4aff22045f5344400040ca8840fd02b32fbafdf055c14d0000000000096446a06c2122cd04153060118680000000a6100000001c741e30000ec606b80002d7600000000d7b065157000103583140001694000089600000004ab1a80e9700000000000a40000117118bc00000000a11db0cd90c5a9093994dea0f680002e70000000000000002280c9c2c800008b500005c20df519a00005da0000d510028fa5313c34b2058000077c0004268000000084b12dc3071c0442429a02ba0000ad03a2c000336c000037e0003a8800000005d938c8000000000026fcf0e1c54c3d1fd838c2fe020f3abe7b53b3b0530149052095cd0119f91812904000000000000000000000000148cec2270c00014300002d84000000000045c8adb15dc1521e3c9f544d800018fc19d0b040000000d7700010e2000099f0000000201c4e8211455724a09cf1fb05d31cf8312aa52d2e0f24667800116f2ed86ae1b90090463061d42fc92522f0f80206cc7e04328a73aca4bb16c1034095079b17e85020000ca80d64000000091816750f700006a30128692331cbae0bde05610080000e682c296fc41540eaf9930c8bb229e44c2416437108700000000fbf17b421b0000806373c63a0b1c6e8072cc73068445f3e6c8e728ec6023608fc9276c037118071a2a390fc03a68cf2de85c505b4137926d0620ce446903c912107eeb531bd0e11aef10fe41bedab1a7cdca0dcc686033509734409e5171a00000000001b2c000375c3dc2a64cb60000000384e89bb96c8f32468000000013e2bdc4762a2072600001ea2e3c0003c801abb558b03000011f37f2dee10806a820a832d8aca2c4107452a2e281292280d003f44f488b6c00040944fa3ee8f0a00004080f8800008d46132b94e71082c8af3dd49bc3c1018584d87811facf7920d04b30c4829602dc8d939e0bf63c5ceb300004c00e185f12b54a661350e9d3edca89018d08b21b05abbe3800009548462daca5a36e4fb8a7144520f9856600005153238cf80ba6000139c0000464e7725582a48000285b0f8000000040f00006e33154cf32024ba5166514308263a73328ae900001a9089a0002140000338470723dcbb30b2428a442072113c8f280e8e1e91fb48c922f80000000d44000028e8000be00000c7a1ca284838811581bc4ffe0dfc5962b74ec3af640004408a00107d00f37100002ae0a1e097033389289a180004ed00e879124dc11d2a589ce31602bfb1a4d6c2f5cd650f627d1322c0001cf03603cf81130000d431e0c58e00004a504bef00254200027b8490063c4a31d8455
  | 41 => 0x1974a230a0c9dd03e4883000000000001b2296466f0000c38311ed75000041e05748a09e9800000000002abc9320600000115d15d420a0001130000373046401f413834dd16a2e78e498000e430000000188016e3b811460000773897c63345f42838000cce0000b7000000003fbc8b000006751e500003f600000001060412c00021880fc000098b0000000304c000000000000000000b2d04722640003ca400000000000000cd400006eb000000000000000000000000000040380002e2400000001d800001369508defc34c0002a6c260a2680001870000049107400008641444dbe3560149952c1222cac0fd0000a52345800005fc000404c0000db8cec0facd3e28c41d146c400035f000006670f3388406a00880001a689503ba4ca13c34b2204ec0003b14a1a92f05050000e4b0470d1900c4e91274c1f71a7000013041940c980000420000198c19a30410333a4844818ad06e3aa000825b40d09312ce8000063b13480000c106ab192cabe0000df20000000331420a00002362df00003b6000000008773761085000083dc35c000000024e0b700000c467298c362b83ed055e1b1cc039c5800000000003f38000142508046a48f02fb86ef3a9c99700008863a58aa813d05a91bd8000333c00000001ef44b418e000000000000002f7cc3b2e44000000000000010c422380002e1c00000008dd32680001ccc0000000519c550c072fd47d62ef866b0ef0000120800046488870000431112ce670174000368eb2812d204600009d61bec2ad0000ed3000020c29b000000000861d2029700004ea1c30000169c000236c00000000000ec4f73000000000008e900000002eb035400002b70000c6a18e01423fd4dc7313435838c0ea0188c6448000bb400006ed1c70000000034700000000454614ac209950e58000447c0000000cbc184476d365078b000000000000001f40404242c1c71c9414f0a1ce890398af50ee4332bd5c02b160879817a88263ba90049ca462d05f40004598b050790831407cacb062412c0cb106b3f84de21248bc5067c3d3138801836a810428143974048f6828fc5d244150a4279292e415901d30509d23df005719a4f6b02d831a049c81015d03f20f0027e303c7b41b684581ab06dd1174c0a24882002dc80e112d0e6d325891c119c63132107ae0588be29856f223e10e04288481cb67cce93396f1f10444e10f8c2151cb4b5b09f4ca51c14f0501d0bd126505ca0bf4fcf2d606bdbef4d812e5042e30d4349217ca8340f8b2327850af000000044ec000384cda90000dec113910a0000b3f35501bc0058ad240a6ff41e10889000081798d89f7000100580007ce34a800027cc6470000c2027ac00017dc0000390d9600000002a4a00019b30d9000000040ec4ac464000009d502ca1d04391f30e1200000001f
  | 42 => 0x6869b23f40c8532641ac31fc0240fcd1883ff4af008b8e2c2b9c4d64054e8d12300003830246c0dc0001f8cef03380dba1eb49c10300a161a1c7f139f4a260cf82fbad78b403c3000e1d445b427190002030b4a074a81a03c07383a4e000000119e1ab44f141ea4661f0835e1ecc10c0b504aab74c73b13388df0b885121982de7386c96b11bc025092d05a0000fd538b4000000037c10a8f9511440001eac9ad000000046f40000000b201bdc02e35807c480002358000000000096c380cba629fa5d825dc272800000046dc27fa14d1b3353c217b778000262472b8f18c702394d7128041fb0ed0fd90648f4110169b515bc0e900080d33772bfb04d51aa13acb31391c27b9ffe67d00002a53b9427333c477e36ec565201400026291000bfcf4f0000a5f0000fcc2b38aa6248c60b32e0a7fbe600000000000000000000005fd004802c06ac00038f6f0f2e4800039fc3c8427423740ac00038880000aa4000390111700004b12016f700e6c2febebc51d10f4bd610bd10109791833f80c22147a4d12cbcd3908986c63714d3624e42a8b7f6bba057022929889889ad01e80f381f029c0384413c55b2e6506ca400e53278a2f51e7ce0b1684c8c1d68d80354c000000060c06608ba418c27928747f9400ca192fbe0c313f07df33fc9081c2041b00f05eb0a6e2b22dd10bc13981f400008140d090bd0000d551e58e3ca3ac74908244092ddc7aa2358c460a64a5022e058b8e40e1e2780e8a0f7a01a27b44b5b1d85810c44d8b0000000000052b3b54000000077882a8eee153400012f4b7100008e6000111b46803211274000055000000005789cac0fb1a1000023381fd4690f2a37fb022029507925d42320820b641680fc2000000034f08850000bcd0000e0e2fcd1b90000d0e1f004cd1916b1f1f9c00037e4e3500d87bc00002fd838042111b000035e00000000e4210489912270cc83ee5098000000018580b921b88b12c505cf29781c62d7c0000000000000000000006070000000000074300000002994000305c7b608ec5911c870c1445498f4438f1633ac0670ef447d00002bf22ce74029dc22f26089123d1026340608f83a3850f3b98000000005e46d092c0000600c08c9f237ee1b9a9ca79300002e70000f130000ac311d4ff907d4cfe0f08d9e00000000054fe98000a3334500351634d66214899e339c69343c024215c4a8c0e88ef43d507fd129880119a00001ef400000003752834525c0e03e8b08c8e300000000000e6b0000a24000113f00000000000000000000025440000000000287c0230f0c59000000000000ce221241320c28c3a252875e446086622b8fae1bd269627a2000135c00045d0bd300010443b7c01741782040864f8980000000c2a7643330cf20e96369140cb32298c330b4a4d3228dc106340806237240
  | 43 => 0xdb72d142c198d0b5a3796000063087143389c4000000036b8297c28c000000038900000000001113330090e384034f169a7a1468ca0e18a4b1d192074d0ce80002404f9019849d8355ceac3c1caa03d42bb81f5095e256c1b6269c4451955106292814728a4c344658a870ff024428d0276281c2ac3f942fb46fc95821709cb02790df0440ffe8388345000048300006e7000000000000002c10d352278151282476a2388a9e079c824000000003e9159364519324d800000000000fdce582aec095358d15542d8f9a38e4bc10cb228b42ad01c43e90191afcf882af463721d86d614b46500d947d84284d1c4444f910ff468f0078abf29d8bfa000017128188780b54f7894e804d22ac1b01730f6921fcd382b8c33c39c845b0f6e000410000000000000000196000000000008250f10f3f000000022d800035c000011c01388000c84b894000000090a00000000bdc000000059835d0b25000111d0866774b1a000012b8cc919d20000000d86146000000000000e3400045209200c7302f35208d7043c00004280000b282342d8c628b8c400000001341ff843604820002ba908b959117925842e8395000039c048606d6dce00000001d76efc2178f4241b40000000000180c0913ee08030000a1717501401f5c0000000ca92850c8800000000000b5d03d108880000ba1d4d09b14a00002a28ebf0000ede11fc000145829e22f42fa00000000000b661a40b3437c46420ea893012c8b4f1a506b70d201a813b05809f240004704130000000000000000000000001000000011ae40b000000000002670000157c19c00001b8073ceff2e00000291cb3026c08b43ab8c0227c4e1705ccfac230853b271c3ca1e2906a9e78f4c29f2e243c24bc80fd46f93a54d2f33c016623909b311dcf1208fd0ac3288d2329600f81c9c52c179115000bc4dd11ec9bb3d7c258029e5ad16bc54622983439c08be51c7c39d168cc410c9e7d31690a8b3d9d0162254000000076901c8cdc0d889a42dfc40b0288ec780010be0000c40088d0e521ec460830464140d4aca2954488309cd24295c12b36751b6000000018f90ff146a0000cc4bc41c8200042e0f762f702113c78e438de0df700002ed000000000002943e1c00010cc00c00000003db800041e01d900000001cbd10d091800034140be0000000255c0001f10000000000005c800000008c400000002a100000bcc0bb25340002cf8522347c4231b78c91012e3163034e763a180000000f032b890b300000000000b0f35891b225550721514dfb0000bad208200000c8c290000e0880005ef000102e00000002ea083a000000043c40001dda0000000000000035a85d000000000003b38ab53f4c34e1878f5b1cfc05312440df217418b06dcfb01fc90ef0000d12000000000000000000ac7000077f00008210
  | 44 => 0x2d24c7131ac549045054f1dd491540921a60e4268d3b0473638d8bef0654406800064d16be000000098d1da087e05f87f003ee49711040000001051a2a4bfd329c539033c6a22adc7c5189c009327d071b764944199c4222e306c420391520c14271b0d8c1f30450761f28aeb361c447178854334b40000308000000004b146e6df2b14b730000ff60000190000000000002bc03b80000000c240000a2b0000d7b2c6c000000042d05e116200000480000000132c00011086793ad83f13ae675b3ac093d2be1028bcb8ee407589a108ef00e87400000516b620c803e1800000046d42eb13e47703f1857abddd0640000cd20000f4e0000000000033600010140000ad7000021a00000000d7c0000e7ed0a00000000000000315c0000000fe80000000224000020d880a0bea27b143469b453881734acf1d0000000429c80fa58c7111f880000e48a7b32b89df24086c323fce8015a82bb1d3050b00009cd800096527fc48a42a88963e34000000000035ac0000000e3b000017540c670a0458d6844ad0488b740000da635b0770b78423834d0cbc000003ae1f101c0003d542fe11b89b42008091b7b62f036bc0e79d983d21fe919d0000abc1f740c80e98851000051b46504aa359cd5c0912e8c109d0492d5c8a8abc462a1c400002b682d48c6444d39b85ec45d482824140d500180000000000000088029b4e5c0000bb920c8c05290c72a2798000000000032e832b216055926b847c00010e800008403f0c8cd0000f3200006ce0ca83ec9960f9d3aa4979256917828f000038325e600000001ebc57e0ad000021a417634de4b03f3470320ec21600000000000df300005693a7830800000001cc020331b0a450000d8f39f800016200004234000218c0333cd40003872a9520dcdcb00002df21e800021a908f16f014a0754000000033b0000b6e0000000346800024fc00000044c6185c0001f2c8c5090c85538543230000000000000000000000ace7863e0c8670000eb9387461929ac00001d826500003d941e6c7dbb40b211e3807a0000d61273a403000000b30042f81ac8ec90c3084f02ce7ee00447db00a016100003063ea80002db64b60bd8426219400039e867c0558cef01e060d00010820000bf246f8000000000000003e8454400003dc3d680003170f400000000000035a0001d486511d8c4b90a6aded000108609be236b1fe000048c67f000000000008980f5e7a4000031e0000000000000007e82d00518af919aa7724004c900000cdf000026022a02703c6800032d463c2d30ed58e823412aa70e132d0df64380e35898a03d0a601440000a7326e0000209c000000000037f43ef923cc3333b82ef08f02898000c0331681e200000002cdc00000004dc083400043ac0000000bde00000d0223400031221f11588d7945b072c0000
  | 45 => 0xb334240da614c11ad259818736480002f2419b16a00ce000046b000038e0c7000028a00001daa000211c00000007883d888f93e7898e1f801ba0000000000092900001a52664d9a0000000199110f3bd4000000053115283368f34e4d24bcb4d29190c30000d060e786018000668c3540cc18e40003de813f00350840000aa3279d01b1fec29f4638f341c4cd4a1fdcb9f0000a3d00004a40cdc0000e14fa3406811117fc000404039f00000000db03628cb8e4427a419e3ea400017a60340ea400000000001b800003cc400000007a23140a7a1584037bbe0b520d6eaf38c40a7439d06f3ac1800010f099b31d4d412c580490000f5e00003cb090ecc208e83240000d7245144fd3f14000040cc2c0000b3900000000404b360000fc040e61ce0000e830bd000005bc0000000c858d00bcb08945730000ca33a04295b41c59c24f83998000000000058c009c64033d40a72d40000457c00005ed0c20000927000103d800053e05641670d8400013d8000000000000000293b1caec18380003794d6a0000f38000000000000000000000251c000203400000000003cb4000000117b20b8000036485b00009490270b792220741202c4ca4340000256e000439000000010cc3684cd63aa800000000002288ee23bb00003f9ce99459103a2e0400006bc000063443f3b5c054068c7b01dbc000000000027ecfa700009ea06aa2663fb4d333db0c592724ac600004fd800000005ce0001c786602dd8983427061b32cc38a00000f30aea9a62a6829d22280002fb0f5333789fa1e9c0001780000415c35113304302b5210b332c35ebab23551fa800028300da06d05b63b4854e463c04300011b8187cfad0000ad40000000075c0000a1108089b044a0ba8efd2344000197ce8705306fd413aff0000000000000001b0000006280002b00fd6402cee3000000043a8f9c2cb840c387ef3d2ec000000010bb000028ac44800000009f424e9128412877598940000c2edc11d100b78000caa296cd5f439c8ef29110210000d253150a5d2508e1129bd0d21204dc0076c00002e00001cc86d1023c1d204dc95c04840003f5c42944e0b3a3d4051c3fa87560d7087d0250ba23638bed00006b5381516b02140001df40583c04fdd32dcffa00005f600009680ac449f18240003194e51000000000007b800000000b8107e052113d44e8aba00000428000030195068a0cfc0000000a5317707653c98bdd00001880cc04780f8400000000002474d7d01e49d53fed12006f4de61d141be2950c86136092a00007d91ba8b1c3e8868317ef0c707ac5401014000086a3813c40700215005f0c5110c013c290175e00039cd0060f608d33d8cd5e2bd836a1fa505f43681c90784f2f0e807592d58c4a2b5a69e4020a64213016b18a077113640001250000052a2fc8000be8
  | 46 => 0x57d0000000151c63015ac0003b2d132000099d03fc000000000000000003cd83b53b3c0001bc8c9302a2a79a498aee00010450abcf0b2e9c00031e019aa7c0de30000000348000000000000676000000036ba1a00003a405c70000ac8336800016dc0003ae000000003c54106d0f00001a997e4c8327687870cc718b0b903640de91ba31bc6fc00001c54558e0d8000000463417a02ac00038da0000000ce680010f21f346ec399000020ac6a72ee263518606ba378447104f097207f8000208cef700000000000ca03df8779000036d128400000006882860df01c9ad2610b0d5014650b92729141452ce44a84c3000c56ae138b8a271e08feb3c849a9b012ca60000df8000000000005c4164c4ba0000bcc0a15025a5a431f06b40000000666019487000b467a317400000000b3398823c85540002eac6cc3734000195c0a34578f65000000004a09e300011c0460116708408cb3f5030d41348922c1cd3136905131a98512a9808a509a0210bcac1f309e646330b8b3d1a900d6090311c17c05d6398086d00000001dde0f600011b010688e8000020201a40000000b0c00000000000000344c00034e2c0b0000c8100003ab00000000a8853d43a48790000f1b00000000000000319c8fe1b640003b005943ed490300009ab3e3a32835fc00027bcde6bde0000000000000010128000aa900005bd2b3482d0f1cfe629341de022c74f3afa70f1a642da031105b000015e363007e000044f000000000009b93bf90f5190a5a620b09bd0000bfe800000006827223e5800039a117c00000001b3c73d0000965a1085360000c8d022000000000002f40563207cf020a8aa3a0d121cc09e827f032c3bb1ec8cf90000da812e0d4b0ce0dd411f862144500002410000000000003a0a1b4014b1730489e18001122395d068970c00000003d380008130000d1d189a19344d4d9031dd1a130ad11e00000410d68c1d103800041ed05408ccc9d000032f92645d4841c0001cb6ed934d009d1d38cf41ae0ea42ec4000121c39e800026e00002208000edc148277722fca6e00000a023f07a31cb80003af89a9145c000245c835000035716125252b7c1700000b3c41fc53200002148f446b11f84cb907b4dff0b4800000005b10000be70000c6e08622b180004133b84000000000000000001f3c8c80000ff218f400014b80002bb40000000dd6000000022900001a748ec03c4010227ed65996cdbf2d1
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1457936047654d1000519249811d9534407586421a187254d100040f259841c9534400181c636107254d100660b189841c95344075924216107254d100040fe63641c9534400103d981907254d100060760c641c95344001c24211907254d1000607613631c9534400148d9210e7650d1000523648431d943440014969110c7650d1000526640431d9434400160d9210f6550d100049364e82d97624400141d949d763d8910004176627518f624400141d949d463d8910006836136314b624400124d9818c52d8910006836106314b624400103d94e1d53d89100048b6508254f62440758557160c52d891000683a118314b6244001a0d8460c52d8910066139c58314b6244075a467160c52d8910066131c58314b6244001455939d571d89100059164c525c7624400124c9660e75d89101e6519c5839d7624400124e989d763d89100058365275d8f624400124d989d463d8910005836527518f6244001a0e8460e75d891000683611839d7624403784e7160e75d89100e6131c5839d7624400122d94e1f53d89100048b6538754f624400188e8750c43d89100059164e755c762440cb05c9760c5258910006071d183149624400181d84dcc52589100050765075d8c624400141d941d463189100068361363148624400124d9818c52189100068361063148624401905c985cd53189100049364e859d8624400144d93a167618910006139d9831d462440759447160c751891000493a6075d8c624400160d941d76318910004936607518c624400160d941d463189105d63121c63544624401924c985cd53189100062361d4310c624407546492606769491000417e4d87d8a524400144f9361f62949100040fa6075d92324400141d941d7638c9100050b65075d8a324400105e981d7634c91006417a5e8654d324400505e989d9534c910004172607654d324400181c87d91534c9100051325d53d89324401944c9754c624c910006152197354f2144175cc27018c62c85100051364c529da214400124e9814b63885100058365052d8e214400144d9314a760851000493a6052d8c214400160d9414b63085100055164c529d821440013469814b630851000591a5852d8c21441a3a468614b6308510005c165052d8c214400164692d946308510004d16605218c2144001646961486308510005c16505218c2144001e07641486308510007811905218c2144035454965cd53085101d6512097354c214407526598d97620851000691a1463d88214400164593a17620851000499e6153d882144001a448518c62085101d4d1261534c821440016449654d320851000691219534c8214418de046454d32085100641b24987595430400160d9210d6550c10064172617354e620401905c97619534c8100651a249655c021040014599314b7644010
  | 1 => 0x49364c82553624c00503e989d954509300660b9c98414b614c01984e7260c52d85300060b6117214b614c00184d835c852d85300641b24987550614c0016259414b61085300059164c52d84214c0016259414861085300059164c52184214c00160d94219534cb20006836156450d32c81835449754c714cb202a711dd9531c532c800144f9754d329872001417a5f83591538800160d9210d6550e200040fe518758e528800160d940c9654ca200051564e651c53288097264926154398620006a150d8210e6188097a447260c529862025e91c818314a6188001a452060c52986200069160f7214a6188001a854360843586201d6911c98314961880358548754d32586201d591249534c96188001a85844c832586200059164c52986218800181d845cc63d952000607611731cf65480014959418c7158d205dc0f25d84149634800103f98dd05258d2000607dd183149634800181c7460c5258d200050d65052dc563480014559314b7158d200050d650521c56348001455931487158d2000523648439d9434800109d9810c7650d2000523648431d9434800121d9810f6550d200058364843d95434801905e97a19534c92000549650521c532481a3c4463148714c9200058365063d95324800124e96a19534c92015493a5c8654d32480cb24c97219534c920004936508654d324800124c98d91534c92000683e136454d324800124c98591534c92000d1325d6454d324800164491591534c920004932598550d324800328c98591434c92000d2325d6450d324800168491591434c9200059125953dc532481a3c44631d4714c9200055125d531c532480016449654c714c9200d7111d9531c532480016459314861885200071258d535c02108097924216107254f1025e910858314b62c40978547160c5258b1025e190878758a52c400124f9854f624cb1025e512097354c21c40973449854d32087100660b989841c9538401984c825cd5398a100048b6508254d6284001a0e8460c5258a100068361183149628400142d941d5628ca100651325d53989328400124c9854d624ca100051325d53589328401984c6260e72d95101d651085839cb654400121d94a0b65d8d10004872598414b634400181e87d9052d8d100048765282dd7634400188f7460a74d8d10004876508714b634400181e87a1052d8d1000607a1d8414b634400181d8761052d8d100050b65285dc9634400144d93a177258d100040f25d84149634401982c726105258d100040fe6374149634400181f7460c5258d10006071d183149634401984c7260c5258d100060b61372149634400184d83dc85258d100041765e82d94634400121d94a0b6518d100059124981194634400121c966105218d1000487e6364148634400181d87d905218d100060761c641486344
  | 2 => 0xc987c848750d421853200781a5543508614c801e059550d421853200781e1543508614c801e048550d4218532006a150d82d00614c8014549654e719813200515259535c6604c8cb84d72219531813200616e1d53580604c801a188454d6018132066131c983149644c40184d83dc8525913106613189831c9544c41984e7660c52d89310049364c82553624c401a0e8361052d893100683a118314b624c401a0d8460c52d893163e89d8584148624c58fa476160c52189310660b20974550624c40144d931d762909310048be6154d89424c41942c975506250931006076137398d658840181d84dce73596210068398d8414b638859724f9660c52d8e2160e0d9c58414b63885838567160c52d8e210060bd8d841c9538840182d636107254e2106649985841c9538840121e9810d6550e210058364843595438841912c985d1548ca210051564e65dc5328840152594148714ca2168f1198c521c5328840160d9498d654ca2115493a5f8654d32884cb24c97e19534ca21004936538654d328840124e98219534ca2100493a636454d328840124e98591534ca210645325d8550d328840124f96615434ca2100ca3a636450d328840348e97d91434ca2100591e5953dc532885a3c46631d4714ca210055125d531c532884016479654c714ca210d711dd9531c532884016499314b60982211d69108583149608840182f726105258d2163e0ddc584149634859384f7260c5258d2163e15dc583149634840160d9210f6550d210058365032d95324840145593194714c9210649324983d51630841984c7260e7654c2106613a1d63dc95308401a0d8458c7254c210054965072dc55308401c45631cb7154c2100549650721c55308401c45631c87154c21065132497558d43084011659814b7150c210055164c52dc54308401165981487150c210055164c521c5430841912c985d1548c8210660b21d64552320840182c87591544c821005836508654d320840164990219534c821635912456454d320861794487e05534c8218565121c8154d320841914c97615434c821006836156450d32084f568491591434c82163d5125d53dc532084193449854d328842100551e5d534ca210840144c9754d32580210048b26154589428c00142d94a1772586300051364e85dc9618c00103c9761052586300660b1c984149618c00103f98dd0525863000607dd183149618c00181c7460c5258630066131c983149618c00182d84dc852586300061360f72149618c0016259414a61086300059164c52984218c0012669814961086300058965052584218c213a248414961086300059164c52584218c01984c7260c52591300061360f72149644c01906c92614715913000607d91831c9544c00181c6460c725513006613189831c9544c211519949d47050d3
  | 3 => 0x3200643a5d841c9534c81990e766107254d32066431d9841c9534c80190d84dd07254d32066131da82dc5534c80184c7660b7154d320054365072dc5534c80184c76e097154d32066131d8825c5534c81984c861c97154d3200543650725c5534c80150d941ca7054d32066131da821c1534c80150d941c87054d32006151da811c1534c801254966047054d32006151d9811c1534c801944726047054d3206417a63865d5434c81905d93e1f6494932335072597450e524c81981c865d14394932066432097450e524c80114f9854e719093200453261535c2424c81921c966154350932064c32498550d424c81960c9650e5250932157031d943949424c80154691e1d53509320054325d8454d424c80160c966154350932166832198550d424c8d1c0c76615435093200683e598550d424c81930c966154350932006832598550d424c801a0c86d954350932157031db6550d424c81950e97551428c9320060b5c98414b614c8cb84d7260c52d853263c9525983d53614c8017059420953d853263c952598550f614c8f59278755142d8532005892595450b614c98d9478754d42d85323d661e1d4350b614c843a848650d42d8532005c16554350b614c98fa267261052d8532006895c98414b614c9b5a457260c52d853261e0de1d5450b614c98f6249255142d8532006a160d4210b614c8018578754d6118532006a150d82104614c801a1643610651853260c9525983d50614c8016509059153185320069121b8254c614c80170594209531853260c952598550c614c80162594195421853200589a5954508614c801e076454d42185320d6a121943508614c8017059550d421853200781d9543508614c801e046550d42185326b5856528550c614c9af617946154318532005912498550c614c835685921d14318532005a46407450c614c983a264261252185320068561143948614c983a265261052185320068590d84148614c983a2642610521853200685a4d84148614c801a1593610521853260e89a4984148614c801a2772610521853260e891c984148614c801a2732610521853260e890c984148614c983a2720610521853200495e5183148614c9a3a479260c521853260e9124983148614c9a3a477260c521853260e911c983148614c983a464260c52185320049566143148614c801a158450c52185320049564c85508614c8358948750d42185320078150e52508614c9a38648714942185320059164c52508614c801e0543149421853284e1921c85508614c801645932154218532005a164e54508614ca1be0643551421853260d89a6154508614c80162498551421853262709e1d54508614c987c2487551421853286589e4d54508614ca1962593551421853200781d5143508614c801e055450d421853262721e1d43508614
  | 4 => 0x54c0142d920c5741895360f09084315d06254c0141f9360174189530050724d805d06254c1942c9260174189530050de45805d06254c0143491601741895300507a4c805d06254c0141d9320174189530650ba48805d06254c014369120174189530050d644805d06254c1942e92cc174189530050b64b305d06254c01c0d328c174189530040fa60305d06254c0103d980c174189530650ba48305d06254c0142d920c17418953007034c8305d06254c01436910c174189530050d644305d06254e018642161f411895300607a0d74d046254c1982e825d341189538070908574d046254c0181d7460f41189530060b5d182d046254dfdc24215d0411895300607a0d741006254c1982e825d040189530041765d831006254c0181d7460c40189530060b5d1821006254c0184d7360840189530060d5d2811006254c0185573a0440189530060d5d1811006254c018557360440189530660b9c98418b6154c0182d845c862d855300519245641c96154c1982c7261062585530060b613721896154c012649260764185530660b9c9841886054c014359418a71181530065120c825c46054c0143594189711815300519249711846054cd111d98dd3735954300447660431c96550e1d81d8610c725954300543648431c96550c01077985c4715954300519249711c56550c01470905c471595430051a249701c16550c01470915c0705954300447a60435d76250c0150d9210d75d89430054364843dd56250c015859210f715894300519249651c56250c015859210c71589430056264843dc16250c014599399470589430051a249651c16250c01c196510c705894300562648431c16250c0150d9210d751894300543648435d76150c0118d9810e72d854300463660435cb6150c0144d9321572d85430041765d8314b6150ccb81d7460c52d8543066139c98314b6150c0184d835c852d854300447a60435d46150c0150d9210d751854300447a60435d76050c0150d9210d75d814300543648435d46050c0118d9810e72181430051364e655c86050c0118d9810d721814300703594435c86050c015859210e711814300561648435c46050c015919010d71181430040fe61741d1639480181f7460c4058e520060bdd182101639480121d9810e7650e5200583648439d9439480121e9810d7650e5200583648435d9439485521c985916350e520660721d6458d439485560d922116350e520651924971986609480141d94a0c76551320660760f421d9544c81984d8390876551320661360d421d9544c801c0d43508765513200519245421d9544c80154691e0b7454d32006151db81591534c801854762056454d32006161db80591534c801858762016454d320068619080591534c80190d84dd37254d32066071d9841c9534c80190e876107254d
  | 5 => 0x910a10000000000100037c000000000000000008700000000000000001398000006100016c36a15d0c9e915200000000000000000004740000019b20434800a3f000000000000009892f0a80000000001c1280007100041018d16000000000938000008c80010b8000005f2210000000000024c1df20106000000001b41fe9a000000000000001b20000000014b0ca3e0cd161227000000004b04dca60990000000000000000005000000000fa0541be0000000003c568000f01465140026f00000000070000318000000000000013e2d0228000004064f13483a1e6000000750c00000000017078c000fe0c2096dea1a342000b205993c000f31783710d3218001b00000013b0007340000000000013466000000878ec0005a441a550000000012d000000000000006553005f85c0d5330b639c6746718c2b27a000000000000004028020020000100700c01000000014004008000000040000100a004000000000040000000200800805000008000040000040100000a04001800000000000010000000880500004c0080100200400003006000018010000000000100600002000012008020010000000280400c000018050000000400700e00000804000000000000020040200000400001800002000000000140040000000e0000100100c00002009008004090030000040080000203801006000000000000000000000000400000000000008000000040000100000800000802000000010000000080100100a01003001000048000060000080000200800400805006000000010000040000300a000010000020000180300a0000000100002800000008040000010020140000b002000028000000040080000000001800002004000000020040100300400400000000004020000041de61711c76454c19c0e625cd74189530050da46865d06254c0143591a19741895300549245325d06254c1982e825d364189530060d5d3815886254c0185573e0562189530060d5d0815886254c018557320562189530650ba4a435d06254c1942e9210d74189530070390d325d06254c01464914c974189530050b64a835d06254c0143691a0d74189530050d646835d06254c0181d8320d74189530050b648835d06254c19c0f934c9741895300703a0d325d06254c01c0d834c9741895300709e45325d06254c0142c914c9741895300709245325d06254c01424914c9741895300507a4f815d06254c0141d93e0574189530650ba4b815d06254e01c2421e0574189530650b249815d06254dfdc242120574189530040fa63315d06254c0103d98cc574189530650ba4b315d06254c0142d92cc57418953007034cb315d06254d8fc2421cc574189530650b24a315d06254c0142f924c574189530650b249315d06254c01c0d324c574189530650ba48315d062
  | 6 => 0xbc790a90000009400281d4020000003840c764001c5000000001d10000004758300030c0000031e0009648411a124720003f64d0001fa000000f78300fa2240005589b4cc0024f00041c0000000034464e020766fc6006b3cb6f2f52360007480787743c0006d09a000000d0256000001130000004c800000000000000003c17b000150000598000000006ce0000000000000000000000000001df000000000420000014f87f0000015f2d40005e00006c1a0d2006000000cc8002746dc000002ec420b191d0006e4150002110000000000000000000000220000e3000001299ad0001d0f68433f8000000000000000004c000000000000a60009a95d0b8830b80e9800358002120001e00018000000000000000001210000006a4000003041e51112312a000000003286d6000002ea000d58003233f4860ca4e499530a643b70000023b20d7500000024419d0b8000000000003200000004808482000a680015a1080025d000859148000002dc8d0a709900000022382148fc000158000d5c17000706000004be000000000000ba7a8000680000025900000000000344000ee8001bc39d1e09d00042c9800000000000000000000000000000000020a00092011800000000001b18086db102280000011c000000000af000000000002390366783f84a000000a0000000000000c400004a2bc0000000000000000000808d400000000000000000000000005be000000000000000000000000081052000000000000002b00000000000000000000000bf0b00000000000056e93400000000a38003a0000000b1000000001df000000001d327a98c000130000000000000000000000116000000002bd00000000000440000e01980008f05503d0006287c0000000000000000000000192000000000000cc00000000176ff5f5050090230e83809440f9a80e44140015c3160000000000025c0000000000000234000000c816d13e7cebe20e07e624002524b8850000111723bc0000038669400039a3e0000000000047027c0000000074a6b0000bcf0098000000130001680000022500000020a1d0202a60009c0a02080000000000000000000000001171b60de55c00000000aa000412000000003810380015b00061c000d33c446c0580000000000047000000000000005e8000004da0000000038831d18000000000fc9b82e899c00000322000908000007b9238000006a888c002720002f0001f23a90d80031c76d035a3000000d7172000000000002b000000000000621248003900008c90f8000f10280007a2940000047c1520026e000000000002060000000020f6ec0000000016c000002ac2a2bb9cb000000000004220000016522a000d78e63e0000e103a880450ed5ba0001a44b471494000fb80000000000000000000768000008b8974623d6
  | 7 => 0x501c90e61f8000853e483c001b00da89c000000005eca88ae15600125800000000c30000000001580000004800000000000000000000000001a2aa2cc001381b8000000a2a2c0b0ff0190c8000d2c000000000003100024867d110000000022b2000000000001a7c400000254000eb0003fb3f021528208000000000002e800000000000000000000003d40000000000000000000d0c00000000ae4390d8000000000000000a80000000035c000000000000000011600000000000002230005cc8c000900934000001900000015280063aed1ac088244ece101428ccc09f60002b6a7a2f12c59c0018a0001b9261ba9ca000d7c0017a510970073f59680000009e334018c146a770de0a60000f6e626a0eb3c85aa1c2868b4a98f4000000000004487fc6ba043fa0505d800000000000000000580000000000087000000000848000000000000028c6607080000081cf0800000000000003b000010000000000989a6000000550003ce086000000000013616e00064c9f800000340dddd706e000bf000000000da40000023c7b91329483492800000000000000000009000038e0b400000224000000b200018e0004542a428c900026c000000480b40000000000014e000002fe6c2001d511c000b10af4268a8460f149c3ec2580cc165bc2687b1f4094001b32561381f0002ae6c46ec002fa16400000000000000b02f2000000000005acc6800290144978000be0010f800248000f28000005380001800000000000000000000003943ac00000000000000000000011886f00009c002570ec000000000000000000000035417d96000000ce0001ec7cc1dc001b2000000368a13b8a4800000000000000003093809b4300013880000000000129119000000a2000000c296bc8c000001c647a000001cf19e000000003c3000000002c906e0000032e374cf800000950a0800000000000000000003d24500000000000000000498000000000012c1968dd000000002400017100000006000000000000000000008680010c000000004b61740000034e2900006a0006d800000000000001603
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xb002f2000000e80003c000020068d804e55880001c5000000000009401964b8900000168011bc0000000000428919bee2c1b900400130000300000002a40a42806a00000003401187160002b000000000019800488f7000d6c38100146c000003a6120012018260000700000001700ac0280000633007c0340000000000010100000000010104000084818100000000340643245325d06254c0121250b2441ae8312a600b01686834c9741895360e80b4648a64ba0c4a980340683245325d06254c01a02c1922992e8312a600d0108693e057418953006048434c662ba0c4a980300d984cb315d06254c0160250a6598ae8312a60090928592cc174189530058094299460ba0c4a980300d984c8305d06254c0160250a64182e8312a600d014c9910c174189530070084341ae9a08c4a980300d86648431c96550c0128250b24218e4b2a8600d025959210c7058943004b0142c9086382c4a180300d98594435c86050c01a02a1922a10ecaa26400a41686976107254d320660190cca0e4b8aa699003044961c9811c1534c801482d20e4c08e0a9a6400c09e1c9655142d853263620f0ecaa86a16c29931e604a66554350b614c98390243328412a630a64d1e0121d4314942185320060890ec990aa10c2994270248726154508614c8015025432aa1a8430a64009816a48550d421853284f0090e42a86a10c29900220da998d8414b638858341350ec6c20e4a9c4200d0198d94148714ca216948894fcb2a638a65108034059458c72dc5530841940653b0ab228699042008892a194149610863000640908c98a4b08431800340463650521c532481a52225392ca98e29924000c09084966107254d100070084231b08392a6883470447166063148624400130253328296c610a2000c81a199414b6308510004c0b49496ca3184288002604a66505218c2144001303d4ec8290c610a2000c8166364148630851000640b30320a43184288002a05a4a1463d882144001502d210a318c410a20008912a48654d3208510
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x2639402000002c060010080460005005b308698cc57418953006401652859210c705894300600496690726047054d32006005a3e1c9655142d8532006004876a48550d4218532004405ba98d94148714ca21004405ba18d94148714c920005005b3084966107254d10004805ba084636107254d10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x4c
  | 5 => 0x4e
  | 6 => 0x138e
  | 7 => 0x94c
  | 8 => 0x94e
  | 9 => 0x124c
  | 10 => 0x124e
  | 11 => 0x138c
  | 12 => 0x3
  | 13 => 0x8c
  | 14 => 0x8e
  | 15 => 0x150e
  | 16 => 0x98c
  | 17 => 0x98e
  | 18 => 0x128c
  | 19 => 0x128e
  | 20 => 0x150c
  | 21 => 0x9cd
  | 22 => 0x9ce
  | 23 => 0x5
  | 24 => 0x12cd
  | 25 => 0x12ce
  | 26 => 0x20c
  | 27 => 0x20e
  | 28 => 0x140e
  | 29 => 0x154e
  | 30 => 0xb0c
  | 31 => 0xb0e
  | 32 => 0x140c
  | 33 => 0x154c
  | 34 => 0xb4d
  | 35 => 0xb4e
  | 36 => 0x144d
  | 37 => 0x144e
  | 38 => 0xccd
  | 39 => 0xcce
  | 40 => 0x15cd
  | 41 => 0x15ce
  | 42 => 0x164c
  | 43 => 0xe8e
  | 44 => 0xecd
  | 45 => 0x94056
  | 46 => 0x95396
  | 47 => 0x21396
  | 48 => 0x20056
  | 49 => 0x140056
  | 50 => 0x155396
  | 51 => 0x1649
  | 52 => 0x449
  | 53 => 0xec9
  | 54 => 0x1a49
  | 55 => 0x138956
  | 56 => 0x209
  | 57 => 0x20956
  | 58 => 0x94b
  | 59 => 0x95556
  | 60 => 0x94216
  | 61 => 0x140956
  | 62 => 0x154956
  | 63 => 0xb4956
  | 64 => 0x94b56
  | 65 => 0x1449
  | 66 => 0x144956
  | 67 => 0x95456
  | 68 => 0x1409
  | 69 => 0x249
  | 70 => 0x94d
  | 71 => 0x14c9
  | 72 => 0x139256
  | 73 => 0x21256
  | 74 => 0x141256
  | 75 => 0x138b
  | 76 => 0x138216
  | 77 => 0x141396
  | 78 => 0x139556
  | 79 => 0xb5396
  | 80 => 0x138b56
  | 81 => 0x145396
  | 82 => 0x139456
  | 83 => 0x98096
  | 84 => 0x20094
  | 85 => 0x20096
  | 86 => 0x140096
  | 87 => 0x150996
  | 88 => 0x140996
  | 89 => 0xcc996
  | 90 => 0x15c996
  | 91 => 0x98d
  | 92 => 0x151296
  | 93 => 0x21294
  | 94 => 0x21296
  | 95 => 0x141296
  | 96 => 0xcd516
  | 97 => 0x15d516
  | 98 => 0xa0c
  | 99 => 0x209d6
  | 100 => 0x1409d6
  | 101 => 0x44c
  | 102 => 0x164d
  | 103 => 0xe89d6
  | 104 => 0x104c
  | 105 => 0x1049
  | 106 => 0x1a8c
  | 107 => 0x180c
  | 108 => 0x130c
  | 109 => 0x212d6
  | 110 => 0x1412d6
  | 111 => 0x1452d6
  | 112 => 0x1a89
  | 113 => 0xb0216
  | 114 => 0xb1416
  | 115 => 0x140216
  | 116 => 0x141556
  | 117 => 0x20b16
  | 118 => 0x154214
  | 119 => 0x154216
  | 120 => 0xb4216
  | 121 => 0x144216
  | 122 => 0xcc215
  | 123 => 0xcc216
  | 124 => 0x15c215
  | 125 => 0x15c216
  | 126 => 0xe8216
  | 127 => 0xec215
  | 128 => 0x140b16
  | 129 => 0x154b16
  | 130 => 0x155416
  | 131 => 0xb5416
  | 132 => 0x145416
  | 133 => 0xcd416
  | 134 => 0x15d416
  | 135 => 0xe9416
  | 136 => 0xed555
  | 137 => 0x144b56
  | 138 => 0xb8c
  | 139 => 0x28c
  | 140 => 0x184c
  | 141 => 0x148c
  | 142 => 0xe9456
  | 143 => 0x15ccd6
  | 144 => 0xcd5d6
  | 145 => 0xd0c
  | 146 => 0xd0cd6
  | 147 => 0xd0e
  | 148 => 0x160c
  | 149 => 0x160cd6
  | 150 => 0x170d
  | 151 => 0x40c
  | 152 => 0x160e
  | 153 => 0xe8cd6
  | 154 => 0xcce96
  | 155 => 0xeccd5
  | 156 => 0x188c
  | 157 => 0x10c
  | 158 => 0x16cd
  | 159 => 0x1a4d
  | 160 => 0x14c
  | 161 => 0xce
  | 162 => 0x198c
  | 163 => 0xa4c
  | 164 => 0x134c
  | 165 => 0x168e
  | 166 => 0x2cc
  | 167 => 0x14cc
  | 168 => 0x24e
  | 169 => 0x19cc
  | 170 => 0xbcc
  | 171 => 0x16ce
  | 172 => 0x3ce
  | 173 => 0x1a0c
  | 174 => 0xd4c
  | 175 => 0x170e
  | 176 => 0x18ce
  | 177 => 0x194c
  | 178 => 0x178e
  | 179 => 0x74c
  | 180 => 0x1409405e
  | 181 => 0x4956
  | 182 => 0x213895e
  | 183 => 0x2c9
  | 184 => 0x289
  | 185 => 0x1489
  | 186 => 0x24211
  | 187 => 0x44d
  | 188 => 0x8214
  | 189 => 0x98216
  | 190 => 0x995d6
  | 191 => 0x128216
  | 192 => 0x129516
  | 193 => 0x24b
  | 194 => 0x131054
  | 195 => 0x20d
  | 196 => 0x154d
  | 197 => 0x21554
  | 198 => 0xeccc21d
  | 199 => 0x16cb
  | 200 => 0x1a8214
  | 201 => 0x45414
  | 202 => 0x1a9554
  | 203 => 0x140454
  | 204 => 0x141516
  | 205 => 0x1403d6
  | 206 => 0x1415d6
  | 207 => 0xd0214
  | 208 => 0x160214
  | 209 => 0x44214
  | 210 => 0x20454
  | 211 => 0x164214
  | 212 => 0x21654
  | 213 => 0x104214
  | 214 => 0x21054
  | 215 => 0x21a94
  | 216 => 0x20d14
  | 217 => 0x21a14
  | 218 => 0x45554
  | 219 => 0x165554
  | 220 => 0x154454
  | 221 => 0x155654
  | 222 => 0x105554
  | 223 => 0x155054
  | 224 => 0x155a94
  | 225 => 0xe8d0cde
  | 226 => 0xd0cce9e
  | 227 => 0xcced5
  | 228 => 0xed715
  | 229 => 0x170cd6
  | 230 => 0xcd796
  | 231 => 0xcd616
  | 232 => 0xd1054
  | 233 => 0x104114
  | 234 => 0xced5
  | 235 => 0x105314
  | 236 => 0x12ced5
  | 237 => 0x104d14
  | 238 => 0x170ed5
  | 239 => 0x105894
  | 240 => 0x1a4ed5
  | 241 => 0xd2d6
  | 242 => 0x1692d6
  | 243 => 0x1689d6
  | 244 => 0x1789d6
  | 245 => 0x25456
  | 246 => 0x24b56
  | 247 => 0x14d9d4
  | 248 => 0x16d456
  | 249 => 0x179456
  | 250 => 0x19d4d4
  | 251 => 0x16cb56
  | 252 => 0x10e
  | 253 => 0x180e
  | 254 => 0x28b
  | 255 => 0x28e
  | 256 => 0x184b
  | 257 => 0x184e
  | 258 => 0x3d5d6
  | 259 => 0x3ccd6
  | 260 => 0x58e
  | 261 => 0x1715d6
  | 262 => 0x178cd6
  | 263 => 0x18d796
  | 264 => 0x11054
  | 265 => 0x44215
  | 266 => 0x24216
  | 267 => 0x16c216
  | 268 => 0xd02105c
  | 269 => 0x104d021c
  | 270 => 0x58e96
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 1506
  | 6 => 6085
  | 5 => 4546
  | 4 => 628
  | 3 => 59
  | 2 => 9
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
  | 8 => packedAt gbK8 (1376+((h/22+packedAt gbK8 (1222+(h % 22)*7) 7) % 80)*7) 7
  | 7 => packedAt gbK7 (63390+((h/639+packedAt gbK7 (55722+(h % 639)*12) 12) % 3370)*12) 12
  | 6 => packedAt gbK6 (325288+((h/2372+packedAt gbK6 (292080+(h % 2372)*14) 14) % 8542)*14) 14
  | 5 => packedAt gbK5 (290197+((h/1691+packedAt gbK5 (268214+(h % 1691)*13) 13) % 6696)*14) 14
  | 4 => packedAt gbK4 (46611+((h/241+packedAt gbK4 (43960+(h % 241)*11) 11) % 1536)*11) 11
  | 3 => packedAt gbK3 (4955+((h/22+packedAt gbK3 (4779+(h % 22)*8) 8) % 141)*7) 7
  | 2 => packedAt gbK2 (843+((h/3+packedAt gbK2 (828+(h % 3)*5) 5) % 19)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f01ff01ff81fffffc0fffffd13e7e3a23f1ff
  | 1 => 0x81fe0ffe0ffe0f807ff07c03eed9b3c5dcce67
  | 2 => 0xfffff0000ffff0007fff8003f0e1c3fe1f0f87
  | 3 => 0x1fffffff00000007ffffffc3f01fc07e00ff8
  | 4 => 0x1ffffffffffffff800000003ffe0007fff000
  | 5 => 0xfe00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x12001100118014a30c00a51a400a16180150ab
  | 1 => 0x9016076206a20d053510682a8658b2c0ccc665
  | 2 => 0x65ab70108b55a00a5aad005130a1416e170b86
  | 3 => 0x21cdaab5a010801063ce52e03b01e807600d50
  | 4 => 0x41f1ccd9cc79ca5c008400803df40007baa000
  | 5 => 0x788100e100610c60030863023fffffb0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36693
namespace PEqualNP.Outside.L_meta_36693
open PEqualNP.Outside.L_meta_36693.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 14 := bs0_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 6 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 13 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 75 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
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
theorem bs5_4_608 : Interval s5Atlas 4 608 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 626 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 bs5_4_192) (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)))) (concat (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 (concat bs5_4_416 bs5_4_448))) (concat (concat bs5_4_480 bs5_4_512) (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)))))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 699 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 bs5_5_384) (concat bs5_5_416 (concat bs5_5_448 bs5_5_480))) (concat (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)) (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 42 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 9 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 59 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_608 : Interval gbAtlas 4 608 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 628 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 bgb_4_192) (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)))) (concat (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 (concat bgb_4_416 bgb_4_448))) (concat (concat bgb_4_480 bgb_4_512) (concat bgb_4_544 (concat bgb_4_576 bgb_4_608)))))
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
theorem bgb_5_4544 : Interval gbAtlas 5 4544 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4546 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))))) (concat (concat (concat (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)))) (concat (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))))) (concat (concat (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792)) (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)))) (concat (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 bgb_5_2080)) (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))))))) (concat (concat (concat (concat (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 bgb_5_2368)) (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)))) (concat (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 bgb_5_2656)) (concat (concat bgb_5_2688 bgb_5_2720) (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816))))) (concat (concat (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944)) (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 (concat bgb_5_3072 bgb_5_3104)))) (concat (concat (concat bgb_5_3136 bgb_5_3168) (concat bgb_5_3200 bgb_5_3232)) (concat (concat bgb_5_3264 bgb_5_3296) (concat bgb_5_3328 (concat bgb_5_3360 bgb_5_3392)))))) (concat (concat (concat (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 bgb_5_3520)) (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680)))) (concat (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 bgb_5_3808)) (concat (concat bgb_5_3840 bgb_5_3872) (concat bgb_5_3904 (concat bgb_5_3936 bgb_5_3968))))) (concat (concat (concat (concat bgb_5_4000 bgb_5_4032) (concat bgb_5_4064 bgb_5_4096)) (concat (concat bgb_5_4128 bgb_5_4160) (concat bgb_5_4192 (concat bgb_5_4224 bgb_5_4256)))) (concat (concat (concat bgb_5_4288 bgb_5_4320) (concat bgb_5_4352 bgb_5_4384)) (concat (concat bgb_5_4416 bgb_5_4448) (concat bgb_5_4480 (concat bgb_5_4512 bgb_5_4544))))))))
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
theorem bgb_6_6080 : Interval gbAtlas 6 6080 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6085 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 (concat bgb_6_384 bgb_6_416)) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))) (concat (concat bgb_6_544 (concat bgb_6_576 bgb_6_608)) (concat bgb_6_640 (concat bgb_6_672 bgb_6_704))))) (concat (concat (concat (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896))) (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))) (concat (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280))) (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)))))) (concat (concat (concat (concat (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)) (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664))) (concat (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)))) (concat (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))))) (concat (concat (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)))) (concat (concat (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))) (concat (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))))))) (concat (concat (concat (concat (concat (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)) (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200))) (concat (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)))) (concat (concat (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488)) (concat bgb_6_3520 (concat bgb_6_3552 bgb_6_3584))) (concat (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680)) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776))))) (concat (concat (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968))) (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)))) (concat (concat (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352))) (concat (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448)) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544)))))) (concat (concat (concat (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736))) (concat (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832)) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928)))) (concat (concat (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024)) (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120))) (concat (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)) (concat bgb_6_5248 (concat bgb_6_5280 bgb_6_5312))))) (concat (concat (concat (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408)) (concat bgb_6_5440 (concat bgb_6_5472 bgb_6_5504))) (concat (concat bgb_6_5536 (concat bgb_6_5568 bgb_6_5600)) (concat bgb_6_5632 (concat bgb_6_5664 bgb_6_5696)))) (concat (concat (concat bgb_6_5728 (concat bgb_6_5760 bgb_6_5792)) (concat bgb_6_5824 (concat bgb_6_5856 bgb_6_5888))) (concat (concat bgb_6_5920 (concat bgb_6_5952 bgb_6_5984)) (concat bgb_6_6016 (concat bgb_6_6048 bgb_6_6080))))))))
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
theorem bgb_7_1504 : Interval gbAtlas 7 1504 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1506 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))))) (concat (concat (concat (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928))) (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))) (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 47 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80eeeaeae0eeeaea80
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372960 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36693.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.and,[1,2]⟩,⟨.and,[2,5]⟩,⟨.or,[4,8]⟩,⟨.or,[3,9]⟩,⟨.or,[6,7]⟩,⟨.and,[1,11]⟩,⟨.or,[0,12]⟩,⟨.and,[0,7]⟩,⟨.or,[10,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36693

open PEqualNP.Outside.L_meta_36693 in
theorem PEqualNP.Outside.L_meta_36693 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
