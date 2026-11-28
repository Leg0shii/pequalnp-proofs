import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_38493.Model
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


end PEqualNP.Outside.L_meta_38493.Model

namespace PEqualNP.Outside.L_meta_38493
open PEqualNP.Outside.L_meta_38493.Model
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

def SBf (j : Nat) : Nat := [7, 4, 7, 7, 7, 6].getD j 0

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

end PEqualNP.Outside.L_meta_38493

namespace PEqualNP.Outside.L_meta_38493
open PEqualNP.Outside.L_meta_38493.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x4b00e0061c089e0400070d40002c1001041000240007ff32fc31fc43fd31ff42fc10ff41bc40ff31fe20ee20fd40f610fe43ff20fc32fd21be40fd42fe40fe30fe42dc30fe10fd41fd43ec20fe21fc40fc41ff43fd30ff10fc42fe31de30fe41ff30ff21ff40fd20f410fd10fd32fc21fc20fc30fe32
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x2c5b00610012011a02021300000c060000004d0012000203082d03030000052a1c00000000010041020000020f01050201012201260012007b0010010000071e020003123c00360b01050000042806000a1600bda82635d53c82eaa3906b10020af298836e508827ea8904f95332af29e853c544c678a890cf95310bc282833c544427ca0204f553329f2a6615c53486bea6a0f908010ba28a61cc30883a861085754f10cea18875d53086bca7904f95031db20021da500c2eea2986d10010d6a1085ce308827ca9195b54a43bb284213c54483ac61085b14940af29c853d548cadca420d714d20b7296813f544c6e8a2a05bd4931b6292613e54086baa620db14910f810021f250043e680085b54b40b7296213d54cc3c841085714d40ce20461d030042daa418fccc010b6a96617b50486eca0086d90210f3100217651c8374a0205714d10d720441b440842dea4a0eb10220afa9a415e530867aa9884fd5110b728041f030043b060085dd45409f2a641ce30082d8a498d754f409faa2436e5290ebca788760c310e6180415f534873c81187c10010f5280415d5390af6a0a0d7d4d40bba8a419e400c39a64196c10010f0100217451482b8a6a0db14941ce2006178504c678a8985b94b43af284613d54086dea4a04fd5130d7200417850486bea6885b54b10aea9e85d430043d040084f94240b6a9687e620842daa420ee10310af280613d54c82eaa3987cc80109eaa063d630043d041885b94b30bb28e817551d02dea4985bd4910dc200216e520c6bca7a05d94730
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x8120104200043006e262d0010e810220042b26090010b498f40043c03088010ac99330042d2608c010b498f20043c23008010e81002004392400c010ac99320043c03008010b898b3004390408c010b898220043a24008010e21003008390400c010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 144
  | 3 => 19
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s0K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/83+packedAt s0K4 (3888+(h % 83)*8) 8) % 144)
  | 3 => 2*((h/13+packedAt s0K3 (722+(h % 13)*5) 5) % 19)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffc07fffffffffffffe03ffffffffff87fff
  | 3 => 0x1fffff803fe01ff00fffffc07f01fc07ff98c7
  | 4 => 0xe0ffffffc0001ffff00fffff8001fff80fe0f8
  | 5 => 0xffffffffffe000000ffffffffe00000fff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x8412c092492145112122a2c58b522d4a93ab5b
  | 2 => 0x825742492528a2a4a45502ad5a556952855ad
  | 3 => 0xb04995762394d348ec89f560663198c7cd98c6
  | 4 => 0x1d8e26473b1b1c8c88ee79b340c1e3e18ee0f0
  | 5 => 0xdef038783c1c1f0f0f0f9e3c78f903060f7e00
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_38493
namespace PEqualNP.Outside.L_meta_38493
open PEqualNP.Outside.L_meta_38493.Model
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
  | 3 => 2*((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 1)
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
end PEqualNP.Outside.L_meta_38493
namespace PEqualNP.Outside.L_meta_38493
open PEqualNP.Outside.L_meta_38493.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1245a0220400402c20003000e10da01449bbd40be42fc31fc41fc20be43fd42bc41fc43ff20ff32fe31bc42fe10fc30fe32fc32fd41fc21ff21bf40fc40fd43ff30fe20ff41fc10bc43fd31fd30fe30fc42fe43fd21ff10fd20ff42fe21fe40ff43ff40fd10fd32ff31fe41fd40fe42be41
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x380c0804144800000400003ec8a008906c2c0c00200000102844686015240000f82458141804000066d48c043c201c00940c04000c0419180004141c10c8044030000128ac000c1000740080044c002c1c042c240044003c0000001dbc20344802d8a4984f151319f2a4613d54c867ca7a04fd53209f294879c43cc678a4a05b149109f298853e53106eaa2105714d10d7294835d53c8758a4a04f542439f2a08177515033ca7215d94643da28a813e54cc67aa020ed104109eaa443b4418c738861879484219eaa4613c53502b8a6a04b94a41d62144177514827ea818cf15330d729085b441486baa6105d94732baa8c859c434c67aa9084f542419faa0659d539067ca721d794c109faa2213e5210aeca3214f94740b7294636e5290edca4185d94632b7a92613d548ca7ea810d754e21aea98216f525035884994f94e419eaa6631e5390b5aa521ed54642daa8c877451502eaa3194f94a41db28c856d520c27ca8184f542429e2a6413d5010ad8a4a06b10b21b7296633e5404278a9885d94430aea9c853c544867ca910cf552209f2a4213e5190a7aa8185b54a31baa8e655e538867ea8984f15130af29c836e520435884104f550109f2a46377514c2b8a69067d4d40b6a90213e5190f3887186710d329b28c87cd320ca7ca221cfd51319e2a241bb50503688298cfd53109f2a6653e5310f3aa7214f540439e2a2652e5290ee8a2906d10610b6a9483365190a78a2a06710f329f290831c535027ca8106b10a32bb288416f524427ca9104f150329e2a0635e5390a7aa9206b10921dba8a813e548ca78a810cf94b40cf29c83d5310c67ca72157d4d209f294856e52906eaa321cfd5132db288832c52502bea6884f550209a28a813e54c867ca320dd145309faa2416d5290ebca6106b94a43cf2988775510c27ea890eb54a418f29c833d54ccb6ca321ebd4940afa9a815e53c867ca2214f948439f288833f54cc338a6a06d10621b6a96633d548c6baa720cf15110
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x20800120ca111e0060e00cc68d000050e1a2408c000029a0808a03160800e87594430c2346155220c9d4851503265254643c514f515022c62540418798f54c822e62d5330c314c525022e62d5131c9548418c72442544208b189548c21c63552208d987544ca2d65108208d98653d021c6354041a95865210a2e62d5031c994a5190f14544c4318d9865310a1e63d50218b98a51d031443547328798e5110a3661d50218798e51d02346154043a358a5310e3661d53308d1855010b0c544c8328b18954843155310621c914b515021e6394b408b98b540862e6294443c314f525022e62d5032c394e529062c6254043c514c515031753145408d59441042366194843c594d5190a1e63948418798f54486366194b40a55865310f2552104108718d5010b0d53108208b98a531062e62d53108798f540cb245214540c9109518cb0d5394a41c310d520c3255294643a358e5210a2e6294f408d987540ca3661d5031c594e5190a3661d5320c554c41042a562944418d185548c30c4354b31c354c42c861e63d5310a558e511061c6355210c554e5190b144354430c9151210870f53149408798f540c70e5354a41
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 186
  | 3 => 84
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/23+packedAt s2K5 (768+(h % 23)*6) 6) % 48)
  | 4 => 2*((h/97+packedAt s2K4 (5022+(h % 97)*8) 8) % 186)
  | 3 => 2*((h/35+packedAt s2K3 (3192+(h % 35)*7) 7) % 84)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffffffffffe07ffffffffffffff87ffff
  | 1 => 0xfc1ffe07e07e07fff8783c1fe0f83e0ffa4e93
  | 3 => 0xffe0fff8007ff81fff803fe0ff003ff07c731c
  | 4 => 0xffffff80001fffffc000ffffc0007f83e0
  | 5 => 0xffff00000000001fffffffff000000007ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x40002410010000001104821010a0284009425
  | 1 => 0xa94664324aa4ae8e582a151a68d0b42b3a4a92
  | 3 => 0x30caa890d349a2b6aa842748ba4139615c6318
  | 4 => 0xa294d1249a0d34db34ce8210dce590426f03c0
  | 5 => 0xc318e1c71c71c71dc7773b9c1086218c77fc00
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_38493
namespace PEqualNP.Outside.L_meta_38493
open PEqualNP.Outside.L_meta_38493.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x2010034000f0801c41010032813c154044058028efe32ff42ff40fc32bc42fe43fc40ff10fd42fe31fd30ff43bd43fe41ff41fd32fc31fe21fc41ff21ff20fd31fe42fd20fc10fd41ff32fd10fc43fd43ff30fe10ff31fc21fc42fe30fc20bf43be42fd40fc30fe20fd21fe40
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xa0e00102040c00082251870e0011000040111e5800300001001c2c18c0e08ac70201190040278a9195794c41af29c433e548875885905bd4943b7a92833d5404278a8994fd51209eaa6656c5250edca598cfd51109f2a0635d53886dca4084f95032af298215f534833ea6a1cf95043b7a92215e53d023aa6215714d209faa2435c534427ca9984f55330d6210433d54cc67ca8084f552439f2a4415d53106e8a2905d947329eaa0616c52506baa6084f95331afa9a219d43ccb5884906b10832b6a90617551ccb3a86994f15110b6a96639d43cc6eaa2184f94a4296292873f544cadaa4084f55031cea1c613f548ca78a8904f95030d6214436d529033aa6214f55032cea18619d434c67aa9106b94842aea9e815d5310a7ca5a1eb149439f2a6653d5390a7ca4216bd49439e2928776510c27aa910ddd4520d6216656e52902d8a4884f15121b7290615e5310b3ca6214f54c42
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x331900280000040009c00008000080000003003154354430a358c42cca8c6250d31c9108514830c6254c42c314c424828d6310920a3189438c28d6310a2187195434ca8d6310b20a358c420861d6395220a3189430c22c6255330c550d51cca1d6315121c910a51ccb0d4354830a318943cca2c6255031c350d52cc70e5310a218b594420ca8c6250f31
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x40000068239286a8e65035d8531092081aed2988510d047250d510c282b988428a41415cc4294732
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s3K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/44+packedAt s3K4 (2430+(h % 44)*7) 7) % 90)
  | 3 => 2*((h/36+packedAt s3K3 (950+(h % 36)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s3K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 1 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 2 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2004088824020000a41280444022914810d095
  | 1 => 0x451891064894a12c0a852429921422b146264a
  | 2 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 4 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_38493
namespace PEqualNP.Outside.L_meta_38493
open PEqualNP.Outside.L_meta_38493.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x1c80007010001040013e80801c000304e1c2000ff42bd43fd43fc21fd42fc40fd30bc42fe43fe41ff10fc32ff40fe30fd32fd31ff21ff31fc43fe31fc10fe42fe32fc41ff30ff43fd10bf43ff41fc42fe10fc31fd20fe21ff20be42fd40ff32fd21fd41fc30fc20fe40fe20
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4287800000288007c0000028000061008100000000000d19221c98a22102807028a80000400004000090a001c1080188500267aa818cf54e429f2a4415e53042dea4884f152329e2a2653d540ca7aa9104f95043bb288616c524433ea6a1cf55221af29e81ac420cadaa5206750c309faa4656e520433a8698ebd4943b6292876f52506d8a4a0cf95031cea1a656e529027ca8185b54830af29c437551cca7aa8085754f409f2a6633d54cca78a8905b94b319f290853f54482dea4a1cf95032cea1c616e520c278a8884f94a429ea98859d43ccabaa710cf952219f2a0213d5490ebaa6084f149439e2a243ac42c83588510cf55030af29885745148358a4a1d794c41d62124175510c258a4a1eb94842cf298853d54cc27ea890db54b31b6a90213e52d0f3aa6214754c42aea9885ac42ccabea6904fd5110d6210437651ccab8a6884fd51329eaa6635c53482bea6884f95330cea1e635d531067ca9995dd4520
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1140204805000c62830d4354830c9108514828c6250d318b594420ca8c6250c30a358c424828c6250f318758c544870c6254c42c550d510c28c6250e30a358c42c828d6310b32c550d51ccb0c5310920a358c42087244294732c394c428861c6550d328758e548822c6255330a358c428862c6255031c350d52cc68c6250f32
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1228239286a8861411c94354732a0ae6214a39940d7614c4248206bb4a621443415cc4214520
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 5 => 2*((h/28+packedAt s4K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/58+packedAt s4K4 (2430+(h % 58)*7) 7) % 90)
  | 3 => 2*((h/15+packedAt s4K3 (950+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s4K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 1 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 2 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 3 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2004088824020000a41280444022914810d095
  | 1 => 0x451891064894a12c0a852429921422b146264a
  | 2 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 3 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_38493
namespace PEqualNP.Outside.L_meta_38493
open PEqualNP.Outside.L_meta_38493.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x10502000000000000bf43dd43ee21ef209d43ec21de43ed20bd43
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x600a00017c7a92878c5250e3aa921e350d20c6a1c438d43086c8a2906350f20
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc150c514828661d494383195434820f6550e21
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | 2 => packedAt s5K2 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/17+packedAt s5K4 (144+(h % 17)*4) 4) % 9)
  | 3 => 2*((h/16+packedAt s5K3 (216+(h % 16)*3) 3) % 8)
  | 2 => 2*((h/1+packedAt s5K2 (152+(h % 1)*2) 2) % 4)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1fffff83ffffff81fffe0ffff83ffffe71f1ff
  | 1 => 0xe0fc1ffc1f83fffe1c1ff0f07fc3c1ffae4e4f
  | 2 => 0xff001fffe003e1ffe01fff007ffc01c1cf8f8c
  | 3 => 0x1ffffffc01ffffe000007ffffe01f00ff0
  | 4 => 0xffffe000000001ffffffffff80000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x40080088010000002022011108044444009095
  | 1 => 0x8a312910ca2550960d0c90a2324288b8a6464a
  | 2 => 0x465a5229474a832ae2172a055ca8150d4b8b8c
  | 3 => 0x94a39c429460d5cd5741888867333811f00d60
  | 4 => 0x18c31873187319f19b99ccce06222021fd6000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_38493
namespace PEqualNP.Outside.L_meta_38493
open PEqualNP.Outside.L_meta_38493.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa282140040000089040007fd5001fd3100ff14005fe5200ff04001fd21007f88405ff21007f4c001ff53017fc8003fc40017f90801fe41017f8c805fc4200ff94007fe53017f08407fe43007f54805fc52027f10401fd5100ff08009ff4101ff14c03fe2000ff90003fc3001ffcc401ff51007f50801fd4101ffcc807fc43007f44001fd50007fc4009fc5400ff84001fe51007f8c401fd40027fd0c01fd20007fd4801fc51007fd4001fd43027fd0001fd54027fd0807fc31027f95005fc32007f4c807ff30007f54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xca200ff582411a7fe61288037f655081fffa126003bf58e3100ff8a1a80037d5414403ff2062042ff0c752005faca88002fd62d5009ffaa48204efd0954277fcc6aa0c7ff4254405fe292a402ff08621006fea6a909bfc3150479ff302842cff0c451047f8c3a9022fc6548005ff1924203ff10d30007fac298002fd64944017fb1a8404ffd0e41007fa86880cbfc2094401fe90a2000bf1855400ffe40a800bfe2048401fe28a4200ffd4e41007f8c2990a7fe5390405763122030ff10d51047fac9a80fffe435485dff082a200ff5855326ffcc4aa0037d5114489ff1028608ffd495028ffe63aa006ff604c007bf29aa62fff94951017d8429082bff32c407dfe302a400ff50b50017f84099023fd54d4003ff9028008ffd5150047fac828802ff60548057f312a006ff14d1026ffca4aa00ffc314c401fe30aa429ff18e41015fcc4a0002fd6448011ff286a605ff10910007fec690003fe5144009fe20c8208dfd475001ef8a7a986bfe6448403ffa022000bfd9520047fac7a900fff31d4c01fea0aa02eff98151005fec4aa013fd4150005ff212a403ff90d53007fea4a000efe634847dff282a415ffc875013ff8c120823fc52d441dff292603eff04152197fc4128802fd6550003ffa826008fdd4551005fac1aa0d3fc63944017eb048202bf98b51047f8a2a800fdc314c4037e3046204bf99754047faa5a8803ff6354805fa10c4201bf18241007fec4a080bfe204c809be2a2a800ff19621007fcca9080ffc318c45ffe312a200ff9071023ffc84a9823ff6214419fe18a4008ff54750025fec8aa022fe655047dff082a446ff04153007fec4a1803fd32440077f31aa403bfd8d43017fca4a1012fe64d4c017eb2c8245ffc8143237fc20a9803bd4150001ffb128030ff18d51097fc64a80037f65440017fb12a008ff19351007fac2a8012fc644c8077fb2aa603bfd8d53017d84299137ff2155011fb288a200ff8c550007fac720803fd6094405ff9024201bf18221027fe8320823fd6014401ff10aa008ff14953047fec1a893b7e5355021ff192802dffd0051015f8c528807fe50c4009fe21c8235ff99251005feca990cfff2094411fea9ea202ffd492101fbc8698022fe6514401ff10a8001ff54120017f864a902bff31c4011ffb16a000ff4c55028ff863aa002df6344005ff10a4200ff595400277e8320807fe30440097f30c8200ff14540007fc62a0003fd43d4803ff206a008ff98f52047f8a1a8813fe4255001feb246200ff58941007fec928803fd4148401fe98a8000ff58a5100ffe60a8013fc5450007ff21a6000ff5852001df8c720813bf4050403fea024003ffcc143045fccaa1002ff6344009fea1a8200ffd895301ff864a9803ff60884017fb028404ffd0a4100df8c0a8823fc53d48017eb0ea608ff95051
  | 1 => 0x7fe4048011ff318a240ffd0552007fec899003ff5290409de2a2a80fff1513000dfcc12081bfe6344001ffb2a2000ff9952000ff02088003fd63944057e312a607ff99110007faa788003fd63c4009fe20aa850ffc87541dffe8099023fc63d5009ff20a8208efd5154007fa6528803ff544c001fe32a6248ffd0553277fca6aa002fd60944057e3148208ff55353017fe6510806fe6054831ff1824201bf1835300ff881a8022fe6548403fe2862000bfd894301ffe8698023ff5454411ff286a430ff94d5101ffea698013fc5450805fe2124218ff1812101ffca698063fe6048401feb22624affc8753007fac0a110bff31d4803fe102a008ff18f50017fe64900c7ff435448dfe302a600ff58931007fac2a00f7fe5350811ffb1ea838ff90f51015f8c488093fe5050491ffa12a608ffd4d51017fe84a910fff40d48017fb2c8204ff9514318ff882a88cffc42944017eb1c4204ffd0d421fff886a901bfc314404dff98a821aff19121007dec48800bfc214843dfe3026200bf58a51007fc831083ffc414c0037fb024037ff90b51047fec9a980afc62d5001ffa9a8428ff8ca41027fc86aa0bbfc6054499ff302a801bf98353015fcc49880efe63d4001fe28c8201ff0814001fe86318803ff658c4017f30ea604bf99251005fac5a8013bf4350809fe20a8436ff04351047f8c9a800ffc4354c01beaa6a400ff90631027e88320803fe414c42bbf296a000ffd952101fe862988037d5314437ff2844202bfd8952025fac920803fd6054807ef98c621cffcc621007faa988023fc52d4011ff30ea800fb50a2100ffaa08800bef2148003fe9862033ff08651007f8c2a180ffe304c801f6a124047ff9495324ffc81a9803fe4148011be280a201ff88150167fe6228823fe50144017fb026221ff94231017f88499013ff415507dfe202a400ff5891000ffa8088003ff6055013ff90e2000ff995421b7fc21a880fff318c46bff2a4a202bf189540f7fca098947ff32d5001fea8e200fffd0530027f886a1023fd52d4001fe30a8400ffd8142017fca4a900fff314c477fe2a26401ff9412014ffe6120803fc6544001fb20e2001ff88140005fec4a0002ff655086ffe196a202bfd8d32047fcc9a8823fe61d40037e306a202bf98a51005fec0a8833ff3148063ffa0aa208ff14c5100df8c0a9803fd42c4007ff996a62aff8c051005fec788107fe30d4809dfa1c8219ff18d21027f8a92080bfc2048409fba0c8200ff94631227f840a1803fd6590491ff322a63bff95132047faa7a8003fd63480017eb18a202bfd892100df8c0a0813ff4255009fe21aa827ff0c241027fe82a10037d5354891be2a2a636ff10351007fec0a8802ff644c4037e306a847ff989530e7f863108037f54548077fb1a6205ff98910017fe84a10027f65484117f3
  | 2 => 0x3013ffc412080efe6350411fe29aa000ff54621015fcc3108237c52144017fb028202ffc8621007fea49800fff324c423fe29a801bff14221047f8a5aa00afe6214405ff90ea403ff0c53200ffe80a8003fe5154001dea1a8012ff0855001df8c6a809ffc209043bfe3244204ff55141047f8a8a880b7c52d4803ffa028008ff19051007fa8298137fc625503dfe2826208ffd495100ff8a090003fe5150013fe1962000ff5954100ff0a0a8012ff6555011bfaa6a008bf99530007fecb88002fd62c4001ffb2a8400bf185321cffe85a8803fd3250001ff32a2004ff9014112ffe42a08137e5455007ff982a608ffd8b53047dea4a909bfc63504017fb22a400bf185431f7f860a90237f53d4017ff3262032ff8c251047f8a5a9823fd63d5001feaa24000bfd8d54007fec29900afe62544017eb1ea408ff15152007fac890803fe414409bff192a832df9425101ff860a9807fe50440013e32a2000bf59110047fac7a8003dd314c001feb02a808f7d4d53027fa84a0823fc62d4c01ff30a6002fb14a210cff8a690823ff54548017fb2a4202bf98b53047f8c1a8802fd65c4011ffa9aa416ff90f50046fea228803ff6244011fe326a400ff55221047f8a8a980ffe324c001fea1a4240ffd0d521fffcc6a9003fd548c4017fb02a641ff90352047fec1a9006fe6050411ffaa2a600bfd893013ffcc12080afe62d50117f32a6200ff14530007faa89880bf421484017eb148206ffcc510007fc4298002ff6150845ff90c6203ff8c53001ffa62980afff2114405fe9924201ff8c140047faa228803fc6150001fea8a6202ff8c94200ffc60a8012fe648842bff216a003ff14d43007f8c2aa00ffe5354c07ffa1aa608ff14354007faa318812fe64d4001ff28a4204ffd0143097f884a8003ff654c403fe086a003ffd4d5300ffa6090003fd4394401feb02a202fb1492004ff8a588003be4150435ffa024202ffc8520005fec29000bfd4288405ff996a44effcc154047f8c5a8003fd4214403ff086a004ff10940005dec4a8803fd5148035ff2a24208ff1435301df8c69080ffc534c801ffb2c8210ff08540047fcc7a8803dd434c8057f3128235ffd0251137fe64a0803fd424c491fe20aa602fbc862100ffe6098023ff51d40037eb062008ff14e51017fa8490007dc304c001feb1a824cff0c1541d7f8c09900ffe3050c27fe31aa000bf59351007fec4aa003ff63508097e322a403fdcc6311d7fcc0990c3ff3054455ff200a202fbc8142007fec918813ff5455009ffa1aa81bff90221025fcc918806ff62480117f32c6214ff95150007faa58800fff328c443ff2046200bf58f51027fca8a0013fc54550017eb26a403bf18e51007fac11887bfe404c4077e31c4201ff0c130005fac3a80f7ff305085dfe182a201bf982310aff865a800
  | 3 => 0xe1944232df14251007fec49800ffc324c401ffb1aa001ffd4310047fac9a991ffc6254c57fe190a203ff0ca31027fc87aa003fd6588409ffaa28403ff50d3200df8c099097fc5250401fe9948213ff0c550047fec7a9133fe2055013ff296203aff94132015fac51080bfb20480017eb06a602df94b521c7fe61a880ffe43d4c05fe296a403bf18c51047fcc028807fc204c003fb0862003bf98f52067fcc69000bfc3248001ffb222000ff59310257fc85a985fff41d4007f7992642eff08151005fac89080fff314c811ffaa6a204ff90b54005fac910847fc3150071fe21ea21bff10221017fe40a9003ff6350411fe326a600f718d1001dfccba993ffc10d5001fea928209ff18b101b7f861a8803ff61508077e31a8400ff5511013ffc612080bfc2050801dfb222001bfd8140007fac6a8023fe52d443dfe2026200bf58221007dec4a8823fc54d4411ff316a208ff14352147f8432080bff52548017f308a201ff1012000ffa6088043fc6250093fe086a601ff88130027f8852081bfc63440037e300a200df55251007faa28811fff2054c0bff90a2000bf58754007fac099007fd5050073ffa0ea200bf58e51005fac5a893ffe10d5073ffa1ea208ff18b5100ff080a00bffe3254411feaa0a202bf98b50047f8a0288b3ff3214451fe3148228ffc8241007ec828805fff42d40097e3246202fb10942007fa848800bee42884057e3146200fec4110047fca7a88bbfe20544017eb2a8404ff95241007fec910823ff64d4411ffa9ea249ff8435301fb862a185bfc43d4001bf28aa22bdf94851007fa8518803ff60548037f3044221ff14231017d842a102bfe43c40077e31e2024ff1414105ff8c988002fd658c4013fb2a2002ff88142007faa6a0812fe644c405f7212401fff14931017f8a510867fc3148411fe290a200ff5493101ff862a188bfc528c401fe32a823cff0c142017ee431080bff5250807fb98a6239ff1075100df8c09080bfe3254811ffb26a000bf1854001ff865a9803fd3254005fea924008fd5445104ffc85881237e5454c01fe90a8000ff5953100ffc8088002fc6154c01be32a641eff98131007fecb108077e5054005fea944202ff14920005fec498807fc10c40097f322a201bfd8d30027f881aa023fd5214401ff30aa803f714d4300ffe4098003fd528c401fea9a404dffc815401ffc64a9803fd5150401fe90aa000bfd8951007faa71080bfc214c8077f31e2000ff50d50007fec090813bf4050c097f322a434ff0c6511fffca6a9023fd5314401ffa8e2000ff58a4100dfcc1a9023fe52d4005ff9028401ff1031017ffe40a8806fe6048401ffb224206ffcc9100fffe4298823fd60d4401feb024204bf19121025fcc890822fc658c407fea9c6201ff8431001ffaa698823fd54d4809fea1a8000bfd95
  | 4 => 0x8bfe628c48ffe10aa608ffd8b5101dfcc68810bfe43d4807fe9926004bf99110005feca88003fe6150c83fe206a400ff58954007fa63a8007fc40440013e32a8400ff50a51005fec690113fc6050c05ff2924002ff90b52027fe80a1002fd6414403ffa824031ff99151004f8ca99003fd6550801feb1a4200df54f52006faa6a8003ff6394455ff080a204ff90d41247fca8a980bff214c8097f322a004ff9054000ffca0a8002ff6154007ef992864bffd0b53047fec8288077c5054001fe992a204ff90941127f820a0813fc43d5011ffaa6a008dfd5051005fac918823fe64d4883fe086a408ff18352267fc60aa007ff30d4027ff98aa032ff902511bffe41a8807de304c0077f30c6208ffd835400ff04090027fe62c4005ff9924200ff1953201ffe64a18abfc1014403ff2828002ff50932007fec2a180ffc43d4c05fe102a44cff0815410ff82118813fc425500177b122008dfd4c5101fbc8718822fc6588403ff1826000bfd8d5010ff88118803fd6050c01ffb22a411ffcc54005ffe8388137fc21550057e312801eff0413100ff861a8023ff52d44017fb024200ff18520077f884980a7fe6390483ff086a41cff98e21047fac3a911bfc2054c75ff202640fff951301a7fe6528817fc5244011feb16a62cff90c5101ffc87188bffc4254439ff21c4229ff14e41047f8a9a8093fe105041bff3224003ffcc543007fea2a085fff43d4001feb0a6400ffd8951047fea7a8002fd6014401ff20a421bff84221007feca98023fe52d5079ff1828403ff90d3100dfac1a8002fd654c01dfe10a6002ff10942006faa8a8067ff31484017fb0a642bff90851017f865a9033fe434805ffe10aa204ff95154017fc85108cf7c5294417ffa162004ff50e41007fccb10803fd654c845ff2146200bf58910047fca7a8003fd5244065fe304a21bff04221047fca5a9822fc65c4005ff9926400bfd89410fffc84988137c54d5015fe21e2002ff8815212ff864a08a3fe6290481fe322a400ff995300077a8720802ff6448489ff2828602ff909200177884a1022fc6544011fe30ea800bfd8b100c7fca0908037d5154063ff2a2a202ff08542007fecaa0803fd534406fff196a208ff98752007fec690813fe5450811be2a6a63eff9815200ff82090013ff4090443ff0846217ff10750007fca32080afc6214411ffa88a203df14d5312ff8c4a0803ff51884017eb146200ffd4631005fec899023fc63d4801ffb026400ffd9310237fc40a9813fc40504077e31a4001ff1411028efca7aa00afc624c001ffa8a402fff98951006faa728803ff514c4017fb224001ff8412001dfcc6a1003ff615403dff082623fffcc15200fe82188053fe6454041fe3226201bf981320277ca8a100afe62440077f31c8234ffcc651197fca12880afe6290405f
  | 5 => 0x435000ffaa0980a7ff3190401bfa8aa046ff10153017fe85a9023fe54d4407fea9a6400ffd8143005fac898003fe654c87bfe18a8440ffd0152007faa69093ffc30d5009ffa128204ff15354047f8a9a9823fc53548017eb1a4209ff8cb10087fe42a0006fc604c4017fb026412ffc8550007faca98022fe65440117f32c8242ff10f52027faa8a0006fc6094401ff10e2003ff0c35301ff886a1803ff6294401fea94a200ff14710007faa2a8003fe31c40057e3128602ff14932005fac898823ff54d4c017fb22a208ff583540c7f8a090913fc5050c03fea026000ff4c71001ff8a6a9877ff4188401fea12a008ff58851005fec2a9813fc4250c47ffa0c6204ffd0f54047f8a1288b7ff4114499fe302a804ff10d41005fecb18823ff61d5003fe9062000ff5454001fbca7a9802fc614c0097fb228208ff94f54037fc8688003fd5394401feb0a8648ffd0153005fac9a8143fc32d5011ffb1ea220ffd0531047fcc82880efc6354807ff29ea604efd0f5422ff842a1803dd534c807ffa1ea601bf9814306ffe8290023fd53d4809fea128001ffc8350017faa499007ff30c4011ff326a60eff189301b7f841a8823fe63d4005ff296a401bfd9550007facaa1802ff62440037f306a200ff59152027f883aa017fe4244001feb2a4208ffd4b5001ffc60a980eff614c401fea0ea001ff9015011ffe851880bff4248011feb06a44edf14d54017d8649900bff4288411ffb16a801ff0411001ff886988b7ff4214441ffa126202ff109520fff8c498803dd434c001ffb02a600bfd8d2103ff8c88812ffc41d4c09feaa28600ff55121005fac690007fe40500017fb226000ff54521007fecaa1807fc30c4039fe21c4245ffc854301ffa86980ebfc504c859fe218a20dff1912001ff88718803fd214c07dff182a408ff58b501effcc6a102ffc54c4011bfaa6a402fb94b52207fcc8a900bff2148401ffa8a2040ff1055200ffc208804fff3254001bfa8ca200ffd5310046fea7a9023fd64d4401fe30aa608ff14d5400f7c80a0023fd61d4c6dff106a229ff0c641007fa86a8833fc4348009ffa0ea802bf98930007fac098803ff6388401de3222003ff14d30007fca298013ff42d5009fea1a8408bf9971005ffe8788003fd5494409ffa02a82eff8c151017f842a904b7c5254001ffa9e2011ffcc940007fec6a0003fe6550c05fea12420aff94f10047f8a3a80f7fc535088ffe212a604ff90143007fec5188abfc401440bfe1922000ff8c750007fac6a0023fc5354411feb1ea218ff9012100ffe8098057fe32d4001feb0a8433ffc8651047f6a0a8003fe5154407ef21ea600ef50d4225ffe83a9803fe21d4011ff290a222ff94a3105ff88388003fd544c801ff20aa002ff94a2118ffe80a8803fd6548081ff2a2a41fff949311eff8c6a1
  | 6 => 0x1ef18a6218ff84121227fc20a180ffe314c4a1ff906a804ff50a41047f8c5aa007bc4050065fe084a201ff8831001ffc649881fff4144025bf292a000ff4c520027ee82a08bbfe5054475fe0826424ff0c141005fec2aa00bfe2148011fe2a6a402ff8c920017f86490803fc514c401fe98c4200ff99541047f8a7a88c3ff3154401ffb226000ff58930047fec7a800ffc3250c11ff2a6a004ff90241027fea8a0802ff6444079ff2828400ff145201fff862a9003fe314806bfe324a204bf19351027f8a8a08137e54d50017fb2a863dffcc542047fea828803ff6390411ff30ea639ffd0351197fc212890fff43d4801ffb226200bf5952101db8c68800aff61484017eb2a8200afd9110077fcc498012fd64d5031fe202421cffcc221047fea7a900efc63d5011feb16a203bf18d5401ffe6118843fc52500077e31a8204ff10143007fea91080ffc3154c07ff9826200fd8c710007fea6a080efc63d444dff29a822aff0c05103ffe84880cffc329444fdf2048203bf18d1001fb86118803fd52540017fb2a6204cf95354007ea638812f7e54d4c87fe20ea404bf19130007f8ca9000ffc308c403ff9824003bf98c51005facb28803ff60944a1ff196a800ff4cb5101ffca6988ebfe104c829fe322a006ff10d1014ffe6520803fd5250001ffb2a4008bf195320dff86110803ef5288401feb02a600ff54d5000ff841a800fff438c475fe2026408ff150510eff8a910822fe6550c03fe282a004ff1054101ffea698803fd6344047fe2a46200bfd8530047fec9a9003fd644c807fe1826204ff90354045f8caa10d3fe6394465fe204a208ff1835400ffe4188012fc6454c01f7a924001ff0c1200e7fca710883fc544c401ffaa46202ff0c932007fccb20837fc5448007ffa9c6200ffd4b10047fcc9a8003fd535005bffa18a204ef10541047fac5aa00ffe32d4c03fa0822000bfd9231047fca628877ff4388401ffaa26200ff5912000dfec8a00dffc42d4401ffa9c4204bf19352005fec6a8887fc608c411ffa98a208bf99520007fea890007fc5050007ff29c6203ffd0d3106ffe86900b7fc41144037e3028600bf58231017f8a490803ff6355001fea0e2025ff949410dff8c11080bf72148487ffa0ea445ff14943277f862aa007ff504400bff292200cff94d20005fcc3aa006fe60550037e302a804bf1915101efca7a980ffc314c001ffa9a4002fb8ca2100fec2088002fd654c801be32a8403d794f5301ffe61a9927fc40d4c07ee29aa61dff1062111ff883188dffc21d44117e32a6001ff88350237fc80a9813ff4150441fe20a6233df94a51005fec2a18c3fc3154405fea924202bfd893213ffca120803fd43548117e32a6208ff14a51007faa8a8023fd61d4007fea9a8600ffd8f10005fec6a000bee324801bfe20a4001fe9
  | 7 => 0x18803fd21d4011ff286a802ffc835209ffc86a8023fe60d4c6dff186a209ff10b10017fe84990effe644c8017f30ea408ff183530077aa8a100afc6250403bf286a000bfd9541007fa849800efe6394403ff1024000fb1891011ffcc918803ff614c0017fb22a01cff18e21017fca490897ff2050425fe312a000ff98553097fc84a8003fd5290403ff9822021ff98231007fa87a8003fd4254405ee1926404ff90d40005facaa180bfe32d48a3ff986a84fff08354047fea32880efc63d4811ff310a208bf99532027fc80aa0e3fc31d4407fe21a6409ff08710007fec2a980bff2088401ffa928200ff1954200ff820a8023ff61d4c99ff282a803bf18f50007fecaa00fffc6354811ff316a800bf18552007faa720893fe6050403ff2026000ff4cb50047f8a7a8013fe4250067ff294a200ffd8d51047fca3a8003fd6388403ff082a001ff0c1101fffe62a9007ff40d4093fe106a60bff95310025f8c9a8003fd62c4015ff31e202eff9015100ff820a0002ff6488411fba8ca200bfd8d4103ff8a88809ffc5090467fe314a246ff941530cffc8690823fe62d4c8bff3128608ffd4550007fea88800fff324c09dff992a800ff1953015ffe4028803ff515008bfe3128604ff90142007fcc29900bfe524c811feb06a622ffc823100ffc20a000afe65d4863fe322a208df14f5401ffe62a980afc62d4c05f61044200ff8c621005faca9893ffe20d5001feb226000bf58f5403ffe8688006fe604c401ffa926225ff8c941005fcc3a807fff204c407ff21a8600ffd4d10025f8c910823fe60d440dff29a2000df55152017fea510807ff2048061ff992a208ff98b50007facb88023ff5214401feb128600bfd9621097f864a8012fc6454023fe31a8000ff98550006fea72880afd62d4849fe3028249ff88353007fa8310802ff61548097e320a200ff5053100fd8409007ffe624c401fea0c6200f7d8d10047fca7a900bff3250809fa20a8201ff8c350007f8a2a0802ff6050c05ffa924010ff0c940017fc849080efd63d4c07df21a8607ff10510007fec098802fd63c4011ffaa6a400ffd915100ff880a8013fd5490403fe1062004ff909430c7f820908a3ff2190437f71044201bf99750007fa8290012fe6454c59ff980a244ff0414301ffc869900bfe424c869ff21ca200ff14621047f8a4a810bff30d4801fe30a6000ffd9150007fc82980037c6548401ffb046200bfd9153007fec68800fdf314c02bfe10ea015ff10b5000ff880a0013ff4350401fe32a8603f790d32137fe60a0807ff1044011feb18a202fbc8352006feca99003fd5190483fe186a44affc8353007f8a31893bff3155007ff98a6008bf1954101fbe60988affe3214405ff1944201fb8812019ffc8528803f541c4007ff1946200ffd4521007fa87a8807fe504c00
  | 8 => 0xf1971013ff82120813bc4150c07fe29ea60eff14930027f882a1803f63144011feb0ea808ff149511affe87288affc2114411ffb18a24bffd0353015f8c5a8813bf4150069ff29ca203ff0c132007fec498853ff4254011ffa9ca200ff55152007fcc2a1003fd5254401feb0aa400ff58141007ea62880a3fc3290401feb1aa244ff98143017f841a9077fe5488447ff2a46200ff5515302ff8c488003ed2148007fd9826000bf59353007faa498003ff519043ffe10a6202fb1495201fbca69909ffe1090405fe2928400ffd5132007f8ca90813ff42500077f31c4202bb18951017f84290007ff20440077f31ea201bf18152004feca99023fc601441bff2a24003ff94d321aff88328823fe50d4407ffa1a6420ff99131007fea488003fd21c4049fe1028200ff50f1001dfec8a1883fe544c4097e3262008ff14154005f8c29000fff534c807fea9a6038ffcc751027fe82a191fff2154c6bffa0ca200ff1855000ff0609804ffe635402dfe18ea004bf99130007fea518807fc504c0097e326a600ff54d51007fec520802ff65500057e312a004bf993520d7fe8290803ed3288401ffb2a6400ff1954001dfcc6a8803fd62540057fb228421ff08231077fe429802bfc53c40017fb1aa400bf58f5012ffcc4a093ffe30d5003ffa062000ff99540017fc41a900bec21d4877fe20a6408ff1415100dfcc388003fe61500037e306a400ff54d42027f88120803fe51c407dff202a401bf98354004f8ca90806fc6050801fea0a2000ffd8554097fca4a8003fd6354811feb26a403ff8c35300ffea0a8123fc6454c01ffb0aa402ff082210effcc910803fd6355055fe100a224ff88141257f843a98f3fc50508037fb0a204aff10b53007fcca98812fc64944a1fe10ea823ff19231027fe84a1803ed3248007ee21a8604ef10241005fac899043fe5250005ffa124204bf1911000ffea0a00037f5454077fe3226400bf58752007fac4a8823fc61d4c3dfe1026204bf99120007fa6588013fe54d50077e31a8000bf18542015f8c5a808bfc628c4117f32c4204af19110057f8c78813bfc6355033fe21a4211ff98d4001f3886a1807fc20480097f3262004bf9935102ffc6488003fd544c005ff992a404efd0943005facb1080fdf3254c77ffa0a6408ffd875210ffc41188d7ff429443dff1026204bf1913101f7886a1803fd6254c077f31a4008ff18750007fc428803ffc644c001ffb0a4008ffd8353007fc6288003fc5144001feaa2a200bfd8953005fecb880037f5354005be292a400ff4c510047fcc7aa023fe54d4c8bff2928601bf98051017fe42a100fff3254c01feb22a234ff10e51007faca8800efe63d5003fe9022002ff88221007faa2980abfe2014411fe29ea832ff98251047fcc1aa007fe30c4009feaa2842fffc8551007fccb
  | 9 => 0x421ff3128000ff99710017fc84a1003dd438c4097fb0a8200ff5915007ffcc89800ffc31d4c03fe0826001ff0c15003ffca888003ff6448005ff902642fff90951005fac5a980ffd438c411feaa6a208df14b50007fa86288ab7e5014401feb128003ff8c943047f8a8a8012fe644c803fe182802eff04151007fea2980037f6548409fe21a804cff8415401ff8a718803fe31484097f320a208ff94451007fec120803ff6254061ff31aa213ff94d50017fea499003fd4388429ffa1aa0009fd9542047fea2a8823fc6314401fea1a4001ff84130006f8ca88003fd3148405bf292a408ffd87501e7f820a10dfff21d4449ff1828203ff50d310177c84a1003fd6444001feb24423cff18142007fa64a080afc624c409ffa1a8008ff18f5119ffc6528813ff5450011ffa9aa028ff94a41017fa4290073fc5388401ff20ea000fb1895126ff864aa022fc6590407ef9828646ff98153006faa7a8002fd63904057fb128419ffcc12111ffe81188bffc3254407fe1926000ffd4d40007fa85a8803fd60884077f31aa83cff8414200ff42188003fe5188419fe29a4003ff14d310effe8110847fe5350003ff286a002ff10b52007fa6428806fe6094401ff28a6202f78c932007fac6a1003fe6154805f79024201df143500a7f882a8003fc6590401ff28a4001ff08110005fac688083ff404c409dfa1a8028ff14a4101dfcc6a8013fc4055011ff306a416ffcc750057f86388013fc4050831fe1824204ff1054001ff860a1807ff40480017eb2a4036ff90351017fc649900afc62544117f32a8008bf1954000ffaa188013fc4250409ffa0a8002ff0c94200ff8809800bfd32884037f3028400ff54d52015fcc4aa00bfc21d485dfe202a204fed01400dffcc110802fc6154007fe9946200ffd81410d7f8a890813fc5450c037f302a200bfd9310047fca9a9003fd61550037f302a619ff98d21007facb18803bf5450c07fe9926200bfd8e21007ea8288013df4350c11fe282a426ff98d4112ff842a080fff4350c01ffaa24202ff4c920015fcc518803df5350c01ffb0a8000dfd5251027fea8a1806ff6054009de2a28621f78c2311c7fe65a8807fe2044001ffb22a602bfd9552027fc8720813fe4290411fe282a600bf58352007fea690813fc42d5065fe184a203ff8c1310d7fe869080ffe308c429ffa0aa001ff503100dffc611080bfc4288407ff29a8600bf5931001ffea6a1813fe5450433ff29a4200df55350015fcc4a980fff304c8077e31aa202ff10920047f8a928803fc658c43ffe2126203bf98d400277ca9aa04bfe6254027fe21aa01aff10521047f8a4aa003fd6454c057e3162002fbc8132117f88518807fe3048005ff90aa408ffd525119ffcc5288037d51d4001ffb162000fb88521045f8caa180afe6250c45fe10c6200f
  | 10 => 0xd00280000102280700000480a80200300002200000200106f0028cc00500100000580201281e80100180600280500080302604000100080881300480100680700286b80402280780580500380b85280000780780200580080200102880000000000300600701b80201680000580280480188906301081f80200300000700a00100000000b80400000081480080000b02881d80600a80480180000101b8050000008830020010be00800000000a00c01880080008c82c04a00480301400c8000070c600280600000000a80100682500480102880080480180800300000080d80c00300201b80480300181780300000880080781a0a000002e01d00300201607200180580804900a80300180f00c80000b800059840804b6e06700380e00000000000000b81300000b80000186f80200000300000101b00000100080001280a8048000010070000040068070ee05680080080a00480400601d80280a81381300002d00000080122200700000200280a0070098068a480f02130f00380000000d8019e287a0108030000038f780584c800013000800007b1d8358118000010cd03900000081780000200500e80a00080301584680280000200100b80003100000480c0818eb80180000a82500e14a80080180000581080500180501100780000200200284000000000402380583780501281401800d80180480000280001600c81000280b802000aa80078050410c200180000102e80080080107f80700006180000380a0368950000230008000968c600989684380000080000180683d81980000d80080b8000328078018ca0bb00000280180280080180600180580300a80500081380000000000a81186e00582e0000b801580788900300180500100700301c08980000200101901100180200f80c04900380680c0070008348040018000000078050de87a0170018000e280081102e80900100000181a80180d80b80004e01b80500c80a80000503580000080e80200380000300c80400481780081a0f100000380000200380085387300000180380580a80680380900380000902780680000f00000000400e00080f80000080208a0a400080280780380000000000280000980000600080380000400200000281601b0000b880881480200000680680000001401d80100e00005180182380c01f8160010038090420020078060048000b580000d00087b0020001bb00c8290002a700700c800006800800002002fd6214411ffb00a200bfd8540017faa4a1013ff40d50097e3224008ff18851187fc86a8803fd628c4117e32a4204ffd0141027de84a1017fc2144001ff28a8216ffccb5015ff88428806ff6044011ffa94a20cff18d20267f820aa002fd60d44057f3162004ff90d4200ffe60a0002ff605501dff2126026ff14d41007fcc290003fd6494
  | 11 => 0x5f00600100080080191680200580080a8000000018078018180010020098008008a480008000280300400f80a00780000380600280680800200400003a8308010070000008060010098038008081b78140008000308b280380000800300f80000080c80280080080380000000003a0fd803b5a03601f81000000100000000281000082280f8009780010710790000050030d888e00b80183880280000a00000880000000481000380000c00680600082c00e80280080083980f87d82100100100583900281081100001300b80100400000902002280000180580280000280180480c0ee80680c00380003200280000500000180000280200000100100000400280000200d80000000700480180c00500001180f00000100507d80b9508438e080000201901980380880780400000000c8018068050110000f180200080380000080380300280500280788280000000689c00101380000100400580000280080400301c80000a85400185380000d000805003000001beb80000600500008700580100583d00100001f00c80402980100c80901880280088000600082ca860a3022001800a6780100880014b80482
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7458d200467c7119542007f231c4110004df73595100075f6550d32006dc64d8d102ccff7650710185f57199531014fc7259541007cf634c920005f77150a31006df43d8d200467c65d4910004fd70d8e21006bf644851013dbe7050e4101cdc7359120004fc7694520044fc7648750006bd72d9110004fd76d454000efa76c4110014fc75d8950044fc76d4d211debc644c910004fd73d96210067c60d9521004fd75d8543044fe75d8f101567f101951000cfe7058f51007b76450710004ff725824100cfd75d9150006bf7459542105bc745813126eee62d8954004fd73185420057d74d46510067f65995310067c64d9532006ef624c91023eec42d89531a6de4358e5118e7d5459641014fc7218540046df7358f50026f57690710014fc721854315d7e7254c5100cfc7654d50006f671d9710016ec624c910044fd73d815303f3e54d511001cfc73d9530006df4358f50044fe75d8d4115f6c5219621004fd7654a31006dd63d4e21004fd74d85502c6f710d85300067f5458251005bd7090541044fc764c75017cfd76d4621046ef5258b53044fc7559132024fe7458251004ff7650f1000cfc7059631004ff755823101dde7394631285bf745954210fd4308c7100457c7550b511fede63d8d52044fe75d89300067c7559110004fe71d814200dec704c9200057f754c9410deed71d8910007b54390510017e76188521004ff7058d212b4fe71d931014f9c43985430feee32d8931006f671d8e21015ee7290621166dc3158c51005df735053100cfe76d8142006ef72587530057d73d465101cfc73d8141044fc76d452049e7c31d953241edc31d85430457c7550a511967f70d95100067e4019521006bd65d9110006f610d8552044fe75185200067d655512001edc634c9100467e741952115e6c2119521006bf64551300067d75d8543004bf7459510006bf74589100467c65145210deee70d8910005f970947100075d534ca51006df21d8d1000cfe76d81210467c6554e210079d6450e3117fe721546211beef2158b5135ebc6550e410967e5259520006ef725911000cfe765051001cfd76146310067d6594531004fd73d81540cede63d8d210067c7559120044fc7559130006bd4358a410067c65d812141ebd74d854300df8705451026eec21d895406ebf4359120046ef5258b50006ec41d8951004fe71d9540006ef73d89100067e54d9520014fd70d9120014fe7258f54006be40d91214967f72d9532006ee73d895101cff7658f10004fd764c851004fd73d8142044fe768c7502cef710d854000cfe70587532e6ef65d492023f6f2054f52004ff7059521024fc7558754005df7454d3200cfe70d95411eedc30d8d42044fe75d8d40007e7624c510024fe74d8132006de30d8d51005dd73905300067f655814200cfc7058f54
  | 1 => 0x495026eec62551101957e70d5251014fd71d8d211967c60945510976c525895011ebc4159231006ed54d89100067e53d95200067f73d952124ddf7359530177f010545102ccff715911001fd7714c5300467c6355051024ef7650a21007f370505100076f65189100467d7419510136bf43592310076f65d891001cfc7318540004ff7058a41004ff7650930006cc63d89100067d6554d20004ff7359521096ec6258950166f5311855301cfc735822125f9e74d4d4319e7c20d95210073f6519110004ff7158b5301e5c6354d50014fd74185420067e43d9510005f771591200067f71d954201cfe73d9621016ec6254950024fe74d8951006cc63189103e7e751d8951276dc63551100069c6418d1001cfc7359510006bf645515212dec725954104eef21d8b10006ef7258b10024bc7458d10004fc7688550006bf6454510004fe76545401fded7299532026bc649053001cff70d9130206bf4358b54004fd7650a5109edc6358d500067e54d951000cfd71d89100467c701952101cfe735805100cfc70d8d51004fd74185302c4ff7158d1028ebf43d91530467e651962101dde73d51321567c2019510004fd72d9310014fe76d89540057d73d45500457c75509500075f6518d10004fe7654d21004fd75d89414f6bc54d9543026bc6450d21004ff735912101cfc73d8954014fe759875213ebf20d91100476c5254a51016ec62509314be7e211954200cfe70d8910044fc764cb504ce7d21d954211ebc41d8d41014fc72580510057f7558121004fd72d8d50004fd72d8d51044ff76595420067e6319542026f4645051000cff768871008ddc7358940004ff7359540007f241c4110004bd74d962101cfc73d85420057f73551522fdef7258d200057d754c5500067f6558d210075d534c9504867f2019532004ff7655120024fe7418530304ff7358d20006de32d8d400269e6450e31004fe764c910026bc6490550015ee72d452101ddc735823100c7c765455000cfc75587500467e6514541004ff7650f500067f6559132036dc32d8d10004ff7058e41004fd70d8552024fd70d854000cfe70d8d2126d7d74d5152024fe74d852022eee32d89430d6ed4258a410467c6554d42005ef734852042ef641d85420057c75485301547e76d455019e7f52d95210457c72d4d500f5f5738c5100447c75591210467d741954201cfc73582510057d74d4550004fd72d913013ebc40d9310014fe725913100cfd75d895001e7e6354f500467e6519641004ff725875000774654c510007af6450920006f970d93100467f62d4d520057f754871000cfd71d911010edc10d8d10014fe72d92310fcfd764c52101cfe73587520067e5259641266fa50d8154004ff7458b530c7f01048510005de71d4d43007eb70509200067f6599641007eb704852006db
  | 2 => 0x1cfc7318520046f751587531fedc30d8d52006be40d9132234ff7059530266f86058154046bc5459353005f7715525110edc3058231004fd75d81310279f7350e41004fe7650d52004ff7458f52014fc7558f5215d7c7254c51006df6350d51475ef72591320f6fa30d813101cfe73d931010edc608c5310079f5450d32006be40d91313fdf77158d21004fd72d815101cfe7398750106bc644c510024be74d96210f6f7604c51001cfe7359120005f57390510004fd75d813202eee32d8910004fe71d813200d7e7054750004fc7650a510467f505935323d7d73d4d520467c529875206fac6450920014fc72d8d510057f7558132005f47158d200067e50d954200d7e70d51501567d751855000cfc7158f10006bd6450f51005bd74d8a513e6ec50d8951006ee10d8951006df7359130005bd74d8a310067c74d953212cff72591210067e525805101cfe73d9152206bc645915213ebe10d91100476c5254950004fd72d9510024ff7659132006ef624c510004fd75d8930124fd74d9310004ff7358251004ff7650530044fe76d95411a6de5358e5122eee62d8943004fd74d895326dec7258d5400cfd72d85200473f6455352004ff76509310067d54580510feec624c5104e79c4319543027b67190541044fd71d895101fd6718c531006bf7459130276dc5359543004fe76d4910006bf7459541004ff7458b50024fe74d8d5219e7d32d952105f3e54d53100067e10195320467c65d4d41004fd76d4530014fe7258e51006ee74d8910024fe7459521007b54390710005ef725954349e7c30d9532024fc7458353004ff768c750004fc765512036ebd40d91300066c6588521006dc614c530004fe76545200067d6554e41004fd74d8151005f47154e51006bc63d911000cfe7058b530467c5359353046ef5258851004ff7359541024fe74d95100067f76544510465d731953201cfc76505310467e7319521014fe7258d10004fd7654e41004fd7688550005bf74585500e6dc3158e21044fc76d4931004ff755913006dbc745852011f9c4150e310467c65d52210067d651953001edc634c51013ebe50d91100057d73d525110fd771d8d103779c43d8143005ef7255221024fe74d8d2101cfe73185400067f41d95100467e76d45504cf6c21d9542006ef6250931006ee43d895115e7f32195210379c4350d1001ef6634c710006ac64d891017eec5259621024fc74d85530057f7550951006df6354d40015dc7250d32136df31d8d41004ff7558a4111ebc4259231006ef41d89513e6ef65d4a21006ee54d8951006ac6418910006df7359531025be7488540006bf6450710026bc6455110046f751587540067c654c91002eee52d8910006dd64d8d10006bc73d911009ede63d8d500057d75d8a414ce7f20d954217e7d525962100df8705
  | 3 => 0xc7259540006ec6148520044fc755931017cfd769962121def725954201cdc7358910006ef72595420deed40d89100467f505935103ebe71d911022fcc2150d32004fd72d96310067d65d5120004fd76552314eedf32d9543106bc645913100cfc70d8d5222eec21591320057f7154c51044fc71592510067c654c510007e761485200467e655523100cff74d9540046df5358f5235ebc6550d401867f5359631016ef604852000cfe7059121004fd70d9531044ff76d51100067f6514540005dd73d8a41004fe7654e2101cfd7158f10014fe72185430467d73195210467c6554d40015ee728c520004ff7655132006ee53d895100cfc70d8941004ff7458231006f42118540184fd76996310467f7019510044fe75d89431df3e54d5132004ff7258051044fc7650750004fc765491029ef531d85304d67c41d9542004fe76885400579c4350f10256ee3258b53024be76d91101acfe761954103ebc42d9110024ff765923119e7c72d95210dcee7618910024fe74d8910004fe764cb1002eee71d89100067f65d4d410c6ec7648520044ff76d4b1000dee704852014dde73196411557e76d4550026be64d5221006ef72595410066c65d8910017cf734c920006ed53d89100467f7219532005dd73995103467f52d95204867c4219532004fe7654930005bf745893000d7c765455026f3f425515218ebf43d915101e7c6354c51156f5101855023eec6254d10027bb60505400067e53d951001cfc73d8152246bc6454d10004fe768c550014fd71d8121044fe75d85320076c754c920014fc72d85302b6be401854003ebf43d9110004fd73d91100067f6555121004fc7654530004fd72d915048e7f43195320066c65189100467f71195100063c6519110004fd72d8550044fc7614710005ef72545100057d73d5150004fd75d9221046fb505835113ebc50d9110014ee76d8910004ff765494001cfe73589100067d6519532014fc72d9520007747155251005df7358550014ff70d91200067c4119532274ff735954300cfd7418540004fd73d9540014fe7218540014fc7218554006f4715912000cfe70d85320157e725515200cfe70d9631024de76d4d430067e10d95420467c6555110004fc715835400cfd74d894000cfc76d4510016ec62d4b10024fc74d8d500067c755913201ef6638c51001edc6354d100057f7558542004fd70d91511957e7619510006fb7058d20024fe74583510067d6519542004fd74d8930004fd7318520014fe7218550005ef7259151024fd75593500065c6518d10004fc764c951005bd74d9621014fe7218553006f77159531004fd74987520375e53d4d10004fd7650f524867d2119532014fe72d8d5400cfe70d89510457c754c9510deee205822112eef21d8941027af6250d4201cde76d8d1000dde7050d30
  | 4 => 0x9521024fc7158a4101cfd7558f50114fd72d8d211967f10d9510004fd70d9621014ff73d9132015ef7450a210067c2119510196f5109875001edc634c710004fd75185400057f7454c510067f6514530004fd70d8d51004ff765523113cfd70d91100057f7454451006bd64552510575e53d4f10004fd71d895019eec6294510044fc76d4530004fe71d91501ddbe74985320267c64551520477b60d4d50006bc7458d200067c52d95411af3f43d52512e5ec75509201cebc40593510467c6554d10004fe761452001cfe76d8d50006bf6450d500057d7590550014fe71d89101eddc73581420067e6419521006ef62d4510044fe75d8940004ff7358352044fc7558d10006f421d8530116df32d8d21044fd74d89540467c65d4f10015ee75d4a21014fc725931001edf6050d3042df77158941006be75d9110025dc74d4d4300cfa76c411015e7d2119521005ef714c920005f47155151116ec6258a31006ef629451001cfe73d92210467c65945400447e76d95101beec62d4510004fe76d4e21046f85058354007db63c41101cebc64d451009df97099530004fd73d8950395fb7058940014fc72d963100d7c7054550006df42d8d1006ebe64d912012eee62d8941015ee72945200067d65145412767e635515211ebe545923118e7f54596410467f5058f5100cfc70d8d41326bd40d91200467c6554521046f671987521aebc64945100047f7558d20004fd72d8543007cd534c9200457c7550b50004fd70d8954005f573907100467e65195310067f654c5211c6dc63d45100067c5459621016ec624cb100057d754c750004fd76d49400067c65d913201ebc6350e41044ff7659710014fd75d8d5201dde73d51310067d73d9542024fc74d81214c67c43195420079f6450d30024fe74d8930044ff76d5130296ed7218520014fe72d85300457e7550d500067d6519520005bd74d4d41046be5458b542179c4350f52024fe745951009f5c6354d5001cfc731854201ddf7450d32004fc764855023dec725915319e7e32d952101cfe76d8d41004fd764cb50015ec72d4d20024fc745835101cfd76906311adbe74d8a510067d5358051044fe75d9121004ff764c9510aeec2158b5001cfe7359350006ef31d89100067d659464110edf30d8d1012eec62589411a6dc6394510004ff7058b5135edc6550d32024fc7158241026bf6050d40004ff7259631044ff76d4e410075d534cb50006f421d85404ce7c42d954225ebc4059353004fd7418552004ff7458e51006f610d853219f6e5258a510edef7650a21014fc72d8d202d6df3118530014ec72595430457e71945510efaf4350a21046bc54593510076f7550a21075ec72545304d67f43d9542014fc7258f51044fc76d5132004ff7558d210067e3219510057d4634c7100267e6455150014f
  | 5 => 0x17eec20d89510ae7e5258b5000cfd7688710044ff7159710044ff76596410467c65d451000cfc70592310056c754c9200467c5358f540067c65d8132006ef72589100467f53984510067f31d952119e7e629455115d7c7254451004ff7654f1001cfe73d8550044fc76d4d4002eec62589100067d5458b50027b76190541004fd72d8d40136dc6358d4100d7c7054750006bc6458910026ef7650a21004fe76509314a5ef7258d420467e65195302e5ee754c920014fc76d452101eef764ca2140df671d9231004ff7058a51004fe764854035edc6550d30004ff7648530006f761985320deed50d8910006ef54d891026ebf4259352005f9708c7100057e75d8a31044fc71d9510024fe7459621006f56118532024fc7458231004ff7650550004fd75d8b10044fc76d512101cfc73d9151004ff7258e410067c7558b101967c20d9510004fd70d923115e7f20195210067f7559540286ec62d51100073f6550d42024fe74d85530f4ff7058d10007cd434ca210deef628851019f6f20d95212467e6454d50006bd6490750026bc64d5110004ff7358b54005bd74d4541224fd74d913006dbc7459520024fe7458b5001e7c63d4e510057f75485400467e6555120044ff76d4d21016ec6288510004fd75d81420eebc648851035f3f5450c514967d73d9532004ff7058a310067f3119510006dc6358910044fd70d8550004fe76d4f10006ec6258151004ff7058f5101cfc73595210067d75d8e21276de43d8d54017eb6048520005f9701471000cfc70d85531567d4019510044ff76d4910044fc7558d21024ff765912014cfd73d9131006df735912022f9d4250d32004fd7650b50026bf6255142006bf745923101cff7158f100467c7319542005ef725471001cff7694631006df7358d1025ebf42d8d543e6ed76d4a210467f515805101cfc73d954223eec2158f52014ff74d954200df5768c710004fd7218553035dc7359510004fd764c75028edc63d511019d7e72d525101f9f7450e3101cfe73d85523f4fe71d922100cfd74d8540006ef7258d20006df7359530006df6314510004ff7654e4147ebf43d913200cfe701854301ede638c6210e6dc63885100edbe74d9621004bf745952010ede40d8d1025e7c54d8d540057c755854200777654c5100457f7654f520067c10d95320457f7455152155f671d9710005ed7290520014fc725925119e7c21d9521004fe71d8953004fe76d4b1010edf71d8d1019eef2058a5100cfe7558f500067f75591100067f65d4910024fc745953000cff7658221006f561185540067f6554d214967c32d9532004fc71591320475c5355153006ef7258d10096ee52d8950007f141c411023eec62589534967f21d953201e7c63d4d50006f671d8f100067c5259631004fe71d81540d6be64d912101cfe735
  | 6 => 0xc629455100cfe76d8152006ed71d89514976c21d9532024fc75d915001ef4638c510006f7619854001cdc73595200467c65d5110004fd76d494101cfc7358b50024fe7459530017e7714852001ede6350d20267787055150024fc7458051024fe74185520075f6354d50024ff72d9542127b87050540024ff7650531005ef73509200067c6588510024fc74d8d20004fd7650f51014fc72d8554014fc71d8910005bd7494540006e46148520004fd71d8953005fb7054550004fd75d8532026bc6450d52024fe7458b1017dee76d8951004ff73591100067f755953000cfc70d8552014fe72593500467e6554d200067d72d951001cff72d9132005bf74585204d67e43d95420067f6599543004ff7650b500267c6455350005bd748854000cfe76d8132036de63d8d10004fe7650d5101cfc735875216ebc4159051005f47150931014fc7258251007b7745051001e7c7654d52046f751587524d67f41d9542005ef7258530096ec21d8950024fc7458f100a73f43d5150006f671d9310006ef624c95119c7e761952101cfe731855000cfe7018553014fc7258d100067e74d95104ce7c74d95420d6bf43d91212767e63552510467d7119510006dc73589100467e7419510004fd71d8d4215e7c42195210957e72d515001cfc731855000ddc764c5300067f4319521006de30d8d41004fd73185400273f755514200df870505100147c7654d5200cfc76545100067f5318550004ff7558d10005ed744ca21004fd74d8e2101ebe6350e410467e659463115eec2158851024fe74d8d10004fc76551101c6f631d8553006f47158d2010edd30d8d1001cfe735951020e7d75d89502467c6454d52007af64189100467f5458051044fe75d8520014fd768c6210475f6354f52014fc7159221445f671d8e41044fc7650851014fc72d9510004ff735835401cfe73d91102767c6355152006ee74d8951024fe7458051007af64d8910266bf405935000cfd768c7100067f411953200cfe7058a31004fd75d8d10004ff7358221044ff7659621024fc74d9510004ef725875303ebf41d9110006be43d911028edc53d915318ebf41d915118ebe54d915125f3c5499543006bf64d5120106bc4159131006bc7459520005f970945500067f6558542014fe72d8d1001e7e6354d52004ff7058b540067f654c910154fe71d971001cfe765453116cfe76945410067e101952101ddf7554d3200dec70d49200067c41195210467c6594510004fe7690550014fc72d8d1035f5f5350c5103ebe54d9110006ed6288750016ee6254a5119d7e72d4e51004ff735971048e7e431953219e7f6594521014fc72d8543004fe76d5132015ec7254521004ff7650f5213fb771d911001eee634ca210467e65d4e410079f6418d1013fb440905100cede4358a3100cfe70d8d42
  | 7 => 0x8f100057f75509104f6dd73d9543004ff764ca410067f655812108f9c4358143004fc7650b100269c6450d30005ed7214621026bc6450f1000dfa708c710044fe75d8e2101e7c6354d5202eec525822113fb44090710047777154451006be53d9110014fe7259310336bd42d9120004fc7650f10006f77159510014fd70d952010fd610d8d1015e7e5258851004fd70d8543004fe7650520024fd72d954201cfc739875419e7e52d9621006dd6354e510057f755891027ebf40d915000cfe7694550005f47154a3101cfe735822114ede4358e41024fc74d9531046bc54593500067f65d4521024fc74583520267e64d5150014fc72593530467c7558753024ff7659310014fd73d85320467d711954201edc638c520006ee70d89511557c7054c51024fc74d89531bcff7159521026bc64505210067f655522113ebe4058241026be64552510066f65d891004776615445117ef6215875213cff70d9110215ef72595320067d5358b50004fd7398754044fe769075004dec72597100457e758c55000dfa701452001e7e6354e51024be74d8e210063f65191100467e65d5231004fd7688530004fe76d4d42014fc72595310057c754c91003dbe74995100073c65d9110004ff7458f51127b7405051001f9f64d4d430467e76d4d503e6ee65885210066f6518910014fd701852013dbe7619110014fe7258750014fe72d8f10004ff7058754007f1709071046eef20d913225e7e64d4d52014fc7558352007d77150e31016ec62d494101cfc7358750005bf74589500067c52185500067f65d5121436bf40d854301cfe73d8554004ff70593514c67d4319542014fe72d81310067e52d95100057f75589400057d7590750006ef625091000cbc7650d4001cfe735875401ede63d4e2100cfc7018554006ee20d8931004fd70d85543ecfe71d8e21006f7611452000cfe70d8953016ec62509100065f6518d10005bf7150e41004ff765454000cfe7058754026bc645091001cfe73d81210067f655511000cfc70d9631006bf6490550004fd71d9542006ed641895115f74211952101dbc73d514317fe4215452101edc6350f5019e7e21d952108f9c5350d40036df32d8d100957e72d4d50004ff75582410efae5450a210457f7354d50004fe71d8d40195f671197100047f7559120086ec6258940004fc764c94001cfe73d96410457e7550f5004eec2158b100067c6558910044fe76d9520006ef725912000cfc70593530067e75d9221004fd76d4b100067f75597100067e7619532014fe7258f510c4fd7648510205bc74581521eedc6350910276de53d8d5439ebf43d8940006ec7259510006ef72595100467c52984512d6f63118530015ee72905200067d71d9532004fd75185321c6df3258f51004fe71d895400cfc7058e4100cfd74d8d4019e6
  | 8 => 0x4ff7688750005f771581320057c755893001edc6354d400076f754ca210467c5298750004fd72d8d54025bc745824126fac725514210ddc7050e31024fe7458f520067f6554d10014fc7259051466df32d8d42004fd7654e212a7d81018d10426de43185320467e65d512019e7d42d952113ebf71d911028f9c53d5143004fc7650d504947f7654f52005ef725512028edf3258f54004fc7654b1002dec7259110044fe75d8542005ed72d4521047775154a514ee7f53d95430967e52d8950006bf745912122faf2050d42004ff74580510f7d8704c5300067e32d9510024fc74d81311947e76195100957e7254550004fc7650931006f56118552006bd64d5221044fc76d4d200deef50d89100267c645525100cff73d9130426f531185320057f754855001dde73506310067f65d8d21004fe76d4e41014ff76946210deee30d8910076ee62d89300deed70d8910004ff7258353046fb5058352006dd634cb5012eef2059121024fe76906210067c6550910007b77450710007775194641004ff7158d2000cfe70d8e21006ec72587540467c5158754024fd72d8d4201cfe76d8d510067f755962101eec634c92000cfe70d9542044fe75d8931006dd65d8d100067c65591214c63f4319542044fc7559231004fd73d9150006ec43d89100ef3e54d522135ebe6550d401a6dc6358e512a6de3018530014fc72582412fcff7258d20114ff7358d21006ef725962100cfc7159310004ff76549310067d54d895001cef764ca21004fc7654520004fd71d81420067f659452000cfd74d954017eee32d895100cfd73d8930004fd74d8d202473e5454d420467c6454f5026cfd7699542004fd74d8950004ff7358b514be7e20195420976c5259520024fe7459531014fc7259631004fd70d8d54004ff7650b1010ede608c5314b73e5355142024fe7654541016ec624c941006ec64d895128e7d75d915324cff7359530005f77154931004fd74d95103cd7e76d5150005ef72545310467c7119532005ed73d4a210467e76d5150005ef7258151006ec53d891001edf6250d3201cfc735911000df4708c510014fc7258e41004fe71d9130006dd73d923101cfc7158231006f5611855317dec72581511a75e43d4e51006ef6418951046fb70580511a79c4350e510457e75d8950026bc64d512000df87054550004fe71d8152014fe76d89504be7d2019542004fc71593530076f72544510057d74d4d521debf41d9132006ed75d891002eee42582212473c54591530956c72545500467f5398750035de73995100067f654c510004fd72d923107ebe64d913001ede634c851006de75d8d10014fc72d8d4101cfc7359710316dd32d8d20004ff725823100dbc7650d400467d711953201cfe73d89402467e545954341edf30d854349e7f30d9532006df735
  | 9 => 0xe7494540046bd5458b54005bd70d514301cfe73d8540127b74050710024fd73d85430467f70195324867c2019532004fd71d95300067d651964101cfe73d8b1001edc63d4d20004fc7159520065dc73591200067c4319510024fc74d95300dcfd70d891023eee32d8953006ee75d891000cfe70d95210057f7550b10006ef31d89510ad7e725475000cfc70d8d10024fd75d89542767e53595430067c70d9532024fe76d91500067f755964135ebd65d5143176fa60d815113ebd71d91100c6fa10d812109ede43d8d50004ff715954008edc6358d4001c7f7654e51004ff7458851446f541185432debf4318540006bf6455153014fd73d813228e7e63d525133e7d50d9520024fe74d853201cfe73d91300a6be64d915001e7f7654e514c76f4219542006df6354510227b87050d40046f451987530057c7550a3100cfd75580510edbe74d8e21024fe74d81510467f5458b50004ff735912001cfc73d9641004fd7650c51004fc7654e410076f7254d52004fe76d5231005ef72545400057f715505110edf20d8d100067c53d95210067f31d9510006f76198554007b7644c51001ef4638c71001cfc7358b511f6fa50d81520067c60d9542046f6719875000ff271c41103f5f671d92210deef71d8910004fc764c5400057f754c8510067c65585320467c5158753024fe74d8f1014ede5358e41006bf64d49100067e60d9532006ed54d895101cfe7358a41016ef61885210e79c4350e2111edd43d8d4107f9f4250d30046f85058353006bf6450d5201cfd71d89311967d40d95100067f6554e21006ef62885500067d5358851004ff715835400df8704c510026ee6450a2120eee76d492013ebf10d911000cfe705935309f5e43d4d50004ff755913117eee71d89510067d6519543025de74d4d430d6bf41d912114ebf43d913109ddc735895009f9c4350d50024fc74d8530004fd764ca41005f47154a4106ebc43d91201f6f86058152006ed53d895108f5e53d4d40004fd75d891001cfe73d95300dfe810d8910006f42118550006f410d8542166df3058c51004fd70d8d210467d76d4e510457e75d9153004ff7158352297e810189100057c754cb10006dd72d8d1019f6c52d962100cf5768c7102b7b810191100157c76551520267c64d515201cfd74d8543007d5638c710026bc6450f500067e40d9532006f761545500157c72d4d52004fc7650e51046f75198754004ef7259521044fc71582510467e6519520024fc74d8931004fd70d85320067d5458851146ef20d912131eef20d89400056c7548520014ee72d85430067c65d8d4248e7f7654f52014fc7258f500067f4119521006ed628871023eee52d89530077751946311c79c4350f51006df63485100473f74553520457f7655051014fe72592510067c21d951000dbc7050d40
  | 10 => 0x893026f3f525514201cfe73d915000cfc7058f510057c7548510024fd72185420067f6554531004fe76d45300067f53582512467c6454e51016ec6250b10004ff7654d210e75e53d4e211c67f7654c510ad6c7254750007e7628c510046bf7459350005ef7258d51006df64d8d10006bc64d8d10024ff7659130004fd765522149e7d30d953200cfc7058a31004fd73d95201675f3254c51007b4648c510194fd70d951010ede10d8d10007cd634ca21044ff76d5132046f771587504967f42d9532014ff7658a31006ef63d8910164fe76945314967f73d95324ecfe7619543006f461945501a57f7654e514ce7f52d9542036de7618d10006ef6318910004fd71d915006faf43509201567e3019510004fd76d491000cfe76485101df9f4050d324c67f401954200cfd71d8d1022fac7250d4201cfc73d9510154fe7694510005ef725515217eee52d89512a6dd731853001cfc735875401cff74d9543004fc7158352004ff71593500cede43d8d2102eee62d89100e5ef764ca2101cfc7358a4126fac21551420067c74d95104ce7c20d954219cfe76145211a4fe76145310076f7550920037d4638c510006bf644c910004ff7359310015ee7250621006be6219110004fd73d97100067c72d9510004fd76d45200467d7419532004dd73d9621157781019510005dd7314530004fd76d4d4023eec21d8953004ff7650a3113ebe40d9310006ef6248710004ff7159530004ff70591310457e758c7500079d434ca4100dfa71c41100475f7354f520467e6594531006fb7059110005df7150d3001cfe7358251014fe72d9151004fd73d894010ede50d8d10004ff7654910005df735911001cfe7359641004fc7654540006ee63d89513e6ef51d895135edd65d4d4325e7c64d4d5001fd66150e310067f659954200cfc75d81510247c7558f54005f77154a51046f7519845126f6c2155352004fe768c520006ef6294551004ff7650e21014fd769062100df4708c7100067e30d9521014fc72d81430e6df3058e2101cfe7359540006de6218d100ddee7050a21006f43118520004fd74d85520eebc6459221206bc40d91520467f5358352004fd76d4d20044fd74d8d540067e70d952113ebc20d9110026bf6050540024fc7458f51004fc7654a31024fc7458e5112ebd4259221006bd64552314c67e4119542004ff764c910006be4359051014fe7258251006dd638c710004fd74d81310067f65d45103aedd43d8d4013ebc6090541004ff72592311967f6594510066dc6358d200057c75581210067d53d89500067c43d9521146ee4258a4100cfe7654510044fd70d895028e7c63d515201eee634c920004ff72591310067c52d9543266fa60d8154004ff71595320467f60d4d5023f5d5254d320057f754875001cfc73d814237ebd43d9130025b
  | 11 => 0x4ff755912100cfc7059531004fc768853010cff7358d10004fd72185401d6f86058132006bd73d9110004ff7458a31014fc72d911044fe75118951014fc764c521044ff76d4d20004fd71d8d54004ff7359221024fc7459710046ef5258b5420efa2058352186dc30d8d51015de7250d32004fd70d9521035dc7359110256df32d8d5200cfe7058f540467e72195320467c65d4d423e5ec754ca210067c601952100cfc70d85424975c32d9532006be52d9110014ff7648510046f75198750004fc768c5400067c65d9121026bc6450d103fcff7158d21005ef7250521044fd73d8553014fc72d9531004ff7458353004fc7654d40005f47154941006dc42d8d10044fe76d9542006bf64551100073f65d9110004fd76d4d41004fd75d91100077751945410267c64553521bef621d855218ebc64591511ef9c5350d420057d73d5152174ff70595100467f545885100cfe76d4510004ff7259543004fd7650e510069f6418d101073e54d5131044ff76d5221006de3258e510467c6555132165f671d96310457e754c5500457e7550e51015ef745092000cfe70d915118ef64158754006df43d8d10004fd73d8542184fd7654531007e762905100467c7419521006ed43d8910006df75d8d1000cfc70d9151166df3258c51005bf735054019f6c52d8a51004fc71591300f7f0704c5100467c5459353025de76d4d43005dd73d8a510067f65d522122eec6250d1009ede53d8d5005ebc41593103edf671d8e210057d7550f52024fe76d9151004fd75d9132014ec7259710004ff7058753004fe765494100cfc70d9152024fe745835202df97098520006dd43185300067f65589103e6ef54d8951005ef72545500067e70d953201cfc7358b1003fb464905104967f32d9532006bf7459131174fd76d4710005ef72546210067f6554710004ff7558b104cf3e42d95423ecfe768c5211e4ff7059120004fc715935011f9e6450e31007e46290510006dc41d8d10015ee75d4920004fd74d8951014fe7558f52004ff764c941044fd74d855410edc50d8d10004fc765522100cfc7018532004fd768c52018cfd76d4641044fe75d8d21004ff7650e51004fd7650b51024fd75d8d541967d50d951013fba4058241014fe72596414ef9c43d954301edc6350d1017dec72591510463e7419542014fc7655152004f77158d20006f77159131024fe7458221004fd75d8f10014fe72d953001cde73d9621007e4628c51000cec7650920004fd70185540067f65d511001cfc76551530473c5455151006f77158d21004fe7654f10024fe76d91300067e60d95214ce7d32d9542044fe75d89102f6f521d85200067f659953001cfe73d81424f6bf42d9543005bf7454941406ec21d854200cff768c7100067f658851001cdc7359510007d46390510356de43d
  | 12 => 0xe76d4920065dc73585201aebf439875432dfb70591200067e6419532024fc74589100467c74195320c7e870485200467e73195320067d74d9521024ff73d9543025bc74549411967c50d97101a5de73d8a5148e7d3119532004ff7059231004fd76d5131014fc72d954001dde739053045f5c5454d32004fd74d9530006be32d9110016ee624cb51004fd75d8d40014fe72d9641004fe76551320067c6558d210467f701952135ede6550d30004fd70d96410067f54d895010cff70d8d1001fdb604c53001cfc7359541004f471595200067c6550d101f5ed729952000cfc70185431ef5e53d4d42004ff76545300057d75985320067f65509100067c659853200cfe7059541004fe71d81530eebc4359221005bd7550d4201cfc7558353014fc7258c514bf3c4219542005dd7399540006ee64d8951044fc7614540044fc76d45402debf411854000dfa70d4510004fe71d8d50006ef521852001cfc731855202dec72545100feef2058d214867e3219532004fd72d9641005df7355153004ff7650b511cef641d8554006bf6490530005ed744c9200457e7550d52007746590510006ec72595410467c65d4e2113df774505100deec70d891001edc6350f52046ef7258b530467f7319521007cd434c920044fc7614621024fe74d9520016ef60d49200067c50d9531004fd76905304c73f43195420067d74d9510005dd73885304d67d54d95420267c64d525125ebf42593530067c71d95320067e71d9532004fd74d95214867d321953201cfe73d95400defa20582210076d54d4a21006bf644c51001cfe7359251007ad5450a210067f6599621006df638c540006be42d9150004ff7648750005dd73d962133e7f50d952000774658c5100057c75487100467f7419532006f761985504ce7c72d9542004fd7418532014fe7258351004fd70d95420067d70d9521004fc7650d200067e50d95310057d76d5251004fc7650530144fd72d91210deed20d8910024fe74d81310467c525835222dec7259543046ef7258b540467c741954201cfc7359540005bd748c54015d7c7255051024fd73d8943024fe7458a51044fc7614641014fe72984510067c53d95201df9c5450d32186f63158753004fd73d8151024fc7458d20095f970995200067c65d8d100b79c4350f50004ff764cb101acff74d9541004fd74d8152004fd71d8d40096ec52595200bdfb705954001cfc7158a31004ff765091000c7e7598750014fe72d8154024fe7459631004fe71d8d5410df7734c51000cfd73185300067e62195102467e54d9153044fe751853223f6c2154f52004fd76d52310feec52d8931014fd74d9542006af64d891001edc6350e21026be6490621006af64189101967e50d97100067c71d9542106bf41d913102eef215822135edc6550e3101cfe7359221
  | 13 => 0x91104ce7c21d9542004ff735954200cfc7654550006ee64d89100076d53d4a21016ef604c9200467c6554531005df73581210467c70195324967d21d953201cfd71d9131006bd74d96414deef52d81520467e615525101cfe73d89411967f50d95100047f7654451004fd7654a41006ed74d895100cfc70d89104cc7e7619542006ee6418910006ec7258d10005fb7055150006ef6254910006df6350e2119f7721d9521004fd701855314edc639051013ebd40d911023f6c7254d521df9c6450d320067d75d9221004fd75d81411567e201951043ebf4318542014ec7259110016ec6254910006ef628c51026eee42d89543e6ec53d8951206bc64549101cebf4259351044fc75591210057f73550511557e705505101cfc7359251116ec628c510026bc6450f52015ee724c621024fc7458e210067e53d954211ebc648c510004fd70d85530057c754c940046ef7258851464ff735913201ddc7350531024fc7459510006ed32185200067c50d95424be7d42195420047f755891000cfe76d81510067f6518542005dd731964128e7e53d91531debe64d91320067f3119542044fc76d5120024fe76d91210067e30195420079d6350e41044fd73d91530467c65551304c67d41195421567d201951001cfc7358a510ae7e52d81520067c311954213ebd70d91104be6f20195420057f7558941014fe76d89314876c321953215e7d3219521006f76198542004fe769453009ddc73585500067c53d951001c7c75587531fedc6354910004ff7459710126fa40d8141006de6418d100067d54d81520467d76d5251004fd70d9121006bc21d91101d6fa60d8132044fe75d8d4200cfe7558b5001edc638c5100067c65185420e5de73d9621004ff764c950006bf6454d10004fe71d8d420467c6454f5201ef6638c710025bc744c9410467f7319542004ff7654e210067c65d814204eee62d8b1000cdc7650d3016cfe71d96410067f63945514867c2119532205be74985520067c52582510076d65d4a210267c645505136ebf40d913013cbe76191100063c65d9110006f441d8520004ff72597100af6c52995200057f7558d201e6fa20d814200cfc7058a4100cfc701854235f9d73d51430057f755814219fe721946210067d74d9532296ec201852048f5e43195321957c7055251024fe74d85504c67c401954200cfc70595320fedf3258e21006f76198530004fd76d493101cfd70d8930005ef72585540079d438c5400473f7455251006be405935305fb464507104ce7e32d9542005ef7254e21044ff7659532024fe7459532006ef62509510447e76d953215e7c20195210467c72195420067f6550d21026bc64551534be7e4219542004fd72d915128e7e63d51520157e7254f520057f755093119eee62d8a51024fd73d8143005ef7150a2100ce
  | 14 => 0x1b5f771595100263c6455150006ef72587540067f31d95420057f7550a5101cfc71d8d10004ff72595300057c75589401957e70d4651004fd7654d10024fc74d8b10006df7359532006f721185300067c65185321c6de4358f510deef40d891001cfd72d9532004fd7614540004fd74d8d2101cfe73185522aef641d8540044fc7558241015ec7250f5201cfd7694631007e762505100067d65d4e4103fb46450510014fc765452100cfe70d954310efa3058231006bd6450e51007e46250510006ec43d89513e6ec65885214bf6f20195420067e10d95320067c73d95100467c6555121236f860581532b5f676905101977810d951000cfe7059543006bf649052001cfc73d922118cfd76996410a6bc6459150044fe75d8540046dc5358f50024fe7458a310467e65147100467e721952100cfe70d953101cfc73d9150004fd74d9531004fe7650b10005fb70485100067d65146211eedc6358d42005ed72145200473f7455150004fc76549300467f7319510004ef7259541004fd71d813202dec72595101debc6459132004fe76d4d40014fe72582413e6ef50d8951006bf6494510006be73d9110006bf7459520006bf64d45100447c75591200079f5450e31044fc76d4d100157e72d515200cfc70d9231006ee60d8951044ff76595434ce7f74d954204dec72547100079c64d8d10037d6438c510007d4635051001cfc76d45310067f75595320067c73d9542197f010945100057f735455048f5e7319532036de43d8d10006bf31d91100457c754cb51004fc7654d20006de3258e41025bf7350d40007cf63d891001dde739453013ef760905100067e50d9532024fe7458f51006ee30d895100cfe7058e2119e7d20d9521046fb505805134dfb7058930085ec72585400457e754c750007cf6318910014ff7658a41006df7358d21004fd76551212073f43d5152004fd7518530006df41d8d1000d7c705515000cfc70d895401cde73d92210067d65d4d201967f71d95100467f701954201cfc7398752146ec6290510004fd73d8550026bc6490510004fd7654d2148e7f3119532014fe7259530006de54d8d100457c754ca511f4fd76995202def641185400fcff7258d21006ef629051000cfc70d91210067d65146312e5ee7548520016ee628875003ebf435824101cfe7359710046fb7058351005ef72595100057c75591100067c43d9510004fd70d89534967f20d95324fedf53d9153046f671987541967e30d951044eef521855217eef205875201cfe73d9151005ed73d492000cfc7059641026bc64507100467c5458f5419e7e20d9521415f77158931017eb60d49200067d6519710006be4059351026ec6450920004fc7159120004fd76d5121004fe7654d42056dc3158f1010ef7608c51001edc6350f100057f754c951005ef725
  | 15 => 0xc764c920006ef7259520005f4715895028ede4358f544ce7f72d9542006ec65d89100467c65d4d40004fd74d8d10006dd73d9221004fe7655130014fd71d912125ebc64d4d10004ff725935101cfe73d81514ce7e21d9542006bc651911017cfd76545210467c70195420067e63d954215f6c5214621044fe75d814310ef860582310067d70d9532065dc735952025ede76d4d43006dc6518d1001cff7614631005bf7458132006be42d913000cfe70d8542006bf64589104967c42d9532066dc43d8d20024fd769464135f3c65d5143006dd6350e510c6ed2058b10004fc7690520015ee7188521044fe76d954000cfe70d8d5100cfe7058c51024fc7459631007e4614852001e9e6350e410067f65905210057f755912001cfd70d8530006ec725875322eee42d8943014fd7614621006bf6450e21044fe751854301cfe73d954213ebd50d91100467d72195100075c65d8d100067e6419510004ff7358a5101edc63d4d102eeee321852001ebc7650d4001cfc7358354004fe76d4d20416ed72d85320067c654c52100cfe70d913210dde7618d100057f7454f52004fd7654d20004fd75d854049e7f43d9532004fe7655120006bf648851000cfc70d922101edc6354d503e76e65d4a2119e7d52d952119eee5258a51005bf745815248e5e43195320dff01088510014fe72595100067c3019542006bf64d5110014ec725875400cfe70590510067c65905100057c755894100d7e70d4550004ff7058f520967c525952001cfe73d814115e7e3219521004ff755931001cfc7358b54226fa40d81434c73e74195420467e6154e51004fe76d51300067c50d95320467d701954220def7259520024fc71d9110326bf40d91200457c754c9500467e7598750066dc53d8d20004fd70d8d41014fc72d8d400467c65d51320475f7354e51004fc76905300067f658c52113fb640905100067c41d953206fae54509204bc7e76d515229ef631d85300157e72d4d52014fe7258754056de43d8f100a5f970995400157c7254f5202dee72995104867e2119532005ef7258d10004fd765512006f3e54d5120006f671d96210057d76d4651026ec7650920006bf6455151006dd6354e410467e65195410467d76d4651005bf7459520014fe72d9543025be74d4d42004fd70987520067c7558d10004ff72583540047d75d8e21004fd75d91300467f71195422767e63551500457f7354d520079f6350d420ddee704ca2125f5e54d4d430467c6554910004ff7650a511967d70d9510017eb604c9200b6dc4358f50004fd74d8931024ff76505100067d53d815218df571995410079f5350d40116ef2058a31044fd74d8154014fd7558b50026bf6250d4201eec634ca21044fe75d81420067c658c510004ff7458d1026eef20593520057f7550b51116dd32d8d21
  | 16 => 0x8530196f860582514ce7d72d9542024fc745952003ebf4158241004ff735891001e5e6354e51006df6354d500157c7654d5205ebf43d9310024fc74185530067f6550d10004ff715954206ebc54d9120014fe721855418ebe64d9151004f4715912026eec62551510067f311952100cfc70d8943014fc7258f5400cfc70d8d2101e7e6354d5000ddc704c5300467c6454c51004ff715913235f9f54d4d43004ff7558d200067f7559520004fe76d4d10024fc74185520475c5354d520067d6594710004fd72185501cdf7715954101cfe7359121007cf7250d32014fe725905101cfe73d9121014bc7650d420067f6554d4200cfc70d95311aebe64d92510467c635535008f9c3150d4007dbc74589300077765905100067f65d8d1000cec76485200057d75d8e2100cff769471001e7c6354f501957e7054e5111f3e54d52310467d7019510006ed63d89510475f7354d500467f5358051014fc72d8f10004fc7158f540057c75485400067c64d95210457f71544514577410d46510067e431952100df4705051001cfe7358b1025f1c54d4d43044fd701855010cfd70d8d10006dd648c5310feee42d89310467e6514641006dc7359520005df7550d320057d7550e5101cff7690631004ff76505200467c6554d2115f6f20195210067f659853227cff74595402b7b57119110005bd744c540044fc7614520006ef62d8151006bd74d8e2113ef81058241004ff7358750006ef7259121256ec62d4d1008edc31d8d40015ec72d52210269c6450d320feef21d89311967d71d951001cfd741854301cfe7358b5135f5c65d4d4301cfe73d91200067f40d952111ebe64d923113ebf70d9110006ec54d8910014fc7650521026bc6450c5119f6c21d9521004fd7648750046f6719875323edf3258f52046bf74593510079d4350a31187d73154631016ec624c95128f3e53d5143057d6438c710004fd71d8d520467c6594530006de32d8d5000777658c51015e7c2119521006f410185521eede43d8d4200cfe7058b51006f741d85200067c60195320057c7558530014fe72d8153004fc765493100774655051001ed4638c5100067f755952101cfc73d95402473c5459543004ff705963100cfc74d814107f9c4150d30004ff764ca510e5de73d922141cff715913100df6708c510014fe72d8540075ec72585300057c7558910026bf63d514300cfe70d8954024fe74587523e76f54d4a210447e76d952116f3f4255051004df7359110006df4358c51014fe72595401567f4019510014fc72d81410073d5450950044fd73185530067e62d9510004ff74596210679c4350d200067f75589100067c5259641015ef7148520125f57490510006ef53d89100076f754c92000cfc70588514d67f54d95420057f7550950036de53d8d10006ec651891001ee
  | 17 => 0x4fd73d8520024ff70d9540004fd76549101957e70d4e510fcfd73d8e21004ff735824100df476505100e7ce634ca21004ff74589100067f75595421beec2058b5100cfc70587541967e20d9510005f47158930126f76050510006bc53d9110014fe72d9541024fd72d85420057c7558142006dc63d8910004fc7159530005bd741963135f3f5450f52004ff725913022cff7259132006dc6218d102b4fe76905100ffe4214c5210067f70d95210467c6514520004fd72d81531767d5059710004ff7158f52024fc74987520063f65d51430467c7319532044ff7659631004fd72987534cd7e76195420067e70d954201cdc7359110006f970d8f10006ef62505100467c65545411aebf4059251006df4358e21007b77150e41015ec7254e21005f47150a313467d52d952001cbe76d5143005f47155251007d7634c510136dc30d8d4112eec62505100675e53d4d20006ec60d8951004fd71d91522def54118540026bc6450510276dc6358d540067e74d9532405f77159121024fe7459710024fe74d95402bdf77158910346ec52d9520004ff7558f10004fe71d8d20006df63d4910004ff764855000cfe70185540457f745505101dde73551320467e76d51520fdec72545314975f73d9532024fd7614641026be6450e5110edf10d8d100057d7550d504be7f21195420067f65d4d21026bc6490520014fe72d95400467f74195210467c65945211ff5e43d4d52005bd741454014f9c5350e41005df73585401ff9c4350d52005f47158940006ef7259543004fd7650750004fe76d51211fddc735815219e7f71d95210063f65d911019cfe76195211adf671196410467c74195100467c65d4521006ec64189511d4fd73d8d20014fe7654521007cf7254d3200d7c70553500467c65d4d1002eec52d89100467c65d513000cfc7098753136dc6350510004fc7655131004fe76d45200467f7119521046ef5258b5101ddf7450e310057f75591324bf6c42195420bebf4259350046fb70583520057f7354750044fe75d8141015ee72505200a73c6455150004fd75d8530006ef72591320067c6558d4222dee72d854301cfc75d8d5013fb640907100067f54d81521b6f710d8550014fc72d954102eee42d89103fef621d85320067f7558b10006bf6450910025bf7150540044fe76d95100067f6599541004fe76d4540006df634c52100cfc7058d21284ff745954201ddc73545310067f7558d20004ff705912128f9c43995430465e7319532375fb7059130006bd6490621004fc7655231005bd7494641014fe72d9131004fd75d81210473f7455350004ff7058e510e6dc6358e21024fd70d8d400067f7558d100deec40d8910004fc7650951026b464905104867d421953200dee70509200067f65d91320467e65146212467e6454e51004fd74d
  | 18 => 0xc7558b50004fd72185431fede43d8d5246ebd42d9132004ff7259251004fe76945200067c54d9521036de4358231004fd75d8520294fe76885101a75e6354e5119e7e5258a510267c76551502767e6355352014fe72595410067e52d9530024fd7159310004ff725905101cfe7318554024fc7418520044ff76d5231046f771587530067d5458a51046df7358c510b5fb70595300457c72d5251024fe745823111dbe74d8a311567c40195100057f7550b50004ff7650d51046be655514223eec6254d51057d6638c7100067f655513025e7c64d4d520057f75591100067e6019542014fc72d912019e7e72d9521004fe71d81430073d5450b500067e52d9540014fd731853228e7e63d5150006ed624cb51004fe7654931156fa2058051004bf7458d20006f7715912028f9c31d51431fedc6358d5200cfe70d9641006df634c910004ff7059352044fc7559131187d4315453118fb74154641024fe76906311e6f8605814201e7e63d4d5201cff7658e41014fc72d85533be7d54d9540004fd7518520004fe7690530024fe7418550024fe7458f5000cfd72d9120015bc7250d42024fe7458e210067c6558121006ef6254950004fd73d89411b4ff71595100067c40d95210467e659454101cff72d953200cfc70d96410057f7558d21014fe725835413ebe30d911013ebf50d911035f5f5350f5200df470507100079f5350d420467c65547102e5ec754c9200457c754cb50276de63d8d540cedf31d8d21004fd74d8d503d67f7654f50014fe72d952041f9c43d85430067e421951000df6708c7100067f65d8132004fd76d4d4248e7e3019532006df7358e210067c53d9542026be6450b5149e7e43d95320457c75485501edde73985420467c65d512110edc20d8d1000cfe7059352056de63d8f103e7e671d4a21004fd73d895103ebc43d9110006bc62191104b73c535514200cfe7058a410067f41d953200cec764c92001cfc73d8121014ee76d895115e7e211952108ddc73585400057f7558530006bd6450d202b6bd7418540044fc76d4d420067c10195420067c63d952101cfc735905119d7e72d4651237787054d5000cfe70d91102aef541d85404be7c3219542006ee20d895125e7e64d4d500067d651954148e7c4319532004ff7258f54005ef725452019d7e7254e5101cfe76d8d21006bf7458d10005f97014520004fd70d913102eee76189100065f65d4d4301cfe73d8954236fa60d8153006bc64d8910006f761985201a6de63d8e5100cfe7059631004fe76d4d210076f6588521006bd74d962141df77159131006df72d8d1001edc6354d51014fc7259351006ec31d8910006ec63d895100d7e7054d502def77650710046f45158750024fc7458b10025bf7350d42005dd73946310467c5258051014fd75d91521967d20d9510
  | 19 => 0x452022fac2150d420467f5358b50006bc7459510004ef7259510006f610d8542046ef7258b50006df648c531004fe7655131006be74d96210075c6554d32136bd43592310075f65d8d1015e7e521855200dbe70505400067e50d9541024fc74d8550024fc7458221024fd73185430477b605455033cfe7619520024fe74d952101ede634cb502767c53595430067d5418552004ff7359351116ef20d8d210447c7559110006df6518d10007e77150a21024fe76d91520067d6519631066de4358d200067c65d8d2101ede638c710046fb5058354085ec725454000cfe70d854319fe4219452122cfd74d9132004fc765513214f5e53d4e41006ee6318951004fd71d913005ebf41d93100067f7654750024fc74d9532425f671d8a31246be64d91530067c6550510004ff7158b5000df4704c510205ed72995420057f754c910005ef71509200deec30d89100deec20d8b101beef611895101cfc7558b530457e7550550004fc7158b53005bd72d5143264ff7059540006be40d9152004ff764c520004fe71d8940005bf7458530044fc7650b500067f6590510004df7359120004fd76145300067c6219510007eb704c920004ef725911048f6f3219532004ff7650d201ce7d75d855419eec629455101edf64d4d43004ff7258f10006ef625495100cfc70d913101ef5768c7100467d731954219eec52d96210dfe410d8910004ff7358051004fe7654d41046bf545905100cfe76d81410067c65d891028dbf74595432bef710d8520276bf435935313fb810d9110004fd73d8954014fc75587520067f6554541086ee62d89402a6dc3018530004ff7159520005f77154a31126fa10d8141297e410189100dcff7258910006ed72d922100ff361c4110004fe7614540005ef7254d20004ff7654d41006ee6518910006de6518d102b7b41019110004fd72d9153014fe76d8910004ff7258f5118fb4415454126eec32d89540475f7354f50005ed729462117dec7258d51024fc75583540067f755954100cfd76147100067f7559543006be651911000d7e70d4d5000cfe70d89410067f655052101cfe75593530067e64d95100067f6554910004fd72d95310467e65195400067c31d952101cfe71d8d10045f671945514875e32195320eebc54592210067c31195100067d5498752004fe764c55001edc638c54001cfe73588510067f658c510046bf7459352024fc74d852001cfe7358750024fe76d91320267e64d5251014fe72d85534d67c43d95420076c725445101dde7388530044ff7659520014fc7298753006ef62d4b100467c7558f54286bf42d91520067f755963119e7e529875200cff7658231007ad5450920047766155051004fd75d91212a7d41018d10004fd768c5400076d54d4920014fc7654d52007f1708c710004ff735952000c7
  | 20 => 0x1cfc73d954100dee704c920026be6450b504ce7d74d954201cfc73d8941006de52d8d10004ef7258d10005f47158142006f421d85500467f7219542007b7648c510024fe749875008edc32d8d4000cfc7059351004fe7650950004fe7650d100069c64d8d100067e6154451004fd70d9153004ff7058b53004ff765075000cfe70d8d1001cfc73d9520004fd701855200cfe70d91521cebf4359351016ee62887100f6fa60d8131004ff7459531004ff745875301cfe76d8d52006ee65d8910005ed70885211aef541987540073c6555142006fb7058d10014ff70d8d20146ec21d9121004fc765055001fcf6254d32004fd765085119d7c7254e51006be62d911000cfe7058f521557e7054451005ef7254d52014fc725913143df671d8a41044fe75d923100cfe70d8d54006de32d8d10004fc7650910004fd76551321577410195100076d53d49200467e6519510024fe7458c51007d7734c510004fd74d8553004ff7458e21095ec7254550014fc72d8d50005dd739855200cfe7058d2113efa405824101c7d75d9153044ff7654510396bf43d81420067d5398752004ff70596211767f50597100477661d465100d7e7054f5000cfc7650510004ff7058e2125ddf73595431fede53d8d52006df634c510006dd638c750465df7359132005df73589100067d5358a51006ee72d854312eec215912100c7c76551501977a5058251025bf7555142004fc7158b503fcff764c6210067f65d8142006bc72d911010efa60d8231004fd7398750246bc54595430057d7550f50044fc7650b51006ed72d8e21006ed4218520024fc74d89512bcff71589100057c7558540015ee724c520007d7634c71000cfe70595320067c65d85324779c43d8943006ef7259710004ff705922100cfe70d89430467e65d4d200067c50d9541146bd42d91210457c70d5251006fb7059530046f45198752044fd72d8d52006f77159521006ef62d4941004fc768c52000cfc7058e51025be7414540006bd75d91101967f40d95100eebf40592210067c54d9520007bb7050d40005dd73d5132004ff7358752006dd54d8d1000cfc70595210467c7558754016ef6050920005f77158d200067e74d9521004fe71d954200cfe7059641004ff7459510004fd7690750006cf6318910006ef6518910004fd72d81540057c7558d2100cfe7098754024fe7418532004fd768c5501ef9c3150d4200df87055150004ff7650950006cf63d8910004ff7558e410067f6554d40005f4714ca4100cfc701855335f9d74d4d43004ff7359352044fd72d8152014fc725954301e7e63d4e51006be4259251044fe75d812100dec765092015e7d4219521004ff7259310004ff7654d100047f75591322feef20d8930025be749464101cfd7218532006bf6519110006f56118530006f4611
  | 21 => 0xd70d8d520467f53588514876f2019532044fd70d91501a6dc3158e51024fe74d9531024fe74d8d5110edd40d8d100467c51593510067e30d95420f6dc764c530006ee641895138e7d53d9530006dc6418d10404ff76506210067c65d854200dee76d4920015ec7254621026bc645515100cfc7098754004fd76d4e410067f65585320447c7558910006ef624c9410077b7054550055fb7058530005ef744ca21006bf64d8d1003fb7439051001dbe73d51430067c73d9521004fe7648530004fd72d95430067f65d4e214be7f4219542005ef72581313de7f7655350006bf6390541024fe7458b510467e65195324967f52d953201fdb6050d30024fc7458d10044fd721855222f9f4250d32044ff7654531004ff71583530067f6599520226f86058143017eb605092043ef54118542004ff7458f1019cff72d9521004ff74595213e6ef53d8951004ef7258754005f47159520024fc74d8d100057f7154e510477661d5251007af72551420f6df3058f10006df634c71002eef21d891019eec6258a51044fc76d49410067f65995210057f754cb1000cfc70d8554194fe7619510044ff76545210957e72d4550006f72118540004fc76505200067e52d9710006dc21d8d101fdde739855217eee62d89514eebd74d9543005bd74995301967f65945500067f65945300d6bf4358a4107dbe749953001cfc73d9521004fc7158f50004fe71d89500467e7019532006df6354d1000d7c70d51500067d53185520067f655531000cdc764c53000df4704c7100067d6594541006bf6450d5100cfe7018532005ef72595310067e761954212eec20d89410065c65d8d100457f7655352004ff7559120024ff76592210067e76195100def810582210067e3019521006bf6450d100d5bc74581210957c7254d500067f3019542004fd76d4a31015bc7650d4201cfe7398451026dc7650d304967c73d9532024fc745885110cde7618d10006ec74d8910026be6455231006bf7459540146ee62d8a4101cfe73d954113fb7649051026dec72585540957e7254d5000cfc705875210ff2708c710024fe769071048e7d43195320feee62d89310057f7454d500457c7548750014ff768c6210067c4319521026f66490710017e67188521004ff7159543046ec5258b50106be64d91310467c5258b500067c30d9521006bd6450851004fd74d9520004fc76945400467c5159353014fe7259231044fd73d8953004fd74d9621004fe769052000cff72d9520026de6450e31004fe764c9400463d74195420067f6555131006dd4358a3118dbc7458151014fc7258e5100cfe7018542006df638c520005ef7254631014fe72593530067f6594540024fe75583541567c3019510086ec21d8940004fe76d4a31024fc7418550004ff765513001cfc73596410057c7558132
  | 22 => 0x85400067d70d9542006ef628854001cfd70d913019e7c6294551056df31d8f1001cfd75d8153006dc72d8d10014fe72d9153006ed73d8951014fe7688710006bd6490631004ff7650d21006de30d8d2117eee75d8951106dd4358e41006de72d8d100067f21195101567c50185500067f65d8d420267e6455350276df3259543006f47159520044ff76d5310004ff7159352004fe76d5110236fa50d8153014ff7158b101c6df3158f510057c7559120024fc74d891025e7e54d8d540473c54551530467e721951000dbc76505402e76f54d4920006ec6418910014fe72d8d4001dde7350530014fe72d96311a67d53d9531006dd75d8d10024fe74d8950006df63d451000d7c76551500467f54987524957e7619532006ec40d8951005bd749853200ddc7050d300067c52d9510024ff76946413867d50d953001cfd74d8143196f8105825100cfc764851001f9f7450d30024fc74587530067f65d5130016ec6288530004ff764c550004fe7650930024fe7458353196fa60d825100cfc70d89534857e76d4d52004fd73d92210067f5458a51006ef72595213e6ec54d8951024fd72d8142007d7734c710005ef72585530067e42d9510004fd70d9152005df7350931024fc7458a31006ed64885210067f53d89500467c6355352006df6394510046de6554d3200cfe7098753024fe74d95301967c40d9510014fc7259130046f77158752044ff765954020cff725952019e7d71d95210467c5158f51004fd72d91310067f659971011ebf40d8d4100cfe7059221004f771595200457c755085100cfe76d813102eec32d89100473f74551520057f7558520036df31d8d102a5f6768c5100476f6254d520457c72d515000cfc70d95420067c659854213ebe20d9110024fe74d8d2023fcc7254d320467e711954201edc6350d5001dde73146314d67d43d954201cfc73d89510057f7154d50024fc74d8d52004fc7655310006ec64d8910006ec6318951005ef7258550016ec62509510deec10d891013ebd20d9110004fd70d95410067d651453100cfd7694710004fd73d9120007ad4350a210067c54d9510004fe76d531000cbc76505403be7f54d95400067e60195210447e75d85434c67e4019542024fe7458b5325ebf4159353004fd7650f503b67d50d9540024fc7458c51004ff7258753095ec7258550005dd73d51310075d534c8511757d75945501ef9c435894301cfc735824100efb61c4110026be6150e4101e7c63d4d5204eee32d8b10006f761945500467e731954200dde704c53036cff7459130006f721d8540126bd4059310006f7715912101cff7654e5100cfe7058b5401cfe7598753014fe76d452101e7c6354f5201e7e6354f52004ff735835128ebe76d514315f6c52145200ad7e7254f5019e7f72d9521004ff7158f50004f
  | 23 => 0x6dd431853203ebe64d9110005fb7050510006f77158d20004fd73d85404be6c21195420057f7558d42046f451587540075f6354d52004fe765053001cfc7358051006ee6018951044fc7558e411567e50185500067f6555132014ec7259510044fc764cb51006df6358910004fc7158353004ff7258351366df30d8d400067f65d4531004fe7654940227d87050d3019e7c32d95211557c7054451004fd71d8143004fd72d81431eedf31d8d42006f771591100067c10d95210067f6494551005ef725454105fb7439071001cfc7359350146ef2058a410067f65d4d10005f77154d51006bf64549100057c7550930006ef65d89104c67f765535228edf3158f540cedc6358d210967c52d895011f9f4050e31006f671d96411567c1019510044fc7558a310077b7054d5000cfc70d85430447c7558d2019e7e42d9521127f070505100067c321951010edd50d8d1000dfa70907104867e2019532004fd74d9631006df6388510004fc764c52001cfe73d8152006df54d8d1028e7c53d91530067e54596210267f76552510067f54185521ce7f76550510067f65d8910004fe7614530006bf648c5104ce7e20d9542004fe76d5120014fe72d8d2014edc31d9131014fc72582310067c64195104ce7d20d95423e7e451d89510067c62d9510014fe72d9110014ec7258753004fe76d493012eee32d89411967e509875019ef52198752006df7358d20024fe76d9110004fd7650d100457f7654f5000cfc701852026f6c7255152007d47150e3100cfc7098752024fe74d8d5048e7e3119532004fd76509100067f65505101beee3258b5100cf476505102e76c65d492019e7c52d9621006ec31d89510057f74545500067e52d9531007776550510006ed64d89100075f5350e5123f5f3254f52006df63d4d20005f771549411cebf4159351025be748c5403feef20d8532044fe75d9132006f721d8530006f56118540177787054550006ed6418910014fe72d8d51044fc7158e51004ff705953103ebc645911019eec2158a51004fd7318552004ff7650d520057c7558b100447e75d9221006de74d8d10005dd73d4531004fe768c540024fe74d96210067c31d9510255df735953211dbe7419631024fe7598754024fc7458f500067e64d953200cfe70d9121004fe71d954347ebd43d9132014fc7258354006dd634c851004ef72595314967c20d9532004fd72d9710005fb705495019e7f21d952111ebf4059231004fe764c950006ef64885210067f6554f10006ee73d891017eee42d8951015ec72d5120004fd76d5310004ff7058f54046df5358f500073f5450e510c4fd72d8b10024df7650e310467c50984512eef52118520006fb7058910004fd74d95321375e53d4d4101cfc7359352006dd6418d1001cfc731855400cfe7058851016ec628
  | 24 => 0xe32d95320076f754852015e7d201952100cfc70d8d5400cfe75987500ad7c7254f50136de63d8d410057d75d8a31004fd7318554006ef40d8951005df73589400467f7419542005ef725854024efa3058353006ed74d8910004fe76551100957c725455001cfe7358b50004ff7558a31006ec74d895115f7721195210467f60545500067e54d953201ebc7650d42004fc76905500067f65995101977410d9510004fd75d8143015ec724c521026f66450710004fe76885304eedc53d954314dde73d8a410467e76d4d52006bc7458d101a6f53198753324ff7459120014fe72582310067f71d953200dec7648520006bf74593100056c7550a2139eed42d8940037d4314c510005bf745812100df6704c51013ebf40d9110005f771589500057c7559132024fc7459521044ff76d5120014fe7259130025bf7350e41007b76450510014fc72d91300067f4019532024fe745952001cfe76d8d5401cff7658e21004fc7655121184ff7359531046fb50583530fedd3258e210475f7354d5249e7d31d95320075f5350d500067c6559110004ff764c8512e5ec754852001cfd70185300157c725535201cfe73d9710046de5358b5301edc638c550124fd7650510007bb70505400feec2158d212767f6555153004ff7259540006bf6450d214d67e41d9542004fe71d915300cfe76d8154004fd75d9131004fc7159542024fe74d8953004ff73590512767e53d8d544d76f42d9542014fe765052101cfe735911001cfd72d853215ef52118552014ec72595412279f3050d40005f4714c94101cfc7359310004fd765531000cfc70595411e6fa60d8142024fc7418530004fd76d4f100067f65d4710015ec7254d200047f75591104ed7f75551531aebc6459251024fe7458d200476f62d5152004fc71595320077751945210067c7558910004ff7358b500057f7550a3101d7d75d91530eebe64d9221016ee61d4a2125e7c64d4e510467e7119532004fd74185501957c7054e51004fd764cb10005ef72546410b6dc3158f50007777154e5128f5c53995430079f64d8d10014fe72593510467c5158f540067c6550d213e6ed65d4a21004fe7650d50004fc764c950006f731d8520046bf7459051026be6450f51004fd7654f10006ef624cb100467f7419510044fc76d5110006f7619855301cfe73d89104ce7d52d95420067c6319542044fc76d52310073f645515002dec7258d1000cff72d91200ceed3258a310467c655513142eed72d8542004fe7650d20004ff7650d1026f3d5255142024fd71d8d410f6dd3058f10026be645085113ebf649051001cfd74d8943004fe71d9530014fd73d95324967c72d953200cff76147100057f7454f504867d20195320067f73d95420467f7219521047766154c510073f5450d500bebc41593504bf3d7419542
  | 25 => 0x8a31046f77158754006dd43d8930004ff7655221006dd634cb5125f9f40d4d4317eec2158752004ff70590510267e64552510057f754c940014fc72d8151146ec6258a4111ebc6459231004ff7650f51004fd751854307dbc745853000cfe7058e41006ec73d8910004fd7655130044fc7650f51006ef42d89100067c655813201cfe73d952100cfe7058a51004ff7258c5115e7e201952120fea70d4920006bf64d4d100057f7454e513e6ef71d89510057d71d52510073d5450a51046dc5358f51007eb62c4110006bc65d91100a6bf43d91500067e75d8e21006df6350d21006ed43d8951006f7715891015d7e7255051005f471591200467e7319510007e862c4110005ed72945200deec60885210073f65d5143007b864c4110044fc7558e210467c52588514bd7e76d51524976c32d95320067c6558142046ec525885114ede63d8e41024fe7558b54004fd7694520004fd71d81540267e64550510467c731952149e7d53d9532025be74d4d41024fe7458f10004ff705925113dbc7050e410067d65146410057d7550d5216ebc4359051006df6350d504967c21d9532004fd7498753004ff7358851005ed7299510044fe76d95320079d43906310057e75d92213867f50d95300067e53596210a6bc41d915001dbe76d5143004fc7650d510057d75507500057c754ca41014fc72d85400065f65d8d10004fd71d9532004fd73d85524866f20195322f6f621d8520004bd74d8e21006be42592310057c7558d10016ee614ca21004ff7459530466ef20d8d42005f7714ca410aeec52d8152296ee2018520006ec62d8151007d863c411000cfe705953100d7c7054d50136dc315913117cff7259521005dd708c531014fc76549510076f6294551126fa60d814100df57690710004ff7258f500467c5098750004fd7650b10016ee6250b510067e61547502467e6454f500079f5350e410067c641952101cfc7359621006ed63189510deef30d8910006df63509103b67f50d9540006ef74d8910004fe76d4931014fe72d85432a4fe768c5101a6de4398753024fc76d454100cfe70592310067f65d5310004ff764c75011f9c5450e31005ef724c5210457e7550c514d67f40d9542004ff745952000cfc7059542015bc725514204eec6258b100e6de63d8e21006bd43d89401eede63d8d420057f7154f500247f7655251066dc31d8d200457e7550750046f45158753005df735493101edf618c53101ede634cb514cc7f765535201cfc73588510067f65d5131186dc6358d51006ef32d8954006f4411852049f5e43d95320057f7558540004fc7650d10005f4715495103fb441505101967c30d95100d6bc6459121047776194551006f761d4520024fe74d85520067c6154550436bc41d85430057d7550550006ed6250b51416f631d85324967
  | 26 => 0x14fe76d89410057d71d51500057f7155251067cc634c920014fc72d97100067c659052118ebc40d9151004fd70d8951015ec725822105fb4415071010edd71d8d10044fd70d8d50004fd75d8d410ad7c7254750014fc72d91534867e421953226eec2159352006ec6018951014fd75d81520457c75509511b6fa1058351044ff76d4a4113ebe70d911025f3e54d4d42006ec73d895101ebc6350d40004fe76d4d410057d71d4e51044fc76d4e210067e63d952101e9c6350d42036df315823101cfe7358352004fd75d8e212279d4050d30404ff71591210067f30d952135f3f5450f5022eec6250d514d67e74d95424975c73d9532004ff7458d21004fc7159540024fc7458b5000cfc70d893110fd6308c510046bf54593522767e635505100cfc7058b53044fe75d8b10006ef6250b100447c7558b1010edc70d8d103e5ee7550a211a6dc3258e51014fc7258f10004ff72593531fedf31d8d52014fc72d855028edf32d915315eec62145100063c6550d42006ed63d89101967e505825114edc6358e410deee40d891000df6704c71010edf50d8d10057d4314c710006ed6318910006ef621451001edc634c52100cfc73d81311567f3019510365df7359130006ed63885210076f7254550006bc6458d10024fc7418532036dc43d8d1049e7f31d953200df87048510006dc73591200c6fa60d812108dde739954016ebc64145100075f65d4d4300cfe705913201cff764c52101cfc73d85540067c658c521006bf74595100467c6514540004fc76485400077461545503e76f53d4a2112cfd74d9221044fc7559120024fe7558f54336bf42d912001ebc6350d42004ff70588511ad7f765525101cfe7359310005df7358142006de3058f5100cfd769071001cfc73d8940004ff7650d50004ff7458a51004ff7654930004fd73d8b100067f65d4d42004fe7650910254ff73595324be7d21195420467f7319532004fd73d931028f3c53d514323cff7259532194fe7614510024fc7458251024fe74d8b10004fd72d8530025be744c540166dc631451003dbc7458910036dc6358d10004df735891001edc6350d514ccfe76195420f6fa10d8131206bf43d9152004ff7458251006ef75d8951004fd76d511003ebc54d911046eec21d9132006ec30d89510067e73d95210477771545500057f73553520ddec7050a21004fd7694540005bf7355142004ff7458b10026bc6450531006f76198552004fd70d9132004ff745875023fcf2054d320467f6255152006f61018552014fc72d8d540057d70945510057f7454750024fe76d9120004ff7558910116ee3258a31004fd74d89104577610d4651015ec7254d5201cfc7558753004fd76d4a4100cfe70592510a6bc42d9150026de6450d32006df6354d52036dc53d8d10006dd43d8132116ee62d
  | 27 => 0xe7190541006bc62d9110024fe74d8e210475c6354f5200cff73d95301567e4019510004ff7359350004fd71d952001cfe7358b54006ee63189100c4ff705891001cfc7654d514be7f2019542046f75198753006bd431854001ede6354e410067f7558d2100c7d75d89500f4fd764c51000cfe70d8552006f410d85520467c75593531a75f3254e510467c65145100467f6254d52024fe76d45410176e75d4a210467c65d4531014fd76946210deed30d89100467c65d513123ddd7399532014fe725963100cfc70d85321ccff76546410067c32d9510174fd7699710014fd70d8520044fe71d95100067c64d95104ce7e72d95424967e21d953215d7e7254451274fd76995431ef9f3050d42006f410185420057f754c950026be64907502775c5358d54005bf7458151006f77158d101ff5c6354d52004fd73d8121144ff72d9121044fe76d95300067f65d51321967c10d95100467d711952115e6f2019521004ff7458c51006bf6450510017af7450a21005bd74d8e210067f40195211967c505825100cfc70d911000cfe764c510005bf7454541046dc5358f5408f9f3250d400057f754cb512467e6454c51006bc31d91100067c6419532506bf54d8d540457f765535001e7c7654d50014fe72d8d500067f53d815226eef20d89540447c7559132004fd70d8943014fe764c521014fe729875428f9f30d5143026bf619054101cfe73d895001dde718c53100c7c7654d50004fd72185300067d651952140cfe7690531026bc645515019e7f42d952114f9e6350e41004fd7688540006ec72595431f4ff7059520006df735951000cfd73d9130106bf4059131004fc764c910004ff7159353014fc72597104d67c40d95424cf3c42d95420057c754c94100cfc7058f520057f7558d100067c60d9532005bf7458d2048e7c31195324d73f43d954200cfc7059121024fe74d8121024fc74d9520006dd73d962101fd7618c53110fd810d8d1017eef21d895135f5f5350f50004fc7694530024ff7614641015ec7254520004fd70d9631006ed6254a51004fd75d894000dec764c920024fc74596210067f4219510006f72118550024fd75d81540067c4019532026df7650e310067f651853201cfe76d8d200057f75591210057e759854214ebd43d9131006df638c55001dde75d4d430157e7254d5200dfa7094710006be43593500057f754ca51024fe74d8530015ec7255221024fe7458910005dd7390631004fc765095026dbd74995420077865c4110004ff7655121006be42d9110116ec2158a313e7e571d4a21014fc74d894001cfc73d8910006bd649053101f5e75d4d43004fe76485504bf6c211954217e7f5259621006bc52d91100467c72195321acfd74d954114f9c3150e411e6fa40d81420067f21d951016df671d964103dbc7459510
  | 28 => 0xc5211567d301951015d6c7254451014fc72d8131004ff7650c51024fc7158e414ce7e42d9542005ed728c621005ef7259541046bc765514201cff70d9530005f77150931004fe71d8d520067e76195214be7c4219542206bf41d9152004fd7098754005ed74d4a21014bc765514215f6c2119521044fc76d51300467c655531001ebe6350d400067f6559110005f47154d51046f8505835100cfc70591320076c7550a211767c76545502a7d61018d100067f6558d42006df735891001ddc7354931014fc72d9151005f77154a4101cfe73582411df9c4150d320067c65591320067d65552311ae7d54d95410467c65d4d21016ec62549510067c7558d21025be74d4541007ad4350920046f45158752004fd71d8d201d7e8704c9200467e74195320047d75d854326eec62589544c67f431954201cff7658d20115ec7254631186de53d8d5101fcf6250d320057f7558930026f66490510005df735815112ebf4259221006ec10d8951024fc7458d211ddbc7458132004fd7650a31044fe76d95214947e761953210fd6308c710014dc7650d32004fd75d9120156f81058051004ff745822100cfc70d9621026de6450d30005ed71d4a21024fc7558f54006de62d8d10004fd71d91530079f5450d30044fc76d4b10006ef32d89100a6be54d9150006de30d8d42186de43d8d51004ff7358b100067e101954201cfe7650531004fd73d912100cfe70d9153004ff7650851024fd71d89410467e6514631004fd75d8d42004ff7158b544c67c4119542026bc645513035ebe6550d42024fc74d8950006de73d9621004fe76d51310067e40d952101dde73d4531175f57199510044fe75d8d20004fd76d5132004fd71d895400cfc70d95320057d71d4d50004ff745953233eed72d95200067d651954010ef81058231004fd76d5221005bf7458d10015be72551420057f755853210dde7050e310467e7019542006f41018532014fc7298750004fd73d81520157e7255352004fc7654d42005f7735051000cfc70d915300cfe76d8143015dc7650d3210ede30d8f100077771552510157c72d51520067f65d8121004fd7518542004fd74d8d5200dbe7050d4001cfe7359351005df735912000cfe705952101cfc73d85400057c755912100d7c7054f50004fe764c5400057f7558943006be63191100057f7155150014fe72d8554026dc6450d300067c6558d1001e7e6354c5112dec7258141006f671d92312467c5459543005ef744c920136df3059131024fe7458750044ff76d4e21006f74118520014fe72185300075c6550d3216ebf4059051014fe72d9130006bf64d891000cff72d8d2041cff7650631044fe75d853001cbf7650e41015be7250d420eeed42d89414d67d41d954217eec32d89510457f7354c51006ee63d8910006ef75d8910025b
  | 29 => 0x4ff73596414847e76d4d5219d7c7255251004fc7158d2015e7e42195210cedc6348510024fc74d8552006bf65d9110005bd74985520deec20582210079f6450d320047d75d9221006fb7059520005f4715815200cfe70d9532004fd72d85400067e52d95410467f62d51520467c72195214cf3c74d95420067c4019521004ff76485400467f5058754014ec7258d10005f7714c9410e7ce434ca210467e7019521024fc7498750006ed65d8910046dd5358b530057f754853025e7e54593530067f755953101edc6354d52004fd73d9521044ff7654541014fc7259110006ed65189100067f32195100079f6350d40006bd651911001cfc73d97104cf6f20d95420067c6319521044fe75d931005ebe64d9310004df73595200f4fd73d8f10024fc7458b51014fc73d89300477771547503f4fe7690521436f641d854300d7c7654d5031def7259120024fe749845117eec6258951006f671d963100cfc7058b54046bc545905101cfe7359621006f56118543044fc76d531011ddf7650e3100dea70d492025e7e64d4e5100cfc70d9541006fb7059120007d4614c530007d5438c51001e7e63d4d500c6fa20d81210467e6519710015ef734ca2110edf70d8d10264fd7699540004fd74d8532006bf745912001cfe76d8d42006bf73d91101a6df3058e5113ebc30d91100057c75585320057f7454d52004ff7358a41024fc7558b54006dd6518d10005f7715515104dfb7058520006df6350d10005ef7448520046ec5258b5401ede6354e51147e42190521356ed32d893000cfe70d9221145ec72546410157c7254d52296f51018520004ff72593502c5f7764c710017e661d4a210076f7254750004fe76549101f6fa20d815200cfe70185520076c6588521006bf74592214967d42d9532004ff7159120046bc6555142005bf744c941007d7639051048e7c3019532015bc765514228f9f32d51430067f70d9542006ef52582210067e71d9542007747154e5100cf576907100067e6319510004fd75d8d210467c6554d41004fd75d8931004fc7650e21004fd71d9132004ff7458351006dd6350f5113fb410d91100dfe610d891025f9c54d4d4310fd7638c510014ff73d95321e7e870509200267e6455352006ef725953109ede435835301cff764c510005ed7448520006be65d91100067e73d954200cfd72d952001cfe73987540067e5259631297e61018910006ef63d89511a7d731946310067d71d95422b7b610191100adfb7059520024fc74587524d67d40d954201cfe735952001cfc73d89500fdec7258131004fd75d92310067f74d9510007f131c4110014fd74d814201cfe755835314edc3158e41004ff72596411debc40d9132004fd76d512026cff72595424be7f32195420ae7c52d815201cfc73d9121005f5748c510117e4218
  | 30 => 0xf20d891017eec625451007ebc41d9130044fe75185401957e70552514f67f54d9543004fd71d954318ebc6454510014fe725954301cfe73d9510004ff7359510024fc74d8e21025be75d51430067f7559121005f5748c7100cddc73581212779c43595430057c7558520206be54d915200df87054d50044fc76145300477b60551502467e6454f52005be71d5143024fc74d81531ef9c6350d42014ec7259531004fd7418520004fe7654b100057f7155350004fd7650e21005e571d4a21056dc6358f100047f7558d21004fe76d5221006fb70595100259e74d4d4301cfc735912013efa60d82410efae6450a211967f30d951000cfe705962149e7e30d9532014fc72d915000cfc7558f50006f671d9221044fc7558a4135edf65d4d430467c6554f100467f505875301cfc765453101cfe73d8542004ff76545200057f754cb50024fe7458e51007db704c530004fc76549400957c725515007f3e54d5130186dc635451007ebc6459130004ff72595410467d7019532004fe71d9132005df7358950044fe75d8131014fc7158e210067f6554d4101cfc73d852025f9c41d4d43176f71058750005dd70d4d4300cfe70d8d410067c31d954222eec52d8943005dd744c530166dc4358c510065c6550d32004ed72d8543234fd7699530004ff764c54000cfe709875215776101951049e7c43d9532004ff76551310067f6514520436dd73d85430067f651452100cfc70d8951017e6614ca2110ede20d8d100057c7558131046f451987540073c6550d4216ef54118554004fc7688540015ee7250e21006ed73d89101867d5359631006ed32582210067c6550521044fe75d8d102c4ff764c7100067c3119521005f7735071041ef631d85430057e75d8543006f76198543286ee4258b54006ef62485100d6bc40d91210069f64d8d10004fd7018543004fc7159352004ff705953235ede6550d32006df6350f10016ec62485100473c6455352014fe7258051014fe755935200cfe70d8d5209f5f3254d5010edd20d8d100d6bc644851005dfb70585402a6f51018530004fd72d8554025be741464126f3f425535200cfd75d8d50044fc7650f520079d43509301679c4350c51006f671d8b10005f47158132246bf4259543006ee2058b5100cfc70587531e4fd74d912013ebe60905410ddee70d4a210fdec72595312eeee421852000d7d75d8950006f771595412eeec52185200067c30d9542006de3058f5435ebf65d5143046dc5358c51006bf7459132046f751987520067d73d9521004ff7058752004fd71d9120044fc76d4f10014fe72d9510014fe755835249e7e73d95322767c6355150004fc7648530004ff7458352004fd73d9152014fc72d953019e7f32d9521005bd74146412073c64551520467c72195100476f62551520057f7558931
  | 31 => 0x875400cfc70d8e210b75f3254f50005ef7258d54076ec21d89300067f65145100467e6594710046f850583520279f7350d401afb44194541004fc764ca51015ee72146210477661d4e51006df6418d1000cfd7218520135dc73581410067d65946212467c54d91530defa60d8221024fc74d9621006f77159520004fc7654a41004dd73d9221406f621d854219d7e761952140cfe71d9231044fd72d91520deee20d8b10196fa5058251024fc74d95212a6df6118d10024fe76d9131004fd76d4d10014ff7614621004ff735875401cfe7358354006df6354910014fc721855000cfe755935006ebc645912000cfe70595420deee50d89101967e40d9510005bf7550d42006ec63d8910004fd75d931001e7c6354d50006de64d8d10006ec6318910006bd4318542004ff70591320067d515805110edf638c510007d5438c7100467e741954201cfe7359541004fd73d8910004fd72d8d10006bc6319110014fd7158b10024fc7458a510067f65d4541024fd701854019e7e529845115eec52185520477b6054d5022f9f3250d422767e53593530067c6548510046fb70583541afb74194641014fe76d89530056c75509201a7d4319453101f9f7450d324c67e43195420067e5218550046bf545935300cfc7558b5000cfe70d855401cfc73d8154004fd701854201c7c7559353004fd72d91101fede4358b53046ec5258b5309edc31d8d50014fe72987531f6ef2058b502775e535513207ebc42d913028cff74595434975e32d95322a7d57118d104c67f4119542006bf21d91100057c7558931006dc75d8d100067d6594631024fc74d97100467c65d4710024fe74d97100067d5418550006ed70d8951024fe7458753005bf7458910014fe7258753044fe76887504cf6c42d9542015ec72d4621014fc7258754006ef30d8951004fd7298750295f671d8b10024bc7458d202aef67690510007b564907100057c7558d420a6bf43583540067c70d95424867f211953201ef6634c5100067f42d951001ddf7450d3001cfd72d8132046fb7058353006bf7458d2022eef205913201d9e73d51431947f765475037ebf43d9130044fd71d8151024fc74595320067d6519510006ef62545100447c7558d10246be54d9153024fc7458b530077b65c41102e7e970d4920005f77159520006de30d8d5201cfd75d895323dec725855314edf30d91314aedd43d8d42024fe7418553044fe751853045f5e5454d320067c6558542004fc768c5500457c70d4651004fe71d95322767c635525113ef86058241044fc7558231026bc6450d51076ee32d893001cfd71d8131004fe71d9120005df7358141006bf6450521005fb704c510245dd7399543014fe72d8d41174fd76545102473e54d91530057f7355251014fc721855322fcf2050d321ae7d54984510dee
  | 32 => 0x134fd74d923112fe42150521024bc7459510126bf4059310004fe76d494001f5f7554d32004fd74d971001ede638c75001cfe76d8d10044fc7158a5100cfc70591310467e701951000cfc76551500447c7558d210467d72195420057c755091038e7f53d953000cfc755935000cfc70d95100477b60d4550004fc7158f52004fc76549410457c70d4e5144fe45118951006ef43d8910046df7358f541bcff765462119cfd72d9521004f47158d2018cfd76545410067c7559121004fe76d4941016ec62885500467e6554e41005ef7259710006df73591312463e54d9153004fc7654d41007d763505100057f755813100cfd73d85301a4ff73d95314ce7c32d9542014fc72d96410073d645525119f6c5294621006bc75d9110004fe7650951005f771581520075f5350d521b4ff7654710306df30d8d2001cfc73d911023eef2058f520467c65d45411a67d5398451106bc40d9131176fa50d81510deec50d891012dec72545410057d75d92210073f6455152027af6255142006dd74d8d10044fc7650f50006ec41d89100057e75985321c4ff715953100cfe7058e51004ff76509510067d65d52310067f65d8532014fe72d81410057d758c5500057c7558d20236df3058f50004fd71d81520067f65d4d40004fd749875000dec705092000cfc70593521acfe76145410f7d7304c510044fc755911033d7f7554950004ff705954200dec7048520006ef42d89512775e53d8d540467c65d5310014fc72595302d6f7764c71002eee3258221004ff75591321567f20195103b4fe7619540026ee6450920026be6450d200467e651453100cfc705925101cfc73d9621004fd74d8f10006ee40d895100cfe70d893107f9c6450d300467f7119532044fe75d89410467c65545100467d7319532126f860581410067c30195211567e5058051004fd70185323a5fb7058d40294fe71d8b10006bd6490710176f8605815117df5719952101e7c6354e51005f970d4510004ff7059541024bc74589104867c3219532134ff7359131004fd70d893103ebe76191103e6ec51d89510075f6554d320073f5450d52044fd71597100067c74d9521004fd72d8553006be72d9110006df639051000cfc72d8121006ef64d8910014fc725835100cfc7018552007e4714ca21006bd4358241004ff764c940006bc32d91102657d74d5150044fc76d4930026f66450510004fc7159543006ef6418910004f7715912013ebc10d91102b6bf61191102a5f671d8f100057f7355150004fe7650e210467f5058f540267e6455152116ec21d8d21004fc7158b5400df67090510364ff73591300deee10d89100e7ce534ca21005dd739453049f6f32d95320067c1019532004fe71d89430ddec704ca21016ee6150a21296ef61189100067f6558d100e6dc5358e210247c755
  | 33 => 0xc4350d21014fe72d9150014fe72583530457f7654c510475c5354d51006ed72d96214f67d54d95430467f539875201cfe7318520006df63d4d104876c21195320067f531855201cfc735891040ef53118543006dc65d8d100067f32d9510006ef628853000df67090710024fe74588510067e64d9521006bc6150540016ec624871010ede30582310067c41195102765e53d8d54004fd72d813128e7c63d5150004fd70d9543014fd70d8d20006ef63885210067c52d9540004fd74d813215cfe71d962100dfa7014710006ef62d49310467f5198451024fe71d9110044fe75d913000cfe70d9510005ef7259153006f410d85320477b60d5150024fe749875214edc3258e41006ec72591100457c72d4651015ec7255120005df744c530004fd764cb510ad7c7255350046df5358f51004fc7654f1022eec6258943005ef725453013cff74591102e6ed65d4920035f970985300279f63d51430976c52885500067e75d854319e7d72d95210067f6599532004fd75d85420467c7319510004ff7654d420067d5498750026f4649071001cfe73987520067c65d911022fcc7250d32005bf7459510004ff7690750136de43d8d41014fd74d85420067d6519531026be6490631004fd76d49300067f72d9510044ff76d5121076ec6258930014fc725835349e7d43d9532007b47150e41014fd74d8d421967d30d9510006bf75d9110044fc76d5221005bf7458131014fc72d9231004fd768c75018cff7459541004ef72595430067e50d952101edc6350c5100cfc7058b51014ff70d95200067f74d953228f9e73d5143005bd74d4d42006bf7459110024fc74d8d51384fe76195302e5ee7550920004ff70595430067e63d9510004fe764c52000cfe70d913110edd70d8d100067f659963101cfd75d9153024fe7458d211567e101951000cfe7018520044ff76d5131006bf6450531046dc7654d321af3f425525100dfa7094550044fc761463115eef205885106ebc41d9120005f5744c5100467d7219521007f3704c5100d73e54d5121014fc7218530005df73545310e6dc4358e2135ebe6550e410067e60d9542046bf5459351004fe7654d201c4ff7654631005ed73485202b6bc401854000dfa7088710024fd73d954319d7e72552511ae7f54d9541006ee20d89412467e5458f54004fd7690520004fe764c95100d7c70d45500047f7558d100467e65195210473c54551520067f7559120004ff7654a310067c6319510004fd76d4e21024ff765052123cfd7699532014dc7654d32016ec62d493102eec42d8910007af7250d420057d75885502a4fe71d8f10004fc764c9410067d53185500067f655452110edf40d8d10006fb70591300067e5298750004ff7654d40005f97090710005f77158940176fa10d815100df4764c510004fd7398752
  | 34 => 0x4d210067c601954200cfc7059051006ec70d89510457f715455010edc40d8d100457e759055019e7c42d952111f9f4250e3100cfc7058c5148e7f301953223eee62d89530057f735535019f7421d952128e7c63d52510457c72d455023fcc2154d3200cfe70d85532467e6454d522bcff7648710006bf6450f10006dd6350d2001dde73145300467d731951000cff7658241004fd74d8d51046ec5258b511beee4258b51086ee42d8940005df73595100e6ed32d893101cfc7559353014fc7298754006bf7459543186df31d8d51066de63d8d200467f5259353044fe75d854314f9f3050e41004fc7654e21004fd72d95401d6fa30d81320467c7558b500467e6594641046f45198750004fd73d91510a73f42551500c6f860581210067d53987500067c10d95420476f62d4d520447e75d8e2101cfe73d895100cfc7059543004fd73d95421879c4350d510467d70195210057c7550b101c5f77159531005ed71d49200f7d5304c510265bd74995401977610d95100076c62945510467c505805101cfe7359542004fd73d9641006ec7259710014ff7658b10435f77158d4101cfc7359351014fe76d894310fda30582312767c53d8d54044ff76595300273e75d51434967e20d9532014fe7258f10004fd7654b100457e75d8d5423f5f5254d320957e72551502eeef211852001cfe73d952015e7f2119521006bc7458910027b771505402e76f53d4920044fc7558f10006f970d9710004ff705935301cfe7558b53005ed72d85430067c50d95210067e72d9510004fd76551310067c4219510006ef42d8953014ff7654a51005f7748c510017af74509200263e64552510067f43d95210c6ef2058b102357d73d4d500feec20d89310176e75d4920005dd7550d32044fc7558910014fe76d89510067e10d95214967d20d9532004fd70d953201ddc7355153235dd73995300cedc30d8d21006bd6450b513f6f52118542024fe76d9153007db7050d30006dc54d8d104976f20d953240f9c4318543024fc74d8151014fe72d9120004ff764cb50014ff7690621014fe7259710006ef32d895108ede43d8d400067f43195100057e75d8a410057f7558b10005ef7258141004fe7655310014fe72d85500067c61d4550004fc764cb100467e6594621006ef7258d2100cfe70591310067f70d9532006df6354d51006dd435823100d7c70d4d500976e52d8950004fe7654d1019e7c5258a510057c75581410067e52d95430feec625893101cfe73d81540067c41d95210067c52d9530006bf6455150004fd73d951020eef20d8950044fc7558221005dd73d922101ebe6350d42004bf7458d1001cfc7359121004fe764c94101cfc74d8d400f7d7304c7100467e651963101cfe768c62100d7e7055150006df6350d520057d759854201cfc73987500cf9
  | 35 => 0x67f6599540006dd73d9631046f45198451026ec6450a2101cfe73583511aebc42592510267e64d51520076c7548520024fc74d8d21024bc74595200457f7455150004ff7258e510057d758875008ede53d8d400067f65d854201edf604c530026bc6450e210467f51987500076c754ca21005f47154931004ff7259510024fe7418520006df6350510007bb64c41104be7d321954200cfd72d8d20006ef41d891001cfc73583520076c755092003ebf42d9110005f77158930014fc72d9131005df7150e310467e6519543005dd7314631005ed728c5200067f654851001cfe768c71000cfe76d81530057d75d854349e7e31d95320076c725455009edc32d8d500067f30d9542044fe75d9221127b54050510226fa60d8143004fe76505500cf5e53d4d21004fd7418553194ff70d9510007ac64d89104ee7d53d95430467d72195321af3e6455251006ee43d8910036de71d8d100057d758c750004fd73d8554004ff7459631004fd72d8141005bf7150d400067c5359621004fd76d513028f1c53d5143184fd76d4631004ff7654b10007ad6450a214967d72d9532005ed74d492046cff745913201cfc73d8550024fe74d815201cfe7359352006df7359543004ff7259110004fd72d9530024fe74d815301cfc73d9310046df5358f54024fe749875301cfe73d8520006ee54d8910006ef62581511aebc4159251007cc63d8910027b66150e4100cfc7058e2101edc6350d21046bc545935228e7e5358f5425ebc54d8d542d6de4318530046f75158750006f561185500967e5258352004fd7694530096ee62d895000df47090510024fc74595314be7c20195420eebc415922119e7f20d95210073f6555142006ef73d89510279f7350d42024fd71d8141004fe7655231024fc74d81520057f735445100cfe7058752047775155251004fd70d8d42015dc7654d32044fe75d91100067d54583520079c6418d10007cc6318910004fe7650d21006ef70d8951015ec725515200d7e70553501a67f53d9531306dd30d8d203feec21d85320457e75885500067f7559510004fc7654d1007ebe54d91300067e73d9510044fc76d49400467e6519542004fe71d8930004fd73185501557c70550510067f5418550006dc52d8d100267c6455150005df7358520006de42d8d10004fd74d8b10046dc5358f52005f5744c710186de63d8d512d6f531185300a5bc745855025f5c54d4d430b6df3258f5015e7c521855203dbc7458d101a4fe761953113ebf30d911000cfc7059621024fc74d81320467c7019510004fd74d852015e7c3219521114ff72d8d210067c10195210067f75591320467c6594520004fe7650f10014fc7259350006bf72d91100467f5498451266fa40d8154014fc75593520467f605515028f5e53d513201ef4634c510004fd76d
  | 36 => 0xc765515125f9f42d4d43024fd70d89400057e75d8e21004ff7159130044ff76d4a310067d535835200dee70d4920044fe75d91200ddee76189100076c65189104d67e40d95420073c6519110004fd74d8121024fc7654541027bb6050d40004ff755911005ebc64593100067f65d91210467f549875001cfc73d9130295ee76d8910044fc76d4d4101ede6350f5100cfc70592212b5be76d91100067f41195100057d76d4e510067f40d95320067f65985422767d75d8d54024ff7159310024fe74d9631014fc72d8154067ce434c9200067c52d9710005f77154951007e47150a2131cff7259120006f970d8b10044fd741855400cfe7059351004fe76552212467c6454d5001cfc735954205fb66490710014fe76d8940004ff7258251026be6490531005ee7618951004ff735925104eec52d8b101d4ff7058d2000cfc70d9132026dc7650d3208f9c6350d4000df6705051017eef20d8951014fc72d9543004fd71d9540126bc765054014edf3058e412a5de76d8d100075c6518d100467f5258f540467f6054d50024fc74987530067f6559121144ff7459121024fe7458d1015cfe7694521026dc6450d3200cfc70d8d42024fe74d8931004fd7650d21005f77158142014fe76d893000cfc70d95210067f6554510006fb70595400067e6019532004fe71d952004eee42d8b1001ede6150e310257d75d8d540f7d5304c7100267c7655152004fd70d9221005f77154e51006f731185200af6c52887500067c7558d20006f461d452035ede6550e31006bf6458d100075d6354e51006bf64145103c57e76d4d50015ee728c621004ef7259710004ff7558e21046dc6554d321967f20d9510046f7515965101cfe7358a510457f76547500067e5258251004fd70d8941004fd74d8153046bf545935012cfd76505214ce7f21d9542007775194531005f7744c510004fd71d8d50004fd7688750004fc7650a31024fc74d96310457c754c851134fd7650531005f7748c710014fe7258c51004fd7614520014fc72d8153006be40d9151026bc64551520057f754ca41006df63d89100deee60885210067f65d4f1001ebf7650e41004fd72987543eef5211853213ebc70d9110006f61018542006be43d9120004ff7059641006f42118530006dc62d8d100067e4019532014fe72d8143026dc6450e31014fe729875027dbf74595401a5f67119631044fc7558d20004fc7655130024fe74d9532004fd70d85420067d5458251014fe72595310076f7255152017cf734ca21015ef734c92001e9c6350d404bf3e4219542004ff7558221006df7359110007ac6418910015de7254d32014fc7259510005fb7054d504967d52d953200cfc764c510316df32d8d204867f4219532005ef72545211aebf4359251025be7454d420076f65d49201bdf77159521
  | 37 => 0x95100067f30195212279f4050d30006ef64d895126eee52d8954004fd73d95411967e6094551005f970887100475f7354c5112eee42d894101cfc73d9152015ec7250521006f6101853201ef4764c510006ed72d854313ebc4058241005f47154a5112eec52d8941004fd75d8943005fb7054510006be74d8e21006f431d852014f9f3250e414be7e3219542006ec7259531006be63d9110015ee7214520004fe7694540006df73595200457e75907502b6f51018540007b76150540014fd73d9132005dd72d4d43004fe7654530014fe72d9710046ef7258b51004ff76553100467f60d455000cfd73d95300057c7550931014fc72d9310004fe76d4a410067d535825101edc6350d52044fe75d91310467c65552210067f65d9110006f56118520005bd7499510005ed729062101cfe735905126faf205514226f6f2055352006f4615455001ef4634c710044ff76d4f10044fe75d813201cfc73d8b10004ff7258754004fd7690550006df74d8d1027efa40583540eebf43d9221024ff765525100cfe70d9621004fd764ca51164fe71d96310457e7550f52127b5405071010ede70d8d10014fe72d81512cdf771591101a4fd73d953113ebd30d91100079d43905301c6dc3058f51466ec21d8d421967e10d9510004fd71d894301cfd74d954300ddc7650d3003df97098540007e7714ca210dfea205822101cfe731854246ebf42d913200cfc70d9543035dc7358910014fc7258753004fd709875348e7d30195320067e43d952101ede6350e514cf3f74d95421c67d75d8553007b46150540044fd72d85520067c52d9531006de65d8d100067e4319510006dc7359510275bd7499543005ef7250f52007d7614c530006ee53d8910006ee50d895113ff2709071010fd410d8d102775c53595432eef62118520026be64907100e6de43d8e21014fe7258f500ad7e7255350004fd71d8153024fc7458f52015ec72d4e21044ff76d4d104866c2119532026f46450710006ed64d8951007cd534ca2114cff73d913101cfc73595200bf3f42553500073d54508510067c70d95211967c70d9510005ef714ca21004fc7650d21004fd72d8d41026bc6450d500473f74550513e5ec7550a21004fd7650f10246bc6459153024fc74d954023f5f3254d52226fa30d8143047775154e51026f4649051001cfc73d8552015ee7250d200067f41d9521005df7359520015ee7294621004fd764c91001cfc73d81510067c63d95100067f5358a510467e7219542017e66150a210457f7654451004fe7654d4000df47090710006ec75d891001cfc735835100cfc7058a51004fd71d8940044fc76d51310057f7550851006ef74d8951004bf7458910004fd71d8930004ff7258d101f6fa60d81520067e54d95210076c65d8910006ed4258221124ff7059110024f
  | 38 => 0x17eec42d8951006f721d8550004ff7458b51004ff765494101cfc73592210067f5158251007e4624c510004fc764ca41007775194621004ff7458752024fc74d853215df671d962114dbf7650e41006ef62d49100157c7255152024fd70d95400def86058221044fc75592211557e7054c51044fc764c85121ebc64d4910146bf42d91214ce7f32d9542016ec62d4910014fc7258750146ec2158a412b5f671d9310044fe75185420067c63d95420057d7550c510deef10d89100a5bc7458950004fd72185540467f60d515017eee7618951046df7358f52004fd75d8d20185dc73581510067d6519621004ff7655110004fc764c550296ef60189104875c321953200cf4764c510004ff73596212b6bf6019110004ff7654d204be7c211954201cfe76d8d400dcff70d89100067f74d9521005df7358152004ff7458d2000cfe70d923124edf30d8d500076c725475000df6705071000cfe709845149e7f53d9532004fd72d9541006ef7259532004ff7458f50004fe71d9152037d4634c5101d6fa20d8132006bf32d91101379c43585430067d73d951001ddc7350931014fc7259641004fe765512104677519875015e7f4219521005dd7398542044fd71d9151006bd43d814201cfc7159231024fc74d8f10216dc63d4910006ef43d8951014fe72591100056c754ca21004ff7158f540447e76d95422767e635535029ef6768c510406ef20d8542025bc74545410067d65147100057d74d4e51046f85058051006be43592210067c42d9510006ef63189510057f7548510024fc745875010edc30d8f102a6df6018d100067f655813200dfa76c41100047f7559121067ce534c920006dc74d8d100067f43d95101aebe545925100777615455008ede63d8d40046df5358c510f6f86058131004fd7655110006dc7359110014fc71582210067c54d9532004fd73d81413e5ee754ca21004ff75592310467f721951000cfc7158b10004ff7058c51044fe76d9531004fd7650d200067f73d9510014fe7258e41014fe72d9531046df7358f510057f75509300467c6514530044fc76d4910006dd638c6214867f32195321567d1019510005f7744c7101ccff71595410057c7558943004ff72595310147c7655152015dc7254d3230dfb7058d20006de73d92210067e631952101cfd72d9132014fe72d931019df67119621004fd72d8f1001cfe76d453100cfc76549500457e758875001dde7390631014fc7259231044fd71d8d51006df7359132015ec72d4520206be64d91520deef70d8910004ff7654a41026f47650510004fc7654d210047f7558b1000cff7690710004ff7559221006bd6450b50494fe7619532044fe76d954310fd4308c51001cfc73d91200247d75d8d54006df65d8d102c5f77158d10044fc7650c510067c41d95101967e70d
  | 39 => 0x3d001402806b12400e40080c601e800000600e4fb21f004e01d006001c00e00a000001003e02308700e401000c002807c02a00000b040c00400100300a800202400300b0144005019805800400e00701400020a602e81440b000c00100006a800000100e443201900780d00000010158098000018177806005402301480ec052019005003401a00d00900000020c436c84a418800f00d139c0080a2004806808009a00a017801602c025002c014001019006005a002000002806c032000000400000607b02e8008010003002c06a0050000014008004001001400e0010000c3400000e0198e093c607c000801c16000100001b083600000180b8048608000002801201e00800800001df08f806c038021005817403a046002802007e000006800004002c00806640060000220008072153008003804c003000063801009c002809801a000002801000e005001801802e0c400000cc00003e00000dc16e0f400000b80ae00000314100060001ca800000201c0050b0821a022000013400a0050220068000005011000400004d00000900cc000000008400000d000000c008000002800402c00000000ec00000c000003000400000180240011060170000014005000004000e000009000c00400a00c80780000000038028006029011800405e000003803c00e027009002000a2eb0008854010000002000000003501e800001e0080028024000194071817009e33900000501f8007013006c022037006000002201a01d800001c0c713c000004400000080a0b8619c00001a801400001e804c03b5a702c80a0048000000000072c000000001802800300e000c00600c072800808e0f8006802c0000c50000204a6400012f00040a0000017800401c00102900500de001000000007802b04e000001c00000380c000000a014000000c00505a800000c02518c80400560040cb00100ce00e01e81180940000030000016005002800005400402000c401806f00c802c01604b0010000000be500000000020070000cf400a03401080101ae0120238008000011009004400e27001edf6254d324967e72d95320467d74195210057d74d4d5019f6c52945204ce7f42d954214cff7459131024fc74d8930046bf745935307f9c5450d300bebc4359350044fc7558b100057f75581412cdf776507104967e42d9532005ef7350a2128edc3058f540079d434c940004fc7650d5200dbc705054000d7e70545504c67d40195420077b7055150004fe768855023eef20d89530457c72d4e510267c64d51500467f545835201ddf714c53013fb610d91100067e53d952116ebf425905101cfd70d9530004ff764cb5134ede43d81320ddec70d4a2135ebc6550d42224ff70591300067c40d9532006f56118542236fa30d8153007b4644c5104875d7319532004fc7650930
  | 40 => 0x1002b005800405400c13a002800000f004000815a004001807c030036001813c002000004007c3be00200c002401e02d006002c00200700100e80001fa010000801e0010260358000025004800001a019000800000611407e801022a001001c5b4000002001006c01e02200002c400e5b50110008002004001000005c00000080100001f30010220008013000807800001800000cc016248060807c0060000810324060006000811400c001004806408a05b0190c9400400200a000001000200400bc000020004800801000000000540c800400a80080240420038088152016005809c13a005009809801201387880b800201600b803401200034580040e800400000ac002595043000809805c015809c048000031803800c00b000005c02c000004832c0120120000054006055003000c06c000025800002a00100d50c001c002002000000a0960f80a9c004031027800003000300c000007800002e802842400e00607fc02a00000380002900110c200540a4029002000000e0900018038016006008006c02806a00000800020621d0875000200302e0008000005003000c1f40180020094008000003026400203f01603e02c400f042803800026c00581a0004002000026003c030018801003201912a803402202b000805808e001179001c09602700a001402600a00001740000030490050006000ac2001401400001880005ae2ba00000000a087300000640e40002820038060005022005004800200e000006c021bb10004052028000004c01a1d300b800000a000005005800e00e009001800800300b00cc01e001003819c05c07a000808c3fe02007b000c0200b700100e802008c001809c0000000068090000000016000404c90800180a0030027005054402600000000c80423fb004002c00800101314c801220400001fc03e009001000002a0430000000084001004801001e0010080020032000000804417600501f08f818608100c837c00a021009b1cc00602600684d8034019008802400000000100480280130118020004003002000400200005a81980c81210280000014017000801001a41703883180820c2001800c07800c0000074006017002800001e0000010000258006237801800804e002800006a016024029c00001e004805c08c00c000007402c01d02b80603d000000286c001201c001800c20417900080ec04803d01b806800601500000540720000028000c0000e0ee80d000400d23c80080000a003c000001802c00026c00160880008df0014084000811800601f0128070000000005800053600c0050000024002216000404200600203a801801403d802400000100580f800800306b8010292001013005800c06a002017402c040020008c006000022007c00600000a00080000a308f804400c00a00f00000dc0010
  | 41 => 0x100b400007a012000007600801300d805402d010002c0ce01300080000000a000403c000c00b0020000000027000009000000002b80bc00000100700040201d200000080b402f00500a002c00500690a824e0030140000128005050086400000000000a00f2000000802401800708b0588062023001800001803b00180300043450028038044001009002801600e005822800001903500140880090a9800402a00047616457440000030590008006000009000c00b035007000a0090071a2c00000601b80080a247800000000480000020028000980000003807037802f003c0140b501480080020130028030012001017803001a0e3000804c0161f7000801805400d000001800201e057800c10c0140080010034e0300000a400a005044000c006007002002001c1a8000010c0080043bb006803200500c8078010004000002801802b00a802003c00107a001800202c0bc8000000000012006c0120ab000010801e0000008038008001005800000200007a002c01200000080440860080aa00bc04202d213000000000c01c00d4084001011801813e00100000005a417503b00300080da00081cc07000100c000401201601280780d802b00880080660ec01b8214000032000801803c01e00e001800006f00517ec1820000d0004000011a011004c01e001000800401e07500181bc052000044806c02606500a006801800a1c4002c01600000500340000020068484054002000003405602c01a006c004107031804800203f002009000400a072000002e00700005a0000004024003400001102b005800a008000002404400203d003001401e00000a40140210bb000000002d000061822002800c8008160005000800c02200a025815400005403c007807e09a00486dc09200f021001022200000380c4056029010800c04a0af012801000200000200000560000060000026036007027c03e01600000300000046c4805402e02c02a8014000078092000000a001004002005e0013a6800c04600f000007403c00c00080b800000901900004000100000008004000000815c04e000000870c2d200312a0040000003002034800000002d80040000da023000400001e000022c00001e09b994006400699c81d401601000109c400e084011193400000f8d6001401a15c01a000400604900b800806000c1af00200160100000008000029047897806a003000000000c061014800401c01a0028b3000000608480388f40860010054016001006800401406d01d005c0a40430100008008027017803c04200206880b93dc00000d0001f20006000000c03201800f806c00c06801401880160161118084064002072807801000306780e4036001000001c01027f3ac81a40ae00004d000c00001602e801802e000001800019600103e000005c0030018acc
  | 42 => 0x1800001e0c2002805c01202600780640000480c185a981c007019000003400c00000080d20100001d9403a07c001006c03600000b0000de800508c8000020003116003801200100000200260b20128000024002009029805e00a00180340c20000058f5800400300a80148a400704d05e4006000000000804800100283480020250058064084000008000008a07c005005400000e000000c000006000800c04a020000001401400001c801c00000001881c400e01a001003c0040071b2809c006002002000e29409000281000000200008000016002000000c0140340010008026007015806c0ce033000014400401e00100d80d6006000024c00400400b800001600501700380201aa005800c00006e01e800c00400000202a81d2000002122002001a00080100020121d480a001203c00800600262d500380000a43b80000030028040003802c01000c00b000800400000200104e805e2d88008000001031800400007c00581c404e09200e00600020000a680a400009406c806000200600180140501120e4001802c0650cc8000084002000000c0140000008000080003000003817e0aa029800004204f00e80bc08c056000005001e00000000000ea0010268034008001000003812e004002005402a00800000200140120000000078006000801805006a022800401400000c800001200c00000e846601102d1670028006000001001c2fe00207bc00400302b000001a07100300644c2086908001116e0110348024000024000000402400f004023001c0240610020000012005809c8260bc00900a806e02b03380000101c503b801c0020e11a0800008a016003005806a0c500200742b0163009002c01403a00000002a002800d803400009703400201540dd0038044000066014000006801b07d000800003684c81c40b0000002003402a00300000640040d6021802001a0042f3000800000100083c400000000180f0e2800204480540ee09e00080c809801b000001000a01d000005002a0040110004000004000804429009b003000000800905d8054008002004801401a1461fe0058006035000001401800000a026007adf900b1aa4000000002803c0020200010010004015000005400e002236000862c028
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xcd77118d624409d8b8c6baa86a800e97a0f6554d4100476c3e83b122000a5e8598b63440071bd0738ec0a1003331cc725911000637ba8e4b1a2000c3c75d9163440018b8cbb9ac8880021f61671d81420443f43e8632a202bc6c621d521c400155d0998ec48826b1b1db75509200043ec3881b2a4290a6e82840654c811878caba4ca98013271d143d89300062fba8e6b122003a9f8658d43904018b8e632ac09080a6b21d5450a210443e438ca9922000cac62dd16244001c58cbb26c4880221f21571d8d4215c3e43aa6b10a200ce7721c564480014bb07a00ca991471718d73d51500264f3a286b0462038de839d952c40051dd05bb2a6881af872106550d32014d643aa8a124000c6f65dc963440112b90ea9a64a80565b209754c75000536c1061b2a8433a6e82cc765484010ff0ea9cc3a80031bdd8725445100747b26c631220cca6d8298065508011ef0eb08c2a00221f215701853200566c1881b12a200a7685cc461480014bd06080ca908023de1d61185542752ec3ecba9a8603cda7618f10440011df04bb26488003175957394631014b6412eaa1ea400a3e840c065484018d8ebb124288002b3a0e64d8910486b5b00ea9924098a3e84cc465508019aee7b8aca900023da067650b100064fba6e6b122000ec46318931440010fb0f218ca90a8fb1604631891001d2fc32c6a9ca20087d87cc465508014bd0bb96c6880028fa16435922100566c14c831a200887e85dd943484019ac8638ac69024a9ba0810d95320043fc32eaa1ea4008ef8759462440374d90ab1443a80032710c7650d2000567c12c831a2000acc825976344001968e838ac6900022fe11701853200536c102032a640887e87d0465484018dce5b2cca880021fe157654d10006c621ae5b0a860087d851da414c0051d9043b2a2900061fa1b754c950006f0086e4a8a2000a9c835d764440014bd072a6ca908221fa1f41195320063bbaee2b1a4000a6d82cc4654840153b06296c88800ea7219438c54013e5a3b6c8a0a20bea5e861946344001938e831ac4881af87e106550d320052ec188032a64008f7815d952440550f90ea8ac0288021f61676509310043ec3e63b2a420087f87594654c4014ed0239eca8814b391d8625051000cdb43ec8a0e202bc6e7119621484658f0c0b84a2a88021f61c32195100046fc1aeca1a4000ae48258461540014bb06086caa10023be0976551310443f42cec9928000c6f75dc962440011db05bb286880062fa1271d814200672396e2b222000a6d8298c654400953d09b1a87108028f61010195210443e42ae9b1a20a3ec41018c62440018eca438aca900de3be1971d4a210046ec18ed20aa000a6e8299365440079a8edb9a62883671bdc8655854244eb2290e2a94a20399c839c75450c051d904b8ec89037b17dcc6558132
  | 1 => 0xb05a0eca90802b960430d895100667b9ee4b2a2056cb47619131441310f90eaa2c52880297a1672d8d1000477c12eda9a20048bc845d8514802b0f90ea9ac5a813b1798f73553500047a40aecaa24000bd180d8d31c40010fd0fa1eca880030fdd774591100065a3a6e2b2a4000a758194f65440030fd0dbaa42a80221fa1676509310045ec26e2b1ea000c3d759d363885c987ae832cc2a10028fa1331195100251f426caaa44200a9f8359764440051790cbaa86a10221fa1671d813200477c3ac83122051b1e83d975450c051dd0fb92caa186f391db62505100443f43eeab22203287e87d4d6094401ac8a438ac4a80028f61331d95210043f438cab222000a6c8558c62440019aee638ac69000a3721d634c85100c76412ebb024200acf8359462440071bd07bb443a8003279d173d962135f0e32ea8a1a600087e861d532440014db0b3a6c4a88029761672d8d100061e3a8e8b1a40038de831c560d50031b90cba262980028f61052d95410063a3aee2b1a4000a6f8559062440051d904b8ec6aa0221fa14768c54001476412ea30a860387c8759553480010ff0eb28caa08021fe1576905300052ec2e87b1a200187c865d543540a51dd0db8a84901228f61f65d51430043f43e63b2a840087f855d932904670ff0abb243a824697a1b6550d320053ac0e8432a2000ae781508614800187ce9b2cca880021fa1c65589100045fc3aca3222000a3e8498b6544001a58ebb2284900122f21171d8d200061e3a6cab024200c3f75d9142440018eeebb8ac89004a5b20971d5150006b2290e2b2a4000caf741c9644400917908baec68800f279cd43582410043fc3aca32a80008fb805d943484014bd06296ca883674b9907550a210056741ccbb122000a9e83997644413fc38a7b22a8a98031b9d672d85434ce36316eaa12207ca6c8558a21c400195ae9396c2a180297a0e64195100055ac202030a6400c5c73d95605080147b0b396c888002aba1273d891000672396e2b2a20008be8714b6444001878c83aac8880ce9ba0830d95214bc3f436e8a9aa400c3c64dd521440011df04ba8c2a180317dd473591100443e42ae3b1a8000a5e8310b654409d4b906b2aa8900025d607754ca510052fc2ae9b1a20bae9571d9063440051dd0fb92cb882a7a960464d891001e2e39aa6b00a2018bc865d2215000187ae92a6ca9004a5b61f65d49200061e3aee8b1a4000a5d85990634415bccc20328c4880af1bd8075485200046fc1aeda922000a3d841cf65484018d8ec392a2a82429ba0810195320052ec1ca9b2a420487c855db54440014bb06292c1288029761763d4d200245e422eca9a4004a9f8650e418c4015990ca1a649027b8760f65d51430066a398e2b224004c3c74551601440187eea3a2ca900021fa1c30d95210043ec3881b2a64b3
  | 2 => 0xc10d95420246e43ac6a1ea20087d859d921500031d90cb9a4290003331cf725951000556c24ca3122098a3e84cc065508019aae7b0cc2a100e3d6187150a310443e42aed18a8000c3e74196614c8018b8ebb1a42880029760c10d95210043ec2ceca9c4200c3c64dd532440011bd0e216c6880122f219709054100537414c7b2a202b87c875516214401d18c8318c4880030f1d774589101543f436ea90a207ca6c8558e21484010ff0ab8ec69000317dd473591200443e42ae430a6000c6f751c9654c40117b083b4a29800297a1743d8d200143f43ecaa922000d95431c53290401a3886baec2a180a3b20976d511001c5e43ac8a1ca20087d8790f65484014bb06296cb8800e67e1d43906310070fa00caa1a6400ad58304361508070f90abb6a68800e37a0e71d81520443f4386432a209aa3e840c365508118bccab98cb2080e2fa1f6450e2101476412ecaa26200c5f75d8d62440010ff0ab80c2a10022f61271d81326d56b40ee6b1c4200c3e549db54440014d90ab1ec4880023de1d61185500443f42eeca1c4200a3d8590364544110fd0a3b482980028fa1263d95100061e3a8e8b1a2000a3d8498f6544001c38cbb228699002ad21161185200070e208caa1a6400a7685d0461480558e8ec32a8288002b9606641895100636b94a5b2a8600acc8359462440051df0eb96c2a18028f61662191100045fc22e130ea651a5e83d975488401cceea30a42900221fa1676485400066bb98e2b2a40018ee829c7604c84f970c0b8482a08ca9d60473d95100243f43ecaaa44200a9c8359764440658e8edb2a628800a3ba1f725954100536412a2b00a20499f8750e315009147908b2aa69000e37e1d73d962100746a1887b122000a3d8404365508011ed033b2a5880063ba1b72545200064fba0e6b12200087e8719564484015cb05a08c29000f271cd431854200556c2061b12a293a5e831d3654c801d1ec9b1ec4880029b60a10195427162fbaee6b2a6400c3e74d96614c80196ae938ec710a668f61073d954200657ba6e4b122004c3c7455160d48031db053b6a6900030f59574946410246e43ac6a1a4000aae8298c64440010ff0abb2a89004a5ba1f72545500043ec388432a20018ee86dc953480014db052a2cb10803a9190629051000557c22c63122000ae58210461480019cee438ac6900023ba1c40d89510053a40acbaa24000c6c75dc96444149d8b0231ec48813b1798f735505100573c0a6430a40008ed82dd9544400147b08292cb208aa1fa1b7154d5000c7743ec490e2000a3e8598c64440051d904bb6a9880032d1d0715952015d36412ca28a6200c6c621d5625040753d07b2286a9002a760e62d9110006363aec490e2000cb774dc565480015a902b1a869000e3da1b71549310053742ce9b1220c2e357119464440014d
  | 3 => 0xa32c429aa3e841cf65508014db0a206c4a88221f21572d814301d4f41ec8a1aa200a5e8398b65440015ab06086c29922f479537454d3200672310e2b1280088ee87d8952440052d904baa86a90021f61f4119532006963aa86a124000a5d8399065484010fd0fb2ac8990029da0430d95420dc7743e83b122000a9d86d51438c4018d8c4b84a2a88029b61741d89510443e42ae5b0262048bc845c76354001938873b2868800e2f21d6450f5100636390cab2220d4e6421196314845f4dd0b39ec4a8a669ba0810d954272d1ec24c632a8497a6e820c06550801d48c9b148288002abe1163d891025e1f322e9a9ca2008f78758461548031d90cba242900039914821185500043fc3aca32a20008df87590634400153b07396c8880029b60b41d95320043ec2ee6b244200c3c641d532440f98d8ebb1264a88029d60652987500043f43eca9922000acf8259463440014bd06080caa10039518f658c51001c6e41aedaa22097d2d841d5428840717908baec6a01af871975350d420053b40861b2a4200c3f75d9163440014df0ab18c4880030f99275d92210064fba6e6b2a2000c5c75dcd63480670fd0fa9ac528a4a1fe15764cb505bf4ac08c9b1a2000d2c7550d42884014db05180ca908021fa1c65509100054f41cc43222000acd83993625440159d07baec4a880393d94631891035d2e42ac6a1a405187c865cf54548b92d90ab9a42900130f9d15458a5100637b2ae532a2000ce47518521480011df04bb6a9880221fa177458f520043fc3aca32e206bc5f53dd943d400195ec9b92c68801237a1f6350d5150d6741cc6312200087f855d952c40011db0f328c4880032710d7650c5100567c1acbb1220b8a9e8619063440011bf06baec88800327dd073591200043ec28eca1a4000a3d849886544001d28c63246288002ab60a651911000477c3ac63122000a6d820c365484010ff0eb28caa1026b9a1c614852000536c1663b2a840887e85dd9431440717d0fb22868800ea7a1b6350d400051f426eab2c4200ad6811d3634404f56b0239ec8880028fa1253d951025e1f326e6aa4a20087d8710b6544009878e8aa6c4a80029be1564d891035e1faa6eca1ea0098ee871852148001c3ecbb20c6881f29ba1731d895101476412eca1a204be1e64d4d43944110ff0ebaec7108221fa167650e210070e218caa1a2000aae8494f625440187ae93aec2a1af3955c46518d100053642a64b0442c8ae681dc962c40014bb0bb1ea6880031bdd7625091010ee8386e698a200087d87100654c8051d904b8ec8a98039319763189100070e32ec9b1a20008dd83dc564d40a3c3cc7aa287288032b1cb64545100045f43865b2220218de87d07634400187ee93a6ca908029b61773d89510061e32ee8b122000a3e8414b65440f9c9ea729ec4a880297a0
  | 4 => 0x544001878ebba2c8880021f61c30d95210051ec20a4b2c6200a5d8395365440674ed0da8ca2908028f61052d95100047bc0aeca122000cb7741c5654800147b08196ca880029760c10d953200557424ca3122000c5c75dcd63440111b90cb9ea8988121fa1f655513017c76436e4b02a2208bd86dc5439040155b093aec488002b960810d8552094b6412eaa0aa000a5c8359465441ab4eb03320ca90b128fa1865191100063a3a8e2b2240028f8865c051480014bb06296ca98383930846550d320062fb9ce7b2a8400a5e8399365484051d904bb6a688002a761262d8d100053b4088032a420087d85dd943c400187eebb2242880028fa13311952100557414cbb22207cc6c75dc961d4d51d4820320c4880021fe1571d91200243f43ecaaa26233c6c62dd5214400147f0ab26a9108031bd9772545100053642a6430a4000c5c75dcd6448001c38c832a86990021fa1c10d952100637bb6e4a8ea000a5e83d96658840117f08b8ec6a80029ba0b31d951000536c2ce7b122004a3e86d9154540019cee438aca9000e37a0e76549412461f322eaa1ca200a5f83594654409d8bcc6baa87288031718c75509100943ec3ea9b12a000d6875dc121480014ed0b98ec2900031d19471581420062e3a8e6b222000c3c65dd163440011f700bb2a89880e1f21571d8d5000556c24cbb1220008bd849c7605493147d08080caa100317d97735812100536c2ee9b12a200e346419641440014bb07310ca88003a319063d891035f0e32ea8a1a640887e8704065484a38bcc6b9ea92880327dd3635891017c76c3821b12a22a87e8794960144011bf06b84c3aa0021f61e43d951000667b98e4b2a20048be849c7604c8071b906b84c3aa2271b1d472587530064fba0e6b2a20018ee86dc954480051dd053b2a2a000a2f21974d4d4200536c168232a6400d1c43dd56250c01958c9b92a2880061f21975505500063bb28e2b02640493d85dcd54508010fb0fb2ea9108031b197725052148d2f41e8032a64038dc835d7644c0439a8edb1a8288002ab61253d89100245fc3ae9b1c420887c855d932440014dd0b320c4880122fa127654b100051ec24c7b2a420387c855db53500011bf06bb482a80021fe1576509100443e428ec992a000c5c65dcd60509c38dee432ac8990029760e54d95320043fc3aa930ea06be1e65d51438c4011db0f320c4a88061f219759055000732328c4a0a2000a5d858c363544010ff0ab96c0a0a5e5ba1f7550a210043fc3aca32a4000d4c7558d32884010ff0ab90c2a18221fa1772583530052f41ca9b2a2000acc8359762440091b90eb1a87288029d61410d85520052f418e9b2a209287f855cf64548090fd0b3b6a9188021f61f31d95104be96c20eaa1240008df835d9544813187ee632a86a1003871936550d320043fc3ac
  | 5 => 0x8023be0976551100052fc2ac7a9c4200c6f65dc9644400117f08bb0a2900023760e765494101c3f43ecaa9c4200c9c431d943440071b906bb0a290002ad61010d85320068e218eab1286008ef825c763550031d90cb90a290002aba12631891028e2e31ee8a9aa000aad8498c62440031790cba262a01af0f1977550d420043ec2ceca126000c6c72d9563440014db04080caa10029ba1664d891001c5f43ec8a1aa400c9c74dcd654800953d09b1a87880031b1977258d100063a328e2b026452ce47618931440018b8ea31ac48806f3a18170885215fd2f42cca31a2000c6c72d9551c40011df04bb284880028f61010d952101d4e41ac8a1a4000a6e8299065440019a8e7b8ac8900123d6187154a410052f41e83b2a4200c6f76dc9511456996ee2322c4880029761474d8d100051f42cc7b2220048ef8759221484f94dd0a086c4a880297a0c74d952100c3f42eed18ea000c9f7650d32904014dd05a08ca880030f1d9545095025c3e432e9a9aa00087f855d9434840917d0fba2c4880023760e71d81420053ac088032a42008f7815d9544c0010ff0abb2a69036eada0774592210043f43ecab224200a5f8559363440011bb0e296c688003175ce53d952117d3742ce9b12a200a9d849cb63440091dd0fb12848800e3720d76509100052ec182032a6400ccd739cb6150c014db05a0eca88002b320964d8d100245f43ee8b2a4003c5e7354d62944011bb07baac9108063ea1b70485100251e422cbaa24000cac72191634400187eebba2c4880031b1d7725912100477c12ecaa260008f787584614c1b9d2886b08c2a180393d9463d891000537c2ac7b12200087d859d943884d7c38cba9a86a024f1b1db754c92001c5fc3ac920a6200c5f75d8d42440014dd0b318c4880030f1d365589100061f3aae9b1c4200d647518521480658f4edb2e2088002ab219435092000752320c498a20008ef825d76050c650f90fb2a42880029b61673d89510461e32ae932a207ca6e85d0762544010fb0e086ca990221f219709455100536c148032a4200aae8498c625440153f08b28c688002ad61010d85420443e42aeca1a4200aad849cf624400917d0fba2ca880030fdd47458d100051f42c87b224000a758198f6550801c38ca320c6880021f616764c91000666398e4b2a2000a9e86d51434c80117f08baec6880028f61331d95100043ec2ee4b046204cba7619310441c1c9e4032a86990032d19071591200445f43ec8aa26000caf7418960544014bd06206ca9080e67e1d43905300072632ec7b12200087d859d9548840917908bb264880032b19372591100463bb8cc2a8ea000a6c85590624400147b0bb26a888023171957314530526673b0c631220018f8805d9544c5b18dee432ac2990021f6167650b10006563a6e4b1a2000c3f751d16
  | 6 => 0x1e1fba0cab028403c9e7350d629040187eecaa285288029d60430195420074a31ec918a2000a3e85cc7644400917d09bb26488003175d573d922135d1f42ec8a1c4297d6b601d542480010ff0abb286900031bdd762485104bd374102032a8400a6d82103654c8014ed03318caa12665be1d54d4a210264f3a286b1462018de87d8d31c40018e8a438aca900030f9507654d420052ec1e83b2a4204cb476dd141440110f90abb482980221fa1c301952101476412ecaa22000ace839536254401878cbba2c0908ca1fa1f41d951000678b802030aa400c3f75d9132440018becab9ccaa004a5b2097550d500053642ac9b12200499c849c75350c051dd05bb286a88221fa1f431952149636316ea9922000c6d759cb6150c015cb05988c29000e37e1d73d92210068fbaea8a1a6400d1c7550d428c401c3ca7b26a6880061fa1f65547100062e39ecab024200c5c7654d32540574dd05200ca908cf99d87658852100747b20c6312201587c8755162d40014db05326ca8806e3ba1f31d89100062ec3ecba9a860887c855c8615012f4dd05080caa10031ddd47158d200043fc2aeca14627ca6e85d0f62544011bf06bb2a690002a7e0d75d91100070e218caa1a4200c9c439d943480090f90abb6a899002b9608311852000557424cbb12200887c855d363480014bd07396ca880061f21572d815101c7743ec49962008c5c655ce65500078b8e6a9ac1a90029760e72d95100443f4382032a640087d8704365508011bf06bb6a8880029b60a101952101c6f43ee6b22400187d85dc960144070f90abb6a6a08023760e7654b1001c6e41aeda922097d66611d542884070fd0fb2aa69081237a1f6350d100064e21eeca1c4203a5e83d9553508019c8e430aa2a8003175d673d92210065a3a6e2b122000a6d82cc765484014bd06086ca908128fa13655531001c3f42ceda9a40008ef825d954c41274bd0da9a86a90121f21571d91500443e42ae430a8600a5d8399365440090fd0fb2aa88800327dd37358d100062fbaee6b222000acd830436254401aceebb8a85108028fa1030d95210056b41e8230a402f9e581dc951884d787d0e32a86a10061fa1e61547500066a39ee2b2a4003a9e86d8d435080753d07b2287108021fe1d65196310461f32ae832c6203a5e83d97538840147b09980caa13ab87ccb65d51430043f43c87b2a2000c5f751cd65480015cd0239ec4882471b1d8754c92000536c2cc6312a200ccf731c964440071bd07bb284880ca9d60474d95100074a326c720a2000acc8259463440010fb0e290c2a800a3ba1f7258d103e537428e1b12a200c6e755cb6150c110f90abb2851889f2d1db644c51019cb6412e3a9ca2008be8719163440078bce6a9cc3a8002aba0a63d91100443f42cec9962000a3d8598b64440014bd0bb9ac71
  | 7 => 0x6c7558932d44011e902bb2a6900021fa1c40d95210055741663b222000c5f75dcd63440010fb0bbb287108021f6177650d100443f42ee4b0482028ec825d9544c001938c9b9ac4880038bd9464189100070f980caa1a8400aad84cc7625440953d0db2286980122f211709875349d2f41e83b2a649796e87dd542480018bae729eca88002b3a0a65d8d100043f43ecab02646be1e84d975350cd7c3ccba9a8720803a51906350510004b6c2ee4a1ea4028dc8758d32d40070f90aba6c6a826a9b60b71d954248d2f4188032a6400a3d84043654c8111790eb22a9188021f21f65509100462e3aac6996a0008bd849d953884010fb0f988ca880032b1d362581510053a42ac230a4000c9c43dd9431440193ee739ec8880022f6137558e21006363b6e4a8aa0028ee82dc563d40071bd07b8ac9a80221f2157650d200243e42ae7b22a000c3d655d0658c40153d06296c8880128fa1365551320062fb2ae728a6000acf8650d32884bb5cd03b1243880121f21d65552310064eba4e7b2c42038f5861c5528c40155d0931ec4880022f61071583530064fba6e6b2a400887e87dd563480090f90eb2aa8900029760f41d95320046ec1ceca1c42ecc3f75dd16550c676cd05a8ca2908023b61e63189100051f42865b22200887c855d943440014eb032a6ca880061f2157650b5048636310ea9922000ace82993634400733d0faa286992621fe1d54d895000c3f42eeca1ea090c6c621d532504014db0b300c4a880e3720d76551100243ec2ee2b26a000aad8498f62440112790eaa284a806f391db624c51049d2f41881b2a6400c3c75d9132440011db05bb286a88221fe1d75d922100536412ca32e200187c855d932d40010fd0e32ac6908028fa12621951013c5f43e63b2220048ee87d8942c400199ee7b92c688002a761265d8d100054f41cc5b22200087e8719563508018bae73aec2a18028f610521855001c5f43ec8a1e20e8a778558461548118bceab1c63a8002ad219439051000572412c230a80008f6819d932c400147b08180caa100e3720d76549100052ec18a5b2a8600c3c75dd164480110fd0fbaac5880033518c7158d200056a41ac230a40048de87d8d43540014b90aba6c6880022fe1176551200046ec1cecaa442008df835c764480014bd0b310c68832ab9e09611852001c3f43ecaa9a8400ec46318a31440250fb0fa9ec4a8002b3a0b41d8d103e53742c87b12a200a7681cc865440018deea392cb880029ba1620d89310045ec26eca92204e87d86dcd54d480196ae9b0cc2992665be1d54d4920044ae43aa6994a29aa3e84cc765508014dd0b31ec4880122fa137654d101543e43aa6b00a200a6d82100654c80155b0532ec8880029da1741d852000666396c6a8a20018ec865ca41480015cd02186c4a880297a0c42195107
  | 8 => 0x6bb2a4880032b1d372595100051f42065b2a2000acd83d0762544010fb0b3b242980029721564d8d100443e42ae7b224200c5e759cf64884110f90ab9ec88800e97a0f6554d2100556c24c6312a200c9c74dcd62440014e902b2aa89000a1fa177650f520061fb2ae930a64008ed829d951500018b8c63aa42880029b215425822100657ba6e4b22200087f855c8614c00153d0932ec6880031718c7558d2015cb743eea90a4000a6d85dcf62440010ff0ab8ec6a10028fa1010195210051f420e7b2a4200d6870dd5324800159d07320c4a8803591c861545500462f32ae628c62038dc835d954481270ff0ab96c0a980b3a9d862c41100546f438c298a6000a6d82953654800917d0938ec0a90029da0474d95100062fb2ee6b122090d4d831d532480011ed03bb286a9002b3a0e74d89510443f4388032a4200c5f7518d624404f974edb2620880021f61f41d95210051f424c632a20048be841da514c001d88c7b1462880221fa1f7558d210062fbaec690a2000a9c845d763440010ff0abb2a6908029ba1731d8910006b4396e0a8aa00087f855d954484574dd05a08ca90b9f0fdd774595420043fc2aec99620afa6e8619462441459ccec31482882435360c754ca2100637baec49922000e4f5394f62440011bf06bb264880122f21176d49100051ec202032a6400aaf8259464440110fd0bb92c118b5799084655052163e1f3b6ca3222000aac8459462440014eb03326ca991461f21973d515001ccf41ae1aa286a3ec61018c62440574dd0db2c4290b978b1c86550d4201c3e42aeda9e20dcab681dd1648c5274bd06086ca99003331cf725911000537414c632a20038dc835c764540018bee729acb108021f61f31d95420045ec26ec9922003a5c8359553480371d90fb12a2880121fa1f65553100264e3a28630a64008ed82dd9434840155d0929ec4880031d1d47158d2000732328c520a2091a5e83d04654c801ad0ebb8264900ab1d1d8654c5100053bc0aa730ea000e8f6418f624400187aeaba6c71080e2fa1f6450d210052ec1e8232a64008bd8799464440051dd0fb92ca988de79e1971d4a212461f326e8a9ea0028ee829d9548c40917908bb2a488003591d4714ca2119db2416a328c4200a5e8599363440010fb0bb92c1208032bd93725451049e37bb6ea9944200c75711c7654c80147b09318ca880032b5d172d85430043ec2ceca1220048ec8758942d44a30ff0cb9ea9289f25b215744ca210066a398e2b2a40008f4815d943480019c8e5b0aa2a828aaba1264189100046f43ca9b1a20028ec825c763480071bd063b482a80028f61432d91100043f438cab0a642aa7a80949601440159b072a6c4a88221fa1f311954219c3f43e83b2a4200a748159753480018b8e7b2ac8880221fa177650d100261f3a2a930ea408c
  | 9 => 0x6458d100052f41e83b2a2000c9c73191624400159b072a6c4881725b215744852001476412e3b1aa05cd2e841d5424800159d06086c4a88030f1d77458d1000557424e7b12a2008f787584614c80195ee9b12c0a88023b61e50d895100476c14eca8a6089ce7865c7528840193ce939ecb108221f215765091000536c2cc83122000a6d82cc765441bf8bae632cc299003471d5434ca4100566c1cebb122051c5e63dd1539452f878ec32a86a10023be0976d51100043f43ecab1a2000ce472dc563440014bb07a0eca880021fa1c42d951000c6e432e728a60e6c6f72195635080317d0fb2283880023b61f41d89510046f438c6b122021cd476d8d31440678d8e530aa2289ae8f2156450d202461f326e8a98a200a3d84cc465508018e8ebb8ac8900031b1ca61547500052ec1cc9b2a420487e87d95544c8018d8c43aac498803171d7735911050e733b0c518a20038dc835c7644c00159b07320c48825e9ba0b31195420045fc22ebb1a400187c865d531540f94d90ab24429081237e1d648c5310051ec2cc63222091c6f761d532884ad17d0db8a86a00030f19574985327070ea10caa1a646bc5f53dd943d48010fd0e32ac2a10022fe1176d491000578c004230a60008ed87103625440753906b2287a880237a1c52d8d100045ec26eca9a2000c6f751c96444001ac8ebb0a42900221fa1e43195210043ec3c8632a205c96c855d132480110fd0f988ca88002aba1030d895100637baee4b2a20b6e958119063440112b90ea9a6428812a7a136350d100443f43e6232a4208c3c7619554508071b906bb4a2a0023171d5634c85101c6f41cecaa4426bc3f54dd943d489d4bd07b2aa9109af0f61c6550d420072a318cb18a2000a74815946548131878c83aa848825b4794f73551423e697420eaa14420087e8790f654849747908b2ea6900029760c52d954048637b00ea992400087d8704065508011db05bb287882628fa1b6550d420063a32ee2b0284038de87dcd64440118d8cab94ca880038b1977250d424952ec18e9b2a6400a5d831d3654400917908b80c2a92431b188754cb103e6363aec4a12a2008bf845d952441218dcc23aa6510802a7a1262d8d1035f0fc18caa1a840087f855cf644800155b09baec4a88af999c465885210043fc2ae7b22204be1c64d4d435480155b08086c4a88029760e52d954300536c14a6b2c42eae1c43d966550c1187ceab2483a80221f21574d8d213e477c12eda9a4200e5431d95314400159d072a6c4880221fa1671d81420053ac0cc832a6400e1c65d906344141a38a9b9aa8a98022f61c32d91100056741e83b12a204c3e74d506154001a38eaa1a849800f271cd43d89400046fc1aed28a800187e85dd931d40018d8ebb12648800393194631891019cb6412e3aa4a2008ef825d952440011bf
  | 10 => 0x9928200c5f65dcd60508030fd0dbaa84a800ea7a0f6450d506c6a7218ea9944290c5c76195434c8018deea392caa1802a76126218d100051ec266232a20ade6410194624400153b0da9a87208028f61052d9710006563a0e4b1a20008bd849d943884051d904bb6a89880637a0e71d813215d374142032a420087e87195324402b2dd0fb92a3a80031718c7558d104ce36316eaa12a2d8d4e631d532884650fd0e292c1288031b1d77258d100051f420e7b2a2000a6e85d0762441252df0ea9ea5109f23be0976d512100556412ca3222000a3e8590f644400147908b28ca8800e37a1f735891000673b10e2a92a2e0e1f42195434c89d2bb0fb2ea6a1812a7a136350d500043ec3ca530ea091a5e83040654c80917d0fba2c68800317dd7634c9100043ec2eeca1aa200a5d83104654c8015c904b08c2980031b1d762509310245f426ed10ea0008bd849d952c400187ae8baec2a182297a174358f500045fc22ed18aa00887e85dd943c4011878caba0a2a006eb960473d891000476c3e63b12a20087f87594514c4111bd0fb1aa6a0003271d073589100046fc1aec28a4000c3c7519162440010fd0fb2ac299003179d573d9221006563a6e4b1220008ee8704362544018b8e7b2ac4882aeb9e0564189100045fc22ecaa22000c3d751d76444001ac8e5b0aa2a80af5ad807548520006caa18e2a14620087f855c7644c8010fd0fb2a848800e3720d75d9120094b6412ea98aa021ad5811d3634418b47d0b328c8881f31b19772545100247b436e29928200a3e84cc7654840193ee831ac4880023be1d6318951006363aec49962000ad683d07614800717d0fb2286a80221fa1773593520047bc3ac230a8600a6d859d3624400187eebba2ca880029b21542185200056741cebb122000a3d8494f655080153d08296c6880221fa1f75591200043f43ecab1a84008dd83dda21d40379d4edb162088002b560c10d85520043ec3e83b2a2000a6e82cc465441258b8edb2a86992cb1b9db6518910006c621ee4b2a8600aae8498f62544018bae729ecaa10030f1d36558d100061eba0e9b2a64008bd841da31540070fd0b3b6a72080e3720d71d91202451f426caa9c4200aad84cc762440070fd0fb2aa688012a72116350f513e717aa4a9b12a200a5d8314b654c4031790cba4a2a02a72b9d86418910006363b0ea90a4000a5d8310065484018d8ebb92c69080a7321d534c92000477c12ebb02829a87f855c86155001c5eca326c488153351d863505100053b40881b2a4200acd839d362440014bb0b316c6880030fdd25459621014e643aa6994420087e87195604c8114dd0b102c5a8802ab21165d891001476412ebb0262038ef8758e214840153d09b9ac7108029b61741d89100052f41cc432a200087f855cf644843f1db0db8a65108032b1cb
  | 11 => 0x48401998e6312c0a88022fe117654d100045ec26ed10ea000caf74dc9634400933d08b96a6a18031794c76551320061e3a0cab122000cb474dc563480019cae4308a2900221f21c65509100063a3aee2b1220b5c7771195624415555d0c320c4880038710f6550d210443f42ceca1620048bc845da31540014d904b28ca9880387d9464d8d100443f42eec9922000e2f65d9062440071bd07bb2a8880029da0664d953200476c3cc6312a2d1a7785584615400793aeca1c83188123ba1f625093128d2e41acbaa240008ef825d953484078b8e6a9ec4a80033318b735891012c76c36e2a144200a6d820c0655080947d09b2aa8988122fa137158f500de74386c490a2003c5e7354e61d480193ec9b9ac48832799148611452000566412c831a2000a5d85d07634400953d09b1a86908023761f41d8d100064f3b28720a6000af1800846154001d48c8314628802237a1f6354d100056641ac831220008ef825d7604c401d88c6312828800a3ba1f72595100043fc2aec9922000c3f65dd160484019a8e7b8ac48800e2f21d6450d2000536c2c87b12a2048bc845d763480018b8ebb1a64880038718c6550d420254e4328720a600087e87d9564440091bb07bb287a80121f21576d52214c51f4206232a8400a5f85590634400147d0b310c888002b360f75d895100536c168232a20038de87dcd65480051dd05bb286883430fdd7745954065ea7218ea992403287e87d45609440193ee839ac888003271d073595200443f42ee6b24420887e851d943480011eb03bb286a900297a0f75596210068e3aa869928000a7581cc86544001a3eeba9a86a10025d6077550a5101c3e42aeda9c4200aaf8650d42884014bb06080caa100a3ba0b76551100054ec1cca3222000e646518931440b9a9d063aa64900021f21f654c91000c3f42eed20ea0008be8794f644400753d07b228690802a7a1272d8d100051ec2ee5b222000a758110365484014eb02180ca90803171cc65581420043ec2cec9928200c3d87d975450c0159b0532ec6880031b19772591100043fc3acbaa2400887e87dd562440672d904baa87288063b219728c5200065bba6e2b1a4000ab684cc46148001958e8392ca88002b360e64d89100043f43e83b2a6400c6f751c9654400117f08b8ec6900029761772d8d100046ec18e2b06a800c9c7650d32500014db0b98ec4a88021f61f53185500062e3a8e6b22409aa3e8404365508051d904bb6a7880029b61664d89100443f42ceca126097c6c621d5424c4018bce632cc2a10ce9b209659471000536c14c832a2008c7a7619710440010fd0fb2ac6908021fa1f655812101477416eca1e2000c77651c56050801c98ca31ec4880021fa1f65585423e6363aee4b0ea87ce6761d8a51544011bf06b8ec8a81f353a0c754ca2101c7743ec4
  | 12 => 0x122fe1d74d96210052ec1ca1b2a62008df835d764480018d8c43aac4a18030f1d47458910006363a8e4b2220038ee87d89324412f4dd05180caa10221fa1676509100054ec24ca31a200887e870406550801c68c9b2a828835b99084659052101476412eca9e20a6ae78158c62440572dd0fb92a2288023be097654b1000566c1683b1a2000c3f655d2654c00159d07326c4a880e1f6177458f5001c5ec26eca1ea02ba6e8204065484010ff0eb28caa18030fdd274d9532006a63aa869944200acd839d362544674d904b2ca2a0803175d7638c5500243ec2ee6b26a051e1c63d51435480196e8638ac8900029da0440195320051e422ca32a4000c5f655ce65440091bd0fb1a8710803531d7634c9204cd37410e1b2a8400c9c7650d424c0014db0531eca880062f219748c5400043fc2aed18a8000ad5830406154801938e9b1ac4880063d61b748c71001d2f41ecaa9e2000acd8299363440439b4edb1e20882631b1d8755092074f0fa16cba9a8608c3e655d051904018b8c7baa84880225721d534cb504843f436e6aa2a400c5c655ce61508071bd073b285880031b1d7624c9410443f43c8632a2000a6d8204365508018c8ea30a429024a5be1d53d49200043fc2ae430a8000a76810c065508110fd0b3b264880121fa1676d512000667b98c4b02a200a3e8494d6588401aceebb8a651081237a1f6350f100143e42aeda9220898ee87d8951441838bcedb28c6880022fa1f64589100061ebaec920aa000ccd735cb6150c07938e6a1ec0a10031798e75d8e2101d4f41ec8a1e2000a6e8590f62440019cea438aca900023be0971d8d500443e42aeca162000aae84dd762544011bb07bb284880023761e6518d100043fc2aeca1a200887c855c7634800953f0cb228718802a721165d8d100051ec28e7b222000a6d85d0f62544650fd0c3aa42880023760e7654e210062fbb2a6994a200c6c7219563440010ff0aba6c688003591d47150a210143e432eaa1aa400aad8298c644400187eebba2c6880028f61764d51200043ec2eeca1a4200a3f855cf644400947908b2aa890002a761052d8d1001c7b436e2a1262008ef825c764540019e0c2b80a2900021fe1574d8d212443ec36e8a9ea400a3c855cf64440051b90cb9ea8990aa1f21d54580510452f42e86b18a200a3d8414b654c00155f04b2ec8880221f21572d81410061fb2ee8a8a8203a5c83d97534400147b08190ca880021fa1875509102461f326e8a9ea4048be849d9524c40147d09396ca880029760c52d95415be4f3b0c831a20cba6d82980654c9230f90ea9ac5288029760c42d95100053b40cc832a6400a6e85d0f6244001d28c831c82880032718f7458d1000667b1ee4a8a200087d859d932c40550fd0db8aa8a80062f21974145400047bc3ac230aa60087d87d0c65
  | 13 => 0x61eba4a9b2a200887c851d942540439b0e1b1a628813b1798f73553520045ec24eca926200a3d840c365508010ff0ab8ec6a000297a0e64d95100064e3a6e6b1a4000a3d8494f65484011db05b8ac7a80023d2057655130006363aee4b1620008dd83dd954440110f90ab9ec890003271cf64589100acb6412eaa1ea000c5f65dcd514c4011db0e186c4a88030f5d074d95210443e42ae3b2260028ec865c221484010fb0e180caa10030fdd474589100243e42aedaa260008df835d9424400193eeca1a8518803171cc6559110006363aee4b226400aaf8459462440014db04386ca908022fe11701855200567c12c9b1a2000e2c6519062440118d8eab1285a88034710e75d85430043ec3861b2a849de1d84d975350dc14bb07320ca9900297a174358e210053bc0aa930ea000aac8458c624413547d0daa286a90021fe19754c7500043fc2aeca92200887e859d932504014eb02206ca99002b3a0a6518d100053b40cc7b2a8400a6d850c362544014bb0b326c6880030f19075485104962e3b6caa9a647cc6c65dc951484011bf06bb2a8880031718f7558d100053ac0861b2a8400ccf73dc964440010ff0eb28ca9800e1f21576d4d214563bbaee2b2a2000a6d8598c62440014db0529eca900031b5d572d85430061eba4a9b2a42accae76d9062440051d904b8ec8a80032710d7650e210043ec3e83b2a64e5e1f3219543508015cd02206c4a880333dcc7258d1001c5ec26eca18a200ccf73dc962440071b906b80c2a10022f61f31d911000556c24c7b12a21596c825d541d40010fb0fa08ca880031bdd77258d100062eba8ebb1a2000a3d840c465508014bb06292cb2081237a1f6350d210051ec2cc7b2220008bd8794f64440011bf06bb286880ae9ba0b31195210052f42885b1a200887c855ca61d5001938c9b9ac8883334b190755092000717b2ec9b1220048f686dc5525040917d0838ac1a9a661fe1574d8d520043fc2ae5b02860087f87594654c8a91bd0db8a86980031b1887558b1000567414c831a2000cb574d86615480187eea322c4880022f612764cb1000556c1663b222000ccc63dc963440018becbb9ac8880030f1d764509100056a4328718a2000d4c7550d324800117b093b2a910802b320d64d89100063632ae110a4200cd7731c56448151d4c20320c4880128fa13655512100c76c14eda8a4000ab584043615480117b0e296c8880121f21576d513113e5c386c8a0a2000a5e8395165884570fd0fb2a42880122f21176d4d100043f43ecab12200087e8719563440110f90e32a428825f1b18875509100043f43865b2a200187c865d6315400147b08292c1288029760e64195100043ec2eec9922004a3e84d97548840147d0b396c88800a3ba0a765453000477c12eca1a2000a6d85dd3624400153f08baec688
  | 14 => 0xd85cc764440011db0f320c4881735a14970145206371ab8eca322209a87f855cb605500147d09318ca908061f219758855000c7c402eca1a42d2c777119560484018b8c7baa4288012a7a136350d520063bba8e2b224000acd83994624400117f08bb2a6900224f21d5450a510254e422c6a1ca200a6d82d0465484110fd0e210ca880029b60840d95210054ec1ccbb222000a9e84994634400117f08bb264880021f61f311952100636396caa8a82e5e1d32195435080117f08bb4a2980ae9b209651454100572c0881b12a2048bc845d953440014db0a386c4a8813271d14318530006363a8c290a4000a3e840c865440014dd05286ca988028f61052d95430064fba0e6b2a40008f7815d943480d78b8cbbaa8699003179cf6599510006363aec4a122000a3d8494365504010fb0fa08ca90803399d461485204c51f4206032a840087f855c0614c8071bd063b4a2a00029b20965195410062fbaee6b224000ae58198c62544014dd0b106c4a08021f61f54185500043ec388032a4200a6c825946550c0947909b2ea8880029761442d8d1072f17900caa1a840887c855ca61d4d270ff0ab90c2a9a631bdd87550a2100556412cbb2220008ef825d954484014df04b28ca88003175cc73d951000477c12eda9e2033a6e82103654840153d07328c8880021fa1b754c9100443e42aec994820087f87594659040717908b8ec6a00063b60a76d512025c3e432e9a9aa400a3e8404365484071bd07baac9108cb1e1c365545100056741e83b122008c7771dd951d4001a58eab2285108028fa1473d91100043f43ecab028400a6d82cc465508910fb0dba2a628b4e9d60663195210052f42e83b1a2000acd83d0762440010fb0b38ec0990ce9ba0b41d95210052f42e87b1a200087e86dd542440018d8c43aac48800e3720d76905504be37308eaa14422ba6e8210065484018b8ebb9ac4880ca1fa1f31d951058d3742cca3122000e1c65d8d435093963d09b2ea6a18028f613311952161e1f3b0ca3222000c3c75d91624400147d0998eca880023be0976d4d410051ec206032a4204a9c8458d43481afcc843080ca908032710f7650f5035d2f42ec6a1c42048f5861c532904010fd0e32ac0908cf1b1cb65545210052f42cc831a202ba6c8259451c40015e300108c2a00030f1d065581210062e32ee6b12202b96c825d5431440147b08080caa1023171d86554d320443e428ec90aa0008ef825c7644c0011bb073b2858800a3b20971d913000cf8402e898a20028bc8759142d40070fb0bb8ac7a80021fa1f43d95212449ec3ecbaa2860387e87d9553505230ff0ea9ec4a800e2fa1f6450d510145e43ac8a16a26be1c8319543509274db05b8eca990228fa16435935000657ba6e4b2a200087e870c365508014eb02200ca990061f215764875000
  | 15 => 0x4baec0a08021fe1d651471000c6e432e628a60048be849d932c40654f500292c1288030f19774581324deb4296e0a92a000aae84cc7625454b59d0c318c48812f871935350d500063bb2ee2b02840187e85dd941d4001878e832ac6880021f614768c5400146e43ac6996a2008ef825c76454dcbc584232a86a1002b3a0c40d89510043f438cab0284bbc9e76d9063440014bb06292cb188031b1db754852001c6e432e118a6203a5c8359753480011dd0e186c4a88028f61262d951001c3e42aeda9a8400e1c43d95434400933d08b86a6a18031794e76d4d100047bc0aeca9a4000a6e859cf62440051790eb2284288023b60b7654d100066ab9ce3b244200a3d8590f6444097878c9b9aa8a80023be0976d51314cd3741663b2a8400cb5749c765884010fb0bba2c71080e3720d701855200727b2ec631220ebc5f75dcd6550c033ad0fb1a638800237a1f63589100070fb2ec9b1a2000bb180d9141c40014bb06206ca908022fe11765091000536c166232a20268dd86dc5438c4018bee739eca90b4f99084654c5210245f420ed18aa000e647518521480010fb0fa1eca908023de1d611852000717aa4a9b122000a5d83040654840196ee838ac8900021fe1d65195210066ab9ec330aa400ae6811d36244001878ea322c688002ad61010185520064fba4e9b1a20c0e5571d9463440091dd0fb1284a88031b197724c5210043fc2ae5b026200ccc73dc962440078bce7a98c2a80030fd97745891000557c22cbb122000e5463d9531440074bd0db1aa6a800a3b20971d8d400051ec24e5b2a20008be87d916344001ad0e1baa849000297a0f41195100061fb2ee8b026400ae58204361508375cb023a6c4880221fa1f75591210043ec3865b2a2000c77751c5654800147d09b2ccb108029760c52d95100061e320eab22400087d87040654c80953d09b1a86a8a6a9b60870d954200746a1887b12a200d7010dd5214400155d093aec48808736181708c53135e2fa9eeca18a200a3e8598b644400156d0998ec290003a319363189104be36310eaa162008c3c7559142d400917d093b2a7108023761e6418d100043fc2ae9b1a402bc6c7219531484014bb07a08ca8832799084101952100536c2cc7b1220008df8759463440658e8edb2a82880221f21571d91203e53742881b12a23396f87597528840155908b1ec4880228f212761954200476c14ecaa462038dc835d764440d787ea9bb28628803a518c644c5100043ec3e87b2a200087d85dd9424416dd2ae2320c6882429ba0a40195320052e42ac831a20ddcd5739c7648c4574dd04180ca9081267a1f5350d424be37b00eaa1240028ec825d954c40014db05080ca990029760c52185500064e21aeca1ea000a9e8498863440090f90abb6a89080ea720d6450e5101c6f41eeca922000a3
  | 16 => 0x550a210052ec1cc5b2a2000c6f75dc964440014eb02186ca90ac2b9e05651891001c5ec26eca1ea400acd8299463440110fd0e180caa13334bd0c75509200061fbaec8b122000c5d731cf65484018d8ebb92c4880028fa1010d95320051ec24c632a4200c6c62dd56244001d18c9b1ec4882425ba1f754ca2100566c1cc8312a233a6e82043654849d0fb0db9aa9a80061fa1776887500064e3a6e6b2a20008ef825d953c40252d904b8ea6a80021fe15765511000672310e2b1260008df835c061508010fd0e086ca99002a7a1b5350d4219c3f438ca90a2093c5c63dd532440010ff0abb2858800317dd7735891035e2f438caa1a64008be8719162440018beebb9aca880229720e76195320063ab88e3b2a8491c5f74195434c8015ab06080c2990029b6083019521006363a8e4b1a2000a9e86d4d43500014ed02180ca908021fe1d65145410443e42ae030a8432a7a80d45609440195ee8392ca8800327dd3735911000c6e432e720a6000a6e82943655040917908bb4a2980029d606631954200567c1ac831220d9d2f431d542884014db0b98ec4880023ba1f625815129477436e29924000a9d8398864440014dd0bb9ec488003a919062505100443f43e8232a2099c3c76d9543508018e8cbb8ac0990121f21576d53100051ec2663b2a840887e859d9214c1330ff0abb285a8002b360e65d891000556c24e7b12a20087d87d0c654400193ae8b9ecb108031b1cb65591100062eb9ca7b2a4091e1f74195434c8970ff0cba6a7288028f61073d95104953741081b2a6400ccf73d8960544091bd0fb1a86a900a3ba1f72587530061e326eab222000a3e8494f65480d7c3d07b2ea8a1a4a9ba0b41d953200572c1021b0a64008dd831da515000917d09baac7108023de1d61185424cd3741061b2a84008df835c061548670fd0faa2c5288023ba1c62581510053b40e8432a2000a5d831d365484018d8ebb1285880021f61f65d4e210054fc1aca32220008ef825d95344097878c8ba6a6a824b1b18b754c9510061eba4a9b2a6400e2c651936244009878e9aa2c128a670f1db655514201476412ebb02860087f865d541d41234bd06208ca990ca1fa1f54582510043ec2cec9928000e1c3119543508018b8e632ac4880ce1fa1f31d95210062e3a8e6b122000e3441d95414409d0fb0db9aa8288221fa1f7558d100047bc0aecaa24000acf825976344135878c9baa84880028fe11651951001477416e2b26a000aad8298f6444001ad0ebb8284900023760f7654910006b4386ea90a4000c6c72d95514c4674dd04386ca908029b60a40195320443e42aec9962004a3f865915494401d88c63148288002976166218d100145f43ec8a12200893c8755142d40071dd0fb1264a8abb1b9d8651891000477c12e3b1a80018dc865ce214c0051d90
  | 17 => 0x2a8433a6c82596514c551d4b02320c48814a3b21971d49200055742021b12a200a9f8459763441138d8ea392c3aa0023de05764c9100055ac202030a8400c3f655d2654400147b09296caa18032b1937258d100070faa4a9b1a2000a6d82043654c8018bacab98cb208032bdd07258d100064f3b28718a8000e646518a314400156d0239ec888003179cf65985420443f4388032a6400a3e8498f65484031e90cba262880030fd9574945400070fb28c831a20018ec865ca51480014bd06200ca908031b1c861545500264e3a287b026400c3d741d365440051d904bb2a6880023b60b715935000672290e2b2a4000ce687185214800147d0929eca908029ba1774d89100046ec1ce3b02a4a7cce76d8c62440011bb0f2a6c688002a7a0e72d911000536c2e87b12200887e85dd942440010fd0e206ca990029b60a30195420053b40881b2a640087e87195644c8014bb06206ca990038719464d8d1001d2f41ecaa9c4200c3c74195604c80117f08bb28690002e5e05439063101c6f43ee6b2a200087f855d9544c80953d0db2286991478718f5450d500043f43821b2a8400cd773dc564480051b90cbaa869933eade1161185400061e3a6cab026400c5d735d76150c0187eebba2c6900033918871589500056741ce9b122000e2c65d90624400117f08bb6a688003271d37358d100051ec24a7b2a200387e87d9553500018beea39aca880af1b1c865505210063bb2ee2b026400ace8399062440051dd0fb92c3aa0121fa1f65551210052f41cc832a4200e4f65d8f62440018deea392caa080e3b21d624cb510064e3a0e6b2a202bc6c621d521440051d904bb6a6a08029d2056554d202443ec36e8a9ea008c5c655ce65440014db0b320c4a88224f21d54508510061f3ace9b1c42048dd83dd94314401878ebb224288002ab61253d89510052f41ca9b2a4090d66611d5328840117f08bb2868800e1f21d6554e4100536c108032a4208a3e8590d641459b5af06b08c2982429ba0840195320051ec20a5b2a800887e85dc960d51238b8c63aa64880ae9ba0a30195210051ec2061b2a4203c5c73d4d60944110fd0fbaac8990063b219744c9200051f42ee5b222000a5c8359465480018b8cbb9ac0908130f9d154987502461e322eaa1aa00399e835cb5450c051bd0fb1a64880028fa1010195320061fb2ee8b1a2003a9e83d9143440011df0eb20c4a88038718f6550d420443e42ae3b226493a6d821c3654c8018b8ebb1a84880122fa137654910484b743eea9924000e3464d9641440f9c98a6a9ec4a892e8fa1365d4e210245e422e030a6400a9c83594644400153d07ba2c9109230fdd7645515300536c2c87b122090a6e82d04654c8051dd0fb92c8880029b20965195103e53742861b12a200ccc73d8960544011bf06bb2a68826b1bddb7
  | 18 => 0x9c99c00002c0000001280000000382907500b402c39c06981007800401403c0008581b00000580608d409c02000020c0603d400c26009400000816403420c00009c00001800019c0500fc0041b801c01820004445c01404c02810c0780b40340005b80040641b400c03c00016803021402c0440080540340081fc0a000400007c00800171475804400400103808c07005c0000e42c000c00801d5c416c08c01c7e80000180000980440040c402800026808400000425002000007006801c00408c0f4fd84940f5ae005c00000c0700000080000600001940040040583700100d0018000c404b802404c00c5f00440000780040000940a018808d2640000fc02401800400002000407801000c25821003808000005806830c77c0080983140000000040180203c00580a804805897c07c0040640000000c401c00001819001005402c0007ac00403c0340280ec00001400001c05c03449c01c0fc1cc00001001401800400003800405005580800006c03402000000c0600b072800002c0c400005c0040140080e00801142dc0080002980741c00080cc09001475801812410409c01401803c0b40a002c0040000000fc04800002409400404800051000032851c0080543cc00400800401401003d28808800c1e40081080b00000000002841501cc6dc01c08402002000406000809000057c0000040ac10c0080b0000b889400300680104a003c03407001c02c04c00015404c0080d00800300001040e42a41bc0000fc0e405408400403c39000014004400800000000037800c0140000c839009000401000006800001c15410008c0200bc00408c0bc00804c06c01c02802402800c00401403c00003c00c014bd0a3a6c68800f271cd43185400246ec1eeca1ea400cd5739c7658857b8bcec328c68802e2fa1c615054000557414ca3222000a5d8310865440011db0f98ec4880aa9e201515805135e2ec38caa1a640087f855c7644c0018becab9cc2a1002a72116518d100061fba8c8b1a2000a3e85dd164884014bd07a08ca90803931977250d320062e3aec6b12200887e85dd16388401958e8312c0a88023be09765513201c3f43ecaa9e2000a5d83d04654840159f06b26c4880230f1d564508510053741683b2a2000ccc63dc9514400187eea3a2c69026387dcc6550d4201caec2ee8a9a64cbd4c631d532480015ab06080c2a109f6c1c374505100054f436a8a1a6008c6c655cb514840159d07328c488383931c86550d322762fb2ee6aa2a600ab481591434800147b08296ca98b3b17dd7735953049537410e1b2a6400c6c72d9551440010fb0e180ca908222fa1f64551105cd4f424c831a200087f8759753480011bb0e216c68814a3ba1b725451000637bb0e4a8ea07ce2c54553625440917d0fba2c6900032ddd07158d200062eb98e7b
  | 19 => 0x940340540481a40080d80140000011840240000600240b00f018402c0000000101280a003800800000001806000012c0680000480682e40086440000240704a4045a440100082ec00401801516cc580f80c801c13c0200300000003940040f002c04806c02801401000c00c00004822c0541206ec0d80000000580040043c811477c14424800006800400400800402cff40f40140080240000681140342f402c0381a41780a8008ff000015c0cc0780d000000000061c0040001780300f1b200180bc5e00ac02803802c00400000001c06c00400403c00049806800803c0240006540000040344582380000680e80000040000a80e80100f400009c0d404c0c00100340000f801803002440800409c6bc0000fc1180000b40200000240680140342083700283a401000410809c03001c00c1440040081b004002008402801000c00c07c13800000000001c04408404e594000c0c06000808001005c1d800006c38001800000c0001700240040000140083680600640ac20c0840080040140286dc0001fc1480680080dc00401403000801007807413011407030008801c00005c004168fcc0ec04800c0000000401203b000c5681f400444002401811801c1688f80699400046840140b00400000c006019800002c07400401c0203d40080b1bd000401023c0c001027c26c01009816064400c0186082280042882f004000000825048008c0213084401ac08c00000402000800000c04139c00426c0080002c80485ec05401c00000011c0100240242600080000806700000080000580c402c00401c0083b800403800800c00001800806000001c0000340a400001800400000c0d46e800007cbedcd401c01c0f002000053403436822025004c0000081b800073c11800401400000012c00001c0980a427800c00000401c0e40009c80040000080640490a803001838001801832000000002401cce41800000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x52800c30000001010000001c00c11400801001c3a4200014a0002760761187d975350c014659714821185500042766043dd9438840109d9810c7650d2000549650521c5654800148d9210f7650e210060b2187550d424800105f985cc73d952100619a0475dc962c40015459314871595200049925582104614800103f985d074d953235d07a5443dd9431440162594148211855000499255820c4614800184c861d5434c92000718148615c0514800143594148715952035c2766043dd9431440141d9399275d92210059164c52084615400141d9498e75d8e210060be187550d4288401a442160c10195210050764c641d5644800141d9418c7558d2000525650631c5634800145593148715952000417e61731cf65508012649160a401952176e19a0475d8921c40014969110c7650d1000523648431d9434809181d8361f65d514335c2766043dd943d4001a2421610101952100613e187550d328840103f985d074d95210052564c641c564480012649160a301952135d07a5443dd943d4001a60526002118550
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2200000000060000000a1869c5260021185500054434010b08080ca90802a41a0085830406548401520d18a4c004230aa0009032959210c7650d200054434829300108c2a800240ca564843dd94388401620d18a430ae028a4000b08690521857014520
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x400db82959210c7650d2000400db82959210f7650e21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x94b
  | 6 => 0x94c
  | 7 => 0x94d
  | 8 => 0x6
  | 9 => 0x138b
  | 10 => 0x138c
  | 11 => 0x138d
  | 12 => 0x98c
  | 13 => 0x98d
  | 14 => 0x9cb
  | 15 => 0x9cd
  | 16 => 0xa0b
  | 17 => 0xa0c
  | 18 => 0xa4b
  | 19 => 0xa4c
  | 20 => 0xa4d
  | 21 => 0x198b
  | 22 => 0x198c
  | 23 => 0x198d
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0d
  | 27 => 0x1409
  | 28 => 0x140c
  | 29 => 0x140d
  | 30 => 0xb49
  | 31 => 0xb4b
  | 32 => 0xb4d
  | 33 => 0x1449
  | 34 => 0x144b
  | 35 => 0x144d
  | 36 => 0xb89
  | 37 => 0xb8b
  | 38 => 0xb8c
  | 39 => 0x1489
  | 40 => 0x148b
  | 41 => 0x148c
  | 42 => 0x2c9
  | 43 => 0x2cb
  | 44 => 0x2cc
  | 45 => 0x2cd
  | 46 => 0xbc9
  | 47 => 0xbcb
  | 48 => 0xbcc
  | 49 => 0xbcd
  | 50 => 0x14c9
  | 51 => 0x14cb
  | 52 => 0x14cc
  | 53 => 0x14cd
  | 54 => 0x19c9
  | 55 => 0x19cb
  | 56 => 0x19cc
  | 57 => 0x19cd
  | 58 => 0xcc9
  | 59 => 0xccd
  | 60 => 0xd09
  | 61 => 0xd0c
  | 62 => 0xd49
  | 63 => 0xd4c
  | 64 => 0xd4d
  | 65 => 0x1a09
  | 66 => 0x1a0c
  | 67 => 0x1a0d
  | 68 => 0xe89
  | 69 => 0xe8b
  | 70 => 0xec9
  | 71 => 0xecb
  | 72 => 0xecd
  | 73 => 0x1a49
  | 74 => 0x1a4b
  | 75 => 0x1a4d
  | 76 => 0x1049
  | 77 => 0x104b
  | 78 => 0x104c
  | 79 => 0x1a89
  | 80 => 0x1a8b
  | 81 => 0x1a8c
  | 82 => 0x209
  | 83 => 0x124c
  | 84 => 0x249
  | 85 => 0x124d
  | 86 => 0x289
  | 87 => 0x1549
  | 88 => 0x16c9
  | 89 => 0x1849
  | 90 => 0x4c
  | 91 => 0x4d
  | 92 => 0x98e
  | 93 => 0x4b
  | 94 => 0x124b
  | 95 => 0x1709
  | 96 => 0x15c9
  | 97 => 0x168b
  | 98 => 0x12cb
  | 99 => 0x1889
  | 100 => 0x1609
  | 101 => 0x180b
  | 102 => 0x130b
  | 103 => 0x1649
  | 104 => 0x134b
  | 105 => 0x150c
  | 106 => 0x128c
  | 107 => 0xe8e
  | 108 => 0x18c9
  | 109 => 0x1789
  | 110 => 0x180c
  | 111 => 0x130c
  | 112 => 0x17c9
  | 113 => 0x134c
  | 114 => 0x150d
  | 115 => 0x128d
  | 116 => 0x168d
  | 117 => 0x12cd
  | 118 => 0x1949
  | 119 => 0x134d
  | 120 => 0x5c9
  | 121 => 0x749
  | 122 => 0x14c
  | 123 => 0x14d
  | 124 => 0x140e
  | 125 => 0x24b
  | 126 => 0x28b
  | 127 => 0x16cb
  | 128 => 0x184b
  | 129 => 0x28c
  | 130 => 0x154c
  | 131 => 0x184c
  | 132 => 0x20c
  | 133 => 0x154d
  | 134 => 0x16cd
  | 135 => 0x20d
  | 136 => 0x24d
  | 137 => 0x20e
  | 138 => 0x19d4d1
  | 139 => 0xeccd5
  | 140 => 0x18cb
  | 141 => 0x178b
  | 142 => 0x188c
  | 143 => 0x160c
  | 144 => 0x5cb
  | 145 => 0x44c
  | 146 => 0x17cb
  | 147 => 0x164c
  | 148 => 0x170d
  | 149 => 0x15cd
  | 150 => 0x104d14
  | 151 => 0x74b
  | 152 => 0x44d
  | 153 => 0x194b
  | 154 => 0x164d
  | 155 => 0x150e
  | 156 => 0x74c
  | 157 => 0x194c
  | 158 => 0x17cd
  | 159 => 0x178e
  | 160 => 0x18ce
  | 161 => 0x20251
  | 162 => 0x20291
  | 163 => 0x24211
  | 164 => 0x25411
  | 165 => 0x21451
  | 166 => 0x216d1
  | 167 => 0x145411
  | 168 => 0x28211
  | 169 => 0x29411
  | 170 => 0x21491
  | 171 => 0x21851
  | 172 => 0x149411
  | 173 => 0x2c211
  | 174 => 0x2d411
  | 175 => 0x214d1
  | 176 => 0x219d1
  | 177 => 0x202d1
  | 178 => 0x14d411
  | 179 => 0x25551
  | 180 => 0x29551
  | 181 => 0x2d551
  | 182 => 0x28251
  | 183 => 0x29451
  | 184 => 0x25491
  | 185 => 0x24291
  | 186 => 0x148251
  | 187 => 0x149451
  | 188 => 0x2c251
  | 189 => 0x2d451
  | 190 => 0x254d1
  | 191 => 0x242d1
  | 192 => 0x14c251
  | 193 => 0x14d451
  | 194 => 0x2c291
  | 195 => 0x2d491
  | 196 => 0x294d1
  | 197 => 0x282d1
  | 198 => 0x14c291
  | 199 => 0x14d491
  | 200 => 0xb0211
  | 201 => 0x42d3
  | 202 => 0x21411
  | 203 => 0x44994
  | 204 => 0x44995
  | 205 => 0x25451
  | 206 => 0x1a57d1
  | 207 => 0x29491
  | 208 => 0x1a9951
  | 209 => 0x2d4d1
  | 210 => 0x2d253
  | 211 => 0x2cb53
  | 212 => 0x2d453
  | 213 => 0x2cb93
  | 214 => 0x2d493
  | 215 => 0x1242d3
  | 216 => 0x45414
  | 217 => 0x45415
  | 218 => 0xb4253
  | 219 => 0xb8293
  | 220 => 0xb8294
  | 221 => 0x24b55
  | 222 => 0x5d2d3
  | 223 => 0x5cb53
  | 224 => 0x5ce93
  | 225 => 0x45894
  | 226 => 0x1a57d3
  | 227 => 0x75313
  | 228 => 0x74b93
  | 229 => 0x74e93
  | 230 => 0x45715
  | 231 => 0x1a9953
  | 232 => 0x2d4d3
  | 233 => 0x17da55
  | 234 => 0x195a94
  | 235 => 0x1a57d5
  | 236 => 0x1a9954
  | 237 => 0x2c053
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2243
  | 6 => 6700
  | 5 => 2554
  | 4 => 42
  | 3 => 9
  | 2 => 2
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/880+packedAt gbK7 (82991+(h % 880)*12) 12) % 2243)
  | 6 => 2*((h/2233+packedAt gbK6 (321600+(h % 2233)*13) 13) % 6700)
  | 5 => 2*((h/879+packedAt gbK5 (150686+(h % 879)*12) 12) % 2554)
  | 4 => 2*((h/35+packedAt gbK4 (2940+(h % 35)*6) 6) % 42)
  | 3 => 2*((h/17+packedAt gbK3 (729+(h % 17)*4) 4) % 9)
  | 2 => 2*((h/7+packedAt gbK2 (184+(h % 7)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7ff80ffffc07ffffc07ffffff4279e3e71f1ff
  | 1 => 0x83fff0703ff83e03ff83e03ffbda69c7ae4e4f
  | 2 => 0xfc1fff803fffc003fffc00380c1c71f9cf8f8c
  | 3 => 0x1fffffc0000003ffffffc00fe07e01f00ff0
  | 4 => 0x1ffffffffffffc000000000fff8001fff000
  | 5 => 0xffe0000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4200080440042884004288a2000821a009095
  | 1 => 0x8348b0321948341194834115c1ca28c4a6464a
  | 2 => 0x68155b842e96802ae96802a06c1451694b8b8c
  | 3 => 0x211e6d5e80c210433e7397008ee07c01f00d60
  | 4 => 0x421f8e6f33e739700c2104010f7f0001fd6000
  | 5 => 0x7384080803042180304218060fbfffb6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_38493
namespace PEqualNP.Outside.L_meta_38493
open PEqualNP.Outside.L_meta_38493.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 19 := block_range (n:=19) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 19 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 144 := (concat bs0_4_0 bs0_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := bs0_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 84 := block_range (n:=84) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 84 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 90 := block_range (n:=90) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 186 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := bs2_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 6 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := bs3_4_0
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
  · exact alls3_2 i (by omega) hi
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
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 90 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := bs4_5_0
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
theorem bs5_3_0 : Interval s5Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 8 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 9 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 9 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 42 := block_range (n:=42) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 42 := bgb_4_0
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
theorem bgb_5_960 : Interval gbAtlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 58 := block_range (n:=58) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2554 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat (concat bgb_5_864 bgb_5_960) (concat bgb_5_1056 bgb_5_1152)))) (concat (concat (concat bgb_5_1248 (concat bgb_5_1344 bgb_5_1440)) (concat (concat bgb_5_1536 bgb_5_1632) (concat bgb_5_1728 bgb_5_1824))) (concat (concat bgb_5_1920 (concat bgb_5_2016 bgb_5_2112)) (concat (concat bgb_5_2208 bgb_5_2304) (concat bgb_5_2400 bgb_5_2496)))))
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
theorem bgb_6_1920 : Interval gbAtlas 6 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 76 := block_range (n:=76) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6700 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 bgb_6_672))) (concat (concat (concat bgb_6_768 bgb_6_864) (concat bgb_6_960 bgb_6_1056)) (concat (concat bgb_6_1152 bgb_6_1248) (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536))))) (concat (concat (concat (concat bgb_6_1632 bgb_6_1728) (concat bgb_6_1824 bgb_6_1920)) (concat (concat bgb_6_2016 bgb_6_2112) (concat bgb_6_2208 (concat bgb_6_2304 bgb_6_2400)))) (concat (concat (concat bgb_6_2496 bgb_6_2592) (concat bgb_6_2688 bgb_6_2784)) (concat (concat bgb_6_2880 bgb_6_2976) (concat bgb_6_3072 (concat bgb_6_3168 bgb_6_3264)))))) (concat (concat (concat (concat (concat bgb_6_3360 bgb_6_3456) (concat bgb_6_3552 bgb_6_3648)) (concat (concat bgb_6_3744 bgb_6_3840) (concat bgb_6_3936 bgb_6_4032))) (concat (concat (concat bgb_6_4128 bgb_6_4224) (concat bgb_6_4320 bgb_6_4416)) (concat (concat bgb_6_4512 bgb_6_4608) (concat bgb_6_4704 (concat bgb_6_4800 bgb_6_4896))))) (concat (concat (concat (concat bgb_6_4992 bgb_6_5088) (concat bgb_6_5184 bgb_6_5280)) (concat (concat bgb_6_5376 bgb_6_5472) (concat bgb_6_5568 (concat bgb_6_5664 bgb_6_5760)))) (concat (concat (concat bgb_6_5856 bgb_6_5952) (concat bgb_6_6048 bgb_6_6144)) (concat (concat bgb_6_6240 bgb_6_6336) (concat bgb_6_6432 (concat bgb_6_6528 bgb_6_6624)))))))
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
theorem bgb_7_1248 : Interval gbAtlas 7 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 35 := block_range (n:=35) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2243 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat bgb_7_288 (concat bgb_7_384 bgb_7_480))) (concat (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)) (concat bgb_7_864 (concat bgb_7_960 bgb_7_1056)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1248 bgb_7_1344)) (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632))) (concat (concat bgb_7_1728 (concat bgb_7_1824 bgb_7_1920)) (concat bgb_7_2016 (concat bgb_7_2112 bgb_7_2208)))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
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
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88eeeaeae8eaeaea88
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 3941264008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38493.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.or,[5,6]⟩,⟨.and,[4,5]⟩,⟨.and,[3,8]⟩,⟨.and,[2,7]⟩,⟨.or,[6,10]⟩,⟨.and,[0,11]⟩,⟨.or,[1,12]⟩,⟨.or,[0,10]⟩,⟨.or,[9,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941264008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941264008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38493

open PEqualNP.Outside.L_meta_38493 in
theorem PEqualNP.Outside.L_meta_38493 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941264008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941264008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
