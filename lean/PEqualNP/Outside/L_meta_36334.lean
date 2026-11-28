import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36334.Model
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


end PEqualNP.Outside.L_meta_36334.Model

namespace PEqualNP.Outside.L_meta_36334
open PEqualNP.Outside.L_meta_36334.Model
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

def SBf (j : Nat) : Nat := [7, 4, 7, 5, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36334

namespace PEqualNP.Outside.L_meta_36334
open PEqualNP.Outside.L_meta_36334.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x344068000ace00000128352602222204024542119714007853a086283c593864c4c0093284f920050a8e00805873668300054300200128b2c4ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1c818011979a080000000b9a800000001900000017028002180000000022001024001b800c1d258b0c8000141f000018801580000eaaa600098000001496121100000a8e0d012a2c0896800000000000071f92a1a0998000038005a10d800000000f00000513a3802b8000000a000000000000000f890000000400001c24802510800000002913002ca2801e8007a7a680000006801b00000028a8008000201d83298015049e002b2706002300400080404101408040400042004040000000c000c0c04080030000400027ca5a1cf55243b7a92876c5250f3ea6a1ebd49439e29287ac5250e58a4a1cf950439ea9c853e5290abca6215754c42cf298853d5310b3aa6214754c429f29085ae5210a7ca9994f55332cea1e65ac42ccaeca3995d547329faa4653c548ca7ea8994f15132cea1a653e540ca7aa8196b10832b7a92836c52506bca620d754c419f2a6633d54cc73a8798db94b31b6a96639d434c67ca818cf550319f2a4433d54886bca710d754e21d6214433f5448678a890eb10821af29e815d53d02dca5205b54a409f2a6613d54cc33a87184f950309eaa0619d430c2dca4185b54830bb2886175510c35885904f952209eaa4413f5448278a89057d4d20ae29a41ac42482eea2905d145209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2600078002c0003a442a000028502c1c29820c1a212e6a048058504e14a201030c6254c42a318943cca8d6310b32c910a51ccb15435473287195434ca2d6510832a318943cc70d4354b31a3189434c62c6255031a358c428870e5310a218758c544868d63108218b18954cc28c6250e30a3189430c30d4354830c550d510c28d6310b208758e548828d6310920c314c42483244214520
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xa811a000008282b988528e65411c9435473281aed2988510d047250d510c206bb0a621241415cc4214520
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s0K4 (2670+((h/30+packedAt s0K4 (2430+(h % 30)*8) 8) % 172)*8) 8
  | 3 => packedAt s0K3 (998+((h/8+packedAt s0K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s0K2 (302+((h/2+packedAt s0K2 (294+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 2 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 3 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2004088824020000a41280444022914810d095
  | 2 => 0x451891064894a12c0a852429921422b146264a
  | 3 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 4 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0fcccfcc0fcccc0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36334
namespace PEqualNP.Outside.L_meta_36334
open PEqualNP.Outside.L_meta_36334.Model
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
  | 0 => 0x1fffffe07ffffc0ffffc0fffff81fffe78fe3f
  | 2 => 0xe07e07ff81f81ff0f07ff07c0ffe0f81af33cc
  | 3 => 0xff8007fffe001fff007fff800ffff001cfc3f0
  | 4 => 0x7ffffffffffff8000000ffffffff003ff
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc104202304108401108c42946188528c085615
  | 2 => 0x4b18aa451ca2acb074355258a6aa4b14ab32cc
  | 3 => 0x862d348a2874d557085a6b114b4d62294dc370
  | 4 => 0x1451c71051461a6aad0308420c718c71f001aa
  | 5 => 0x1861861c61871b8cce638c6380610841f6a800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaa0000faaafaaafaaa0000faaafaaafaaa0000faaafaaafaaa0000faaafaaafaaa0000faaafaaafaaa0000faaafaaafaaa0000faaafaaafaaa0000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36334
namespace PEqualNP.Outside.L_meta_36334
open PEqualNP.Outside.L_meta_36334.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xb0011124007401012ad695383d496264462636000000048f821a1c425425c01a323852730a83003ca02a028b0001068c0110032408c32d300004a052ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x917d354ca41000c521249504295c00310114c93d584ccc010850002c0068ecac0000e000d0700c9cdc0130004400a00058014000b94800000001192971600000000154e4480000a800c00024000098d9781c008c4019740080007c00e80000010c014460000000000000f800f400006c0039511d2c1400b400000000003c01102001880000000001685c0835800000d4796cbc0455840088b0000164f00000fc007538008464000000040000140802000000000a020006042600021c060400000a1804000006020206073d5490edca521db54a43cfa9a873e5410edca421db54843af298855d5310a7ca9994f55332cea1e656d538cb5e87196b50e32b728c659d434caeea2995d14532e7a9a65af434cb9c86996b50d32e6a1a658d434cbcea2995b14532f228a6564514ca7ca8194f55032b7290655e53d06baa7a0db94b41b6a96836f52506d8a4a0cf953319eaa6636e52cc6daa598e750e31b7a92636c524c67ca818cf55031cea18636e520c6daa418de94031bca80636f53886daa710ebd0e21d6a1c436e51886dea610db54c21d7a1843ad43086dca210f994421f398843e431086dea4a05b14940af298815d53102dca4205b54840bb2888175511027ca9984f55330cea1e616e52cc2daa5986750d309f2a0613d540c2dca4185b54830bb2886175510c2eca3105d546209faa2413c54483c843885b94a10b6a94213f5444278a88857d4d10ae29a216f52442d8a4887908510
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xe4820140050131c93c334100b40420600a00044c00608065287154314532a3592434cb8543d4532c350c514cb854314532c9d0c514cb464314532c950c514cb454314532c150c514cb0d4354831c650d500c70f5350e21c354d4308665650c421e150c31086e1600c421c350d52cc2646154b308758c54483445308510
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x880006056550c3108740a1ac0188438150c6154b30
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s2K5 (826+((h/15+packedAt s2K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s2K4 (2937+((h/33+packedAt s2K4 (2673+(h % 33)*8) 8) % 172)*8) 8
  | 3 => packedAt s2K3 (833+((h/7+packedAt s2K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s2K2 (150+((h/1+packedAt s2K2 (147+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ffff81ffc3fe0fe1ff0ffff87f03fd23f39f
  | 1 => 0xf81f0ffe0ffc3ff0fe1ff0e07f87fc1edccce7
  | 3 => 0xffe00ffff0003fff001fff007ff8001f1f0f07
  | 4 => 0xfffffffc3ffffe000007fffffe3e00ff8
  | 5 => 0xfffff000000003ffffffffff80000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x3042008c2084000120230123180908c401518b
  | 1 => 0x12c4111465005050620d1045288258484cc4a5
  | 3 => 0x618eaa28c3aaaab71116aa0a75503193170f06
  | 4 => 0xc510cc410a220b2a954088104664a303a00a50
  | 5 => 0x861888718c3333ccd998cc9c0440c203faa000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800eeeeeeaaeeee8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36334
namespace PEqualNP.Outside.L_meta_36334
open PEqualNP.Outside.L_meta_36334.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffc0ff87f843f87f87fff87f07f8093f73c
  | 1 => 0xf0787ff0ff87ffc3f87f8703f87f83ff6cc9cf
  | 2 => 0xff807fff0007fffc007ff803ff8003ff8f0e0f
  | 4 => 0x7ffffff807ffff800003fffffc01f00ff0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x6110046210800804809809198091188c01531c
  | 1 => 0x250088a2400a0081882882288825092424c145
  | 2 => 0xc23551443555455c44555053550232598b0e0a
  | 4 => 0x8a466208a441566a55044082664a6011d00ca0
  | 5 => 0xc64438cc66667b3666664e0440c4061fea000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0eeeeeaeaeeeec0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36334
namespace PEqualNP.Outside.L_meta_36334
open PEqualNP.Outside.L_meta_36334.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8437c53086fca410fbd0821f621043ef32087d86410df94421fb98843f431087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81be439037887205f94a40bea94817e51902faa3205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c52502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea94617e518c2faa3185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617c514c3bc6298770c530fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4185f94430bea88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83dc43907b08720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220fda0441f840883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920f719241ed32482fea2905f14520f710a41ec21483f680907e10120fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52843dca5085b94a10bea9421ed52842daa5085f14a10bea8c217e50843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42ef29c855e5390afaa7217754e42aea9c857e5290b7e85217bd0a42bf28c857d5190afca1217e94242bd284857d5090bf2a1215e54242bfa9a857c5350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332efa1e65dc43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0f7d4d41afa9a837c53507b8a6a0d714d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498fbd4931b7a92637c524c7d8a498db14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f7d0c31ee218637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fb98e43f431c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef42887d88510fbcca21f6194437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea9
  | 2 => 0x800000000000000007b40020644c2e800000000000ca1a3000588ee000000000b792500035400000000000000000009282822710a000001a6000000000000007b800215000000000000000000004e00000000000000834000000000000021f00058ca80000006840000031a001028000000000000000054800186000000000000008a80017f3ca0000000000400000000000000000000009180008e000000148000000000026208a000001c10003a4e380000000000000000000000f8000000000000000000000025c000f400023e000000002be1cc00000000000000f3000000000000009308493545658487000000000298cd3ee000b71950005e000000254000c280000046000000000488000000000000000000000000169000000000bf000000001bf000000001fb0000000010a000000001ce0000007801e33e000c08000000000006200000000000000000ed20200000000000000000000ee3ec001248e100044400a4f00000000000000000000002aa05c00000000000000002f8000f10001e8000000201f600016890000860000940000000001f118000000000008387e8003ae904000750ec000000000002b83b8000c20000000000000000000000000000004b400000200000001320002040000000000000000000322000000f14760012c0000007500000012299400000000000d880022a0001e000000000000000000000000000000000069000144000000000000000015e0000010d0000011a00033628400000000000000a6000000e11c8000364000002a200000000366000000000009540019211e388001bd0000000000000000000000000671008002e6000000000f00008380000c00000170000000000000000000000000000000000080000ae80035a000001f22505e40000000038000000000000078000000b800000262000000000000d0cd06e4728f0000000006400006a000000000003180011c000000000000000000000040000000000400000002000008000000000000600200000803000000000010060000000000800001806000000010050000040000300000c0080100a0080100000a00c018000000000180000000000002002018000000040000080000400000801000004000020040000080000600400000000000008000060000000000a00c008000000000000100200c02000000004000000000040000100000c000030020100000100c000018000060000100300200800000002004000010020040100000000000000002008000000000000000500400000000000000000040000000000000400000000002000000000020100000000000000000002000000010000000000100400401800000014010020000080100000400000000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x2362d800000000330730000008c80000035800000000000000000000000000025c000000000000000003c9054b22f80924d45c000b38931ee8505a8b1000530000580000004d80000006c000000000000000000000079216000000001a70004f00015600083ced80000000044800076000000130000000000000070c000000000003d10c44a000f7a673aa340002290420000009d01613c0024205800000000010590000000009843680000000000250000000000ef00000000000000000001bb0c60008e8000000009d0004486d00009a25a35c00000000000001192ee000000680000000009500000067943000000e50002f600000000000000500fa3ea6005120a3440000011a290000652402bc180c5244000000001cc0002580000038a0dc000000000a8000000000000014400027c00000000000b413600039c2a0240000000000017a00011866028784a48000006bc3882229a0000000005e0001280007419c0000028290c4e000000000000000000000014e000000000000002e04f0000002b40000046a00072a1700000006800000000000000000000000000000108a080001540011c33200000000152000f480000000000000000000000002cc0600700000079d0ca221ba7788925f47a00000000146000001981be4500000000000000000000000000000180004c0003c60c0000000000011b85d000000000000bc148ff800000000000000004d000000000000cb0001b4064000000000000000000000000000000000000000000011d00a000000000ac000780bb0000000000025436e2ecc123008221c000000ae0cc001b51d6000000000000000015a39e0003d8000007d0000000000000000028a000000000000000012100000000000000000000000000007400049663c0000049c000000000ac00116800000400000000000d5018000002200000000050832933000528000003ba00000000000000001a5000000001b000000000000000000a380000000000000000000000001da0000025e0000e00000000000110000000000000000000002200900000000000000000000000000c5318004660992880000045c1399d10481c0000000084c000003f20000000047c5c8001c94a6000001580007f40020c00000000000000000001930000000010b000000001fc30e000001b2000000b50000967cc7a8b42560000000007e7400000000020c00000000000000e4000000000000000000006435291d090420b82a06400000000099000206565331571fc40400000000000648000006f8000003be000458000000000000010c0000000006c00000000000000000000000000000000000002800000000401b800029c00000000000000000001fc0a843000000000000000000012045e0000000040835800000072001118c40000000e
  | 4 => 0x14b05000000000000000001d3450124001a4000000918000000000000000000000000000000b2800000000000000000000000000000000000000420378000000000019e000360000002a82f0521970000c8000cb3407e85ba520066ac0896d27a7a800000000000f20000004a4d71740004c0158740001b00000009a00108000000000238000000010d0100000000000000000000000000000000000004180021e164000261160000005580038c0000000000000000000000000000000000012e8003a2000f31380000000d0000e4000ec8000b40000b0001020002d8002d8000960001bc000468ec316638000d100000000126000000002090be000000004c0000000920000000000036c00071a0b00000118848094000000000000012d8000000000015b000000000003e27ac581d6000314020a524e0009200045831c9c800000000000001f22640007e000000000004900005c9cb25e6a000000114000000000000000023f0007b0000003a40000000046c3040014f0000000015c0004fc00000000000000000000000000043a001228d43f000000000000000bd000186000000004380000000026e000c48000000003e0000000000000000073400000000000000000fa00000000000000ff0ff37800000000000000000000006101f0aa23c000000000000000025721e0006d8000000000000000000059800000000e006b0000006980000000023000436318000fc0005f4000003e0000c1975442000380000004f8820001b87100017128030800000310000038001a4580b5913000338000000000000017e3b06a80001c000000001101ec30000097000000dd0590000001e8840003a80000000000000000000000000000004ed2b00028c00000000000000001b9000000a9800000000
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xd51d026f62547409b18951d035853d0140c714e40503586054c40c754e431034e5394840d354e521036a6094840d394d521034d5354840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440dc181511023f6550040a718d401027b6550040b618d40102d86050f30b518532cc26f62547309b18951cc2d96310330e690c40cc26e62152309b588548c27661152309d584548c23e649513097d8d544c27b60551308f994544c31d631513097996434c31c5490d3097195434c31c5450d30b6181434c31c54cc930c7151324c2d4614c930c7152314c2da608c530c7150314c33854cc130c7152304c26e62d50309b58b540c25e63150309b988540c26d62150309d984540c275611503097597430c25d6510c30d3d0d520c34c4354830da54b400c2796510030e610c400c3695210030d354b300c369528c03097d95300c29c644c030d3549300c27b654c030ae191300c369524c0309798f54c825d63d53208f99353c823d64d4f20b358e42c82e4614cb2097d8d51c825c6354720ab59021c82cd6308720d954421c825f63552209718d548825e63152209758c548827661152209d584548827661d4e209d58753883395410220b658c40882f16110220ae191308825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d18553482cd6390920ba982424826c65509209b19532482e4614c920ab59021482cd6308520ba980214827a65d0120b658c40482ea6210120bc5844048278654c120ae19130483c9324c1209798f540825d63d50209e983540825e63150209758c540826e62150209d9845408275611502097596530825e6314c209b988530827a6014c20d354f200835953880209bd95200834d53480209ed95200835953480209798f54c425d63d53108f99353c423d64d4f108f99052c423d6414b109798c52c425d6314b10bc18141c42f161103109798f548425d63d52109b98b548426d62d52109798c548425d63152109b988548426d62152109b98b538426d62d4e109b988538426d6214e109798f528425d63d4a10d394e528434d5394a10da982528434e5354a10d354d528425e6314a109758c52843595388210d654d208436a524821097d8d544425c63551109bd89544426c62551109ed81544423f6454d108f191534426f6254d109b189534423f64549108f191524425f63549109718d524425e63149109758c524427465505109e195204425f63550109718d540425e63150109758c540426e62150109b588540427661150108f990530423d6414c109b988530426d6214c108f990520423d64148109798c520425d63148109e980520425e63940109758e500426e62940109b58a50042796510010ce550400427965840109dd95100427b6544010
  | 1 => 0x10c00e0081103c0101c05000000000a0100300401000060180700400004010000301402000000001301c0000c0b03410004100000a00000000020141000400024060a00004000000020540200001008019e98252d0e796094b439b9885050e6d6214143d6d0c5050f3a4314143da9885050f6962141438fd954310eb86050c4397d954310ed86050c439bd895110e6c6254443d694e5090b595394242d694d5090b5953542429798c5050a5d63141428fd954210a6f655084297d8d5110a5c63544429ed8154cca7860553329e983548ca7960d52329d986544ca7561951329dd85544ca7461551329ed81544ca78605513297997434cace62d0d32d5d0c514cb544314532d9cc8514cb5632145329798f540ca7a60d50329e583540ca7661150329d584540ca7a60150329e580540ca5f654c832b5185320ca6f654c832b9185320cb5b3254032da8c9500cb593254032da4c9500ca5e6394b419758e52d067a6094b419e58252d065e63942419758e509066e62942419b58a509074f53d4941d314f525074f5314941d314c525072c52d0941d6d4f505075853d4141dad4b505076852d4141d6d4c50507585314141dad48505076852141418fd95411067765504419b98b54cc66d62d53319e98354cc67960d5331b518532cc67a60d52319e583548c6d9600ca319b98a508c66d62942319b98a544c66d629513197d8d544c66f62551319b189544c67b60551319e181544c67a60149319e580524c76a6014931da580524c65e65cc931d314b324c74c524c931b5185324c76452cc531d314a314c67b60550319e181540c66e62150319b588540c67a60150319e580540c65d6510c31c7550430c6d56110c3197596320c6d9600c83197d95310c6cc624c4319dd95310c6e4624c4319798f54c865d63d53219e98354c867960d53219e98053c86796014f2197d8d548865c63552219ed8154886786055221ba580328865e63942219758e508865e63951219758e544865f63551219718d544866f62551219ed81544867860551219798e534866f6254d219dd85534865e6514d21d514f214874c53885219798f540865d63d50219e983540867960d50218f596540872c62550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c21d318953087546154c218f990530863d6414c219798c530867a6014c219e580530872d54d08219b59442086e56110821d354f320866d650c821ba580320875553cc421f1ccb3108675650c421f10c8310866f6548421b318d21086776548421b518d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500865e6394b409758e52d025f63547409718
  | 2 => 0x1cab0bf0741123e0018646000c819400212002caa7b380032e4b800350000000016b28a023c000fe9d988950b8002023982c8a99617b1600300000fc198b6001f6c281aab20e4d290af12c841fe51a4a0c800bd800671d6290009c2188a07e610bec91b42e83c7509e000420000037000000d294a9236a323c800378004c0c41b0c2851560c116229a685800cd800002de3da6c000003591e9f164002ce668ce2b0a67c0902522466098bf8d86d8008691205ad8002e6a6902002d0000045fa8673b089d106180b4889723d2e45e04c5a10e0d1c210084690ea1badc00000880008e1cc1aab6380b0469ea989ae000826a8c645332002ae628ec388000022ec4800b303600128000009e000520a0000aa15b220024242af4c401c0030691078a080015000001f8ca800b0b26c6aa05f00090132532a8ba14225a580e21e019c6af8007615ab18b2149f48e940422b28da8e4e2984f9bc2384a2a2840492608960741b86789c68154c31003b98e6400006092cc1ac632f00025aa207a60aa4598141c30e7e8cc7a00c000a23e800aeab4a58000024c541205d0807b858001dc000ca03a66588c04f234cb1040031800020b011c001be341ec0029cce80000000000000000000050831e400000000000000000268120000020a76af8432720022681828001e68000000000b1264000000e9702316e00000c7a7e493020015c529e2002e0972ee9221c3a2a2028000b9101887ca5026002f253800001d27c800001584d85c5aa56939b06c8c8002a6bb3348b1ca118769b8f0b53044aa04002c80013aae0000417a000007828c77888578aeb6886191c4392d626922be80009000001c0000009e83e8c314b8800c716c07980649ba0a8bc1a2500000000260b4800a2800000003e0000026a5d94482152ba9a213a46000000025eaa8007f1c8001a800000008080040002c0304401008000082f0001601c01038000080002005000040100102423000000a80003402000050280700807008020000101003018030040000c01008000380003c180380e03001000020000300809010010040301c0200
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x5422c55c100024000030050060d0004160ca1c811318f48e44008002186101325c262d0d32a8ce5a18a299550714c9500cab038a64a8065525c0524c931a30e0aa08618cc472584430c6a4b80c4a9843911886154c21988e6b088410dc1700c831086a4b90c0a9881861506050d30992e4302869861454185324c30c2a4c118a61325ca608c530e1086a90801860c64549300c314322a498061511cd5108720a30e6aa08110688644c930482e038a6498241461cd5410010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x6800004020941809cb4314532a41801886154c21c08545c86050d30c08545ca608c530c80641c5324c120
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (18887+((h/205+packedAt s4K5 (16632+(h % 205)*11) 11) % 1740)*11) 11
  | 4 => packedAt s4K4 (17112+((h/138+packedAt s4K4 (15732+(h % 138)*10) 10) % 546)*10) 10
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s4K2 (304+((h/1+packedAt s4K2 (300+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf81ffffe03ff841f0f8ff1ffffc3fc040cfe7c
  | 1 => 0xffe07e1fffffffe00ff0fe1c07fffff87333ff
  | 2 => 0xffff801ffc1ffffff000ffe007fc3fff83c38f
  | 3 => 0x1fffe007ffffff000007ffc007fc03f0
  | 5 => 0xffffffe0000007fffffffffff8000007fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x48c30d0238412c03418530a471e2643404563c
  | 1 => 0x11491024490a00a006905208924489503130d5
  | 2 => 0x6284254890d4254d5004a4c124aa32a582c30a
  | 3 => 0x47165991228736766b260082473320c6dc03e0
  | 5 => 0x84186001c31843988c48c913800003036ba800
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeac8c0c8c0feeafeeac8c0c8c0feeafeeac8c0c8c0feeafeeac8c0c8c0feeafeeac8c0c8c0feeafeeac8c0c8c0feeafeeac8c0c8c0feeafeeac8c0c8c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36334
namespace PEqualNP.Outside.L_meta_36334
open PEqualNP.Outside.L_meta_36334.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c817e52902faa5205f94640bea8c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c53502fea4a05f14940bfa8a817c51503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461de328c3b865185f94630bea8c61df318c3ba63185f94230ef98461fb308c2fea8985f95130beaa2617c544c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617c514c3bc6298770c530fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa418778c830ee190617e510c2faa21877cc430ee988617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83dc43907b08720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220fda0441f840883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc84907b50920f719241ed32482fea2905f14520f710a41ec21483f680907e10120fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52843dca5085b94a10bea9421ed52842daa5085f14a10bea8c217e50843f481087e50210fd98421f830843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd20221f940443f660887e0c110fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xe5390afaa7217754e42aea9c857e5290b7e85217bd0a42bf28c857d5190afca1217e94242bd284857d5090bf2a1215e54242bfa9a857c5350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332efa1e65dc43ccbdc85997b50b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65de438cbba87195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6197790c32eea18657e520cbdc84197b50832ef99065ee320cbba64197b4c832bf288657d510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0f7d4d41afa9a837c53507b8a6a0d714d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53107bca620d794c41bea9883dd53106baa620df94841f7290836e52106faa420fb54841b6a90837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7b88718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118fe94231bd284637d508c7f2a118de54231bfaa2637e544c6faa898df15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f7d0c31ee218637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef42887d88510fbcca21f6194437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487dc8490fb50921fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ef42087d88410fbcc821f6190437e51087de4210fd88421f690843f521086fca010fe94021bd28
  | 2 => 0xe0001980043c0014b2473922bd198000006b4bb0002b045c001963e09749113b0006146017722c1dc118b300000000000000000001b04c20e47a0002b6434fa8001160000015908a698000002209d90c06744e001268000000011c00000000000006000150000002686f4000004845c80000003c00055000000001090000008b00010a4100000000000000051800000000000df1de00000000000000000003bc0104880003e514c88d10008dc001930005b80022233c000f28002182d11d800086444002660005002827c000a3d158000000000018d3ce001298002c6000639d10fc000000000002dcb50e64d873d4480000000036a794ce5f4848c200000111a950000000000000011c390000005c4fb80000000000000270000002973f097c0012b1647c85e87926c9fc661aa2d61c40013d4b269000130000000b300007a21cc580036e000000000002850086c0000ac991133a89b8b080025a000d71f11d693000175234411328fe0bea44d4095494a00002864c682c002004aa640631192e8000878004d60992800000000000000000000520000006280100033a090000000000008100e00000000000000a340000000000026204000000002741a60001f1d70640f0000001904a01106b0148d4fc9ef3d080cde114000000001ac000000e18a800076c818fd3cc5b4000004b8178000000006611f9b3000000001050945288381233e474001671a0000000000010040040080d0080240000100000403000022004008010020040000102000005800000000018010000000100000002c02800000000028000000040080000406c00006008014030020080000100200c0000000000600c0000602600802809006004010020000040000200c008028020000080080f012004000020000140100200001003000004000018010060100200100e0040000a0020040280000000401003002000010020000040100000a00000005000004000020000040280400001c00804000024008030100000380000800001007000018000020020000000100e00000000000000030000000200800b00400c0000000203004807002008010040040100100a0000040000400000000007002000008000020040080100000000000000004008070060040080000200001003bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e85de53d0abca7a15f54f42eea9e855d53d0afca3a15f54742bf286857d50d0afaa9215f94e42ef29c855
  | 3 => 0x7607d00006e540539a900087042a3e0ec2c00012329600000000000000000000002d4fb219000000000000000000000820c7284b80049c524b49a30b472c5c9434e64610289b1f2714bf1dd364a2c70a6d3aa051130e33e62ec8425a11c0000000039a000000000009c0348360000000000000000c0000000018c00000000000028700001580022e000000000000000013880009e0007aa2a4640012000003600000000000218ed19700061c0c0a60006640018c00000000092000000510003d2574000400000000017026e15c3307d088338ee00021c684002680008e8a10004c49c879800388700d2a5e00074cd894e1881b80b8002021844ca8a33620018800038000001b80000a467800000000170002c47fc9d10b000138720fc0b89180004b01a0d0f5a2f434000000000007640009f1b000000249000000001352c00849fa880822a4da0002f62801000000095d0f8000000001f8000000b4da800472000000001dc000000003c451c6f1d6000000000bc2000000028c000874001e42ca6483020d0b2000001c215a7314807b2a4258dd8000d01208d800000000000000000004e800000001420e8000174000002f22242300117c35c002114b64909780015c840a62563084a5168d2488000710d900085c3a0005269600000028c5bc960004960010b1573d485000000000000000003e88d0a08651ee5cc001441b8001148ea50a3ecd58000000001380038c1e0001b60005fc0012719a6204689e0000008e00029e1bc89000000a38e095e340000588f202a00104800000000001e1102000000194140001296c00000000058000000002833d8000ce0000000011e8e73340009893e03a368001ee3c02ac000003f8000000160000000008f000000000000009140012e0000004d20e43636c001820000a8320001ba78c000001f0000098520000000000005e03c000000002405f9812429200000000001cef800000a48ad26f44a9500000037e6f8000001820000002c0000453200034400000000000570049830205913b8d5528000648a535e188dd15600024cfd8004265213d9680503280022132a000000940009f8c3000000000420000000014113350e000dc84229a83d3c1fa0009a41d80000000070000000208658000000003e2360000682a800158001300000005e0fe800000000001c70003c40000018a031350000000008f0000000000017a1ac000000000000000000000000128800000000001203121349e1ed2be81c618003900000017c118394440000001cc000000000001823031c0000027d39c47c001264488a0000000703c09c9531143a4248984623d8e828124a9d4000510745511e07a4869e85c2152a22e84e0001fe0000000031e3b000000000000000000008300000022a00035194106000000000ea9047680b0f
  | 4 => 0x2d80034e000aa80025480829a4f0009480022006a748c00d40007f8000000000000000040c0005b000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5434c2d86050d3097997324c2da608c53097994314c26e62d50309b58b540c25e63150309b988540c26d62150309d984540c275611503097597430c2ce62d0c3097594430c34f4354830d310d520c25d658c830d354a320c34d520c830b6580320c34d52cc43097d95310c2cc624c430d3549310c36952d00309e594400c3695210030bc584400c34d52cc030da54a300c25f654c030d3549300c27b654c030da549300c25e63d53209758f54c825e63953209758e54c823e64d4f208f59353c82cd6390b2097d8d51c825c6354720ab59021c82cd630872097d8d548825c63552209798c548825d63152209d984548827561152209d987538827561d4e209798e518825d6394620b658c40882f161102209798e544825d639512097d8d544825c63551209dd85544827461551209798e534825e6514d20d358853483596014d20b358e424834c5390920ba982424826c6550920cb151424834c5350920d314e324826c654c920d314e21482ad6408520b358c214834c5308520ba980214827a65d0120d614f40482d96310120d614c40482ea6210120bc5844048358538c120f28ca3048278654c120f24c9304825e63d50209758f540827a60d50209798c540825d63150209b988540827661150209d584540825d6594c209798c530826e6214c209e980530834d53c8020d654e200826f6548020d354d200827b6548020d654d200825e63d53109758f54c425e63153109758c54c426e62153109b58854c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c42f06050710d694f40c435a5310310bc58440c425e63d52109758f548426e62d52109b58b548425e63152109758c548426e62152109b588548426e62d4e109b58b53843586054e109b988538426d6214e109798f528425d63d4a10d394e528434d5394a10da982528434e5354a10d354d528425e6314a109758c52842d86350210d654f30842e9620c210d654e20842d86348210d654d208436a5248210b698f108425f63551109718d544426f62551109b189544427b60551109798c544425d63151109b988544426d62151108fd91534423c6454d109bd89534426c6254d108fd91524423c645491097d8d524425c63549109798c524425d63149109d195414427a65901109e19540442d863501109e99730442e9620c1109e19520442d86348110bc18520442da63c411097d8d540425c63550109798c540425d63150109b988540426d62150109d984540427a60150109e983530423e6414c108f590530426e6214c109b588530425f63548109718d520423e64148108f590520425e63148109758c520427a60148109798e510425d63944109798e500425d63940109b98a500426d62940109e59740042796510010bc584400427965840109dd95100427b6544010
  | 1 => 0x74d5354841cb54b411063f6550441cb54941106776550441d694e50107595394041da94a50107695294041d694d50107595354041da94950107695254041dc905501077141540419b98b54cc66d62d53319e98354cc67960d53319b98a54cc66d6295331b618143cc67a60d52319e583548c66e62152319b588548c67a60152319e580548c6ce62d0e31b6580328c66e62942319b58a508c75b4394231d610e508c76a6294231da58a508c75a3294231d60ca508c75b31942319b98a544c66d629513197d8d544c66f62551319b189544c67b60551319e181544c65e6590d3197195434c6d86050d319e980524c6796014931d390c524c74d4314931da980524c769601493197997324c74c52cc931d3149324c74c528c531b6982314c67b60550319e181540c65e63150319b988540c66d62150319e980540c679601503197597430c6ce62d0c3197594430c65d658c831b6580320c65f654c431b3189310c677654c4319798f54c865d63d53219e98354c867960d53219798e54c865d63953219e98053c86796014f2197d8d50c865c635432197d8d548865c63552219ed81548867860552219798c548865d63152219e980548867960152219e983538867960d4e21b398f42886e9600ca219798e508865d63942219798e544865d639512197d8d544865c63551219bd89544867b60551219e181544865e6394d219bd89534865e6514d219b996424874c53909219b195424874c5350921d314e214865e63d50219758f540867a60d50219e583540863d6595021cb189540863e64150219798c540865d63150219b988540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c21d3189530863e6414c218f590530865e6314c219e98053086796014c219b597420872d54d0821b398f420866d6510821cb550420872d54cc821d354f320866d650c821cb55032086e9600c821cb553210866f6548421cb55121086cc63484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500865e6394b409758e52d025f63547409718d51d026f62547409b18951d025f6354a409718d529025e63946409758e519035853d0140d6181531034e5394840d354e521036a6094840d394d521034d5354840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440dc181511037151900408fd95401027b6550040b618d401037151500409b98a54cc26d6295330b618143cc26f62547309b18951cc2da608c730b658c40cc2f161103309b988548c26d62152309d984548c2756115230b398b438c2d9600ca30b3189318c26e62951309b58a544c25f63551309ed81544c25e6590d309719
  | 2 => 0x2c48140018700000000000098000000000007400000000000000000000000050003380000000000000000000000778000000004f00017600000000000000490fa0000000005880004a000450001da000000000fc00000000212000000d70003a40000041a000000000000000019f000000048190000000000000000000000000000000001ea000180000001a0b39b600000000183272000f58002c080000000000000000000000000f800270000001212e450c0012d000000000000000000080000055400000000000df00000000000000000774000e60b6748e79e8000000b400024c00c0000023a510000b000068400000000000000000000000000010c39c0019029e000000000000000040000000000001802002004000010000000000100200000002004004008000000080000000000000000002000000020000000000200000401000000000008000020000080000000c00007002000000010000080100000000000000002000000010000040000000000000800004000000020020000000000001000001000004000000040000200000000000001000004000000020040000000000400001000000000030000000000000800000800002000008010020040000400000000000002000010020000100080100200000001000000028010060040000100a000000020060000000000000000000000010008000000027a6094b439e58252d0f6a6094b43da58252d0ece62d0e439e9825190e796094643b398b4350e6e62141439b5885050f5b4314143da9885050f6962141438fd954310e5f6550c43b61814310e6f62544439b1895110f4c6254e42b398f4290b5a5394242d654e5090b5a5354242d654d5090ace63d09429798c5150a5d63145429e9805150a7960145429798c5050a5d63141428fd954210a6f655084297d8d5110a5c635444297d8d5010a5c63540429ed8154cca786055332b398b43ccacd6390b329e98251cca7960947329e983548ca7960d5232b6181438ca5d63951329b58a544ca7761551329d185544ca7b60551329e181544ca5e65d0d32b398b434ca5e6510d329798f540ca7a60d50329e583540ca7661150329d584540ca7a60150329e580540ca5d6590c3297d95430cad86050c329b596420ca5f654c8329bd95320cb5a4354032d650d500cb6a4254032da509500cb5b3254032da8c9500cb593254032da4c9500ca7b6054f419e18153d065e6394b419758e52d067a6094b419e58252d065f63543419718d50d066f6254e419b189539065f6354a419718d529065e63942419758e509066e62942419b58a509074f53d4941d314f525074f5314941d314c525072c52d0941d6d4f505075853d4141dad4b505076852d4141d6d4c50507585314141dad4850507685214141d394e521074d5394841d394d521
  | 3 => 0xf790c00000000012000364000000000000000000064c000003e2144001c500038c00000000000000001a6444001971c2000000000ec00002000000000001ae0007180012800083ca08000002f0000c8000000000000000000000018c4800000000057c4b80000078c690ee000434c20000000000000000000000105000000000000000000006c000254ae00000000000000000000000000000000000000009800000000000318002f80001b800000000cb0003b0001060000000000000032800000000000000000000003f80000000000000000000000000e00000005e800000000000980000c80004a302000000000000000000026c000000000000000000000000000000000000000000000003800028e76820800000000fb0000000000000000033c0015b000000f20000007e0000000005f400000356000000dd00000000000170000000000000005d000000000001ca0007b8c28f302e00000000000000919c40000000006f000000000000000540000000000000000000544031d700000000000364000001e10ac0000014e000624000430000009d00032a000428000b0000000000002100000000000000000050000300000000000000010e00000000000000000c90000003c800000000000001123a83e000000000000de1501900695e1520000000000000000000000000b780000003c0000000017800000000000ab8000000002300000045c0000000017d088771d076cac0621aa03000000000100000a10000009e800000000000000004b00018f000000910f8000000000a500000000132166000000000000000000039c0000012a000000000233f45c400000000000000000007f8e99ec0000000002a000370000000000003c03338e000000000000000008f1ac000000000000000000000000000000000244b68000560000001e2d26f0f68000006b40016600000000000000000000000000005c8000000000d800040000a2a09000000000000000000a0003a8508001e006c1500013400000037000000000b5800000000000830000000007a11a000000003845d08000027c0006a14939200000000000460d3800000084000000000000000005c2fc0e881314000000002040007c8000000005a00000000000000000000000000003c0000000001841c000000000530aa4300000000000058c000000000003d8500000000000000012508000000000a01532ea000000000000010501c0000000000023611c220000000000719d000000000001d68680000000000000000000000560f4322534000001d81c48a000000000d9800234000ae80000031c00000000660000000004c50086a352000000590003380000000000000000000268098d11be5900000031c4c05180035402c001650000000000036a6ec3f8000000680c00000000008
  | 4 => 0x14c00000000000000000000000006a018800000000cd8000ba0000017a0000000003e000000001250004d40009c0005ec00000000308fd9b400000000000000000000000003410700029629040000208564001f7000000000000000000000034600000000000000001b122478800000000000b7000000000001a600000000000252000000000000010b80014e000168000000001216c3242b41e83c1de000001330000008c8000001480000021c0e4000000000000004b000818ea8000000005580013e0e8e69c138686400000052000000000007580020207e00000000000000000e20ea62cd0000000000000000004dc8391c0000000021200000000000000000ef8003ca80c0007d00000000000000000de800000000001a5000000f5000000000e58000000000017e000000358000000000005718019ca400000026cff80000081c00000000000729d925c0000000004e000808000005c0001ac000000001151f47a4000000000002e0000d2518001ba000000000001ec0000000023e000000002d4000000002ac000000000a60084580000000000000000000000000005dc0000000043cb98000000000000036e138390000cc5e00008c000000d8000000000c320b000000000bb000000001f30002d4001e7294000e60c33907440000000000000000216000001162a400062000000000001b900000000000000000000730000000000000000000000000540b089400a7f46d800000000000c10000000000000000000000000000000000004ec00000000000000000000000018d2f224c0009e00016800000000000000fb22600000000000288ad0004100000000000000000000000000000fc11c690668000000000000033c00000000000000000000000000000000000000214000000958002a80006d0001fe00000000000000f3000000000000000000000017f000000000000006fc0009613a0000000000084c720003b88102780000032c001080000000004d42c00000092344478038f20006bc0000000000000000164000000000000005f000000000000000000000010a000000fe0450000000000000070000000000000440003ea4fc000cc0000000000006a0000000000000000000000000000000000880000000000000127000000000000006e02418000005800034332000f80001040000018200000000000000000000000002dc0000000000078800000000001f92061085780000000000000000000000c5000000000990da00000000000000000000100000000005e668000900760000000016c00000106000000000000000000011014063057055000000000110000000000000062000000000000000000003f40000000000065065000854000000e84bc000001ee0b06c000000000f9000000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x840b00744c6032420003c04c600a00e0445d458548d54018806a807529cb4314143a92e0312a7214c97098b434caa53968728463521c14314931a92e02926498e4852982314c6a4b80c4a98438355263d0821c52a8b006410e0d5418d21086a4b90c0a98819418d5150040992e430286984c972982314c330a92c220061925896014d2089aec29c849044d7614c2148306b20a610a41165d85310120ca0a6b0880906525358440c42a4b90c0a9c21161d95348210
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x41804000849869cb4314143849869cb4394231849861c143149318498714a608c531
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1164)*11) 11
  | 4 => packedAt s5K4 (22451+((h/179+packedAt s5K4 (20482+(h % 179)*11) 11) % 1673)*11) 11
  | 3 => packedAt s5K3 (1265+((h/8+packedAt s5K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (244+((h/1+packedAt s5K2 (240+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe07ff1fe07fc21f0f1fc7f07ff0ff020dce7c
  | 1 => 0x3ff83fe1ffffffe00fe1f87f81fffffc3273ff
  | 2 => 0x3fffc001ff87fffff001ff8001ff0fffc3838f
  | 3 => 0xc0000001fff803fffffe000001fff003fc03f0
  | 4 => 0xfffffffe000003fffffffffffe000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x9231863027109603430ac2911c78991a04c63c
  | 1 => 0x845088024101002005204823049122281050d5
  | 2 => 0x18a212548a3612cd50099304292a8cd2c3830a
  | 3 => 0x11c72c9914639b766e4c020a51ccc8637c03e0
  | 4 => 0x21043000184421988891244c60000081ab2800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeec8c0feeec8c0feeec8c0feeec8c0feeec8c0feeec8c0feeec8c0feeec8c0feeec8c0feeec8c0feeec8c0feeec8c0feeec8c0feeec8c0feeec8c0feeec8c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36334
namespace PEqualNP.Outside.L_meta_36334
open PEqualNP.Outside.L_meta_36334.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c18001ffd50077f5401ff95007fd5401df55007fc54027fd4c09fe53027f54c09fc5301ffd0c07fe4301ff50c07fc43027fd4805fe52027f54805fc5201ffd0805fe4201ff50805fc42007fcc805fe32007f4c805fc32027fd4409fe51027f54409fc5101ffd0407fe4101ff50407fc41007fcc401fe31007f4c401fc31017fc8401fe21007f48405fc21027fd4003fe50027f54003fc5001ffd0003fe4001ff50003fc40007fcc003fe30007f4c003fc30017fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x824001ff4c120007f26090007fc3048003ff9024002fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007fe1048003fd0824001ff04120057fecb8802aff65c4015ff32e2004bf99710057facb8802afd65c4015fe32e2004bf1971004ffec988026ff64c4013ff3262003bf9931004ffac988026fd64c4013fe3262003bf1931004ffea9880277f54c4013ff2a62009ff5531004efaa988027fc54c4001ffb1e2000bfd8f10007fcc788002fe63c4001feb1e2000bf58f10007f8c788002fc63c4015ffa9e200aff94f10057faa78802bfc53c4013ffa1e2009ff90f1004ffa8788027fc43c4001ffb162000bfd8b10047fcc58800afe62c4001feb162000bf58b10047f8c58800afc62c4015ffa962008ff94b10057faa588023fc52c4013ffa162008ff90b1004ffa8588023fc42c4001ff9962008ff8cb10007fa6588023fc32c40037f30e200affd4710057fca38802bf651c4015fea8e200afd54710057f8a388027ff41c4013ff20e2009fd9071004ffa8388027f541c4013fe20e2000ffcc710007fc6388003fd31c4001fe18e2008ffc8710007fc4388003fd21c4011fe10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe8218801fff654400f7fb2a2007ff99510025fcca8801ffd654400f7eb2a2007ff19510025f8ca88017ff644400b7fb222005ff9911001dfcc888017fd644400b7eb222005ff1911001df8c888017ff544400bbfaa22005ff9511002ffaa8880177d544400bfe2a22000ffd8d10005fec688003fe63440017f31a2000ff58d10005fac688003fc63440017e31a2007ffd4d1003ffca68801ffd534400ffe29a2005ffd0d1002ffc8688017fd434400bfe21a2000ffd8910005fec48801bfe62440057f3122000ff58910005fac48801bfc62440057e3122007ffd4910037fca48801ffd524400dfe2922005ffd0910037fc8488017fd424400dfe2122000ffcc910037fc6488003fd324400dfe1922001bfd851003ffea28801ffe514400ffb28a2007ff5451003feaa28801ffc514400bffa0a2005ff9051002fec8288017fd414400bfaa0a2005ff10510007fe6288003fe3144001fe98a2000ff0c510037fe4288003fe2144001fe90a2006ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001fe9011000ffa8088017f94044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044001fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3ff21cc001ff10e6000ff48730087f84398006fd60cc003ffa866001ff9433000ffaa198007fc50cc003ffa066001ff9033000ffa8198007fc40cc003ff1866001f78c33000ff46198007fc30cc003ee1866001ffc833000ffc4198007fc20cc003ff0866001ff0433007ffeca9803eff654c001bfb2a60009fd953007ffcca98012fe654c01ffeb2a600fbf5953007ff8ca98012fc654c01fbe32a60049f19530077fec89803aff644c01dff3226003bf99130077fac89803afd644c01dfe3226003bf19130077fea89803b7f544c01dff2a2600eff55130076faa89803bfc544c0037fb1a600fffd4d3007ffca69803fde534c01ffea9a600ff754d3007ff8a69803bff434c01dff21a600ef790d30077fa869803bdd434c01dfe21a6000ffd8930005fec498037fe624c0057f3126000ff5893006ff8c49800afc624c01fffa92600dff9493007ffaa498037fc524c01dffa12600dff90930077fa8498037fc424c001ff9926000f7cc93006ffc6498003fd324c001ee992600dff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c01fffa8a600fff9453007ffaa29803ffc514c01dffa0a600eff90530077fa829803bfc414c001ff98a6000ff8c530007bc6298003fd314c001fe18a6000f70c53006ffe4298003fe214c001fe90a600dff0853000dfec098007ff504c003ff2826001ff5413000ff8a098007ff404c003ff2026001ff5013000ff88098007ff304c001fd9826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000ffe4098007fe204c003fd1026001ff0813000ffc2098007fc104c019ffb2a400cbfd9520067fcca90012fe6548019feb2a400cbf59520067f8ca90012fc6548017ffb22400bbfd912005ffcc89000efe6448017feb22400bbf5912005ff8c89000efc6448017ffaa2400bdfd512005ffca89002ffd5448017beaa2400bff15120007fec690002ff6348001ff31a4000bf98d20007fac690002fd6348001fe31a4000bf18d20067fea690033fe5348019fea9a400cff14d2005ffe869002ffe4348017fea1a400bff10d2000dfec49000bff5248005ff2924002fb94920017faa490033ed5248005fe2924002ffd0920017fc849000bee4248005fea12400bfb50920017f8849000bff3248005ff1924002fb8c920017fa6490003ed3248005fe1924000ffd8520005fec290003fe6148001feb0a4000ff18520005f8c290033ff5148019ff28a400cff54520067f8a29002fff4148017ff20a400bff5052005ff88290003ff3148001ff18a4000ff4c520007f8629000bff2148005ff10a4000fb88520017fa429000bfc2148005f610a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fd1
  | 2 => 0x21007de651080bfe3288405fe9944202ff0ca21017d8651080afe6188433ffa8c4219ff946210cffaa310867fc5188431ffa0c4218ff906210c7fa8310863fc4188401ff98c4200ff8c621007fa6310803fc3188405ff90c4202fbc8621017ee431080bfc2188405fa10c4200ffd82210bffcc110806fe6088401feb044200bf582210bff8c110806fc6088433ffa844217ff942210cffaa11085ffc5088431ffa044217ff902210c7fa811085ffc408842fff1844217ff0c221017fe411080bef2088405ff1044202ff082210bffc211085ffc108842dffb2a4216bfd95210b7fcca90812fe654842dfeb2a4216bf595210b7f8ca90812fc654842bffb224215bfd91210affcc89080efe644842bfeb224215bf591210aff8c89080efc644842bffaa24215dfd51210affca890857fd544842bbeaa24215ff15121007fec690802ff6348401efb1a4200b7d8d21007fcc690802fe6348401feb1a4200bf58d21007f8c690802fc6348401ee31a4200b718d210b7fea69085bfe534842dfea9a4216ff14d210affe8690857fe434842bfea1a4215ff10d21015fec49080bff5248405ff2924202ff54921017f8a49080bff4248405ff2124202fb90921017fa8490857ed4248405fe2124202ffcc921017fc649080bfd3248405fe1924202bfd85210b7fea29085bfe514842dfea8a4216ff145210affe8290857fe414842bfea0a4215ff10521007fe6290803fe3148401fe98a4200ff0c521017fe429080bf72148405ff10a4200fb88521017f8429080bec2148405fa10a4200ffd8121005fec090853fe60484037f3024200ff581210a7f8c090806fc604842dffa824214ff941210b7faa090853fc504842bffa024214ff901210affa8090853fc4048429ff1824214ff0c121017fe409080bfe2048405fe1024214ff841210a7f82090847ff65cc0277fb2e6013ff99730025fccb9804ffd65cc0277eb2e6011ff19730025f8cb98047ff64cc0257fb266012ff9933001dfcc99804bfd64cc0257eb266011ff1933001df8c99804bff54cc025bfaa66012ff95330097faa99804b7d54cc025fe2a66001bf98f3009ffea798047fe53cc027ef29e6013ff54f3009fbaa798047fc53cc025ffa1e6011ff90f30097bc879804bfd43cc025eea1e6011ff10f3008ffec598043fe62cc0057f3166000ff58b30005fac598047fc62cc0057e3166013ffd4b30087fca59804ffd52cc021fe2966012ffd0b30087fc859804bfd42cc021fe2166011ffccb30007be6598043fe32cc001fe9966000f74cb3008ff86598047ff61cc001ff30e6000bf98730007fac398002fd61cc023fe30e6013ffd473009ffca39804ffd51cc027fe28e6012ffd0730097fc839804bfd41cc025fe20e6011ffcc730007fc6398003de31cc001fe98e6011ff0c730007b8639804
  | 3 => 0xf3226222ff59131115fac89888bfc644c4077e3226222ffd5131116fea89888bfe544c445feaa26222df55131117f8a89888fff534c447ff29a6223ff54d3111ff8a69888bff434c445ff21a6222f790d31117fa869888bdd434c445fe21a6200ffd8931005fec498803ef624c40177b126221ff98931015fcc498803fd624c443fe3126202bf18931007d8c49880aec624c447ffa926221ff9493111ffaa498887fc524c445ffa126221ff90931117fa8498887fc424c401ff9926200f7cc93110ffc6498803fd324c401ee9926221ff0c93111ffea29888ffe514c447fea8a6223ff14531117fe829888bfe414c445fea0a6222ff10531007fe6298803f7314c401ff18a6200f78c53110ffe4298887fc214c401ffb026200bfd8131107fcc098806fe604c401feb026220ff1813100df8c09888fff504c441ff2826223ff54131107f8a09888bff404c441ff2026222ff50131107f88098883fe304c441fe1826221ffc8131107fc4098883fc204c441ff0826220ff0413108ffeca18876ff650c43bff3286204bf994310effaca18876fd650c423fe3286204bf1943108ffec818872ff640c439ff3206203bf990310e7fac818872fd640c423fe3206203bf190310e7fea8188737f540c439ff2a0621cff550310e6faa818873fc540c43f7f318621dffd4c3108ffca618877fd530c423fe298621cffd0c3108ffc8618873fd430c423fe2186211ffd88310dffcc41880afe620c401feb106200bf5883108ff8c41880afc620c43bffa90621bff948310effaa41886ffc520c439ffa10621bff908310e7fa841886ffc420c423ff990621bff8c8310dfbc6418803fd320c423fe190621bf70c8310f5fcc218877ff510c43bff288621dff544310eff8a218873ff410c439ff208621cff504310e7f88218847ff310c401ef9886200ff8c431007ec6218803fd310c401ee9886200fd4c4310dffe421886ffc210c423ffb00621aff9803100dfcc018803fd600c4017eb006211ff1803100df8c018877ff500c435ff280621dff540310d7f8a018873ff400c435ff200621cff500310d7f8801886bfe300c423fe180621bffc80310d7fc401886bfc200c435ff080621aff040310cffecb10866ff6588433ff32c4204bf996210cffacb10866fd6588433fe32c4204bf196210c7fec910862ff6488431ff3244203bf992210c7fac910862fd6488431fe3244203bf192210c7fea9108637f5488431ff2a44218ff552210c6faa910863fc5488401ffb1c4200bfd8e21007fcc710802fe6388401feb1c4200bf58e21007f8c710802fc6388433ffa9c4219ff94e210cffaa710867fc5388431ffa1c4218ff90e210c7fa8710863fc43884057eb144202ffd4a21017fca51080bfd5288405fe2944202ffd0a21017fc851080bfd4288405fe2144202ffcca
  | 4 => 0x3fe614c801feb0a6400ff18532005f8c2990b3ff514c859ff28a642cff54532167f8a2990afff414c857ff20a642bff5053215ff8829900bff214c805fe10a6400ffd8132005fec0990abfe604c8037f3026400ff58132157f8c099006fc604c859ffa82642aff94132167faa0990abfc504c857ffa02642aff9013215ffa80990abfc404c855ff182642aff0c132017fe409900bef204c805ff1026402ff08132157fc20990abfc104c823ffb2e6229bfd973114ffccb98812fe65cc453feb2e6229bf5973108ff8cb98812fc65cc423ffb26621fbfd93310fffcc99880efe64cc43ffeb26621fbf5933108ff8c99880efc64cc43fffaa6621fdfd53310fffca99887ffd54cc43fbeaa6621fff1533114ffea798847fe53cc453fea9e6211ff14f310fffe8798847fe43cc43fef21e621fff50f310ffba8798847fc43cc423ffb166228ff98b31015fcc598803fd62cc4017eb166211ff18b31015f8c5988a7ff52cc451ff2966229ff54b31147f8a59887fff42cc451ff216621fff50b31147f88598847ff32cc401ef9966228ff8cb31007fa6598803dd32cc423fe1966229ffd473114ffca3988a7fd51cc453fe28e621fffd07310fffc839887ffd41cc43ffe20e6228ffc8731147f84398847ff60cc44fff3066201bf98331007fac198802fd60cc423fe3066201bf1833114ffea19889ffe50cc453fea866227ff143310fffe819889ffe40cc43ffea066227ff1033113ffc6198847fc30cc451ff9066227ff8833113ff8419889ffe10cc44ffe0866226ffd9631135fecb1889bfe658c4097f32c6226ff59631135facb1889bfc658c4097e32c621effd92310f5fec91887bfe648c4077f324621eff592310f5fac91887bfc648c4077e324621effd52310f6fea91887bfe548c43dfeaa4621edf552310f7f8a91888afd638c44dffa9c6226ff94e31137faa71889bfc538c43dffa1c621eff90e310f7fa871887bfc438c401ffb146225ff98a31015fcc518803fd628c4017eb146225ff18a31015f8c51889bff528c44bff2946226ff54a3112ff8a51887bff428c44bff214621eff50a3112ff88518803ff328c44bff1946225f78ca31007fa6518897fc328c44bee194621cbf98631137fea31889bfe518c44dfea8c6226ff146310f7fe831887bfe418c43dfea0c621eff10631007fe6318803df318c401fb98c6225ffc863112ff84318803ff608c449ff3046201bf98231007fac118802fd608c449fe3046201bf18231137fea118893fe508c44dfea846224ff142310f7fe8118893fe408c43dfea046224ff10231127fc6118893fc308c44bff9046224ff88231127f84118893fe108c449fe0846223ffd953111dfeca9888ffe654c4097f32a6223ff5953111dfaca9888ffc654c4097e32a6222ffd9131115fec89888bfe644c4077
  | 5 => 0x1e00001800000004008030060100180402a004000010100040000500e00000800000040090020200000e8050000040000101600401000008000050000020140000000c02400000022004008040040200180a00601400802002018038040200100080000000c0000104800c00000004020030070080700300300203c0180d000000000000040000a80300000002000018004000090040080680000801000800000010000070000300000000403c00000002000000000000000180c00002c0181600000001008000004000040160000000100802000018014004000010000100980d0120000080a0080000580b000000000010000000b80000405c0000001803c0000001c00c008000000080100d0000100080b00000000003000014000070080280102b00603c0400700e0000381800000801000002000000000000200100100000c0480200c01c0200100c0080080400e0040e8020000100000202800803801002000020000040000080000e008000070040200880001000c010000000000300b002008000080000000000600200423ffb2e642fbfd973217ffccb99012fe65cc85ffeb2e642fbf5973208ff8cb99012fc65cc823ffb26642ebfd9332177fcc99900efe64cc85dfeb26642ebf5933208ff8c99900efc64cc85dffaa6642edfd5332177fca9990bbfd54cc85dbeaa6642eff15332015fcc7990bfff53cc823ff29e642fff54f3208ff8a7990bbff43cc823ff21e642eff50f3208ff8879900afd62cc805ffa966402ff94b32017faa59900bfc52cc805ffa166402ff90b32017dc859900bfd42cc85df6a166402ff10b32017fc659900bde32cc805f71966402ff0cb32017b86599047ff61cc801ff30e6400bf98732007fac399002fd61cc823fe30e642fffd473217ffca3990bffd51cc85ffe28e642effd0732177fc83990bbfd41cc85dfe20e6402ffc8732017f8439900bec21cc823ffb06642dff9833200dfcc199003fd60cc8017eb066411ff1833200df8c1990bfff50cc85bff286642fff5433216ff8a1990bbff40cc85bff206642eff5033216ff881990b7fe30cc823fe1866402ffc8332017fc419900bfc20cc85bff086642dff04332167feca990b2ff654c859ff32a6404bf99532167faca990b2fd654c859fe32a6404bf1953215ffec8990aeff644c857ff3226403bf9913215ffac8990aefd644c857fe3226403bf1913215ffea8990af7f544c857ff2a2642bff5513215efaa8990affc544c8057fb1a642cffd4d32167fca6990b3fd534c859fe29a642bffd0d3215ffc86990affd434c857fe21a6402bfd8932017fea49900bfe524c805fea926402ff14932017fe849900bfe424c805fea126402ff10932017fe6499003ef324c805ff1926402f78c932017f8649900bdc324c805f61926400ffd8532005fec299
  | 6 => 0xa674a1f80000004020005c67560006640000000006600002760000000001e60000005b404c0000003940001464800de00000000061e65a35e5808e872c46000047a1cc9764c072a0000006760005fa49278a4a01ac38a9701f40120d600000073e00077800000000000000005c8a079600088400028c2fc00060c01670e1b42362123dc8c68de4662f41663ae5600009aa9866be77a26209c8100ee95e19421c4c60000000009066c008400081254e00092e0000000006900000000000000740003569a08cc99c72420e6560000000007a60000006a40480000000005127aa0c200068a3fe0008ec2464989025c800057c03200082a00076831c5242ae62600000017c4aa31a7d667405e00047c24c0006b421000000017a0001ec22c6380002744d674e85261298a6ba01a97209895a06c0000000000d832c0006bc2e25b070699a8e64821bc00018073c00000000033600000065800013a7a222e0000005d00008d27b497800000000000000088000000068800000000006a0000000000000000003bc00000000037218a00036c0002963306d24fa6e20006e43d80000000f80002ac0360b61de00000000010c00000044c6a00002942568907865da08e0ae76c5968fc4b24f414a75470a0f605238000004e0000000006ee7dc0009a481e9925784cc07e8f40002060006f00d200000000001e1aa4880008a689a00000056c81897e5f61ea07c73456a09067c86227071e00000034a00000071a5ce0000000002fa2f87300000a00001540000004d45386042e80885aa00071400000000083800045200000014023a1928c280e4ca83600033885604045c80493c5dc00000088e0000004ec00079839c0bc79e1d63920007b20002488786182042d61b259a5ee4322821a820c3ca50e1303ba83e99689c26447e4149460649320000000007720000000000005ec00090e00e0000000008d82000505e074c1ce8684ea8ba6d000000000071000016e4bc7d40001ca47875e61a7c864400000015200000076e4507428b884200085072696e67e7a81c437c49662e3ea7ac1dc3486403e84a48f842893a7c63160c072e2ea8ac03a1766205d43f406060e92214e14484e14226c00000045e0008e054430000043864a94800053e0680aa46e0180000005fe3b02fe3f041800059c48e60800000071200089415600098400e01c04800020000018010000180000c002000050020020000000d00c0280000300e0300800200400401012012004018010000000000801000807008004000030010020000000200c0000080800a0001081400000402005002000010000000040700101600400021000000010000000100080301800400802006040008090020040000002e0040000000a00400005002000048000000180001b0040100080200201400800000000000
  | 7 => 0x60008d600049a00000000033e0008582d40080009360000005de7187d00002b88bc00027812e00000000079c67a0e000040a3b471611a3c27fe51a5680022505c239a6e000038241e58e24e0005480000000000008fe23c3466ce0000009183c03688a84580000000000008f60286061a04e25ae0005560000006929420200003902ce83454a0002180000000000a48247e848c43c7da2a268293416a6fa3de7743544723ac1742da98210431434000027e8466fc0004c87be0007207629680008261320e62ee0000000000001c800050c00000000000061400000000064e4ce9940000000b20003aa1e032a4300009a624029c3082262c60000b068c1200001c62987520000000000040fa0fe81a52a64600000084a5e67924d85cc6982923246420823e609a2a60f41b69668d44700001f65180000000700000000000008b03883d00000003be0003980001086a627a7ae0000000007f600000000049450640859200000068022835a0007b60004fc0000007e600000026a0002220003d26628fa02e00010018443402419600000078885e7640004426360426d443668e2d05306fe00002c5645ba4de3e020a25e48a12c58a70028e94c3789806520002e469e2600f07760004b813c2be0000000000004be0000000003da00000000012200000044e00000000000000a0008300000004f22a095c4a67fc0001fc7ba5722804ee0002201025c069c0003a20000000000000004e824438608a00050262434c00017019800041090a67207662c44072858c2908f232e58218c62267050a19c52e7ce0f24dc0007902bc6da7ca24a2082240007d80003200006861820d06ca5540006b05285f27c43125fc8446b611e59006677c0006b230e8e40000004066b807a22a6540007e00008e200000033256237066c0000000000000ea6cc2e01603e200000066e0000003a809e35000085c13866a0860001a28be0004e400073a00000000053a49c76600000084800092651e0005087225a67480004b400042c0002544b00000005c40007f20ba1e20000006ac36a3662525045a43d60780ac7448067c00000c86ae0004040007080004ae33c57e8740009747ec36039699000000000088881437498e69423023e0007949ae40e68400052600008c9b264c00000087287e4e67de00004a33a9080dc00047400076000000000000060a00051c0000000005b600096a0007380006660003440007b00001e85366321685f866800055000000071c2a42387c205a0be0000006000002cc39e70c0448c442474654235c91e1067ea9508ca30a0b458876a38c44a69a2ec8c81d015e2423b21f27824f65e882c4d07584226d66500001ae00000000092a3280002b240000091c80209257a1100001fe0000ca00000000063c8b200000036e00057021e0000002c46280000
  | 8 => 0x2868ce6109129640004ba0002580000000001140cc94e81c0566347a40007402020001c01640340a880a52c00086a3640da46a03029e2b09600008d00004f821a0002f26ea1240a237a8f07801f000002a9563620007f86ec6c431e01081675a10e0002a800000000000000003e0000000000005000000001d417e0000004ac46c01400000030600028a4840004562f00005e400098c00096200055e9ac2d200000094059497a00015c6de2b65d28545660003fc00041a1c25407323c86780006dc0006f29b09143f294a48600000006200000055a57600012a3b61ee6f400097c00034286005802207264800083c89254600000011683233480c5b800049e3ee0002c06a20000002341d20c41b80000000000380003a46024484b621642e1880e282295400092800061c27c5ea7a05985861263520008200000000000005100002d80000000e41ba78465e79a3260000008400000004544640008dc8863f877e1fa1488b600000063e56e41287c0262b48662e60000000005ac65c93e90c84c62a0005a813e00000000000005400085a27200000075029a54c0001127365a24440000000002143e40000000fc3b85ca00083a87a0007d23fa06e0965be01c8282c28760000001866c20002840b812826800c2f63ce7041906f64a84907708703104682de3cc51688c0006f81366307f46a89521620e84168ea0003580001a68b40008644d21da00000000098826691000008025c0000ce0000009a80d45e20008da5f42325206e80002dc92c7e44c40000006e64da13459e42a8a469600000000000000043a4260005d837e00053c00092400016c3ec2ca1e49208c00063768ae5bc3c431842040c55c4467ee17219a18e1501b02ba86c91a3f64c21787b83023221a400063a0001583d48987fa5b251411c00019e89e4a293826e1183a00001d80004fe0008820002884f00008ee52278c5a030414c8a288a0c678e0ec80803c0000000006d85d67cc6aa15a0009985345580004627e20000949043845522c85746c800025a4e075c0000000007028aa00000000000000041c00095886e30c6166c67f04769161be0460000002aa00045a00000096c38e3c68969305f000010a9a299e9007bc34e00094453200058480000082e00000043e0003a
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd7018d1000cfc7018d1008edf3018d100d6dd3018d10014fe76d8910036ee62d8910004ff75d8910024fe75d8910004fd75d8910024fc75d8910004ff74d891001cfe74d8910004fd74d891001cfc74d89100067f54d89100067d54d891008cfe73d8910004fd73d8910036ec32d8910014fe71d891000cfd71d8910014fc71d8910036ef21d89100bcff70d891000cfe70d89100bcfd70d891000cfc70d89100beef20d89100beed20d89100057f755891003d7c7558910005bf745891002dbc7458910005df7358910005dc7358910036ec62589101bdf77158910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe7458910004fd745891001cfc7458910006bc745891001cbc74589100067f54589100067d5458910004ff7358910006df7358910004df735891008cfc7358910006dc7358910004dc73589100bcff7258910006ef7258910036ee4258910006ed42589101bcff7158910006f77158910036ec21589100a4ff7058910006fb705891008cff76cc910004fe76cc910004fd76cc91008cfc76cc91008ede63cc910006dd63cc910006ef62cc910016ec62cc910004ff764c910004fe764c910004fd764c910004fc764c910006de634c910006dd634c910005f7714c910005f4714c91000cfe76cc51000cfc76cc510006df63cc51008edc63cc51000dfa70cc510005f970cc5100d4fe768c510006de638c510006dd638c51008cff764c51000cfe764c510104fd764c51000cfc764c510006df634c510006dc634c510005ef724c510035ec724c510005fb704c51000df8704c510124fe760c51008ede630c510006dd630c5101b4fe7688510016ee6288510006ed628851000df87088510014ff764851000cfe76485100a4fd764851000cfc7648510005df7348510005dc7348510006ef6248510016ec6248510005fb704851000df87048510035f87648110016f87648110014f876481101adfb74481101adf9744811019f7b544811019f795448110006fb6348110006f9634811000dfb724811000feb7248110007eb6248110016fa6248110016f86248110037e86248110037ea52481101a7e95248110037ea424811019fe94248110037ea3248110007e93248110007f37148110005f87148110007f0714811000efb614811000ff361481101a7f251481101a7f1514811019ff2414811019ff14148110007ea2148110037e8214811000dfa76c411000efa76c411000cfa76c4110195fb74c4110195f974c41101877b54c41101877954c4110005fb72c4110005f972c411000dfa71c411000ff271c411000efb61c411000ff361c411018ff251c411018ff151c4110187f241c4110187f141c4110
  | 1 => 0x8b10006f970d8b100befa10d8b10014ff7658b10046ec6258b10004ff7558b10024fe7558b10004fd7558b10024fc7558b10004ff7458b1001cfe7458b10004fd7458b1001cfc7458b100067f5458b100067d5458b10004ff7358b1008cfc7358b10006ef7258b10046ee4258b10006ed4258b10014ff7158b10014fd7158b1000cfc7158b10046ec2158b100a6ef2058b100a6ed2058b100a6fa1058b1008cff76ccb10004fe76ccb10004fd76ccb1008cfc76ccb1008ede63ccb10006dd63ccb10004ff764cb10004fe764cb10004fd764cb10004fc764cb10006de634cb10006dd634cb10005f7714cb10005f4714cb10104fd76cc71000cff768c71000cfd768c710006de638c710006dd638c71000dfa708c710005f9708c71013cff764c710005ef724c710045ec724c71000cff760c71000cfd760c71008ede630c710006dd630c71000dfa700c710005f9700c71000cff7688710014fe768871000cfd7688710016ee6288710006ed628871000dfa7088710005f970887101bcff7648710005df7348710005dc7348710004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d10004ff74d8d1001cfe74d8d10004fd74d8d1001cfc74d8d100067f54d8d100067d54d8d10014fe72d8d10004fd72d8d10014fc72d8d10006de32d8d10006dc32d8d10124ff70d8d10124fd70d8d10126df30d8d10126dd30d8d10126fa20d8d10006df6398d10105f57198d1008cff7598d10024fe7598d10004fd7598d1008cfc7598d1008cff7498d1001cfe7498d10004fd7498d1008cfc7498d100067f5498d100067d5498d1008cfe7398d1008ede4398d10006dd4398d10014fe7298d10004fd7298d10014fc7298d10104fd7198d1008ef57198d1013cfd7098d1008ef97098d100057f7558d1003d7c7558d10005bf7458d1002dbc7458d10005ef7258d10035ec7258d1013df77158d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d10004fd7458d1001cfc7458d10006bc7458d1001cbc7458d100067f5458d100067d5458d10006df7358d10006de4358d10006dd4358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d1013cff7158d10006f77158d10104ff7058d10006fb7058d10106fa2058d10124fe7618d10006dd6318d1008cff7518d10024fe7518d10004fd7518d1008cfc7518d1008cff7418d1001cfe7418d10004fd7418d1008cfc7418d100067f5418d100067d5418d1008ede7318d10014fe7218d10004fd7218d10014fc7218d10006de3218d1008edc3218d10124fe7118d1008cfc7118d1008cff7018d1000cfe7018d100d4f
  | 2 => 0x15ee720c520005ed720c5200dfce320c52000dfa700c520005f9700c52000dee76885200beee768852000cee76885201e5ef75885201e5ed75885201ddef74885201dded74885201d76f54885201d76d5488520005ef7388520005ed7388520006ee6388520006ec6388520015ee7188520017e67188520006ef6188520007e76188520007e4618852000dee70885200bfea7088520007e9708852000dec7088520016ef6088520017eb60885200bfea30885200bfea1088520015f8764c12006ef8764c120014f8764c1200077b754c1201cf78754c1201c77b544c1201c779544c12000dfb734c12000fdb734c120007db634c12008efa634c12008ef8634c120007d8634c1201cfda534c1201cfd9534c1201c7da434c1201c7d9434c120007eb724c120015fa724c120015f8724c12006fe8724c12000efb624c12000feb624c12006fea524c1201cfe9524c12006fea424c1201c7e9424c12006fdb324c12006fea324c12006fd9324c120007e9324c120007c9324c120005fb714c120007da314c120007d8314c120007ea214c12006fe8214c1200557e75d8f100057d75d8f100d5f671d8f10004ff75d8f10024fe75d8f100067e75d8f100247e75d8f10004fd75d8f100067d75d8f100047d75d8f10024fc75d8f10004ff74d8f1001cfe74d8f10004fd74d8f1001cfc74d8f100067f54d8f100067d54d8f10014fe72d8f10004fd72d8f10014fc72d8f100d4fe71d8f10006f671d8f10006f970d8f10104fd7698f10006df6398f1008cff7598f10024fe7598f10004fd7598f1008cfc7598f1008cff7498f1001cfe7498f10004fd7498f1008cfc7498f100067f5498f100067d5498f10006df5398f1008edc5398f1008ede4398f10006dd4398f10014fe7298f10004fd7298f10014fc7298f1008edf3098f1013edd3098f10004ff7558f10024fe7558f10004fd7558f10024fc7558f10004ff7458f1001cfe7458f10004fd7458f1001cfc7458f100067f5458f100067d5458f10006df7358f10006df5358f10006dc5358f10006de4358f10006dd4358f10004ff7258f10014fe7258f10014fc7258f1008cff7158f10104fd7158f10106df3058f10106dd3058f10006dd6318f10125f67118f1008cff7518f10024fe7518f10004fd7518f1008cfc7518f1008cff7418f1001cfe7418f10004fd7418f1008cfc7418f100067f5418f100067d5418f1008cfe7318f1008ede7318f10014fe7218f10004fd7218f10014fc7218f10124fe7118f1008ef67118f1008ef97018f10046ee62d8b101b5f671d8b10004ff75d8b10024fe75d8b10004fd75d8b10024fc75d8b10004ff74d8b1001cfe74d8b10004fd74d8b1001cfc74d8b100067f54d8b100067d54d8b1008cfe73d8b10004fd73d8b100a4fd72d8b101b4fe71d8b10006f671d
  | 3 => 0x97098d2008efa3098d200057f7558d200657c7558d2016def7258d20085fb7058d20004ff7558d200067f7558d200047f7558d20024fe7558d20004fd7558d20024fc7558d200067c7558d200247c7558d20004ff7458d2001cfe7458d20004fd7458d2001cfc7458d200067f5458d200067d5458d20006df7358d2016cff7258d20006ef7258d20004ff7158d20004fc7158d20154ff7058d20006fb7058d20224fe7618d20006dd6318d2008cff7518d20024fe7518d20004fd7518d2008cfc7518d2008cff7418d2001cfe7418d20004fd7418d2008cfc7418d200067f5418d200067d5418d2008cfe7318d2008ede7318d20006df5318d2008edc5318d2008ede4318d20006dd4318d2000cff7218d20014fe7218d2000cfd7218d2008eed7218d20014fc7218d2021eee4218d20006ed4218d2008edf3218d2008eee3218d2021edd3218d20004fe7118d20004fd7118d2021eec2118d20014ff7018d20014fd7018d2008ef97018d2008edf3018d2008efa3018d20216dd3018d2000dec764c920156ec764c92000cec764c92020def754c92020ded754c920205ef744c920205ed744c9201ff6f544c9201ff6d544c920015ef734c920017cf734c920007cf634c92008eee634c92008eec634c920007cc634c920005ec714c920007eb704c92000dee704c92000dec704c920157e8704c920016ef604c920017eb604c920157cf304c920157ea304c920157cd304c920157ea104c920004ff75d8520024fe75d8520004fd75d8520024fc75d8520004ff74d852001cfe74d8520004fd74d852001cfc74d85200067f54d85200067d54d852008cfe73d8520004fd73d852000cfd72d85201beed72d85201f6ee42d8520006ed42d85201f6f621d85201f6f521d85201f6ec21d8520014fd70d85201bef710d8520006f76198520035f970985200057f75585200657c7558520005bf745852005dbc7458520005df7358520005dc7358520045fb7058520006f56118520004ff7518520024fe7518520004fd7518520024fc7518520004ff741852001cfe7418520004fd741852001cfc74185200067f54185200067d541852008cfe7318520004fd731852000cfd72185201eef621185201eef5211852000cfe7018520014fd70185201eef9701852000cfc70185201b6fa10185201b6f51018520004fe76cc520004fd76cc52008cfc76cc520015ee72cc520005ed72cc520007cd32cc52000dfa70cc520005f970cc520004fe768c520004fd768c520004fc768c520006df638c520006dc638c520015ec728c52012fce328c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520005ef724c520015ec724c520007cd324c52000dfa704c520004fe760c520004fd760c52008cfc760c520006df630c52008edc630c520
  | 4 => 0x85300067f65185300067c6518530006f56118530004ff7518530024fe7518530004fd7518530024fc7518530004ff741853001cfe7418530004fd741853001cfc74185300067f54185300067d5418530014fe7218530004fd7218530014fc72185300d6f510185300d4fe76cc5300067f65cc53014e7c65cc53008fd830cc53000cfe768c5300067f658c5301367c658c530006f7618c530006f4618c53000dfa708c530005f9708c53000dde768c530126de768c53000cde768c53027ddf758c53027ddd758c5300075f658c5302775c658c53026ddf748c53026ddd748c5302675f548c5302675d548c530005dd728c53012ede628c53012edc628c5300d5de718c530006df618c530007d7618c530007d4618c53000dde708c530127da708c53000dda708c530007d9708c53000ddc708c530126df608c530127da208c53000cfc764c5300067f654c53011e7c654c530005ef724c53006dec724c530006f7614c530006f4614c530005fb704c53000df8704c530107d8304c53013cfe760c5300067f650c5300ee7c650c53013dde760c530006de760c53025ddf750c53025ddd750c5300075f650c5302575c650c53024ddf740c53024ddd740c5302475f540c5302475d540c530005dd720c5300dede620c5300dedc620c530125de710c530007d6710c530006df610c53000dde700c53000ddc700c53008edf600c5300d7da200c530004fe7688530004fd7688530004fc76885300067f65885300ce7c6588530005df7388530005dc7388530006ef6288530016ec6288530007cf3288530004ff7648530004fe7648530004fc76485300067f65485300b67c6548530005df7348530005dc734853000dfa76cc13000efa76cc1300077b65cc13023f7865cc1302377b54cc1302377954cc13000dfa73cc13000fda73cc13000efb63cc13000fdb63cc13008fda53cc13023fd953cc13008fda43cc130237d943cc130005f972cc13008fdb32cc130007d932cc130007da31cc13008fd831cc130004ff75d8d20024fe75d8d20004fd75d8d20024fc75d8d20004ff74d8d2001cfe74d8d20004fd74d8d2001cfc74d8d200067f54d8d200067d54d8d20006df53d8d20006dc53d8d20006de43d8d20006dd43d8d2000cff72d8d2000cfd72d8d2022edf32d8d2022edd32d8d20004fe71d8d20004fd71d8d20014ff70d8d20014fd70d8d20226df30d8d20226dd30d8d20154fd7698d20006df6398d20155ed7298d2006df97098d2008cff7598d20024fe7598d20004fd7598d2008cfc7598d2008cff7498d2001cfe7498d20004fd7498d2008cfc7498d200067f5498d200067d5498d2008cfe7398d20154fd7298d2008eed7298d20086ee4298d20006ed4298d2008eee3298d20004fe7198d20004fd7198d20086ec2198d2016cfd7098d2008ef
  | 5 => 0x2c67d73d95302c67c73d95300067f43d95300067e43d95300067d43d95300067c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300067e32d95300067c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95300067f21d95300067c21d95302c67f70d95302c67e70d95302c67d70d95302c67c70d95302c67f40d95302c67e40d95302c67d40d95302c67c40d95302c67f30d95302c67e30d95302c67d30d95302c67c30d95302c67f20d95302c67e20d95302c67d20d95302c67c20d95302c67f10d95302c67e10d95302c67d10d95302c67c10d9530014fe76d89300067f65d89300067c65d893006eee62d8930004ff75d8930024fe75d8930004fd75d8930024fc75d8930004ff74d893001cfe74d8930004fd74d893001cfc74d89300067f54d89300067d54d893000cfd73d8930014fc73d893006eee42d8930006ed42d893006eee32d8930004fe71d8930004fd71d893006eec21d893016eef20d89300057f755893007d7c75589300067f65589300067c655893006eec6258930214fe76cc9300067f65cc93017e7c65cc93000df870cc93008fd830cc930215de76cc93022ede76cc9302bddf75cc9302bddd75cc9300075f65cc9302b75c65cc9302addf74cc9302addd74cc9302a75f54cc9302a75d54cc930155dd72cc930016de62cc930016dc62cc93006fce42cc9302a7cd42cc930005de71cc93006fcc21cc93008fdb70cc93000dde70cc93000ddc70cc93008fd870cc93008edf60cc93016fda20cc93000cfc764c9300067f654c9301667c654c930006ef624c930016ec624c93006fcc324c930005fb704c93000df8704c930157d8304c93000ddc764c930016dc764c93000cdc764c93029ddf754c93029ddd754c9300075f654c9302975c654c93028ddf744c93028ddd744c9302875f544c9302875d544c93016ddf724c930007cf724c930007cf624c930016de624c930016dc624c93006fcc624c930005dc714c930007db704c93000dde704c93000ddc704c930157d8704c930156df604c930157cf204c930157da204c9300067f65d85300067c65d8530004ff75d8530024fe75d8530004fd75d8530024fc75d8530004ff74d853001cfe74d8530004fd74d853001cfc74d85300067f54d85300067d54d853013edd73d8530006de43d8530006dd43d8530014fe72d8530004fd72d8530014fc72d8530006df32d8530006dd32d853013efa20d853013ef710d853007d7e75985300057d75985300067f65985300067c6598530006f761985300057f755853007d7c75585300067f65585300067c6558530005bf7458530075bc7458530005ef725853006dec725
  | 6 => 0xf3258b3008eec3258b30004ff7158b30004fc7158b30156fa3058b30156ef2058b3000ddd76ccb30016dd76ccb3000cdd76ccb3008ddf75ccb3032ddd75ccb3008ddf74ccb30325dd74ccb3031f5f54ccb3031f5d54ccb30016de62ccb3008fce62ccb3008fcd62ccb30016dc62ccb30087ce42ccb3031fcd42ccb30005de71ccb30087cc21ccb3000dde70ccb3008fda70ccb3008fd970ccb3000ddc70ccb30224ff764cb30016ec624cb3008fcc324cb30225df764cb3021edf764cb30315df754cb30315dd754cb3030ddf744cb3030ddd744cb303075f544cb303075d544cb3008fcf724cb3008fcf624cb30016de624cb30016dc624cb3008fcc624cb30005dc714cb3000dde704cb3000ddc704cb30157cf204cb3008ef76198730004ff7598730024fe7598730004fd7598730024fc7598730004ff749873001cfe7498730004fd749873001cfc74987300067f54987300067d549873000cfe7398730014fe7298730004fd7298730014fc729873008ef7319873008ef43198730126f51098730005ef7258730085ec725873008ef46158730004ff7558730024fe7558730004fd7558730024fc7558730004ff745873001cfe7458730004fd745873001cfc74587300067f54587300067d545873000cfc7358730106dc7358730006de4358730006dd4358730004ff7258730006ef7258730004ef7258730014fe7258730014fc7258730006ec7258730014ec7258730006df3258730006dd325873008ef7315873008ef43158730106f71058730104fd768c730105dd768c730006dd768c7302fddf758c7302fddd758c7302f5df748c7302f5dd748c7302ef5f548c7302ef5d548c730005dd728c73012ede628c73012edc628c730006dd618c73000dde708c73000ddc708c730124ff764c730005ef724c730085ec724c73000ddd760c73008edd760c73000cdd760c73008ddf750c7302e5dd750c73008ddf740c7302dddd740c7302d75f540c7302d75d540c730005dd720c7300dede620c73008edc620c73008fd6710c73008fd6610c730006dd610c73008fd5610c73000dde700c73008fda700c73008fd9700c73000ddc700c730004ff768873008cfe7688730004fd7688730005df738873008ddc7388730016ec6288730007cf3288730004ff7648730004fd764873008cfc7648730005df734873008ddc73487302cd7e76d953007e7e76d95300247e76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95302c75f73d95302c75c73d95300075e43d95300075d43d95300067e62d95300067c62d95302c75e30d95302c75c30d95302c77830d95302c77a20d95300067f74d95300047f74d95300067e74d95300067d74d95300047d74d95300067c74d95302c67f73d953007e7e73d9530
  | 7 => 0x8d21006ed4218d2108edf3218d210dedd3218d210deec2118d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d2108edc3018d2112dde7618d21006de7618d2112cde7618d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d210075f5418d210075d5418d210dfce4218d21007cd4218d210dfd72118d210dfcc2118d210dfd42118d21006de6018d21006dc6018d2108edf7518d21006de7518d21006dd7518d2108edc7518d2108edf7418d21006de7418d21006dd7418d2108edc7418d21006df5418d210065f5418d21006de5418d21006dd5418d210065d5418d21006dc5418d2108edf7218d210dede7218d210dedd7218d2108edc7218d210dedf5218d210dede5218d210dedd5218d210dedc5218d210dedf4218d210dede4218d210dece4218d210dedd4218d21006cd4218d210dedc4218d2108edf7118d210dedd7118d21006df5118d21006de5118d21006dd5118d21006dc5118d21006df4118d21006de4118d21006dd4118d21006dc4118d210dedf2118d210dede2118d210dedd2118d210dedc2118d210decc2118d2108edf7018d21006de7018d21006dd7018d2108edc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d21006df4018d21006de4018d21006dd4018d21006dc4018d210dedf2018d210dede2018d210dedd2018d210dedc2018d21006de1018d21006dc1018d21014fe76cc521014fc76cc521006df63cc52108edc63cc521015ee72cc521005ed72cc5210dcfe768c52112edf638c521006dc638c52108cff764c521014fe764c52110cfd764c521014fc764c521006df634c521006dc634c521005ef724c521015ec724c52112cfe760c521006df630c52108edc630c52133def748852133ded74885213376f54885213376d5488521007cf6388521006ee6388521006ec6388521007cc6388521006cc6388521015ee7188521017e67188521016ef6188521017e7618852100cfe76d8121006df63d8121006dc63d81210a6fa60d8121004ff75d8121024fe75d8121004fd75d8121024fc75d8121004ff74d812101cfe74d8121004fd74d812101cfc74d81210067f54d81210067d54d812108cfe73d8121004fd73d812100cfc72d8121046ee42d8121006ed42d8121014fd71d8121006ee21d8121046ec21d81210a6fa20d81210a6fa10d81210057f75581210b57c7558121005bf74581210adbc7458121005df7358121005dc7358121006df6358121006dc63581210a6f86058121014ff7658b3008eec6258b30004ff7558b30024fe7558b30004fd7558b30024fc7558b30004ff7458b3001cfe7458b30004fd7458b3001cfc7458b300067f5458b300067d5458b30014fd7358b3000cfc7358b3008ee
  | 8 => 0xbefa20582210bef81058221004ff75d8d21024fe75d8d21004fd75d8d21024fc75d8d21004ff74d8d2101cfe74d8d21004fd74d8d2101cfc74d8d210067f54d8d210067d54d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21006df43d8d21006de43d8d21006dd43d8d21006dc43d8d2112cff72d8d2112cfd72d8d2112edf32d8d2112edd32d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210075f54d8d210075d54d8d2112fce42d8d21007cd42d8d2112fd721d8d2112fcc21d8d2112fd421d8d21006de60d8d21006dc60d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d210065f54d8d21006de54d8d21006dd54d8d210065d54d8d21006dc54d8d2112edf72d8d2112ede72d8d2112edd72d8d2112edc72d8d2112edf52d8d2112ede52d8d2112edd52d8d2112edc52d8d2112edf42d8d2112ede42d8d2112edd42d8d2112edc42d8d2112edf71d8d2112edd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21006df41d8d21006de41d8d21006dd41d8d21006dc41d8d2112edf21d8d2112ede21d8d2112edc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d2112edf20d8d2112ede20d8d2112edd20d8d2112edc20d8d21006de10d8d21006dc10d8d21006df6398d2110df57198d2108cff7598d21024fe7598d21004fd7598d2108cfc7598d2108cff7498d2101cfe7498d21004fd7498d2108cfc7498d210067f5498d210067d5498d2108cfe7398d210dcde7398d21144fd7298d2108eed7298d21146ee4298d21006ed4298d2110cfd7198d2108ef57198d21146ec2198d2100cfe7098d21004fd7098d2100cfc7098d21145f77158d21004ff7558d21024fe7558d21004fd7558d21024fc7558d21004ff7458d2101cfe7458d21004fd7458d2101cfc7458d210067f5458d210067d5458d21006df7358d2110cff7258d21006ef7258d21004ef7258d21144ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d2112cfe7618d21006dd6318d2108cff7518d21024fe7518d21004fd7518d2108cfc7518d2108cff7418d2101cfe7418d21004fd7418d2108cfc7418d210067f5418d210067d5418d2108ede7318d21006df5318d2108ede5318d21006dd5318d2108edc5318d21006df4318d2108ede4318d21006dd4318d2108edc4318d2108cff7218d210dcfd7218d210deee421
  | 9 => 0x5534c431007e7724c431007e4724c43100cff765803108ef86058031004ff7558031024fe7558031004fd7558031024fc7558031004ff745803101cfe7458031004fd745803101cfc74580310067f54580310067d5458031004ff7258031014fe7258031014fc72580310d6fa5058031006f950580310d6fa4058031006f9405803108efb305803108ef830580310d6fa20580310d6f8105803112fcc32d8e210ddf671d8e21004ff75d8e21024fe75d8e21004fd75d8e21024fc75d8e21004ff74d8e2101cfe74d8e21004fd74d8e2101cfc74d8e210067f54d8e210067d54d8e21006ed72d8e2112ede32d8e2112edc32d8e2112eec32d8e210dcfe71d8e21006f671d8e2100cfe70d8e21004fd70d8e2100cfc70d8e2112eef20d8e2110cfd7698e21006df6398e2108cff7598e21024fe7598e21004fd7598e2108cfc7598e2108cff7498e2101cfe7498e21004fd7498e2108cfc7498e210067f5498e210067d5498e2108ede4398e21006dd4398e2108edf3298e21146dd3298e2100cfe7098e21004fd7098e2100cfc7098e21004ff7558e21024fe7558e21004fd7558e21024fc7558e21004ff7458e2101cfe7458e21004fd7458e2101cfc7458e210067f5458e210067d5458e21006df7358e21006de4358e21006dd4358e21006ef7258e2110edf3258e2110edd3258e2110eec3258e21004ff7058e2100cfe7058e2100cfc7058e2110eef2058e21006dd6318e210dfcc3218e2112df67118e2108cff7518e21024fe7518e21004fd7518e2108cfc7518e2108cff7418e2101cfe7418e21004fd7418e2108cfc7418e210067f5418e210067d5418e2108cfe7318e2108ede7318e2108eed7218e210dede3218e2108edc3218e2112cfe7118e2108ef67118e2100cfe7018e21004fd7018e2100cfc7018e21006ed76cca21346ef64cca21346ed64cca213476f54cca213476d54cca21015ee73cca21017ce73cca21006ef63cca21007ce63cca21006ed63cca21007cd63cca21007e671cca21005ed71cca21007e571cca21016ee61cca21017e661cca21005ed70cca2110cfd76cc621006df63cc62108edc63cc621015ec72cc621007cf32cc621014ff768c621014fd768c621006de638c621006dd638c621015ee728c621005ed728c62112fcc328c621144ff764c621006df634c621006dc634c621005ef724c621015ec724c621007cf324c621014ff760c621014fd760c62108ede630c621006dd630c621015ee720c621005ed720c6210dfcc320c6210befa60d822100cff76582210bef86058221004ff7558221024fe7558221004fd7558221024fc7558221004ff745822101cfe7458221004fd745822101cfc74582210067f54582210067d5458221004ff735822108cfc7358221014fc71582210befa4058221006f94058221
  | 10 => 0xc9313af5f54cc9313af5d54cc93110ddd72cc931007cf62cc931016de62cc931016dc62cc93110fcc62cc931016cc62cc93110fce42cc9313afcd42cc931005de71cc93108edf61cc93110fcc21cc931014fc764c931006ef624c931016ec624c931005f7714c931005f4714c93110ddc764c931016dc764c931014dc764c9313a5df744c9313a5dd744c93139f5f544c93139f5d544c93110ddf724c931007cf724c931007cf624c931016de624c931016dc624c93110fcc624c931016cc624c931007d7714c931005dc714c931007d4714c93110fcf204c931006ef62cc531146ec62cc5313977754cc5313977554cc53108fd643cc531397d543cc531007e762cc531007e462cc53108fd732cc531007d532cc531006ef628c53112eec628c53135ddf748c53135ddd748c53138f5f548c53138f5d548c531005dd728c531007cf628c53112ede628c53112edc628c531007cc628c53112ecc628c531007d7618c53100cfe76d8131006ef62d8131006ec62d8131106fa60d8131004ff75d8131024fe75d8131004fd75d8131024fc75d8131004ff74d813101cfe74d8131004fd74d813101cfc74d81310067f54d81310067d54d8131006de43d8131006dd43d8131014fe72d8131004fd72d8131014fc72d8131006df32d8131006dd32d8131006de31d8131106fa30d8131106fa10d81310057f755813111d7c7558131005bf7458131115bc7458131005ef725813110dec7258131006ef6258131006ec6258131106f86058131014ff765883108eec625883108fcc3258831004ff7558831024fe7558831004fd7558831024fc7558831004ff745883101cfe7458831004fd745883101cfc74588310067f54588310067d54588310deee5258831006ed52588310deee4258831006ed425883108eef32588310dede32588310dedc325883108eec32588310deec2158831004ff705883100cfe705883100cfc70588310deef2058831144ff764c8310dddf734c831146de634c83108fcc324c83108edf64cc431386dd64cc4313875f54cc4313875d54cc4310ddde72cc43108ddc72cc431006dd62cc431005dd70cc43137ddd738c431376de638c43136f77548c43136f75548c43108df5738c43108ef6638c43108fd6638c431367d6328c43108fd4328c431004ff764c431005ef724c4310ddec724c431005df764c431006df764c431004df764c431356df644c431356dd644c4313575f544c4313575d544c431007cf724c4310ddde724c4310dddc724c431007cc724c4310ddcc724c431006dd624c43108ddf714c43135ede614c43134fd6514c43134fd5514c431005df704c43108df7764c431006f7764c431004f7764c43135777544c43135775544c43108df7734c431007d7734c43108ef6634c43108fd6634c43108fd6534c43134fd
  | 11 => 0x16ee624ca31006ed624ca3112fcc324ca31005f7714ca31005f4714ca31005dd76cc631006dd76cc6313c6df64cc6313c6dd64cc6313c75f54cc6313c75d54cc63112dde72cc63112ddc72cc631006dd62cc6313bfd651cc6313bfd551cc631005dd70cc631005f576cc63108ef576cc6313c77754cc6313c77554cc63108fd653cc6313bfd553cc6311357e75d82310057d75d8231126fa60d823100cff7658231126f86058231004ff7558231024fe7558231004fd7558231024fc7558231004ff745823101cfe7458231004fd745823101cfc74582310067f54582310067d5458231004ff7258231014fe7258231014fc7258231006fb5058231126f85058231126fa4058231006f94058231126fa3058231126fa2058231126f81058231014fe76d893110eee62d8931004ff75d8931024fe75d8931004fd75d8931024fc75d8931004ff74d893101cfe74d8931004fd74d893101cfc74d89310067f54d89310067d54d8931006ef52d893110eee52d8931006ed52d893110eec52d8931006ef42d893110eee42d8931006ed42d893110eec42d893110eee32d893110eef21d893100cfe70d8931004fd70d893100cfc70d893110eef20d8931006ee20d893110eec20d893110dee76d8931014ee76d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d89310076f54d89310076d54d8931007cf73d8931007ce43d8931007cd43d8931006ee60d8931006ec60d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d89310066f54d8931006ee54d8931006ed54d89310066d54d8931006ec54d8931006ef73d893110eee73d8931006ef53d8931006ee53d8931006ed53d8931006ec53d8931006ef43d8931006ee43d8931006ed43d8931006ec43d8931006ef71d893110eee71d8931006ed71d8931006ef51d8931006ee51d8931006ed51d8931006ec51d8931006ef41d8931006ee41d8931006ed41d8931006ec41d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931006ef40d8931006ee40d8931006ed40d8931006ec40d8931006ee30d8931006ec30d8931006ee10d8931006ec10d893110eec6258931005ee761893110eee7618931006ef6518931006ee6518931006ed6518931006ec6518931006ef6418931006ee6418931006ed6418931006ec64189310076f54189310076d541893110fcd7318931007ce4318931007cd431893110fea701893110fe97018931006ee6018931006ec601893112cfe76cc931016ec62cc931005de76cc93112ede76cc93112cde76cc9313b5df74cc9313b5dd74c
  | 12 => 0xa20583323eeef64cc9323eeed64cc9323ef6f54cc9323ef6d54cc932015ee73cc932017ce73cc932016ef63cc932017cf63cc932005ed70cc932004ff75d8532024fe75d8532004fd75d8532024fc75d8532004ff74d853201cfe74d8532004fd74d853201cfc74d85320067f54d85320067d54d8532006f741d8532006f441d8532146f621d853200cfe70d8532004fd70d853200cfc70d8532006f76198532006f56118532004ff7518532024fe7518532004fd7518532024fc7518532004ff741853201cfe7418532004fd741853201cfc74185320067f54185320067d54185320dedd7318532006ef32185320dede32185320dedc32185320deec3218532006f74118532006f441185320def5211853200cfe7018532004fd701853200cfc70185320deef201853200cfe76d8132156fa60d8132004ff75d8132024fe75d8132004fd75d8132024fc75d8132004ff74d813201cfe74d8132004fd74d813201cfc74d81320067f54d81320067d54d8132014fd73d8132004fe71d8132004fd71d8132156fa30d8132156fa20d81320057f75581321657c7558132156f86058132014ff7658b3108eec6258b31004ff7558b31024fe7558b31004fd7558b31024fc7558b31004ff7458b3101cfe7458b31004fd7458b3101cfc7458b310067f5458b310067d5458b3108eef3258b3108eec3258b31146ef2158b31004ff7058b3100cfe7058b3100cfc7058b31146ef2058b3108ddd76ccb31016dd76ccb31014dd76ccb3108ddf74ccb313e5dd74ccb313df5f54ccb313df5d54ccb31016de62ccb3108fce62ccb3108fcd62ccb31016dc62ccb31147ce42ccb313dfcd42ccb31005de71ccb3108fd671ccb3108fd571ccb31147cc21ccb310dcff764cb31005df764cb310dedf764cb310dcdf764cb313d5df744cb313d5dd744cb313cf5f544cb313cf5d544cb3108fcf724cb31016de624cb31016dc624cb31005dc714cb31147cf204cb3100cff765833108ef86058331004ff7558331024fe7558331004fd7558331024fc7558331004ff745833101cfe7458331004fd745833101cfc74583310067f54583310067d5458331006de4358331006dd4358331004ff7258331014fe7258331014fc7258331006df3258331006dd325833108efb305833108ef8305833113efa205833113efa105833112eee62d8a3112fcc32d8a31014ff7658a3112eec6258a3112fce3258a31004ff7558a31024fe7558a31004fd7558a31024fc7558a31004ff7458a3101cfe7458a31004fd7458a3101cfc7458a310067f5458a310067d5458a3112eee4258a31006ed4258a3112ede3258a3112eee3258a3112edc3258a3112eec2158a31004ff7058a3100cfe7058a3100cfc7058a3110cfd76cca3112dde73cca31016ec62cca31014ff764ca3112ddf734ca31
  | 13 => 0x2000000c00200000300000040060040024000002000001000000000000000000060008000004000001001400e00000180280020010000008000009000800000a0000030000000002000000000000000080340100010000004000003000000400000100000000000060008000000002000000400200200000040040010010000006000000000400e004000000c00400000180040040040008028002001000000c008000004000c000002001800000800500080040000000000004000002001000400a00000000040000000000024002001001000c00000000400080000020000000000001000800c00400300000000060000008004002000001800800200000080040000000000008000005000800c000002000000400200100080040000050058024000002000801c0100070000004000000002000400000000000000040000000004000003003000000000100080000020010018008000000000000400c001000800400800200500000000010008000002000003800800000200280000000030000000002005000001800c0000008000006001002800000200900100000000010008018000000002001c002000004000c0000000048000002000003801c006005002800000600100000000000010000008000000001000c002000001000400000f000800000600300100080000000000018008001000000c000000003800c0020000000014000004001000000e00200000040060000000004000005000800800200700200040080000028008002000001000000400100200000000010000008002001001000c00000000200000280020008014004000000000800000000000000020010000000002005001000c00000200080200000010008000000000002000400c00108ef76198732004ff7598732024fe7598732004fd7598732024fc7598732004ff749873201cfe7498732004fd749873201cfc74987320067f54987320067d5498732014fe739873212ede739873212ede329873212edc329873208ef7319873208ef4319873212ef5219873200cfe7098732004fd709873200cfc709873208ef46158732004ff7558732024fe7558732004fd7558732024fc7558732004ff745873201cfe7458732004fd745873201cfc74587320067f54587320067d5458732014fc735873210eee4258732006ed425873208ef7315873208ef4315873210ef6215873210eec2158732004ff705873200cfe705873200cfc705873200cff765833208ef86058332004ff7558332024fe7558332004fd7558332024fc7558332004ff745833201cfe7458332004fd745833201cfc74583320067f54583320067d5458332014fc735833206eee4258332006ed425833206eee3258332004ff7158332004fc715833206eec215833208efb305833208ef8305833216ef
  | 14 => 0x710a0fd47f308c00005e24a80c00000a1c75324915dc3104222ac186800038a1840ce0d244473ab872041886700000000000000000000a444a31178000d1a0dd00e8000d722a10000000f100000000000e980003f680000008901da80008d84ac31085200001ba0000b5404c00000020d89480002e59b087746e809e0000164000412000000000000000000008171038000b3c44208480002820003719f1ce923772b621a88ce5100001f5c6304d939994dc5da7af0000478000186000000004015800008800728d20000df0fac5c33208000e3400000021b84562f931e8000ce40cc217967c0cc000000000000021b0ad0000000000000153400000000015c4ef2482000000000000000000004000000000ae839e0f01ba11cd0d80000000ab800000000013f800000000015240480000000000d260003e500000004983939fe408661300000000008a933f80400b44ea0001594000000000000003679900000006ae3d114b09d80000000001340000000000000000044d000000000000000011d8000484000217014e00000000008e074205100009e857413696182980000d700003c846524f0c44cc6525376a100c0000180000020010050010000009000802800a00000000000000010008000000000000000c00c0000000004000009000800c00000700180000000000000004002000004800000000000080000060020010024004000001000800000000580280000020028000000000000000400600000300040000000008000006000000800400200000000000000020000010000004001000000000000080000000010000000004002001800000000100080040020010000000002000000000000200500000180000000040004002004000801800000000100040060010010000002000000000001a00000000080000020018004000001000800000800a0068000000000000000c00400000080140020000000000002000008800c006001000002c000000000000c002003000800400e00a00380000020060000000002000001000400000100400040040020000000018002003800c000000000800000400200000000020000000010002006003000000000100180000000000010010004004000004c0000010010000006000000800400200000000080020060000000002001000003400000700000000000000000000000009000000400000200100100020010018004000001002800000600000000000020010000004000000003000400600500000000040000000018004000003000000800d000800800e000000800400800000000000000010000000004003000000000c0000018000002001000000000000000180000000000020028000000001800002400000000140020030020000000007003000c000000000001000e001000001800400
  | 15 => 0xc200017280002c43d23a780004ea0b539680000001813bc1b206d40000001ee000000022f866914a3430001b480000000000f8400000000000000001d70001bfcd668dd3c70e70a260070000250c9c39f1d88000112515000000061800000009cc7ea24c00000000000000e118ed17600000000000000000000964e160000000000e767130000b986e48af00008c000000045082e0000000000000098c46d335000000043c000000000000000000009820000001e8c24c00003180000006280000db8ff0000000000000000044189e89f4000000000000000000000000001d30000000b2c00000007040007d00000000b041b9000000000000041400000000000000070000000060000000053615f22f000024e00000000000000918c34d8a2eb0000000000150167800034800016a21880000002e380000000000000000000211000145cfbc2bf00008080000fa0ac951c00014900000000000003c9868c15a09338f87308620000001918daa36d474049400048f0000eac0001ea000000000000000000000f400010e000064014f0000000000000000000000070e00000000c400000000000000000000000000000000044caba0001efa2005928ce38900007840000f0000108e00000017cc0008c038681dc0000001ae8740e72000000000000060812393ec000000000000000000000000005d8378000031c2ee2c30ba9ac88603f338c8d641ae47d43200006a64231bc94100de22e2b81b943688380001540484000000000000000000000000000001f3000059c00000000007f4000356168509a5212cd8438e3a0001a81b248de6990000c94f4c16824d80000000003ce959c0006893ac8000000000000000069600001d94900008cf000228c018000000000100c0003c799400000000001f4caea0000001ca000085200000000da00034b97c8e6e2790b804c414a0db3931e1000035600006500005de0000000d7012c3410bec0008630540000254780453000000000036200000005d900000000000003580e5450800000018cc90000000014b0000744000000000000000000007228552570000dd688f06e0b00000000000000000019d1558000e8c0002f388cc0fe05417997607b86d33a900004f00000f919d078600011d80007ae0000a11e70c625c92b21ee81000e40d880cc8c8000000000000000000000002ac00009380000000000000c7000013e0000cdc00082200000009da0002a0800084a00000002bc4de0000001f800002d217f00000000003c69a790a653528117b439a3513ad800001440a00007102566533d480011605933e400008cc3323471b000000000002360fc400000000008a611600080000001ca31600000000004190628000000052014800051e3cf9d0c3c664814d11a400000000017f800004527189140007d205
  | 16 => 0xf000095a7f00000d6c4a4000105800000040205e00005ba7bc0d8000000000000000004c82d923f000000000e4450000000000187110000000038b000000065c00001289423c825c00000000000000000b8c00000000000008260001ba800039e28c000000034d00000000fa00014080000000002029f2400054c1d60000a860f242d1fa4d5a3f417080002e400016888600004501b79bd84141d8181987010e0e70001c9031a000000123831c0003d421c400000012483f453656f00000000f20003f3000051a0000000000000000000017000025d000176c1180000690000000000000000000000002080000004152f28d940008e100000009725a035a80003ee0001d680000000000000000516000000000000000000011680000001ad0000aec2230000d506800000000000ac00002fb000000006500000000000000001cc00000003381c183500f935596e40008e700013d51823f624d000000063000000002641a0000000000000013603a80bc000000051cb560000000000bd85fb00000000004c200000000000c813197fccbe00044a03acb7802e00010d40000000f809a013a00000000000000000000f94a0e000000014c7a81e20a183807761970000000000000000000000000000000003660000000000aae86d00014e8000000000058c0008e300004a43ea000174800000000022580000000000000000e7400036a0000c3c0000001aa400021600000000005ac000000000000007096507f035e00000000004563aa8000142000462000000069d00000011c827e1a90000000184000091000000028c8a7496406934a000061e1302148000bc86fa40b02606780000001e587d25201f5800000000000011784120003ec800000046e0000ef80000000000ea8b3868f000000041c0ee0be800000000000010e40000000c802080000d60000000f5c4a237600009cc22c4160000000629000080400060a000000000077d1cc8ccc76e0000cb16000000000000000d7e000000000000000000000000000000000000f040001be92cc00000000000000002ff1301ba4000000000182c0003ae0f287b407c0004118b280005aa000000000000021590e80000002df80000004ba00009c84e011a2d30e2c04a751194a01029c0d901481ec0002c41c70000000000000152c7340002fc8000b8847c4170ad000000036700000000000598144d0a0002cb80001de0000000000000000000000000020400000000000002850000000000000000000000027e0000e08192000000000068445d0d900005cc0000fe40000000001af4afa32307106d481e000000000000076500021f4000000023a1240003cf18f80009ba8611ea98400008330000d98000000000206c1820000000000adc00000008e464e0000000000afc44a0000000e0a3152b680000
  | 17 => 0x3848000f4a4164281548ec80000000fbd018057000163862600011f8e880000000000000000673000000000000000000000006751a22020a2241e0000ab4000573000000022a538000078474079100000010e02ee2a5000000004426e21390d200037e800000000029c8000b9c3b330b04e85668e0000000000000026b800054a0000000d2800055a0c622f800000006708dc00000000012ecec42aa45580000000000001db402a0000000884000554000000000022a000132c57a00000013b800000030a8000cd8000222800000044e00015440006200000000d9645c000000013487723c0bd40001643cd000000003500016680d4532147800000030a0000000c5c41f18b000105e00000009580000003b70b6c4ca0003b5196433e06730f80000000000cc800000000028e80000008961af800000080f0a8872c90c1aa0000950f4e0f63c600001245660001a2800050d0500ea097e438000074800041300000000003f11b4130c00000000000005bc00000013800000000001508000000000000093200007b800000000000000007b04ef00019d80001dc0000e3492642c00000000005af00002c4c98000284800000040d2d88cd400003c46100000000000000000000000000000000000016c009c000000000055ccd03b80001588d7415c0000000f9e0d100014191b80001a4937800000000011440000000001bd01aa33a04209182a60d4000000000000037c81d43380000d29df8296334000021447a2b80650000f5a6da43f80000007a100000000003b218080003ac0003db128000070717380010340001488000a5c00000019980000000d30ac8fb80003f3800000021400000000003c61b601642f86383e880000000001029a682240000000c90f28000000000000000008b800025c3883ba2054c3a59143c8f680007b14058000b6633d00021ac00020f0001c3d13c3302f08dc000000000000003e80003bf8000000000000000000045420a028c27e70c43a88940005721e80000000000000000000075f0001d9c00000005e80000007a40000000000000388000000081231223a417c000311800000061400000006c01141cb8cfc00000000020a8dfc5562f8800000000000023400002670001ca800079e0000000232000000000000004600000000005992940000000000090000028a3550001b84c440000001ee400041a0000000dc05a80000000cd65a239593fd1725f700000000000000ff93940000003e6022825a6a1000000086c714264a1bc65e00019b0000000000000000042a00036f000026c5bb00000000002dc00000000004f932c0000000000000127d0f000000016f80005231f105bc00000004417ac00041700000000000000c8800000000000019b800022400020d01c62a216b80003fa000000000070e0001
  | 18 => 0x26f800000000000000000840000000000faa0000001dccb6e0000c592d092a58f00005ac0008cb3e2800000064b415906400020800012a4ce257c00010a80002993ab000065800000022f4000000000000028800000012c00000000000000000000000000000057f208025d07637e08e0fc00000002e893a4d8e540000204068a7db07a865510c02200000000007f712d8000000000000000065c58920397000007ec000000000000005b951870400000007751920cf000000000000007a0000b0200030200009106640000000f8675a0b70000fb059d18d1decc88851000000000000045c089c9d600000000000000000001e54d768db1c60e188863cc0ef9e8800000021d95a8a0a6ef2e81a909ce09501f9d70000000442070000003d000000000000000000000000002de9bc086e000000000000400006c19480000000001d346820002ad80005500000001ad800000042d800049a00024b0798e063ec00d204c81c0ab2a99f8cfec000000017c87a00000000002c20000000000000859444800000000000018f000049407f86ec0906693010000d2c41b0b68000000400000000064c000000000000000000000007fe8091218000000000000000000000019f16d0a160000000da40000003551c70af639d22b8b3045a46800320e8bc63e8000085c0005dd0000dec56e8820d69c6000030437380002ec590227800000025a0d6000111000010194d00002d00000000d862f440e8000000292000210c0000002100000c30023000000073070a4458d3c0002b039b000000000013090cc0000000a0000000066f293158c6d67e40001f3400000030180000002ac1f3800000000026b0000000347231000000000000000000003c01190f6cc240002cc02640004a600018389a60bb00009980003e31310000bf049d14c197806e3bc40280007f80000000000c6825c00016140000311fb800000076103985e400000000000000007ab000000022000000019f800000012000000006350af193c0000002451e60dc80c519d83b4a6258717900c85d002f00007bc0003a1224805c4d4302000000000060d000000000072500016940005840000f4c2a80001ae0000d3e1670000000fe20000001030000000000164800069c30481c4ba85830000bdc83a71112a800018608f144800000089c0001180f60448000000000009f213a330672000000000056c10c000000000000036800000000003c919948ba74512b92bc00055c0000a8000071b0000e2405a00004080008986064551a040001ec000145853804c15393c8fbe3c52da82589c20000098a981d0064000170400086019696e90a881818d9514a242c72089ffc922000398921c00024f00002e91cc68c000000000017833e800059a0a643d91e4eec87c188111800073510d00000007b40000000
  | 19 => 0x11ec00045200023680000d3087a394caa625000000009c00000000000000002d480003a27c600002fc43a000205800000075e000000000000003011fc00000000000000007850748718e7c00012f9a54006342000000000000033c00000000003918ad40000002670000d6e00000006f116200036799ec50489d00000000000000001ff000000000008d40007dd432a2b4c0a483000000000000044a80004327320000f100006e234400005620000ba0c8896e00000000002480b9000075400000000000002700000001af8f206362021a8c0000004221f2c0006f82f800008e401e1e0800102800004f22040001853b80b20d20105000000060a00028e16c89a84f337e06f44a07630088000d3658d00005488b625318e800000089b3bb9934bbe5ae0001d4000009c3f08000000122000023800062b0000000a9046100002b0000000000000000072225e80005c60003df80000000000a51b750783b000016202d28d127b0e98ad263e00017a00d010d0001fec3b60000000000a520003e100000008df00010b4000000000000000087e0001fc8b5a0000000000e5e66d09ca2d4000012000199c60e2ef39e8000ba4108195a0b4cb4000408a2b0e008420000818000000000174c0000000000a7c8ea05622201400001fb269000020e3cd00000006122292f7136050e0002c520790ba8de32d9e5c7d403443a21140000000000e94a78000000000005600f32180007020000000000000000000000000000037980000e0841000057cd160001de93dc90a00000012240002e0000000000021f407131c000872000000000000000000d80003a7449800000000000000000005e603b0000d50000000131000000000020f909e000000000009a4b100000011ae80d000000036413b00000000000000000000000000000000000028a1d180000000003ba80008ee07c00001b8330000000000000064526d800018c30b00021cc0ba00031305a80aa00000023647da4590000000de26d820c19e4bb80002b090fc00000002c00001a000000000000000001a4231d03e7bd000194400037f37a80000003ca26299e82660003b48b2c92000000000011860000000c50aaa7890001a80f1684c00001d07c815d000197485c00044f8000d780000000000bea0000db9f00a7a000255101800000000022fc0000000000000b4852b1fe802400000023a00001e200038f14ed12263718b93340d600000000000000da0000ed00000003a080005ec1f80021d3800012144c00005ac00000007d83b20aa1c180000000f8000000000051f000000000000000001f811a3dd2e40000e2a28c30d8000c5e0002bc800002c00000000000000001440000e708190000000a28000000000047800000003b0ad06ca00000000000004000000d0e0000000000000000
  | 20 => 0x2085fc11a0e6c812000000000058400013a2389040000363212829a19b0000000000000000000000031e0fe0000ffc84b000079c34278a00019802aa0001b088980005f43be0e10000000000000000000025b1734a343fb000000115026b000022c00027b2af9d80c8e3a916d07e43bc0b01b107ac0004cc0001ff508c00000012f800000026d000000045513f9f940008970000000c946d941f864c0000003b7803511800000006f8bae000000000000000013b8000e940000001de8b8a00026409f400000025e04dc0000002ea8d190b070114189c4d5e83505487e8b2a24828191600000000000fb80004fd29980000001c5178000000000000020c0000000000016c6240000488d3800023800011e85c80000000a5494a000000000000000000000000007c400023287240000000000ad6394000000000062a2a216c084873f2af00000000000000c64f0e4211ec863c268183065800000000035280000002d3000000000000025a80003dc4e22652214f7c8c839014fc5f81283d98b142fe19e3ed13c50be00035300a055e0001bb0000f6e654306000000016600000000007eb0000f7800037126880000000000002268000000000215ca7c0f33ac00000000000000f24000000453904877e4c03211768b6c7ee0bf03780000003191d2c00028500004bcd626a714994bcc2243e0000000000640000000000000000000000000000001d20df64ec2f00400000000000000000000000000000003ce31d0a1891600000007cc03010b00000000006560bd000053c00000015641f600045b80005283210668418000000000000000000000000000000000000000fe81820dc00649d05a31d784740007f53308ca83d000000000000000000000000000000000231400076800004f40000df00000006b000000000000005ef0001a450ec00b3b88000c320002f500006f47fa0000000d820000000000000000000000080282529397a506e3850000000cae00043400000001c900019dc00079b41c8000000000000000000000000000000004cf00010700008033b61390c021b6000200435600000000000000000001d500000000000000520000253800060c00000000000000000d48fc800046a07300000004320002070a008a23d906fc000000000000000058c00018b40000000001d74cf863f0611e05124000466946c0927833d508c40001a73248000bf480a010813c000000000000074800000003f8af08ae20180005487a00001404000000000042800072900001e0938038137000000088d000000000000014b870d0ac8990001708e680004240000000187000000051c24a0001a8800000036f80000000002c59b3000054f0000000000000000000092e1460ad80000003800200000e040000000000000222000000000018943d10d
  | 21 => 0x8d30ff00000007ef39600001882bc00000008c67ce0001420000000171068800000031380000002df00000004d20000001b6c000471000143ca5410200003f00005a72981a0100e831072a2800000000000000d9a1730001988a9c2ea000000000000030380000004d50d780000000001608000000821307873809609b000000107a5ca0000001148213000000023600012f00000000001a60dd4e2e7210001eec00000000000005fa6f712c00000006860001a607961f1000221cb7048d0000000000000000173c0581da0f49ed400086645b0000f5800000007500000001db000072c0830000000bc400041381c800000045a000049600000000000000000000000c2e0050000000e7803000004440000000e380000000003a380006ce0001068ee42e27c100000000008020b00be0da250c08f8cc44503e0154a2391640001eb000000003a0002350ddc40805a18e400000000002d80006f20001b9800072e00000000544f00000000ecc00046b0000000086000000057216c0000000000000000000000000009a800000023a00000508d66dc35a1d000d8101000000000000000000006c6000000000019201f1ff17580003283c3040c9565fd00000002f685e0000000000000000110471e28000000000007723f4059400000000000011aa3c727c0000000373000000000000018009f042025115d9dacd5c000000231848248c1c980005f4236000000000068345990980006d600015e8dae0001c8024000052d000000047c00015180000000003ea00009020080000000e102c60000000000212000000105200
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc3f745536344007878e8aa6c688002b660032d8d1001e1f3a2a931a2000c3d745526344001c3aa8a1cc6880121fa1f7558d100043ec26eab1a20008bf845d5634400717908baac6880023be097558d1001476412eab1a200087e871d5634400717d0fba2c6880030fdd77458d100061e3aee8b1a2000c3f85dd163440018790bba2c6880021fe157458d100243e42ae8b1a20008ef825d163440051d904ba2c6880022fa1c7458d100061fba8e8b1a2000c3c751d163440010fd0faa2c6880121f21f5458d100061fba6a8b1a2003c3c74d5163441038d8e5aa2c6880021fa1d5458d100043e43aa8b1a2000c3f745516344007878e8aa2c6882031b1c95458d1001e4e3a486b1a207fccc7290d63440071b90ea1ac68800f271d14358d100070eaa286b1a207eccc7250d63440051dd0fb92c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031bd537258d1000636aa6e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440011bf0eb18c688002b32096318d1001e1f3a2a831a2000c3d74550634400187ee8aa6c48800f0f1d154d891000666310e6b12200487e87dd562440010fb09baac4880022fe11755891001c5e422eab1220008df835d562440231b906baac4880021fa1c755891001c5f43ee8b122000c3f75dd16244001878ebba2c4880030fe1774589100061e42ee8b12200087f855d162440090f90aba2c48800237e0d745891008c6e41ae8b1220008be871d1624400187eea3a2c4880030f1d474589100043f43ea8b12200487c87d51624400187ee9aa2c48800f0f1d354589100043f43aa8b12200087c87551624400187ee8aa2c48800f0f1d1545891008c6f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f54dcd62440018baa9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac48800317d5073589100062eaa0e6b122000cce421cd62440019984239ac488003331cf725891001c7643a84b122003cac745096244001c5aa8a12c488003331cd42589100146f41ced99220008df8758f324400559904b1e64880021fe15764c9100243e42aec99220008bf845d9324400717908bb2648800237e0d764c91000477c12ec99220008de8798d32440051b90eb1a648800ab3209634c91000c7b436e299220018df8758e314404b59904b1c6288003331cb634c5100046f438c698a2000ccc7218d31440011bf0eb18628806eb3209630c51000c77c3ac510a2000acc8358a2144037998c439a4288003331cf624851000c7d436e090a2000eca32d8d20440051f10eb1a4088003b258d3248110005f040a6490220178fa861c5204406d5d50d10a408800a3ea1b72c4110
  | 1 => 0xf06baac6900021fa1c7558d200051ec20eab1a400087f855d163480090f90aba2c6900023de057458d200047a40ae8b1a400087e87d5163480090f90faa2c6900021fa1d5458d200043e43aa8b1a4003c3e74551634800187ae8aa2c690003171d77358d200046fc3ac631a4000a5c8558c63480231b906ba8c69021f1b5cb5418d2040e3cb86a831a4003c3e74550634800187ae8aa0c69021b1b5c95418d204063cb82a831a4000e1d5450c63480fd9b2e0a18c6900038b5514218d2001674b828431a40019ea801c532480031db05baec2900063b60b74d852043e36b96a9b0a4003c3e74553614800187ae8aa6c29021b1b5c954d852001e563a285b0a4000e2d5450b61480011ef0eb08c29000a3e60375185200147cc06e830a4081c7970d50614800787ce8aa0c2900030f5d154185204063cb82a830a40018ec865cb314803739f0e996629000a3e21970cc520006e4992e198a40028f8865c231480051d9043b262900063ba1b724c520014e643a6498a4000ccc764c931480010ff0abb062900121f215760c52000c76432e418a40028f8865c031480239b0c6b8062900063ba1b738852000476c3cc710a40068ed87d8621480018f0edbaa6090006ba219324c120016743b2649824011ec8634c930480037910e992609000b7221d324c12000de5432649824001bc8864c93048055d910c9926090047b2dd9324c120016e53b2649824002dc8764c9304801bd90ec9926090216f2e15324c12042de4c2a649824000f4b754c93048109e90ea992609020ef2e11324c12041de4c22649824082f4b544c93048105e92a89926090002f2205324c120014f5416e29824000dc932dc530480033b50f18a6090002b6a1a314c12012e6c3b4629824011cd8760c530480017930418a609000b3a1da214c120005e5c1c42982400087d879d763c400147b093aec7880121fe1d75d8f100043fc22ebb1e200487e85dd363c40010fb0bba6c7880121fe1f54d8f100043ec3ea9b1e200087f8755363c40010fb0eaa6c7880030fdd154d8f1001e1e3a2a9b1e2000c7a755c363c40014bd0bb1cc7880463720d7598f1001e1f3a2a931e2000c3d7455263c4001c3aa8a1cc7880030fdd15458f1001e1e3a2a8b1e2000a5e85dcd63c40011bd0fa9ac78800317dd75358f100056b40ea6b1e2000a9d8414d63c40071b90ea1ac788003875514358f100046fc3ac631e2003c3e7455063c400187ae8aa0c78804637a0f75d8b100046ec1eebb162000c3f7455362c4007878e8aa6c5880030fdd15458b1001e1e3a2a8b1620038ec8750962c4001c5aa8a12c5880121fa1676ccb100043ec2ced99620028de839db32c40090fd0b3b265880021f616764cb100146e43ac69962002acc8258d32c40031eb0c38a65880473698d700c7100047cc06ebb1a2000
  | 2 => 0xc74d95302c43f43e87b2a600087d87d0f654c00187ee9a1eca980029ba0b43d953000536c1687b2a6000c3f7450f654c0010fd0e21eca9803e1f61c43d95300051f424e5b2a6000a3d849cb654c0af4bd06396ca981629760c72d95302c53d400e5b2a6000a79801cb654c0010fd0fa16ca980021f61f42d95300061fba685b2a6000a5e83d0b654c0014bb07a16ca980030fdd142d95300043f43885b2a600087d8710b654c0b14f500196ca9812e97a0f71d95302c52ec1ee3b2a6000a3f845c7654c00147908b8eca980021fa1f41d95300043ec3e83b2a6000c3f74907654c0010fd0e20eca980021f61c41d95300061fba083b2a6000a5e83107654c0014bb0620eca980029ba0841d953000536c1083b2a6058a7a80107654c0014f30020eca980021fa1c21d95300043ec3843b2a6000a3e84087654c00147b0810eca9800297a0c21d95300052ec1843b2a6058a7a80087654c0014f30010eca980028f61065d893001e1f3a2a9b126000c3d74553624c0071df0ea16c4980038b55142d89300243f42ce3b12600087d859c7624c0051bd0738ec4980063ea0271d89300043f43ecab12600087e87195624c00147b0832ac49822717dcc655893000ced404e39926000e4c32d95324c0b18b8edb2a64980039318b654c9300051ec20cbb0a6059c5d73197614c0031bb07baec2980063760f74d853043e2eb9ea9b0a6003c3e74553614c00187ae8aa6c29821b175cd54d85300046ec3c87b0a6000e1d5450f614c0011bb0f996c29806e37e1d32d85300051ec20cb30a6088c5d73196614c0090fd0dbaac2980021fa1f65585300061e3a6cab0a6000c6c72d95614c0010fd0e32ac2980028f61065585300061e3a0cab0a6000c6c72195614c00187ecbba2c2980030f197745853000637b2ee4b0a6000c6c65dc9614c00147b08328c2980023de1d611853001e1f3a2a830a6000c3d74550614c0018f0cab846298163179db658c5302c6ad386cb18a60019da805ca314c001caecbb0c629800676e1d708c53000636396ca98a6000c6f65dc9314c0018d8cbb926298003720c3724c5300dc6e432e418a600087f855da214c0090f90abb442980022fe11768853001c5e422ed10a60018de86dce214c0033b501b9c42980121fa1776485300043ec2eec90a60118dc831d9214c0031bd0db9a429800317d9773485300062e32ee690a60019da80dcd214c0018beca39a42980031719473485302c63d3b6cb9826058e5b63d97304c023b9664b9660980827661e31cc13001e1f3a2a9b1a4000c3d7455363480018baeba9ec690002b360b53d8d200054ec20a7b1a40038df8750f6348001c3aa8a1ec69000f0f9d15498d200061eba2a931a40038ef8750a634800795ce8a14c6900038b5514298d200243f43eeab1a400087d84dd563480011b
  | 3 => 0x231a4200acd82d44634840159f04a88c69086eb32095118d210052f42e8231a4200a5d85d04634843759d05a08c690802b360b4118d2100746a168231a4200e1d54904634843759905208c690802b3e094118d210dd664128231a4200e8d4250463484231bd0e208c6908023761c4118d210052f4288231a4200a5d851046348401c3aa8208c69086eb3a084118d2100566c108231a4200ada8010463484015b300208c69080297e157018d210052e42ae031a4211cd8705c063484231bd0e280c6908023761c5018d210054f420a031a4200a9d84140634843759d04280c690802b36085018d210056b408a031a4200ad58114063484014bd0ba00c690802976174018d210070eaa68031a421bace82d00634840159b05a00c690803875514018d2108c6f4388031a42008dd8710063484014bd0a200c690802976144018d210dd674108031a4200acd8210063484015ad02200c690802b56044018d2108c6f43c2031a42008dd87840634843759d05080c690802b360a1018d2108e6631ae598a4225ccc72d8d3148437998e431a62908033318f724c52110c76c3cc710a421bace8398e214840199ee831c4290803335d0638852100727aa0c710a4200e4d5418e214843799ce231c429086fb19c463885210061fba2a9b024203c3c745536048401c5aa8a16c09080237a1f63581210062fbaec6b024200c5c75d8d604840193ee9b1ac090803271d363581210046f438c6b024200c5f7518d60484018b8ea31ac09080327dd063581210064e3a0c6b024203c3e7455162cc00187ae8aa2c59800a3760c7158b300061fba2a930e6003c3c7455261cc0031b906baac3980023be09755873001476412eab0e60018dc835d161cc0011df04ba2c39800a3b209745873043e2e39ea8b0e6081c6c72d5161cc00187ee8aa2c39800f0f1d154587304362e39aa8b0e6080c6c7255161cc0ff998e521ac3980023721d43587300070eaa286b0e607eccc7250d61cc0051dd0fb92c398003331cf725873000637aa6e4b0e6000c6d54dc961cc001998e6392c39809637a1f32587300166639664b0e60008dc874c961cc005998e4992c398096b3209768c73012c6fc32e518e60018df8758631cc04b59904b0c639806eb3209610c73000c6e41aed10e60258df835d921cc0031b906bb243980021fa1b74d95300243fc3ec9b2a6000c3d74d93654c0010fb0f326ca980030fdd264d953000537414c9b2a6000a6d82993654c0010ff0eb26ca980030fdd164d953007c3ec38c9b2a6000c3d74193654c0b14b90ca1eca9800347dd143d95300070e32287b2a6000a3e8498b654c00147b09316ca980030fd0374d95300061ea06e9b2a600087d879d3654c00187ee93a6ca980030fe1174d95300043f438e9b2a6000c3d741d3654c1154bd063a6ca981629760
  | 4 => 0x34840153d093aec690802a761275d8d210062eba8ebb1a4200a5e859d363484014bb0b3a6c69080297a1474d8d210052ec28e9b1a4225ace821d3634840159b043a6c69080387d5254d8d210070fc22a9b1a4200e1f745536348401c38e8aa6c690a4387d0954d8d214870ea12a9b1a4200a9e84d47634840153b09a8ec69080395d4651d8d210052f42e83b1a4200a5d85d076348401c3aa920ec69080237a1c41d8d210046ec3883b1a4200a5e8510763484014bb0a20ec6908038755041d8d2112d6741083b1a4200acd8210763484015b50020ec690802b660041d8d210052f42ee1b1a4200a5d85dc3634844b59d05386c690802b360a70d8d210066db84e1b1a42008de8714363484011bb0e286c690802a7a1050d8d210054ec20a1b1a4225ace82143634840159b04286c690802b5a0450d8d210056ac08a1b1a4200a5e85d0363484014bb0ba06c6908038755340d8d210070eaa281b1a42008de8710363484011bb0e206c69080297a1440d8d210052ec2881b1a4225ace82103634840159b04206c690802b5a0440d8d210056ac0881b1a42258de8784363484011bb0f086c690896b3a0a10d8d2100566c1421b1a4203c3e74552634840187ae8aa4c69080e3be1d4298d2100716aa28531a421bcce7350a63484011bf06baac6908023be097558d210046fc1ae8b1a42008ef825d163484011ef02ba2c6908030fdd15458d2101e1e3a2a8b1a4200c6f54dc963484018daa9b92c69080237e1d6318d2108c6e41aea31a42118dc835d0634840787ce8aa0c6908030f5d15418d210052f42e8631a4200a5d85d0c6348401c3aa9a18c690802b360b4318d210070eaa28631a4200e2d5450863484010ff0ab80c6908121f2157018d2108e6c182e031a42008dd87994634840153d09328c690802a76126518d210046fc3aca31a42008dd8799063484014bd0b320c690802976166418d210046fc3ac831a4292ad78159063484014bd0a320c690802976146418d2148e2f3b6a831a4290c5e765506348401c3ec8aa0c690803871915418d2100747b228431a4200f0d54508634851f5ab03300c69084717dd67518d210052f42ce831a4200a5d859d0634843759d053a0c690802b360a7418d2147727216a831a428ee4c21d50634851b4bb0b2a0c69080387d525418d210dd67414a831a4200acd829506348401c3f08aa0c690803879d15418d210070eba2a831a428ce1f425506348519c9c84aa0c690a33875095418d214672610aa831a428ba5e85150634843759d042a0c690802b36085418d210dd67c228431a421be8f845086348401c9ea8a10c690803a39514218d2100726aa28431a4200e8d545086348401c1aa8a10c690803b1e054218d210056640a8431a4200ec481508634840153d09a88c690802a76135118d210dd67416a
  | 5 => 0x88023b61e10d89310056741c21b126200acd83843624c4011db0f328c498802aba12651893100556c24ca3126200acd83994624c4011df0eb28c498802b3e0d651893100476c3cc83126200a6e85990624c4014db0b320c498802b360e641893100477c3ac83126200acf83590624c4015cf02b20c4988029ba14641893100536c28c8312627face83190624c523c9ec7aa0c4988038bd91541893100716322a83126290e4f63550624c40159d0d218c498802b3a19431893100566432863126200e8f6450c624c401e1aa8a18c498802b360e601893100572c0cc03126225ccc629db324c40559d0db166498803339db62cc93112e66314e39926200ce7621c5324c44b59d0db92649880b331db724c93101567436c49926221ccc76d89324c437998c438a649880371dc8714c93112c6e432e518a6225ccc625ca314c44b59d0db1462988030fdd154d813101e1e3a2a9b026200e1d5450f604c405998e4996c0988023ba1f625813100637baec4b026200c6c75d89604c40195ee9b12c0988032b1d3625813100477438c4b026200c6f75189604c4018d8ea312c0988032bdd06258131006563a0c4b026203c3e74551620c40187ae8aa2c4188463b21d525883108c7643a84b106200e2d54509620c4371bf0eb16621886f339c962cc4310062faa6ec9886200c5d54dd9310c4019aca3bb2621880335547764c4310dce743ee49886200ccf76dc9310c40199eec392621886e3721d624c4310de66392c49886200c7754dd9310c4018eaa9bb262188473594f764c4310066aa9eec9886200ce776dc9310c4019ceec3926218a4f71dcc724c43101e1f3a2a8b006200c3d74551600c4231f10ea82c0188463e21d40580310071caa280b0062018fa80dd763884011f301baec7108023da0774d8e210061fba2a9b1c4203c3c74553638840787ce8aa4c7108030f5d15498e210070eaa28731c4200c3f745516388407878e8aa2c71080e3721d4358e210070eaa286b1c42008df8758c638840787ce8aa0c7108030f5d15418e2112c77c3ac799442259cf8758f328844bb8ce738e65108a23be1971cca2110e66bb66598c4225ccc72d8d31884011bd0e31a631086f331c8634c62112ce743e6498c4228ccf76cc931884011bf0eb1863108030fdd1545822101e1e3a2a8b0442038f8875016088401c72a8a02c1108030fdd154d8d2101e1e3a2a9b1a4200c5d75d4f63484091bf0ea9ec690802a7a1053d8d210054ec20a7b1a4200a5e85d0f63484014bb0ba1ec6908038755343d8d2101c6fc3a87b1a4200e1d5450f63484014bd0a21ec6908029761443d8d2100566c1061b1a4200a9e84997634840153b0932ec69080297a1664d8d210052ec2cc9b1a4200a5e8519363484014bb0a326c69080387d9154d8d210070e322a9b1a4200f0d5450b6
  | 6 => 0x80101101e0240c816002014010020180000000003c1740f00400c000008000060380002300a0980002004c00c0200e0900e81900a37a0f759873200c7d406eb30e64008f980dd661cc8051bd07ba4c399207179cf54987320061fba2a930e6403c3c7455261cc9018bce6aa4c3990030fdd1545873201e1e3a2a8b0e6400e2d5450961cc80787ce8aa2c1990030f5d1545833200716aa284b066411dcb305c3324c80787ce8aa6c2990030f5d154d85320071aaa083b0a6400ad583107614c8015cb0420ec299002bc60041d85320047bc3ac230a6493ad783584614c8051bb07ba8c29900a3760f741853240e2eb9ea830a6403c3e74550614c80187ae8aa0c299203175cd54185320071aaa08230a6400af180104614c80787ce8aa6c0990030f5d154d813200c76412e3b026403c3e7455162cc40187ae8aa2c59880f0f9d154583310061eba2a8b066200e1d5450d60cc40187ee8aa2c51880f0f1d15458a3101c7643a84b146200e2d54509628c527b886438a651889637e1d62cc63112e67392c598c6200c3f74551608c407878e8aa2c11880e3e21d40582310071caa280b046200c3f74553624c407878e8aa6c4988123be1d52d89310053742e85b126200a6d85d0b624c401c5aa9a16c49880e3be1d42d893100716aa285b126200aae84997624c40155b0932ec4988029ba1664d893100536c2cc9b126200a6e85193624c4014db0a326c498a071b9db54d8931406373b2a9b126200e2f64553624c401c58c8aa6c4989fb339d943d893100786aa287b126200aae849d7624c40155b093aec4988029ba1674d893100536c2ce9b126200a6e851d3624c4014db0a3a6c498802b3a0c74d893100566c18e9b126200e2f54953624c401c5f08aa6c4988038bdd154d8931007163a2a9b126200e4f5394f624c40155d0829ec498802ab61053d89310047743e87b1262008ed87d0f624c4014dd0ba1ec4988029b61743d893100716aa687b126200e2d5450f624c4014dd0a21ec4988029b61443d893100557426a3b126200aad84d47624c401ccea328ec4988029ba1741d893100536c2e83b126200e2d54907624c4011dd0e20ec4988863b61c41d89310053742883b126200a6d85107624c401c5aa820ec498802b3a0c41d893100566c1883b126200aea80107624c4015d30020ec498886b3a0e70d893100566c1ce1b1262008ee87143624c4011db0e286c498802aba1050d893100556c20a1b126200ace83143624c40159b06286c498802b9a0450d893100572c08a1b126200a6e85d03624c4014db0ba06c4988038b55340d893100716aa281b1262008ee87103624c4011db0e206c4988029ba1440d893100536c2881b126200ace83103624c40159b06206c498802b9a0440d893100572c0881b1262008ee870c3624c4431db0e186c49
  | 7 => 0xbbb6a0005d84cb123d60c092800000000002e80588354925c492001ac03e10c35800061000504001d10003f00031454a0004580055a0000026527669c663a400098174a7f000dd8003054a6bcd0480000032cee97206c939c239d5fe4b02f96d15e8483328d1c47710abb73888588f00d58a55558a700006b52c1c90d2e4da130c48ab0c82b381d07d1289fd5402c4891ac5fa6903baa374c6cd7381245209d1900000046c9fa6f7809597e38154cde4ff8c057eb7da084d0f42459635d654735448cf4c8108ff0172f08dc6d0492727958f0aa1ae6f8001ec0005d03505a17898d9d2fb1c2510db8ad42e6c40002664838c002500000000030d0005bc00369102d3d221bb752964bf00044800000000000001b837f184010878de0349d43f84b182e18863b9370d2c86bac208130f40086e69a58097013e0e43c2a12ba40c1e9674b434c002ba3dc001d90241b21b5ba00020eba8d4000000a6d678000005386d8000000010e80b000a90cc2760002e0b58136c693c7d00054e86508a83000c803000000052d859970402d8941a1000be1733a731cae5bd8327303a4002d4744000001d436421c000006a0121583805c4640912a835e7484a0f6068eadcb9311a423800a9d56456c5f2de32a650b99d34284e055a3b61c5000620447e534c680063e260ed1ab290e84ebb8f1cc91c0017c07e001aa05c006b740035f01c334a3a2b05a701050a45d800036000000345c38a922e270af94c1de9ec0034c6b6275bf28f000dc4000000000018e0004be001830c610a0000027119425505b8e6364d4de000344000011115c0898f99a96922ed65bb56aa001a40003ce644000000000004f00076c001cf000000000000b45eaa4d7900401701e0100001b0000000280700800c02000000008000000100680400002800c06803004054028030000200380000200400801022010068000000000d80100400400010000000480010040000080b02a0040002000a08c0000002e08008807006004148170160000180200a044000190060180102800c0000001200621808814000008200090260b8040000080000380002e0100300406e0700080100002c078000240340000000e0480000c00000000020082010010020040182f8020020040400200a01000014008000000020040000000600e068008000100000501b000004008120020181200000e000018050020000b801052010038050020000c81c00008c038b701c03c00084004058018490060280a02f01e00800001018000038000020080101a000000000210140001d8070000040380c0020100100307e000040010021a80180402418c0000c006018000020ae0000500a006020008060900401701202803c000000380000900b0060000800400204800804004018010020020200080401c02
  | 8 => 0x240bacc3a8e000e815eb2f00060c000006a43f4eb0000007e4000f74e6000000c46ea1c91a8091aa9dc111e11c871cef8a726ea7c532fe56c188279d543683c5ea8a0005656d82900042015a395809f988a985882ddc1a421e6ab92ea4a000bb833a80532db42a38938a00028a073b08052916a34a06c0034a5706e4003c159ad003da62042d145438a5f4468973100fae20ec9f161ecd0199300002316121039424000037340c8554b390942b0001514e4001412bb000a047a800000b84c42c9604c100a11d0ec0140010a08c3e4003156cc2490111356aa69360002f4ef5cc99c2f29055607925eaf00034356e3b9dd9fa0e80000039c00078d3709b6aed710f0002e20011024c0000e9670000000000036c19c4e9308004d0abcc12d626699c000003ea6c00000000054d7ba7d3826a92f19b2024008318c6568d183b641a0e541a8682b8a5d990ff36a7c8398f0724c5ce420c2ac871949ed2c8281be17b69a18da33be1c0a70b2a2a6cedf485a665a41ac7f0231d80f095bae65ae088c00a0aa499b7850020d88ad22c50eb1cfbadc5e8470c787c59862dd281d6109d14b1fc4962685d18a1423c511a8575ae58410fb0dcde1cf9ae0ca101608c8660db88a23a30264cf81ce2b053d8d02f7500c5d1b90252a2c921d024621023828032e459f04e64a2b99b9996322fc8fa4d4f073c4022f26c3711896102289d918d404aed0a91c30b69e51e89630acfdb2ad73d2818b307521250dc586f172820d30c501ebbd1684164415de234733ea886f949030000451e03681c0f5000426c75e181600e235242aa03eb4c000445e00013d02a3b6000b622e2dca300000000080cde8000004f5af243294589c68b23de000510f45da000000003cc220002556629f000333612455d52d822c0002b1190b0790000002844d1d7b3d44496caf12a0008cd4804353cec0a832777e674cb19238cb28002465289ac619a366a3e13508f6e4708cf05d0005d40f21840036096abe6a6a21942c8434b40e623c4424400039a1ca58d433b80fc95de11682a88c1ca10e1bad44499ba7746fd2a361000a10000003f60005283b43e518ef038000000c480070a1c43200665c2d49f0b01465f444bb1000000e5ad13348f978a366c0000ab8000000000a8ea52a1780000016600181ab4556000000005c88a1200c9000da07692140ac4c0034e000600b002e2d2e6c001320a4d64228001ce31d93145000b94000eb000c602cb6b3f049c9e2d9038c298026d5b4b199da2541c14dad000566000000835aa0018b1b66ee3c8fb37a678be44bb8c522d5881344308bd99b2e30008e0f10007660000017f778618
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x482130002c540c9424010400000000c400055d48f508440138b11cd560a4f100e4003cd05870a0ec6158b95080915468e11400f8fce830504000014415114c10cd248d20c00000c82934bc75189801409c7c00d8001c8408784d28b45cad3cdc34190c6400a8386c892c10100043c892061c1860000800040401620003820a5408a1e5c01a155460c41d85320068955182107614c801a315460041d85320068c55180104614c80782c875514258a3101e0e21d54501608c529c0e7655143d89310058364c74553624c40182e8755343d89310060ba1d54107624c401a0d5460c41d89310068a55180107624c401a0e865514318931006832195450c624c5274c696dc8714c9310050da4774553638840781c875514358e2101e0e21d54501608840160d921d154d8d2100607a1d541076348401a0d5460841d8d210068655180107634840121d94a1770d8d210063260b709c3634840782f875514298d210068355182d0c634840160d929d15418d2146d83656545086348401e0554e054218d2100683550815086348401e05542054218d210068361542d04634843728c985094118d210060761d541046348401a0d546084118d210068655180104634840121d942157018d210068355182d006348401c0f7455063885210060721d5450d61cc129c0c7255143587300060bdd182993654c00903e98dd164d95300040fe6174193654c00103f985d074d95300060bdd182d0f654c00181f7460f42d953000607dd183107654c00182f7460841d95300060edd180107654c00782f8755142d89300040f65287d95624c00181f736106558930006075cd84197614c00181d7361065985300040f66074195614c00182d841c865585300040fa6065dd1614c00142d9419772585300050e650655c2314c00142d94197724c53000472a6030dc9314c00141d94197734853000507650651cd214c00781f8755143d8d2001e0be1d5450a634800903c985d15458d200050d24574551634800141d941d77358d20004876508558c6348129c19705514318d204070a5c1545086348001c4876dd5324c1200dc72e6132dc530480032ca96e0e214c1200240fa637455363c4001439949d570d8f100048765285d8e63c400121d94a177358f1001e0721d5450d63c400782c875514258b100050725d5450d634400781c875514358d104a7031c95450d634400148d9408473589100050b25d54509624400782c875514258910007035507350962440054c89758d3248110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94d
  | 6 => 0x94b
  | 7 => 0x94e
  | 8 => 0x138b
  | 9 => 0x138d
  | 10 => 0x138e
  | 11 => 0x98d
  | 12 => 0x98e
  | 13 => 0x9cb
  | 14 => 0x9cd
  | 15 => 0x9ce
  | 16 => 0x168b
  | 17 => 0x4
  | 18 => 0x168d
  | 19 => 0x168e
  | 20 => 0xb09
  | 21 => 0xb0d
  | 22 => 0xb0e
  | 23 => 0x1409
  | 24 => 0x140d
  | 25 => 0x140e
  | 26 => 0x249
  | 27 => 0x24b
  | 28 => 0x24d
  | 29 => 0x24e
  | 30 => 0x144d
  | 31 => 0x16cd
  | 32 => 0xb49
  | 33 => 0xb4b
  | 34 => 0xb4d
  | 35 => 0xb4e
  | 36 => 0x1449
  | 37 => 0x144b
  | 38 => 0x144e
  | 39 => 0x16c9
  | 40 => 0x16cb
  | 41 => 0x16ce
  | 42 => 0xcc9
  | 43 => 0xccd
  | 44 => 0xcce
  | 45 => 0x1709
  | 46 => 0x170d
  | 47 => 0x170e
  | 48 => 0x138955
  | 49 => 0x138956
  | 50 => 0x95395
  | 51 => 0x98955
  | 52 => 0x98956
  | 53 => 0x94995
  | 54 => 0x209
  | 55 => 0x1549
  | 56 => 0x9c995
  | 57 => 0x9c996
  | 58 => 0x140995
  | 59 => 0x99415
  | 60 => 0x99416
  | 61 => 0x4b
  | 62 => 0x124b
  | 63 => 0xcc995
  | 64 => 0x98cd5
  | 65 => 0x98cd6
  | 66 => 0x3c9
  | 67 => 0xcb
  | 68 => 0x15c9
  | 69 => 0x12cb
  | 70 => 0x1689d5
  | 71 => 0x1689d6
  | 72 => 0x249d5
  | 73 => 0x9c255
  | 74 => 0x249d6
  | 75 => 0x9c256
  | 76 => 0x1449d5
  | 77 => 0x9d455
  | 78 => 0x1449d6
  | 79 => 0x9d456
  | 80 => 0xcc9d5
  | 81 => 0x9ccd5
  | 82 => 0xcc9d6
  | 83 => 0x9ccd6
  | 84 => 0x1709d5
  | 85 => 0x9d715
  | 86 => 0x1709d6
  | 87 => 0x9d716
  | 88 => 0x17c9
  | 89 => 0x5c9
  | 90 => 0x25695
  | 91 => 0x168255
  | 92 => 0x168256
  | 93 => 0x145695
  | 94 => 0x169455
  | 95 => 0x169456
  | 96 => 0xcd695
  | 97 => 0x168cd5
  | 98 => 0x168cd6
  | 99 => 0x171695
  | 100 => 0x169715
  | 101 => 0x169716
  | 102 => 0x140b15
  | 103 => 0xb1415
  | 104 => 0x171415
  | 105 => 0xb4256
  | 106 => 0xb4255
  | 107 => 0xb5455
  | 108 => 0x144253
  | 109 => 0x144255
  | 110 => 0x1456d5
  | 111 => 0x24b55
  | 112 => 0x16c255
  | 113 => 0x144b55
  | 114 => 0x16cb55
  | 115 => 0xccb55
  | 116 => 0xb4cd5
  | 117 => 0x170b55
  | 118 => 0xb5715
  | 119 => 0x16d456
  | 120 => 0x16d455
  | 121 => 0xcd6d5
  | 122 => 0x16ccd5
  | 123 => 0x1716d5
  | 124 => 0x16d715
  | 125 => 0x170cd5
  | 126 => 0xe8b
  | 127 => 0x178b
  | 128 => 0x104b
  | 129 => 0x1a8b
  | 130 => 0xcc9c99d
  | 131 => 0x9c98cdd
  | 132 => 0xcc9c99e
  | 133 => 0x9c98cde
  | 134 => 0x1049
  | 135 => 0x1a89
  | 136 => 0x5cb51
  | 137 => 0x5d5d1
  | 138 => 0x9d796
  | 139 => 0x25a93
  | 140 => 0x104253
  | 141 => 0x25053
  | 142 => 0x1a8253
  | 143 => 0x24953
  | 144 => 0x105453
  | 145 => 0x1a9453
  | 146 => 0x25853
  | 147 => 0x25453
  | 148 => 0x104e93
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1242
  | 6 => 2282
  | 5 => 965
  | 4 => 89
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (50508+((h/414+packedAt gbK7 (45954+(h % 414)*11) 11) % 1804)*12) 12
  | 6 => packedAt gbK6 (119416+((h/760+packedAt gbK6 (109536+(h % 760)*13) 13) % 4408)*13) 13
  | 5 => packedAt gbK5 (60466+((h/321+packedAt gbK5 (56935+(h % 321)*11) 11) % 1159)*11) 11
  | 4 => packedAt gbK4 (6433+((h/29+packedAt gbK4 (6230+(h % 29)*7) 7) % 107)*8) 8
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fffc3e0787f87f80fff0ff0014c0cfe0dce7c
  | 1 => 0x83807c007f83f83ff01ffffff2b073303273ff
  | 2 => 0xfc007fff8003ffc0001ff0fffcc783c3c3838f
  | 3 => 0x7ffffffc0000001fff000f07fc03fc03f0
  | 4 => 0x7fffffffffffffe000000ff80003fffc00
  | 5 => 0xffff800000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x148740621815814821c789906004045604c63c
  | 1 => 0x810904002880881260491224a01031301050d5
  | 2 => 0x581259aa801355808292a8cb44c582c2c3830a
  | 3 => 0x10246ed375580101451ccc818b06dc037c03e0
  | 4 => 0x4040331c466266258e0000020fe80001ab2800
  | 5 => 0x62780018044044060800000c0ffb6ba8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36334
namespace PEqualNP.Outside.L_meta_36334
open PEqualNP.Outside.L_meta_36334.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 6 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 90 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
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
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 99 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
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
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
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
theorem bs4_4_384 : Interval s4Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 414 := (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384))))
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
theorem bs4_5_608 : Interval s4Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 616 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 bs4_5_512) (concat bs4_5_544 (concat bs4_5_576 bs4_5_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
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
theorem bs5_4_512 : Interval s5Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 bs5_4_224))) (concat (concat (concat bs5_4_256 bs5_4_288) (concat bs5_4_320 bs5_4_352)) (concat (concat bs5_4_384 bs5_4_416) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 89 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_960 : Interval gbAtlas 5 960 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 965 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 bgb_5_576)) (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704))) (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832)) (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)))))
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
theorem bgb_6_2272 : Interval gbAtlas 6 2272 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2282 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))))) (concat (concat (concat (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)) (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))))) (concat (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)))) (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)))))))
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
theorem bgb_7_1216 : Interval gbAtlas 7 1216 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1242 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 (concat bgb_7_384 bgb_7_416))) (concat (concat bgb_7_448 bgb_7_480) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))))) (concat (concat (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)))) (concat (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056))) (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0feeefeeafeeec8c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4277061824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36334.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[3,6]⟩,⟨.and,[2,7]⟩,⟨.or,[4,7]⟩,⟨.and,[0,3]⟩,⟨.or,[2,10]⟩,⟨.or,[9,11]⟩,⟨.and,[0,6]⟩,⟨.or,[1,8]⟩,⟨.and,[12,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277061824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277061824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36334

open PEqualNP.Outside.L_meta_36334 in
theorem PEqualNP.Outside.L_meta_36334 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277061824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277061824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
