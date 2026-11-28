import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36352.Model
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


end PEqualNP.Outside.L_meta_36352.Model

namespace PEqualNP.Outside.L_meta_36352
open PEqualNP.Outside.L_meta_36352.Model
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

def SBf (j : Nat) : Nat := [6, 6, 7, 7, 8, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 50]

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

end PEqualNP.Outside.L_meta_36352

namespace PEqualNP.Outside.L_meta_36352
open PEqualNP.Outside.L_meta_36352.Model
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
end PEqualNP.Outside.L_meta_36352
namespace PEqualNP.Outside.L_meta_36352
open PEqualNP.Outside.L_meta_36352.Model
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
end PEqualNP.Outside.L_meta_36352
namespace PEqualNP.Outside.L_meta_36352
open PEqualNP.Outside.L_meta_36352.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x400a12130c80c002a00080008c00000b11210e7569b1c50f00009400f4e2559200004001a642a9000011c006800a0000010169889606a8017187c38080140018512180010800102ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x562556d16203f10000a1335670d0065690044000000331f6e4000000000024f0060005e5a4300504c262b1d63293400385b7172481c2428465f0b522a4b66043d005c6b112215232e170049084e3e3a58743000001b39064d1e120e54730c5d31143c09016f59003b5718362c2f006c0027210364471961001a3700002d517025076a45564a0f68410032425306968100000d83850683000400011e030003840303010100068004800104038502850b808180004f55243b7294876d5290eeea2a1dd14543cfa9a87b75150f68a2a1cf95043b7290876d5210ebca6215754c42d6a10853e54cca7aa9996750f32b6a9c65af438cb5a87196750d32bba8a6574514cb9ea6996bd0d32e721a65ad434cb9a86996350d32f3a8a65e4514ca7ca8194f55032b7290655e53d06baa7a0db94b41b6a96833e54cc67aa998db94b31b6a96639d438c79a6518cf950319eaa0639d430c6dca418db54831e6990637a500c6f2a018cf953219eaa6435e53c86baa790dd94640baa8c816f52502d8a4a05794c40aea98816e52102daa4205d94440baa88813e54cc27aa9986750f30b7296616d52cc39a65985d94630baa8c619d434c39a64984f950309eaa0616e520c2daa4185d94430baa88617651882eaa3104fd51209e2a2413e540827aa8105794c20aea98417651082eaa2106dd0f10daa1e21e632c43ca65885d546109faa2213c54442bea6885714d10b7a92216c524436ea8886d15110eba9a21d4534436e86886d50d10f3a9221e452443cc6488794c910f9a8221f230443e260885d94410
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xa82796ba690ab00614712a0638000040000031a880108000800080140202103c354d4210b154314532a3592434cac46150d32e1d85434cb846150d32e150f514cb854314532c350d520c70d544c831c650d500c74932540319358c525030d4354b30c355132cc21d6315120e150d32c43145414d108d19543443445314910991953244385434c910e450d30443c1324c110
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xc204000a0cebb0a86994877650f514ca823aa869922181195434c910
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s2K5 (841+((h/15+packedAt s2K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s2K4 (3471+((h/39+packedAt s2K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s2K3 (960+((h/8+packedAt s2K3 (912+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s2K2 (200+((h/1+packedAt s2K2 (196+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x87ffff07fe1fff07e1fe1fffc3f81ffe91f33f
  | 1 => 0xf81e1ff83fe1e1f8fe1fe1c1fc3fe1c16ecdcc
  | 3 => 0xffe01fffc001ffff001ffe01ffc001ff8f0e0f
  | 4 => 0x1ffffffe01ffffe00001fffffe01f00ff0
  | 5 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x90400110802000002022024440484444005115
  | 1 => 0x12c4223194028228620e208cc412c48c26c54c
  | 3 => 0x218d54430d55515b11155411aa8189398b0e0a
  | 4 => 0x65119884291055959541102133251811d00aa0
  | 5 => 0x461910e6319999e6d999993822061021fda000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00eeeeeeaaeeeeaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36352
namespace PEqualNP.Outside.L_meta_36352
open PEqualNP.Outside.L_meta_36352.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x689320001c02314872450a8200a851d008459722892004c7c020508c025003c0001cb09800000f05002168334ac0000c58da720602000d02001c2000040080100ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x3f0000000000001c002200170072060011425d151400510865260434104e0025531e0073614736194535400d0000000712003c445e320000005800641a6c33003b2e6f00003a70745c0b246a6b2f462c6939215b0a054c163143564d6d09710c3d4a4f1f2b29606e2a0241525f031b680e5001183e4938664b5700370000003063546200005a2d27005513286748000000001d0000002300200f59000300028019028000858b860587000480010180818011010e01018d00008202050080010200014f55243b7294876d5290eeea2a1dd14543cfa9a87b75150f68a2a1cf95043b7290876d5210ebca6215754c42d6a10853e54cca7aa9996750f32b6a9c65af438cb5a87196750d32bba8a6574514cb9ea6996bd0d32e721a65ad434cb9a86996350d32f3a8a65e4514ca7ca8194f55032b7290655e53d06baa7a0db94b41b6a96833e54cc67aa998db94b31b6a96639d438c79a6518cf950319eaa0639d430c6dca418db54831e6990637a500c6f2a018cf953219eaa6435e53c86baa790dd94640baa8c816f52502d8a4a05794c40aea98816e52102daa4205d94440baa88813e54cc27aa9986750f30b7296616d52cc39a65985d94630baa8c619d434c39a64984f950309eaa0616e520c2daa4185d94430baa88617651882eaa3104fd51209e2a2413e540827aa8105794c20aea98417651082eaa2106dd0f10daa1e21e632c43ca65885d546109faa2213c54442bea6885714d10b7a92216c524436ea8886d15110eba9a21d4534436e86886d50d10f3a9221e452443cc6488794c910f9a8221f230443e260885d94410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1a89600c382006494010aa6b8800081e004a0a62472c3440450421c354d4210b154314532a3592434cac46150d32e1d85434cb846150d32e150f514cb854314532c350d520c70d544c831c650d500c74932540319358c525030d4354b30c355132cc21d6315120e150d32c43145414d108d19543443445314910991953244385434c910e450d30443c1324c110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x100c10a0cebb0a86994877650f514ca823aa869922181195434c910
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 4 => packedAt s3K4 (3471+((h/39+packedAt s3K4 (3159+(h % 39)*8) 8) % 155)*8) 8
  | 3 => packedAt s3K3 (952+((h/8+packedAt s3K3 (912+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (199+((h/1+packedAt s3K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x87ffff07fe1fff07e1fe1fffc3f81ffe91f33f
  | 1 => 0xf81e1ff83fe1e1f8fe1fe1c1fc3fe1c16ecdcc
  | 2 => 0xffe01fffc001ffff001ffe01ffc001ff8f0e0f
  | 4 => 0x1ffffffe01ffffe00001fffffe01f00ff0
  | 5 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x90400110802000002022024440484444005115
  | 1 => 0x12c4223194028228620e208cc412c48c26c54c
  | 2 => 0x218d54430d55515b11155411aa8189398b0e0a
  | 4 => 0x65119884291055959541102133251811d00aa0
  | 5 => 0x461910e6319999e6d999993822061021fda000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0eeeeeaeaeeeea0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36352
namespace PEqualNP.Outside.L_meta_36352
open PEqualNP.Outside.L_meta_36352.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x11200200002800000067c00000015804e3401d3438028484000c389400914994912a802160e19505360001844051970084c8b3c000131e24054100710000400000fff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41f741fe41fd41fc41f441ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x261de434c3ba86985fd4930be29261df324c3ba64985fd4530be28a61f7414c3e882987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c2fca4187b94830b7290617d520c3daa4185b54830bf28861f6510c2eca2185f54430faa886175510c3ee82187d10430bf28061df300c3f46018774c030fc980617f54c82fca9905f55320be2a6417f53c82fca7905f54f20be29e41ee42c83da85907b8cb20f6996417e51c82faa3907dd0720fa20e417f54882fca9105f55220be2a4417f53882fca7105f54e20be29c417d52882fca3107d94620bb28c417d51883eaa3105d54620fba0c41f441882fca1107e8c220fc98441ef20883f641105fd5120bf2a2417d54482f8a8905fd4d20bf29a417d53482f8a6907b90920f6a1241ee32483da64905fd4520be28a41f741483e882907e8c120fc98241fb20483dc40905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf29841de53082bca6105f54c20eea98415d53082f8a6105f94820bf28841f651082eca2105f54420faa88417551083ee82107d10420bf28041ef20083f440107b48020fc900417f54c42fca9885f55310be2a6217f53c42fca7885f54f10be29e217f52c42fca5885f54b10be29621f741c43ec83887d50710fa20e21f731c43ec63887d4c710fa18e21f721c43ec43887d48710fa10e21f754c43eca9885d95310faaa621f454c42e8a9887dd4f10fb29e21f553c43e8a7887dd0f10fb21e21f543c43e887887dd4b10fb29621f552c43e8a5887dd0b10fb21621f542c43e885887dccb10fb19621f532c43e865887dd0310fb20621f540c43e881887dcc310fb18621f530c43e861887dc8310fb10621f520c43e841885fd5210bf2a4217d54842f8a9085fd4e10bf29c217d53842f8a7085fd4a10bf294217d52842f8a5085f54610baa8c21f741843e883085f94210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ee82887d90510faa0a21f441443ee62887d8c510fa98a21f431443ee42887d88510fa90a21f421443f620887d84110fbaa221b754443eca8885d95110faaa221f454442e8a8886d151109a2a221f753443eca6887d54d10fa29a21f743443ec86887d50d10fa21a21f752443eca4887d54910fa29221f742443ec84887d50910fa21221f732443ec64887d4c910fa19221f750443e6a0887dd0110fb20221f540443e880887dcc110fb18221f530443e860887dc8110fb10221f520443e840885fd5010bf2a0217d54042f8a8085fd4c10bf298217d53042f8a6085fd4810bf290217d52042f8a4085f94410bb28821f741043e882085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf41907ee8320df94241bea84837f53506f8a6a0dfd4941be29283f7415077c82a0dfd4141be282837e54106fca620df54c41dfa1883bd43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea8083f654106eca820ed95041fba9883f653107eaa620fd14c41fba1883b743107ec8620fd50c41daa1883f443107eea420fd94841faa9083f452107ee8420edd0841fb21083f5421076a8420fd10841fb99083f632107ea6420fd0c841fba8083f650107eaa020dd54041fa280837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a6637e52cc6faa598fdd0731fa20e637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31bf294637d528c6fca318fdd0631fa20c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a2637f524c6f8a498fdd0531fa20a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863f7410c7e88218f7cc431fb18863dd310c7ea6218df94031bea80637f54c86fca990ef953219f2a6437d54c877aa990cf55321be2a6437f53c86fca790df54f21be29e43f741c87e88390fdcc721fa18e437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21bf28c43f741887e88310fd8c621fa98c43ef21887ee4310df94221bea84437f54486fca890df55121be2a2437f53486fca690df54d21be29a43f741487e88290fd8c521fa98a43f721487dc4290dfd4121be282437f54086fca810df55021be2a0437f53086fca610df54c21be298437e52086fca210fdd0421fa20843f731087e86210fbc8421fb10843ed21087ea4210df94021bea80437e53d02faa7a06fd0f40dea1e817e52d02faa5a06fd0b40dea1681f751d02fca3a05f54740fa28e81f741d03e883a05f55240bf29c817d53902fca5205f54a40bf28c81f651902eca3205f54640faa8c817551903ee83206f90640de20c81f4419036883205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940dfa1281bd42502fea2a07dd4540bba8a817c51503e8a2a05d14540fba0a81f441503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2207dd0440df20881bc41103e882206d10440bf28081bf40103f480206f50040fca00817f54cc2fca9985f55330be2a661de43cc3ba87985f94b30bea9661df32cc3ba65985f94730bea8e61f741cc3e883985fd5230bf2a4617d548c2f8a9185f54e30bf294617d528c2fca3187d94630bb28c617d518c3eaa3185d54630fba0c61f4418c2fca11877cc230fd984617f544c2fca8985f55130be2a
  | 2 => 0x4000000020160000000000000c03000000004000000080040280200a0080780300800000008002008030010000100000500400002001000000008000020000000500000c01803000000000060000000000100200c0000500000c0280703000400007008010000020000000080200000400804014030018010140080000000000800000000008000040020000000000e00800800000004030010000100000300000802801000020008010020000a8040020180080600602c0080000200016807002000000000080140100200201c0400700200800802000004008030020000100100600c0580000c00c000010060040300600401c030000000800000000a00000000000000010040000000000400c00c03810006000000010000040480100400004000002000018040000080080000000004000002020010010020040000d008004000020020080280000200000800008004020030000000000300001000001008004008000080040000100000afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1fdd4543bba8a877c5150fe8a2a1dd14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c85f65190aeca3215f54642faa8c85755190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a17dd4542bba8a857c5150be8a2a15d14542bfa82857c5050afca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e837e52d06faa5a0df94341bea8683f753d07eca7a0fd54f41fa29e83f743d07ec87a0fd50f41fa21e83f752d07eca5a0fd54b41fa29683f742d07ec85a0fd50b41fa21683f732d07ec65a0fd4cb41fa19683f750d07eca1a0fd54341baa8683f450d06faa920df94e41bea9c83bf439077a8720df94a41bea9483bf429077a8520df94641bb28c83b
  | 3 => 0x47c000000d200034000000000000af000818000eb000860031dd4dcb1d010000002502719c5a8000452d05388848a904050504048c05780015c86528e12c0000000004c3d8ae14a845560000004491905329c000d293e19208c00017000a60840000289dd75000000b54000002863b0980000002f4958c15841fd849f90007fc470000000000713b554c38da06601a67c002de000b7c002ab08a000c180030400080225000a98000001f408478b16000000952d932475400000614000000000002ac8680052c634089fd594000000b70002580020d000c55110000c46f0001010fc0000026328448c0004710e714040000004954226706a000fb8bb0003b81f8002389640000000000107a72102000e705c3582980005b37a000002241e670c37000000c80000fe3ea7050f2fb38c5fd041531f2001602b42debfc000002a8be49b80000000000000000000081b50000006b800000000620922f2c0c000604407d8c99720349700005a4cc00092000236c2c002e5000ba01c15b4fc7992d89b086000002195026451b0cd06e2c8ae00022c00000000000a7c000365480ed060000e4144000f705ac3cf600048ebccf180000065c2c2cf000001178001100000000022880c0000000000000000000000000b84840000012e0000000011151e1f071a4803c664b52124d60000021a1b4760179a10d80012c231000000000000009e12580018c2780180026ab8162a8b000060880120003f026139000000e8a3a5822d0292073747ed7b2b55c60a4000004fa000519580005e80215528c000268005203a80000000053000241370c48000000000014d80043ac70d69cf2c2668002b70548e0002fe2f8a500000049c95530af53e06ecc30002a4abce00fb5b48f8000000007a53a18761a42c708150000012b02c63e000002a5000acc0000000000115000000000b4aef3b21d5378e700078800000000000002802dc000000003f400180acc000000eb8705102141830c4a8000001d40008d0c21eb0be3780030403e329501a92e87ccef1d30000002f0004a00009f8000000004000000026405a0116225cfc15f18400000000000000000000008a40000c000094002600008fcb031d0d6b70000003946a09c22d000001000774580000000000000000244542000a680000000000257000a14c52e11a00000000000400000000000001460d8000000460000000ac000000000000026435e000f7927354641763002424681207950430c002ba0000011a8005c8190e209d49877c1a00000089c0000023087d072231dab980018e00009c00000000000001f115a374001be51a2c093000292600561e160eb58d92ed13e558d01671e06fcb20cb2046786890f3309a55eb024fe0000023c000000001b100068954800000000000000d4ae0598000009a904acb0060
  | 4 => 0x1eca1c001da5ae000628006289a0d300032a6e40013d1222f80000008c7200000000022c00000000a9d898000001e01100a550014b9a1735c855362d83c00000004100e0580017d38e3593d8000000000018f172424001a300052c4a94f3665a0000000003e0b283e57c24cbda9734ec853c8004ba000412141404780025e4ea080000004143bc002fa4200000007d2cc0002a21c5a431c002620e658c2e80052a7d000243092004000df07a000000002ee3557480000000053a760000001e0000000000000040a76c968000000008180000066cbaaae2fc00000000000268f200016a000860002e0bf40012205c000000002500000003a000a74a4140398464000005ce9941c8000ae000000f2426810a88610004c8002a33da15800188000740002b10009f05b22b4367340009c3842908b8590aa624001ab00000120181000000001060a06900006d0000000c8d93b8000872f2240a795f8005f80000000046023400136000001488332269c40000051294c000f53ca4a4643115eebe020283328000000005600006a0000000000031a0deb10130e80007b98815e0848ec222b63fc0007f8005e0aec3b1591542f0c28d349e000b5b055e8b3943249524568d820b2148f4000982da33d1ba8a036c795927000000000133000968988001987a929086000000000000ce3d00000000079c74ad336e0000019d000000002735a200000032632ab4000a9000000960000000007e94a526898000000000000e800000000000000001e8728000001200012f09eb34c5944000000448dc1c4b0c000000000009a1fc392390000000e80016491d1208e56e93c1c0758a29052baa88000001428596d84a0000018da3319c20d631f24bec60e93062aebc4bb299000bad641710009e9288a23d0001368002f00000016c000348000bf610000001cb1088b800000000000000db5dc03d8b9625340012524511e0000013a00000018800000000000a848c0000e1500003980022836c1c4cb10751c0017100017418d2698c00
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x840c42e56210310ad99030c42b5640c310b998830c42e5620c310ad99020c42b56408310b598c20c42d563083109798c548425d63152109b988548426d62152108f990538423d6414e109b988538426d6214e108f990528423d6414a109798c528425d6314a10cd95341843345410610cd587544423e64951109dd85544427461151108f99454443376115110cd584544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524427665d0510cd15341442766590510cd15241442746550510cd15141443375410510cd150414427665cc510ad99331442b564cc510cd1533144334548c5109d1953144334544c510cd150314427665c8510ad99321442b564c8510cd153214433454885109d19521443345448510cd15021443345484110ad99254442f160951109d992544423664951109d58254443716095110bcd8154443355415110cd99054442b66515110cd99454443376315110cd98c54443356315110cd18c54443376215110cd98854443356215110cd18854443376015110cd580544433454d4d10ad99253442b56494d10cd15253442f16094d10add9153442b46454d10cd15153442e76254d10b918953442f36054d10cd150534433454d0d109d99643442756590d10cd15243442776550d109d19543443345450d10cd15043442f26010d10bc580434433454d4910ad99252442b56494910cd15252442f16094910add9152442b46454910cd15152442d76354910b518d52442f36054910cd150524433454d09109d99642442756590910cd152424427765509109d19542443345450910cd15042442f26010910bc580424433454cc910cd1523244277654c9109d1953244334544c9109d9943244275650c910ad99032442b5640c910cd15032443c5320c910bc98032442f1600c910cdd53504433454d4110dc99750443b354d4110ec153504433454d01109d996404433454901109dd9540442746550110cd15140442766510110cd15040442d66310110b558c40442e66210110b958840443b14010110cd1533044276658c110cd1523044334544c1109d99430442b6640c110ad5903044334540c110b998830442e5620c110f44c0304433454c81109d99620443345488110cd15120442766508110ad99020442b56408110cd15020442d66308110b558c20443e120081109d987540427761550109798c540425d63150109b988540426d62150109d984540427661d4c108f990530423d6414c109b988530426d6214c109d984530427661d48108f990520423d64148109798c520425d63148109d984520427664944109d597410427765104109d594410433654104109d586500427965840109dd9510042b464440109ed9510043725144010
  | 1 => 0xc2756115030cb952520c32d5494830cb951520c32d5454830cd952510c3355494430d994a510c36552944309d992510c3365454430cd551510c3665254430d9549510c27464544309dd97410c27565d0430cd953410c33554d0430d994b410c36552d04309dd94410c2756510430cd950410c3355410430d9948410c3655210430c7553300c34d52cc030da54a300c25f654c030c7551300c34d524c0309ed95300c369524c0309d98754c827561d53209dd8554c827461553209dd8553c82746154f208f99053c823d6414f209d98453c82756114f20d314d32c83365410720cd55041c83a542107209d987548827561d52209dd85548827461552209798c548825d63152209d984548827561152209d987538827561d4e208f990538823d6414e209d98453882756114e209d992518823f64546208f19151882b46454620cdd9151882746454620cd191518823464546209dd97418827565d06209dd9441882756510620cdd5041883345410620bc580418827661d51209d587544825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f59053482766114d209d584534826c6550920ba181424826c654c920d314d32483375410520cd15041483a54210520bc5804148278654c120f24c9304825e63d50209758f540827661d50209d587540823d6595020cdd86540833461950209dd8554082746155020cdd85540833461550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c20cd95251083355494420d594e510835553944209d99251083365454420cd55151083565354420d554d510827464544209dd97410827565d0420cd953410833554d0420d594f410835553d04209dd9441082756510420cd95041083355410420d594c41083555310420cb553200834d53c8020d654e200826f6548020cb551200834d53480209ed95200835953480208f99253c423d6494f108f99252c423d6494b10cd95041c43355410710ad99331c42b564cc710ad99321c42b564c8710bc58354c43355415310bc58054c43366415310dc58054c42f160d4f10ad99253c42b56494f10bc58053c433454d0f109d99643c42756590f109dd9543c42746550f10cd15143c42f160d4b10ad99252c42b56494b10bc58052c433454d0b109d99642c42756590b109dd9542c42746550b10cd15142c4277654cb109d19532c4276650cb109d59432c42b6640cb10ad59032c43c5320cb10bc98032c42f1600cb10cd95340c43345490310cd95140c43345410310b598c40c42d56310310b998
  | 2 => 0x6494a318f592528c7365410631ad993318c66e62951319b58a544c67761551319d997414c73454d0531b598f414c7365410531ad993314c67661d50319b988540c66d62150319e980540c67960150318f992530c63d6494c319d594410c7365410431cd550410c6d5631043197d95310c677654c431cdd8654c873761553218f99353c863d64d4f218f99053c863d6414f219e98053c86796014f21cd95341c87365410721cd55041c86b664cc721cd95331c8736540c7218f992538863d6494e21cd95041886b664c86219798e544865d63951219dd85544863e6494d218f59253486776154d219d997414873454d0521b998b414873654105219d9963148674654c521ad993214867661d50219798c540865d63150219e980540867960150218f990530863d6414c219d984530867a6014c219e580530863e64948218f59252086756510421cd95041087355410421b9588410867565cc421ad9933108675650c4219bd95210867765484219d98653d02756194f409dd8553d02746154f409d98652d02756194b409dd8552d02746154b40bc58341d02f16010740cd54441902b56510640cd59441903355310640cd54841902b56010640cdd0c51503354314540cdd08515033542145409d99741502766510540cd146405034e5394840d354e521034e5354840d354d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d9549511035653d0440d554f411036652d0440d954b41102f160d0440c754e411032d5290440ad98641103355190440c754c411032d5210440ae58041103565310440d554c41103665210440d954841102f16010440e594c41103355310440e554c41103155310440e994841103355210440e954841103255210440ec98041102b56010440ec58041102b16010440cd106501031d53d0040cb54b40103b041900408fd95401031d5350040cb54940102b461500409ed9540103b341500409d98754cc27561d53309dd8554cc27461553309dd8552cc2746154b30cd95041cc3355410730e550c41cc27661d52309d587548c27761552309d185548c26e62152309b588548c27661152309d584548c27664946308fd91518c23c6454630ad191518c33764546309d191518c33464546308d191518c27765d06309d597418c27765106309d594418c3375410630cd150418c2f160106309d987544c27561d51309bd89544c26c62551309dd85544c274615513097195434c2d86050d308f990524c23d64149309d984524c2756114930d3149324c3375410530cd150414c3954310530bc580414c26e62d50309b58b540c27661d50309d587540c23d6595030cdd86540c33461950309dd85540c2746155030cdd85540c33461550308f990540c25e63150309b988540c26d62150309d984540
  | 3 => 0x439d5865010e766194f429d58653d0ab46150f429d98650d0a756194342cdd0a5190a7560946429dd815190a7661942429d5865090b1c5350d42ab1894350ab46150d42ad9864250a7560d4542cdd0c5150b3543145429d5805150a5e63141429758c5050a7661141429d5845050a776154c429d1855310a3f65508429bd954210a7661940429d5865010a7661d53329d58754cca7761553329d18554cca7661943329d58650cca7661d52329d587548ca7761552329d185548ca7661942329d586508ca7661d51329d587544ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca3e64d45328f593514cab664d45329d993514cb3664d45328d993514cb3564d45329d583514ca7664145329d580514ca3e64141328f590504ca7661141329d584504ca7661d50329d587540ca7a60d50329e583540ca3d6595032cdd86540cb3461950329dd85540ca746155032cdd85540cb3461550328f990540ca7661150329d584540ca7a60150329e580540cacd638c83297d95320ca6f654c832b3d95320cb4f654c832e3951320cb8d544c832f1d85320cbc4614c832cd952510cb355494432f14ca510ca7664944329d582510cb365454432cd551510cbc532544329d191510ca7760544329d986500ca756194032ce952500cb395494032f24ca500cb725194032dc546500cb726194032dc586500cb4d3254032ce951500cb395454032f24c9500cb725154032dc545500cb5b3254032da8c9500cb593254032da4c9500cb493254032dc985500cb716154032b998b53d06e562d4f41d5d4e53d07954310f41b598f52d06d563d4b41d9d4a52d07a54210b419dd9532d0674654cb419d99432d0675650cb41ad99032d06b5640cb41f14c832d06f2600cb41bc58032d06d66314341b558c50d06e66214341b958850d071e5350e41cb94942906b76150c41add85421063f65504419dd9541107366495041ad58e54106b56295041ad98254107555314c41b998853106e56214c41bc98053106f16014c41e594f431079553d0c41ad58b43106b660d0c419d59643106b56490c419dd9543106b76550c41cdd9543107976350c41add8943106b46050c41ad99043106d66314841b558c52107655214841bc98052106f16014841ad58f42107a652d0841e954b42106b660d08419d59642106b564908419dd9542106b76550841cdd9542106b76350841e9d8942106b46050841ad99042106b664cc841ad59332106b6648c841ad5923210677654c8419d19532106b6644c841ad5913210676650c8419d59432106b6640c841ad59032107c5320c841bc98032106f1600c841cdd0d50107354354041cdd0950107354254041b598c50106d56314041b998850106e56214041cdd8654cc7376155331cd95341cc7365410731cd55041cc63e
  | 4 => 0x8208000000a8000001ee000000a354a2710d8c90005282f2a81da950d8b5462e1080024c00058468b1800016d631f72b052c000d75260018e000000d78f3afd2b84dd9c9090000000000049c7613da7c2588416622b57057c958a84c09c80134b52cb2d3a1a2210d34000002dc3201180006c000be2e359ebf01f9f000077964000000000c91590008a000000000d44b22e92ceba0d90d41787983f92122eaf553a0103a13cef9042d02201eae21585b0870d66088f48f8e12ec94563b3f0801dc089e82f25e12f2643a800d9a82d154000ed800000bc546000000000b7a5838089d9e2ff64ad6406a526dc5a995b49524a78b6911000128300a9000cf41a80026875c9f00001c19446910446001648680001e53c053000001340006b4d314a80023c6156a008000c41508515ce29d4894835a6380f0fe6cc000c99253dc001a72633c400115000648718a21d93920014c06b60cb5c9999762cb04f4aa25dc0a0ff83a32818c221ed3b80000015a00013585b0f2ac1605a0275068c03c2db0385d0aa23c000cd8001460006d84981953811524162580001532d05100019f0002c06a4f08166d20310f096302d11071516b613075b2120e08513132000378d32b600075461b074300012cabb148000450cf5ac0cd4cb500a4230391c35688c50417353ece11db2a468bb47c98f62a3f4622e408c71d672903847ac5b8ad22a61d9d0d34ac888810f85e00020000181900a00c00003020004040180000000580000001c0000605a0180080f036110118000040140a80d01a01000807004000010000000a8068030000d4008030240400200301a03c1100a010020040070000080c00c0100000000200009c0600d006014048010000100001c0020380786800200008008000040018080100680082e0020080501108608c0080001608c1802b0040c0000080100040080900600c0280500000c02806002000110000180880200b01e0480200200600400018004028078020020040581000c0800201c0000300100001c0000100301a038018000000240080800805c0300600002004005004070000030100180480501600003000010000008000100080000d000008000000000040402103801c010000040040000603003c0305c0040940c009004030000040020041e80000e00c1e000002044020110080541082601e0101d80708c000018000040000000201e05007802006024090010060440800200e0000000200001c0580b00c0200300a00c008000250020140000d0340380180100001400002000002766194b439d58652d0e7661943439d58650d0f3743946439d5825190e7760546439d9865090e756194243ad9864350e7560d45439d5805150e6e62141439b5885050e7661141439d5845050e3f6550c4397d954310e7761548439d1855210e766194
  | 5 => 0xa28798122b66b132ae02842780028e000000000ea35eb78002bf2e20005985d24c53c4b8e8040aac272ae48236d4299d5b206cf90d92700ad101243fc000002665f4c6451000000c44af095398aa48b1053507c43800043a0a4a61f842e55ccb36c13a669860145d881c9f830690334fe2974800e0c50894d872879000512cb924a112f4501b20005ca51cdf20c66e7cc002861620009822c61caf8000000d8d59690003f64e5312c339a24800000310c6d6fa21000000ba9e5000ad474800000000e89905d4000000e526c1b857a05000010000b80f48508d949000cb42e0591f8360680003de4d40017013e0006703e65e00150000000bcc0027e1408b8c10b90007a8df9d634ad8934b716280014dad3030660000000000003da7d45a630d71e3044c7d7b83b14a22c1b801306d54a9b02058b71a081f43e0412319c1deb85a3ab02502996c0f60fc474b595d0ec910da294564c256100738a1852d2c5562d49408c6246d1580b57174d705fad14c299ce221321ed7db3a4329cc4c85361516af0d00004dc6dd01800664971599b30009cc000002449b50d3232ee001378000000000036b0000d0590573780f1a5056348a8c898804746542d00b6ba3913a8001e000000184026418001503900006087c50e000a685f484000b48173f2000d0b205f28e00028234e62d1c8843323d000000000828002ad19638c0013a0aa8c93594146e0012ab6d18e9fc000000ea3c447b721569357d80045e00119800000a119da9d660000002f20004b89e97e1806019a1da072c0c000990008d47034f1d81b4000000000012988e00006800000000218322b900074c0a97d0923ec39b584049e96aa0436010c660dc2629c123b284e2bf8d19ce0de1994016533e618b1ac4400120410ff610aa817a192860287d1fa278ab0890623564652d9bb5cc1c4dd2500fa73c8a1e066266d7a16600a8242a20d6ca4a58f10d61a8f91231a3e8d4d521b816cdbca9000184add2b8002180c4000c53a40005700040c9140018d000b280020b5ec858002775d600073333202a34650000000006f9fd5ea0000480064e000858006e083d5780028a000000265b47d9829f51204a8738bd680a68801274f2da87132c4be2c0f22cd04ac896e91c01e3555d12d61411d0e09b2aa775093605f0c752799e10a2d4dc869106ca4dab006848d843b686860007709a2406444a17b1228945d9d0096d8c5f0004ba348979032e4c989db461424683a24a3124601206a05cc48338001028a5259ec47e140bfa6a064bbce0a8f1b4260de9aa1ba72d0a8061ea9d
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1b400523c800ec002100000240000000440d918e000000acfa7f00000de75000006481001049a66139f8004c2500000003d1410e000e1d00000000b08006218000058288f4e48e24064ae0000000005a06034008f358d06a261f001000000000405000006000102010003020d010104000000090000000302010a020401000901050000080206010000041803868e8b0ca19943474586508ca1a3a2c028a65619d3614c832868e8b04a219705544c9510ca1a3a2c3280654c1d16194032e14a8992a019709544c9500cba0994a2a8065d04c95154032e86e2992a019740714c9500cba0994c2a80654c1d16154032e8264b0aa01954672d4e53d06a339ea52968351dd5320cb41d8264b0065a0e45535885310728a9ac029883295c86050c41c8ac6a90a420e6152580521064ab98c0a10831c5c0654c841960e0b226420e45654c83210760992c0190834c1c14354041a60e0a12a020d2672d8654cc692b94a820a63459cf619532186ce9b0aa690d1573950414870ca9ac0208818a5496010440ca2a6b008220661525804110382a9ca420881c194d5210440e0aa6a908220711539804110390a94c0208818554d6010440c4aa4b008220711535804110390a92c0208812cdd56010440c66eab008220692535804110318a9ac020881a454d6010440c22a6b0082206a2525804110318a92c020881a85496010440c42a4b008220615531854010312a90c2a00812c9db415004086ce9b0aa59852572150418c3182a2c020c61325c86050d30a28eaa1882985907050c414c3182a2c020a61a450d601053086ce9b0aa79043474587538828ab98a820c418c1516010620992e630284905247550841482d03828420a418c1516010520d4284b008290648654c93048319322c02a6210d9d3654cb10d8264b0065884367695140c430a2a2c620621891516210310a2ae62a0830852572150418428b39ec22a221455cf6115110a4ce5b08a88852572d84544421a3aac998a210ddd854cc510868eab26428843776153214430ab18c62a221499c86315110a4ae4318a8885317018c544428b398c42a221455cc6215110c4ac4310a8885317018854443122a6c4a9a21891506254d10c60a9300868861454d8d524430a2a0c6a92218c152601091086ce9b2a648843474594324421a3aac8192210ddd8540c91086aec2a06488544754c832443822a264192218c152600c910c60a8b0064886c132580324430a2a4c620221851516310110c48a931080886245458840442983aa8020221a458d4010110d42c4a00808843776150304421abb0a81822189152620c110c48a8b106088691644c030443882a26018221b0589300c11086eec2a0408843576150204430a2a4c610221851516308110d42c89004088720544802044360b1a40102210d1d16194010
  | 1 => 0xe20032988dc2f1c958002242a091a001e04028451b000aa1a00000e6010000000000005cd46304024c01834950422544014a6000b00000000008c0e5e1700000133205400002e2309c37000c0d8610000000000000054380003c003b0e800b612058007e003b92c400e00000005f08964621e020000000418000668000011600001ecba001400000671d0286602149e00000420003e863e11c5a0027a24004900001140
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x6b00000007241023287a6898406aae00058e200b00480c8a520304000046040905859d3614c832b0284dc53254032940874c96154032d00744c96154032a43854c9600cb41921821c14354041911831c14254041e01539496010440e02535496010440e01535496010440a21821516010630981821c14310530a11831516010620981831c14210520c05635c86315110c11635c06315110c05735886215110c21625c06215110a0586151320c910e00544c9600c910c107558d4010110c20755894010110a1186151300c110e0054589300c110a21861512008110e005458d2008110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 802
  | 4 => 883
  | 3 => 144
  | 2 => 26
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
  | 6 => packedAt s4K6 (788+((h/14+packedAt s4K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s4K5 (24591+((h/267+packedAt s4K5 (21654+(h % 267)*11) 11) % 1280)*11) 11
  | 4 => packedAt s4K4 (36788+((h/294+packedAt s4K4 (33554+(h % 294)*11) 11) % 1060)*11) 11
  | 3 => packedAt s4K3 (7440+((h/48+packedAt s4K3 (7056+(h % 48)*8) 8) % 229)*9) 9
  | 2 => packedAt s4K2 (1608+((h/8+packedAt s4K2 (1560+(h % 8)*6) 6) % 35)*6) 6
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3fe1ffff07e3fff063c7f1fff8e0fffc11f0ff
  | 1 => 0xc1fe0f8ff803c78f83f8fe383f00e1c0eecccc
  | 2 => 0x1fff00ffffc07fffc00ffc03fff01ff0f0f0f
  | 3 => 0xfe00000ffffff80fffff00003ffffe03f00ff0
  | 5 => 0xfffffff00000000fffffffffc0000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x84242001104400000041104888202448005055
  | 1 => 0x9c4ce31231c98b1381c87211b9064c9866cccc
  | 2 => 0x2080452442809404a400a482124a01310b050a
  | 3 => 0x8190a48850201294a92000424949802b00aa0
  | 5 => 0x31118c00e613264e7324c92700181023dda000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36352
namespace PEqualNP.Outside.L_meta_36352
open PEqualNP.Outside.L_meta_36352.Model
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
end PEqualNP.Outside.L_meta_36352
namespace PEqualNP.Outside.L_meta_36352
open PEqualNP.Outside.L_meta_36352.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x17290230f2649013d3d86d386924c8111c267840635100000002280963eb5000121c76002696b400000800005458ac02e8c94500200289164e9a000109f0000a9c0018020a94800000000000091294141c000010000094001810022000003204108180005ff54015fd5005fe54017f550057d54017f15007ff5200ff94801fd5200ff14805ff4200ff90805fd4200ff10803fe32007f4c803fc3201ffd4401fe51007f54407fc51017fd0405fe41017f50405fc4100ffc8401fe21007f48403fc2101ffd4001fe50007f54007fc50017fd0005fe40017f50005fc4000ffc8001fe20007f48003fc20007fc4001f710007f84001fd10007d44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42005ff8821002ffa4108017fc208400bff8842005fdc4210027f62108003ff65440017fb2a2000dfd9510004feca88033fe65440077f32a2000ff59510005faca88033fc65440077e32a2000df1951001cf8ca8802fff64440177fb222000efd91100057ec88802ffe64440057f322200bff5911005dfac88802ffc64440057e322200bef1911001578c88802fff5444017bfaa2200bff9511005ffaa88802f7d5444017fe2a22000ffd8910005fec48802bfe62440037f3122000ff58910005fac48802bfc62440037e312200cffd4910057fca488003fd5244015fe292200bffd0910057fc848802ffd4244015fe212200aff8c910007fa648802bfc3244019ffa8a200cfdd4510027fca288003f65144001fea8a2000fd54510027f8a288033f45144017ffa0a200bfdd0510027fc828802ff64144017fea0a200bfd50510027f8828802ff44144015ff90a200afdc8510027fc4288003f62144001fe90a2000fd48510027f8428802bf42144019ffa822005ff94110007faa088017fc5044017ffa022005ff9011005ff4808802ffd4044017fca022005ff10110057fe4088017fe2044001fe9022005ff08110027fe2088013fb104400bff0822005fd84110007eeca88003776544019fb32a2000fd59510067e8ca88003746544017fbb222000edd911005fecc88802ff56444017fa322200bed1911005feea88802f775444017fb2a2200bfd5511005eeaa88802ff45444001fbb12200afd98910007eac48802bf46244019fba92200afd94910007eaa48802bf45244017fba12200afd9091005fea848802bf44244015fb1922000fd4c910057e86488003f76044001f9b02200cfdd411002feca088003f5504400bfa282200bfdd011002fec808802ff24044017faa02200bfc5011002fe8808802bf7204400bfb1022000fd4811002fe84088017ff650400b7fb282005ff9941001dfcca08017fd65040017eb282005ff1941002df8ca08017ff640400b7fb202005ff99010015fcc808017fd64040117eb202005ff1901002df8c808023ff5404011bfaa02008ff95010047faa8080237d5404011fe2a02005ffd881002dfec408017fe62040037f3102005ff58810005fac408017fc620400b7e3102009ffd481003ffca408003fd520400ffe2902008ffd081003ffc8408023fd420400ffe2102007ff8c810007fa640801ffc32040097f3082006bd98410027fea208013fe5104009fea882004ff14410027fe8208013fe4104009fea082004ff10410027fe4208013fe2104009fe9082004ff0841002dfcc008017ff500400bff2802005ff5401002ff8a008017ff400400bff2002005ff5001002ff88008017ff200400bff1002005ff4801002ff84008017ff100400bfb8802005ff8401002ff42008017fd100400bfa8802004fe44010
  | 1 => 0x3fe5148001fea8a4014ff1452009ffe829004ffe4148027fea0a4013ff10520097fe6290003fe3148001fe98a4012ff0c52000ffe4290007fe2148003fe90a4001ff0852000dfec090053ff504800bff2824000ff5412002ff8a09004fff404800bff2024013ff5012002ff8809004bff304800bff1824000fe8c120007fa6090003f9304800bfe1824001ffc812000ff64090017fe204800bf71024005ff0812002fd84090007f82048009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2000bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb262006bf59310027f8c988012fc64c400dffaa62006dfd5310037fca98801bfd54c400dbeaa62006ff15310027fec588012ff62c4009ff3162001bf98b10027fac588002fd62c4009fe3162004bf18b1008ffea588043fe52c4001fea962010ff14b10037fe8588043fe42c400dfea162010ff10b10087fc6588003fd32c4021fe1962004ffd471008feea388013fe51c4009fb28e2004ff54710007eaa388013fc51c4009fa28e2004ffd0710037ee8388013fe41c4009fb20e2004ff50710037ea8388013fc41c4009fa20e2004ffc8710087ee4388013fe21c4009fb10e2004ff48710007ea4388013fc21c4009fa10e2011ffd431002ffca188003fd50c400bfe2862006ffd031002ffc818801bfd40c400bfe2062010ffc831002ffc4188003fd20c400bfe1062004fdd971008feccb88003f565c4009fa32e2004fdd9310037ecc98801bf564c4009fa3262006fdd5310036eea98801bf654c400dfaaa62006dd55310037e8a988013f762c4021fb3162000fd58b10027e8c588047f752c4021fb2962000fd54b10087e8a58801bf742c4021fb2162006fd50b10087e88588043f632c4001fa9962010fd0cb1008feea188017f650c4001faa862005fd14310037ee8188017f640c400dfaa062005fd10310087ee4188017f620c4001fa9062005fd0831002ffecb08016ff658400bff32c2003bf9961002ffacb08002fd658400bfe32c2005bf1961002ffec908016ff648400bff3242002bf9921002ffac908036fd648400bfe3242005bf1921006ffea9080377f548401bff2a4200dff5521006efaa908037fc548400bffb142005bfd8a1002ffcc508006fe628400bfeb142000bf58a1002ff8c508016fc628401fffa94200eff94a10007faa50803bfc528401bffa14200eff90a1006ffa850803bfc428401dff1942000ff4ca10077f8650802efd61840177ab0c200fffd4610027fca308003fd5184009fe28c200dffd0610027fc8308037fd4184009fe20c200effc8610027fc4308003fd2184009fe10c2005bf9821002ffea108017fe508400bfea842005ff1421002ffe8108017fe408400bfd2042005ff5021006ff28108017fc408400bff9
  | 2 => 0x500d7fac8a806afd6454035fe322a002bf1915001ffea8a800f7f5454007ff2a2a003ff551500d6faa8a800ffc5454001ffb12a000bfd89500cffcc4a8006fe6254001feb12a019ff1895000df8c4a800fff5254007bfa92a003ff9495001ffaa4a80037d5254007fe292a01affd09500cffc84a806bfd4254033fe212a019ff8c950007fa64a8067fc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa004bf1855001ffea2a800ffe5154007fea8aa003ff145500d7fe82a806bfe4154035fea0aa01aff105500cffe42a8003fe2154001fe90aa019ff0855001dfec0a800fff5054007fda82a005ff9415002efca0a8017fc505400bbe282a003fe141500d7fe80a8017fe4054035fea02a005ff101500cffe40a8017fc205400bffb2c4005bfd962002ffccb1000efe658800bfeb2c4000bf5962002ff8cb10016fc658800bffb244005bfd922002ffcc91000afe648800bfeb244017bf5922002ff8c910016fc648802fffaa44017dfd52200bffca91005ffd548802fbeaa44017ff1522002ffec710016ff638800bff31c4015bf98e2002ffac710002fd638800bfe31c4005bf18e200c7fea71005bfe5388001fea9c4016ff14e200bffe871005bfe438802ffea1c4016ff10e2000dfac510007ff5288003ff2944001ff54a2000ff8a510007ff4288003ff2144001ff50a2000ff88510007ff3288003ff1944001ff4ca2000ff86510017ff618800bff30c4004bf9862002fecc310002f6618800bfeb0c4000bf5862002feac310002f5618800bfe30c4018ffd4620007fca310003fd5188031fe28c4017ffd06200bffc831005ffd418802ffe20c4016ffcc620007fc6310003fd318802dfe18c4001ffc862000ffc4310007fd2188003fe10c4005bf9822002ffea110017fe508800bfea844005ff1422002ffe8110017fe408800bfea044005ff1022002ffe6110017fe308800bfd1844005ff0c22002ffe4110017ef2088003fd9044005ff0822002ff04110003ff65480017fb2a4014ff9952001dfcca90003fd65480017eb2a4014ff1952001df8ca9004fff64480277fb224013ff99120015fcc89004ffd64480277eb224013ff19120015f8c89004fff5448027bfaa24013ff9512009ffaa89004f7d5448027fe2a24000ffd8d20005fec69004bfe634802b7f31a4000ff58d20005fac69004bfc634802b7e31a4014ffd4d20097fca690003fd5348025fe29a4013ffd0d20097fc869004ffd4348025fe21a4005bfd892000ffea490007fe5248003f72924001ff54920007daa490007fc5248003ffa124001ff9092000fdc8490007fd4248027f6a124001ff1092000ffe6490007fe3248003f71924001ff4c920007da6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4004bf185200a7fea29000
  | 3 => 0xe31c4204bf18e21117fea710883fe5388401fea9c4220ff14e2110ffe8710883fe4388443fea1c4220ff10e2100dfac510807ff5288403ff2944201ff54a2100ff8a510807ff4288403ff2144201ff50a2100ff88510807ff3288403ff1944201ff4ca2100ff86510812fe6188409ffa8c4204ff94621027faa310813fc5188409ffa0c4204ff90621027fa8310813fc4188409ff98c4204ff8c621027ec6310813fc3188409ff90c4204fbc862100fee4310813fc2188409fa10c4204ffd8221027fcc110816fe6088409feb044200bf58221027f8c11088bff5088445fe2844221ffd022110ffc8110887fd4088443fe2044220ffcc221107f86110807ff2088403fe1044200ffd9521005feca9087ffe65484077f32a4200ff59521005faca9087ffc65484077e32a421effd91210f5fec89087bfe64484057f322421eff591210f5fac89087bfc64484057e322421effd51210f6fea89087bfe544843dfeaa2421edf551210f7f8a890803ff63484017fb1a421dff98d210adfcc690803fd63484017eb1a421dff18d210adf8c69087fff534843bff29a4200ff54d210eff8a69087bff434843bff21a421eff50d210eff88690812ff6248403ffa924201ff9492100ffaa490807fc5248403ffa124201ff9092100fdc8490807fd424843df6a124201ff1092100ffe6490807fe3248403fe9924201ff0c92100dfec29087fff5148409ff28a4200ff54521027f8a29087bff4148409ff20a421eff50521027f88290877ff3148409ff18a4200fd8c521007fa6290803f53148409fe18a4201ffc852100fee4290813fe2148409f710a4204ff08521027d84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024205bf181210fffea09087ffc504843dffa02421eff901210f7fa809087bfc404843bff982421dff0c12100ffe4090807fc20484077eb2ca005ffd925002dfec928017fe64940057f324a005ff592500e5fac928017fc649400b7e324a003ffd525001efea92800ffe5494007feaa4a01cdf5525001ff8a928017ff629400bff314a001bf98a5002ffac528002fd629400bfe314a005bf18a5001ffea52800ffe5294007fea94a003ff14a500e7fe852806ffe4294039fea14a01bff10a500dffc6528003fd3294037fe194a005ffd865002ffcc328012fe619400bfb30ca000bd9865002ffac328002fd619400bfab0ca000bd5865002ff8c32800fff5194007ff28ca000df9465001ffaa32800ffc5194007be28ca01cffd06500e7fc8328073fd4194039fe20ca01bffc8650007fc4328003fd2194037fe10ca005bf9825002ffea1280177f5094007fda84a005ff1425002ff0a128017ff409400bff204a005ff5025002ff88128017ff209400bfe104a005bfd95500d7fec8a806aff6454035ff322a002bf991
  | 4 => 0xa7ff3054853fe182a401ffc815200fde40a9007fc2054801ffb2a6400bfd9532147fcca9900efe654c801feb2a6400bf59532147f8ca9900efc654c84fffb226427bfd913213ffcc89900afe644c84ffeb226427bf5913213ff8c89900afc644c84fffaa26427dfd513213ffca89909ffd544c84fbeaa26427ff1513200dfec499007ff524c803ff2926401ff5493200ff8a499007ff424c803ff2126401ff5093200ff88499007fe324c803ef1926401ff0c93200fd86499007cc324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6404bf18532147fea2990a3fc514c84fffa0a6427ff9053213ffa829909ffc414c803ff90a6401ff08532007fec099002ff604c801ff3026400ff58132007f8c099016fc604c851ffa826428ff1413213ffe809909ffe404c84ffea026427ff1013200ffe4099007ef204c803fe1026403bf59651027fec928812ff6494409ff324a202bf99251027fac92889afd6494409fe324a204bf1925101ffea92880f7f5494407ff2a4a203ff55251136faa92880ffc5494409ffb14a204ff98a5100dfcc528813fd62944017eb14a204ff18a51025f8c52880fff5294407bfa94a203ff94a5101ffaa5288037d5294407fe294a226ffd0a5112ffc852889bfd429444bfe214a225ff8ca51007fa6528897fc32944097f30ca204ffd4651026fea32880ff75194409fe28ca204fd14651027fe8328813fe4194409fea0ca204ff10651027fe4328813fc2194409ffb04a204ff9825102dfcc128813fd60944017eb04a204ff1825101ffea12880ffc5094407be284a226ffd0251137fc812889bfd409444dfe204a225ffc825112ff84128812ff6554449ffb22a224bfd9151127fcc8a880afe6454449feb22a224bf59151127f8c8a880afc6454407ffaa2a203dfd515101ffca8a880ffd5454449beaa2a203ff15151007fec4a8802ff6254447ff312a201bf98951007fac4a888ffc62544037e312a203ffd495101ffca4a880ffd5254407fe292a224ffd095111ffc84a8893fd4254447fe212a223ff8c951007fa64a888ffc32544077fb0aa203ffd455101feea2a8813fe5154409bf28aa204ff14551026f8a2a880ff45154449ffa0aa204ff90551127fa82a8813fc4154447ff90aa204ff08551007fec0a8802ff6054401ff302a200ff58151007f8c0a8816fc6054407ffa82a203ff14151127fe80a8893fe4054449fea02a224ff1015111ffe40a888ffc2054409ffb2c4204bfd9621027fccb1080efe6588409feb2c4200bf59621027f8cb10812fc6588409ffb244204bfd9221027fcc91080afe6488409feb244221bf59221027f8c910812fc6488443ffaa44221dfd522110ffca910887fd5488443beaa44221ff15221027fec710812ff6388409ff31c4215bf98e21027fac710802fd6388409f
  | 5 => 0x300300000000100000000100000200000500000100000700000300000000300200200000500300100100600000000000000001600200100100c00300201000000a00000000200000200000a00000400100100100300000500000000300000500100000c00000000000201000000000500200200000100000b00000000000600000000200200100000a00100c00000300200200000200000100400400100500300000000100b00300000801700900500200400500000000000000800400200000000100800000000000000101f00000000000000a00000000200000000500000100000000400300300000400800000100700800500500700500700200700300100000b00000a00100500000200300000200100400000000300000500000000200000c00c00101500100200000a00200100200b00200200100100100000700a00100400000200700400100100000300200100100200b00000101000100800100000000500200100600700000200200100300100000500000600300000200000000100300000d00300900100400300400400000200900600200200000000000000500200100100100300600000000400800200200100200300100000400000100100100200300600100500000800300100100600200b00200500100300800300000600000901d00300400900c00301400000400100f00b00000900f00000000a00001100300100000002900500200000000100001200100200000700000600400000700300400100500000000000100000600600d00100e00100000300000200200300000200100000100700200100100300300000100400100000100000600100000200000400700c00100000100400500100000000000a00000c01400000000100000000100000000100000100000101900200100200e00200002600800dfecaa90abff64548557fb22a42aff99152015fcc8a90abfd64548557eb22a42aff19152015f8c8a900fff5454807bfaa2a403ff9515201ffaa8a90ab7d5454807fe2a2a400ffd8d52005fec6a90a7fe635482b7f31aa400ff58d5214ff8c6a9056fc6354807ffa9aa403dfd4d5201ffca6a900ffd5354801bea9aa403ff14d52157fe86a90a7fe4354855fea1aa429ff10d5200dfec4a9007ff5254807f7a92a401ff9495200efca4a9007fc5254803be292a401fb1495200ffe84a9007fe4254803fea12a401ff1095200ffe64a9007fe3254803fe192a400ffd8552005fec2a9003fe6154801feb0aa400ff18552025f8c2a900fff5154807fe28aa403df14552157fe82a90abfe4154855fea0aa42aff1055214ffe62a90a7fc3154803ff90aa401ff08552007fec0a9002ff6054801ff302a400ff58152007f8c0a9016fc6054807ffa82a403dfd415201ff8a0a90abff4054855ff202a42aff50152157f880a9
  | 6 => 0x5e649042600010e8aa4c60001fd00049e0ae8c884415617c61a4d188c5e855c44218434290e85a37862e4280aa70a06061c2065c27ed2097654c20008be28a13e6cc00000049c71a48c80a2f289072734190a0d26124406b20001b96140009360000008245870000006d483c0e05a879f0000005880000005cc0000b212286b0000000000002681106e000000015f0bf39e19a0007fc12e4ee0000008160000008c20000002aa0003a000009d0000002242a008c2d029200025f2f18f200026000000046c00039235852242703e0007140005c03aa39434325a1fe49600078a00025c76600038666016a2f600000038a8b200000000075059783a2f50003882481d200038c00016b0b400000077e0001f54d50000001f62224940000a400000000000012a3460001025242c000018c0000445e40de0c043e1f00e20005c41f21694d75d26080007120340004366d056882a00072c00074413c2df6f41bc0000fa5a626e00030232c6c876f00000069c7bd52000043c53b31a0007342e011a6d859e0000006f208079c1623265b20007aa70e4ae0001208b46c091e0000000000000000a60003ba0000000006c212c0000000c90008dc00077b66e6002fa01418800000000068200024e24005d2ce32e1260003e40006164ac05100000047a05f00000033074234c4ff1657ba3516503720180000000002ef0004620004243d820a00027000000000043a00061877f52c84a8d474c0000000004144780000558027f879a1b40001c61e40004b20000003c853412800093e0000000005530000007322be0983be0e64100000002fe0666640cf0000005383000000000000000004e45193cc00036a0006b91a82934b084600027800000025d0f800067a00000055080428869a63c8e20007bf05200016e6880b046a25e6b600038e3ea1dc8cc31428e00000014a0003de00000000017e0004060000006483900006720000000000005b81f38008560000000000004c00003f427200064e59a0002160008585ac0e493a00052e0007b61240000000500001f400000000084000000000089e5c80008d891c8a003653626d14c6ae0cd5082960000001364d30000580000000000000000000000002320004c80000005570533b89062ad63e00000051b49245a7df6c400010a3750006fa8a80000000425ae00081e81c0000000004c40000006c643200000027420355900075800000027600000056200090c77701351273a0f418237e84c0000008502418650000000003ca5aa00077c00000010641c8227d205a0002f933a32a6943f00004fd40c5dc82e47400000015942a5f200000014800010c00300100300100000000100200100000500200200700000700800200000c00000200100200000700000000300200100400500a00200000000400000000000300
  | 7 => 0x3f600000068600000000000000092e0006ac0001b092847c0000000000000000000d46e400088400000073e5722561d87ee1a40000001b653c0977e20002d80000000007740005e20000000005060004f035400058f03c5409386e30002f00000005ee00000091800000000087665e81000092a4d030e0920000002b24fb1ce8de8c66a03f840e4340000004864fc8d07f488e5931788946a20000007e020800035c2da0000000004f60617410004f80000000002c47c69266c10008180003e260c8924180005da7ec0008780004847b24b80003d623a11609a0001d600012700078c83b8540000000ce00042c11d7e317a68c5990000000002f40560007f18740000008573c659002b00012b0000002137eb0000000000001ea0680000006102980220000004370000004f20000009044540000007f700048a3b517619c0000000000000760000f26020002e72d645601e2ff00000000000079200078600000000000029c00000058e00000032286e00000000000077337619600000000092056000000086331816c44a2eb3890005964b40000002820008983244e24be04d1e80002c20006b723e16d7e68b60da72269e2581570151038da3f25917885c600023019e0000004487bc4762f866284e7db8b05be74364433600000063438474e7dc0000000000000004150000000ac36c5ce4820000000000000001252e88080007847d60000007d84da0000dc00000020f0000001ee00000c0000006ba0001461294886380007a24801641de0005a264616f0000000000740000000004000004f904e0000000002461be00051e0000000002e60d80ee8f87f02650002fc6390000004fa00005c0380002753380008142c824a00028c5925153ee7673730000006be59c55222a3b00002ee6240000008ba1ba3e84460000004ec6b000034802a0d08125898ae61386a26900059f58a3822e98307b001a00020c0d10006680301fb8b800000000058415e0c19140993b405773c5867361c000000000050d77229712344400062200000000069279e7a875490253e5301187b407a82800060400000693c1ff0004220000000000008a400067c26600062a0000000000000007763a800000000000031e1141660006de00a0000cc00017020739c86151c5176361440006ec93268481f7063c402e08400000001044c4b51800000000000000000007f90007c22ea0000fc0000000000001fc0001556e210726442500000000800056e00000000000000023439a2ac2c62e11a22106e892c6098ec7d934076e0007fe26c0242e200000000022c56600000036e54408e8d248e7da00032853a3a60000002dc0000005b62675322de0000000000001fa0000000006ce59b0005980000657908621210fe73029a1e03b20c824587a41200002c7f6626202000852000
  | 8 => 0xc43821c7705111a607833c6fe58b26f7ca1d93ce8380000005745ba8a600015c85f76b0005f80009305148600000c20000000000ea08a04953d00000000011e13800006c0000ca21850a2715d875a4d460a15300085c00004a0000001544356a822623c66f7a60002632ec2437c082000070014e00044e0002b13fa6700c580c7e915000000033e3ae6aa00042e0002a600000000088600030c4b10000001088e000000000000000000000009b7e50000000006fc20d0000000000002a25b01f958c0000000000000001b70000000000000000000590000003160000000000002d256489c0008ac76c7160003fc0000000005f60f60000005160000007be3fe3746280004aa00074007e0002e38960007fb0007633563bc40a46e7605427642286905542994e68d606a91a6dc0008260007c85045703650c655a1e675e00081a77a4a80000008320007ae00f5950000000005d400005b11c6424728ca0000007943e67282fd1421120001000000bd0be0006a60000007046f60000000002e43200008e667482c26a4f40004a257e81d0b82af00038054a3a29240ba0006300000004dc0007ea0000006b818e2543a48e883e00009e30a3620000000005ca5583c000045e00000007c0000003524a085b0000002cc00000000000000025000013283400088087220085d0120002051d52860002fb00000000000000034e00054e88864085e0001cc2b05184b67fa0297f515189a5f45011741985a33ec29e4024e83e026191261e45c3c21d072e1527242bc0000001c80000000006660000002ed3ac6582470006200004304ba00078e0000005fb0006d20000000004640000001a00000000007f234460670868e0005070001925561ae47009671886d7d01400901f70a80003127e492200000000000000000000000068a0000003eb8fe1bb8a200057a74650e80e0000001610000000000000000005d00004040005fe2b82940700000000000000007ef2622800007d476163a17120478239600000000087000027300051a5025281306da7759162ca3d43980001b27627c481b0000000000204ea00000000000000017257602d0006800001c20003702a85bc00000000007264c00010121e0bb1f87380000000000d62ae8f60ec1aa00002f31c4605a056c24c0005f01e20bc5002ba3dc0000004de00058035a00008626b65c87c34a93400041a06e3688c42b40624680007a000077150c5135f95104583b60000007100f00000000000007021d45a57e16ca0000000004507cc6bc1c45d65034520007a42841da00000000052a6b45820007e74082206f020169659d66c50b0671048397800cb55e00041375216800000004f67870c0000000000002b647e86f7782420005ea00000001111f7250000000000000000000000000000d335e5ec71e1ec0000
  | 9 => 0x4b775c8f02140000000008690883da0007480006e671c0006d60641b58f430600000000000000000000005400015d00000000000000000000000035300019083600000000000000058d0000008825de2440008bc20e0280000002a40b633200000004b0004a66980000002b500006986604c6f81340004fe00030857c64a4208ee3342ab00031067e8fa5260a037c04688a7267792b90488ce00060b0007e815a0400000000008fc4a43604e000065400076901660e7561b890800408256a4665b418a79630465a00000000072a0007ac4bc72186441616700000049a0000000001d377d2f30264d209c54c8420000000002909104d879815886c5fa76d0000000000c30000004731940005a16560000004ce50900000013a41e49850f8670a200000066a2955fc2122361602f700000000054627c0007dd0000006760c72e56ee0940000007ce5056527b80000636a415b22e0000e80007a13d062c0000004511864ca76a00023800000059400025200000055500000000000000000003a00e01c6ea2b30000004d610516337a00000000021a2b700057827e35005e0000003642115a43870000000000003d28c02d400087e0000c40000005485e09007680000008ea1ac0000000021ca20b6327203668483637f30001d727a0007de74a8060000000008680320000008e44c
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x54d8110027f372d8110027f272d8110027f172d8110027f072d8110007f362d8110187f262d8110007f162d8110187f062d8110197f352d8110187f252d8110007f152d8110187f052d811018ff342d8110187f242d811018ff142d8110187f042d8110187f232d8110007f132d8110187f032d8110065f77654110025f67654110065f57654110065f4765411002df7755411000777655411006774655411017df7745411005df6745411017df5745411005df47454110007b76454110177b46454110067775454110177755454110005f77254110055f67254110055f4725411006777525411000775525411002df7705411002ef76054110007f36054110067f3505411002f76505411002f74505411002ff0505411002f70505411002ff24054110177f1405411002ff22054110055f77648110025f67648110055f57648110055f47648110005f77548110065f67548110005f57548110065f4754811000777654811000774654811016df7744811005df6744811016df5744811005df47448110007b7644811015fb4644811015f77544811015f755448110005f77348110165f67348110005f57348110165f4734811002df77248110007e76248110057e46248110057e65248110007e55248110057e6424811015fe54248110057e63248110007e5324811002df7704811002ef76048110007f3604811002ff25048110007f1504811002ff2404811015ff1404811002ff23048110007f13048110057f3204811002fe6204811002fe4204811002ff0204811002fe0204811002cff755941002e7f7559410004ff7459410014fe7459410004fd7459410014fc745941004e7f54594100067d5459410004ff725941000cfe725941000cfc725941004e7f5259410024ff7159410024fe7159410024fd7159410024fc71594100267e51594100267c515941002cff705941002cfe705941002cfd705941002cfc705941002e7e505941002e7c505941002ef7105941002ef51059410004ff755881001cfe755881001cfc7558810004ff7458810014fe7458810004fd7458810014fc74588100067f54588100067d5458810004ff73588100acfe73588100acfc735881002cff725881002eef725881003eee525881003eee4258810006ed425881003eee3258810024ff7158810024fe7158810024fd7158810024fc7158810026ee2158810026ec215881002cff705881002cfe705881002cfd705881002cfc705881002eee205881002eec205881002ef7105881002ef51058810004ff765481002cfe7654810004fd765481002cfc765481001e7e65548100067d655481000eee6254810006ed6254810086f66154810004ff764c81002cfe764c810004fd764c81002cfc764c81000eee624c810006ed624c81003fcc324c810086f6614c810
  | 1 => 0x8910065f47558910007747558910065747558910007776558910007746558910005f77458910007b77458910005b7745891005df67458910005f5745891005df47458910007b4745891005db47458910007b76458910007b46458910007775458910007755458910005f77358910007d77358910005d77358910165f67358910165f47358910007d47358910165d47358910006f76358910006f56358910055f77258910007e76258910056f66258910056f46258910057e46258910057e64258910007e54258910005f77058910007f37058910005f37058910007f24058910007f14058910005f77654910005f67654910005f57654910005f47654910055f775549100077765549100677465549101bdf7745491005df674549101bdf5745491005df47454910007b764549101b7b464549100677754549101b7755454910005f77354910165f67354910165f47354910067775354910007755354910055f77254910067e75254910057765254910057745254910057e45254910005f7705491002df6705491002df470549100677750549101b7f240549101b7f14054910057e72054910005f7764c910005f6764c910005f5764c910005f4764c910005f7754c910065f6754c910005f5754c910065f4754c91000777654c91000774654c9101adf7744c91005df6744c9101adf5744c91005df4744c910007b7644c9101a7b4644c9101a777544c9101a775544c910055f7724c910057d6324c910057e4324c910057c4324c910005f7704c91002df6704c91002df4704c9101a7f2404c9101a7f1404c910057e7204c910065f675d8110005f575d8110025f475d8110006f765d81100077765d81100067765d811008ef665d8110006f565d811008ef465d81100077465d811008e7465d8110025f774d811005df674d811019df574d8110025f474d811018ef764d8110007b764d8110006b764d8110036f664d811018ef564d8110036f464d811018fb464d8110036b464d811018f7754d811018f7554d8110055f672d8110005f572d8110025f472d8110006f762d8110086f662d8110006f562d8110086f462d8110197f350d811002ff250d811002ff050d811018ff340d811002ff240d811018ff140d811002ff040d8110187f320d811002ff220d811002ff020d811002ff276d811002df276d811002ef276d8110027f375d8110027f275d8110027f175d8110027f075d8110007f365d81100077365d8110197f265d8110007f165d8110197f065d81100077065d8110027f374d8110025f374d8110027f274d8110027f174d811019df174d8110027f074d811018ff364d8110007b364d811018ff264d811018ff164d811018ff064d811018fb064d811018ff354d811018f7354d811018ff254d811018ff154d811018f7154d811018ff
  | 2 => 0x57774d95100077674d95100077574d95100057574d95100077474d95100077764d95100077664d95100077564d95100077464d95100073464d95100077772d95100077672d95100077572d95100077472d95100077662d95100077462d95100077742d95100077642d95100077542d95100077442d95100077632d95100077432d95100077770d95101d77670d95100077570d95101d77470d95100077740d95101d77640d95100077240d95100077540d95100077140d95101d77440d95100077720d95101d77620d95101d77420d9510065f77559510007776559510066f66559510066f46559510067746559510005f77459510007b77459510005b7745951005df67459510005f5745951005df47459510007b4745951005db47459510007b46459510067775459510007755459510005f77259510055f67259510055f47259510005f77059510007f37059510005f37059510007f24059510007f140595100677676195100057676195100667676195100677774195100657774195100677674195100677574195100057574195100677474195100077764195100077664195100067664195100077564195100077464195100067464195100073464195100063464195100677772195100677672195100677572195100677472195100077662195100077462195100077742195100077642195100077542195100077442195100077632195100077432195100677770195101cf7670195100677570195101cf7470195100077740195101cf7640195100077240195100077540195100077140195101cf7440195100077720195101cf7620195101cf74201951005fb676d911005db676d911005eb676d9110007b775d91100073775d9110007b675d9110007b575d9110007b475d91100073475d9110007b765d91100073765d9110007b665d9110007b565d9110007b465d91100073465d9110007b772d9110007b672d9110007b572d9110007b472d9110007b662d9110007b462d9110007b752d9110007b652d9110007b452d9110007b632d9110007b432d9110007b770d9110007b370d91101c7b670d911005fb570d91101c7b470d911005fb070d9110007b750d91101c7b650d91101c7b450d9110007b720d91101c7b620d91101c7b420d9110055f676d8910065f675d8910005f575d8910065f475d89100077765d89100077465d8910005f774d891005df674d8910005f574d891005df474d8910007b764d8910007b464d89100077754d89100077554d8910165f673d8910005f573d8910165f473d8910006f763d8910056f662d8910057e662d8910056f462d8910007e732d8910057e432d891002df670d8910055f570d8910007f240d8910007f140d8910057e720d8910005f77558910007777558910005777558910065f6755
  | 3 => 0x47094510026f76094510027f360945101d77650945101d774509451020ff2409451020ff1409451002cfc76545100067f655451001e7c6554510006bf6454510126bc6454510065f77154510005fb705451002df8705451002df4765451001ef4765451002cf47654510025f7755451002777755451000777655451001ef6655451001ef46554510067746554510205f7745451005df67454510205f5745451005df47454510007b764545101ffb464545100677754545101ff755454510005f77254510055f67254510055f47254510007f3705451002df6705451002df47054510007f07054510026f76054510027f360545101fff240545101fff14054510005f67688510026f67688510025f77588510065f67588510005f57588510025f47588510007776588510007746588510025f7748851005df674885101f5f57488510025f47488510007b764885101efb464885101ef7754885101ef755488510025f77388510165f67388510005f57388510025f47388510006f76388510006f56388510055f5728851000ef6628851000ef4628851002df6708851002df47088510026f76088510027f360885101eff240885101eff1408851002cfc76485100067f65485100fe7c6548510006bf64485100f6bc6448510006ef624851000eec6248510055f77148510005fb704851002df8704851002df4764851000ef4764851002cf47648510005f77548510065f67548510005f57548510065f475485100077765485100077465485101e5f7744851005df674485101e5f5744851005df47448510007b764485101dfb464485101df7754485101df755448510005f77348510165f67348510005f57348510165f47348510006f76348510006f56348510025f77248510027e77248510007e7624851000ef6624851000ef46248510057e46248510057e642485101dfe54248510007f3704851002df6704851002df47048510007f07048510026f76048510027f360485101dff240485101dff1404851001cff7654110064fd7654110024fc76541100067f655411001e7c6554110006bf64541100d6bc6454110005f77154110025f4715411002f78505411000cff7648110054fd7648110024fc76481100067f65481100a67c6548110006bf644811009ebc6448110006ef624811000eec6248110005f77148110025f4714811002fe82048110065f676d9510066f665d95100677665d9510066f465d9510005f774d951005df674d9510005f574d951005df474d9510007b464d95100677754d95100077654d95100077554d95100677454d9510055f672d9510005f572d9510055f472d95100677752d95100077652d95100677452d951002df670d9510065f570d95100677750d9510007f240d9510007f140d95100657676d95100077774d9510
  | 4 => 0x911021fbb10d91101c7b610d91101c7b410d911021fb810d9110006bf75d91100063f75d9110006be75d9110006bd75d9110006bc75d91100063c75d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bc52d9110006be32d9110006bc32d91101c6bf71d911021ebe71d911005eb671d911005ebd71d911005eb571d911021ebc71d9110006bf51d911021ebe51d911021ebc51d9110006bf21d911021ebe21d911021ebc21d911021ebf70d91101c6be70d911005ebd70d91101c6bc70d9110006bf50d91101c6be50d91101c6bc50d9110006bf20d91101c6be20d91101c6bc20d911021ebf10d91101c6be10d911005ebd10d911005eb510d91101c6bc10d911000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910056ee62d8910025f671d891002df571d8910057e721d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d89100067f54d89100067d54d89100acfe73d8910004fd73d89100acfc73d8910006ef32d8910056ec32d8910024fe71d891002cfd71d8910056f571d891002cf571d8910024fc71d8910056ef21d8910056f721d8910056f421d891002cfe70d8910024fd70d891002cfc70d8910056ef20d89100057f75589100657c75589100067f65589100067c6558910005bf745891005dbc7458910006bf6458910006bc6458910005df7358910165dc7358910056ec6258910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc74589100067f54589100067d5458910004ff7358910006df7358910004df73589100acfe73589100acfc7358910006dc73589100acdc7358910054ff7258910006ef7258910056ee4258910006ed4258910074ff7158910006f77158910056f72158910056f42158910084ff7058910006fb7058910004ff7654910004fe7654910004fd7654910004fc76549100067f655491001e7c6554910006bf6454910156bc6454910005f77154910025f47154910067745154910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101467c654c910006bf644c91013ebc644c910057cc324c910005f7714c910025f4714c910005f67694510026f67694510065f5759451000777659451001ef6659451001ef4659451006774659451001e746594510025f7749451005df67494510215f57494510025f47494510007b7649451020fb4649451006777549451020f755494510055f67294510005f57294510025f4729451006777529451000775529451002df6709451002df
  | 5 => 0x67e54d95100067d54d95100667c54d951000cfe72d9510004fd72d951000cfc72d95100667f52d95100067e52d95100667c52d9510024fe71d951002cfd71d9510066f571d951002cf571d9510024fc71d95100667f51d9510066f751d9510066f451d951002cfe70d9510024fd70d951002cfc70d95100667f50d95100657e76d951001c7e76d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067e62d95100067c62d95101d77771d95100677671d95100077571d95100077741d95100077641d95100077541d95100077441d95100077721d95100077421d95100077a40d95100077940d951022f7b10d95101d77610d95101d77410d951022f7810d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067e32d95100067c32d95101d67f71d951022e7e71d95100667671d95100067d71d95100067571d951022e7c71d95100067f41d951022e7e41d95100067d41d951022e7c41d95100067f21d951022e7e21d951022e7c21d951022e7f70d95101d67e70d95100067d70d95101d67c70d95100067f40d95101d67e40d95100067d40d95101d67c40d95100067f20d95101d67e20d95101d67c20d951022e7f10d95101d67e10d95101d67c10d95100667c6559510005bf745951005dbc7459510006bc6459510064ff75595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510004fd7459510014fc7459510006bc7459510014bc74595100667f54595100067d5459510004ff725951000cfe725951000cfc725951007cff7159510006f77159510066f75159510066f4515951008cff7059510006fb70595100057e76195100667e76195100047e76195100657f74195100057d74195100067f64195100067e64195100067d64195100067c64195100073c64195100063c64195100067e62195100067c62195101cf7771195100677571195100677471195101ce7f61195100077741195100077641195100077541195100077441195100077721195100077421195102267f60195100077a40195100077940195102277b10195101cf7610195101cf74101951022778101951005dbe76d911005ebe76d9110014be76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be62d9110006bc62d91101c7b771d911005fb671d911005fb571d911005fb471d9110007b751d9110007b451d9110007b721d9110007b421d911021fbb70d911005fb870d
  | 6 => 0x75354b10007755354b10085f77254b1008fe75254b10087765254b10087745254b10087e45254b10005f77054b1002df67054b1002df47054b1008f775054b10087e72054b10005f7764cb10025f6764cb10005f5764cb10025f4764cb10005f7754cb1008df6754cb10005f5754cb1008df4754cb10265f7744cb10035f6744cb10265f5744cb10035f4744cb1025f77544cb1025f75544cb10085f7724cb10087d6324cb10087e4324cb10087c4324cb10005f7704cb1002df6704cb1002df4704cb10087e7204cb1008df77654310025f67654310025f4765431002df7755431008f766554310007756554310255f77454310035f67454310255f57454310035f4745431008f77545431024f755454310005f77254310085f67254310085f4725431008f77525431000775525431002df7705431002ef5605431008ff3505431002f76505431002f74505431002ff05054310085f77648310025f67648310025f47648310005f7754831008df67548310005f5754831008df47548310245f77448310035f67448310245f57448310035f47448310237775448310237755448310005f7734831023df67348310005f5734831023df4734831002df77248310087e66248310007e56248310087e65248310007e55248310087e64248310237e54248310087e63248310007e5324831002df7704831002ef5604831002ff23048310007f13048310087f3204831002fe6204831002fe4204831002ff0204831002e7f7559610004ff7459610014fe7459610004fd7459610014fc745961007e7f54596100067d5459610004ff725961000cfe725961000cfc725961007e7f525961007e7f515961002cfc705961002e7e505961002e7c505961002ef7105961002ef51059610004ff7558a1001cfe7558a1001cfc7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a100067f5458a100067d5458a10004ff7358a100acfe7358a100acfc7358a1002eef7258a10076ee5258a10076ee4258a10006ed4258a10076ee3258a10076ef2158a1002cfc7058a1002eee2058a1002eec2058a1002ef71058a1002ef51058a10004ff7654a1002cfe7654a10004fd7654a1002cfc7654a1001e7e6554a100067d6554a1000eee6254a10006ed6254a10056f56154a10004ff764ca1002cfe764ca10004fd764ca1002cfc764ca1000eee624ca10006ed624ca10077cc324ca10056f5614ca1001cff765461002cfc765461001e7e65546100067d6554610005fb705461002df8705461000cff764861002cfc764861000eee6248610006ed6248610005fb704861002df8704861001cfe76d95100667e65d9510006bc64d9510025f671d951002df571d95100677751d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100667f54d9510
  | 7 => 0x9710004fd7459710014fc745971008e7f54597100067d5459710004ff725971000cfe725971000cfc725971002cfc7159710026f4715971002cf4715971008ef751597100267e51597100267c5159710026f4515971008e7f5059710026f71059710004ff7558b1001cfe7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b100067f5458b100067d5458b10004ff7358b100acfe7358b100acfc7358b10026ef7258b10086ee4258b10006ed4258b1002cfc7158b10026f47158b1002cf47158b10026f63158b10086f72158b10026ee2158b10026ec2158b10026f42158b10086ef2058b10026f71058b10004ff7654b10024fe7654b10004fd7654b10024fc7654b1027e7f6554b1001e7c6554b10005f77154b10025f67154b10025f47154b1027f765154b1027f745154b10004ff764cb10024fe764cb10004fd764cb10024fc764cb10087cc324cb10005f7714cb10025f6714cb10025f4714cb10025f7765471004ef7765471002777755471001ef66554710026f4655471029df77454710035f6745471029df57454710035f4745471008f775454710297755454710005f77254710085f67254710085f4725471002df6705471002df47054710025f7764871003ef77648710005f7754871008df67548710005f5754871008df4754871028df77448710035f6744871028df57448710035f47448710287775448710287755448710005f7734871023df67348710005f5734871023df47348710026f76348710006f56348710027e7724871000ef66248710026f46248710087e64248710287e5424871002df6704871002df4704871001cff7654310024fc765431001e7e65543100067d6554310005f77154310025f4715431000cff7648310024fc764831000eee6248310006ed6248310005f77148310025f47148310025f7765971002777655971008ef66559710026f46559710027746559710005f77459710035f67459710005f57459710035f4745971008f775459710007755459710005f77259710085f67259710085f4725971008df7705971002df4705971008f775059710025f77658b10005f77558b1008df67558b1008df47558b10005f77458b10035f67458b10005f57458b10035f47458b10007775458b10007755458b10005f77358b1023df67358b1023df47358b10026f76358b10006f56358b10027e76258b10086f66258b10026f46258b10027e46258b10087e64258b10007e54258b10085f77058b1002df47058b10087e72058b10005f77654b10025f67654b10005f57654b10025f47654b10085f77554b1027f776554b1027f746554b10275f77454b10035f67454b10275f57454b10035f47454b1008f775454b1026f755454b10005f77354b1023df67354b1023df47354b1008f7
  | 8 => 0x4ff7458d20014fe7458d20004fd7458d20014fc7458d200067f5458d200067d5458d202a4ff7258d20006ef7258d20004ff7158d20024fc7158d202ecff7058d20006fb7058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2001e7e6554d200067d6554d2000dee7254d2002dec765492001eec765492002cec765492000def755492000f6f75549200076f655492001eee655492001eec65549200a76c65549202e5ef74549202e5ed74549200a76f54549202df6d5454920005ef73549200a76f53549200076d53549200a76c5154920007eb705492002dee705492002dec7054920007e8705492000eef605492000feb60549200a76f505492002dec764c9200aeec764c92002cec764c920005ef754c920005ed754c9202d5ef744c9202d5ed744c9202cf6f544c9202cf6d544c92000def734c92000fcf734c920007cf634c9200aeee634c9200aeec634c920097cc634c9200aecc634c920007eb704c92002dee704c92002dec704c920007e8704c92000eef604c92000feb604c920097cf304c92001cfe75d8520004fd75d852001cfc75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d85200067f54d85200067d54d85200acfe73d8520004fd73d85200acfc73d852002cfd72d8520076ee42d8520006ed42d8520076f621d8520076f521d852002cfe70d852002cfc70d8520006f76198520055f970985200057f75585200a57c7558520005bf745852009dbc7458520005df7358520095dc7358520085fb7058520026f66118520006f56118520004fe7694520004fd7694520024fc76945200067f659452001e7c65945200076d5294520004ff7654520004fe7654520004fc7654520004fe768c520004fd768c520024fc768c520006df638c5200aedc638c520026f6618c520004ff764c520004fe764c520004fc764c52001cff765412000cfe76541200ccfd765412000cfc76541200067f655412001e7c6554120005ef725412000dec72541200076d52541202c5fa768c12002efa768c1202bf7b548c1202bf79548c1202a5f9738c1200aefa638c1200aef8638c12002feb728c12000dfa728c12002df8728c12002fe8728c12002efb628c12002feb628c1202b7ea528c120007e9528c1202b7ea428c1202bfe9428c1202b7ea328c120097e9328c12002ff2718c12002ff1718c12000cfe764c1202a4fd764c12000cfc764c120005ef724c12000dec724c120007cd324c12002fe8204c1200aef8764c12000cf8764c1202af7b544c1202af79544c120007eb724c12000dfa724c12000df8724c1202a7e8724c12002efb624c12002feb624c1202a7ea524c120007e9524c1202a7ea424c1202afe9424c1202a7ea324c120097e9324c120007c9324c1200267f7559710004ff7459710014fe745
  | 9 => 0x47558620006747558620006f77458620006b77458620006f67458620006f57458620006f47458620006b47458620006f75458620006775458620006f65458620006f55458620006755458620006f45458620006f77358620006f67358620006f57358620006f47358620006f75358620006f65358620006f55358620006f45358620006f74358620006f64358620006f54358620006f44358620056f67258620056f57258620056f47258620056f75258620056f65258620056f55258620056f45258620056f74258620056f64258620056f54258620056f44258620056f73258620056f63258620056f53258620056f4325862002ef7705862002ef6705862002ef4705862002ef7505862002ef6505862002ef5505862002ef4505862002ef7405862002ef6405862002ef5405862002ef4405862002ef7305862002ef6305862002ef5305862002ef4305862002ef7205862002ef6205862002ef5205862002ef42058620024ff769462002cfe7694620004fd76946201d67f659462001e7c6594620026f66194620006f56194620004ff7654620004fd765462002cfc7654620026f66154620006f56154620024ff768c62002cfe768c620004fd768c620026f6618c620006f5618c620004ff764c620004fd764c62002cfc764c620005ef724c62000dec724c620026f6614c620006f5614c62001cfe76d95200a67e65d9520004ff74d9520014fe74d9520004fd74d9520014fc74d95200a67f54d95200067d54d95200acfe73d9520004fd73d95200acfc73d95200067e53d95200a67c53d952002cff72d952000cfe72d952002cfd72d952000cfc72d95200de7f52d95200de7d52d9520024fe71d9520004fd71d95200a67c51d952000cfd70d95200a67f50d95200a67c6559520005df7359520095dc73595202f5fb70595200dcff75595200067f7559520004ff7459520014fe7459520004fd7459520014fc74595200a67f54595200067d5459520004ff7359520006df7359520004df73595200acfe73595200acfc7359520006dc73595200acdc73595200a67f53595200ccff7259520006ef7259520004ff7159520024fc71595202f4ff7059520006fb70595200acfe76d8d20096de63d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d200067f54d8d200067d54d8d20006df53d8d20096dc53d8d20096de43d8d20006dd43d8d2002cff72d8d2000cfe72d8d2002cfd72d8d2000cfc72d8d202b6df32d8d202b6dd32d8d20024fe71d8d20004fd71d8d20096dc31d8d2000cfd70d8d20096df30d8d200057f7558d200a57c7558d20096dc6358d202edfb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d2001cfc7558d200067c7558d2001c7c7558d20
  | 10 => 0x85500d5bc745855008dfb70585501ce7f6518550026f66118550006f56118550004fe7688550004fd7688550024fc7688550004ff7648550004fe7648550004fc764855002e7f7559620004ff7459620014fe7459620004fd7459620014fc74596200c67f54596200067d5459620004ff73596200acfe73596200acfc73596200c67f53596200ce7f52596200ce7d5259620004ff7159620024fc715962002cfe705962002cfc705962002e7e505962002e7c505962002eef205962002eed205962002ef7105962002ef51059620004ff7558e2001cfe7558e2001cfc7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e200067f5458e200067d5458e2002edf7358e200b6de5358e200b6de4358e20006dd4358e202a6df3258e202a6dd3258e20004ff7158e20024fc7158e2002cfe7058e2002cfc7058e2002ede3058e2002edc3058e2002eef2058e2002eed2058e2002ef71058e2002ef51058e20004ff7654e2002cfe7654e20004fd7654e2002cfc7654e2001e7e6554e200067d6554e200aede6354e20006dd6354e20005ef7254e2000dec7254e20026f77598620026f67598620026f57598620026f47598620026f77498620026f67498620026f57498620026f47498620006f75498620006775498620006f65498620006f55498620006755498620006f45498620026f77398620026f67398620026f57398620026f47398620006f75398620006f65398620006f55398620006f45398620006f74398620006f64398620006f54398620006f44398620026f77298620026f67298620026f47298620086f75298620086f65298620086f55298620086f45298620086f74298620086f64298620086f54298620086f44298620086f73298620086f63298620086f53298620086f4329862002ef7709862002ef6709862002ef5709862002ef4709862002ef7509862002ef6509862002ef5509862002ef4509862002ef7409862002ef6409862002ef5409862002ef4409862002ef7309862002ef6309862002ef5309862002ef4309862002ef7209862002ef6209862002ef5209862002ef42098620004ff75586200067f75586200047f755862001cfe755862001cfc75586200067c755862001c7c7558620004ff7458620006bf7458620004bf7458620014fe7458620004fd7458620014fc7458620006bc7458620014bc74586200067f54586200067d5458620004ff73586200acfe73586200acfc735862002ef77158620006f75158620006f45158620006f74158620006f64158620006f54158620006f44158620006f73158620006f43158620056f62158620056f5215862002cff705862002cfd705862002cfc705862002ef6105862002ef41058620006f77558620006777558620006f67558620006f57558620006f
  | 11 => 0x14fe7458650004fd7458650014fc7458650006bc7458650014bc74586500667f54586500067d5458650004ff725865000cfe725865000cfc725865002ef77158650066f65158650066f5515865022e7c5158650006f74158650006f64158650006f54158650006f44158650006f72158650006f4215865002cfc705865002ef6105865002ef41058650066f67558650066f57558650066f47558650066747558650006f77458650006b77458650006f67458650006f57458650006f47458650006b47458650066f75458650066775458650066f65458650066f55458650006755458650066f45458650006f77258650006f67258650006f57258650006f47258650066f75258650066f65258650066f55258650066f45258650006f74258650006f64258650006f54258650006f44258650006f63258650006f53258650006f4325865002ef7705865002ef6705865002ef4705865002ef7505865002ef6505865002ef5505865002ef4505865002ef7405865002ef6405865002ef5405865002ef4405865002ef7205865002ef6205865002ef5205865002ef4205865022d7f74946503257d74946501d67f649465031e7d64946500067d629465001d7e719465001f7671946501d67f61946501d776619465022e7d61946501d77561946501d77a70946501d57d709465022f79709465001e7e609465001f7a60946501d7771094650024ff768865002cfe7688650004fd7688650026f66188650006f56188650004ff7648650004fd764865002cfc76486500057f754865001d7c7548650026f66148650006f5614865000cfe76d89500ceee62d895002cfd75d895000cfc75d8950004ff74d8950014fe74d8950004fd74d8950014fc74d89500c67f54d89500067d54d89500acfe73d8950004fd73d89500acfc73d89500c67f53d89500ceee52d89500c6ed52d8950006ef32d89500ceec32d8950024fe71d8950004fd71d895001cfd70d89500ceef20d8950005df7358950315dc73589500ceec625895030dfb705895002d7c765495000e7c765495002c7c76549503057f74549503057d74549502fe7f64549502fe7d64549500057f73549500067f635495001d7f725495001f6f72549500076f625495000e7e625495000e7c62549500cf6c625495027e7c61549500077b705495002d7e705495002d7c705495000778705495001e7f605495001f7b60549500cf6f2054950004ff764c950004fe764c950004fc764c95001d7e754c9500057d754c9500cfcc324c95002cfd75d8550004ff74d8550014fe74d8550004fd74d8550014fc74d855007e7f54d85500067d54d855000cfe72d8550004fd72d855000cfc72d855007ef651d855007ef551d8550006f741d8550006f441d85501d67f6598550006f76198550065f97098550005bf745
  | 12 => 0xf7458d21014fe7458d21004fd7458d21014fc7458d210067f5458d210067d5458d21334ff7258d21006ef7258d21354ff7158d21006f77158d21004ff7058d2102cfc7058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2101e7c6554d21006df6354d210aedc6354d2101cff765452100cfe765452111cfd765452100cfc76545210067f655452101e7c6554521005ef725452100dec7254521027e4215452134df6768c521026f6768c52133f77548c52133f75548c521335f5738c5210aef6638c5210aef4638c52100df6728c521025f4728c521026f7628c521027e7628c521347e6428c52133fe5428c521005f5708c52100cfe764c521334fd764c52100cfc764c521005ef724c52100dec724c5210aef4764c52100cf4764c52132f77544c52132f75544c521007e7724c52100df6724c52100df4724c521337e4724c521026f7624c521027e7624c521337e6424c52132fe5424c52101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d81210067f54d81210067d54d81210acfe73d8121004fd73d81210acfc73d8121024fd72d8121086ee42d8121006ed42d8121086f771d8121006f631d8121006f531d8121086f721d8121086f421d8121086fa20d8121006fb60981210057f75581210fd7c7558121005bf74581210f5bc7458121005df73581210eddc735812102efa6018121006f96018121004ff7458a50014fe7458a50004fd7458a50014fc7458a500a67f5458a500067d5458a50004ff7358a500acfe7358a500acfc7358a5002eef7258a500deee5258a500a6ed5258a500deee4258a50006ed4258a500deee3258a50004ff7158a50024fc7158a500a67c5158a5002cfe7058a5002cfc7058a5002e7f5058a5002e7d5058a5002eee2058a5002eec2058a5002ef71058a5002ef51058a50004ff764ca50004fd764ca5002cfc764ca500057f754ca5001d7c754ca5000eee624ca50006ed624ca500dfcc324ca50026f77598650026f67598650026f47598650026f77498650026f67498650026f57498650026f4749865008ef7549865008e77549865008ef6549865008ef5549865000675549865008ef45498650026f77298650026f67298650026f57298650026f4729865008ef7529865008ef6529865008ef5529865008ef45298650006f74298650006f64298650006f54298650006f44298650006f63298650006f53298650006f4329865002ef7709865002ef6709865002ef5709865002ef4709865002ef7509865002ef6509865002ef5509865002ef4509865002ef7409865002ef6409865002ef5409865002ef4409865002ef7209865002ef6209865002ef5209865002ef42098650004ff7458650006bf7458650004bf7458650
  | 13 => 0x895111eef21d895102cfe70d8951004fd70d895111eec625895136df77158951004ff764c951004fe764c951004fc764c95111fcc324c951024fd75d8151004ff74d8151014fe74d8151004fd74d8151014fc74d815108e7f54d81510067d54d815100cfe72d8151004fd72d815100cfc72d815108ef771d815108ef751d815108ef451d815108efa50d8151006fb6098151005bf7458151125bc74581511d67f651815102efa6018151006f960181510267f7559621004ff7459621014fe7459621004fd7459621014fc74596211167f54596210067d5459621004ff73596210acfe73596210acfc735962111e7f525962111e7d5259621024fe7159621024fc71596210267e51596210267c5159621004ff705962102cfc7059621026f71059621004ff7558e2101cfe7558e2101cfc7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e210067f5458e210067d5458e21026df7358e21106de4358e21006dd4358e21336df3258e21336dd3258e21024fe7158e21024fc7158e21026de3158e21026dc3158e21004ff7058e2102cfc7058e21026f71058e21004ff7654e21024fe7654e21004fd7654e21024fc7654e213667f6554e2101e7c6554e21004ff755822101cfe755822101cfc7558221004ff7458221014fe7458221004fd7458221014fc74582210067f54582210067d5458221004ff73582210acfe73582210acfc7358221026f67158221024fc7158221026f63158221056f72158221026f42158221026fb7058221006fa4058221006f94058221056fa2058221026f71058221026fb1058221026f31058221026f8105822101cfe76d95210fe7e65d9521004ff74d9521014fe74d9521004fd74d9521014fc74d95210fe7f54d95210067d54d95210acfe73d9521004fd73d95210acfc73d95210fe7f53d9521024ff72d9521024fd72d952112e7f52d952112e7d52d952100cfd71d95210fe7f51d952102cfe70d9521004fd70d95210fe7c50d95210fe7c655952135df7715952112cff75595210067f7559521004ff7459521014fe7459521004fd7459521014fc74595210fe7f54595210067d5459521004ff73595210acfe73595210acfc735952111cff7259521006ef725952135cff7159521006f7715952127e7e515952127e7c5159521004ff705952102cfc70595210acfe76d8d210eede63d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d210067f54d8d210067d54d8d210eede53d8d210eede43d8d21006dd43d8d21024ff72d8d21024fd72d8d21346df32d8d21346dd32d8d2100cfd71d8d210eedf31d8d2102cfe70d8d21004fd70d8d210eedc30d8d210eedc6358d21355f77158d21004ff7558d2101cfe7558d2101cfc7558d21004f
  | 14 => 0x4fd7459532014fc74595321467f54595320067d545953238cff7259532006ef7259532004ff7159532024fc71595321467c5159532004ff705953202cfc70595321467f505953238eef2059532024fe76d85321457e75d85320057d75d853213dbe74d8532005bd74d8532357cc32d853201cfe75d85320067e75d853201c7e75d8532004fd75d85320067d75d85320047d75d853201cfc75d8532004ff74d8532014fe74d8532006be74d8532014be74d8532004fd74d8532006bd74d8532004bd74d8532014fc74d85320067f54d85320067d54d85320acfd72d8532006f741d8532006f441d8532356f621d853202cfe70d8532004fd70d8532347cc3298532006f76198532337cc325853234fcc3218532026f66118532006f5611853202cfe76d81322efcc32d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d81320067f54d81320067d54d81320acfd72d8132024fe71d8132004fd71d81322eefa20d81322b7cc3298132005f67198132005f57198132006fb60981320057f75581321457c75581322a7cc32581321457e75181320057d751813213dbe7418132005bd74181322c7cc3218132005f67118132005f5711813202efa6018132006f96018132004ff7458a51014fe7458a51004fd7458a51014fc7458a510fe7f5458a510067d5458a51004ff7358a510acfe7358a510acfc7358a510fe7f5358a51026ef7258a5112eee5258a510feed5258a5112eee4258a51006ed4258a51024fe7158a51024fc7158a51026ee2158a51026ec2158a51004ff7058a5102cfc7058a51026f71058a5127d7f7654a5100e7f7654a5100c7f7654a513857f7454a513857d7454a5127e7f6454a5137e7d6454a510057f7354a510067d6354a5101d7f7254a5101f6f7254a5100e7e6254a5127f6e6254a5100e6e6254a5127f6d6254a5100e7c6254a5127d7f7154a51007777154a5127f747154a5101e7e6154a5101f766154a511d57c7054a5112f6f2054a51004ff764ca51004fd764ca51024fc764ca5101d7e754ca510057d754ca5112fcc324ca51004ff7458251014fe7458251004fd7458251014fc74582510667f54582510067d5458251004ff725825100cfe725825100cfc72582510667f52582510067d5258251026f67158251024fc7158251066f75158251026f45158251026fb7058251066fa50582511d67c5058251006fa4058251006f94058251026f71058251026fb1058251026f31058251026f8105825100cfe76d895111eee62d8951024fd75d8951004ff74d8951014fe74d8951004fd74d8951014fc74d89511167f54d89510067d54d89510acfe73d8951004fd73d89510acfc73d895111eee52d8951116ed52d895101cfd71d89513767e51d89513767c51d
  | 15 => 0x600200900200200501c00300e01001201500700c02300002400000801000000100800b01700300101300000000200100000008500f00601200100000c01100300200200801f03401300000900a00503c00200b00f01400f02d00300c01202700a00900000701201f00600500000000400100000b00c00200400000800b00200300200002700700201400100e00001002000102a00400600002f01400001a0040150000130000090070060ac01300000200502f01100000100601701302800000100000100700000200500800300200400d00000000101800001b00a00400900a00600601a00000600100700101402001900200000301500601b00802200002900000000001400800101200100c0000010040acfe76d8d5214ede63d8d5200cfd75d8d52004ff74d8d52014fe74d8d52004fd74d8d52014fc74d8d523be7f54d8d520067d54d8d5214ede53d8d5214ede43d8d52006dd43d8d5201cfd72d8d523b6df32d8d52024fe71d8d52004fd71d8d523be7c51d8d5202cfe70d8d52004fd70d8d523be7f50d8d5214edc30d8d523b6ef20d8d5214edc6358d523adef7258d520ae7c7654d5200c7c7654d523a67f6454d523a67d6454d520076f7254d5200d7e7254d5200d7c7254d5238f6c7254d5200d6c7254d5201e7f6254d5201f6f6254d523667c6154d5238f6f2054d52024fe76d8552155be74d8552005bd74d855200cfd75d855235e7d75d8552004ff74d8552014fe74d8552006be74d8552014be74d8552004fd74d8552006bd74d8552004bd74d8552014fc74d855236e7f54d85520067d54d85520acfe73d8552004fd73d85520acfc73d855201cfd72d855236ef651d855227e7c51d8552006f741d8552006f441d855235ef621d855202cfe70d8552004fd70d8552006f76198552026f66118552006f5611855202cfe76d815200cfd75d8152004ff74d8152014fe74d8152004fd74d8152014fc74d815230e7f54d81520067d54d81520acfe73d8152004fd73d81520acfc73d815230e7f53d81520067d53d815201cfd72d8152024fe71d8152004fd71d815230efa50d81522f6fa20d8152005f67198152005f57198152006fb6098152005df735815214ddc7358152155be7418152005bd741815214dde7318152005dd7318152005f67118152005f5711815202efa6018152006f9601815201cfe76d95321467e65d9532397cc32d953238cfd75d9532004ff74d9532014fe74d9532004fd74d9532014fc74d95321467f54d95320067d54d95320acff72d95320acfd72d95323967f52d95323967d52d9532024fe71d9532004fd71d953202cfe70d9532004fd70d95321467c50d9532396ef20d953201cff76595321467c655953239def725953238fcc3259532394ff75595320067f7559532004ff7459532014fe7459532
  | 16 => 0x701800100100001a01c00500e00001400c00400200300400100700400f00004c00000300600d00200d01a00001200300603800200001c00000500000000300000100700400000000100701100100600100200000000500600801000101000200300301f02800002401401900200100100100300600100600a00a00600300302e00000104600300700002101500001100003000000f00802801202602500b00901703d01a00200000100400201100000000400b00300000300e00000100100000200f01d06500600400000400300900201e00000100d00002b01000000000300000400f00000000100500100500000000d00000001c00602100100502f00e01803200200000000500c03200000100400f03f01202301b01100c00202d00200100a00002700201b00300300000500100000801601800000200d01200000000100600000001b00101900600000600601701100200500700c00000000f00100300200000202200b00000502200000200200100001b00000d00201900100a00001d01801000500c01500400100300905601c00000500800a00000803000100000200100100000100000900101c00200200d00500901d00001700000a01500002100900400000500e00004f00302e00c00802000000200c01800001f00400000300400200000700900c00900301001f00a00700b00700000400300001500200000800000500300200000000e00b00500200000001f03400000200603c00000000400601100000200402005600002800000000000100300100000100d00600100100800002700b00000100800502701f01900a00a00100200400300100400000000200200600400500f04200d00200100501e00000100100000400300000701200000000c00e00101500800200400107100904100300400000901100c00200000700d00700501103c00000100001c00000900700100400700c00500100200000000400200100600000600200000201500200601600300600101004101500b00400200400100700304a01e00400100100300500001500000f00000300b00100000000d00000000500200b00401201200201500102000100800200101000000101d00000000401e00200700103301600300100000000202b00803000000000000100200100200500402700900101c01000400300500c00400303100200400000c00900f00800600100600900f00100000200700000000302000300e00d00600903400000400200001c00d00300100001200602b00401300a00f00100100000601400600000100201500101200001200000000504c00500000000301901b00601500900900100b00100400901301b00400000000100600500000a00200000000500800000800102e00100201900700000400800300400000400101300c0030080080080200
  | 17 => 0x6845ae401101127c00034c000000000000000000000006612a60a0d2901680f8481e0006f700f80000009622a01dc80006c630898dcb7a9d040acaf10e80000000000000000000000078277b2a50000f7409600029107200000000ab40000000001ed864b0004bfa8340009db50a99308766ea00007b2bb862d2aa08701ba43c3fc02b859c0e604a85c4bec1fc18280008be85907f98e0ff2914222cdc08350005314660f0c123485063000054847000008282310001d4d2c84f74da266060400001a28f41bc0e9400939020a0000f00000c8c6003550110b4633d4e2227800000000000000009f000002b00a800000006b53b249e000000000026800021549704a80ea000000021d2d218941af00000007490925660001f880005d33cf0000f6600000000000009ca336000000018a8000000f0800015390e06de98416280640006ac2ec91000000001be0000ad7a11995005476632b1ca86beeb43ee00029e0ca22b214201182b0000140000037072242ea23800086f9a55ef2c5405708a1ac08b01e20000e4a000185c9a0f5a00083411f80000000000ef61909c22501161a0d10800040f05f0d020c43a48fb531c4ce1368d6c0b3a5e10a993cc4231a5039f42cc46ab13e159c36a1221481a253229b129087193409923ef87ed41c0a835e1d48f847bb8db27c88f996e00e4ce538012806a44e0fad3161b057781086d209655b128e3cc1849da064e55e86ba1ce90a83b52b16881e06650701dee7bf87f3c09e7d0dc1d73f3a80110197738c97443b255f0ae85a8e8477726b28c4ae26af45765f894e02c24988bc4d610e38c09494e462e06d25389a223a4660b0d2d84b94b9d170ad94290699b601fa727311a74d286804aaf1d3ca0ea0b3fe8dec9ef7ad302954207a17a3d58f2d0ed0004cfa2d458831b1e1662137aa7a250840c5110b401598685a03611ec001d40c78e16e16500816c01d5a9201301de0291d2f0333a244d8fde0005fa0c90b186e826ac01c000f447e842b000000068b507c0003b81870289c840ea6f92a283ccbfe5463b681f887a00004492410147dd02c27c4fe439b2ea9b5c91f0004aba7e06f200002400400b00000e00300000100000000001400800700f01d00700501f01e00b00a00000700000401c00400500100000001700000000e00000300000900e01000002200200000001300101500800102901100000101402900902800000800a00800f00d00800a00000100100102700103600f00001606300300b00200600000600301100000c00100d01600400302400102101800000200001600001b00000600303500500000400100100303e03101100800801a00900000000000000000000000004202100501400100000200e00400c00200000100200101502800600200402300100100000001300700000700f00
  | 18 => 0x28a3ba8790fea96f47d9f5620e81eb0129981d8209b6b192d1c82f50428288c24a2403e8f3484e590041c5701f5903243a36072c3da0bfa05800052545ca1f80b814209b0fc00000003b80000f380002a594c878a8b605d8266a4c7f33fbdbac6e27ac06c063858443427280009b18fc39000004900001df19410eb09bc8d8e9522e0002238f8200000000026e8bca8f52b504f5026294299a18d0b6a109781bd01863e43179cc8e78000000242d38900022489382e00043ab228473a5c08001b9d1d000015706f533800000005053cc00040c2500b1a00000000007260004fba972b9883f000000130060a0001ccc7c21893b20db86b40003f6dbb53f700000481ba4089e14c192dcd8400026980000000000000b480000004da81acb22000060158f0e12ef485e0c268f0003d51880e0043303b17d061e0002818f50e235e70000001062a21000000035b7d42c589740000fe25115ac5b090d06d87c485471f0f9df843370004608000b2c8f94b18d540000003dc8a1406c6641320000bde0530e7801519a7b42889fd91066b42d28000b8c1a32fda4d8c3623e4c500000000004c7800085e91029718784410b800000000000000001ef00000000001f4e3b05792e8278c78e00000020f519c24023ca94cab443622c4d8c80477e000000000046f25e238409667400000000004861fcc6c600013229f97806422122f70af4830279971288d4f20000001ea52a66cd50d8cb232627a4079e744ec9dbc4600003d65054ea924460c5e64591a511026cb28e0ee00002f91d6a6b0ce688a1732074aa2000000158a0007c512308e04760003a69a9400000000015b42620000921f786c89c543122880000000001bc8cf44954eb26e000000000010c84b858f030a962ba3a102e484854b32e11251f20ed259e12625d814f9093359922ec6241a638c0c84c50bcef05c21a82324b391541de25e40224ac64a8b02169c4c5ca00140e515c8fc7603d20a2a6e64743e392246f455ccb520f14246bf36a0d20be40001309bf11ca00013f8facfc812a3989c5804a75128a9e6c0008803e768bd1a605699da4bc60b35309327d00be29d25213c535a20620d96f0e943e8370920c93023545e20e12b07d61f0027610b87ac1026e48607982470074d7a3ef2570318ef024d40683263c69e005e9c1c9aa5a62778a5cf9907b413a1e039a72d38929967ac7b846187042005062a99a84ecaa081e3c38806a8c2512862f09c00e4d7000074200c04380000000001dd833c0000002268e90aa04ac2cf60a81c688249208141227b6b9b8950e284c30e55208d762390b70a4417c30fa1109b8cb75584d284bc94654f00026a807e0000001ed421200034f99700004ca49f8b04ade660000167c00050a0001858000000487a7243840001c58ed230f00040bcd486b23ba0fea
  | 19 => 0x923a26e79ec111a70de240309280002680d9ac41d7c41c45b46ea5f02885ac26c80014b884d39f99993269ce483946c445a3800022b51b468813014b010d38a2040bf13a82ca0a3cb8cec43f61e4e02c0000000000000182376c3fe98c44e8d600004e80006280518000b5a92940ddc304d72891e2d83cb3a1791802350b912a01739c150ae8250db9b7c0000000658ea20f25c1abd00000008290001bed3dc97d497262400093500001e20004371491f800003ae0002864cc626645f0268b140000a480006d618639a000141e00049b80000000004e5800073e08200000000000003808114e8e1cc18c865800000000022a09102ae89391a078d9701f480000004701f38600bc21b08342545238338aa9222c000163538000012e1c02849ab43b429c00001dd2ac06e1b61460ee69c72490f246c4194394996106ca4c4bb56c09b6927105c91cbd61481fd800016a9ea32d23441388790381adcb000002f480012ca5591c31ec037833e4b09cc01ee00026c242068c9c627b211c26a1829f88a2d2d6717000000107c00041728ba00016527a0988ba8a13311000016c00326b96600009af0e8800053e0004919e94ec268d0a840000004cd518157ec1c77c2f99a9d066011212cf485040780c801086102a10d30a600004fd00010ad19079a8dd002e0660002b803b91202200831d392e697a0000d16772a5f2c38590cbaa4246d9eface037e0aa86b800058134b93c898a57416ea2f47fc2e8490a90cf160fca581e643fc5ed4df0cfcba128f13e8bf71809b646f9fbcf064603dd91227041ce4598ab248697b3e8a3f80008390f8c7bc8627b2425a4e8a5303b2578000be24ff3e7c000a024dc4fd1d6cff83dd44a80013f80b11981f3929a1174e18a983578434638e0c7a200053580005c05f380019f400085f3b5196d48e50d90180013981f830201f029c00040003cf1da55d4a29e4109052702692d83961303512984f4c42c1758d7cca61d605080000000003880000f7c1044a786a72e903802d80280cc8e92c210489e06c80fb0e50ebc0721fa12c869e335479250b24c60b000087d3e600040353500009a612b847c8f571a110800029a9441aa22ecc0f66700018711f00000948d34141188d19a00c7f75023fc4c8044a51602b000103421642f0ba92b87cd36d01c4b8a6153aec0000002491b484cc8f865647b1264f9427b40b8120f509693491bbc00000030b9b4c34a98100011d8aea0001f99fb45bc8189a1e1a80005392798c4c3625123761fe8f1a0003870c020d3000322a7fd0b49e40000000000a6236600007303a637c028e6a2519342800000081f1d382385020d10001a8cf267cf2aec7cc0049d11b302cc15e3f25142110000000185c84c70a65900017693b13120b085d6b82a54163a01910a6b209f063533c06c46591106fe
  | 20 => 0x33f5000092c00000049f131102256f832a25ca7607f06500988f79b70b9a2b80c619f0d9a0311ae74316b1758a5aa5d27500014a08d5438d2e333295436289760aa50c486465c518a040f92990ff6a520bbe8a847a3f8c788b9010903a2ff0358de69f9183e2c444418352d5e44d5c2518ba9b1c44665739b02806ca8403181f36f47576a89a2ac00000000012d40007412e58000a863113a00000cd46e04f611dd4d82af3aca1040007d185503c800074507b00000000003df88b800000047100006ac0001e4000000089843292cc7f5000000000072e00000010441b2301c94106813f60c43dc732a2854d06a86281a02da1d79000b8e85dad380c0a6ea5731216087ca8a331b0b545d290e056800145a53531d13f80000000c88be84e472f000051c00000018c0000b7c915235976d28469b530c0000001770002658000000245a6ccc8650e4a6000007c3df44789e10d844f1c38bec98c5cf00000000002510002130bbe87c9a71f0146e816cfe800000c04a0001c452a45343dec1b500e2b08000ca105642e30c0aa4e3878239214f8dec000209a06b40b9110cec0492aa92c4a30f4c68202e3d0869c2b43581e1e8d904200014c853082e93b34029640000c837d06052e224f0cd99b93906db3f64de083c26f03380011d40000001bf8c0c51005fa65d4f8490c46a8accfe99d008113078352443a4cdd1ee1c80d5885096839c39d250e78c4fa51a0f40bf30c543d06b280e9b005c908400031d48c95b800000006b5ad405a9da1ee00000df4e90000ad52891f592b0000af0555108929404610d0a30d4111013f00020160001ddac30cbb0b080805368584887762ab1fb83886f548c111a4b6a4d13511c84349330f7cd10b3628e0a80cb0fb062b0a199d8db293c22296808a260d244db70c9c57714d067513a000511102ca9da5eb49a38cf7a757000119507468a337a73cd721e522d1e5089608d24b19ae8da77f001c11cc7a1990d5109095a000506099c3e5000273076d4046870811c6cd9c2b93fb8ae12f0394c4f652908c16d20f8d2400037613800000002a40000804fa62584f780012009bf4c5800009c8861ac67342307881b4293d411a690d411b13ce2fd25ea31124a7d94cd00004e819a02080c43ea32e39e898d0d6968417953e1026cf4af8000ce49928000000f2e5d22e21a3cc0e64d2610a2600000043486b112837d0dd8178a3c0001ae1f0ce6a0000000000b33050000120480a1850001f4a000000065c00051084a22120c6e9809cbee082d00a0c245c0c3014c5ab19c2982bb044a343150827628d03b5950e045cd3c6046cdaa3db5249e011740c904f0bb8a1a4693599e9d1120d3a7005886849664d201a44be6824ad21d45263bc35f0898f2469023c51cc9984972d798f88f43d540e19861365b51c61b0c3098f4295
  | 21 => 0x505288e26f0287a93814b0003ff013064922826e9e252da20a1439fc02387c1000070c5ee00015f80007ae19e000167055f9c10860b7c691517000099402c00000014131a00000000b003d410a0a9991a03430453b8000000564baf456d16b30e1da21c92e4a5d895938cbf039215599088f3541049a66c8bc56826b491400098724521d94b61ee0fd2290d5012c1ef02180005ec00002207f87e3000000000008017b25d11dc91f072859875589311485d8c324d222090386ba3cf21145484689a84e90c2807214b223e9b87d88684c10d12d2201300029000003c31880000b723342d08edc47881dbe319dc34057b2a70fdce1052a1d40a5804019c827a4a80c0a1f014105445600034a9118b32112404935ec5818437e9df464c49c00016b8cda9953a800000004192be96c43e900000000001183c4b201410dba00000015fc0003ce3ec68e80007eb00000008d40002e70dd6caa21853b00000000000000000d32000000000000000026785e04ea1f7467a0081c236a31c828a0008a5005800065b0001bfd1990e5601000048e4813013d1853c7125440bea8f8da23d786c608d2963882f40a94a347951348000e903b53d7296875489139264f44e27032b99648c26a2c48d19e0b1206a4bc81c65902fe33a92e8ca4406477a038bea61f3d2dfd0eba6b64630c711403c200026a414e00049c082466d0d58c5826a9f62ec43ea5de6ee5f937121080c86c40000fe915402715618425763912acc4b74725dd16da85c13d19c4bae96f4d057e3e60b241be0cc17989054063670121a68727a7439504b87809eb124c82314921938f15810c09e902d1788b641400379b292820212100b4c8200f9465110c36703f9f322fc45a57c20610d4faf0a93ba01d13fc6330c7989c7888660000370b180ba000287455b2d43ac057d4948104f9d60cd709314fb1a90e2a34001523ac92831407a002090056206682502a31e607d947489032d0fa10e477e65aac98bc922420a8740000bfaa6738e96fcfcaa0ea29032a00098c10f16a03481d029828d4b6c2ed32513685445bb0968d154126690a29298ce21f916688400c465f0b61058e5c87303980c94640000001dbd02a00028f9b9114e41c2f826eca19000000142c00000013b9e3c8ba00000000000002954ae81e8791a3c3f61ba48a81f03db8a79138000346000000000050d18f12a00000014aa8aae000276a4040000000ca8000bc6000000108c0003e200027700000003e214d8b2e4a93d7a13c0007d5473a414a78a4534ea92c3db91e168493affea012dc0ccc65e0831f1a85003835e1dac0005fe0000000000b897a000b62d0000000479a634d2c00000000000005640da0bc547e89233d96d00003f93b602dc56c34a2e40b5623a000000102800086125887542206a048e98ecb862730f5d13904
  | 22 => 0x9213c139d8200000b20e48ad0c063841d61ac48a0346c38926871e9900b783e83d01bf0aa156a2535eeb3ca9ecece1203c28c2d1e07392d4883c67801880026151cc253000000066429b0c114bd0f84fc16782c023c82d4eb9a6070247b2cd06c0c621e73c3845514ca1c4288ece5a28264ad96dc11e6ba47f82f077a90423e964325a09f2740a185a93a33bd00008085aa24d8c8c46e8d227a80001c8000183914cc8274600013b8000372371a9545b23ca00015a201a16ac4b1524e0c6481cf276021e24f8d7a89c0005d3c0fc0014522cb412214c57c0000e98000ea89fb47ea26540a188020c00042e49d2501c2800025a0d94c350de5f8c3b800137870400011fcfae560b4f0000982000489a1500004c01989034000000000121041961d4290000a7470f15980503d2a7500027d40a972b1db172934600042e19f89c400000000007521e14f102a62790000001c2c000644050cd2c00000000027b52ea4be1b00d5c7406a615d0890ae44c913c619cc6870d00005ed1d823300024c804400000c0000b2b0f50001700000a410001c8c000000067000000021b0001e5805e89f05440007f04673bc800000008b0d49fa8e2d00000011b343c1600b3800000000000025242340005051aa53280005289f2cf9246350c05ac0003fd2dd20c0c8e5632910c88000a650000954e9675fa6400000003b10b7d61409238d00f23645e861425d805c14a73e21fa9cc6749061921d5430d337bb8a9b51586c107523e82ae32941919a05a50ab4af0000fa06321ff923400018989c8164e50456000000144000000024090e02a332f1f98bd453d0ac8d0d42276e46f1fa49d8538069134063e9e51d821b48b20430e5189930c2793729654a629dd51d80000006102b49a100000000001fda0002cc07580000006ff000123cbbb230106245806e3750d095d9244156043cf64ab611108c959470000f40a0c8e3bf0922eb8290ad308a18f08004bfa4640912fc734a600c1c0f02bc4df230948d1349df0215b9887c46e00005f8e582b700000000002073741d111b88c93e9077468e87b39c00005628b739d824122f0000f6902471c7b152fe7062e884508080000001b21fe55850508af2c722a401d0002e1000085081900000000006d031f87ba38e0003770ec945c27e000044c0001ff1b6800000082c284243000041d27389b00000e715415860000000000000bf800031480000baa7119b1e282ed00027c1c9803da5800000000000000d74fa800000023c000099641980d800000000004c94a42a283500003c400076b451da38cf89303cd18d44541aa800072e0001df53792aca4031500003ef2b21c50001c9400000000028993640004d383f000050007c1d98eb88871abd1d48c810b0b90d7ee121ec00027a0ab831726f1188fb40003ea49090366c953
  | 23 => 0x103c4fb1a21cc96cc4100000df182413a000212923000000000000006938c536f08d904100029427ea0004f94d126ad38496041ba4e54c954715813ac2107f110693e2ab70a4a1d06e42d20ed014a141240380af20ea65f07db06397dc4b21162550100c
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x9748754d52440156c904a9aa4880325da17764c910004bac2eec992200b9b684dd9324400136b09bb264880032d193764c910004f8c06ec9922000dc4329d932440012ef0abb264880325d215764c910004dbc22ec992200b9b4845d932440013cf04bb264880027ce01764c9100065a320ec9922000dc4321d932440013e700baa64880167c201754c910007a2196ca9922000e34641953244001e886432a6488003e10cb644c91002c7a432ebb02207d9f3805d7604400b1eb0fb2ec088012bc60365d81100071a326cbb022045c7687d9760440758eb0fb2ec0880029de1365d81100053ac26cbb02203ae7280d97604408bce301b2ec088002ade1165d81100355a422cbb022000e346419760440f956d0db26c0880038dd9764d81100071a32ec9b022043cb687d93604407196b0fb26c0880038de1764d81100071a42ec9b022038eb280d936044087d6301b26c08810fac5c364d811002c7a432e5b02207b9f3805cb604400b1eb0fb16c088012bc60362d81100053bc2ac5b022011a748558b604400156f08b16c08801aad21162d81100056bc1ac5b022047ad48358b60440896e50db2ec0880eb5c9db65d81101d7393b6cbb022000b7384d9760440016e309b2ec0881175cdd365d8110006b8ba6cbb022000f3064d97604400176708b2ec0880c6ec21165d811022db9430cbb022032e72861976044073ae4ec32ec0880e79c9d865d8110195b9c20cbb022000b71841976044089ae6e832ec0880035c5d065d811000798320cbb022038db387d936044087b610fb26c0881eaeca1b64d811019f59436c9b022038db276d936044071d64edb26c088003cce1764d81100079842ec9b022000f3365d936044001e60cbb26c088002dce1562d8110195b842ac5b022000bb38458b604406376108b16c088002f4e0d62d81103cde841ac5b022030fc0324cb60440198e8edb2aa088016dca0365541101c798286c8a82200597487549504400b6e100a92a0880327ca1f6054110026783b6c0a82200cb7285d8150440013af06baa40880b27520d75481101d7b0106ca9022000e34641952044073ec04032a40880e3e80836448110004bbc2ae6902200c974855cd204400b3cd0fb124088016f8a03624811002cf243aa49022005be080549204400b3c90e99240880b3711cd324811002df040264902200a9f287d8120440099e0edb02408802af8a0b6048110054f843aa0902200cd707554120440157c104a824088003d85495048110054f843a60902200abe0824c12044001f8264982408800a1f21774594103c47bc0ae8b2820048f4815d1650400b0f90eaa2ca080030fdd154594100161f3a2a8b102000c3d74551620400b1d90ea12c4080038b551425881002c3e43acaa9020058ec87589520400b1d90eb126408056b320d624c810
  | 1 => 0x4edb86c8880c7ac9db70d9110006d9baee1b222000f3375dc36444001a66ebb86c8880036c5d770d9110007983aee1b222000f3365dc36444001e60cbb86c8880036cdcb70d9110006d8b96e1b222000e346519362440014e90caa6c4880034ddd154d891005e9a3a2a9b12200a8f587d8f6244001d8865b1ec4880036cdd140d891005ed83a281b122000f315450362440192ed0fbaac4880025d6137558910004bb43ecab122000d3474d956244001aa8e7b2ac4880039918b6558910004bb438cab122000d34741956244001aa8e632ac4880167c203745891005cdb43ee8b122000d3775dd16244001a68ebba2c4881f26da1b74589100069bc2ee8b122000d3485dd16244001a6ecbba2c4880034d1977458910006d9c06e8b122000977855d162440192e90aba2c48800275e0d7458910164ea41ae8b1220009f3805d1624400136d0e3a2c4880034ddd474589100069a3a8e8b1220009b687d916244001a6eebb22c4880034d1d76458910006ca39ec8b1220009b6871916244001a6eea322c4880034d1d464589100071a328c8b122000d947319162440012ed0faa2c4880325d21f54589100069bba6a8b12200bd3474d516244109aa8e7aa2c4880025da1d5458910004ba43aa8b122000a74865516244001a6ee8aa2c48802f4d1d1545891041eaa39aa8b12202c9d687dcd6244001aaeebb9ac488003551d77358910006cbba6e6b122000d9474dcd6244001aaecbb9ac488003551977358910006cbb26e6b122000d9464dcd6244001aaea9b9ac488003555537358910006abba8e6b122000d54751cd6244001b2ee839ac488003651d073589101666a39ec6b12200a8f48758d6244001b88e7b12c48802e7921d425891000792aa284b122082dc473509624400b1e90db82c4880035cdd77058910006b83aee0b122000db374dc16244001b60e9b82c48800374dcf7058910006e839ee0b1220059f086dc16244001ae6cbb82c4880035c1977058910004f8c26e0b122000db364dc16244001b60c9b82c4880035cd537058910006b8aa6e0b122000de362dc16244061bc0c5b82c4880c37890b7058910006f0a16e0b1220009f2879016244001ae6eb202c4882075c1d64058910006d9ba480b12200bdb0749016244001ba6e7202c488203741ce4058910004f943a80b12200b9f0875016244001ae6eaa02c4881ff5c1d54058910006d9ba280b12200bdb0745016244001e62a8a02c48800374dcd40589103f6e839a80b122000fa142501624401736d09bb2a4880026d61376549100065a326eca9220009f180dd952440012ef0abb2a4880026de11765491005cda422eca9220009d7835d952440593a906bb2a4880027ce0176549100065a320eca92200a97687d9552440018eeedb2aa4880031d1db6554910055b3416caa92200a
  | 2 => 0xa42195100071a3248432a2000a778650865440014e90ca10ca880034d5d142195100071a3228432a200c9768710865440012eb0e210ca880038d19042195101cdb94008432a2000b71801086544001c68c9190ca880325da1c3219510004bac386432a2000a76860c865440014eb0c190ca88002cda1032195100059ac206432a2000e34640c865440736e500190ca88002dc6003219510064bb43e8032a200097587d0065440894e90da00ca880034d5d340195100071a3268032a2000b72869006544073ce50d200ca880eb5c9da401951040f393b48032a2085b71849006544103ae6e9200ca880035c5d24019510007393248032a2000e70649006544001e60c9200ca880038c19240195100053bc328032a2000a74865006544001a6ae8a00ca880038d1914019510005b84328032a2000e708650065440014e10ca00ca880035c9d940195103ff393b28032a2039b73845006544073e6708a00ca881ff5cdd140195103ff993a28032a2000d717450065440ffe62e8a00ca880034c5d1401951000799b228032a2000e72645006544001ce0c8a00ca88003cc191401951000799a128032a2000f31425006544001c68c9900ca88002ada1b75d91100059b436ebb222000e3686dd7644400146d0dbaec8880034d9db75d91100071b3b6ebb222000d3570dd76444001e60e1baec8880032d9da75d91101c5d9404ebb222000bb1809d7644400176700baec8880e2ec20175d91100055b430ebb222000cb6761d76444001a6aea3aec8880034da1c75d91100059b430ebb222000e36861d7644400146d0c3aec8880034d9d875d91100071b3b0ebb222000c36761d76444001e60e03aec8880034d9db65d91100071b3b6cbb222000f3070d97644400136b0f32ec8880032d9da65d91100059b42ccbb222000e376599764440017630132ec8880026de1d65d9110005d9c02cbb222000cb676197644400166d0e32ec888002cd21c65d91100059b430cbb222000e36861976444001a6cec32ec8880038d9d865d91100061b3b0cbb222000f3070197644400156d0db96c8880034ddd772d91100059b42ce5b222000b35859cb644407176501396c888002ec60272d91100059bc2ae5b222000b34855cb6444001a6eeab96c888002e5e0d72d9110005ca41ae5b222000bb3805cb644407176100b96c888002ada1872d91100059b42cc5b222000b358598b644400176301316c8880026da1c52d9110004dac38a5b222038bb28014b644400176300296c8880026da1c32d9110004dac3865b222000ab6860cb644400156b0c196c888002cda1432d91100059ac2865b222038bb2800cb644400176300196c88802eada1b70d91103d65b3b6e1b222000d3775dc36444071b650fb86c88802eeca1b70d911021f59436e1b22200bab286dc364440f5b6
  | 3 => 0x5b2a2044c7676dc36544075ae4e1b86ca880331d9d970d9510004bb43e81b2a200097587d036544001a6ee9a06ca88002dca1a40d95101d73943481b2a2000d73749036544001ae2e9206ca88003cc19240d95100069bba281b2a2000b70865036544075e6708a06ca880035cdd140d951000799ba281b2a2000d33745036544001ae2e8a06ca88003cc1d140d951000799b2281b2a2000f30645036544001e6684a06ca88003cc50940d951043cba42ee8b2a200b9b687dd16544001a6f0bba2ca880034d21774595100069bb2ee8b2a2000d3465dd16544001b6701ba2ca880023de197459510004bbc2ae8b2a20009f3805d1654400136d0e3a2ca880032ddd874595100069bba8e8b2a2000e346519165440172e90eaa2ca880029d21954595100069bba2a8b2a200bd34745516544001b66e9b82ca880036c1d37059510006b9b2ee0b2a2032d7065dc165440013e309b82ca880036c1937059510196b9aa6e0b2a2000d7154dc165440013e50f202ca880036cdd2405951005ed83a480b2a20009f28750165440173e10ea02ca880036cdd1405951005ed83a280b2a2000f315450165440198ed0d3b0ca880025d61276195100063a432e832a200cd37845d065440238eec0ba0ca880025de1f64195100069aba6c832a20009758799065440016e301320ca880029d61e64195100063ac3cc832a2000a768499065440018eee9320ca880031d5d264195100053ac04c832a2000e718099065440012ef0eb20ca88002dce016419510064bb438c832a2000975871906544001a6ae8320ca880038d5906419510005b3410c832a2000b658219065440014ef0e320ca880029d61c64195100063ac38c832a2000875871906544001c6d08320ca880031ddd064195100071b3a0c832a2000c75741906544001c6ae8320ca8800399a08641951000732c10c832a2000e71801906544001a6b0e320ca880038d9d8641951000793410c832a2000f25821906544001e6300320ca880038de1c64195100071b438c832a2000e3587190654400186b0e320ca880038d21c64195100071bc10c832a2000e36821906544001c4d04320ca880038d608641951000712c10c832a2000e34821906544001c6ee4320ca880038d9c864195100071ab90c832a2000e34721906544001c6f00320ca8821b8da0064195100071ac00c832a2000e3180190654410dc6900320ca880038ddc064195104371b380c832a2000e3570190654410dc68e0320ca8821b8d88064195104371a100c832a2000b3684988654400166b09310ca880038d1926219510005b8c04c432a2000e346418865440192ed0fa10ca880025d61f42195100069aba68432a2000e3464d0865440016ad07a10ca88002d560f42195101cdb94068432a2000b7180d0865440014ed0d210ca880029d61
  | 4 => 0x2440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bea9b9ac4880031755373589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100066639ee4b1220028ec875096244001c5aa8a12c488223331cd42589100145f426eca9220008bd84dd952440010ff0abb2a4880022fe1176549100145e422eca9220008df835d9524402b1b906bb2a48800e1f214765491000c3f43ecaa922001a6e82d95524408b8e8e3b2aa4880163da1b71549100063bb2ee2a92200b9b684dc5524400136b09b8aa4880032d193715491001c3f42eec992200087d85dd9324400517d09bb264880022f613764c91000666194ec992200087f855d932440070f90abb264880022fe11764c9100145e422ec99220008ef825d93244001998643b26488003930cb654c91000746196c899220058f686dc532440192ed0bb8a64880025d617714c91005cdb426e299220009b584dc53244001968c9b8a64880032d192769451001d3b436cb28a2000c7676d965144001c68cbb24a28802a5de1d52945100053a432a528a200ad667254a51440758f0e1b2aa2880eb1d1db65545101c65a3b6c8a8a203ad73751c15144001c68c832c42880b23d61f638851000d72412c710a20058f4865d521440758e8edb2a42880039918b65485101ce3a3b0ca90a2000e34641952144071968edb2242880163d21973485101666a39ec690a20018f48758d214408b8e8e3b2aa0880032d193715411002c7b436e290220008f686dd36544001a6ea9ba6ca880029d61a54d95100069aba4a9b2a2000b718095365440172ef0eaa6ca880034d5d154d9510006d9ba281b2a200bdb0745036544001e64a8a06ca88003cc55140d95100053b436e9b2a2000c7686dd365440018eced3a6ca880eadca0274d9510005b8c04e9b2a2000d37845d365440014ed0c3a6ca880034d5d074d9510005b3410e9b2a2000b65821d365440756e5003a6ca88002dc60074d95100069aba6c9b2a2000e376499365440016e301326ca88002dce0164d9510064bac38c9b2a2000d357419365440016cd04326ca88002d960864d95100069ac38c9b2a2000f26821936544001e4b04326ca88003cc60064d95100059b424e5b2a2000b35849cb6544001acee5396ca880eadca0272d9510005b8c04e5b2a2000a76861cb654400166d09316ca88002cd61262d9510005b8c04c5b2a200097687d0b65440012eb0fa16ca880034ddd342d9510005ab41e85b2a2000b5583d0b65440756e501a16ca88002dc60342d95100069bba285b2a20009768710b65440012eb0e216ca880eadca0042d9510005b8c0085b2a2000976870cb65440012eb0e196ca880029da1832d95100053ac3065b2a2000b36840cb654400166b08196ca880eadca0032d9510005b8c006
  | 5 => 0x81129e21940195100069cba28032a2000a3e86dd7644400187cedbaec8880034d9c775d91100069a38eebb222000d3b70dd7644400147d0c3aec8880030f9d875d91100061f3b6cbb222000e3581d976444001c6ce3b2ec8880038d5c765d91100045ec3ccbb222000a3e85997644400117f0eb2ec8880028fa1865d91100061f3b0cbb222000e35811976444001c6ce232ec8880038d5c465d91100051f42cc5b222000a3d8598b644407136d0fa8ec8880026d61f51d91101c55b436a3b222078cb676d476444001c6ecba8ec8881eb2d9d851d91100071bb28a3b2220389b687c87644400136b0f90ec888002cda1721d91100059ac2e43b222043ab681dd7644407156b03baec8880038da0775d91100071ac0eebb222000c3e71dd76444001c6ce3baec8880038d5c775d91100061e38eebb222000c3f70dd7644400187ae1baec8880028fa1675d91100061eba8ebb222043ab6811d7644407156b023aec8880028fa1c75d91100061f438ebb222000e36811d76444001c6b023aec8880038d9c475d91100071ab88ebb222000c3f75dcb644408756d03b96c8880e2ad60772d91100051f42ce5b222000a3d859cb644400147f0ab96c8880028f21572d91100061fbaae5b222000a9f835cb644400153906b96c88810eada0472d91101c55ac08e5b2220008be8714b644400117b0e296c8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c88810eada0432d91100055ac0865b222038aba800cb644400157300196c8880e22fa1f51d91100045ec3ea3b2220388be87c87644400117b0f90ec8880028fa1721d91100051ec2e43b22203ac7571d9762440738eae232ec4880e32d5c764d89103e65ab88c9b1220058f581dd3624410f8eae3aa6c4880030fdd154d89100161e3a2a9b12208bc757155362440750f90dbaac4880021fa1f65589100061e3a6cab122000c5c73d9562440010fd0e32ac4880030f1d065589100062e398cab1220028be86dd162440711790dba2c4880030fd9774589100061e32ee8b1220008be87d91624400187eebb22c4880030f1d764589100064e39ec8b1220008be87191624400187eea322c4880030f1d464589100064e398c8b122000c5f65dcd62440018b8cbb9ac48800327d9373589100064e326e6b12200387e87dd562440010fb09baac48800a2fa1f74589100061fbaee8b122000c3c75dd1624400187f0bba2c4880030f21774589100043fc2ae8b12200387c855d162440011bf06ba2c4880563720d74589100045f438e8b122000c3f751d16244001878ea3a2c4880021fa1f545891001c3e43ea8b122000c3f74d516244005878e9aa2c48822b171cf54589100043f43aa8b12200087c87551624400187ee8aa2c48800b0f1d1545891044e2e39aa8b1220158de87dcd6
  | 6 => 0x663b3b683b2a2000e3764d0765440756e501a0eca880038d19241d95101d53a43283b2a20009768710765440192eb0e20eca88002d9a0841d9510005b2c1083b2a203ab728010765440752ed0f90eca880025d61f21d95100059b42643b2a2000b3584c876544001c70c9206ca88116dca0640d95100079920c81b2a2000f3041903654408b4f10ca06ca880034edd140d951022d3b40ee9b2a203aa7581dd365440018ed03ba6ca880031d60774d95100061fc22e9b2a2000c3d741d365440014dd043a6ca880029b60874d951022d3b408e9b2a203aa75811d365440754f5003a6ca881169e60074d95101d53ac0ee5b2a2000a3e849cb654400147b09396ca880031bdca72d951022d3b408e5b2a203aa75811cb65440010fd0fa16ca880021f61f42d95100061fba685b2a2000a5e83d0b65440014bb07a16ca880030fdd142d95100043f43885b2a200087d8710b65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb654408b4ed02196ca880029d60432d95101d53d40065b2a2000a79800cb654400147f08b8eca880028f21171d95101ce3bc3ae3b2a2000e37845c76544001c6908b8eca880031ddd171d95100063aba2e3b2a203a87e87d0765440010fb0fa0eca880ea1fa1f21d95100043ec3e43b2a2000a3e84c87654400147b0990eca881161fa1f40d95100043ec3e81b2a2000c3f74d03654400187ee8a06ca880030f19774595100145f43ee8b2a2000c3f75dd1654400187f0bba2ca880030f21774595100043fc2ae8b2a20008f7815d1654400117d0e3a2ca880030fdd474595100143e43aa8b2a2000c3f745516544005878e8aa2ca880032d1d371595100043ec24ec32a2045c76819d865440758eb033b0ca880021fe1f64195100061eba6c832a200087d8799065440010ff0eb20ca880029de05641951001c3f438c832a200087d87190654400187ae8320ca880029ba08641951000536c10c832a2044a7481190654400187b0e320ca880038ba08641951000716c10c832a2086e37811906544001c6b02320ca8821b8ddc464195100071b388c832a2000e35711906544001c68e2320ca880038e60064195104371b080c832a2086e3410190654400147d09310ca880028f61262195101ccbb43e8232a200097587d0465440734ed0da08ca880038d19341195101cdb94068232a2000a76869046544001a6ae9208ca880038d19241195101cd3a4328232a2000e346450465440192ed0e208ca880025d61c41195100069aba08232a2000e346410465440016cd04208ca88002d960841195101cdb94008232a203997687c8465440012eb0f908ca88002cda1321195100059ac264232a2000e3464c846544001c68c8108ca880038e1924019510225b940c8032a2000f32419006544001e6083200ca8
  | 7 => 0xbd841d9534802b0f90eb2aa6900569720d6554d2000536432a6a924000bc9831c1524800b1d90cbaa6490056b3a1b634c9200161f3a2a9b0a4000c3d74553614800595ce8a16c2900038b55142d85200047bc3ac230a4003a6c8654a51480018dceca94a2900123da06768c52002cb643aa4a824005a6c86549504800b6d100a92a090002f2e0d528c12002d66432649824001ccc764c9304800b791009926090003d254d524c12002de5432649824005bc8864c9304802bd910c9926090007729d9324c1200af643b2649824001cc8764c930480017970a9926090002f2615324c120475e5c2264982408ebc9844c9304811be96a89926090237d2551324c12002c7a40ae8b2e200487c8755165c400187ee8aa2cb8800b0f1d154597100253a40aa8b2e208bc747155165c400b1e902ba2c58821f1d1c75458b100061fba2a8b162002c3c7455162c41178e8e2aa2c5880123b21d4258b1000716aa284b16200187d85dd952c400517d09bb2a5880022f6137654b1002c7b40eeca96204fc7651dd952c400b1e902bb2a58813e5d6177154b10034db426e2a9620009b584dc552c40070fd0bbb265880021f617764cb100145f426ec99620008bd84dd932c400b1ed03bb265880163d205764cb1008cbb42ee2996200097585dc532c400d36d09b8a65880026d613714cb1023c7a43ac690e208797485dd165c40011ef0cba2cb880125d21d54597100253a432a8b2e2000d377455165c400da68e8aa2cb880034ddd15458b100369a3a2a8b1620108f48758d62c40093c90ea12c588003c95514258b1027cbac2eeca96204fc7765dd952c400d36d09bb2a5880026d6137654b10084ba43aa6a962010b648254d52c40232ed0bbb265880025d617764cb10034db426ec99620009b584dd932c400b2e90ea92a18800275e0d754831023cea41aea9062000977855cd20c40232e90ab9a41880167921d524831002cf243a649062047dc4734c920c40213e10e9824188003f04c9304831002c3e43aa8b2c2000c3f74551658400587ce8aa2c5080030f5d15458a1002c7643a84b142000e2d54509628400b0f90eb2aa5080163b21d6254a1002c7643ac49942015acc8358932840f996ae2326ca880030fd5374d95100247b40ee9b2a20058f581dd3654400187ae92a6ca880029d60654d95100053cc04a9b2a200287f87553654400187ae8aa6ca8822f1d5c554d95100061eba6c9b2a200c87d87193654400187ae8326ca880029ba0864d951000536c10c9b2a2000c3d871936544001c5d04326ca880038b60864d95100071ac08c9b2a2000e36711936544001c7300326ca880028fa1262d95100051ec24c5b2a2039c76765c7654400166f08b8eca88002cd21171d95100071a322e3b2a203a97687d0765440012eb0fa0eca880ea9da1b41d95104
  | 8 => 0xebba2c3100e32ddc374586200053b42ce8b0c4000a75859d161880018e8eb3a2c3101f2ada1274586200053bc2ae8b0c4000a74855d161880014ed0a3a2c3100029d61474586200063a3a8e8b0c4000ad6831d161880015ab063a2c31002ab9a08745862000572c10e8b0c4005af2801d161880015e3003a2c3100e2ada1c74586200065b438e8b0c4000e36851d16188001c6b0a3a2c3100038ddd474586200065b3a8e8b0c4000cb4751d16188001c68ea3a2c3100030d1d474586200074b418e8b0c4000e95831d16188001d4d043a2c310003a960874586203e759400e8b0c4000eb1801d161880f996ee03a2c3101f32d5c074586200053b43ea8b0c4000a7487d516188001c6ee9aa2c3100038d1d354586200071baa4a8b0c40008f78755161880011e90eaa2c3100031de1d54586200053b43aa8b0c4000a748755161880018e90eaa2c3100021d21d54586200071bc22a8b0c4000e37745516188001c68e8aa2c31023f8dd09545862047f1aa12a8b0c408bc777055161881178eae0aa2c31022f8dd01545862045f1aa02a8b0c4000a76859cd61880014eb0b39ac310002ada1273586200055ac24e6b0c4005af2809cd61880015e30139ac3100029de1573586200053a42ae6b0c4000ab7845cd618800156908b9ac310002b9e0973586200055b420a6b0c4000ab58414d618800b5e50029ac310002bc60053586200053b42e86b0c4000a7585d0d6188001c6aa9a1ac31002ab9a0b435862000572c1686b0c4000e355450d61880014ed0a21ac3100029d614435862002d7940086b0c4000af18010d61880074e90ab0ca3100022fe1176546200145e422eca8c40058f487585518800b1eb02bb463100163d207764c6200043fc2aec98c400387c855d9318800117f08bb2631000a2f211764c62002c7a43ac298c400ace47258531880091ed03ba6ca900023d60774d95200143fc3aa9b2a4002c3e74553654800187ae8aa6ca900029d20554d952000536c14a7b2a40008bf845c7654800517908b8eca9000237e0d74595200ac6e41ae8b2a40008f7815d165480091e902ba2ca9000a1f21d54595200061fba2a8b2a4089c5c73551654802b1bd0fb9aca9000317d5373595200062eaa6e6b2a4000c5f751cd6548001998e7b92ca9000b0f9d154d8d200061eba2a9b1a4000acd82d4f63480051bf0ea1ec6900038755143d8d200043fc2ae3b1a400387c855c7634800117f08b8ec69000a2f21171d8d2001c3f43eeab1a400087d84dd5634800147b083aac6900021fe157458d2001c3e42ae8b1a40008f7815d163480091e902ba2c6900021fa1f5458d2001c3e43ea8b1a400087e8755163480010f90eaa2c69000b0f9d15458d200061eba2a8b1a4000c6c75dc963480010ff0abb2a6900023be097654d200145f420eca9a40008
  | 9 => 0x72586500055bc22e4b0ca000ab4845c961940015af06b92c328002b520d72586500653b42e84b0ca000a7585d096194001c6aa9a12c328002b5a0f42586500056ac1e84b0ca000e355450961940194ed0a212c3280029d61442586500047b43864b0ca0008f5870c961940194ed0a192c3280029d61432586500055b42064b0ca000ab5840c96194001d8a64192c328016bca00325865000578c0064b0ca0058f5815da219400b1e903bb243280022fe1176486500145e422ec90ca0008df835d9219402b1b906bb243280163d21d61486500663a3aac290ca000c3f7455362540014db0b996c4a80061f21571d89500045fc22e3b12a0028bc845c76254001998653b264a800a2fa10764c9500045ec20ec992a000ccc321d9325400b0f90cbaa64a800b0f9d154d85500061eba2a9b0aa000a7585d0761540014eb0a20ec2a80038d55041d855000578c0083b0aa0008f787584615400156908b08c2a80023de0574596200247a40ae8b2c400587c87551658800187ee8aa2cb1000b0f9d15458e200061eba2a8b1c40058dc8750d6388001c3aa8a1ac7100161f21d6554e2002c6e43ac6a9c4000e375495261880011ef0eaa4c3100123d21d54986200063bc3aa930c4093c74875526188001c6f08aa4c31024f8ddd1549862049f1a3a2a930c4092e37425526188125c6a84aa4c31022f8dd01549862045f1aa02a930c4000ab68414e618800156b0829cc3100029da1743986200053ac2e8730c4000e3554d0e61880215cd05a1cc310002b960b43986200071aaa28730c4000a768510e61880014eb0a21cc31000e1fa1f75586200043ec26eab0c403ac7581dd5618800517d0fba2c3100030fdd774586200061e3aee8b0c4000c3f85dd161880018790bba2c3100e32d60774586200043fc2ae8b0c400387c855d1618800187eea3a2c3100030f1d474586200043f43ea8b0c400387c87d51618800187ee9aa2c31000b0f1d354586200043f43aa8b0c400087c87551618800187ee8aa2c31000b0f1d154586200055b426a2b0c4000ab584d4561880f1968e9a8ac3100031ddd4515862048e5a3a0a2b0c4000a7685d0561880014eb0ba0ac3102331d1d741586200165a3a482b0c4000e3554905618800b1e90ea0ac3100029da1441586200053ac2882b0c4090c7475105618800196ee820ac3100038d55041586200056b41882b0c4000ad58310561880015cb0420ac310016bca0041586200053b42e62b0c4000a7585cc5618800156d0998ac310002ad61331586200053ac26eab0c403ac7770dd561880734ed0b3aac310002ada1275586200055ac24eab0c4000ab7845d5618800156908baac3100ea9da1c75586200063b438eab0c4000a75841d561880738eee03aac3100038de1774586200071a42ee8b0c4000e3775dd16188001c68
  | 10 => 0xb1c4200e1d5450d638842b0fb0bbb2a71080a2fa137654e210045ec26eca9c42058f581dd16088529ce621aa2c1108030fdd154582210161e3a2a8b044293e731055160884095e503202c1108123e21d40582210071caa280b044205cf17150160884031eb03ba6ca9080a1fe1d54d95210061eba2a9b2a42008f7815d165484050f90eaa2ca908030fdd154595210161e3a2a8b2a4200c3f745536348405878e8aa6c69080a37e1d43d8d210070eaa287b1a42008f7815d1634840187ee8aa2c69080b0f1d15458d210145f426eca9a42008bd84dd9534842b0fd0fb2aa69080e37a1f6354d2102c7a40ae9b024200c3f745536048405878e8aa6c0908038b55142d812100578c0463b0242108f4874c760484619e2e3b04c0908023ee1d60181210161f3a2a8b14a000c3d7455162940014e902aa2c5280163b21d4258a5000716aa284b14a0058ec87589329402b59906b1265281e31de1d549865049e3a43aa930ca087a77845526194023c6f08aa4c32824f8ddd1549865049f1a3a2a930ca08be37405526194117c6a80aa4c3280469da1742986500053ac2e8530ca000e3554d0a61940015ad07a14c328002b560f42986500071aaa28530ca011a768510a61940014eb0a214c3280123da1c32986500047ac386530ca011a76850ca61940014eb0a194c328002ada1032986500055ac206530ca000ec5320ca619400b5e500194c328002bc60032986500061faa6e8b0ca0028be87dd1619400187f0bba2c3280030f21774586501c65ac0ee8b0ca000c3e51dd16194001878a3ba2c3280030fdd154586500161e3a2a8b0ca045a748155161940014eb0ba0ac32800b2d1d241586500071aaa482b0ca0058f48750561940014eb0a20ac3280032ddd041586500071aaa082b0ca000ae68210561940015cb0420ac328016bca0041586500053ac2e42b0ca000ab684c85619400156b0990ac3281169d21774586500071baa6e8b0ca000e3785dd16194001c690bba2c3280038d1d774586501c65bb86e8b0ca00ca76859d161940014eb0b3a2c3281f2ada1274586500053bc2ae8b0ca00ca74855d161940194ed0a3a2c3280029d61474586500071baa0e8b0ca000ae6821d161940015cb043a2c328016bca00745865000578c00e8b0ca038ab6871d1619400196d0e3a2c3280038da1474586500071ac28e8b0ca078cb6751d16194123968ea3a2c3280038d1d4745865000753410e8b0ca000ea5821d161940f9d65003a2c328003ac60074586503e65bb80e8b0ca07ccb5701d161940f18ef0eaa2c3280029d21d545865048e3a43aa8b0ca087a77845516194019c6f08aa2c3280038ddd154586500071a3a2a8b0ca08be37405516194117c6a80aa2c3280329da1672586500053ac2ce4b0ca000ab6849c9619400156b09392c3280029de15
  | 11 => 0x801803002400000000802001802800000401800000800800c00000004000000800001400405800800c01000001400800402000800000802000800400c04000000c00003800800000001402000000000000400800003c00000403400c00000000002400400401402c00400401002402000001c02400803400800000400000800800000402800000804c0000100080740100040400187ee8aa6c6a90029d20554d8d520146fc3a87b1aa400e1d5450f63548032dd0fb92a6a90061f61774d85520045ec3ce9b0aa400c3d759d3615480187ea8ba6c2a900a2fe1d74d85520061ebaae9b0aa400c3e855d3615480187b0aba6c2a90032de0574d85520061f28ae9b0aa400c3c515d3615492b0fb0eaa6c2a900b0f9d154d85520061eba2a9b0aa44fa748155361548014eb0ba0ec2a90029d61441d85520065aba083b0aa400e355410761548015cb0420ec2a9002bc60041d85520047bc3ac230aa4008f7815d360548091e902ba6c0a90030fdd154d81520ae2e39aa7b02a4008fb8758060548091ed03ba6ca990023d60774d95320143fc3aa9b2a6402c3e74553654c80187ae8aa6ca990023de0574595320247a40ae8b2a64008fb805d1654c80b1f100ba2ca9900a1f21d54595320061fba2a8b2a6400a7481551654c80517d09b8aca990022f6137159532006a6192ebb0a6400d8c325d3614c8070ff0ebaec2990021fe1175d853201c3f42ee9b0a640087d85dd3614c80117b0f3a6c2990030f9d674d85320061ebace9b0a64028bf875d3614c80187ceaba6c2990030f5d574d85320061f42ae9b0a6400c3d855d3614c80196f02ba6c29900e1fe1f54d85320043ec3ea9b0a6402c3e74d53614c80187ae9aa6c2990021fe1d54d85320043ec3aa9b0a6402c3e74553614c80187ae8aa6c2992331d9d741d85324863b3a883b0a6400cb574107614c801c6aa820ec299002b960841d853200578c0083b0a64008f787584614c8011ef02ba6c0990123d20574d81320161f3a2a9b026400c3d74553604c801b886538cc099003710c97198132006a6196eab026400d4c325d4604c801b1864ba0c099003710ca7118132006e2192e230264008fb87580604c80187ae8aa2c5288123b21d4258a5100716aa284b14a2028be84dd9329440117b09bb265288030fd5374582510247b40ee8b04a200c3d745516094527ce620aa2c1288071b9c9525825127f39882a4b04a204af28190160944091f10ea02c1288038e55140582510061fba2a9b12a202c3c7455362544010fb0bbb264a880a2fa13764c9510045ec26ec992a28c8f7815d3605440187ee8aa6c0a880b0f1d154d815119678b8ec1302a2008fb8758060544091e902ba2cb108121f21d54596210061fba2a8b2c4202c3c74551658840187ee8aa2c71080b0f1d15458e210246e43a86
  | 12 => 0x1bd06f27e0a29340000df9c09148b323ba781e101894e1c200000008991e8000000e54000000878e830e80000000000000015682d00011b0961490000bba969ca0000000001d7003a9c96e8e180032d9256d59b61be00030b0000000000c38c98003051b023d84012bd738d64001ae93c288a4d99c8b893f8e609018f85714769507723e128a16995a2397f8679c324d03c24671721a80532698a85c8cc2b38130002e280c1aba99aab1c900023c1409c5acc00002529aa8d800000212ae400026daa48002f20be9da800329a9480031c9fb22f80004d00004e1570b28000001590000002df0000000001888d41ad24680025d8e91cd8721a90000002328203189e26bc2f924e3301220002d6913a8b8b51710000000002b02d40000000001ceb2922593010d868000007001c00400001401000c00c02801c01400400003400402401000801400c01c04804000002800003005c01c00000401c00001000800801001c00000000804c00800c01c04400401001c07400000000002c00c01800001402001c05c00802400000000c02000001800400800400000000000000800002c00000002000000404004c00400002000800405000800000000402800400000c00400004c01800400001c00002401400000400800c01800000002403004000402c01800800000001003c00400000c02800401401000800003800000400000802400800000400003400801c01c00000003001400000000407401c02800400400800800000c00000801001800000000400000c00800000801000000003002000c00000c03000000c00400800c00000400400001000c00401000001005c00800000000000004400000401800800400c00c00400001800000000400801400800805c00000001c00800c00000800800800001800000402c00000403004000800400c00001800c00001001400802c00001800002403000400400401801800400004c00801400400801000000403401800c01000403401000c02000000c05800000800c00000400800000000403000400401000000003c01800000000001001400400400000400000800800c00002402c00400c00400002400003c0040000080680080400000380080000200040380000000000140240000780300000080180000080540140000a003000000000000007800000000001c00400406001c00c00001000405000c00001000400800c00801c00401c00c00801402405c02804010403801c00409c00000400000c00000001005400001400002c0c803c00408402400400400002c01802c01000001800004c00800400400802400801800409c03400800000402800001400001400c01000002800401c0000000180080180040240b002800000000001000805801000000000c00000000800001401001c00000000
  | 13 => 0x50002908002ae8000000001f70148458a705d8002bc96c0ce6250000a59d5acd80013b0000000000003120000dd80001794c0002810ee80e2980479c400021ed8c00000021e05aaa39438000000000001962c800015a2410f81980000068003159f31bf80000009c8aaa8380003724a192a85a3a20aa8d1412832278b11ee9a519996900026e00025d0359fa1be8000000450e203500000000000000000000000014e8001a40f12cf80000000020185b91f1ba9bda5f86fc0000010b8860000932729972248000a40e280002324a98b16b9aa80020c3338c096421326ba5523f29619413992017f27c2f13310f30472262ce9771cb30c094b0f0000fa055a749bc12c092876800005a189e609c40000000007e2ffaad8000000000000e5065a13aed0d084c8000001d49829501f29ba00031a13967a86a9f38e88000548882c89870002a000000027400007800000018589080000012f800000000000000000000000286a6f0440000818000000002a61af263215ae5b1e90788e93e2470268000001068fe8f014a9e380015c00000026c10e0000002408000000c10001819702340000000000000000e40001edd7a00033580014a26f9f612e26c80020987119d1012d621812425c92c9268b6a818d80e84f5af310080080a9f1ac48000000000000001a89ec80000012083ba97ac08002508002ec0000000000000000000ea1621ef89a9d53071af8000000000001b640000000000031195f0000000000000000000000000000000000000000002f395da721bb0000003278000799b78e080017c91d980839ad28000000000001a611200021f8000cd0000000002148000001d08000000fd0000000000b080029f0002860000ff12b6209c78000c800006999a8002fa80013a1d680e9e89e50000eba8087c99524ea820c28b80001a7952ad900007b0002df80007fa142ae1788ad00015516f1d30df40421721232005e9932a58000a200005192794980000000030384b8000003288000000000002a12c39c6aa42cb93f25922d01f3350761ed22c9b703d07badea769181f81471e285080017b9e70448001610000002b7852b2bab51ce00caa32a29b193e8ac1f41168d3089086a6882a1ad88661b1c53340002010000001160000002f8afe00000000000000000022e0000aa00000012b8bd0bf8000000002c19fb80011507003f8001d195e0001b500000028c00030580029f8002198000000cd8000000000001e58003360000001b90003089261ae1ff8a623485500000221f00000016531397e2b5b320000002970000001d01ff2b98b6064810ae188485b1ec3142bf63ea008b38418378decc002e8002c69a186eabe96e0918f08000000dc1da2d0000034ad98000262bb8fe2432d8a65880000310138a41863a58ae72cc80000000025c0000000
  | 14 => 0x2d7800000179a578cc7040b014f8001e980011bc6f8fa8001030ed1630000000129b82a99860e1ee99d90000dd6d50002ea85c2b089e8000f18000000000000002cf41196815395c9fe233221c7c00010a9de00a1453318002271b38000003090211923069939c88331db00000025400016db2d1854000000000000000b480000000000018e12d00013227ba4f14b9a4ac542093cca92030ec90a0000002db98900022d5c104eab917aaaa2f8124c000f90e0053176210a840003079a58000000cadea80000180000010f0000001f998499da2da49ad380020826610984388b8002f1b1240016b29d9bc8000001ee11aa092560000000001a2d0e9b98002ab8f3b0b8d893d9460cf0000000e5c8d8b2c001910b20000001f59ea0000000000000002f5a668000002f78f4acf2f2a77af4afc8d7cdc8a82c72672f63242702ba2e6acb06bb228db06d1e48000002da8000ce9db80000011026780000000301f80026931f80026a0a88d39649d10000ad8000002708000000000158140d540028980000000021d2f72bf0000001a80d013902580007080000003a1d844a1a6e2920c92ea95afb15baa18002cec002e80ce1359ca96f800098c0025f000000172309874a7d1228cf8a08490a384c0301a2ab2ee91df0e68dd1659ccb36a4ba6b0048de4e98d5877b2c2ef1ef2b885fadc21c86402a94028019889827b1dd8f7800304a3100008a8318660da0caa51941af421c11c8992f5162afe9662601900cb146a4c9c700003cab1400255b34b238c8800210242a46c48b199e30e3abd0001cd00020000011300032521e40000030626090922a00000000f09b8001cb873080ae52bdb30b263112761d8a9224b0a30c60b79f8987ab1a0da6480004f29880014803393780000016a29182b1fc8582be1a699e20d1750000280000000fb0c40000080000000f23000002fc04803080000000019b80026110ae0e9edaa929b80026d0001311e0800073827ad1a513150a030c95892b1440840bb09c2359b888f27512a01902f8e324601c09121a0cb93ba990a516010a50503930a26401a87f2bb00024220b0e71579e42aa869132a770de96689d8acb331a670217d90b2a780ba05b169219b10ed637a7f0139f531c1698de00003b0fc0729b2ae022e829093acd1b317480000d000000000000228aeb9b3dd20002520000000002a69cf8000000608000000620e58199a0126e85068a226a645d024000268044c000002c20000651ecc000b180007d80017d00000031e1488000001778000000d98000000000f880000010d30e01ea016a53208000000ea9638000ddc028001599082dc8239dd085df6a4f8bca790598e15111d8e281308d10b93258d228a8d3f12ab409b0002c90000000001b0a2a8e0c002368002ca0000001374001a30001a200001b87
  | 15 => 0x100007594b1238001cf12980618e8edea22938ab8fbb0186d8e06732232bfcc20852c2a910542eeb132ee06c0dff2e01732f2719b4497a531793232f98ef8000000c4aa719c0ba80025a01140011d0830d788f8000002308270000000110ae0289a08d480028fb2711c15d1eb00015e8001cc0000002e38f719b000324ab69de80008c2e0adf6c780012a8000002e60a680000000000004a8002488002d080000009527e8003190002300001908810000af86007a1b200000009e03db1d2e4b2ca9b16a9522ddd9a041145aeda5b85206b2c602b857a61aa88be2049259510329e685a10227d8855d4161a0226280fa759880001c48ef03e8001581990382d4a3fa3d0000742de00728a181db498f2fdb109531349548002179fd00013a8000001810000000002ac9688001df80011e2b30002160002a0a0e00000004f9821f01782c428c8002c4e1f5670fd918b1f1c8000150ab732a2241e92d70ca0b5a6392d86c8218000c1b14a829732d122007aae20db9c39c1a879a34858000000000f52b200030a96d1a72c1183a338000d680022100017c0000cfd768922e327f9ac14d2b826530825493811b8000002f08000002479729249acafd31a8a118d0000a780025e80000001a1292932c3078ad201e0f980020f8000000968002ca846a269608cc8000000000002ea0500000c512f3029019d817b0002380151280ec18a142974008a3b02c1919d61850003161c60169088e7d1080026e8000001070000000ba2fb8001718000001fe80000000000000000015b1a98002f00000001319e80628076362150091f100028e90385e01d040a7c9b5e0897e80002f16c858aac0d500980b2ef8e4aad0000000eda7380000000001c9b4000083b210001128000a98000f403ec000000001558d703a94204d88a1ee55615a800000000186a39095888adb1679f9238a352c5aec9708bd82999f24423990006100010c2b60af0ab0bf1d78000001e000025e0002ff1f49f79432438000000001e1a07aaf00006304b0d2a788c3007a2b86728b0001c00000c718328f1170002028ff8000e100000000020a0000000000000000388002698000000da97587e80011198c9fa8df0002ba8000001190001968b9b1780000032ea3180000014f3328000000002ce00021180000029e02d80000002c80000000008b03100000000013ca501141b685610600000020500032f9360f681200031b02e0002afab280000025980000000027a0001bbab100000021e8829898fc9d398d8001fd80000d84980022b28480000000006e2eb2c531d8000180f280008728e252ada0c580000000000000025804200022285111e5fc0002710000618c789703f0eb10f8c90c6a4900005f1d280000032210ca9a00000000000008c8d622999f9210003280000000002539c9859
  | 16 => 0x1842dd89f80000025a80001d80010580000000000000011f800000135000066b0100009a2870a49270002928000001a380000000003200024000000000023a8000001048001a100000000011980026200029e8002f68000000000000000000001028a1917a1dab4800151afa0b70d35ab0340d195f8bc08d0718002dd2451f20000790001e780021dc0000014c8160002941d1c8223200000003e000147b21936915b0f8940000001c28000000000000cdd540001e200000020f000036a6aad3000203b180000000000000e7a56a070ee0f61d052300014d80032b099822a22133a2f00024c2883030000000460002e122c40013700000000025723700000019e8002110b3e3ca041b599783609f00030d91a29d0002bf8220000d8700800144b2a80020b93d00022181b1040ae85398004308e30d00006a000000244ae7a8909d098ad80001e1c0000029c07d0b360600024800021b9266c00d91949f08000000000001d99eba798b40000248000428001aa2e880031b93325b1ec62c0002a80002192900000002c9800000000000000000000000125245a068101dc9dc1bf18b8568000000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x10da328019042195100048d251860c865440012349661032195100048de60640c865440012359819032195100060da1c640c865440018358719032195104368ca00640c86544001a306460032195102241d25987d0065440014359719340195100060da1c64d00654410b931845d240195100051c65c649006544001c3197192401951000788a48649006544001e219219240195100050d65c64500654410da339421940195100061cdd0865006544001a327421940195100068c5d0865006544001870865d140195100070c259745006544001930865d140195100070c21974500654400153397d9140195102249ca62645006544001c317499140195100049ca606450065440014719719140195100054c65c6450065440017219219140195100054c65f425006544001a3086d094019510005c464f425006544001a308650940195100054964a76dd76444001836865c375d91100058ca5870dd76444001a32861c375d91100050d662761d76444001c26929d875d91100070964a761d76444001c31909d875d91100058ca58701d76444001a32861c075d91100070c9d8701d76444001632961c365d91100048da58871976444001235989d865d91100060da62761976444001835989d865d911000709a4a761976444001c25929d865d91100070c642761976444001632961c065d91104cf0c9d870197644400143696dd572d911000645dd7835cb644400193375e0172d91100050da5b75dc3644400163296dd770d91100068ca1b75dc3644400153296dd770d91100070ca5b75dc3644400193286dd770d91100070ca1b75dc36444001632961d770d91100068ca1875dc36444001a3286d9770d91100068ca1865dc36444001533955cb70d911000564e4d72dc364440018347421954d89100060d21b7455362440016c1900cb63d89100064ce1780dd16244001c14651cc64589100041d258875516244001834742195458910006151cc86551624400183486dd154589100070519464dcd624400145496553735891005e4921d5450962440016249655142589104c7411cd545096244001d215450b70589100054ca5d5450162440015309755140589100064ca1d5450162440179308755140589104bf441cd545016244001d1154dcd405891005d6825d42501624412dd807350940589100060da1464dd932440015c1900ca764c91000721190321d932440015c1900c8764c910005d064032d953244001345980c8654c91000781190321953244001741900c8654c910005e064032d913244001a3180e1764d81100064cdd184197604410dc327619065d81100064c21f85d93604400163296e1764d81100058ca5885d93604410de2020190654811002cd826152541204400b56097549504811002d7025d324c120440159c0874c93048110
  | 1 => 0x60e21974500654400142d929db75d91100060da1a71dd76444001525929c775d91100060da1871dd76444001235989c765d91100048d66271197644400142d929c775d91100050e64271dd76444001235989c475d91100048de61711d7644400181f75e0d72d91100160b21d545096244135c0c73551425891000532640329d932440014c9900c8764c9100059264032d953244001689900cb644c9100060da1464dc5324400183686d5374d95100050da5b845d36544001b058360864d9510006c86098019365440019637260272d951000645dd183d0b65440019337460342d95100058ca5b745036544001c3296dd140d95100058ca58745036544001721921d140d9510005c864864503654400153297d0940d9510005c464f42503654400193385e0374595100060d1d086551654400183486dd1545951005d4c25d54501654400193287551405951005e4c21d545016544001630965514059510006495d182190654408927190e1c64195100041de6174190654400186587a0864195100061961d821906544001a458360864195100061c61d801906544001a6282600641951000698609801906544001925876086419510006c160d821906544001931876006419510006c860980190654400162692e1c64195100058964b87190654410d63290e1c64195100058c6438719065440016269221c64195100058964887190654410d6329021c64195100058c64087190654400143597e08641951000585a4f82190654400161593e0864195100058c643821906544001c2587a08641951000781a0e82190654400183587608641951000689e61821906544001a278760864195100068961d821906544001c258760864195100060961d821906544001a2783608641951000781a0d821906544001a258360864195100078160d821906544001a058360864195100050d65c8219065440016169320864195100058564c8219065440016319020864195100048da60721906544001235981c8641951000585a4c721906544001615931c86419510007095c872190654410d632901c864195100058c64072190654400143597e0064195100060d61f80190654400162692e0064195100058964b801906544001a2582e0064195100060d61d801906544001a258260064195100068ce1d801906544001a318760064195100070c61d8019065440018318760064195100068ce09801906544001e228260064195100068c609801906544001e2182600641951000688609801906544133c30705c064195100050d65c64d0865440018368719342195100060d61c64d08654410da328019342195100068519283d0865440019157460f42195100068519183d0865440019317460342195100060d2197450865440014359719142195100060da1c641086544
  | 2 => 0x400028080080e00000014030000202400018090240200405000010180102006004060040000c00000040241c044100000301000044016149155143d8d520060d205745536154801a255460841d85520062c5d1801076154801a315460041d855200552640325d7614c801589900c974d85320050de5d54107614c801a255460841d85320061c9d580107614c8018b17460041d85320068c55180107614c927434915d154d813200570640329c6604c8015c1900c971981320055264032dd5604c801549900c9751813200562640325d0604c8015c1900ca711813200570640325c4604c80581c875514358e210160e21d545016088517c3171551405822100589245545096294001a155460f4298650006b04c9800ca619400183481dd154586500068955182105619400143697217745865000689615821d16194001a858360874586500062ca1d801d16194001a31856007458650006a8609801d1619400183487dd1545865000589648745516194001631901d154586500068555183d096194001ac132600325865000532640329d9325400188d840c8764c95000532640321d93254001a315460041d85500068955182d0e61880014349755241586204841d25d85105618800143497550415862000685551831056188001a255460841586200061c1d5801d1618810d436959d474586204cf0ca00751d16188001c1475a0c745862000685615831d16188001c147560c7458620007091d6821d16188001a25856087458620007091d5821d16188001a858360874586200062ca1d801d16188001a318560074586200070c1d5801d16188001a91836007458620006a8609801d1618800183687dd354586200060d21c74d51618800107697a1d54586200060de508755161880018374221d54586200060d5088755161880018374021d54586200060d50087551618800183487e1154586200060d21f745516188001834871d154586200058564c745516188001625921d154586200058c6407455161880014349755343586200068955182d0d618800143497551435862001607e1d5450f634800703c985d15458d2049d0d24574551634800142d941d77258d200160b21d5450962c4127924875514258b100867021d324c120c4001a0d8360864d95100068a60980193654410d8367621171d95102241da5a87107654400181f7460f42d95100060b5d182190654400182d8760864195100068360d8219065440018398760064195100068a60980190654410d8368719341195104368ca0064d0465440018368719041195100060d61c6410465440016259219041195104368ca00641046544001a2464a084119510006495d1821046544001a246460841195104cc8d25984c8465441332379819321195104360da1c64c84654413363296906401951
  | 3 => 0x25c09945989d68387e40c00826a80494032a22481c08020a530d01caa10e16841c00001789620c000629d000001e06a93f279e4000008596a000600000090914000000001e00000309519e8001a1417d800000aa0680059da252846000003b40086990438000027b1b882000000c8ea31a609794e2908a466387f9a8721083622e5ca32a21ca2b26a1989325a8e0019c3f05eab07c3800aa52461d1f4a11ef4b23c46dd19acc88fa726790a4d17c2d8009413a25546000f66080078a1c00198520003ca707e80000124158009594348a52111a455800698001b1b60014d6e8000aa2800282551863d10027c90310008e80000212001800017070800001b84d8007956b001c60013ea9a30001649208e000a83e800000005e8000002c2e8582c90400000455d4000000002843000281f7070fe2890b0322056810586aa13800294340f8e8091ff540766d24c4c26c3e1730029065000000007d464809840c0c9664c01f4b079a7616a249f15e00204998037a054620a6000367100051d1e629ac7a83a60e1e928865d55f4e08c74949a709c8b000001c5588000013c89a770800069d1a39000000061fe2a0021832d962f800012144982e4f47a000d4000ee00171571f00028a34800476540004a10878731328d8000019240a3425000a59122a54433a064406a734b86810500292a6280000da0018e3b2401557b9b80000000170002ba44378023fc70000756c18c370000000041a6f471606f9ce35898000845b0007b000000007ca9a038b499109130002f1da00000ab80006000771164ba083897d284000895214d66021187857e0f29ea91ae00000000000025a001dd778000009a001bc00176000167b892a896e2200000268a3197100f077dd0001d8ac080668003301414000000e6121b27e278938005617400000000525a52a4a2867f1429faa0840120480601008000000000703c010000000c01048000000302403020030080c010020000202c0100403004060380100400008080040303403048020040f00c21000020201804004028010440a04c1101c090380000805014240080002c030000400002014050040000401004020000200000008040
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x700268c8c0033900373505eb8000000342488536004b4544594010000000d089638d8009780006dab7404cc2a1c00037800059b80acb0bb2000212d5538c5504f1adc8efa4805731153c160564a4ecf3a918805a2441a070200300021c00e060008504281800000100027428100504f4eaa30420ec299002833a755180107614c801844c2320190ec992a000a0529d5460c41586200050494eaa30420ac3100038047560d821d16188001c083ab06c00e8b0c4000e081d582600745862000502b47a110eaa2c3100030148764c74551618800181243b243a2a8b0c4000c0c21d901d154586200050494eaa305a1ac31000302587648641046544001502d18c8c108232a2000c09a19929c775d91100060610e4b2a8a02ca88002a05a3e1d821906544001510d070ec10c832a2000a0969f83608641951000544341c1b04320ca8800380587a0d821906544001c02c3b06c10c832a2000c09661721c8641951000680b26b90e4320ca8800342172640721906544001812c3b25c00c832a2000c0965d82e00641951000640b26c1700320ca88002a21a2e1d801906544001418d3f04c00c832a2000a8468f8260064195100070430f41300320ca8800382187609801906544001d0141b04c00c832a2000e8060d82600641951000502b4e32307a10ca8800342197648649006544001b00c9b243248032a2000c0c65c86d0940195100064210cc9e84a00ca880034059364a761d76444001a10c93213b0ebb222000d0164d929d865d911000684324c84ec32ec888002816a6dd7835cb64440018194b50dbaee1b222000a0568c7421954d8910005063403a10caa6c48800302487259545096244001a023992caa284b1220009216a4640c8764c910006900c8c80643b26488002605a9190321953244001902cc0c8190ca9922000d80191900c8654c910
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x1
  | 6 => 0x138d
  | 7 => 0x4b
  | 8 => 0x4d
  | 9 => 0x4e
  | 10 => 0x94b
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124d
  | 14 => 0x124b
  | 15 => 0x124e
  | 16 => 0x138b
  | 17 => 0x138e
  | 18 => 0x98c
  | 19 => 0x98d
  | 20 => 0x98e
  | 21 => 0x4
  | 22 => 0x128c
  | 23 => 0x128d
  | 24 => 0x128e
  | 25 => 0xa4b
  | 26 => 0xa4d
  | 27 => 0x134b
  | 28 => 0x134d
  | 29 => 0xb0c
  | 30 => 0xb0d
  | 31 => 0xb0e
  | 32 => 0x140c
  | 33 => 0x140d
  | 34 => 0x140e
  | 35 => 0xbcb
  | 36 => 0xbcd
  | 37 => 0x14cb
  | 38 => 0x14cd
  | 39 => 0xccd
  | 40 => 0xcce
  | 41 => 0xd4c
  | 42 => 0xd4d
  | 43 => 0x98955
  | 44 => 0x94c
  | 45 => 0x94995
  | 46 => 0xa4955
  | 47 => 0x94a55
  | 48 => 0x138953
  | 49 => 0x138955
  | 50 => 0x138956
  | 51 => 0x95395
  | 52 => 0xcc955
  | 53 => 0x94cd5
  | 54 => 0xd4955
  | 55 => 0x94d55
  | 56 => 0x1489
  | 57 => 0x2c9
  | 58 => 0x14c9
  | 59 => 0xb0955
  | 60 => 0x94b15
  | 61 => 0x140955
  | 62 => 0x95415
  | 63 => 0xbc955
  | 64 => 0x94bd5
  | 65 => 0x14c955
  | 66 => 0x954d5
  | 67 => 0x130a
  | 68 => 0x14a
  | 69 => 0x134a
  | 70 => 0x99395
  | 71 => 0x138c
  | 72 => 0x138995
  | 73 => 0xa5395
  | 74 => 0x138a55
  | 75 => 0xcd395
  | 76 => 0x138cd5
  | 77 => 0xd5395
  | 78 => 0x138d55
  | 79 => 0xd4a
  | 80 => 0xb1395
  | 81 => 0x138b15
  | 82 => 0xbd395
  | 83 => 0x138bd5
  | 84 => 0x9cb
  | 85 => 0x9c995
  | 86 => 0x12cb
  | 87 => 0x12c995
  | 88 => 0xcb
  | 89 => 0xcc995
  | 90 => 0x98cd5
  | 91 => 0xd4995
  | 92 => 0x98d55
  | 93 => 0x168b
  | 94 => 0x198b
  | 95 => 0xd4a55
  | 96 => 0xa4d55
  | 97 => 0x150e
  | 98 => 0xa4c
  | 99 => 0x14d355
  | 100 => 0x1354d5
  | 101 => 0xb4b15
  | 102 => 0xb4b
  | 103 => 0x144b15
  | 104 => 0x144b
  | 105 => 0x24b
  | 106 => 0x16cb
  | 107 => 0x19cb
  | 108 => 0xeca
  | 109 => 0x154e
  | 110 => 0x1a0a
  | 111 => 0xd54d5
  | 112 => 0x14cd55
  | 113 => 0xecb
  | 114 => 0x17cb
  | 115 => 0x1a0c
  | 116 => 0xecd55
  | 117 => 0x170e
  | 118 => 0x1a4b
  | 119 => 0x15ce
  | 120 => 0x19cd
  | 121 => 0x138954
  | 122 => 0x10a
  | 123 => 0x95393
  | 124 => 0x289
  | 125 => 0x95396
  | 126 => 0xa0954
  | 127 => 0xa0956
  | 128 => 0x130954
  | 129 => 0x130956
  | 130 => 0xd0954
  | 131 => 0x104954
  | 132 => 0x1a8954
  | 133 => 0x94a16
  | 134 => 0x282d1
  | 135 => 0x1a89
  | 136 => 0xd0c
  | 137 => 0x104c
  | 138 => 0x1a8c
  | 139 => 0x1049
  | 140 => 0x184e
  | 141 => 0xcc9c99d
  | 142 => 0x9c98cdd
  | 143 => 0x104953
  | 144 => 0x28e
  | 145 => 0x2cd
  | 146 => 0x105393
  | 147 => 0x104a
  | 148 => 0x1a8a
  | 149 => 0x104b
  | 150 => 0xd0a095c
  | 151 => 0x104a095c
  | 152 => 0x104d095c
  | 153 => 0x2c291
  | 154 => 0x104d14
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 1184
  | 6 => 2685
  | 5 => 1646
  | 4 => 345
  | 3 => 56
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
  | 8 => packedAt gbK8 (1369+((h/21+packedAt gbK8 (1222+(h % 21)*7) 7) % 92)*7) 7
  | 7 => packedAt gbK7 (49664+((h/488+packedAt gbK7 (43808+(h % 488)*12) 12) % 2337)*12) 12
  | 6 => packedAt gbK6 (141192+((h/1026+packedAt gbK6 (128880+(h % 1026)*12) 12) % 3694)*13) 13
  | 5 => packedAt gbK5 (104086+((h/581+packedAt gbK5 (97114+(h % 581)*12) 12) % 2531)*12) 12
  | 4 => packedAt gbK4 (25510+((h/136+packedAt gbK4 (24150+(h % 136)*10) 10) % 542)*10) 10
  | 3 => packedAt gbK3 (4711+((h/25+packedAt gbK3 (4536+(h % 25)*7) 7) % 101)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc3ffe18387f0fe01fe380ffff14823e1330ff
  | 1 => 0x3fc381e03f87f0ffe0fc00e0e02b1dd86dcccc
  | 2 => 0x3ffc01ffc007ff0000ffff00ffcc61e18e0f0f
  | 3 => 0xc00001fffff8000000ffffff00f07e01f00ff0
  | 4 => 0x1ffffffffffff00000000ff8001fff000
  | 5 => 0xfffffe00000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4404840008090120422080222200000a011055
  | 1 => 0x1c410c6018831049c2e4064646010cd8254ccc
  | 2 => 0x2aa810aa4006aa0284492a009c4c21608e050a
  | 3 => 0x80002154b55000050892549c00b05601700aa0
  | 4 => 0x220419f2664cc961c00180808fe8001daa000
  | 5 => 0x33327806044088181000601010fffbb4000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36352
namespace PEqualNP.Outside.L_meta_36352
open PEqualNP.Outside.L_meta_36352.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 24 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 117 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 24 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
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
theorem bs4_2_0 : Interval s4Atlas 2 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 26 := bs4_2_0
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
theorem bs4_3_128 : Interval s4Atlas 3 128 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 144 := (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 (concat bs4_3_96 bs4_3_128)))
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
theorem bs4_4_864 : Interval s4Atlas 4 864 19 := block_range (n:=19) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 883 := (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat (concat bs4_4_96 bs4_4_128) (concat bs4_4_160 bs4_4_192))) (concat (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)) (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 bs4_4_416)))) (concat (concat (concat bs4_4_448 (concat bs4_4_480 bs4_4_512)) (concat (concat bs4_4_544 bs4_4_576) (concat bs4_4_608 bs4_4_640))) (concat (concat bs4_4_672 (concat bs4_4_704 bs4_4_736)) (concat (concat bs4_4_768 bs4_4_800) (concat bs4_4_832 bs4_4_864)))))
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
theorem bs4_5_800 : Interval s4Atlas 5 800 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 802 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat bs4_5_96 (concat bs4_5_128 bs4_5_160))) (concat (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)) (concat (concat bs4_5_288 bs4_5_320) (concat bs4_5_352 bs4_5_384)))) (concat (concat (concat bs4_5_416 (concat bs4_5_448 bs4_5_480)) (concat bs4_5_512 (concat bs4_5_544 bs4_5_576))) (concat (concat bs4_5_608 (concat bs4_5_640 bs4_5_672)) (concat (concat bs4_5_704 bs4_5_736) (concat bs4_5_768 bs4_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := (concat bs4_6_0 bs4_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 56 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_320 : Interval gbAtlas 4 320 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 345 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320))))
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
theorem bgb_5_1632 : Interval gbAtlas 5 1632 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1646 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))) (concat (concat bgb_5_608 (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800))))) (concat (concat (concat (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)))) (concat (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632))))))
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
theorem bgb_6_2656 : Interval gbAtlas 6 2656 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2685 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)))) (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)))))) (concat (concat (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)))) (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))) (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))))) (concat (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)))) (concat (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464))) (concat (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)))))))
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
theorem allgb_7 : Interval gbAtlas 7 0 1184 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
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
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 36, 38),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
def fullWord : Sig := 0xfeeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0feeefeeafeeefaa0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36352.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.and,[0,6]⟩,⟨.or,[3,6]⟩,⟨.or,[0,1]⟩,⟨.and,[2,7]⟩,⟨.and,[5,8]⟩,⟨.or,[4,11]⟩,⟨.or,[10,12]⟩,⟨.and,[9,13]⟩,⟨.and,[3,6]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36352

open PEqualNP.Outside.L_meta_36352 in
theorem PEqualNP.Outside.L_meta_36352 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
