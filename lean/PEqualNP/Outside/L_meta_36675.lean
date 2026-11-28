import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36675.Model
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

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

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
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
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
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
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


end PEqualNP.Outside.L_meta_36675.Model

namespace PEqualNP.Outside.L_meta_36675
open PEqualNP.Outside.L_meta_36675.Model
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

def SBf (j : Nat) : Nat := [4, 6, 8, 7, 5, 6].getD j 0

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

def checkRow (g : Atlas) (k i : Nat) : Bool :=
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

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_36675

namespace PEqualNP.Outside.L_meta_36675
open PEqualNP.Outside.L_meta_36675.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfc07ffffffffffffffff01fffffffffffc3fff
  | 3 => 0xfff803fe01ff00ff007ffe07e03f01fc07cccc
  | 4 => 0xfffffc0001ffff00007ffff8003ffe0007f0f0
  | 5 => 0xfffffffffe000000007fffffffc0000007ff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x940924921451121252151628aa4552a551d555
  | 2 => 0x2b42492528a2a4a4a42a815554aaa54aa42aaa
  | 3 => 0x4d5762394d348ec836cfab06663331f036cccc
  | 4 => 0x726473b1b1c8c88ec773cd9c183cf860c770f0
  | 5 => 0x838783c1c1f0f0f0f87cf1e79f20c18307bf00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36675
namespace PEqualNP.Outside.L_meta_36675
open PEqualNP.Outside.L_meta_36675.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3200c5000100c076904b024a19080bf42bd42df32dd32f621f521be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x400218d424cb4a8490f14c921
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
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
  | 4 => packedAt s1K4 (244+((h/4+packedAt s1K4 (224+(h % 4)*5) 5) % 19)*5) 5
  | 3 => packedAt s1K3 (84+((h/1+packedAt s1K3 (81+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x3f807ffe01fffc0f03f83f07ff07fe0289e7c
  | 3 => 0x3fff80fffe03fffffc003ff83ff83fff0e38f
  | 4 => 0xfc00000fffffc000fffffc0003fffc003f03f0
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x808504022420480014584508450842a832cb5
  | 2 => 0x595534a651d4a915782aa2b46ab46b41a8965c
  | 3 => 0xa264a52a9491b234baa0432d232d239530c30a
  | 4 => 0x3346c6cd191923a6dcf36a0843ce71063d03e0
  | 5 => 0xc387070e1e1e3c38ef3c73ce720842183ef800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36675
namespace PEqualNP.Outside.L_meta_36675
open PEqualNP.Outside.L_meta_36675.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x2018f0056000164069381302cb82000000000a46054624c8f1a84900001c0000000026140019300000000050e8000008a2000000000940045400f9b1054e00509070082060018000002020008183ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31f731fe31fd31fc31f431ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xe61f431cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa71877d0e30df21c61bc438c3b887186710e30bf294617d528c3bc6518770ca30bf28c61f6518c2eca3185f54630faa8c6175518c3ee6318778c630ee18c61f4318c3a863185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c37c86986f10d30bfa9261ef524c2dea4985f14930f6292616c524c3be6498774c930bfa8a61f7514c2eea2985f14530fa28a6174514c3ee62987d0c530fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30df21861bc430c3b886186710c30bf290617d520c3bc6418770c830bf288617d510c3ee6218778c430ee18861f4310c3a862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20df21e41bc43c82fca3905f54720fb98e41f431c83f661907e0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20df21c41bc43882faa5107bd0a20f621441ef32883d865105f94620bea8c41f731883e863107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20df21a41bc43482fea2907dd4520bba8a417c51483e8a2905d14520fb98a41f431483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20df21841bc43082fca4107bd0820f621041ef32083d864105f94420fb288417651082faa2107d54420baa8841f731083e862107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10df21e21bc43c42fea5885f94b10bea96217c52c43ec83887d50710fb98e21f431c43ec43887d48710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10df21c21bc43842fea5085f94a10bea94217c52842faa3087dd0610fa20c21f731843e863087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10df21a21bc43442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec82887d50510fb98a21f431443ec42887d48510fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10bea98217c530437c86086f10c10bfa90217e52042faa4085f14810bf28821f741043e882087dcc410fa18821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0x643cc7ea8798fd10f31da21e63f752cc7eca598fd54b31fa29663f742cc7ec8598fd50b31fa21663f732cc7ec6598fd4cb31fa19663f750cc7eca198fd54331fa286637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c7be8718ef90e31de21c63dc438c7388718df94a31bea9463df328c7ba6518df94631bb28c63df318c7ee6318df94231bea84637f544c77ea898cfd5131bf2a2637d544c6f8a898ef151319e2a263be434c7788698dfd4931be29263f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c7be8618ef90c31de21863dc430c7388618df94831bea9063df320c7ba6418df94431fba0863f6410c7ea8218fd10431ef98863f6310c7ba6218fd4c431bf280637d500c7eea818fd95031faaa063f4540c7eca618dd94c31eb29863f7430c7ae8618fd90c31db21863f5430c7e88618ed10c31ea2186394430c7eea418fd94831faa9063f4520c7ee8418fd90831faa1063f4420c7ee6418f5cc831fb19063f5320c7aa6418fd0c831fba8063f6500c7eaa018fd14031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21df21e43bc43c87ec8390fd50721fb98e43f431c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21df21c43bc43886faa510df94621fba0c43f441887ee6310fd0c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21df21a43bc43487ee8290fd10521fb98a43f431487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c530877c8610ef10c21bf290437e51087ec8210fd50421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740fb98e81f431d02faa9205f94e40bea9c81be439037887205f94a40bea9481be429037885205f94640bea8c81be419037883207dcc640fa18c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037c86a06f10d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fb98a81f431503f680a06f90140bf2a0817e53102faa6206f90c40de218817e52102faa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2206f90440de20881f731103e862205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330df21e61bc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730fb98
  | 2 => 0xa02c0003a0040380180000600c0181500804002005000008010030000080200600001804800004008038020040000000200e028080110000000000500000802003010026fca5a1df54b43bf28e87f651d0eeca3a1df54743faa8e877551d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090e7ca721efd4a43df29487bd5290f78a521efd4643df28c87bd5190f78a321efd4243df28487bd5090f78a121f7d0d43df21a877f5250ef8a4a1dfd4543fba8a87775150ef8a2a1fd14543ba28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021ef94c439f298879e5310f7ea421ef94843dea9087bc5210f7ea221ef94443dea8887bc5110f7ea021ef94043dea8087bc5010efca7a15f54f42df21e85bc43d0afca3a17d94742bb28e857d51d0beaa3a15d54742bf286857d50d0afaa9215f94e42ef29c855e5390afaa7217754e42aea9c85be4390b7887215f94a42dfa1485ef4290afca3217d94642bb28c857d5190beaa3215d54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216f90c42de218857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbbe87996f90f32de21e65dc43ccb3887995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32df21c65bc438cafca51977cca32f7994657e518cbeca3195d94632bea8c65f5518caeaa3195f94232bea84657f544cb7ea8994fd5132bf2a2657d544caf8a8996f151329e2a265df434cb7c86996f10d32ee21a659c434cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0997ed4132bda82657c504cbf0a0995e14132bfaa0657e540cafaa8195f15032bf29865be430cb7886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077c86a0ef10d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f5411076a8220df94041bea80837f54cc6fca998df55331be2a663be43cc7788798df94b31bea9663f741cc7ec8398fd50731fa20e637e50cc6faa198fdd5331fb2a663f554cc7e8a998fdd0f31fb21e63b
  | 3 => 0x2000e9b4f3320000011764a140a59b231e5e0071a81a2001ae9dc0220f85f2b420c000c307d0003f4002ee06455c0030e02a000001a41e29153182a5c4000002ca0e84a80000001e4e8d295900000000000000000000001b200188800128a643c000330258510000bc268428004ca2607305a35a070a69882dc0000036900079494890000571248bb0707c80015a6cca804f8005fcbe4128880004f431af147c000002d10001a0001fb00028c0021a00022d5caf058c00182256000001118e800000000206000000002356529f800131000d488a1be1a81f800205000001aa12e0c0cf8b980000044d6291115a8609c128482000000240009b8e921d42e7a840b626c6b1da09cf3c08049ba5e6045fcf497e00030ced000382945450002ac95c002a355e1598e9d725accc000005ac2640e9b86f2a587716b6622d8d70005cc3384110d2d22c80019469a4c92a31918a09d8ba5a66a6d925b3250e3dd3987c53004d1987a07a688612da526000001df000000149a00004780011d00000000000000db8a8a7f3ba83846000612000001f62f6c013900052a11ca48001c6459aa8a50da2f118b085447d4000005203212630d2666406b8ab6e63e144800000b0d568f60002b8bc8090a89e85c07f53e7017632f1c41c08c0331e071c00021000a2c6d97c50a371200312eeaada30e7000870a9855338a9cff94a0b000000000290d3021a9d32268cc62773c2001181221de0019e15b5880013a8370cab080000016e7a113800694000b7b0b00a894d08b51aaac00003c5426c0da29c5d48552305241a0011c8003e6cc153130644cb4aa0004aad707d11a17e7b5959ef000a30d580012a124000cb5a0c040000061e299b0ad8214880001bf0be098002863520b9ab187684b8c002a50000003606b0000783b01a1b4c18c236f4740018aa214ce3edaca474d8050a31c86683e58d00400300600c018040000000080300a0140800100401c010060060300c02601a0040000700600c020050020000000600403400816006000000000040300003a0280180101d01600001001012034010010280180080500203c000000000180000300c050018000040000780c028004020010040140000100c0040000400a000040000020340000b00200406001002010000090000140200100c00c0000100c000018000020b8050000060100080101802c0000400000000803004000000050060100800a00000800002006010058030020080000000e0000f806018038068010000100000300401002800014000000000020080100301e0080280301a00c00800000004000030080080080101400006801002080010150060000f02c05600000000012004078020020080a8020000400080100002c0000000c0080a81801600002001004004070000000100200201c0000002e0
  | 4 => 0x42c1e57b1f024ed200036868831c308010ba86567a3d0001dcb6195298380002c8000001af8000000019ead71927e86fb054f2b2400338000374608002c4200002aa03600000000448b552e1215c2001b235a506c84ed9470501c4b09455de0000010c0000d14900032e170cd000372bf1322b50007e0a1aff4d28b5540003aa1214d8b122a311721c4060b94fba605c0908c19c20a2738b90aa6207d0651de5a8dd0c51e62486a89a12552e001479640146000010b01853db92290003940000063c614501cb59878867a680000000010435e1d4000006400000015f000001413673a8a056e00010e0016f14464e840000c027ebac002662baadc0000021c20c00023494000b026b0000000c81f000000b82f368e3480000011c228000645006c5b280000034c02000000440000000000d91b00069c7f4000004ba4d51102c158001a5a0f4b23a8aaa0309c14c2c91b11e358212e71b0498598002040002580032cd60001bb000d00001194242755c1c666e26c00000000448e8800020d0c00000000000c12740d2d810119d0002c0d300007648d27b3a53c219178000004700026a142000f3908202cb15f000000634b29bd49c9113786e1fedb53809125858c2bacb000001088bd00000000376016000bd1ba112a459c84d57a1a8002260008f0001420000008486f0002492831c000a344f0225ee3d4000000040003100000081c000003fc000790411fc0e9b82ce6e290d240e95e487c001036060bd47208256001058a739a0017e975000270b3b6b578948520035f0da9421b7458c9926a1e0cc810c08ed056ca9ab9406506d56db364da64cbea715b2c60e500027c84da499b31c9609b2284b63855d0f301abd4232d26bc8285795e0806b080120000ab8eb2e81723407603556497cf613c4761118d89362c5d8c5a2b6281ccb68086a01ece28b45105a0fc9bc18cb0400345000db0000003c8ad8001711507315480000001866800000cec0027d5800000000041870ca08005dac9000000000c497d94e3dc6ccc903f0723d0e48004549f016afa00000033ad30000000004a33c540002615be0000026262600166800000c1d58b0a5d2415bc097000000000004287c42d800174afd1c0000008dc000176180580015846800197000000598d3a534f078c0035b000c8d1fb1f00013000276272000420cc0001150d91f3d67f0ec96a5e8a50cfb3f45ca68000001bca915995211a3f0ec209040b7483b53312ddd00000030741ba80015204827a7b5584ec03a3225e3ac002bb2e800000072000390878006a
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x520082ac6448020b318d20082e461480209ed9520082d863480209798f54c425d63d53109b98b54c426d62d53108f99353c423d64d4f109b98b53c426d62d4f108fd9153c423c6454f10c794c43c431d5310f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798e52c425d6394b10cd15141c42d46350710d594c31c4355530c710e510c31c42b564887109798f548425d63d52108f993538423d64d4e108fd91538423c6454e10c794c438431d5310e108fd91528423c6454a108f990528423d6414a109798c528425d6314a10cdd50418435653cc610d514c3184394430c610ad99321842d663c86108f98f544423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109dd85544423e65151108f98c544433561151108f993534423d64d4d10c7d53534431c54d4d10c7993534431d64d4d10d5587534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd8553442746114d1097994534431f5414d10c7150534431f6414d10c719053443576114d108f996434423c6590d10c7d4e434431c5390d108f994434423c6510d10c7d4c434431c5310d10cbd53524432c54d4910d3d4f524434c53d4910cb90f524432c43d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524432e4314910cb10c524436561149109d99641443345490510d514e414436452905109d19541443345450510b518d41443545350510d9149414427665cc510cdd53314433454cc510d514f314436752cc510d914b3144337540c510cd1503144357530c510d514c3144394430c510d9d483144364520c5109d99621442b56488510cd15221443545388510d914a21442746548510cd15121443545348510d914921443345484110d514e104436452841108f596540423e639501097d8d540425c6355010a718d540431f63550108f18d540431c63550108718d540433461550108f990540427661150108f993530423d64d4c109d987530423f6454c108f19153042776154c108f990530423d6414c109b988530426d6214c108fd96430423d6590c108fd94430423d6510c10c7d4c430431c5310c108f993520423d64d48108f990520423d64148109798c520425d63148109d984520427565d0410cd55341042756510410cd550410433654cc410cd5533104275650c410cd9503104335540c410d594c3104394430c4109d59721042b664c8410cd55321042d663c84109d59421043355408410cd553100427965840109dd9510042b46444010cd55110042d46344010b9189100427b6544010
  | 1 => 0x823e64d4f208f59353c827661d4f209d58753c823f6454f208f19153c82776154f209d18553c831e5310f20c754c43c823e64947208f59251c8356530c720d554c31c8394430c720e610c30c83d0310c32097d8d548825c63552209dd85548827461552209d984548827561152208f993538823d64d4e209d987538827561d4e208fd91538823c6454e209dd8553882746154e20c7d4c438831c5310e20b9987428838c43cca208fd91518823c645462097d8d518825c6354620d5d4c3188354530c620e510c31883c7320c620ab992218823e63d51208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551208f994544823e63151208f993534823d64d4d209d987534827561d4d20c7d53534831c54d4d20c7993534831d64d4d20d5987534835561d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f191534826f6254d209dd8553482746154d209ed81534825e6514d20c7d50534831c5414d20c7d90534831c6414d20d5d8453483546114d208f996434823c6590d20c7d4e434831c5390d208f994434823c6510d20c7d4c434831c5310d20cdd53514833454d4520d5d4f514835453d45209d98f514833643d4520cd10f51483375414520cd15051483575314520d514c51482766314520cd90c514833443145209d997314827465cc520cdd53314833454cc520d5d4f314835453cc5209d9943148274650c520cdd503148334540c520d5d4c3148354530c520e510c314835853c8120cb152204834c5388120d9146204825e63d50209758f540827661d50209d587540823d65950208f98e540823c6355020cb189540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831f6494c20c719253083576194c20d5186530823f6454c208f19153082776154c209d185530831e5454c20c7551530831f6454c20c7191530834c6254c20d5d8553083546154c20d6181530823e6414c208f590530825e6314c209d98453082756114c208fd96430823d6590c20c794e430831d5390c208fd94430823d6510c20c794c430831d5310c20cb55342082e661d08209b594420834d53cc820e310f320826d650c820cd95251083355494420d594e510835553944209d98e51083364394420cd10e51083365454420cd55151083565354420d554d51082746354420cd90d510833443544209dd97310827565cc420cd953310833554cc420d594f310835553cc4209dd943108275650c420cd9503108335540c420d594c3108355530c420e510c31083c7320c420ab99221083655188420d654f30083cb32cc0209e5943008398430c020f20c830083d0310c0209bd9
  | 2 => 0x52cc540d914b3150276650c5409d1943150357530c540d514c3150394430c540d9d483150364520c540c714e405032c5290140cd14640502776154c409d185531031e5310c408f596421029e6390840ad98642102766394440cd90e5110334439444097d8d511025c6354440b518d511035763544409d18d511035463544409518d51103364354440cd10d51103364254440cd109511023d6590440cd546411033551104409dd97311027565cc4409dd943110275650c440e510c311033551d00408fd95401029c6350040ab18940102b46150040cd545401027b65500409b98b54cc26d62d53309d98754cc27561d53309d98654cc27561953308f99252cc23d6494b309d98652cc2756194b30b618132cc23e64947308f59251cc394430c7309d987548c27561d5230c7d8d548c27661152309d584548c2d661d0e30c7550438c29d6510e30c7594438c31c4354a30a7992328c2d6618ca30c710e518c3365494630cd552518c3944394630d5d0e518c3364394630cd10e518c3544394630c510e518c3365454630cd551518c3944354630cd90d518c3344354630cd953318c33554cc630e510f318c29e648c630c7952318c31e540c630d5544318c336540c630cd550318c396430c630e510c318c2d5650c630d5594318c356540c630e5950318c316540c630e5550318c354540c630d5548318c23e64951309b98a544c26d62951309d986544c275619513097d8d544c26f62551309b189544c27761551309d185544c23e65151308f98c544c23c63151308f996434c23e6510d30cbd53524c32c54d4930cb90f524c32c43d4930cbd50524c32c5414930cb90c524c32c431493097997324c31c54cc930d314b324c31c544c930d3149324c2d8604c930cdd53514c33454d4530d9d4b514c36452d4530cd90f514c33443d4530cdd50514c3345414530d9d48514c3645214530cd90c514c3344314530d5cc8514c35532145309d997314c33754cc530cd153314c36752cc530d914b314c276650c530cdd50314c334540c530e510c314c367520c530d9148314c36852cc130c7152304c34c528c130d5146304c27761550309d185540c26e62150309b588540c27661150309d584540c2d661d0c30a798e430c25d6510c30c7994430c31d6510c30e6980430c3996010c308fd91520c23c6454830c710d520c27761548309d185520c25d658c830a7992320c2d6618c830c710e510c23f64544308f191510c39443cc430a7992310c2d6618c430e590c310c394430c430d5950310c354540c430d5548310c3d2600c430f4580310c23e64940308f592500c31c4394030d50c6500c398438c030f40c6300c25f654c030a7191300c2cc624c030b5185300c27b654c030ba189300c25e63d53209758f54c827661d53209d58754c827661953209d58654c
  | 3 => 0x31ad990500c6b56414031e510c500c6e66214031b9588500c65e63d53219758f54c863e6395321cd58654c863c63553219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c7d9253c871c6494f21d5d8653c863f6454f218f19153c871e5454f21c755153c871f6454f21c719153c87576154f218f99053c863d6414f218fd9643c863d6590f21c794e43c871d5390f218fd9443c863d6510f21c794c43c871d5310f21cd95241c87565390721cd95141c86d46350721d594d41c873654cc721cd55331c875653cc721cd95031c8735540c721d594c31c8755530c721e510c31c863e639522197d8d548865c6355221a718d548871f63552218f18d548871c63552218718d548873461552218f993538863d64d4e219e983538867960d4e218fd91538863c6454e218f990538863d6414e218fd96438863d6590e218fd94438863d6510e21c7d4c438871c5310e21cd55341887355410621cd953318873554cc621cd9503188735540c621d594c3188794430c621ad993218873554c8621b598f2188675619512197d8d544865c63551219ed81544867860551218f993534863d64d4d218fd91534863c6454d219dd85534867b6054d219e181534871f5310d21c714c434867665d05219d994414873554105219d997314875453cc521b998b3148756530c521e510c31486b664c8521b598f214863e64141218f590504865e63d50219758f540867661d50218f993530863d64d4c219d987530863f6454c218f191530871e5310c21c754c430863e64948218f592520865e63948219758e520863e64944218f592510867565904219dd9541087345450421b518d4108675650c421d594c3108755530c421e510c31086e5620c421ad592210866f65484219dd95210863f64540218f191500865f63540219718d50086776154f409d18553d031e5310f40c754c43d025e6394b409758e52d02766194b409d58652d02b561d0b40a718d41d0356530c740d554c31d0394430c7409dd8553902746154e40c794e43902776154a409d185529029e6390a40ad9864290356530c640d554c3190394430c6409d987535027561d4d40d5987535035561d4d40c7d9053503576114d40d5184535031c5390d40c7d4c435034f53d4940d314f525032e43d4940cb10f525034f5314940d314c525032e4314940cb10c525023e65d0940c714f425032c52d0940ad587425031c5350940cb149425035753d4540d514f515036752d4540d914b515027663d4540cd90f515033443d4540d5d4c51503545314540d9d48515036452145409d98c51503364314540cd10c51503374214540cd508515023e65d0540c714f415032c52d0540cd147415029c6350540c714d415032c5250540cd145415027665cc5409d197315035753cc540d514f3150367
  | 4 => 0xbd89501066c6254041cd505501066e62153319b58854cc63f6454b318f19152cc7365450731cdd5041cc63e64943318f59250cc6d663d5331cdd5254cc6d66315331b998854cc6e56215331e598c43cc7675294b31add9152cc6b46454b31ad99052cc6b56414b319d99742cc67565d0b319d99642cc6756590b31b598e42cc6d56390b31e510f32cc6b6648cb31ad59232cc6b7644cb31ad19132cc794434cb31bcd8132cc6f0604cb31f14c832cc6b664d4331ad59350cc6e662d4331b958b50cc6b66494331ad59250cc71f6355231c7550438c69d6510e31c7594438c71c4354a31c7953328c69c644ca31c7951328c74e524ca31b6181328c73654cc631cd553318c71c43942318f992544c675619513197d8d544c67761551318f994544c63e6590d318f994434c73754cc531cd153314c71c548c5319b98b540c66d62d5031b5587430c69e6390c3197594430c71e6510c31c7594430c7966110c31e5584430c63e64948318f592520c71c4354831a7191320c6d7614c831b6181320c63e64944318f592510c71c4394431e510f410c6756590431b558e410c7944390431cd151410c6d76350431e510d410c6756510431cd550410c7944310431ad992310c6b5648c431e510e310c65f654c431a7191310c677654c431add91310c6b4644c431e510d310c71c43940318fd91500c63c64540319bd89500c66c6254031b598f540c6e662d5031b958b540c7355415031b598c540c7566394c31b5992530c6d56294c31b5982530c67565d0c31b5597430c75565d0c31b558b430c6d660d0c31b598e430c6b66390c31a598e430c7365390c31e594e430c6776550c31e550c430c6b66310c31e598c430c7365310c31e594c430c6d76510c31b5594430c6d66410c31e5990430c7965410c31e5550430c6d56210c31b5980430c7976510c31e5994430c7956510c31e5194430c7976210c31e5988430c7956210c31e5188430c7976010c31e5980430c7956010c31e5180430c6b664d4831ad593520c79443d4831ad992520c6b56494831e510e520c7944354831e510c520c76552148319d997420c67565d0831e510f420c67665908319d596420c6d66390831b558e420c7944390831b5d8d420c6d46350831e510d420c6d66310831b558c420c7944310831e590f320c79443cc831b5993320c6d464cc831f194b320c7c552cc831b5983320c675658c831ad992320c6b5648c831b558e320c794438c8319dd95320c6b7644c831ad191320c796434c831e510d320c6f3604c831bc181320c6d7654c831d5d95320c797644c831b5991320c6d4644c831e5191320c694644c831f1d89320c7d3604c831b5181320c7d0604c831b4181320c6d6630c831e510c320c79443d4031e510e500c6b76454031ad191500c7944354031b9d89500c6e46254
  | 5 => 0x5110f355114443abd895010eac6254043add855010eb46154043ab9885010ead6214043ad9845010eb561140439dd8553d0a746154f42c794c43d0a766394742cd90e51d0b34439474297d8d51d0a5c6354742b518d51d0b5763547429d18d51d0b5463547429518d51d0b364354742cd10d51d0b1f6494e42d5d865390b546194e429dd855390a746154e42d5d855390b546154e42c794e4390b1d5310e42c794f4290ab561d0a42d594e5190b5553946429d98e5190b364394642cd10e5190b374294642d594d5190b5553546429d18d5190b364354642cd10d5190a7661d4d429d5875350b1c5390d42ab98a4350a9e6390942ad9864250a7661141429d5845050a776154c429d1855310b1e5310c42c754c4310aad6210c42ad5874210a3f65508429bd954210a5f63540429718d5010a7761540429d1855010a7761553329d18554cca7661153329d58454ccad661d0f32c799443ccb1d6510f32e398843ccb8d6210f32c710e51cca3f64547328f19151cca3e64943328f59250ccb1c43943329d98650cca7561943329d987548ca7561d52329d984548ca756115232c7953328cb365494632cd552518cb364394632cd10e518cb573294632cd951518cb355454632cd90d518cb344354632c758f544ca3e64951329d986544ca7561951329e982544ca7960951329dd85544ca7461551329ed81544ca7860551328f994544ca5e65d0d32b398b434cad661d0d328f996434ca9e6390d328f994434cb1f5410d32a7994434cb1e6510d32e310f324ca9e648c932b5986324cb3754d4532cd153514cb9443d4532cd90f514cb3443d4532c710c514cb375414532cd150514cb944314532d5d0c514cb364314532cd10c514cb544314532c510c514cb3b54d4132ce153504cb9843d4132dcd47504cb7051d4132ce90f504cb3843d4132c710c504cb3b5414132ce150504cb984314132dcd44504cb705114132d6d0c504cb3a4314132ce10c504cb584314132c610c504cb6b3214132d68c8504ca5e63d50329d987540ca7561d50329d986540ca756195032c794c430ca3e64948328f592520ca5f654c832b6181320ca6f654c832e390d320cae8604c8328f992510ca3d64944328fd91500ca3c64540329dd85500ca746154032c794c43d071d5310f41a798e42d06b66190b41c794e43906b561d0a41d5587535071f6414d41d5d84535071c5390d41ad986435071f5310d41a798e425071c5390941ad986425063e6510941c714c425075453d0541c714e415071e5310c41ad584431065e63948419758e52106b561d08418fd9542106b564904418fd95411069c63504419dd9541106d46350441add9541107376550441e5d8d41106b46350441e518d41106946350441cd94d41106b76250441cd94941106b4605044197d8d501065c63540419
  | 6 => 0x3b200076400000000042851e1b60da90a31887000096005c55c2e80d200076e1027407ea26e0005100000000000005965028bc0000000000002400000000002844aa000a280000000000000b40000004ca0005420000000000009f800065c646696a6027409884a4b24d87823762a65ca93c4de0cc00085672e00009c19200000000000000000000000101100000400000000200100000000000200d00200000000600100000000500000300400200000800101c00600000200000200700100100500000000400e00100100000100000500000000300b00000100400102600000700100200201000000000200700100000100100100000000000000200500400000200200000000400500600900700000000000000100200400000000800100100500300000300400000100000100100500100000200100200000100500500000000300200000000200000100300400000c00500600400400500000100400000000100300200d00000000200700400200000100300000300500200200600200200700100300400800100001501700200000100700900000300201400000500100000100000000000000400000b00300100201300000100100700000000100100100000000500100000700600000000000000000700100400000100300600500000100000000000000000000000000000600000200000000500000000400200300000100500000000001800000300400000100000300c00001800000000000000600000100200500000100400100100100000000300000000100000200101e00300000300500200100500000800000000100200400100000100300000000000000000000600000300500101000000100000000000300300100000000000100001400100000300200100200000200100100800000300400000000100000901300100300100300b00800200400000000200300100800500100000000100000000500000100300100000100200000000000700200000100100300000200300000d00a00000700000000500000300000200300700300500000100200000000300000600100000300c000001002000002000000004001002002000000003000002001000ad9874390eb561d0e439dd855290e746154a439d9865090e756194243cbd4a5290eb76154a43ad1855290eb66114a43ad5845290f375194643ab9885190ead6214643ab98b5090ead62d4243ad9875090eb561d4243ad9865090eb56194243cd90f5150f574314543cd90c5150eb661d0c43ad5874310e3f6550c43add854310eb46150c4397d954310ed46150c439d9865210e7561948439bd895010e6c62540439dd855010e746154043c798e5310e9d6294c43a79865310e9e6094c43ad9875210eb561d4843ad9865210eb56194843cb5485210eae62d4443ab58b
  | 7 => 0x7de0000000000000e400045820e0008cc0006d2666000a0c0008680008162dc98091a0004b60008623cc6ee86446200036e0001b422040c36600000058e0007e44260000000000000000000000000004543ea0001d000000093e6520906e000000038e0000006160000008100000000006ca1cc0009e00000009c000092c00000011000089c0007f817400095054c24a0009bca3400000000029e0000000009d00000008ac4d26f064c8b00004e40005fc41e00091c4a60000001160008e6000000a002b20000008d889e0000000000000003ac79a85e00000000000041c6d472070e000322476330a5c34400000059c0941be00000c0000001905e800003200000000000000627663440000a3d06580001280001701e03427fc0000000009888b80001aa6980000000000000000006e8858000a748385d23960000000000001a400033e2289045460008422ea0000002aa28e3fe0002868aa6c003a0000008a82cc0008d439e0000001d6a3009266800000068a2165c065e89816400023641a7e04ac9f016a15c5500003ee91e9d42bc6fe0000760000000003460007a642200050e0004fe00037a7423bc0000000000001ec7245126d852200000000000000000000000030a00054000000094c97a00000033a97c0008dc9721229840006b42b40f828000400000056a00000000099c0a615400075a8144f80006d04a895400072c0007c20fa0000002600000000000000009c2000000000a5802e4ae77c3d41e23049fe52a58a3da3c60d679e29000056200000000017c0000000000000000000000006e60007b453640800026c44c8f40000000004a45b04e88ae10c13e8122fe0000001342e01c005e0008320000005de2220000000009420000000000003d80001b20000000005aa0009f400000000000000000008288a3f00fe3166600000007f4000a5486600000000010a00039a000000000246a1248000000000080e000000000000a5a0000003c48044a2a2a45e0c09de8e26aa0002ee0002c80007781c457200000000020200061a29a000000624000000a4a0000009460dea6c4a00000560006941ce2c21040a45a40006120000000008360002f238471022a0002ce00048400098c2268ba0000000001e80000006de5c86f40000000002d65bc0000005b438a000a4e05a0ca00026647e59400000014c3f60000f25f60000ac00000088e65000083c0000000002f4a3e0000004da8a05e27888d0a6400061800015215a00026a3d24168a4a260000000000000003380003267bc00021c9d80004dc00000086a40400082ea4400043c2a404e9020000007ec81e82800050000000000040a73e310000a506422b87d06ce11200000000000000000000000075067ea0e5ba0000000000006625566b68ca4380004700e20001ca00000068207800
  | 8 => 0x4000018c3360000000000000007a40005c464a7180000009900009b40008c400000058600008e00094015e66c00000000073c69226400001800000075200080ca6a2fa2d2a680000006444c0a4281c0000000003483f40000000000002e67609a679052860490800000034c8300000003c022e00000084403e0000001ae5980000002244147260005a8000a700340000000001a637405430c12a00004c34046c34a1660468525ea0d838219656e2509000000000001463a200000000000044e4d02147300000000000000360009a40003008180001761e657c0001e40500000000000000002ac07211400000000046e0000006760e000000000000000000000000000000019c6565d44fc3149780000000000000000002c00000001a876252655a46653237c69099e00006e96e53e8c27ca9f6a6600002621a8be0008060005707709ee5600000000009442568ce0000001ac87400089a00000000007e0000000000000000000000000005665ae00051c0000008f80002de0000008ec7c871e03000006c2927029826cc2343ba00002232c1c80000006881c64e238882a35835000065a9e60007aa00000059a72a66e0001189566bc8c6000000194600a4c1608ee0160002ae0008900000703d660a09e1260001b80082b023e0004f60001fa00000000000000059e00000000025e0000000000009e81864948d20000000000001626140006480000000003e623806a68000000000000000082c0009322962f639200062800036475e2be9d200070a2d094a0000000000007e6000000000000000590000000000a48456000a0493a1ba0003f200060628c0f493678e19e2040682c613c4e035e08495c77a000678000000a360000005e600046a0003342823dc00000000000037e0000000000000000000009a80000007d219a61ca2c1003a098a4342ca8269ec00000000098e0004ee2306080000000001a20fc4723a400031a5ce0001a00009581580006e49a200067a7041fe0000003869486f652ea3a8c8124a5e36c0000c26306645760a00000000000005b60000006fa0000006c40000002e20000000000000005140005ee9529661de00000000050c9ca0000000000001080000000000000000005b8850a2096a0007cc0000000000003a80000006c800000003c13243e0007d88ea0865800000003986d60b00000000ba0000003e400006225c0000000002322189620ae87e7c40003c20004741f45547442b61f20a89247946ec18207a0008f23de5ac00076c0006841da7e806678624c0007064240000bc4f014002428800012c0003b00d00000000000002e482451829c3900202ec42c5342c492088800076877e32a7be6dc0b63680000000009145f86740000000006da86e0000ee0004460000006ac53a378000000000000150000000000876
  | 9 => 0x8960007545cc6a06c20000001dc00000031c0001f6418000a1600078a7b80f00000000001980002481ee9760000000006320000120009743b4000000a028221880000000000007b04f40000000009cc6ba00018e000602a2450600048e04255297e5c60000009c602a6f839c1bc7482f849e106a229183027a24026ea2da4526a48de81a7761307368a269a1209106a82005302a27ee492002a6e00018a8783120003be96455861e00000088c0003ca10e0000003540000dc00027e8e00007d658845a1f87742780001840000000000000009aa0009127809964ea53808057856424443686c28a7a000050400000026200004848a00000008c9ae8da0003e24c892269c00000054467c5a280800056820633274644083e7345be0f67b251a34e2ba42a5fa1568006be7664600000000000b20007920004b074e0000600005a6000000a5258400020a21270c0003e80a27d4738000000a623063709c87ac92600000000038c7b60002d400017a38040e8824bc00043a52400000000060e2104884b89be0006360005c22680000000000008b200000000085c9e43560000000000001448860000007da7e20000008e40c463e0140002580000000000000000000c81780000000000000004be000a1a9e2000a1c8924d492800014a7567980000000000000004e60000000000007f63aa54e0000009980000000000000004ce00000000000000062e21e0000009b262a0000006c60aa48200001a0000004420000000000000000002940000006720008d600000045c052992000a14722000a466227840000000006547f200000011a2f09380000ce3a67729da69e71a0000006a690625a90e9b60005d04906389b86fc2700000000000009b068c3f850a00047c00000088000032000064e4985200005928a604a75c42000017e9163ae000000000548728000000000000000a182a800057a1ea02c5f4a0607432e7fa00055e6b242e0d400063c92e99a0e60880009ac3082520000001420c60007120000ea00000000000000000000000062c0000003520000000008944ec796136a2e4c674a6b01d20281d4a104f26b87dc70027a0009c40007ce00014e0000000000000000009fc0005f063a5ec80266a49c00096c7c60003b684000011c000000000000a323e00001802721721d8a0a3c858200044a0000649a07ba8b405800e52c5080009d601e8604fa00000000000000098600054a0000008f600020807c00000049a0000000000000000000009ba4488fe7f036a5161c20007ae000000000000a7200085400000000035a0000009dca3c0008b657446400000085a0004cc47822c00000078c4109f28720b884c00000084e00000012e0be30e3620000009340962d800000000000068e00079c00057e80a0e80004b40000002a0a409ce0000000006
  | 10 => 0x8a00097037213890c3fa0008e89940000008847fe8200003940000000000000000000000000000000002420000381b00000008f03ce0000000007c07a81f000016e11e2fc8460000005da00056c00048c00087c5a06a271600016861060c53c000000000a565fe95e000000406848328708000000a0800000035c83a4d600000016c00073a0000004ba00013a5d831e8fa0000ec5f2298148444000000a1e0000000000000000001fc0000000000000004124c40000003ec0000003240000000000007320000000000000000443b892a20c0000000008344504325b20006e224e0005e4a764966705dc9ea58c4c20108c06269fa62087a6ae000000000a3800043023a00000023c5e08fc00093000009a00096800000074c71c00000000047a6863fc27c94e6f200075800001c00000076a71448633c2545d636004095a46800
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x18c957610e520c78221aa4290638599443d0831c2cca21c8418e156510e420c6c2b908621063259d260cc831c2aca21c6418c967690d320c74821ec099063a490c604c831d20863026418c9674991320c669384c899063a4193604c831ca6ca3026418e9364181320c748320c099063b0d88604c83192cec21aa018e8443d89500c742218c4a8063a110e6214031d0886b10a018d147358654c870b2a0c6a0e43451cd540c721a28e8a986390d177510c31c868aba88618e4385dc46355221c28e231aa910e1463185548868d386a621c43451cd54d0621a28e6aa08310d1473553318868a39aa818c4345dd4430c62186eecaa64310d1473553218870aaa4c790c43151cd6195121a28e6aa08290d3070550414860e39ac828243071cd6494421c28a831a8210d147454c310870ab288618843a110d620c421928e6b244210d147154c43d024a39ac3a1681159cf6154a40a2ce3a9886a049473587425030a29ac3a12818914961d0940c2cc621ea2a060c63149415030a318a2a0a8185994430c540e0887a9062a070443148315030bba0c6a8881851d06354440c28c721aa2206146310d511028b39c84a88818518e4254440c28c6212a22051473546411028a39aa22088185d94430c440a28e6a8e802051473545401030a31aa2a0081891895150040c30a83026498550704c8514c28b3a88618a6185994430c530e0887a90629870443148314c28a38aca21861621c96010c30c288630aa41854572150310c28a3a2a418861701c9600c430c2cc818ca0184547358654c828a38aa621e41071cd6494720a28e8a98639045473584548828b38ea621c41459d3530c620c2cc930ea69061464184534828b38ea621a418598c43d4520a2ce7aa0629051674d4c314828b3a88618a41451d4430c520c2cca21862906146510c314830a320c329841851906154c20c30c8302a610648621815308328308c0a9841451c55310c20a1aea21e64106146310d510828a39aa818841451d1530c420a2eea21862105157510c310830bb28861884185594430c420c8acb99062106196510c3008328b286218041851506350710a28e8a9863884947359221c420f39ec8a9421459cf5410610a28e6b08a8885147114c434430a2a0c6a0a21151d85350510c88c6292828851673d50314428b3a6a618a21459d4430c510a28ea218628870443d483144382218a418a21251cd648851086aec2a442886156414e2144312b20a510a2185dc46355010c28e231aa80861463185540428b38ea621821075d85310c10a1ae4298860841c73593520428a39aa9a0821451cd5410410a28e6aa6620851473550310428bba886188210ddd954c8410a28e6aa642086155498f210428a39aa810821451cd54c4010868ecaa2200851473551100430aaa0c688021895506244010
  | 1 => 0x31a29708b3c9acd0780f0f02a42258ed3a4e1cb559e656f211a4ab15b00747b4da2434aa0036d52d6220cc5c16260c4001205010d2b60400110770007000dd360c11e66471f5a8b1681c14ad9402f19874000b4ec9161120001b398d8fc722fb80c21051af4005b20960164a3d2a16ee1000d16aa706085449c101789a7c150000024642b0a4ba63a6470000bb4400941b958a01f0c000000037b5c000d079817e00001a9b85c652f892195a2e4125d649b58a014baec00276595ca82829a6028924ab347e001f16934b01aab5667f070980c8d3888d3e4508a5858c3310a502052c8f40e000024c4a00002999c00002780000000000022000000000622bc06000019caad828b7d5c645200086e24380164c609b4c9e820ea18dcc101001420017a0c64750021400006d0008ea00011920404600005058200a100103c0c2c010408a110003400020a8140204000001604008002a03000044e070001402030618c0a00040e83600020040e010c800021007808000e000041a06028003e28000a800020b83c6e22004947158a5310e4b38cc12988785dd06354742c28e831aa3a16146390d51d0a8a38aa621c85251cd61d0a42c2ca6b0e85216146310d5190a2a39ac228285451c55310c42928e6b0e84216144398650ccb88218a3a8265469d44314132e2087a88a09971043144504caa53968628265549c74314132e1087990a09951a748c8504caa938c6428265a290c604c832928e6b0e8520d0e72d9053506a3396c229a838514e6190d41c28a730c84a0c9473587421070bb28c6a088385dd46350441c28c729a8220d1673949411070a31ca4a0883451cd4154041c28c6a0aa020e2462505501068b39ea92a663a410c604cb31b80e09906598e1a54181328c725290c099463435ca6510c31a2aea2188218c947458a530c64b3a4c129863315cb6510c31b0ce5b288618d8572d94430c6c3394ca21863615ca6510c31c2aca3288618d1575d88430c68abacc421863a15886210c31a2eeab008618d8772580430c6c2392c021863619c86010c31b0ae430086
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x10000c428400012038c0b215a000000000c08840a0682dd06354742a0682dd46350441c04731894154041a0682dc463552218148755263c8621c047314961d0940a0682dd06354440c04731895150040814875905388510a04835905288510a0682dc463550108148755263c8410814875506344010a04835506244010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
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
  | 4 => packedAt s2K4 (56272+((h/446+packedAt s2K4 (50920+(h % 446)*12) 12) % 2352)*12) 12
  | 3 => packedAt s2K3 (11798+((h/75+packedAt s2K3 (11123+(h % 75)*9) 9) % 273)*9) 9
  | 2 => packedAt s2K2 (860+((h/4+packedAt s2K2 (840+(h % 4)*5) 5) % 28)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffff81ffffffffffffff0fffff
  | 1 => 0xf81fc07f80fff80ffe0fc0f81f07ff80f6327c
  | 3 => 0x1fffffff03fffffff000fffff81ffff83f8f
  | 4 => 0xffe0007ffffc000fffffff001fffe000ffc3f0
  | 5 => 0xffffff800000000fffffffffe0000000fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8404508922091010052c929250a28aa02d4b5
  | 1 => 0x52ca93390e4923579605585b0b475d0676325c
  | 3 => 0x45130a52241a464aaaa0209652d11654b82b0a
  | 4 => 0x619a2c644890746ccd39b2041ce58418dd43e0
  | 5 => 0x861c307870e3878f71ce3ce780861860efbc00
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaaa00aa88aa00eeaaaa00aa88aa00eeaaaa00aa88aa00eeaaaa00aa88aa00eeaaaa00aa88aa00eeaaaa00aa88aa00eeaaaa00aa88aa00eeaaaa00aa88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36675
namespace PEqualNP.Outside.L_meta_36675
open PEqualNP.Outside.L_meta_36675.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x3a9400029f0030008285c00148ac0212c00509269802846a8ca5009c70020000002a3c00000b41a2161800258446980878e9c2468d8108b049207002041140102ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xd801418400781d4444049000008495656c3c880c9c24000150010d28000000002cb534002120a449191558ac7098000000e500f189795c00dcc068305ce83960506408d5397d3c0000b8c800101800002854ec00e000fd247568f9314c5880a0607d74157000cd1d0401118000c400b08d546d08f44cbc004034a800d12d480202140c0c0c00020206400002021a00000602100018040000060c0e10060c14057b5050ef0a0a1dd94742baa8e855e5310abaa6214fd51329e2a26577514cae8a2995ed4132bc282653e540ca7aa8194f943419eaa483b75150678a0a0cf950419f2a4633d548c6f4a118de542319f2a0633d540c76a8390cf952219eaa4433e540867aa810d794c21aea9843b541086f4a010de54021af29e815d53d027aa3204f94240afa9a815c53502eca2205d54440db288813d511036aa2204d544409f28081ba501027ca9984f55330dc206619f418c33a83185794230cf204619c408c27ea8984f15130dc200619f410c33a82185794030ed28061db400c33c80186710030ec2006198400c27ca9904f55320af29e415d53c83b061904fd51209e2a2415f53482b8a6905dd4520ba28a41d8300827ca9884f55310af29e215d53c436a83884fd52109e2a421d8308427ea8884f15110afa9a215c53442dea4885b14910daa0a21d8304427ca8084f55010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x8c012000188a0400052479602602028e69c41800088000000108008302586054c42cc50550086b16110330a5584408c2b16110030a6181410c29a6090030a5584400c2d16110030e4984400c2996110030e4584400c29161100308d58654c831a540c320c615030842346550510c91494144318540c110d21483044391410c110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x1085117195030c82883aa8218221c0149410c110
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
  | 4 => packedAt s3K4 (2937+((h/33+packedAt s3K4 (2673+(h % 33)*8) 8) % 130)*8) 8
  | 3 => packedAt s3K3 (840+((h/7+packedAt s3K3 (798+(h % 7)*6) 6) % 33)*6) 6
  | 2 => packedAt s3K2 (149+((h/1+packedAt s3K2 (147+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc07ffc07ffff0383fffff81ff83ffe00fe73fc
  | 1 => 0xff81fff81ffffffc0fc0ffe0ffc3ffff638c7f
  | 2 => 0xffffffffe07ffffff000fffffffc1fff83ff8f
  | 4 => 0x1ffffff8003ffffff0000ffffe003fc0ff0
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x530c447145122480b2c93909380532182e31bc
  | 1 => 0x8524c890c824619405584b284a4354a9628455
  | 2 => 0xa111122034882295020945294a80952815a8a
  | 4 => 0x2c59a244920ecb4e69b20610e7328063d40f60
  | 5 => 0x3061c3871c70f3f38e3ce79c06231183fbe000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36675
namespace PEqualNP.Outside.L_meta_36675
open PEqualNP.Outside.L_meta_36675.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 1 => 0xe0fff81f81ffffe0f81ffc1ff0f80fffb38ccf
  | 2 => 0xffffffe001ffffff001fffffff000fffc3ff0f
  | 3 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126014a690c16315c
  | 1 => 0x4a6450c832930ca05b09650a90d0aa54b284c5
  | 2 => 0x8488a2034524114b04128a552a0144a9415b0a
  | 3 => 0x14d1049260365a729640c219cca58031e80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf38188c608c1ffe000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeae0eae0eac0eac0eae0eae0eac0eac0eae0eae0eac0eac0eae0eae0eac0eac0eae0eae0eac0eac0eae0eae0eac0eac0eae0eae0eac0eac0eae0eae0eac0eac0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36675
namespace PEqualNP.Outside.L_meta_36675
open PEqualNP.Outside.L_meta_36675.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x604a208002bf43bd43be40bc40de30dc30
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x20270a0a1e610030
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (104+((h/2+packedAt s5K4 (96+(h % 2)*4) 4) % 9)*4) 4
  | 3 => packedAt s5K3 (56+((h/1+packedAt s5K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3fffc0fffffe0c1ffffe0fff07fffe00f3f3fc
  | 1 => 0xc1ffff03f07fffe0f83ff0fff8780fff4c7ccf
  | 2 => 0xfe0ffffc007fffff003fff0fff800fff8f8f0f
  | 3 => 0xfffffff800fffffc0000ffffff003f00ff0
  | 4 => 0xfff0000000000ffffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x84204628a0101005284e0113008a621811b15c
  | 1 => 0x94448a1904a484a05a1290a54850a4a94454c5
  | 2 => 0x8a914406949094b04252a0a950149528a8b0a
  | 3 => 0x294e20924c0dae729681888ce6658063e00ea0
  | 4 => 0x318c38e38e71cf9ce739ccc0c4460183ff6000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeae8eac0eae8eac0eae8eac0eae8eac0eae8eac0eae8eac0eae8eac0eae8eac0eae8eac0eae8eac0eae8eac0eae8eac0eae8eac0eae8eac0eae8eac0eae8eac0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36675
namespace PEqualNP.Outside.L_meta_36675
open PEqualNP.Outside.L_meta_36675.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001007fd5001fe54007f55001fc54007fd4c05fe53007f54c05fc53007fd0c05fe43007f50c05fc4300ffd4803fe5200ff54803fc5200ffd0803fe4200ff50803fc4200ffcc803fe3200ff4c803fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41017fcc401fe31007f4c405fc3100ffc8403fe2100ff48403fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc40017fcc001fe30007f4c005fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42006ff48210037f2410801bfc2084007ff8842000fdc421001ff62108003ff65440017fb2a2000dfd9510004feca88003fe654400f7f32a2000ff59510005faca88003fc654400f7e32a2000df19510004f8ca88003ff64440017fb222000efd91100057ec888003fe64440017f3222000ff59110005fac888003fc64440017e3222000ef1911000578c888003ff5444001ff2a22000ff55110007f8a888003ff63440017fb1a2000f7d8d10005bec688027fe63440057f31a2000ff58d10005fac688027fc63440057e31a2000f718d10015b8c688003ff5344013ff29a2000ff54d1004ff8a688003ff4344013ff21a2000ff50d1004ff88688023ff62440117fb122000fbd8910005dec488023fe62440037f3122008ff58910045fac488023fc62440037e3122008fb1891000dd8c488023ff5244011ff2922008ff54910047f8a488023ff4244011ff2122008ff50910047f88488023ff3244011ff1922008ff4c910047f86488003ff5144007ff28a2000fd94510007faa288003f55144007fe28a2000ffd051001ffc8288003fd4144007fe20a2009ffcc51001ffc6288003f63144001fe98a2000fd4c51001ff86288023ff2144007ff10a2008ff4851001ff84288003ff5044001ff2822000ff54110007f8a088003ff4044001ff2022000ff50110007f88088027ff3044001ff1822000ff4c11004ff86088023ff2044011ff1022008fe88110047fa4088023f92044011fe1022003ffc411001ff62088003fe1044001fb0822003ffd941001dfeca0800ffe650400f7f3282003df99410004fcca0800ffd65040017eb282003df59410004faca0800ffc65040077e3282003ffd901001dfec80800ffe64040017f3202003ff59010005fac80800ffc64040077e3202000ffd5010007fca808003fd5404001fe2a02003ffd8c1001dfec60800ffe63040057f3182003ff58c10005fac60800ffc63040077e3182000ffd4c1002ffca608003fd530400bfe2982000ffd0c1002ffc8608003fd430400bfe2182003ffd881001dfec40800ffe62040037f3102003ff58810025fac40800ffc62040077e3102004ffd4810027fca408013fd5204009fe2902004ffd0810027fc8408013fd4204009fe2102004ffcc810027fc6408013fd3204009fe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff08410035fcc008003ff5004001ff2802000ff54010007f8a008003ff4004001ff2002000ff50010007f88008017ff3004001ff1802000ff4c01002ff86008013ff2004009ff1002004ff48010027f8400800fff1004007fb8802003ff8401001ff4200800ffd1004001fa8802003fe44010
  | 1 => 0x2ff614c001ff30a6000ff58530007f8c29800efc614c001ffa8a6000ff94530007faa298003fc514c001ffa0a6000ff90530007fa8298003fc414c005ff98a6002ff8c530017fa629800bfc314c01bff90a600dff8853006ffa4298037fc214c0057fb026000ffd4130007fca098003fd504c001fe2826000ffd0130007fc8098003fd404c001fe2026002ffcc130017f6609800bfe304c001ef1826002ff0c130017b8609800bf8304c01bff902600dff8813006ffa4098037fc204c007ffb2e2003bfd971001ffccb8801efe65c4007feb2e2000bf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc988002fe64c4007feb262000bf5931001ff8c98800efc64c4001ffaa62000ff95310007faa988003fc54c4007ffb1e2003bfd8f1001ffcc78800afe63c4007feb1e2000bf58f1001ff8c78800efc63c4001ffa9e200cff94f10007faa788033fc53c4001ffa1e200cff90f10007fa8788033fc43c4007ffb162003bfd8b1001ffcc588006fe62c4007feb16200bbf58b1001ff8c58800efc62c4017ffa96200bff94b1005ffaa58802ffc52c4017ffa16200bff90b1005ffa858802ffc42c4017ff996200bff8cb1005ffa658802ffc32c4007ffa8e2003ff9471001feca38800ffd51c4001faa8e2003ff1471001ffe838800ffe41c4007fea0e2003ff1071001ffe638800ffe31c4007fb18e2003ff4c710007ea638800ffc31c4007ff90e2003ff8871001ffa438800ffc21c4001ffa862000ff94310007faa188003fc50c4001ffa062000ff90310007fa8188003fc40c4019ff9862000ff8c310007fa6188033fc30c4017ff906200bff8831005ffa418802ffc20c4001ffb2c2000bfd9610007fccb0801efe6584001feb2c2000bf59610007f8cb0801efc6584001ffb242000bfd9210007fcc908002fe6484001feb242000bf59210007f8c908002fc6484001ffaa42000ff95210007faa908003fc5484001ffb1c2000bfd8e10057fcc70800afe6384001feb1c2000bf58e10057f8c70800afc6384001ffa9c200aff94e10007faa70802bfc5384001ffa1c200aff90e10007fa870802bfc438400dffb142006bfd8a10037fcc508006fe628400dfeb142006bf58a10037f8c508006fc628400dffa942006ff94a10037faa50801bfc528400dffa142006ff90a10037fa850801bfc428400dff9942006ff8ca10037fa650801bfc32840117eb0c2000ffd461001ffca308003fd5184007fe28c2000ffd061001ffc8308003fd4184007fe20c200affcc61001ffc6308003fd3184007fe18c2006ffc861001ffc430801bfd2184007fe10c2003bf98210007fea108003fe5084001fea842000ff14210007fe8108003fe4084001fea042000ff10210057fe6108003fe3084001fe984200aff0c210037fe410801bfe208400dfd1
  | 2 => 0x4008ff88620043bc4310023ffb10800fbfd884007ffcc420006fe621001ffeb10800fbf5884008ff8c420006fc621001fffa90800fff9484007ffaa42003ffc5210023ffa10800fefd084007ffc842003ffd421001fdea108011ff1084007ffe642003ffe321001ffe990800fff0c84008ffec220003fe61100077f3088000ff58440005fac220047fc6110001ffa888000ff94440007faa220003fc5110023ffa088000ff904400077c8220003fd4110023fe2088000ef10440087fe6220003fe3110001fe9888010ff0c44007ffe422003ffe211001ffe908800fff08440095fcc020003ff5010001ff2808000ff54040007f8a020047ff4010001dfa008000ff90040007f48020003fd4010001dea008000fe50040087fe6020043fc301001fff900800fff8804007ffa402003ffc2010001ffb2c6000bfd9630007fccb1801efe658c001feb2c6000bf59630007f8cb1801efc658c001ffb246000bfd9230007fcc918002fe648c001feb246000bf59230007f8c918002fc648c001ffaa46000ff95230007faa918003fc548c0057eb1c6002ffd4e30007bea71800bfe538c005fea9c6002ff14e30017b8a71800bff438c001efa1c6002ff90e30017fa871800bfc438c005ee21c600effd8a30075fec51803bfe628c0037f314600eff58a30075fac51803bfc628c0037e314600effd4a30077fca51803bfd528c01dfe294600effd0a30077fc851803bfd428c01dfe2146002ffcca30017be651800bfe328c005fe994600ef74ca30017f86518003ff618c001ff30c6003bf98630007fac318002fd618c001fe30c6000ffd4630007fca318003fd518c001fe28c6000ffd0630007fc8318003fd418c001fe20c6002ffcc630017fc6318003de318c005fe98c6002ff0c630017b8631803bff218c01dff10c600eff48630077f8431800afe608c001ffa846000ff94230007faa118003fc508c001ffa046000ff90230007fa8118003fc408c005ff9846002f7cc230017f6611800bfc308c005fc184600effc8230077fc411803bfd208c01dfe1046000ffd9530005feca980037f654c0013fb2a6000ff9953003dfcca98003fd654c0017eb2a6000ff1953003df8ca980037c654c0013e32a6000ffd9130005fec898003bf644c0015fb226000ff99130005fcc898003fd644c0017eb226000ff19130005f8c898003bc644c0015e3226000ffd5130007fca898003fd544c001fe2a26002bfd8d30017fea69800bfe534c005fea9a6002ff14d30017fe869800bfe434c005fea1a6002ff10d3006ffec498036ff624c01bff3126001bf9893006ffac498036fd624c01bfe3126001bf1893006ffea498037fe524c01bfea92600dff1493006ffe8498037fe424c01bfea12600dff10930017fe649800bfe324c005fe9926002ff0c930007fec29800
  | 3 => 0xe2868017ffcc3400bff861a004fff20d0027ff1068013ff4834009ff841a0003ff65900017fb2c8000ff9964003dfccb20003fd65900017eb2c8000ff1964003df8cb20052fd6490001ffaa48000efd5240007fca920003fd5490001fe2a48000ef15240007fec72005bfe63900057f31c8000ff58e40005fac72005bfc63900057e31c8000ffd4e400b7fca720003fd539002dfe29c8000ffd0e400b7fc872005bbe4390001fea1c8016ff10e400b778872004bff62900257fb148012ff98a4000dfcc52004bfd62900257eb148012ff18a4000df8c52004bff5290025ff2948012ff54a40097f8a52004bff4290025dfa148012ff90a40097fa852004bbd4290025fe2148012ffcca40097fc652004bfd3290025fe1948000ffd8640007fcc32000efe6190001feb0c8000bf58640007f8c320003ff5190001ff28c8000ff54640007f8a320003ff4190001ff20c8000ef90640007fa8320003fc4190001de20c8016ffcc640007fc6320003fd319002dfe18c8012ffc8640097fc432004bfd2190025fe10c800fbf98240007fea120003fe5090001fea848000ff14240007fe8120003bf4090001fda048016ffcc2400b7f8612004bff2090025ff1048012ff48240097f84120003ff65500017fb2a8000dfd9540004fecaa0003fe655000f7f32a8000ff59540005facaa0003fc655000f7e32a8000df19540004f8caa0003ff5450001ff2a28000ff55140007f8a8a0003ff63500017fb1a8000f7d8d40005bec6a0057fe63500057f31a8000ff58d400aff8c6a000afc6350001ee31a8002b718d40007fea6a0057fe5350001fea9a8015ff14d40007fe86a0003bf435002bff21a8000ff50d400077a86a0057fc4350029ffb128014bfd89400a7fcc4a0006fe6250029feb128014bf589400a7f8c4a0006fc6250029ffa928014ff949400a7faa4a0053fc5250029ffa128014ff909400a7fa84a0053fc4250029ff9928014ff8c9400a7fa64a0053fc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8003bf18540007fea2a0003fe5150001fea8a8000ff14540007fe82a0003fe4150001fea0a8000ff105400affe62a0003fe3150001fe98a8015ff0c5400a7fe42a0053fe2150029fe90a8014ff08540007fea0a0003fe5050001fea828000ff14140007fe80a0003fb4050001ff2028000ef901400affe60a0057fc3050029ff9028014ff881400a7fa40a0053fc2050023ffb288000bfd9440007fcca2001efe6510001feb288000bf5944008ff8ca2001efc65100277f3208000ffd50400077ea820047fe5410001feaa08011ff1504000778a820047ff6310021ff3188002bf98c40007fac620002fd6310023fe3188002bf18c40007fea620043fe5310001fea988010ff14c4008ffe8620043fe4310021df2188000ff50c
  | 4 => 0x6eff6254037ff312a001bf989500dffac4a806efd6254037fe312a001bf1895003ffea4a806ffe5254037fea92a007ff149500dffe84a806ffe4254037fea12a01bff109500dffe64a806ffe3254037fe992a01bff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a800efc615400fffa8aa000dfd4550007fca2a8003fd5154001bea8aa007ff14550007fe82a8003fe4154001fea0aa000ff105500e7fe62a8003fe3154001fe98aa01cff0c5500dffe42a806ffe2154037fe90aa01bff0855003ffea0a801ffb5054001ff282a000df941500e7fe60a8073fc3054037ff902a01bff881500dffa40a806ffc205400f7f328a007ffd905003ffcc828002fe641400ffeb20a000bf5905003ff8c82801fff541400fff2a0a000df9505003ffaa82801ffc541400fbe2a0a007ffd8c5003ffcc62800afe631400ffeb18a000bf58c5003ff8c62800afc631400fffa98a007ff94c500cefca62801ffd531400ffe298a007df14c50007fe8628067fe4314001fea18a019ff10c5003ffec42801eff621400fff310a001bf9885003ffac428062fd621400ffe310a001bf1885003ffea42801f7f521400fff290a007ff548500c6faa42801ffc5214031ffa10a018ff908500c7fa8428063fc4214031ff990a018ff8c8500c7fa6428063fc321400fffb08a007ff9845001dfcc22801ff661140017b308a007ff58450005fac22801ff561140017ab08a007ff1845003ffea22801ffe5114001bf288a007ff5445003ff8a22801f7c5114001ffa08a000ff90450007fa8228003fc4114033ff988a000ff8c450007fa6228067fc3114031ff908a018ff884500c7fa4228063fc21140357f300a007ffd405003efea02801ffe501400ffd280a007ff54050006faa02801ff95014033ff980a019ff0c0500c7fe4028063fe2014031fe900a018ff0805008ffecba0002ff65d0001ff32e8007bf99740007facba0002fd65d0023fe32e8007bf19740007fea9a0047fe54d0001feaa68011ff1534008ffec7a005ffe63d00057f31e8000ff58f40005fac7a0047fc63d00057e31e8000ffd4f400bffca7a0003fd53d002ffe29e8011ffd0f400077e87a005ffe43d0001fea1e8000ef50f4008ff887a0047ff62d00277fb168013ff98b4000dfcc5a004ffd62d00277eb168011ff18b4000df8c5a004fff52d0027ff2968013ff54b4009ff8a5a0047ff42d0027ff2168013ff50b4008ff885a004fff32d0027ff1968013ff4cb4009ff865a0047ff61d0001ff30e8003bf98740007fac3a0002fd61d0023fe30e8000ffd4740007fca3a0003fd51d0001fe28e8011ffd0740007fc83a0003fd41d0023fe20e8017ffcc740007fc63a0003fd31d002ffe18e8013ffc874009ffc43a004ffd21d0027fe10e8000ffd4340007fca1a0003fd50d0001f
  | 5 => 0xc531017ee629880ffe314c407ef18a6203ff0c53101fb8629880bf4314c441ff90a6203ff88531107fa429880ffc214c401ffb026200bfd8131007fcc098803fd604c401fe3026200bf18131017fe609880bfc304c441ff9026220ff88131107fa4098883fc204c40fffb26a007ff99350005fcc9a801ffd64d40017eb26a007ff1935003ffea9a801ffe54d400ffeaa6a007ff1535003ffec7a801ffe63d40057f31ea007ff58f50005fac7a801ffc63d40057e31ea007ffd4f5003efea7a801ffe53d400ffea9ea000df54f5003ff8a7a8003ff43d403fff21ea000ff50f500fff887a801fff62d400f7fb16a007ff98b5000dfcc5a801ffd62d403d7eb16a007ff18b5000df8c5a801fff52d400fff296a007ff54b5003ff8a5a807bff42d403dff216a01eff50b500f7f885a807bff32d403dff196a01eff4cb500f7f865a801fff61d400fff30ea003bf9875003ffac3a8002fd61d400ffe30ea007ffd475003efea3a801ffe51d400ffea8ea000df5475003ff8a3a8003ff41d4001ff20ea000ff50750007f883a807fff31d4001ff18ea000ff4c7500fff863a807bff21d403dff10ea01eff487500f7f843a807fff30d403ffe186a01effc83500f7fc41a807bfd20d403dfe106a01bbf59650007fec928003fe64940017f324a000ff59250005fac928003fc649400fffaa4a000ff95250006fca928003fd549400ffe2a4a000df15250007fec728077fe63940057f31ca000ff58e50005fac728077fc63940057e31ca007ffd4e500effca7280777e5394001fea9ca007ff14e500eef8a728003ff439403bff21ca000ff50e500eff8872806bff62940357fb14a01aff98a5000dfcc52806bfd62940357eb14a01aff18a5000df8c52801fff5294035bfa94a01aff94a500d7faa52806b7d529400ffe294a01affd0a500d7fc852806bfd4294035fe214a01affcca500d7fc652806bfd3294035fe194a000ffd8650007fcc32800efe6194001feb0ca000bf58650007f8c32801fff5194001ff28ca000df94650007faa32801ffc5194001be28ca000ffd0650007fc8328003fd4194001fe20ca01dffcc650007fc6328003fd319403bfe18ca01affc86500d7fc432806bfd2194035fe10ca007bf9825003ffea1280037f509400ffda84a01dffcc2500eff8612806bff2094035ff104a01aff482500d7f84128003ff64540017fb22a000efd91500057ec8a8003fe6454001feb22a000ff19150005f8c8a8003bc64540015e322a007ffd5150007fca8a8003fd545400ffe2a2a000ffd8d50005fec6a8003df63540016fb1aa01cff98d50015fcc6a8003fd6354039fe31aa002bf18d50007b8c6a800adc635400fffa9aa000dfd4d500e7fca6a8003fd5354001bea9aa007ff14d50007fe86a8073fe4354001fea1aa01cff10d500dffec4a8
  | 6 => 0x17eb288203ff1944101df8ca20892fe6410401ffaa08211ff95041007faa820847fc5410407ffb188203ff98c41015fcc62080ffd63104017eb188203ff18c4101df8c620803ff5310447ff2988200ff54c4111ff8a620847ff4310401dfa188223ff90c41007fa8620803bd4310423fe2188203ffd884101dfec42080ffe62104037f3108203ff58841115fac42080ffc62104077e3108222ffd4841117fca42088bfd5210445fe2908211ffd0841117fc842088bfd4210423fe2108222ffcc841117fc642088bfd3210445fe1908203bf9844101ffea22080ffe5110407fea888203ff1444101ffe822080fbf4110407ff2088203fd9044101ffa822080fbd4110401faa088203ffcc44101ff8622080fff2110445fb9088203ff8844101ffa422080ffc2110407fa1088203ffd804101ffcc020802fe6010407feb008200bf5804101ff8c02088fff3010447fe1808222ffc8041117fc402088bfd2010445fe1008203ffd963101dfecb1880ffe658c40f7f32c6203df99631004fccb1880ffd658c4017eb2c6203df59631004facb1880ffc658c4077e32c6203ffd923101dfec91880ffe648c4017f3246203ff59231005fac91880ffc648c4077e3246200ffd5231007fca918803fd548c401fe2a46202bf58e31017fea71880bfe538c405fea9c6202ff14e31017fe871880bfe438c405fea1c6202ff10e3101ffec51880eff628c407ff3146201bf98a3101ffac518886fd628c407fe3146203bf18a3110ffea518887fe528c443fea946221ff14a3110ffe8518887fe428c443fea146221ff10a31017fe651880bfe328c405fe9946202ff0ca3101dfcc31880fff518c407ff28c6203ff5463101ff8a31880fff418c407ff20c6203ff5063101ff8831880fff318c407ef98c6202fdcc63101ff8631880ff4318c407ff90c6203ff8863101ffa431880ffc218c407ffb046203ff98231005fcc11880ffd608c4017eb046203ff18231017fe611880bfc308c405ee1846221ffc823110ffc4118887fd208c443fe1046200ffd9531005feca98803fe654c40f7f32a6200ff59531005faca98803fc654c40f7e32a6200ffd9131005fec898803fe644c4017f3226200ff59131005fac898803fc644c4017e3226200ffd5131007fca898803fd544c401fe2a26203bfd8d31017fea69880bfe534c405fea9a6202ff14d31017fe869880bfe434c405fea1a6202ff10d31107fec498882ff624c441ff3126201bf98931107fac498882fd624c441fe3126201bf18931107fea498883fe524c441fea926220ff14931107fe8498883fe424c441fea126220ff10931017fe649880bdf324c405ff1926202ff4c931107ba649880bfc324c4057fb0a6200ffd453101ffca298803fd514c407fe28a6200ffd053101ffc8298803fd414c407fe20a6202ffc
  | 7 => 0xa0847ff63d0453ff31e8202bf98f41007fac7a0802fd63d0423fe31e8202bf18f41007fea7a08a7fe53d0401fea9e8229ff14f4108ffe87a08a7fe43d0401fea1e8211ff10f4108ffec5a0892ff62d0449ff3168201bf98b41127fac5a0892fd62d0423fe3168201bf18b41127fea5a0893fe52d0449fea968224ff14b4108ffe85a0893bf42d0449ff2168224ff50b411277a85a0847fc42d0449ff9968224ff8cb41127fa65a0893fc32d0401ffa8e8203ff94741007faa3a080ffc51d0453ff98e8203ff0c741127fe43a0893f721d0407ff10e8224ff4874101ff843a0893f421d0423ffb068200ff98341005fcc1a0803fd60d04017eb068211ff1834114ffe61a08a7fc30d0449ff9068224ff88341127fa41a0893fc20d0407ffb2c8203bfd964101ffccb2081efe6590407bf32c82009f9964101ffacb20802fd6590407beb2c82009f5964101ff8cb2080efc659044b7eb248200ffd5241007fca920803fd5490401fe2a48203ffd8e4101ffcc72080afe6390407feb1c8200bf58e4101ff8c72080efc6390401ffa9c8228ff94e41007faa7208a3fc5390401ffa1c8200efd0e41147fc8720803fd4390401dea1c8228ff10e4101ffec52080eff6290407ff3148201bf98a4101ffac52089efd6290407fe3148203bf18a4113ffea52089ffe529044ffea948227ff14a4113ffe852089ffe429044ffea148227ff10a4113ffe652089ffe329044ffe9948227ff0ca4101dfcc32080fff5190407ff28c8203ff5464101ff8a32080fff4190407dfa0c8200fdd064101ffe632080ffc3190407ff90c8203ff8864101ffa432080ffc2190407ffb048203ff98241005fcc12080ffd60904017eb048203ff18241147fe61208a3fc309044fff9048227ff8824113ffa412089ffc2090401ffb2a8200bfd9541007fccaa081efe6550401feb2a8200bf59541007f8caa081efc6550401ffaa28200ff95141007faa8a0803fc5450401ffb1a8200bfd8d41137fcc6a080afe6350401feb1a8226ff18d41015f8c6a0803ff535044dff29a8200ff54d41137f8a6a0803ff435044dff21a8200ff50d41137f886a0897ff625044b7fb128225ff9894100dfcc4a0897fd625044b7eb128225ff1894100df8c4a0897ff525044bff2928225ff5494112ff8a4a0897ff425044bdfa128225ff9094112ffa84a0897bd425044bfe2128225ffcc94112ffc64a0897fd325044bfe1928200ffd454101ffca2a0803fd5150407fe28a8200ffd0541007ee82a080ffe4150407df20a8226ffcc54101ff862a0897ff2150407ff10a8225ff4854101ff842a0803ff60504017fb028200ff98141007fac0a0803fc60504017e3028226ffcc141137f860a0897ff205044bff1028225ff4814112ff840a080fff65104077fb288203ff9944103dfcca2080ffd651040
  | 8 => 0xf95251007faa92881ffc5494407ffb1ca203ff98e51015fcc72880ffd63944017eb1ca203ff18e5101df8c72881fff5394401bfa9ca22fff94e51007faa7288037d539440ffe29ca200ffd0e5117ffc8728803fd439445ffe21ca203ffd8a5101dfec52880ffe62944037f314a203ff58a51175fac52880ffc62944077e314a207ffd4a51177fca5288bbfd529440ffe294a22effd0a51177fc85288bbfd429445dfe214a22effcca51177fc65288bbfd329445dfe194a203bf9865101ffea32880f7f519440ffba8ca200ddd465101ffe632880ffc3194407ff90ca203ff8865101ffa432880ffc2194407ffb04a203ff98251005fcc12880ffd60944017eb04a203ff1825117ffe61288bffc309445dff904a22eff88251177fa41288bbfc2094401ffb22a200bfd9151007fcc8a8803fd6454401fe322a200bf1915103ffea8a8803fe5454401bf2a2a200ff5515103ff8a8a88037c5454401ffb1aa200bfd8d5116ffcc6a880afe6354401feb1aa22dff18d51015f8c6a881fff535445bff29aa22ddf94d51007faa6a881ffc535445bbe29aa200ffd0d5116ffc86a8803fd435445bfe21aa22cffd8951165fec4a88b3fe62544037f312a22cff58951165fac4a88b3fc62544037e312a207ffd4951166fea4a88b3fe5254459fea92a22cdf5495103ff8a4a88b3ff4254459ff212a22cff50951167f884a88b3ff3254459ff192a22cff4c951167f864a881fff515440ffba8aa203ff9455101efca2a88b7ff3154407fe18aa22cffc855101ffc42a88b3fd2154407fe10aa200ffd8151005fec0a8803fe6054401feb02a200ff18151005f8c0a88b7ff305445bfe182a22cffc8151167fc40a88b3fd2054459fe102a207bf9945101ffec82880ffe64144017f320a203ff59051005fac82880ffc641440fffaa0a207ff9505103ffaa82881ffc5414407ffb18a203ff98c51015fcc62880ffd63144017eb18a203ff18c5101df8c62881fff531440fbfa98a207ff94c5103ffaa6288037d531440ffe298a200ffd0c5115ffc8628803fd4314457fe218a203ffd885101dfec42880ffe62144037f310a203ff58851155fac42880ffc62144077e310a207ffd485103ffca42881ffd521440ffe290a22affd0851157fc84288abfd4214455fe210a22affcc851157fc64288abfd3214455fe190a203bf9845101ffea22880f7f5114407ff288a203fd9445101ffaa22880f7d511440ffaa88a203ffcc45101ff8622880fff2114407ff108a203ff4845101ff8422880fff6014407ff300a200bf9805101ffac028802fd6014407fe300a22bffcc05115ff860288abff2014455ff100a22aff48051157f84028847ff65d04017fb2e8200ff9974103dfccba0803fd65d04017eb2e8211ff1974103df8cba0803ff54d0423ff2a68200ff5534108ff8a9
  | 9 => 0xc0f7f32e8600ff59743005facba1847fc65d0c0f7e32e8602bf99343007fea9a1803bf54d0c23ff2a68600ff5534308ff8a9a1803bc54d0c057eb1e8602ffd4f43017fca7a180bfd53d0c05fe29e8602ff90f430177c87a180bde43d0c05fe21e8602ef10f4308ffec5a18ceff62d0c67ff3168601bf98b4319ffac5a18cefd62d0c23fe3168601bf18b4319ffea5a18cffe52d0c67fea968633ff14b4308ffe85a18cfbf42d0c67ff2168633ff50b4319f7a85a1847fc42d0c05ff9968602ff8cb43017fa65a180bfc32d0c23ffb0e8600ff9874301dfcc3a1803fd61d0c017eb0e8611ff18743017fe63a180bfc31d0c67ff90e8633ff8874319ffa43a18cffc21d0c23ffb068600ff98343005fcc1a1803fd60d0c017eb068611ff18343017fe61a180bfc30d0c05ee1868633ffc834319ffc41a18cffd20d0c67fe1068600ffd9543005fecaa1803fe6550c0f7f32a8600ff59543005facaa1803fc6550c0f7e32a8602bfd9143007fea8a1803bf5450c01ff2a28600ff55143007f8a8a1803bc5450c057fb1a8602ffd4d43017fca6a180bfd5350c05fe29a8602ffd0d43007be86a180bfe4350c05df21a8602ff10d430177886a180bdc4350c65ffb128632bfd8943197fcc4a1806fe6250c65feb128632bf58943197f8c4a1806fc6250c65ffa928632ff94943197faa4a18cbfc5250c65ffa128632efd0943197fc84a18cbfd4250c65dea128632ff10943017fe64a180bdf3250c05ff1928602ff4c943197ba64a180bfc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8603bf18543017fe62a180bfc3150c65ff90a8632ff88543197fa42a18cbfc2150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028600bf18143017fe60a180bfc3050c65ff9028632ff88143197fa40a18cbfc2050c0fffb26a207ff99351005fcc9a881ffd64d44017eb26a207ff1935103ffea9a881ffe54d4401bf2a6a207ff5535103ff8a9a881f7c54d440fffb1ea207ff98f51015fcc7a881ffd63d44017eb1ea207ff18f51015f8c7a881fff53d440fff29ea231df94f5103ffaa7a881ffc53d440fbe29ea200ffd0f5118ffc87a8803fd43d4463fe21ea207ffd8b5103dfec5a881ffe62d44037f316a207ff58b51185fac5a881ffc62d44037e316a207ffd4b5103efea5a881ffe52d440ffea96a230df54b5103ff8a5a88c3ff42d4461ff216a230ff50b51187f885a88c3ff32d4461ff196a230ff4cb51187f865a88c7ff31d4407fe18ea230ffc875101ffc43a88c3fd21d4407fe10ea207ffd835103ffcc1a8802fe60d440ffeb06a200bf5835103ff8c1a88c7ff30d4463fe186a230ffc8351187fc41a88c3fd20d4461fe106a22cbf5965101ffec92880ffe64944017f324a203ff59251005fac92880ffc649440fffaa4a200f
  | 10 => 0x42aa003ff60550017fb02a800ff98154007fac0aa003fc60550017e302a83affcc1541d7f860aa0e7ff2055073ff102a839ff481541cff840aa01efe65150717f320a807ffd505403efea82a047fe541500fdf2a0a807ff55054006faa82a01fbd5415023ffb18a807ff98c54015fcc62a01ffd63150017eb18a811ff18c54015f8c62a01ffe531500ffe298a837ff90c5408ff8862a047ff621500f7fb10a807ff9885400dfcc42a01ffd621506d7eb10a811ff1885400df8c42a01fff521500fff290a836df9485403ffaa42a01ffc521500fbe290a811ffd08541b7fc842a0dbfd4215023fe210a836ffcc8541b7fc642a0dbfd321506dfe190a811ffd845403ffcc22a00efe611500ffeb08a800bf5845408ff8c22a0dfff311506ffe188a836ffc84541b7fc422a0dbfd211506dfe108a811ffd805403ffcc02a002fe601500ffeb00a800bf5805408ff8c02a0dfff301506ffe180a836ffc80541b7fc402a0dbfd201506dfe100a802bf9975303ffec9a981ffe64d4c017f326a607ff59353005fac9a981ffc64d4c0fffaa6a607ff95353006fca9a981ffd54d4c0ffe2a6a607df15353015fac7a980bfe53d4c05bf29ea602f794f53016bca7a980bfc53d4c05be29ea602ff90f53017f887a981fff62d4c0f7fb16a607ff98b5300dfcc5a981ffd62d4c6b7eb16a607ff18b5300df8c5a981fff52d4c0fbfa96a607ff94b5303ffaa5a98d77d52d4c0ffe296a635ffd0b531affc85a98d7fd42d4c6bfe216a602ffccb53017fc65a980bfd32d4c05fe196a607ffd875303ffcc3a980efe61d4c0ffeb0ea600bf5875303ff8c3a980bff31d4c05fe18ea635ffc87531affc43a98d7fd21d4c6bfe10ea607ffd835303ffcc1a9802fe60d4c0ffeb06a600bf5835303ff8c1a980bff30d4c05fe186a602f70c3531affe41a98d7fe20d4c6bfe906a635ff08353015fecaa9803ff6454c017fb22a600ff99153007fac8a9803fc6454c017e322a607ffd5153007fca8a98037e5454c01feaa2a607ff15153006f8a8a980aff6354c05ffa9aa607f7d4d53017fca6a980b7e5354c05fe29aa602df14d53017b8a6a980bfe4354c05fe21aa634ffd89531a5fec4a98d3fe6254c037f312a634ff589531a5fac4a98d3fc6254c037e312a607ffd49531a6fea4a98d3fe5254c69fea92a634df5495303ff8a4a98d3ff4254c69ff212a634ff509531a7f884a980bff3254c05ef992a602ff8c953017fa64a98d3dd3254c05fe192a600ffd8553005fec2a9803fe6154c01feb0aa600ff1855301df8c2a980bff3154c05fe18aa634ffc85531a7fc42a98d3fd2154c69fe10aa600ffd8153005fec0a9803fe6054c01feb02a600ff18153005f8c0a980bff3054c05fe182a634ffc81531a7fc40a98d3fd2054c69fe102a611ffd9743005fecba1803fe65d0
  | 11 => 0xe000000000000a00000200100000040048014002001002800400000100000040040020000010006001000000c000007000800801000000000080160060018000008000000800000e004003002c0120080000004000000001001c0000010048030002000002000000e003002800000000000080000000000010024004001000000400c00200180080000000028008000009000800c00600000000040000000040000004000002800c0060020000000000003002001800a009000000000a00600000180120010010020000004000000400800000f001c00a000000802400000603ffec7aa01ffe63d50057f31ea807ff58f54005fac7aa01ffc63d50057e31ea807ff94f5403ff8a7aa0f7fe43d507bfe21ea807ffd8b5403dfec5aa01ffe62d50037f316a807ff58b541e5fac5aa01ffc62d50037e316a807ffd4b5403efea5aa01ffe52d500ffea96a83cdf54b5403ff8a5aa0f3ff42d5079ff216a83cff50b541e7f885aa0f3ff32d5079ff196a83cff4cb541e7f865aa01fff61d500fff30ea803bf9875403ffac3aa002fd61d500ffe30ea83dffcc7541eff863aa0f3ff21d5079ff10ea83cff487541e7f843aa01fff60d500fff306a800bf9835403ffac1aa002fd60d500ffe306a83dffcc3541eff861aa0f3ff20d5079ff106a83cff483541e7f841aa0e6fd659500f7f324a807ffd5254006fea92a01fbf54950019faa4a811ffd8e541dffcc72a00afe6395001feb1ca800bf58e5408ff8c72a00afc6395077ff29ca807ff14e541dffc872a047fc4395023ffb14a838bfd8a541c7fcc52a006fe6295071feb14a838bf58a5408ff8c52a006fc629500fffa94a838ff94a541c6fca52a0e3fd529500ffe294a838df14a5408ffe852a0e3bf4295071ff214a838ff50a541c77a852a047fc4295071ff994a838ff8ca541c7fa652a0e3fc3295023ffb0ca800ff9865401dfcc32a003fd61950017eb0ca811ff186541dffe632a0effc3195071ff90ca838ff886541c7fa432a0e3fc2195023ffb04a800ff98254005fcc12a003fd60950017eb04a811ff182541dffe612a0effc3095071ff904a838ff882541c7fa412a0e3fc209500fffaa2a807efd5154007fca8aa0037e5455001ffb1aa800bfd8d541d7fcc6aa00afe6355001feb1aa83aff18d54015f8c6aa0ebfe535500ffe29aa83aff90d541d7f886aa0e7ff62550737fb12a839ff9895400dfcc4aa0e7fd62550737eb12a839ff1895400df8c4aa01fff5255073bfa92a839ff949541cffaa4aa0e77d525500ffe292a839ffd09541cf7e84aa0e7fe4255073fea12a839ef509541cff884aa0e7ff3255073ff192a839ff4c9541cff864aa003ff61550017fb0aa800ff98554007fac2aa003fc61550077e30aa83affcc5541d7f862aa0e7ff2155073ff10aa839ff485541cff8
  | 12 => 0x2001002001c0040060028000000003000000800000a001800400000300080000000000000000004003000000001000300000100040090010000004000000000c004000000800001600d0000004006003000003800000000180000000040060000006000000000800800800000000020000038008004000000800000a00100200000000080000008002001000800c000000002800000800a00180000040000018004006001000000400200200180140000000000008004000000802400a00400000000000010000008002006000800400000000080080040010060008000000000000000200100000000000020008000000001002802c00e0010008000000004002000400c004000800000400600000680080000010000002000000000000c000002800000000d000000000a0040008008004001001000800800100000100000040028000002001000001001e000000800c0000010028008006003001000c0000060000000000006000000400c00a0000008000000000002c0060020000000000001001800000000500080000000000008010004000002002800000100000040180010018000002000001000000e000000800000000700100040000030058000000007000800000000100000000000000010014000000000003000200000500000080000000014006001002000000600100000240000020000000000000000000400400a0048004000000000800000200b001000000000100400000000050000018006001001800800001400000000000020000010004000000000400600200180000000030000004002000000800000400700c000400000c0000004000001000000000000200080040080010010000000000000000800a00500100000080090078008002000000000c00000900180040080020040008000001001000000400000080000020090018030002000000000400a0000010008012001000001400000200080000000000060000004000000800000a000000000000600000180240040000008010008000001000000400100000000000040020000000002001001c00a001000000000e00000000040000010000008000003000000000400200300080040170070008000008000000800600100000040060040048004004000000000000000000380000000060008014006005000000800200100000080080030028028002007001000c0000010010004024009000000800000300000100020040058004008001000800000e0010010000000000002800800400300000300140000000004008002000000c00400c0030018016000001000000402000200000020000010034000001003000800000000180000020000000000000008001001400400300180100040000028024000002000000000400300280100040020040004000000000
  | 13 => 0x15c80006a537a00000000004202014000000316800000009637c08346340001d69ff4c7200021b0b5101000035d80003a03a34c780005d80000000d580007964df8000be884f4ce14f40002400000000000000000226418e60b3e514152306171b5274c0003b748580003b85410001ca901268846b80000000002b200008023814b09cd52f61ae51080006f8571373a4381d20000d480011aa9af16e899480e00000010c8d9e000000000089a000000000000000000000000000000001f98000000042118c9c03fa3d40820000000000000000027600004f000000011f8c6cbac82423ea1707f69b412ba10800077b0cf80004880000000000000000000168000015c3278908a3000000000000003780d200007dc2540002740abe551000000011015f17f00001922f100000013a80000000000b58014000000129e2e001da8bc0007fb4290234b06a1837b21412621e33609adc000000000190c0007e92be91252a400000024940000000001e6cee459b000000000000000012f000079200000000000004d38000caa0003f888f53b04a100000000000004de80000000000000000d200004da99640000b60e59f2d2aa5d72a016cc0008c4193988831000000015d5046000000262c2964d908b1f00736986303897cd888c80b79840e3281e4869580d249c008d159c5cc0553fc1a1898c00024a80010aa00000000000007704918000000000000251c0000004298cac7764b700027e80000000001d0c00000000011d00000001e681780009a30000000b884dc3ac241800000000008046c40000cd00012c4250158a4c87943bc0001ccc00041400000000000004b49cb037c51108a8e4400015e0001cf8e823a43489044f40000020800000000000000000009d2000091c1bc394000000109c0000e08c5800000033003fc7b63c1000254490600046f0a28cf25680db23609a07da0000000000000000000134000000000000004aa000000000000000000000000da46b06641a85b53ab800000005f32f00000007620000000c6448604e000000000023b00010202c10000444e0a00034d010075c00015aa65000020f000231c00000025c000000000021ca4aca369073a29434b1ca2414f002537c63c4428624d563203e284c91d202a29a83f874a928000074421095f23022c8d1467800007300007491298000d045910000000001000000000c0000000004000002001000c00000600000140120030008004000000000800c00a0020000004000009000800001a0000010004000000000000c006000006000c000000000001800200500080200000080008000002000000800800000000080080020050050000002003000800c000000000000401a0040020018000003000000800200100000100060000048000004002000800c004002005801c00
  | 14 => 0x83e07da2a011851c1fa99d47d427100022685760030b922610d826b04c14f003e5040001f58000000231000000000047900003f29e80000000000376000000034443a0000e8040ca1e000000121400000000012ca51a000000000000000026b80002e500000000007f01300000baa3c400017fc9ee9cc00020d1086023067a3c0000000000000000050e4c01520000000000028c00086f133047400000050105c4000000000009800082a00000000006d129d8810000000000000113a00016214e902800046e83102707aa2f495182cc00000026e093615b00000000002513eea26cb94a1700019380006a60002688000909451273c00091439000003ec8a410a927926e183000147885c000000000026c0000002538ecc00000011b4000000000000000074a0000000e260004db00011ea2e13b88e9d0569352d7064114012942f88cca322850001c580000000000000a9230a4ff848000000044b0000fd48db0000000000a281a19000862724399000031c0000dc00002b49761d4a2ac0001d42fe99602c800027984d53dc8c3235000000000000019dc0000004e700000009dc20b12c00000000000000e98000000000000013a0000f5929a59a43481d000095932107f91520001e88ba91e875a0001fd811c4b65070000db446f00000006ae05c165a6e8000000210a2300000001410000be07262a524e44ce817502849ce747e20000ea0aa01d3000079800050600008b4000286291800000035e2e80c7118441d00000007603711c801182028c10ca12740fe88833da47c0a48ce4f90d6cab81bd1e60000a485a4167a22cede16743400000003020000f6800053100000000005293c40dbcd8a0644969d747122d200000003248ad25fa67c00000000000004900001918128bfc79f00000000000001b39c5400000048000000000000000000000000000191c9aa0000000000ccc1ca0c8953022805a114952c8380003600c9853016e3478f1931c9a9000168cd5202c08207a0f2843826c011c37867e1c794213cc79a0e30d80a403995020d600e40000000c000701812b78001414963000063cc76000000173c00058d0a80000a4a69800027d00000000000000dd20003968ee829260823927bc6e60003068660db209a4ba0000c8c00011f07600000002b6a7140000001421c7c0000000000000c0c4e501f82c4c2a89c22788692884f9000043522e000000000000062e0000c8800002f46c95344040004bc9acc28004c0000000986000000000000000000026400f64d40000d8c0004c03c7976028a3ec3099630ac63614321658a428e801d00013145fc36994490746500001c8cd9c1973721cc47de97700011e091c69628a25f4000000000082517000028800000000003d6000015e000000000000000039a000013c00
  | 15 => 0x25a0000b04a00000211c000000000000067c000122903400042630700000000000e7000010c0004100b454220002a784304227561c680000000003fb800000020a000215917c74829f1fbcaa472900002f0acc5f60000db40000002f1a850b0c00000023e0c48542000000000000000008d48be00000025280009200000394bcc15d0e4162400098800000000004b2000243cb022ce10023704947513ee1b5cd6a9d100003f00008fb33b000000022e4ae91e493481c03708154529a135225400000000610cec89062827d0000e7622f0000000f9e00039421210c48600001bb09da0000000cfc000000315800000000023b800000031225700000006f915203c50081de00005c09e07c74ae07cccdc7120000a7000085700000013ce249184000000016000011c4020000000000000060c2fb80000008c600020940a8a2237ba5913aa0273779ac48b6000000000000079d00000011f22e33a3254c0004cc48d800000039f24c8000f1a0002520000fda0a242300013b60000000f20000000000000000000000023000005ad00000012b000015f00000000001a88070ec80000000a6c00000000019054260a538d9c448f600010e000000051546d038ca000002e009600005e53d9998d18a00000000003c000000000005028c90000000000000000000085439216c800037e000000000000000004f800000010937d886c5ac74d00000004ac000000119c00000034180000002220000f2d3e277a00000000000002168000000000000000067a94b0000000376000000000044c000000000000045d000000000082c02e80010ea91c00013bc0000000768038f3c000000000000000000013ec2f495e41a8e9800066a0e900000008280000e545000003af00000000001f18a300008840e1000000000000000001aa98d00002cd26800001a0000000000232800134c0000000f9095e0000000000b1e000000000071c00000000004b4000000101433600000000000004290000000000000000000028610528388dc0004c54f9a72c00067f0001c940006ba4470a58000489235822c000752033a5300307c100025cc39e4841ff11a45a6630000000112e83133880008a60000001ce40001e53c3a14455600000027e0000000000000106c5a24c900007fe00000009c0e0c000000177075e5c2000034800040305d16480000000000c780cc00029115d0aa800004387240002c80000000000000000000078400000000001e82250182624fc26c323f8fac00064522d06092447d93378000000000000123508200025680000000000001d500000000000cbd0e03141e018d04aa0004d4000052e45100000000000ce0000440000000000000000076a26700009be0004cb000000000000000002f66aa07c079c170000000154c0000000fa0ab086a67200100
  | 16 => 0x2e4bf4503452800055e9f950824e90e26d00569ec0bc439d00023f48847f500500000009bb2e183f400086a000000088a930000000033c35915f9bd4f527b2000059400088d000000043a00003b90287105392e427dd03a1b53c88000a1200000000009380004ee9eb80005c12e60d50a8600000000007aa0004eb000081600030da56800000000000000000000000c54a044fd00000000000003710000dfa91000022246741460000000f7e37d03e8000e2860a0d5133c0000004570c4141e7bc00000009d800050d270800030100000000003d94e41c403e25e118997ac4f400000000003084b14a080000000810001f108aa0000000000c804cd3320f791a0769000000093e2ca00000013f6000000000000000000014c00000ae0979e70b1425c0000000c3c5c5000058453200000008f000072705a8000fd887f35e8e300003e148109fc6720004eb80000003c73000d14e2e00000000008c80003cc15e05fe8b54aa1d8c9d62cd1ba06707c411c3160a0c9ea12d14917b4a680002bf800000000000011100000004d60c100b000018b800117800038001f055c537406000136239a00001a0dc600000000000001c72688d3c1f408a11d88e882e4cb2e58dac69a0d705e8000f7c0000a78000ce862327c0000000000000000119482d00002ec0001f743e088457200000016c138e9cd0000d900000003ea261c5340000000de4000000440251944a1dd09420a4b7e329000069800045c02d8a1c0000000328000bea17635e03dc0001f542680000000000a995cc000000000000000000000000000000003cb800000060900000004726ed0ac04d0ecaa0601282b008a0000699b50b2e185000000023e0512b0a048dd69a52d91f20136000403888087c73c45d1d84ba43961a8087cf8c4040e1800097a0000000000c30000031800000022b000000000000000000009fe00000025f10b25690988125208670000a13084a0043340d9424c000000000000002240c0000a260000000000c7474b00015e86541fa3518000c6a6e10ef8c9020e0590002464d02000418000000039e26da678a167bb26b000000041f03b10d00e099700000000006851f000000000000000000000000035043c06e0001f6a0580000000d68000ac43800000000000000000187c000000000000006c1ba00000012b684b43f22fc8fc93b2c9a7f52424590000001306665000153800000018fa1dc0000003a9800000056a1528000000000000000000085817ea0bcaca35c00000c80006f1066242070882e3eba0f107e1b1000000009617735400000000000002414804000436a3e800038700018d80001b40f900000000001f814fc0000c51320000fe8a0b48d020cc3481a23080e446836811b26600000000002430f9c000000103000021e000000018000000000000000
  | 17 => 0x15600001b0000000000006800000000000000000000000000000782000000000000037e12982d4785000107800000000000000000002bf28984d877f19e24f45b000036e800000009330b0074bce00000013b942a0ee24b830cbf06010001430f6c0d93358efc8e60000001c7000000018705492f45450f781100007222408490194000000000000000000024f80000000001a7c4fa440000048800000000013a089491334e800000000000021d85d2000000000000077317109f119e3345008f74000353000000000024e0000000fd60000001c0c0006ca000000087634000010880005010000000c7e000000096d12a0002080000f4a01900300000004f1000000000030c2500000000000000187400015708b863000043c000000009e000000000000012b34992e800028d0b180000000000000000d702f61b3000009a5d11598a2000047500000013b49ab4008000e3000000000000007404478e1945a0531a3a3f13601b3273255ce8ea2a31f00013c80000000b00000000000000000000003c80000000000000000f7a2241b70f7c0000000000000000000134000000000000000002d62fb244218cfb000000000008dc7930210000aee8f700027a800081543d962c0000e73e6038411206b0f6018887a0001630e0c0000000d811513bc8cd3b400000003d2301836c0000003ef80000000000002184e1000000000000000000000000000000000000130448c11c000059246c1448000216000374088c0000000000000000000000089ca704302489620db042b3128000b5e00000008650922f713da16927e00030e1d80000000000000000000035780010046c243d00000002f900618140240000fda2180000000001090e1a00000000000001a53c58e60000470000071506652c0799614c5418d00001cc1040000000c7400000000000000000001e28000000000000219800000000024040000003c0109cb000001378b1533a0002d88d240002b209f9ee80000000000bf00000003ef2240e4200000000002b20000000fdc0006ad18280000000f624b00000000003aa8c0c000000425204cc4c000407000000000044f1bcd3ca76c3a2000024651600014ac00080b13aa0c906e24b1a58000d3c0002fc9de0c2292f432807800000000000000007010a509e0a3e5f100000000003ce000000000000051380000008bb4f588c0b2a9c60f800000000000000000bf600000023d8000627000037c0009454ef800000009d3308bd4a8e00004b80000000000001b9800000000000840000000001ffc000000000000000000000000011223090002458930821000000009c61900012cc0004b931c00000004fc0000fc4000000000227c00000000000006aa0000000000000000149a66c40600029312f8000000000000000049309ea
  | 18 => 0x18480005ce3d08de868c00016e069c69411b2099eac000141177906c27600022b196c0005f23439f9471652e0f113d8b4e7423858ed85be0000ed800088c6b200000000000001dc83a8c4276b3f403040003b424580000001d9000083000078e00024cc000a163bb80006420001e1a44869898500000000009ad000000000000000017a00000f90000370a6400000000009a694900000000000000000000cbe273339800000000000014b400000005395690220563250b54000000000176916280617680013c42310ea800075400000000010f200000025b8af600000024a800000005f000029c0001780d0802a0001058000000000000000000000013b82140003b23fd16ac14200003f2820a3a4f225380009460000fe800112600000000011a25a940000005200002ea17240004c801206e4db869b31000211e672f19b1c311da000000054445800039f83909940002952098f2aa230b484ccf6a0754c21c68c7a65400000010fa2a20bf800000027437707b80002de0002724ca43282ed967434035a2cca6cc77c00003d00000007e73459f24d7e0000000000b4a0000f501804989700000000bbc1fc0000fe0000000466015c9b40002270000f32207000000027250a0000000db6000000000000087800000007f200000000000000000000a551289b90000000ebe12e24826051680000000cb801e00000019209fc57949c000000000000028ad10200000000007d200040d9fcc00033126f00011ca0000000000000000207000000028b00000000000003f916e89c400000008a02581ac000000083037f083000081e2d700015740000002f700000002e700020f400000034000000009e3000000000000041c000000077520ca83115800000000011240000000000fa000049e000000000000000000000000000000000000000000000000000000000003822340f700001af000000000000016101c47ec00000000010440000591b2c00000000000000003b524900003b480d08c08400000000000344d28000048800017200000ba0283d600000009740620002261780000000168000056e74f04a0db00000001a70000abc00007400004fc0003e9272800070f00000007b059f000270490a37222c000000019508f000143e00041c800000046600000000005c7000200c42800000014d80000b00000c4419a7db46900000000000000000000000000085c5286c80779c1c06a66747716100860b73bb000122a13018399b0efa00000003b000000000000000000003d18000d986a200016a80000000000000b7c000000000002600037282001e40c84cd1e9800000005409794245330000f9c8ae000000000000068400000000005e4297931c8f882708c8fd04f24c91a900007d04200002630d2a10e43a00000000000001104ae074e32e994c000
  | 19 => 0x60004f080000000000001f9122203d32d264c0000000000ad800056c2f7993477a000000000115e71e00016d01cc447439216cf122fa1968dc000024d2548984fa24ea0000e140a01930d900000000eb00000000000005049af89ba29d0000f400408ea00d955800000050c8000000000000000000000000016a000000000000000000000000000aec1790000000bd41b716d24980006b6000000114e1621720f4c0008e23f1a1ac0000000001df000000000000013b20003f7000002207800000000004870000be0000000000000081200000000000000004ab00000002ba25100010ce000217800000034400b00000007d50c500012d00000000a8000000029415b80000000000298000000131000000019d2c38a3c9e800010b26f000017400024909141cd00000000009ed443a3fc632028378061cc048824b6207d3d21e134c8e28eb24c200026c93483cf219a32d2ea1420000000f0896615302811a83b82ab800000075c4faa5bc0004372291850c5241500016d8000000000038800000000000011428a3000000000021300000010dc0004bc1048e6e000000000000047a08000000000480000000000000000000000000000019e80001480001a3400000008180000002bc0000000b380003da19f4b308df4e20bb895626e0000000a1e000000149c16892706b00000000003fc9be829812a4a196e000006144182ac72e1c42748cd47f845034b901801a3061b480000000002ada3f8edc0000000ec4dfc00000005d400080f16628b8ab23fd00000000002c73ba09c93e097100000000005df49608a805600000005f00000000001f8000000000022c00000001758aa4be692900000b914c8b7000247431665747592a125c00038e85b0dc01132dc8f94756a070eb07b4d1c0aa000145c0000001e4800057a2ad00000004825d30000a38d121470001d6c7cc06d2aa9ee466434843987a44b260416180006ea9c30d082400000003e68554b284e447603743000002738e88000000470a5091140004a40918e1c000000042800073000005f800000000000000d20000002110000000000000000000000000000003254b90408dbe7c2187a50087e7671bd832c07c67c00006a000000006c00009ae00031b800000000000027f00000003581ee000083b4b6a66400000000000000005a60001b1c0008b60000df811e0000d59718f1800012795600001730000264f445bc4702174b3c00050e0000000000000000000000047382fcd5c91e1ea0eb00000000eb910c0000002f600000000003248a440003f336b2390f142523bc81bc05a6ac4bfa2cc00000000000000000000000000d4231800000000009aa00000142fa000326123ccb800000013482d0a032be0a8cd386c633483403fe41a4fb1e047ae03c2de9294c1e34110c05b414877e369
  | 20 => 0xb6e8f1000098cdaa000397001c4240000001ba885800004900000009e000019580000000700000000337000090c000000000287400062f331120841c00000000009c6000422800028800000000000000000000000e0400000009a93226334818000f20000000000098800000000000001c01c98ac0d6899522f00a4b9a65151600009820003820c340660000fc0000000000000055026e00000002a400035f1790000f5e26d3648000e1200019996852fc85e39c26dc9768bd04aa5a80000000bc1db454e00b0001e9053e4231741a9d26c7360000ecc0000000f21ec40000000000bd0000a0d0630000ffc967000234c0000003c18fc80007ad25600014364b500000011cc0000001e1800056b2ee9910464000000112c5428e300004486587500000ad12d66f236f12502423380cb0c2c00085434600000000000001b340000002c827f80007b70001cad15426900000000008ef0000e7029a12509f1cf53d80000001e9c0000000c31a8000064b17996ec1ea00019810a08106b91551764f8635d37f83c00008193fe0ae09c24800000000cda544000000055000000000012c063116d8e840007d35100ddc0000000001c2834
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe76d5010004fd76d501001cfc76d501003e7e65d50100067d65d501008cff769501001cfe7695010004fd769501001cfc769501003e7e65950100067d65950100073f5495010004ff765501001cfe7655010004fd765501001cfc765501003e7e65550100067d655501008cff761501001cfe7615010004fd761501001cfc761501003e7e65150100067d6515010004ff7558c1003cfc7558c10004ff7458c1008cfc7458c1001edf7358c1002ede4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c1002edf3258c10006dd3258c1001cff7158c1001cfe7158c1001cfd7158c1001cfc7158c1001ede3158c1001edc3158c10014ff7058c10014fd7058c1002cfc7058c1002edc3058c1001ef71058c1003cff76d4c1001cfe76d4c10004fd76d4c1001cfc76d4c1003e7e65d4c100067d65d4c1002f5e53d4c10004ff7654c1001cfe7654c10004fd7654c1001cfc7654c1003e7e6554c100067d6554c1008cff76d0c1001cfe76d0c10004fd76d0c1001cfc76d0c100067e65d0c100067d65d0c1008ebe64d0c10006bd64d0c10004ff7650c1001cfe7650c10004fd7650c1001cfc7650c100067e6550c100067d6550c10006be6450c10006bd6450c10016de6350c10006dd6350c10004fd76d401003e7e65d40100067d65d4010004ff769401003cfd769401003e7e65940100067d659401001df67194010005f57194010004ff765401003e7e65540100067d6554010005bf7454010005bc7454010005df735401002ddc735401003cff761401001cfe7614010004fd761401001cfc761401003e7e65140100067d651401001df67114010005f57114010004fd76d00100067e65d00100067d65d0010004ff7690010004fd76900100067e65900100067d6590010006be6490010006bd649001001df67190010005f57190010004ff76500100057f75500100057c75500100067e65500100067d6550010005df735001002ddc735001008cff761001001cfe7610010004fd761001001cfc76100100067e65100100067d651001008ebe6410010006bd641001001df67110010005f57110010054ff768c01001cfe768c010014fd768c01001cfc768c0100067e658c0100067d658c010016de638c010006dd638c01001df6718c010005f5718c010054ff764c0100057f754c0100057c754c0100067e654c0100067d654c010005bf744c010005bc744c01001df77644010006f77644010004f7764401000777754401000774754401001ef7654401001f766544010006f5654401001f756544010006756544010007b77444010007b47444010007d77344010007d4734401001ef76344010006f56344010007e772440101ffe4724401001df7704401001ff370440101f6f6604401001ff26044010007f25044010007f15044010
  | 1 => 0x4110007e76284110207e4628411001df6708411001ef7608411001ff36084110207f22084110207f1208411003e7f749941003e7e749941003e7d749941003e7c749941003e7f739941003e7e739941003e7d739941003e7c73994100067e43994100067c439941003e7f729941003e7e729941003e7d729941003e7c72994100067f42994100067e42994100067d42994100067c42994100067f32994100067e32994100067d32994100067c329941001e7f719941001e7e719941001e7d719941001e7c719941001e7f419941001e7e419941001e7d419941001e7c419941001e7f319941001e7e319941001e7d319941001e7c319941001e7f219941001e7e219941001e7d219941001e7c219941003e7e709941003e7c70994100067f30994100067c30994100067f20994100067e20994100067d20994100067c209941001e7f109941001e7e109941001e7d109941001e7c109941001e7f7559410004ff745941008cfc7459410004ff7359410014fe7359410014fc73594100067e53594100067c5359410004ff725941000cfe7259410004fd725941000cfc72594100067f52594100067e52594100067d52594100067c525941001cff715941001cfe715941001cfd715941001cfc715941001e7e515941001e7c515941003cff705941003cfd705941001ef710594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067e43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067e32594100067d32594100067c325941001e7f715941001e7e715941001e7d715941001e7c715941001e7f415941001e7e415941001e7d415941001e7c415941001e7f315941001e7e315941001e7d315941001e7c315941001e7f215941001e7e215941001e7d215941001e7c21594100067e70594100067c70594100067f30594100067c30594100067f20594100067e20594100067d20594100067c205941001e7f105941001e77105941001e7e105941001e7d105941001e7c105941003cfe7599010004fd759901001ebe7499010014fe7399010004fd7399010014fc739901008cff729901000cfe7299010004fd729901000cfc729901008ebf4299010006bd429901001cfe719901001cfc719901001ebe419901001ebc4199010004ff755901003cfc755901001ebf7459010004ff7359010014fe7359010014fc7359010004ff725901000cfe7259010004fd725901000cfc7259010006bf4259010006bd425901001cff715901001cfe715901001cfd715901001cfc715901001ebe415901001ebc415901008cff70590100a4fd705901003cff76d501001cf
  | 2 => 0x777654c51000774654c510007b7644c510007b4644c51001df7734c51001fd7734c510007d7634c510016f6634c510016f4634c51004fd4634c510007e7624c51020fe4624c51004fd7324c51020fd5324c510007f3704c510005f4704c510007f0704c51001ef7604c51001ff3604c51020ff2204c51020ff1204c51001cfe76d411001cfc76d41100067f65d411003e7c65d4110006bf64d4110006bc64d4110006df63d41100fedc63d4110006ef62d41100f6ec62d411001df671d4110005f571d41100077551d4110004fe76941100067f659411003e7c6594110006bf6494110006bc6494110006df63941100eedc6394110006ef62941100d6ec62941100077651941100077b509411003cff7654110004fd765411001cfc76541100067f655411003e7c6554110005bf7454110005bc7454110006bf6454110006bc6454110005df735411004ddc7354110006df63541100e6dc6354110006ef62541100deec6254110005f7715411001df47154110007755154110004fe76141100067f651411003e7c6514110006bf6414110006bc6414110006df63141100cedc6314110006ef62141100c6ec621411001df67114110005f5711411000776511411001cfe76d01100067f65d01100067c65d0110006bf64d011008ebc64d0110006df63d01100bedc63d0110006ef62d011009eec62d011001df671d0110005f571d0110004fe76901100067f65901100067c6590110006bf6490110006bc6490110006df63901100b6dc6390110006ef6290110096ec629011008cff7650110004fd765011001cfc76501100057f75501100057c75501100067f65501100067c6550110006bf6450110006bc6450110005df735011004ddc7350110006df63501100aedc6350110006ef62501100a6ec6250110005f7715011001df47150110004fe76101100067f65101100067c6510110006bf641011008ebc6410110006df6310110086dc6310110006ef621011007eec6210110064fe768c1100067f658c1100067c658c110006bf648c110006bc648c110006df638c110016dc638c110006ef628c110076ec628c110007d6318c110014ff764c11004cfd764c11001cfc764c1100057f754c1100057c754c1100067f654c1100067c654c110005bf744c110005bc744c110006bf644c110006bc644c110006df634c110016dc634c110006ef624c11006eec624c110005f7714c11001df4714c1100067f65841100067c6584110006bf6484110006bc6484110006df6384110056dc6384110006ef6284110036ec628411001dfa708411001efb608411001df6768411001ef6768411001cf67684110005f77584110005f57584110007776584110007746584110007b76484110007b46484110005f77384110005f57384110007d76384110007d4638
  | 3 => 0xf73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d891023eee71d8910046ed71d891023eec71d891023eee51d891023eec51d891023eee41d891023eec41d8910006ef31d891023eee31d891023eec31d891023eef70d8910046ee70d8910046ed70d8910046ec70d8910006ef30d8910006ec30d891023eef10d8910046ed10d891023eec10d8910004fe76d45100067f65d451003e7c65d4510006bf64d4510006bc64d4510006df63d451018edc63d4510006ef62d4510186ec62d451001f7651d4510005fa70d4510005f970d4510005f6769451001ef67694510235f5759451000777659451003ef6659451003ef4659451000774659451003e746594510007b76494510007b46494510005f57394510007d76394510007d46394510007775394510007755394510007e7629451022fe46294510005f6709451001ef7609451001ff3609451022ff2209451022ff1209451003cfc76545100067f655451003e7c6554510006bf6454510006bc6454510006df635451016edc6354510006ef6254510166ec625451001f745154510005fb7054510005f8705451001ff0105451003ef4765451003cf4765451001df7755451001f77755451000777655451003ef6655451003ef46554510007746554510007b76454510007b46454510007765454510007745454510005f77354510007d76354510007d46354510227765354510227745354510007e7625451021fe4625451021f77525451021f755254510007f37054510005f47054510007f0705451001ef7605451001ff3605451021ff2205451021ff12054510004fe76d05100067f65d05100067c65d0510006bf64d051008ebc64d0510006df63d051014edc63d0510006ef62d0510126ec62d0510005fa70d0510005f970d0510004fc76505100067f65505100067c6550510006bf6450510006bc6450510006df6350510136dc6350510006ef625051012eec625051001fb44150510005fb7050510005f87050510005f6768c51001ef6768c51001df7758c51001f76758c510005f5758c51001f75758c51000575758c51000777658c51000774658c510007b7648c510007b4648c51004df5738c510007d7638c510016f6638c510016f4638c51004fd4638c510016d4638c510007e7628c510217e4628c510005f6708c51001ef7608c51001ff3608c51004fd4308c510217f2208c510217f1208c510014fc764c5100067f654c5100067c654c510006bf644c510006bc644c510006df634c510016dc634c510006ef624c510106ec624c510005fb704c510005f8704c51004df4764c510016f4764c510014f4764c510005f7754c510005f5754c510
  | 4 => 0x8d1024edf70d8d1004ede70d8d10006dd70d8d10006df20d8d10006de20d8d10006dd20d8d10006dc20d8d1024edf10d8d1024edc10d8d100057f7558d100057c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10006bf6458d10006bc6458d1004edc6358d10005ef7258d10045ec7258d10006ec6258d10004ff7558d100067f7558d100047f7558d1003cfc7558d100067c7558d1003c7c7558d10004ff7458d10006bf7458d10004bf7458d1008cfc7458d10006bc7458d10004bc7458d1004cff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d10054ff7158d10006f77158d10064ff7058d10006fb7058d10005de7618d1004ede7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006df6218d10006de6218d10006dd6218d10006dc6218d10007cc6218d10006cc6218d1004fd57118d10246df6018d10007da2018d10007d92018d10247db1018d10247d81018d1003cff76d4d10004fe76d4d10004fd76d4d1003cfc76d4d100067f65d4d1003e7c65d4d10006bf64d4d10006bc64d4d10006df63d4d10016dc63d4d1004f5e53d4d101aeec62d4d1001df671d4d10005f571d4d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1003e7c6554d10006bf6454d10006bc6454d10006df6354d10016dc6354d101a6ec6254d1008cff76d0d10004fe76d0d10004fd76d0d1008cfc76d0d100067f65d0d100067c65d0d10006bf64d0d1008ebc64d0d10006df63d0d10016dc63d0d1019eec62d0d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d100067c6550d10006bf6450d10006bc6450d10006df6350d10016dc6350d10196ec6250d10005fb7050d10005f87050d10045ee76d8910046ee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d891023feb70d8910047e870d891023feb10d891023fe810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006e
  | 5 => 0x6bd5219110006bc5219110006bf3219110006be3219110006bd3219110006bc321911008ebf7119110256be7119110006bd711911008ebc7119110256be5119110256bc5119110006bf3119110256be3119110256bc3119110006bf2119110256be2119110006bd2119110256bc211911008ebf7019110006bd7019110006bf3019110006bc3019110006bf2019110006be2019110006bd2019110006bc2019110256bf1019110006bd1019110256bc101911003cff76d5110004fe76d5110004fd76d511003cfc76d51100067f65d511003e7c65d5110006bf64d5110006bc64d51101eedc63d51101e6ec62d511001df671d5110005f571d511008cff7695110004fe7695110004fd769511008cfc76951100067f659511003e7c6595110006bf649511008ebc64951100073f54951101dedc63951101c6ec6295110004ff7655110004fe7655110004fd7655110004fc76551100067f655511003e7c6555110006bf6455110006bc64551101d6dc63551101ceec625511008cff7615110004fe7615110004fd761511008cfc76151100067f651511003e7c6515110006bf641511008ebc64151101bedc63151101b6ec621511001df67115110005f57115110014fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d1004ede63d8d10006ec62d8d1003cfe75d8d10004fd75d8d1008cfe74d8d10004fd74d8d1004ede53d8d1004edc53d8d1004ede43d8d1004edc43d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d1004edf32d8d10006de32d8d10006dd32d8d1004edc32d8d1001cfe71d8d1004cfd71d8d1001cfc71d8d1004edf31d8d10014fe70d8d1001cfd70d8d10014fc70d8d1004edf30d8d1004dde76d8d10014de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d10007d771d8d10007da20d8d10007d920d8d1024fdb10d8d1024fd810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d1024ede71d8d10006dd71d8d1024edc71d8d1024ede51d8d1024edc51d8d1024ede41d8d1024edc41d8d10006df21d8d1024ede21d8d10006dd21d8d1024edc21d
  | 6 => 0xf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d911025ebe71d9110006bd71d911025ebc71d911025ebe51d911025ebc51d9110006bf31d911025ebe31d911025ebc31d9110006bf21d911025ebe21d9110006bd21d911025ebc21d911025ebf70d9110006bd70d9110006bf30d9110006bc30d9110006bf20d9110006be20d9110006bd20d9110006bc20d911025ebf10d911025ebc10d91100057e75991100057d75991100067f65991100067c6599110006bf649911004dde7399110005dd7399110045ee7299110005ed7299110006ec629911003cfe759911008e7e759911003c7e7599110004fd759911008e7d75991100047d759911008cfe7499110004be7499110014fe739911008ede7399110014de7399110004fd739911008edd7399110004dd7399110014fc739911008cff729911000cfe729911008eee729911000cee7299110004fd729911008eed7299110004ed729911000cfc7299110004fd719911008ef57199110004fd709911008ef970991100057f75591100057c75591100067f65591100067c6559110005df735911004ddc7359110005ef7259110045ec7259110006ec6259110004ff75591100067f75591100047f755911003cfc75591100067c755911003c7c7559110006bf7459110004ff7359110006df7359110004df7359110014fe7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef725911000cfe7259110004fd725911000cfc7259110006ec725911000cec7259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c6519110006bd6419110006ec621911003cfe7519110004fd751911008ebe7419110014fe7319110004fd7319110014fc7319110006be431911008ebc431911008cff721911000cfe7219110004fd721911000cfc721911008ebf4219110006be4219110006bd421911008ebc421911001cfe711911001cfc7119110094fe701911008cfc7019110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6319110006bc6319110006bf6219110006be6219110006bd6219110006bc6219110007ac6219110006ac6219110007ba2019110007b92019110257bb1019110257b8101911008ebf7519110006be7519110006bd751911008ebc751911008ebf7319110006be7319110006bd731911008ebc7319110006be5319110006bc531911008ebf7219110006be7219110006bd721911008ebc7219110006bf5219110006be5219110
  | 7 => 0x95100067f21d951026e7e21d95100067d21d951026e7c21d951026e7f70d95100067d70d95100067f30d95100067c30d95100067f20d95100067e20d95100067d20d95100067c20d951026e7f10d951026e7c10d95100067f6599510005be7499510005bd749951004dde7399510005dd7399510045ee7299510005ed7299510006ec6299510005bf7459510005bc7459510005df735951004ddc7359510005ef7259510045ec7259510006ec62595100067f7559510004ff7459510006bf7459510004bf745951008cfc7459510006bc7459510004bc7459510004ff7359510006df7359510004df7359510014fe7359510014fc7359510006dc7359510014dc7359510004ff7259510006ef7259510004ef725951000cfe7259510004fd725951000cfc7259510006ec725951000cec7259510004ff7159510006f77159510004ff7059510006fb7059510004fe761951003e7e65195100067d6519510006ec62195100057e76195100067e76195100047e76195100067e63195100067c63195100067f62195100067e62195100067d62195100067c62195100076c62195100066c62195100077571195100077a20195100077920195102677b101951026778101951003e7f741951003e7e741951003e7d741951003e7c741951003e7f731951003e7e731951003e7d731951003e7c73195100067e43195100067c431951003e7f721951003e7e721951003e7d721951003e7c72195100067f42195100067e42195100067d42195100067c42195100067f32195100067e32195100067d32195100067c321951003e7f711951003e7e711951003e7d711951003e75711951003e7c71195102667e41195102667c41195100067f31195102667e31195102667c31195100067f21195102667e21195100067d21195102667c211951003e7f701951003e7d70195100067f30195100067c30195100067f20195100067e20195100067d20195100067c20195102667f10195100067d10195102667c10195100067f65d91100067c65d9110006ec62d911003cfe75d9110004fd75d9110014fe73d9110004fd73d9110014fc73d9110006be43d9110006bc43d9110004ff72d911000cfe72d9110004fd72d911000cfc72d9110006bf42d9110006be42d9110006bd42d9110006bc42d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ac62d9110006ac62d9110007ba20d9110007b920d911025fbb10d911025fb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006be53d9110006bc53d9110006b
  | 8 => 0x56dc3058e1003cff76d4e10004fe76d4e10004fd76d4e1003cfc76d4e1003e7e65d4e100067d65d4e100575e53d4e10004ff7654e10004fe7654e10004fd7654e10004fc7654e1003e7e6554e100067d6554e1008cff76d0e10004fe76d0e10004fd76d0e1008cfc76d0e1008ebe64d0e10006bd64d0e10004ff7650e10004fe7650e10004fd7650e10004fc7650e10006be6450e10006bd6450e10005fb7050e10005f87050e1003e7e65d46100067d65d461001f7651d4610005fa70d4610005f970d461003cff765461003e7e65546100067d6554610005fb7054610005f8705461001ff3105461008ebe64d0610006bd64d0610005fa70d0610005f970d0610006be6450610006bd6450610005fb7050610005f87050610014ff764c610016de634c610006dd634c610005fb704c610005f8704c6100067f65d421003e7c65d421001cfd769421003e7e65942100067d659421001df67194210005f571942100077b50942100067f655421003e7c6554210005bf7454210005bc7454210005df7354210055dc735421001cfd761421003e7e65142100067d651421001df67114210005f5711421001cfd7690210006be6490210006bd649021001df67190210005f571902100057f75502100057c7550210005df7350210055dc735021001cfd761021008ebe6410210006bd641021001df67110210005f57110210014fe768c21001cfd768c210016de638c210006dd638c21001df6718c210005f5718c21002cff764c2100057f754c2100057c754c210005bf744c210005bc744c210005f576c421001ef576c4210006f765c4210006f565c4210006f763c4210006f563c421001ff260c4210007f250c4210007f150c421003cfe76d9510006ec62d951008cfe74d9510004fd74d9510014fe73d9510004fd73d9510014fc73d95100067e53d95100067c53d9510004ff72d951000cfe72d9510004fd72d951000cfc72d95100067f52d95100067e52d95100067d52d95100067c52d951001cfe71d951001cfc71d951003cfe70d951003cfc70d951003c7e76d95100067e63d95100067c63d95100067f62d95100067e62d95100067d62d95100067c62d95100076c62d95100066c62d95100077771d95100077a20d95100077920d951026f7b10d951026f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d951026e7e71d95100067d71d951026e7c71d951026e7e41d951026e7c41d95100067f31d951026e7e31d951026e7c31d
  | 9 => 0xe6450310006bd6450310005df7350310065dc7350310005f7715031001df47150310256bf641031008ebc641031004cfd768c31024edf638c310016dc638c31001df4718c31024fd6318c310014ff764c31001cfc764c3100057f754c3100057c754c310005bf744c310005bc744c310016de634c310006dd634c310005f7714c31001df4714c31008cfe74d9610004fd74d9610014fe73d9610004fd73d9610014fc73d96100067e53d96100067c53d9610004ff72d961000cfe72d9610004fd72d961000cfc72d96100067f52d96100067d52d9610006f571d961026e7e51d961026e7c51d9610006fa70d9610004fd76996100067f659961003cff76596100067f7559610004ff745961008cfc7459610004ff7359610014fe7359610014fc7359610004ff725961000cfe7259610004fd725961000cfc725961003e7e65196100067d651961003cfe75d9210004fd75d9210014fe73d9210004fd73d9210014fc73d9210004ff72d921000cfe72d9210004fd72d921000cfc72d9210006bf42d9210006bd42d9210006f571d921025ebe41d921025ebc41d9210006fa70d9210004fd7699210006bf649921003cfe7599210004fd7599210014fe7399210004fd7399210014fc739921008cff729921000cfe7299210004fd729921000cfc72992100057f75592100057c7559210004ff75592100067f75592100047f755921003cfc75592100067c755921003c7c7559210006bf7459210004ff7359210014fe7359210014fc7359210004ff725921000cfe7259210004fd725921000cfc7259210006bd641921003cfe7519210004fd751921008cfe741921008ebe7419210014fe7319210004fd7319210014fc731921008cff721921000cfe7219210004fd721921000cfc721921008ebf4219210006bd421921008ef57119210256be411921008ebc411921008efa701921003cff76d5210004fe76d5210004fd76d521003cfc76d521008cff7695210004fe7695210004fd769521008cfc76952100067f659521003e7c65952100073f5495210004ff7655210004fe7655210004fd7655210004fc765521008cff7615210004fe7615210004fd761521008cfc76152100067f651521003e7c6515210056de63d8e1003cfe75d8e10004fd75d8e1008cfe74d8e10004fd74d8e10054fd73d8e10004ff72d8e1000cfe72d8e10004fd72d8e1000cfc72d8e10056df32d8e10006dd32d8e10006f571d8e1024ede31d8e1024edc31d8e10006fa70d8e10014ff7658e100057f7558e100057c7558e10056dc6358e10004ff7558e100067f7558e100047f7558e1003cfc7558e100067c7558e1003c7c7558e10004ff7458e1008cfc7458e10006df7358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e10056df3158e1001cfc7058e10
  | 10 => 0x9310004fd759931001ebe7499310014fe7399310004fd7399310014fc7399310006be439931008ebc439931008cff729931000cfe7299310004fd729931000cfc729931008ebf4299310006bd429931001cfe719931001ebe419931001ebc4199310004ff755931003cfc755931001ebf7459310004ff7359310014fe7359310014fc7359310006be4359310006bc4359310004ff725931000cfe7259310004fd725931000cfc7259310006bf4259310006bd425931001cfc715931001ebe415931001ebc415931003cff76d531001cfe76d5310004fd76d531001cfc76d5310006be64d5310006bd64d531001df671d5310005f571d531008cff769531001cfe7695310004fd769531001cfc769531003e7e65953100067d65953100073f5495310004ff765531001cfe7655310004fd765531001cfc765531008cff761531001cfe7615310004fd761531001cfc761531003e7e65153100067d651531008ebe6415310006bd641531001df67115310005f57115310004ff7558f1003cfc7558f10004ff7458f1008cfc7458f1001edf7358f10066dc5358f10066dc4358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f10066df3258f10006dd3258f1001cfc7158f1001ede3158f1001edc3158f10066df3058f1003cff76d4f1001cfe76d4f10004fd76d4f1001cfc76d4f102a67f65d4f1003e7c65d4f10016de63d4f10006dd63d4f100675e53d4f1001df671d4f10005f571d4f102a77651d4f10004ff7654f1001cfe7654f10004fd7654f1001cfc7654f1029e7f6554f1003e7c6554f1001df67154f1029f765154f1008cff76d0f1001cfe76d0f10004fd76d0f1001cfc76d0f10296bf64d0f1008ebc64d0f10016de63d0f10006dd63d0f10004ff7650f1001cfe7650f10004fd7650f1001cfc7650f1028ebf6450f1028ebc6450f1001df77654710006f7765471001f77755471001f77655471003ef6655471001ef4655471001f746554710007765454710007745454710005f7735471028776535471028774535471027f77525471027f755254710005f4705471001df7764c71002ef7764c710005f7754c710005f5754c71001fd7734c710016f6634c71001ef4634c710067d7324c710277d5324c710005f4704c71003e7e65d43100067d65d431001df671d4310005f571d43100077551d431026e7f659431003e7c659431001df4719431026f76519431003cff765431003e7e65543100067d6554310005bf7454310005bc7454310005df7354310065dc7354310005f7715431001df471543100077551543102667f651431003e7c651431001df67114310005f5711431026776511431008ebe64d0310006bd64d031001df671d0310005f571d031025ebf649031025ebc64903100057f75503100057c7550310006b
  | 11 => 0x5bc7458530006bf6458530006bc6458530005ef725853006dec7258530065fb70585300067f65185300067c6518530006bf6418530006bc641853001ef66118530006f56118530004fe76d4530004fd76d453003cfc76d45300067f65d453003e7c65d4530006bf64d4530006bc64d4530004fe7694530004fd769453001cfc76945300067f659453003e7c6594530006bf6494530006bc6494530007775194530004ff7654530004fe7654530004fc76545300067f655453003e7c6554530006bf6454530006bc6454530004fe7614530004fd761453001cfc76145300067f651453003e7c6514530006bf6414530006bc6414530004fe76d0530004fd76d053008cfc76d05300067f65d05300067c65d0530006bf64d053008ebc64d0530004fe7690530004fd769053001cfc76905300057e75905300057d75905300067f65905300067c6590530006bf6490530006bc6490530004ff7650530004fe7650530004fc76505300067f65505300067c6550530006bf6450530006bc6450530004fe7610530004fd761053001cfc76105300067f65105300067c6510530006bf641053008ebc6410530015de7310530005dd7310530014fe76d4130014fc76d41300067f65d413003e7c65d4130006bf64d4130006bc64d4130015de73d4130005dd73d41300ccfe76941300ee7f659413003e7c6594130006bf6494130006bc64941300077b509413003cff7654130014fe76541300e4fd7654130014fc76541300067f655413003e7c6554130005bf7454130005bc7454130006bf6454130006bc6454130005df7354130015dc73541300ecfe76141300067f651413003e7c6514130006bf6414130006bc6414130005f67114130005f57114130014fe76d0130014fc76d01300067f65d01300067c65d0130006bf64d013008ebc64d0130015de73d0130005dd73d0130084fe76901300067f65901300067c65901300b6bf6490130006bc649013008cff7650130014fe76501300acfd7650130014fc76501300057f75501300057c75501300067f65501300067c6550130006bf6450130006bc6450130005df7350130015dc73501300b4fe76101300067f65101300067c6510130006bf641013008ebc64101300075f658c1302b6de658c1302b6dc658c1300075c658c1300065c658c1300079f648c130006de648c130006dc648c1300079c648c1300069c648c1302aedf628c1302aedd628c13024edc618c130015de708c130017da708c130016df608c130017db608c13001e7f7559710004ff745971008cfc7459710004ff7359710014fe7359710014fc73597100067e53597100067c5359710004ff725971000cfe7259710004fd725971000cfc72597100067f52597100067d525971001cfc715971001e7e515971001e7c515971003cfe759
  | 12 => 0xc75591300067c755913003c7c7559130006bf74591300acff7359130006df7359130004df7359130004ff725913000cfe7259130004fd725913000cfc7259130004ff715913001cfc71591300bcff7059130006fb70591300b4fe76191300067f65191300067c6519130006bd641913003cfe7519130004fd751913008ebe741913008cff7319130014fe7319130084fd7319130014fc731913008ebf4319130086bd431913008cff721913000cfe7219130004fd721913000cfc721913008ebf4219130006be4219130006bd421913008ebc421913001cfe7119130004fd7119130086dc30191300b5be7619130006be76191300b4be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c6519130006bf6219130006be6219130006bd6219130006bc6219130087bb30191300879c3019130087b8301913008ebf7519130006be7519130006bd751913008ebc751913008ebf7319130086be7319130086bd731913008ebc7319130086bf5319130086be5319130086bd5319130086bc531913008ebf7219130006be7219130006bd721913008ebc7219130006bf5219130006be5219130006bd5219130006bc5219130086bf3219130086be3219130086bd3219130086bc321913008ebf7119130006be7119130006bd711913008ebc7119130086bf3119130086be3119130086bd3119130086bc3119130006bf2119130006be2119130006bd2119130006bc211913008ebf7019130086bd7019130086bf3019130086be3019130086bd3019130086bc30191300869c3019130006bf2019130006be2019130006bd2019130006bc201913003cff76d5130004fe76d5130004fd76d513003cfc76d51300067f65d513003e7c65d5130006bf64d5130006bc64d513008cff7695130004fe7695130004fd769513008cfc76951300067f659513003e7c6595130006bf649513008ebc64951300073f5495130004ff7655130004fe7655130004fd7655130004fc76551300067f655513003e7c6555130006bf6455130006bc645513008cff7615130004fe7615130004fd761513008cfc76151300067f651513003e7c6515130006bf641513008ebc6415130015de7315130005dd73151300067f65d85300067c65d8530006bf64d8530006bc64d853003cfe75d8530004fd75d853008cfe74d8530004fd74d8530004ff72d853000cfe72d8530004fd72d853000cfc72d8530056f631d8530056f531d8530006f721d8530006f421d853001cfe70d85300057e75985300057d75985300067f65985300067c6598530005be7498530005bd7498530006bf6498530006bc6498530006f7619853004df970985300057f75585300057c75585300067f65585300067c6558530005bf7458530
  | 13 => 0x953003e7e65195300067d65195300ed7e76195300067e76195300ec7e76195300067f62195300067e62195300067d62195300067c62195300cf7b30195300cf5c30195300cf78301953003e7f741953003e7e741953003e7d741953003e7c741953003e7f731953003e7e731953003e7d731953003e7c73195300ce7f43195300ce7e43195300ce7d43195300ce7c431953003e7f721953003e7e721953003e7d721953003e7c72195300067f42195300067e42195300067d42195300067c42195300ce7f32195300ce7e32195300ce7d32195300ce7c321953003e7f711953003e7e711953003e7d711953003e7c71195300ce7f31195300ce7e31195300ce7d31195300ce7c31195300067f21195300067e21195300067d21195300067c211953003e7f701953003e7d70195300ce7f30195300ce7e30195300ce7d30195300ce7c30195300ce5c30195300067f20195300067e20195300067d20195300067c20195300067f65d91300067c65d913003cfe75d9130004fd75d91300b4ff73d91300b4fd73d91300b6bf43d91300b6bd43d9130004ff72d913000cfe72d9130004fd72d913000cfc72d9130006bf42d9130006be42d9130006bd42d9130006bc42d913001cfe71d9130004fd71d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130006bf62d9130006be62d9130006bd62d9130006bc62d91300b7bb30d91300b79c30d91300b7b830d9130006bf75d9130006be75d9130006bd75d9130006bc75d91300b6bf73d91300b6be73d91300b6bd73d91300b6bc73d91300b6bf53d91300b6be53d91300b6bd53d91300b6bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d91300b6bf32d91300b6be32d91300b6bd32d91300b6bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d91300b6bf31d91300b6be31d91300b6bd31d91300b6bc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d91300b6bf70d91300b6bd70d91300b6bf30d91300b6be30d91300b6bc30d9130006bf20d9130006be20d9130006bd20d9130006bc20d91300057e75991300057d75991300067f65991300067c6599130006bf64991300adf9709913003cfe759913008e7e759913003c7e7599130004fd759913008e7d75991300047d759913008cfe7499130084be74991300bcfd739913008edd739913008cff729913000cfe7299130004fd729913000cfc729913001cfe7199130004fd71991300acfd709913008ef970991300bedc30991300057f75591300057c75591300067f65591300067c65591300bdfb7059130004ff75591300067f75591300047f755913003cf
  | 14 => 0x24ddc748c63024ddf728c6302bddd728c630015de718c630017d6718c63024fd6618c63024edd618c630007d5618c63024fda708c630005dd708c63024fd9708c630016de608c630017da608c6300e4fd76d42300067f65d423003e7c65d4230015dc73d42302b75f53d4230014ff7694230014fd769423003e7e65942300067d6594230015de7394230005dd73942300ef5c53942300077b50942300efdb30942300fcff76542300067f655423003e7c6554230005bf7454230005bc7454230005df7354230015dc73542300075f53542300e7db3054230014ff7614230014fd761423003cfc761423003e7e65142300067d6514230015de7314230005dd73142300cf5c5314230005f67114230005f571142300acfd76d0230006bf64d023008ebc64d0230015dc73d02300079f43d0230014ff7690230014fd7690230006be6490230006bd6490230015de7390230005dd73902300b79c43902300bcff76502300057f75502300057c7550230006bf6450230006bc6450230005df7350230015dc73502300079f4350230014ff7610230014fd761023008ebe6410230006bd6410230015de7310230005dd73102300879c431023003cfe76d953008cfe74d9530004fd74d95300ecff73d9530014fe73d95300ecfd73d9530014fc73d95300ee7f53d95300ee7d53d9530004ff72d953000cfe72d9530004fd72d953000cfc72d95300067f52d95300067e52d95300067d52d95300067c52d953001cfe71d9530004fd71d953003c7e76d95300067f62d95300067e62d95300067d62d95300067c62d95300ef7b30d95300ef5c30d95300ef7830d95300067f74d95300067e74d95300067d74d95300067c74d95300ee7f73d95300ee7e73d95300ee7d73d95300ee7c73d95300ee7f43d95300ee7e43d95300ee7d43d95300ee7c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300ee7f32d95300ee7e32d95300ee7d32d95300ee7c32d95300067f71d95300067e71d95300067d71d95300067c71d95300ee7f31d95300ee7e31d95300ee7d31d95300ee7c31d95300067f21d95300067e21d95300067d21d95300067c21d95300ee7f70d95300ee7d70d95300ee7f30d95300ee7e30d95300ee7c30d95300067f20d95300067e20d95300067d20d95300067c20d95300067f6599530005be7499530005bd74995300e5f97099530005bf7459530005bc74595300fdfb70595300067f7559530004ff7459530006bf7459530004bf745953008cfc7459530006bc7459530004bc74595300e4ff7359530006df7359530004df7359530004ff725953000cfe7259530004fd725953000cfc7259530004ff715953001cfc71595300fcff7059530006fb70595300ecfe761
  | 15 => 0xf659523003e7c65952300073f5495230015de7395230005dd7395230004ff7655230004fe7655230004fd7655230004fc7655230005df7355230015dc735523008cff7615230004fe7615230004fd761523008cfc76152300067f651523003e7c6515230006bf641523008ebc6415230015dc73152302b6dd76d4e30015de75d4e300175e75d4e302b6df65d4e302b75e65d4e302b6dd65d4e300075d65d4e300065d65d4e30005de74d4e300075e54d4e302b75c54d4e302b5df72d4e302dddd72d4e302b75f52d4e302d75d52d4e3024dde71d4e302b7da70d4e30005dd70d4e302b7d970d4e30005d970d4e30016de60d4e30017da60d4e30006dd76d0e302b5de75d0e302b5dc75d0e30015de74d0e300179e74d0e30006df64d0e300079e64d0e30006dd64d0e300079d64d0e300079f54d0e300079c54d0e302cddf72d0e302cddd72d0e302c79f42d0e302c79d42d0e3024dde71d0e30007da70d0e30005dd70d0e30007d970d0e30016de60d0e30017da60d0e3002dfa70d8630006f761986300057f75586300057c7558630005bf7458630005bc7458630005ef7258630075ec7258630004ff75586300067f75586300047f755863003cfc75586300067c755863003c7c7558630004ff7458630006bf7458630004bf745863008cfc7458630006bc7458630004bc7458630004ff7258630006ef7258630004ef725863000cfe7258630004fd725863000cfc7258630006ec725863000cec725863004edf3258630006dd325863004ef6315863004ef5315863024edc315863001cff70586300057e75186300057d751863001ef66118630006f56118630055fa701863003cff76d4630004fe76d4630004fd76d463003e7e65d46300067d65d4630015de73d4630005dd73d463018f5c53d463001cff7694630004fe7694630004fd76946300067f659463003e7c6594630015de7394630005dd73946300075f539463001ef66194630006f56194630007775194630004ff7654630004fd7654630004fc765463003e7e65546300067d6554630005df7354630015dc735463016f5c535463001ef66154630006f5615463001cff7614630004fe7614630004fd76146300067f651463003e7c6514630015dc73146302b75f531463008cff76d0630004fe76d0630004fd76d0630015de73d0630005dd73d063001cff7690630004fe7690630004fd76906300057e75906300057d7590630006bf6490630006bc6490630015de7390630005dd73906300079f4390630004ff7650630004fd7650630004fc7650630005df7350630015dc735063001cff7610630004fe7610630004fd7610630006bf641063008ebc6410630015dc73106300079f43106302b5de758c63024f5e758c6300055e758c63024f5d758c63024ddc758c630005de748c630
  | 16 => 0x40004ff76500400057f75500400057c7550040005df7350040085dc7350040005bf7650040006bf7650040004bf76500400073f75500402f5be75500402f5bc75500400073c75500400053c75500400079f7350040085be7350040085bc73500400079c73500400859c7350040006bd63500402edbf72500402edbd7250040255bc715004008dbf70500402e6be605004008dfb7650040006fb7650040004fb76500400077b755004000778755004008dfb7450040007bb745004008efa645004008fba6450040007db7350040007d873500400ef5c53d96300cdfa70d963008cfe74d9630004fd74d9630006dd73d96300ee7e53d96300ee7c53d96300eedc53d9630004ff72d963000cfe72d9630004fd72d963000cfc72d96300067f52d96300067d52d96300eedf32d9630006dd32d963001cfe71d9630004fd71d96300ccfe70d9630006fa70d96300e4fd76996300067f659963003cff7659630005bf7459630005bc74596300067f7559630004ff7459630006bf7459630004bf745963008cfc7459630006bc7459630004bc7459630006df73596300e67f53596300e67d53596300e6dc5359630004ff725963000cfe7259630004fd725963000cfc72596300e6df3259630006dd3259630004ff715963001cfc715963003e7e65196300067d65196300cf5c5319630005f67119630005f571196300edfa70196300b79c43d9230085fa70d923003cfe75d9230004fd75d9230006dd73d92300b6be43d92300b6bc43d92300b6dc43d9230004ff72d923000cfe72d9230004fd72d923000cfc72d9230006bf42d9230006bd42d92300b6df32d9230006dd32d923001cfe71d9230004fd71d9230084fe70d9230006fa70d92300acfd7699230006bf649923003cfe7599230004fd759923008ebf43992300bebd439923008cff729923000cfe7299230004fd729923000cfc729923001cfe7199230004fd71992300057f75592300057c7559230004ff75592300067f75592300047f755923003cfc75592300067c755923003c7c7559230006bf7459230006df73592300aebf43592300aebd43592300aedc4359230004ff725923000cfe7259230004fd725923000cfc72592300aedf3259230006dd3259230004ff715923001cfc7159230006bd64192300879c43192300b5fa701923003cfe7519230004fd751923008cfe741923008ebe741923008edd7319230086be431923008ebc431923008cff721923000cfe7219230004fd721923000cfc721923008ebf4219230006bd421923001cfe7119230004fd71192300b4fe701923008efa701923003cff76d5230004fe76d5230004fd76d523003cfc76d5230006bf64d5230006bc64d5230015de73d5230005dd73d523008cff7695230004fe7695230004fd769523008cfc76952300067
  | 17 => 0x8dbe74d4c40005bd74d4c402f73c54d4c400875e53d4c40004ff7654c40004fd7654c4008cfc7654c4003e7e6554c400067d6554c40005bf7454c4008dbc7454c400073c5454c40016de6354c40006dd6354c40005fb7054c40005f87054c400bcff7650c40085bf7450c400bebe6450c4008f9c4350c4008ef7619844001ef4619844008ef46158440004ff755844003cfc7558440004ff7358440014fe7358440014fc7358440004ff725844000cfe7258440004fd725844000cfc7258440006bf4258440006bd425844008ef7415844008ef44158440006f62158440006f5215844003cff76d444008cfe76d4440004fd76d444003e7e65d44400067d65d444008dbe74d4440005bd74d44402f73c54d444001cff769444008cfe7694440004fd769444008dbe7494440005bd749444001ef66194440006f56194440007775194440004ff7654440004fd765444008cfc765444003e7e65544400067d6554440005bf745444008dbc74544400073c545444001ef66154440006f5615444001cff761444008cfe7614440004fd7614440004fd76904400057e75904400057d7590440005bd7690440256bd76904402f5be75904402573e75904400053e75904402573d7590440255bc7590440085be7390440255bc7390440006bd6390440255bf729044032dbd729044008dbe7190440256bd6190440005bd709044025ebe6090440004ff76504402f5be751044008dbc7510440085be731044008dbc7310440006bd631044008dbf7210440325bd7210440255be711044008fb6711044008fb66110440256bd611044008fb56110440006b5611044031fb72110440257b4211044008fba7010440005bd701044008fb9701044025ebe601044001cff768c44008cfe768c440004fd768c4400057e758c4400057d758c44008dbe748c440005bd748c44001ef6618c440006f5618c440005fa708c440005f9708c440004ff764c440004fd764c44008cfc764c440005bf744c44008dbc744c440016de634c440006dd634c44001ef6614c440006f5614c440004fd76d4040004ff769404003cfd769404003e7e65940400067d659404008dbe7494040005bd74940400073c5494040004ff7654040005bf745404008dbc7454040005df7354040085dc735404003cff761404008cfe7614040004fd761404008cfc761404003e7e65140400067d651404008dbe7414040005bd74140402f73c5414040005f67114040005f571140402f5be75d004008dbc75d0040085be73d004008dbc73d0040006bd63d004008dbf72d0040315bd72d0040255be71d00402edbd749004030ebe649004008df9749004008efa649004008fba6490040007bb549004008fb85490040307ba439004008fb8439004008fbb42900402ffb94290040007ba419004008fb8419
  | 18 => 0xf634c540016dc634c540004fe76d414008cfc76d41400067f65d414003e7c65d4140005be74d4140005bd74d4140006df63d41400fedc63d4140004fe76941400067f659414003e7c6594140006df63941400eedc63941400077b509414003cff7654140004fd765414003cfc76541400067f655414003e7c6554140005bf7454140005bc7454140005df73541400addc7354140006df63541400e6dc6354140004fe76141400067f651414003e7c6514140006df63141400cedc6314140005f67114140005f571141400067f65d01400067c65d0140006df63d01400bedc63d01400077b65d01400077865d0140007db63d0140007d863d014008fbb43d0140007b943d01400067f65901400067c6590140006df63901400b6dc63901400073f6590140336be6590140336bc65901400073c65901400063c6590140005bd73901400079f63901400b6be63901400b6bc63901400079c63901400b69c639014035ebf629014035ebd629014025ebc6190140007bb609014008cfe74d944008ebe74d9440014fe73d9440004fd73d9440014fc73d944008cff72d944000cfe72d9440004fd72d944000cfc72d944008ebf42d9440006bd42d944001cfe71d9440004fd71d9440004fe70d944008efa70d9440004fd769944008e7f659944008e7c659944003cff765944008e7c655944008e7f755944003cff745944008cfe745944003cfd745944008cfc7459440006bc745944008e7e545944008e7c5459440004ff7359440014fe7359440014fc7359440004ff725944000cfe7259440004fd725944000cfc72594400067f52594400067d5259440006bf4259440006bd4259440004ff715944001cfc7159440004fd76d504008f3e54d5040005bd76d50402f6bd76d504008dbe75d50402f6bf65d50402f6bd65d5040085be73d5040085bc73d50402f5bf72d5040355bd72d50402f73f52d504034f3d52d5040255be71d5040005bd70d5040336be60d5040004ff765504008f3c545504008ebd7615040004bd76150402f5be751504008f3e751504008ebf651504008f3e65150402f6bd651504008f3d6515040085be731504008dbc731504008dbf7215040345bd721504033f3e52150402f73c5215040255be711504008fba7015040005bd701504008fb97015040336be6015040014ff7658c4008edc6358c4008f9c4358c40004ff7558c4003cfc7558c40014fd7458c40006bf5458c40006bc5458c40086de5358c4008edf4358c40086be4358c40086bc4358c4008edc4358c40004ff7258c4000cfe7258c40004fd7258c4000cfc7258c40006bf4258c40006bd4258c40086df3258c40006dd3258c40004ff7158c4001cfc7158c40086df3158c40086dc3058c4003cff76d4c4008cfe76d4c40004fd76d4c4003e7e65d4c400067d65d4c40
  | 19 => 0x4d4003e7c6554d40006df6354d40016dc6354d400b4fe76d0d400067f65d0d400067c65d0d40016dc63d0d40005be76d0d400b6be76d0d400b4be76d0d400073f65d0d4037ebe65d0d4037ebc65d0d400073c65d0d400063c65d0d400adbd73d0d400079f63d0d40016be63d0d40016bc63d0d400af9c63d0d400169c63d0d40376bf62d0d40376bd62d0d40296bc61d0d40005be70d0d4008ebf60d0d400af9c30d0d40014fc7650d400067f6550d400067c6550d40006df6350d40016dc6350d40005fb7050d40005f87050d400adbc7650d40016bc7650d40014bc7650d400073f6550d4036ebe6550d4036ebc6550d400073c6550d400063c6550d400adbf7350d400079f7350d400079f6350d40016be6350d40016bc6350d400af9c6350d400169c6350d40366bf6250d40366bd6250d400af9f3250d403679d3250d4028ebc6150d40007bb7050d40005bc7050d40007b87050d400067f65d85400067c65d8540006df63d8540006dc63d854003cfe75d8540004fd75d8540014fe73d8540004fd73d8540014fc73d8540004ff72d854000cfe72d8540004fd72d854000cfc72d8540006f721d8540006f421d85400057e75985400057d75985400067f65985400067c65985400adde7398540005dd7398540006df6398540006dc6398540006f761985400057f75585400057c75585400067f65585400067c6558540005df73585400addc7358540006df6358540006dc6358540005ef72585400a5ec72585400067f65185400067c6518540006df6318540006dc631854001ef66118540006f56118540004fe76d4540004fd76d454003cfc76d45400067f65d454003e7c65d4540006df63d454018edc63d4540004fe7694540004fd769454001cfc76945400067f659454003e7c6594540006df639454017edc6394540007775194540004ff7654540004fe7654540004fc76545400067f655454003e7c6554540006df635454016edc6354540004fe7614540004fd761454001cfc76145400067f651454003e7c6514540006df631454015edc6314540004fe76d05400067f65d05400067c65d0540006df63d054014edc63d05400057e75905400057d75905400067f65905400067c6590540006df6390540146dc6390540006f7619054001ef46190540005fa7090540005f9709054001cfc76505400067f65505400067c6550540006df6350540136dc6350540006f7615054001ef46150540005fb7050540005f87050540004fe76105400067f65105400067c6510540006df631054011edc6310540007b54110540004fe768c540004fd768c54001cfc768c5400057e758c5400057d758c5400067f658c5400067c658c540006df638c540016dc638c540004ff764c540004fe764c540004fc764c5400067f654c5400067c654c540006d
  | 20 => 0x67f62195400067e62195400067d62195400067c621954003e7f741954003e7d741954003e7f731954003e7e731954003e7d731954003e7c73195400067e43195400067c431954003e7f721954003e7e721954003e7d721954003e7c72195400067f42195400067e42195400067d42195400067c42195400067f32195400067e32195400067d32195400067c321954003e7f711954003e7e711954003e7d711954003e7c71195400067f31195400067c31195400067f21195400067e21195400067d21195400067c211954003e7f701954003e7d70195400067d40195400067f30195400067c30195400067f20195400067e20195400067d20195400067c2019540004fe76d51400067f65d514003e7c65d51401eedc63d5140005fa70d5140005f970d5140004fe76951400067f659514003e7c65951400073f54951401dedc639514003cfc76551400067f655514003e7c65551401d6dc6355140005fb7055140005f87055140004fe76151400067f651514003e7c65151401bedc6315140014fe76d8d400067f65d8d400067c65d8d400aede63d8d4003cfe75d8d40004fd75d8d40014fc74d8d400aede53d8d400aedc53d8d400aede43d8d40004ff72d8d4000cfe72d8d40004fd72d8d4000cfc72d8d400aedf32d8d40006de32d8d40006dd32d8d400aedc32d8d4001cfe71d8d40004fd71d8d400aedf31d8d400aedc31d8d400aedf30d8d400adde76d8d40014de76d8d40006df65d8d400075f65d8d400065f65d8d40006de65d8d40006dd65d8d40006dc65d8d400075c65d8d400065c65d8d400079f74d8d40006df62d8d40006de62d8d40006dd62d8d40006dc62d8d40006df75d8d40006de75d8d40006dd75d8d40006dc75d8d40006df74d8d400aede74d8d40006df54d8d40006de54d8d40006dd54d8d40006dc54d8d40006df72d8d40006de72d8d40006dd72d8d40006dc72d8d40006df52d8d40006de52d8d40006dd52d8d40006dc52d8d40006df42d8d40006de42d8d40006dd42d8d40006dc42d8d40006df71d8d40006de71d8d40006dd71d8d40006dc71d8d40006df21d8d40006de21d8d40006dd21d8d40006dc21d8d40006df70d8d400aede70d8d40006dd70d8d40006df20d8d40006de20d8d40006dd20d8d40006dc20d8d400057f7558d400057c7558d400067f6558d400067c6558d400aedc6358d40005de7618d400aede7618d40006df6518d400075f6518d400065f6518d40006de6518d40006dd6518d40006dc6518d400075c6518d400065c6518d400af9d7418d40006df6218d40006de6218d40006dd6218d40006dc6218d40004fe76d4d40004fd76d4d4003cfc76d4d400067f65d4d4003e7c65d4d40006df63d4d40016dc63d4d400af5e53d4d40004ff7654d40004fe7654d40004fc7654d400067f655
  | 21 => 0xd729064025fb6619064025ebd6190640007b5619064025fba7090640005bd709064025fb9709064001cff765064001ef66150640006f56150640005fb7050640005f87050640005bd761064025ebd7610640335be751064025dbc75106400b5be731064025dbc7310640006bd631064025dbf721064038dbd721064025fb6711064025ebd6110640387b7211064025fb42110640005bd701064001cff768c640004fe768c640004fd768c6400057e758c6400057d758c640005be748c640005bd748c64001ef6618c640006f5618c640004ff764c640004fd764c640004fc764c640005bf744c640005bc744c64001ef6614c640006f5614c64003cfd769424003e7e65942400067d6594240005be7494240005bd74942400073c54942400077b5094240005bf7454240005bc7454240005df73542400b5dc735424003e7e65142400067d6514240005be7414240005bd74142403373c5414240005f67114240005f57114240005bd76d0240006bd76d0240335be75d0240335bc75d02400b5be73d02400b5bc73d0240006bd63d024030dbf72d024030dbd72d024025dbe71d0240007ba50d0240007b950d0240005f976d024008ef976d024008fba54d0240007b954d024003cfe76d954008cfe74d954008cfc74d9540014fe73d9540004fd73d9540014fc73d95400067e53d95400067c53d9540004ff72d954000cfe72d9540004fd72d954000cfc72d95400067f52d95400067e52d95400067d52d95400067c52d954001cfe71d9540004fd71d954003c7e76d95400067e63d95400067c63d95400067f62d95400067e62d95400067d62d95400067c62d95400067f74d95400067d74d95400067f73d95400067e73d95400067d73d95400067c73d95400067e43d95400067c43d95400067f72d95400067e72d95400067d72d95400067c72d95400067f42d95400067e42d95400067d42d95400067c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95400067f31d95400067c31d95400067f21d95400067e21d95400067d21d95400067c21d95400067f70d95400067d70d95400067f30d95400067c30d95400067f20d95400067e20d95400067d20d95400067c20d95400067f65995400adde7399540005dd7399540005df73595400addc73595400067f7559540004ff7459540006bf7459540004bf7459540004ff7359540006df7359540004df7359540014fe7359540014fc7359540006dc7359540014dc7359540004ff725954000cfe7259540004fd725954000cfc7259540004ff715954001cfc7159540004ff7059540006fb7059540004fe761954003e7e65195400067d65195400057e76195400067e76195400047e76195400067e63195400067c6319540
  | 22 => 0x9640004fd725964000cfc72596400067e52596400067c5259640006bf4259640006bd4259640004ff715964001cfc715964003e7e65196400067d6519640005f67119640005f5711964003e7e65d52400067d65d5240005fa70d5240005f970d5240336bd76d5240336bf65d52403373e65d5240336bd65d52400073d65d52400063d65d52400b5be73d52400b5bc73d5240335bf72d52403b5bd72d52403373f52d52403af3d52d524025dbe71d5240337ba70d5240005bd70d5240337b970d5240005b970d52400067f659524003e7c65952400073f549524003cff765524003e7e65552400067d6555240005fb7055240005f870552400067f651524003e7c65152400073d5415240005bd7615240336bd76152403373e7515240336bf65152400073f6515240336bd65152403373c65152400b5be73152400b5bc7315240335bf72152403a5bd721524039f3e52152403373c521524025dbe7115240005bd70152400b6de63d8e400b79c43d8e40014ff7658e400b6dc6358e400b79e4358e40004ff7558e4003cfc7558e40006bf5458e40006bc5458e400b6be4358e400b6de4358e400b6bc4358e40004ff7258e4000cfe7258e40004fd7258e4000cfc7258e40006bf4258e40006bd4258e40004ff7158e4001cfc7158e400b6dc3058e4003cff76d4e40004fe76d4e40004fd76d4e4003e7e65d4e400067d65d4e40005be74d4e40005bd74d4e403373c54d4e400b75e53d4e40004ff7654e40004fd7654e40004fc7654e4003e7e6554e400067d6554e40005bf7454e40005bc7454e400073c5454e400acfd76d0e400b5be74d0e40016dc63d0e400b79e43d0e40014ff7650e400b5bf7450e40016de6350e40006dd6350e400b79c4350e40005fb7050e40005f87050e40006f76198640004ff755864003cfc7558640004ff7358640014fe7358640014fc7358640004ff725864000cfe7258640004fd725864000cfc7258640006bf4258640006bd4258640006f72158640006f421586400057e75186400057d751864001ef66118640006f5611864003cff76d4640004fe76d4640004fd76d464003e7e65d46400067d65d4640005be74d4640005bd74d46403373c54d464001cff7694640004fe7694640004fd7694640005be7494640005bd749464001ef66194640006f56194640007775194640004ff7654640004fd7654640004fc765464003e7e65546400067d6554640005bf7454640005bc74546400073c545464001ef66154640006f5615464001cff7614640004fe7614640004fd76146400057e75906400057d759064001ef66190640006f56190640005fa7090640005f97090640335be759064025f3e75906400053e759064025f3d759064025dbc75906400b5be739064025dbc7390640006bd639064025dbf7290640395b
  | 23 => 0x14fe7359740014fc73597400067e53597400067c5359740004ff725974000cfe7259740004fd725974000cfc72597400067f52597400067d5259740004ff715974001cfc715974008f3e54d5340014ff7658f4008edc6358f40004ff7558f4003cfc7558f400bedc5358f4008edf4358f4008edc4358f40004ff7258f4000cfe7258f40004fd7258f4000cfc7258f400bedf3258f40006dd3258f40004ff7158f4001cfc7158f400bedc3158f400bedf3058f4003cff76d4f4008cfe76d4f40004fd76d4f400067f65d4f4003e7c65d4f40016de63d4f40006dd63d4f400bf5e53d4f40004ff7654f40004fd7654f4008cfc7654f400067f6554f4003e7c6554f40005fb7054f40005f87054f4008dbd76d0f40016bd76d0f40014bd76d0f4037ebe65d0f4008ebc65d0f40016be63d0f4008f9e63d0f400169e63d0f4008f9d63d0f40016bc63d0f4008ebf62d0f403c6bd62d0f40296be61d0f40005be70d0f4008fba70d0f4008fb970d0f400bf9c30d0f40084ff7650f40005bf7650f40086bf7650f40084bf7650f4036ebe6550f4036ebc6550f4008f9f7350f40016be6350f40016bc6350f403bebf6250f403bebd6250f400bf9f3250f403bf9d3250f4028ebe6150f40005bc7050f400057e75987400057d759874008ef7619874001ef4619874008ef46158740004ff755874003cfc7558740004ff7358740014fe7358740014fc7358740004ff725874000cfe7258740004fd725874000cfc725874008ef7415874008ef4415874003cff76d474008cfe76d4740004fd76d47400067f65d474003e7c65d474001cff769474008cfe7694740004fd769474003e7e65947400067d6594740007775194740004ff7654740004fd765474008cfc76547400067f655474003e7c655474001cff761474008cfe7614740004fd761474003e7e65147400067d65147400057e75907400057d759074008fb4415074001cff768c74008cfe768c740004fd768c7400057e758c7400057d758c740016de638c740006dd638c740005fa708c740005f9708c740004ff764c740004fd764c74008cfc764c74003e7e65d43400067d65d434008dbe74d4340005bd74d43400067f659434003e7c659434003cff765434003e7e65543400067d6554340005bf745434008dbc7454340005df73543400bddc73543400067f651434003e7c6514340005f67114340005f57114340006bd74d9640014fe73d9640004fd73d9640014fc73d9640004ff72d964000cfe72d9640004fd72d964000cfc72d96400067f52d96400067d52d9640006bf42d9640006bd42d964001cfe71d9640004fd71d9640006fa70d9640004fd76996400067f659964003cff76596400067f7559640006bf7459640004ff7359640014fe7359640014fc7359640004ff725964000cfe725
  | 24 => 0x62158450006f52158450006f4215845003e7f505845003ef7755845003ef6755845003ef47558450006f77458450006f67458450006f57458450006f4745845003ef7545845003ef6545845000676545845003ef5545845003ef4545845003e745458450006f77358450006f67358450006f57358450006f4735845003ef7535845003ef6535845000676535845003ef5535845003ef4535845003e745358450006f74358450006f64358450006f54358450006f44358450006f77258450006f67258450006f57258450006f4725845003ef7525845003e77525845003ef6525845003ef5525845000675525845003ef45258450006f74258450006f64258450006f54258450006f44258450006f73258450006f63258450006f53258450006f43258450006f67058450006f4705845003ef7505845003e77505845003ef6505845003ef5505845003ef45058450006f73058450006f43058450006f72058450006f62058450006f52058450006f4205845003d7d76944502667d76944500047d76944500057e74944500cd7e73944502657c73944500067d63944502657f72944503dd7d729445003d7e719445003f76719445003e7f619445003f7661944502667d619445003f7561944500067561944500057d709445026e7e609445003f7a609445008cff76d045003cfe76d0450004fd76d045003d7e75d04500057d75d045001ef661d0450006f561d045001cff769045003cfe7690450004fd769045003d7e75904500057d759045001ef66190450006f56190450004ff7650450004fd765045003cfc76504500057f755045003d7c755045001ef66150450006f5615045001cff761045003cfe7610450004fd76104502657f751045003d7c751045001ef66110450006f5611045001cff768c45003cfe768c450004fd768c45003d7e758c4500057d758c45001ef6618c450006f5618c450004ff764c450004fd764c45003cfc764c4500057f754c45003d7c754c45001ef6614c450006f5614c45003d7f76540500067f76540500047f76540500073f74540500057c74540500073c74540500053c74540500075f73540500cd7e73540500cd7c73540500075c73540500cd5c73540500067d63540503d57f72540503d57d72540502657c715405003f7661540500067d615405003f75615405000675615405003d7f705405003f7b70540503ce7e605405003f7a605405008ebe74d9740014fe73d974008ede73d9740014de73d9740004fd73d974008edd73d9740004dd73d9740014fc73d974008cff72d974000cfe72d9740004fd72d974000cfc72d974001cfe71d9740004fd71d974008ef970d9740004fd769974008e7f659974008e7c659974003cff765974008e7c655974008e7f755974008e7e545974008e7c5459740004ff7359740
  | 25 => 0x415003f7b609415008ebe749905003ebf549905008ebc5499050014fe7399050004fd7399050014fc739905008cff729905000cfe7299050004fd729905000cfc729905008ebf4299050006bd429905001cfe7199050004fd719905003ebf745905003ebf545905003e7c545905003ebc5459050004ff7359050014fe7359050014fc7359050004ff725905000cfe7259050004fd725905000cfc725905003e7f52590500067d5259050006bf4259050006bd4259050004ff715905001cfc715905003d7d76950500067d769505003d7e749505003f3e74950500067d64950500cd7e73950500cd7c73950503f57f72950503f57d72950501c67e629505003e7c62950503ef3f42950503ef3d42950502657e719505003f76619505003f7561950500057d70950503e67e609505003f7a6095050014fd7558c50004ff7458c5008cfc7458c500067e5458c5003e7c5458c5003edf7358c5003edf5358c500ce7e5358c5003e7c5358c5003edc5358c500cede4358c50004ff7258c5000cfe7258c50004fd7258c5000cfc7258c5003e7f5258c500067d5258c500cedf3258c50006dd3258c50004ff7158c5001cfc7158c5003e7c5158c5003e7f5058c500cedc3058c5008cff76d0c5003cfe76d0c50004fd76d0c5003d7e75d0c500057d75d0c5008ebe64d0c50006bd64d0c5037f3c54d0c50004ff7650c50004fd7650c5003cfc7650c500057f7550c5003d7c7550c50006be6450c50006bd6450c5036f3c5450c50016de6350c50006dd6350c50005fb7050c50005f87050c5001ef7759845001ef6759845001ef5759845001ef4759845001ef7749845001ef6749845001ef5749845001ef4749845003ef7549845003ef6549845003ef5549845003ef4549845001ef7739845001ef6739845001ef5739845001ef4739845003ef7539845003ef6539845003ef5539845003ef45398450006f74398450006f64398450006f54398450006f4439845001ef7729845001ef6729845001ef5729845001ef4729845003ef7529845003ef6529845003ef5529845003ef45298450006f74298450006f64298450006f54298450006f44298450006f73298450006f63298450006f53298450006f4329845001ef6709845001ef4709845003ef7509845003ef6509845003ef5509845003ef45098450006f73098450006f43098450006f72098450006f62098450006f52098450006f42098450004ff745845008cfc74584500067e545845003e7c5458450004ff7358450014fe7358450014fc73584500067e535845003e7c5358450004ff725845000cfe7258450004fd725845000cfc725845003e7f52584500067d525845003ef7715845003ef7515845003e7c515845003ef4515845003e745158450006f73158450006f43158450006f72158450006f
  | 26 => 0x4fd74d8550014fe73d8550004fd73d8550014fc73d8550004ff72d855000cfe72d8550004fd72d855000cfc72d8550006f721d8550006f421d8550005be7498550005bd7498550006bf6498550006bc64985500e5de7398550005dd7398550006df6398550006dc6398550006f76198550005bf7458550005bc7458550006bf6458550006bc6458550005df73585500e5dc7358550006df6358550006dc6358550005ef72585500ddec7258550006bf6418550006bc6418550006df6318550006dc631855001ef66118550006f561185500057e76d455003e7e76d45500047e76d45500073f64d45500067c64d45500073c64d45500063c64d45500057d73d45500075f63d455018e7e63d455018e7c63d45500075c63d455018e5c63d45504167f62d45504167d62d455001e7e61d455001e7c61d45500057e70d455003e7f60d455003f7b60d455040d7d7594550006bf6494550006bc6494550006df639455017edc6394550006f7619455001ef4619455003f775194550005fa7094550005f9709455001cfc7654550006bf6454550006bc6454550006df635455016edc6354550006f7615455001ef4615455003f745154550005fb7054550005f8705455001c7c76545500073f64545500067c64545500073c64545500063c64545500057f73545500075f635455016e7e635455016e7c63545500075c635455016e5c63545504067f62545504067d625455003d7f715455003f77715455000777615455001e7e615455001e7c61545500077461545500077b70545500057c705455000778705455003e7f605455003f7b6054550004fe76d0550004fd76d055008cfc76d0550006bf64d055008ebc64d0550006df63d055014edc63d0550004fe7690550004fd769055001cfc769055003d7e75905500057d7590550006bf6490550006bc6490550006df6390550146dc6390550004ff7650550004fe7650550004fc7650550006bf6450550006bc6450550006df6350550136dc6350550004fe7610550004fd761055001cfc761055003d7e75105500057d7510550006bf641055008ebc6410550006df631055011edc6310550004fe768c550004fd768c55001cfc768c55003d7e758c5500057d758c550006bf648c550006bc648c550006df638c550016dc638c550004ff764c550004fe764c550004fc764c55003d7e754c5500057d754c550006bf644c550006bc644c550006df634c550016dc634c550006bf6494150006bc6494150006df63941500eedc639415003dfa709415003efb60941500073f64941500067c64941500073c64941500063c64941500057d73941500075f63941500ee7e63941500ee7c63941500075c63941500ee5c63941503fe7f62941503fe7d62941500057d719415026e7c619415003d7e709415003e7f609
  | 27 => 0xd74d8d500e6de53d8d500e6de43d8d500e6dc43d8d50004ff72d8d5000cfe72d8d50004fd72d8d5000cfc72d8d500e6df32d8d50006de32d8d50006dd32d8d500e6dc32d8d5001cfe71d8d50004fd71d8d500e6df31d8d500e6dc31d8d5003cfd70d8d500e6df30d8d500e5de76d8d50014de76d8d500075f75d8d50006df64d8d500079f64d8d500069f64d8d50006de64d8d50006dd64d8d50006dc64d8d500079c64d8d500069c64d8d50006df62d8d50006de62d8d50006dd62d8d50006dc62d8d502b7db50d8d502b7d850d8d50006df75d8d500e6de75d8d50006df74d8d50006de74d8d50006dd74d8d50006dc74d8d502b6df54d8d50006de54d8d50006dd54d8d502b6dc54d8d50006df72d8d50006de72d8d50006dd72d8d50006dc72d8d502b6df52d8d50006de52d8d50006dd52d8d502b6dc52d8d50006df42d8d50006de42d8d50006dd42d8d50006dc42d8d50006df71d8d50006de71d8d50006dd71d8d50006dc71d8d502b6df51d8d502b6dc51d8d50006df21d8d50006de21d8d50006dd21d8d50006dc21d8d502b6df70d8d500e6de70d8d50006dd70d8d502b6df50d8d502b6dc50d8d50006df20d8d50006de20d8d50006dd20d8d50006dc20d8d50005bf7458d50005bc7458d50006bf6458d50006bc6458d500e6dc6358d50005de7618d500e6de7618d500e75d7518d50006df6418d500079f6418d500069f6418d50006de6418d50006dd6418d50006dc6418d500079c6418d500069c6418d50006df6218d50006de6218d50006dd6218d50006dc6218d500fedf6018d5042fdb5018d5042fd85018d500057e76d4d5003e7e76d4d500ec7e76d4d500073f64d4d500067c64d4d500073c64d4d500063c64d4d500e57d73d4d500075f63d4d500167e63d4d500167c63d4d500e75c63d4d500165c63d4d504267f62d4d504267d62d4d500057d71d4d502a67c61d4d500057e70d4d5003e7f60d4d5003f7b60d4d500e75c30d4d50014fc7654d50006bf6454d50006bc6454d50006df6354d50016dc6354d50005fb7054d50005f87054d500e57c7654d500167c7654d500147c7654d500073f6454d500067c6454d500073c6454d500063c6454d5003d7f7354d5003f5f7354d500075f6354d500167e6354d500167c6354d500e75c6354d500165c6354d5041e7f6254d5041e7d6254d500e75f3254d5041f5d3254d500057f7154d5029e7c6154d500077b7054d500057c7054d50007787054d5003e7f6054d5003f7b6054d50004fe76d0d50004fd76d0d5008cfc76d0d50006bf64d0d5008ebc64d0d50006df63d0d50016dc63d0d50004ff7650d50004fe7650d50004fc7650d50006bf6450d50006bc6450d50006df6350d50016dc6350d50006bf64d8550006bc64d8550006df63d8550006dc63d855008cfe74d8550
  | 28 => 0x425003e7d76d42500057e74d42500ed7e73d425003d7c73d42500067d63d425003d7f72d425043d7d72d425026d7e71d42500067d61d425003f7a60d42504377b20d42504377820d4250014fe73d9150004fd73d9150014fc73d9150006be43d9150006bc43d9150004ff72d915000cfe72d9150004fd72d915000cfc72d9150006bf42d9150006be42d9150006bd42d9150006bc42d915001cfe71d9150004fd71d9150006be63d9150006bc63d9150006bf62d9150006be62d9150006bd62d9150006bc62d9150337bb50d9150337b850d9150006bf75d9150336be75d9150006bf73d9150006be73d9150006bd73d9150006bc73d9150336bf53d9150006be53d9150336bc53d9150006bf72d9150006be72d9150006bd72d9150006bc72d9150336bf52d9150006be52d9150006bd52d9150336bc52d9150006bf32d9150006be32d9150006bd32d9150006bc32d9150006bf71d9150006be71d9150006bd71d9150006bc71d9150336bf51d9150336bc51d9150006bf31d9150006bc31d9150006bf21d9150006be21d9150006bd21d9150006bc21d9150336bf70d9150006bd70d9150336bf50d9150336bc50d9150006bf30d9150006bc30d9150006bf20d9150006be20d9150006bd20d9150006bc20d9150006bf64991500e5de7399150005dd7399150005df73591500e5dc7359150006bd6419150014fe7319150004fd7319150014fc7319150006be431915008ebc431915008cff721915000cfe7219150004fd721915000cfc721915008ebf4219150006be4219150006bd421915008ebc421915001cfe7119150004fd7119150005be7619150006be7619150006be6319150006bc6319150006bf6219150006be6219150006bd6219150006bc62191502f7bb50191502f7b8501915008ebf75191502f6be751915008ebf7319150006be7319150006bd731915008ebc73191502f6bf5319150006be53191502f6bc531915008ebf7219150006be7219150006bd721915008ebc72191502f6bf5219150006be5219150006bd52191502f6bc5219150006bf3219150006be3219150006bd3219150006bc321915008ebf7119150006be7119150006bd711915008ebc71191502f6bf51191502f6bc5119150006bf3119150006bc3119150006bf2119150006be2119150006bd2119150006bc211915008ebf7019150006bd70191502f6bf5019150006bd50191502f6bc5019150006bf3019150006bc3019150006bf2019150006be2019150006bd2019150006bc2019150006bf649515008ebc649515003f3f54951501dedc6395150005fa7095150005f97095150006bf6455150006bc64551501d6dc6355150005fb7055150005f87055150014fe76d8d50006bf64d8d50006bc64d8d500e6de63d8d50014fc75d8d5008cfe74d8d50004f
  | 29 => 0x1c67e62952501c67c62952503e73f42952503e73d429525026d7e71952500077a70952500057d709525000779709525000579709525003e7e6095250006be6455250006bd645525003f3c5455250005fb7055250005f8705525003f7b50552500057d761525003e7d761525003f3e74152500073f64152500067d64152500073c64152500ed7e731525003d7c731525003d7f72152504557d72152501b67e62152501b67c621525026d7e71152500057d701525003f7a60152500eede63d8e500ef5c53d8e50014ff7658e5003d7c7558e500eedc6358e500ef5e5358e50004ff7458e5008cfc7458e500067e5458e500067c5458e500ee7e5358e500eede5358e500ee5e5358e500ee7c5358e50004ff7258e5000cfe7258e50004fd7258e5000cfc7258e500067f5258e500067d5258e50004ff7158e5001cfc7158e5003cfc7058e500eedc3058e50014ff7654e500ed7f7554e50016de6354e50006dd6354e5003f5c5354e50005fb7054e50005f87054e5003f7b5054e5008cff76d0e50004fe76d0e50004fd76d0e5003d7e75d0e500057d75d0e5008ebe64d0e50006bd64d0e500073c54d0e50004ff7650e50004fd7650e50004fc7650e500057f7550e5003d7c7550e50006be6450e50006bd6450e500073c5450e50006f76198650004ff745865008cfc74586500067e54586500067c5458650004ff7358650014fe7358650014fc73586500067e53586500067c5358650004ff725865000cfe7258650004fd725865000cfc72586500067f52586500067d525865001ef66118650006f5611865001ef66194650006f5619465003f775194650005fa7094650005f970946500057e74946500ed7e739465026d7c73946500067d639465026d7f729465044d7d729465003d7e719465026f76619465026e7d619465000775619465000675619465026f7a70946500057d709465026f79709465000579709465003e7e609465001cff765465001ef66154650006f56154650005fb7054650005f8705465003f7b50546500057d761465003e7d76146500057e74146500ed7e731465003d7c73146500067d631465003d7f72146504457d721465003f76711465026e7d61146500057d701465003f7a601465008cff76d0650004fe76d0650004fd76d065003d7e75d06500057d75d065001cff7690650004fe7690650004fd769065003d7e75906500057d7590650004ff7650650004fd7650650004fc76506500057f755065003d7c755065001cff7610650004fe7610650004fd761065026d7f751065003d7c751065001cff768c650004fe768c650004fd768c65003d7e758c6500057d758c65001ef6618c650006f5618c650004ff764c650004fd764c650004fc764c6500057f754c65003d7c754c65001ef6614c650006f5614c6500057d76d
  | 30 => 0xc311813102ef9301813108ebe749935003ebf549935008ebc5499350014fe7399350004fd7399350014fc739935003e7f5399350006be439935008ebc439935008cff729935000cfe7299350004fd729935000cfc729935008ebf4299350006bd429935001cfe7199350004fd719935003e7f519935003e7c509935003ebf745935003ebf545935003ebc5459350004ff7359350014fe7359350014fc7359350006be4359350006bc4359350004ff725935000cfe7259350004fd725935000cfc7259350006bf4259350006bd4259350004ff715935001cfc7159350004ff7458f5008cfc7458f5003edf7358f5003edf5358f5003edc5358f500fedc4358f50004ff7258f5000cfe7258f50004fd7258f5000cfc7258f500fedf3258f50006dd3258f50004ff7158f5001cfc7158f500fedc3158f500fedf3058f5003d7f7654f500ce7f7654f500cc7f7654f500067e6454f5003f5f7354f500167e6354f500167c6354f5003e7f6254f5046e7d6254f500ff5f3254f5046f5d3254f500057f7154f5029e7e6154f500057c7054f5008cff76d0f5003cfe76d0f50004fd76d0f50016de63d0f50006dd63d0f50004ff7650f50004fd7650f5003cfc7650f50005fb7050f50005f87050f50004ff745875008cfc7458750004ff7358750014fe7358750014fc7358750004ff725875000cfe7258750004fd725875000cfc725875003ef7715875003ef7515875003ef4515875003d7f76547500067f76547500067e64547500057f735475016e7e635475003e7c635475003e7f62547504667d625475003f77715475003f77615475001e7e615475001e7c615475003f7461547500057c705475008cff76d075003cfe76d0750004fd76d075001cff769075003cfe7690750004fd769075003d7e75907500057d7590750006be6490750006bd6490750004ff7650750004fd765075003cfc765075001cff761075003cfe7610750004fd761075003d7e75107500057d751075008ebe6410750006bd641075001cff768c75003cfe768c750004fd768c75003d7e758c7500057d758c750016de638c750006dd638c750004ff764c750004fd764c75003cfc764c75003d7e754c7500057d754c750006bf6499250014fe7399250004fd7399250014fc739925008cff729925000cfe7299250004fd729925000cfc729925001cfe7199250004fd7199250004ff7359250014fe7359250014fc7359250004ff725925000cfe7259250004fd725925000cfc72592500067f52592500067d5259250004ff715925001cfc7159250006bd641925008ebe6495250006bd649525003f3f5495250005fa7095250005f9709525003d7e74952500073e64952500067d64952500073d64952500063d64952500ed7e73952500ed7c739525045d7f729525045d7d7295250
  | 31 => 0x953129e7c5159531004ff7059531004fc705953117cfe761953103e7e65195310067d65195310057e75d91310057d75d913103cfe75d91310067e75d913103c7e75d9131004fd75d91310067d75d91310047d75d913101cff73d913101cfd73d9131146bf43d9131146bd43d9131004ff72d913100cfe72d9131004fd72d913100cfc72d9131146df32d9131006dd32d9131004fe70d9131004fd70d9131006bf6499131135f5719913103cfe7599131004fd759913108cfe749913114cfd739913108edd739913108cff729913100cfe7299131004fd729913100cfc729913108ebf4299131006bd4299131134fd719913108ef57199131296be419913108ebc4199131004fe7099131004fd709913114df77159131004ff755913103cfc7559131006bf7459131134ff7359131006df7359131004ff725913100cfe7259131004fd725913100cfc7259131006bf4259131006bd4259131136df3259131006dd325913114cff7159131006f7715913128ebe415913128ebc4159131004ff7059131004fc7059131144fe7619131006bd641913103cfe7519131004fd751913108ebe741913101cff731913101cfd731913108ebf431913111ebd431913108cff721913100cfe7219131004fd721913100cfc7219131004fe7019131004fd701913103cff76d5131004fe76d5131004fd76d513103cfc76d513108cff7695131004fe7695131004fd769513108cfc769513103e7e65951310067d65951310073f5495131015de7395131005dd7395131004ff7655131004fe7655131004fd7655131004fc765513108cff7615131004fe7615131004fd761513108cfc761513103e7e65151310067d6515131014fe76d4531014fc76d45310067f65d453103e7c65d4531015de73d4531005dd73d453101f7651d453103cff7654531014fe765453116cfd7654531014fc76545310067f655453103e7c6554531005df7354531015dc735453101fd43154531014fe76d0531014fc76d0531006bf64d053108ebc64d0531015de73d0531005dd73d053108cff7650531014fe7650531134fd7650531014fc7650531006bf6450531006bc6450531005df7350531015dc735053103cfe75d8131004fd75d813108cfe74d8131004fd74d813101cfd73d8131004ff72d813100cfe72d8131004fd72d813100cfc72d8131066fa30d8131006fb60981310057f75581310057c7558131005bf7458131005bc7458131005ef7258131105ec72581310057e75181310057d7518131006f9601813103cfe75181310067e751813103c7e7518131004fd75181310067d75181310047d751813108cfe7418131004fd741813101cfd7318131004ff721813100cfe7218131004fd721813100cfc721813102edf3218131006dd321813102ef57118131246de3118131246d
  | 32 => 0x67d42596310067c425963116e7f325963116e7e325963116e7d325963116e7c325963101e7f715963101e7e715963101e7d715963101e7c715963101e7f415963101e7e415963101e7d415963101e7c415963101e7f315963101e7e315963101e7d315963101e7c315963101e7f215963101e7e215963101e7d215963101e7c21596310067f70596310067e70596310067d70596310067c705963116e7f305963116e7e305963116e7d305963116e7c30596310067f20596310067e20596310067d20596310067c205963101e7f105963101e77105963101e7e105963101e7d105963101e7c105963103cfe7599231004fd759923101ebe749923108ebf439923114ebd439923108cff729923100cfe7299231004fd729923100cfc729923108ebf4299231006bd429923101cfe719923101cfc719923101ebe419923101ebc4199231004fe7099231004fd709923114edc3099231004ff755923103cfc755923101ebf7459231136bf4359231136bd4359231004ff725923100cfe7259231004fd725923100cfc7259231006bf4259231006bd425923101cfe715923101cfc715923101ebe415923101ebc4159231004ff7059231004fc705923103cff76d523101cfe76d5231004fd76d523101cfc76d523103e7e65d52310067d65d523108cff769523101cfe7695231004fd769523101cfc769523103e7e65952310067d65952310073f5495231004ff765523101cfe7655231004fd765523101cfc765523103e7e65552310067d655523108cff761523101cfe7615231004fd761523101cfc761523103e7e65152310067d6515231015de7315231005dd731523103cfe7598231004fd759823108cfe7498231004fd7498231004ff729823100cfe7298231004fd729823100cfc729823101cfe719823101ef6719823101cf6719823101efa7098231056f93098231006fa2098231006f9209823101ef7109823101efb109823101ef81098231004ff755823103cfc7558231004ff745823108cfc7458231004ff725823100cfe7258231004fd725823100cfc725823101cfc715823101efb705823104efa305823104edc3058231006fa2058231006f9205823101efb105823101ef8105823103cfe76d953108cfe74d9531004fd74d953101cff73d953101cfd73d953117e7f53d953117e7d53d9531004ff72d953100cfe72d9531004fd72d953100cfc72d953117edf32d9531006dd32d9531004fe70d9531004fd70d95310067f659953116df5719953118df771595310067f7559531004ff745953108cfc745953116cff7359531006df735953116e7e535953116e7c5359531004ff725953100cfe7259531004fd725953100cfc72595310067f52595310067d525953116edf3259531006dd325953118cff7159531006f7715953129e7e515
  | 33 => 0xe70d0c4111f9c30d0c4114cff7650c4128dbf7650c4114ebf7650c4136ebe6550c4128ebc6550c4108dbf7350c4108f9f7350c41016be6350c41016bc6350c4128ebf6250c4147ebd6250c4111f9f3250c4147f9d3250c4128dbf7150c4128ebe6150c4128fb66150c4147fb72150c4128fb42150c41005bc7050c4101df77650441006f77650441004f7765044101df7745044101fb7745044108ef6645044101fb6645044108fb65450441007b55450441115f67250441115f47250441477b6425044108fb4425044103cfe7598041004fd7598041014fe7398041004fd7398041014fc7398041004ff729804100cfe7298041004fd729804100cfc729804101efa709804108efb409804108ef84098041006fa2098041006f9209804101efb109804101ef81098041004ff75580410067f75580410047f755804103cfc75580410067c755804103c7c7558041004ff7358041006df7358041004df7358041014fe7358041014fc7358041006dc7358041014dc7358041006bf4358041006bd4358041004ff725804100cfe7258041004fd725804100cfc725804101efb705804108efb405804108ef84058041006fa2058041006f9205804101efb105804101ef8105804103e7f749963103e7e749963103e7d749963103e7c749963103e7f739963103e7e739963103e7d739963103e7c739963118e7f439963118e7e439963118e7d439963118e7c439963103e7f729963103e7e729963103e7d729963103e7c72996310067f42996310067e42996310067d42996310067c429963118e7f329963118e7e329963118e7d329963118e7c329963101e7f719963101e7e719963101e7d719963101e7c719963101e7f419963101e7e419963101e7d419963101e7c419963101e7f319963101e7e319963101e7d319963101e7c319963101e7f219963101e7e219963101e7d219963101e7c219963103e7f709963103e7e709963103e7d709963103e7c709963118e7f309963118e7e309963118e7d309963118e7c309963118e5c30996310067f20996310067e20996310067d20996310067c209963101e7f109963101e7e109963101e7d109963101e7c109963101e7f7559631004ff745963108cfc745963116e7f535963116e7d5359631004ff725963100cfe7259631004fd725963100cfc72596310067f52596310067e52596310067d52596310067c525963101cfe715963101cfc715963101e7e515963101e7c5159631004ff7059631004fc705963101ef710596310067f74596310067e74596310067d74596310067c745963116e7f735963116e7e735963116e7d735963116e7c735963116e7f435963116e7e435963116e7d435963116e7c43596310067f72596310067e72596310067d72596310067c72596310067f42596310067e4259631
  | 34 => 0x514103e7e65151410067d6515141014fe76d8d41136de63d8d4103cfe75d8d41004fd75d8d4101cfd74d8d41136de43d8d41004ff72d8d4100cfe72d8d41004fd72d8d4100cfc72d8d41006bf42d8d41006bd42d8d41296be41d8d41296bc41d8d41136df31d8d41004fe70d8d41004fd70d8d41136dc30d8d41136dc6358d41004fe76d4d41004fd76d4d4103cfc76d4d410067f65d4d4103e7c65d4d411375e53d4d41004ff7654d41004fe7654d41004fc7654d410067f6554d4103e7c6554d41144fe76d0d4101cfc7650d41006df6350d41016dc6350d411379c4350d41005f77150d4101df47150d41004fe76d454108cfc76d45410067f65d454103e7c65d4541005be74d4541005bd74d454101f7651d454103cff7654541004fd765454103cfc76545410067f655454103e7c6554541005bf7454541005bc745454101fb4415454101dbe74d054101ebf64d054101df674d054101ef764d054101fb764d0541126f662d0541126f462d054108fb742d054148fb542d054103cfe75d8141004fd75d8141014fe73d8141004fd73d8141014fc73d8141004ff72d814100cfe72d8141004fd72d814100cfc72d8141006fb60981410057f75581410057c7558141005df7358141135dc7358141005ef725814112dec7258141006f9601814103cfe7518141004fd7518141014fe7318141004fd7318141014fc7318141004ff721814100cfe7218141004fd721814100cfc7218141006bf4218141006bd4218141256be4118141256bc411814101cff755944101e7f755944108cfe745944108cfc745944108e7e545944108e7c5459441004ff7359441014fe7359441014fc73594410067e53594410067c5359441004ff725944100cfe7259441004fd725944100cfc72594410067f52594410067d525944101cfe715944101cfc715944101e7e515944101e7c5159441004ff7059441004fc7059441004fd76d504108f3e54d5041004ff765504108f3c5455041004ff7558c4103cfc7558c4101edf7358c4111edc5358c4108edf4358c4108edc4358c41004ff7258c4100cfe7258c41004fd7258c4100cfc7258c4111edf3258c41006dd3258c4101cfc7158c4101ede3158c4101edc3158c41004ff7058c41004fc7058c4111edf3058c4103cff76d4c4101cfe76d4c41004fd76d4c412a67f65d4c4103e7c65d4c41016de63d4c41006dd63d4c4111f5e53d4c41004ff7654c41004fd7654c4101cfc7654c4129e7f6554c4103e7c6554c4108dbd76d0c41016bd76d0c41014bd76d0c4137ebe65d0c4108ebc65d0c4128dbd73d0c41016be63d0c4108f9e63d0c4108f9d63d0c41016bc63d0c4108ebf62d0c41486bd62d0c4108fb671d0c41295bd71d0c4108fb571d0c41296be61d0c4108fb661d0c41487b721d0c41297b421d0c41005b
  | 35 => 0x146de4358e41004ff7258e4100cfe7258e41004fd7258e4100cfc7258e41146df3258e41006dd3258e4101cfc7158e4101ede3158e4101edc3158e41004ff7058e41004fc7058e41146dc3058e4103cff76d4e4101cfe76d4e41004fd76d4e4103e7e65d4e410067d65d4e411475e53d4e41004ff7654e41004fd7654e4101cfc7654e4103e7e6554e410067d6554e41134fd76d0e410067e65d0e410067d65d0e41295bd76d0e41136bd76d0e4137ebe65d0e412973e65d0e410063e65d0e412973d65d0e41296bc65d0e41016be63d0e41016bc63d0e41296bf62d0e4149ebd62d0e41295bd71d0e41005be70d0e411479c30d0e41014ff7650e410067e6550e410067d6550e41016de6350e41006dd6350e41005f77150e4101df47150e4128dbf7650e41016bf7650e41014bf7650e4136ebe6550e4128f3e6550e410063e6550e4128f3d6550e4128ebc6550e410079f7350e41016be6350e4128f9e6350e410169e6350e4128f9d6350e41016bc6350e4128ebf6250e41496bd6250e411479f3250e414979d3250e4128dbf7150e41007b77150e4128fb47150e41005bc7050e4101df576d064108ef576d064101f7665d064101f7565d064101fb674d064108fb654d0641007b554d0641126f662d064101ef462d064103cfe7598241004fd7598241014fe7398241004fd7398241014fc7398241004ff729824100cfe7298241004fd729824100cfc729824101efa7098241006fb3098241006f83098241006fa2098241006f9209824101efb109824101ef81098241004ff755824103cfc7558241004ff7358241014fe7358241014fc7358241006bf4358241006bd4358241004ff725824100cfe7258241004fd725824100cfc725824101efb7058241006fb3058241006f83058241006fa2058241006f9205824101efb105824101ef8105824103cfe76d9541014fe73d9541004fd73d9541014fc73d9541004ff72d954100cfe72d9541004fd72d954100cfc72d95410067e52d95410067c52d9541006bf42d9541006bd42d9541004fe70d9541004fd70d95410067f6599541005ef725954112dec72595410067f7559541004ff7459541006bf7459541004ff7359541014fe7359541014fc7359541004ff7259541006ef7259541004ef725954100cfe7259541004fd725954100cfc7259541006ec725954100cec72595410067f52595410067d5259541006bf4259541006bd4259541004ff7159541006f77159541004ff7059541004fc7059541004fe761954103e7e65195410067d651954101cfe76d514101cfc76d51410067f65d514103e7c65d514101df671d5141005f571d5141004fe769514103e7e65951410067d65951410073f549514101cfc76551410067f655514103e7c6555141005f7715514101df47155141004fe761
  | 36 => 0xd6554741005bf745474108dbc745474101fb6415474108efb609834103cfe7598341004fd759834101cfe7498341014fe7398341004fd7398341014fc7398341004ff729834100cfe7298341004fd729834100cfc7298341006bf4298341006bd429834125ebe419834125ebc419834108efb409834108ef8409834108ef86058341004ff755834103cfc755834101cfc7458341004ff7358341014fe7358341014fc7358341004ff725834100cfe7258341004fd725834100cfc725834108efb405834108ef8405834103e7f749964103e7d749964103e7f739964103e7e739964103e7d739964103e7c73996410067e43996410067c439964103e7f729964103e7e729964103e7d729964103e7c72996410067f42996410067e42996410067d42996410067c42996410067f32996410067e32996410067d32996410067c329964101e7f719964101e7e719964101e7d719964101e7c719964101e7f419964101e7e419964101e7d419964101e7c419964101e7f319964101e7e319964101e7d319964101e7c319964101e7f219964101e7e219964101e7d219964101e7c219964103e7f709964103e7e709964103e7d709964103e7c70996410067f30996410067c30996410067f20996410067e20996410067d20996410067c209964101e7f109964101e7e109964101e7d109964101e7c109964101e7f7559641004ff7359641014fe7359641014fc73596410067e53596410067c5359641004ff725964100cfe7259641004fd725964100cfc72596410067f52596410067e52596410067d52596410067c525964101cfc715964101e7e515964101e7c5159641004ff7059641004fc70596410067f74596410067d74596410067f73596410067e73596410067d73596410067c73596410067e43596410067c43596410067f72596410067e72596410067d72596410067c72596410067f42596410067e42596410067d42596410067c42596410067f32596410067e32596410067d32596410067c325964101e7f715964101e7e715964101e7d715964101e7c715964101e7f415964101e7e415964101e7d415964101e7c415964101e7f315964101e7e315964101e7d315964101e7c315964101e7f215964101e7e215964101e7d215964101e7c21596410067f70596410067e70596410067d70596410067c70596410067f30596410067c30596410067f20596410067e20596410067d20596410067c205964101e7f105964101e7e105964101e7d105964101e7c105964103e7e65d52410067d65d524101df671d5241005f571d524103e7e65952410067d65952410073f549524103cff765524103e7e65552410067d6555241005f7715524101df4715524103e7e65152410067d65152410073d5415241004ff7558e4103cfc7558e4101edf7358e41
  | 37 => 0x905101ebe415905101ebc4159051004ff7059051004fc7059051004ff7458c5108cfc7458c5101cff7358c5101edf7358c5103edf5358c5103edc5358c51004ff7258c5100cfe7258c51004fd7258c5100cfc7258c5115edf3258c51006dd3258c5101cfc7158c5101ede3158c5101edc3158c51004ff7058c51004fc7058c5103d7f7654c5118e7f7654c5118c7f7654c510067e6454c5103d7f7354c5103f5f7354c510167e6354c510167c6354c5103e7f6254c514a67d6254c5115f5f3254c514a75d3254c5129d7f7154c5129e7e6154c5103f766154c510057c7054c5108cff76d0c5101cfe76d0c51004fd76d0c51004ff7650c51004fd7650c5101cfc7650c5108cfe7498051004fd7498051014fe7398051004fd7398051014fc7398051004ff729805100cfe7298051004fd729805100cfc729805101efa709805103efb509805103ef85098051006fa2098051006f9209805101efb109805101ef81098051004ff7458051006bf7458051004bf745805108cfc7458051006bc7458051004bc7458051004ff7358051006df7358051004df7358051014fe7358051014fc7358051006dc7358051014dc735805103e7f53580510067d5358051004ff725805100cfe7258051004fd725805100cfc725805101e7f515805101ef6515805101e7d515805103ef5515805101efb705805103efb505805103e7c505805103ef85058051006fa2058051006f9205805101efb105805101ef8105805108ebe74d9741014fe73d9741004fd73d9741014fc73d974108cff72d974100cfe72d9741004fd72d974100cfc72d974108ebf42d9741006bd42d974108ef571d9741004fe70d9741004fd70d9741004fd769974108e7f659974108e7c659974103cff765974108e7c655974108e7f755974101cfc745974108e7e545974108e7c5459741004ff7359741014fe7359741014fc7359741004ff725974100cfe7259741004fd725974100cfc72597410067f52597410067d5259741006bf4259741006bd4259741004ff7059741004fc705974108f3e54d5341014ff7658f4108edc6358f41004ff7558f4103cfc7558f4101cfc7458f4114ede5358f4108edf4358f4108edc4358f41004ff7258f4100cfe7258f41004fd7258f4100cfc7258f41006bf4258f41006bd4258f4114edf3258f41006dd3258f4128ebe4158f4128ebc4158f4114edf3158f41004ff7058f41004fc7058f4114edc3058f4103cff76d4f4108cfe76d4f41004fd76d4f4103e7e65d4f410067d65d4f4114f5e53d4f41004ff7654f41004fd7654f4108cfc7654f4103e7e6554f410067d6554f41016de6354f41006dd6354f4111cff7650f4108f9c4350f4103e7e65d47410067d65d474108dbe74d4741005bd74d474101f7651d474103cff765474103e7e65547410067
  | 38 => 0x4fd721915100cfc7219151006be421915108ebc4219151004fe7019151004fd701915101cfe7695151006bf649515108ebc649515103f3f549515101df67195151005f5719515101c7e769515103d7e74951510067f64951510073f64951510063f64951510073c649515116d7e739515116d7c73951514b57f72951514b57d72951511c67e62951511c67c62951514bf3f42951514bf3d429515101d7e719515100776719515100775719515101d7c719515103e7f619515103f7761951510057d709515101cfc7655151006bf6455151006bc6455151005f7715515101df471551510057e761515103e7e76151514b57e741515103f3e74151510067f641515116d7e731515103d7c731515103d7f72151514ad7d72151511b67e62151511b67c621515101d7e711515101d7c711515103e7f611515103f7761151510057d7015151014fe76d8d5103d7e75d8d5116ede63d8d5116f5e53d8d5101cfd75d8d5101c7d75d8d5108cfe74d8d51004fd74d8d510067e54d8d510067c54d8d5116e7e53d8d5116ede53d8d5116e5e53d8d5116e7c53d8d51004ff72d8d5100cfe72d8d51004fd72d8d5100cfc72d8d510067f52d8d510067d52d8d5103cfd71d8d512a67e51d8d512a67c51d8d5116edf31d8d51004fe70d8d51004fd70d8d5116edc30d8d5116edc6358d5101cfc7654d5116d7f7554d51006df6354d51016dc6354d51005f77154d5101df47154d51004fe76d0d51004fd76d0d5108cfc76d0d5103d7e75d0d510057d75d0d51006bf64d0d5108ebc64d0d510073c54d0d51004ff7650d51004fe7650d51004fc7650d510057f7550d5103d7c7550d51006bf6450d51006bc6450d510073c5450d5108cfe74d8151004fd74d8151014fe73d8151004fd73d8151014fc73d8151004ff72d815100cfe72d8151004fd72d815100cfc72d8151006fb6098151005bf7458151005bc7458151005df735815116ddc7358151005ef7258151165ec7258151006f9601815108cfe7418151004fd74181510067e54181510067c5418151014fe7318151004fd7318151014fc73181510067e53181510067c5318151004ff721815100cfe7218151004fd721815100cfc72181510067f52181510067d52181512667e51181512667c511815101cfe749905101ebe749905103ebf549905108ebc5499051014fe7399051004fd7399051014fc739905103e7f539905108cff729905100cfe7299051004fd729905100cfc729905108ebf4299051006bd429905101e7f519905101e7d519905101ebe419905101ebc4199051004fe7099051004fd709905103e7c509905101ebf745905103ebf545905103ebc5459051004ff7359051014fe7359051014fc7359051004ff725905100cfe7259051004fd725905100cfc7259051006bf4259051006bd425
  | 39 => 0xf3258e51006dd3258e5101cfc7158e5101ede3158e5101edc3158e51004ff7058e51004fc7058e5117edc3058e5101ef71058e512a57d76d4e5103e7d76d4e5116c7d76d4e510067e64d4e510167e63d4e510167c63d4e512a67f62d4e514de7d62d4e5103d7f71d4e512a57d71d4e5103f7661d4e510057e70d4e5117f5c30d4e51014ff7654e51016de6354e51006dd6354e51005f77154e5101df47154e5103f775154e5129d7f7654e510167f7654e510147f7654e510067e6454e5103d7f7354e5103f5f7354e510167e6354e5129f5e6354e5129f5d6354e510167c6354e5129e7f6254e514d67d6254e5117f5f3254e514d75d3254e5129d7f7154e51007777154e51005777154e5129f747154e5103e7e6154e510057c7054e5108cff76d0e5101cfe76d0e51004fd76d0e5108ebe64d0e51006bd64d0e51004ff7650e51004fd7650e5101cfc7650e51006be6450e51006bd6450e51016de6350e51006dd6350e5101f7576d465101d7576d465103e7576d465103f7774d465103f7674d465103f7574d465103f7474d465101f7764d465101f7664d465101f7564d465101f7464d465103f7773d465103f7673d465103f7573d465103f7473d465101f7763d465101f7663d465101f7563d465101f7463d46510077743d46514cf7643d46510077543d46514cf7443d465103f7772d465103f7672d465103f7572d465103f7472d465101f7762d465101f7662d465101f7562d465101f7462d46514c77742d46514c77642d46514c77542d46514c77442d46514c77732d46514c77632d46514c77532d46514c77432d465103f7770d465103f7670d465103f7570d465103f7470d465101f7760d465101f7660d465101f7560d465101f7460d46514cf7730d46514cf7430d46514c77720d46514c77620d46514c77520d46514c77420d465108cfe7498251004fd7498251014fe7398251004fd7398251014fc7398251004ff729825100cfe7298251004fd729825100cfc729825101cfe719825101cf6719825101efa7098251006fa2098251006f9209825101ef7109825101efb109825101ef81098251004ff745825108cfc7458251004ff7358251014fe7358251014fc73582510067f53582510067d5358251004ff725825100cfe7258251004fd725825100cfc725825101cfc715825101e7f515825101e7d515825101efb7058251006fa2058251006f9205825101efb105825101ef81058251014fe73d9151004fd73d9151014fc73d9151004ff72d915100cfe72d9151004fd72d915100cfc72d91510067f52d91510067d52d9151006be42d9151006bc42d9151004fe70d9151004fd70d9151006bf6499151005ef7259151165ec7259151006bd6419151014fe7319151004fd7319151014fc731915108cff721915100cfe7219151
  | 40 => 0x935101c7c755935103ebf745935103ebf545935103e7c545935103ebc545935103e3c5459351004ff7359351014fe7359351014fc7359351004ff725935100cfe7259351004fd725935100cfc725935103e7f52593510067d5259351006bf4259351006bd4259351004ff7059351004fc705935103d7d76953510067d769535103f3e74953510067d649535118d7e739535118d7c73953514ed7f72953514ed7d72953511c67e629535103e7c62953514e73f42953514e73d429535101d7e719535101d7c71953510057d709535101cfc7558f5101c7c7558f51004ff7458f5108cfc7458f510067e5458f5103e7c5458f5103edf7358f5103edf5358f5118e7e5358f5103e7c5358f5103edc5358f5118ede4358f51004ff7258f5100cfe7258f51004fd7258f5100cfc7258f5103e7f5258f510067d5258f5118edf3258f51006dd3258f5129e7e5158f5103e7c5158f5118edf3158f51004ff7058f51004fc7058f5103e7f5058f5118edc3058f5108cff76d0f5103cfe76d0f51004fd76d0f5103d7e75d0f510057d75d0f5108ebe64d0f51006bd64d0f5137f3c54d0f51004ff7650f51004fd7650f5103cfc7650f510057f7550f5103d7c7550f51006be6450f51006bd6450f5136f3c5450f51016de6350f51006dd6350f5101cfe759835101c7e759835108cfe7498351004fd74983510067e549835103e7c5498351014fe7398351004fd7398351014fc73983510067e539835103e7c5398351004ff729835100cfe7298351004fd729835100cfc729835103e7f52983510067d529835126e7e519835103e7c519835103efa709835103e7f509835103efb509835103ef8509835101cfc7558351004ff745835108cfc7458351004ff7358351014fe7358351014fc7358351004ff725835100cfe7258351004fd725835100cfc725835103ef6515835103ef5515835103efb705835103efb505835103ef8505835101ebe7499251014fe7399251004fd7399251014fc739925108cff729925100cfe7299251004fd729925100cfc729925108ebf4299251006bd429925101cfe719925101e7f519925101e7d519925101ebe419925101ebc4199251004fe7099251004fd709925101ebf7459251004ff7359251014fe7359251014fc7359251004ff725925100cfe7259251004fd725925100cfc7259251006bf4259251006bd425925101cfc715925101ebe415925101ebc4159251004ff7059251004fc705925108ebe6495251006bd649525103f3f549525101df67195251005f5719525103f775195251006be6455251006bd645525103f3c5455251005f7715525101df4715525103f775155251004ff7458e5108cfc7458e5101edf7358e5117ede5358e5117ede4358e51004ff7258e5100cfe7258e51004fd7258e5100cfc7258e5117ed
  | 41 => 0x67f52595430067d5259543006bf4259543006bd42595431d6df3259543006dd3259543004ff715954301cfc7159543004ff7059543006fb7059543004fb7059543004fc7059543006f87059543004f870595431dcfe761954303e7e65195430067d6519543014fe76d5143014fc76d51430067f65d514303e7c65d5143015de73d5143005dd73d5143015be76d51431eebe76d5143014be76d514336ebf65d51430073f65d51430063f65d514336ebd65d514336f3c65d5143015be73d51431ef9e73d51430159e73d514336f9d73d5143015bc73d51431eebf63d514336dbf72d514351dbd72d514336f3f52d51435173d52d51431ef9f32d51435179d32d514328dbe71d5143005bd70d51431bcfe769514303e7e65951430067d65951431bdbe74951430073f549514308f9c439514303cff7655143014fe76551431d4fd7655143014fc76551430067f655514303e7c6555143005df7355143015dc73551431d79c43551431dcfe761514303e7e65151430067d65151430073d54151431ddbe761514336ebe76151431edbe751514336f3e751514336ebf651514336f3e651514336ebd65151430073d6515143015be7315143015bc731514308ebf63151431bf3f53151431bf3d531514336dbf721514350dbd72151435073e521514336f3c52151431bf9f32151435079d321514328dbe7115143005bd7015143015de74d0d430179e74d0d43016df64d0d430179f64d0d430079f54d0d4308f9c54d0d4308ddf72d0d434fddd72d0d4308f9f42d0d434f79d42d0d4303cfe75d8543004fd75d854314ebd74d8543004ff72d854300cfe72d8543004fd72d854300cfc72d8543006bf42d8543006bd42d854314edf32d8543006dd32d854314ef631d8543006f721d8543006f421d8543004fe70d8543004fd70d85430057e75985430057d7598543006f76198543005fa7098543005f9709854301ef66118543006f5611854303cfe75d8143004fd75d8143004ff72d814300cfe72d8143004fd72d814300cfc72d814301cfe71d8143004fd71d81430befa30d8143006fb20d8143006f820d8143006fb60981430057f75581430057c7558143006f9601814303cfe7518143004fd7518143086bd7418143006bf5418143006bc5418143006df4318143086be4318143086bc4318143086dc4318143004ff721814300cfe7218143004fd721814300cfc7218143006bf4218143006bd4218143086df3218143006dd321814301cfe7118143004fd7118143086f93018143006fb2018143006f8201814301cfe759935108ebe749935103ebf549935108ebc5499351014fe7399351004fd7399351014fc739935108cff729935100cfe7299351004fd729935100cfc729935108ebf4299351006bd4299351004fe7099351004fd709935101cfc755
  | 42 => 0xe7118153006f6711815301cf67118153004fd7118153006f57118153004f571181530cef9301815308cfe74d974308ebe74d974308edd73d974308cff72d974300cfe72d9743004fd72d974300cfc72d974308ebf42d9743006bd42d974301cfe71d9743004fd71d9743004fe70d9743004fd70d97431d4fd769974308e7f659974308e7c659974303cff765974308e7c655974308e7f7559743014fe7459743014fc74597431d6bc745974308e7e545974308e7c54597431d67f53597431d67d5359743004ff725974300cfe7259743004fd725974300cfc72597430067f52597430067d5259743006bf4259743006bd4259743004ff715974301cfc7159743004ff7059743004fc70597431d4fd76d534308f3e54d53431d5bd76d534337ebd76d534337ebf65d534337ebd65d5343015be73d5343015bc73d534337dbf72d534353dbd72d534337f3f52d53435373d52d5343295be71d5343005bd70d53431ef9c30d53431ecff765534308f3c54553431d79e4355343015bd761534308ebd7615343014bd761534308f3e751534308ebf651534308f3e651534337ebd651534308f3d6515343015be731534308f9e73153430159e731534308f9d7315343015bc73153431bf3f53153431bf3d531534308dbf721534352dbd72153435273e521534337f3c5215343295be7115343005bd70153431bf9c301534308ef7619874301ef4619874308ef46158743004ff755874303cfc7558743014fc7458743136bc7458743004ff725874300cfe7258743004fd725874300cfc7258743006bf4258743006bd425874308ef7415874308ef44158743136f63158743004ff7058743004fc705874308efb609834303cfe7598343004fd7598343014fe74983430b6be7498343006bf5498343006bc54983430b6be43983430b6bc4398343004ff729834300cfe7298343004fd729834300cfc7298343006bf4298343006bd429834301cfe7198343004fd719834308efb409834308ef840983430b6f9309834308ef86058343004ff755834303cfc7558343014fc7458343004ff725834300cfe7258343004fd725834300cfc7258343004ff715834301cfc715834308efb405834308ef840583430aefa30583430aedc305834303cfe76d95431debd74d954308cff73d95431dcfd73d95431de7f53d95431de7d53d9543004ff72d954300cfe72d9543004fd72d954300cfc72d95430067e52d95430067c52d9543006bf42d9543006bd42d95431dedf32d9543006dd32d954301cfe71d9543004fd71d9543004fe70d9543004fd70d95430067f65995431d5bd74995431edbf7459543005fb7059543005f870595430067f75595431ecff7459543006bf74595431d4ff7359543006df7359543004ff725954300cfe7259543004fd725954300cfc7259543
  | 43 => 0x8353004fd729835300cfc729835303e7f52983530067d529835301cfe7198353004fd719835303e7c519835303efa709835303e7f509835303efb509835303ef850983530eef93098353014fc7558353004ff745835308cfc7458353004ff725835300cfe7258353004fd725835300cfc7258353004ff715835301cfc715835303efb705835303efb505835303ef850583530e6fa30583530e6dc30583531ee7d75d915303cfd73d91531eebf43d9153004ff72d915300cfe72d9153004fd72d915300cfc72d91530067f52d91530067d52d91531eedf32d9153006dd32d915301cfe71d9153004fd71d9153004fe70d9153004fd70d9153006bf6499153005fb7059153005f87059153006bd641915308cff731915303cfd731915308ebf43191531bebd431915308cff721915300cfe7219153004fd721915300cfc721915301cfe7119153004fd7119153004fe7019153004fd7019153014fe7695153006bf649515308ebc649515303f3f5495153015de7395153005dd73951530157e76951531de7e76951530147e769515303d7e74951530067f64951530073f64951530063f64951530073c64951530157e73951531df5e73951530155e73951530075d73951530157c739515303e7f639515303f5f639515355d7f729515355d7d72951531c67e62951531c67c62951535573f42951535573d42951531df5f32951535575d329515329d7e71951530057d7095153014fc7655153006bf6455153006bc645515303f3c5455153005df7355153015dc735515303f5c53551531ed7e761515303e7e76151531dd7e741515303f3e74151530067f64151530073e64151530073d64151530157e73151530157c731515303e7f631515303f5f631515303d7f721515354d7d72151531b67e62151531b67c62151531bf5f32151535475d321515329d7e71151530057d701515318e7d75d855308cfe74d8553004fd74d85530067e54d85530067c54d855303cfd73d855318e7e53d855318e7c53d8553004ff72d855300cfe72d8553004fd72d855300cfc72d85530067f52d85530067d52d855318edf32d8553006dd32d855318ef631d8553004fe70d8553004fd70d8553006f7619855301ef66118553006f5611855308cfe74d8153004fd74d815303cfd73d8153004ff72d815300cfe72d8153004fd72d815300cfc72d815301cfe71d8153004fd71d81530fefa30d8153006fb6098153005bf7458153005bc7458153005f67118153005f57118153006f960181530ce7d751815308cfe7418153004fd74181530067e54181530067c541815303cfd731815342edf53181530ce7e53181530ce7c53181530cedc5318153004ff721815300cfe7218153004fd721815300cfc72181530067f52181530067d52181530cedf3218153006dd321815301cf
  | 44 => 0x8d7f76550540067f76550540047f765505408d7f745505403f3f745505408e7e645505408f3e64550540057f73550541b57e72550541b57c725505408e7f62550545767d625505408f3f42550545773d42550540057f71550540057c705505408edf7358c5403edf5358c5403edc5358c5408edf4358c5408edc4358c54004ff7258c5400cfe7258c54004fd7258c5400cfc7258c541bedf3258c54006dd3258c54004ff7158c5401cfc7158c541bedc3158c54004ff7058c54004fc7058c541bedf3058c54004ff7358454014fe7358454014fc7358454004ff725845400cfe7258454004fd725845400cfc725845408ef7715845403ef7515845403ef4515845408ef7415845408ef44158454004ff7058454004fc7058454014fe7398054004fd7398054014fc7398054004ff729805400cfe7298054004fd729805400cfc729805401cfe7198054004fd719805408efa709805403efb509805403ef8509805408efb409805408ef84098054004ff7358054006df7358054004df7358054014fe7358054014fc7358054006dc7358054014dc735805403e7f5358054004ff725805400cfe7258054004fd725805400cfc7258054004ff715805401cfc715805403e7f515805408efb705805403efb505805403e7c505805403ef8505805408efb405805408ef84058054014fe7599353014fc759935308ebe749935303ebf549935308ebc549935308ebf43993531debd439935308cff729935300cfe7299353004fd729935300cfc729935308ebf4299353006bd429935301cfe7199353004fd7199353004fe7099353004fd70993531dedc3099353014fc755935303e7c75593530147c755935303ebf745935303ebf545935303e7c545935303ebc54593531d6bf4359353004ff725935300cfe7259353004fd725935300cfc725935303e7f52593530067d5259353006bf4259353006bd4259353004ff715935301cfc7159353004ff7059353004fc705935303d7d76953530067d769535303f3e74953530067d64953530157e73953530157c739535356d7f729535356d7d72953531c67e629535303e7c62953535673f42953535673d42953532a57e71953530057d70953531df5c3095353014fc755875303e7c75587530147c7558753004ff745875308cfc74587530067e545875303e7c545875316e7e535875303e7c5358753004ff725875300cfe7258753004fd725875300cfc725875303e7f52587530067d525875303ef7715875303ef7515875303e7c515875303ef4515875316ef63158753006f72158753006f42158753004ff7058753004fc705875303e7f5058753014fe759835303e7e75983530147e759835308cfe7498353004fd74983530067e549835303e7c54983530ee7e539835303e7c5398353004ff729835300cfe729
  | 45 => 0xc60d52545973f30d52545973c30d525458f3f20d525458f3e20d525458f3d20d525458f3c20d5254014ff7658e540073f5458e5408edc6358e5408cfc7458e5436ebf5458e5436ebc5458e541dede5358e5408edf4358e5408edc4358e54004ff7258e5400cfe7258e54004fd7258e5400cfc7258e54006bf4258e54006bd4258e541dedf3258e54006dd3258e54004ff7158e5401cfc7158e541dedf3158e54004ff7058e54004fc7058e541dedc3058e540073f549865408ef7619865401ef461986540073f545865408ef4615865408cfc7458654004ff7358654014fe7358654014fc7358654004ff725865400cfe7258654004fd725865400cfc7258654006bf4258654006bd425865408ef7415865408ef44158654004ff7058654004fc70586540073f549825408efb609825408cfe7498254336bf5498254336bc5498254014fe7398254004fd7398254014fc7398254004ff729825400cfe7298254004fd729825400cfc7298254006bf4298254006bd429825401cfe7198254004fd719825408efb409825408ef840982540073f545825408ef8605825408cfc7458254004ff7358254014fe7358254014fc7358254004ff725825400cfe7258254004fd725825400cfc7258254004ff715825401cfc715825408efb405825408ef8405825403dbe749515403ebf649515408d7e749515408e7f649515403f3f649515403e3f649515408d7f72951545857d72951541c67e62951541c67c629515408f3f429515457f3d4295154014fe76d8d541d6de63d8d5403cfd74d8d5437ebf54d8d540067e54d8d5437ebc54d8d541d6de53d8d541d6de43d8d54004ff72d8d5400cfe72d8d54004fd72d8d5400cfc72d8d540067f52d8d540067d52d8d54006bf42d8d54006bd42d8d5401cfe71d8d54004fd71d8d54004fe70d8d54004fd70d8d541d6dc30d8d541d6dc6358d54005fb7058d54005f87058d540067e54d8554014fe73d8554004fd73d8554014fc73d8554004ff72d855400cfe72d8554004fd72d855400cfc72d85540067f52d85540067d52d8554006bf42d8554006bd42d8554006f721d8554006f421d8554004fe70d8554004fd70d8554006f76198554005ef72585541cdec725855401ef66118554006f56118554014fe73d8154004fd73d8154014fc73d8154004ff72d815400cfe72d8154004fd72d815400cfc72d815401cfe71d8154004fd71d8154006fb30d8154006f830d8154006fb6098154005df73581541d5dc7358154006f960181542f6bf54181540067e54181542f6bc5418154014fe7318154004fd7318154014fc7318154004ff721815400cfe7218154004fd721815400cfc72181540067f52181540067d5218154006bf4218154006bd421815401cfe7118154004fd7118154006fb3018154006f83018154
  | 46 => 0x1b01300040000007003000c004c000000c018000400200000000000003001c00000100060164000001800b000800500200000024002001c00300080030010003005c00b00000000008003000401f00380080000006000400400080000018011000000600140010000028001800f0008000000000d000000a001003e0068001001c003000c00100b800700000000000002000400700100040008003000c00e005c00b014c0160004056000c000001c0020014011000000401100010020003004001c000001e00000060048019000000000840060000004002c016002402800600020008002000404200100400000011002000400200010018000000000200cc0120018014000c002001c00c002401700000050010000005c00a001400f0000003009400400040120000004001400900180000000009000c0000018009004003f03e7c5458f5403edf7358f5403edf5358f5403edc5358f541eede4358f54004ff7258f5400cfe7258f54004fd7258f5400cfc7258f5403e7f5258f540067d5258f541eedf3258f54006dd3258f54004ff7158f5401cfc7158f54004ff7058f54004fc7058f541eedc3058f5403e7c5458754004ff7358754014fe7358754014fc7358754004ff725875400cfe7258754004fd725875400cfc725875403e7f52587540067d525875403ef7715875403ef7515875403ef45158754006f72158754006f42158754004ff7058754004fc705875403e7c5498354014fe7398354004fd7398354014fc7398354004ff729835400cfe7298354004fd729835400cfc729835403e7f52983540067d529835401cfe7198354004fd719835403efa709835403efb509835403ef85098354004ff7358354014fe7358354014fc7358354004ff725835400cfe7258354004fd725835400cfc7258354004ff715835401cfc715835403efb705835403efb505835403ef8505835408d7d76d525403e7d76d525408f3e64d52540057d73d52545973e43d525408f3c43d52541c57e72d525403d7c72d525408e7f62d525458e7d62d525408f3f42d525458f3e42d525458f3d42d525408f3c42d52540057d71d52540057e70d525403f3d76d52540053d76d525403e3d76d525403f3f73d525403f3e73d525403f3d73d525403f3c73d525408f3f63d52545973e63d525408f3c63d525403f3f72d525403f3e72d525403f3d72d525403f3c72d525408f3f62d525458f3e62d525458f3d62d525408f3c62d525458f3f32d525458f3e32d525458f3d32d525458f3c32d525403f3f71d525403f3e71d525403f3d71d525403f3c71d525408f3f61d525408f3c61d52545973f31d52545973c31d525458f3f21d525458f3e21d525458f3d21d525458f3c21d525403f3f70d525403f3e70d525403f3d70d525403f3c70d525408f3f60d525408f3
  | 47 => 0x1801b00080000050001007003500000000098009007c0020018004000000a00000030038003002c00a0000001001000200000030008043005c01801f80010004001000002c000400500b40070030001002400001b00000090014000c00800380010000003000c001001c0190000001000402500000080000000014000800000040004000000800a000000600440000008001001000e00000050090004000c000000000a003c00400200000018000001c00000e8000000400a004800d0040004002800000180120048001000401300a8000001801b002c002000c006000000300140040008001002c01100000000044025001c00000500000020001000400000200000014001001000b000001f007801a0000013000402b000003000000080000000002c003019c000000000d0000000002000700000000004000001c0070040004003400c00040040070000000003f0018002004000b00000000004001000c003002000900000000008004001c03600500030000010003003d00100070004000002402c00100200000016001c00000100080008001004000900040000010014000c0010010000002400000040060000004000801c00440010018025003400a0008001005803200340000004004004000400f4001000c0020008002024c00f00100000010003006c000000c00000500030024002006405800000010024008002c002000800600840000018003000c004001c005000c0200068002003800200000070000003000000b004000c000000100280220000006000003300780020008013000000400000000000004000c004000400600f800900c0002000800100000000000005001401c00a80010018003001800000280000054000000801f0074005002c0060004002000c00b002803f0008010000c0080000001002c0140074006003c000000001a0000001001400e000401800b80120004006000000000140000008013000401800d80060014002002400d004801e002400a000001b000c0080020000001000200000050014009001800001000040008008001001e0048013001400700280000044001001400600440020010004000000000200320004001002c002001c00400640000000002000400000000000020000000c00600000060034007000c002006400e005800000d001e0008002000000500240030050006002800b000800c0000004000000f0088001004400000540090054006004c025008c00000080040060002001800b0008000003c02c0018003004400000940000004010001800f00180020000003001001800e00170000008000800401340020000020009c00200540020008000000000b0024009003c0000018008006802500d0000002c000000800500200060008002000000c00040040028000001c00400140130004
  | 48 => 0xc003002004100400020010002000c001000c000000000a0000003000800100080000000008001c003000400400d40020000017000400100300000130022000403500e400800040240098015004c005001c0180004003001000b002000f003003d00180030000002000c01f000001100100010014000003000000440080008000000000600080180000005002800200340040000007000001c0018001004800000000020004017001c000003800b01e40020070023000000000000000000026002405a0010009001800000b80030060009000c000002000200040010040010001000600080060020001000000e001400600080080000025000400a000000f000c003001800200040160004007002400d000400a0124003002800f000000a0000016001400400240050034000000c012004c002001c001000c00d000000400b4000001400200080140004005000400100080020014002004003a000400100000020004003000c0120010012000400500b00070030000008400f0058002000000100b400d00140040024007001c00000040000000004000c003001400400000010024007002400900000000004005000c000000800000240030004002006002b000000000100000014002000c057003000500000010000018004c001000c00a000000300000160000003000400b0000006000802701c400700000050004000002802d001400700240000004020001c000006400300080100000004003801c00780000000000008000800000130014006000801500040010008005000800d001c00d001801a00800250060014000001b007c00d00400000024006011c00d000400b00040220000000000800400040040010025001400000280000014007000400100700030004001000800c0054001002400f0014004002c01800280100000002000c001000c00000ec00000200050028000000800500000040000000000c00200280120008002002c001000000000040010054018000401000a40000010001001400400040020014000000800200000050030003000000a00000030008003004400000600010014000002400b00e00000004000000000000040020024002008800b0008000000000b0020002012801e009c021000c02700540010004018002800c00280010008002000c005000802c00080000004002000000a0028000001000400180080008001001800000000030028000000000c000000100180280014011000000000000470000001008c010000c0040014001000000200b4000000401c002400800d8009000800000180040040007000800a0004000001c004007c016000c0070000000000000000440140014000007c00000000040010002000400f00000040020009000800c0034000000c007006c02b001c0050090007000c031000c024
  | 49 => 0x74003001c005000400000000000054003000c000001c0000010011008c00a0000000001c002000002100180030000007000000000000070018033000c000000c002000c00d0000003002c002001c0240014000000000000b0000000c0000000000000000a00080020010005008c0030000008000c0020004001000c0140010000000400100080000098003002c0060020001001c0010008015000804c00140130000002000000b000800400d0002000005a0028006000400100dc008001c006001001f001c014000001e004400800000070008010000400100140020014003002400a0024013000000400180000004001000000400040040000001001800e0000000000000a00000130004002000000100500030018000004c0000044009003c000005c0000000002001000000180020054000003c0000020012000400a000c00100c0006005800c0040018008800500180040010000005c00c001800e000000200680000010003000800a0018000000800600180180010000005c00b000000600040030010013001000300bc02300000190000005000000b0000005000800600140060008003008800500480190000005008c0040004026009c000007802f00000090004010000401c0020000001c003007805a000401100300000000000005c000002400000940080004001000c0030004007001400100b4000000002300100010048006000000c0054001005c01300140010004045005401b007400e0088000003c000003000a002c03a000c000005800d000400200100020030018000400d00000030010000002c003005c00900000110000004002c0060008024001c0090008006000003b00040000000005001001700100010004000000000100540040010000002c00d000c009001400500d0001000c00e0060000000000500540010004000001000d000c00700000000018002001000700380040020001000800100a0000001001e00100520014008000801f00000010030001001400000080000004017001c01a0074002003000000bc0020048001000401d000000800c80060100001004c02500040000000004000c0040000000001000700040010018000006400200000120000002000800600180000058007003c001000800d000000a000c000001c003004800200240000008051000c0000000007001c004001c006004405d00040020048000002c0000000007000400400040000060000000801b0024003000000900100000000002000400400080020000011001000a001000d002c0000004002000c03a0014002004800000080000104005000000100000050044050006c00000080350014005002000b00040030014010001000a0000000003400f0000008000001a0008004000003000240000008001000c0010000000000c000002
  | 50 => 0x1c0000004008000800000100000024002002c015000400c0000008000002b00000020050028000801400000020064007001c0000000000001c00f0010002000802d0004000000400e000800100000000040000000c01100140050004015005400d0014059000c019001002400200060000002001000000200080000001000c00100000050000004000c000003c0030004016005c00b00000090024002042401b0004003000400f000000c000403a0000003001800000000000048001000001000340050000002001401700180060018001000c01c000000000000090008000001c006000c002000c000000000500f404e00d4000003000a002800a008400f00b40000000003000c00200280000074017001400800000010044002003801b000000000000010150002000000e0008012002002d0008004000000f001802b0008011000000200280020068007000800900ac0000090000006400f0000018000c001001000f019400a0008000001001c00040220004000001c007004c001000400c0000038000000100700000008002000001400a001100a400c003001700fc002009400400140030010005000c006008800300300080020008000800c00000230070001000000a0004000004c0000008046002c00000100030060009000000000000040008000012800200440040014001000000b00c801d000000000600040024015001c01f017c0040014000001400b00080000000000009c00300040040018000000802000000060030001001c00a0004004000001100200080014003000000600200110000004002c00d008c0000000002000800b0004000001c013001c00b00ac003000800200080010000043000002c00080040038011001400100000000004000000001a0028007001c00300dc0000040004000000300480020004071000400c001000e009c00a000001400140010000003000401600280090060011000c00700040020000007000800400080060014007000c0020000001002800100040000000004003c00100000000004001000001900100040008002000801300000050040002000800000a4000006c0000138004000c00400280000004013002c007000000200000000000001000c000008000f0010018000c00b001400400c0005000000300000000008008000000d00a000000080000070006002c0010000001001000100000020000004000c00a007800000000000004000006c0020014008005c00600780030060000003c0050024004000800000b0009000801d000000600080050014077006c0020000002001000200c000500000060028003001c00100000050008001005800a00040040004001000000100300000000003003400100040030000001004803b000401f000c0000000000001000100000080000000000003
  | 51 => 0x3e0043a80af88cacbb6396cd2eb8d2bbb8d24be20452609887453f1a2e1ac9890defb850c2925aacd5114893b901291e284ea320f72bc12c78cba99cc743b32a341a13ce5b832ea55ac288903b7862328c60f32372b0fad6e7d416ea4132da84a63716f88138a5a41210a378a5cb62952cc71b34a9a708321e7a75c5101aec0398534ac69f5c50394ec0f99c82bf0ab06a2ebcd0bb22ab8b942c30e7e3a340001940bdc00009a91c2829e0bacc8b8e3ca12ba6e48f166eacc313c933210c6068000000220aed8a834dbeb4b270f396a4882aca922a1cac11b78ca7e0e486d7015086b881000000006f613d0776acc60000000f7fa558aec85ca2a896b2d7fac60bac9f40d53aa8c38b37c20001120b4921780000000ec0873200007048632884254b9f42c02e2a299aaf8f2b12580321cb2589b47a19e0000988af90a2c8ce8a358c323ee1108000000000000006f90c464058cbe43d9e7081db4503928b880003c242e70a18f6e0aa4e7fb6f6e22b468b6f272c00000000a81c6ccea318a0b1b238f718530202148e66611da8ae00001ef000060ea49e85db10e0000d9e227182098934848b6b94850425ba624a6fa96d3996f62b9ee7dd9796233b4f20000f422d6000c80d800078f20bc0002b7c2b0a24c5630a7ec23a2d0d62906263e95b0c21a7ec79901481d2a7000001ba282c055c5ab9a38292b9dcf4991e2990000000000000002a70f2080002328000de907da91b9d32000122c0002f340b50ee600e2c7eb0e9bb44ef9f8ae3a80003343c180000000568a9a8000049cf1fb24a982bd34865196cf2f1b0e2c1287aa3eb6c26888d4c44f928e0002104a009a0e0001ff05f7301af30072e000179463f12f0d3dbdaa0003646e3434340001b74980000073295bec60a096d0808124e99ffaf6609460003250d9d0000645837296f08361f72f7a8e8372400017083b81c4a0000b1e21c8000e463148883998ae6080f0b2b38b43b21f8e00026760002034f8a0000802023ceb5800000015f44bc9766e25b054f6b129e3ec265488cabcc6a222fe000000048900000003330d04800057200001962cde03e966ada89e321b087fabae896eebebd68002401e00140030050001000001b0048009003000000040080030001009c00100000060008000000000000300010008058000000c0028000003c0330000000000c002008400e001c00000000110000003000c003001000300080050000006001c000000400102e4008001c0120034005000000000880040000003007800000440070000048001001e000801100540000004001009000000000170008027000000300680020000005000800100100100064006000800b000000400340080024015001000300740010010001002805c00dc00100080040000005000800700200120010004003000b00
  | 52 => 0xcb8882ce38d7e00008f422b8000e7413e400000000000000c9a24a44c52aeca9b91942313d7a298136ebeb99d878b2af4058336eca009e6dca8de401733627eb0b3c0003b427892b286713b7c26f23be60301ceb012d50c7d26beb8180000da9c2c41bb1ac8d88000000123e0000000e629956000133aebd2cdaec9b424e2b8b345aeb8de43ebd1800029a2000310457f89c80002fda1f88254111242a0278000ecf1d1c456850abc28ae20531fe800036960003a3ae178d74d39abc80d5b8bed88916000000004be00005f2847c34e16d43c18c628318000ee586ba75fa7cea9236d856600003c52aa08dea3b872904722368fda00018a4000024cc78a98ecae3bb25991fe642a244c85ba8ccf680130df882408cc80009fa195854084ce0000318000048e000053ac42235a36584c446902dae268000b482402023b6de830a6e80003d00223a1545fb3328e81ba2a1c4000091d13ee3c21de87d2a5dcd67a8a429c176415fb5f0f73800024a173000000000a3821c00018d485c0d4400024babeabdfcb06b7923d60ceaeec07401a423dc5093ad217a3baa19514a6c88abb042e335cac8864000005ded65a442f012164eab80006cc878200009aaf1da7f200000009188c1a8368f827270fd4c173dde4faa8364f10682490a302889aed20003d4600032e8c2f004e3fb14ee00000002b4bc78aaf04763d82064cab091465e064265a354452d35220002a4e0000000ae8159a59139e05eaaa80db236bea980a96c10328c3e98eee000104e6b3ae2c41c0006e0a3cb44b30000000000000035e24de8000a6e9a20b0f1bf47f4bbe000028924f48000067a82e13238e2984b60254bb46c3d7a496cf023a4df7956e0001e58b7da0b20002c7a00000000002db40002d123f0ac86744197a993aa5e8ad2b10bf214c8895a4f660d13e2eca81240f3888c9f72944ddfb72cb410414a4fbdf06b610a655520a45888744f00ae4a878b8b617887a0aa5854a1d1a57200036b6169a3d6bfb3a643fd17b46a78000b2310c278886d0210b04200023640b8b5560002e1c297a5486959098c00ab80dd1135cea70626424bc605dd9b22b5a0844ef285aa0003482e2b2e9200002063c080008bb156c0001ebe0ac163a2e5b486d41a16cf7c80000000c669b1981cd028628b71115c2bf0c5e814812680f0000e203066c8a87ce90280b6f820ae41891aa0807244e000068af0a00000661d686da0d0c0003526d7c9d9c9e4a982166b0ce519add27e312e200001427301d0ae942068d15aeb01af2c9278d2adc0008c94eeea824f489ec879bbb0c7e0a73a8dc27160002f28c801da0db1378e37c326c3ff9d3ae703b4ae1b1e406c19f14a28a63200000009eb259c3890db604533e2a0734b471328987f70cc4d0f20eecd226a67d100004b1855ec2dbc8cb4e1d0200014
  | 53 => 0x8ac6928b4e65117d64e080708b49660c37180a000204ad7dafbc7062b5ee769f363d221f6cc503ecc4635469fb8a628768c00c1b1fdadc6ae7c336142252e2cd258e13682b794509723b08423973206f2ea2d8f9dcaeae13c0f87b7640003cf8000233c0000000bdf8000a8d800029ea4c60002c06cb926aaa54964011f879a017add49c3bde6bd81c88d0600e2ceb9ebab691b240003adc000236caa38790f52a4f05b711869bdb62c1cd196a8968730e972b6e46981e0ce1b9e242aa91adeb0000c12000000000e834696ce9268aee1aa2428d8c86145ba26fe86418ec403952a2c1bd78669252a2809302d7333dcc7a1b864af8c082842f367fd84700a704eed970afee79a1b03dd2688ec939aa8cea8b8de994482a41ac03461cec39616daf6305da9970718e052224185888824388f676d162e884aabe13c19bc5d69e60e1304c2f868f4ceb1af422b531ec1c69c3251b03f822da4769b3b6aaec028b6c9eba9ac89b4ea3c7a4caf4730c635f291c0c8b5e62242466c8fa694d632a7e9ff877a60c8f10f2e93709441d448cd07021498950e96192808a87c2d649e561a60ddedfc96880a289de7309aa43b70030cdc1dba1523c48efcafaca2594d2f5533cc57e34987ae3dda0670e1810da534aeb16b01681412cd005ba8488576a482986ce88200489a2cc99ab83c7dc1e169098000810000000000006130000d6905a20001c1c209b12cda78146c15a30c0000000000056c36caa525ee89560000de00000578d872e4ce2ea6e44811006e80b1dc3422cbab1728dc2709abcc60000033e800000005202b1a984f6b800023b90f4e6c01c00000c88e74a942e758000af4a11ca22b140ec424fc8adac7c1f2291023517803f60bb0a7190f0cae96a8a87149099eaf3ab02089e219b05a4002eaa65902980b21bf02690d36e3dbd0c031389e07b315240cbba0ba71d8e4c80dfce8caa622b21b1034128449f088346779ddca002bf089b3a5ae55071287501b83912eea72eb19600027ea000288800000000002e3200004ec61a38d89d0afd00000000000000099f347ecc20000000225200002469e534c0f500000d52b41e1c50586b0d3d2a7579e140003a8268a259800000007cebe24b1100008381414238a15e000129a08394766b2807430099e000020944eea2728a3058853c276edd71bfee282bc4846aa2a35bbaba40719662aa9bd41ebb5502f809327e013b03772aa20c68ba27f113124a108587e90e8ae1003f000008a80002a0c16e2692d28000000000004cda0285b23030b93a62ab8e928af6014060003816b1308cc7820000576800092f27a024800123663ac835ca90682e08c23242b1431b8b2abe3067ca15091a48509d07529f2834eab78370bb70b7ab2f8b351c92c3236e6216928c7562852c5e914c6b99c689b88c1c2d88b8ce
  | 54 => 0x424381e3168a868c8af5c39f00000000000c841af00f821deed10000a1303ea000000080e80007c20f343ceb6b000013b4aa90abea883a4400034940061908868a0fcb8429e2000000000017a21bc94281940000000224800000000002fcce30281a0000574000384800000de210000098f138c0000d226ed89924f20ed0be51eb4000000001fb172000000000000009d5800000000003edab6aa7092a6000000000032fcef7846400036daaab06d82b980000003212954910ae67800090b367a0000000e1c0000092b55c0001190de02d98b0907640d9b4dc9d635be623857227fb1e40d701f659d0d46ace9ef60000656ad1180000028228b29c0606b9eea7298e623d50e7ec49af1e7020000da183b0000082213e8d88000000052c08d087232d491e936013a000002c1a46f898000943a04477420e44821cdef6392c88a18c300002f14a63161cd2a9838d4d8d4e5a8851ad3408fe8be8302a839a10a73b8fe14fae6e0d310947d3813809899e61fd8000c450000d14a4d60001fae0001dec2c8936645921064c10000cb28fca4ee0fdc653a30af6f000076b130aaac15d67721d5c000057a6bf0bd4eb1319024793f06ca95b87489508dc0800005e8b2cce10000226b4ceb17ba4800000006a3303ae7b000000011b600f358ec90360e0000000cb99b04cd82360cbb000079180009f18d82ea23d307033862dfdace68fa0110f0c836052009546ba972a8e2b7ce00819b65da822205790482193cb81f0208ae0a88be10c06809061e043c708c838284626ff284811080b279705ac3c99cda3152e2e7a2aa329b10c7255135125beba56c821862970bce25f891c60003570912999210c9eec0e781b6f2028b4a1c302ac3c9072a7da92cd82b38c8c18e4033cb1a2b839bc61d8a23094a33de4c6ae8800000000cab7f07241f7c9ca9c3e82d0bfe8aeb15e6901fa096c3a4c00030783bfa818136845429933520000fee87a8b085a086e2c760c8c8ed0000c85838c0000000c812908000323085000000f0a580bbe2fa0000000000000000001dc04b0aa06f65a5e2567950c0002b96e0726c01281a6887e0c705d2070000000003402fb288bb8580001c5ac0f80003a9bcaaee880001e99a0a2378000000000000028c27e61ed200000000001a321e5b3940002ee27ec202ce5dacfe0001f740002c6228f9f0a00010145fa8000000268254eb34675ca02a57ea31cb609f06bb7a73e7d98404dcc17c44fcb1f66b8006e018b0c014a14ead4baff2037249ce47043cd2db06a26b11b4eb536f2bce33a62358000ca13528330bb9e826a9cc102011ec9111d06e7000021800003aa86060002eda9e10000000275e229a502e682aa687cad70a3f17924418df22153ca82403d8806ebc8a5933914ede9f040003db26301ec20e521f043ab9c622516560ff9
  | 55 => 0xa4c2ce801a8000332ed5f0904af68cd61062ac01548a2ea298182e2300002d507867d5a27614038e007c8f2c1ca1c2ef74800000038420002fd800030e800007ac00030d64e13b18874bafe28c8dfa81eb75e6cf894c2c6905a1ca8a94f3f02e60e6822c601abd04a1b944bc73b348a79b442f33bac5b4aa86ca2a16ab28a18875e2f9abbc0000eb7878061834049fc3704d930a3c769a3467843e2ec7338a40983cd400039b2b803bf0994342613f85d09843cb22af3db0ba2b5b49e4000061ea6845c991f8853a722dad38540000000b0b00006428a26c3ba6047e400000003694e4eb7840669ce68051c2a2a0846a000263a0ab2cca4f6835a00000004888000000336cee027365be369800034a67cba4300001b8869900002f8800088f9b760791cd44943920ee2a17e000065a00004224b68f7c8eeb7ba0000000000151e0002c4656d225800000000000000000207c23b375836f169ac5a28621260fa80003d740000000aaa2b7e53e1b485d88df69f033981b4bdd67a00eea5a580d44a820483ae11b874481e624ea21c1f186fccf39dbc61fbae41b50428000172c00000000003c702f12ece1f330626ae04dc86d9bb2a1b9bfa0bc80004040e1ceed33d00000b2800023f24c206fe10d00009d9277c8c9b2dac162e827a88bc84b818e200018468d23ce8a4323ce1be8d5412a23e21fd093c0d480945c3afd421a99900001ce4afa30d43f4016e5172b042b29ca08840b5a36fb186e813e16b67000045085b0e0d0c6a8ba29122900ba4ce4211ed3eab0c4ff1aba0708fac12f00006db800078fb07c0002fce0001f18b081972a758000d8abbae3e61c48aa1267e5392b60173ae9e7e580000000dea0002d76a9cb4360000d2810baa9e25e800000000000000000f39852200cb312e9c3652e8f2e3cc951c8e0001c80a9d800000031ee7ec80007d50000bee80000002dee6db0ce4ee72cd6e4c0862e000000f7e000000000000e2823664809f064f0000000000000010ec0000384f43af0600003e4513800000000000001e8c4ce3444590bd2c0002d6abfe98440f604b073d000018324d000a236ae6f0000ac620724e1800000027f40000000005000048080003e4b81a52a2e200000000437002a2a31e6c000000062cac363a8000018fa318a4100009e5931c5af931e000141c23c91fe0f71cce741000061624d200b00009ea8cb42170dc8abd8804be18e76df516f600035c4000000064f9e8213830da41eb42c00022d6000000026cb77066c13160000278e5622c00ab92ec00020acae910d200006cc0fbbd5600004a6e2399060743aa419f9a6c1a9886cee9ab7a0d3b6ae42f82f8ccf13886d9989a17f108418403860000aeac8900009512f4ab498e00dc7397c0751a24631b6180c3965ed8e9ff2c5d95467e534f849d965abd409c6
  | 56 => 0xeac7934c59509b0db29b84a960d2051921ee2e0a60c60ab932c22b2b4000216000023c86d3954243e0000e13971c00011bc2ef8342a4e942a75b2c484e432a400000009398426000103ea58324ec04000090e8000e508000000174e8e308242eab174a0780000cb112a45b9f3c52f0000f6d8000146259e93a2edcb70298817111cc0001edae9f1b086dea7fc558851041800000002c8260391d63bb1b588699bf8e92acb412e91a05f1b27ee3309d6478179af0500000000adc00000000001444ee13a72325900800033baedb1f105468000df119f011604b8e4a000058800004f716de000157eca681440000000ba6122ea01939a0002b622b60cbc67cbbda4d08f0ec2ba9725d1090881330e6c67af181c302d00003ca2ec521a800000006df1d3e1911740c0ba89e723000099c8000000000000020caac380000000e942d1800000000006ba09ecca78000f8d19ca620800094d875ce6e1134356af92d2b026eaf5398e00029c80000000000025caba8c40b42b5308c7a7525a0143481d18fe5a11746d9c1ed6518b75a58a33e6e7331ce028b3fa87f800063e06da79a0d92a391fd63b51044c50a9b4a253a96ad00000f592ae29dc2842cbd0000a4f30261cea0163c300002ed8e4c0592d1000023b27e6800000000002f191ecc6c9b529732208db4289a2b814ce3d4a2220001be25c180000000f56000000045c2d6c0f68ed6578abd609d2f6c04aad8c00017708588e16000000000000006a60000d7b206ea3680000003d4800011a235c30604f5278ad4e08dc01d9fb8f05a8e0211b35a6220e38002850e24b9a8a333219838c00965c2a8bcbbd0000000359a6969d62e8e00006d90000afe841a0003392d00bc000000000f7a80004c60fe600000006620000000000000012ee00000000550000000095a00008b4063890659280008d58c9229b878c0bb25841970000b519e52d0e9fea492863c53598a000020f8a8b800030a232e96c8f5cd6b2cbe0002b0a5e40da8c1f9a82026b2a0a1b3888e5ea3d47de94f4bc680009f589429c8060a2cfb26e0002206d40000000000b87180c56adb17680003d0292da7341e127506378b26817a5e08ddb2c0493000e59a00000a49df6b96a0a82079530096a56a0000d102d490e29cbb8b8aa2b772dc3016690f9beef25878e00026c8b060cec96916f29ee0000dcc859e1583a6cbc98662d59b0720001da884d10749d9acf8c1b80364f82fe200021e648a20c4dd3a7e2b65245e08492963c033d6a1912687d49552b8280002e1173ca0a000000023e0c9cae30b798102acf29c0000206077aa5d0000315058a94da26a32fac6a147a0001e1cd072b3e5b09ab015c3c9ae89ba0c239ae8052b818ce7a09dae71210e20fa526496b87869716e26652242babadae41fb9ba8718cf6b781694be119fa9e7
  | 57 => 0xcb728462b092d60318e000199ccdd35e0e8a38b00001396ec78c4e59ea3549dd00007be84d063c161a55f0bb400019f65c5b5b090f26ae6553c34585a4def3fac6ed030b483bf15ec59f927225da4b22a2bb1a8010ea80f404f230d03c649b86889b7bb82dbd071c98709d8e82bbbeda98dd6ee387a2e76010e6c5b7f4ba831c0d000192ad28e12b95905ef4e0a88d7208fa17c8bf21e62d4ac6fa53a04e9e12d7080001ac24464431f38a6cac70ea894300001734272800095d8eac0fd90a2c6d137800000000001cd8000000073fa608000000001510048740f9ad9100006e900000003cc20001252222b8ca000000000008843ad80000022030000000038d01e88648d424a500008ff95c6667aefe7d30000457960ab250208d5035bc0003c74de83de2f0985a46e7b564171958a097a58e0002ae6b8215a430f0b56b76abea0000c8e000000057d80008fc0a24c0a1cfa0000000a5636f0cde89b60001ba6b2f1de00000000c7f8000a6e3860da80000cd911820c3191a09a3a8ceb09bf6000000065d8000b4c06b8d4100004b40000b6b2ec00f28fcc0000000d9a259000002d8b88a126999abee00008a0000000000022ced810000663879c00000003da000000026d8b852cf4e9a8cca00000009bbacb263c8000000106c2e38a56856801e22f2a6ca0437dc00028140001f420001d5aa462cb6197a9d2db32fa24d2167870497ac668ac420003c4a96b0ca46473144d2e2b58000270424c1594a1192b208e34ca310b3a47dfadfa7083bc85d429f2dba8684000318cb859db85399ca278e2f4e8b9aef203cb5d837616b445d0bbcc692132def09e0742312800032d02db3bf4ed8049252aa1b8a5731aa2c30ee8b9a201e00013bc10eb15654006eaea2a6b25118fa4b718edaa438a1cb92331022b0982c52bc3e77397a017bb8d601306b4e75347ccc38000344abc0bc2000031915a0979aa5ab1d3c723e3af7ca8d2328b520fc016705ea2610db4f6ea172b6ea642f721398022b83acbc902e0000168f1a907600033809701bf205e2da27edb16e1b80a52c0133be6050978eaf80002440e68c4c13fa081140a07705580000000dea9d906e30aec2e98756000163cd38800035e1e365cd812e0003d7000030c29650000d5608aa184bdb47341290a930040a698000d55254e295000000000000000000000000000020ba96308b20000000bf02b8ce7ead3ce0c2564b072400338abae4ca80001a908ea6e09f840001484b4ca1bc9578d6a29db5602f02516f270e6c5253af2801b14c576112247ea78c0dd8e96e36aea435b3be8f35bb0673e0ace0210f304fa393c170379cbab07fc000273848e276a0003b5622c2b9c1b38eba0b59dae430192438fade88d4b892eb8a690c362d3e1da296c691189e0b3000000017147ed04488a636b2f539a7
  | 58 => 0xe6ef1670bd496e6b210a1428480000000a50e32000062c0000d2935b6b7f8f9cbefa4eaa1687be13aadb84f326da44626140003234b77a506be7154842c9ea84d621aa61739248f1b50858914f203b9b1eb22135a1c2800004890fc50b23bc74d8f466403b0ee2aaf56c4e07062cc83c470502482179942f8c3562df4b5a8cc7afe46ef8f6c60b227e3cc948c59cb514dc380001761ecc6e5055ae3d3bfe71407e88609ef2000242ed7f3da8f0780000000000000156492211ceb2c0000f4ca712ae995de00005b60edb54c93e8000e7a80006210c523ed0bf44eba1e08420cde0000000cd79538ef01bd6e270000062212a00009484c8a55444b331a00000005d7a1306309d948cc10244639c5214112b6000000048183084dc8312d188000838800017b2b849531a540c70c862fb07d0180379ed56b6e8dd01d2c6a40000293abbacdf812cef626a00f5a378b7c000000034e04b903825bc2ceab16091c374a748a6488a4da402a48b2178e74aa97e1db15f071aa3da000176e0001f86dc988fc3883cf27ad93b605d0aa664d9ba0ed3a7b002b8c1ee6b83a4dc4be2c28380007988000000280a0003112d1280003e7a626ca9a12c25ab5e47e78a74cb623f4000395691818dc2589d2ea1e226667aa0b604c8e8ce98a0807322c0c0121152f110000f54a24a3fd8cb06588000ea800000002a54c0636ac67f000083380002a49c24b08b28ed74b34e6f28c24f5cb5ae281affe2e43b4014f1cb03a3acfcee4ad22170bd9495020eadf000da1aa9232c6f27b23df9c74aad88806eea9f0e1d260e302a57cdf836504272d44cfc2ea69ddb2705160bfc3979e1e0cd2a22a3430e2e5299dc304a6bc0c58d2e4e936a41d7a8e8b6d9524e1103b40003706f47a8f6e3c13b28679046bad9bc21dfa8b05a7b97208d0ef6c98971eb53393e0001ebc1ab397ec781528000264a68fb3bc4d2bdd880312f44279bc8c242b920000306c539f48288b64e1f79a92b6a96520001ee6a0fabfe29628ca328927a98d0d34cda040edcf98d82d2899abee236861f10ba2dc10285f935241d09c5602f36166d82e0c39cafa4b1ab5ce1e49b3ab640c440003442aa201a243a2d2eb00006c50dacce0b707caa8f17feb552fe000026b8bf79edec298ecc00031647e2015ad7b80000001dd8b95313e50138b275801ac54c99d0c2f800000000002e280002f63b663afacd01a4a6d60a6800000012de17e31da0000000000000000000005de99841a1bcb045036d20001356b05a81278090ae38381da0002c4a30bb4c4000378ab4200000000000d1a8000a900000463360c00000000003d865c61876259a23aa3f9f6c000000086d00000001db61d4800030b191200000006523678af72b266df8b60cf52a92ac83bd053794424f39e9e49b1f34e9782ca67490d000000000c
  | 59 => 0xfb28eef608000a59b07aab4b990766a4e07de177e000359cf4280000000608e6a111600028046b780006ab99c000036ba0001d00e5a0000000000056a0290f4822026d0ac52c74800000015e000029f41e9311000018083af31ba0a5000000000007950000c69a95e3852d58b861f222dd99aa94f10a48990fe243980009bf25a2afd800044b8eb0b29ad8e1af9c307c0906463692aa54896928f315bc0000000c6d8000bb91aa870e017e44c0ceeaa68bea670a6d40adb4d80001bcc3fa1d98394000000023c463380006d32a24bb42a82477b00a70eb1929480e8231d37389adb08c5539196df30878cc1211451f8a6cbd61576e4aa4fe05d9d2435ebb4c44e180255a2fa80e884fc85a1fa2e5d26ccca0ab36d9f8000d61206612a969892b00005aa8000c7f37da875a5f86aa83106ebb334be02d062e50e54f2218a68fd8a1eb610bced31b71419816a0dfe38a66bca432e533070bdd9f0c7c835c63170c1062a32525cba4b40003032d1b976008600007c4bca668f0d528459dcc3958000b2632607cb0000000328800000007f2000028811b0c971f5e52780000002d720000000f019630000223699616d014da3ea00000007112cf6b6fa6ca90200008852ea8d5d80004dd02c4da492bccee3080b3b1b46e3112644a225d688d000000002806ce182e2a8049e0002ed60462c9a00024903b79ff8f7014082579ed8000101ad3b177811d2e86df600000003c220000000b5900007310b1c0000fa000032d25970524000377c00023e68bda0226d58c20000000065719b8b4a04502ce16fc56b80000e48000d1784c63daa144e49ad347058000a6aa7d40000000edaa652d6c8fbc0ad0000b568a9e3c924c056d9d38a2325ea3f382be9d50f287ab3d2ea800000d1310802bc0000a86a7b6000000000038f800015042b5ac76eab21fc1783ab25dd00000690000dde98220b0836e777975c94f80000000000000312a69f0722c1dad662d7016a2fe90cea47b91a487a1869a1a4542fc268ae0b8df813d800000009721118da497b2850000239c5ed8ed837a2e364eb00005e2304400000000000000d43a1121391f60ca72ff03578a48f8e219cf338724f7b9d8ad9f35eaf1522b0ce7266800032f6000000001a00000001a30f56800002a880c4ea9f1c41009740002f10f27a2f0ee52f481a810260003e02be0908a4cb07f27ee96485e2ae04774ae622ae2ce8e722596a039d2600033c6dd5222cd5cb02c3b18f908978f7a10805bca8e060255e917815f3e3698b93a2000000000034d63528000000000082b85b2eccab9e00009c44c900000000000f849d4000000006a68000c27341a9040000bf5b146000389400020cc81aa35821a000000035ba3a190780000000be61d7a00014a49e3a9545d087aaefb0a989100000edf80001c2195e5fb8d
  | 60 => 0xa0cae1ad7ab87aecaefab0d099b9f0e2ea093600022f47943aa60003a08b4b00007f8361046712a20000090b9097f8dda8a46e94800084fa94e2811754d320d560000000a741416a5d80001fb80000000000bb53a4eaf3ab988301be81d6800096a18664cd01be1ed9ad2ed4271400038a23b881fcb438ac4f3b34d4ce6800000012d64ac136232a8000000319a000000000024ecc6700008360d808160938d7ebb38de5b3884160000000206c99e0b789cc91d800001aa7e980007a52730129295a000359806180003561ee8542bab00641a526b3087a839ad4e000018aaed33f254482f4f3dad7871f3b1c000154c00000000000000f83000086b00000002bbe00023b6e3ba10ab5f345c000357e0003396d80037ac7218c4000000000000000fc8000c3f0cc081e1d56000000048283e2d9a986ed7589b4d0c9566e9d094a1949e1a0eaaefa6c4abf4a5a350a54db8f26f6b12018d3642ae28776d523a2099b2d2a7a19ab66b59af4ea4885668a86f05e90350f37b68076fb614ebb1a780bf163e4b514b2562034673c9a7a2a712481129812a5b9da4a90a94829132c6d54b49612306f83ad28866f71c02dd180004d1adcaf67011c4ffad1e80e0000dae1b36f440a722ce9d664b03bb8c570cfe2dfa5247aa800013500004c41c9a3121e0c71ba69a1b9a026a4022f28090da09860000b55903400000007920000b8f80000bc0000000000066b30de585384654700003f20000000000048d98aa00001282c5a48c00029dae373326764b3020b01c9613636ceb9dbc102dd2a0af45b8567f3aebecb78546f7128c445f9c70f86017023604668f6069a8c4af44f08150e7fd3296684b0226f112621ea0cdcc580d3089f074c117251e9989ae22f7884acea9e9045c9030a2a94a0d4b11444ea2b52916213643515601d9911ca9d3afc000034a1f580000001b0064e8000f23864800000000000000b0080008feaf24e621cdcc708542bd0238840b2d92d233cf40c92ae0961a9743c617a8827a94c4e01b2e000000068529901601db0e40bb04e85a55ad509c5892a87d46961ae4bcf8774000000000000000000000745100c60f05f019b27a6137b1844ba8be846abcea4b4a9222c91292b9c9d6ef5f1842378ba36f0680b40140582d1680007d91dfe33680009da201047200008509ca88173b9073a8000d1cae78f07014050e800000029de28eb9caea3ad746411e982c80000d2286c40001a5e9b49354b74000037b1110f57040631da6d066b8f4e46b23a8ee21582cbc0532118364ac288b30e33a31a3ce0000a9a9a6a7b517f2ac5a7e600005409e1b804bd9299cde5286a44a2832efe0c8a3e1927065f99c623032ce7a80760c7c9590f1939863630d4091c299497f000047d99a81b188f832e862c68b22a079f0db83140000444a34e79297026
  | 61 => 0xea785d65e1944cec29870b7098ae249a3b09e88e06104841cd392fb4c41a0326d68bda2050a7cab90d1ce212f120001fee57c801647c2e521fe2702a0984f440a985e32c8dca4c3103c86109d20003e140e624a88b700984858b121c838fcd0b9f008209b340bb82e0aed8000eaaa65eb6999100003922251236e687af0095e99ee38cacc47a70000a1a00000000ea20003718700205a47ba6483d10000000000063b8000000000046a32c40002f5e0e80ff2c56b19460f9578000000007595d0486024eed78ea4a928000e5880000000ccea3d337cbd9a5a69a03a22b6c96e0f17800013597980000000f6780000000000a39800000037fe0000228d7a0c820001d288a21a720001de21bd37c60a59c94f69ab4e99d168c7882128a80b6e0770825636ab950dfe80000a995e467d33389f69be00aeb628b5730ca97ca35e370041651c929c3a690b62792c9ce008dcee4434c25f03722e918958de214c2a30073e08088a2165357863d3b9807d11f400006e8d478ab646cac2ec49114e0d139f063d88862ac0b4432a295044c92fadedb87ecc18dee00008025e70db09ef28600b92ad48c01c1ef2938a88a29e664c1ae7e66e9cac64b1886bc834288520d484d4b818e0e25cee4b283acaca8900bd92a4b8e2472c332fee64c0e9cf57a1561478672e1b8d0a000000026180005709e92000306873593920003b5800005f40a3035ec3c347882184023c83a7e000301438a892a0003c4631f83547dabc66996bde400000005d6000097bb3da64baafaa99a0f23408000000020cf3e854ecfa0a4c5e7afb6a388a0a1591eeef5ab416000322000024c8d150000d65330a277346427e2ce00000000000241e03085d29400000f8aba0e000045a661a0d6f770000000000000005c88a89c222be8000d3d2b74f781d883821150000325ac4e800000000009a5aa7c188ba1a2fdb4fe19387b8865afc41610172a6f97d48910000082856685303201fb2a9006c290a2d78000873bc5a3a43b1672e0ee400021d80000000000075486ebe103e89d70f158acc0003d1a6148f7824d39043732b1c00000008ac8e8000000000003036000149600000009efb61eaad2b70ea182644599d54d470b6e4ae91e404d813ecf21468b242ee03ef9ee0d72800044e8dfe57ba61e00033ee760b6886272a94ba32970000353200000000000000d4f17fc5989a040df0758e9db7749448e3ada698cad62100aa8e911a10e0000d4e945adec014e42c00000002f5420c285c0002b465cf899eb450c38000139e00000008a129ea001363647a800093711dc173155a3e33acc12b921c4fb39cea781260bcb80000000000632049aa1d85504c994c000008d22591b1cc14804a0e389fcd40a0980002872163125e97f80000000000bcaa436681961e915b1f817d99f80168f3e2a00
  | 62 => 0x168a80b800099c00000001176000249820e80be943199abe2941eafb2f7834500001b72b422670a28a1fb952b65b52058005e40002a163161054104098c257082edfa1952000356e01f2dce1f1021471916360003bce03f3624d46800018c35829d8800000037d0f8f8000938800000034220190efac192550837803a4d921c4a8c11ba263bc94780356c0b7baf69c72b0077e01b434f1b26000000018c8000a810000ab580000000000000387a30309185938000c77a6985fe800000000006789124000000075d82840f521c03d00000c5e000097915fc36880000000de600022e4303a514000275a59da85688800000af2342c40000000018547d8b6bc400a9dc052a1102969126a5f270670403f445a2b54aea00007cfb274b22aae889814544d101cca67b4b060930e4abfb1b8df59bde6568ce0c97ae744268d86191991838a1f5821dad5e79d1376cfdaec65b925de12ca45245f221abb0a788c01840c0003890f45000035930e06c524d8f54279c55cb2eea0a9df40001f1652f864af2f970439aa76c8d10cfc9030e5c399913cc4caf4665d1f5a0ba304a97123fc000069eac4b00eab33ba85751088bbb3c4c14bac9e7f6056a9bc3bf631e1c7225f23ae6250056552a166c261cfc1db8c16685a9e62c28f969fd9a8e87e8000c2b00001cf21be8df9af616b94209310000273000060c000083c1d9e42d16f4000170cbf480003d980000000000761953c000066882380000002ce4d269a66000106a811aaf2f812f2c00b8000c8f0000ad20000f4134be42b1816b282ba2d8e0a2c0da00001a3309ac428d903e28512bd8a37cc0e218a6600e740000aacdec89ceccc9a94958a2968e98508771b95c23a000000007d869226e607c2cfa6a7247ecad8a6af8f1df098c3c08bb1234a000000052e85448bb8482d2700000003dcae6d12ac00031709121b2ca05a63830fb17e5c830bab4d8cf0094225c39083de4fd90e4c2a0b7a27ba19a2429586dc7a3d210ab8865ee158ea339d7ca72862e8283b48ecb171204683bcabc1f9cbfa84865813c9055432dc0000000000232cc208ac02ee000000038d4431b05072d95aa0003a1890584a2d3315266c833e4f0e19d402496ec094a568b0c800044d800000034bc97c0000f17263e4b700000000ece34795066f4aecc8000d32a713662768a4d445620901b212120000000d7e08c64798000074b2d64453868c838c148543a24000092400000000002f0ce871a4e09d965880800008dd050c0002c4e5b58be43f8365a213800000000000002d18c8687e4b998000b869f24a7b20fa6e590deb15b0a021c166c33e0cc6e981daa643a2be10784885a19fc69471c664bf33b0d20334402eb8fa12521529f2a996bf2a38030db90cb84bc428a93bdc000398cec4ac8e29a02307f2922a92fa45c26029a0
  | 63 => 0xb0a8000f66bcdc000033c0c118b4000218e0cdadf200033d29ca2ada1348100b038196ba39a606c6832840e000000000004ba31d0206921acaa1afa386ad52c562c6c76009d48c3927e09f1e761bd992aeeda2c6e68aad019d0000a7637aee5e0000d5a85909c3339e072b4e8e653cc800010429be30248c52a567f30052af09c762bdb2be96219e412289a0a6620fe6d8ad86d8998e0753861ee0f8592eca016243c86948220a345c03e32eda257451b9478a4d26a88232aaa7cc24f800013f800004960000000000322cc960b40bf9b1e66d03c92f39246ca4916ca19b800095b899443ba1dca59066662037a202980002e6af8e718bdec94c04acf362820000000009602ce4b615e655d0fb20002f22840000000000001a380000000000782ab82952800000000006398456b6c2cf0ab10000b903c5049f000000028ea9c2000000003300000000034800000025c6dd3099677c9c869a8aee6048277a515bdf652297c2d958bca6d28816cd60000000169c000300cf689b708600f04c0010caeb036305453458ba5b826b7f23944fd149abcf082ceb9923a97495105e0940c1211722a9427a4b19a04256e800045b27820002fb0d1380009e617dac2d33c2856047a3638000ab3b93600000000001ffea4a8ad0d1c26207c99ec4abf0000d9526bac408e2e000298a000000000000000001e5a000092c248986c1b01afe765822613329806e394264710000db184bee1f000068e80000001caaaf60aae09b32a256b0538e9033ea1c980003570000e1480003fe033e0000d26c7c1c1a011000065801eaf0b9faaef19a4c0003d920002f5a948af68c3d1608e950eb298b31c40000b9e676852a3181180880271857ab9a648c0506e3980d65f9aa281798000000138e8f02a086e4026600000000002b5aeadabbc2da32868e0a77e8e49878000390a96bae283980636ed6aaba3a49932436a7608a0b292eaf077c604133e0000000000369c000026a000366cf691e263bd3786de6b906a353b9ae9e06388ca8000163a8a051f011655027d2f4202103c8add807b8000f0ab68e51790c4d880af8b143b36270000018812786b200000000a8ea91124ee613b8ce6fb7689cf1c98673b68abaf00000000000cdc87b0c87b2bc2383998834a36655ab5a08298bba00000a0038370ac3d80000000000526167c83438320001fd094101e21f990e00ce3a140000000000343e52b0000000000011e0000240b63c91431fac9924046eb04b6000016cb3012fe957000000010184e80d763992fc60001d0cc850c6c5c6b9349ab1dfc701123431295ccf1484ca30e91000000000290b9660911a26cd58cb856ca420c179bd01c7945220e14cc0dc2308c5f0be6000304c58480000ceb2fe339a3de000149c000268c3c6b74a2e01c42c34b898a5ead008490ec48c1
  | 64 => 0xdf4d7d0000d579fbc00000000001606cdd8000cc59b9a00016b80000000efebb6495fb016c2a96c6140b336ae39b923d29b500c9b9de000142e7a59ad05a38b86ad7241a00018e49a3972420a37e638da294329b33e225b47673a17526a9ad16cfd000000000000290082c93224e88a00000001fe240812c47efb3b27a92d3a04f3cb6193120e20ab7c8675b490d8bb0ec06510fe5b63ace199000000013d8000000092105a83feb322870800073180005372e446cf39b600018486bb80006b6ac72c75316a0003720a9e80000001ece00000006dc80004db000010f80007fb000000000007713350ca4002400034669b82b32d37b90e0001f720ff000096d9ea677e8000000000000010565f83af02fe2e6a2c3800000020e83f58e1ef7eb3b6b679abe07619962ecb4f00000000b362c54071860482a8a9a00018746542644cd0b4da7bd0d84f04bd58e84839617eb8e8d3f247c5bbb9f24f28000e5799a04da9ef07c6a6562c503c019ab3d8bc08000b58a962cc8000089b9fc200036dc7bf98d04e528d80f2081cf1b0e044d01a80985ae02d02140031e8cd2d978f62000153e8b837fc65c06e41b7a51aa7514b64198a1ac873a009648c0411a0000f750ae8779ba42dc238720001ad45f3bc0e00018cc183ae46077b23a3699432000000000017385838c9ca2f9ac600022c40000000d2a0220f8eb5a2000330c0001cb4000000073d8000d27800013e326603338206cc36f85dc807826ea8308142f1644097b20003d2436501a61bb153495e3aa8727b1a00300ca0280003e14b181828aba2e90d1d06420ade4f0297cc4620e224320000f510e4eddb87fe6a1be1c95b1fd40000000538285e0baae6c00016ccace03ae00024e4000380617f82244971be60ee3ad0eb2bd769d3934e466963416fa2bc1f480a88ab2b9af4a16b6475135eb05141aeb6b7e40fe94fa000203e8b50000000000000000000003242165830aa3e183632023f82082c684b9800000011c2cb0a71ed4d3b3a16618a20c0023ed3ba1a42d913c20222a465fd88e4f34a4869ad0dda745a80c07117bc0a201fe753102296e2932102b3c4b3216bcf6fa7d800000003db8000d239c5e8eb021e1bbb2e27b9251800031cab040000019a9a427c85161d22b660a0a0ec9ed00000000034000233e49d0000caba324f4e8ecac1d2ac2c07b3f8cff8000a85304eb3bbb7447c80000002b8825c200e2d99cee713a636dcdbccab5f9946000213ac83178c9bd37340000000000392e5f62858b9729409628d688be3c5826889f4b9c00000003430ac08000599887ee2080008462ff88a9a17c94c8000ad592821b2955e0ec9ce0244a3362141af800018bce03a26236b9de4db5977cb4690bce878058031bb866143cc46860000f5b8f5ad248000548097e74c027ae69143c5fc000
  | 65 => 0x4eba40d9aa45a20c19c2ccc43592b856039c22f72d425a900001399280ac900005558a380001e420003df401e937cb8d117ad96015293680003d42f967478e9805f3d62000385ca208eae612b2321dc9c8400000000001c5c59429b68d40c4c8bab12e000000090e30c42ebbc4e00037ca5d2b34c1ad9804000104a8a394e8574a102634a602ad3308491aa9363ebbbd40ef8736b7715c069d9bc09d3326a6eab36a686ba108518dc4008b6a8f5f8216472b836e9985b4ea423c281c2e6000009985a9911ebcc99822858000c8d94cabbdb6768c5bdcc9de3c3c9f12ee8f368cb62d416c4c3f876ac2c04804ad000053625423ea8000000103af1f01c8f2b89a66c0a3ca531800007e30b8ced1b0aaff3b52f31af6e9f41d466a109ea0003b7200006a20d01c548481146020108c0003a7a0003e0a6ab0000b290000000000092880008680000b47086ec3aacdcf3300000003b5c89e800039e9ab4b2b9b785610000959854c00000000000000000174c4800000dc000006c338c2000329800025ca0002efc0002d801473be20001eca67f8000cb20000b2aa14ab9ea468710001ae4e2406eef3808cc936ecb2e1896041ab082d09eb28aa9ec647f098a6b1313433d036430a96febfa2398345b256c6c056e07e976ce041e30d69bc8636ea4220a1baf809ca254e2f0e0c0682246e518f3ca51aaaeded1154f59bba44cc1a50ae43ad8e669d18d9837ee441126a85d1470af29a0c524a3e4c469646c7aa2d8a9e1b54278a0f6968015c68d3be494280ea452adc8c918f7011ba79a67a3778a7e9c3696f9ed079c85541093a2c3bc24f2c6625fae1995ce39b8314d45831e0aa810885734a2c25252e0ae159c87300f6905096c7522e58d441bb82e63a941302062ca533fc02183ac97d0232b2a350cc3e9f6e68d8e4652197b0583274087d181e8061938aa6353e04131223f18390c430f2ed5a2fdc1ab90a078ab0f886c90363c28960d9bba846c612ca25000fe9c2acc2b7330348aa289cf88abe6327b99c87b1c7a7b7137e1a73748821155c110252c0bfb73a177372e0339728f3bb900253b382de4269e62fa34cdbf37762bcac5a975061ae5680728e6ba3eae50f16669a88e53437607be27f82bd27ccd5ead60eff3c8427e94823061a1c25a2a1875d2772da1320ada090869f229e823c3ae0d92308851823964913bcc7819aa2c808000640861cb10194a0003d420d8930000036fe7f90e845b025f61ce299a0e7151858b22fcd9c8c262431b9862e9fde61ca0be4f18fea0001e8ea34b96089aa59adee26c20000c6841482b23cab586d0e28a8000000003602fa903bb30044bbee5ab0000000000000019be00000000001ffc0001fc07bf00000000000a5a800032b85149c42baa81f985a0001156ce288526531050cc0044ca6c0f849b7229010
  | 66 => 0x6064d06183b0838849580000003206aee3824d9980ec2ac919894e0000000000000000009ebab763583d060001474000000079307eae8c00002c6229206c81800002874c278000f281adccc736c0c5b327cdd5a3206b08c7cbc38000b3cb5745808fd21ec83a8c0230b2e033a6836b07ba73303a6f38376ca4a3992cb818e87b0205467b010ce191e18ba100e40003612d902a267ea01346e28d2c00025e8cde0cc82263c624999e8804280009191d1a9bb0000af7bdc23718000ef10d2a358af9ea9a2744000375272f905c22ea1e4824ac380f49e4400027deecfb7ea738a7264f98c060002c64af1bd4c85eb5dee591e3a3740ff02c0aff68d70000eba809c8a000001c3800078a32aa87a3d368e78000750801ca4e32cc0dfb9f689d00d0e5c261aa972390a6f385a201b8c626e18648138374d700b1053f8988c922df4d7709bea0e1570955829e9763d3e4f7a27002b229c1fc2880dc425084aba1381ed23ee407991e2e4bd90648a4440230cd4f74120c08b83e84e70ffc3e534106f3b5aa9919516c75ac0add09e7a8e13876d01ac801e202a200000002f49cf027a2866ba68b6a6fa8046c0f23d0adca9fc000125479380000001caef1a0e26000360800024b0ad40000000148841f0000000000062e2b3400000008ea800092e00009200000960800000026066103278c621332cd980006ea0000b66823a9ac3cf0a02197c0000000490248e9208e8850094e2af92dec00037a8acaa9786138000a3cb52a5e982420000c84d0380007abbc7a8350000958161071f8b7c00024a600029acf26000000000005f4292ef8183780002664abbbb540e02eb86720f36a790000ef4a45ae5002703d933ac39e1c26f0c02a869bb21812d0794200363466c8000a3c386a63aa3868c4087c41a14f600000006da8dd4bcc1a740000000d992f7418a8b36e5388483b03762b992dd64d420c80db056800000002cb8000b048000a408000e0b0000b500000acb29fe2132e2600020025efa0dc01a88920002b683b49cd2615a4a0d46205600039e4a4980000001bb030899b41241f1e2458000dbb92ce20611922e817f41de09f662295e81dc000083d0000ad93b6ef5b17de22e0000c59b5da8ce1a706ac80000000a08e390f760000bd6887a2380001f68000000000000005c41246998075058600008b0893eec891d20000000a0b0000433000000000008b8800000035d4b098000b7e390865baade5288000c0480000001eb0571146aa1000f87118000d818000e45a83c88f2a10d0517ae06134ae0000000edda6f20000000da30000f4f0000904afa6de0874e61a95ca2f0bc36775b6e48858676bdcb228e02bd8409fbd602a1000089e212e00000008d024ce783b91eacb9b284363798a1f000078b9e5e35400260002ce25658000a84a3a2d0a84
  | 67 => 0x8940000000391203d110e0000000d222da0000220400011844cf00005699c8a000302000034744c39db279a8a30ccb0000a9929eeab198982b6998c1b5a2ae649aab20001d345770e02f0b119e18ebe00ef9800076337668a6800000011c00000aa8a2bb8123260fc42ae80000002d020d6000039c00009c931365f48b7275903baf103bc289a274a0002a1e00027806a5bab4ec8000026b975693d000098a28ec0000562a8f9d3cf0e8000c47800082703481c582d26452ad805637ec9092ffc72f080ed11a7a8e3b3ae8db8bb46ea61d6aa52b3e01750f88d180e1050e0b4c9070ef8f839e7e3c4872c8289f2af7a3116162ac1ed6e36d45312f4ce128156c25a494d7413288068000afcbbd67ccaa2cd120000b78a2187611558d869096e6b000095c1418b97a54668000004588e5a6d78000032b590af83c0c80280009fe8ab40109e846908e5246f9dd4564867aa451c0e5ceb3cae601a08a2b32b05f21b803f90e9e9f804e22fba3ec0000000dcf055634f97848e3883cccea7e400000000000ef28b78d9caa716321f82d0c00000009d18696000132e88a8d8a46bae940001d503e01c0ad348000d1027ba71e38223eea930bda9a024f59f4645a97e82f41dee117a0124bd8c9ae7f12a828d9d20b2598d6afe3d129ba94d4000190c2643750c9d8000c6b9a62754800047a3162202a5da7e4842c00000000000000ab20000bad3c6e0000000c55000011b1828b623aee9249e789c680001e2a64ccc60d66a6bae240001ee2512b3ecc47301c7a6821a0001c3492baff43f7800000018b60
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87c8754965040074e902a92ca080028fa1052594100051ec20a4b282000a5e8314965040014bb06292ca080030fdd274594100061eba0e8b282000a3e849cd650400147b0939aca0800317dce73594100043f43c86b28200087d8790d650400147f08b92ca080028f21172594100053bc0ae4b282003a74815c9650400147d08392ca080028f61072594100052f418e4b282000a5d831c965040010ff0ea12ca080021f21d42594100053bc0a84b282003a748150965040010fd0e212ca080021f61c42594100052f41884b282000a5d8310965040014ef02992ca0800e9d20532594100043f43864b28200087d870c9650400147d08192ca080028f61032594100043f43860b28200087d870c1650400147d08182ca080028f61030594100053741060b282000a6d820c165040074ed02182ca080029d60430594100043f43e40b28200087d87c81650400147d09902ca080028f61320594100052f41e40b282000a5d83c8165040074ed03102ca080029d606205941001d3b40840b282000a758108165040010ff0ab94c80801e1f215729901001d5a40a85320200087f855c9640400f0f90ab92c8080923de05725901001c7a40ae4b2020038bc87509640400756902a12c80800e1fe1d65950100051fc22cb2a0200387c87595540402347908b2aa80801e1fa177458c100043ec2ee8b1820038f4815c963040071b90e992c60800e1f21d6554c1001c5e43ac8a1820038dc8758d43040078ece2b2ca0080023de1971940100063ab2ae3280200387c85dd950040018b8e6b2aa00819b0f99774540100061eb2ee8a80205ec3e651d1500400187aca3a2a00815b1799773540100062eb2ee6a80200387d855d8500400f1eb02bb0a00800f1d9c5651401003e3b32ae22802000c75655c450040078ece2b2c800800f2d9c564900100063ab2ae3200200087e87995400400f0f90f32a8008003171ce65500100043f43acaa00200087c8759540040018b8e6b2a80080031799773500100062eb2ee6a002003c767159440040018eacab88800800f1d9c5658c01001c6fc3ac718020008f7865c630040018eacab8c60080021fa1e654c01003c3e43cca980200087e8759530040010f90eb2a60080030f997744c0100061eb2ee89802000c3e651d1300400187aca3a26008003391cb76440100063bc2eec8802000c7485dd910040018eeedbaa20080031ddd87544010006b2390ea8802000a768759510040014e90eb2a2008003991c9654401001e3bb82ca8802003e7370595100400196eedba220080038d59774440100065bbb0e88802000e35651d11004001b48e43a2200800335ddb73440100072ab2ee68802000cd7761cd1004001caaca39a2008003711c8734401000673bb6e48802000e6565dc910040019e6ed28220080033cdd95044010
  | 1 => 0xce3b10a0880031dd95711411003e3a32ae22822000cb7645c45044001968c8b88a08800335d8d71141100066a31ae22822000ce7625c450440019c8c4b88a0880025d61e511411026e3b3b4a2282200087f855d9404400f0f90abb2808800237e0d76501100146e41aeca0220008ef825d940440031d904bb280881321fa1b75501100062e31eeaa022000c6c62dd5404409b0fd0c3aa80880031718c755011000636310eaa02200087e87d95404409b0f90fb2a8088003171cf65501100043f438caa02200787c8719540440018b8e632a80880030fdd764501100061e3aec8a022000c9c73d914044097968e3b2280880030fdd464501100061e3a8c8a022000c9c7319140440911bd0db9a808800317d9773501100062e32ee6a022000c9f64dcd4044001938c9b9a80880033318b73501100046f43ec6a0220498dc87d8d40440018beebb1a8088003171d7635011000637baec4a022000c6c75d89404400199ee7b128088003331cf625011000672316e2a022048cd6768c630440990fd0dbaa60880771718f754c11000636316ea982204d87e861d530440338b8c63aa60880031b188754c1100cc3f43eca982204d87c87d95304403b0fd0e32a608801e1f21c654c1102545f436e89822000c3f65dd13044001878cbba2608805b2718f744c11000656316e8982204b8be861d1304400187eca3a260880030f194744c1100864e318e89822000cac621d1304402117d0fb22608812e2f21f644c1100061fbaec89822000c3c75d91304402d17d0e32260880462f21c644c1100061fba8c89822000c3c7519130440018beebb1a6088003171d7634c1100064fba6c69822000c9c74d8d30440939a8e3b1a60880031bdd7624c110006363aec49822000caf74d893044001958e9b1260880033918b714c11026e3b3b6cb082204de7360d96104400f8ecec32c208800399188658411025e5b3b6c90822011cb6761921044001d48c4324208800a3da1b7384110004bbc2ae70822049cd676d8e10440059acec31c2088003b1188638411023e733b6c5082200787e8790e65040010fb0f21cca080021fe1d429941003c3e43a853282000a778150a65040074e902a14ca0801e1fa1c42994100043ec38853282000a5e8310a65040014bb06214ca0801e1fa1c32994100043ec38653282000a3e840ca650400147b08194ca0801e1fa1c30994100043ec38613282000a3e840c2650400147b08184ca080029ba08309941000536c10613282003a76810c265040014eb02184ca0801e1fa1f20994100043ec3e413282000a3e84c82650400147b09904ca0800297a0f20994100052ec1e41328200387e8794d650400147d0929aca080028f61253594100062fb9ca6b2820008bf845c9650402317908b92ca0800e3d205725941001c3f43ca4b282003
  | 2 => 0xf31d89100053742e63b122000a6d85cc7624400155d0998ec488002ab61331d89100047743861b1220088ed870c362440014dd0a186c4880029b61430d89100055742061b122000aad840c3624408f5cd02186c4881371d94676d451001d3a40ecba8a204be3651d935144095c6ca2326a2881279594763d451023f3328ec5a8a2007c78659c3514409bae4a3386a2880033918a769451003d3b436cb28a2000c7676d965144001cc8c432ca2880038d19764945100071a328c928a2000ea4621925144001ca8cbb1ca28800395194639451000762310c728a20b397587d4e51440014e90ca9ca2880039919762945100063db28e0a8a2000e64621955144001d48c4322a28801f1d1da545451003e3a3b0a8a8a200397585dcd5144089aaca7b9aa288003b11886354510266b9ba8e0a8a2011cb8649c34144023968823b282881378d10765505100065db20e0a0a2000ce4629da3144089aa8c6bac628800359189758c51001e3bb02eb18a2003d73605d63144001ae440bac62880035c481758c510004bbc3ecb18a2000e5463d9631440012eb0e32c62880039518c658c51000732310cb18a2000d3575d923144001d28c7b2462880034d5d4648c5100074a318c918a2000ea46219231440055ad0db1c6288003359db638c510006aabaec718a2000d6575d8a3144001d88c7b14628800e3da1a708c5100066db18e098a20008f4865d531440018e8edb2a62880039518f654c5100063a3b0ca98a2000e64621953144001968edb2262880032d1d8644c51000752310c898a2009cd476d8d31440019c8edb1262880025d614704c510246e9b98e098a2007a748654750440998eced28ca0881369ea1b50941100071db26a12822000e5b63d42504410dcd0c5a84a088136dca0750941100045fc22eca8220118bc845d950440011bf06bb2a08800a3720d765411000477c12eca8220018ec825d950440018b8e7b2aa0881371d1c765541102545f436e8a822000c3f65dd150440cd878cbba2a0880032718f745411000656316e8a82204b8be861d1504400187eca3a2a08817b0f19474541100064e318e8a822000cac621d150440bd17d0fb22a08812e2f21f64541100064e39ec8a8220668be8719150440231790e322a088003271cc64541102446f436e6a822000c5f65dcd50440ad8b8cbb9aa08800327d9373541100064e326e6a822000ccc62dcd504410b1bd0fb1aa0881263721f63541100064fba6c6a822000c9c74d8d504400195ee9b12a0880032b1d3625411000667b9ec4a822000ccc73d8950440018eecbb8aa0880033918b715411001cba43aa2a822007a74865455044001a68e8a8aa088113551cd5154110005b8402a2a8220038f4819d8504409b8ece3b28a08812f2d9c764141102565b388c82822049cd671d8c504408f9c
  | 3 => 0x431a2000ec6711886344001d8ae2310c688003b26006218d10007643144031a2048ad8864806344001d90c4900c6880031794e76d4d100143e42aeda9a20008bf845db534402317908bb6a6880023be0976d4d1000c76412eda9a2002a5c83d975344001c3ca7b26a6880038794c64d4d100052ec2ec7a9a2049cd671d8f534400f1e90cb8ea68800335d8d71d4d1000672312e3a9a20118be84dd9534400117b09bb2a6880063ba0b7654d1000476c16eca9a200087f855d9534400117f08bb2a6880462f2117654d1000477c12eca9a20018ec825d953440050fd0fb2aa68801e37a1f6354d100043fc2aeda1a200787c855db434400517908bb686880023be0976d0d1000c76412eda1a200787e85dd943440010fb0bbb286880063ba0b7650d1000476c16eca1a200087f855d9434400f0f90abb286880022fe117650d1000477c12eca1a20018ec825d9434400517d0fb22868804637a1f6350d1001c7d436e0a1a2000c7865dc143440019d0c5b8286880031e1947050d100065db20e0a1a2000cdb631c143440019d0c438286880031b9db65d891000476c3ccbb122000a6e85997624400155d0932ec488002ab61265d89100056741ccbb122000acd8399762440011df0eb2ec488002abe1165d891000556422cbb122000acf83597624400159906b2ec4880029ba1865d8910006373b0cbb122000e6581197624400195cedb26c4880038bd9764d89100071632ec9b1220008ed8799362440014dd0b326c4880029b61664d891000557424c9b122000ace83993624400159b07326c4880023be1d64d891000537c2ac9b122000a6c85593624400159f06b26c488002b320d64d891000557430c9b122000cae761936244001c5eca326c4880038b19464d8910006673b6c7b122000e4f65d8f6244001c98cbb1ec488003a3d9363d891000746326c7b1220008ed8798f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f624400159d0731ec4880023be1d63d891000537c2ac7b122000a6c8558f624400155f08b1ec488002ab21163d891000567430c7b122000cce7618f6244001c9eca31ec4880039319463d891000747b20c7b122000e8c6418f6244001d8b0231ec488002aba1275d891000556c24ebb122000ace839d7624400159b073aec48811eb9a0475d891000572c08ebb122000a6e85dd362440014db0bba6c48811eb9a0774d891000572c0ee9b122000a6e859d362440014db0b3a6c488002b3a0e74d891000566c1ce9b122000e2f5495362440014dd0b39ec4880029b61673d891000557424e7b122000aad849cf624408f5cd0239ec488002b960473d891000557424a7b122000aad8494f6244001c9ea729ec4880029ba1643d891000536c2c87b12203faea80dc762440011dd0f98ec4880023b61
  | 4 => 0x34400153d09396c688002a761272d8d100056d400e5b1a2049ad9801cb63440011bd0e296c6880023761c52d8d100054f420a5b1a2000a9d8414b63440014bf0aa16c6880029721542d8d100056bc0a85b1a2049ad48150b63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b63440014bf0ab8ec6880029721571d8d100054fc22e3b1a2000a9c845c7634400159f04b8ec688002b320971d8d1024c6f43e41b1a20008dd87c8363440014bd0b906c6880029761720d8d100054f42641b1a2000a9d84c8363440018b8c7baac6880031718c7558d100043f43ecab1a2000c6c72d9563440010fd0e32ac6880031b1c86558d100061fb2ee8b1a2000c3c65dd16344001938c7ba2c6880030fd947458d100061e328e8b1a2000c9c631d1634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac7219163440031dd0db92c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880033318f7258d1000637ba8c4b1a2000c6c75189634400195ee8312c6880032b1d06258d1003c3f43eeab1a20118be87dd1634400187eebba2c6880030f1d77458d100061fba8e8b1a2000c3c751d163440018beebb9ac688003171d77358d100064fba6e6b1a2000c9c74dcd63440031dd0fb92c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c68800333dcf7258d100043fc2ae4b1a200787c855c9634400117f08b92c6880462f2117258d100046fc1ae4b1a20008f7815c963440011dd0e392c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d1000672396e2b1a2000c5e76d946344001caae3b28c6880023761e6518d100052f42cca31a2000a9e84994634400153b09328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440014bd0c328c688003179d86518d100072ac08ca31a2000e5571194634400193cedb20c68800387d976418d100070e32ec831a2000e9571d9063440011bb0f320c68800297a166418d100052ec2cc831a2000a9e84990634400159d05320c688002b360a6418d100046fc3ac831a2000a5f8559063440014b90ab20c688002b3e096418d1000566412c831a2000a9e86190634400193cec320c68800387d946418d100070e328c831a2000e957119063440011bb0f310c68800297a166218d100052ec2cc431a2000a9e84988634400153b09310c68800237e1d6218d100052fc2ac431a2000a5c85588634400153f08b10c688002a72116218d100056bc0ac431a2000e4f651886344001c98ca310c688003a3d906218d1000746320c
  | 5 => 0x8003aa18a20191102555c432403222011c3f759d4644400147d0b398c8880028f616731911008c5f43ca632220008bd8794c644400147f0ab90c8880028f21572191100055bc0ae4322204aab4815c8644409556d03a90c888002ad607521911008c5f438a432220008bd87148644400153d06290c888002a760c52191102555b40e643222000ab581cc8644402317d0e190c8880022f61c32191100051f428643222000a3d850c8644402317d0f988c8880022f61f31191100051f42e623222000a3d85cc4644400155d05988c888002ab60b31191100051fc2ae03222000a3c855c0644400153f06b80c888002a720d701911008c5f4386032220008bd870c0644400147d0a180c8880028f614301911000557410603222000aad820c0644409556d02180c8880462fa1f20191100045ec3e403222000a3e85c80644400147b0b900c888002a7a0f20191100054ec1e403222000ab781480644409556902900c8880028fe1510191100051e42a20322201187c855db54440011bf06bb6a88800a3720d76d511000477c12edaa220018ec825db544400147b0bb26a88812f2d9c764d511003c7a432e3aa22000cb7645c754440019c8c4b8ea8880462f21176951100046fc1aed2a220028dc835da54440011df04bb4a8880063b20976951100051ec26cb2a22000a3e86d52544400f4790daa4a8880030f9db549511008e1e3b6a92a220b2e1c63d525444163c58c5aa4a88800a37a0f76551100046ec1eecaa220018ee82dd954440011db05bb2a88800237e0d76551100146e41aecaa220008ef825d954440031d904bb2a8880461fa1f655511003c5f43ec8aa220008df835d854440051b906bb0a8880023be09761511000c76412ec2a220118f4865c45444023968c8b88a8880022fe1175d8d1008c5e422ebb1a200087f855d3634400f0f90aba6c68800637e1d32d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100072ac08cbb1a2000e1f65d936344001c38cbb26c68800297a1664d8d100052ec2cc9b1a2000ace82993634400159b05326c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c68800387d9464d8d100070e328c9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000a5f8558b63440014b90ab16c688002a7e1162d8d100054e422c5b1a2000e4f6518b6344001c98ca316c688003a3d9062d8d1000746320c5b1a2000ec98018b6344001d90c5106c688126b621920d8d100054fc22ebb1a2000a9c845d763440018baea3aec688002b560475d8d1024d6cc06e9b1a2000a5f855d363440014b90aba6c68800387d5254d8d100052f42ce5b1a2000a5d859cb6
  | 6 => 0x51ec2ce5b222000a9e839cb644400153b07396c888002aea0072d911025d5cc00e5b2220008be8714b644400117b0e296c888002a7a0c52d91100054ec18a5b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b2220008be87cc7644400117b0f98ec8880028fa1731d91100051ec2e63b222000aae82cc7644400155b0598ec8880022fa1c30d91100045ec3861b222000a3e850c3644400147b0a186c888002aba0830d911000556c1061b22204bab6810c3644409717d0f906c8880022f61f20d91100051f42e41b222000a3d85c83644400153d07906c888002a760f20d911008e1e324eb3222011c3c645d664440018bce7b2cc8880031b9cb65991100062f398cb3222000c6e72196644400187cebb24c8880030f5d764991100064f39ec93222000cae72d9264440018becab9cc8880031719573991100064fb22e73222011c9c645ce64440018decab94c8880031b195729911000657b22e53222011cac645ca64440018dcea314c8880031b5d4629911000667398c53222000ccd7318a64440010fd0fb2ac888003171cf655911000636396cab22200087e8719564440018b8e632ac8880031b1c865591100062fb2ee6b222000c5c65dcd64440018decbb92c8880031b197725911000637ba8c4b222000c6c75189644400199ee6312c888003331cc62591100061fbaee8b222000c3c75dd164440018beebb9ac888003171d773591100064fba6e6b222000c5f751cd64440018b8ea39ac88800327dd0735911000637baee4b222000c6c75dc9644400195ee9b92c88800333dcf72591100066639ee4b22200087f855c9644400f0f90ab92c8880022fe1172591100046fc1ae4b2220028dc835c964440011ef02b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc725911000672396e2b2220008bf87590644400147f0ab20c8880028f21564191100054fc1ac83222000a9c83590644400155f04b20c888002ab20964191100051f42c863222000a3d8590c64440010ff0ab90c88801e1f215721911008c5e422e432220038f4815c8644400147f0aa10c8880028f21542191100055bc0a843222000c3e76d94644400117b0f328c888002a7a0e65191100054ec1cca3222000aae82994644400155b05328c8880022fe1d65191100054fc1aca3222000a9c83594644400155f04b28c888002ab20965191100061f3b0ca3222000e3581194644400147d0b318c8880028f616631911000557414c63222000aad8298c644400117b0f310c8880028fa1662191100051ec2cc43222000a9e83988644400153b07310c8880022fe1d62191100051fc2ac43222000a3c85588644400153f06b10c888002a720d621911000717b28c43222000e2c651886444001d5300310c88
  | 7 => 0x3f751d165440018beebb9aca8800327dd373595100064e3a6e6b2a2000c5f751cd654400193ee839aca88003271d0735951000637baee4b2a2000caf74dc96544001958e9b92ca8800333dcf72595100066639ee4b2a200087f855c9654400117f08b92ca880462f21172595100046fc1ae4b2a20028dc835c965440011ef02b92ca880031bdd4725951000657ba0e4b2a2000cac741c9654400199ee6392ca88003331cc725951000672396e2b2a200087f87594654400147f08b28ca880028f21165195100052fc1aca32a2000a5c8359465440014df04b28ca880029b20965195100051f424c632a2000a3d8498c65440014dd05318ca880029b60a63195100043ec3cc432a2000a3e84988654400147b09310ca8800297a0e62195100052ec1cc432a200087f87588654400147f08b10ca880028f21162195100052fc1ac432a2000a5c835886544001cd300310ca88003991897119510007343144032a204ca7886480654400f0fd0f218ca880021f61e43195100043fc3a8432a200787c8750865440014ef02a10ca881329d205421951003c3f4388432a200087d8710865440014bd06210ca880029760c42195102653b40e6432a2000a7581cc8654400f0fd0e190ca880021f61c32195100051f4206432a2000a3d840c8654400f0fd0f988ca880021f61f31195100051f4266232a2000a3d84cc465440014dd05988ca880029b60b311951003c3f4386032a200087d870c0654400147d08180ca880028f6103019510005374106032a2000a6d820c065440994ed02180ca8801e1fa1f20195100043ec3e4032a2000a3e84c80654400147b09900ca8800297a0f20195100052ec1e4032a2000a778148065440994e902900ca880028fa1643d91100051ec2c87b22200787e85dcb64440010fb0bb96c8880023d60772d911000c5fc3a85b222000a3f8550b64440014790aa16c888002ade0542d91100051f42885b222000a3d8510b644400153d06216c888002a760c42d91100054f41ccbb222000a9d83997644400155d0532ec888002ab60a65d91100054fc1acbb222000a9c83597644400155f04b2ec888002ab20965d91100071ac08cbb222000a3e8598f644400147b0b31ec888002aba0a63d911000556c14c7b222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b222000a3f8558b64440014790ab16c888002a7e0d62d91100054e41ac5b222000e2f6518b6444001c58ca316c888003aa60062d91100075431441b22204bab886483644400187aea3aec888002ad60475d911025d5cc06e7b222000a3e851cf644400147b0a39ec88812eada0473d91100055ac08e7b2220008be8794f644400117b0f29ec8880028fa1772d91100051ec2ee5b22204bab681dcb644400156b03b96c8880028fa1672d91100
  | 8 => 0xe4a96cb081369d20552d96100043fc3aca32c200787e85dcb64840010fb0bb96c9080062fe1d42d921000e5739285b24204bab48150b64840010ff0ab92c90801e1f21572592100045fc3ac8324204aab481508648400147b09b2ca9080063ba0a765521000476c14ecaa4200087f855d9548400f0f90abb0a9080021fe1574d8e1003c3e42ae9b1c20018df874cb638400f0fd0fbaac7080021fe157258e1003c3e42ae4b1c200287e859db53840010ff0eb2ea7080021fe157654e100143e43acaa9c20028be849db43840df4790ab2687080021fe157650e1003c3e42aeca1c20028bc8759143840db4790ab22870800aa720d6450e1001c7cc30e0a1c204d87f87597518409717f0eb26830812a2fa1e64506100063ab2ae32842000c5c73d95508400187eca3a2a10817b0f19474542100043fc3aca2842007c76655c450840018eacab88a10819a8f21564902102f51e42ac82042011cb6645c440840ad4b90ab1c61080029de1563c42100051f424a7b2a2000a3d8494f65440018bae729eca880029d60653d951000c3fc3aa5b2a2000a3e8414b654400147b08296ca8800297a0c52d95100052ec18a5b2a2000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a2000a3e8498b654400147b09316ca8800297a0e62d95100052ec1cc5b2a2000a3f8458b654400147908b16ca8800297e0d62d95100052e41ac5b2a2000e698018b6544001cd0c5106ca881369e21920d95100073431241b2a2000c3d741d3654400147d0839eca880028f61073d95100062eb98e7b2a204da76811cf65440014eb0239eca880021fa1e43d95100043ec3c87b2a2000a3e849cb654400147b09396ca8800297a0e72d95100052ec1ce5b2a2000a7a801cb654409b4f300396ca880021fe1d42d95100043e43a85b2a2000a778150b654409b4e902a16ca880021fa1c42d95100043ec3885b2a2000a5e8310b65440014bb06216ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca880021fa1f31d95100043ec3e63b2a2000a3e84cc7654400147b0998eca880029ba0b31d951000536c1663b2a200087e870c365440010fb0e186ca880028fa1030d95100051ec2061b2a2000a6e820c365440014db04186ca881369da0430d951026c3f43e41b2a200087d87c83654400147d09906ca880028f61320d95100052f41e41b2a2000a5d83c8365440018bce7b2cca880031b9cb65995100061fb2ce932a2007c3c659d2654400187ecaba4ca8801f0f19574995100062fb2ae732a2007c5c655ce65440018decab94ca8801f1b1957299510006573a0c532a2000cad7418a654400199ce6314ca88003335cc629951000657ba0c4b2a2000cac74189654400199ee6312ca88003331cc62595100061fbaee8b2a2000c
  | 9 => 0x76105300ce2f398ca20a6000c5c655cc414c023938c8b988298043279cc64d413003e2e32ae7a826000c9c645cf504c03b4f50da84a0980038ed9350941300ee2e39ecaa8260108be86dd1504c00187ecbba2a09819b0f19774541300b45f430e8a826000c3f651d1504c0bd878ca3a2a09817a2fa1f64541300b45e43ec8a826016c9c73d91504c0cd17d0e322a0980462f21c64541300864e398c8a826000c5f65dcd504c0ad8b8cbb9aa09800327d9373541300064e326e6a826000c77659c4504c00f8e8cb388a0980032dd9271141300065a324e22826000c77655c4504c00f8e8cab88a0980032dd9171141300065a322e22826019c5e73197404c0018b8cab9e80980472719173d01300cc3f436eaa02601d87e861d5404c0010fd0fb2a80980761f21f65501300ee2e39ecaa02600087e87195404c00f0f90e32a8098067171cc65501300061fbaec8a026000c3c75d91404c02d938e7b2280980030fdd464501300061e3a8c8a026010c9c73191404c0018becbb9a80980031719773501300064fb26e6a026000c9c64dcd404c0334bd0db2c6098077179db658c1300ef2db06cb1826007c5e76196304c0338bce032c6098067969c0658c1300b64f3b6c91826000e1c65d92304c02b1bb0f324609815a97a16648c1300854f424c91826011c9e76192304c001c3eca324609800387194648c1300864f380c91826010e9a70192304c0070fd0f29acb880028fa1253597100062fb9ca6b2e205487e8714d65c40070f90ea92cb8800e2f211759931001c5e422e732620518bd8790e64c400147d0b21cc9880028f215429931001d5a40a8532620038be8790d64c400147d0b21ac98814a2fa1c43593100043fc2ae4b26200787c855c964c40071e902b92c98800e2f21d42593100051e42a84b262001cac7250964c400756902a12c98800e2fe1d64d53100051fc2ac9aa62003cb67159354c40070ff0eb2ca9880028fe11659531008c5f426eab1e20008bd84dd563c400f0fd0bba2c7880021f6177458f1001c6e43a64b1e200287c855db53c40071bf0eb1ea78800297e1563d4f1001e6b38ac7a9e200287d85dd953c40071ed03bb2a78814f1d9477654f100145e422eda1e20038df8758f43c400517b09bb2878800f1ddd77654710286ab29ee6a8e2000975851c131c40990ff0eb2ea1881325de1d51d43100062e39acaa86205ec3e651d150c400187aca3a2a1880034d1d15154310286aa39aa2a86204cc77655c450c400f8e8cab88a18812a2fe1d64d031025c5f43cc8a062000c3c7599140c4001938e732281880030f1d564503100064e39ac8a062019c5e631d530c402193cc63a26188003171d5634c3100064e3a2c69862000a3e8494f65840018bae729ecb080462fa1372d96100045ec26e5b2c200187f8754b65840038dc
  | 10 => 0x32260038f4815c8644c00147f0aa10c8980028f21542191300055bc0a843226000ab481508644c17987cedb28c8982ef870c365191300045ec3cca32260baa3e85994644c00117f0eb28c8982e6aee0165191305c51f430ca32260b7c3e76194644c16dc7660328c8982db870c065191305b71c180ca32260008bd87988644c00147d0b310c8980028f61662191300045fc3ac43226000a3f85588644c0014790ab10c898002ade0562191300055a40ac432260b5abb80588644c02387eeb3a8c8980028fe1572191300051e42ae43226000ab7815c8644c00156902b90c8980462fa1c52191300045ec38a43226010a9e83148644c00153b06290c8980028fa1671191300051ec2ce232260118be87084644c00117b0e108c8980028fa1421191300051ec28423226010a9e83084644c00153b06108c898002aea0021191300055cc004232260118be87c80644c00117b0f900c8980028fa1720191300051ec2e403226010a9e83c80644c00153b07900c898002a7e0d20191300854e41a40322601187c855db544c00147b0bb26a8980462f21176951300051ec26cb2a26000a3e86d52544c00f4790daa4a8980030f9db549513008e1e3b6a92a2600087f855d9544c00117f08bb2a89800237e0d76551300047dc02ecaa2601187e87d95544c00f17d0fb22a89801e1f215761513008c5e422ec2a260568df835d8544c0231b90cb98a89801f17195731513008e4e322e62a2600087f855d3614c00f0f90aba6c298002b560c21d853000578c0043b0a6049c5f639d6614c00187ecb3a4c2980030f196749853024e4fb1ce930a6000c3f655d2614c001878caba4c2980030f9d764985300061ebaec930a6000c3e75192614c00187aea324c2982d32e5c064985300043f43ecab0a6000c6c72d95614c0010fd0e32ac2980031b1c865585300061fb2ee8b0a6000c3c65dd1614c00187eca3a2c2980030f19474585300045f43ec8b0a6000c3f75d91614c001878ebb22c2980032b1cb64585300045f438c8b0a6000c3f75191614c001878ea322c2980032b1c8645853000637b2ee4b0a6000c6c65dc9614c00195ec9b92c2980032b19372585300047bc3ac230a6000ae482584614c0070f90abb6a2980022fe1176d453008c5e422eda8a60008bf845da514c02317908bb4a2980029d60765945300071bb26a328a6000e3464d46514c02317d09bb2a2980022f61376545300045fc22ec28a60118bc845d8514c0010ff0abb6829801e1f21576d05300043fc2aed20a600787c855da414c0010fd0d3ac82980021f21975905300043fc3ecb20a600087d87d96414c00f0ff0e32c82980021f61c65905300061f3aec920a6000c3d75d92414c00187cea32482980030f5d4649053003c3f42eeca0a600087d85dd9414c0010ff0abb0829801e1f215
  | 11 => 0x4c0010fd0e10eca980021f61c21d95300051f42043b2a6000a3d84087654c03b4bd0610eca980029760c21d95300053d40043b2a6000a7980087654c03b0fd0f906ca980021f61f20d95300051f42641b2a6000a3d84c83654c03b4bd07906ca980029760f20d95300061fb2ce932a6007c3c659d2654c0ad93ec73a4ca980030fd95749953003e1e32ae932a6000c3f75dd1654c00187eea3a2ca9800327dd373595300064e3a6e6b2a600087f855c9654c00117f08b92ca980462f21172595300046fc1ae4b2a60008f7815c9654c0071e902b92ca980032e1d370595300043fc3aca32a6000a3f84594654c00147908b28ca980021f61e62195300051f424c432a6000a3d84988654c0010ff0eb10ca980028fe1162195300051e422c432a6000a7781588654c0014e902b10ca980021fe1d421953003c3e43a8432a6000a7781508654c0014e902a10ca9801e1fa1c42195300043ec388432a6019a5e83108654c0014bb06210ca9801e1fa1c21195300043ec384232a6000a3e84084654c00147b08108ca9806697a0c21195300052ec184232a6000a7a80084654c0014f300108ca9801e1fa1f20195300043ec3e4032a6000a3e84c80654c00147b09900ca9806697a0f20195300052ec1e4032a6000a5f83480654c0334b906900ca9801e1fa1772d91300043ec2ee5b2260038f681dcb644c0011eb03b96c8980062fe1d42d91300051fc2a85b226000a3c8550b644c00156f02a16c898002ad20542d91300051f42885b226000a3d8510b644c00153b06216c8982df870c065d91300051f42cc5b226000a3d8598b644c00147f0ab16c8980028f21562d91300055bc0ac5b226000ab48158b644c00187aea3aec8980028fa1772d91300051ec2ee5b226000ab681dcb644c00156b03b96c8980028fa1672d91300051ec2ce5b226016a9e839cb644c00153b07396c8980022fa1c52d91300045ec38a5b226016a9e8314b644c00153b06296c8980028fa1471d91300051ec28e3b2260008be87087644c00117b0e10ec8980028fa1421d91300051ec2843b226016a9e83087644c00153b0610ec898002aea0021d91300055cc0043b2260168be87c83644c00117b0f906c8980028fa1720d91300051ec2e41b226016a9e83c83644c00153b07906c8980470f192759913008e1e322eb3226000c3e75d92644c00187aebb24c8980021fa1f65591300043f438cab2260bdc7b70195644c00187eebba2c8980030f1d774591300062fbaee6b226000c5c75dcd644c0010ff0ab92c89801e1f21572591300045fc22e4b2260008df835c9644c0011ef02b92c89800e3d20572591300047dc02e4b226000c7875dc1644c00117f0eb20c8980028fe1564191300051e42ac8322600087f855c8644c00f0f90ab90c8980462f21172191300047bc0ae4
  | 12 => 0x28f21564192300051e42a843246000ab481508648c02396882b88c9180028f61764d52300b64f39ec9aa460078df865cf548c00147b09b2ca918077179cf659523008c6fc32e72a460008fa809d9548c0010ff0abb2a9180022fe11765523003c3e42aec2a460118bc845d8548c0ad8bea6bb0a91807657e1d65d4e300058e422cba9c601da5f87597538c0018bf0eb2ea71800387e1165d4e300070e422cba9c601f8df865c3538c03f3b70cb86a71821736e1970d4e300b46fc3ac9a1c601699f87593438c0016390ab268718002a761854d0e300b6cd3a4e1a1c60178df865c3438c0018be65baac3180030fdd774586300061e3aee8b0c6000c9f32dd1618c00187eea3a2c3180030f1d4745863000c7743ee4b0c6000c6f75dc9618c0018d8ebb92c3180032bdd37258630006563a6e4b0c600087f855c9618c00f0f90ab92c3180022fe11725863008c5e422e4b0c6000c6f751c9618c0018d8ea392c3180032bdd07258630006563a0e4b0c6000c5f754c9618c00193ee8992c318007331c9325863001e3b30aea30c60008f787584618c0018eaeab08c31800e1fa1676d46300051e422cba8c604995c855cf518c0071ed033b4a3180029d607659463016caec3ea728c6007a7485586518c00117f08bb2a3180462f211765463000477c12eca8c60018ec825d9518c00147908b2aa3180031759773546300045fc22ec28c60118bc845d8518c0ad8bea6bb0a3180021f61f65146300061f3aec920c6016c9e73d92418c00187cea3248318003479d743906300043fc2aeca0c600787c855d9418c0011df04bb283180063b20976506300043fc2aec20c600787c855d8418c0918bcc13ac63180c756982758c6302446fc32e118c6000a3c84596508c0018bacab9ca118076d620f50942300143f43ecaa84601dc5c73d95508c00187eca3a2a11817b0f19474542300e4ecc06e6a84601d95e87d4d508c03f8beeda9aa118003471d353542300043fc3aca2846000a3c84594508c00f8eccab88a1180031d59571142302b6aa29ae22846015c9d76d0f408c0cd4790ab24811800a2fa1f64502300061e3aec8a046016c9c73d91408c00117d0e32281180030f1d464502300864e398c8a04601699e87d0d408c02f93eeda1a8118003471d743502300045fc3ac8204605ea3c85590408c0030ff0ea96ca980028fa1052d95300051ec20a5b2a6000a5d8314b654c00147d09316ca980028f61262d95300051fc22c5b2a6000a3c8458b654c0014ef02b16ca980029d20562d95300061eba0e9b2a6000a3e849cb654c00147b09396ca9807697a0e72d95300052ec1ce5b2a600087f8750b654c0010f90ea16ca980029de0542d95300053a40a85b2a600087e8710b654c0010fb0e216ca9807697a0c42d95300052ec1885b2a6000c75711c765
  | 13 => 0x64e31ae72028016a9e86d8e4050001c38cbb1c80a000b279d863901400070fb28c72028000e1c6518e4050001c76cbb0480a017a8f21542d944008c5e422e4b2880008f7815c965100071e902b92ca200061f21d52594402f45e43a84b288066cba605c354100cd17f0cb80a8200426720d70150402f69c282e02a080028bd84dd5631002117d0faa2c6200030fdd75458c400854f41ea8b188010a9e8315163100010ff0ab92c62001e1f2157258c400047bc0ae4b1880038f4815c963100211790ea12c6200028f2154258c400055a40a84b1880018dc874c9631000517b09b8ac62017a8f21165d4c400849e42ae9a98800287c87595531000147b0c2a2a620003871516354c400069c2a0e0a98800087f855c9611000f0f90ab92c22012a2f21d425844000e5639284b08804aab48150961100031e90e90ac220046ad21121584402f61e2a2eda88805ea3c8459751100952790aba6a2200023be09765444000c76412eca888011c3c74595511000147b0c2a2a2200472d1d1615444008e5a20aed208804bc3e609d6411002117f0eb1c82200030f9d563904400864f39ac72088010c9e7358c411002356f0eb0882200032de1d611044008e5bb92c22088000cb57258441100bd2790ab8082200426720d701044001e3b30aeb1888000c757558631100bd27d0bba2622000a3d21d614c44008e5a3a2c298880118bc845db501000147b0c2a4a02019a2fe1376540402f51e422ca2808007c76655c450100018eacab88a02017b4d15171140400845fc3ac7a008010c9e7358f40100015730daa48020002cea1641900402f49f43eeaa008000c3f76dd5401000187eec3aa802019b0f9807550040084cf43ee6a008000c9f76dcd4010001a38ebb9a802000327dd873500400068fba8e6a008000d1c751cd40100211790eb1a80200030f1d563500400864e39ac6a008000c7b76dd540100018f6ec3aa80200034e1d774500400066dbb6e6a008000cdb761cd4010001ab0ea39a80202fb66dd0735004000c3fc3aa5b2c60018df874cb658c00193e65ba2cb180030fdd474596300061fa98e8b2c6000c3d531d1658c0394b90bb9acb1800327dd373596300064e3a6e6b2c60008bf845c9658c02317908b92cb180023de05725963001c7a40ae4b2c6000c9f744c9658c0010ff0eb28cb180028f211651963003e3b32ae232c6000c75655c4658c0adaa8a6b88cb1801e1fa1772d92300043ec2ee5b2460038f681dcb648c0011eb03b96c9180023ea0372d923000c5fc3a85b246000a3c8550b648c00395ce4a16c918002ad20542d923000c6fc3a65b246000c5f32dd5648c001878ebba2c91800317dd773592300062e3aee6b24600087f855c9648c00f0f90ab92c9180023de05725923001c7a40ae4b246000c5f754c9648c00117f0eb20c918
  | 14 => 0xc639db435000187cedb2e86a00038718f65d0d400061f3b0cba1a8000e1c631974350001c386032e86a000aa7a1b63d0d400064f3b6c7a1a8000e1c65d8f435000517d0d38686a00030f19670d0d400b64e31ce1a1a8000c7865dc143500018f0ca38286a000336d8c7050d4036d1f436caa1a8000c3c76d954350001c38c7b2a86a00030f1d86550d400070e318caa1a806fc3f731954350001c3e6432a86a0003874c86550d400b54f436e6a1a8002c9c76dcd4350001c38cbb9a86a000aa7a1b6350d400ae4e3b6c6a1a8000e1c65d8d4350001c70cbb8286a00030f1947050d400864e318e0a1a8000e38651c14350001b36e638286a00021fe1573d854003c3e42ae7b0a8000ab58408761500015e30010ec2a012f0fd9275985400062f39ecb30a8000c5e7319661500018becab9cc2a00031719573985400062f3aec730a8000c5d75d8e61500018bcea31cc2a0003175d463985400043f43ecab0a8000c5c73d9561500018d8e5b2ac2a00021fa1c65585400062e398cab0a8000c6c7219561500018becbb9ac2a00031719773585400046f43ec6b0a8000c5f75d8d61500018b8ebb1ac2a0003331cb63585400046f438c6b0a8000c5f7518d61500018b8ea31ac2a0003331c8635854000637b2ee4b0a8000c6c65dc9615000199ec7b92c2a00033318f72585400047bc3ac230a8000ae48258461500070f90abb6a2a000237e0d76d45400146e41aeda8a80008df835da51500051b906bb4a2a00029d60765945400072bb1ea328a8099e5463d4651500051bd07bb2a2a00023760f76545400046fc1aec28a80028dc835d851500010fd0d3ac82a00031718e75905400043e432eb20a8000c5c635d641500010fb0fb2c82a00021f61c65905400062f3aec720a8000c5d75d8e41500019b0c738482a00033618d70905400071bb2a8220a800087f855da315000f0f90abb462a00021fa1a758c54018e2e31ceb18a800087c865d6315005b8b8c6bac62a00021fe1f658c5400043ec3ecb18a800787f8719631500010fb0e32c62a0003179d7638c5400062ebaec718a800787e85dd931500010fb0bbb262a001f0f19674d41400064e31ce9a828007c3c655d35050001938c6ba6a0a00029ea1b50941400072db1ea128280028dc835d950500018b8e7b2aa0a00030fd9774541403361e32ee8a828000c9c63dd1505000187eca3a2a0a017b0f19474541400064e318e8a8280008de86dcd50500018becbb9aa0a015b17197735414042c6f43ec6a828000c9f74d8d5050001938e9b1aa0a00031dd96711414003e3a32ce22828000cd7639c450500019a8c7388a0a00031dd95711414003e3a32ae22828000cd7635c450500019a8c6b88a0a00039619463d01400061f3b6cb2028007c3e76196405002d1790cb9c80a00030f19573901400b
  | 15 => 0x2a10caa00029d205421954003c3f4388432a800087d8710865500014bd06210caa00029760c42195400051f4266432a8000a3d84cc8655000f0fd0e190caa00021f61c32195400051f4206432a8000a3d840c8655000f0fd0f988caa00021f61f31195400051f4266232a8000a3d84cc465500014dd05988caa00029b60b31195400051f4206232a8000a3d840c4655000f0fd0e108caa00021f61c21195400051f4204232a8000a3d8408465500014bd06108caa00029760c21195400053d4004232a8000a7980084655000147d09980caa00028f613301954003c3f4386032a800087d870c0655000147d08180caa00029ba08301954000536c106032a8000a76810c065500014eb02180caa001e1fa1f20195400043ec3e4032a8000a3e84c80655000147b09900caa000297a0f20195400052ec1e4032a8000a3f84480655000147908900caa00468f21365d514003e3c32ce1aa28000a3e86d5254500cd87cedaa4a8a02cb8718f54951400063db28e0aa28000cd8631c1545000517908baec6a000637e1d32d8d400043fc2ae3b1a800787c855c7635000517908b8ec6a00023be0971d8d4000c76412e3b1a8000e1c65dd363500014bd0b316c6a00029761662d8d400052fc2ac5b1a8000a5c8558b63500015af02b16c6a0002b520562d8d400054fc22ebb1a8015a9c845d763500018baea3aec6a000387d5254d8d400052f42ce5b1a8000a5d859cb635002b53d09396c6a0002a761272d8d400046f438a5b1a80008dd8714b635000153d08296c6a0002a761052d8d400052fc2a85b1a8000a5c8550b63500015af02a16c6a0002b520542d8d400046f43885b1a80158dd8710b63500014bd0a216c6a00029761442d8d400052fc2ae3b1a8000a5c855c7635000153f08b8ec6a0056a721171d8d4000567c12e3b1a8000acc825c763500014bd0a38ec6a00029761471d8d400046f43843b1a80008dd8708763500014bd0a10ec6a00029761421d8d400054f42043b1a8000a9d8408763500015b50010ec6a0002b660021d8d400052f42ee1b1a8000a5d85dc363500011bd0f906c6a00023761f20d8d400052f42e41b1a8000a5d85c83635000153d09906c6a0002a761320d8d400062e31eeab1a8000c5c631d563500010fd0fb2ac6a00021fa1c6558d400062f3b6ca31a8000e1d74d9463500011bb0f328c6a000297a166518d400046fc3aca31a8000adb8059463500014bd0c328c6a0003179d86518d400070eba0ca31a80008dd8798863500014bd0b310c6a0002976166218d400054ec24c431a80008df8758863500014bf0ab10c6a0002972156218d400054fc22c431a8000ad78158863500015a902b10c6a0002b6e016218d400062f29ceda9a800287c855db53500054b907b2ea6a00029761763d4d400143f43ecaa9a8016c9
  | 16 => 0x458e400b45f43e84b1c8000a3c85509639000156902a12c72000a1fa1676d4e400b49e42ae9a9c80038f6811d953900011eb023b2a72000a1f21d6554e400152e41acaa9c8000c3d65dd1539017db3086382872012e2fa1f425864025d5a40a84b0c8000a7585085619000156b0810ac320002b560c21586400057940042b0c8003c76615d461900011ef0eb08c3200031d5d5611864001c3f42ceda8c8066c3c549db519000f87ccaba6a32000e3da06769464001e5b30ae928c8000c3d65dd151900078ecc2bac83200031d5d561906400061f3aac720c80168bf8758c41900cd2790ab80832005a6720d701064001c7b40ced18c8003c76615d6319000796cc2ba463200031d5d5618c64003c3f428ec98c800087d851d931900cd27d0bba2632000a3d21d614c6400061eb2ae92848007c76655c450900018eacab88a12019b4d15171142400b45fc3ac7a048016c9e7358f40900cda70eb28681200028f61253d95400062eb9ca7b2a800187f8754b655000147b08296caa000297a0c52d95400052ec18a5b2a8000a5e8398b65500014bb07316caa000297e0d62d95400052e41ac5b2a8000a778158b65500014e902b16caa00028fa1073d95400051ec20e7b2a8000c5d731cf65500010fb0f21ecaa00028fa1272d95400051ec24e5b2a8000a5e839cb65500014bb07396caa00da1fe1d42d95401c43e43a85b2a8000a778150b65500014e902a16caa00021fa1c42d95400043ec3885b2a8000a5e8310b65500014bb06216caa00038b50842d95400043f43865b2a800087d870cb655000147d08196caa00028f61032d95400063ab88e3b2a800087e87cc765500010fb0f98ecaa00028fa1331d95400051ec2663b2a8000a6e82cc765500014db0598ecaa00021fa1c21d95400043ec3843b2a8000a3e84087655000147b0810ecaa000297a0c21d95400052ec1843b2a8000a7a8008765500014f30010ecaa000297a0f70d95400052ec1ee1b2a800087e870c365500010fb0e186caa00028fa1030d95400053741061b2a8000a6d820c365500014ed02186caa00029d60430d95400043f43e41b2a800087d87c83655000147d09906caa00028f61320d95400052f41e41b2a8000a5d83c8365500018bce7b2ccaa000317d95739954003e2e32ae732a8000c5f75dcd655000193ee9b9acaa000317dd473595400064fba0e6b2a800087f855c9655000117f08b92caa000237e0d72595400146e41ae4b2a80008f7815c965500071e902b92caa0003361cf70595400043fc3aca32a8000a5f8359465500014b906b28caa00021f61e62195400052f41cc432a8000a5d8398865500010ff0eb10caa000297e0d62195400052e41ac432a8000a778158865500014e902b10caa00021f61e43195401c43fc3a8432a800787c8750865500014ef0
  | 17 => 0x8a000ae5820c1611400f4ed0b902c2280029d61720584500055b42640b08a000ab584c8161140015ad07902c228002b560f205845003d3b42c40b08a000a7585881611400f4ed0a902c22801e9da1420584500053ac2840b08a007c76815da511400f8eb02bb4a2280661fe1d63944500063b3a2c3288a000c767358651140998e8e6b0ca2281331ddc961944500063ab92c3288a000c75615c2511400f8eceab0e82280031d5d561d045001c3ec2aed208a003c76615d6411400f8eceab0c82280031d5d5619045000477c12eca08a0018ec825d941140018eeeab0a822801f1d1d561504502663bbaac2208a007c747558441140070fb0abb4622800f1d985758c45003e3b3aac3188a000c757558631140010fb0dbaa622800a3d21d614c4500063bbaac2988a007c7475585311400187eedba2a0280030fdd874540502f69b308e8a80a05ed35611d150140bda74c03a2a02806657a1f73540500062fbb6e6a80a000d1c74dcd50140018beec39aa02800347dd073540500068e3a0e6a80a01987c8758d5014001878e8b1aa028067171cd63540502643e43ac2a80a000c3c7458550140018b8e6b0aa0281331d1c561540500063a43ac2a80a000e377458550140018e8e8b0aa0280038d1d161540500061a3a2c2a80a000e577358550140018ece6b0aa0280031d1cd61540500072a39ac2a80a000c547358550140018eee4b0aa0280031d5c9615405003f39b82c2a80a011a3e8494d65d00018bee729acba00061f21d525974000c6e43a64b1e800787e85dc563d00010fb0bb8ac7a00063ba0b7158f4000476c16e2b1e800287c855db53d00010fb0fb2ea7a000a97a0f65d4f400052fc2ac7a9e800287e87d9553d00054bd07b2aa7a012b0f992759874003c3f42ee6b0e800087d85dcd61d00070f90abb6a3a00c697a0f65d47400053bc0acb28e800387e87d9551d005b4bd07b2aa3a00021fe1d651474018e2f31ceb18e8000c5e7558e31d000f0fd0bbb263a00021f617764c7400ed2f41ecb2868011c3c7459550d00018b8e6b2aa1a00021f61f65143400cd2f41eca2868000c77655c450d000f8e8cab88a1a000e3da0772d96400047ac0ee5b2c800187f8754b659000317f0ea16cb200072b9c942d96400043f43ca4b2c8000a3d8494965900018dee5292cb200021fa1c52596400051ec20a4b2c8000a5d8314965900cd17d0fa12cb2019a8fa1742596403351e42a84b2c800087f87594659000f8eccab88cb200031d59571196403369a2a2e232c8066d38549c354900cd47f0eb2ea9200030fe1d65d52402f45fc32e1aa480009bb865c354900bd9770cb86a92019b0fdd165552400043ec3eca2a4800093f8755054900cd878cabb0a9200024f61f65152400059d406ca2a4801699c835c0549002d17d0e2a2c72005aa7a0c5
  | 18 => 0x40014eb0b904c228002ada1320984500055ac2641308a000ad683c8261140015ab07904c2281321fa1e54584500061fba4a8b08a04ca768195161140990fd0f29ac2280028fa1253584500062fb9ca6b08a04ca768194d611400f0f90ab92c2280022fe11725845008c5e422e4b08a04c87c8754961140038d8e4a92c2281329d205525845003d3b42e62b08a000ab684cc5611400156b0998ac228002b9a0b315845000572c1662b08a007a74850c5611400f1ed0f90ac22801e9da17215845003d3a42c42b08a0018f487485611400f4e90a90ac228007391c9215845003d3b42842b08a000ab684085611400156b0810ac228002b5a0c21584500056ac1842b08a000af280085611400f4ed0bba2c22801e9da16745845003d3a42ae8b08a000ae7825d161140015c904ba2c22801e9d21474584500053b43ca8b08a007e36849516114001c6ee92a2c2280038d1d254584500053b41ca8b08a000a758295161140014eb012a2c22801e9da17735845003d3b42ce6b08a000a75859cd611400156d0939ac228002ad612735845000573414e6b08a000ae5829cd611400f4e90ab9ac22801e9d21473584500053b43ca6b08a000a768494d6114001c6d0929ac2280028da1253584500071ac24a6b08a007a768394d611400fcad0729ac22800395dce53584500072a39ca6b08a000a758294d61140014eb0129ac22801e9da1743584500053ac2e86b08a06fe3454d0d611400f4ed0b21ac2280029d61643584500053bc2a86b08a007a748550d61140dbc68a8a1ac228002bce0143584500057840286b08a000a778510d611400f4e90a21ac22801e9d217725845003d3b42ce4b08a000a75859c961140014ef0ab92c22801e9d21572584500055bc22e4b08a000ab4845c9611400f4ed0a392c2280029d61472584500055b420e4b08a000ab5841c961140015ad06392c228002b560c725845000672b90e4b08a000af2801c961140015e300392c2280029d21d52584500053a422a4b08a000a7483549611400f4ef04a92c22801f99e09525845000733b92a4b08a000e647254961140014ef00a92c2280029de17425845003d3a42e84b08a000e3654d09611400f4ed0b212c2280029d61642584500047bc3a84b08a0008f48750961140014ef0aa12c22801e9d21542584500071b2a284b08a007a768510961140014eb0a212c228002b5a0c42584500056ac1884b08a000a7785cc9611400f4e90b992c2280039594f325845003d3b42c64b08a000a75858c961140014ef0a992c22801e9d21532584500072b29a64b08a007a76850c961140014eb0a192c228002ada1032584500055ac2064b08a007a7485cc161140011ed0e182c22801e9da1430584500053ac2860b08a000ab6840c1611400156b08182c2282179514c30584500057341060b
  | 19 => 0x32b1cb64585500045f438c8b0aa000c9c731916154001958e4322c2a800327d9373585500064e326e6b0aa0008de87d8d615400193ee9b1ac2a8003271d3635855000666396c6b0aa0008de8718d615400193ee831ac2a8003271d0635855000666390c6b0aa000caf64dc96154001958c9b92c2a800333d8f72585500066631ee4b0aa0008f78758461540015c904b08c2a80030f9db64d45500061f3b0c9a8aa03187c865cf5154001878c8b9ea2a80c71718d73d455018d2f436c7a8aa000c5e76d8f5154001c38c9b1ea2a8003179d863d45500070fb20c7a8aa000e1c6418f5154001878c9386a2a80031718e70d45503371ba8ec928aa05ee375119251540adcaea3b1ca2a817b8ddc464545500043f436e6a8aa000c3c64dcd515405b8b8c7b9aa2a80b697a1b63545500070e326c6a8aa000e1f6418d5154001c38c831aa2a80038d19361545500072a31ec2a8aa000c3c641c151540018b8c6382a2a800237e0d76d05500146e41aeda0aa00387c859da41540011bf06bb482a800a3720d76905500062e31aeb20aa066c3e75d92415400187aebb2482a817b0f9d464905500061eba8c920aa056c5e75d8e41540018baebb1c82a800a37a0f76505500046ec1eeca0aa003ab681d9141540011bf06bb082a800a3720d761055008e1e322ea20aa000c5c635d441540070f90b3b462a80022fe11768c55008c5e422ed18aa02dc5c635d631540cd87cebb2462a80030f5d7648c5502f61f3a8c918aa000c3d7519231540ad8bcebb1c62a8003175d7638c55008c5f426ec98aa0008bd84dd9315405b8b8c6baa62a817b0f9d4644c5500061eba8c898aa066e3b60d92505400f0f90cb9ca0a80030f19173941500ee2e31ae7282a01da5e86d8e50540398bcedb1ca0a80038719363941502b72db06c7282a002c5e7618e5054001c3ec831ca0a800387190639415003c3e432e3282a000c3c645c650540018b8c6b8ca0a81371d18571941500047bc0ae5320a0038f4815ca641400f4790aa14c8280e21fe15725905003c3e42ae4b20a0008f7815c964140071e902b92c8280062f21d42590500143ec2ee8b18a01987e87951631400187ee92a2c62806697a0e5458c5003c3e42ae4b18a01987c8754963140031b90e992c62800a1f6177158c500cc9e422eba18a0028bc8759143140dbc38a8b1a86280034e1507050c5003d3b42c87308a000a758590e61140011ef0ea14c22800e3d21d42984500053bc2a85308a007a748550a611400f4ed0a214c2280029d61442984500056b41885308a000ad58310a611400f4ed0a194c2280029d61432984500055b42065308a000ab5840ca61140011eb0e184c22801e9da1430984500053ac2861308a000ab6840c2611400156b08184c228002b9a08309845000572c1061308a007a7685c82611
  | 20 => 0x5ac0860322a0118be87c80645400117b0f900c8a817a8fa1720191500051ec2e40322a000a9e83c80645400153b07900c8a80028fe1520191502f51e42a40322a011cb8649c25454001976c8382a8a80033618c70551500143e42ae9b1aa0018df874cb63540050f90ab8ec6a80022fe1171d8d5008c5e422e3b1aa0008ef825c763540031d904b8ec6a800387dd464d8d500054f424c5b1aa000a9d8498b635400153f08b16c6a8002a721162d8d500056bc0ac5b1aa000ad48158b63540014bf0aba6c6a80729721574d8d502b70faa4a9b1aa01ca5e859cb63540014bb0b396c6a8002a7a1272d8d500054ec24e5b1aa000a5f8550b63540ad4b90aa16c6a8002b5e0542d8d500056a40a85b1aa0008de8710b63540011bb0e216c6a815a97a1442d8d500052ec2885b1aa000a5f855c763540394b90ab8ec6a8002a7e1171d8d500054e422e3b1aa000acf825c7635400159904b8ec6a80029761471d8d500046f43843b1aa0008dd8708763540ad4bd0a10ec6a80029761421d8d500054f42043b1aa000a9d8408763540015b50010ec6a8002b660021d8d502b46f43e41b1aa0008dd87c8363540ad4bd0b906c6a80029761720d8d500054f42641b1aa000a9d84c836354001938c7ba2c6a80032718c7458d500045f43ec8b1aa0008be87191635400193cedb20c6a8003875d76418d500046ec3cc831aa000a9e8499063540011bf0eb20c6a8002b6e016418d500054f430c831aa000c9e761906354001c3aea320c6a82ffa6d406418d505ff4c280c831aa0008dd8798863540014bb0b310c6a8002a7a126218d500054ec24c431aa0008df8758863540014bf0ab10c6a8002a7e116218d500054e422c431aa000ad78158863540015a902b10c6a80771718e76d4d500061f3b6c9a9aa000e1c63d93535400187cec326a6a80038718c64d4d500070e180c9a9aa002a5e86d8f53540018bcedb1ea6a80038719363d4d502a43e432e3a9aa000c3c645c7535405b8b8c6b8ea6a800a1fa1a70d4d500061e324e1a9aa01dc5c639c35354001970c9b82a6a80032e1907054d500066db18e0a9aa000c3c76d915354001c38c7b22a6a80030f1d86454d500070e318c8a9aa05ee1f731915354001c3e64322a6a8003874c86454d500152f436c6a9aa01cc5c76d8d5354001c38c9b1aa6a80021fa1b7154d500061e326e2a9aa031c5c63dc55354001c70c9b82a6a80030f1907054d500ce2e318e0a9aa000975811c15354001c70c8382a6a821756dcc7054d500145e422eda1aa0028be87d9143540014eb0a10ec2a8002bc60021d855026e1fb2ce930aa000c9e73d92615400193ce6324c2a800327d9173985500064e322e730aa000c9e74d8e615400193ae9b1cc2a8003279d063985500064eba0c730aa0008be87d916154001938e7b22c2a80
  | 21 => 0x7558631940012f301baa632800a3d21d614c6500063bbaac298ca01d87f8758f509403b8bce6b1ea1281361fe1d61d425026e3b38ac3a84a000a3d8590f64540071ed03b96c8a80023d60772d915000c5fc3a85b22a000a3f8550b645400395ce4a16c8a8002ade0542d91500055a40a85b22a000a3d8510b645400153d06216c8a8002a760c42d91500054f41cc5b22a000a9d8398b645400153f06b16c8a8002a720d62d91500055bc0ac5b22a000ab48158b64540cd47d0a39ec8a80028f61473d91500045ec3ca7b22a066e1f5394f64540cd47d0bb96c8a80028f61772d91500055b40ee5b22a000ab581dcb64540cd47d0b396c8a80028f61672d91500054f41ce5b22a000a9d839cb645400195ee5396c8a80022fa1c32d91500045ec3865b22a066a3e850cb645400147b0a196c8a80032ddc671d91500051ec28e3b22a0008be87cc7645400117b0f98ec8a819a8fa1731d91500051ec2e63b22a000aae82cc7645400155b0598ec8a80022fa1c21d91500045ec3843b22a066a3e85087645400147b0a10ec8a8002a7a0c21d91500054ec1843b22a000aba8008764540015730010ec8a80022fa1c30d91500045ec3861b22a066a3e850c3645400155d04186c8a8002ab60830d91500055b40861b22a000ab5810c364540cd17d0f906c8a80022f61f20d91503351f42e41b22a000a3d85c83645400153d07906c8a8002a760f20d91500064f39ec9322a000c9f645ce6454023938c8b9cc8a80022fe1d64191500054fc1ac8322a000a9c83590645400147b0b218c8a801e1f215721915008e56212e4322a0008f7815c864540071e902b90c8a80028fe1542191500055bc0a84322a000ab481508645402396882b88c8a80022f61e62191500054f41cc4322a000a9d83988645400117f0eb10c8a8002a7e0d62191500054e41ac4322a000ab781588645400156902b10c8a817a8fa1673191500051ec2ce6322a0008bd8794c64540bdc3ea7298c8a80028fe1572191502f51e42ae4322a011cac725c8645400156f02b90c8a8002ad20572191502f51f42e64322a000a3d85cc8645402317d0e190c8a80022f61c32191502f51f42864322a000a3d850c8645400147b0b388c8a80472d1c5711915008c5f43e62322a0008bd87cc464540bd47d0b988c8a80028f61731191500055741662322a000aad82cc464540bd47d0a188c8a80028f61431191502f51f42c42322a000a3d85884645402317d0e108c8a80022f61c21191502f51f42842322a000a3d85084645400153d06108c8a8002a760c21191500055d40042322a000ab980084645400153f06b80c8a8002a720d70191502f51f42e60322a000a3d85cc0645402317d0e180c8a80022f61c30191502f51f42860322a000aae820c0645400155b04180c8a8002ada043019150005
  | 22 => 0xb96ca988022fe11725953108c5e422e4b2a62008fb805c9654c4011f100b92ca988061f21d525953100e36392a4b2a6253a7481549654c4031b90e992ca98a671ddd771595310043fc3aca32a6200c5f325d7644c40f0fd0bb96c8988021f61772d91310147ac0ee5b226200c5d754cb644c4a556902a14c8988021fe15725913103c3e42ae4b2262008f7815c9644c4011f700b92c8988023e201725913100c5e43a84b226201cac72509644c4a356902a12c8988063721d32591310045fc3ac8322620087f855c0644c40f0f90ab80c8988028fe11659513116e2f39acb2a262038dc865ce544c4010fb0b3b2a8988023be09765513100c76412ecaa262008fb805d9544c4011f100bb2a89881e1fa16761513129c3ec3ecba8a6200c5f65dcd514c4a317b0fb26829894a2fa1c64505310047dc3ac03026200c75719d4604c4018eae2ba8c09880317e0d75181310062e41aea3026200c5f325d4604c40f0fd0bb90c0988021f61772181310147ac0ee43026200c5d754c8604c40399ce4990c09880b355c5321813136c5ec3c87326a007a3e8590e64d400f4790aa14c9a8002ad205429935003d1f42c86b26a06f8be8710d64d400f0f90ab92c9a80023de05725935001c7a40ae4b26a0018bc8750964d400f4790aa12c9a8002ad205425935000c6e43a64b1ea0118be84dc563d400117b09b8ac7a80063ba0b7158f5000476c16e2b1ea002a5e8399153d40a70fb0db8aa7a814f1d9877154f50004bac08e0a9ea0028bc845db43d400517b09bb287a80025e6177050f5003e3bb8eeca8ea02d87d86dcd51d405b8bcc7b9aa3a801f0f9d6649075003e1f3aac920ea04c87f865d441d400f8bceab1c63a80023de05725925001c7a40ae4b24a000a3e84d49649406d0f90ea92c9280022fe1d64192503345fc3ac92a4a000a3f87592549400187f0eb24a9280025ee1970952500063dc32e12a4a05e8be87991549400127b0fb20a92817acea0364152500061ebb0c82a4a066b3a80190549403b2b906b80a9280761fa1c5458e500ed2f418a8b1ca0008f7815c963940071e902b92c7280761fa1f5258e500ed2f41ea4b1ca01dc5f7558d539410bab0a6382a72800a2fa1276d0e500ec9ec38a9a1ca01db1e8315343940012f301baa872800a2f21d6450e500061fbaac8a1ca002a9c83591439409b0fd0e2a2c3280030fdd0545865026d3b408a8b0ca00087e8794d619400147d0929ac3281369da06535865026c3f438a6b0ca04da768114d619409b0fd0fa92c3281369da0752586500047bc3ac230ca00087f8758e519409b4ef0eb0ca3280031de1d6194650004bdc32e128ca04cc7b865c2519403b0ff0eb18a328077179cd63146500049e422e028ca01d95c835c051940012f301baa832800e3da06768c65001e3b30aeb18ca000c75
  | 23 => 0x595410043fc3aca32a8200a6c82594655040147f08b2ca8a08e29b20965951410063bb2ee2aa2820087f87594545046d4d904b28a8a094aad20542d8d410143e42aeda9a82008ef825db53504031d904bb6a6a080a1fa1f6554d4103e1e32ae9a8a82008ef825d951504031d904bb2a2a08030fd9774545410047dc3ac0302824aab481508605042347d0929aca2080317dce53594412a43f438a6b2882118bc845c965104071e902b92ca2080e1f21d525944101d3a40aa4b2882038f4815c963104071b90e992c62080eb52053258c4103c3f428e0b18820087d851c163104031dd04382c6208023b6087058c410143e42aeda988200a5f8558f53104050fb0bbb2a6208026d6047050c4108e5b2a6eca088200cb77655141104011bf06bacc02080a3720d75980410043fc2ae7300820787c855ce60104071f30f104c02080a37a1f73580410062fbaee6b008200c5c75dcd60104018beea39ac020803171d473580410b45f43e86b00826fc3c75d0d6010405938e7a1ac0209b70f1d543580410164e39a86b008200ab88050d60104010ff0ab92c02081e1f21572580410046fc1ae4b0082028dc835c960104071f10e902c0208021fe1d429963103c3e43a8532c6200a778150a658c4074e902a14cb1881e1fa1c42996310043ec388532c6231a5e8310a658c4014bb06214cb1881e1fa1f20996310043ec3e4132c6200a3e84c82658c40147b09904cb188c697a0f20996310052ec1e4132c6200a5f83482658c4634b906904cb188022fe11725963108c5e422e4b2c62038f4815c9658c4070fd0f292cb1880e1f21d525963101d3a40aa4b2c6200a3e84149658c40147b08292cb188029760c52596310061fba4e8b2c6200c3d741d1658c40147f08b92cb188028f21172596310053bc0ae4b2c6203a74815c9658c40147d08392cb188028f610725963116d2f418e4b2c6200a5d831c9658c4010ff0ea12cb188021f21d42596310053bc0a84b2c6203a7481509658c4010fd0e212cb188021f61c425963116d2f41884b2c6200a5d83109658c4074ed03382cb188028fe1170596310051e422e0b2c6200a5f835c1658c4074ed02382cb188021fa1f20596310043ec3e40b2c6200a3e84c81658c40147b09902cb188b697a0f20596310052ec1e40b2c6203a7681881658c4014eb03102cb1880e9da0420596310053ac0840b2c620087f855ca648c40f0f90ab94c91880ead20542992310043fc2ae1324620787c855c2648c4010ff0ab92c91881e1f215725923101c7a40ae4b2462038bc87509648c40756902a12c91880e1fe1d65952310051fc22cb2a4620387c87595548c42347908b2aa91884637e19731523103e2f32ae62a4620087f855d2608c40f0f90aba4c11880e3da07729823101c7cc3c4130462038f887481608c4051eb03
  | 24 => 0xe820787e85dca60d04010fb0bb94c1a08072b9c9429834125d5a40a85306820087d8790e65904710ff0ea14cb2081e1f21d42996410053bc0a8532c8203a748150a659040f0fd0e214cb208021f61c42996410052f4188532c8200a5d8310a659040147d09994cb208028f613329964103c3f4386532c820087d870ca659040147d08194cb208028f61032996410051f4266132c8200a3d84cc2659040f0fd0e184cb208021f61c30996410051f4206132c8200a3d840c265904014dd04184cb208029b608309964101d3b4086132c8200a75810c2659040f0fd0f904cb208021f61f20996410051f4264132c8200a3d84c8265904014bd07904cb208029760f20996410051fc224132c8200a3c84482659040147b0929acb2080317dce535964101c3f43ca4b2c820387c87549659040147f08a92cb208028f61052596410052f418a4b2c8200a5d8314965904014df04ba2cb208029b20974596410051f424e6b2c8200a3d849cd65904018bee739acb208021fa1e43596410051fc22e4b2c8200a3c845c9659040147d08392cb208028f61072596410052f418e4b2c8200a5d831c965904710ff0ea12cb208da1f21d42596410053bc0a84b2c8203a748150965904010fd0e212cb208021f61c42596410052f41884b2c8200a5d831096590401c5a84212cb208021fa1c32596410043ec3864b2c8200a3e840c9659040147b08192cb208028fe1170596410052fc1ae0b2c8200a5c835c165904074ed02382cb208021fa1c30596410043ec3860b2c8200a3e840c1659040147b08182cb208029ba08305964100536c1060b2c8203a76810c165904014eb02182cb208021fa1f20596410043ec3e40b2c8200a3e84c81659040147b09902cb2080297a0f20596410052ec1e40b2c8203a768108165904014eb02102cb2081f1d99571d52410059ac0ea92a48200c7565dc5549040127f0eaa0a92081e8fe19541524101c6e43a64b1c820787e851c163904010fb0a382c72080e1f21d6554e4128e1eb9ccba1c8200e1c30997439040187ccb386872094b0fdce6550e410070f994caa1c8200e1d32995439044d53b0db9a8720803879977350e410061f328e0a1c8210c9e631c143904010ff0ab9cc12081e1f215739824100574c106130482038f9878826090405938e7a1ac1208422f21d43582410055c40286b048200ab9840c16090401d3686182c120802ba608305824101d7940860b0482038f887481609040147b09296caa08031b5ca52d95410051ec20a5b2a8200a5d8314b65504010ff0ab92caa08022fe1172595410047bc0ae4b2a8200c6f751c9655040195ee8392caa08021fa1f525954100e36396a4b2a820187c8754965504038d8e4a92caa08022fa1f425954100e5639684b2a82018bc875096550403958e4a12caa0803391cb71
  | 25 => 0xc01d9265900c0a181e8f21542993510055bc0a85326a2008df835c264d44051b906b84c9a89bf0f153735935101c3e42ae4b26a200a3c8454964d440f4790ba12c9a88062f21d425935103d1e42a84b26a200ab78150964d44bd878a8382c9a881f0f9d1769535118c3f43ca8b1ea231a5e8395163d44070f90ab92c7a88c61f21d5258f5100c6e43a64b1ea26fc3c545db43d446327908bae87a880e1f2157650f5136e1e2a2eca1ea2008fb805d943d44011f100bb287a880a2f21d6450f5103e1e3aac8a1ea26de1c5458d43d44014f3012a4c1a88028fa1253983510053cc04a7306a20387e85dca60d44014f700a94c1a88028fe15429925101d5a40a85324a2008df835c264944051b906b84c92880e3d205725925101c5e43a84b24a200a3f855096494403958e4a12c92880ead205425925101c7a40ae4b1ca2038dc874c963944012eb03386a72894e5d61b7154e510063ac36e2a9ca299d5732dc55394401aaa65b8aa7288021f6187054e51004bac08e0a9ca2038bc8759143944071ed03b94c12880e3e61e20982510162e39ea6b04a200a7a80d4d60944330f90ea9ac12880e3e21d20582510053dc2a40b04a2078f581dcb645440147d09a96c8a88da1fe1d52d91510051e422a5b22a200a3d8590b645440147b0a216c8a8802a760c42d91510045fc3ac8322a200aac8259064544011bf06b80c8a880a3720d70191510051ec3ec92a2a200c3d87d9254544990f90cb84a8a881f1dd86761515116cae41ae02a2a22d87d87153635445b4bd062a6c6a881e3d60772d8d5116c3ec3ea5b1aa22da5e83d4b63544a94e902a96c6a88b717dd76354d5129e3bb2ee2a9aa2028bc845db43544011df04bb686a88063b20976d0d5108e1e322eba1aa22d93d87153435445b63d062a686a880a2fa1f6450d510061fbaec8a1aa202a9e83d9143544011f70eb00c0a88021f61e53181510051f424a6302a207c757194c60544994e902a90c0a881f1d5c5521815103d1e42a85320a203ab48150a641440f0f90ab92c82880e2f21d425905101d5a40a84b20a2038dc874c963144054bd07322a6288025d6047054c510145e422eda18a2028bd84dd943144071f30f104c02899b0f1d774580512f61e3a8e8b00a25ec3f531d1601449587ea23a2c02892b0f54474580512f61e280e8b00a2028de87dcd60144ad8b8ebb9ac02880327dd373580510064e3a6e6b00a285c5c751cd601440193ee839ac028803271d073580510061e3a2a6b00a202c5c7354d601440117f08b92c0288462f21172580510046fc1ae4b00a2028dc835c960144071f10e902c02880ebc20520580510045fc3a85b2e820187c8754965d04014ef02a92cba08021fe157258f4103c3e42ae4b1e8251ab48150963d04031b90e992c7a080a1f21d6554f4108e1e3a2caa8
  | 26 => 0x2ce2016415153014ae41ae02a2a631a5e839536154ca70fb0e2a6c2a98030f5d054d855329d3b408a9b0aa60287d85dcb6154ca70fb0fa96c2a994e9da0752d85530162ebaa65b0aa601cce724cb6154d858eaebb0cc2a98023de1d61185530047dc3ac0302a6c1a7b855806054c0157108b00c0a986697a0e54181530143ec2ee4302a6038f681dc86054c011eb03b90c0a98021f61f52181530162ebaa64302a601cce724c86054c018eaeb388c0a98031d5d571181530063bc2ae2302a600c74855c46054c018eca8b88c0a98031d15171181530066bc1ae2302a600cd4835c46054c018eca6b88c0a98031d14d71181530063ba92e2302a600c75525c46054c019ae64b88c0a9803354c9711815337d1e42a85b2e86028bc845c965d0c011ef02b92cba180e3d205725974300c3e43aa4b2e866f8bc8750965d0c0533906b86a9a185a2fe197015343014ce41ae02a6860087f855c961d0c0f0f90ab92c3a180a2f21172587432945e43a84b0e8601cac7250961d0ca556902a12c3a18030f5d754983430055cc06a9306860787e85dca60d0c010fb0bb94c1a180a2fa13729834301c7b40ee530686008f581dca60d0c0117f0ea14c1a18028f215429834300e57392853068600ab48150a60d0c0517b09b96caa18028f61252d95430052ec1ca5b2a8600c6d7294b6550c0147b08296caa18029760c52d954336c5ec3e85b2a866da3e85d0b6550cdb4790aa16caa180b275d132d95435961fbaee8b2a860087f855c96550c011ef02b92caa180e3d20572595430047dc02e4b2a86008f8805c96550c010fd0fa92caa18061f21d525954300c5e43a84b2a86018dc874c96550c018f6ea382caa18032edd070595430066db98e0b2a8600cbb541c16550c01970a8382caa18031ed4870595430063ca90e0b2a8600cbb421c16550c0197284382caa180336cc870595430066c990e0b2a860087f875946550c014f100b28caa19b74715173d514336d1ec3ecbaa28600c3d87d975450d81c3e65b2ea8a1803874cb65d51430845e432e1aa286c0a3f845965450c014f100b2ca8a19b70fdd365551430062fb2ee6aa2860087f875945450c014f100b28a8a18024fe1d54151430049fc3aca2a28600b1f835945450c0167100b28a8a180a6720d70151431d4cec3ea9a1a86028bd84dcb6150ca317b0fa16c2a1946ad20542d85430164eba265b0a8601cce724cb6150c0156b0810ec2a1802b560c21d85430076299043b0a86008f7875846150c014f50b906c0a18023ee1d60181430053c42ac030286beabb845806050c2153d07aa0c0a180a2f61372181430045ec3e843028600ab980d086050c014790aa10c0a1802ad20542181430055dc02843028602c9d744c86050c0399ce4990c0a18029ea1720181430055cc26403028600ad983c806050
  | 27 => 0x8015006800402000000a005401e004008001800000a0018000006005001002400a03a02f002400600800380f802c00d000000c01e002003000004403b00c8008006003000809c002001005800c00a01a000001c002006000002000000200300000080000008000014000005001800800200000240080100000024062003000002c00c0080038000000000000003802c0090008028006001000803800200100000040020020000010022008008003c02005f000003000e018dc874c963d50071ed02382c7aa0023d6047058f5400e36392a4b0ea807a768508561d500156b0810ac3aa002bc60021587545968f21ae7aa4a811c3f635db549502387ec4bb6a92a0030f58976d525408e1e30aedaa4a811c3c605db549500147b0daa2c72a0023de057258e5401c7a40ae4b1ca86da3c8550963950031b90e992c72a00297e153258e540051ec36a930ca801cac72509619500147b0daa4c12a00e3da0772982540047ac0ee5304a866a3c8550a609500395ce4a14c12a0023be0971d8d5400c76412e3b1aa800cd8631c163550014eb0b90ec2aa0029d61421d85540055ac2043b0aa8008f78758461550015c904b08c2aa0029e61430d81540055cc2061b02a8008fb8758060550015b106b00c0aa0023be09711815400c76412e2302a807c3f84dd9541502387909bb2a82a0470fd0f765505408e1fa16ecaa0a800c3d42dd9541502387883bb2a82a0470f103765505403c3e42ae4b18a8018dc874c9631500f4b90a992c62a0063ba0b7158c5400476c16e2b18a8018ee821c163150011db04382c62a00e3da047058c540047ac08e0b18a8008df835c660150051b906b8cc02a0023be09719805400c76412e3300a8028de87dcd60150ad8b8ebb9ac02a217171d473580540046fc1ae4b00a8028dc835c960150011ef02b92c02a00e3d20572580540047bc0ae5326a6038f4815ca64d4c0f4790aa14c9a980a1f21572593530047bc0ae4b26a6038f4815c964d4c010f90ea92c9a98062f21d4259353014ae41ae12a6a65487e8795161d4c0187ee92a2c3a980a1f21572587530045fc22e4b0ea6118bc845c961d4ca90f90ea92c3a98071b1c952587532a53a40aa4b0ea607a768508561d4c015ab0610ac3a9802bc60021587530061eba4a9306a600a798095260d4c050fd0bb94c1a98021fe1d52983530053dc02a5306a60287d85dcb6454c071ed03b96c8a98023d60772d91530043ec3ea5b22a600a3e84d4b6454c6d0ff0ea96c8a980b175d532d91530045fc3ac8322a600ab8805906454cdb17b0fb24a8a98028f61f64951530061ec3ec92a2a6b2e1f32d925454c01c3a65b24a8a980a57e1d73951530cc3e432e12a2a66f8be871915454c0527b0f320a8a9b030f9da641515336d8ec1cc82a2a60093f875905454cdf63f06b20a8a980
  | 28 => 0xe80000000010000000000026005802400a004001002800000e00580000020020000014010001000000400404f001003000001e000000c0020000000040004012001007400002b000003400000a011004800400f000005c004032004800801a002003800c02200c00380b401a007000000c00a0020000008000008009800401c0030080028008003003000002001301c80440440060008044000006005002002e00e000002000400100200d0000002000806801c0060048088002000004800c016001000007c01a000000002c0080000060160000009002003c08401002c000003e006003005c00a000002000001803400380240040070360018002002006800800000f020000000c010009800802e005000805c000003001800802e000015800000200a0030060020020001803800000300200d00160150010048014000003000800c001000800c0800120000008000014005001000000a00180440660030008000010001000800003c008000007c00001400b004c008007006806400600f007000003a00d002001000a086018800000205201c00280120000010004002000004800c008001001800001a00000080340040060030010000002000000800201500280400000270040004012000000808404a000000801400000000000500360030020028004015006000800404e001000000800f0000008002002000003000000900100cc038008006000c00400200a801c00200a0078058000002002800400200f0020004000003000003400402c00f00200000010000000004001021001000000601d81b8018002000002401e00f00d800c0060100050004006001000806400c004000000000e00a00080300120030018004000003001800005c0000000030006009000803804e006001017000801e005000c000001001002c00803200000000000020030000010002006800c01800500200040020080060014016002002001801a0330018008006002004001803c00000000340000010000058016000005800c00800a001004c0120270000000004005000000000400c00080100060520000008014000000803c0260000038084008000024800000200d003801800c003001800000400a001800c004003000813c030000006000400200e0050000014009002801403000500080080000040040000006001009003c00000400280a401600e014800804601a00000300000070000028000002008800000c005002000002000000180880180090018040000004002001000e000002800800400d0010004008000000000401201c00080000060030000034006008003809c00600000180000880000040044020000015000804e000002800400200500200100020070000030000009003803c00000000400b000000100c000400e00c01f0000016008002809001
  | 29 => 0x9c46298146880013360006bf1fc853400071c143513a16400000005f69e060521f400000000032c800000000002943e035400019c4cfa7366c000000000005880001ce400032c04944b271f27504f030a34f1e738f14f627a1fd8000000cf872ab7716883c100038406744bd48fac84642000000259cdc2dcc00013d9c26e155afa2815c264e0001e61b1c002003c002040001804c006000000000001a001000800400000000180c403e005006002001a00b003800c0000180008010008002000800001802d000802c008004001000001a00a000000400a0020080018004016000000802201500680b4032001000801c01003a00f000000002f00a800c002000001000802000800a003c00c0040000018008006002000c0000080058010004051002805800c0000000000016025005003c0120060008080004019005800400a0010000014006003000001400600f024800400000c002000004a0000068004002053000801c006008007802800c002009800404a0020030034000003008004001e000004000000600c0010024046000011800801200900b001019801d00a8028008000000002c0280010088054004001006800000400301280000060050148004000007007801806e01900001cc014000007004800a00e0058008018013000003000a007000800000000900e000c01200100400080140030008014006029004801c004000006000800600100f000000200300080a8004007001803c01e007000001c01000d003000c0160060018038004006001001800600000580380000020020000010000006005001601b000804401800000280040120000030008008000004000c02a02300000080000200220030046000000002400c0010058050010000020000000200100000140140000000000000001000001800200f000800403a018000001800000f000000c02200100b000003a006000001c00201f014001401a00300200240020000140034026000011800000600100280200020080010004010003000003802e00c000000c01a041000800000000002680000520000000000006002002800400800000480c400002c0038004032001000800000a0100058000008003000802c0040030000024002009000800000000000f00000020080058008000000000001c0060040000000000027002000c05a0020000018000017002000400000d000001401c001007800001000c00000f8000001000000000c0070278008000001001800000000c0018014014018003000c012001009804c00401e003801c000000013802c0080080018020034004015002400000300f001801002e003801c01c013000001000200c00080040040000008010034001004008800000f00280a4002013000808c00c00600380080100010170018010012003000002200101
  | 30 => 0x94000030c07e4211f22e0d99c0000003014000c17362800071e00026600000005da3ab28f8c608094e68b600785b9000000141e0004f71df8c1e5fe5d7bb4c4c07445fd8b092489385c6b58c2dc53c4308ab514ab4f69900000007ac000387cac673c0cc3270a0a543623901c0000005a9271d8281b50000ef0c00d5d54c8bf5d1ccf20ab3c0c0003190002e444ba36a13b86ac000af20001fd8000000493aaec10850b0002204000bb237a80000000b21e431e887ee3020035c148600055892493b800047fbb68000cd647b1bb02800004b880000000004d89bb441cc11006808195043d00000004d20d8000127463ab71728065d04034320b36e8000332515800138c1fc0000000fb6c225c7800000000076004a56828a66f9b24c89211506f1ae1836c290000001ab4478000000104874d00000003167970e824758a25e52af00006fe45f600ba0d81c64f2b5800000000000028451e80002a49f8000062a23732085c808100024c592a0c80268000000ebf149024da507321b200011b60004e1941db5cda577d00000004dc4fd35595e67bf445a9699eeef870b869840a38d5ab01dd5645ab00120a4f20c5d3488c011a80953a3279960a02f0029420d005c161515303ecd412fca819a1a72c5bd9b5d6e87a40bd02f8ffe15d70d34f1b3e37353883518e6b8e3aeb60d2068846a9b5c87f855407f878477a6c16abb76ceeeb783828e71baea2858f8b1857c63e4b68921996a2067e9745b1aed069a346d84014270db7f04506536b796151a672a7262e141122c825f2b810aa8641c4a775dee6073918541a10c690d10d4db7ae5d0750580f6ece86ae2d098e885100baeb45c46781d7b9e92100000000e89412d1c1023c4834e7100938ae520cd21306851815e5b722a94fd726ba870582c4b4093d32b00d4eeaa8131a8000f26a0711e8dbc0007ba5670c4c88e2230000a90000b5128016bc9d67d03368be1c3a0000b794ada9082274d8000bf80000108000000dff7460150376d4906f88a48729464e937e4cea8e768324b86e4000000083000000073e26799c4dce25c13e87ceca05461de878a7ec1120e78f78c386ee800037e6541d39b80beee216be8001d5c79b29237f4000c8c00022905e0954716ab4cb6cee10ca8001be2e1e71a8cb01ded24060a2551ee4cd019b43d0865bc69b192800088000018cc0004ce0ec274430e03800011a5d0a00046338457b4af968e80006f40000001b60ec49c800024391f80000002431d3834960c0d340f6eea628000162a42b7190000000aa0000320053ee443b9b754950eff662254542e76004001c93fea630ccb678fd0e6b6aa163cff20d01890ce0a2a6972e435a87942100d790b80005300000000472000000000193cd161172740000ad800002cd0a826100033e8a0459a1590000000b73369a2
  | 31 => 0x92d68056717632e16d66612e0329038c0005d00c24a321764ff0ca41f42984612ba4fcc4990000000000d172da80000000000001e080b8afb12e00001b8d9549e37240f20ed2ba8468000000269110c96c6444bab2d449a35031480000004e439f0000000cd820423c80008121d62529158966656b6b47182895b1aa15026a2a559ba642820fc28300000003d60003590e50a972b4bbb8f9e5947650d14000a3256b2cb4d5a00000018ed54acfc0c0a68073e4d93ca87b04aaae66582fe45bab81000378d52609e08daa6cf0c00062d22d423e76f44428f5396000162ab45cce0a421232297107000001c695ba0003cb36f80008da13a91f9d5052f0c40000d3c16128e26b4d6c00031ea3f8e4a3075e2bb443b40000001241a0a6fa58f25d8218ba5120b8a07c630e3d5a9fd9360000e289c5c6ee68513a270e76e542c7056c522000433000199098204e00000004c753a0ca88c200005690ed62c6286c822d95f44fd59d1a1d8f63d244f35800000000000000c1000009c800000000f52a1b88000c0459580000008e806100012e6955573800000040e4201f700380321e68c70576c33011b1c003a64c00005dc2cc78836a08c9b689f860196e0000000363a8b90045c553b174d7a2d4d27c147c7d810b01b89111f68792f08fa000000063e80000000004492cbc4eccb675c93f9a2abb70001d6c0000004a4a42978848b00000010d294723a92c93423050002a00dd0dee5ffa9c92609b52078000de0cb41b016d1beae264b91160a2808200008f87d41d761b213c000efb5ff3bb464411244b045d26a83619e0000bf00000002d14e44066704b9f8ca012c348000195403e5d8ad840000004029d7d648e751900cc0992ac8302b16d41615c3be841d1bc80e585a2a581806e58e1a3400077f00039e59940711f9113471631b7852911602471431136045a4284bc37e84a67573ad2eed6989234c8b34d2c48892be0e9094aa253fd81ac3bc9a50e39a801f029902536cc110da02ed868c414cd95800cdc02400a4f48b9cc060132d8873814e88633d16a9022a0455facf88d62a2233b7f8000ed448987d0000eba0b19ef440c57855a03950e034104c2f88558de96649e780003f433f122561c7701bc3189b3009a24694687565ec6200001446e060000001424cfb0e6137c2dae2708b39816cae035248a18c2a06735a00899cc6dc1778d8518a83b41c2a40ea04ac0679445168ad25868b952d05bb6880bf19bc59d05eaf50a96a10284b6a5402aa730b36d4da09156f32c09496ae86c31a1187e48c09b26616bc17420aa11816c4c81e39a85b9a88e1c291a03fc553736a7c9dd6a6e2a307219ec4db2b734ac60655f206001d98c6772548c09bf682e3b516283623b714221a114695c670a711550cf33a5b8ec000b9270c945cc2248a535b515134a
  | 32 => 0x9d30002a3dc729424af0e4d85eebe00db4f533a3c36cb0a5d5044876b716057c8b944a811805e67f323d2d8155a804721215dbbc72b00030201143d800c04e03821091da09b5d54a6a41c890094611e6e804a0426e0c10019a464c9a96a78000a842bc29080014c464923e1a25e0088205c1f380008e234c35780180e15601f7d8b0c3b326ba897c095f050807d1d8b0838534e97e629c43785957bcd65609a1794d8db851820cddbe7d33720000fea00006cbb640004413a138bd920e976ce314c000a34780a7dcbce3a56892905caecdf01b12e4f44eb336e8001d7082c47a80018040007620a280003dc0000000fc60002e900000007594dcaf0c7f45990f505f8e1c35f1079d448a663c77182442d808e5051b119dc21b3290000be80005d100007028065518000000dc21e496593005cd61288540002b60001ccc000dd45149ff18ec33b47e9d61be0a19143b710a9ed0705b92512406460a9a7f1ce8bfa1ec812db44808110af2d37486b5db175558243669a81e0a88eef066b2f019221e2428000a6e7d620500016629f313213153fa0006a515f4dfe5ef01327c150676403095b172e7eb3168000f1e0006fb8000000ece0a18000000a9e56e0000b001e70000001c1041a62faa1854c40448f1198000c4c0001500000826000269979ca583b8a9f400085f4672484e94000109000145e1ef5c631100000005f4b9cc31af103328a80556a6f0002fd5af4a227011729734cbf3c0a618b88a9f2fe8ac1deae8b0ac3b0c7644181c01b39d28bf2000294ce085233bd94b50ce5c373f80000be80a23b89d0b20a480002da50426254910f54000e361b6263c0900006a22fb0000b282fa8001c4847f43512000003b678880019069c06c107dce2a20d15d11e4000ab60458a0c0007bb3a400004ce58b45e2a1000052a57525580765ff4880001c7ca5e731981983a1ba70b36dc3f63de5291db4000c1900000001b60000000000fe00000002de8aba00000000100000000003351204a1e4ce0d180002df000009471c02a5d22411d04028036800194a39a0000000000d0234a800142c5fb0003b256700006e980000004983f730b401cb1937c1c5d0340000002f30000a674a2000033c5bd3e32940294ea044fa8680000001ea0001a58b4d15282b1bc479125a2dc8de4c3e32d1b18000d3f4aca5910282d36f509cd03883c6c9b28400063a1b8b5c40aa73a00d2e780008250001461cb600030cb2dd172e4d03639f55945f00ca09384d4c120299acdde0de7236b158aa069f5fa2f98baeb6e022865938ad381fea764c08c4221621dcc42d6b67386f03c44de4a6231c904d232a08a206aa9071d88b550628192738b251d4a9615a1cb42b2b3b0a42da906434200032b185c00077f28540b4000208ac4c9e494f09a2ecc936a5f229373c6cc6a73d33
  | 33 => 0xe7a0002f98490bc800063095cce68cc51cb3540a6aad70000000ac26df2ea21257e00002d115700faeac526ac69e108e610a308428a2b123794491b00b01bd80002ce4934749c70b2200021018700008cf10d1205106ed776900007c239b0c4831c9ea8bd1e139780002086802ef98ae26c25e36c85c29ca51338fd6b023a0743214fe8de80cd2a71a34c9d32f8b29cc2f0c76c188146c4aa00031b04f2ef9393933d9344d40001e1455c62203aa1e80006f63d9984cb980000bdaa99192d0a111097cfd27ad00000000007990bc2c0dd1ae2c0000bb510a69d0000000000abc0001990000000663800064a00045719b80000003e28001466000723ba7c0003340d680012f85e86fb0000000410000000000030b6661b64000b9f00005c0c187165040c5db081b771120ac0004a04139ae48b4000148128482480337a0fb4394000000212cb087a70000001254e9100008653843dd76abac5bb02ee01394994a2d7872b1b6ca58a5c0ea8000f88bd8062a4dc0003691ffb674d9023c00019d12580d76030001ae60003a98cf4d8666b086b704518000000390c1509bd02922f83e21c22d72b8db324e943f896829c000000000074699300004a8ddc2c717ab3f8cec000774300194ee90161b098000000261ab0d86400053c10980320000001e2da520ee6a32ed16441b656a1369282b623c512994ac45c24b8f8088c8af3b31dc96a892946907cd39c9ac6a9005483ec91622a561e2a8bf5a32aa4f06cef1f498d9cd84237422db4f983985a5a0fdad0713460069492a68b36898e51826a443a0398e1ecc253404096fa7b94658d5d016dd16351e7c4b03d31eba4cc00010017c8749cc42ff1199ea0e4061f1691690000bc1765b4885000006c90000000d5539ab2f80feaa2000000083a69a2ca8000a94c433ae2e41694c3964900000004d70ab8764650ce4105a8900000006d2245800000044810a977400021d30693c80000003a8d60e406000325dc0263215f995400000030e9b34f8e6e91318001dc46fb280b614eeca2c37380018920401dfb450000c715629860b2400002833ac84e8f37442aa90a0496676bc380000000169f0d2bad7f353305800000018f0d71754d1976b3598b12ca90600ed59d400045437ad36400014689ec0ca9050de94d8a083cf3f215380989f639c3bf01c021f31a03e5d604480000000aacca61fca8e0a442e66519fb44f8c4e19880d06ea7d40002b89792b232b20000000699340b83c00048e32ba86000008509d237013a218260b1500000002f1afbc4600006e1800062ae531d414a445608f63380001ea0aa00000000000005f3818c6e890f000105c52a92500019641464d657b35b0bdac3a4f580000008d50a3ac5db56712000000000051075d8000974000000024001211800000004c4531341800177e
  | 34 => 0xc61266e10c0f5c43102492791765971153b153507a30cd8000b0c34b4e78db5be81304758001314e9859f87503065a3232aa74f18c075a80d4800088c4d980019aef0d0d0ba9c476dc6000000027c68a51a9b09514aba22606e1bc26aa0002138000b677730000d1c00017f381031e0fe0feae9dcee7676a189ad3eacf069530adab0000400000010c62b66196cd56af070a90001d143100000b380000000000000ce071105f920d5bcef10000000e7eb2514d80007242854c2988ca7c54d182307cac44373398fcddba0dd000260c9a6792478b4c4000000292b78146e01433e0000aaa32d02c1635c900001010001d6a0000000b05a060000003538d7a00041b8000000c7f0003040aa46961e22f4054e3fe028a4bdb94c941668d64a509450ce2c446ecc2c04d8b50dd4a3931f9114cc67cb6ed0744c903ae4fa1aec000d594178045d7a99616dadf8da400070288b0d780eb0001869cb481b05ab0d0dee0004c92cc13aa0000000250be27243b480c4000d017520000f346bf470a990c169ed378a1d92c2a1c22508994f226512f0e2169213257a21340b28ba23536e59c608c000194400074c5e980000000005f2a8b526c9014ed800000057136f33fdace18c7722cb1e048b067011b021000008080000008e30003b2000031f00000003eae3a1d0a68800000000009e00c80003fc3bc82fa00056f8eecab693a02383ed2ae0005ae2cb951059e4fcb2c4000e9a0002fdc0e65d04c38b8000041b0002108d46b5d0931aa400044000000008bc1aa48580000000000002ec1c405f60000adca68000078a2287ec0005b61b94fde9b74ec05c874c8d924fa8fcec6041637140dc8a1512eb00014f4ab87073adc6344ee0001065d8e2382280af59ea9995d4a7ec3d213b6dfac74cf20002d48000b300000003b196668dd0000d8d37e81840a971d9ca00042215fd64e3f860f00015966fc00000000000004298cb8bd223418a0234000c410eb0000000dc759e0ba8000b68113af5c0005453561cdc8689ea56612880001f95e30a2c7205485a733b1c921e6209a4d00009da121076cf1c4442bb83911dc2376573b040d00000e02f49b368630912341060af74d19a48948b962899e75aee24f635a1f00000001959bf891edcb73723c09c26ca49c80008ac0002701ebc0000005caa335bd8edb7498f453346cf0f425d1a222a112b39009ee85808a2ae420c52e40380017ac2515210870048000000262000035a3ea815d3d085d0001ec41e60004e604b89c69b40002f3c68ea9a495ab545025ac1682901aea8160002ee0d260000002bf409e00017180000000006ca2f28fa4995644258c0001d30a58ba141c46346b8c60fb25b041ab2100fc00066da0046d696f00024000000007549d558c617f7509138fa286d48e3c14364e801c304dcdaa2572d3
  | 35 => 0x216a0f6c34e041b035bca1be38c038dd0e617461bc24766000668a999046e5900026b833ecbb43c2fe095a00002325a436051b0000000000bed0000000e9e00065e9de44dca3b12829749c487b4a58001498b396eb19ec00029d0003a1813ee660f28eb5e2ca606c89bf48060001c206905ac0000e59344cd43390a6addd31c7615ed9340e3295a00000000007893070894a1ea0532d961ce0269b5c1000cbc0edc3a48000d804055a428c4e800064168e8112e6263e49db87a007a0000000b2600000008800000870000ba4780f0b3d0b5ec0002d100026ec00000000038b800004e000000000097723a22ac000b890002a840004e813f9f357beaf82e11f01ab6a5741d2ef0232d4b262166c43aeaf19980007e20004078e5c24242f3c699701eebac5cc000103ac153fd00000003e2253ae1db149900b11be45b498b141237c30cb0c19b35841d8e760002adc00055a32e8000000000000189d88c4020d02fa9916637358159800011c47024fcb4a92d76f362c8e456d1540e0c0003236e02460208b8b05a1df000053d48c8000000bfd5c30bd866a0002b02dc15ea67f67492b83229a4767a1cc00056a25aa0d086414428b12686fc9e24f8ac6177a2702e30339cd4a8d6788298f54c9f21c03580f81a96fc15f8492a2127e1a51640df20b515e818c10a2d092dc0e0d765f1b96086ac525ce9b58ed894d4e09d1c64899f6c487c96ccd4c689832cc148566c39e50494d3725893cd89abb964b12ad22ed183a731e4b7c2963541f9d28043c0002180e067be12dab19612a7e04c90042262aa178b2354d2de43013198000774096aca43da24553bbc4c000e1204b321859e53b08e9ad578e6624f3a5a92a445436494295120971793bd1360dc56d0853176ac990a782ed2c0e341dd17e81a44f10ee34e4e3a58c712b3048c44ff3e08000320a925cc80018bc83e0001cbce4253975b3ac8b7e23f51d2284f0ed7c19fb9ed0e4660371890c2624af59b8674d98d0b6862e70000c4b63e05a57f8d0e5fb18bc0001ac6930311166c8f097a26186002c0bcb47c70402e321879000097d000173800000059a2808838c31527ba78d4437d4a993d0060308532a4249da24c6320058002bdd4a19d4903c0a269685d40001204c49f08bb00000b5b09ce60ada0003480ed06450002e8dcca0001ca2eb94945d92380b11234e46783392800096e4f1a05d0fc0000c12abc3fe7f12f5b90400090d00000015b2000543800056600000000014265765c50000000000472277934ea8e0aa0628000b040002234af200021289989f600000002b800034c1a200011ac06a0003a054b276b0000d5800000000000000007450790b01b4c8c40002bc1cd203a15ab4bd2fc8c84dc225179ac09493004068086c277a1692f228f0da0fbce1ab1b3f08e659f2b6425d834d74
  | 36 => 0x1008000000e312b28b64e6200000036680007fd76613005bca030e1bc102203c63ebb9498d07b822e8000ae00bc5060001378eec2058001b2e7022f938cc0005ba472afa1c0e3da57fa954d6e7de7748f2cd56b5b3ff1ca55b65386bca3bdcdedbb5668388e36707323bb807985c909a87749d8b5968480005526143162e6dd4ac3d4e4a6f99744d52d38ef91f451d26301bd516c984f2a07d3188b81ac0354b04b2665c85a00c0ac4272b4b8e3c7b557e2fadbb200022bb0dc3005ee0c23b345ae2b823e9e715dca9561e3c3dc4600066023298f05e602e9f952fe0e96d79d50000a1d42610a52f66af55615d122234a35f0a5191cd51000291c000000242308c0007084db0db916e3f575a1f6040e96c1d82f016b42933201c506ee22f000000119815539725390906675b7b21c000c3547c977d11e2f4265aac1c30aed2598a793deb1268f0e547cc30615782e47be3ee014973d2f41b334e02acab203d293857898457b09fa91864ec4a379af55cf0b0611b3509d124422f10e44e18268772b6d82e259f4c68949b467b2448a451bda84a1ed84154f8c776b1000000051e005a115dfaad02e588580acead34331c95dec755678d9d966b534a4112c7eeef31ce8b2d1329aa42381a53083e51c391ec7d6c1c5c03a483c610e62cb9c50500f666804cd2cad81538092c3d68752ee89c84a83b8091843d902da8050303c392f1406621c40bcd8c74a88456ea4e639c80012e00923462105a80ccf35d0d79a8e1cd30090255e21cf000286c000aeb2b7adfd0a4b0f6822d0ddced6966aa4f8ce4daa3082cd40721ee35909f8cdeb325638001c1a00000000012365de325800181600030f0000eca3652a88001c7a00006d2a4400000070e1c1884457200007e107a9df00018e000000000039c115acda4081f746e06eb7479bbc3c07ea227a16400077875e091ca1c00000013e41ce6850002850000a3c0d7040c7e0c603d029b4000c4852291d85f40082c1b8acf52aa470a000085a0000000001b7899753980008b63a90002d1c00068f0001d053ae4330000d215cae0a72fb7200006a50c71191a4edb159eaf6400013d373000065e86500003c155cbab2d68000e86000000228800000013780015d89ab45934c06c45ea0a4b13c6f2ae4358a759592491341155ca74cab18b189087ccd21c5190985080c1878d743f41733da1905d4ce2a05d1c2493827d4ca37bdabe9124b598b9b1e8930000001c52e516d8000161459c47683f400085b5d0aa600c4ccd33403443260002440c28bb89af65134940002a35c20bac084e0063795a165461b3c224c9c9ccdd1861e94ab023550f9a2195e6cb72e0710c625206d3bbd9d84bf14ad8a39a76e9662a9c2c0b65321b413c11368f83e42af962850c0549f698cad3e67a1c993a8b7950686e54b6be161
  | 37 => 0x17c25814cca8e0000ef80005eee640000918fee780088b224fc46da20f12fc6228873af280000019232f00016aaac2095a984000afe22c885c0ec02b4940d4400030d00013740003b900019b00000006efa1b9790d7400016c800007400022c4d5cd8800005686b685c0002af46f87b0000032800000000034cc000dac4f618251542cc00f37496ae15f49d8824828000021b171ada47316e0111d5658853a9f2901a00020680016f800007a31b475400026500000001a85ee0001c9e666243000155600074e91458fc000101afb949c9e159b0000000b761808cf80000004152f080
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x22423c00100013002600000000049d000040018640001a0038a0050f10065c012007000040000110000b00046c000482c01a00002800c00000000118030940000800a8e3e000c000000c08000003030400014349150b765505400515a4e545c46054c014369494d71181530048e25580d086050c01838542017650f510060e1d48050d601040103f985d074596310060d191811c15354001854636047054d505ff06dcc641c15354001a3054201435845037c8da538510d61140014a4945c872584500060d21e54509611409907697e1732584500048da5385cc96114001c1474dcd61540500050da5273585501410b456939cd615405000705dd0735855014001c14741cd61540502641d261725855014001434945c961540500051524d72585501400145693d9571143405f526a5b731c14350001c1865dcc7050d400050d251655c4658c00181f87e1165d4e300050d251655c4508c001c4463189758c5100061561c63196314400186587188658c510007095d46219231440bd834861d151541100040fe61741d16504001864871c9654401000709594721d11004001c45651c87344010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x2
  | 4 => 0x4b
  | 5 => 0x4c
  | 6 => 0x124b
  | 7 => 0x6
  | 8 => 0x94b
  | 9 => 0x94c
  | 10 => 0x124c
  | 11 => 0x138b
  | 12 => 0x138c
  | 13 => 0x9cb
  | 14 => 0x12cb
  | 15 => 0x10b
  | 16 => 0x10c
  | 17 => 0x5
  | 18 => 0x130b
  | 19 => 0x180b
  | 20 => 0xa0b
  | 21 => 0xa0c
  | 22 => 0x130c
  | 23 => 0x180c
  | 24 => 0x14b
  | 25 => 0x14c
  | 26 => 0x134b
  | 27 => 0xa4b
  | 28 => 0xa4c
  | 29 => 0x134c
  | 30 => 0x198b
  | 31 => 0x198c
  | 32 => 0xb4b
  | 33 => 0x144b
  | 34 => 0x28b
  | 35 => 0x28c
  | 36 => 0x184b
  | 37 => 0xb8b
  | 38 => 0xb8c
  | 39 => 0x148b
  | 40 => 0x148c
  | 41 => 0x184c
  | 42 => 0x2cb
  | 43 => 0x2cc
  | 44 => 0xbcb
  | 45 => 0xbcc
  | 46 => 0x14cb
  | 47 => 0x14cc
  | 48 => 0x19cb
  | 49 => 0x19cc
  | 50 => 0xe8b
  | 51 => 0x18cb
  | 52 => 0xecb
  | 53 => 0x1a4b
  | 54 => 0x74b
  | 55 => 0x74c
  | 56 => 0x194b
  | 57 => 0x104b
  | 58 => 0x104c
  | 59 => 0x194c
  | 60 => 0x1a8b
  | 61 => 0x1a8c
  | 62 => 0x95253
  | 63 => 0x94053
  | 64 => 0x124953
  | 65 => 0xb4953
  | 66 => 0x144953
  | 67 => 0xbc953
  | 68 => 0xbc954
  | 69 => 0x14c953
  | 70 => 0x94bd3
  | 71 => 0x128a
  | 72 => 0xca
  | 73 => 0x12ca
  | 74 => 0x10a
  | 75 => 0x130a
  | 76 => 0x14a
  | 77 => 0x134a
  | 78 => 0xb5393
  | 79 => 0xbd393
  | 80 => 0xbd394
  | 81 => 0xe8a
  | 82 => 0x18ca
  | 83 => 0xeca
  | 84 => 0x1a4a
  | 85 => 0x12c9d3
  | 86 => 0x12ce
  | 87 => 0x12d453
  | 88 => 0x18d2d3
  | 89 => 0x12d8d3
  | 90 => 0x1a52d3
  | 91 => 0x12da53
  | 92 => 0xa1313
  | 93 => 0x10a13
  | 94 => 0x10e
  | 95 => 0x130113
  | 96 => 0x130114
  | 97 => 0x131813
  | 98 => 0x11813
  | 99 => 0x28113
  | 100 => 0x10293
  | 101 => 0x11493
  | 102 => 0x130e
  | 103 => 0x74113
  | 104 => 0x10753
  | 105 => 0x1a8113
  | 106 => 0x11a93
  | 107 => 0x130a13
  | 108 => 0xe8a13
  | 109 => 0xe8e
  | 110 => 0x18ca13
  | 111 => 0x18ce
  | 112 => 0x29313
  | 113 => 0x130293
  | 114 => 0x131493
  | 115 => 0x75313
  | 116 => 0x130753
  | 117 => 0x1a9313
  | 118 => 0x131a93
  | 119 => 0xe9813
  | 120 => 0x18d813
  | 121 => 0xa5353
  | 122 => 0x14a53
  | 123 => 0x154d3
  | 124 => 0x195353
  | 125 => 0x194153
  | 126 => 0x15953
  | 127 => 0x134a53
  | 128 => 0xbca53
  | 129 => 0xa4bd3
  | 130 => 0x19ca53
  | 131 => 0xeca53
  | 132 => 0x1a4a53
  | 133 => 0xce
  | 134 => 0x199353
  | 135 => 0x135993
  | 136 => 0x1342d3
  | 137 => 0x1354d3
  | 138 => 0x134753
  | 139 => 0x135953
  | 140 => 0xbd993
  | 141 => 0xed993
  | 142 => 0xb8293
  | 143 => 0xe8293
  | 144 => 0x18c293
  | 145 => 0x184b93
  | 146 => 0xe9493
  | 147 => 0x18d493
  | 148 => 0xec2d3
  | 149 => 0xbc753
  | 150 => 0xbd953
  | 151 => 0x194bd3
  | 152 => 0x19d4d3
  | 153 => 0x19d4d4
  | 154 => 0xed4d3
  | 155 => 0x1a54d3
  | 156 => 0x1959d3
  | 157 => 0x19d953
  | 158 => 0x18ce93
  | 159 => 0xe98d3
  | 160 => 0x74e93
  | 161 => 0xe8753
  | 162 => 0x1a8e93
  | 163 => 0xe9a93
  | 164 => 0x758d3
  | 165 => 0x18c753
  | 166 => 0x1a98d3
  | 167 => 0x18da93
  | 168 => 0x74ed3
  | 169 => 0xec753
  | 170 => 0x194ed3
  | 171 => 0xed953
  | 172 => 0x195a53
  | 173 => 0x1a5953
  | 174 => 0x104753
  | 175 => 0x195053
  | 176 => 0x105953
  | 177 => 0x1a9953
  | 178 => 0x1a9954
  | 179 => 0x94bd4
  | 180 => 0x10954
  | 181 => 0x11514
  | 182 => 0x14114
  | 183 => 0x15314
  | 184 => 0x11354
  | 185 => 0x11994
  | 186 => 0x10154
  | 187 => 0x134114
  | 188 => 0x135314
  | 189 => 0x15814
  | 190 => 0x11314
  | 191 => 0x100d6
  | 192 => 0x195a94
  | 193 => 0x15354
  | 194 => 0x19cbd4
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2608
  | 6 => 7968
  | 5 => 3863
  | 4 => 39
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (107793+((h/869+packedAt gbK7 (96496+(h % 869)*13) 13) % 4581)*13) 13
  | 6 => packedAt gbK6 (419648+((h/2656+packedAt gbK6 (382464+(h % 2656)*14) 14) % 9562)*14) 14
  | 5 => packedAt gbK5 (244648+((h/1287+packedAt gbK5 (227917+(h % 1287)*13) 13) % 4636)*13) 13
  | 4 => packedAt gbK4 (2821+((h/13+packedAt gbK4 (2730+(h % 13)*7) 7) % 80)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff03fffff01fffc07fffff80109f9f9cf3f3fc
  | 1 => 0x3fc0f81ffe0ffff83f007ffef6c6ce34c7ccf
  | 2 => 0xfffff001ffff03fffc0007fff07070ff8f8f0f
  | 3 => 0x3fffffe000003fffffff8003f807f03f00ff0
  | 4 => 0x3fffffffffffc00000000003fff8003fff000
  | 5 => 0xfc00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x24005282700144c0051534818005858c11b15c
  | 1 => 0x211405909520e95483a0552a872c2ca14454c5
  | 2 => 0xcaaab0212a5a02a96800a255305050568a8b0a
  | 3 => 0x43cf29740308233e72cac0063b807a03e00ea0
  | 4 => 0x83f3ce79cf9cb00c208300183dfa8003ff6000
  | 5 => 0xf08200400c10c030430c04603eff7ff8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36675
namespace PEqualNP.Outside.L_meta_36675
open PEqualNP.Outside.L_meta_36675.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 3 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 14 := bs1_4_0
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
theorem bs2_3_224 : Interval s2Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 227 := (concat (concat (concat bs2_3_0 bs2_3_32) (concat bs2_3_64 bs2_3_96)) (concat (concat bs2_3_128 bs2_3_160) (concat bs2_3_192 bs2_3_224)))
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
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 2 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 39 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_3840 : Interval gbAtlas 5 3840 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3863 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928))))) (concat (concat (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152))) (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)))))) (concat (concat (concat (concat (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)) (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112))) (concat (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 bgb_5_2240)) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 bgb_5_2368)))) (concat (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat (concat bgb_5_2496 bgb_5_2528) (concat bgb_5_2560 bgb_5_2592))) (concat (concat (concat bgb_5_2624 bgb_5_2656) (concat bgb_5_2688 bgb_5_2720)) (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 bgb_5_2848))))) (concat (concat (concat (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)) (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 bgb_5_3072))) (concat (concat (concat bgb_5_3104 bgb_5_3136) (concat bgb_5_3168 bgb_5_3200)) (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328)))) (concat (concat (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456)) (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584))) (concat (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 bgb_5_3712)) (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 bgb_5_3840)))))))
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
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7040 : Interval gbAtlas 6 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7072 : Interval gbAtlas 6 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7136 : Interval gbAtlas 6 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7168 : Interval gbAtlas 6 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7232 : Interval gbAtlas 6 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7264 : Interval gbAtlas 6 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7296 : Interval gbAtlas 6 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7328 : Interval gbAtlas 6 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7360 : Interval gbAtlas 6 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7392 : Interval gbAtlas 6 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7424 : Interval gbAtlas 6 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7456 : Interval gbAtlas 6 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7488 : Interval gbAtlas 6 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7520 : Interval gbAtlas 6 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7552 : Interval gbAtlas 6 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7584 : Interval gbAtlas 6 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7616 : Interval gbAtlas 6 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7648 : Interval gbAtlas 6 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7680 : Interval gbAtlas 6 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7712 : Interval gbAtlas 6 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7744 : Interval gbAtlas 6 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7776 : Interval gbAtlas 6 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7808 : Interval gbAtlas 6 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7840 : Interval gbAtlas 6 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7872 : Interval gbAtlas 6 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7904 : Interval gbAtlas 6 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7936 : Interval gbAtlas 6 7936 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7968 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960))))) (concat (concat (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184))) (concat (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440)))) (concat (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696))) (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 bgb_6_1952)))))) (concat (concat (concat (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 bgb_6_2176))) (concat (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304)) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432)))) (concat (concat (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560)) (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688))) (concat (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944))))) (concat (concat (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))) (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 bgb_6_3296)) (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 bgb_6_3424)))) (concat (concat (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552)) (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 bgb_6_3680))) (concat (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 bgb_6_3808)) (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 bgb_6_3936))))))) (concat (concat (concat (concat (concat (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032)) (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 bgb_6_4160))) (concat (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 bgb_6_4288)) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 bgb_6_4416)))) (concat (concat (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544)) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672))) (concat (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 bgb_6_4800)) (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 bgb_6_4928))))) (concat (concat (concat (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024)) (concat (concat bgb_6_5056 bgb_6_5088) (concat bgb_6_5120 bgb_6_5152))) (concat (concat (concat bgb_6_5184 bgb_6_5216) (concat bgb_6_5248 bgb_6_5280)) (concat (concat bgb_6_5312 bgb_6_5344) (concat bgb_6_5376 bgb_6_5408)))) (concat (concat (concat (concat bgb_6_5440 bgb_6_5472) (concat bgb_6_5504 bgb_6_5536)) (concat (concat bgb_6_5568 bgb_6_5600) (concat bgb_6_5632 bgb_6_5664))) (concat (concat (concat bgb_6_5696 bgb_6_5728) (concat bgb_6_5760 bgb_6_5792)) (concat (concat bgb_6_5824 bgb_6_5856) (concat bgb_6_5888 bgb_6_5920)))))) (concat (concat (concat (concat (concat bgb_6_5952 (concat bgb_6_5984 bgb_6_6016)) (concat (concat bgb_6_6048 bgb_6_6080) (concat bgb_6_6112 bgb_6_6144))) (concat (concat (concat bgb_6_6176 bgb_6_6208) (concat bgb_6_6240 bgb_6_6272)) (concat (concat bgb_6_6304 bgb_6_6336) (concat bgb_6_6368 bgb_6_6400)))) (concat (concat (concat (concat bgb_6_6432 bgb_6_6464) (concat bgb_6_6496 bgb_6_6528)) (concat (concat bgb_6_6560 bgb_6_6592) (concat bgb_6_6624 bgb_6_6656))) (concat (concat (concat bgb_6_6688 bgb_6_6720) (concat bgb_6_6752 bgb_6_6784)) (concat (concat bgb_6_6816 bgb_6_6848) (concat bgb_6_6880 bgb_6_6912))))) (concat (concat (concat (concat (concat bgb_6_6944 bgb_6_6976) (concat bgb_6_7008 bgb_6_7040)) (concat (concat bgb_6_7072 bgb_6_7104) (concat bgb_6_7136 bgb_6_7168))) (concat (concat (concat bgb_6_7200 bgb_6_7232) (concat bgb_6_7264 bgb_6_7296)) (concat (concat bgb_6_7328 bgb_6_7360) (concat bgb_6_7392 bgb_6_7424)))) (concat (concat (concat (concat bgb_6_7456 bgb_6_7488) (concat bgb_6_7520 bgb_6_7552)) (concat (concat bgb_6_7584 bgb_6_7616) (concat bgb_6_7648 bgb_6_7680))) (concat (concat (concat bgb_6_7712 bgb_6_7744) (concat bgb_6_7776 bgb_6_7808)) (concat (concat bgb_6_7840 bgb_6_7872) (concat bgb_6_7904 bgb_6_7936))))))))
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
theorem bgb_7_2592 : Interval gbAtlas 7 2592 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2608 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)))))) (concat (concat (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)))) (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 (concat bgb_7_1728 bgb_7_1760))) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 (concat bgb_7_1888 bgb_7_1920))))) (concat (concat (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 (concat bgb_7_2048 bgb_7_2080))) (concat (concat bgb_7_2112 bgb_7_2144) (concat bgb_7_2176 (concat bgb_7_2208 bgb_7_2240)))) (concat (concat (concat bgb_7_2272 bgb_7_2304) (concat bgb_7_2336 (concat bgb_7_2368 bgb_7_2400))) (concat (concat bgb_7_2432 (concat bgb_7_2464 bgb_7_2496)) (concat bgb_7_2528 (concat bgb_7_2560 bgb_7_2592)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 50, 58),(inputs.getD 4 zero, 42, 58),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0eeeaeae0eae8eac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372960 * 2 ^ 32 + 3941132992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36675.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.or,[1,2]⟩,⟨.and,[5,6]⟩,⟨.and,[4,7]⟩,⟨.or,[8,9]⟩,⟨.and,[3,8]⟩,⟨.or,[3,10]⟩,⟨.and,[0,12]⟩,⟨.or,[2,11]⟩,⟨.and,[1,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 3941132992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 3941132992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36675

open PEqualNP.Outside.L_meta_36675 in
theorem PEqualNP.Outside.L_meta_36675 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 3941132992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 3941132992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
