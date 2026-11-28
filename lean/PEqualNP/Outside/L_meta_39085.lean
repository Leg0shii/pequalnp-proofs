import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_39085.Model
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


end PEqualNP.Outside.L_meta_39085.Model

namespace PEqualNP.Outside.L_meta_39085
open PEqualNP.Outside.L_meta_39085.Model
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

def SBf (j : Nat) : Nat := [6, 6, 7, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_39085

namespace PEqualNP.Outside.L_meta_39085
open PEqualNP.Outside.L_meta_39085.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1000de43dd43bf439d43bd43
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x100581985050f2ea2a1c755243c6292879b5050f28a2a1e3d4943
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x100003105114143c11485150f085214143
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 5
  | 3 => 7
  | 2 => 3
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
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/8+packedAt s0K4 (80+(h % 8)*3) 3) % 5)
  | 3 => 2*((h/9+packedAt s0K3 (189+(h % 9)*3) 3) % 7)
  | 2 => 2*((h/15+packedAt s0K2 (114+(h % 15)*2) 2) % 3)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfe03ffffe03ffff03ffff03ffff03ffcf8fe3f
  | 2 => 0xfffc07ffffc07fffc0ffffc0ffffc0ff3f1fc7
  | 3 => 0xfffff80fffff80ffff03ffff03ffff03cfe3f8
  | 4 => 0xffffffffffffc000003fffffff003ff
  | 5 => 0xfffffff0000000fffffffffffc000003fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x229850a2238912300b2cb11554b11554586e1b
  | 2 => 0x4429314444872452c0555544995544992b16c5
  | 3 => 0x8850a26889120e95550269a61269a6128da368
  | 4 => 0xe162c58f122448e9a6980c30c38e38e3f001b6
  | 5 => 0xf183060e1c3870ee38e38e38e00c30c3f6d800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0fcc0fcc00000fcc0fcc0fcc00000fcc0fcc0fcc00000fcc0fcc0fcc00000fcc0fcc0fcc00000fcc0fcc0fcc00000fcc0fcc0fcc00000fcc0fcc0fcc00000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_39085
namespace PEqualNP.Outside.L_meta_39085
open PEqualNP.Outside.L_meta_39085.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xbd43bf43
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/1+packedAt s1K4 (32+(h % 1)*1) 1) % 2)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x80ffffc0fffffe07ffffc0fffe07fffcf8fe3f
  | 2 => 0xff03ffff01fc0ff83e0fff07fff83e034f1fcc
  | 3 => 0xfffc0ffffe000fffc00ffff83fffc0038fe3f0
  | 4 => 0xffffffffffffff000003ffffffff003ff
  | 5 => 0xfffff00000000fffffffffffc0000003fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xa6082046244842014a12c42946214a98186e15
  | 2 => 0xa58c48a1c915658168555259aa92c294b16cc
  | 3 => 0x14316914483a6aaac109a6b12d3588528da370
  | 4 => 0x58a28e2091230d34a5a0308431c63163e001aa
  | 5 => 0x60c30c38e1c38dc739ce38c601842183f6d800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_39085
namespace PEqualNP.Outside.L_meta_39085
open PEqualNP.Outside.L_meta_39085.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x8624604000004809400001200b045003016440101fe42bd43fe41fe20ff40fc31ff32ff41fc41fe21fd21ff21fc10ff20be42fc43fd10fd31bc42fe10ff30ff31fd40fc21fd41fe30bf43fd42fd32fc30fe32fd43fe40fc32ff43ff10fc20ff42fe43fc40fe31fc42fd20fd30
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1a3410000280000000a80021401b70080d700581020000010003808508001911e040013c00027260810300000800200016525b3ea6a1cf55032b629283ac424833a86994f94b43cea18613d5490e78a8995b94b319f2a0633e54882dca5206b10821d6216653f54486eca39957d4d108ea98859d434c678a8905754c41d7a92876f525067aa998cfd5232cea1c613e540c27aa9104f54c429e292877551ccb58a4a1d754c10aea98853e54ccae8a2905b948309faa2655e53106daa5204f550109f290855e5310b3aa6215714d20b6a90216d520c278a9195dd45209f2a4433e5404278a8885d94430aea9c433e54cc33a87996b10a21baa88613d54cc2bca6085714d10cf298855d53d0278a890cf94a42af29c433e54cc6daa598eb10b209eaa6655f534835884194fd51109f2a0879d43cc67aa7214b14943b7a92876c5250e7aa8184f95032af29e813f54482dea4886b948429eaa0636c524427aa910db94810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x18118400102004000000c8000004118802828c6250e30a3189430c30c5310920c550d510c22c6255031c394c428870c6254c42a358c424830d43548308b594420ca1d63151218b18954cc32442145208758e54883244294732c550d51cca8c6250f32a358c428868d6310b2087195434ca8c6250f31c350d52cc68c6250d31a358c420868d6310b32
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x20200282b988528e65411c94354732a08e4a1aa21840d7614c4248206bb4a621443415cc4214520
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s2K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/58+packedAt s2K4 (2430+(h % 58)*7) 7) % 90)
  | 3 => 2*((h/29+packedAt s2K3 (950+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s2K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 1 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 3 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2004088824020000a41280444022914810d095
  | 1 => 0x451891064894a12c0a852429921422b146264a
  | 3 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 4 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_39085
namespace PEqualNP.Outside.L_meta_39085
open PEqualNP.Outside.L_meta_39085.Model
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
end PEqualNP.Outside.L_meta_39085
namespace PEqualNP.Outside.L_meta_39085
open PEqualNP.Outside.L_meta_39085.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x844000400204000300310b1400003400400000010000041802c100004002aff31fd43fe21ef42fd42fc32fe43fc31fc42ff43ff40ff21df43fd21fd31fc20fe42ff41fd41fd30fc21ff10ff20fd20ff32ec42fe31fe40ff42fc10fc43fd10fc40dc43fe10fe41fc41fe30fd32fd40fe32ff30fc30fe20
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x6657e548c6f8a4a1ef90c42bf29485ef42903de85987b4c920be29283ec42486faa1a1db54830ee21a81ef424c7b8a3a1fdd0541f729021df4310afca220df94c41efa1a637e53483be87987e84010b7294857f51502fea0a0df15131efa1c81ee5410afea690fdd0610bf29c855d53043de85885f55230fda82839e5410efca710f710c10b7294837e5190afea2907b14442ee29a817f52042faa01977d0e32efa1e217d51842faa020df95032be2a2617e520c3de84195d14540f629e85de51d0fbca1a1dfd4c20bf284857d54903dca6217b48020bea9687ed52903f460187bd0a32bea8463ee4310afca8187bd0821f790c437f5050efca1085794c10bfaa661ee32486fca7a0df95021bf2a621dc430c3f641107bd0f42b629281f641106fca7085fd5132bea8685f7314c6faa3a17750c43f7a1421dd324c6fca1195f14b10f7a1683dd32cc2faa921df95131ee21c817d528c2faa8985f14c21bf284617f514cafca2197b88120dea0883fb20482f8a8085fd5310beaa041dd5110fb8a221fb94a41dfa1c87ec42c83b886217710f30ef29c81df43d06daa4085f94831efa90875e53082fea918ef90140f7290617c53442faa4887d10410ee21a637e539079a64195f54042bf298617e53443de42905f55110bc282837d520c2fca5a07bcc932be2a463ec42907bc64995fd4f21bf290657e528c6eea2a07794043ee21e217e50d06fca020df55120be2a063de5210ef8a9086fd0641ef29c857f540cafaa7a05f54e31fd884217e50102fea890df95221efa8687ee32c82fea5887b10940bea88877d500c6bea6a0fb10910ee21c65ef52506fca5885f94a41ef984617c54c43daa41877d0e10bf288857c54c82fca20877d0c32bea8865ef42506baa720d714d41eea9821f5310c6fea6a06f90942ee980617f504cbbaa3a1fb10810bf28e87dc50d0ef8a9994f15132beaa063df434cafca7907bd0932beaa243ed32486fea990dfd5110f728e85f451503f680a077d0d41dfa0a817e51ccafca3905f94043f621061dc43d07de8510fd88421ee98a61fb308c2faa3995f55132be290215d53903baa021f7d0c21ef29821f9300c37c82a0fb48421eea98437c54487bca821fb54042f621e85fb40043d88498df55232bf2a6617f53882f8a990fdc8621af29c85df43482bca610fb50c42bea9e83df31cc2fea9085f54043bf2a0877d531037e80205f95041bfa8a87dd320cbf080085f54e42f710a43dc430cbdaa418df14143ce21c857c54482f8a790dfd4f20f7a14617d53086fea6905f94343bf296637d510835886217b54810efa1c43df43083d885987b14941be29841bf4290bf660987bd0820bea90217f540c6fea098fbd0a20eea9841ed32c83eea2a07bd4042ee21a65f510042f8a4a07b10a40bf2a2217e51903f280207754e41
  | 1 => 0xd520c6faa9085f95210bea9a41ec4310afaa5a0fb10941f7286857d538c2f8a2985f54720efa1c636c52506faa3207b10821b729481dc4350afca5a1df94443eea9c81df43106fca818dfd4943f7190657c53842faa2205f54d21bf294217d54cc2faa120df94c31ef29c837e54c86f8a5087bd0841ee21e81ec5010afaa3217e88020f6a94837e51cc3f220087b54442e621e857e52106dea4a0df14d42beaa263f920082fea4a04f95010efa1e857f53042dca8216fd0c43ef99065ed5290fbc60985f54021be29a41ef52503ee820877d0d21bf2a081ee32c875ca8217b14342bea98217d50887de8490f7d0e43ef98a61dc5210ebca821fb10a21aea98437e508c7d884106f50040bea9a21f610442faa321df94c10bf29a435d5390abca7205fd5030b6a9481f721487ee6318f710c40f721085ec42102faa8197710c319eaa0217d50cc6fea2985f95232c6218857d518cabaa6105f95020beaa485df43906fca6207b10a30f621441df324c3bca6105f15032bf28c657d5290efaa5a07bd4342be282837d52106fca890f7d4d41dfa04817e51082faa520df94240f721e85ec42482f8a498df94431fc282836e5290efca318f710e31bfa9263dc43d0af8a2907754b43efa8887ec42c86fca6197b14742efa9a857c514cbdea7a17bd4943f621261ec42cc6fca48877cc030efa9a81bd4210afaa918df54630ee21a437e53882fea090fb4c832bf2a461ee5290fb8a6a0dfd5120b7290217e53082fca320cfd5132de2a265df52d0fbe87907b48720f7a1641f110043f620885f94a40f7192417f54886d8a4a1dfd4941af29c877d54087ec6218df15220bf28483dc5010efaa5887754843efa8087ae4310bda84215fd4d41bea90877e510c3be6598f754343bea94437e5410afaa1215f54f10be298217d54c82b8a6a073d0c42f621681ed5310bde84885f54f20efa1a21dc5350afca010dfd4a10bea8c417c540c3ba63985f94840be2a661ee520c6fca9106f95010be29a83df310c6faa720efd0740f7a12817e50c86faa1a0df54c41efa1a817d51d02fca198df14540bfaa6657e54042fca6215f94440b7290617d54882faa2185fd4910efa18217e54482fea9105f94032f7a1021de53086fca5187b10b32dfa1085ec5310bdaa1a15f14e20bea94817e5310efaa99977cc631bf29021f7108437aa8087b10831afa9a857e52cc2fca110df15221beaa443ed51d0afaa7205f14132bf29487be4350fde65197b14943bf29843ef5310bbea3a1df94740ee21e417f53c43da87a16f50740f7a1061df430c2fea2a177d0d43bfaa6417d540c37887215f54a10be28a85dc43906f8a810db94831e621885ef21086faa7085f14930f6214637e50d0ab8a6a15f15331dfa0883ec42106faa8087b94a40f6996437e52082fca8997710d10bea8
  | 2 => 0x280a04886008160e80a0003c22966000a0048060d02a008201a802000060d0005b04c000500b8000401e3e03c0580806000018181d020038ea000120080806840018440e8000201e07056158021c042000021200206806048000282e0c00e1a00000034018c80980621054218004c010140000d84000000be802045600100000800108065300c038b6138080201a000000e8460000a0d8120c8140007408804688000a8140581e0b8680700219a2e058080106408038050200000e3a858068000380c0207200016018020003e0002e00008080520800a070000d0022900e0b8140b81400820258161304a0d01200000000000101c7481a038ba188000300a00824008000103000002130080011403000000000b82e0200c01014068120016a13804009124385a0000c0802069006878000080004000038240d812010e20f066088ea0404a870240300c138002b8361980400016028022601e7a000540920b000020081784c000222f00203806018001080200868138561f0000100201001ee53d0afca8987710e10efa1c417d53083dca2215f14f20bf280637f540877a82a05fd5331efa1c61ec42c437ea8995f94332be29a437c54443b886a0df94630ef218877d53d0afaa3a1df14543ee21c857e54c83d885195f94a32f7a12417e54cc6faa710f7d0d30bfa82857e5210b7c87215f94042f7a16437c53887b88610fb48520bf28021df43c87f681205f15230bea96617d538cbb8879977d0f31efa1c857d54c86f8a9195f55241f7a1261df32cc3ba6218df55331bea86437d54c43bc6298f7cc931f629281ef42cc7f681885f94843f7a88857e53902faa4205f15132bda82836d520c7de85215fd5130bfa9843de52d0efca310fd10610efa1e817e5390fb886107b10b41bea8e617d53883baa7215fd4930f7a1483dc43887de40107b54f42be29a817e5090fde86215bd4943bfaa4657f53442f8a8105bd4940be282637e52d06fea898fbc8220dea18877e51d0afaa518fe90040bf28c41ef42d02f8a7885f54442bfaa041f840c439e87a15f54243bf29e43df328cbba64987710e20bf28441f541106bca720df94421bfaa461dc438c2faa1195b54a43fba0c83df4350b788621774cb31be28243ef51d0bb88620fb94042bf29e81ef21c82daa520df94f42f7a12857e50082fea7087b10932bea94417c52442fca7887710d20bea9e43dc52d0fde85997710f21bfa9a857e500c3de84205fd4e21fb88021ec420cbb886985f94643efa1e657e52086faa598df54c42efa1863dc43cc7be86207bd0a31f7a10639c4310bd8850857d4d40bf2a6657c5050afea8087d48421ef288877
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4540ca6f65480209e580540cb2e43149439b588514c32c62550109b58b544c33451d05409b594420435b43d4141e310c428c25c6454c10b65805210f1f63151329b988530834f43d4940b358a51d0f4d524c431b3588430ca3c6454d109b597420438c43508429dd95100434c4354810d6d4f50506ce6394742d3d0d520438c4310940b3d95320ca786055121d394f420826f65d08309798f540432d5494810cb950428c26e65d09419bd89544825d6314520d394c429072f6295010ba9805110b8d6510c428f191534878c4310a328fd9153486d960144439b992520432f62151329b191520c78c43d4442b398b434ca3c6454910e39904310a6c62151208fd91534426f65d0831b39885110f4e544c832cb950420425c6355110e310c424c6cd6214043c795043cc2ce6390c4297d95300c32d5410a309b59652042ce63144429759743042ad6290c42f8109100431e5410c3197594430c2ae6390c42c7150434878c4310b21cb150424c25d6394742d354d200825c6355020e310c424834d53d0810e310e5010aea6014c42ab19132c82cd6394742d394d529026d6215030cb150424cace644c832b99845310b8e6010c42cb950428ca5f6355221d3d4c525028c644c832d354e52043575314540d5d4651d0f8e6510c429e580540c6cd6390842d314f525026f65d0810cb18a54043685214141b39904310a5e65d0d309b58b530429c6350842d5d4f51502d8604c53097d97430826d65d0830e310f5010b1e5410f32cb150424425d63d5021e39504310b8d6110c42d354b300c33860550109758f548865e6314121c7d50434426e62d50109b988540c74f53109419b58b540c25d63d51219798c52c426e62947408f993530432c54cc9329bd95320cb4f53d49419bd89548c74f43d4941e39844310b3461550109b58a51d0f4d3254432d314c425066e64948309718d54c836842d41419b588538436852d4141d394f429029c644cb31d314d324826f62551319758c540425d6314b109bd89548431d5410c10e310c42c42e661d0921d354b310c66c625503097596530874f53d09409b195324867561150309e58354c866e6294f419718d544829d6510e429b98b548c2e96014c429ed95300c34f5294b439bd94420434f53d0942e310c42cc26d6590c429798f544434c43149419bd8953442776550441e31944310a6e6214c10a7191324c34c53149419e181534866d62d52309758c504878c4310b31cb953428826d6294740e310c420c2766115030cb550428cad66114043e3d804310b4f4394a43b39885010f4c53d4941e310c424423d64d4c10d354f4290a6f6255130d314f425066d6214c10ec551100425e63d5210d394f420427b60551319718d54c867a6015021cbd50424caf06050441d9d4651d0a6d6510821cb153424831d5410e20
  | 1 => 0x34f4394a40d310e529023f6454d2097d8d54842da6014843b358a4310f4c534c921d354e529078c43944429798f540c65e6510d40d314f425027b6054d219b58a50d066e62d50319b58b540436451485209798c52042cf6350842d610c505069c644c832cb95042c878d6010c429b58b544c72c54d092197594430ca6d62d5310c7953438c7695014042bc19110043655114442ba580420823e6495132d510f515038c6110c429e98053c874d53d0a40d354e52902cd63140429d58453c823f64549109b58b548c75b4314141ab19132c866d65d0831c7d8d540434e5310a4097594430434e53108109758f54c86766115020b95845010a6f6548421ecd07400434f4354a43ab1894310f8d4310c429bd954310b5743145409758c52042756510410c7950430c31d5454c10bc185401035b53141419758e50d0b7051d01409b594420c26d62d5330d394e529066c6255330d310c52502cc6250c4397997434c67b60551219798c514834d5348421c7150434ca6e65d09329b98b544c78c4310b40d394c420874f43149409798e51d02776155110a798a5410e6e6214c21cb550428c65d6510c21b5987434c78c4310832f4d0d100434c4394831b398a50d0e5e63d5321ec951100426d62d5331d354c5310a5d63d5310c7950430ca746154d209798c540435551144439758e52d072f62550109798f520426d6510820cb95342ccb4f5394f42d9d48515023e6414c10d3d0e520c66d6510832c7950430425d63d5320d310f525029c644c9319718d548834c534cb21e310c42cca5e6394b40d354d529066e62d5130c718d54042cd638c832cd553410434d524c030f410d100431d5410e21c7d50434ca5e63d5032c7953430438f644c832e3d844310b1e64950439b98a50d0f545314540d3d0e529065d6510c3197d8d54c825c63553109dd95310c65e63d50209718d54486ac644c921d514f515026c62553319b189544431c5410d109b189534431c54d0d308f990540427b6544010b398e4210b1c548c932b6983434c23d64d4e219b189544c66e62d5021cb950420cb5853d4141cb553420425d65d0c21b55845010f4f4314943c7153434cb8c4310a10bc586100432e64950429b992520c71e54d0e32d354f420834f4394830f8549100434e5354a41d314c525026e62d53108fd95411065d65d0c209bd8954cc66e62943419dd85544834c4394830da108505067a6015032d354c429066e6294743b318d4210a6e65d0921e39534310b4c43548319758e50d071d5494c109b988514c38c6010c42b6580430c2ce62947439798c540871c5410e329ed81544434d53108219798e50d0b644214540d910b515025d6314910d610f505074f43548319b58b544438d5310c429e596100438c4310a41c7953438c32f541093197d8d544c72e54548109d98
  | 2 => 0x62550319d98453c827661d53309b191520431c4394842e310c5010b8c4310b20d354c420834c53d0942cb5964310a6d62943439758e52d026d62d52108f993538876742d4540dad08505072d5454810b358e50d0a776154d20d354f429078c43144429dd85544c2746155130b3d894310e6f6255010e39884310a5d63d51109d58754cc25f63553219b997424836b5214141c718e540425c6355021cb95042083674214540d314c425025c63550109758c540834f43d494397d97430425c6454c2197d8d544863e64d4e209b58853c42e96014442d6d4250d0e7960d5331cb58b544ca5e65d0d429b98b548c66e6294f409798f544863e64d481097d94430866c62553109798f548826c62552319bd89540c78c43108219b98b54442e56114c42e398c4310acd63108329bd89544cb8c4354042b59845210e7765484219b98b54cc26f6510831b358c5110af36544010d35485210f8d6210c42d310d520c34d53c84219798c528423f65500409b189544c34f43548309e98354c871c5410d20d394f4290b4d5354810a719132cc25f6355132d394f429074f654c8329b98b548426c62552108fd954210a756115032f494d100434d5354a409b98b54cc76752d4540ab191320cb8e6410f42d3149324c26f6510830c758f544cb1d5310e42cb953420425f6510c10d5d0f515038c4310a40cb953428866f6255110d394c420826c654c920bc58041042cc644c832e310c42507e3424401097d8d524432e5494810ab5964310a6c62550109b58a53d066f6255310d3149324c72e5410a319798f540865e6510d42d39534310a5e6494c2197997435066d6294f409bd8954cc34d3254032cb150424c65e6394341f8949100434c43d494197d95310c65c6355221d310e529074e5410c42d310e520434f4354a419e98354cc6b86050740d354c420423d6414c108fd954310f2c54d09329798c530432e5410b20b398a4310e5e65d0d329b98b540c27561150208f990520431d5410f329b58b540c6ce63943429e594400427561d53209798e52d06ce6314042bc584400425f6550c43e394c4310a7461551209798f540c2da6014443ab191324825f63550219758f520434f53d0941dad0b505071e5410e21d3d0e520426e6510941ab98e5410b8c4310a219798f548866f6255020e310c421023c6454d20d310d529067a60150319718d524425f63550309798c524426f6255121d65405010e6c6454830d9148515027b65500409b98b540cb6452d4540a398e4310a6e6214810dad4250d0a5d63d5220d614c505065f63552209b594420c65e6314c21c75944390ae661140428f590520426f62552309b994425038c644c832b9584420866e62d5020b398f424ca6e65d0940d394d520436b52d41418f994544ca5d6394740c795043cc65d63d5210d510c515
  | 3 => 0xa3c010185300c1900012430293b0001200707c030103005c090e0100302c0dc340140100414000000380315c000457c0000074c0002c03000340ac510046600400000632c004000140000201c0e0380001c1f1b2880c8001480003c009ac32024880080d000040c65f06c000580300068004112888c0180200000934000780f01c0a0e000544020140454ce600002498030d40b0f080004090141e01800000cc0ac000f40006000000130026b0002d015615180f0a088009d77b8000bc0301c001588100802078000080a0784b000c9b1d270643505c51300004d000004000341d000080000004c071a801050000080203003054040018500c060840d004001f4062f00114005224a9004030d8040000d0080204001005cc0000b04000295ee09c910380801cd30082f00402020a0070610400112c250b81b51c260025301c000000400428154080ac010901e03c004ea41a9c01e310c424871c539094297d8d544c32e541082197596530838c4310a208f593520434e53948109bd89540c25f6355120d354c429026e62d4c109758c540865c6315130dcd04505078c4310b419758c528427b6548020c7553430427860551319b189548c25c6355210bc991100425e6494c20d3151320cb4d53c80209758f544838c4354442e310e4210b2f5410930d3d0c525065e65d0d409e58054086d56114843b5584430c66e6214e10d5145314c34e53d08219b98853c425e63d5120e3d944310b4c534cb209b988504c71f5410d219b988540431e5494c108f596540423d64d4e20ce553400425f6355020c7951530434f5314941b358a50d0e6e62150309d98754c825d6510c20ba181214834f53d4940c7153434c6ae6310c4297994435072f5410910c7d5043482cd62144439b588504c74f531094097191530826e6214d109798e51d0b4f4354a40e310c420c7d15344010e310c424c37365440109798c530832c5410b32e310c421065d63d5010c7d8e540425d6594c1097d95320cb8c4310a31a798e4310b2d5410810d310d529025d63d50209e58053c865f65d0c219798f54c426d621501097d8d540425e6494c10e310c420434e5394a40ba983424825f6355110e310c420831e5410e209798c540826f65508429b588534438c43109329b588540c74d53d082197d94430825e63d532097d8d54c426c
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x28097010e0090c0c118860200080080002d0a2400b02001803c0400f0a200000a14101140019201915895114443a1ce7aa08488688435805110a87ba88621021239d2644c832c18c6312a80854571151320caa4b80a899065a81904244010c8ac6a88a221688439805110b06320a89906543dd44310821838e8b18a48860c5498f424ca863a2a621041629c06110c42a18e8992a0197044310b5150286392a821821615c46510c42b12e032886217084310b5050722a9ac22988583190534cb21a1eea218841050c7454c4204324a9ac029885c110c4214540c18c821aa408586711944310b4221ac22808583190534cb20c18c92a2641950d7510c42042c2b88c02188583190534c921a92e021aa4185517510d10043483208688021c85515244010ca2a2b00a221e0c5498b434cb06320a69924183190524c931b14e032886215617510910042163a2c429a2183dd4644c832d0ac2308862160f6510c4204330b0aa02808583190524c930b0ce2300862160c6318a5404388aa2a688021c210c4214141c92a6b0084107804310910042a2b88a699641c110d5114442c1eca2188418684439845010b0632086a9061925895014043a18e8992a21960f6510c420c707b28c899065525c0534cb21a18e8a988410f08435405010ac4b80c221885a25806010c42c18c821aa418d0e72d504344330a8ac0288859154d6110821a18e6aa08408649635405010aa2b8886a9063915496114843c1aca218840850c721504348328b0aa028087925496014843
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x60056005200c04645c4534cb20d017510c4244010c04645c44354831a048454d6110821e00435855014042b018510c4244010c08645c04354830c81615c06110c42c08645c0544c832c08645c0534cb21e00435456014442a088454d6010820c81715806010c42c04645c4544c832
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 779
  | 4 => 754
  | 3 => 85
  | 2 => 14
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
  | 6 => 2*((h/42+packedAt s4K6 (704+(h % 42)*6) 6) % 44)
  | 5 => 2*((h/308+packedAt s4K5 (21033+(h % 308)*10) 10) % 779)
  | 4 => 2*((h/272+packedAt s4K4 (28652+(h % 272)*10) 10) % 754)
  | 3 => 2*((h/49+packedAt s4K3 (4165+(h % 49)*7) 7) % 85)
  | 2 => 2*((h/11+packedAt s4K2 (840+(h % 11)*4) 4) % 14)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ff81fffffffff81f83e1ff0fffffffa071fff
  | 1 => 0x81ffe07ffffffffe003fe1ff0ffffffc38e3ff
  | 2 => 0x1ffff80f01fc1ffffc001fff1f07c07c0fccc
  | 3 => 0xfe000000ffe001fffffffe0001ff8007ff00f0
  | 5 => 0xffffffff000001fffffffffffe000007ffff00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x44a420a12448880590a0a505254a552030d55
  | 1 => 0x28908914248911160214a0a504a94aa41862aa
  | 2 => 0x54e1452641d21baaab408936613c7036c0b4cc
  | 3 => 0x18c5965889039dcd33a6cc0441ce60c76d00f0
  | 5 => 0x610618600e1c2071c43911c888000301b6db00
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee8fee888888888fee8fee888888888fee8fee888888888fee8fee888888888fee8fee888888888fee8fee888888888fee8fee888888888fee8fee888888888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_39085
namespace PEqualNP.Outside.L_meta_39085
open PEqualNP.Outside.L_meta_39085.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x50001400102c10171020c00000c02c0080000269008001000302282fd30ec42df30fd32dd30ff30fc31fe32fd31fc10ff43df43fe10ff21fe21ff10ff42fc40fc30ed20fe43ff41fe20fe41fd41fc42fe42ff31fc32ff40fd43ef20fd40fc41ff32fd20fc20fe31fe30fc21fe40fd10fd21dc43fd42ef42fc43ff20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x265ef42906bea690df14940be292837c540c3baa7205f54740bf28c87dc5010efea998dd94440ee21881cf43483de8510df94e41efa1c81de53087bca6105fd5230afa9a85df5010ebca721db94830f619241df43503eaa2205b54042f790c43dd324c3de8498df15110b6a9487df4310afca621774c020beaa4437e53087bc86985f94c10fc28283de43cc2faa51877c8730f7a8e41ed31c82faa2107710e21b729421df4350efca710d754c40bf29c417d540c6bca6205b14941e698241de524c3ba8621f710d20dfa0c83ec51c83f260185f54a20efa1a43ec42ccbdea1a15f94e10fd90241ec30483e8830877cca329f2a021dc424c2fca1995f14142f729e415d53882f8a8997750130b6a90639e5410ef8a990df94232fa908437e5290efaa7085f94f42bea8487dd214c2faa020df15232af29c85dd52d0efea8905dd4540ee21883ef214837c82a0df14540ee98e617e51906f8a7905fd5032f7a1465ee528c2dea498fb4c832ee18e61dc51d0fbe61905b15320bf28c63fb308c3b8a2985b94a41beaa261dd43cc3ba829877cc631bea80657e548cbde85107bd0720efa1e81df310c6f8a810f310f20b72a241ec51483de41105f94210f720e41df30882baa720df94740bfa9c43ef42c82faa5085f14f10be298217d52907b886087b88720f7a1243ee32c83d885085f94a41bf2a265de404c3be86a0df95210efa0e61ed31483be8798d754c10bf2a665ec524c77ca8087790730fb90c437d53c86dca8217755130f710241f710842fca3a17b10b30dfa0883df43442baa1a1f7d0b30ef196617d53903ba6598f7d0d42e621e857d52886f8a498fbd4520faa0a217f53503dca8907b54a43ef10e617e50902faa6885f94410efa18437c53483be62987754843bfa9c217d54ccbb88618fb50f42bf29681df5210edca4105f14d40f7210857e53486bca6185795330f720a417d538cafca218df94221bf2a6417f54cc3b887887794c40eea1261ef41483de6410f7d0130f7a82415d53082fca3987708530ef2a087dc54cc2fca821fbd0920b6292817f504cbbe60907b94f42bfaa4217f5250ef8a9887b50f20df212857f54ccbdc64905fd4141ee982217c504cb9e86215b54a30bea9087ee21483daa6907e88020aea98437d538c2faa4205f94220bea9a43ef52502faa9885f54242bf28c85df438c3bca7087754c10bf2a243ec420cbbaa7087710d40bf2a4617e520c7b886995ed4141bea9e21de4310ef8a8087710d30bf29887dc43083ec8220fb4cb21f7a1021ec420c3d6a0907b94a40bf2a065dc50d0fd8839077d4d42be28a61ee52906fea098df94442bf28e41cc424c2daa51077d0c32bfaa4417c52042fca4085f94c20ef182617f53c83dea7a15f95231bea9661cc43482faa9195f55121b729487ed5010afca221fb14f20
  | 1 => 0xe53c86fea6087bd0b32bf2a4417e50d0efca2187b08520bea98435f535039885985754e40bf29481df414c2fca1a0fb48110bfaa0437f53443bea8986f90d43be282877c5150ef8a910fb54a30f6212617d53c83d884107bcca32efa1e41ee51c83d884995f94842ef20a61dd30883b887217794043efa12617c52843bc64985f14e10bf29463fb405039a64195fd4142f721885ed5110abca821df54f41f7a16837f52842fea4a07b10d20bea9c83dd434c2faa3185f14c21f7996417d52cc7ee8320df94a32f6aa6417d50d07bea6a0f7d4730ee986417d54086fea2a07b54810bf2a083ef42cc2faa021fb8c120eea8087df43886fca121f714d21ef29661ed54482fca420f788530dfa0081f621087b886197b10940f7a1083ef32887de8598f7d4f40bea94637f54c83be65987bc8720fd08021de5390abaa7185f95031bf29683ed520c7de64905f54a40b729081ee5110afea890dd54440f621243ef42842fea910efd0c43f7290617e518c2fca1187710c30bf28483ec42886fca2207ed0240efa1a41f541106f8a9995f14532f6280857e544c2fca4185f55220bfaa6437f524c2f8a8985f54841ee29687df43106dea4a0d794c20bea8085be40502fca3a1df54a43bf29043ef20842f8a090fec4210f628e85bf4290af8a6887710f21ee20a61dd51cc2f8a890fbd0830bf29421ef53483dca3a15f54231ee982417d538c6fca990df14d42be2a663de54cc3b887907714d42bfa9841ec42902fea4a0fbcc320efa88877e54c42faa7a077d0c10bfa9e43ef4290bdea5a07794e40bfa8243df320cbbe61085f15032b7294817e53c83bea5985f94b10fba0c217e54cc6fca4885f95010eea9c417f524c6dea4a077d4b43bea9c437c52c43be60187d44010efa1e217d520c79e87a15fd5132f6218857c514837a84217b90b20f6216637c504c7b88698fb10941f7a1065cf43c83ba600877d0c40faa0e217f548cbb887a0fb54f20ee21c837c54cc2fea8105f54b40f6a10855d5390afea6a0fb8c832fb98c637d544cafea2907b94042f6216817c54c83da41085f95120bf29687df430c6faa1997790b30f728a41cf424c3d88410df54c40be29221ee53483da4210fb94840bea8865ec42442fca910f7d0e31dea0e81ef30483d865905f95030bfaa261dc53503f660987754530bea8663ec428c3de8590f34c320ee29e817f544c6fea4887bd4931f7aa6417e51107b880987b54c42bf2a0857d53106fca3197310c42ee18a617f514cafaa1a1774c310ef18a61ec54c82fca4195f14d21ee21e85bf40902fca010770cb30fd90441ec30c83b8a6a0df54241bea9a41df53503b887197b8cb21f6194437c53506fca4107b54a10efa1a65dc5210fb887107b90920ef99263df434c2fca210f7d0c20eea9c836d52902fca72077d0e43f799
  | 2 => 0xc37e82a07b14940bfaa6217c548c2daa520f70c831beaa483de51cc2fea88877d5330fca0081ec42c83dea0215f94432bf294617d54843bca421fb54f42dfa1085ec40482fca0197d84110eea8e87dc43cc7b886a0df14e21f721e41ed30c82faa221fbc8020bf29087ec42d07ec83885f55242f6214837d548c3ba61087794343dea0a81ec31483b886a15b54840bf28c43dc43d02faa3905f94041eea8887dd53083d885197714443f690621ef52507b886887710c21f621441ee31482bea6a0fbc8421f7a9e417d52043bea09877ccb31ef98041ec5310afea690f7d0e42bfa8a857c544c7daa1a15b94810bf29c85dc438c7da819076d4130f7a1a417c53883da64905fd4d42e7982417d5310bbca720df54430ee194637d500c7d8a6905f55231f728685de514c3d8a4a0df14943bf29c876f5250eb8a9987710b30bf28061dd52cc3da43905f55330bf28063dd40cc3bc84985f54640b729485ec50d0afca598fb54742bea9683ec42483de85207bd0320ee21c61ee43482faa8907b4c120b6a9061ed20083dca6215714d21f6a18857e53103de84a15f94242bf29e837d51103baa6205f95110beaa221ef5250efaa7105f14930fa20821dd21cc2daa1a17bd0821ee99065df214c3b8649877d0c30f710a43dc43ccaf8a790de14141aea9c21bf41d03da80905f54b10bf29a217e54083d8a5a07b90320f7a1283df50d0ebca7087bd0b40f6a1641dd41cc2b8a6a15f54730fba0a83fa40103dea2215fd4530ef28e87ec42106bca72077d0f21af29c837c53083f680085fd5031f7a98853d54042fca3995794c21bf28841de324cbbc81987b54520bea86875c53507ba60187b54840bf29865f910043da42905794c10ef2a261ef31c82bca7105b15120f621463ee52043da83905f94331f7a12217d5190fba6218dfd4d20bfa8a877d53043dca521df94640bf29081ec42043d8a2216fd0e43d72a085df438cafaa898df55320bfa8287f7314c7baa7215f14141ef18a63bd40102dca5185f54642bf28c417f53883d887a17dc4010efa1a63ed51c83be63987b94831bf29e21ef20443d843907d8c431bf296617d5490efca898f750b30fda0621ec43c82fca6187710e10f720241ef40483baa4985f54442ae29a817d508cafea7885fd4810f7a1461df40cc2faa190fb15120fda8283bd4310ff620885f54c20ee992637d54082fca9987708730ef98221ef31482fca00877cc230f6a0a416d52043d884207b94a10bfa9621dd314c3d88418f715130bf29a417e508c6faa8197b4c921bf28643bd41107bc6418f7d0f41f6216217f54043be8720f754c21f7a1885bd54043d8a4a1fd14540f7186417e5010efaa3997d90510f6a1241de53042fca620f7d4930b629287dd54cc3bc6518f710f30ef29687df43d0bbe87105f54743beaa6437
  | 3 => 0x1612a00004058121500e5d80c0491a3b4f62580017008000003139e268c40081e000162946409d9c0005e008220208000081478007680000000001be080000382802b68da8260400030808a0800068e60081e16a50110160c8000000e1e0003307602800020081cde6378022a810050383a8a00200000802000980a82a008060187e0083c0002a1b81a0100093816160000681206830ae8000505800006760020201600000523760307e000021b80006800450062001022000050000680c3080a010380000e010000780a0d8a001e1e0800a0a836000022f0440437e370002b000bb86a049ca010002e88e008300b0540e0020400003012410421d8460081602068149320c800000000202203004049380002e4d806005fa008795781c018960000400152020000105630002300780100c07000028ce0281803000008121d8220083e2a01a2323816016148100d87aa7010060002686a0100c038000000c03006030000303e0c02200000080ce00004010000b006070180102c0080a308236f00a6786c1082201064018740303a041161c82c0080c000000580a00b5cf8004088000008a0039c00012030020000a138000380001292086aa00802259780186402004078120485e0001a007e10010b7290637d51883de40085f55240f6a1a417e5290abaa021f710730ee99661dc524c3dea8907d94440efa9a43df43cc3de8418f710c42fc90041df43ccbd88590fe8c030beaa663dc43487d8a7a15f54830f7a10815e544c3bca221db54a10bea8043ee54c83de85887b10931bea9221de31cc3be60085f15220ee206617d518cbdaa520fb8c921bea8443df514c2f8a9087bd0932be2a041ef428c7dea3a17bd0940ef29c41df324c2fca1a17b10320ba28a817c5150bbaa1a1fb54a40bf28085ec41483de87a15f54b43beaa0617f540c2dca9905f54f42f618e41ef20c43ee4290df95040f718e41ed32c83b8a39873d0b30be2a4637e530c6faa7217dd4540bf2a043df30c42fea918df94f40bf28081df51d0ff081887714b30fa988637d54043ee82087bd0f20bea8e85ed20042fea610df54610ee21c81df43842fca010f3cc320be2a241ef424c2d8a498fbd0820f72a0857c540c7d86410fb90f42f6a90615c544
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5250e5d6510c329b58b53842c96010d209b98b540875b43141419b588534434e5410930d3d0d521035443d4540cb553420425e63150209bd89548c75453145409b994425074f4354a419758c548826f6550f209b597200434c544c1209bd8953c4275611522097d95300c23f6454d109bd95320cbcb504c12097594430825d65cc0109b588504c66f6255121d310c524c66e65901208f990540425d6394021b319330c825d63d5221d5d0e511025e6314c10b398a304c31d5494c10c7150424c34d53d0820b398e204832c54d0920b3988404c34e53548409b580524c74e54d0f20d314d32c82746550510cb952520434e5310a10d394e520426c62547409b99252043675214540b358343d0b4d5348010b59845210ed9601444397994435065e65087309b19543483655114520b398f54c826e6295131b398e42c825f654c832d3d4f42487e12044010d554e511025e65d0d329b58b544431e5450330d310d520c2d56114b30d9949511034c5410f209b58a53d065d63d5021e39534310a6e65cc9209b59641c825d6054c109b98a51d0e6d62951319d996414425e6590930b398850d0f1f63950109798c548425e6315010cb153424cace631012097d81539071d544c010d5d0f515025c6548530e3d50424c26f6254730dad8b505074e524c010d394c420832e54d0a2197597430834f53d4b40d354d52102cf63547209b588538425f6354b109b58a500425d6315020d394f429034d530cb20b3d8d41c826e65d0920cd5531004274615512097597300835853d4141b358f51d0b4e52cc0309e980540c7596015330d658c505066c64548319d984540c26e6590d20b399043482766115230d3d4a52d0ecd63101209758c5050a6d6094a41d354e528426d65d0831b3189414c26e65d0931ba58353c82cd63108329b58b548c34e5354a40cbd8a540434f4394831b5185404c31e5410c32d310e520c74d520c831b6983214c26d65108309b18953c434f4354830c7953438c66d62d51309798f54c834f53149409758f54c866e658c9219b98b540ca5e6394341b658352cc25e63d5032c7953438c26e6494830d9d08515034c4394a409798c5050ace63d5120b318d404834c54d0f209b588514c34f5310940b358343c838e6410f42b318d51c834f530ca219b195414826e629424197d8d544c65c655053097594430865e6394b419e58053c874e5394a10cb950428ca5f6355021d3d0d5010acd620c7309ed95401027a6014f2197d94430c25d63145209b99431c82d96014730b398e4310b4d53c8020d394d52906d661d4b43d5544514c2cc6350520d395042cc25e6394b4097d8d51c826d60d49419b98b548c6cf6250330d310d5010acf63487209798c50506ce62d5130b3d8d42482e661d5320e399043c834c524c930d310c52502ce6308520
  | 1 => 0x432e54d08109798c540c26d6590c429d58754c825f6548530c7951300425f635503097195434c26c6254f40b6d8141cc25e6394041b3d8931cc29f6454930b3991304834d52cc431b318d42c831d54d0c10abd91514834d5348210b658354cc26e62d5110c7d50434432c5490520b5584404c25e63d51208f993538866f6255331cb150414834f43948109b58b540434c4394a30cb550428c7674254440d394f420426d6294f40b958450d0ae96014720b9d85544825f65d0c21d910b515026f65d0a309b18954442e960d08409b98b54842d661d53309d58453c825c6354841b958754c825d6314141d354e521025f6354740b99845010b4d53d0a42ba58354c82cd60d0b30b39885110f4f5314b409798f54042cd628c1309b189540c74f4314941b3d8d51482ce6410930d314c42486ce631444297d95424c26e6214c20d394d208434d53108219d584540cb5863d4141b2580424c36842d41419dd95310c66d62d5310d3151320cacd629013097594430c65c6355210b3d8954cc2ce6290530d614c50506cd63d5120b358c5110b4d524c2109d584548c2eb6050520d354c534836a6214141b358851cc25e6314c21b99845310b4d3254032d3953304826e62d5030979974350b574314540d6d8f50506776154d2097597438826e62d5031d610c50506ce63907209b58a501065f6355210d3549310c74d53c8220bc58440c43cb604c320d3951320cb4f53d494197d94430825d6094e42d3d0e528c26d62942439b195324874f654c8329bd94420c2e561103209759421cc31c54501308f593530426d62d52319b5885050eeb6054520d394d200826e6494a10b358b544c34e52cc2109bd815290f4d5310a109718d54c874c53149419ed95200825d60d4d429d185544c26d62943439bd9442842ce6290d30da582544834e53d0a42cb953200434e524c020d3d0c524c6ac6454d20cb950428c71e5410c319ed81544c65d6510c30ba580424426d6215030b3d81320ca6e6214530c7990544c2cd62145309b98a501065d63d5020b358e42c82796015032b358a4310ee960144429d584540c25d63940429bd8954082ce63d0932d5d4f515025e63d5031e39504310ace64cc120d315342cc34e53c8010b318954cc25d6394020b658043843544394440975805350ae960105209b18954c434d52cc0109799353486ce6394742cb15340482cd62143439bd8954482b86050740b658052cc34e5410f20d3d4f425066f6254443e3150434827a60150219dd9521087c96010d209b5835250ece62943438fd9541106cf6350120b658043d023f6454d209b994425035a534c0309798f548872e54d0b32b398c50d0acc6250d30b398e434825d63d4810b6582524c32e5410820d3d0f5250e6d65d0a10d3150424c34c4354840cb150424c25d63943219b58
  | 2 => 0x62d5331d314d324834c43948209b19543c826f6550842d954421c825c6454e20cb990544826d6095120da58054c82cd62d4743b3580434834f4354a408fd954210a6c6254d10da14b505066e62947408f1915348355510c73097d81530866d62d52109b583524c6e56114042b358e414823d6414c109b996304826e62942319b197424c72f54109109758f54042cc6348520cb150434825e63d5110d3d0e5290f4e53c82209b98a53d070c5410930d3949300c34c52cc931d354c5310b644214540b31894310e6f6254740d315330c826d6214f10b398b51d0e6f6550120b3d89404c2e960951209b58a51d02e96010840d394f420872e6415320d354832cc23c6454d109b98850506cf62505309b98a5010e5e6590130cb95140c82e761501208f59352043a44250441b318931cc25f6510c109759641cc2cc62544439758f528426d629474397d8d544c34f53d09429bd89534866f62553109799253082cd62940439b990524c74d53c8010d315043482ce6314720b5d85524c26e65d09419b98a50043c843d41209798f528438e6410c4297596424c25d6510e208f590520425d6394341b358c214826f654c5209ed95300c2cd6310320ba582514838f5410d2097994214c26f605483197d8d52d034d53484219758e509075653944409798e500825e6494c309759642cc34d5394810b318d40c826e6294331cb95042087655114720d914521482d960d0f40f2d0b504c2cd63143429b98854842cf6350b2097594430425c6550730d354e529026d6510a109b19531482cf6250f30b398831cc34f4394820b6580434434f43149439b18954cc25d63d51219718c544c26f62550309b596520432d54548109b580525073451d054097997435034c53d0940d394e521026c62552109759653042ce6214043c7950438866e6294f40c7550430425d65d0c309b992520c6d96095130d3189530867661d533097994435025f6355132b9987424865d6314121b35804310b4c4394810d910a51103944350441b358042cc25e639422197d8d540434c4394840d314d32c865d60d4d21bc181411066e6510931b958453c83cb43d4120d394e529076862d41419dd95411078c4310941d310c525065e6395121d354a320c66f654c720ce55340043544314540b358a43cc34e53d0a41b398b434ca3e64d4c1097d9743842e46154d20d354c429025c635522097d9542cc25e6314b10d354f42882cc6250330b3191304838c5410930d914b515026c6255230c7950430c31f6355010d3153434831e5494c109b59732086cc6350720ba98041482e56110821b358b54cc3684214141c755153042ce621453097d8d544426f6255130b398c51482d461551309b18953106d96010e20d354c53c831d5410e21d394c420c32e5410b20a7d91514c31c54d0d329bd89544
  | 3 => 0x220cd550410434e52cc230d354f20842ce6290330b3189544c25f63553219e580540c71f5410d209b189540426f6255131b358a41cc25d63d5210d395330c831e54d03309799641cc2cf6354442d3951304825e6510d21b3d895110e6d650c7209718d540874c5410b30e310c421025c6454c218fd91524425e65d0d4197596414c2ea60cc5209b997424cace6290c43d3d4c425066e65905209798c514831e5410c1097d8d54c825e63943218f990520432c62550109bd89548426c6454810d55445110edb6055130b318d54c82cf6254530ba580428c2cc644c320b618141cc34f43548319798c540866c6454a309d986544cae46150120d3d4f42502d66110330d3949308425e6494e20cb951520434c43d49419b98853086ce644c832d39504310a6f6510a309e580540874e53c821097d9530082d56110c319798e50d0a7561951329718d544866d6510810f2580424c25c63553109758f544835443544409b98b540826c6454830a7191514c2cf624c5309b58b530434f43d4940bad8141c826e62d52309758e52d034d5310a41e3990434834e54d0b30b3d8d40c825c63551109e181544c66d6590d20b6980424c26f6054a41b6d81514c2746154d209b594420c65f65487309758053486ea6010d20d3549300426f65108109b188544831e5454c109b189544c76751947429bd97420c65e6494c1097d95404c25e6394010e399042cc25d6394010b59845010e5d6394221d314a314c65d6314a10b398851cc34e53c8020d914851502e960d4720d394e52902776155120d354d52907c930480109b588530434c53d4b409b597420c2ce63d47429b597420425e6510130d310d52902cd60d0c42ba58331483734114141f44c1100434c4354a10d354c320875653544409b195404825c6354b10d3d0f525074c4394a419b59442082d96010c409bd954310a776155130c7953430426e629403197d815390a6d6590f20d3d4c424871e641533097d8d54c434c53885219b58b54cc2cc63545209b988504c6da6014443d354f420425e64951309b99742502eb6054d20d554451cc2cc6355120ab191514835743544409b597420826c6255130d354f320878c4310b41d354b300c2d661d0d31c715043482ce6310320dc147405025e63d5210d954a511034c53d4941b398c304826e62942439ed81544425c63550209bd89544cacf625513097992538425e6394042d394c42903555354440b358840cc2f06050510cb550420425f6550530d314f52502cd6214443d3d0e52906d76150330b398a51d0e6f6550520d3d0d528434e53d0840d95445110b4f4354a309bd89540c65e6590b309d984548834e54d0c42b358e404826e62d50109798f540866e650c1209bd8953442ce6308720d354f421025e6314c20b399330c82e860505209bd8954cc26e
  | 4 => 0x314c425025d65d0c21d3d0f524c6d96010530d394b30082cc644c8329b99641c825e63947429b189540c2e96010d20b358e41c832c62950109758c52c42cd6010f20b658343102cc62547309b588548c25c6454c209b191528434e5310a419b58a509066e62d5131d314d32486e661d4f429b9885050ecc63487209b997424863f6550040b398e40483c842d4130d3d0d52042ce62103309718d52442ce63943429759443842e661101209b18954cc65d65085309b98b53842ea6014442d354c42882ce620c5309b19541c82ce644c3209798f52042d96014843b3193304826e6215010c7153404c3c9404c120b958753d0bcb50cc120b6d81524c2ce6314042cb950420cae761503209719542cc2cc63508429798e53486ce62901309718d54c82766115020d354f428431c5410d10b6d81414c2cf6355320b3d8d414826e62d5130d6d4f50506d461549309b98853c426d6215210d35485210ed56114843d315330482cd6314520b358c21c834e5310810d310e520c25e6394242b398e4210a5e65d0d309bd9742842ce62d5330d314c52d025e63d52209e594400425f6510c21b3583424c2d76155130cb950420430c5410d20d354c32482e66114342d3953424c27b65440109b594428c276611501097d8153042cd6010930dad4b505065e65d0d319bd8953d02cd6290d30d394b300425c655013097597438425f6550730d910951102cf6355120d354d528426d62d5030b3189404c32e64950429b992520826d6054810b358e5010a6e6294341ce181540433554d04109b99643c83696214141d3149324c7665294440b358e4210a6e6494a309758f544431d54cc010d354c420823c6454910b398a424c25c63551209b58a50d074e53d0a10b3583434834e5354a109798f54c874c53d0941c7152424c34d53480209b19542482776155110979944350b4f53d4940d314f4250b2e54d0a209bd97420c2cd6394342da14850506eb605512097d8d548874f43948309bd8954042cd631404297d8d52442cc6250730b3d89434c2d96010d2097596530865d6094c21d354852cc26e6214d10b318d5110b575194743b658351cc25d6394742d394f42882cf63485209b98a50d0f4c43548319bd9541c834c43d4940d5145314c25c65d0d21cbd89540426d6094a439798c52442d46150330bc185401025f63551219718d51d03b341d00109e98354cc66e6215230b55845010f4e53d0820b6583214c26e65101209b594320874c4354a3097990534866f6510820cb151404825c6355010c718d540434e5354810b3189310c66d62d51319b58b54cc71c63950109798f54c43ca6010930b3189514c29c6454930b558450d0e5c6550930cb55120042e96014f20cd551100425d6315210d310d52906d561d53309b195324825f63552209d597410425d63d5
  | 5 => 0x528436752d4540b3d8941cc25d6594c20ba580428426d659052097d8d5110b4d53c8421da949200826e62d5330b358a414c26e62d4c10b6580424c25e65cc931b318d21087ca404c1209e98354c863f6550c4397582544c34d5310810f24c120c436b52141419b597428c34c4354342c7953300434f4354a43b3588404c26c654c7209758c524425e6394021d9d0b51502cd638c8329b58a5010f4f431494097994534865f65d0e20dc181511025e63d50309bd95200427661d5320b558752d0f8e6410930b558440cc25f654c431d3950434825f6510e10ba58342d025e6590d309798c548825c6548730b318d424836b42141419b98b54c42d860505309758e51d02ce6390520b358e204826d62141419e596100434e5310840bc18141c42cc614c832d354f42903ca6010d209b98854083674294440d34c9510ca5d63d5320b998453c834f5394f42b3189314c25e65d0d219b99431482d66110130cbd50424c26e6214810d354b308c36552544409bd95210865e63d51219758e544863d6595010d354c42103cb604c120d394f420c31e5410f3097191530434d5354a4097996414c2e56114c42d395130c82cd6010f42b598450d0f4d52cc210b35885010f4d53d0a41cb150424434d5394a41b3d8951cc25d63943429758e5090b596095130d3d0d50d0b2d54948109b988540c2cd6314720d310e528432e5448010c795043ccace62907309b59442086cd62903309d584540831c549053097d9743042766115032abd91534827960d53219798e509072e5410b21b5d85404c25f65d0c209b58a500c66d6215010d310f524c6e561101209b58a508c72c5490d20d3953434834e53480109ed81544867a60150329d58754cc2cd6394742b358e40c823d64d4e21b3588430cb4c5310941c7150414c34d53d0821dad0b50506ce6290f30d314f424866e6214c10b3d8d4210acd63909208f990530434e53108219d594410426f6254c41d310d520438c4310a4097580535065d658c8319798c50486cd638c120d314e32486766114f20d3548524c2ce62940439758e501065f6510e20ec50740c426c65109319b988538431e5410f31b398e42482da6014843cd185540426d650c52097583535066f65d08109b98b530826d62943319b993524c678605512197194434865d6315021cd54540102e960153209b582520c6cd62947439718d52d025c6454e109bd89548c34d53548109bd94420c7575314540d3549300c31e54d0e32b9185544834c53149409bd95434834c544c320c79925410f5a631414197d95300434f4394a109b988540c75b5314141d3d0e521033551d0040b598452cc2cd620c5309dd95100434c54d09309e58354cc6e66110320b6582514c2cc6250f30b358a50d0eda6010530ba18141c82d960153309758253906e96014c42d
  | 6 => 0xe0020120740209f0320040880900001002039000030010671e60080081402e00c16854000000008050420000200e0020000501c0120380104e02a0600d1160420251b80306000400801006028030bf0ea150bb802000018008000061943c82f06c0e4120000248e00000b008000440050a40f40285a20a0c4000010904b80004904417c1180b00202402a42004004088a400c004028270880000003202c000170170000040494757400c0080005403802051000a700800d0169b8030000621dc0302d0161a8000040040200706e05004cf98b200e0000380101c00c108000000000125f038024948370020116c00504400800001004020000eb00402809018012ac8008000da2340500002c0702700501a01c00000036030012840dc0404b8000001087200700000c0400f00400c9597b000018320000200a4330d204203c2200b5d819c7d8870ae078018160020a4028010020100f81905025c0001c00a18c020030145f84f8000680503180112e9680719500000085821048000010002220186b050002040098100040001380900008c1b0000000180006f144258150030140040180a0000d00081800a58805000014004071860020303881e00600005820000000000090002bc118000560000400600e44c0000b0040080980502c03000068002058b20000000a0178a700000805804008028009030062780501506e22c0085f0121600100001e0141d0003c602c2b82200c19c3082106e0ac080040005401f82301c0781511a00c0009100301a0040080d08a0a80283403819c0101b0003580000005e0182100100004c02804032010028100048f40100400a03c330150020001987f0441080288e0e602c078160b83c27c00003c6400000b05018c6e00700a09c0980b48e058730050060026f6548020ba580424c26f605481097992530871c54d0d319758c54042ce6394042d514f515026d62d503197d8d540825c63552219b99642482e76154d20ba58042d025e63d50209798c52042ce6410c42cb153424866d65108329758c520434f5314941cb553200426c62547309b588540c74e5310a20b3d95320ca5d65d0c10b358f54c826c625523197d954310ece63903209758e52d071c54d0d3097d8d544825c6354442d610f505065c6354720d358853486e96094d20ba9805310a5e6394740b3d894310f4f4394a409b1895110e3e64d48109b992544835b43d4141b918540c825d63d5310cb95340c825f63548419798c
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x212000c5880000300000429a240838074021000004000000060110880030400080021c0000020512000808400041097a2400300000060618016120402d0a58183000800018002800000300c10a8b008690645635445110b44322809824191589510c730e0886212a22050e74d4c32887062a4c720a41325c26290530b80e2a0260906884358042103142a2c021261c21526010930c18c821aa50860e6410f524c6163a2ca18a41921516010930a8ce5a8ca3a1e4a5458043482863a2a621421a21516010930c18c82a6609050c7454c42882a338ea729e85a2d516010d20c8ac6a88a3904c970988514c2923a2a228a41321d9404c120c92a4b00a421f08431085050722b12a228887c85512044010d20863028220d517010d51102c4b808621081985456014442a8ae22a264194c97098e4148298bae83a0021861516010d20e10a8a026090651515805110f84aa26090021821516010930838e8b2842985497010d52842a238aa429261319c6644c832a8ae229a65905447154c3248322a92c229087585c04254440c18c821aa5185457110d520c722310a298a6183192544c832c48a830a80904c97098b544c2a4b80a89906552dc13254032a8ce3a18a498d0e74d4c424870c2a2c021261a81086050441a88e4a88a29850e7495043483062a0c4a02619154d6114f20c8ac6a88439061454185404c3062a2c021a41511c55314d20a88e6a88a2904c97098f5448324a9ac021081915895114730c18a931482986445398742486a4b8086a90819118c5148520a92e029a6590e45535845310aa339ea328e85c45513044010e10a8b00849854671d4a52d0e263b2a690843325c26314520c8aa4b08a59850c74548524c234b80ca212639154d6110821a92e021aa02170854580434828a3a2a228a61929516010930c90a8b008690548755013048324a9ac021421a2d516010930d10a8b008690628545804348324a9ac029885831516010930a18e8a98649060c5418d4048306320a898241439d25410930c18c82a2619050c7454c53483842a4c021a41165c06510d21
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x60220000b018010c4254440c08545c26390520c08545c26290530c80641c5404c120a088454d6010a10c0875191404c120c0876151404c120c08645c04354a10d00541c5404c120d00435c04254440
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/37+packedAt s5K6 (768+(h % 37)*6) 6) % 48)
  | 5 => 2*((h/367+packedAt s5K5 (27459+(h % 367)*10) 10) % 1017)
  | 4 => 2*((h/476+packedAt s5K4 (51110+(h % 476)*11) 11) % 1345)
  | 3 => 2*((h/86+packedAt s5K3 (5488+(h % 86)*7) 7) % 112)
  | 2 => 2*((h/10+packedAt s5K2 (600+(h % 10)*4) 4) % 10)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffe0ffffffffff03e0f0ff0ffffffffd031fff
  | 1 => 0x7ff03f87ffffffc00ff0ff0e07ffffe1ce4ff
  | 2 => 0x7fffc00781f83ffff000fff007c1f03e0f8cc
  | 3 => 0xf80000007fe003fffffff000007fe003ff00f0
  | 4 => 0xffffffff800003ffffffffffff800003ffff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x11221054084111006410510523152929010955
  | 1 => 0xa24448a0928a222c08650650442a52d20c64aa
  | 2 => 0x538a293521d43755ad044b66094f1c1b60b8cc
  | 3 => 0x631cb2c645073b9aceb6604412739863b700f0
  | 4 => 0x8410c300061840e310c88c889c000080dad600
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeea8888feea8888feea8888feea8888feea8888feea8888feea8888feea8888feea8888feea8888feea8888feea8888feea8888feea8888feea8888feea8888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_39085
namespace PEqualNP.Outside.L_meta_39085
open PEqualNP.Outside.L_meta_39085.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x60005801f00800800890430830030713c2042147007f84001fd20027f54c077f54027fd4003fe4200ff8c807ff41017fcc407fc4001ff90003ff20027fd4809fd52017f0c4077d54007f88403fc42007f48405fe43027f54005ff3000ff0c805fc4301ffd0c01fd3201ff55007fd4101ffd0801fd3101ffd5005fc30007fc4007ff40017fcc807fd4201ff95009fd5101ff50c01fd3001ff90407fc4100ff14801fe30027fd4409fc5100ff94809fe5001ff15001fc10017f94c03ff21027f94407fd40027fd4c01fd10027f14003fc21017f14c01fe31007f88003fc20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x8a4006f758c10137f8871081aff630400bff32e2030ff94132037f8ca0801ffe420400b7f308202fffd9132037fec710007fe524840b7fb2c4223ff14d21047fca608086fd648c00dfea002003bf191210f7fa809801bfc400400dff8842002bf18d21157fc8098817ff2104061fe32a6406ff14120037fc608806ffd4388045ff28c6022ff54a3002dfec98800afe630405dfe2846202ffd0d31157fec89881bfe658c00d7e3202006ff10110035f8cb0800bfc328c055fe2a26206fd8411017dfec8990a7fc204c40dfe32c2005ff90621005fec49880bfe324c4097e32a6405ff0c6310d7fca710077fe524c01bfea1a202aff5093115ffea298807fe4288003ff90c4000bfd8121037f860980bffc644c803f790a6406ff9421013ffaa91081bfe650402ffe21a400bff90910007fa431801bfc6588017ff3122006ff1923013ffc811080bfc534c04fffa1c420cff94d10017f8609880bdf304c843fea0c6006ff9923002ffc63108abfe544c42ffe18a4005bf18e2101df8c899017ec214840bffb1e200bffc851000ffc4290037fd4044055ffa0a6216ff54310007fa6408003fe604c431fe3224024ff50d21005fac5180a7ff214c40b7e3262004bf9952111ffca69089ffc54884097f32c6005ff10531005fac710003ff6344057ffa826200bfd853000ffc651081bfe304c031ff20a402bff545310affea988017ff5188403fea144202ff14e30037fea10801afe608403fff32a6030ffd9532107fca5180bf7d544c80dff0802001ff909210c7faa890053fe43c4005ff1946202ff50d30127f8809081bbe6404049fea024205ff9931000ffe4290817fe63c4055fe2026205ff1471013ffca91081bfe638800d7e3024206ff0c23009ffe418801bfd6204003fe9944005bf1922102ffaa310802fd6388431fe2a2402affd0931137fca710803fe314800bfea0c4202ffd0e31007fac4980477d548405b7eb246200f74c93102ffecb880ab7f544c43bff2126002bf18d100c7fe869001bfc6304005ff29a6001ffd0a2102ff8831081aff6248003fe1926406ff10130007fa648800efe648840dff1042005fec421000ffc64900b7fd428c401feb1a2030ff9453200ffaa499002fd628c403fea124019ffd45200effe42980b7fe408c40bee18a6206ff9012002ffcc110836fd618400d7fb2c402cff08231037faa00807bff644c00dfe1024019ff19520017f060980027d6504033ff32a4018ff9512009ff8a58801bfe618804bfe32a4206ff8411016ffca91885bff52c400bff98e2012ff54a1002ffcc588002ed62040577fb2a6205ff9461000ffa6490862ff644800bfe10e2027dfd5221025fcca8800bfd438c00dffb146005ff10631037fa8118073fc518800def3182005bf197100cffaa2900637f544800d7e324600fff0ca10
  | 1 => 0x7fe548400dfeb142000bf58a1017ff88299007ff208841dffa822001ffc812002ff842988bbfd508c40bfa18c6211ffd0a10037dac408002fd630400dfe8802003bf991300e5facb10007fc528840dbeb28202affd0131017be629806f7d548800bfe10c6202ffcca3009ffca58801bff65880017eb16200dbf59110007fec290017fb104400dfe1862012ff5461002ff883080b7ff548c40dff2826003bf1911002ff8cb1881aff658c05fbfaa2640dfd5051002ffa420803afd6544003ffa126407ff0c8100a7f8a78800bf4314c405ff21c6217ff90d2006efaa888097ff5048401fe30a4018fb50920037fc4088007ee32480037f3146202ffcc131067f8c688067fc514800dfe30c6001ffd4a2102ff8a3188a7fc424c40bfeb24422cffc823115ffcca988477f5484005fea9a6202ffd4d320bff8c690073fe5188003fea94402effd4a3102ffec518817ff518c401fe3024206ff8c3100bffe629001bec2048003fe1044206fdc4210167f8a51881bfd3004003f61926402bf98d21005fac7080937d544840dfeb246001ff48620007fec298007ef204844dff984421fffd413002ffa8208003ed324840dffb202006bfd922000ff88510817fe514400dfeb1c200eff5491005ff86488017fc658840d7f3044227ffd022100ffea490057fd43c401dff32a2002bf98e1017ffe829901bfe508c0097f32c4201ff1492005ff8c48800efe644840fff2902013ff90b10037fcc808017fd64c400d7fb242019bfd9520037f8600801bfe6384003773102005ffcc631007fa42880b7ff408c429ff29e2001ff085200f6faa89800afd638c00dffb242028ff54e2102ffca290817fe418c40bfe3044203bf9913100ffaa49081bfd308800bfe3162008ff14c1008ffe8308096fd654840dfe2062015ff5031002ffe4388012fc654c457fe2826212ffd4e1001dfcc90800bfe534c431ffa024001ff0c92102ffca298817fe414c401ee98a601bff50620037fc6008092ff6448453ff3126206ff58a3002ff22008007fe528800dffa846000bfd8131037be611800bfc434c40d7e32c601fff5493000ffe6499017fc314c40bffb1c4205ffd8221007fa608801bef208800bfe18c4223ff0c121037f8611007ffe514c03ffe32a6017ffcc12002ffc6298837fd4144005ff984622cff10a31037fa8110017fd3188401fe9962001ff10920087fe650806bfc5388033fea9a4006ff59010037f8608802ffe52440037fb126402ff54e31007fa42980a3fc5088405fe1926021df5523004ffa8608016fc628c40bffb2c6216bf59710017be629901bfe6484033feb2a4024bf59121035feca08002fd624400dff1844024ff5052102ffacb18807fb2048019fe29a2002ff10e3100fee429087bfd414c055feaa26224ff19121037f88110003fe6148001fe9
  | 2 => 0x21004feca99016fc614c861feb2a6406ff9431000fd8a490012fe6584037ffa0c4006ff99610017fe8718087fc548c00bff31c4224dfd512116ff88118812fe658803dfe20a6019fbd4920006feca99003fd604c443fea146008ffcc8100cffaa09000bfd438c401fe3026205ff193100c7fa869008bff518c00b7fb162001ff9092002ffec910816ff658c40bffb262006ff90230037feca0800afd638c443ff2a4600effd4d10187f8a099003dd324c045fea8c6006ff0823006ffe828800bef324c805fe21a6406ffd8c100f7fe849801bff10040017fb122000ff4c6100f6fea89808ffe6348461fea8a642cff90a31007fac299093fe644840dfe2024016ffd431002ffe4318803fd634800bfe324422fff991320bffca69001bff618c001ffb0a642dff50231037f8a1080a7fc624c431fea024001ffcca20017f86299006fe624c403ff90a4001ff4ca21005fec690803fc604c8017eb1a4200ffd8d20127fe829081bfe6304005ef9926206bf188100afea8388017fd608c44bffa9a4225ff59521007fcc299002ff614c821fe21c2002fdcc531067fe64880bffe414c80d7fb2c2006ffd961002df8cb10887fc418c00b7fb124206fd4401015ffaa0988577d54c40077e3224006ff94010187fea099016ff648c40b7f30c6205bf1923102ffc43080b7fd548c40b7e31e2001ffcc92102ff86308003fd624405bfe2a4622fff55132037fc4188007fd424c805fe29c6205ffcc6210f7fe8298063fd644800bfe10c4224ffd912112dfeca90817fe648c40dfe3202021ffd0a3010efea91800bff534c00bff8822005ff90610017fc8698816fc614c0093f3282022bf59630155fec89881afe6088005fe994622fff1513208ffaa9080abff544c4097e32a4001ff4c920017fe6498017f4218840bffb246205bfd8e2102ffca38805bfd52c4005ffa1a6406ff94220007fac090802fd63c400dffb2c6005ff8c610037fa4108017fc514c40bfea0e2002f790d30037fea008003fd624c40b7fb1a6201ff8c932127fac8908abfc644c4037eb144029ffc8131185faca990c3ff514c8077f3224028ff5422109ff8658801bfd638804bff32a422fff9013201dfcc910006ff634c81fff1942006ff94110055faca08047fc5484023ffa1c2001ff0813202ffa438802bfd5204003fe1944002ffd4e3008ffa85080bffe544c80dffb1c2006bf1813202ff8a31081bfc208400bfeb2c4206ff9881004efaa808017ff608c443ffa0c6012ffd461011ff8c690817fe658c431ffaa24026ff90e2113ffea91081bfe408400dffa844030ff99532025fcca9000bf7318c4057f31a2005ff1971012ffaa0908afff524c40dff1002002ffcc53101dfcc888097fe5048453fe2926200ff4c310037f8cb18003ff604840d7fb1c2005ff94410025fcca9904
  | 3 => 0xf10a2007ff8c810025fccb88027fd420402bbfaa62001ff54a21017fc869901afc6304059ff2946205ff94621037faca08017fc518402bffa162000ff58d21007fec6908b77d548c40bffa882006ffcc23006ffe868802ffe3244037fe2a44005ff9051002ffe8388017fd648c45fffaa26406ff1413000ff8651081afc648800dfe1002001ffd0a2002dfcc318017fc410400dfea842000ff8c62002ffac51880bfc328c40dff102401bffd0e20087fc8708017fe2148413ff2a0201fbfd953006ffaa8880a7fe524c40bff20a4205f78c531017faa718017fd510400b7e32c6202b798c10005fac310003fe218c019ff31a2005ff8c51000ffe4099003fd2044003ff1944006f70c130177faa518802ff614804bffb2a4202ff10d3000ffa8510017fe518c4015eb202024ff5512102dfcc310007f721884057f31e2006ff9022000ffaa490003fe214c023ffaa4200dff509100cffca29000bdc534c01bfe2a22006ff0822002df8c29001bfe4044005fd9826001bfd8120037fcc91001bfd630400b7fb2e2006ffc8210077fea28800bfd318c0037f314601bff9522000ff8649009bfc538840bfeb044216ffd4f10015f8c690017fe3148457feb2a6206ff5962004ffe840801afc6484003ff2944202ff50d31037f84088007fd2148039fea8c4001ff1493202ffcc118837fe6444003ffa926406ff19210037f8a11809bfc3088449ffa1a4224ff1512102ff84308007fc214c81bff2a22000bf586300dff883100277f5404003ff1924202ffcc5320f7faa898093fe404840bfeb2e2027bf5922100ffa849083bfd654400def1826002ff94e3112ffea290817fd418c405fe21c6006ffcc210077faa28801bf7100401ffe2942002ff8c53000dfcc58806f7f5488021ff98c2002fecc230017fe8698007fc2048401fe9824017ff98d200f7f8a898093fe5448425ffa942003bf191310f7ba869801afc638801bfe3222029ff909310c7fa8290037fd6444031ffb224005ff1051017ffe809900bfc318c005fe1846200ff1853000ffca4900abfd404c4037e312601eff509300fffea298002ff624c04bfea8a4206fb988100fffaa29804afd658400d7fb142006ff90130037f8609001bfc204c00dffb142001ff1093202ffac7108a2fd65884377eb244006ff5961010ffc831807afd644c00dffa042017ff14d2006ffe8488017ff4104005fea9a6406ffd9220057fea608012fc654401b7fb22201eff9513006efea8880affc654c401fe30a6402bfd8130037facb18012fe654c41ffe2142012ff54e10175facb18807fe4288405fe9926205ffc862108dfac908073ff538804ffea044202ff8c630035fec40807bfe644c00dfeb242027ff1022100fb8649903aff654400dff1824002ff8ca300cdfaca9007efd654c00dfc1044001ffd09
  | 4 => 0x63ff4148057ff2826206ffcc22000ff8a510007ff528803ffea82602bbf59531037fe800801bfc6384003f71924206ff14310007fcc09906bff3188001f69924000bfd8d2002ff8a29080bfd434c833ffa9a4005ff18f10037fc610801bff3004003fe2144004bf99530037f8c71001ffc4204021ff29c2011ff50e1005ff8a488033ff314401bffa022006ffd88100a7f88788007fe424c83bfe2926030bfd9532057faa60803bff524400d7e3282006bfd8e200f7fea898017fe21c4005ff21a6002ff94d32156faa898817fc214400dffa044006ffd8620007fac099026fd640403d7fb226002f7cc131155fac898877ff204c00bffb2c421fff1453000dfcc488002ff634405ffea02642fff10132127fe8090817ef2188403fe2924201ffc8532017fe651881bfd6488051ff2844200b758c1000ffe649003ffe42840017eb1a4000ff981210affaa988016fc62c401fff90c201cff54e20007fac290017fe41c4003ffa924206ff5021002ff8429083bfc6544047ff98a4206ff54230037fcc31801bfc618800d7fb246001bfd852102ffa620801afc628c00dfe204200bff1091006ffec888003ff604c80b7fb1e2005f7cc631067fe608800bff304c80dfeb0c4001fec8220005fac11880afe638840dfe3102001f30c93215ffeca9881afc658801bfb20a2005bfd9221037f8a008017fe31c405dff2846218bf5912002ffac78803bfd53440077f3246200ff4831010ffea91808bfc518c01dffb2a2004bf99410017fc8718057fd42c402bffa1e2002ffcc5300fffea498077fc214c011fe2182015ff1531009ffc6588017fc628c451ffa844202ff14d31037fca0900bffd644c8017fb026406ffc823013ffa8710817fd51c4047ff9824230df1953200ff88490817fe210400bffa8e2002bf98e20005fac408017fc638840bff1882006ff90310037fcc51806bfc318800bfe1882025ff54d21025f8ca90803fd328400dfe2844006ff0831017dfac899003fd314400dbf3282000bf58d10157fac898853ff32c400d7f300201effd0130035f8c09880bfd314c00dfeb0c6000ffd89300affca9880affd524c44fbeaa44202ff0c93102ffc820806bfc4388055fea0a6200ffd8910107f8851800bff304c03dfeb226001fbc852000dfcc498077fc424c00bfe20e2006ff1411001d7cc808027fd5404041fe10c6022ffd4a300fffaca9800bfd534c03bfe3126003bf99310037fc800801bfe6588003ff10c4019ffd412002dfcc310833fc43440037e3126205ff58b10177fea118803fd3148405ff98c6006ff4801002ff8629081bff408c00bfe20a4204bf9963111ff88690897fc5048431beaa24002ff8c9300e7fea310027ff43040057fb0a6221ff5523002ff8628806ffd5488061fea82641bff9062001df8c898027fc540400bf
  | 5 => 0x1204c004008080840d40704100000405803012015208020780000d01008c008090110144cc008130683381a80f0720001481702604c058010984380100f0000300000f00000401017070008010150000000385309a0002380401000012000004060001eb04e9d4030010060181b803000068200060220000f04f0060140096f086084060ab00a0000000e020c54008c80140a800823028008090070180108a80515401c0004900427001006016020041f20045b0000120021281a00002a008000000700200080100200004813008000048ef0380000084f00c114348840060d40080d000000008720000c40200702a00c0180f00c0002700b008034008250000700000100002c7980800e0181c8000140144b0060120000280600800c230010000280101104a0000689408e0061600702400005a1600a2503200f000000018000040047600200601c010050021a872800048028061cd05c0001f88a02600001345000010038010120000106900004c0700a00202c0100300006800003002004008ae00400c0e8010100100280f0000f8000040000040780700a4e0010230022280283a03e040188050000d807000000014108170000dc01800016004028000660180105407a0004d80300e008030470040000d83a01001c022ae040204d60010000200500201803807059008004000000040000000d047fc860801bfd508800ddeb202018ff1052004ffea808017fd518c4037eb144202ffd4d3108ffa8308006fe6204005fe9926005ff14410007fa430801bfc648800dff9002020ff90a30037f8c518012fc654c02bffa062001ff9493200df8c4880abfe644c4077f3246005ff99621017fca71803bfd5044001feb0a6006fb881200ffbea69801bfc408c001ffb02622fff5053202fec8388053ff30c4041ff90c6005ff18231037fec918017ff418840d7fb202005fb8852100fde4099007f4214840dfd0802013ff10b1000ffe849006fff5488005ff9926205ff192310d7fc87100b7ff428c40d7e314201dff989300b7faa788017fe628c40dfe984202ddfd5231017f86099002fd608840dfc1846002bf98d20127fea890883fc528c001ffb126223ff90d2103ff8a40800bfc534c851ffa9c4206bf98231037fe4110017fe64884077f320201fffd953000fbc649907bfe414c005fe18a60049f19532067fc868801afe608c01fff294200dffd51100c7fcc89002bff520400bff9882005ff08410037f86108006fe628400bfe28a2030ff14532017be6498017ff62c403dfe3226006ff18a1000ffe409082fff204400dff3142003bf99132087f8a708017fd31c400d7e31c2002ff4ca30007fa6310067ff6548001f690a4000ff9853000fdc849000bff538c403fe10c4005ffd0631035fec698056fd64c400bfe18e2001ffcca2100ff04090
  | 6 => 0x80b809002000110180900241f81502a0240000006a05c96000004088038010120040383c4a000c0080204401c0401101e3180100700e528a18001ac0ac060ae00a0441f0040020140095706c070000b71280500002d000004000000000004c83c006000018020460040000a03803c0100000e000018000020640f0ad0620040001400a0bc008000008fc020250040000080e0001dc0a00411c0680000801e9e0088
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe624c930005fb704c610006ed7558810006f96018121035ec7048520004ff7058a3102ebd5159010004fd764c91000eef6048520005ed7218530106ec5258a30006ec7458810024fc7558e20004ff7458620005bf7458d20024fc7558e210067f74d9532007d8704c530036fa60181211857e7598532004fd7558e2102ede4158c1001cfe7458d200067d74d9532006de32d8d1002cfc71588100c5bc7458520034fc7058e20036dc1058c10036be20590102367f43d9532035ec764c920036dd1058c1003eee425881002ebd3159010007d4614c530006ed32d812102cfd70d8910004ff75d8d2100fcf734c920036f77158620006ec7558810036ef7058810036ed505881009fcc324cb101a5ef744c920006ef5258a100067e3259410034fd72d8d20007d4714c931006df7358d10007cd324c120017d7614c931036df5058c1002edc5158c10004fd75d853002ebf7159010034fd705881002edd3158a310067f545891002df4714c31002cfc715823102edc7158c10005bf7458132066f53158630006dd5458c10004ff7458231036ed2058620006be525901002eee61485200067d54d89301b5fb7058d2002eef31588100fd7c755853000cfc7258d1002cfc7648110036bf7059010004fd74582210067d54d891002dec714c92114cff7258d21004ff7358b100067f745941002e7d215941002eef51588100067f65d8132006dd634cb100057d74d9532015df724c9311b7cc32d81320067f5458d211bf5d544c5302367c31d9532004fd74d8d10004fe768c520016dc638c520014fe7358910006ef425881023d7e76d9532005bf7458530034ec76485200067c70d95320067d5458e2005eec625891000eee624c9100eeec21d893002cfc715822100dec724c120034fc7058c1002edd3158231024fc75d8132006dc5258c1011eed3258a31195ed7448520007d8704c9300067f5458f1006dbc7458d100bede63d8d200367e705941009dfb70585200067d5458e10036df1058c100edec725853002eee71588101d5dd744c930005ed728c52001cfc745823101cfc74d8d20024fc75d853202ede3158f1002cfe71d8d1002eee21588100067f7558d20006fb7058d10024fe75d853002cfe764cb10006de5458c1001cfc7458e1014eef2058d21004ff75d85300067d5458c10004ff7458630104ff7358d2014edd3258e2100cfc7258f1002eef215822100feb604c9200757c754c910006df634c52100cfc764c1200067c41d95321e6fa30d813211ddc7358121005f7714c11011fcc634c9210557c754c810024fc75d852000eee62486100bfcf314c920006bd755901006dbc7458910004ff74d8132006df7358d21006de7558c10004ff7458d20015dc734863002ee4614852001cfc7458d1000def71485200067f5458221006df4358c10
  | 1 => 0x8d2109eef2058b10036f61058630004fd74d8930006bc7359010006ee735881014eec52d89310d6ed32d8930046de4358c1022e7c73d9532005f47158d20006ef3258810004fd7558c10006bc5359010024fc75d8530004fd75d85200047d74d953202eef7158810024fe7558a3102df4714831002ebd21590100cdec754c9200067d435941022e7d32d9532004fd74d8d20024fe75d81310067d5458d21034fd72d85200067f54588100067d54d853202efb105822101cfe74d8d20004ff74d8d20004bf7458d200367c40594100367e4059410004fd7458a31014fe76d8d21014fe76d8d10066df30d8d10024fc75d89100067c65d853201cbc7458d10036df3058630004ff764853022f6f21d953202ef8105822101cfe7458a31035de704c5300057f74d9532006bc7458910004fd72d81310efcc624c9300fd7c7558930066df3258d10004ff75d81212376f32d953200cfe76d893002cfd7158c101b6fa20d81320067d425941000eee624863001cfc74d8532004fd75d8131036b710590102367e31d953207eee32d8520036ee30588100367e1059410004ff7458e2122f6c32d953209efa20d81210bfcc634c920034fe7058810014fe7358a1000eee624c810004fc76485300065f5458c100057f754c910034fc705862000cfc72d81310067c64d953201cfe7458231006ef5258810014fe73582210067f7359410036dd2058c10005f4715813201cbc7458910024fc75586300057f75589300067c655853200eec62485100057f754c81001cfc74d8520016ec764c92122e7f72d9532024fe75d8d2014fcf204c93100eec628853005cfd76481100067d54582211867e76d9532004fd768c5200367f305941002e7d4159410035f8704c51014cfd764c521004fd7558a30034fe76d8132014ff764c12000fcf734c92102eef7258b10004fd74d8d211fcff7158d21004fd7458b1000cfe72d853005fcc324c910004fd768853002eee2158b1000cfe76d89310beed3258a30006ef7258d10016ec634c921006bf725901022f5c32d9532006dd634ca1001cfc74d8930016de634c810004fd7558910024fe75d89310057f7558d1011edc53d8d21004ff75d8931004ff7558d10014fc73d81210367c2059410004ff75d813200cfc7258630004ff7558f10004ff7458a300eedd3258e20006fb60981210067d54d8931036dc7058c1001cfe7458a3003fcc324c810046de5358c100057f754cb1002df4714ca1007eef2158a100eeee62d893002df4714c11011fcf304c921004ff7158d20004fd7558630006fb609813102cfe71d89300bedf3158d2022e7d73d9532006fb705891000edc764c930004ff7258e1007ef521d8520036ed30588100067f5458a10006dd634c810004ff755862002ede3158c10016de634c310014fe73d812100ed
  | 2 => 0x2cfc7158e2002cfd7158810024fc7558d100057f755813101cfc7458d200067e74d95320067d7259410004fd7458231016cc634c9200067c7459410064fd764c1100067f5458b100fdde754c530006be73590100065d5458c1002cfc7158a300067e4259410006bd52590100067f6558532034fc764c810036ed2058e200bedf30d8d20014fc7358810006f77158d100047f7558d100367d7059410136ed32d893101cfc74d8931006f641d853202cec764c921036ee2058a30007cd324853000edc624c93102ebd7159010006dd634c620036be105901002edd5158c100067e7459410006ef5458810036ec70588100067e7259410216f631d8532036bf3059010017db604c93002cf47158d20006df624c5300067f651813201cfc7458a300367f2059410006dd43d8d2100cfc72d8d10004fd7458d21006dd7558c10006bd5359010034dc764c5300a5fb705853000feb604852014fcf214c9310067d5458a10036bc2059010006bf7359010006dc4258c1002edc614c530166ee3258a31005f7714c810004fd7688630024fc75d8d20006bd7259010006ef6248110014fd72d8132024fc7558d21015df714c530004fe7648530006ef6348520036de2058c10034fc7058630024fc75d8930066df31d8d1014fcc3258532004ff75d853205df97098520195ef7448520015de738853002e7e2159410006f731d852001cfe74d813202edd7158c1001cfc74d813102e7f7159410004ff7058d210067f54d85320067c65985321c5dd744c53001cfc74d853002e7f31594100067f651853202df47148110036ed4058810004fd7458f1021fcc321813200cfd73d813201cfe7458e200067c6518132036ec3058810036ee5058810034fe70d8d210067f425941022e7d20d953202edf4158c1002cff72d8d21005ef724c120004fc764c91005dec7258d10006de5258c1005ef521586200247e76d9532004fd764c810007e4714c921034fc764ca1022e7f73d953222e7e72d953217dbe7498532006f7619852003eec3258810004fd7558a10004ff7558a30036df4058c1014dee7218131024fc75d8131005df704c931004ff755891007ef621d852002edf7358e210067f5458d10036bc5059010024fe75589100d6de4358e2001cfe74d8d21036fa6018132004ff7358620024fc7558a31024fe7558f10004ff7458a1011fcf314c92114eee62d893102cfc7158a31006be3259010024fc75d8931046dc4358c100067f54d8131036f7715863019f6f544c920014fe73d8520024fe75d8520086de4358e10036b5105901002cfd73d8131005ef7258131004ff7558d2122f6f20d9532004fd7458e20014fc73586200067d5458910007cf634c920155bc7458131086f531d8530006f54158630004ff7358221004fd7648630034fc70d8910006f7715
  | 3 => 0xc52588100067c6558132004fd72d8d10004fd75d81210a6df32d8131004ff764cb1009eee32d8121024fc7558620036ef105881001cfe745891000cec7258d1005ef62158620046dc5358c100757c7558d10006f56118520006de3258c10006ef7258d2102eec2158b100067f3259410034fe768863001cfe7458f1001cfe74d852000fe7614c921005ed734852002e7f2159410034fc70d8520086dc5358e10005ef714c920004fd7558221034fe7058c10006bd7359010005bf7458d1011ede63d8d212075d544c9310057f75585200d6dc5358e2002edf3158a311857c7558532006ef435881002cff768c6200047f74d9532004ff7558d20005ef72585300a6df3058f10005ed7218131004ff7458c10004fd75d8532065f97098530034fe70d85322367c43d9532004ff7458d10006ee54588100067e41d953202edf3158231136df3058e21034ff7058c10006ed624c91002ebe21590100c5bc7458d2002cfd72d8121004fd74d89102367e43d953202efb7058231024fe7558a10004fd74d8532004ff75d8131024fc7558b10007eb704c920004fe764c910005ef704c9210bedc6358d20014fe73d891002edd2158c10016ee634c920024fc7558e10034fe70d8910004fd75d8910034fc7158b100063d755901001cfe74d8d10035de704c930167cc3298532034fc7058a300067f41d95320067d5458d1019f6d544c9200067d71d9532024fc7558231004fd75d8930015de73485302367d31d9532006ef5358810006f54158620004fd7458810034fc7648610006be725901022e7e20d9532036dd3058630004fd74d89310067c74d9532024fc7558d200047d745941020f5c754c931004ff73589100fdde754c930004ff7458b1000cfe7258e10005f77158132004fd755823122e7c42d9532014fc73d891001cfe745881000cfe764c52102eed2158e21024fc7558f10036ef725881002eec3158810004fd71d8132005fb7048610035f87048610006ef7258910007cf634c9210067f65d853200cfe764c120125bc7458121004ff764863002eec2158810006df634c110004fd7558d210067d545881001cfe74d812100edc624c93000cfe72d8d10066de63d8d10024fe75d853222e7c72d953217dbc74581320eeef2158d20024fe7558e10024fe7558a3007eec5258a100057f7558910006bc7458d10004fd74d852001cfc7458c100067d64d9532014ff764c61000cfc72d8d20036f61058620004ff745881011edf31d8d21037f01048110006df7358d20006ee75588100067f5458d20004fd7558d200067c72594100a6fa30d8131024fe7558e2001cfe7458630006dd7258c10007e761485200067f40d953202eec4158810004ff7558b100067f71d9532004ff7158a3002eee5158810006dd634c6101af6c754c9200367d3059410
  | 4 => 0x82210247c7558d210cd7c7558d2000cfe7258c1011edc30d8d2101cfc74d8d21005df7358910007e8704c920007eb704852000dec724c620006dd4358c1001cfc74d8121006dc7258c10034ff7358c1000ede624c931004ff75d89101e6df31d81320057f755813200cfe7258d10005f77158d20006df7558c100075f754c9312075f544c931036de4058c1001cfe7458a10005df73486300067c6518532036dc4058c100067e64d9532016dc634c521034fc764c610036df7358e10004fd745862002cfe76d8532016de634cb1022e7d72d95321d5df744c93002e7c215941002cff7158c100067e70d95320067f5458630004fd70d893100edc764c931006dd4258c100067c7558d2102eee3158810014fc73589100eeee32d893002edd4158c10007e87048520006ee5358810006ed624c81001cfc7458e21036ec2058a302367e73d953201cfe74d8910166df32d8d21004fd7458c1022e7e32d9532005bf7458910024fe75d8121006df7458c10004fd73d812102cfe71588100047f7558910006df634c120006dd5258c10034fc7058d21036de7058c10036ef2058620006ef624851018f6f54485200067f54d8d1001cfc7458630106ee3258a300067f755891011edc6358d21006dc5458c1002cfc71d891002eee4158810024fe7558d2102cfe7158e21036df7058c10006fb7058d2001cfc7458a31036de1058c100067e735941001cbc7458d200067d5458d20024fe7558e2114eec6258931004ff75d8d10066dc32d8d100076f754c920215f7715893102ebf3159010036bd3059010036ed1058810036ef5058810014fd71d893122f4c32d9532034fc764c51022e7d21d9532006dd5358c10006f960181310067f65985320957c754ca10036dc2058c10015df724c9300cd6c754c9201857e75981321ef6f544c92100fe77148520004ff74d852002eec5158810014fd72d8532004fd71d8930036ec1058810034fc7058a31004ff7458910035ec704c9200367d40594100367e3059410004ff7558630036bf2059010004ff7558221005ef724c620036dc5058c1001cfe7458c10006ef75588100067d5458b100367c3059410004ff7558e21036bd5059010017db604c53000cfe72d81310067f7558d10006ed5458810016dc634c120035ee7048520036df3058a300067f54d852000cfc7258c10004fd74d8121005dd731852002eee2158a311a5ed744c92014dec7258131066fa305823102ff0104c510004fc764c520006ed62486300367c7059410004fd74d8530004ff764c910004ff7558c100ecfd764c120024fc755822102ebf5159010016de634c52002ebc7159010166ef20d8d21004ff75d8d20017cf724c931006dc7458c10006ed624ca10004fd73d8910006bf7458d2002dec764c921006ef7358810004ff7558a1003ee
  | 5 => 0x2ebe7159010004ff7458f1003eee525881000dee724c5200367f1059410034fe7058a300fddc754c930005f77148310004ff7558e100057f754ca100d6df31d89300067c6598132036ef40588100cdee7548520036ee2058a10034ff72d8d20034fe7058e20004fd7458e100067f54d8d20016ec764c920006dd634c9100067d54d8d100057f7558121036df7358c1002eec71588100247c7558d20086df3158e10006df53d8d21004fd7558620034fc70d8d10024fe75d8132036dd3058a30006ec4358810036be5059010024fc7558a10036bc30590102367d43d95320247c7558d10036dd5058c1000def734c920006ed624cb10036bd7059010024fe75d8d21024fe7558d20004fd7558b10006be7559010016de634ca1002ed4614c530007cf624c9310067f54d8d210067d54d8131006bc325901017ebe644c8100d6df3158e200067e40d95320067f5458a31034fd71d8d100757c75589100f5bc7458530007db704c5300067c40d953202edf5158c1015d7c75581310067f4359410005bf7458930006df4258c1005efa20582210067f5458620006ee435881001cfe7458e1007fcc324ca10024fc75d8121024fe755823122e7d42d9532005bf745813102cfc764cb1002edf7158c1014eee32d89310fddc754c53002eec6148520004fd7558810136df30d89310067d54d8520024fc75589100057f7558d20006dd7458c10006dd4358e2002eed2158221004ff7258d1000cfe7258630006ef7258d20004ff7258231006f431d8520004ff7458e10006dd634c310004bf7458d100067f65581322367f30d95320edee72185300067c3259410004ff75d8520014ff764c521004f77158d200067d41d953202e7c3159410005df73585200067f5458231006bf325901002ede2158c1002cfc7648310004ff764c620064ff7358d1002dde714c931014ff764c110004ff74d8931034fd7058c10004fd75d8d21005ef724c52102ebf21590100067c71d95320047f7459410005dd7388530005bf7458520016df604c93001cfe7458e2102edf7358f1001cfe74d81310066f5458810036ef7258a10036fa6018131004fd72d8530005dd731812102cfc764c11022e7c20d9532004ff75d8930006fb6098132006dd4358e10024fe7558630035f8704c61015d7c7558931166ef2058a31006de7458c10004fd7558e1002cfe7158c10036ed70588100067f7259410004ff7258630034ff70588100a4ff7058d1002ff01048510024fe7558b10006f761985300efcc3258132004ff7458e200057f755853202e7c415941002cfc76885300efcf204c930006f76198532006bf5259010004ff74d8910024fc7558810004fd7558d10004fd7458e21024fc7558a301857c755813207cff715891001cfc7458810036be3059010004fd7558a3101cfc745
  | 6 => 0x77158d20004ff745822102cfd70d8d100067f659813200cfc73d89302367d30d95320057d759853201cfe7458d211867e654c81002dee714c921006bc7458d20036f41058630014fe7358810006ed6248610036de3058e101e5fb7058930006f47158d20034fd71d891022e7f20d953201cfc7458b102367f31d953200cff7648110016de634c620016de634c910006ed7358810016cc634c921016de634c6100057f7558931007db704c93011dde7318121004ff764c8102375f30d953200cfc72d853002eef2158e210067c7558d1002e7c7159410006bf7458d10036de3058e20004fd7458d20006f721d853002efb1058231004ff74d8d211c5df744c530004ff74d853022e7e42d9532036ef7258a300bddc735852002ebc3159010016df604c530024fe75582210067f70d9532004fd7458910086df32d85300066d54588100a6df3258f1001cfe74d853201cfc7458a100067d654c81022e7f42d9532006df5258c10034fe70d8d10004fd70d8d21036ef2058e200057f7558530004ff755823101cfc7458d2102e7e415941000cfe72d8d2001cfe74582210367d1059410036be7059010107cc32981320067f54d8121005f47158930004fd73d852005eee3258910006bf535901014fcc624c931036de3058c100076f754c921035dc764c9300bdde7318520004ff74d813102cfc768c52002ebe5159010006ed42d893102e7e7159410006f541d8532004ff7058e2102cfd72d8d2102e7e3159410024fe7558620005f7714ca100067d54d8d2100cfc7258e10017cf724c93003eec4258810004df735891001cfc7458f100067e71d95321fdf77158d2102efb7058221005f771481100067f54d853022f5e32d9532006f96018132006bc7259010004ff764ca100367f7059410024fc75d8d1000eee624ca1012d7c7558d2102eed5158810216df30d85320367c10594100cd7c755852002ede7158c10036df2058c10024fc75d8d210067f7558d21004ff7358a10006ef62885300047f7558d21036df7358e200047f7558d2002cfc764c310016df614c93100ecc624c93111edf3058d2102ebc215901002cfe71d81320efcf214c930106ef21d8d20014fe76d8d20036ee20588100057d759813214edf3258e2102cff7158810004ff7258f1002eed3158810007d7714c931036dd7058c10106ee4258a30004fd74d8132006df7358910006f561185300067d545863001cfc74d8d10004ff74d8930034fe70d89311cf5f544c93018f6d5448520004bf7458910006de4258c1002eef7258a31066dc6358d1002cfc7158e2102df4714c810005fb704c51014eec20d8931036ee7058810007cd324c520006de7258c10006bf7458910065dc735891002eef415881001cfc74d8910017d7714c5301ef6d544c92100dec724c521164ff7358d21
  | 7 => 0xc52002ddc764c93102e7f4159410005df714c930007cd324c521006df5458c1001cfc7458e20006ed745881002edc2158c100067d54d812122e7e21d9532006df7258c10005dd7348530004fd70d8532035ee704c920006bc7559010005f77158930014fe73586200cdee754c9200057f7558d21034fe764c8100367f405941022e7f21d9532004ff7458a3102cfe7158a312367e30d9532006df638c520036de5058c10004ff7458d2100cfe725823102ebc5159010036bd105901002ddc714c9310067d54d85300067c7359410036ec50588100067f54d893000eee6248530036bf5059010036f41058620014ff764c31002edc3158f100067c4359410036dc3058c10004fd7558f1002ebe3159010036dc3058e20004ff7558e20035dc704c93000def734c9211df5c754c9300067f5458e10006f64158630016ee634c9210067f5458c10007e7714c92100cfd70d8d20006ef7458810037f0104c11000cfc72582311b4ff7058d200067f5458e20004fe764c520034fc7158f10004fd75d8d10014dc7358910034ff7258810004fd764c620006f56118532006ed4258a10036dc3058e10006ee745881002edc3158e21004fd745863014eee42d8931014fe7358b10036bc70590101bf5f544c5301ffcc32d85321f76c754c921024fe7558d100067d745941000eee624831003eee3258810036dd4058c10006ed6248310004ff7158e20004ff74d8121004fd764ca10006dc7358910005df7358121166dd32d8d211cf5d544c93000cff7648610024fe7558810004fd7458d1001cfe74d8931034ec764c920034fe764ca1002cfd73d8931046dc3258c100eeec6258930006bc5259010024fe75d8d10016dc634c510004fd7458a10006ec7258d101fef621d8532036bf105901009cff7058910034fc7058e21005bf745812100cfd73d85320bedc31d8d20006ed4258a3001cfc745862001cfe74d893000eee624cb10106ef2158a30006ec5358810006ef5258a30024fc7558c100eeef20d8930035dc704c530024fe75d89300067d54d8d20004fd75d8d2002eec2158a3100eef604c92002eed71588100247c7558910036ec2058a10086df3258e100eedf3258e20005df724c53002cfe71d8d2002cfe71d891000cfe76d8910006ec73588100067f5458e21006f421d8530084ff7158d100067f5458a3005eef20d891000cff76483100367d205941002fd4314c6100067f54d8132004ff7258c100067d54582310067d5458620034fc70588100067c7558910034fc7648630005ef7258d1007eee3258a10006ed32d852000ecc624c930014fc7358a10006dd634c520046df3258c1002cff76886300067d5458a31106df32d8d20004ff74d8532066f6315863002edf2158c10004fd74d813101cfe7458d101b6ef21d813202ef66118520006f
  | 8 => 0x3606611406019006d380000200a049a10010241600480a0380e41484409061c00002002094150f2466dc82616001004c1283a03a02403000056114038060ba004a000c004040020090000385195805025c0180103001c0882303e01c0280125c15c000410665800900000043c160294ca04c0680101c0000100900e00009806002014620290040140f00d002139ff001002088010060008b40b8496d4044000000000b01280100009c1000c0000f04b0010b6014430130580001c80604601c098050840700000202c9640046a01e0580087d05eee62d89100cdec7548520034fd73d8530006bf755901009eee3258b1007eee4258a10034fd705862002cfc71d8d1022e7c21d953205cff725891002ede3158e21006dd32d853002ef8105823101cfe74d8530004ff764c520034fe70d8520004ef7258d100ecff7258d2014eef21d8931034dc764c930014fc73d8520004fd7558e200067d5458a30004ff755881001cfc7458910004fd7458a3002ef66118530006dd32d81310067d5458e21004fd75d8132006ed43588100067e435941002edc3158c10007d7614c530036bd20590100fd5c754c930004ff7558a3105eec32d89100067f54d893102ef66118532007cf624c930086f631d85300067f64d953202cfc7158d20036ee4058810034fc7058a10006df5358e10016ec634c9200075f754c930006be5359010036ec40588100067d70d9532006ed6348520004fd764cb10006ef52d8931004fd768c6200b57c754cb10005ef734852002e7d715941012d7c755812111ede43d8d210067d40d9532034fd73d893002cfc7158c10006df5358e20006df5358c10004fe7688530006ed425881001cfe7458620006df634c510016dc634c110034fc7058e10227cc3218532004ff74d8d1000eef614c92102cdc764c931004ff7358810004fd71d8d20034ff70586201feef20d85320f5bc7458930014fc7358221106dd32d8d20005fb70485102367c30d95320067d735941000eec62481100067d5458f10006ed525881002fe42148610014fd70d893002e7d31594100063e755901000cfe7258f100067d54d813222e7c32d9532006ec5458810005f7714c310034fe768c62022e7f32d9532005bd7498532034fc764c620004fd75d893102eed4158810036ee10588100367e20594100067c4259410024fe75d891002ede5158c1002ede614c530036bc105901000cfc764c52100cfd71d8d21006dc7558c10036ef305881002edc4158c10006bd644c8100067c7558d200bfcf304c92001cfe7458b10006ef32d8910014fc7358b10007e46148520035f8704851005eef21d8910006f77158910006ed53588100067c65d8132036ec205881001cfc74d8132034fc7648510006f64158620024fe7558c100067f54d89102375f31d953200dee728
  | 9 => 0x2080019200003820014270068000020906488700200c160dc092008248980060002e9622121a80d8090004d00080e0ea01c0d01300423c4880100401c0980401212800a270040d8030000360e80500b040004049900060001101b1640483601603c168030000000000c80d0022580b8030ac04a5681a0120100001000c1880a2b22480509f0050621d4028020060001f3d402e0280000202e000388110080000110d000004000000265680086e6ec0040c91900202405000022000000000260081782b0020280800f00256008800006000000054b60709080800201c0007c09200c050000080080f88a010000018000060002b00201c0084d003006048ad000000060020e200800c0180300a0040a00002210c0f8229000fc0280005c0048c01100a0000003e5aa010008350b20e00a0650261fc0080000e0001001101c8dc030000020001e0006e80862606d00217805815032cc807010002014210360020001c0840020d0000030000c4001bb01e174000130d00880382f0861ac0002603a0441100100c000010030040e8018180066883501307a06c1001e010480060000060041d0096b80701806d000638f700d11e0080700200c0000080101c00001197000074040220050740895900e0ac0680101a0300100200c02c068b5000014d99730ae01c7c0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87d87d09650400d1db05baec6900030f5d154d81322561fb8aeab202005ad4815c9630400d1bd0fa9ac7100031be0974594100052ec28e8b18200087e87d51634800187ee8aa6c4880023de057558d200346f43e86b1820008bd871496404001b8865b8ac0990029da0440d95320146e41ae8b122000c7765dc5604c807878e8aa2c318002976167458c100146e41aebb0242008be8714d64040015ab0610ec2980021fa1c75589100062fbaea6b1c400087e871d563484014eb02206ca99002aba1053588100066bb98e2b1a4003c3e74553624c40117d0e292c808003630c974985320243e43ea8b1a4200a3d841d56348401ad6ea382649000387d525458c100052f428e8b18200487c855d163480018beeba9ac7081278b101545881024d2ec2ca8b182000c5c7558d32840010ff0aba2c6880030fd0b74d953224e1e202e8b282003c3c7455163480014d90ab9ac4080028f61773590100061fba2c9b2a6400e1d5450963040031d904baac688117171db754c9302451f428eab20204ae34815d56404093c7100baac8080121fa16764c9100043e43aa8b1a2000c3d74551628c4011df04bb2648811b9318f754c92000716aa284b146000e2f825d564040011f700ba2c6908030fdd154582210243f436eab0264068f686dc520440610fb0e326ca99003331cf72589100051f420e4b282000ccc321d932440019c8c438ac49800f0f1d3545891001e1f3a2a9b026200d8c32dd1604c80187ee9aa2c6880021f61c425941000536c2ce8b102000c77651c5604c8938f100ba2ca080021f61e74d95322ae36b90ca3026400caf741c963440014db0ba12c40801a37a1f5358c100054fc1aeab20204ac74815d1650400187aeab92c80800f0f1d154d89300051ec20e6b2820068ec82dd9320400787ce8aa2c7880030fdd47458d100061f3a6cb30a6400a79800c965040014dd0a21ac4080021f61c43594100055cc0064b202000c3c751d163480090ff0fb26ca9900297e0d74594100061eba2a8b182000c6f751c9634400d1d90cb9a429011a9b60870d953229da642a64982401996c855cd214800d1d90eb1264080030fd97745813201e1e3a2a9b122000c9c741cd624400187ee9a0eca99003932095458c100047dc3ac03024200e1f835d564040071df0ea16c49893f171cd54589100055ac0864b2020038bc845d932840018beeba9ac6080030fe1d75590100065bba6e2b1a4000e1d54d0d630400153b08292c60800f0f1d154d85200066a39ee2b12204796e87dd53248001878eab2264080029d604325941000716ba2a8b102005ae4815cd62040011bf06baac6908033358f724c6200062fb9ce6b282000a9c835d56404001aceea38a649080f0f9d15458a3122f26316ea99260068ec825d7604840717d0fba2c6901268f61e7559010
  | 1 => 0x906b1264080038755143d8d210347743ea4b10205ac6f72195614c8ad8bae632cc099003530c974d953201567436c69924248a6e85151620400d3990e992609000393d4e535881002d5b40864b202000c3f74d51624400d1b90eb1a65080030f9d065985320063bba8e2b1a4000c5d75d4f63484014bd0b3a2c6080029da0664d95320243e42eec990204ae1f41551630400153d08292c60807e572157348530006363a8e4b1a2000c3d7455162c400187cc9baa6408003335c87258c100243e43ea8b1a4000e2d54d09620400117b0e29ac8080163d205764c81000536412e8b282000aac825d5640400147d0bb92c8080031b5537258d1000636c16e9b2a6400a6f855cd62040019c8e5b8ac6880030f5d342594100061eba6c9b2a6400c3d741d3654c80199ee6b1243180063b20975d81310061fba2a8b1c40008df87551630400187ee9206ca99003335cc735881001e1e3a2a8b1c400087d84dd563480011df04baac690963930c865d813224f1a882eab2020008df835d932440010fd0faa2c48800f0f1d154d8d1000637baac499020018ec825d1634400b9c8e2b12418811a97a0f74d95320061e32ee8b026400a6d8510d620400717908baac488127871015458c100053ac0cc9b2a6403c3e74551638840147d0a392c8080021fa1d5458d1000572c1063b0a40008df835d1624400147b0832ec299006b3209634c91000556c20a6b102000a5c855c9630400187ae8aa2c40800f0f9d15458d2102e5a30ae930a6401ccc764c9314848d4bd06206ca990023de1d61185320346e43ac69902005ab4815d5640400196ee838ac6901270f1c1755901000557420eab102000a3d84194614c801c5ce8aa2c408002976174258c100063baa6e2b1a4050c5c73d5162440011bf06baac5880030f50f74d95320051ec2ee4b202000c6c825d165040a58d8e5aa2c68800f0f1d35458d10006a6192eb30a640487e87dd562440010f90eb2a6408007331c932d85300243e43ea8b122000c3f759d5640400147d0bb9ac8080031d19471581320043fc2aec9922000c6c75589328400187ae8aa6c4988030fdd154d85200156641ac49962000aaf825d5640400d57100baac8080021fa1d654c8100043f438cab0a6456e4c32195604c801958e8392c6880030fdd35458d2002d3a40ae8b282045a6e82103654c80d1b90cb9a429800327dd073589100045fc22ec9922000c3f74551628c00187f0bba2c4880038b20975590100346f43c64b182006a78805d1650400359d0db1264988121fa1f7558d210061e3aee8b1a2000a6f825d165040010fd0fa12ca0812b8bd0554588100346e43aa6b18200087e87103654c8090fd0fbaac6900038d5514158630006b43aee09924000a3d851cd640400787ce8aa2c58815657a1f754c9300043f43e86b282000
  | 2 => 0x1545881022d2ec1ee9b2a6400d5875dc1324c00199865bb264080021fa1d54589100061fa1ee9b2a6400ccc325d932040090f90abb264080038de05755901000717c22a8b102000c7b805d1650400153b083aac6081171b98b754c8100061fc22e9b2a64068dc8750d63880018baa9b9ac48801aaea0032590100047bc3ac230a6046a5e831c7654c8019cee438ac6901238d44275590100045fc22eab1a400487c855d16348401878ebba2c69011a9b60871d95320243e42ae8b122003c3e745516304001878ea3a2c4880021fe1d64d95320051fc22e1b2a64068f8805d1634840187ee8aa6c688003875514358e2002d664326498a4203c3c7455363480010fd0e32ac0990021fe157458d210061ebaee6b202000c3d74553634840187ee8aa2c7080163d2057458d200046fc1aebb024200a6d851d162040010fb0fa06ca990028f61065581320062e3aee6b1a4200a6e859d16204001c3aa9a12c60800297e157258c100043ec3883b2a6449e2e40551620400187eea3a2c4881270f9c175590100051ec24e3b2a6400c77815d1650400187ae8aa2c6908023be0975d81312452f428a8b182046c6c76dd5324848b4dd04386ca9900317e1d5458c100061e3a6cab026400c3f75dd163480018e8cbb8ac0990033958b714c8100051e422e1b2a64008ec8755162040090f90faa2c688003530cb74d953202ce643a6498a4200c5f7558d3204007878e9aa2c6900032d1d07158d200053742e86b102006acc864c930480014db0ba1ac408117171db754c93100716aa284b14200087e8755163484010fb09baac68800e37e1d43d8d212563a38aa8b1a40008dc87551630400d1b90ea1ac7080031bdd77258d102de2fb98cab0a6402ace86d8d324800187ee93a2ca080023de057458d2000d66412c699020008be871d1634800187ecaba4c2990038b55143588100061fba283b2a6401ccc764c93048001968e9b8ac6900021fa1b74d953200666194ec9922000a6e851d1620400b1e902baac6900021fa1c7558d100061eba286b2820008ef8755162040018beebb9ac48800e2fa1f745891002c6e43ac698a4003c3e74553614c8018b8ebb9ac4881169ba0871d953200e6639265b026200a5d83103654c8011bf06baac488002b320d545881002d3b40864b282003c3c74551628c001878caba4c2990030f5d064d95320066a318e2b1a4000c5f759d56304001c3ce8aa2c60801a3b21d624ca102362f31eea990205be4c32196614c805998e6996c290006b3a1b624c9300063a3a8e2b1a400087e871d5634800d1d90ea12c51800a3720d755891001e1e3a2a9b0a6047c5d73194604c807878e8aa2c5080030fdd154586300061fba4e9b2a640087c875516244001ab6ea38264980030fdd154d8d200061e3a8e8b1a2000cb574d86614c80559
  | 3 => 0xab162000c3d74d0d650400b1b90eb1a65881169760c70d95320062e3a8e6b122000c3d755cd64040010fd0e20eca9900393e095458c100061eba2a9b0262008ef825d563440010fb0dbaa64080021fa1f5458d2102e5a38ac89902000c7554dc563480018dea9b92c6880030f1d0655813202c7643ac49962000a5e85d0d63040010fb09baac4880022fe117558d100043e43aa8b1a400087f855d93284001d8a6590ec29800387e115458c10006a6196eab0a6403c3c7455163840ab8dae4328c2991369ee0174594100347743e64b102045e4c62dd5324c40359904b1a65080029b60840d953225d5dc02eab202003c3c74551608c40187ae8aa2c71091a97a0c70d95320062e43aa8b18200087d859d9324400717d0fba2c6880023be097458d1002e6a38ac69862006bc8804c9304808f8dce4328c099002b3e095458c100147643ac49922000c3c75dd1624400d1d90ea12c4080030fdd154d893022d2ec18e3b2a6400c3f74551628400187eebba2c48800e3de1d41d85320156641ac4994200087e871d3654c8018dd05ba6ca990021fa1f41d95320062ec1ee9b2a6457c6d72196604c89956f02baac8080023be097558f100051ec20cab0a6400c3c85dd1634800147b0832cc29912b8b50554588100061ebaee4b202000e1f5394d64040018d90eaa2c4080030f5d154d85320043f43e81b2a640487c855d932c4093c3c80aa2c6080028f610725941001c5e422eab1a2000c5f751cd62440010fb0e206ca990021fe157458d2024f1b882eab202000c3d74553604840b1d90eb1a429001a3720d75d81310051ec20ca302640087e87d95614c8010fd0eaa2c6900028fa1473590100047bc0aec9922000e4c32595320400187ee8aa2c68801a3d21d41586200064e3a6e6b122000a6e85d0962040010ff0abb264080021fa1c43594100347643aa4b10200487c855d932840019aac7b8a6408003875514358c1000716aa285b126206a7a800c96504001958e9b92c68812b0f5c575590100061fba2a8b1a4000c6c75589320400147b0832cc099002976174358c10006a6196eab0264008be871d162440031d904baac788003875514358e1000746192c8990204ea77815d1650409387c80ba2ca080030fdd5644c8100346e43a86b182003c3c74551624400187a85ba6ca990063ba1f7258d100061fba4c9b2a6400acf8355162040051bd0fb9ac4880031be1d54588100072641aa8b10200487c855d1634400147d0938eca990022fe11755891000556c20eab10200087e87109650408b0f90dbaac0990031ddd77158d200051ec28e4b2020008fb87580604c4018d8ebb92c6908028fa1073594100071dc02eab202000c3f85dd1634800147b0832ec0990021f61e64d95320043ec3e86b282000d4c325d6604c80195ee9b92c68800f0f9d
  | 4 => 0x44081d80961c9e00c010001a0288701c02008586c40301c06091360d4000ac000a80203c0a0008d16c320045e011ae1481d03c17014eb0043a048010983f0640c008030240316005008130780009c5312c23038250086603818004d2144000425606484038010640a1d80004c7a0e0020846f00c0f1282001c05000640000b000100003c00400260070000105d5d05401000001303b08c010600b0cd76001330000304d560c495024040304c0482307c4b00439090000300000008000030040704c03374110a02c1c0060e9c71400c048000000c00011018001d04f004000c00413024051130202a0f8161000000c0c00000000020140f00017054990a00002c0708801008063b8000000808c020002a000013880d0280187ee8aa2c310003331d9324c52024d36c2ca8b102005bc4814c931484010fd0fb2ac0990038d55141d85320071aaa282b0c4003c3c74551608848f8bae6328c29900f0f9d154d8132006abba8e29926200c7475dc5634800193ee9b9ac48800317a0f74d95320166639a65b0242018dc8758d32440014b906ba2ca0811b9318f754c9210043f43ea8b1a2046c6c76dd5324800d1d90ea12c508157179cc651813222d37416e9b2a644987d879d1650400559906b1264881221fa1c74594100061fba8e8b1a4000c3f74103654c88d4db05ba6ca99167930c865185320347a43a82b0c600087d84dd5634840199ee6392c6880021f21d5458d210062fc1ae8b282000e2f54951620400b5a902b1a62900030fdd77458d1001e1e3a2a8b0c4000c3c85dd163440014bd0a212c6080121fa1f7558d1002d7240ac690a4000a9e841d5630400717908baac6900022fa1c7458d100070eba2a8b182000c5f54dcd6244095c3a82aa2c60801a3ba1f5258a1002d73436c290a400087f855d932c40a38d8e4aa2c688016b5a1b614c5302a63a38ea8b1a40008bf845d9328400196ac9b8a640800e2f211764c9100061e42ee8b122000e2d545096204001d8a6598ec2900023de1d611852000566412a8b182000c3f7455162440018b906ba2ca08002b520d611852000572412c230a6000c3f845d1650400187ee8aa2c118803331d93248530006e2190e2b0264068dc83dd9320400359904b1a6588003171d5634c81001e1f3a2a9b1a4200e1c835d56404091c6e213aac808002976144258c100043fc2ae8b122003c3e7455360484010fb0fa0eca990023ee1d60181320061fba2a9b0a6000c3d745096504007878e8aa2c68800297a174258c100061fc2ee8b1a20068ee87d096204001c5aa9a1ac4080121f215764c91000727c1aa8b1020068de87d4d638400187ae8aa2c7880031b1d77258d100146e41ae
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x7008900000120201a06161000208007800214102001c007622c59a0c2048d0000000640800200607dd183103654c801a0c32610659853201e0d21d54505618c001a0c8320975590100053164432dd9320400103d94a1f65585322f6079cd84194604c801689900c9644c8100050b65075589320400781c875514358e2000711194321c5604c80141d941d5634c8100060b5c984196604c80181d7361065181320040f66075591320400184c8320974594100050b65075dc96348401a0c3261065d8132005926403259532040b9a3381e01755901001e0b21d54509628c00144e960cb75581320054665075dc1324c001529941d7704c92001e0be1d5450b624c4010cd980c8764c9100060b5c984194614c80781f8755143d8d2101e0de1d54507614c801c0c329d065985320061321c8355162040078348755141586200050d650651c5604c80782c875514258a102ee0b9c984194604c80184c872095458c100040f65087595320400122d942157358810005076507558d3284001a0c3261065185320053264032dd9320400181d73610659813200487650855c9630400181f7361065585320240f26174551634840141d941d77358d21007030c874195604c8018377460440d9532006075cd84194614c80103e9819774581320050d65065dc5604c80182f7460840d95320060ddd181993654c801a0c32610655813224d0e24174551634840184e860cb74d9532005a164432591320400903e98dd164d95320040fe6174193654c8bf84e83a0b74d95320059164432595320400103f985d074d953201e0721d5450d638400182d7261065181320060bdc984195614c80142d941d5624ca100040f66274196614c80103d981d06558132
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x8100001806cc0643a0cab026400a826803261065d813200580b483286438ac09900280da70c984194614c801806cc0653a0cb30a6400a81684326106518532
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
  | 23 => 0x98c
  | 24 => 0x98d
  | 25 => 0x98e
  | 26 => 0x128c
  | 27 => 0x128d
  | 28 => 0x128e
  | 29 => 0x9cb
  | 30 => 0x9cd
  | 31 => 0x9ce
  | 32 => 0x12cb
  | 33 => 0x12cd
  | 34 => 0x12ce
  | 35 => 0xb0c
  | 36 => 0xb0d
  | 37 => 0xb0e
  | 38 => 0x140c
  | 39 => 0x140d
  | 40 => 0x140e
  | 41 => 0xb4b
  | 42 => 0xb4d
  | 43 => 0xb4e
  | 44 => 0x144b
  | 45 => 0x144d
  | 46 => 0x144e
  | 47 => 0xccd
  | 48 => 0xcce
  | 49 => 0xb0995
  | 50 => 0x98b15
  | 51 => 0xcc995
  | 52 => 0x98cd5
  | 53 => 0xcc996
  | 54 => 0x168b
  | 55 => 0xb49d5
  | 56 => 0x9cb55
  | 57 => 0xcc9d5
  | 58 => 0x9ccd5
  | 59 => 0xcc9d6
  | 60 => 0x150c
  | 61 => 0xccb15
  | 62 => 0xccb16
  | 63 => 0x16cb
  | 64 => 0xccb55
  | 65 => 0xccb56
  | 66 => 0x154c
  | 67 => 0xcb
  | 68 => 0x24b
  | 69 => 0x17cb
  | 70 => 0x164c
  | 71 => 0x5cb
  | 72 => 0x1a89
  | 73 => 0x1049
  | 74 => 0x104a
  | 75 => 0x5995
  | 76 => 0x59d5
  | 77 => 0x5816
  | 78 => 0x5856
  | 79 => 0x104c
  | 80 => 0x1a8c
  | 81 => 0x104b
  | 82 => 0x1a8b
  | 83 => 0x9c996
  | 84 => 0x1a8a
  | 85 => 0x44c
  | 86 => 0x5c9d3
  | 87 => 0x44994
  | 88 => 0x5d693
  | 89 => 0x5c253
  | 90 => 0x45414
  | 91 => 0x5d453
  | 92 => 0x198059dd
  | 93 => 0x150e
  | 94 => 0x168e
  | 95 => 0x445d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1220
  | 6 => 1501
  | 5 => 650
  | 4 => 68
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/27+packedAt gbK8 (1612+(h % 27)*6) 6) % 62)
  | 7 => 2*((h/483+packedAt gbK7 (45140+(h % 483)*11) 11) % 1220)
  | 6 => 2*((h/507+packedAt gbK6 (72048+(h % 507)*11) 11) % 1501)
  | 5 => 2*((h/223+packedAt gbK5 (38350+(h % 223)*10) 10) % 650)
  | 4 => 2*((h/43+packedAt gbK4 (4760+(h % 43)*7) 7) % 68)
  | 3 => 2*((h/9+packedAt gbK3 (486+(h % 9)*3) 3) % 6)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff81f01e07fc0ffffffffff09e81c7d031fff
  | 1 => 0xc1ffe001ff83ff07807fffff3690e38e1ce4ff
  | 2 => 0xfe1ffffe0003fff8007c1f00c71f03f3e0f8cc
  | 3 => 0x1ffffffffc0000007fe000f81ffc03ff00f0
  | 4 => 0x1fffffffffffffff800000ffe00003ffff00
  | 5 => 0xffe000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa28030820144028a315294a00280c35010955
  | 1 => 0x41516010ca819505042a52b41290618a0c64aa
  | 2 => 0xac1aad5a0212e6b0094f1c06451b02d360b8cc
  | 3 => 0x81cd69d7358042012739818a81db403b700f0
  | 4 => 0x210718e19c6338c65c000020ffc00000dad600
  | 5 => 0x318000c018403084600000c0ffe6db6c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeafee8feea8888feeafee8feea8888feeafee8feea8888feeafee8feea8888feeafee8feea8888feeafee8feea8888feeafee8feea8888feeafee8feea8888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_39085
namespace PEqualNP.Outside.L_meta_39085
open PEqualNP.Outside.L_meta_39085.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 3 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 7 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 5 := bs0_4_0
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
theorem bs1_4_0 : Interval s1Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 2 := bs1_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 6 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 90 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := bs2_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 14 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 85 := block_range (n:=85) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 85 := bs4_3_0
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
theorem bs4_4_672 : Interval s4Atlas 4 672 82 := block_range (n:=82) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 754 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 bs4_4_288)) (concat (concat bs4_4_384 bs4_4_480) (concat bs4_4_576 bs4_4_672)))
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
theorem bs4_5_768 : Interval s4Atlas 5 768 11 := block_range (n:=11) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 779 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 (concat bs4_5_672 bs4_5_768))))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 10 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 112 := (concat bs5_3_0 bs5_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1344 : Interval s5Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1345 := (concat (concat (concat bs5_4_0 (concat bs5_4_96 bs5_4_192)) (concat (concat bs5_4_288 bs5_4_384) (concat bs5_4_480 bs5_4_576))) (concat (concat (concat bs5_4_672 bs5_4_768) (concat bs5_4_864 bs5_4_960)) (concat (concat bs5_4_1056 bs5_4_1152) (concat bs5_4_1248 bs5_4_1344))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_960 : Interval s5Atlas 5 960 57 := block_range (n:=57) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1017 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 (concat bs5_5_288 bs5_5_384))) (concat (concat bs5_5_480 (concat bs5_5_576 bs5_5_672)) (concat bs5_5_768 (concat bs5_5_864 bs5_5_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 48 := bs5_6_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 6 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 68 := block_range (n:=68) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 68 := bgb_4_0
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
theorem bgb_5_576 : Interval gbAtlas 5 576 74 := block_range (n:=74) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 650 := (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576)))
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
theorem bgb_6_1440 : Interval gbAtlas 6 1440 61 := block_range (n:=61) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1501 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 bgb_6_672))) (concat (concat (concat bgb_6_768 bgb_6_864) (concat bgb_6_960 bgb_6_1056)) (concat (concat bgb_6_1152 bgb_6_1248) (concat bgb_6_1344 bgb_6_1440))))
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
theorem bgb_7_1152 : Interval gbAtlas 7 1152 68 := block_range (n:=68) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1220 := (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat bgb_7_288 (concat bgb_7_384 bgb_7_480))) (concat (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)) (concat (concat bgb_7_864 bgb_7_960) (concat bgb_7_1056 bgb_7_1152))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 62 := block_range (n:=62) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := bgb_8_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafee8feea8888feeafee8feea8888feeafee8feea8888feeafee8feea8888feeafee8feea8888feeafee8feea8888feeafee8feea8888feeafee8feea8888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813544 * 2 ^ 32 + 4276783240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_39085.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[3,6]⟩,⟨.and,[0,1]⟩,⟨.and,[3,6]⟩,⟨.or,[2,9]⟩,⟨.and,[5,10]⟩,⟨.or,[0,10]⟩,⟨.or,[8,11]⟩,⟨.or,[4,13]⟩,⟨.and,[7,12]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276783240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276783240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_39085

open PEqualNP.Outside.L_meta_39085 in
theorem PEqualNP.Outside.L_meta_39085 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276783240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276783240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
