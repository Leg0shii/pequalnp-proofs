import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_38003.Model
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


end PEqualNP.Outside.L_meta_38003.Model

namespace PEqualNP.Outside.L_meta_38003
open PEqualNP.Outside.L_meta_38003.Model
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

def SBf (j : Nat) : Nat := [8, 6, 8, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_38003

namespace PEqualNP.Outside.L_meta_38003
open PEqualNP.Outside.L_meta_38003.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x4000300308078228134408b0022025850006431400d8fc31fe42fc10fc43fd31ff43ff31fe21ff42ff41bc40fe30fd40fe20ff20fd21fc32fd42be40fe10ff30dc30fd43fd41fe43fe32bf41fc21fe40ff10df31dd31fc41fc40fc42fe31fd30ff21de30ff40fd10fd20fc20bd41fd32fc30ff32fe41
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x841df42cc6fca198df95031ef29c43de53c82eea2905fd4142de19283ee21883ba60186f55031f790c43be42506fca7106f10020bfaa041bc52103da43904f55031be2a4637d54c42fea99877d4d10cf988817e50042faa9086f50710bea9663fb20482fca9985f15010fc90041ed320cb78a89077d0f31bfa9a417e53086f8a098dfd52309f2a463de300837a64a0df94441fb88021df53843aea298db14910bfaa4637c53486fca5885f94630efa0e63be54c42f2a010f78c320beaa261bc51902fea5085f55320ed28061bf544c3ba87994f952219eaa4833c54442faa7a17790c30df28283dd50cc7ee4310df94031bea9c65df319037a8390efd0430bea8c657e52843be6318df95232de2a265bf414c2f8a990dfd5121efa9a85ef21482fca3215f94c31ef298857c548cb78a6205f55030ee216637e530c27ea9085794c21be2a6653e54c43dc40905f54740be29421dd310c3be6310f714b31de2a261bd548c6faa2217708430beaa241be400c3bca81857d4d20bf29e437e54086fca3a17dc4210dea1a835c504c7ee42086f50620ef988633e541067ca810de94021be29021bd43903de84a15fd5320ee21e637c5150efca918f7cc440de20c817c544437c80985f94a32df29481dd210c3ba62987710430bf290857e510cbbc64187e94021bf2a2417d510c2f8a890df55121bf296837c54c42f8a6885f94b31eea10617d54906fea70877cc410dfa1c87be54042fca910efcc941df21c819f410c2fca6207dcc631ef290617e5104378801877d4a30eea98837f534433c80185f94231eeaa461ee210837aa9907794931de21683de539077c87a0e710030efa00617d500c77e8298f7cc520bea9683bc425077880987790d31bf2a621de52cc67aa3205f54021bf28c413c54482fea9087794030ee29a417d54cc77c65205f14540df2a063de438c3be84187dc8610bea9c43bf53d06f8a6105f54630bea9621ee21486fea2a16f54e40ef98a217e521037aa910efd0421bfa82637f524c7ba8498df54f40df218815c53443bca5186f0c640ef2a2635f53442bea7085fd5131ef18261dd31086fca021df54b43bf29043dd319037c65a0ef50731de10c817e500837ca6a0dfd4940de98c815d510c37a82a077cc610beaa487bf41487be86185f54620ee29c21bd505077e8220f7d0430ef188617d519037e86a15f54a30ef98e21bd21903bc8398f714931ef98e617e530caf8a788778c931eea96637e54cc7da40105f94e21ee98a43fb40902fca9186f90c42cfa0a63dc414c77a85206f50b41ef200615d53886baa3187708630ef990657d53483bea8187755131de988813d54087ba86997b48421dfa9081bf41d033a63206f50420dfa0481dc430c37842206f94640dea0e415e50cc7ba63a05f54a40aea9e817e50d0e78a8995f54242
  | 1 => 0xe519027aa9985f94730bea9021bf51506faa7206f95231ef282637d53102f8a2986f90310bf29e81bc54843ba63885f94641bea88417e53c82fca4197bc8020bf29487bd43d0af8a4a05f94830aea9e217d544c77c84204f54440eea0a63dd324c77e83107d8c4319e2a261df308c3ba8698fb8c832bf29c217c538877864205f55242dfa8c81be54886faa70877d4131bf29a41bd41043de85217790f31efa9a81df52cc6fca820778c932bfaa265bd410c77a8310f7d4430bf294617f53c837aa8195754e31bf2a641f751483be62186fd0721bf28061bc40c43bc85185f54432de99081dc328c2fca5987ed0140bf2a087be53102f8a498f74c620eea0061f9300c3bea898ef14941dea08817e52d037886a0f714d40bfaa261dd31c877e43205f94910fba0c83ec52442e8a29077d4630ef21e65dd418c2fea4085794f20ef18621be408837ca4205f94021bf2a0836f52442fca40877d4830b6a9021bf32d06fca420f7cc530f7908437e53c42fca121df54730bf2a4215e53d03f62088774ca30beaa661df430cafaa1a1ef50c43dfa9481ec21882f8a898df94c10bf280817c540c6f8a8986f54a40ee18041df324c77ca9986fcca40ef28861bf21103bca7885f54831dea0a41dd518c3f621084f55032bea96817d52107b861905f54f41eea9e81bd43102bca0185fd4f10de20441bd519037ca7a0df94221de2a2217d5010efea2905f94431deaa043b751507be43187754a30eea1c61de30882fca9106f55310fa88021bd41443be65195f94e42efa9a417e51086fea8185f54331bf2a0657d50d06faa8996f95320bea8c857d52906fca0216f90541be28a657d5210ebca7885fd4132be29e43bd41843baa720df14142df99081df50cc67ea8887754931bea9661dc430cbee4290fbcca32af29821bf41502faa2207715030fd10221de548c2fca721e750c439e2a4216e52043be6210df15230bf28c63bf31903bea298f714d42beaa0657e5290af8a4a0df94c41dfaa4217c53087ba62a06f90140ef19663bf410837e8621f7d0d43ef994617e5210e7aa9887710731bea9c85bd41cc2fca8997750b31fd10421df31486fca1087e50040bf2a085f7415077e83907750c43bf298857e5190fba64197714430bfaa043dd31c827ca9986f50f41df28881bd521037c80105f149109eaa6417d53443baa710ef94e40bf2a643be40c83dc842167d0731be29287dd530877887a0df54042be2a0437d528837e62206fd0b41ee98841bf50d07ec20886f50040dea96837e528c778a5a0ef94341aea9c83bf52506faa720fe8c030ef98e819f31902fca5a1ef10320df292837d548cb78a7a0dfd5110af29883ec21083ba81186fd4b41bea8465bd52507ee6298f714630faa08837d520c3be63185f54610ee29a217f53086f8a9085f15331bea9
  | 2 => 0xc6baa7906f14e40bea9843dd5310afaa118df94032bea8e657e50883be85187754830ef218877c54083f480206fd0621ee182217e52082fea090f788630ef98e437e510c2faa790ef8c440de286837e51c82b8a7085f94321df10c817d54ccbbe83186f50430dea8881de54cc7bca610d714d20dfa08817d52843bca198ef50530ef210619c408c2fea4a1df14b10ee184217f54ccafaa121ef54341bea9487bf410c7ba8798efd04109f28683bc439027aa918f710d31ee98821be50103ba62205f54e20eeaa6637d50907bc82185f95121bfa9261dc424c7be63106fd4e40dea0e817e51d0efca2215fd41419f2a0637c54c837c42206f10a40ee98863be43506faa518f794c41df21c857f5350afaa9187790230df20021dd31442faa620d754c41beaa043bf41483b887195fd5032ef18c617e50ccaf8a8185fd5010ef996637d5190f7c80887d88421be29821dc320c2fea5886750430f6a90217f5050fbaa8186f10c40bfa9a81be40483e842085f54c10ee98a417d50107b8a9185f95010df192837e51ccb7880085fd5321ef98061ed4210afea7106fd0510fca8043bf5310378a6a0fecc230bf29a43bc42102faa0196f10c429eaa443bc31103e8a2907710230beaa6437d50c87baa7906f14141dea0843dc438c3de43907d4c431bf284617e520c6faa918f7c8430dfa0c837e50d0b7ea6a0d7d4d42bf28683bf41843de41105f14d40ef18021bc52903b885187b48520bea9c617d548837880906f50531deaa661bd41487b863185f15032bf2a2613e5090278a0a0f74c610ee28663be40842bea6a04f55010df2a0437e509077c86a1df94632ef182417e50106baa608770c310ef98a817d5110ff220085f14132dea0883ef52443baa218774c830efaa663dc504c77c83206f10110ef20a637d51c82fca720f750430dea9a837f5150e7ea8905f54910be29a83bf511037a83185f94420bfa9c437e518877a84a0df14542bea8443bf41cc37c82205f94a40fc90221ee520437e85217e84010efaa461de53042fea9885714d40beaa4439d414c7b8a4185f94740bfa9e43bf544cafea2996f10210af28461de30443be62105f54c42be28a41bc51102fea9195f54342eea1861df31c83f241084f95032bf2a665f641106fca621ef4cb419f2a6417d53c437c81985f94240ee19263dd31cc2fea6107d08610de19683bc4390a7ea8996f4ca40bf288877e54083baa788778c210efa92637d50ccb7a86a15f14141df216835e53907bca318770c220be29261dc54cc77e8398ef94b41bf2a2637f535077ea8885fd45309faa2617e53443bc83186f506409f280817c5050f7865205f15220ef21a657d538c6fca8185f55010de20661be429037e83887790931dfa1a83bd418c77ca8196750630ef990617f52442fea8905f54a21aea98857
  | 3 => 0x1180c010100b01e000103c880079560a014018060a81e001ea00a41a48080a04ef38000200c000ac002ec080100000208006000220480603000088260086a090000701c30a4e000780000a02042038a00c80006879b189003808830000b80000800168060c800061f234a04006bc03812008010600200c5200802780320001e0080000012198200001403800198120b000868106487e0701a018100d0000283c158281386a010041800611b580b000008000785e6d81c0109c0082201008000000480001030008201281c0408a0009e8b80007802718020000c040000e0040100002020010260103e030120c80405000068dc03160054ea008020102c0000405000018280080002014010004b03001002138061a0141784c0100c078023e07e418082680c0c04a2103a1486209810008e400802090da01888090541b002020181400e2001000026598041040201024020081681e8a9461101c01c85ce0142e2100a0121e0040000000026050121c094000140a02c030000180401004000e20300a05006000160081e0429a000060100800000148040b0000001c00004e70100000003ac8390d204800f780c000560003e10800428720503bc5800010021106e06000030460182a018000054e00810028060282620114020060004a0c80000800018051080806800018001185e275fd5220cea0e63bf43d0afca520efd0630ef10861dd530437c84a15f14d42be29c217e508cb7882206f8c840efa1263fa200837a42205f94242df20461de328c37ea0a0f710030dd280817e53082fca7a0f7d0e43ee98c61fb20882f8a8997714a30be2a2417d54903ba4318674c440af29c43bf42902faa7905f55020cfa0c61dc310c37e87205fd4941dea98817c53c83b884187d48421bea9a43fb304c37a84205f15221ee196637e53d0b7e87a0fbcc932bea9081dc418c2baa610ef55010ee18021dd31887bc8598df54743bfa8a81bf401037ea8907794f40bfa9821bd4210b7881185f54742bfaa6637c53483ba851877d0d31ee2a263bd53d06fca2205f14121af298857d54442b8a6a1770c120efa0461bf42102f8a7106fd0640eea8263df414c7ba6598df55031dfa0c637f548873c81186fd0c40af29863de314c6fca8887750731dfa12833e54042fea690f7d0e30bf29c81bf4210af8a99877d0e32df18c817f540
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x442cc6cd62d4331a798331102cd62146309759531d031d5350410c7d53318435763d4520a758c425071e5494e218f990540434f5294a308f98254886766115332a798e519033464d45209d984540c23c6454d209e983548ca5f6354910b6980518c2da60d46309e98052042d561150309758e544c23d6414931a7993528c33954540219b98a544423e64949108f592510423d6414f21a7586400c23e650ca40c7151430c26f6548421c714d415031e53900108f590514c355515043097996414c63e65d0510b5984520c2ad621464097995314839a50100309798f5050a9d6310a40c715331842db6048430a7592410c29c6454331a7d8d521031e54cc421ab988519025f635424197d8d50c865d6194c42d694e50087e32148210c755230c423e64d4121b6580210c3976150630c7150304826d6215331c714e40502786055121a7d91324c69d648c430b5587424c72c52d051097996410c23e6515132a7983410c2b86050730cd945410834d5354810ad984521025d63d4121cd15351482da60086308f19153486ba6014a408f587544cb1d53900109718d54442756114c20b558452cc65d658c010a798e219025e63d41419758f52c431c5414d20b6181310825e63148109e583548cb1e540c320c7550430c26f6254d10e5d85414c63d6595031a798c411031d54cc410d5d4c514834c52cc510d518f514831e54cc4318f992510429d648863097d8d52103a84048020ab18950506b56114c40a758c411027b6054d218f99052c431d544c621975875350b1e5350410c7d4c404831d4354443d354830042bb6048440c754c40c825f654c431dc58051483556114e1097181538865c6354b418f584544c32f52d0510c755131c423f6550040cd584548433551d0440e5545410c31f54d4d20d6d8e500872f5294a408f594311029e6010030c714d414834e5354810b5584308431d5454c21a7181410c29d63084408f58654c831e544c4109bd89544427661150208fd9541cc2b56190010d64c6500875551884308fd95410869c644c030c795230c42e461480208f995414c31e53507208f59252842b56114f41a7d91524c65c65cc520a7983414c67761551209d984530831e548c010ae580211025c63543418f191524433451901209d584540c3555148430ced91500865f63551208f59741cc398400c010c795131c431c53901208f990538865c6354a10b5d85544c65e63d5031c7d4f418432d5210010c795253c825f6550a309ed8154486796014c21cdd93514825e6394642c755253c423d6494d10e610030c42d56115331a718d42d069d6414b319e583540871f535051097195434c65d6594c21a7191524c69f644ca30ae181410829f6550c438fd95329025d63947208f592510826e6294d1097997315025d63948208f596400425e65cc520
  | 1 => 0xc71c5350d41ae980511031d4394043cb15052442796015021c794f41c4399419403097594418c31f5410e30c7950300429d6490c43a798c419034c528c110c715131842ad62144409758e524431e544c421c7952530865e65d0d3197994420c395414c721a718d4210a5f63550208f191500863e650cb418fd9153483976150430a7990218c31d54d0c328f592510c32c54d4910c754c40c425d639521097d96300423d6550720cd546311029e63144409798e510823d6588640c794f41d03692154021a758c511029e640c8309798c54c829e6310840d314c524425e6315031e6942400c23e65d054097594430ca7561153329798e518829e6390440ae181311031e544c431d354852cc63c64548309758f505071d41141319718d54c863c6454e10b6181544c69e6494a30ae582321032f54d4910b6980210c29e6390640b5987424c63e60151329758c52c429d6314b419758f548869d6488430c7552300429e6314b418f596211031d5494f209d986544825c63551218f994321025e650c1108f993530423c6454d1097596210c23c6454231a798e415074c524c510a758e211031e5454c10c755131042d5618c2109b588540425d654c720c754d41c831e535062197994410c23d61d5130d3d4a304425e6315010c795153c8277654c43197594424c65d63149419b58b530431d5350421c755030c429e640c6309e980530863f64542319758c540431e54cc730a7990524c72d5210840d314f52443345414520c7951438c2bb6054941d3d49314425f6154f408f993538863f6454d21a7593528c25d65906308f592520823f65504419758e510431c54d4d208f993538829d64149319b58a54443a54148421d5945311023d6115132d654d500863d6494910a758c419031e53d0431979825310b4e524ca3097d95320caba60d4840c755230c829d64cc230ce980548425e6315310a798c521031f5390120c754e40c829d6308640c7952530423d61d51209758e51d032d525041097982530872d5494810ad98453103645148520c714c408425d65cc7409718d50c87394154021c755131cc31f53505209798e51c825d6508630a7d91320c25d65d0c3297994418c32d5214941ae580219029e648c6309798e548425e6315021ce983548423e6494d10b5584520c23d64d4e208f592530c2b56114b418f99052042ba6008440ab98853d069d640c4309758e5108755514c440f20c1200823c6454032c5545410c23f65d0730da14a20442d56194931c7d4e539029c64541319798f504865e6395220cb54a400423d6508640cd587548435453145208f5935204395514c4408f994219027960d4c21c7d53314825d63d4810cd951411063d658c4409798f5408715514c440a7992210c23d6494421a7992314c71d5310f419798c540823e60950319759
  | 2 => 0x64944309758e51d0a3c6454b31cb14942506b56194941a758e419031d51d043097d8d544ca3d6494e1097596410c2d76154931d6982500c25d63d52208fd85540425f6154c429798e529023e64951209b98854cc71d5314d41a7d9152cc65d6314542a71814310e5e6395120a719152cc6776154d20ae1815250737515052097195315031e544c730c754e40c433754d4520a718d521031d540c0109798f54c823f65d0720c7153314429e64146309b99721483345150520b6d81544c65e6014d4297997314c23e64d4810b5584300431d53d0842b3588540c31c5450f31d3148304423d6414c10cdd44404831d544c72097195314423f654c8409758c54c831f54cc530c75525304357510c1208f195329023e6414d219e983530863e650c9418f990530863e6494820c754c431029e640c43097996304431f54cc510c7553320ca3e651512097d8d50086d561d4b319718d548433551484409b59621082e9600842097d95420c31e5454e21d3d48304433551d07409b58a534425e63d53109e983540863c6550530c754d418863c64542329798e51d0a5e63151219dd9510042ce6214630a7993308c25d61d4d209758e519023f6590010c795030c42b5611021097d8d501069f6354941c7552538863e6414931c71523084356631452097994424c65f6354341a758f50d063e6494420cb148404423d64d4f10a758f401025e631454097587535023f6454d109718d521023c645433197996218c31c5350610d654e500875561d4e10d3d4c524423e6494720a758e219023f6510010a758f409025d63d5021c794f410863d64d41219798e524434f52cc510c714f41442ad6214c40c7d06500c23f6454c20cb54852d076552c8410a7191520c31c5390210a7d9132cc75863940218f19150c86e462440108f992528c31d5350740d9185520431d540c320ce506500872f521011097d94300425c6054c218fd9150cc71f544c520c7547418c2b86050430ae980219023e64145329718d500871e53504418f990514c31c63550329d584540823e6590130cd546211031c548c932c7551310c71d5314c40ce552500865c65cc540a7990324c65f6354342c7d51318423d6590440a7992310c2b661cc94197596310c23e64150318f596540429e6414b31add85535071f5310210c7d4e405034f53d49109758e518832e5454810d394b310431f548c1209d185544825e63944429b98a524426d62150308f992510c71f5410e32a798f50d071d5410f319758c5448798604c440c7d52308425e63d5220a718d505063f6454a10a718d421032e52d0410a798f505071d5350441cb54842d065e63145209b994524425f654c740abd89505072f54149109798c540ca9d6390440a7983319029d64cc030e6cc6501025d6315021c7550434c71f53d0540e5d47414
  | 3 => 0x4309758e544831e5310310c7152434ca5e6510b31c7150534431c5450f329b58b548c27b6550040c754c53d0738649402197195434cb1e5454c219758c54c863e6414c20a758e519031c548c110c7550430ca3e64947329758c540831c544c51097597400c2da60d52308f99252842ae62d4341cdd45415023d6494a309798f540425e654c540b3189544c63d619533097584534825c6550b31c794f418871f548c1109718d508869e63d0040c755153c423d6414520a7993300c29d6390541c7d5053442b86048440b558754cc66e62148109798c525065e6395110b398854cc71d53d0410c7d51314431d4194331cb149414429e64104308f993504c65c6550a30c714f4350b1d5454e218f191508863e658c4408f99054086cd62d5230ce95150087c53148421c7d51314c25e6394421a758c5190356534c4318fd9541c823d6115120a7191320ca5e63944108f992510ca3e658c6408f59251cc397614c640a6181311023d64d4f20a719132cc6b561cc9419758f540423e64946328f992518c23d650c840ce982501023d6494632c7d52548c23f6454221bc580218431e5454f10a7592528c29e63109419718d50106cf6255131ae181535065d65cc7208f99051482d8604c7408f99353c825e63d4b10b6983510c3696014910cb551520425d6590c3097994304832f5250510c794f410425e6510531979963048355514c4209ed95200832c5290110d514731482ba60146408f590534871c53909428f596319033754145209758653d025d63153109798c54c866d6214c10a798f529023d6494431971815310b3451d0520a7590510c2f06148210add85525069c6350941ad58753d063e60950328fd8554cc31c53d05209ed81544c69c604c640b6980528c29f6350b41a759032cc6d8604c4408f994319025d65cc421a7990414c69f6350840c7d4d418433b6494021c7d50304829e630c4409758e511025e6508430ad584521032f5290110ae980521031d5454c109ed95100425d6315221e5945311031f540c2108f996219025e6510a30d9147214823e6508440ce191500874e528c010d5d47314829e6310a408f181548874e524c410a758f505065f654c030e64c6501025e6094e41c7553310871e53d0720e6980408c29e640ca309b988540c25d6510c308f99352c431f5390210f8086208423e6494c30d5547310c31d5415030cdd47414823c654cb4197d95400c31f5414d208f195414823c6454c209b98b530425f654c720c754d41c425d6395220c7d4f414425e631522197d8d544423e649473097195420c29c6350a40ad586535069c6354941a758c525071d51cc440a7992518c25c6355120c7544400c23c60552319758e5190b1d5454f208fd9532d063d65d04109798e51d031c540c210b5984540c25f6154c10a7990210c29d
  | 4 => 0xb98b548c23f6454021c794e40c429e649443097d95424c63d6508440d9146204823c6015110a758c521025f6354a108f181540c65f654c4109e181544c71d5415131a7d91520c23d65507308f592510ca9c6354b41ce952500863d65950329758f54c42d8604c5109798e511025e6394820d5945310835a60d4e109e181534869d640c931ae980531029e63d0240a7d8d429023c6550510b358854cc66e6214c1097d8d544c27761549108f992538423d659502197994534431d51cc640d354e520423d6414b108fd9150ccabb6054d41e6d8131102b56110010c714c404423e6588440e6980400c25d6314810c7153314836b2154021b3189504c6ad6214f418f5964310a3e6515110c794f4110754518c1209718d5010a3d650c94197d95310869d64146308fd9532506ad62d4341b6980548c25d6510430a7191328c25e6094c41b6d81410c29d64d4331a7590328c2ba60d0610aed81311031c53d0540c7553318c63d6494630a718d50d06796584010c7153534429f645433197d8d54c869e60d0731d5145314831e53d064197d8d5010a9e6394a40c754f411069d64d4131ae983519023f6454321a7d8d505069e6414830c754f410865d6114d42c754f41c833551506409bd9520082d56195131b6980510c25f65cc720c7953318871d5494c218fd9152cc71e53504318fd91520c398400c22097584535031f54d4d109bd954210ada60150308f997414c23f65504109758e544423e6495110d5d46304825d6588630d3948300431d5350842b398b548c29e63084409b189544c74d5214931a758e311029c644c931a7993504c63f6155320c7940400c23c645403197181539073b4154021d354b310432d52d0410d558c514835b31540218f992518836952840108f593530871d5110230b3588510c23d65d04218f996404423e64944309bd95320ca3d6414c20d394e520435551cc7308f994544c2da6014830a7590218c23e60950218f593538869c60507318f59251c831f53d05208fd91500c757514c520cd59051482776550441c7551310865f6550b318f992534829d6494630a7d8d50d06d5618c01097994218c23e65101308f59053886ba608c840ae181418425c6354242c714d4350b1d514c440c7545410c25e6314542c7d04504c6986050430c7151434c66f6255131cb949429023f6550c43b6181410c23e65d0d42a7584408c23f645423297195424c63d6414f209758c514825e6314c219798e534429f6354b419758f5050a9d6310b4197d8d548431c54cc530cb948400425e6014d10975855304336641452097997314431d51900308f5925388395414c510a799032cc63e6414f21b6181318431f548c130d3548520c397614c4408f195321029f63500408f593504cab56190210ae983511029d63d4a40d6d8d50086d86048
  | 5 => 0x4044335515042097594210c31d53d071097594420c25d6594c108f594400429d63944408f997414825e6314b10d914a104434d520c830e6181410c354510c120ae983539023e64d4c218f995414823d64d4b10b3988540c31f31940409718d540829d6190230b6983540c31d544c832c7545319029c63500409798e51902e96008620a798e21102ac6254d41d618d500863f6454032a7983418c31c544c520c795230c829e64d4331e6100304831c54d4e108f597410c74d520cb3197594428c31d31940409718d50d0a5e6394a109798f520431e5494f10ae18141c829c644c8308f993504cb1e5310010ad58752d065f6550c43c7152304823e6414f10c755331cc25d63145408f982548c63c6454f2197996210c23e650c440a7592318c23e649513097594300423e6414f20b618131c82d96090830cd545311026e62d5010a7990510c25d6394a1097d8d5090a5e6094e21c754f418871e544c72097d8d544865f6354b41c754e4310aba60d4c40abd89535071d54cc621c794d410865c6054c418f990540ca9e6488630a7982400c29d6490531c7951318866d62d5010c714d414423e60d5132c7953310431d4194030a7181418c25c654c520d6cc6500871c53d0610a7590320c31c53901109d185534823e6510120979835350a5e63d52218f590520435551904308fd95410c6d96008630ab988511035a5354021d3149324c71d5150630c755331c431c5310120d354a300429d6408430d64c5500874d524c410c750d5210ece6214430c7152304c3355150430a798c219033451101208f586540caba60d0510a7d91504c63e6590120c7942400c23d650cb418f59741c825d6394a408f99253882ae6214c4097180534425e6590630ced06500863d6494620ae980539029c6050531c754f41d025f6354221e5945410c3365150430b398b50cc6da60d4830a7584400c31d51902308f181540863f6155032b6983528c27765484219718d524435453d45209b18954442ad62d4e408f594329023f6454e108f59251cca9e6314941cb949410431d54cc4319ed95300c26c6254d10c755054cc66e6215010c7d954310f1e5350e408f191528431c5414e10c794c40c823d64d4c10da549100429e6394440c7d4d415025e6314c10e5d45414c69e63146408f197414c23e64d4f10c794d41c425d63d5320c795331c431c544c5308f593504c6ba60d4a409798e534831f5414e10c7150304431f41943319d594210431f5310110a7d91300c2da60cc6108f181540cb5a6014e10ae18141442d860549318f59053c432e5290010d5545318c23e6495132cb548521029f6350941c7d50304423e6414c10c794d41d025c63542419d98653482756194d208f590530863f6454910a758e529039b41940308fd9153c863d650c640c795331c829d64148309
  | 6 => 0x85e28050240140a8000080580996b0060840000500c05800000000109aa0d215a8a06300e04401c028002c80082e14a242130ac8000000940100000a00c0094800e011a28160000092fc880000080187c06a0140080000041817000006024000000000003d0000002080081f1160300b80201e0280101c07207c62c4700706000062082038f30003840540200755c06c02bfd0000881d809000108d380603a15c0a000004000598030040300300087a078099c35ee1542282e0060001a802458d1000000002001c580408660004000000000108170020281a8191206640000664c0301802804e5040402d000000028800480f00887400a2b0008048400800000c00801c0c01601a0080b010118278040015be0980021501e0e4058f70460041300b01c084ab819776004738000040000703a0000603780412e6f41341f00e00c05942094238310260040094204f0141640200c022030000000309ac2180f0000101200f01400cb800004a02d25000512010099301300083187b0060c0000000020a866009074010029350020100200f46601000001054000940460160a00000239800c018000040001700188aeac0388404e7fc010690f8054dc02f000000000050045e80782301e0cc34830004030189f01f029c0681f0e00102500a00a0543508606c0080000d0001041c82902200c070014d01e0008650042a00581b002004000325567641e00434c03000000002370048024bc058003af114970050050065e8960145860040281000a02036ae00160000e80e1440081c8260000840003605400800811018078338001300ac2101300003c17008000014000000040a0018330000940604c0a408000844000de8010020000040004b000cfc1501d0040d40308842c1bf5753d4520b6d81524c65e6590d32a7592314c65d6394420c754c400423c6454332a7590318c31e54cc631c754f4190757514c5309e19520443375190120e6d81410c31e53903208f99251086ae62d4e40b6982420c3976150731c754c4310a3d6155010a71894310e5f65cc740b3d89504c71f5390110cb95252042756195120a7d854310f1c5450d328fd954210b1d6315132c755331c825d63944428f195325065d6194f20b6983314427a60150218f197414823d6414532e5505310865e6514d20e550531c426d6594810a758c421023d6494d2097597310425f6154f20a7181311031f54d4e10a798c42d063e60151108f994
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x608ad204000000008e06005010004400c3748800008000027000116300800400b0f00002800418286400020a0a0000b0230290000080000000130244380a6001130c00000e22a2302821861853181414430c2a0c098a21261c16494430c22a2302622069161100300430cb28801802145dc54354443838ecaa264195157195131cc318a88c0988818354d6214f41e08a4a0a6288615535844004306b1aa429683835516215331a18e4a98a6a0e0c639494290306b22a419663431d15214931c2aa6b08a62050e72d52548c390a0a42a80438614c6050610c1ac6a908420514755053144306b1aa421683c4547604c440e20a2200609069151181410c306aa2c42a06185d4d6110210c18c9292651862552584521021ab88ca99081c45476050430930e0b1ca22061554584300424c382c710881431cd521494192ae3318a4a0d4870548524c70a32a8298a21461c15415131a30e0aa08698d9070505314424ab8cc829263455c45450c30c90a4302628860d6354852102873a6a529461439cb5394e40a1ce7a94a5205157194d41c830d298c0a0e41a81844048020c1ac8a90a598e4552584520c384a9080180218a1486050510a30e0a08a098e0c631494250749288c0a0861269c36454830c1aa6b10a6205157115143ccb0aa88c098881a4504604c510c2aa23028218691511813110294382a429283465d4400c010a34e1aa0871961561544400c30ca88c0a0861645c4400c010a18e4aa08698d187054c535061c382ca19283431c95415131c32a2302622060c64149324c788a0a62a8043855915188430c8aa4b0860084e276c85208430ab1aa310881855516115030ca2a2302622049a70d8d521028ab8ca6a0e81c4544604c440c22a2302821849870592210c30d2a0c098e4186150604c610a1ce5aa0871861754584308428c3828728087895496110010c1ac8a90a4185157195131c8286b90a8a1861d04c52154021ca2a2302821850d7215143cc62c382ca212638c54460504308aae232a8418692511813110306b22a419061b01843048020
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x30000800001d00521c1414c510e0152584400c010c11655c4400c010a108058d5188440c1175584400c010d01525c4400c010e0052504604c510a118194c6050720a1181950604c720a10805915188430
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 6 => 2*((h/30+packedAt s0K6 (768+(h % 30)*6) 6) % 48)
  | 5 => 2*((h/395+packedAt s0K5 (27459+(h % 395)*10) 10) % 1017)
  | 4 => 2*((h/469+packedAt s0K4 (51110+(h % 469)*11) 11) % 1345)
  | 3 => 2*((h/79+packedAt s0K3 (5488+(h % 79)*7) 7) % 112)
  | 2 => 2*((h/17+packedAt s0K2 (600+(h % 17)*4) 4) % 10)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 2 => 0xf07fffe0fffffff81f07fc3ffe1fffff463c7f
  | 3 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x210c08c42890400165098044c022425818d1b1
  | 2 => 0x44109102412221280a422429121494a1422446
  | 3 => 0xa22522481a440652a084ca8265412a0a854a98
  | 4 => 0xcb59c4929076ab9cd3d06223b9980c33e80f60
  | 5 => 0xc61871ce38733e71ce77330311030c3f7b000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_38003
namespace PEqualNP.Outside.L_meta_38003
open PEqualNP.Outside.L_meta_38003.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x80c18023000411008000000bf41df31dd32bd43de43dc30bf42dd319d43be40bc40de30bf43bd41dd43df32bd42
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x4000080000000014600080001c000400004d54440aaa88611f5250e3aa898c7550308ea9e851d54cc66aa3a153548308eaa4872d521023aa62055547328ea9e831f548c29aa598c71414396a96831d54cca3aa89947d4543
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x10200000835885050e156114143855875250e0d62d4543
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
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/19+packedAt s1K4 (272+(h % 19)*5) 5) % 17)
  | 3 => 2*((h/28+packedAt s1K3 (567+(h % 28)*5) 5) % 21)
  | 2 => 2*((h/15+packedAt s1K2 (152+(h % 15)*2) 2) % 4)
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
end PEqualNP.Outside.L_meta_38003
namespace PEqualNP.Outside.L_meta_38003
open PEqualNP.Outside.L_meta_38003.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x400800051d534000310400005270100000000000a18000000a0001df000100000200fe31fc31ff21fe21ff41fd21fc40fd10fe42ff20ff10ff43fd40fe41fd43fe10fc42f510f710fc43fe43fc21ff32fe32fd32ff42ff30fc10fd42fd30fd20fd31fe30fc20fe20fc41ff40fc32fe40fd41ff31fc30
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2837d54442f8a810774c831be29a437c53882f8a2907b94840bfaa2657f5150b7a85a07d90310ef21a657d54c87baa790dd14532ef29841f640443ea84885fd4143fa29e217c54882fca9987d50b10bfaa641ed42c837e81205f94a41bea9e81f431c42faa6105f54f41bea86437c544cbeaa6887b54b31be292817e5090fe862885f94a10bea9e21ed32087bc64995f94831e699065bd43d0baea6885f14d40fb18e217d54903ee42887750d32fb90e21f441cc7e8a5885f94840bea8e81dd434c2faa920df94c42bf286837f54882eaa2105f54f21ef984617d52902faa598fd14542bea80437651102daa421df94a30bf2a6417e50842fca221fb4c920bf29a437c51502f8a9995f947439faa221bd4350be842885f54342df208817c53c83de65195fd5321bf28c83f421c427aa998f714d10f6994437e5190feea2a15fd4b10fa906217f514c2faa121df95021faa8c417f54443ea61887d48110fc980617f524c7bc62185f54332ef29881df328c7b862185f94230b7296637f53486fea710dfd5032bea9c837d538c2bca6105f14132bea9c857d54cc6fca6197b90920fd10041f621443be6418fd88710bfa9283f654443b863184f55030faa8c61de43cc2fea8905f55132bf29e217d51882fca2197b90a21f721043bf4350bec82885f94a409eaa643f7314c7be86a1fdd0541bf29661f641c42faa4186f95020be2a4217d51c83f220085f15310bea9885be4350efea4a1fdd0731bf298837c53506faa9996f50441b6a9663f442443e885887dc4210bea98817c54cc6dca4205f94732bf28c81bc54442fca890f794c42bea8c657f53c87e88210df54e31ef18a637c548c2faa1a0fb90842baa8c81dd310c6faa1197d4c110bba8a65d453442faa5107e8c030f6a14657d520c6eea2a15f54e10bf28c63bc41903dc64905f95220be2a0657e52c43f420085fd4532afa9a21ec21882faa5a1fbc8220bea94217d54086fca421f750f30dea1c83f532442fca0205f94e10fb98c63f731c86fea4085f94b41fa99621f552c437e8520df54b30bfa9a85fb40503ba60185f54442beaa485ef4250afaa610fd0cb10dea1083bf41907da65906f90140f721265bd42502faa6885f94830be2a063bf4210afca420df55010bfa8a87ee20483da64197e50040fba82217c53c42fca218df15030baa8c41ee52d077aa8105f94821bf2a4637e500caf8a5887b88620bea8c61ed20083ec84885f55210bfaa0217d540c6eca3207d90b10ef99261ee42c83ee40885fd4a10fb90621f753442fca1995f14e10b6a90617c530827ca990fb8c821fba8a87f7410c7baa6217d50441af29881f741c86f8a9905f95131f7194437d53042faa3217d84110fa192217e54887ee6210fdc8521ef218877e51886fca018dfd4540bf29821b454443be8721df55330
  | 1 => 0x4514cbea86885fd5330beaa463f552442f8a098df94410bfaa6217d54c82fea810f794f41bea9e853c54443bc87997d08110f229221f420c43ea87886f50a41be2a0437f5050aeca3107bc8020bf28083bf42d02faa0197d14543beaa041bf43d02fca521dfd4d109f2a663ee320cafaa020df94842f7a1485f753c42fea4987d94630fba0e217c548c6faa898dfd4c21fa21a217e51883ee82887d94640be282857f51483ea43885f54432bf298437f53842faa110fdd0d10fa90a21f443c437aa990f7cca32bfa92817651042f8a2985f94231bf29a417c50507baa6205f94010beaa261bf4390efaa7105f54841bfaa2617c52506bca7a0fd4c431bf294657f50487ec8220fec4110faa0621be54c877ea8885f54730bf298877e50082f8a090fd54440beaa0617e500c3eaa8887bc8621ef18c61be41902fca618fd94430eea1e65e752442faa2185f54b41bea9463fb304c2faa018d754c20be2a2217c53042faa8905f94742baa8c217d53486fea8185fd52219f2a0657e530c37a84217b54b41be2a2635e5310afca2105f55230bf28687dd324c3eca2105754f41fd884217d52042f8a4885f94220dea18877e53882fca7a17d50710be29a217f53c83f240105b54840bea88817d5110fec6218f790e31aea9e437e52442fca68877cc431ef21863f5404437a80206fd0f42deaa0617e50902fea8107d0c721be29a417c5150ef8a9985f15321bfa8263f553c42fca518df95040fb880217d51ccbe882885fd5232bf29e817e53c86e8a2a16f90942bea86877f54486fca3185f95210bea8087f350443bc60985f94b43dbaa221f541442f8a790fd10710fba96217e50887bca790fb50920beaa621df318c6eaa2186f10440bfa82657e520cafea6087dd5110bea9e417e50907ea20085fd5230f7992656d52d077e84a07b50a21f6a1043bf4310feca2205f14143bfa9221f430442fca8907750e31fb992217d54883e861886b50842fb996217e544cafca3217d0c421eea18637d51d0abaa6205b14910bea88417d52443ba64195f55243bf2a0857c5250ef8a2a15f94442f790843f7218877a86a05754c42bf284657c5350afca7907b54843fd984617651082fca721fd88421dfa14857d53107e8a9887b50842bfa9e217c514cbf641105f14810be298437e541077a8620dd14543beaa243df53443eca5887d8c510bf280877f53083eca7885f54a21beaa0657e51cc3eea2996f55331dfa1a817e5090afca720f74cb30bf2a0877e5390aeca3185f15010bea86637e51102faa421fd4c710bfaa421f551082faa1217d4c510f7290877d53902fca598df95031f7296637e53d06fca9885f94e21dfa08837f54ccafca3a07754f41dfa1c83bf43107bc86987d54640f6a12657d52907eaa2185fd5031bf2a665f741906dea4885f94e40bfa8
  | 2 => 0x67802010220180202b200e008050aa4b005010a04b0020001a00042008246503126224038320080011004022d4000069f800000020d8080d8100b80a048181700801b300682e0000a0004a428140403e0e0dc28858f58085582a068283080c018108f8a80903a07008088008e8000001e3003010812048721281a018280900000a7c198c40381a013b0380181886a35830008660304a0783a0b0000780401012c08100f812021121e006410bc0081201000001160100201814218000289e2f2720215620896030f2018160008a1f8ba00040b88ac02018c98001488000078030041681c08014048602f8060e822aa000f406802806000020a0000a006049420380c009d26a8480301c200002204a0fbe00401235800002540a0000001e018283d8160505206810d281003006038520100404086005fd4d40be29421be540cafaa5a04f95020bf280857e54c86fea7104f95030bf296817c53886fea918df15121fb982217d508c6dca5a0fb54830eea18877d528c3ec61887d8c110b729087ec21082fca2187b88420bf2a2217e51086fca1a16750c43bf2a26176510c37ca998df94c20baa8881f730c437e8420df14930f7290617e540c3e8a8885b94830fa29a217f53483eea9885f95331fba0843ec52442faa321df54a43bf28883ee32c827aa8195f54042fa29221f653443ea4210df15221ef98061f440c43dc4290df94a42df20a8375518c2faa4205dd4543f6908437e52043ec86885f54610bfaa663bf40102faa710df95020fa20221f740c43ec87885f94321ae29a217e520837ca8185f95010af29e437e51c83be64197b54840fd90241f654c43ee80887dd0b10bea8e877c54483ec65887d88110beaa465f620c42f8a498df15232bea9c65f632442faa3206f50f40fd20081f441c86fca010df54241bf2a4657d53482fca8197d55310bf29881f731c42faa5884f55020fb98a21dd328c7e88218df15130fb28c41fb40902fca9185fd5131bf28c65df32cc3dea4887dd0f10bf28663f752442faa910dfd4d41deaa065f742443baa6107b90a32fb29221f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x54210a7661940429718d51902b5640cb10cdd8554cc7576154c42e9d5052442ac6250d42e5d854310eb564c87109718d518834c524c930d5d4c314426d6215130b558c40442756115030d5950534433461550329bd89534423e6414c209d1855310a3d6414a10cd15253443c5320c4218f596540c2766194232b5994534426e6215331b598f21c42f160d4f10d5d8d518826e62952319758c525027461551308fd954210a7761553209d98752042d56394b108f59253c42796014c21d9949510c2b6640c310ab5924210b8d43948439d9875488334540c5109dd9543c427661d533297d8d54482f16095110a758f419063f64549108f59252442756194042cd15252443655254430bc582534423f65500409dd9542c425d6314a10a758f411063e6414e20ad992544423c6454910c7552310c2f36054d10c7151434ca7465505109dd85534867561d5020cdd91518c2766115030f414f50442f16014b10d5544318c31d54cc832c7551300c277654c431cb949429063d6414e10d994841cc72d5494b319dd85544c27461551329d984520434d520c4308f99053c82e76254d10d514f214426c62551109d58650d0ab764549109b19542482746154f40cbd5352443a5421091097d8d51883a461508429b588540429d64cc431d354e4210a7461553209e980540c6756114e20d394e52102d76150c31ad590304431d54cc030cdd85540ca7561d4c209d59431086b66494f109d18554cc32d52d0040ad59252c427661141438f191518c32f43548439798c540ca746154f209d584504cb1e5450e319d984530426d6214e10ad592524427661141329758e520872c5250940f1185320cad46150d329b98a524431e5454f219bd89544c2746154d208f992534875453d4110f1d85320cb5463546409dd855210f2d54480209b988530825e6314a10ad19152443545314910cd153314423d6414c109b588535027b6055132d9908514ca3e6414132b558c20c436551884209b988540cae562d07109b98854cc23d6414f21d994c524426c654c920d9508514ca766510110b9588404434e5394b41d594f41c86cf654c832c754d40102746550f10e9d53524426e62152309758c548423e65151109d18552cc3565394420d554c31c8674654cb108f592530c67665cc5109d984540823e6494b109758c54482d663953109dd85544c764520c510cd95251082d66310910b318d424cb675208510b998a52442746548510d3549300c36562d4543cd993514ca6d62d5030b9189544426e6215020b9988304427561942429e580540875553944408f59253442756194032b9d85320872d54c80208f593514ca5d63951109b988538423f65504419d586544ca6e62150109798c54082e5620c110bc980434433554944209dd8554cc32e5450a218f590530831c5350d40
  | 1 => 0x3676154b41d558753442d663c85109d984538831d53d08428f59252c423d64d4c20c7d5353443c453d49108f592528c66f62546309d984548826e62141438fd9153483564314532ab593210865e6394d10d9189519036552544409d987540c2b46454d109d984540425e6394b109bd8954442766194032cd552510c31c5450f32f1d4c524436752d41108f59052042f160153109d5805150a756510431b598e544434d5394840b358b318c6756194232cb550210836665149109dd95434432c5450920d998b5150f2d5494830cd15021442756194343b598f41c87a45414910c755253c879754d4d10b358b310c74e5354b41b958843c425d6395221b998b31c42d463549108f59253486b6640c110cb551520c25d6594c20d994a510c3645288510d598f5150a7561d5332dc99750442776154c42bc5825244372514401097d8d524425e6395310c915052442d663949109d195324431d4394443d514e52442776154d209d987530423f6454620cb5095010b576154f218fd954310e5c6355110d354d52d06d66394d10c715143cc27a6014c219dd8552cc3a542104219798c54482b664c8710bc58042442e762551109758c52042776155132f1d4f524434c534c8219b98a544c66d6294d21c714d4350ab6640cb10d390d5210ee562d0510c354d4210a6e62151309bd95210874f544c8329dd8553d026e629511097d954310e5c6550d328f590530874f53d4910d9949511025d6394910b598f41c427561141439758c5050ad563081109d987540827561141429e98054086d76354910abd954210b1e5454c20b958a54c42b664cc7219ed95200833564d45329d9865090a3e6414d209d185540ca6f654c832cb54d4210b2c54d49109d58454082776154f20ae580411026e62d4543b998a54c431d5454c20cbd50524432d43548439d5835150e6d62d5331d954a510c27560145439e580540c6756014532bc58053c42b761508419758f540832f6550842cd191518c27661940439d587548c36452105109758e54c433554544309d195424431d540c4308f590504ca6d6215230b518d544431d53d0040ad59020c42766194243d9150524423e6414810b358f21886776155120c350d5210e5e6514d10ad99331c42f1600c910d518d51883954310f10cdd50414425e63d4542b558c424436561149109d98650d0a756114c2097d95310c74d5308420d594d5110276650c110bc58354c432e5454b31b558e524434e53548409d5865010e7661d5010cd54441902e662951109b58854cc66d6215030b958b314434d5350842b558f41c434d4354843e915352442d663083109b98a53c42746550d109dd85540ca3e6495110ad99020c434f654c832cd99454442d7614c831d994b41cc7c5320cb10cd55041cc754538c5109d98650ccb354314542e9d8
  | 2 => 0x5314910c754c411027560d4542cb951520c2e662cc5109d587540c25d6315321b9588434423e64949109798c54043a54210b10d514c414434d53c80208f993530823f6454d109758c54c831f5414d10d3551320ca766590110d914b504426e6294d109b58a54c4336540c7219d584548c27661951329b98a54c43946150c43bc980424423d6595020d51855310a5c6550d308f59053482776550441e354d4210a756194332ad9932144277654cb109d984548c3145414d10ad59253c43676254630f114c524431c54d4d10c7151434c2b6640c910d9189518c2e662d07319d987530836551086209d98650d0f545414d109b58b5150e3e6494e219798c520423e6494d10a75924310ee46254d109798c54c83e052d4110ab59321886e46150a32b598f41443555354440b958840c427860551329d586500432d54884209b588530425e63d5321b6580310c27661d52329b98b540c25d63951318f592520876461548439798e52906b6649491097d8d54442d66310b108f99053c86756510421add91534425e6314c20d554d51082746154843b9d85420867665d0510cb151428cb8e544c8328f99054082f160d4b109d996204425e6394821b358e320cb2d548c8328f19151882e66210f10d550c514cb9454d4d108f596540ca6d629511097d8d519039543104319dd95210873654544309798c54882e66294d109758c54087b354d4110cd95331c86e6620c310d994a51102d563d0431f44c030443975414d10c7151430c63d64d4f21cb151424cab664cc5108f993514cae5620c310c795253c863e6414a10d9d89519032d5290440e550c43442d563c8710d558453443645314910d394d32887346454620b998840c42e562cc4219d584548826c6254640d114c524433754d4110d514c214435653944409758e52c433561151109798e54442b564c8510cb5484110276658c1109d9845050b676154843b558f414427560d4532cdd9151882d663081109ed95100426d6295131ad59331c423d6494e21ad990204434c53d49109d98753882b66494b10d354e210823d6414e20d914b41442e562951109758c540832d5454b31d34c9500cad76355110f14c832442e562d0421ad590324431e5494c208f191534426d62153309b988540c26c6255130c7551320cb1d43540438f990538434f53149108f19153482f360551109dd9510042b46150f42b3189434ca3d64149309758e52907e352d4110ad590204432c5450b20cb150524425e63d5020cb15142086d66310310cd152414425e6315021d5d8d519025c6354910e394d4210a7561d52209b189518c2e56294f10add85431078d544c832ad992534425e63949109b58a54486e662d07108f99253c423e64150309718d544831d5494c209d587538826e6214c109b988548425d63d45429d18552d
  | 3 => 0xc2800808004a903c1303c18054080000500002040000241045007010251f80e010111380b070000d00008c220600c1d8151584c01c49000010185f004650f005050bb004020282e0740c00c0100c0d0007501c2706401014223a4011141b0841c002230000c0000200c0012c55000024804100402004020449e08c32114ac0300007c02000001ac000c4040101101ced0495a000000040002c080040f0046007402084030c401004036f0007505400420030030200907c052ac030680f07c240cc0116c12000000b00b00412000a3000160240d14c0308001018230000e058050201d00400050140006204001470060800100164034080056f14c1a1ac2e1080802005012b200035020030240b01003004210041e46402020010040003c1c2048a0184d08c3101c09008000682fb6804124030080407804000260d4740601c0240032c009b588540c6776154b40cd58754442776550910cdd0c5150ae66210d10b558f214426e6294e41ab58b419066f6548020c7150534434d52cc030d354a310c27b65500409d587548cad46150f32cb95252cc66d6294e41ab58b411069d64cc631cd55041c876561d49109b5885050ed66394b109b59642086f16010d10ad9945444274654c5109b98b54cc6e562cc7108fd91518c33454c85109798c540c26e62150319b58a548c65d6315220d9d8552cc6d56310b10ad593314426d62152109d5865090f6452cc5108f990524c34e524ca31c755153c867661d5230c794d43906d56395310b558c40c42b46150d429b99452443576154f41d354d200835453d0510b598f410865e63149409b58a53c43d353d41109d19542c425d63951219bd954210b4c534c9209798e548867761551218f992530c65d63150109b58a53443565354420b998a53c433654544209798c548425f654c030b358f21086b56494d10e515053443b054d41108f99053042e662101108f59053c834d5354840cd153504431f6550c43d5d4f504426d658c821cb549401025e6314142c3551320ca5e6315321b9185424cb8d43509329dd95324427461551208f992528c6e662d04318f99053086766508110cdd8554c867b654c0309d997214426f6254640ec50040442766114c208f99353c872d544c832c754d4210ad66310110bc98032443355454420d594c41c8755518c430e350d5210fe12008110d954a51102e662d0510cb50a5110b5563d4542bcd8152442b664cc421d314d32c823e6494821d5994534425e6395121cd952510c2e665149108f990540cae96008420c750d5210f3454149109758f54c869f6550c43b558e544436654149109b195424cb345414d10b958a534425d6590c31d34ca510cb1d53904409b988535032e5494830d354e52d0735519044097d95320cab5640c3109e596100435553944209b189534434c
  | 4 => 0x43e0bc0a6740405c2800031018001680d00c08018000e00a0267f1440503015090060001a020020
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x16005864e040b1000010000e4000180038000140800a0288706282820010180780c0003000001080c3030438cea16250040442a339ca8292218a5516008420e0ee2aa2641950d739494290686ba4a499463c115053d4910d4284b0084886245498a53443822a6a629221435d2534ca21c88c6312a320705431855210f82a1ec2a90879198c52d0510d0a86b1087886445398b4144360992c019221611c54350932c48c8312a3187045414c524438238a86a9087435c85450d30e0ee2a1aa421d0d72951438c760b1a4010221b0589300c110e0aa630a84214547558c4244286b98a8a1043c11c55350842d0ac89906588649535802108383b8aa6a1085435d6544c832d0ac6a10848870553d854210a86b90a8a1863431d54350932a1ae829a6490434755903244286b9ca8a1443435d0534c821a1ae42a287985467295053442933a4a829221435ca5350e41e0aa830a641952475508424430a2a4c790a21435d0534cb20e0a86a10a299691644c03044324a92c018861435cc5450b20c18caa1a849968543588434430b320a729221511c5544c832d0a8630a84995247154d4210b0a320c6a8c41a450d6010d10c2a8630aa421f075414c524430a2a4c7292218599053c8510c4cc829662885467394c5244294b80a8a1043c11c5544c832c52a4b0082205497014d3208686b98a8a12418654d6010440c48a931662886856350842c430caa2c018861499d25314910d0ac899064885147550c434428b3a4a829a21191d56210d10a88ea990648870554d85320ca86b98a4a1281435d0524c930a1ae429a86a051970151430c750b224010221a458d4010110
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x210001b71009078750f6154843a048550d6210d10a048558d421091090787553614c832a0686dc5544c832c0475591320c910c047558d4210910a0686dc55350842c047550d6210d10a0686dc54354843a0485591320c9109078754f6150842
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 741
  | 4 => 794
  | 3 => 91
  | 2 => 12
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
  | 6 => 2*((h/49+packedAt s2K6 (672+(h % 49)*6) 6) % 42)
  | 5 => 2*((h/247+packedAt s2K5 (20007+(h % 247)*10) 10) % 741)
  | 4 => 2*((h/292+packedAt s2K4 (30172+(h % 292)*10) 10) % 794)
  | 3 => 2*((h/51+packedAt s2K3 (4459+(h % 51)*7) 7) % 91)
  | 2 => 2*((h/11+packedAt s2K2 (720+(h % 11)*4) 4) % 12)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc1ffffe0ffffff81fc3fc3fffc3ffffd11f1ff
  | 1 => 0xfe07c3ff03e1f0fe3fc3fc383fc38382eececc
  | 3 => 0xfff803fffc01ffffc003ffc03ffc03ff0f0f0f
  | 4 => 0x3fffffe00fffffc00003ffffc03f00ff0
  | 5 => 0xfffffc00000000ffffffffffc0000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x44100022080000000404404884048888005055
  | 1 => 0x8cb184463942a1161c41c4119c41191866c6cc
  | 3 => 0x1062aa8850d548aac222aa822aa822730b0b0a
  | 4 => 0x39453310a2906acd6aa8220433327023b00da0
  | 5 => 0x2186221cc3198cf1b333332702204043dda000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeaaaa00eeeeeeaaeeaaaa00eeeeeeaaeeaaaa00eeeeeeaaeeaaaa00eeeeeeaaeeaaaa00eeeeeeaaeeaaaa00eeeeeeaaeeaaaa00eeeeeeaaeeaaaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_38003
namespace PEqualNP.Outside.L_meta_38003
open PEqualNP.Outside.L_meta_38003.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x200000004c0061410e000b012641009001106085045fd10fc40fd31fc41fe31f710fd43bf42dd32ff32df32f510ff40fd32fe41fc32bd42fc30fe20ff42fd41fd20fc10fe42ff20fe32fe21fc31fe40fc42fd21ff21ff30fc21fe10fd42ff10fc20ff31fd30fe43fc43ff41ff43fd40fe30
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x3400028580090004085040c000120c001061c0030a001060028216020b300000420514004010000401180000000240a68c001890204000000400f02003120000000000005754f20b729061f350442eaa3204f95331daa16219f424cb5a85195d14532cea188775518c3e2408875cc910b7296633f544c2daa4204f552429eaa043ad42086eca2204f55020d6a12413e54086dea4884f95030ea28a653e54c835ea4a16dd0b10bd280435e530835a84997390932b6a90619d424ca7ca81075d4532e6a1265ad4288678a8885d94640dba8a855e53086b8a6a05d94410f3a92213e540ca78a8985d94630afa9a2176510c2baa7215794c429f2a085ad42c836a84885794f21bba8a65f220442daa598f54cb10da2a2213d54c82b8a6885754c40baa8841cd320873a85995754c20c6a12655f53503aea6885b948409faa2216c52442dca5a0dd54620e6992416d5210fae65886dd0910baa88613d54cc67ca990f514d109eaa0615e5390abaa7a0d754f21aea9885775150aeaa3085754e32f2292219f42ccb9a6510edd5110da28a853e548cabca6195d94420af29e413d54c879ea4995794f419eaa0656d52d06bca620734cb20bca80436e5210eeca310754c910ba28a853d548cabaa610dd54440
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x21005410002200c000102810000e150932442c46150932c355132c8385424cb10d24c9500868d6490932e1185424cb0d5350821e150b514cb2542145329358853503294254021f04c9204438542145328b588544c30d544c821c354d42c83445314910c9150524430d43548439519532443876150932e850920442346550910
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x8390eeca16a29950675d85424cb0232a8499221411d5424c910
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/29+packedAt s3K5 (736+(h % 29)*6) 6) % 46)
  | 4 => 2*((h/81+packedAt s3K4 (3159+(h % 81)*7) 7) % 117)
  | 3 => 2*((h/22+packedAt s3K3 (912+(h % 22)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s3K2 (196+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x83ffff07fffe1f07f0fe1fffc3fff81e89f3f3
  | 1 => 0xfc1e1ff83c3fe1f8ff0fe1c1fc383fe176cd9c
  | 2 => 0xffe01fffc03fffff000ffe01ffc03fff870e1f
  | 4 => 0x1fffffc001fffff00001ffffc001f80fe0
  | 5 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x884001108000200010120244404888440050b1
  | 1 => 0x19442231905402287106208cc41192c432c594
  | 2 => 0x208954420aa91153088954112a822519850a0a
  | 4 => 0x729598852a0d559daaa11021b3270189d80f40
  | 5 => 0x431910e6333199e6cccd993822040611efa000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_38003
namespace PEqualNP.Outside.L_meta_38003
open PEqualNP.Outside.L_meta_38003.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x7400002a80082140080011445a00002000000200081080040340ff41ff30fc40fe20ff40fe10fd30bf42f510fe40ff42fe21fd40fd41fd21fc41fc10fd20fc20fc30f710fd31fe30bd42fe42fc31fc21fd10ff31ff32fd43ff43fd42fc42fe43fe41fc32fd32ff20fe32ff21fc43fe31ff10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x441bf42ccb7ea6a15f14e20bfa98217e51c83be6218f790f30bea90617e518c2f4a0195f95310fa182217e5310afea9197d88110fb986217d53c835a84907d14532bf28c63bf5050be886885fd4d10dea16817c514c2fca898ef54142be28a65fa200837ea8985f94d10dfa1443f930882fca310fdc8110faaa6217f504cbf260187dd4910bfaa2417d510837a84a0fdd5110f690041bd51d0afca9996f14342dea9a857d500cafca421df94342fba1621f452442faa3107750c43dfa14617d51cc2fca821efd0b41dea1a81f732442fca410ef95032beaa441bd54c8278a8985f15121bf280857d54c82eca2207cd41109eaa641bf428cb6e85885f54910bea96837d5210efca010efd0a10bf2a0657d5190efaa7a05f54b10bea98417d544c2fca0205f94742bea88817f534876ea8886f50e41bea94837c5050afaa7217d4c521bf28861f643c43ee828877cc631fb98a213e540cafaa8105f54a21beaa2217e520c67aa9196f90640fa98e21de434c37ca8105f54b31bfa82637d53d06fca990ef508209f2a043f621443eca2205fd4f10dea12617e51d0efaa4086f952329eaa0417e5290bda84215f15221dfa1e85755190eeaa2185f95021bea8483f454443dc64195e54021fb182217e520c3eca3205f54630beaa4877551902faa7885f14141bea8e877e510437a8420df54031dfa1221dd53087e86390ef50040fba8a657c54c43eca2105f94431beaa465b454442fca198df14542be292837e508c77e85a06fd0930ef990657e548c2fca4207d54430fb082217c540c2fea5886fd0e43bf28c817d52cc3ee82a0de54032bfaa0417e50843ba6598fd8c521be28a817e52d0fee6298efd0941bf2a641f520c42fca998dfd4e20fb2a621be54c877887205fd5230bba8a65f4534437e8320fd8c910bea9c217f50506faa7195f54443fba1a217f50486fca220dd94643dfa9285f2204437e8720ef50931bfa92617e50ccbe88298df14d42dfa8e857f540c6fea2985d94620fa20c63ee32c827ca9905f55332dfa10657c50487de85215f14931fa10e213e54cc7e863887e54032bf29e85f6524437aa810fd54b10fa90843df4350efca5a05f15130bea9a217e528cbee80886fd0820bfaa661bd5150afca1a0fdc8521bea9463f651882fca320df15330df21a85f721c43de65195f14e21fb188637e5090b7a8621dfd5321af29841bf42907bc64997d50510be298437d52903e8a9885f55231de28a857c524c2fca2107754c20bfa9281be41103ea81885f94632be2a241ed52102f8a6a05f54a10be29a43fb20483ba64985f94c31bf29c21f75150af8a998df54321bfaa263f542443f280206f50b30baa8841f640c43ec85887d50f10bf284817e500c7ea43886f10440bf280417e508c3e885885f14131beaa2417c54c837ca9905d94630
  | 1 => 0xe53086fca5985f95040de29a85be41507daa4185e94021bea9a437d544c7e842884f55321fda02817c534837a84086f50a41fb99621bf4210afca890f750f30bea8c817e51ccbbe64985f54442bea8465bd424cbf62108774c931bf2a021bd41107eca7885f55132df28e857e5390afca2217d48110dfa00817d53106faa121df15131fb98e217d50d0feea9887e48020dfa1887fb104437a84195f94241bfaa2437d54843da64195f55242bf29461fb20883ba65987d88710de282857c53842fea2a1df95330fc982417d53086f8a918efd09409f2a0417e53083f681207d8c6219eaa485f7318c7eaa321df14b10dfa14817d548c3bc60985f94f20fa18a21f653443eaa3186fd5110fb186217e54082fea0a17dd0710df21c817c54ccb7e8490efd0b10bea8c657e548cafca0197dc8510bfa94217e50883f420087dd4d10dfa8a85f7108437a85107d54432bf28881bd421037a84185fd4d41fb196217d538c2fca8887e8c030bea9e853e54c877aa998df94243fba0c63de4310efca598fbc8220be2a461bc4350b7e8518db94830bea9081be4350f7a87a15f14132fb29621f540442faa3a07d55110bea8685bd428cb7e8420fd90110dea1665f551902fca610dd54432ef99663be50d0bbe60185f54e20dea16417d53886f8a5085794c40fd18441bf42043eaa2107d10910fba1e21f910042faa6085f54430fb21221bf424cbdca4185b94840fb28c877f53483eea0885f95120bf28c85f740c43ea42884f55032bf29887f5524437ca2a17dd0641de2a221b75150bf4a0197b94840deaa065bd42cc77ca7a15f54e31f7a1285ee42c82faa818df55032bfa9a817d54c43f441087d14f10bf29c877e50106fca918df54331ef29881f510042fca8216f14742bfa9c21f120443be65987d50710f790c43af5250bec62885f94c41dea1443bc41902bca610fb509209f2a085bc544c2fca321dfd5032bf29c41f5434437a85a0fb8c920beaa2437e52042baa6105fd4532faa1621bf42102fea4a1df54341fba0a637c53042faa5187d4c431bb288657f524c6f8a2906d50b10bf28c417c525037a85185f95210fd102217e544cb7e85107794c20bf29085f45150afca690dfd52319eaa0437d520c7ee6210cf95232dfa1061f641442f8a6a0fd14b10bf2a441bd43107ea64886f50a10bf28087f420c437887a15f94e41fa192217e544c37e85905fd5320ef984617c548437e87a06f90c40bf28887ee21487ea61887d0c421bf298617f52506faa010fe54021bf29e837f540c2faa020dfd5331bfaa021f441442faa118ddd4542bfaa043f541106faa9207d54d10bea9083ed32c837c80a05754c40df2a0437551842faa021f7d0e43df212857c54c86fca420efd0d42dea1e817f54ccbde6499774c832fa202217e53102f8a2a1ef50910bea9
  | 2 => 0x5441001b31400002cf3051b6088000000007c08220143c0170040006c0600c01000371686e1b8010900b01c151481d0182d02c00018141240020de20700200086030052440f0544a00cae158000001714c14014060281010c0d058b307c060040006011014000ac00458010040e09c410008c000030000100c060009b0200704407000060000202cb203041014647440505400014030400e028a31801e024080261a0401702c160e40f0002f0111703c17828022a0340084a00043025dc08c3f030114501300c0022c0b03c090040b148630a426044027dc1405c0000400014007618c0200291c03018000f40503000070005d0523e01d3bc03000b1000020000a03c05000270600c0752c000111200e000440000a0340201c0e018040c80a1300302c320000100c0a3681206822004c5df21e857c53c836a84885f94d20bfa9e437e52d06f8a790df94a40bfa9c437e528c6fca4107e8c120fba9e217c548cafea2907b50b20bfa92217e540c2faa3995f54f21bea8865bf50d0af8a8107d4c110d6a16417d539077ca998df14910fd98461f9208437a84905d14532fa10221b45150bec83885f55221bf29865f4410877aa990fdd4b10bfa98417551882f8a8995f54a43fb18e21bd50d0afea8887d95110f721241ef20083e88390efd0d40fd200817d5090afca5084f95030fa98c43bd42c86fca0187750d30bfaa443bd420c7ee8390dfd5210de21881bd420877a85885fd53109faa221ef21087ba6218fd54620fb108437d5310afaa9985b54840ef99465fa50086eaa2205f94343fb88021bf42cc6fea4085f94f10df2a061f532c437aa9195f94a439e2a2217c54882fca7205fd4540dfa12637d50ccafca210df15031dfa04817f544cafaa3a17d54440bf29e4376510c37a85205d54630dfa16617c5050fbaa6205f15110bfa9a85f432c42fca520df95221bf2a0637d54086fca110df15021be292875d53086fca820df54042fba12217f53c82fca4195fd5220beaa643f441c42faa6905f54b43bea96817e510cb7e8220db54830beaa021bd53d0beca2185d94410dea1281df324c6faa110fd10310f690843b7424437e85215d14542dfa16437d51c83eaa7886f55030fa98a21bd4210b7a8490fd90d10dfa10437e50c86f8a8195f54e40bf28021bd54083f240885fd4c21dfa12417d540c3e861887d94432fb28c61f620c42faa6206f94142df29a857f544c2f8a6886fd4f42f699241f731c867aa8185f94740bf296213d54cc7ba60185f14c20f7102417e51cc3e887886f14f42bf29e817d54cc6fca710ef50d42fb982217d5190a7ea8985f94c10bfa8287de314c6fca1196f50a31fb90c43ee4210af8a7887dd0421be2a0217c520437e8620dfd4542fb906217d51842fca4885f55241fb208837651082eca3206fd0831fd98261d
  | 3 => 0x6a05809054063fc0b014010080a004106dc4107035004060201a0999705c000ac09001ec6
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x352c42746550910b958830442766114e20cd54c5150a766590d108f59253c423d64d4532cd50a511026e6214c20d554d511023e6494d10ea50920442b5640c310cdd4b5150a7765484218fd91524432e54508429dd85534833742944308fd89540c27960149319d984520432e6494830ecd0a204432c5250931cd151534437251540329d987544c27661943439d98453483715188020c754f42082b664cc421b9d8953442b664951109d185548caad60d4942c75525308734544c510ab59242482b6640c110d5cc9510cab761541428f99053042b96010440ad191524426e6214c109d58754cc3b054481109dd85544ca796015021cd509510c2ad648c920ea181424837260946209b588540c27661d4c10cd150524429f6354142abd895350b1d5390c40cdd0951883b05488110dc88550087b342d4110d594d51102b564085108f191534827665901109b98b540c3354294620ce50a500873743145429d5865010e7960d4c21dc546500ca3f62553319d19531486f16094d108f992534863f6550830cdd4c5150a3d6414e209d99430443665254440bc586304826f6550842cd987544c3376550b108f992524431d53d08218f59742cc6d663d53109d18552cc3374294410c794d42082776154f20cd19542c427a6014c20cb55120082e5620c310cd509518832d5210440ad997424425e63d50209d58653d032c6550920d554e51082b66114142cb54b42d067661152208f59252c426f65484219d98754883715154032ab58853d0a746155132cbd49424c678654c120d954a510c2e6620c1108fd9150887b054d4110add91524433554544328f99353087a76150920ad99030c423e6494820dc98550086766194342c7552530832e6295320ea50930482b66494d108f590528427561150209758c540433b4254021cdd0b514cab661d4f429d584540c27561d50208f994544c32d52500409b588540c63e6414810cb592520c33454d41108f990538433554107219d59643c42746154843cdd9151883354314542c7553300c3a542481109d994404431d53d0040d64c9500ca76658c110d6cc9500ca796584010d554d510827561d5220ad59021c431d5310f428f590524c35953880208f99052c431e53d0820e9d4b5150b345494910cd551510c23e6494b10c7551530875953480209d987540c23e6550930e9d89424427960d5231bc58053c427661d4c208fd91534833654944308f99252042b564c87109798c520427665081109d997314431d544c030c754c431023e64948309d99432c427665d05108f191538832e6454830cd15231443546154c21ad992524427661d50319d58754ccb655294440ce552500ca9c63541429b588548c23d64948218f596540cab661943429d1855348355530c421bc58630882e6620c3109798c54086d4614cb31
  | 1 => 0x42f26548110add85421063e6414a10ad995424427a6015031cdd91518c32d54c8020cb949429025c6355120cdd0a518c2b66515110d694e50087b35448110c754d421026e6214e108f992528c2b465d09108f59253442b665145428f597420867661d5020cdd85548cab66414b109bd95320cb3542d4532dc99620443b14288110d654d500867561141329758f540873b42940328fd9153882b664d4f10b9588404427960d5032cd50a510cb3654544329b58b540c2766194332bc58052c42756194032ad5864350a7a60d5231dc946500cb7161540328f59353c431d5350040c794d421031d53508208f58a54cc6b564081108f99252cc73454c85109b58a544c7b35488110ad5865350ba54248421c754c53d0a7a60d50329798c5050b3a5454021e950b204427461551209d58650d0a3d6414b10bc58054c427b6055132e9185424832e52508409d582510cbb142d4110b558c52c433554d04218fd9542cc7a76150b20dccc5500867661d5032da8c9500ca7860551329d99721442f160109108f59053086776550910c7551530832d52904409b18953442776154b308f595420c23f6255020d394d521025e63d5310cd552510ca6c654c9208f597420c3b354d4110c754d42086b66114342e9d485150b3542944109d984548c3376155320ad58854442b56494d108f59053082b664cc7109b58853842746550510cdd08514ca7561d4e208f990524c6d66308310ad59232c431e5494c208fd9542086b664cc6318f597420cb366515110d554e51102e56210310cb549420423f65d0b31d554e21087ab60509208f59654086756510421ce952500865d63152208f592528c23d6414931ad590304433754d41109798c54882b664cc7219d587540c33742546309b988540c63e6415030ad99253c427761551219bd8953442346550910ad98643d0b2d5250a10ced09500ca756114c209d594310866e6215010ad5805150a7561942329d984540cb3542944308f191524433b42940219758c54843374254640d594e51103e23248110c754f42102b56408310cdd09511026e62152109d98754ccba542c83108f19151882d86050d30d994a511033554944308f9925444275650c910da54a300c2766114f20cb54b42106f2608c9109d58454883355190440bc98043443c9324c1209798c52842756114143ad59353c427661d50109798c52c42746548510d554d21086ad6294d42ad59052c426d6214c10ad58753d0b5a5354021dc54520082d563d5310cbd49425065f6550c438f58a540c32e5250a30b9189534433942540218f992520c7553254432ad58643d0a74654c910ad99042442f160d5310ecd09204431e53d0840f44c0304427a60150328f990524c25e63951218f997424431e53d08219d9865010b2d52508319d98453086766114132bc58
  | 2 => 0x52d08309d19532c427560d45329ed9510042b6648c910c79515308277654cb10cd19542442746154f208f592528435553cc421cd993514ca746154b40ce951500ca756014532cd509510ca5d6395121d394e52102b564c83109b58854042d56308510cb94942842d66310310ad990204426e6215030ad986431033554944208f58b544434d5394840cb591520c2b4644c110bcd8154442b66190e408fd9153442f36050d109dd9532442d56308310cb991521023c65509308f589540823e6494e21cb54b42d02b56114142bc58252442b66408510b598c21c42786548110b598c20442b6648cb108f19150ccab76154d42bc986204429d63143429e580540cbe242481109d597310863e64d4f108f99353c82d663d05318f195424423f65d0830ad58650d0ab46154d42ad593314431d6315130cbd9542c827661940439d98753882d663149109798c54082ad62d4f429dd9542c4274654c51097d8d544823d64d4f20a798c50d0a756194243cb54b401032e5250820cd191518832d5494830c7952530877161940329758c52c42e562104219e98052043345490510ad990324427561d5230d514d314432e54548309e98054086e662103108f590538427661d4810cd58454442756194343d554c53442766590f10cd9945150b3542145328f99542442b664c8510add91534427a6014c218f58b544c2b465509109d987548c2756114e208f992530c72c43548409d19542c42756114930ad99052442b4644c310cdd485150b555314f10ce509500ca3d64148109d58653d0b345114142ad99020c42f06050d10cdd0a519027661d5330a798f51d0a3e6494b309b58854842d563087109d596434436932540329d9845050a6c65509209dd8554482766194242cd509518c23e6515110f8149204427561d5032ad58b544423e6414c21d354d52102f065481109b5885050e5e63150108f59654082f16090910cd54441902766114c20ad9864350a5f654c0309758c540837121540219d5865090a9d6314142ea50b20482b66408710ad99321c433542546409dd9510043374294432ad59331c425e63d5021ad592424427b65500409d5835150b1e5350821cdd09510825d63141429d5845050ab66194142ab59232c82b46150b41cdd0a510827761553209d98653d0a7661942328fd91518c2b5648c9109e58053c872d5250a30cd58754442f265881109ed95300c23d6590c40ad99032c423d6595030c754c41102f26008510cd185540867560946439e983540865d63d5310d354d20082b664cc5108f19150886b664cc531f8d8920442776155232f84c9204427661150109d584534823f6550c438f992528c7b142481108f592538872e54948308f58854442776154b409bd9520083374254432ea50a304827760546439dd95411067665881109798c548
  | 3 => 0x4418f997435023d64d4c20ad993204425e63149108fd9542082f2600c910cb549420c33742946208f59053c86b86054d429d98653d02f16288110cdd09510c3345194142da549300c2766115020d994a510c3e35248110ad1855050a5f654c832ea509208433564d45329d58650043665254430ad59252c435553d04219d586544cb4d524c030cd952510ca3d6494a31e9d8942c433765509108f99353c86f16010d10dc985500ca3d64948308f59053483395454021cd150214427461553208f592520825d6314810cb95142c823e6414f208f990504ca5e6314c21d554c41086756115032bc980204433954940219d9845050f7031540219d986500cb3743946439758c524433654544308f59053042f1600c9108fd954210a5c6550d30e8509204425d6314a108f19153442766115030cd50951102b564c8510c754c5350a7561d4c20aed815350ab5640c910ad58653d0a9d63d47429759653082b560d4542dc986500cab461508409d59432c433454d4d109b98854082d66314b109798c540c32e4354840cb54b42103725144010add91304437265d4110ad99320c433761553219b9885050ed463549108f588544c2b56494910d95495110356535442097d8d524432d5250a408fd9540102b66190d439dd81510ca3d64948108f197424c31e5350e418f592520c71c5490d309d984524c23e64948329d997414c63d65d0820cb949420423d6494832cd185548ca3e6414d20d354f20082b66194d429759653086776154843abd9542c826e62951318f990540823d6494c319d58453c82f162d4110cd55151083354294640bc98032c423f6550832cd50a518c27561943329b988548c3374294440b558c404427960d5021d3149324c63d64d4f21d654e500863e64d4c208f992544c2b661945429d994324431d5390440ad19153443734154021ad59032c423e64150328f191518c23d6494b31ad98653d0a3e65d0930bc58232442b564c8110bcd8152442796015031bcd81534423d6494d21cd18554c825d63150219d986544cab66494b10cd50951082d66308510bc58032c42766114c10b558c52442756115230ad590524423c64540318f99053c867560145429d587544c23f6454620e3509320cab7644c310cb949420c3b140101108f197424423e64150219dd85534871e5454c21cb551520c33464546308f9925284277654c431c714d4350ad56308110b598c404423e6414c20ce952500cb354294420f850920443a46150b209d996314875653944209e98053c87704154021cb949420c6f16095110cb549429063e64149108f99053882b56194142cdd50414425d63d50209e983530863d64d4c21d554c31c433561d5130cb94b420c33942940328f99252086e662101109798c53082d763549109d5865010a3e6494f108f59053c832d
  | 4 => 0xc510380902428000001080016c827c00f0c0470580d04c0004cb200401248000200a1080a05989000311240617c3601f3603c0024067000052186b00401024160422d0604e5784c05c000840060000124020000d01c0309c5107cbdb480100018024140700c07818070270c4020000028c61002160400000c3801479085f5020280000a00002010038daf1000130440a08c100552e4595b028010319d0002f0000500004080000641404428008120e400004003a8060000018c0137c02000010041b07001000510503b1c024034010001179c2a0100001e9f000001040d0141404c2b0140000a50044349106d020040b80b005de2cc020dc2f7540000033080090000f0040401005148000496f00001004000001601c3a0000395c0700037008010042b0440100c1e00ce30080401c010707b0843100c0007e25000290a01c050022bcb8100000089a04c130380517400050360dc150080d00000000071100316c1a0301900000000010a4ad00c07140055a8ad0000005c1a03013220f23007e0180a094c70000003c200d40103d44008019381303824b558c40c42f160d4f108fd9150ccb3654544208f59542cc6766194243d9549510c23d64949108f993514ca796014c219718d52443395454032ad59253c429e6314142bc980424423d6494b30cd952510823d6414910ad18542902f260c8510ad58450d0a7a6014931cbd95424823f6454031cbd49425027b6548020e950920c425f654c431d354b300c2f260909108f590504ca3f6550
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x100816000a804418f89020000014000001000e861a2c002063c1802804000a88e4a98a6886916350040442d13aa84902218554e6190c40b42e42a24088589731814248298b80a228285685d2424811086ceb32a84886166454f3108748b2260182218654d6010440a50eaa12408856172105500870ab18a228285495c85414910c2aa630a84204c972181434c2b03aa84902211c5c06154843b42e030a849043476509518c382a1264a8865c154d4248421a60eaa144088434755923244350a12c3182412c5c06150840b82e6292408842d72191500c712328c2a1241525c0524c931c8aa6b108210da1741492044252b94c998843a85894010110e428490aa010d187054c5350a9338c86a9081851516308510e1284992a019720541492044360b126018221385c86050d1086eeca16a2996a061181424821abb0a810a21681d54248110a48eaa1240885307054c5150b18328a890221c8dd54248110c28a8b18a488525721502144258b84c321881c81d54248110a40eaa1240885a1748c920443122a0c4a9a21491d542c8110c52a4b00822043675d9130442983aa84902210d1d94254620a52e02928498c347559320442d0b88c0a12414c9d33154021
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x50b2025a00c11535c26190c40c11635c05114142a05821516308510921829d33154021c11535c06150840922859d54248110a05821516314910c20655c85448110d00545cc5248110c20655c06150920921809c64354840c817318460509208a087509618c120a058299153cc421920855d23248110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
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
  | 6 => 2*((h/35+packedAt s4K6 (704+(h % 35)*6) 6) % 44)
  | 5 => 2*((h/273+packedAt s4K5 (22140+(h % 273)*10) 10) % 820)
  | 4 => 2*((h/326+packedAt s4K4 (33972+(h % 326)*10) 10) % 894)
  | 3 => 2*((h/36+packedAt s4K3 (3332+(h % 36)*7) 7) % 68)
  | 2 => 2*((h/12+packedAt s4K2 (900+(h % 12)*4) 4) % 15)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x8ff87fff07c7fe3863c7e3ffe387fe0e09f1f3
  | 1 => 0xf07f878ff8071fc783f8fc707c070ff076c99c
  | 2 => 0x7ff80ffff81ffffc00ff807ff80fff870e1f
  | 3 => 0xff80000fffffe007ffff00007ffff001f80fe0
  | 5 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa10910011088004000412091208122240050b1
  | 1 => 0x2713311231922c0981c86423641264e432c994
  | 2 => 0x4820022442005002240089040920090885020a
  | 3 => 0x206454885040494ca9200085254c041580d40
  | 5 => 0x4c446600e62699277324d24e00608189efa000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafae0fae0feeafeeafae0fae0feeafeeafae0fae0feeafeeafae0fae0feeafeeafae0fae0feeafeeafae0fae0feeafeeafae0fae0feeafeeafae0fae0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_38003
namespace PEqualNP.Outside.L_meta_38003
open PEqualNP.Outside.L_meta_38003.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x4000010010010000000c00060020400000c000000001f00014200000308d0400c000014000704000000002b000ff30fe43fe31fe41fc10bf42fd10fe30fe20fc20ff10fc40fd43ff41fd41fc30fd42ff32fc21fc31ff40fe32fe42fc43fd32fc41fc42fd40fc32bd42fe21f510fe40fd31ff21fd20fe10fd21ff42ff43ff20f710fd30ff31
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe85bf51d0afca1a16f14f42fa102213e540cafea6a17d10510dea12617e5310efaa690db94840bf2a221f754c42fea9195f54f41bf2a081bd5350bba64196f50d40bea8861bf4310ff621086fd0820dea14837e5010a7aa990df15332fb90e217e50883ba86986fd0841bf2a443ef20883ec61885fd4e10fba0e217d53c836ea8885f95042bb288817e53c42f8a5885f55031beaa4617d52906faa610f74c931fa98a437d5290378a0a15f55332be29421f752c42faa598df54840deaa6637d52d06faa6085d54440bfa9a41f632c43e8a88877cc832dea1a857c544c77aa7a17b90920fd18241df324c7da64907b50920bf2a4417d544c3ee84886f50910bf2a6637d53906fca810df95232bea8e41bc43d0aeaa2187d88421bea8e61f75150afea8986f50040baa88417d508ca7ea8885fd5032bf29483f431087eca9887bcc932bfa8263be54cc7ba6218fd8c431bfa9e437c504cafaa190cf55232bf288857f5150afaa7885f55120fba0c63f4434437aa810dfd4941fb29a21f631c43ea4210df54c40dea1065f552443de4210fd90310af298417e51082fca3206fd0d40be2a221be540c37a8418fd10531bf28663be53d0bf440107ec4110be2a041bc544c2fca8195d14542bfa8243bd54082f8a090fbc8020dea1265f920842faa0215f94643bea9c417d50886fea498efd0441fb88421f731c877c84a15794c40ef21a61b542442fca721df94d20bf29a21f720443eaa3185f94021bf29e85f454c43e860885f54910be2a243f731c43eaa2207d4c310bf28e61bd42ccafca3905fd4d21bea8e65bf42c827aa9905f94230fba9e21f45150b7a8498df94f41bf29021f651902f8a2a16fd0830be29821775150aeca2106fd0240faa02213d5490bdca4205f54b43bea9c437e53902f8a710cf95020be2a4437e538877e85a0df14543dea14437e52082faa518ebd4942bd28043f930482faa1215f94a30bfaa041f651103ee6318fd90710f9a8221f9500cafaa7215f94c10bf2a061ed320cbee8320df55021df21c81bd43907ec60887d48310dfa1281dd32cc3be65986f90541bea90617e53087ea8220fdc8510be29a817d50ccb7e8590dfd4e20bfaa0617e520c3ee4290df55020bea8083bf428c3daa4186f14742bca8065f7414437ca9197dc8621be29c217f54c43eaa3205f54331d6a1641bc5350a7aa8185f15132bfaa443f7504437aa2a15f55240be2a0617c524c2faa521df94241beaa4437c514caeca321fd8c910dfa1a85f5534437e85195f94030be2a043bf42c42fca410fd14910dea10217e508c6fea9995f54032bf2a6417f504cafca990ef10640aea98417c52503f240887b88120bf290817d53c877c82207b94830bf29c217d5190fee65885f54341dea1283f640443eca4885f95041fb18a217e51043ea65885fd4b10
  | 1 => 0xe54043ee64886fd4942dfa16657f54043e864885f55320bfaa643dd530837ea1a177d0e43b6a90817d538cafca1a0df94842fb10621bf4290b6e84887754c21bf29865f9100435a84905f14141beaa441bd50d0a7ca998f750c43da2a221f730c427ca9196dd4542fd982613f544c3e862886f55320fa90e21ef4250afaa3105f94632fa98a217f53503e881886f10d42bea88657e544837e84197bd0a42fb10a21f7415077a84185f55232bea9661de324cafea2905d54610faa0e217d500877c86a1efd0931bfa98417e53883e843887d90f10de286857d50d0afca3185f94f40bf29a437f52843e885885f14142bea96217d540c37e8418efd0a219e2a221bd548cbee87885f54e31be29a417d5010f7a84907e88110dea1683f740c437ea7a16f50f40faa88657d5190bba6598ef50b20ef994657f544c6f8a9106fd0641bea9063bf43d03e88390df94c20fb18a43ee32483eca7887d94620bfaa2437d544c7e883885f15232bf28843fa300c2f8a610df54243baa8c417f54483e8a5886f50c41df218817c54cc3da85907d08310bf28c6377514cafca5885f54343baa88657c54843da65907d14d10faa9e217e5110f7aa8184f55020dea1461f920082fea810fd44010f7216417e544c7baa6207c88110beaa4637e5010efca620778c531bb28c61b45150bba64985f54d20dea12817c544c37a8590efd0810be29e217d5110f7e80206f90640faa8c877e510c3be6598fd50d10bf296877e50ccafaa3a1ed50b10df28a857f54842fca9084f95030ef218877e528c77a87a15f94210fa98c437d54cc7e88318df95132ef980617c53442fea4a07d4c431dfa1c877c5350af8a6105f55121fba16216d520c2fea2996f94d42fb982217c540ca7aa810ef50b10bf2a461f753442faa5085fd4943bfa9c43bd428cafca6187d88110bea90837c520437ca810df94e42f790c43f521442fca598cf95320be29287df324c2faa921ef10440fba92217d53d03daa4205b94830fd28065f443c437a8220ef50c43dfa14417f530877a8518df54442bf29e41bd428427ca990df94621fb21a217f5050be880885f94221ef988637d528877e85985d94430ef984617f53442f4a0195f14d41be28a81f5414437a85205fd4540f7994657e500837e8490df94032dfa18837d54c437ea8885f14d21dfa1081bf43d0b7e84215f55210fb906217d5210feaa3107d08510fca80437c54c83ee86887d95110dfa1283f740442fea4885f55032fb208837d51082fca2205f94841bf28481f430c42faa4085f55241bf28e81ee320cb7ca1a15fd4543fa212217c54cc77ca8196f10c40be2a063f7514cbf260186f50b31bea88817e5410efca5085f94243dfa1681f741c87ea81886f94142bf284657e5290afaa120df54c20bea98857e54cc2fca320fec8120bea9
  | 2 => 0x10020200f0002c044000089a0bc0b0101409407004491e009bc8070046b0000603c010100003006074050005406c4c0180d125a30048f4c03d1101e0240f8c95e41c190280a004010bc0d01c010ec2900c1800000090290a8000182002c1903c010281109017000003d4e40ec0902c7101401010490b4461b807014190f802008000040d15c391f81300c1a0000017c2863c1902800010120103a028030005d0e8010003212c050042706c0d0b40506402040040480d004140140201806000340582f0281b0f0000c8040380724818044011cc0d0281b0180101401050080000604c530001e0000400c7701006000660786a0c821008240082801c6c04c070040301000378000142a00097000050142300c00014000300c000000100006800054000403c13cf5010100b8170443006005dfa14817c504c7eca3185f55321fd904417e5190be8a2997d50b10bfaa2657c540437e8720df54d109e2a2617d538c2fca3995f94832be292217d52d037ea6a15f95231bf28063bf428c7ee8298fd90b10bf2a2617d528c3eaa5885f55330bf29465f120443ec20885f94242dfa1421f6510c2fea0a1f794c40fd184417e50c87eaa2104f55331bf2a063bd42882fca9885f94843ee980617c54c43bca610ef50b30bf288637f54cc2e8a2996dd0b10bf298857e50103e865886f95320fca0081bd540cbe88210fd4c710be29283bc43902baa610fdcc510bf2a665bd42487bca6107e90040fa18e437c51482f8a0a1ef50840bb288217f54cc7ec43886f50821fa982217e51d0efca0085fd4f20f690041f7544437e8598fb88521df28e85dd43cc3f661185f94910dfaa2617f524c2fca3106fd4142fd280437e5290ef8a918ef90f42fa18e217c53882faa318778c130fa90221ee32c837e84985fd4141fb29621be4350afea9906f95321bf28865fa100437ca8105f94c31be2a643f6414437e84905f94c41bf28083bd54c877e8520df94343dea10857f54882fea818df55010dea1681f453c43ec6310cf55032bfaa4637f54442f8a8905f54640efa1a877f53043f441085f15230beaa2657e51d0bf680a05fd4d41af298437651902faa5106f15110fb288417f52042fca220ef50820bea9c817e52d07da84215d94620bea9c217d508c6fca5a05fd5230baa8c61ed21086faa018fdcc531ef98c63bf42443eca2195754c40faaa221be40503ee20087dcc421be29e437e53c87dc84217dd0421baa8c877551902fca720df54740dea1083f5510c3f681205f94b30bea8c217e544877e84995f54742bfa9e2176510cbea87885f94831de28a85bf42086faa9215f55110ef21e617d53106f2a010dfd4530bf2a041f930883eaa9887d50910bf29481bd51d0af8a7906fd4542fb28c877d518caf8a2986f54142fa99221f642442f8a498cf950429f2a0437
  | 3 => 0x4009001074110000106c190004a02d98028010b8120141f00024004260e0240002001405724650884d0281c0f8550000605d80148020
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5534827461551328f59252042b960104409dd95310c6d663085108fd9742cc7395454021bc580324425f6550c43d994951103b35488110cb54b42107b354d41109d58754ccab86054d42cd50a51882d56314b10b598c52c42d56310110bc58353c42b664cc5109e983540cb5553104219d587540832e5250831cb54b40103595354021e9d8542c83b05488110ad9864350b6552544308f58a54cc73742946409e983540869f635414297d95300c27561d4e209798f5408276658c1108f58b544c26e62150208f596540863d64d4c21ec500404433542946308f191538835932540329b1953248275650c9108f992534437151940328fd95411071d544c030c7952530863f65d08309d984524c32d5250a419dd8554c834c524c931bc9862044334544c5108f191534423d64948329759653083346454630ad5835150b3742944329e983548c63c6550930cbd9542c823d6414a109d98453082766114f209d19531486b664cc721e950920c423d64948309e980530833a54940329d99643443b14288110bcd8153443b054d4110bc58052c423d64d4532ad990204427665d05108f99052c433554544329d58454882b465509109d5845050b5532544329758e54486d66308310ad59331c423d6590c409d19542c423e6494a10d554f310866c6254d109759653087355410721dc0c5500874d52cc0308f990540cb2e52508309d987540833554544308f59742cc73542544208f58b544427661943438f995424427b654c030bc582534432d5448020bc983214423f6550b31cd553410872d5250a10d954a511033454085109dd95324427461553208f596540c31d53d0840b918953443c9324c1208f99053c823e65d0930b958830442b661d4f429dd85548cb354254620ad185429027a6015032c754e43102f2600cb10ad59321c429c63541428fd95420ca766588110ad191534423d65d08209e980520433b4254032d554f410867561d5032ad992534423e6414c218f592524427a60150319e98053c86d56308110b9988404437041540219d9845050b7265d4110cb94942043b142d4110ad590214431e53508409b588530433542944208f58a540c33a5494021cdd8554c872e5250820cd50b514ca7661d5130b558c21443595388020b9588410863d64d4f20bc980434423c6454620ad59032c42b561d4f42d9549511026e6214e10f8509204431d54cc030c754f42082776154843ad98650d0a7661d4e20a798c5050ab664cc6319dd8554486b5648c9109798c52c423d6494c31c794f420863e64d4f109798c5050ab6640c910e9d8542482f16090910cd185540866f6550842cd50a51902b562d5110c795153086b6655091097d8d524427661942328f592528c65d63d5021ad59030443e362481109d587548823d65d0832cd185548cb733154021
  | 1 => 0x835a53940218f992528c6ad6214f429e980530873542544409d58453c83726194032b558f54c42d663087108f990524c6766194032b9988304423e6414a108f99253c423d6494d10c7152434c27661d50109d587540c27765509109d586508cb3764546309d59643c43354294430dc946500cb69524c0309d994324429d6314142c795253082756114c20d554e51102b66515110c755153086b66114342ce50a500ca7561152308f997424423e6494a30ad185421027560944328f99053882b664083109d984504cad4614cb31cd508514cab6640cb10cd951510ca3e6494c319d9845050e5d63149109b588548423e6414930c754c53d0a6e62150308f589540825f654c8328fd954210af162d4110cb551520c23d6550b318f59252082f06050d10cdd0a510c3376550b10cdd0a51883355494432cb5484110277654cb10d354d521027b60551328f992544c2b76150841ad9925444355530c4219bd9520083555354440ea50920442f360551108d19542442776155132ab5835250ad66310110cd952510c32d5250040b9d8953442e5620c3109b988548423d6215110b558c20c42766115032ad9865350a3e6494820ad98643d0a3e64d4c20cbd49425023d6414c209d584540ca756114e209758c54082746154b40dc546200825e63d5310b998840c42b56494d10bc580424433454c8510b958840c42766195132dc98550086746154f20ce552500872e54948309e19530483366514542ad197424435a53540219d586544ca6e6214143ad1855050a3c6454d20ad99052c427561150209d98454083376155232cb549428c2b665d0910cd551510835953480208f990534833664d45329d596434425e6314810d994a510c3345194142ad986431026f6548421b558c5244275650cb109d19532442b564c8110d654e500873542546308f99252c423c645422197195434c23e64d4c21ad59242443a9428c120ad59232c432e52d08309d19532c42d563087109dd95100423f6454630ce551500ca3d6414d20cdd0a518c3b342881109e580524c73742544208f59252cc6f1608c910d6cc9500cab5640c310da8c9500ca3e6414c209e58353087355494420ad5864350a756194332cdd0a51082b66194542d994a51102b664c8110c754e411032d54c8020cb591520c2b661941428fd9542083376454620da4c9500ca6d62152309758f54c425d6314b10cd152414423c65d09308f588544c33742546209798c530863e6494d21add855050b4d524c0309d58650d0fa86050920c794f421025d6314a10ad588544425d6315010cb549420c7e05248110cd1515344276658c521a798f51d0a3e64150209dd8553c82b4644c1108f19542443b342d4110cb54b42d02b560145429d996404427561d5130ea50b20482b664d4f10cd152314427560946439d18
  | 2 => 0x6494b108fd91518827661940439d997314423d65d08219b588540c66e6295131cd952510ca746154b30c75525308275650c421cd191518833542544329758f54083376155320c754c4110354534c510cb54b421023e64d4532cd19542c423e6414c10ab58a5350a7a6015021dc545500ca3e64149108f59253c42b6648c910cd153504433b4254021c794f420826e6214c10ad5845050a7661152208f590530871d5314d42bc58352c42d66310310ad99321443d1300c110bc982324427561940329d987520423e65151309d9865010a3d6494831abd895350b374254440ad99253c423c6454910cd50a510423d6414c10c754d42086b664085109d987540c6f160951109e580540863d65950208fd8954cc7a752145429d5865010f3752145429dd8554482756194342b518d52443e35248110d594d510823d6494e218fd91500c6766114d20d9949510c25e63d50218f99252cc7365454430add91524423d6414132cb90d52102766114c10cdd50414433461553209d994304427661943429798c52842756114132ce50a500873b42940328f59353c871e5350e419758c540871d5310c40d354e521023e6415030cb992520c2b664949109d584540c27661152309d994204427560d4542ad9945150a7461548438fd9540103565394440add9153442b564c8310ad9845050a6d62141439dd81510cb4d53480209d58754cc27661148108f59052043b35448110ad98653d0b716194032e9509210863e64948108f59252843a76250910ad990524434e5354840cb549429033454d4d10ec15120442f36054910bc58053c425e63152109d5865010b565394420cd584544431d53d0040ce951500ca3e65d0d408f992538863e6494b30ad99320c42b7644c1108f59353c427465485109b98853082f260081109d997214431d5494c218f992544426f6254d10ad191524429e63143429d987540c2ad648c9209d98754cc27661d4c109798c540863d6414e108f990504cb2c43548409dd8552d02b56194142a758c50d0be24248110cb991520c3565354440ad590204423c6454630dc985500cb354294440c794d42082756114d20dc585500cb3465509108f994544423d6494b10cb949428c355530c710bc996204427960d50329d987530826f654c832ad99252c42b4644c3109b98b540c2f1600cb10bc586308825c6355120ad990304432c6550920dc88550087725144010b598c52442776154d21b558c40c42776548421b598f54c43a14248110ad58643d0b3942540219d5865090e5e6395121e950b20c43374254630ad990424433551106408f597420c32e5250a409d98453086b664cc710bc98242443b14248110c7951530831d5310f42cb54b42d067561141439b988540c65e63150308fd91538826d6214e109d984538823c65d0910cb95142c
  | 3 => 0x110ad993314c63d6494d218fd8954083375314542cd150524433942540329e580540ca7561d52309b19542482786548110ad99321c423f6454d109798c530827b65500408f59053c827661d5032cdd09519033765509109d98653d03655294430cb951520c2776154b30ab58b53d0a756194242d5cc9510ca6d62951319dd815190f546154c21e9509204423e6414f219e5805308674654c510cb54b420c3a46150b209d19541442b6648cb109e980524c6b7644c310cb54a411023e64948309b588540431d53508408f191500c7345114142cb94942842f16010d108f596540ca776550441dcd0550086d763549108f59053c86766590f108fd9150ccb3742544329758c5050ab76154d428f59252087e23248110f84c920442f1618c120aed815350b555348421dc982518827b6548020dc945500cb3665151108f99052043395494032e9d8942c427960d5231e9d4b5150aad6490920cd54641102b564149109d98650cca7a60d4c21ad58450d0b1e5350821cdd09510c3a9424c120cd95251082796584010d554d510825d6314810cdd0e5190ee562101109798c540832d64948308fd95420872c5250931dc99620442f06548110bc582524432d5494830cb98a54c831d53d0821ead81424833554944308f590524c6b66190e409e58053c873a54540218f99353c87715148020b6181434c2b564cc510ad9864350f3742944108f99353c82d663081109758c54882f260109109d98653d0a6e6215010ad1855350ab564083108fd91508867b65440109d58753083a46150920bc58354c42b56194342bcd81434427661942439dd9542c425e63152209d58653d0a7661d5332cd15252442b6640c310d554e210863e6494821ced0a500863d6494a309d185544833561d5130cdd4b5150a3e6494831d354f200827960150319b988548c27565cc421d554e51082b56414b109d580514ca3f6550830c754d420823d6414b10d394e521033543145429798c52442f2600c910cd509510c27665d05319e583540863f6550c43ad593214433564d4532ecd09204423e6494832ad590324433561d51109d987548c2e6620c310c758c544c276650cb10d554c534427860551328f590524c2756194010ad59253c43a94248210cd987544c32f6550920cbd49424c65f654c431cbd49425072e64548408f990540873553145429798c540427461552329b588540c2af6550b209d584524c2756194f40c714d4350a756014542ad59353c423c64543329b58b540c25f63551208fd91524429d63d4742ad59021c431d53500409d994404425d63152109d594410865c63549108f59252cc32d5250830ad5865350b2e5450842da54a300c2ad648cb20dc48550086f16015310cdd0a511033754d4110bc995204427661d5220cd509519032e52508408f99252442b5
  | 4 => 0x92d0000ac02004000005e3fc0002021004091541a04c140047e134ea0000812000680b11464c0780b0783200c2200006050340086014c090081498425008271880706c0204c6e0380a044010e8040003309caf01811000062a42d10c15048630084e000000080314c0f0480000c062784b030022880a03c3331cd617c2200c1105ce10100a06017024e304c24a941302425000042cc540040e00000038000a8051718700003000000b0110e40900c01014000040007c86010380009b00c02d84030300809407381e715000150004b42f1141f0140a0080002003044050600d858310b4445b06a19c0b01c10050010000a1181c00038018000000d00400040230203a0040802cd50001e0385f014930680700c007a01b440120081300408028000bc1e5000409407054330000201c07b540a4fc0a030060040f00c3a0a8020080901433071df1a0040883f000820f4350af30004000080102dfa0007c0705b008000003e01004018180102e00010bf13b104009dd8553482b664cc421ad58653d0b3654544208fd89540c33742d45329d583514ca3d65508309d98454042766115030cdd08514cb354294432e3509320cad663d05318f59052443555314f109d9865090b3743145429d19542442f260085108fd91534823d64d4c208f995424c32d52508108f59053883a542c8110ad592524431d5454c208f99053842b46150b41ad99021c42f16288
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1000e00080080c0800a000900074010000010200700010004080000c000000080c0004003000030000000270400105000c400000078104000000010100a4ce321aa42072375509204421a3b284a8c412c5c06150840c2aa630a8420705424c9510cb84a1264a8065891946150920b42e23028490721424855008718328a890221b0589300c110ac0eaa124088471701855210ed13aa8490221625cc6050920c8aa6b108210ea1425863048292b90a810a21385c86050d10e40eaa1240886166454f31086d0ba0a4902210d1d564c8110a50eaa1240884a57299331086b0b9082a8043481d54248110b42e030a84905a07550920442a2392a629a218654d6010440a30e0a98a6a15247550920442993a662a8043685c8544811086aec2a042885307054c5150b50308c0a1241491d542c811086cebb2260884377650b514cb0a2a2c6292218558c5114142c52a4b00822042d72191500c748b1a80202214c5c05114142a52e02928498d4970149324c782a9a84908430d1d94254630b82e62924088436759954244348b2260182218554e6190c40b42e91924088530755092044350b1280202214c1d54288110b42e921240887205414920443122a0c4a9a21495c85414910868eab2464886145458c2144258b84c321881325c86050d30
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x260000105077a058215163149108a087509618c120c20655c85448110c11635c05114142c81731846050920a058299153cc421c20655c06150920921809c64354840921829d33154021c11535c06150840922859d54248110d00545cc5248110920855d23248110a05821516308510c11535c26190c40
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
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
  | 6 => 2*((h/63+packedAt s5K6 (704+(h % 63)*6) 6) % 44)
  | 5 => 2*((h/287+packedAt s5K5 (22140+(h % 287)*10) 10) % 820)
  | 4 => 2*((h/298+packedAt s5K4 (33972+(h % 298)*10) 10) % 894)
  | 3 => 2*((h/78+packedAt s5K3 (3332+(h % 78)*7) 7) % 68)
  | 2 => 2*((h/12+packedAt s5K2 (900+(h % 12)*4) 4) % 15)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x8ff87fff07c7fe3863c7e3ffe387fe0e09f1f3
  | 1 => 0xf07f878ff8071fc783f8fc707c070ff076c99c
  | 2 => 0x7ff80ffff81ffffc00ff807ff80fff870e1f
  | 3 => 0xff80000fffffe007ffff00007ffff001f80fe0
  | 4 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa10910011088004000412091208122240050b1
  | 1 => 0x2713311231922c0981c86423641264e432c994
  | 2 => 0x4820022442005002240089040920090885020a
  | 3 => 0x206454885040494ca9200085254c041580d40
  | 4 => 0x4c446600e62699277324d24e00608189efa000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeafae0feeafae0feeafae0feeafae0feeafae0feeafae0feeafae0feeafae0feeafae0feeafae0feeafae0feeafae0feeafae0feeafae0feeafae0feeafae0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_38003
namespace PEqualNP.Outside.L_meta_38003
open PEqualNP.Outside.L_meta_38003.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x31800087000000000000000000081040400000000020c040800224113060000000000004aa4001000011c0800001062450300ff14003fc30015fd4803ff40017fd4807ff31017f8c803fd1000ffd4001fe31016fd0803fc20017f54809fd43017f48403f710017f90803fd20017f0c803fd4002ff54c05ff32027f95003fc4000ff84005fd4202ff94403fe2000fd44005ff2100ff54007fc4301ff94c03fe4000ff940057d52017f10803ff30027f50409fd54007f4c407fc5302ff14409ff41017f4c809ff4302ffd4409fc41017fd0807fe4300ff4c005fe21017f14805bd4200ff04009ff5400ffc8009fe4102ff54405fe5200ffc400bff5301ff0c409fc5400ff8c005fc21
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x35680440589830040024102000001c38000009c0341c140014000200100000014c380004001401b43c0010e48000c8080c38480410117eb126203ff8ca31055feca9881bfc514c417fe1046209ff5053103ffcc098812fc644c419bea946206ff9823104dfac89881bff628c411fe2126206bf9863106ffca91882bff654c415ffa8a6208ff58931046fea49881aff634c407ff982620cfd48631047fa849880ffc328c4097f3246208bfd8931037f86298823fc624c4157eb2a6209ff99131037f8c11881bfe214c407fe29c6206bf1963101ffea698827fd644c40dff18a6207ff88131047fec498827fc644c4057f3126204bf9913105ffe411882fff508c40b7f32c6207ff84131037fecb1882bfd514c411fb10a6208ff98931037f8209881ffe404c407fa18a6208ffd0931067fc851881bff418c411dfa126203ff90e31047fca49882ffd508c411fe90a6206ff9463105ffa411880ffe308c40dfea0c6206bfd823103ffe809882ffc508c411bea926201bf98231047ba649880ffe538c417ff2846207ff08131057faca9881bff108c41bfe2a46206ff90631037fec11881bfe514c40f7eb026206ffcc631067fea51880ffe324c419dfa146203ffd0d3104ffca89882ffc408c419fe2946206ff44231037fe431881bfe628c40ffeb026208fd48531037fac11880ffd538c40d7e3246203ffcca3105ffa811880ffd438c4077eb1c6206fdc4231075facb1880ffd328c413ffaa26203ff14d3101ff86118806fc608c407fe21c6206bfd963104dfec89881bdc314c40dfe10c6203ffd0e3106dfac91881fff504c41bfeaa4620bfd4423101ff86498827ff644c411ff90a6203ff8c131047fc849880fdf324c407fe9846206ffd923101fee631881bfd658c40dfe10a6203ff90d31037f8831881bfc518c40fff9026206ff58a3103ffa409882ffe208c413fe2a2620cff50a3103ff8a09881bff104c415fe32a6206bf18a3104ffe829880ffe534c419fea946206ff19231037fc82988337f528c40b7e32a620cff10a310677a851881bf4318c4177eb046206ffd4631047fea49881bde314c4037e302620cff94a3101ffe611881ffc404c40ffea026205bf9953101ff8869881bfc318c40ffe8826207ff1813101dfec29880ffd434c40dff10c620aff99531037fcc91880afe628c40ffb8826208ff1493104ffaa89880fff314c407fe9926203ff54d3101ff8609881bfc658c40dff0846206fd8863101ffa609881ffd504c407ffa9c6206ff5463103dfec09881bfc108c417ff2046207fd44131067fe851881aff648c40dfeb246206ff48631037fccb18837ff548c40fff282620cbf58a31047faa49881aff628c407fb98a6206ff18a31037f8829881fff604c417ffa046208ef50931037be6318806fe604c4057e3126203ffcc931
  | 1 => 0x8000164084434145c4404240004ac040ce424040400241088bc02044c14000cb458dc000040043c0000301001
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x2
  | 7 => 0xb49
  | 8 => 0xb4b
  | 9 => 0xb4d
  | 10 => 0xb4e
  | 11 => 0x1449
  | 12 => 0x144b
  | 13 => 0x144d
  | 14 => 0x144e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 210
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/57+packedAt gbK8 (1716+(h % 57)*7) 7) % 66)
  | 7 => 2*((h/98+packedAt gbK7 (7770+(h % 98)*8) 8) % 210)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f0fff860f0fe1fffc703ff80f14413e09f1f3
  | 1 => 0x87f0e0780ff0fe1c0f80383ff02b8ed876c99c
  | 2 => 0x7ff007ff000ffe00fffc03fffcc30e1870e1f
  | 3 => 0xf800007fffff00000fffffc000f03f01f80fe0
  | 4 => 0x7ffffffffff000000000ffc001fff000
  | 5 => 0xffffff80000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x901210001012024241008882200000a0050b1
  | 1 => 0x83104318071062086c809192e201865832c994
  | 2 => 0x4aa042290009540812500250c4c10a085020a
  | 3 => 0x5000084d2aaa00010a4aa70040b02b01580d40
  | 4 => 0x40881077ccccd993c003020184fec001efa000
  | 5 => 0x66cc9e0180881102000c040608ff7df4000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_38003
namespace PEqualNP.Outside.L_meta_38003
open PEqualNP.Outside.L_meta_38003.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_96 : Interval s0Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 112 := (concat bs0_3_0 bs0_3_96)
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
theorem bs0_4_672 : Interval s0Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_864 : Interval s0Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_960 : Interval s0Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1056 : Interval s0Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1152 : Interval s0Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1248 : Interval s0Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1344 : Interval s0Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1345 := (concat (concat (concat bs0_4_0 (concat bs0_4_96 bs0_4_192)) (concat (concat bs0_4_288 bs0_4_384) (concat bs0_4_480 bs0_4_576))) (concat (concat (concat bs0_4_672 bs0_4_768) (concat bs0_4_864 bs0_4_960)) (concat (concat bs0_4_1056 bs0_4_1152) (concat bs0_4_1248 bs0_4_1344))))
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
theorem bs0_5_768 : Interval s0Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_864 : Interval s0Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_960 : Interval s0Atlas 5 960 57 := block_range (n:=57) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1017 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 (concat bs0_5_288 bs0_5_384))) (concat (concat bs0_5_480 (concat bs0_5_576 bs0_5_672)) (concat bs0_5_768 (concat bs0_5_864 bs0_5_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 48 := bs0_6_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 12 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 91 := bs2_3_0
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
theorem bs2_4_480 : Interval s2Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_768 : Interval s2Atlas 4 768 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 794 := (concat (concat (concat bs2_4_0 bs2_4_96) (concat bs2_4_192 bs2_4_288)) (concat (concat bs2_4_384 bs2_4_480) (concat bs2_4_576 (concat bs2_4_672 bs2_4_768))))
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
theorem bs2_5_576 : Interval s2Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 69 := block_range (n:=69) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 741 := (concat (concat (concat bs2_5_0 bs2_5_96) (concat bs2_5_192 bs2_5_288)) (concat (concat bs2_5_384 bs2_5_480) (concat bs2_5_576 bs2_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 42 := bs2_6_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 24 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := bs3_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 15 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 68 := bs4_3_0
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
theorem bs4_4_768 : Interval s4Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 894 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 (concat bs4_4_288 bs4_4_384))) (concat (concat bs4_4_480 bs4_4_576) (concat bs4_4_672 (concat bs4_4_768 bs4_4_864))))
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
theorem bs4_5_768 : Interval s4Atlas 5 768 52 := block_range (n:=52) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 820 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 (concat bs4_5_672 bs4_5_768))))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 15 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 68 := bs5_3_0
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
theorem bs5_4_864 : Interval s5Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 894 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384))) (concat (concat bs5_4_480 bs5_4_576) (concat bs5_4_672 (concat bs5_4_768 bs5_4_864))))
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
theorem bs5_5_768 : Interval s5Atlas 5 768 52 := block_range (n:=52) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 820 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 (concat bs5_5_672 bs5_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := bs5_6_0
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
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 210 := (concat bgb_7_0 (concat bgb_7_96 bgb_7_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 66 := block_range (n:=66) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 66 := bgb_8_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0feeefeeafeeafae0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276812512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38003.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[4,5]⟩,⟨.or,[3,6]⟩,⟨.or,[2,7]⟩,⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.or,[8,11]⟩,⟨.and,[3,11]⟩,⟨.and,[9,10]⟩,⟨.and,[12,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276812512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276812512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38003

open PEqualNP.Outside.L_meta_38003 in
theorem PEqualNP.Outside.L_meta_38003 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276812512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276812512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
