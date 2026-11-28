import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37375.Model
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


end PEqualNP.Outside.L_meta_37375.Model

namespace PEqualNP.Outside.L_meta_37375
open PEqualNP.Outside.L_meta_37375.Model
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

def SBf (j : Nat) : Nat := [4, 6, 3, 8, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37375

namespace PEqualNP.Outside.L_meta_37375
open PEqualNP.Outside.L_meta_37375.Model
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
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffdfe0ffffff803fffffffff00ffffffe1ff
  | 4 => 0x6bff07c1ffffc00ffc01ffff00ff007e38
  | 5 => 0x73fff801fffffff00001ffffff00007fc0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffff8022108825924992c5245b4b4b4b6caedb
  | 2 => 0xffff804421104aa492a54a48ad959595b5576d
  | 3 => 0x209e422093762349939136c0e6e6da61b6
  | 4 => 0x1508f43b1c473b8e231dc7e6c0f81c7a38
  | 5 => 0xe1087bde0783c0fc3e1f8f8f8c0e07dc0
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xc0c0c000c000c000c0c0c000c000c000c0c0c000c000c000c0c0c000c000c000c0c0c000c000c000c0c0c000c000c000c0c0c000c000c000c0c0c000c000c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37375
namespace PEqualNP.Outside.L_meta_37375
open PEqualNP.Outside.L_meta_37375.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x8c38062001ab30128504a00065bf43bd43bf42bd42be41bc41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x82180028010065aa5a1c754f428ea98832d52107a060087808010
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
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
  | 4 => packedAt s1K4 (244+((h/4+packedAt s1K4 (224+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s1K3 (170+((h/2+packedAt s1K3 (162+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfe03fffffffe01fffff80fffffff01fff1fe3f
  | 3 => 0xfffc03fc03fffe01fffff01fc07ffe07fe63c7
  | 4 => 0xfffffc0003fffffe01ffffe0007ffff81f83f8
  | 5 => 0xfffffffffc00000001ffffffff8000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x9604848428a224242450b162d48b628a26acdb
  | 2 => 0x2ba1292a51451d4948ac0ab56955115551562d
  | 3 => 0x4caba2329a69491d913d58198c66b4479a6346
  | 4 => 0x713233a3639191911dce6cd03078d9e11d83b0
  | 5 => 0x81c3c3c383e1e1e1e1f78f1e3e40e1861ff800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaa0a0a0aaa0a000aaa0a0a0aaa0a000aaa0a0a0aaa0a000aaa0a0a0aaa0a000aaa0a0a0aaa0a000aaa0a0a0aaa0a000aaa0a0a0aaa0a000aaa0a0a0aaa0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37375
namespace PEqualNP.Outside.L_meta_37375
open PEqualNP.Outside.L_meta_37375.Model
def s2K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (i*4) 4
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (5+((h/1+packedAt s2K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffdfc7fff87ffe3f
  | 3 => 0x6bf878ff8783cc
  | 4 => 0x73ff80fff803f0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffff8041102888a8d5
  | 1 => 0x20b2245455522a
  | 3 => 0x1517459d461b4c
  | 4 => 0xe2476e66463b0
  | _ => 0
def s2Atlas : Atlas := ⟨2,rawDecor 27 s2Pos s2Neg, 0xaa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37375
namespace PEqualNP.Outside.L_meta_37375
open PEqualNP.Outside.L_meta_37375.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x2a80000000289001b3e8002a0e0cc0b0c980232200797180000d0000002006472b26691042000f0000954953a00027000050038580211248400020000001040000116183012024000ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461be428c3788518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930df21261bc424c3bc6498770c930bfa8a61f7514c2eea2985f14530fa28a6174514c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c2faa4186f90830de21061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20df21641bc42c83bc6590770cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea9441ef428837c85106f10a20f621441ac42883de6510778ca20ee19441ec328839865105f94620bea8c41ee21883d843105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c534837c84906f10920ef19241dc32482fea2907dd4520bba8a417c51483e8a2905d14520f790a41ed21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef420837c84106f10820f621041ac42083de6410778c820ee19041ec320839864105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10df21621bc42c43bc6588770cb10fd90621f820c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437c85086f10a10ef19421dc32842faa3087dd0610fa20c21f731843e863087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910df21221bc42443bc6488770c910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437c84086f10810ef19021dc32042fca2087dd0410fa20821f731043e862087dc8410fa108217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xc525077c84a0ef10941ef19283dc32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083be42107788420f78c841ee190837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598df54b31df21663bc42cc7bc6598f70cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718f790e31eea1c637e528c7dca518db94a31bea9463ed528c6daa518ef90a31de21463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931df21263bc424c7bc6498f70c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863de430c7ba8618df94831bea9063be420c7788418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f7a1643be42c87788590fb10b21d621643ef32c87bc6590f70cb21f619643cc32c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53887bca710d794e21bea9c43dd53886baa710df14e21bea9443be42887788510f78ca21ee194437e51887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487de8490ef90921de21243ec42487588490fbcc921ef19243dc32487d86490f30c921fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043be42087788410f78c821ee190437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40ef19681dc32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481be42903788520778ca40ee194817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c525037c84a06f10940ef19281dc32502fea2a07dd4540bba8a817c51503e8a2a05d14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52102faa4206f90840de21081de32103b864205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30df21661bc42cc3bc6598770cb30bf28
  | 2 => 0x4020000010000040380800400400002002008000010020000000000c01003001000000000030040040380100e00000800000000050000020140000200001000000004006fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa9287ef5250edea4a1df14943f6292876c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42ef29e855e53d0afaa7a17754f42aea9e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85be4390b7a87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1216fd4e42df29c85bd5390b78a7214f94a42dfa8c85be5190b7aa3216f14642dfa8485be5090b7aa1216f14242bfa9a85df5350abea6a15f14d42ee29a855c5350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216fd0c42df21885bd4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042dfa9885be5310b7aa6216f14c42df290853e5210b5ca4216fd4442df28885bd5110b78a2216fd4042df28085bd5010b78a0215fd5332bf2a665be54cca7ca9995f55332deaa6653d54ccaf8a9997bd0b32df21665bc42ccbd885996b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbbc87197750e32ee21c657e528cb7c85196f10a32ef99465ef328cafca3195f54632bf284657d508cbbea9197795232eeaa465dc548cabca51977d0a32ef214659e428cbba85197710a32ce21465df518cbbca3197754632ee28c65df508cbbca1197754232ee284657f544cb7ea8994fd5132bf2a2657d544caf8a8996f151329e2a265be424cb7884997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8195f55032be2a0657e530cbbe86197790c32eea1865dc430cafca4197bd0832df21065bc420cbd884196b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032efaa065de540cbbaa8197715032ef290655e520cb9ca41977d0832e7a1065de420cb3c84197750832ee210659c420cb9884196310832efa8865de510cbbaa2197714432efa8065de500cbbaa0197714032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf296837d52d077c85a0ef10b41ef19683dc32d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720efd0e41dea1c837e52907dca520db94a41bea9483ed52906daa520ef90a41de21483de32907b86520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837
  | 3 => 0x7e2348710a2c42a47cd8d8002bc9c44200000000000312000cbc65297000be0e2366252465a60d82ac0000012b1d0001520000003cc000000000003793d1684400020d4b899198b6200000000000000000f1147000000002941f200015b290000000000043c00000202000001060000001a80001600000000000364089531910007b0548000000000000000056c0000040a0001080043a000000003822c9ab95a106000ce800000000002b62a2000002ed202c7400000000734000000007789b0000000000008f0009480000022e00194000000dc99c0be0003dc000005765b8002b037c000000000008dc000001220018b8000ce0000013e0000000d34800000000000000a080011e24c001271c60001a4ea000000000131d160aaf8000004de0000000000000018000000a81818000000011700000000091a89000d680bb334fe001588004f47f876000000000000000006d80036f094a9d4285109cbadb08f63de0003c0005fe00000000092000000004fc0017322a2f6000000003b2240d28441e413d0518a35e0011f000000000000002689652800019e0004e000000000000005d2001b4880000000000000000000000035c0000024a000000000000000000004d000000000001fec29128a4568a1c6e2cb000a203faec4b65cca30006b6000f8a2b46409cde8006f2bdc000004c21c922a41062000ae000000604000000005300032c0000012d00000000000000594cfca280000000000000680000000ed00000000000000740001bc0004b400132166000000000004a8000000000000008c2de68d46000000000001c50007300000000000000000000000f3098000860002290845fd1ea510008857a00000000000000000d9400175000000850fa59e000e5ae50107e8000e3292b618100000000000000000000000110000bd610af0002f4000000002980000000400a01002800002010000050000000180200000c008010000040000300c0000000000000003000000000008030000080000100000002800000008000030020000000000000000000008018000000000080000100a000038060020040200000a0040200200200800001006004000000020040000100000802000000004008060000000200000200000802000028008000000000080000400c00003000000008010000000080400000000003000000018030020240000500201400005000000008010000000000000400006000000000000000040000080300200400000004008020040040000480000400000003000004000030020040400000000000000008004030060000000000200c00000000002004008000000080100000400003001004000000020000080000000c02c000030020000200100000400802008004000010000140300400602002001002004000030
  | 4 => 0x380000e48000000000034b60e0000000000000000000000ae80000049a43174000000d29881372940018413a208000002fd6d00001400000000000000000000000000da7ac75a0b4f898843b545667e5182fe520308feb3d0f6000000480001ac8980000000183000000868000004882753680029c000000000003e02e80000000000000000000000002a600000000644000ed80018c00000000000000000000000000031e000001ae9f60000017c8001ca000000005c463c00000000000001a72d6000002a5238000cd9f800000000128580490002c86685645c8000001800000000000000000000c60d489327200000000002389118055ec000000ae61ad9c000006e00009980059c001169ac14670d9b80000000000000000000a18fc4a80019d0000007291d31964ad403e800080000000002a000000000000b40000da000000fa800000000000006c029c00000000000003351b200000227000000030000000000000000071c002490000016f8000b8b747000000081800000040bd44aaaa42e0000023f1deca8c6a354ee7857218400035c4b8000caaa00000016c0400026e0003916480005cb04fa00013e9305e000280001a32380000005423455c160000000c800000000312000aa8000001688400022200000000000000000000000000024b3f823866343572000750000000012109600000123b6364c104000000045900026b27091908800000000689ea53650400000000000148003f6c10749270000017080061e5b0000004ca15c002fc000000000000006700033951e2b03a373176a34b00d227690c00000000ab4810006bc30c00000000000000006e8cb800000000000d23783340000000053c0013c00000000000284000d3c000ee21e0000003b0000000004c602a44d31e75c6b6cb880052642c000000000002aad968e001189ff00000184a330000000020e0000000000000000000000000b9c56aab19a000000000000000000043e86d7800000000022825000000000df6d612cc5995244d35380000000000000000000192353564030bd00000059c0000000000000286676858fb85b0007b41b800000001301bb000000000154be00021800360000a598c0000000006c6a4000730db000000000000003016180000003c5c08105aafc002d231c324000000000004500000099c0000053e9982f1000000017000020e0017916d61800000292342039549dd058064000000000005b80065a00000341320b1c0000000000000000000000000000005d8002792aebbc0026a0000000000000000023000500000002035ac0000011d0000000000d30a0016d0f4000800f90006260000000000000134800000000000004d0a64002243e00008a1a80d057d090000006b452800000960d980000000000000384b50000002844bc0000000
  | 5 => 0x7000157b550001c0000004e80014e0d600000073862000000000000000000000007a264001181289000000035401c00000000000000004500016e0002fa00000000000000001880009b0b4acc42a06c3d0d30000000033c61c001798c813c8ec0014d638be95b9ba054000001b521c000670000002e8c007c000000001e313600117aac5f6001ba886656000b08003d20008680000000000000640458000fb6420000000061600131800000000000000000002b2551340000013500000000000000000000f00002c5ac8000000002fa19660588000000000001c80000000000272000001279990000000017007c001a88ab41e4b95080028894ce7800000000000000000000025e12400000023262af4000000005d1ae220160150000000e27a00e0000000000000000000000000000311b50756d8c58eb0006acc8da222c000000001d326022c000000009ec00000000000be1bf0005c8aa0000000014500008e4840028b000000000001447b8bc8000001b8003156ee00000000408000000610001652b00037022000000000000000001fc00000183142cc800000546000000000009cc000001aa00000000000000000000000011100023600000004000000001962cab14f00000ec6dd13000000d387e8351960006a0000480008318700004c00000000224b41d700000000000000d7c6ea810000018f99f506c6975012154000003140000000000018a001a4986000000000006e26ac0000003ca74001e50000001e1a03040cd3a8005a69f55a8006223856b8c71a04b09f9b44782d5b68002c60000028e6c8000ea800402000e90003440003bb423c821577296000000000000000016f0000000000c050534db8dc8000000000019e000cd8cc00032400000000000378000000000000025d0000000000024a00046b27000000a400017e0010493c0000d8000003b0050cb8000000282980000000ced1b100095c000000000000016a00018c7a873000000ac30059a448001096ec20805a390000001d0000a4000002b80000000001f52a000000c139081c0000007e4800000000077000000420738000005aa5e08a993000000000000000255e000000000ae8004260000017e23e0c9043582cc0003c81d000000001df0003c450177490a600033e0000000000029e651a280000000000103000000000000009d8002c600000000000000000000000680015123600000178ad100019882800
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xf528425d63d4a108fd91528423c6454a1097d8d528425c6354a10cbd48428432c5210a10d3d48328434c520ca10e310832842d663d0610ad99331843a442c8610f10cb218423e62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544427761551108f994544423e6215110c7d53534431c54d4d109798b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d1097988534423e64d49108f593524425e63d49109758f524432f54d4910cb153524434f53d4910d314f524432e64d4910cb593524434e63d4910d358f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524427b60549109b994524432f5414910cb150524434f5314910d314c524432f6414910cb190524434f6314910d318c524423e65909108f196424431f5390910c714e424432f5290910cb14a424423e65109108f194424431f5310910c714c424432f5210910cb148424425e658c91097196324431f548c910c7152324434f528c910d314a324425e650c91097194324431f540c910c7150324434f520c910d3148324438c420c910da14b10443345484110d514e104436452841109798f540425d63d50109b98b540426d62d50108f596540423e62950108f189540433461550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c109798a530431e5454c10c7551530425c6254c10d5185530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432f6494810cb192520434f6394810d318e520423f64548108f191520425f63548109718d520432e5454810cb551520434e5354810d354d520432f6454810cb191520434f6354810d318d52043646154810da181520423e64148108f590520425e63148109758c520426e62148108fd96420423d6590810c794e420431d5390810cb94a420432d52908108fd94420423d6510810c794c420431d5310810cb948420432d521081097d96320425d658c810c7952320431d548c810d394a320434d528c81097d94320425d650c810c7950320431d540c810d3948320434d520c810e3108320433554d0410b598f41042756510410ad993310435553cc4109d594310436552c8410e910b21043c432c84109d594210436952c8010f8c8720042796508010ea10820043c83208010f8084200427965840109dd9510042b46444010b518d10042e462440109ed9510042e86244010
  | 1 => 0x825d63152208f993538823d64d4e20c7952538831d5494e20c7951538831d5454e20d3d89538823e6414e208f59053882ce63d0a20d394f428831e5390a20c754e428831e5310a20c754c428832d5410a20d394c42882ad6510a20cb594428832e5310a20e394c428830e5310a20e354c428832c5310a20ab993328832e54cca20c7952328831d548ca20e310a328831e540ca20c7550328838e420ca20e3108328832e540ca20d354c32882cd650ca20d3594328834e540ca20e3950328830e540ca20e3550328834c540ca20cb109518834c3254620ab99221882ce63886208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551208f994544823e62151208f188544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534825e6514d20c7d50534831c5414d2097988534825c6214d208f996424831f5390920c714e424823e6510920c7d4c424831c531092097996324831f548c920c7152324825e650c920c7d50324831c540c920e3108324833754d4520cd153514835753d4520d514f514833642d4520cd10b514835632d4520d50cb51483375414520cd15051483575314520d514c51483364214520cd10851483563214520d50c8514826e65c8520cb153214834c53c8520d9147214832c5448520d314d21483645148520ba181214837051c8120cb152204834c5388120d9146204825f63550209718d540825e63150209758c540827661150209d584540823f6454c208f191530823e6414c208f59053082766114c209d58453082ce63d0820ab98a420826d6510820cb994420832d6510820cb94c420832c5310820ea98042083a96010820ab99332082ce628c820e310a320838e420c820e3108320826d650c820d3994320834d650c820d3950320834c540c820f298032083c9600c8208fd91510823c645442097d8d510825c6354420cb109510834c32544209b59621082ae6488420b398e210823e64940208f592500825e63940209758e500832c4294020d30ca50083a84288020f20ca200826f6548020ab19120082cc6348020b9185200827b6548020bc185200825e63d53109758f54c426e62d53109b58b54c425e63953109758e54c423e64d4f108f59353c426e62d4f109b58b53c423e6494f108f59253c423e64d4b108f59352c425e63d4b109758f52c423f6454b108f19152c425f6354b109718d52c432e5210b10cb54842c434e520cb10d354832c438c420cb10ea10820c43c8320831097d8d548425c63552109bd89548426c62552109798c548425d63152108fd91538423c6454e109bd89538426c6254e108f990538423d6414e108f993528423d64d4a109798
  | 2 => 0x32145408f997415029d63d0540c714f415032c52d0540cd147415031c5350540cb14941503345150540c714e405032c5290140cd146405025e6294c409bd89531026c6254c40b3189531034f6254c4097189531034c6254c4093189531023d6590c40c754e431031d5310c4097d8d521025c6354840c794e421031d5390840c794c421031d5310840cb948421025f658c84097596321025f650c84097594321038c420c8408f596411029e6390440c754e41102ae6290440c754c411031d53d00408fd95401029c6350040c754d40102ac6250040ad185401027b65500409b98b54cc26d62d53309d98754cc27561d5330c715143cc2cc6250f308fd9152cc23c6454b30cb94842cc32d5210b30d394832cc34d520cb30e310832cc23e64947308f59251cc26e62947309b58a51cc29d64cc7309b98b548c26d62d5230c7d50438c23f6454a308f191528c32e5210a30cb548428c34e528ca30e3108328c23f64546308f191518c29e648c630b398a318c23e62d51308f992544c26e62951309b58a544c27661951309d586544c25f63551309bd89544c26c62551309dd85544c27461551308f994544c31d63151308f988544c25e6590d30c7152434c25c6550d30c7151434c2cc6250d308f993524c23d64d4930cbd53524c32c54d4930cb993524c32d64d4930cbd50524c32c5414930cbd90524c32c6414930d3d8c524c34e4314930d350c524c23e65909308f196424c32f5290930cb14a424c23e65109308f194424c32f5210930cb148424c31f548c930c7152324c34c528c930c7d50324c31c540c930d3d48324c38c420c930cdd53514c33454d4530d9d4b514c36452d4530cd90b514c33442d4530d58cb514c35432d4530cdd50514c3345414530d9d48514c3645214530d590c514c3554314530cd908514c3344214530d58c8514c354321453097997314c29d64cc530c7153314c34c52cc530d5147314c31c544c530d3149314c354514c530c7152304c34c528c130d5146304c23d65950308f98a540c26f62550309b189540c2ac6255030c718d540c32f62550308f189540c32c62550308b189540c23e64150309798c540c25d65d0c30c7553430c25d6510c30c7550430c23f64548308f191520c23f65908308f596420c23f65108308f594420c31e548c830c7552320c31e540c830c7550320c34e520c830e3108320c25d658c430a7992310c31d548c430b398a310c31d540c430c7553300c25f654c030a7191300c31d544c030b3189300c2d4614c0309ed95300c25e63d53209758f54c827661d53209d58754c825e63953209758e54c823e64d4f208f59353c827661d4f209d58753c823e6494f208f59253c838c420cb208f99251c823d64947209798e51c825d6394720ba18121c825e63d52209758f548832f62552209798c548
  | 3 => 0xe21c794e428871d5390a21c794c428871d5310a21c7952328871d548ca21c7950328871d540ca21e3108328872e54c8621d394f218872d62d51218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e6515121c7d53534871c54d4d21d358b534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c7150534866e65d0921b398f424874c53d0921b9987424863e6590921c7d4e424871c5390921ab98a424863e6510921c7d4c424871c5310921cbd50424874c5310921ab994424872e6510921e3d4c424872e5310921cb14c424878c5310921c314c424866e65cc921ab993324872c54cc921b9987324865e658c921c7d52324871c548c921b398a324878c428c92197994324871f540c921c7150324878e420c921e3108324872c540c921d3d4c32486ce650c921d3994324878f540c921d3950324874c540c921e3150324870c540c921e910b21487c432c8521ab99221486ce6388521ced53504873854d4121d6d4f504875853d4121ea10b50487c832d4121ce90b504873842d4121d68cb504875832d4121cb108504874c3214121ced5050487385414121d6d4c50487585314121ea10850487c83214121dad08504873a4214121ce10850487684214121ca108504876b3214121d68c850487583214121da0c850487483214121dcc84504876a21141219798f540865d63d50219b98b540865e63950219758e540863e64d4c218f593530866e62d4c218f992530863d6494c21cb948420874e520c821e3108320863e64944218f592510865e63944219758e510866f6548421ba18121086776548421e990921087c63248421bc181210863f64540218f191500865f63540219718d50086ac6250f4097d8d52d025c6354b40cb94842d032d5210b40d394832d034d520cb40e310832d025e63947409758e51d026e62947409b58a51d029d63d074097d8d529025c6354a40cb94a429034e520ca40d3548329038c420ca4097d8d519025c6354640a798e41902ae62906409798b535025e6214d408f997435031c53d0d40c714d43502ac6250d409798f525025d63d4940d3d4f525034c53d4940d398f525034d63d4940d3d4c525034c5314940cbd90525034f6314940d318c525032f4314940cb50c525031f5390940c714e425032c5290940c7d4c425031c5310940cbd48425025e658c94097196325034f528c940d314a325025e650c94097194325034f520c940d3148325038c420c940d5d4f515035453d4540d9d4b515036452d4540cd90b515033442d4540d58cb515035432d4540d5d4c51503545314540d9d4851503645214540cdd0c51503354314540cd90851503344214540d58c85150354
  | 4 => 0x7189539071e53d0e41c794d43906ac6250e41d394e529074d5394a41cbd92529074f6394a41d318e529072f4394a41cb50e529065f6354a419718d529074e5354a41d354d529074f6354a41d318d529071e5390a41c754e429072e5290a41c794c429071d5310a41cb548429065f658ca4197596329074e528ca41d354a329065f650ca4197594329074e520ca41d3548329078c420ca41a758f419071e53d0641cb94b419063e6510d419798f525065d63d4941cb14a42506b66190941d3d48325074c520c941e3108325069e6390541ab98a415065e63141419758c505063f6550c41ab189431065f63548419718d521072e5210841cb54842106b56110841d3948321074d520c841e3108321069d63d04418fd954110677655044197d8d501065c63540419bd89501066c62540418f98a54cc66f62553319b18954cc6ac6255331c718d54cc72f62553318f18954cc72c62553318b18954cc71d54d0f31c755043cc63f6454b318f19152cc63f6590b318f59642cc63f6510b318f59442cc71e548cb31c755232cc71e540cb31c755032cc74e520cb31e310832cc66e62d52319b58b548c71d63952318f98a548c63c62552319b988548c66d6215231c7952438c71e5450e31b3189438c72e5494a31cb552528c72f6494a31cb192528c74f6394a31d390e528c74d4394a318fd91528c63c6454a31cb951528c72d5454a31cbd91528c72c6454a318fd96428c63d6590a31cb94a428c72d5290a318fd94428c63d6510a31cb948428c72d5210a31c7952328c71d548ca31d394a328c71e540ca31c7550328c74d520ca31e3108328c69d64cc631c7953318c74e52cc6319758e544c66f62551319b189544c67b60551319e181544c65e65d0d3197994434c71d5410d318f993524c63d64d4931cbd48424c72c5210931d314a324c6d6618c931e3108324c69e648c531b398a314c63e64141318f590504c65e63d50319b98b540c66d62d50318f992530c63d6494c3197596430c65f6550c31c7151430c6cc6250c318fd91520c63c6454831cb948420c72d5210831d3948320c74d520c831e3108320c6d5610c8318f992510c63d6494431a7593310c65f654c4319dd95310c63f64540318f191500c66f62540319b189500c65f63553219718d54c865e63153219758c54c863f6454f218f19153c863e6414f218f59053c86ce63d0b21cb99442c872d6510b21cb94c42c872c5310b21e998442c87a56110b21ab99332c878c428cb21e390832c878c420cb21d399432c874d650cb21d395032c874c540cb21f198432c87c5610cb218f99250c863d64943219798e50c865d6394321cb10a50c874c32943219798f548865d63d52219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414
  | 5 => 0x5090ab561d4242a798e5090a9d6394242d314f4250b1f5390942c714e4250aad62d0c42abd894310b1d5310c42a798f4210a9d63d08428fd954210a9f6350842a718d4210a6f6550842b318d4210a5e63944429758e5110a5f63540429718d5010a7761540429d1855010aae62d4c42ad9875310ab561d4c42c754c5310aae6214c42cb98a5210aae6394842ab5865210aae6094842a798f5110a9d63d4442a798e5110a9d6394442cd5445110a9f6354042a718d5010ab76154042ad1855010a9e6314042a758c5010ab66114042ad5845010b2f6255332cb55042ccaad6510b32cb59442ccb2c4254732cb10a50cca7661152329d584548cb1e5450e32c7d50438ca9e64cca32a7593328ca3f64546328f191518ca3e64942328f592508cace62d5232c7d52548cace6215232b5984548cad56115232e3988428cb575194632a7d91518ca9c6454632a7990518ca9d6414632a7993508ca9d64d4232b5987508cad561d4232a7992508ca9d64942328f992544ca5d639513297d8d544ca6f62551328f994544ca3e65909328f994424cb2c54cc932c7d52324cb1c548c9329d987540ca7561d50328f992530ca3d6494c3297596430cacd6290c32c7151430cacf6250c3297594430cb1d5410c32b358f420caae62908329b594420cb8f4310832e390c420cb8d4310832e310c420cb2e6510832cb594420cb8e6310832e358c420cb2e5310832a7993320ca9d64cc832e310b320ca5f654c832a7d91320ca9c644c832e3109320ca6f654c832ab191320ca3e64944328f592510cb2c4254432cb10a500ca3f64540328f191500ca7761540329d185500cace62d5032b5987540cad561d5032c7550540cace6215032d398a520cace6494832b3586520cace609483297597420cacd65d0832d3597420cacd61d0832b3983420cace6290832a798a420ca8e6290832c794a420cb8e529083297d95420cb8d4210832a7988420cb8e6210832c7948420cb8e5210832b3d94420cacd6510832b3990420cb8e6410832e3950420cb8d5410832b3584420cace6010832e3d94420cb8e6510832e3594420cb8c6510832e3d84420cb8e6110832e3584420cb8c6110832e3d80420cb8e6010832e3580420cb8c6010832a7993510ca9d64d4432e310b510ca9e6494432a7592510cb8c4294432e3109510cb8c4214432d5544510cb8c42d4032e310a500ca9f6454032a7191500cb8c4254032b5d85500cad46154032a7990500ca9d6414032e3108500cad66114032b5584500ca5e6294f419bd8953d066c6254f41b318953d074f6254f419718953d074c6254f419318953d071d5390f41c754c43d065f6354b419718d52d071e5390b41c754e42d071e5310b41c754c42d072e5210b4197d9632d065d658cb4197d9432d065d650cb41e310832d065e6294e419
  | 6 => 0x7a149eb80027605a8a50a00000a403c9570e309982f09401e8000e80c68a08449b517a8dd9558f68a80001de2532710f11649678f18000002668a91aaa1a2980cd0001d329114c8000000791781ab85d00020f096a030290001070bc1320ba2429f8a658d4000219038a6986405104f9c59b211aa5e9f021617612098c8c08580001e29689cd8b21a380018e0001b703612fa8c8000001230000b324c093a3d85f9f4a74060800185268a7c1db93b29495798411281b8090000ab9df16c00b80000000c000020000480080101c04c00800004008020010080001780100a0100180000405c00001024008008030100e8000030080180100000605c0100201e0140182600e01400000002000008000000001480202a0440101400a00c0180206000024001018000108080000200000300600000802004010000020020080180102a0000280100c004018010000000002602e008000030020000081101a0300281c00a00405815008028058000040140000000a00c040040020d800096004014138090040440c00600a0000001500c0040000202000c1300100004c0180300a0080901700c0482180300e00c0280001a00c000060000380000301e00801002010010000020000180000b04e010000000060080002b00801402815006004000040080ec00009012000008080160780d8000160200000604a038000000140280100a000000000070580100085000e09c0480009400c07002012020018050080100300604405801000008000008010080000201a052064048000040140500000400c0000502e0000181101800001001020004000050020000980d00002c000030060040100a024020000050080340001500002c0200e0000280700000600c0005900c000038020040101680200c00c0080001601000828000018018210060080001802a0380787000001c0f80100805c03006006030020020000282280800000005815026010080040000180c806020034008060000000f01102e000018020020380100000404c01002026018050080040000001900200c0180d00400003809024000010000000100280001808c0b8030080200d0030000380381b01a00c0780000601c00038cbd905250f4f6314943d3d0c5250f2e4314943a75924310e3f6550c43ab1894310e5f6550c43b31894310e9f6550c43c7d954310f8f6250c43a71894310f8c6250c43a31894310e9f6150c43a71814310f1d4394843c750e5110e6e62944439b58a5110f1d43540439bd895010e6c62540439dd855010e746154043d3d8953d0b1e5350e42a798f4290a9d63d0a4297d8d5190a5c63546429798e5090a5d6394242ab98b5390b1f5394e42ab9885390ab66114e42ad5845390b375194642a7d8d5190a9c6354642a798c5190a9d6314642a798f5090a9d63d4242ad987
  | 7 => 0x1a612e80028900000004380023498780024d852a4785497121d9e41b291693aa972951bf8429790fe0d88d9140a10a2509d8e012b9460ef8000cb80028da0a9c08d72551c31cb1ad9200e4a540d5800000000000000191117a8e8f7a3910b00006108ba1f8000001c50001729bf041000236a6180007f0af95199d9ca10a800206a3e04f19e0711e00cf1f301f8000da8a117329b9680518531108c88ada1d024a0c033a5282110a08d99d0ee89b0f60000001a80000000000818000001df8000002330001dd0000c005516917b85380d0001d780014e86e95a8061069be1ac8c2178a769590000000320d8179a9c98c006a9190c8f380022922c04692e0000dba2404a91809300000004200018d92a9771da00998f00020100b1e3129a3009b90491b1e59e11978000000002209a200000008c9c79d080000013e1d997f9870bd8e7946990a12944a9d0ad0cd8ed1ffa538d291d0000000000f32720001e600026100000000320a17f0000d087f85619529927b13ba09a99a5225487e11993f0e981a1b197226aa2a0501cfa411839598000761609d91e499008d06584591c0489348eb0a3a9b0318bca071eda938ef2799e19f999f800156800250a41a8f9c20750b59d39381a50758958002000a79c02931e8a4b0a2a0094f26ea2f832977a8484ca6400000000a9d40310000ff23ea279ef8c50569890ff8ec1ff0748002780a68ca0001a01a49d59240e509ca51a0e8910f50180b9a8f1c70478919d48161b316d84918b0df1e0a1a8fb9c48002510002880000001930002600a18b88001e7a360b10288302599d88d49ba01487a11ba0910e1f1026a3a1388001510d523110b85795e97da2180009f81ca138001ce8000000001f802500014c22103d04a000212000223a7d80014895393a0000af0660b426e0202889c626786e00000e8000000002908261a32171170000368128e29bc03912d29000d8c99d28dc9aea2f0cb08f99f0000000002111699ad2481a99e69d20441a903f20ca0515882d1050000001532420e41db21c1459a095f1dc8d300c9b48f423f8e71e20c305580f1cb82298f8698de235902114a018001228df8001ac2049bd8340002220be0851271caa1f0000002859c418120810600024f81d9610880d196f26da7504b0a20a600013d0cc1341c8a4a82190116a8b699a11e0ca90419b0e107e9800888520950051d712a08483d9ea10da181fe8001b39c2800192879870a7b89a0002898000f90fc9c38aa08c1999a880010c14b99b9130000000000fa97696325900012d8809261418b623419e956070195a0380000002a12185c02a8509f192522980000017428a15f96b0d38ee0000ba993a5c8c61b5a2ea57a729ea9fc247171a5c20424381923283e0591b0a7d1b12771bea8095c1b4027a3513194207
  | 8 => 0x9a8002961a41b81701d000223191180000009727f90f8000649a7981a200000ac01986916f8bba8d22313d80000000021300016ea8297e0d622d2322488dd20da96a60800163a7184000009e128266071913a759e515c9668002100c80000619cd08606c928a2d9492920e19c906aa08801a4b8081f609f0841f686683a25a162063a7f0772571a12288f088e9fd03b965a389a5a651480ac80003801f1f297a008800072a9a18a14784c083a4680123d0000120189bb25b8bf16c99491400007d8000000000000000000c58630330a49cf1f580013900006f1b018890980021405b1a68141f41f71ab28688321680395213386a26495b28e05e937139a958000d014f98d00c22c84da8ba272248c70e083782992382717b13291f0170bb06898829a9aa04d0a893f86c0001661849fa9c6a2608219700003720e01c08aa2a9fda4413580012b0002460f58fe811a6d1e8067a779451000fd0b49da9b626f8b716503a9eb08f00013515d897a7c889a449fc94a0100000000d691f8e919424e1b6a1b9161c11080890fc2060000000eb9fa00013c0b905a12c9af95b82b86d000000183000040a5594d9ee80019895d0b3804a6c1f08b501100027887c80029c0c383f84e03b0780db1379bd0921c82378f80450000868042430b79cc80000021881680018ea5f8001918540f28002630000001e99c189280002207427a8001868001090000f98398eca1e9b8800000273a840bd0000000000000000ae000000108a7ea3b10d12797e96d01a8000000ea9860801ce105a8c00002b2409110b00a30cc82080a00005e173a7028222800008e06280006ba4989889c267103a8390f29400000008580002810310ea6380018ba2e06023086b1ec8001471ef0002338001a720b06f89600009d0002878000f88b0a5017d126a1b00023c00020d0000a7182a490de8e88431498a59f919c1541dd91e84ba19a5894400019800019c8f01f394a8a9a692118c426c8ed8fa24d07d0000c7a4ca9d996a8b29288b0721310178990b180021e000082a1521580000003500020580001e15a0001822681bb8001859259a29de9551f20588fb1300e598a80014302e28aa5f1640bf8028001ec0000cf8000da245a5d1151750359f51dc2850ce80025d81522b9ee1962580f228607c000118a870001428d79898d11ed20227496186802c8c4a2299a810a3aa79160090a819b91368670c182c23820f80580e07b297a2b05c99911c8aa8e688a087912175a7a05b9a1a451d10b802312482fa6a0b2a3b80f94e0fd93ea0ba0795497484e930a39859a629f78be82396e11586200017c8ce01324ea810000738c11079e383e80004713616a05726b08123f06d8000d200011a11915e1290001330001e909e8c2a0290197c0001920f480013c87328303496b8ab1fb800180800
  | 9 => 0x15811d82da7081d000152807900a5b0dc00085da5680025e0c90001100460e380000000002e89480000000012124a24f00704807aa370f714387b8e22400309b99b78001400240651cc12201380027e0499501e71c98000982258ea1d828000001b1508e61ae25a85f12c1d1815a269fe0901af21ca179709baa561629d60002989d68000788000870000ae8000d9a731fb041a6f12f0000001d500b94d14123c9bc90282583c26b96714b0768002620
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x98d0c7255232cc686392a81966343dd4420cb31a18e4b1ca918e0e54189438c686392a819463431d1520ca31a1aea2106518c8c72593318c60ebb4a998c638359252cc631a18e4aa08698d1870550434c616392c828263831506250c31a18e8a906418e8442584320c646392c998863431cd6510b21a18e8b286590e0e6310a50c87073206528643439ce5310921a54e12988490e0e6510a32486873ac8419243439d2540c921a94e12a06490f085310b50487842a065a8243c210832d4121a54ea210a090f0b5310850487842988428243529d43214121e16a8190a090f08540c850486a539e8428243589c74214121a54e9990a090d6271cc850487842146428243c29083214121e1084190a090f2042c8450487a019642282434a9d22114121a94e7108a090c4c7258e5408616392c929843a89086048421d84643024210d0c7354842d0246392c7a0e81139cb6354640c18a631286a050e72d4c425028739ea42128183994420c940e0884196a2a05247250c51503822106428a81231c963d0540c1ac629682a0615631474150307ba0c4a9881831d06254c40a18e4a9c862050c7254c4310286392a721081431c95310840c1eca210642050c7254e4110306a9cc520881431c95310440a18e4a9e802050c7254d4010306a98c4a00818554c6150040c18a8312879850c7454832cc246392c998e61439cb5410e3085ce5b22a31850c7258c544c3062a0c4a1a61439cb540c930a1ce9a90649850e75108324c38221065a8a61511c94314530e0884190a29848c72593314c20ebb0a998a618359052cc530c2ac828e629860c63189540c307b98c4aa061831cc6255030a18e4aa6861850c72550430c286392a919061431c9540c830a1eea210641841f76552310c286392a91886183552628c430a18e4aa0621850c72553300c20e3b2a898061431c9544c030c1aa8312601861554185300c286390a819241439d4420c920c1cca2106490704420cb51483822106428a418a1506048520c90a6302429050c735944208216bb0a621041495c45310820b40e2b00841050c745943208226bb0a819041515c4540c820b80e2b00641060c63109510830632064a88418398c4294020c1cc8194a01044c7258e54c4216392c929e21431cd5210b10a18e8a90658844c7258c5484216392c829c21439cf5210a10a1ce9a90650860e6498f5244306320c629221439cb5310910a1ce7a90848850e72d5032442873a6a419221439d4420c910a18ea210648860e6510832443063288419221831906394810c18c831aa408628641815204324318c0a9021981846054810a18e4a98840850c735484204286392a819021431d1520c810a1eea210640850d751083204307b28841902183594420c810a4aea2164208545750cb2104314b288410021925943208010
  | 1 => 0x112001f83cd00027040000000001badc22abc308b001b4c47f000d000005880128a9040000000220b0000031800a20000160a000001acaa002b00000000000000000000000000000042000001c00a25e0000093000000000001293c00000009ac96580da83a000580000000f8002925a15c0260000000bd41001a48d0329c266044001a6382d0516415000687a0000000d4000000000003f00064000000084bb00204bcbe7094d3a97059b050b800a7c6e044d0003e8e279c8e6006211c000056a5400001800000003806400000030cee0013834ca0000000006706091202b0100054000032876003d1a558b046001220038a1136c55f8e436806a875989c0000168833d800faa8003000000000000000000018e0000000000071364de00001d4000000000000e5000000003ca840a00003200074688bc86ae2a26400000000146610000000220000000005cb405a0a1195d8c595a80000005b3399e0060918beba0000000a50000000000f258ba00261706a5b101b82ea655a1ccc000033400000000000006ba6000da1b00066df4300092000480000000000080b30036dbc4800149140020b60f076003582431002a924640023d84a4000004ab73e0f05c110e002040100c08010200004010100400010280402030100c080200000000000004160b0002c0400010100201000001a000181c0c03000040404028000800000240000000080201010180a270000c140003800020608d2671d905250ea338ec62928783d946250c43c1eea3128621d0c7250e5210e8639287288878350e6294443a18e4a1aa021e0d431895010f0aa18c2a8087439cb5394e42918e6b0ca42148e739825210a87396a92a465835944310832a4ae3328841948c74586520ca473a4c129065315c76510832b0ce3b28841958571d94420cac338cca21065615c66510832c1aca328841950d75984420cb42b08c22106543dd56010832b0ee2b00841958471580420cac3388c021065615c4601083291aec214a21970442544510ca473b084a8065a110b6154032d088430aa01968442984500cb42212c22806583dd06254f41c18e8312a7a0d0c7254e43d0686392a621e83431c95390b41a18e4a9885a0e0f6510832d0707298c4a1c83431c95310a41a18e6a908520e0d651083290646392c7a0c838358e52d0641898e4b18a0a0d0c7354842106c2b888419083231c963d0441c18c6312a998e0f7318954cc706398c4aa663431c954d0f31a18e4aa087
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x3069008073340a284005a0802440a0681dd46250c43a048250c6154043a0681dd06254f41a0681dcc625533180c8759252cc631a048258c51d0540a0681dd06254c40a048254c615004080c8759052cc530a048259051cc530a0681dcc625503080c87552628c43080c87550624c030a0482550614c030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
  | 2 => 14
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
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (802+((h/14+packedAt s3K6 (704+(h % 14)*7) 7) % 69)*7) 7
  | 5 => packedAt s3K5 (27286+((h/296+packedAt s3K5 (24030+(h % 296)*11) 11) % 1890)*11) 11
  | 4 => packedAt s3K4 (55826+((h/446+packedAt s3K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s3K3 (11798+((h/75+packedAt s3K3 (11123+(h % 75)*9) 9) % 399)*9) 9
  | 2 => packedAt s3K2 (860+((h/4+packedAt s3K2 (840+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffff81ffffffffffffff0fffff
  | 1 => 0xfff03fff81fffffffe07fe07ff03fffff38e3f
  | 2 => 0xfffc07ffe03f80ffff83ff81ffc0f80fcf3cc
  | 4 => 0xf000007ffffc000fffffc0001ffff000ff03f0
  | 5 => 0xffffff800000000fffffffffe0000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x121105109048920200594a8a254510aa0534d5
  | 1 => 0xa4a48a290c912545960294454a22ad54728a2a
  | 2 => 0x88c2934a243a4159aaa8275113a88e06b8d34c
  | 4 => 0xce8b2c744920766ecd34c1861cf3c418df03b0
  | 5 => 0xf0c307871c3878f71c739e780c30860efec00
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xe8e8a8a8a8a88888e8e8a8a8a8a88888e8e8a8a8a8a88888e8e8a8a8a8a88888e8e8a8a8a8a88888e8e8a8a8a8a88888e8e8a8a8a8a88888e8e8a8a8a8a88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37375
namespace PEqualNP.Outside.L_meta_37375
open PEqualNP.Outside.L_meta_37375.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000005a1011d5898d95063002e1c0120d52691a51071380321c03160004aa0050585000000a226000042780014000780505979300889100000000005cf80560204602060031202240001600100ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1fc040a29800f87a48088a2192a800b8984a134e614000f41c37150240000448804800461844a38340f0be5b0d8212e4c4f81ce29d39054f680488113223230a464000000058574987c306900000dc441aa0c003b25000005a2902d387702a38220f2a1a90e63018005678518b89c003580000000023d3666000c400000000082591a1e4908d4a9142e4242268606700214b02f068007e5d50140264038000927d3a2084e3e10994247514005447e238cd143636068006f1d0707264440583c1d27a7800432f28524062b0304c6225a0400003b290202d00181160036a590c00000082851f048182040584008b90010196071a0505828200838100020600030680038115818080010a8100019e81810001050004000b804f94b439ea8e873e50d0e7aa921dbd4943b6292879f5350f5ea4a1cf14943d6292872c5250e7ea2a1cf141439f2a0875e53d0abaa7a14f54e429f294853d5190a7ca12157d4d42ae29a853d5310a7ca4216b948429ea88853e5010a7ca9994f55332d6216653f548ca78a91967d0e32cea1c659f548cb38a9195794a32cf214659c428ca7ea8994f151329f2a0653d540cb3e86196750c32d6210659e540cb3aa8195794832e729065cf420cb3c84196710832e6210658c420cabca7a0d754f41cf29e833d53d073aa7a0c754f419f296839e32d073865a0cf943419eaa4833f5350678a4a0e78c941ce19283b75150678a0a0cf950419f2a6633d54cc67ca918cf55231cea1c636e528c6daa518cf951319eaa2633e540c67aa818e750c319faa6433c54c87986590cf952219eaa4435e53886baa710cfd51219e2a2435f53486b8a690f30c921bda824378504867ca810cf550219ea9c813e529033c6520670ca409ea8c813e50902bca6205754c40cf298813d531033aa6204754c409f290819e321033864204f544409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f550309f2a6413d54c827ca9104f55220af29c415d538839865104fd51209e2a2415f53482b8a6905dd4520ba28a413f5408278a810730c8209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x4d9b04600590121542700002191e346150ed148364456a5047801a72012003e2002a3ab0bb60001594000003a2c6c000000100600e071c1488018000090000c57004c840806e000000001abb5e10081810404600040000306041000238000c3d4c5250f0f631494387d8d5190a1d63942428d584548ca8e62d5232a3988548ca9561152328b594420ca8e6290832a3d94420ca8d6510832a3584420ca8e60108329318953d062c6254f41a318953d070f6254f418718953d070c6254f418318953d061f658cb418759432d070c520c9418758c505068c6250e31c350e528c61d63951318b189544c6386055131a3189430c61d6315321c315032c870c540c921d20c8504861d6395021c3948329021f635464093189531022c6254c40a3189531030f6254c4087189531030c6254c4083189531021f658c84087594321028c6250f308b98b548c21c6550d30a3189434c30d4314930c550c514c21d6395320c3950328821d63150208d584540830c540c8208758e54c421d6315210
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x3080129100180e9001c68338ec629287215c76510832818e4b18a0a0c0c7258e5408607396c6a8c81411c9431453081aec2a06410505711503208206392c72a621031c96315210
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => packedAt s4K5 (912+((h/16+packedAt s4K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s4K4 (4895+((h/55+packedAt s4K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 1 => 0xf03ffffe07ffffffe07fe07fffc1ffffce3e3f
  | 2 => 0xffc07ffff80fe07fff83ff81fffe0f01f3cfcc
  | 3 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1105108c412248100594a8a25012915414d0d5
  | 1 => 0x248a29103244942960294454a6412aa8ca262a
  | 2 => 0x42934a2490e904caaa8275113aa40c0d634b4c
  | 3 => 0xb2c74492481d974d34c1861cd39c031bc0db0
  | 5 => 0x8c307871c70e1e7f1c739e780e3188c1ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xe8a8e8a8e888e888e8a8e8a8e888e888e8a8e8a8e888e888e8a8e8a8e888e888e8a8e8a8e888e888e8a8e8a8e888e888e8a8e8a8e888e888e8a8e8a8e888e888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37375
namespace PEqualNP.Outside.L_meta_37375
open PEqualNP.Outside.L_meta_37375.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x248060a30a000302380071658000268489b34001064e00ba91e10a2a4c54e803c711900a215804a25200007cc8d4404001608968005f040042ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x881be501027ca0206e94040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730dfa0e61bd41cc3be6398774c730df20661bc40cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c61bf418c37a8318778c630ee18c617e508c37c81186f10230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4987bd4930b7a92617c524c3d8a4985b14930bfa8a61f7514c2eea2985f14530fa28a6174514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea9061de320c3b864185f94430bea8861bf410c37a8218778c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c837e83906f50720f790e41ed21c837c81906f10320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef32883d865105f94620bea8c41bf418837a83107b88620f610c417e508837c81106f10220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53482fea2907dd4520bba8a417c51483e8a2905d14520dfa0a41bd41483de42907b48520df20241bc40483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef32083d864105f94420bea8841bf410837a82107b88420f6108417e500837c80106f10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c437c81886f10310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21bf418437a83087dcc610fa18c21f721843e843085f94210df20421bc40843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd414437c80886f10110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2086fd0410dea0821f731043e862087dc8410fa108217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xe435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef19663dc32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31f7294636e528c6faa518fb54a31b6a94637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7bc6498f70c931dfa0a63bd414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87de6590fb0cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53887bca710d794e21bea9c43dd53886baa710df14e21bea94437e518877e8310ef50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f799243ec324877e8290ef50521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf290437e510877e8210ef50421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40bf296817d52d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c817e509037e81207ed0240dfa9c81be539037aa7206f14e40dfa9481be529037aa5206f14a40df99481be329037a65206f0ca40dfa8c81be519037aa3204f54640de28c81bf319037c63206f4c640de18c81bf219037c43206f48640de10c813e50902fea6a05f14d40bfa92817c52502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53102faa6206fd0c40df21881bd431037886205f94840bea9081bf421037c84206f50840de210817e51102faa2206fd0440df20881bd411037882205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28881bf311037c62206f4c440de18881bf211037c42206f48440de10
  | 2 => 0x24c15f2b40080007faf513c56d0a2d06349b40000029650c0000009c5388b0e561e00009810038000100801002010000786a03002000f400028020380087c0400200806000040081401800010140080e0000021034008000200a09824018080102a0083c00800020000d0020200003808030000100015000060020100207004008020100201000000000581c0000800010060a002806030040180c0200800008088060080205004058020181e118000b8140d80e000040080a0181e00818000061200c11818008000080a0a0020d020020000100a008100003c008060c0120000a030940082c03804000222282a00000008300001200800028020202402006000220300603802028581c80c000141481a00802000061801e008260e8120000e0102e0383e010741505e00002000020f8000200014800128b21e0520001017808008020481e0081000044018000a800000000781e01030098000089001052000000080e028060101a00800008000f80602df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250fdea4a1dbd4943be29287ec5250ed8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855f5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997bd0b32f6216657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cbbe86197710c32bf29065ef420cbd8841977cc832f719065dd320cbda6419734c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83b
  | 3 => 0xde38c4e2195a46bcd42175aa0c4291670522111783e34a5a523aef0761c8cc28b2ba2d4ffa8e172000500de30e45c041966206ec302b9032ac00027e0a22018a2200000000000058a0013b911000238000f4272000001571107d4ae30a28c198d903018eacc7f1e72280015d2260061e4d49bc000000001cb0504007e978098c0d8e8a60002d02b26c2909f135964114795029c45587756594d5aca997723c640b7c619b344a0052c8445e4c39150485e273c7cb0c2be9b87d8bc2cc404c623162402c6725e1c869d4e234000669702330f0ab43b2123fc749280f60003406931527826d54aea15aa78921c54e6aa97406e528a0d001895dab450e1e61c2c05258a547a2fd0d2e75d29614da040ae2ec21073146260f522d05cb20dc82c0c80dc2023e048aac4a28838e2657800c6326c4002bf3366f5708000ca12d8b24508e089060000748b0f82dc5b495d650002ea000249910461703e000208000000ac000164002013d60000d2955261c4630875642f43badb000a080019929e000000cb5b05c00d9ec3e4000000000005892e00000000086242000208000000000002ea710001ec0000002a0000010f3da7e8001e25024717610907a17d6ba7658c585261ab11a5c40012e0000009dae23b86044e8464123b88103260ebe0000001f42c00001c0a64e09a19420e2ac0008519ac5c001631f084cef29052400006a8d50c5111d25a43ec2d30965230c2467912000000000ea0c42dd251a62103d4b92210005688d8b62e6545321355e6988490003c63b4ec15e0005b5071b70005e8c69e123a5f8ef9b509e51c4813e5c839d660004cc745822f65445f01528f4a29a1450a70007c4549ef3064898c22b1de8c86e0c14be4d8000630008d4bd8004fab8c000001e60002a8af17446857000000000001421267a5488d325854d5b9312163641a1030b6001350001d8828000000002558e07d29482d5b00a000a58c000020a9196f1c3000000158963925ad1dafc37c2a8b782d1804fc9b8001ae6d17d8004f68e54fa37446a24002fd53a48537a02636000000e254a0006a8003aa6d8002bd3e6ac4ed2981b06893f80000074c2a0005426080b000000000000000fc498250000000000019d0f4001302380000d93901f45c9a43624e2662c448b025f200000000000000000004a841822b1e0004bd2793a000b05639ee38c8d8109452f2678700ca63e4b4102c3320ad5068673900250c0db1d6000d02a457801c2c1ac07096d26a0f43c019380b2000845180000d6948d220343aa8c2d1f700a530ba1c035c1340012904c44cca96c220141462d42826157a27a000620a018b54e1a8dc0000008fcfe26540c4f46b0f21ee3997329938427c00000000000b51232ecc180000040e790c31ca00063c540da00043400156480bdccf9f6000b08000894f
  | 4 => 0x32e62800313000b24bf9e84ba638e60753b69218280061a00142984192048fc8d40825557281106a03ce81e01be2ccea0142fa094c99d93541fc3400003a8a08a91e35a560fd869142580872eb5a60414baff42a04d0d80055022c958270044952b1500000015d9273fa3c1620c45fc6e8aa2873242f84d1d74aa5b8000830863f16ea67000078001194441794d17701c8a44b8394880005c0a2580230002491025a00b8002540015c308214308df9cd0005248f8a459e89d121c12b23753c2800e898d801d6190344748180c27e000274000000788864a6b38d82a007ea109419c346be90b06d4eaabc9008f4863316ca08482684e70c53e8b35889321d05481987055c0bc1e210
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc404831c5310120cdd4440483345110120d314e204836451881209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209b594320834d530c8208f992510823d6494420cd94541083355150420ae181410826d6588420b398e210826f6548020b318d20082e461480209ed95200823e64d4f108f59353c426e62d4f109b58b53c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c433561d5210ce98354843356115210ce980548423e6494e108f592538423f6454e108f191538426f6254e109b189538423e6494a108f592528423f6454a108f191528425f6354a109718d52842ba60d0610ae18141842b56190210ad584408423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414423e6590110c7d4e404431c5390110cbd4a404432c52901108f994404431f5310110c714c404432f5210110cb14840443545384110d914a104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d5185530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520423e64944108f592510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410435553cc4109d594310436552c84109d594210423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400427965840109dd9510042d46344010b918910043b040440109ed9510043b34144010
  | 1 => 0x2ba60d4440a798c511029d6314440ab98851102ad6214440ae980511023e658c4408f59631102ae628c440ab58a3110335518c440cd54531102bb604c440ae181311023e650c4408f594311023e65884408f596211029e6388440a758e21103355188440cd54521102bb6048440ae181211023e65084408f594211033a60940408f58654cc23f61553308f99251cc23d64947309b98a51cc26d62947308fd9741cc23d65d07308fd9541cc23d6550730ae18141cc26e62d52309b58b548c23e6494a308f592528c23e64946308f592518c2ce628c6308f587544c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c23d6115130cbd53524c32c54d4930cbd50524c32c5414930cdd53514c33454d4530d9d4b514c36452d4530cdd93514c33464d45308f990514c23d6414530cdd50514c3345414530d9d48514c3645214530cd990514c33564145308f997414c23c65d0530cbd4b414c32c52d0530cdd47414c33451d05308f995414c23c6550530cbd49414c32c5250530cdd45414c334515053097997314c34c52cc530d5147314c34c524c530d5145314c23e6590130cbd4a404c32c5290130cdd46404c33451901308f994404c32f5210130cb148404c3375110130cd144404c34c528c130d5146304c26e62150309b588540c27661150309d584540c23e6494c308f592530c23f64548308f191520c34d520c8308f992510c23d6494430cd945410c3355150430ae181410c25d658c430b398a310c25f654c030b3189300c2d4614c0309ed95300c23d61953208fd8554c823e64d4f208f59353c827661d4f209d58753c823e6414f208f59053c823e64947208f59251c825e63947209758e51c823f65d07208f59741c823f65507208f59541c82b860507209798f548825d63d52208f993538823d64d4e208f992538823d6494e20d3d4c328823e64946208f59251882ce63886208f587544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6115120c7d53534831c54d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f191534826f6254d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f514833764d4520cd193514823e64145208f59051483375414520cd15051483575314520d514c51483366414520cd590514823e65d05208f197414831f53d0520c714f414833751d0520cd147414823e65505208f195414831f5350520c714d41483375150520cd145414826e65c8520d314f214836451c8520d314d214836451485208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4
  | 2 => 0x5214941ad98732506b561cc941ad98632506b5618c9418fd95325063c654c9418f994325063d650c941e34c8325069f6354141a718d50506af6254141ab189505063f65504419dd95411073654504419b98854cc66d62153318fd9152cc63c6454b31d354832cc63f64543318f19150cc66e62d52319b58b548c63e60952318f181548c66e62152319b588548c72e5494a31cb552528c72e5454a31cb551528c72e52d0631cb54b418c72e5250631cb549418c74e52cc6318fd91508c63c64542319bd89544c66c62551319ed81544c67860551318f990524c63d6414931b5986324c6ce628c5318f993504c63d64d41318f596540c63e60950318f181540c63e64150318f992510c63d64944318f597410c63f655043197d95310c795414c4319dd95310c63f64540318f191500c66f62540319b189500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c874d530cb218fd9150c863c64543219798f548865d63d52218f982548863c60552219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e21c794f418871d53d0621c794d418871d5350621d394f218863f64542218f191508865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e6414d218f590534866e65cc921b9987324874d530c921b398e214863e64d41218f593504863d65950218f982540863c60550218f990540863e64d4c218f593530866e62d4c218f990530863d6414c219e98053086796014c218f992510863d64944219798e510865d63944218f597410863f65504219bd9521087a541484219dd95210863f64540218f191500865f63540219718d500873551d0740c794d43902af6250e40ab189439029f6350a40a718d429032e5250a40cd54541902ae62d4e40ab58b53902ba60d4e40c7d4e53902ba6014e40a798f529029d63d4a40ae983529032f5294a40ae980529023f654ca408f195329023e650ca408f594329038d320ca40ae983519029e6314640a758c51902ae6214640ab58851902ba60146408f996319023d658c640ab98a31902ad628c6408f994319023d650c6408f996219023d6588640a798e219029d63886408f994219023d65086408f997415033751505409bd89531026c6254c40abd8943102ac6250c40c754c431025f63548409718d521029f6350840a718d421032d5210840cd547411023d65904408fd95401027b6550040ae98353102af6254c40ab189531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae98053102ba60d4840a7d8d521029c6354840a798c521029d6314840cb54852102b66114840ad58452102ba60148408fd95321023c654c8408f994321023d650c840e34c8321
  | 3 => 0x51cb57c568002e60006b8d309e5049c0611f44b0000001ba32400000002002006010020020020340f0000040080100000602c010000000080f0000020180080a00000006000000008020010160040200900a008010050160340f0090080000600102200c0280101404c008020000000080100400c1981d000054018180040080280e00a01400800030000078080000740101b002064038180000200000300402c0080004a000078020000240f0080080080080402402c088060380000083600200401002000008040030000d0008000000d8010030040001d8000080a00480001a0b0068000000040780e000000070020040000380203800c020310000300001a0120000c80000000c0000703c01000018026028000020060040000000401c0000100000802801030000000000000100000500001c0000401400002000028004008030000000180100c0040000101e00000800002008018000000000000102603c0380400402001001006078008080000040000300a04808000004010000000180634f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3e64947328f59251cca3f64543328f19150cca7661152329d584548ca3e64946328f592518ca3f64542328f191508ca3d61d51328f983544ca3e649513297d8d544ca6f62551328f994544ca3d61151328f980544cb2c54cc932c7152324ca3e64145328f590514ca3e64d41328f593504ca3d65950328f586540ca3e6095032c718d540cb2c62550328fd85540ca3c60550328f990540cb1d54d0c3297594430cacd6210c32cb553420cb8f43d08329b594420cacd6310832e310c420cacd638c83297d95320ca9c644c8329bd95320caac644c832b3d95320cb4f654c832e3d91320cace644c832b3191320cb8c644c832a3191320cb8e544c832e3551320cacf614c832b3181320ca3e64944328f592510ca3f64540328f191500ca7761540329d185500ca6f6254f419b18953d06af6250f41ab18943d071d5310f4197d8d52d065c6354b41a7d8d42d069c6350b41cb54842d06b561d4f41abd8953d06ac6254f41c754c53d06ae6214f41ab58853d06b56114f41ad58752d069f6354b41a718d52d069e6314b41a758c52d072d5214b41ad58452d063f654cb418f19532d063e650cb418f59432d078d320cb41a798f50d069d63d4341ab98b50d06ad62d4341c714d43506af6250d41ab189435069f6350941a718d425072c5250941ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506b56194941a7d8d525069c6354941add8552506bb6054941ae181525072d
  | 4 => 0xbc0010a1fe1955e9a501069c000540009b8d8afc5ca6693a830304515369cf0f20010690f39c000000000000004a21d2febc8000bc000000000000004b8002eb59a000000000008e0000000001b57f090156485328003fc6053a2fb0008c0001be1ba354b5a0b592001118005ba2b8c503746c0f80024852039d2ba7b000594002685d258c000d04640015521b4a866cac832318900772610325f0002fd2067585c1c73e0000000002f00953b00031080c000002fc0015d0000005700900000074582800000000ce0004727ec2e87e0a40000004927caf000000000b280000000075000000000000000005ac1d8002433304f00020e28c35c10800000000000c70f8bcd2e00040463c22acb0001a57120023aa01390d93d0684f99bc000230421c00003f0932f80886ed150002a27715ba25000000000000be3e4001cc0003a400000000390470740269f0000005300bc9d905456000000001bebb4002a60ee5380016c000a654f2ee09058477934000a04a81180000000003626a0007800009a7dd6890b00000047a372006e048800512000000000000016c0412bc000560e61ea480c8823550810742ef0125818300053600000000000200842df0b4b3c012c4074635290004ba87d351ef0008841c8ba0003d8f5a495b272079a121986b11d1830006c80012c0009e40000006844d4b1f908e0449686604cb4cef84a000a1d1002d604038002bb0dc4dc9c8152da000ca922000998000000002b400102382000a9a44284b9d5f9165bc99025ab2040b40410a822e3257085c2a828cb3a712aa2551a2785062e40d06c3fe018d5adb2ac9148a06a02e2c07b8e02743345509c10e2bd1708338c67c062463a600cbaab54fe5ec388c52e81a180a3d00e8640000025e001851012246cc0e87f2cc27c5f1441626002d80024e7b000000522058631da218c00001a053a5dc1e16826032c339ed4b6a4c9f92a3aa439581720eabe9029a24ac909450003ea02cce8640005a4cb8001b6000002603b6000618580e60fcb987d000b908d83d0084e1602104180047d03b0847416bab65846a800207264b48d68d4612a88bd2e8000bd0e69e41d6000001a4414531608ce3164d8609d21a22943d9060009e9588004629a4440003ce001130000002d8d780049a00000000430b50000000000000025a0000000000011a000001c2466070000245b40000012b29ea488225f292000000000c6000afa3f000000e20004489b08e00f2967784d8a1000000f12511e20c4000001e85d94b800606ab8002636081bc651e337e4542aaff3f047c718bb3320e17830b26225c35b0810c33c99a9f49c83d2a91e03c818868002b610c5327d30e1187ea354bcc31461931a44950a10749800100aa14440014304c30ca5000000000a711415743c760391e95983201615833c050
  | 5 => 0xa0650708004226d4e1af6000000dc8da00aa10000003b2964538003f8638da2173128f983a7e22284c0005701a001548000bca911609d0007743002a17e784a921a0006596280000000133a732de3a84903305c8b4001a3000a3d5c0003ca09c409240f406d0e0dc572281310004d65345a8292fa3e1632950002900000042ca80002853945897b856168000000005d85b91d828000929539841880004d0960000000c2f90f06a0b504009e4a0b8129000a2c762ac3e2b54fe9b72867e8311b62c8a388d000044359519f22322892988b5b8a69041d71802dcb88d845e228000ed2122a556800000224f30100006c0f5000000780a3a8842a214aeab33923ecf72c3280378a405317aaac30ac70566a44c9855d4000590703ec24c0028d2f200123859220000c80005c0824272f1000000a0aaf1fc2cc002f549e714710000009dd13ae34a00004c0001e40009e81f00000125800590001670e5478ad0001bd0a20d4001234828a46994a54a9
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2f00880090030c96026d38046707a63000baa0eb423622405b70c359b406c9aa452502b01c2141556745315848000040099a007d08040780004a01705800004001140818624186872c04000c18c6312a81948e74991320ca46b88c899065239c0644c832918ed2a2641948c76551320ca86392a621e83431cd5210b41a18e4a98a7a0e0d5358853d068639aa4296838358d5214b41a18ea99065a0e0d654c832d0706298c4a1a838318c5250941a18e4a98a6a0d187054c535068639aa4292834a1c15214941870e0b2864a0d0c754c832506863a2a419663431d1530cb21a18e8a986490d487054c3248707298c4a1c818318e5250a40a1ce5a9ca72050e73d4a5290287baa6419481431c95310c40a18e6a90842050c7254c5310306a9ac4298818554d6114c40a18e6a90a42060d635485210312a92c2290810d5c4654c840a18ea990642060d654c83210312b12a3188818558d5188440a18e8a90641863151181410c2873a6a619441431d1530c820c62a2302821063161983548430c298c0a0a218a1486050510c2aa6b0880086255258440043483188088021a81884044010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x129a00818885811da544c83280c87595320cb41a048254d6114c40a04835496114840905811d5320c84080c87595320c840
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s5K5 (24297+((h/267+packedAt s5K5 (21627+(h % 267)*10) 10) % 962)*11) 11
  | 4 => packedAt s5K4 (32538+((h/260+packedAt s5K4 (29678+(h % 260)*11) 11) % 1031)*11) 11
  | 3 => packedAt s5K3 (2870+((h/18+packedAt s5K3 (2744+(h % 18)*7) 7) % 68)*7) 7
  | 2 => packedAt s5K2 (366+((h/2+packedAt s5K2 (360+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffff81ffffffe07ffffffff81ffffc7ff1ff
  | 1 => 0xf81ffffe07ffffff81f07c1fffe1ffffa23e3f
  | 2 => 0xffe03ffff80fe0fffe007fe0fffe1e03c3cfcc
  | 3 => 0x3ffffff000ffffff8000ffffe003fc0ff0
  | 4 => 0xffffc000000000ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x882808c4122400016509421280222a80cd0d5
  | 1 => 0x924519103244986580a4291a53215551a2262a
  | 2 => 0x2149aa2490e909aaaa084f489d54181ac34b4c
  | 3 => 0x859634492481d2d34d3d0210e6998063740db0
  | 4 => 0xc6183871c70e1cfc71ce739c07111183fbb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeaa8e888eaa8e888eaa8e888eaa8e888eaa8e888eaa8e888eaa8e888eaa8e888eaa8e888eaa8e888eaa8e888eaa8e888eaa8e888eaa8e888eaa8e888eaa8e888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37375
namespace PEqualNP.Outside.L_meta_37375
open PEqualNP.Outside.L_meta_37375.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xb0040d001af108000f58240000013000150f00c8000000199d005d33e00380223e808800000000002403a687822750000014afc02c6cedb80006c00032b9c005a706310e000166a154b9288c000042801506ac906302002f0204080000604184000010400083091a0c48001ffd5005fe5401ff55005fc5400ffd4c037f5300ff94c03fd5300df54c03fc5300ffd0c03fe4300ff50c03fc4301ffd4807fe52005f94807fd5201ff148077c52017fd0801fe42007f50805fc4200ffcc803fe3200ff4c803fc3201ffd4407fe5101ff54407fc51017fd0401fe41007f50405fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc2101ffd4007fe5001ff54007fc50017fd0001fe40007f50005fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200bdf1951001cf8ca88003ff64440017fb222000efd91100057ec88802bfe64440057f3222000ff59110005fac88802bfc64440057e3222000ef1911001578c88802fff5444015ff2a2200bff55110057f8a888027ff63440137fb1a2000f7d8d10005bec688027fe63440037f31a2009ff58d1004dfac688027fc63440037e31a2009f718d1000db8c688027ff5344013bfa9a2009ff94d1004ffaa6880277d5344013fe29a2009ffd0d1004ffc8688027fd4344013fe21a2000ffd8910005fec488003ef624400177b122000ff98910005fcc488003fd62440017eb122000ff18910005f8c488003ec624400176312200bffd491005ffca4880037e5244017fea92200bff1491005ef8a48802bff4244001ff2122000ff50910057f88488027ff3244013ff1922009ff4c91004ff8648802fff5144009ff28a200bff54510027f8a28802bff4144009ff20a2000ff50510027f88288027ff3144009ff18a2009ff4c510027f86288003ff2144009ff10a2000ff48510027f8428802fff5044017ff282200bff5411005ff8a08802bff4044001ff2022000ff50110057f88088027ff3044013ff1822009ff4c11004ff86088003ff2044001ff1022000ff48110007f84088013ff1044009fd8822000ff84110007ec2088013ff65040097fb282004ff9941001dfcca080137e65040073f3282004ff5941003dfaca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff99010015fcc808013be64040055f3202004ff59010005fac808013bd64040015eb202004ff19010025f8c80801fff540400dff2a02007ff55010037f8a808013ff63040097fb182004ff98c1000dfcc608013de63040036f3182004ff58c1002dfac608013dd63040016eb182004ff18c10025f8c608017ff530400bbfa982005ff94c1002ffaa6080177d530400bfe2982005ffd0c1002ffc8608017fd430400bfe2182004ffd8810025fec408013fe62040017f3102004fb98810005dcc408013fd62040017eb102004fb58810005dac408013fc62040097e3102007ffd481003ffca4080037e520400ffea902007ff1481003ef8a40801bff4204001ff2102000ff50810037f88408017ff320400bff1902005ff4c81002ff86408012fe6104009ffa882004ff94410027faa208013fc5104009ffa082004ff90410027fa8208013fc4104009ff9882004ff8c410027fa6208013fc3104009ff9082000fdc8410027fc4208013fd2104009fe1082004fd08410045fcc00801fff500400fff2802007ff5401003ff8a00801bff4004001ff2002000ff50010037f88008017ff300400bff1802005ff4c01002ff86008003ff2004001ff1002000ff48010007f84008013ff1004009fb8802004ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0x3ec21080297f3004013ffd402009ffca01004ffd5008027fe2804012ffd0020007fc8010003fd4008025fe2004011ffcc02008ffc6010047fd3008023fe1804000ffc8020007de4010003fe2008001fd1004000ff48020007da4010003f92008009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2010bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb262000bf59310027f8c988012fc64c4021ffaa6200fff95310087faa98803ffc54c4009ffb1e2004bfd8f10027fcc788006fe63c4009feb1e200ebf58f10027f8c788012fc63c401dffa9e200edfd4f10077fca78803bfd53c401dbea9e200eff14f10077fe878803bfe43c401dfea1e200eff10f10027fec588012ff62c4009ff3162000bf98b10027fac588002fd62c4009fe3162004bf18b10087fea588043fe52c4001bf2962010ff54b10087f8a5880437c52c401fffa162000ff90b10007fa858803ffc42c401dff996200eff8cb10077fa658803bfc32c4009ffa8e2004ff94710027faa388013fc51c4009ffa0e2004ff90710027fa8388013fc41c4009ff98e2004ff8c710027fa6388013fc31c4009ff90e2004ff88710027fa4388013fc21c4021ffa862010ff94310087faa188043fc50c401fffa062000ff90310007fa818803ffc40c401dff986200eff8c310077fa618803bfc30c4001ff9062000ff88310007fa4188003fc20c401bffb2c200dbfd961006ffccb0800efe658401bfeb2c200dbf5961006ff8cb0800efc6584001ffb242000bfd9210067fcc90800afe6484001feb242000bf59210067f8c90800afc648401bffaa4200cff9521006ffaa908033fc5484011ffb1c2008bfd8e10047fcc708006fe6384011feb1c2008bf58e10047f8c708006fc6384011ffa9c2008dfd4e10047fca708023fd5384011bea9c2008ff14e10047fe8708023fe4384011fea1c2008ff10e10007fec508002ff6284001ff3142000bf98a10007fac508002fd6284001fe3142000bf18a1006ffea508037fe5284001bf294200dff54a1006ff8a5080377c5284019ffa142000ff90a10007fa8508033fc4284011ff9942008ff8ca10047fa6508023fc32840137eb0c200dffd4610027fca308037fd5184009fe28c200cffd0610027fc8308003fd4184009fe20c2008ffcc610027fc6308023fd3184009fe18c2000ffc8610007ee4308013fe2184001fe90c2004ff08610007e84308012fe608401bffa84200dff9421006ffaa108037fc5084019ffa042000ff90210007fa8108033fc4084011ff9842008ff8c210047fa6108023fc3084001ff9042000ff88210007fa4108003fc2084009ff8842000fdc4210027f6210802fff65440177fb2a2000dfd9510004feca8802ffe65440077f32a200bff5951005dfaca8802ffc65440077e3
  | 2 => 0x20007fac310002fd6188001fe30c401affd46200d7fca31006bfd5188035fe28c4019ffd0620007fc8310003fd4188033fe20c4014ffcc6200a7fc6310053fd3188029fe18c4000ffc8620007fc4310003ee2188001fe90c4000ff08620007d84310046fe6088035ffa84401aff942200d7faa11006bfc5088033ffa044000ff90220007fa8110067fc4088029ff9844014ff8c2200a7fa6110053fc3088001ff9044000fbc8220007f64110063ff65480317fb2a4000dfd9520004feca90063fe65480077f32a4018ff595200c5faca90063fc65480077e32a4018df1952001cf8ca90003ff64480017fb224000efd91200057ec89005ffe64480057f3224000ff59120005fac89005ffc64480057e3224000ef1912001578c890063ff544802fff2a24018ff551200bff8a89005bff634802d7fb1a4000f7d8d20005bec69005bfe63480037f31a4016ff58d200b5fac69005bfc63480037e31a4016f718d2000db8c69005bff534802dbfa9a4016ff94d200b7faa69005b7d534802dfe29a4016ffd0d200b7fc869005bfd434802dfe21a4018ffd49200c7fca4900037e5248031fea924018ff149200c6f8a49005fff4248001ff2124000ff509200bff8849005bff324802dff1924016ff4c9200b7f86490003ff61480017fb0a4000fdd8520005eec290003fe6148001feb0a4000ff18520025f8c290003f461480017a30a4018ffd45200c7fca290063fd5148031fe28a4017ffd0520007fc8290003fd414802ffe20a4016ffcc5200b7fc629005bfd314802dfe18a4000ffc8520007de4290003fe2148001fe90a4000fb48520007f84290063ff5048031ff2824018ff541200c7f8a09005fff4048001ff2024000ff501200bff8809005bff304802dff1824016ff4c1200b7f86090003ff2048001fd9024000ff88120007dc409004fff65080277fb284013ff9942001dfcca1004ffd65080277eb284013ff1942001df8ca10003ff64080017fb204012ff99020015fcc810003fd64080017eb204012ff19020015f8c81004fff5408025ff2a04013ff55020097f8a810047ff63080237fb184011ff98c2000dfcc610047fd63080237eb184011ff18c2000df8c610047ff5308023bfa984011ff94c2008ffaa6100477d5308023fe2984011ffd0c2008ffc8610047fd4308023fe2184015bf9882009ffea41004ffe5208001bf2904013ff5482009ff8a41004f7c5208025ffa104000ff90820007fa841004bfc4208023ff9904011ff8c82008ffa6410047fc3208001ffb084000ff98420025fcc210003fd61080017eb084000ff1842009ffea21004ffe5108027fea884013ff14420097fe8210003fe4108001fea084012ff1042008ffe6210047fe3108023fe9884011ff0c420007fe4210003fe2108001f71084000ff48420007f8421000
  | 3 => 0xeb1a801dbf58d400eff8c6a0006fc635003bffa9a801ddfd4d400effca6a0077fd535003bbea9a801dff14d40017fe86a000bfe4350005fea1a8002ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0002fc625003dffa92801eff94940006fca4a007bfd525003dfe292801edf14940017fe84a000bfe4250005fea128002ff109400effe64a0077fe325003bfe992801dff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0012fc615003dffa8a801eff945400f7faa2a007bfc5150005ffa0a8002efd0540017fc82a000bfd4150001dea0a8002ff105400effe62a0077fe315003bfe98a801dff0c540007fe42a0003fe2150001fe90a8000ff08540015fec0a007bff505003dff282801eff541400f7f8a0a000bff4050005fda028002ff901400077c80a000bfc4050005de2028002fe101400effe60a0077fe305003bfe982801dff0c1400e7fecb90072ff65c8039ff32e4003bf997200e7facb90072fd65c8039fe32e4003bf19720007fec990002ff64c8037ff3264002bf99320007fac990002fd64c8037fe3264002bf193200e7fea99006ffe54c8039feaa6401bff153200affec790056ff63c802bff31e4001bf98f200affac790056fd63c802bfe31e4001bf18f200affea7900577f53c802bff29e4015ff54f200aefaa790057fc53c802bffa1e4015ff90f200affa8790057fc43c8039ffa96401cff94b20006fca590073fd52c8039fe296401cdf14b200dffe8590003fe42c8001fea16401bff10b200affe6590057fe32c802bfe9964015ff0cb20007fec390003fe61c80097f30e4000ff58720005fac390003fc61c8039ffa8e401cff947200e7faa390073fc51c8037ffa0e4000ff90720007fa839006ffc41c802bff98e4015ff8c7200affa6390057fc31c8001ff90e4000fbc8720007fc4390003fd21c8001f690e4000ff087200e7fea190073fe50c8039fea86401cff143200dffe8190003fe40c8001fea06401bff103200affe6190057fe30c802bfe9864015ff0c3200d7fecb1006aff6588035ff32c4003bf996200d6fccb1000e7e6588035feb2c401abf59620006facb100027d6588035fe32c4003bf19620007fec910002ff6488033ff3244002bf99220007fac910002fd6488033fe3244002bf192200d7fea910067fe5488035feaa44019ff152200a7fec710052ff6388029ff31c4001bf98e200a7fac710052fd6388029fe31c4001bf18e200a7fea7100537f5388029ff29c4014ff54e200a6faa710053fc5388029ffa1c4014ff90e200a7fa8710053fc438802d7eb14401affd4a200d7fca5100037e5288035fea94401aff14a200d6f8a510067ff4288001ff2144000ff50a200cff88510053ff3288029ff1944014ff4ca200a7f86510003ff6188001ff30c4004bf986
  | 4 => 0x803ff60484017fb024200ff98121007fac090803fc60484017e3024227ffd412113ffca09089ffd504844ffe2824226ffd0121137f88090897ff304844bff1824225ff4c12112ff86090813ff65084097fb284204ff9942101dfcca10813fd65084477eb284204ff19421025f8ca10813ff64084097fb204204ff99021015fcc810813fd64084017eb204204ff19021025f8c81088fff5408445ff2a04223ff55021117f8a810813ff63084097fb184204ff98c2100dfcc610813fd63084437eb184204ff18c21025f8c610887ff5308443bfa984221ff94c2110ffaa6108877d5308443fe2984221ffd0c2110ffc8610887fd4308443fe2184224bf9882111ffea41088ffe5208401bf2904223ff5482111ff8a41088f7c5208445ffa104200ff90821007fa841088bfc4208443ff9904221ff8c82110ffa6410887fc32084097f3084204ffd4421027fca210813fd5108409fe2884204ffd0421027fc8210813fd4108409fe2084204ffcc421027fc6210813fd3108409fe1884204ffc8421027de4210813fe2108409fb1084204ff48421027da4210803f52108409ffb004204ff98021005fcc010813fd60084017eb004204ff1802111ffea01088ffe5008447fea804223ff14021117fe801088bfc4008443ff9804221ff8c02110ffa6010887fc3008441ffb2c8020bfd9640107fccb2000efe6590041feb2c8020bf59640107f8cb2000efc65900057eb248002ffd52401077ea92000bfe5490005feaa48002ff1524001778a92007fff639003f7fb1c801fff98e4000dfcc72007ffd639003f7eb1c801fff18e4000df8c72007fff539003fbfa9c801fff94e400fffaa72007f7d539003ffe29c8002ffd0e400177e872000bfe4390005fea1c801fef50e40017f88720003ff6290001ff3148000bf98a40007fac520002fd6290001fe3148020ffd4a40107fca5200037e5290041fea948020ff14a40106f8a52000bff4290005ff2148000ef90a40017fa852000bfc4290005de214801fffcca400fffc652007ffd329003ffe1948000ffd8640007fcc320012fe6190001feb0c8000bf58640007f8c320083ff5190041ff28c8020ff54640107f8a32000bff4190005ff20c8000ef90640017fa832000bfc4190005de20c801fffcc6400fffc632007ffd319003ffe18c8000ffc8640007fc4320003fd2190001fe10c8002bf98240107fea120083fe5090041fea848020ff14240017fe812000bbf4090005fda048002ff10240017f0812007fff309003fff184801fff4c2400fff8612007bff655003d7fb2a8000dfd9540004fecaa007bfe65500077f32a801eff595400f5facaa007bfc65500077e32a801edf1954001cf8caa000aff6450005ffaa28002ff95140017faa8a000bfc545003bffb1a801dbfd8d400effcc6a0006fe635003bf
  | 5 => 0x8f21127fea7908937f53c8449ff29e4224ff54f21126faa790893fc53c8449ffa1e4224ff90f21127fa8790893fc43c8459ffa96422cff94b21006fca5908b3fd52c8459fe296422cdf14b2115ffe8590803fe42c8401fea16422bff10b21127fe6590893fe32c8449fe9964224ff0cb21167fea390813fe51c8459fea8e4204ff1472115ffe8390813fe41c8401fea0e4204ff10721127fe6390813fe31c8449fe98e4204ff0c721007fec190803fe60c84017f3064200ff58321005fac190803fc60c8459ffa86422cff94321167faa1908b3fc50c8457ffa06422bff10321127fe6190893fe30c8449fe9864224ff0c321027fecb10812ff6588409ff32c4203bf99621026fccb1080e7e6588409feb2c422abf59621026facb108027d6588409fe32c4204bf19621027fec910812ff6488409ff3244202bf992210277cc91080abe6488409feb244200bf592210277ac910802bd6488409fe3244204bf19221157fea9108a7fe5488455feaa44229ff15221027fec710812ff6388409ff31c4201bf98e21027bcc710806de6388409feb1c4228bf58e21027bac710802dd6388409fe31c4204bf18e21147fea7108a37f5388451ff29c4228ff54e21146faa7108a3fc5388451ffa1c4228ff90e21147fa87108a3fc438844b7eb14422affd4a21157fca5108037e5288455fea94422aff14a21156f8a5108a7ff4288401ff2144200ff50a2114ff885108a3ff3288451ff1944228ff4ca21147f86510812fe6188409ffa8c4204ff94621027faa310813fc5188409ffa0c4204ff90621027fa8310813fc4188409ff98c4204ff8c621027fa6310813fc3188409ff90c4204fbc8621007ee4310813ff6088409ff3044200bf98221027fac110802fd6088409fe304422affd4221157fca1108abfd5088455fe2844229ffd022114ff881108a3ff3088451ff1844228ff4c221147f8611089fff654844f7fb2a4200dfd9521004feca9089ffe65484077f32a4227ff5952113dfaca9089ffc65484077e32a4227df1952101cf8ca90803ff64484017fb224226ff99121015fcc890803fd64484017eb224226ff19121015f8c89089fff544844dff2a24227ff55121137f8a890897ff634844b7fb1a4225ff98d2100dfcc690897fd634844b7eb1a4225ff18d2100df8c690897ff534844bbfa9a4225ff94d2112ffaa6908977d534844bfe29a4225ffd0d2112ffc8690897fd434844bfe21a4227ffd492113ffca4908037e524844ffea924227ff1492113ef8a49089bff4248401ff2124200ff50921137f88490897ff324844bff1924225ff4c92112ff8649089fff5148409ff28a4227ff54521027f8a29089bff4148409ff20a4200ff50521027f88290897ff3148409ff18a4225ff4c521027f86290803ff2148401fb90a4204ff88521027dc4290
  | 6 => 0x3fe98a8431ff0c542007fec0a1002ff6050801ff3028400ff58142007f8c0a1002fc6050865ffa828432ff94142197faa0a10cbfc5050805ffa028402ff1014218ffe60a10c7fe3050863fe9828431ff0c142027fecb20812ff6590409ff32c8203bf99641026fccb2080e7e6590409feb2c8230bf59641026facb208027d6590409fe32c8204bf19641015fac92080bff5490405ff2a48202ff55241017f8a920813ff63904097fb1c8204ff98e4100dfcc720813fd639045f7eb1c8204ff18e41025f8c7208bfff539045fbfa9c822fff94e4117ffaa7208bf7d539045ffe29c8202ffd0e41017fc872080bfd4390405fe21c8204ffd8a41027fcc520802fe6290409feb148200bf58a41027f8c5208c3ff5290461ff2948200df94a41187faa5208c3fc5290461be2948202ffd0a41017fc852080bfd4290405fe214822fffcca4117ffc65208bffd329045ffe1948204bf98641027fea320813fe5190409fea8c8204ff14641027fe8320813bf4190405fba0c8204ff10641027e88320813ff3190409ff18c8204ff4c641027f86320813ff6090409ff3048200bf98241027fac120802fd6090409fe3048230ffd4241187fca1208c3fd5090461fe2848202ffd0241017f8812080bbc409045fff984822fff8c24117ffa61208bffc309045dffb2a822ebfd9541177fccaa080efe655045dfeb2a822ebf59541177f8caa080efc65504097fb228202ffd51411777ea8a080bfe5450405feaa28202ff1514101778a8a08b7ff635045b7fb1a822dff98d4100dfcc6a08b7fd635045b7eb1a822dff18d4100df8c6a08b7ff535045bbfa9a822dff94d4116ffaa6a08b77d535045bfe29a8202ffd0d410177e86a080bfe4350405fea1a822def50d41017f886a0803ff62504017fb128200ff98941007fac4a0803fc62504017e312822effd4941177fca4a08037e525045dfea92822eff14941176f8a4a080bff4250405ff2128200ef90941017fa84a080bfc4250405de212822dffcc94116ffc64a08b7fd325045bfe1928202bfd8541177fea2a0813fe515045dfea8a8204ff14541017fe82a080bf74150409ff20a8204ef90541027f882a0813bc4150405fa20a822dffcc541027fc62a08b7fd3150409fe18a8200ffd8141005fec0a0803fe6050401feb028200ff18141005f8c0a08bbff505045dff282822eff54141177f8a0a080bff4050405dfa028202ff1014116ffe60a08b7fe305045bfe982822dff0c141167fecb908b2ff65c8459ff32e4203bf99721167facb908b2fd65c8459fe32e4203bf19721007fec990802ff64c8457ff3264202bf99321007fac990802fd64c8457fe3264202bf19321167fea9908affe54c8459feaa6422bff15321127fec790892ff63c8449ff31e4201bf98f21127fac790892fd63c8449fe31e4201bf1
  | 7 => 0x3a00400800a00400200000000000600800000a00000a00001200000800000200800000400000000600000800002000000400200000000000800000000200403c00000604602e00000400200000600800003400a00200800000001e00400a02402000000400000600dfd92521b6fcc9290037d649486dbe324a435dfd8e521acfec7290d77e639486bbeb1ca4359f58e521aef8c7290d77f439486bbf21ca435df50e521aef8872900f7e62948073f314a403db98a521b6fe85290db7c429486bbf994a435df8ca521aefa65290d77c3294801bfb0ca400df98652006fac3290037c619486dbfa0ca436df106521aefe63290d77e319486bbe98ca435df0c652006fec1290037e6094801beb04a400df182521b6fe81290db7c409486bbf984a435df8c2521aefa61290d77c3094869ffb2c8434bfd96421a7fccb2100efe6590869feb2c8434bf596421a7f8cb2100efc65908057eb248402ffd5242017fca92100bfd5490805fe2a48433ffd8e4219dfec7210cffe63908037f31c8433ff58e4219dfac7210cffc63908037e31c8433ffd4e4219efea7210cffe5390867fea9c8433df54e4219ff8a72100bff4390805ff21c8433ef90e42017fa872100bfc4390805de21c8402bf98a421a7fea5210d3fe5290801bf2948434ff54a421a7f8a5210d37c5290805ffa148402efd0a42017de852100bfc4290805f62148433ffcca4219ffc65210cffd3290867fe1948400ffd8642007fcc321012fe6190801feb0c8400bf58642007f8c3210d3ff5190869ff28c8434ff546421a7f8a32100bff4190805dfa0c8402ff1064219ffe63210cffe3190867fe98c8433ff0c642007fec121003fe60908017f3048400ff58242005fac121003fc6090869ffa848434ff942421a7faa1210d3fc5090805ffa048402ff102420177881210cfff3090867ff1848433ff4c24219ff861210cbff65508657fb2a8400dfd9542004fecaa10cbfe65508077f32a8432ff59542195facaa10cbfc65508077e32a8432df1954201cf8caa100aff6450805ffaa28402ff95142017faa8a100bfc5450863ffb1a8431bfd8d42007bec6a1002df6350863ff31a8401bf98d4218ffac6a10c6fd6350863fe31a8401bf18d4218fb8c6a1006dc6350863ffa9a8431dfd4d4218ffca6a10c7fd5350863bea9a8431ff14d42017fe86a100bbf4350805ff21a8402ff50d4218f7a86a100bfc43508057fb128432ffd4942197fca4a10037e5250865fea928432ff14942196f8a4a100bff4250805f7a128402ff909420077c84a100bfc4250805de2128402fb1094218ffe64a10c7fe3250863fe9928431ff0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1012fc6150865ffa8a8432ff94542197faa2a10cbfc5150805ffa0a8402ff1054218ffe62a10c7fe315086
  | 8 => 0x4000edd944d100000011e9650230000000000abca78309b48d4c1c102d8510e4339690f51860a0cc7c000000e6400000058827c4c0c882e06e53cc7ad3ac000704b0c001701408000000001b44508000000001b180000016945200018a4c7439c0016a00004c46b9789060caca386f82548f0bccd44e69184160c9d97c16546c95d229990ca08a0000ffc000aec26d4ac11d0f8f803b11f0000700674d88ed90701fdb2c00184d2c0f3000069c00180902850cf10760524a401940011b400030cb2c000218000000000000000b798f4b7c988001444274000808070001708001398000e95220ce99a80c8ce541c00000000124d9d00001cc000fc000000001801600201c00000000000200002800a00000000001800001400800a00200a00000200000c00e00800000e01c00000600400000600000200601801600000200000601200000e00400200200801e00400200200000a00400e00000200200000203200200000601e00e01400000800400e00600c00600a00c00400400000400200202c01201800200a00200200200000000000000800400801400600600201c00600200400000c00000000000400000800200a01001000a00001200000000000c00200c00a00000402603400c04800000c00200000200000000201600c01001200800400000000600800000000400000400002200600400400200200200000200000400a00a00400000400600e00e00000400000005001400200201200c00601a00c01400400000400800001000000200007a01e00200000000002802000400402c00200200200002a00001200000600000401c00000e01000000a00200000400600200001400e00c00202200200200200e00001200a00200200000600200400003200801e00400800200000401a00c00002800000000200200600604c00000002600600000000200a00001600200000a00800200000000000400803e00200c02600601400000800e00200e02400c00200800000000400001200402e00000c00600000e00000000000a00000a00200200000600200600800000200600002201c00000200001400000200000800000600202000001602400200200400800200000601400e00200000200200400002a00002800201001800e01000a00600800200000200203e02402602a00000c01e00200600400a00200400600600400000a00000000802200a00600200001200000000000c00200400000000000600000200600200400000400e00000c00200000201c01400000200400c01a00200000600000600400400600a00400c00a00000200400000000400000600400000200600000000001c00200000600802000a00000600002200801e00200a01400202200400000400800600001400800200000000a00000200000a00801400400202a0060000000020
  | 9 => 0xf480b49685cc6490745a4c980000000000000006fc0000000000005e40008ddaf0001ae89100002957e574152c0000012bc001af96400008c80011c961000000000079c001438000a591c4eb99fd4c40001756a4000948001aa800000088c0f03400000000012710ece28ea40000000000010a4a9da6d9a48cc00000180dabc260001294000ac8fc4c58c2000082c001b000015580012b99615540000000001a9790000da8000ef53e44f863d7693505f484930403c93176475c0280000001303e421c8d40000003e14fc0006086ed5080401059a1128000000000810000738c49490000bfd00c0018380009a0000ea01854b8278000a340e8000d6c3652c4000018001601230000000000000e844fc9413789640b11406f00017542e84340007d8c400000000005c55a0000000000000000000758e500000000e1a902516b9164000791539ab8000c0c0014296393704259ac00000000585c000000694000000000d7c000000000001440000000ed00001e09203c0b5c83d22482871874596c4b58ac5d53b413c125310f39510000df8cbd0688400019998e14d8749b113800010952e5afc2586f56e40cd1ec6b400000000000000000054400052d29c0015a8000740e8d5fc000350000c1da0ce446d186d51c750c199c88d0668a5c33da751bcda4a054f4da1688330a0042d21c0010f40003d11e40000000000015e40001b800000000000110019c000600001840604e989000000000003600000000002c101400000000168c0013a04600007d40000007bc914000c800015a49718f0000665144001745aec000328001414000000000001411784000000b7407d75d588000f7400000133000000116c6848ec1e4ce0000428001a59368000a4400154c0000000000000000017c45f86b00000300009e006c6c4e3cacd8bc0000000000007a055c0001f4001a340000006c8f052ad0b8110b080009580003d807898150cba16f13095c000000062c0000005280000000000c40007b47304e80016297bcd094501c474c000000000001810001ad4fcd814444000001b40001a040000000013f994c000ae89a8fc84a40014bc238a4c5808a405c0000f89f0000000000000000879aad0a90f131877c0000000000843100015b0c902ecb296cc4196d84ec000000000001ad000000000113000000000112c868a94830001279a14000320000000c1159d79cfd4000ff40007948e4c389b18e8d3c00034d458000d81514874e70000000001848f14000a48768fb0dc132d4dc1d97c84219690252547ed8e4ad17f93286205d822cf3d56435da68de42816c16640016bc9c02bc00148909800000016c8b40d00a4001adc0000000007e40003907f564c9f8001aa03254c80000012884dd17d3c0000001a2c950ba8001a2800181991109ce1869800088111545
  | 10 => 0xfc0000011d400015c000f953f42d0d585380012b40018200000000000012398848f40000000b97480018c9934554f2400000000176143000134147886cc69208f1ca303e85b03181286a400189400161800000000022047939c000001774000000f8c001248000df04987203748980008ad8b40010cd8340001c9a4408cadc00000068d7340000006bd0080001ecb617a40000000006507a80000009c400000000000143c6917f55d800000001084c000001931b05300dbc00047cc34e54ff8faca90b643fc244000cc80019d50dd8300957e0a50455160af00008b8f6c00000067c8d8000000001005a9cdcc000ddceb400189000054861d4d00002a45355e90512687280016546cc918aa51f911054d150000000be55201716e138cb3c000388001a64000d5400000000000000115c888464f912fd53ce7c1554e133548545d78c770860d855d0001658000c149940011a400000183c5ad01000029dae4b1c0000003c5a819f85ec8a87243ad69c2f52a43ec0012d1a3889000113cc28000000f899b40000000000005dc66000161513926c1ad2ed6dc00160c000000db02ccab08bc000000c00348000000680001b4d168b4172c0007c0000000d70494000000000000490611280f44000efc6d58540257519e40018a198c9603152f400191995d3c800000197503024d3a96785c800105d0bda60e08000000a88000001b500000019ec0007554a0000d906297dd6e8fe46e882522d65c0fd0d80002b1550814000644798488000a08000dd5388eb018d67c1680016f40740000011b16a920d1880000007b90b00013943dce200000001986354c0b9c000ec0a98e8871400147c12c0000000000015284c9a7d824000d040000000000013649e400000000000000048c8200000003a8b54000b8d57d27d3dd7ac0000001d000134400000057d73970cc54150cb40018c4cf8000384b9871cbd800000000000000107c40c000000224000f0d85948d97022853cd004ccbf80019395f54f9a480c0570000000aac00065caa8064d38d68f214d40000000008712f00013fc0007d120000057800189817d5257595f91cc0013bc0000000000000000010540000005c0000000000de10d091c7f1b315ec4f0001320000ebd9e97c0ba50fc000069634344000e5cb44179868e5976c7e87f949cd0c0004694991544804b00bc7c45840014241209fc25d1a90e1338369a1d8a8000000e14001ac4500001064cc400171020400000097800130c9380004f42f83a00013edac8000d480000017fc8e0090000000001a3d56988d58ca6800085d35cfb42ac6a9a887b0c049b8c784840acc607dc864bc51b9a097300000017a8504e9c02cfe9078d3540cf08de8d747fc148414bc8a2d8b96c98c06ace350b4671519b08049b28c719dd4f11182653d021498cca963c
  | 11 => 0xd391420000000eed7cc000000f9d669984000001609980000000000bec0000000006781a5a713613540000000000000005580000000013d8d5cfa0e60c2dac00004e0780851540a14000000774240f60001474f84000afc000bacdb52d85145fcdc8000f7d0000005b4ab508ca7c000200ed40a86c0b859e18d8f2d829631ad86a1274dd80e537c0dc000614234d1934daf400000087d74cb24cd41801359bc3947843c94ec0003b4a3c4acae0a645e915823ce91645471a503719643cc58ca6d374380015958000e78bb44d0284c940014a47895b8f689d91dd3b956cd2590d901648000000b0000096c001a943a4000000a18000000e302b904ce6d2e09f400125000043d55ce494180015f0595570a75448c64088fe0000000000000000000d40000e74000000000248ded234f9950593db144d546000131446d9c577cee4000b481dc00d3f13e96248fcaf8bdd5612051a02c8ff06d935800064d2b0cc09259d99255dd404000640954e040000014698884a0f5d2450c8f59a118cc0000000012dc97c0000000001b5049080000000000000000000818458000000e80630000001ae00013a40000000000002697f0dd128521901d72966c2909e832ce1cc8d1095c59c04b89d49a561c7094e8358000ac400119c8858700000011d0000000ccc9ed038d9400000000005400000179936c000f640580012a8fa80012f8000ef1979590b118fcbd180592c53133d7d5175264ca46594b4fbd4018795791f57b90344bdacca716d4ea8000f7118d040b94c509ad77154572436c10d9f110c001a4040800124037cd8cbd4cfc000ae592153499114c0012cd3e16f8c31928000000aa0f197ec779120000108000000b04000000574db91955750c56ec7a49bc8043bc2dc0003f82b40001880980000000014657140f55d4000f54404ab96980000000006191340000352d400000013800149494c0080017d8858a8c0008540019f400000045171cb4d6b1214000000001800bf40007c98dce10378000000000288d64fb8b810919b80002c4001385260000000001580710000f28000ad8000cf00014a800000000199400000000182c000000fd00000015994805bc0001d40000000a0b8814041004511c5687e17b4000d15a78001875ab11e00013b0000c6d03d8b0298000000000894000cf4000800d60ee8001864bf0001298df4000c249280d45e03559893c48342a8dadb34a280002080006550d41f16c456d90400166106c001aa55e15ac0000000000016ad1900005b8d20bb0000be178098460cb38d9c1a01bd8d09dca1d0ac09cd1c000000ef845c4d8431084000b1400189c0002d82d4a55940000b50000a251c0d500005900014359cd0586e0e006dc81ccb0b18e24a8484489ce385f0b6d99da5404d1acee0638001718000001b38cd8be85a91
  | 12 => 0x40118162cc5c000ec573c000af456400000031c14da98000e2c00195514870c561b2400187c33400000190944c4a8934000974000e0d044001a84e4da30000ad51249cc0018d531cecc3000000000010880d890cbb8c4cb312e9348000f4c9b400000000080c73570438c000000d28fdc0000394e55cc72c001b0da4c7ccc3d198b58000021a18cb820cfed0181f800006142d794f78c459502f13245181588b16b51d821188168044c76c304dc48e97d0598000001a000016d00003f00000000000000000000009c9a200005418452c94cd1701180010200001e81146249d16757208c5684000001670ead7783995c97e8270b21ab4fa4944b698ec51d104bc0e412a1620a604703f4d98f410c19b0fd80004e48f8d3191c000000cd01b0000ac000000049d500a202a0449178000000dfc0000000000000005a159523c838000c09a8c000145a5c000550000000001b1c73cb913d5584d78cec2e55b400092d530051b20ec800041c00047478c0018f80000012100000000000017b00000005d0bbd91428c99981d2584396fc00154800099c000100908f0194801c3b8904d2d5bc00066d0a1a243d46897a0000001b3c8c129093d28cc840001914b0000000000001604764a810e8b700ec00008059c440000000f340000002fc510a10b34cdd25
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7690810004fd7690810024fc76908101a67e65908100067d6590810016be6490810006bd649081019ede6390810006dd6390810006ee6290810006ed6290810004ff7650810024fe7650810004fd7650810024fc76508100057f755081003d7c75508101967e65508100067d6550810016be6450810006bd6450810005df735081002ddc735081018ede6350810006dd6350810006ee6250810006ed6250810005f77150810025f47150810005fb7050810005f87050810025f576c8410006f576c84100277665c84100277565c8410027b664c8410027b564c8410027d663c8410027d563c84101ff7753c84101ff7553c8410025f672c8410027e672c8410026f762c8410027e662c8410006f562c8410027e562c8410006e562c84100077652c84101f77452c8410005f570c84101eef660c8410027f260c8410064ff7690010024fe7690010014fd7690010024fc76900101067e65900100067d6590010016be6490010006bd64900100fede6390010006dd6390010006ee6290010006ed6290010025f67190010005f57190010064ff76500100057f755001003d7c75500100f67e65500100067d6550010016be6450010006bd64500100eede6350010006dd6350010006ee6250010006ed6250010004fd76c80100e67e65c80100067d65c80100debe64c8010006bd64c80100aede63c8010006dd63c8010006ee62c8010006ed62c8010025f471c8010007e721c8010004ff7688010004fd768801003d7e75880100057d75880100d67e65880100067d65880100cebe6488010006bd64880100a6de6388010006dd6388010006ee6288010006ed6288010025f67188010005f571880101e7e42188010004ff76480100057f754801003d7c75480100c67e65480100067d6548010005bf7448010035bc74480100bebe6448010006bd6448010005df734801002ddc73480100b6de6348010006dd6348010006ee6248010006ed6248010005f77148010025f47148010007e72148010004ff7608010024fe7608010004fd7608010024fc760801009e7e65080100067d6508010096be6408010006bd640801008ede6308010006dd6308010006ee6208010006ed6208010025f67108010005f571080101dfe42108010025f77644010006f77644010004f776440100077775440101c7747544010027766544010027756544010007b77444010007b47444010027b66444010027b56444010007d773440101d7d47344010027d66344010027d563440101d77753440101d7755344010007e77244010005f67244010005f47244010007e47244010005e47244010027e66244010027e562440100077652440101c7745244010025f77044010027f370440101cef66044010027f260440101c7f250440101c7f150440101bff340440101bff04044010
  | 1 => 0x8810026ec5198810026ef4198810026ee4198810026ed4198810026ec4198810026ef3198810026ee3198810026ed3198810026ec3198810006ee7098810006ec7098810006ef5098810006ee5098810006ed5098810006ec5098810006ef4098810006ec4098810006ef3098810006ee3098810006ed3098810006ec3098810026ef1098810026ee1098810026ed1098810026ec1098810004ff75588100067f75588100047f755881001cfe7558810004fd755881001cfc75588100067c755881001c7c7558810004ff7458810014fe7458810014fc7458810004ff735881000cfe7358810004fd735881000cfc73588100067f53588100067d5358810026ef7258810006ef5258810006ee5258810006ed52588100067c5258810006ec52588100066c5258810006ef4258810006ec4258810006ef3258810006ee3258810006ed3258810006ec3258810024ff7158810024fe7158810024fd7158810024fc7158810026f47158810024f47158810026ee2158810026ec2158810026f421588100acff70588100b4fd7058810006ef75588100066f7558810006ee7558810006ed7558810006ec75588100066c7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026e47158810026ef5158810026ee5158810026ed5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec3158810006ee7058810006ec7058810006ef5058810006ee5058810006ed5058810006ec5058810006ef4058810006ec4058810006ef3058810006ee3058810006ed3058810006ec3058810026ef1058810026ee1058810026ed1058810026ec10588102057f76948100067f76948100047f76948102067e76948102057d76948100067d76948100047d76948102067c76948102067f64948101b67e64948102073e64948101b63e64948100067d64948102073d64948100063d64948102067c649481021d7f739481021d7d73948102067f63948101ae7e63948102075e63948101ae5e63948102167d63948102075d63948100065d63948102067c639481020d7e729481003f6e72948102067f62948100067e62948102076e62948100066e62948100067d62948102076d62948100066d62948102067c62948102067e619481020774219481006e7e60948102077710948102077a1094810207791094810004ff7690810024f
  | 2 => 0x6be5359010006bd53590100063d5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc52590100063c5259010006bf3259010006be3259010006bd3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf5159010026be5159010026bd5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc2159010036bf7059010006be7059010006bc7059010006bf5059010006be5059010006bd5059010006bc5059010006bf3059010006be3059010006bd3059010006bc3059010026bf1059010026be1059010026bd1059010026bc1059010006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c100065c5258c10006df4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c10026de5158c10026dd5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c1002edf7058c10006de7058c1002edd7058c1002edc7058c10006df5058c10006de5058c10006dd5058c10006dc5058c10006df4058c10006dc4058c10026df1058c10026de1058c10026dd1058c10026dc1058c10004ff75988100067f759881001cfe7598810004fd759881001cfc75988100067c759881001c7c7598810014fe7498810004fd7498810014fc7498810004ff739881000cfe7398810004fd739881000cfc73988100067f53988100067d5398810026ee7298810006ef5298810006ee5298810006ed52988100067c5298810006ec52988100066c5298810006ef4298810006ec4298810006ef3298810006ee3298810006ed3298810006ec3298810024fe7198810024fc7198810026ee2198810026ec2198810006ef75988100066f7598810006ee7598810006ed7598810006ec75988100066c7598810006ef7498810006ee7498810006ed7498810006ec7498810006ef5498810006ee5498810006ed5498810006ec5498810006ef7398810006ee7398810006ed7398810006ec7398810006ef53988100066f5398810006ee5398810006ed53988100066d5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec4398810026ef7198810026ee7198810026ed7198810026ec7198810026ef5198810026ee5198810026ed519
  | 3 => 0x671c8110005f571c8110004fe768811005d7e75881100057d75881100067f65881100d67c6588110006bf64881100cebc6488110006df63881100a6dc6388110006ef6288110006ec6288110004ff7648110004fd7648110024fc76481100057f754811005d7c75481100067f65481100c67c6548110005bf7448110055bc7448110006bf64481100bebc6448110005df734811004ddc7348110006df63481100b6dc6348110006ef6248110006ec6248110005f77148110025f47148110004fe76081100067f650811009e7c6508110006bf6408110096bc6408110006df630811008edc6308110006ef6208110006ec62081100067f658411006e7c6584110006bf6484110066bc6484110006df6384110046dc6384110006ef6284110006ec6284110025fa7084110026fb6084110025f67684110026f67684110024f67684110007776584110227746584110007b76484110007b46484110007d7638411022fd4638411022f77538411022f755384110007e76284110006f66284110006f46284110007e46284110006e46284110007765284110227745284110025f67084110026f76084110027f360841100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100047c72594100067f42594100067c42594100067f32594100067e32594100067d32594100067c32594100267f71594100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c215941003e7f70594100067e705941003e7d705941003e7c70594100067f40594100067c40594100067f30594100067e30594100067d30594100067c30594100267f10594100267e10594100267d10594100267c1059410004ff755901001cfe7559010004fd755901001cfc7559010026bf7459010006bf5459010036be5459010006bd5459010036bc5459010004ff735901000cfe7359010004fd735901000cfc73590100067f53590100067d5359010036bf4359010006be4359010006bd4359010036bc4359010004ff7259010004fc72590100067c5259010036bf4259010036bc4259010024ff7159010024fe7159010024fd7159010024fc7159010026be4159010026bc4159010014ff7059010014fd7059010034fc7059010036bc4059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf53590100063f5359010
  | 4 => 0x8910006ed53189100066d5318910006ec5318910006ef4318910006ee4318910006ed4318910006ec4318910006ef71189101deee7118910006ed71189101deec7118910006ef51189101deee5118910006ed51189101deec5118910006ef41189101deee41189101deec4118910006ef31189101deee3118910006ed31189101deec31189101deef7018910006ed7018910006ef5018910006ee5018910006ed5018910006ec5018910006ef4018910006ec4018910006ef3018910006ee3018910006ed3018910006ec30189101deef1018910006ed10189101deec10189100067f76949100057e76949100067e76949100047e76949100067d76949100057c76949100067c76949100047c76949100067f64949100073f64949100063f64949101b67e64949100067d64949101b67c64949100073c64949101b63c649491023d7f739491023d7d73949102367f63949100075f63949100065f63949101ae7e63949102367d63949101ae7c63949102375c63949101ae5c639491005d7e729491005f6e72949100067f62949100076f62949100066f62949100067e62949100067d62949100067c62949100076c62949100066c62949102077b1094910004ff7690910004fe7690910004fd7690910004fc76909100067f65909101a67c6590910006bf6490910016bc6490910006df639091019edc6390910006ef6290910006ec6290910004ff7650910004fe7650910004fd7650910004fc76509100057f755091005d7c75509100067f65509101967c6550910006bf6450910016bc6450910005df735091004ddc7350910006df635091018edc6350910006ef6250910006ec6250910014fc76505100067f65505101767c6550510006bf6450510016bc6450510006df635051016edc6350510006ef6250510006ec6250510005fb7050510005f87050510004fe76c85100067f65c85101667c65c8510006bf64c851015ebc64c8510006df63c8510126dc63c8510006ef62c8510006ec62c8510005fa70c8510005f970c8510004fc76485100057f754851005d7c75485100067f654851013e7c6548510006bf6448510136bc6448510006df634851012edc6348510006ef6248510006ec6248510005fb7048510005f8704851007cfe76901100067f65901101067c6590110006bf6490110016bc6490110006df63901100fedc6390110006ef6290110006ec6290110014ff7650110054fd7650110024fc76501100057f755011005d7c75501100067f65501100f67c6550110006bf6450110016bc6450110006df63501100eedc6350110006ef6250110006ec6250110005f77150110025f47150110024fe76c81100067f65c81100e67c65c8110006bf64c81100debc64c8110006df63c81100aedc63c8110006ef62c8110006ec62c8110025f
  | 5 => 0x67e759891001c7e7598910004fd75989100067d75989100047d759891001cfc7598910014fe7498910006be7498910014be7498910004fd7498910006bd7498910004bd7498910014fc7498910004ff739891000cfe7398910006de739891000cde7398910004fd7398910006dd7398910004dd739891000cfc73989100067f53989100067d5398910004fe7298910004ee72989100067c5298910004fd7198910006f57198910004fd7098910006f970989100057f755891005d7c75589100067f65589100067c6558910005bf7458910055bc7458910006bf6458910006bc6458910005df735891004ddc7358910006df6358910006dc6358910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006ef72589100067c5258910004ff7158910006f77158910004f77158910004ff7058910006fb7058910004fe761891005d7c75189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc6318910006ed62189100076c5218910004ff75189100067f751891001cfe7518910004fd751891001cfc75189100067c751891001c7c7518910014fe7418910004fd7418910014fc7418910004ff731891000cfe7318910004fd731891000cfc73189100067f53189100067d5318910006ee7218910006ef5218910006ee5218910006ed52189100067c5218910006ec52189100066c5218910006ef4218910006ec4218910006ef3218910006ee3218910006ed3218910006ec3218910024fe7118910024fc71189100a4fe701891008cfc7018910005ee7618910006ee7618910004ee76189100076f75189100076c7518910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d53189101dfeb10189101dfe81018910006ef75189100066f7518910006ee7518910006ed7518910006ec75189100066c7518910006ef7418910006ee7418910006ed7418910006ec7418910006ef5418910006ee5418910006ed5418910006ec5418910006ef7318910006ee7318910006ed7318910006ec7318910006ef53189100066f5318910006ee531
  | 6 => 0xd52d8d10006dc52d8d100065c52d8d10006df42d8d10006dc42d8d10006df71d8d10246de71d8d1004edd71d8d10246dc71d8d10006df51d8d10246de51d8d10006dd51d8d10246dc51d8d10006df41d8d10246de41d8d10246dc41d8d10246de21d8d10246dc21d8d10246df70d8d1004ede70d8d1004edd70d8d1004edc70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d10006df40d8d10006dc40d8d10246df10d8d1004edd10d8d10246dc10d8d1005d7e75d89100057d75d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d89100076c52d8910004ff75d891001cfe75d89100067e75d891001c7e75d8910004fd75d89100067d75d89100047d75d891001cfc75d8910014fe74d8910004fd74d8910014fc74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006ef52d8910006ee52d8910006ed52d89100067c52d8910006ec52d89100066c52d8910006ef42d8910006ec42d8910006ef32d8910006ee32d8910006ed32d8910006ec32d89100076e75d89100076d75d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d89101e7eb10d89101e7e810d8910006ef75d8910006ee75d89100066e75d8910006ed75d89100066d75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d89101e6ee71d8910006ed71d89101e6ec71d8910006ef51d89101e6ee51d8910006ed51d89101e6ec51d8910006ef41d89101e6ee41d89101e6ec41d8910006ef31d89101e6ee31d8910006ed31d89101e6ec31d89101e6ef70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef40d8910006ec40d8910006ef30d8910006ee30d8910006ed30d8910006ec30d89101e6ef10d89101e6ec10d891005d7e75989100057d75989100067f65989100067c6598910055be7498910005bd7498910006bf6498910006bc649891004dde7398910005dd7398910006df6398910006dc6398910006ef6298910004ff759891001cfe7598910
  | 7 => 0x9110006bc63d91100079c63d91100069c63d91100073f53d91100073d53d91100073c52d9110257bb10d9110257b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d91100063c52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d9110256be71d9110006bd71d9110256bc71d9110006bf51d9110256be51d9110006bd51d9110256bc51d9110006bf31d9110256be31d9110006bd31d9110256bc31d9110256be21d9110256bc21d9110256bf70d9110056be70d9110006bd70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d9110256bf10d9110256bc10d91100057f755911005d7c75591100067f65591100067c6559110056bc6459110005df735911004ddc7359110006dc6359110005ef7259110005ec7259110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110054ff7459110006bf7459110004ff7359110006df7359110004df735911000cfe7359110004fd735911000cfc7359110006dc735911000cdc73591100067f53591100067d5359110004ff7259110006ef7259110004ef7259110004fc7259110006ec7259110004ec72591100067c5259110064ff7159110006f7715911007cff7059110006fb7059110005be7619110056be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100079c63191100069c63191100073f53191100073d53191100073c521911024ebf601911024fbb101911024fb8101911004dde76d8d1004ede76d8d1000cde76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d100075c52d8d10247db10d8d10247d810d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006d
  | 8 => 0x7e76208610006f56208610007e46208610007765208610277745208610005f57008610027f26008610014fe7690210024fd7690210016be6490210006bd6490210025f67190210005f57190210034ff76502100057f755021006d7c7550210006bf6450210016bc6450210006ef62c8210006ec62c8210007e721c8210024fd768821006d7e75882100057d7588210006ee6288210006ed6288210025f67188210005f57188210007e421882100057f754821006d7c7548210005bf7448210065bc7448210005df7348210045dc7348210006ef6248210006ec6248210005f77148210025f47148210007e72148210024fd7608210006ee6208210006ed6208210025f67108210005f57108210007e42108210005f576c4210026f576c421026f7753c421026f7553c4210005f672c4210025f472c42100077652c42102677452c4210027f260c421005d7e76d951005e7e76d951001c7e76d95100067e64d95100067c64d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100057e72d951025f7b10d951025f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100047e72d95100067d72d95100067c72d95100067f42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d951025e7e71d951005e7d71d951025e7c71d95100067f41d951025e7e41d951025e7c41d95100067f31d951025e7e31d95100067d31d951025e7c31d951025e7e21d951025e7c21d951025e7f70d951005e7e70d951005e7d70d951005e7c70d95100067f40d95100067c40d95100067f30d95100067e30d95100067d30d95100067c30d951025e7f10d951005e7d10d951025e7c10d9510014fe76d91100067f65d91100067c65d9110056be64d9110006dc63d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110006bf54d9110056be54d9110006bd54d9110056bc54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d91100067f53d91100067d53d9110056bf43d9110006be43d9110006bd43d9110056bc43d9110004fe72d9110004fd72d91100067c52d9110056bf42d9110056bc42d9110024fe71d9110054fd71d9110024fc71d9110056bf41d9110014fe70d9110024fd70d9110014fc70d9110056bf40d9110055be76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d
  | 9 => 0xc405921006d7e75d8a100057d75d8a10004ff75d8a1001cfe75d8a100067e75d8a1001c7e75d8a10004fd75d8a100067d75d8a100047d75d8a1001cfc75d8a10014fe74d8a10004fd74d8a10014fc74d8a10004ff73d8a1000cfe73d8a10004fd73d8a1000cfc73d8a100067f53d8a100067d53d8a100067c52d8a10006f571d8a101e6ee21d8a101e6ec21d8a10006fa70d8a10004fd7698a10006ef6298a10004ff7598a1001cfe7598a10004fd7598a1001cfc7598a10014fe7498a10004fd7498a10014fc7498a10004ff7398a1000cfe7398a10004fd7398a1000cfc7398a100067f5398a100067d5398a100067c5298a100057f7558a1006d7c7558a10005bf7458a10065bc7458a10005df7358a10045dc7358a10004ff7558a100067f7558a100047f7558a1001cfe7558a10004fd7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7458a10006bf7458a10004bf7458a10014fe7458a10014fc7458a10006bc7458a10014bc7458a10004ff7358a10006df7358a10004df7358a1000cfe7358a10004fd7358a1000cfc7358a10006dc7358a1000cdc7358a100067f5358a100067d5358a10006ef7258a100067c5258a10006f77158a10006ed6218a10004ff7518a1001cfe7518a10004fd7518a1001cfc7518a10014fe7418a10004fd7418a10014fc7418a10004ff7318a1000cfe7318a10004fd7318a1000cfc7318a100067f5318a100067d5318a10004fe7218a10006ee7218a100067c5218a10006f57118a101deee2118a101deec2118a10006fa7018a100067f7694a100067e7694a100067d7694a100067c7694a100067f6494a101b67e6494a100067d6494a101b67c6494a102957f7394a102957d7394a1028e7f6394a101ae7e6394a1028e7d6394a101ae7c6394a1006d7e7294a1006f6e7294a100067f6294a100067e6294a100067d6294a100067c6294a1005e7d6194a102067e6094a102077b1094a10004ff7690a10004fe7690a10004fd7690a10004fc7690a10006bf6490a10016bc6490a10004ff7650a10004fe7650a10004fd7650a10004fc7650a100057f7550a1006d7c7550a10005df7350a10045dc7350a10005f77150a10025f47150a10014ff7650610016be6450610006bd6450610005fb7050610005f87050610006ee62c8610006ed62c8610005fa70c8610005f970c8610006f576c86101ef7753c86101ef7553c8610025f672c8610006f762c8610007e662c8610006f562c8610007e562c86100077652c86102877452c8610007f270c8610005f570c8610007f170c8610026f660c86100057f754861006d7c7548610006ee6248610006ed6248610027e42148610005fb7048610005f87048610005f57608610026f5760861027f77530861027f755308610027e67208610006f76208610
  | 10 => 0x931000cfc73593100067f53593100067d535931007ebf4359310006bd4359310004ff7259310004fc72593100067c525931007ebc4259310024fc7159310026be4159310026bc415931007ebf4059310004ff7598b1001cfe7598b10004fd7598b1001cfc7598b10014fe7498b10004fd7498b10014fc7498b10004ff7398b1000cfe7398b10004fd7398b1000cfc7398b100067f5398b100067d5398b10026ee7298b100067c5298b10024fe7198b10026ee2198b10026ec2198b10026f41098b10004ff7558b100067f7558b100047f7558b1001cfe7558b10004fd7558b1001cfc7558b100067c7558b1001c7c7558b10004ff7458b10014fe7458b10014fc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b100067f5358b100067d5358b10026ef7258b100067c5258b10024fc7158b10026ee2158b10026ec2158b100067f7694b102067e7694b100067d7694b102067c7694b102067f6494b101b67e6494b100067d6494b102067c6494b102a57f7394b102a57d7394b102067f6394b101ae7e6394b1029e7d6394b102067c6394b1020d7e7294b100876e7294b102067f6294b100067e6294b100067d6294b102067c6294b10004ff7690b10024fe7690b10004fd7690b10024fc7690b10016be6490b10006bd6490b10004ff7650b10024fe7650b10004fd7650b10024fc7650b100057f7550b100857c7550b10005df7350b10075dc7350b10005fb7050b10005f87050b10054fd7690310256bf6490310016bc6490310014ff7650310024fc76503100057f75503100857c7550310016be6450310006bd6450310005f77150310025f47150310006ee62c8310006ed62c8310025f671c8310005f571c83100857e75883100057d75883101e6ef62883101e6ec62883100057f75483100857c7548310005bf744831007dbc7448310005df7348310075dc7348310006ee6248310006ed6248310005f77148310025f471483101deef62083101deec6208310066be64d9210004ff75d921001cfe75d9210004fd75d921001cfc75d9210064fd74d9210006bf54d9210066bc54d9210004ff73d921000cfe73d9210004fd73d921000cfc73d92100067f53d92100067d53d9210066bf43d9210006bd43d9210004fe72d9210004fd72d92100067c52d9210066bc42d9210006f571d9210256be41d9210256bc41d9210006fa70d9210066bf40d9210014ff76592100057f755921006d7c7559210066bc6459210004ff75592100067f75592100047f755921001cfe7559210004fd755921001cfc75592100067c755921001c7c7559210006bf7459210004ff735921000cfe7359210004fd735921000cfc73592100067f53592100067d5359210004ff7259210004fc72592100067c5259210066bf4159210024fc7059210066b
  | 11 => 0x6f63158420006f53158420024ff705842009d7e75184200057d7518420095be7418420005bd741842008dde7318420005dd7318420026f66118420006f56118420024ff7690420004fe7690420004fd769042009d7e75904200057d7590420026f66190420006f56190420004ff7650420004fd7650420004fc7650420016be6450420006bd6450420005ef7250420005ec7250420026f66150420006f56150420005fb7050420005f87050420024fd76c8420336ee62c8420026f661c8420006f561c8420005fa70c8420005f970c8420004fd768842009d7e75884200057d7588420095be7488420005bd748842008dde7388420005dd73884200076e528842032f6c5288420005ed76884201deed7688420004ed76884201df6e75884201df6d75884201dfae74884201dfad74884201dfce73884201dfcd73884203276f53884203276d53884201ddee71884201deed6188420005ed70884201e6ee6088420004ff76484200057f754842009d7c754842031eee62484200076e52084203176c5208420026f66108420006f56108420007e52108420005fa7008420005f9700842030f6f530842030f6d53084201ddee71084201dfe671084201dfe661084201deed6108420007e561084201dfea7008420005ed70084201dfe970084201e6ee60084200ccff7690020014fe7690020014fd7690020094fc7690020016be6490020006bd6490020005ee7290020005ed72900200ccff76500200057f755002009d7c75500200076e52c80203076c52c80202ff6f53c80202ff6d53c80201ddee71c8020006ed61c802009d7e75880200057d75880202eded72880202e6ee62880202df7a75880200077975880202f77b53880202f77953880202edf972880202e6fa6288020007ea62880200077a52880202df785288020007ea2188020007e82188020004ff76480200057f754802009d7c7548020005bf7448020095bc7448020005df734802008ddc73480200076e52480202af6c5248020005f77148020005f47148020005ef7648020006ef7648020004ef76480200076f75480202af6c7548020007af7448020007ac7448020007cf73480202c7cc73480202c76f53480202c76d5348020007e771480201ddec7148020007e47148020005e47148020006ed61480202d5ef70480202ceee6048020005fb7648020006fb7648020004fb76480200077b75480202af787548020007bb7448020007b87448020007db73480202c7d873480202c77b53480202c77953480202bdfb7248020007eb72480202b6fa6248020007ea62480200077a52480202af785248020007f37148020007f07148020004ff755931001cfe7559310004fd755931001cfc7559310026bf7459310006bf545931007ebc5459310004ff735931000cfe7359310004fd735
  | 12 => 0xc76501200057f75501200c57c75501200067f65501200f67c6550120006bf6450120016bc6450120006df63501200eedc6350120005ef7250120005ec7250120006f76150120006f461501200067f65c81200e67c65c8120006bf64c81200debc64c8120006df63c81200aedc63c8120006f761c8120006f461c81200077b65c812035f7865c8120007bb64c8120007b864c8120007db63c8120367d863c81203677b53c81203677953c81200077a52c812035f7852c8120007f361c8120007f061c8120007eb21c8120007e921c81200c57e75881200057d75881200067f65881200d67c6588120006bf64881200cebc6488120006df63881200a6dc63881200076e52881203576c5288120006f76188120006f461881203576e75881200076d75881200076f65881203576c6588120007af6488120007ac6488120007cf638812034fcc638812034f6f538812034f6d5388120005ed7188120007e761881201e6ec6188120007e46188120006e46188120007eb6088120096be64d9020004ff75d902001cfe75d9020004fd75d902001cfc75d9020094fd74d9020004ff73d902000cfe73d9020004fd73d902000cfc73d90200067f53d90200067d53d90200dcfe72d9020006ee72d90200067c52d9020024fe71d9020004fd71d90200ccfe70d9020006fa70d9020014ff76590200057f755902009d7c7559020096bc6459020004ff75590200067f75590200047f755902001cfe7559020004fd755902001cfc75590200067c755902001c7c7559020006bf7459020096be5459020006bd5459020004ff735902000cfe7359020004fd735902000cfc73590200067f53590200067d5359020096bf4359020006bd4359020014ff7259020014fd7259020094fc72590200067c5259020096bc4259020004ff7159020024fc7159020096bf4159020094fc7059020096bc40590200e67f769482001e7e769482001e7d769482009e7c76948200067f64948201b67e64948200067d64948201b67c64948203457f73948203457d739482033e7f63948201ae7e639482033e7d63948201ae7c639482009d7e729482009f6e72948200e67e62948202067e61948200077a70948200077970948200d67e60948200dcff7690820014fd7690820016be6490820006bd6490820005fa7090820005f970908200dcff76508200057f755082009d7c7550820005df735082008ddc7350820006f761984200057f755842009d7c7558420004ff75584200067f75584200047f755842001cfe7558420004fd755842001cfc75584200067c755842001c7c7558420004ff7458420014fe7458420014fc7458420004ff735842000cfe7358420004fd735842000cfc73584200067f53584200067d53584200067e52584200067c5258420006f65158420006f55158420
  | 13 => 0x8520006f55418520006f45418520026f77318520026f67318520026f57318520026f47318520006f75318520006775318520006f65318520006f55318520006755318520006f45318520006f74318520006f64318520006f54318520006f44318520026f77218520006f75218520006f65218520006765218520006f55218520006f45218520006745218520006f74218520006f64218520006f54218520006f44218520006f73218520006f63218520006f53218520006f43218520026f77018520026f57018520006f75018520006f65018520006f55018520006f45018520006f74018520006f44018520006f73018520006f63018520006f53018520006f43018520006f52018520004fe7690520004fd7690520024fc76905200c57e75905200057d75905200067f65905201867c6590520006bf6490520016bc6490520006df639052017edc6390520005ee7290520005ed7290520006f76190520026f46190520004ff7650520004fe7650520004fc76505200067f65505201767c6550520006bf6450520016bc6450520006df635052016edc6350520006f76150520026f46150520004fe76c85200067f65c85201667c65c8520006bf64c852015ebc64c8520006df63c8520126dc63c85200076e52c85203976c52c8520026f461c8520005ee76c8520006ee76c8520004ee76c85200076f65c85203976c65c8520007af64c8520007ac64c8520007cf63c852038fcc63c852038f6f53c852038f6d53c8520007e761c8520026ee61c8520026ec61c8520007e461c8520026e461c8520005ee70c85200c57e75885200057d75885200067f65885201567c65885200bdbe7488520005bd7488520006bf648852014ebc64885200b5de7388520005dd7388520006df6388520146dc6388520385ed7288520006f76188520026f46188520005fa7088520005f97088520024fc76485200057f75485200c57c75485200067f654852013e7c6548520006bf6448520136bc6448520006df634852012edc63485200076e524852037f6c5248520006f76148520026f46148520005fb7048520005f87048520024ec76485200076f754852037f6c75485200076f654852037f6c6548520007af6448520007ac6448520007cf6348520377cc63485203776f53485203776d5348520007e77148520007e76148520026ee6148520026ec6148520007e46148520026e46148520007eb7048520005ec7048520007e87048520004fe76085200067f650852011e7c6508520006bf6408520116bc6408520006df630852010edc630852036dee7208520006f76108520026f461085200dcfe76901200067f65901201067c6590120006bf6490120016bc6490120006df63901200fedc6390120006f76190120006f46190120014ff76501200bcfd7650120014f
  | 14 => 0x67f53d85200067d53d85200067e52d85200067c52d8520006f751d8520006f651d8520006f551d8520006f451d8520006f741d8520006f441d8520006f731d8520006f631d8520006f531d8520006f431d8520024fe70d8520006f765d85200077765d85200067765d8520006f665d8520006f565d8520006f465d85200077465d85200067465d8520006f764d8520007b764d8520006b764d8520006f664d8520006f564d8520006f464d8520007b464d8520006b464d8520006f763d8520007d763d8520006d763d8520006f663d8520006f563d8520006f463d8520007d463d8520006d463d85200077753d85200077553d8520007e772d85200077652d85200077452d8520006f775d8520006f675d8520006f575d8520006f475d8520006f774d8520006f674d8520006f574d8520006f474d8520006f754d8520006f654d8520006f554d8520006f454d8520006f773d8520006f673d8520006f573d8520006f473d8520006f753d85200067753d8520006f653d8520006f553d85200067553d8520006f453d8520006f743d8520006f643d8520006f543d8520006f443d8520006f772d8520006f752d8520006f652d85200067652d8520006f552d8520006f452d85200067452d8520006f742d8520006f642d8520006f542d8520006f442d8520006f732d8520006f632d8520006f532d8520006f432d8520006f770d8520006f570d8520006f750d8520006f650d8520006f550d8520006f450d8520006f740d8520006f440d8520006f730d8520006f630d8520006f530d8520006f430d85200c57e75985200057d75985200067f65985200067c65985200bdbe7498520005bd7498520006bf6498520006bc64985200b5de7398520005dd7398520006df6398520006dc6398520006f761985200057f75585200c57c75585200067f65585200067c6558520005bf74585200bdbc7458520006bf6458520006bc6458520005df73585200b5dc7358520006df6358520006dc63585200067f65185200067c6518520006bf6418520006bc6418520006df6318520006dc6318520026f66118520006f56118520005f67618520006f67618520006f76518520007776518520006776518520006f66518520006f56518520006f46518520007746518520006746518520006f76418520007b76418520006b76418520006f66418520006f56418520006f46418520007b46418520006b46418520006f76318520007d76318520006d76318520006f66318520006f56318520006f46318520007d46318520006d46318520007775318520007755318520007e57218520007765218520007745218520026f77518520026f67518520026f57518520026f47518520026f77418520026f67418520026f57418520026f47418520006f75418520006f6541
  | 15 => 0xf7359120006df7359120004df735912000cfe7359120004fd735912000cfc7359120006dc735912000cdc73591200067f53591200067d53591200ccff7259120006ef72591200067c5259120004ff7159120006f77159120004f77159120024fc7159120006f47159120024f471591200dcff7059120006fb7059120005be76191200bebe7619120004be7619120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c6519120006bf6319120006be6319120006bd6319120006bc63191200079c63191200069c63191200073f53191200073d53191200073c52191200b5de76d8d200b6de76d8d2000cde76d8d200075f75d8d200075c75d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d200079f64d8d200069f64d8d20006de64d8d20006dd64d8d20006dc64d8d200079c64d8d200069c64d8d200075c52d8d20006df75d8d200065f75d8d20006de75d8d20006dd75d8d20006dc75d8d200065c75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d20006df72d8d200b6de72d8d200b6dd72d8d200b6dc72d8d20006df52d8d20006de52d8d20006dd52d8d20006dc52d8d200065c52d8d20006df42d8d20006dc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d20006de51d8d20006dd51d8d20006dc51d8d20006df41d8d20006dc41d8d20006df70d8d200b6de70d8d200b6dd70d8d200b6dc70d8d20006df50d8d20006de50d8d20006dd50d8d20006dc50d8d20006df40d8d20006dc40d8d200b6dd20d8d200057e76949200d67e76949200d47e76949200067f64949200073f64949200063f64949201b67e64949200067d64949201b67c64949200073c64949201b63c64949203a57f73949203a57d739492039e7f63949200075f63949200065f63949201ae7e639492039e7d63949201ae7c639492039f5c63949201ae5c63949200c57e72949200c76e72949202067c61949200ccfe76909200067f65909201a67c6590920006bf6490920016bc6490920006df639092019edc6390920014fc76509200057f75509200c57c75509200067f65509201967c6550920006bf6450920016bc6450920005df73509200b5dc7350920006df635092018edc63509200bfac4250920005fb7050920005f870509200067f65d85200067c65d8520006bf64d8520006bc64d8520006df63d8520006dc63d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520014fe74d8520004fd74d8520014fc74d8520004ff73d852000cfe73d8520004fd73d852000cfc73d8520
  | 16 => 0x95200c57c72d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d95200c67e72d952001c7e72d95200c67d72d95200c67c72d952001c7c72d95200067f42d95200067c42d95200067f32d95200067e32d95200067d32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95200067f70d95200c67e70d95200c67d70d95200c67c70d95200067f40d95200067c40d95200067f30d95200067e30d95200067d30d95200067c30d95200c67d20d9520014fe76d91200067f65d91200067c65d91200bebe64d9120006dc63d9120004ff75d912001cfe75d9120004fd75d912001cfc75d9120006bf54d91200bebe54d9120006bd54d91200bebc54d9120004ff73d912000cfe73d9120004fd73d912000cfc73d91200067f53d91200067d53d91200bebf43d9120006be43d9120006bd43d91200bebc43d9120014fe72d91200bcfd72d9120014fc72d91200067c52d91200bebf42d9120024fe71d9120004fd71d91200bebf41d91200bebc41d91200bcfd70d91200bebf40d91200bdbe76d9120014be76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120006bf63d9120006be63d9120006bd63d9120006bc63d91200079c63d91200069c63d91200073f53d91200073d53d91200073c52d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d91200063f53d9120006be53d9120006bd53d91200063d53d9120006bc53d9120006bf72d91200bebe72d9120006bd72d9120006bf52d9120006be52d9120006bd52d9120006bc52d91200063c52d9120006bf32d9120006be32d9120006bd32d9120006bc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006bf31d9120006be31d9120006bd31d9120006bc31d9120006bf70d91200bebe70d9120006bd70d9120006bf50d9120006be50d9120006bd50d9120006bc50d9120006bf30d9120006be30d9120006bd30d9120006bc30d91200057f75591200c57c75591200067f65591200067c65591200bebc6459120005df73591200b5dc7359120006dc6359120005f77159120005f47159120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c75591200bcff7459120006bf7459120004f
  | 17 => 0x16bc6490a20014ff7650a200057f7550a200d57c7550a201967e6550a200067d6550a20016be6450a20006bd6450a20005df7350a200a5dc7350a20005fb7050a20005f87050a200d57e75d86200057d75d86200067e65d86200067d65d86200067e65986200067d6598620006f761986200067e65586200067d6558620004ff755862001cfe7558620004fd755862001cfc7558620004ff7458620014fe7458620014fc7458620004ff735862000cfe7358620004fd735862000cfc73586200067f53586200067d53586200067e52586200067c52586200d57e75186200057d75186200067e65186200067d65186200cdbe7418620005bd74186200a5de7318620005dd7318620026f66118620006f56118620024ff7690620004fe7690620004fd76906200d57e75906200057d75906201867e65906200067d6590620004ff7650620004fd7650620004fc76506201767e65506200067d6550620016be6450620006bd6450620005ef7250620005ec72506201667e65c86200067d65c86200d57e75886200057d75886201567e65886200067d65886200cdbe7488620005bd74886200a5de7388620005dd73886200076e52886203d76c5288620026f66188620006f56188620005fa7088620005f970886201e76e75886201e76d75886203d76e65886200076d65886201e7ae74886201e7ad74886201e7ce73886201e7cd73886203cf6f53886203cf6d53886201e7e661886201e6ed6188620007e561886201e7ea7088620005ed70886201e7e97088620024ff76486200057f75486200d57c754862013e7e65486200067d6548620026f66148620006f56148620005fb7048620005f8704862011e7e65086200067d65086200076e52086203c76c5208620026f46108620007e52108620005ed76086201e6ed76086203c76e65086200076d65086203bf6f53086203bf6d53086201e7e67108620007e761086201e6ed61086201e7e46108620005ed7008620014fe7690220014fd76902201067e65902200067d6590220016be6490220006bd6490220005ee7290220005ed7290220094ff76502200057f75502200d57c75502200f67e65502200067d65502200e67e65c82200067d65c82200076e52c82203af6c52c8220005ed76c8220006ed76c82203af6e65c82200076d65c82203b76f53c82203b76d53c82201e5ee71c8220006ed61c82203afea50c82203afe950c8220005f976c8220006f976c82203af7a65c82200077965c82203b77b53c82203b77953c82200077a52c82203afea52c82200076a52c82203afe952c82203af7852c82200c57e76d95200c67e76d952001c7e76d95200067e64d95200067c64d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95200075c63d95200065c63d
  | 18 => 0xa70c8720007e970c87200e57e75887200057d75887200ddbe7488720005bd74887200adde7388720005dd73887200057f75487200e57c75487200076e52487203ef6c5248720005ef7648720006ef76487200076f75487203ef6c754872031f6f534872031f6d5348720007e77148720026ee6148720026ec6148720005ec7048720026f66108720006f56108720005fa7008720005f970087200bcfd7690320006bf6490320016bc6490320014ff7650320014fc76503200057f75503200e57c7550320016be6450320006bd6450320005ef7250320005ec72503200d57f76596200d67f765962001c7f76596200067e64596200067c64596200057f73596200057d73596200067f63596200067e63596200067d63596200067c63596200067f74596200067e74596200067d74596200067c74596200067f73596200047f73596200067e73596200067d73596200047d73596200067c73596200067f43596200067e43596200067d43596200067c43596200d67f72596200d67e72596200067d72596200d67c72596200067f42596200067c42596200067f32596200067e32596200067d32596200067c32596200067f71596200067e71596200067d71596200067c71596200067f41596200067c41596200067f31596200067e31596200067d31596200067c31596200d67f70596200067e70596200d67d70596200d67c70596200067f40596200067c40596200067f30596200067e30596200067d30596200067c30596200d67e20596200d57e75d92200057d75d92200067e65d92200067d65d92200cebe64d92200a5de73d9220005dd73d9220004ff75d922001cfe75d92200067e75d922001c7e75d9220004fd75d92200067d75d92200047d75d922001cfc75d92200ccfd74d9220004ff73d922000cfe73d9220006de73d922000cde73d9220004fd73d9220006dd73d9220004dd73d922000cfc73d92200067f53d92200067d53d92200cebf43d9220006bd43d9220006ed72d92200067c52d92200cebc42d9220024fe71d9220004fd71d9220006fa70d9220014ff76592200067e65592200067d65592200cebc6459220004ff755922001cfe7559220004fd755922001cfc7559220006bf7459220004ff735922000cfe7359220004fd735922000cfc73592200067f53592200067d5359220006be43592200cebc43592200067c52592200cebf4259220004ff7159220024fc71592200cebf41592200cebc40592200057d7694a200c67d7694a200c47d7694a200067f6494a201b67e6494a200067d6494a201b67c6494a203e57f7394a203e57d7394a203de7f6394a201ae7e6394a203de7d6394a201ae7c6394a200d57e7294a200d76e7294a202067e6194a2009e7e6094a200bcfd7690a201a67e6590a200067d6590a20006bf6490a20
  | 19 => 0x85400057f75485400f57c75485400067f654854013e7c6548540004fe7608540004fd7608540024fc76085400067f650854011e7c6508540015be7408540005bd7408540006ef6208540006ec6208540006f76108540026f461085400073f6590140106be6590140106bc659014040f3c65901401063c6590140416bf6390140416bd63901404173f53901404173d5390140006bc62901400073e529014040f3c5290140005bd7190140256bc6190140015be7090140017ba7090140016bf6090140017bb60901400e57e75d93200057d75d93200debe64d9320004ff75d932001cfe75d93200067e75d932001c7e75d9320004fd75d93200067d75d93200047d75d932001cfc75d93200dcfd74d9320004ff73d932000cfe73d9320004fd73d932000cfc73d93200067f53d93200067d53d9320006ee72d93200067c52d9320024fe71d9320004fd71d93200debf41d9320006f970d93200debc40d9320014ff76593200debc6459320004ff755932001cfe7559320004fd755932001cfc7559320006bf7459320006bf54593200debc5459320004ff735932000cfe7359320004fd735932000cfc73593200067f53593200067d53593200debf4359320006bd43593200067c52593200debc4259320004ff7159320024fc71593200debc41593200debf405932001e7e7694b2001e7d7694b200067f6494b201b67e6494b200067d6494b201b67c6494b204057f7394b204057d7394b203fe7f6394b201ae7e6394b203fe7d6394b201ae7c6394b200e57e7294b200e76e7294b202067e6194b200077a7094b20007797094b20014fd7690b20016be6490b20006bd6490b20005fa7090b20005f97090b20094ff7650b200057f7550b200e57c7550b20005df7350b200addc7350b200dfac4250b200e57e75d87200057d75d87200ddbe74d8720005bd74d87200adde73d8720005dd73d87200e57e75987200057d75987200ddbe7498720005bd74987200adde7398720005dd7398720006f76198720004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720014fe7458720014fc7458720004ff735872000cfe7358720004fd735872000cfc73587200067f53587200067d53587200067e52587200067c5258720026f66118720006f56118720024ff7690720004fe7690720004fd76907200e57e75907200057d7590720016be6490720006bd6490720005ee7290720005ed7290720004ff7650720004fd7650720004fc7650720006bf6450720016bc6450720005fb7050720005f87050720024fd76c87200076e52c87203f76c52c8720026f661c8720006f561c8720005fa70c8720005f970c8720024ed76c87203376f53c87203376d53c8720026ee61c8720007e661c8720007e561c8720026ec61c8720005ee70c8720007e
  | 20 => 0x67e75d894001c7e75d8940004fd75d89400067d75d89400047d75d894001cfc75d8940004ff73d894000cfe73d8940004fd73d894000cfc73d89400067f53d89400067d53d89400067c52d89400ceee42d89400ceed42d8940006ef32d8940006ec32d8940024fe71d8940004fd71d89400f57e75989400057d75989400067f65989400067c6598940006ef62989400bdf970989400057f75589400f57c75589400067f65589400067c6558940005df73589400eddc7358940005f77158940005f471589400ddfb70589400f57c75189400067f65189400067c6518940006ed6218940004ff75189400067f751894001cfe7518940004fd751894001cfc75189400067c751894001c7c7518940004ff731894000cfe7318940004fd731894000cfc73189400067f53189400067d53189400067c5218940096ee4218940096ed4218940006ef3218940006ec3218940024fe7118940004fd7118940096bf4118940096bc40189400067f76949400057e76949400067e76949400047e76949400067d76949400057c76949400067c76949400047c76949401b67f649494043d7f739494043d7d73949404367f63949401ae7e63949404367d63949401ae7c639494042d7e72949400f76e72949400067f62949400067c62949402067c61949401b73f41949401b67f60949401b77b40949401b73c40949401b77840949400067f65d85400067c65d8540004ff75d854001cfe75d8540004fd75d854001cfc75d8540004ff73d854000cfe73d8540004fd73d854000cfc73d85400067f53d85400067d53d8540004fe72d8540004fd72d85400067e52d85400067c52d8540066f641d8540066f541d8540006f731d8540006f431d85400f57e75985400057d75985400067f65985400067c6598540006f76198540055f970985400057f75585400f57c75585400067f65585400067c6558540005df73585400eddc7358540005ef7258540005ec725854007dfb70585400067f65185400067c6518540026f66118540006f56118540024bc76505400073f6550540176be6550540176bc655054041f3c65505401763c6550540426bf6350540426bd63505404273f53505404273d5350540006bc62505400073e525054041f3c5250540015bf7150540017b77150540007b76150540026be6150540026bc6150540007b46150540007bb7050540005bc7050540007b87050540016bf6050540017bb6050540004fe76c8540004fd76c8540004fc76c85400067f65c85401667c65c8540006f761c8540026f461c8540004fe7688540004fd7688540024fc76885400f57e75885400057d75885400067f65885401567c6588540015be7488540005bd74885400edde7388540005dd7388540006ef6288540006ec6288540004ff7648540004fe7648540004fc764
  | 21 => 0xc5290a40255be7190a40007ba7090a40005bd7090a40007b97090a40016be6090a40017ba6090a40035fa70d8640006f761986400057f75586401057c7558640004ff75586400067f75586400047f755864001cfe7558640004fd755864001cfc75586400067c755864001c7c7558640006bf5458640056bc5458640004ff735864000cfe7358640004fd735864000cfc73586400067f53586400067d5358640056bf4358640006bd4358640004ff7258640004fc72586400067e52586400067c5258640006be4258640056bc4258640056f64158640056f54158640256bc4158640056bf40586401057e75186400057d75186400fdde7318640005dd7318640005ee7218640005ed7218640026f66118640006f56118640065fa7018640105be75906402573e75906401053e75906402573d7590640255bc7590640255bf7390640465bd739064045f3f539064045f3d5390640005be72906400073e52906404573c5290640015be7190640017b67190640257b66190640256bd6190640007b56190640257ba7090640005bd7090640257b97090640016be6090640017ba6090640004ff76c8640004fe76c8640004fd76c8640015be74c8640005bd74c8640006ee62c8640006ed62c8640024ff7688640004fe7688640004fd76886401057e75886400057d7588640015be7488640005bd74886400fdde7388640005dd7388640004ff7648640004fd7648640004fc76486400057f75486401057c7548640005bf7448640015bc7448640006ee6248640006ed6248640024ff7608640004fe7608640004fd7608640255bf7408640015bc740864044d7e76d95400f67e76d954001c7e76d95400057f73d95400057d73d95400067f63d95400067e63d95400067d63d95400067c63d95400057e72d95404473f41d95404477b40d95404473c40d95404477840d95404467f74d95404467e74d95404467d74d95404467c74d95400067f73d95400047f73d95400067e73d95400067d73d95400047d73d95400067c73d95404467f43d95404467e43d95404467d43d95404467c43d95400067f72d95400067e72d95400047e72d95400067d72d95400067c72d95404467f42d95404467e42d95404467d42d95404467c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95404467f41d95404467e41d95404467d41d95404467c41d95400067f31d95400067e31d95400067d31d95400067c31d95404467f70d95400f67e70d95404467d70d95404467c70d95404467f40d95404467e40d95404467d40d95404467c40d95400067f30d95400067e30d95400067d30d95400067c30d95400f57e75d89400057d75d89400067f65d89400067c65d8940004ff75d894001cfe75d8940
  | 22 => 0x821005f5719082115cff76508210057f755082111d7c7550821005df735082110ddc7350821117ac4250821025f77648421006f77648421004f7764842100777754842149f747548421497775348421497755348421025f77248421027e772484214a6f66248421027e6624842100776524842149fe6524842100766524842149fe5524842149f745248421007e64248421007e54248421497e63248421497e53248421005f47048421004ff759802101cfe7598021004fd759802101cfc7598021014fe7498021004fd7498021014fc7498021004ff739802100cfe7398021004fd739802100cfc73980210067f53980210067d53980210067e52980210067c5298021026fa7098021006fa3098021006f93098021026fb1098021026f81098021004ff75580210067f75580210047f755802101cfe7558021004fd755802101cfc75580210067c755802101c7c7558021004ff7458021006bf7458021004bf7458021014fe7458021014fc7458021006bc7458021014bc7458021004ff7358021006df7358021004df735802100cfe7358021004fd735802100cfc7358021006dc735802100cdc73580210067f53580210067d53580210067e52580210067c5258021026ef2158021026ed2158021026fb7058021006fa3058021006f93058021026fb1058021026f41058021026f810580211057e75d8a400057d75d8a400fdde73d8a40005dd73d8a40095fa70d8a40006ef6298a40004ff7598a4001cfe7598a40004fd7598a4001cfc7598a40004ff7398a4000cfe7398a40004fd7398a4000cfc7398a400067f5398a400067d5398a400067c5298a400deee4298a400deed4298a40024fe7198a40004fd7198a400057f7558a401057c7558a40004ff7558a400067f7558a400047f7558a4001cfe7558a40004fd7558a4001cfc7558a400067c7558a4001c7c7558a40004ff7358a4000cfe7358a40004fd7358a4000cfc7358a400067f5358a400067d5358a400bebf4358a40006bd4358a400067c5258a400beee4258a400beed4258a400bebc4258a40004ff7158a40024fc7158a40006ed6218a400cdfa7018a400067f7694a400067e7694a400067d7694a400067c7694a401b73e7494a400073d7494a401b67d6494a4048d7f7394a4048d7d7394a404867f6394a401ae7e6394a404867d6394a401ae7c6394a401b73f4394a404873d4394a4042d7e7294a401076e7294a400067e6294a400067d6294a401b73c4294a402067e6194a401b73c4194a401b67e6094a401b73f4094a401b77b4094a401b7784094a40105be7590a40105bc7590a4047dbf7390a4047dbd7390a4019ebe6390a4019ebc6390a404773f5390a404773d5390a40015be7290a40017ae7290a40007ae6290a40006bd6290a40007ad6290a400073e5290a4046f3
  | 23 => 0x6f87059121004f870591210057e76949211567e76949211547e76949210067f64949211b67e64949210067d64949211b67c64949214d57f73949214d57d73949214ce7f63949211ae7e63949214ce7d63949211ae7c639492113d7e729492113f6e72949212076e219492114cfe76909210067f65909211a67c6590921016be6490921006bd6490921024fc76509210057f755092113d7c75509210067f65509211967c6550921006bf6450921016bc6450921005df735092112ddc7350921005f77150921025f47150921014ff7650521134fd7650521014fc76505210067f65505211767c6550521006bf6450521016bc6450521005ef7250521005ec7250521027e421505210067f65c85211667c65c8521025ee72c8521026ef62c85210077765c85214bf7465c85214c77753c85214c77553c8521025f672c8521026f762c8521027e762c85210077652c85214bf7452c85210067f65d81210067c65d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121014fe74d8121004fd74d8121014fc74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d81210067e52d81210067c52d8121006fb40d8121006f840d8121006fb30d8121006f830d812113d7e75981210057d75981210067f65981210067c6598121006fb60981210057f755812113d7c75581210067f65581210067c6558121005bf7458121135bc7458121005df735812112ddc73581210067f65181210067c6518121006f96018121004ff751812101cfe7518121004fd751812101cfc7518121014fe7418121004fd7418121014fc7418121004ff731812100cfe7318121004fd731812100cfc73181210067f53181210067d53181210067e52181210067c5218121006f721181211deee21181211deec2118121006fb4018121006f84018121006fb3018121006f83018121004ff755902101cfe7559021004fd755902101cfc7559021026bf7459021006bf5459021116bc5459021004ff735902100cfe7359021004fd735902100cfc73590210067f53590210067d5359021116bf4359021006bd4359021114fc72590210067c5259021116bc4259021024fe7159021024fc7159021026be4159021026bc4159021004ff7059021004fc7059021116bf40590211667f769482101e7e769482101e7d76948212067c76948212067f64948211b67e64948210067d64948212067c64948214b57f73948214b57d73948212067f63948211ae7e63948214ae7d63948212067c639482120d7e729482111f6e72948211667e62948212077671948210077571948212067e61948212076f21948212077621948212076d219482115cff7690821024fe7690821014fd7690821024fc7690821016be6490821006bd6490821025f6719
  | 24 => 0x552c86214df7452c8621004ff759822101cfe7598221004fd759822101cfc7598221014fe7498221004fd7498221014fc7498221004ff739822100cfe7398221004fd739822100cfc73982210067f53982210067d53982210067e52982210067c5298221006f72198221026f42198221026fa7098221026fb1098221026f81098221004ff755822101cfe7558221004fd755822101cfc7558221004ff7458221014fe7458221014fc7458221004ff735822100cfe7358221004fd735822100cfc73582210067f53582210067d53582210067e52582210067c5258221026ef2158221026ed2158221026fb7058221026fb1058221026f8105822113d7e76d952113e7e76d952101c7e76d95210067e64d95210067c64d95210057f73d95210057d73d95210067f63d95210067e63d95210067d63d95210067c63d952113d7c72d95212076e21d95212076c21d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210047f73d95210067e73d95210067d73d95210047d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95212067f72d952113e7e72d952113e7d72d952113e7c72d95210067f42d95210067c42d95210067f32d95210067e32d95210067d32d95210067c32d95210067f71d95212067e71d952113e7d71d95212067c71d95210067f41d95212067e41d95212067c41d95210067f31d95212067e31d95210067d31d95212067c31d95212067e21d952113e7d21d95212067c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067c40d95210067f30d95210067e30d95210067d30d95210067c30d95212067f10d95212067c10d9521014fe76d91210067f65d91210067c65d9121136be64d9121004ff75d912101cfe75d9121004fd75d912101cfc75d9121004ff73d912100cfe73d9121004fd73d912100cfc73d91210067f53d91210067d53d9121006be43d9121136bc43d9121024fd72d91210067c52d9121136bf42d9121134fd71d9121136bf41d9121004fe70d9121004fd70d9121136bc40d91210057f755912113d7c75591210067f65591210067c6559121136bc6459121005df735912112ddc7359121005fb7059121005f87059121004ff75591210067f75591210047f755912101cfe7559121004fd755912101cfc75591210067c755912101c7c7559121134ff7459121006bf7459121004ff7359121006df7359121004df735912100cfe7359121004fd735912100cfc7359121006dc735912100cdc73591210067f53591210067d5359121136bf4359121006bd435912114cff7259121006ef72591210067c5259121136bc425912115cff7159121006f77159121004ff7059121006fb7059121004fb7059121004fc7059121
  | 25 => 0x9221006bf7359221006be7359221006bd7359221006bc7359221006bf53592210063f5359221006be5359221006bd53592210063d5359221006bc5359221006bf7259221006bd725922114ebc7259221006bf5259221006be5259221006bd5259221006bc52592210063c5259221006bf3259221006be3259221006bd3259221006bc3259221026bf7159221026be7159221026bd7159221026bc7159221026bf5159221026be5159221026bd5159221026bc5159221026bf3159221026be3159221026bd3159221026bc3159221026bf2159221026be2159221026bd2159221026bc2159221006bf7059221006be7059221006bd7059221006bc7059221006bf5059221006be5059221006bd5059221006bc5059221006bf3059221006be3059221006bd3059221006bc3059221026bf1059221026be1059221026bd1059221026bc1059221006df7558e21006de7558e210065e7558e21006dd7558e210065d7558e21006dc7558e21006df7458e21006de7458e21006dd7458e21006dc7458e21006df5458e21006de5458e21006dd5458e21006dc5458e21146df7258e21146de7258e21006dd7258e21146dc7258e21006df5258e21006de5258e21006dd5258e21006dc5258e210065c5258e21006df4258e21006dc4258e21026df7158e21026de7158e21026dd7158e21026dc7158e21026df5158e21026de5158e21026dd5158e21026dc5158e21026df4158e21026de4158e21026dd4158e21026dc4158e21026df2158e21026de2158e21026dd2158e21026dc2158e21006df7058e21006de7058e21006dd7058e21006dc7058e21006df5058e21006de5058e21006dd5058e21006dc5058e21006df4058e21006dc4058e21026df1058e21026de1058e21026dd1058e21026dc1058e212057d7694a2113e7d7694a2113c7d7694a212067f6494a211b67e6494a212073e6494a211b63e6494a210067d6494a212073d6494a210063d6494a212067c6494a214f57f7394a214f57d7394a212067f6394a211ae7e6394a212075e6394a211ae5e6394a214ee7d6394a212075d6394a210065d6394a212067c6394a2120d7e7294a211576e7294a212067e6194a212076f2194a21134fd7690a211a67e6590a210067d6590a21016be6490a21006bd6490a2119ede6390a21006dd6390a21014ff7650a21024fc7650a210057f7550a211557c7550a211967e6550a210067d6550a21016be6450a21006bd6450a21005df7350a21145dc7350a2118ede6350a21006dd6350a2114fac4250a21005f77150a21025f47150a21025f576c8621006f576c86210277665c86210277565c8621027b664c8621027b564c8621027d663c8621027d563c86214e77753c86214e77553c8621027e672c86210077652c86214dfe652c86210076652c86214dfe
  | 26 => 0x24fc72593210067c525932115ebc425932115ebf4159321004ff7059321004fc705932115ebc405932101e7e7694b2101e7d7694b210067f6494b211b67e6494b210067d6494b211b67c6494b215057f7394b215057d7394b214fe7f6394b211ae7e6394b214fe7d6394b211ae7c6394b211657e7294b211676e7294b21007767194b21007757194b21024fd7690b21016be6490b21006bd6490b21025f67190b21005f57190b21114ff7650b210057f7550b211657c7550b21005df7350b21125dc7350b21014ff7650721014fc7650721016be6450721006bd6450721005ef7250721005ec72507211657e75d83210057d75d832115dbe74d8321005bd74d8321125de73d8321005dd73d83211657e75983210057d7598321006fb6098321004ff759832101cfe75983210067e759832101c7e7598321004fd75983210067d75983210047d759832101cfc7598321014fe7498321004fd7498321014fc7498321004ff739832100cfe7398321004fd739832100cfc73983210067f53983210067d53983210067e52983210067c52983211e6ee21983211e6ec2198321004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321014fe7458321014fc7458321004ff735832100cfe7358321004fd735832100cfc73583210067f53583210067d53583210067e52583210067c5258321006f960183210067f74596210067e74596210067d74596210067c74596210067f73596210047f73596210067e73596210067d73596210047d73596210067c73596210067f43596210067e43596210067d43596210067c43596211567f72596211567e72596210067d72596211567c72596210067f42596210067c42596210067f32596210067e32596210067d32596210067c32596210267f71596210267e71596210267d71596210267c71596210267f41596210267e41596210267d41596210267c41596210267f31596210267e31596210267d31596210267c31596210267f21596210267e21596210267d21596210267c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067c40596210067f30596210067e30596210067d30596210067c30596210267f10596210267e10596210267d10596210267c1059621004ff755922101cfe7559221004fd755922101cfc7559221026bf7459221006bf545922114ebe5459221006bd545922114ebc5459221004ff735922100cfe7359221004fd735922100cfc73592210067f53592210067d535922114ebf4359221006be4359221006bd435922114ebc43592210067c525922114ebf4259221024fc7159221026be4159221026bc4159221004ff7059221004fc705922114ebf405922114ebc4059221006bf7559221006be7559221006bd7559221006bc755
  | 27 => 0xd70d8941006ef6298941135f571989410057f75589411757c7558941005df735894116ddc735894115df77158941005fb7058941005f87058941006ed6218941004ff751894101cfe7518941004fd751894101cfc7518941024fd7418941004ff731894100cfe7318941004fd731894100cfc73189410067f53189410067d53189410067c5218941116ee4218941116ed4218941004fe7018941004fd70189410067f76949410067e76949410067d76949410067c76949411b73e74949410073d74949412067f649494152d7f739494152d7d73949415267f63949411ae7e63949415267d63949411ae7c63949411b73f43949415273d439494142d7e72949411776e72949410067f62949410067c62949411b73c42949411b67f61949411b77741949412073e41949412073c41949411b77441949411b73f4094941024be7690941175be7590941175bc759094151dbf739094151dbd739094119ebe639094119ebc63909415173f53909415173d5390941015be7290941017ae7290941006bf6290941007af6290941007ac62909410073e529094150f3c5290941025be7190941007b67190941007b57190941025bc7190941016bf6190941017b76190941005bd7090941004ff75d814101cfe75d8141004fd75d814101cfc75d8141024fd74d8141004ff73d814100cfe73d8141004fd73d814100cfc73d81410067f53d81410067d53d8141004fe72d8141004fd72d81410067e52d81410067c52d814107efa40d8141006fb60981410057f75581411757c7558141005df735814116ddc7358141005ef7258141005ec72581411757e75181410057d7518141006f96018141004ff751814101cfe75181410067e751814101c7e7518141004fd75181410067d75181410047d751814101cfc7518141024fd7418141006bf5418141036bc5418141004ff731814100cfe7318141004fd731814100cfc73181410067f53181410067d5318141036bf4318141006bd4318141004fe7218141004fd72181410067e52181410067c5218141006be4218141036bc421814124ebe411814124ebc4118141036bf4018141036f9401814115ebe64d9321004ff75d932101cfe75d9321004fd75d932101cfc75d932115cfd74d9321004ff73d932100cfe73d9321004fd73d932100cfc73d93210067f53d93210067d53d9321006ee72d93210067c52d9321006f571d9321004fe70d9321004fd70d9321014ff76593210057f75593211657c755932115ebc6459321004ff75593210067f75593210047f755932101cfe7559321004fd755932101cfc75593210067c755932101c7c7559321006bf745932115ebe5459321006bd5459321004ff735932100cfe7359321004fd735932100cfc73593210067f53593210067d535932115ebf4359321006bd4359321
  | 28 => 0x96410267c71596410267f41596410267e41596410267d41596410267c41596410267f31596410267e31596410267d31596410267c31596410267f21596410267e21596410267d21596410267c21596410067f70596410067e70596410067d70596410067c70596415467f40596415467e40596415467d40596415467c40596410067f30596410067e30596410067d30596410067c30596410267f10596410267e10596410267d10596410267c1059641004ff7598a410067f7598a4101cfe7598a41004fd7598a4101cfc7598a410067c7598a4101c7c7598a41004ff7398a4100cfe7398a41004fd7398a4100cfc7398a410067f5398a410067d5398a41026ee7298a410067c5298a4115eee4298a4115eed4298a41006ef3298a41006ec3298a41024fe7198a41026bf4198a41026bd4198a41026ee2198a41026ec2198a41004fe7098a41004fd7098a4115ebc4098a41004ff7558a410067f7558a410047f7558a4101cfe7558a41004fd7558a4101cfc7558a410067c7558a4101c7c7558a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a410067f5358a410067d5358a41026ef7258a410067c5258a41136ee4258a41136ed4258a41006ef3258a41006ec3258a41024fc7158a41026ee2158a41026ec2158a41004ff7058a41004fc7058a412057f7694a410067f7694a410047f7694a412067e7694a412057d7694a410067d7694a410047d7694a412067c7694a411b67d6494a4153d7f7394a4153d7d7394a412067f6394a411ae7e6394a415367d6394a412067c6394a4120d7e7294a411876e7294a410067e6294a410067d6294a412067e6194a412073f4194a411b7774194a41207744194a411b73c4094a41004ff759824101cfe7598241004fd759824101cfc7598241004ff739824100cfe7398241004fd739824100cfc73982410067f53982410067d5398241004fe7298241004fd72982410067e52982410067c5298241024fe7198241026fa7098241066f94098241026fb1098241026f81098241004ff755824101cfe7558241004fd755824101cfc7558241004ff735824100cfe7358241004fd735824100cfc73582410067f53582410067d5358241004ff7258241004fc72582410067e52582410067c5258241024fc7158241026bf4158241026bd4158241026fb7058241056fa4058241056bc4058241026fb1058241026f810582411757e75d89410057d75d8941004ff75d894101cfe75d89410067e75d894101c7e75d8941004fd75d89410067d75d89410047d75d894101cfc75d8941024fd74d8941004ff73d894100cfe73d8941004fd73d894100cfc73d89410067f53d89410067d53d894114ebf43d8941006bd43d89410067c52d894114eee42d894114eed42d894114ebc42d8941004fe70d8941004f
  | 29 => 0x5667d63949421ae7c63949425675c63949421ae5c63949421b73f43949425673d439494242d7e72949421976e72949421b67f62949421b76f42949421b73c42949421b76c42949421b72c42949422067c61949420073f659094254f3c659094255dbf739094255dbd73909420079f639094219ebe639094219ebc63909425579c639094219e9c63909425573f53909425573d5390942015be7290942017ae7290942016bf6290942017af62909420073e529094254f3c52909420067f65d85420067c65d8542006df63d8542006dc63d8542004ff75d854201cfe75d8542004fd75d854201cfc75d8542004ff73d854200cfe73d8542004fd73d854200cfc73d85420067f53d85420067d53d854215ebf43d8542006bd43d85420067e52d85420067c52d8542006be42d854215ebc42d854215ef641d8542004fe70d8542004fd70d85421957e75985420057d75985420067f65985420067c659854218dde7398542005dd7398542006df6398542006dc6398542006f761985420057f75585421957c75585420067f65585420067c6558542005df735854218ddc7358542006df6358542006dc6358542005fb7058542005f870585420067f65185420067c6518542006df6318542006dc6318542026f66118542006f561185420067f65d81420067c65d8142006df63d8142006dc63d8142004ff75d814201cfe75d8142004fd75d814201cfc75d8142004ff73d814200cfe73d8142004fd73d814200cfc73d81420067f53d81420067d53d81420067e52d81420067c52d8142024fe71d8142004fd71d81420defa40d81421957e75981420057d75981420067f65981420067c659814218dde7398142005dd7398142006df6398142006dc6398142006fb60981420057f75581421957c75581420067f65581420067c6558142005df735814218ddc7358142006df6358142006dc6358142005f77158142005f471581420067f65181420067c6518142006df6318142006dc6318142006f96018142004ff751814201cfe7518142004fd751814201cfc7518142004ff731814200cfe7318142004fd731814200cfc73181420067f53181420067d5318142096bf4318142006bd43181420067e52181420067c5218142006be4218142096bc4218142024fe7118142004fd7118142096f940181425467f74596415467e74596415467d74596415467c74596410067f73596410047f73596410067e73596410067d73596410047d73596410067c73596415467f43596415467e43596415467d43596415467c43596410067f72596410067e72596410067d72596410067c72596410047c72596415467f42596415467e42596415467d42596415467c42596410067f32596410067e32596410067d32596410067c32596410267f71596410267e71596410267d715
  | 30 => 0xd53982420067e52982420067c5298242024fe7198242004fd71982420cef94098242004ff755824201cfe7558242004fd755824201cfc7558242004ff735824200cfe7358242004fd735824200cfc73582420067f53582420067d53582420067e52582420067c5258242004ff7158242024fc71582420bebf41582420befa40582420bebc4058242006f9601824242d7e76d95421967e76d954201c7e76d95420057f73d95420057d73d95420067f63d95420067e63d95420067d63d95420067c63d95420075c63d95420065c63d95421b73f43d95420073d43d95421b57c72d95421b76f42d95421b73c42d95421b76c42d95421b67f74d95421b67e74d95421b67d74d95421b67c74d95420067f73d95420047f73d95420067e73d95420067d73d95420047d73d95420067c73d95421b67f43d95421b67e43d95421b67d43d95421b67c43d95421b67f72d95421967e72d95421b67d72d95421b67c72d95421b67f42d95421b67e42d95421b67d42d95421b67c42d95420067f32d95420067e32d95420067d32d95420067c32d95420067f71d95420067e71d95420067d71d95420067c71d95421b67f41d95421b67e41d95421b67d41d95421b67c41d95420067f31d95420067e31d95420067d31d95420067c31d95420067f70d95420067e70d95420067d70d95420067c70d95421b67f40d95421b67e40d95421b67d40d95421b67c40d95420067f30d95420067e30d95420067d30d95420067c30d954218dde76d8d4218ede76d8d4200cde76d8d420075f75d8d420075c75d8d42006df65d8d420075f65d8d420065f65d8d42006de65d8d42006dd65d8d42006dc65d8d420075c65d8d420065c65d8d420079f74d8d4218f9c74d8d420075c52d8d4257fcf42d8d4257f9c42d8d4257fcc42d8d42006df75d8d420065f75d8d42006de75d8d42006dd75d8d42006dc75d8d420065c75d8d4257edf74d8d4218ede74d8d4218edd74d8d4218edc74d8d4257edf54d8d4257ede54d8d4257edd54d8d4257edc54d8d4257edf72d8d4218ede72d8d4218edd72d8d4218edc72d8d42006df52d8d42006de52d8d42006dd52d8d42006dc52d8d420065c52d8d4257edf42d8d4257ede42d8d4218edd42d8d4257edc42d8d42006df71d8d42006de71d8d42006dd71d8d42006dc71d8d42006df51d8d42006de51d8d42006dd51d8d42006dc51d8d4257edf41d8d4257ede41d8d4257edd41d8d4257edc41d8d42006df70d8d42006de70d8d42006dd70d8d42006dc70d8d42006df50d8d42006de50d8d42006dd50d8d42006dc50d8d4257edf40d8d4257ede40d8d4257edd40d8d4257edc40d8d4242d7e76949425767e769494242c7e76949421b67f649494256d7f739494256d7d73949425667f63949420075f63949420065f63949421ae7e6394942
  | 31 => 0x86521657e72186522076e72186521656e721865220e7e621865211f6e62186522057e71186522067f61186522077661186522067d61186520077561186520067561186520057e70186520057d70186521b57e74d82520073e74d82521b53e74d82520057d74d82520073d74d82520053d74d82521b57c74d82520067f64d82520067d64d82520057f73d82521ad7e73d82520057d73d82521ad7c73d82520067f63d82520067d63d825209d7e72d82520076e72d825209d6e72d82520e67e62d82520e76e62d82522057e71d82520057d71d82520067f61d82520067d61d82520c57d76982521b57e74982520057d74982521b57c74982520067e64982520067c64982520057f73982521ad7e73982520057d73982521ad7c73982520067f63982520067d63982520d67e62982520d76e62982522057e71982520057d71982520067e61982520067c61982520067f60982520077b60982520057f74582521b57e74582521b57c74582520067f64582520067d64582520057f73582521ad7e73582520057d73582521ad7c73582520067f63582520067d63582520c67e62582520c76e62582520057f71582522057c71582520067f61582520067d61582520077b60582520067e60582521b57e74182520057d74182521b57c74182520067e64182520067c64182520057f73182521ad7e73182520057d73182521ad7c73182520067f63182520067d63182520e57e72182520076e72182520e56e721825209e7e621825209f6e62182522057e71182520057d71182520067e61182520067c61182520d57e70182520067f60182520077a60182520067d60182520077960182520067960182521b67f7694a4201e7e7694a4201e7d7694a421b67c7694a421b73e7494a420073d7494a4258d7f7394a4258d7d7394a425867f6394a421ae7e6394a425867d6394a421ae7c6394a425873e4394a421b73c4394a4242d7e7294a421a76e7294a421b67e6294a421b73f4294a421b76f4294a421b72f4294a421b76c4294a422067e6194a421b73f4194a421b73c4094a42006f761986420057f75586421a57c7558642004ff75586420067f75586420047f755864201cfe7558642004fd755864201cfc75586420067c755864201c7c7558642004ff735864200cfe7358642004fd735864200cfc73586420067f53586420067d53586420067e52586420067c5258642136f64158642004ff7058642004fc70586421a57e75186420057d7518642026f66118642006f561186421a57e75d82420057d75d82421a57e75982420057d7598242006fb6098242004ff759824201cfe75982420067e759824201c7e7598242004fd75982420067d75982420047d759824201cfc7598242004ff739824200cfe7398242004fd739824200cfc73982420067f53982420067
  | 32 => 0x120000090004004002004004000400000c00000000000000000000013002802001800000880800040060038000006008002003c014002002800401000200380000100040098004000000003002400000200680400020080018000016000000004c000005004001c00e00c0000000002000003000c01e0030008000006012004801c02a000000006400200f009000400400000300300020000020008002011004000001a0000000000002000000000c018003000800400600700380380060000008010000002000801800c039000000000c00201000080000000000004004006001800000400100b0014010000005800402e0170008000000001000800400200100280100040090028000006001000000000000a0048070018000001000402c00a003804400a012001800802a00e016800000c000002800400000100000280060020000008004005000000c01000001b8000028000008803000000200200240280051b57d74d92521b67e64d92521b73e64d92521b63e64d92521b67c64d92520057f73d92521ad7e73d92520057d73d92521ad7c73d92520067f63d92520067d63d92525957e72d92520076e72d92525956e72d92521a67e62d92521a76e62d92522057e71d92520057d71d92520057e70d92520057d70d92521b57f76592520073f64592521b67e64592521b67c64592521b73c64592521b63c64592520057f73592521ad7e73592520057d73592521ad7c73592520067f63592520067d63592521b73f43592520073d435925201d7c72592521967e62592521976e62592521b73c42592520057f71592522057c71592521b73f41592520057f70592520057c70592521b73c40592521b57e74d86520057d74d86521b57c74d86520067e64d86520067c64d86520057f73d86521ad7e73d86520057d73d86521ad7c73d86520067f63d86520067d63d865211d7e72d86520076e72d865211d6e72d86521667e62d86521676e62d86520057e70d86520057d70d865213d7d76986521b57e74986520057d74986522057c74986520067f64986520067d64986522057f73986521ad7e73986520057d73986522057c73986520067f63986520067d639865220e7e62986521576e62986522067f61986520077761986520057e70986520057d70986520057f74586521b57e74586521b57c74586520067e64586520067c64586520057f73586521ad7e73586520057d73586521ad7c73586520067f63586520067d635865213e7e625865213f6e62586520077761586522067e61586520057f70586520057c70586521b57e74186522073e74186521b53e74186520057d74186522073d74186520053d74186522057c74186520067f64186520067d64186522057f73186521ad7e73186520057d73186522057c73186520067f63186520067d631
  | 33 => 0x7800000e00100100100020000030018004000004801001600500000340180010000000014000000003001c00200280040080040000038000000002800801400300480140000220008000018000003800c000000000800400600e002800002200000600280040010010010004000000001c05a010000801400c00100d0008002010009000c000002008800c01600e004000c00c002000802c00000000000000000000020004024002000800804600700000300000080008000002004002801800000000b0028002040000000000800300f001c024007001003801400b001800804e0000138000012002000802401e0020010004032014000000000200f00500100020010000018014003003000c002005000801c006012004800c004000000002800000500a8030008000024000000a0070000004002000008001000600000500040000120030040006000008800400000400000000060040088004032004004800002e00500c80bc006002009000c010001000002401800000580140380020000000006005000000005a00000c803400000300d0000002017000801003800c0010000018021000000401c002000000c01c0050010004020005001002801002b01700000060000080000022004000001c00000200800700000160010000028007000000400200f00a803c0060030008048006002000802400200700700000020000008010000005000007001a00500a800800200000b002000400a000000800201100000000080010000080002001009800c006002000003400000d005004000000100500100020030008004008003000000400e0000028000002014000000c00800b0070064008005001000c0100000008010002014001004c000000000001c002004000801001c007000000c000005001800c00e000000000001a008000008c04000b000000000400200a8000002001001000800800b002800000002c00100780180000020048002000009002401c000000004001200300f0060022008006800000c00500380140000180008008002004000001c0020010070000000000000004c004000000003001800600a0000014000019007800c00a00380000060000018000020001003800400a0010068030004000008005400a0000048004014000003800400e000005800000200101600040020070000034000006001801c06e000001002000000f0010008000033000000002a016008006c00800000000000000050048000000004011801400a004006801c00200300480a009e007001807400800b000001000000000b0008006000000000001800500280000040020018004006000002802c000000002800002600f004000c0020030030000014001001000401e001000000001200a0020000082011002000800002a00e80000040000000000
  | 34 => 0xc02a003000800400a0010040000006000003801000a003001001c01600000000a00280000020058006000000000c004001007000400000a00080040000000000084004002000802000000300000040000070028014000003002002000c00f000000c00a000000800800000c0000004006002000800001a00000d003c000001001800c0020020048000004001000000001a000000800400200300100280260020008000022038001808801600200200000000020000024008000000000800600100580000040070000008004005002007800000e00c001400400600000000000080010000016000002001800c001007803c0000010018114000002003800000000100300180020020018004000013006000000800500a8050014002000800c01800a004801400e00700600040040010130004000002000000c00201f000000000a0030060000046000002000800000100100280020080000064024009001000c008003001000c01200000580000060000058000000000000002000a009000002000000a00f002400c004002801800c006000800400e0030090074016023000800000a0110070000000004001000000000b004000000200b0040008004005000001800c00100600080080020000014004003006803000000400200400080050000000000000002000c0000070000048002002003000800000800000400060050010000004012000800c00200700b0000004001000000001e005001800400000000400000060010000074010001000802401000f000801401401f000800000e0030000008004000003800000e001003801005600200400040300010050004002000002003400201d002004800c0060008024002003000003800000000180040040030008020040002002004802e0190010030020005001001c008006000801c02a00000a0004004003007002400400000400000100000000008008005006801004200700000340000010010034006001000800c00000100580080140380088008006000000802000000a0000000000011005800000400100f80000240090050060002005002800400400000c8000010006001000800800000400040020070000000014023001004400800200600000020030000010008000014000c008007001002800000d00180000020010018140000002007002002800001a804800a000000002c000003004801401001000480400220070000000012005001800c006002002800c024001001001c016003000000800600500e800000000100880d800000100b000c008000003002c000000007801400a00600100340000030010024000000005002c0060110018008002003000000402c00300080400000010000004008009004800400601b0000000010005001001400200000100200000000018014020002
  | 35 => 0x50c00004c28c6454b01be03bc000000000000000001e7800044080004bc400045d836a00000000068956193472a4e24f6346e0000095948f000000053407e913ac54204f14f331a000028c91eb44294551134dc61e200002bc943a207105f0be44c71800e6a084423714dd4413d34000411539855705b7363c616491c5f8000109f014c03f37900f423386330ba51742ff4abb529957407e14da44c81b144bc17842dc4bc04b10eb4dd80001928bf14ba4caf46cc8602394b57555550541bc0003e80b511104000023c7444fa07760110a613cd46f02bd0b910ce07e81d0c48355342a930389bd0210000000015b000048938e89030000bd013f8b0f39a50505008c7c2e9cf422e10000000087303b00001b246b00000fc849c00000001279000040c00009172be03ae35a482422382df2b1041525848522f5461d182936e1ee47983c3c00048ac27f487d3010000f733070c044aed32d000134a380059421d11401bd9243474068400008e900000002dfc00000000000000000000010728e4000000000005b800000000000000d3c1df030a568c17d4580006004000400e00300480040000030040024000001000000000000300180340040000098004014003000800400a00e0078010016005001800400c00000780180200010008014000004001806c0080020028004000000000000000000b000000000c00000100100020090000040016003007801800000000f001c020004000003c004008000000000000c00000000000030008008000002001000000c008005800400400c0008008018001000000c03c00c000001c00000000c000c00a0020008000010004000001402c00500000000000060008014006000000000400000000000040120020008008048002000800c0000020010000022000009000c000000002003403c0010040020000002000002400a0020000000016002000000c00e0000028004008000002000800800600080a00020000000000004000007800000201000200000040000028000012004003000001e0220040034044002000000001e0050000020002002000002c01400100000080060010098004016000002800c000017000002c006005000003400c00002a000000e000000002000200600a001c010001000002000000c005800400000100a80440040120068000000001000801400a0010008000002002000800808401c00880240000020000000000000000802000600e0058014000006002003400c010000000800e001000000c0080060010170004009001000402800000300280020000008000000000007000003002c0060000006017003001400a000009004000a002000000000000b007803000e000000001400c0020008048010000008800008a0090058078000002004000001a0050038000000009000800
  | 36 => 0x3c0000329117207c00008d0000167d52a477889e112c0002c2ce1b000000013610884a0d3b22418dee1b3c00000014de3c310b619bceb54fe85bc0000f3300000001e9000033dc93e410074641e03023e9c8130000fe9000000000000000000a6d03a10130d1d00336645800391344248ce5c0efc000200800021f067a43a4c77000080b1f907d34f38406449d43400010aa1e74a0d45b000000011854090f18372149545b4e3022a923c0ad12cd40b4115222847e00005390af534131b897a21542801b348a30e74d16431007d385c50e2354ca205ac1462b2002236a016a0b386312454aa32f50000000000000005a920b86dd09a400029545030000f3b1eb4ae9143400028183e42f4924d31594b200003670000b48556400007e400027f02a52f34b3d0001188220458203c0f24344400041580000000f11000000046f044600006461ea00000fe40003b842070d1000019003120000000000000020413b3406c41422440003b4c000566540a55e80f529ec0002784000000007c0000000000001200000003f5400053880000000c1a21ecf300000b4600012312eccd6c08a856a0000dd4000012004d4f9a3a691891b54d9b146c0004c08e3906d53af30f498f15dc2b343fc858227ccb73ddca7f164829b4a594e11ad1380142120c0000000143139b0000000000096f2d2c35e06244e74c5061b29386c2071544619ec9b33b81044000000049a03a70d40000000135700000000000392438d4c021f49d2000030e000000000000000f20000000000054c0c34458c88b00006630a21128000052643dd22e1b9d3b44824fbd305c00035f15b20000e940000000057559d0fd15312a2d5714394ea510ac18b3f0c0000ca8e0b51849ef4918774000050f00000000000b59512c000000034e29c0be7000054029ac14706a4000520924c000000041d8000000159700000000000009565404e2fe51560eb40d70000ebb000045a2298c142d010fc18184be34ac86700015a1000152e14c40001a5140527445dd00000004c403980000e6f364031b00000000000b7413ec4e132380000000d26000045f000020a49f41b427ed3e902647ac2df84ac483918020d508556a800042600002210f090000000000000030b885113c8d9d42640000cc8948444cac33ef8b9747340003cd0dfc05ec0002f0044f46540000da072f22513c52c84b1944dc00006382093c400000fec429389924041840002c606f900013d933847dd01894a23e310a90000fee1fc4000141c000000000032e40ba00001c9243800000003ff0ec49e4055000000000003e8c00033600003e28000000119c0d841a3561111a2f585f916b85fa3d20000000000002bd40e0000e992e9895e1eb8ea701d80001a4404b56ecb2b4da0000447c197000000050bc4542b1cfcd4ead3fd4c6400
  | 37 => 0x47a40004fd852020300001a5437d06b0d6000000292a1c10900500003fcc0000000000172914900009f138592770000e8255881da056151d27fcd484b84585375c4c44b68ca912306660000a77000000008ccecf1811114339067241200000d8871c0fb04e6000106b3be8513282d4562ef800e4718e2434fc00028440000000f84389d17054acbfc241c0d5273931c39909414938cf33078b5d26ac29434b07ef0000a2313807272da4dd80d04a83314d5140fc063047ec9434bd427b0d8c803209c38d4a9ce810bc4da01a0014a2a3cc404afc91d267011d0000000000020400010f812648091f24cb1347c0000c600002c494ae286100427d40000b7867016d0eda49ec000000000018091180000e6d0000000197cca808607962708b3c088000000015632b08000000061800010371a6c0002920000000000027acff6000036c3710e1d0000a2e0000b1e313405c20549d9259d23507351034648ce64e10e792d900a50d20ed2063d30727f441129655760000deb00012a64fe53c1000094b0000eea2ed8d9832fc00017bc00013780003cc92d83878da6354cc3a00000003a2055a08a158103e9420492c0005050ed800015833c95282407c0004be954f16c000021050022b54e444b280003c8c9500001460000000050e4e150000c0f000000019744a700000003ed405f1f452050000000000139148cce7310dcd9c4a7958d3f94c8306e46b60000cb800011cc2e7c391456445d4be00000a6946e0a0c0000000000089ce760000be50a3c000000090f49784da0ac00c60000b0235dc26001201442f3c9b8000150f000012e26d84fa406800032f84192a74e4733091d115504001af8f4515187a935745633f2539315995b64ee4d1d26653ef47f83dc1d30ff1042078e2ab0000192400041c000048bc7b7213c00000000003ded0b00b18000000061704d000037dc55d0001501399c0004f7402833580000000c36000012f1d9943c2608aed4d4468c3ec007717c123b2eec2ed3c1d2d1197910028a10e624480002f600001fb0000000000000013c200000002bbc25100000000000cc9000076e000062040d4331531926b000000057103b217a49dc20b000000009c0045d0f308751b1489800000000002a6c000000037406c91a039c146800000001f9400047e00000000b9c1ba00004adce1146e851a075c00000008e1098866000006bd0000000000000000000003ae8000000110f000121540e545f4ee83231904d8c2c000e71510cae071903e41f40000000000372cd051c590ad23f8b374ec52902ce001d13f04010000f5d0c913de171920f4b2400000014be0ab496c0000000000056911ed4b02af40000000000000000000004ca24402e400004d11a700000000000126ceb7237c89a32400000000000180400033c13c315b80001e
  | 38 => 0x2780000000b7a49980000000e4c00010cb509cbc2000034900001dd0a5c00025b552811c0d193b7873b0000dae2f10a0a0b346d91694cf9356935f1d7137f2324a54487910833348b717815a74138e9f08c08ad2dcc61a00bd2f434e805252a83fa172cbe6115d47525cccfc0fcc0a8199c62332300004948ee20000000351c0000000000000000000004584b0472e12d80000198d8a34080eb2d28669000072c17a8bb8344800037d88ac4abc040212895f00000005244edc2ea400031487243310222362505529b8e5405c813922c13db55ec98828510381534734542c8a118913350848a2b12c4436189c49112c8b49359866d3494abf0b283d64d0921c2ac89ac36a4ed51cc150c3b94aeb104c72611a802b29d000022f4d4d06d8c2a262800000000000000000000000000015820000d683900eaf15e000037f4ab835d89b24e9c5020eacf163b006b31b6c36629b0b040d6481835ec90c37352ad4694000097400012e09250c2000040f4000000061013703840000000000001700012ab4af10670000d9e360d101417907326f947a19a957207fd1574cd83bb1588ad31ab0000000075b1b901f42f68b360ac4000000139a0001485284826310744ce000120334407e228048364a84c994cd0f804f54bb7496c01f128cac527887ba1e2c00000008e748e0bb5052ce1f3fa08ae2fc000024f0a890000c2f0d44d2e355506519f8be30fdc4312168000000129838940001b4c000471000000009e816653ea4630b9345987541c40d0a2350faa21090c34d40a811ad409b3a1ce042118a490000bb154d8f5b3e70f7e2d6d4150000d8d321cf1c480400002f400044980005540000275100f00008c502252532064000561ce4b50408071d8cc44017536135e000013b926c23c4fa12d34ba14b78306050ca201248fb617041bd074809e00010d84d7878019f50422fad00a0c840463a781244ca471d26014c235bd4b638314eb3bdca8c3d48e3632cd17247895a5522c3ce2034ea043852d416e00000c2400017448774f4410f3db0cde3bb835f000000024d883f2cc51f43318cd31cd88b30000000000000000003892ffc00007000002c894f11f5c7113f1902c31ec0001ec13ed195400000000000000afc00000cf2d509f600008fb0e6c0000000000075000000002f6230cc7500000003e184820000000568800000000000000ff951a47c11a7c94d000031f0000000122d3270d300005364202000000035400000000000000000000008054d608fc3a308f311e949425d893400000100d809641d785a0000000019d05e729703883b7d18200009b110cc3862898000198806f41a85cd127889834d0b32166045102a946f03c52b8000071f0ed846d000013a3f6483b31e52c200012134d3c34033300002aa0e620000c45000000000000003d800
  | 39 => 0x99549a47a6000000049e0000000107555ac28e36c0f9e46a4b1d2a689c9251854a24c54a005e8f121e8899737450522720fa417a04cd0d512cb26954541add4d6279476f2ae4b1f0274fdc099ce5925ad22a563c3b03f481a7233142900000004ac40a00b8d51946687cf00010124014000000126700001aa000000000002293b5817000000003084d8049d400045383be2d9c03754092893de469308f8f4b355d0d407552d53ac02fc34ec90237b05ac002cb8c48b53314e651442b80cb200c000001e437b071c163169cac149f936620382014288f06553000000000000b980004a2ca98441018344300193e88000313c0005220d92415c45e158043f0000960261863e55380002908bfb00005b5000017600005c03bc4c4714ac000000000013080000000baf3840f011bf13b60f4c63b38dcbf2000000000000002db400000004d60000d9429990a65089220567c6c0476c9c532041dc0000aca51987c60730f5c564411e231cbe906e0cac276140400006e23a3429552e906d4174c270000d7f000068a38f07b12a40ae3307d18b00000000b4c00042c895244842ac00009bb3a100e9284cb8a50789da28bd2e300000001e70fb955294a735c0df923042724c200003bbcd0e03fcfbc04f85aa0bf444e49951d8229c43e4cb00002a9800000004234331561000000000c830f4b114480000000394064c1595094278000006fc1f609f831500000004de09a6167846114b88381f1c000173000000012584e30a4b4130ce245fc05701b04c140048a8387079441b800000000000000f40221526f00000000000a4f448cb150db800000014ff0000c20233c48f3d545e443ec000000000022d80001dac6a50000625221d5ba00000b14794895006c0001d2014000000001b2c2d7000000021e822b00005451b68039275482816745ff42910df3960771161857b24153383edceec46c8cc714d42f749245c430404123e1ce2c352857137e12485480a2d33007ce37cc0000ad80310000a31429400052011933e3d2df513512b030d2ec35914cc08501d610d4f2c3de07613af87f652dd32602cc79f56cc4430e5504a1f614f5008cccf4bc94fc31a93033cb86c54d200000b40000521c0004ae459327e012922e8e332a4c29e237118a44a45cf42546ba009826f15bcbd733a000053c89374d2c2e237700ac3804c6132549090000da43b9cae500001ab000000012013bc052000000014bb00003db18bc000371c4e437c52fd2b6c00000000002ad828645491f724f4feb175400008b8000078c7bd14e0c2348a0ec50000000526c0d03370f1d000003300007df2d3cabc085cef9000000000000000000c8a00006fb0000920028929f43709493fc0518000000000000000000fd43f8c5fd07f45a103f44c0000138f1bb426632ec000189935900000003
  | 40 => 0x8850a800000023bcd32e3f8920d0000e4d264cf0e0001394433c0003ee919e1b50000000000040fc0002dc4000149400046fc44846e40001dc837e285c000260c7e62e68a02334000012e52f93a003430e14f43000000001691b44c849f00000c0b1f20e55035908a1e8c19f0f341c300001c246a065153bc7120000000319d5a0514d09c55692cc2ab87cb31240960b640000bfc58d000000031440002f2069e064852753a8db800013400000f760dd4a3f12ec7282ce886f0e787bb09140071aa4000000147300000000000000000000000000000000000000000033a40003015317000000000000003ce94fa04588eb3bd00b000010ab25c4a350b50174000070e01e914631e04162ccc00023fd1e603d8000000000000000002f146d03d5937d3164000000000050fc0003efc00009cc0004a2018600000000e80c9149d00000000072121025c3b1889b0b308d15438069076cec100002912074b554c88b601bd0000000000042350683e64abe15b453b0000528100c000428000054c80003fa86cc000145a0338b064a4c862306481e42cd1731a242311bacc7a51f4cea434c86d047cf653a84cc836549a31878a72424d0fa0e3c0004ded02314480001a5c0000000fa555b079a014000011b800047a0df55648a0e000000050e003a3348844000114823b0eeb1024e280000e7a000007b1ec8708048d175432034244947683aa85210fc477d026920445553e316e8356060154b343159c506471539ad37e251055056e536d175c1a044643e605080005324481534c52c00000fb000000000005811da4d0030e13be000000042386362e093790000000000033d00000001e0c5d2460c73a2b015213c150d23cdceac04093a90c70e754a68f5135b497014413e00000ca44c307863eec000000036524c095444cc9533828ae7403000046d40004619072539800000002f03e211e13cc536b000000001a80004f1c9900000bde43c871b14d014c413c00000009e60000000403874a4f4c10d4ba8c9b000150856f914c0f7800004b4000542499d46b040d34801034e403870f10f1a1c28c9315b0df00000000236800005843d149851bb09b8652212000036c89184470a71000110d32d4b5800000002904dba31cc591024d26e1d88e0f52b526300011944dbc39a297c1af29790321a68e2f000030c00000c2472800031a48b537b51054144e5d00000004e846fa0190051106909700014c334f800035880004c2506911540581c787fb1d59198374c91e000000004cd57d30340003f013690f0000044b8f3d1a8c9d338a896313b4d312310fd616987403e4d4b134a02aa2198f5a34bc61507b8af90134add4acd2214b9cce500000000000199000000000000000000000132000000010310000000093939c03a89654bf800024582320000
  | 41 => 0x45f538b27b00000bd43e818b4000000021b19dd21b0000bef000000007c800056d40000000000160c0003eac3460ebcafa1c60dcf0000000257000000008be494400052580003f68000000092d4f100000000000000112a0000dac4c3c00000000002e955b15400673539525c407002a35641912434000000062b00010ef40014501d64a270000000052442500012d208641c8000026500000000000d35000000004a8000000101e00002361dc081409d40000000b0300008780f880000cc069d490401637f800034900000000000000052f034c3783b412e814b458c032000037a000012b8a073df14e8341c26c23b81f50000efe512533f12a40e00b3c1064ed54d5041411141e92722ced51618d14f00ae084e000000000000004ee090411cc0000d28035000153a2de523a229000000008343ac913b50343ea4e185c2074c81b2ad471352846053d4d5410af8dc03d1c0a738f90191b5c0732cfc0000000000000000053e0c5e0b6c2930000fcc1964000000000050b02a043f800038ec0002bd499154182e510885d0000091940ec0985000dc30a9c0005348000000000c00000002208aaf000000013e14a31de8d2309d800029f4000000144300000004ff882623a122536d00005374a6424d48922940dc51c5027d256ce8606747f748dc5a82b7caf11dec6f72a44c7f513ca3b13d4e02468c00038693f10c7903009a800000009a20f3c42e10f11af301c3900bb88b40fd412b33d8000000000000005743af50e81cccc29000152511a485d2c8cafd317c08b47246ad2dac55e504cd5447653e731410f90c4ce3f54700000e50239000000030e488c3e60a1936f0d72439c4e52e000002c5cba202a40003b5073d0e84bc90000ca54e907550c40c890bec0002f8400003e14bc25ec4ad3aac35200004974a0487252fc0000000000497400000009cf10e05723d7c0552e8021f10b0b8755a50f6350c0000000de544f80e116fc00000000003e5942347cc7b8022868348c878702c89b946dc3bc4750475547868f382558a077800055e525900f81533518fcb2c1c2af1cfd40300000003b38e8a0000d650000e92456c2c32ae846f00013a83d10d8600003fc15f4ac6354400000004df562d0580000b954c18f7515fd2840e2ca1600011f51e845c800011ad4840000000000000004cb0000d0100003271040b340a1400032752d02e7956d3ab505a05bca7c3380e60441d4b5192c4e82d3800000000002388000124c000030400000012d61cac00019385f2350878142f468b0000a04504502f2a788e3436512415f0c6b2eac13010e4a9506cc6a426693a223192db217139f4bb85bd28900003fd4487000116900000ee3a8d150394c14147b80001b492501d340830000ea92f3000005955af336cb2f4fd400024b84080000f940f60000
  | 42 => 0x13f81573187041e31d800011f12560c940b739ec32d01d00002b3c1f10fb546c0ee0fec116ce6506154c40a050ec4ce892a3249452353cde10f6853a4bec5de478c9c10dad12245f0a9c1e0907c1a402160f50b5e1d946434eb09b44fd0b2e1761236000024433c485649290711bc89d0000013f1fe53774908000000020b042951a000000033c80000000657000000034e0c541114a8d00005d3464400000007be000141b00006865190f2252f4ec4237545c548cbce091952d13647e0255d23d0e98dde3048a850000000003c0002b48a47107c8470000cee000000000004b553f80001624a650000f9b4cf000000001954ad45410000c2c0000000550c00000013320000784000159e00000c500001d142ec2570000e981ac48a239f824d36ac00053f4bf524c8b5f0f2c9213cbd546416d1dc218450a05a07171d14fe10d7035d0954f271769086220154912ac3392ac48503f78f0a19e53da3e440202678e950e952ff223cb990b048880000cbd00007d2414d5663ffcf6a04648d001e0cef0350a9f3d18d9125c800034184c510287f0163c44a3c5425e0c582c21b38edb10984d73e142892240fca47c82eb13195781e252081940b1a428c000000000028cd41835780002dd4dc100003fd2d58369290c4742c40ad94f580184eecb47000000016bca6a342079345693451f790dd107099f17ac83d3db80004a4446821b8bbd4ef4bc33054b5a16ccb0d2db8aa4000000000000003b314ac05145f112bc5e1446c38200001a63a444bd19603d229cc0002fe8d8b129800000000002eb8b0e08bc00000004950000000000143137a400025dd3df45c4000541c3e0208d00635841e8436d5bd1a04b8e0e700de00000003098cca19a00850000a3c369ceae20cc98b2a5864422fca880000f810000aa71bf54a44284000335000000013cd40d0ffb4f180004448c251cb4aa23b2064843b87852b7063d2234e8f21d5586444434f48f873e4ea91c32fa8fdb54f4f9d2efc0003eb8dbd3ce4e0607ac505269cc8412901e000014724b2143529a400000010ae1b94ab73160f92004400000007531549082361525549a833a35f4a78000000039fc1843c109cc48000000000f7200000000e293f81ac8045000037200002e8481800000000001220f142e0c000279c00001d47b34a54f7d50a0000083c000221937311484a52bdcc303a2c9131984eb82625580202040b4300ef53b2c1ca1c1c000000000000000003a5c2bb000000000000001bf8e710cb12f73758cd530c48541d4400038e132a1e94f28409520a1e3000001c54c82eb0b454cdcbf400000000000000383800053d8b9614d800021c115c0244000000004118a4000000000000000002718000280068e00002a30000a360000000522528008d4000000040508940004a640003fe81cf000
  | 43 => 0xf50b90871484000000054fc5c500000000000ed10000ff71c250414480fed4fac6e020dc75d381c00041f92bd17592dd1bcd02224a0000000000045e40000000f64109d3cb421013d004c000000126236a800000015ae0df0f083e990cd47b0f0d000108900000000000000000155d531538200015b000011ce00000002d4049400001ba2e745a44d705612b50a532b308a0162c0003978d6b17b80c94cf8a450000c4c2ba833e2f889b702209e90e04d27130d44433b00000000000000000041346af4cbc8fa000000020c00000f853ae000d07f48880002528ee84910ab00dc4fd3000062100000004a6c00004d8bcb1bbd46308992ce1f6853015606650000e46044ce6820106bf50f8000157c81a2ff8000000101d000024c2aa4ad053d000030fc2ec000000035006710968595182d1fa4c6c4ff4d3029014f549f0000c130000d8856212b00d340000000fdd1a2000022c42c52df11e74c4c0004fb8a941530c48066c155457d1f044e0000155c30400000000dd80000000fef2df400007844f00000db94171083046908720c80684ca115326bc462191540726610110000a294fc0f0b4a809a1000000027f800031bc00000003f20ff83f8319901832146ee44c00001af10600000a822ca8d8e46052a50dbcc1d51452d92134c9750700000000ad8000000000012240000175079050000000004bcc000195800011e41593d305fb010c50b3b0c00000000000000b0a31b0c0c1f5022d19f06e900000000000c8610bd36350ec4cc0000ef6000115406283c51844c6d457867f537079121a94d727c8d9f18a80003f612f638893953eb142b1a9c00000000000b48cb0199094c182545b39f53872e04f4909c48b814c8fce0bccc3528f49bf21781180ecc0000000e080000e51378083a119086548fcb2d0eb0000000114a0548cfb0001325059c93f04502d855a8b9b46d87c200014653da00dd15d833714a4fdf56394ec079555700002ae0000b90150d5641b04000084d2340000027365d07b2bf829600004781ba80004388de3000000000788f70c0516e135400051fc0000000c330af01a14aa110e3688547127557700005b23ff116410f55543ad8101384914247e4a210000cf5469016c52bcc82000147028b0bd310095b42444000133d3cc4c3903a00000000578000000133005fccfa3bec3ba4454d0f295819003493601f640b817240000a9136400002474e20eb30bd00000000e7230280001764d3907a4000484400000000000000000000116200012144084000000000000012ef14184280394000000000013e4c1100014e0000063800009c430f80000001535057105408ec76c1c3cb3902194360000000000000023d46dc2d7010c56b50790000000451432b3b647b400004f15434000000002453b8719000000042bd48639087e
  | 44 => 0xd70300e23000000025640004e350d11950000019c7fc0c889812390f2a515c6220000bb90000000000016d000095d28680000000f9737988f600004aa00011da1a1473234551d50000000000000000000000001300316d0d000007fd10c88963b8ceed3a880000000aab393c0000000e45461d131318082b171ca0535d07e74c613dc56accce000141d123800012187e30ca13ff0000fb13c8081725f50b830acdfb36dcc7e0028675101c5ce4ae8f623a711b055941794e141bc435447754908cd18380fe3db46ab14a8a8411643b7399949901841324338eb436084b0234d217025c3a323f4305280c9690aa0188000113429a00001d2c25847fd39e000104b33151c70000b6107ccc184e383ca000000004950363a142b200002e74fcc97c00008992c4c14d00000002a187d632d0aec00003d018207ca203c5be2fb818d01287971ce53530230bb4544c2790d611d743c060342e95a822bc59b1b215332c80a4a12fd4982360a8a0000eb93118619145d01521a400022a557f3a240000f040000000f66298800024ac00052a098d13b00003b740004fdc00000000000000cdd06dcc6537c8000300d29c2c451c1000036d000094e00006871c0c00051b51160000d1844d4000000035a31040002348a0c1240000000000000012c60000aa542d12b61d24d043d7800012dcf264b5c6a238c88f9036014e000086b1490984000004232514b400000003ff82e0000020d0000b290000000196872228d0cb619d94084dc80000000ba80f941ea00008974c8121a00001fa2acc00016280002e2533d0001091000085b0000f38302403b29f8705000026436ec9f7419870450ccc4b569000000000002fb4d1e28e80001f540003730000423c44c0000e5a08f119930ec5fc0001490000113917f80000f640001e48fc230a12180558000000061203686474de8e5b18510491404def1fe87bc2779598000000032a8b1b0a99481000000000015bc000000014cc0000000d7a00007d0000147942f813800001a53b245f40c346a0327c90000002b7136c00008fc00025089740000ae800000000000000287c07e3200000336856b0cd8000322c8ed000114153dd28f0000000287489c000144e2028dca000003c11b131d310c00000008214808dfa2c30de205f8004000053f56dcf7f310943242409a0386477e458527a531cbc738c46e150180000a7c00000007eb3be021e009400023091c239dd5c0270cc9c000032f0180b424ab8da5038800045dc00000000000000efd4bc13c8547cefc41b062800000004fb0a58000105929d54122b2c2dd0c513ad3fd0e6102ec84007388bb0bc92b409015754a1c1044db07c5283c2c82b24c8f2d94dbf24290bf14503c924e95120124000016531a2d4c92c20f031d533d50a00012e40000d2a0000000000000013
  | 45 => 0xae14b84f3ca764418e2b20bcae40179143472142e4f007412b84d1a06895602774f172e3c8392d10cfe0800fb34b1c1002dc020809dd0260200f69193c0b951286a84e8153b55a11f133acddf1cf08f81ed42ba2e489c7123498e1d402500f3002c435d49e3c0045c3d84f2b329d31156a5471011c421290046316391ea1bc50f411088ca5625343238026d2598a3715f82cb1c686c4549946200015443d043c7397d40923008cb52ac00000014594e5d26d4a1518e14240360a885e54b14000179874f4efc00024506f500000001b981cb00015473538000000137400004530c00000398c0000000d3d00000000000aaa538ccab2a8032900011a13188000549c5dc352c54e4fec9ea56b075741dcdaf564cdff3eb546b20947951c9400d18b023851f949a2a00da123bd24f1ed913a25e144c3c840cb094d2b20f9cb8b3bfc9620d54ec751d80004230849031c157505c37317894ce487528a4864747028cf8b4f241280e5844416ed3830fb918f000017100000000000000000143d000000024ec000373800007dc000315c0000b8517a00008682690b8500000001be11511c3400034d800031c00000000000000049f00008d900000002d8800045a80000000ced51d000052a4c0031d079919b8000000000000010da000006334c819600000001198fd7000000000000000000c9a0000000473ca7900000002c982103b28871046ca2a4d7457920b451d00000003c7c57a00012a91c1892600010c73284cdf3344a9910805230be02d128c02520014000411ca1535244340ea43bd392804c4dc027039b01fe24cc12209e85db0158cc3287916b32b494f037127c2f289db392125700002fe0001510000031a1c3116747d8700106ce0d18b911e4f94e4319ad22c159c00000014f90000548519c1ae16c45ed00000004bf15532fd9503000000000008a551600000fbc49c000008d0000000000000030f0000372553c00000000000db1000100906300000000ada1e35109329884b536cba40000bb22cb061f24a40000000a44157000017d43eb0d6c0e607b119b275c6d109204f600e033300004e94594575000088300000004b888064a34000000112c469cfb827b40000a280000000bbc092426813cc173300813b502c000057c0fc26c000012cc2c9224c00000000003f44ca02e194260000000000132b2bfc0000000000000000000000003d500000000000000000000002980690ab4000000042d4b6f0c44a3e47909244b0c0004688f36316942135d40004d500002fdc8b911d90e0539c5702420000000000011c536a00015403c0d02e339c0004a190ea0001539000086c00005ec000028221e40003bc037f26a051e3ed000000000003a74e831558d5b465c4d2555829c00012270ced17b45bcad130887ea000000054a4000570c3aa18d43
  | 46 => 0x32e800039b83190000447293019c0000c4a07c04b439580003ec80001f3102935604652c14000027c0003f140000000166021d4d408180000ed40004f413152f752a411007a03020cf83e540005548b1410902b50cd02152468a63121400043780000a752303e080d1200103c00002c055b80003afc2d528884042758357451d34943908db20453814c7863739380b61d811dd09d00000e38bc607f0ca34a382bf0000ce34b3cd21038c8c850582990000000533555857043dd061c79b000024a2d0449a2f440000000b680000000000000025546ca0c8002d43f4ff2000000014580000ed040f0000947000091f000059a36593523e392e00e88958115893900000000000000090400053a53b73304d1400009f9056806e50900002544317485800053b45040000d790f8cf8350dc000380c82200001690000ed7000010e000114d0f0934751a8e781ddc03438f40822ddd1bd1a64000498147b132496a1fb86c3507cccb5454000156c00010a90c200014e400001622980bb00984ad625154d13d9d11d4dc48644c582dc49fc8d7170d4923bc85ad15545d411fc68d2a5c3a41db4dd54d6d0624268b3e3dc1367000097e168c3990678000134cb2800011104324000000000000700f3376c0000000acd00000004f9894000000005238000249c0002c20000000002e2b983640c1cfd02fa0379214ce3402f0b1644f00003af0b66000000012880001c8caf300007aa246c00052cc000000142d3a580004b4c37a2bed15816ac0004d94000054477500006de000046700000004b94c9817d82fa2cc0773474d39d196d38a00003df00014fb00008de09ac20e3058a5b00009870000f290000d8714542ea3548ee61fb400011ac000000056455449683e7cb7b4118fa8295cba33c789ca097d56f4df07dc3a992a31c0455319b12391ae439303c8d9a0000000351464241913fc0cd4b88545c43026b872126f130512800a402052452d8ce7c4cece74313800054bd36200000000000588287075a23c8ddd01506e34b70da338611fd2c912c01d60696374947c047060d4fc8d5639480000000922019508b392510b4248f7a0000f4e000155f30dc9df14f9333183c00003b4a3834b4f593cb4fe40cb8f9000006a1218c00000002c426589ba013c85f00000000cfc7293424ea8153c9754a88ade3ba400056e12eb000083e0248df434714972948db32f6c3b93ebc8f41c090964f5c00005dc76747b45220000e3502fce21346c353000000054dca6731c528c3530254361030b26d4d81374000038b558528943d5359ce8e031000044f50b113dca4620800001f1140101b40002e605b930181ef24bc0000001396401d42a000000035f84dd2bd8d5c1e410c13f9c24334a4fc42a484f452706df2734bc12f70bad335c1e62ee818247480db2db0ffd1
  | 47 => 0x3dd00000000c7221fcb5200002b90000812000000038147f302500000000008511400000000004d380002398b722d0c7cd481caa140cc00028240b400012540bbd29d08e90a71f00639213006b049c7781b587ab12a13d84634597559c5491d3957c300438c4d591c04a50137345d31f000023d1d491c5000141a0a1c44915642a1000054b27cd08109f00003c0803d56582c7000159a370876402b91cb0364b25000051f33d05b600006c73d3c00052e4f7126a400025b8e29177d3043a4c97f37647ff36d4a5d427547846a91df2630000000000000000005579063000102b184c00000000000000259000021a36b400000000000000000467c0004ab00cc22f1223357c9380cf157e4658000042c24b3a6cd3323c059c0000a080ddd29207640950000aad0334a4d1dfc00055215c22614dda51dc1b0000090b18f0f8d40a840e15a008e093cb6a0000a5a00009940001542537cc6329bc0ab064d15d46754c1215ce1331544a1096d30d27d063f10ed48c41d1080105d32410e94ca54d051100001500000000200400046991be37a800000015451ebd0bc36f800019e0f1906a028d4848b78532caee04c4c5c1688f504050d444d68db652750ca47804e30000baa1830000000116835b8000435934600004ea405c8ab426cad71b18889522800617dc0003e246a63c6c0002f815040284000000000000015a6566c00045e13750a1112d240428b000000000006980000d41496897901c04e2379cb09000151b4058692079c4ef00003034c2c7311e289fa06b4f1354610f500000df000089d1bfcd3726b4e144e940000000b35548800011812ed49d80002114d0d4af951143c544030b45512b883a840a000000009e300010430000b1c0000992000039f3cf80000000fc100011ef0270c963f1ccbc20a44722f9081648a438020a949302b429243146aa4ce4d7150945871bb155b12e81c429e81c13dbd13614f065c00003e9074113f46ac00000004d000000003ac400000015380000a100000d0b529473740348b23d5c17c09e14d83b907a735cc2da4b9875f266c0003d280215234e41210c42d1d093a623a95bf2f7c0000440b943f3c000409cf3c000114f181d3d40650779517400021d85f300003c3106034b01fc2ab1f0d2aa053c12618e8af00000d6300000000000000059000011401df09090ac21646530fd8fa90dc13ca2c9c0002fcd3e10d1491c482ce200c981e250310082f64ecd2fe0cff402d25f15cd3b00004d303a911ae5108a8e178d44706ed590563048a3488b7630c8f6b02983831da883100013e41ce00be1c80d9307ec2034f486bb4d551fc000028c27b800021f8000000051c00000000000cd92d3000000008d645f8c8d0240d13499153e4a5c735520c7bf5178c7d00011d6126095a1ab8ff81c2c7f24e8c0001a08
  | 48 => 0xa1b04480000890a510761190408000049cc7f4088c7db0000205066012103e44d4005400000001ed1fe140f33f40002fb0c1b165818102d47f535a8f3f11f4e2e000134d0e5c00000006d8272ce90452cec214640004c495702c04e571610000000000000002d60000000000000000013e208b0c240001184016c160340d2713d60fe64318c8818c9323164000012593920668ace5651010000000003dc9aa0000c5d000020c1ff800042783c62e350ed
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc6c7598940040018deeab1280080031b1d562500100247a40aed9002000ce576c8720040070fd0bbb440080021f617768801001c3f42aed100200087f865d6200400187cc8bac40080031798d75880100043fc3acb100200087d87596200400187ceab2440080030f5d564880100062f3aac71002000c5d7558e20040018dceb31440080031b5d66288010006373aac51002000c6d7558a20040795c902b14400800339589718801001c3e42eec90020028bc84dd920040031b907bb240080123b20b76480100047bc0eec900201887d86dd5200400187cc9baa40080031798f75480100043f43aca900200787c875952004001878e8b2a4008003171cd65480100263a38aca90020178bd86dd1200400187ccbba240080030f59774480100064f31ee890020008be87591200400d1790eb2240080030fdd564480100061e3aac89002000c9c735912004009968e2b22400805a3761b73480100062f32ee69002000c5d65dcd200400193cc9b9a40080032759373480100046f43ac690020058dc8758d20040018beeab1a4008003171d563480100064fba2c69002000c9c7458d20040099a8e2b1a40080031bdd66248010006363acc49002000caf749892004001958e9312400800333dce62480100066639cc49002004ce47198920040018deeab1240080031b1d5624801000657ba2c49002000cac74589200400199ee6b124008003331cd62480100267238ac49002000c7665dc520040018eacbb8a40080032d99371480100065ab26e29002000cd663dc520040019aac7b8a40080033998b714801000672b16e2900203c9e687c8520040019ceed90a40080123b60976080100263b38aca1002004cb67159020040099ace2b1840080123b61e62080101dd7240ac41002000c75655c4200400196ac8b8840080033558d710801000673312e21002000c7475dd910040019a8e7bb220080031de1776440100063a42eec8802000cb784dd9100400196909bb2200800335e0f76440100066a41eec8802000c7753dd910040018eaa7bb2200800339e0b764401000672416ec8802000c7452dd910040018eeedbaa20080032dddb74440100065bbb0e88802000d94731d110040019aeedb9a200800339ddb72440100047ac34e4880203b9e6829c91004001ac8a4392200800339dd87244010006b3ba8e48802000d64751c91004001b4ee83922008003691d07244010006e3b98e48802000dc4731c910040773cf0c39220080ee796187244010006b3c28e48802000d64851c91004077accca39220080ef5959472440101ded3320e4880203bda5641c91004077b8cc639220080ef7158c7244010006b3a98e48802000d65531c910040019ccc039220080ef789807244010006f1a00e48802000de0401c910040018eeed2922008003591ca5244010
  | 1 => 0xae639ac4080029ba1f53588100053643ea6b1020b3e6471d4d62041694db0b29ac40800393d4e53588100053743aa6b102000a6c8754d6204001c9f06a9ac4082d3991c5535881059d37428a6b102000a6e8590d62040014db0b21ac4080029ba14435881000536c2886b102000a6e859c162040014db0b382c4080f3391c670588101de72388e0b102000e6b50941620400155f08a82c408002ab211505881002573408a0b102000ae58114162040014dd0a202c4080029b61440588100257340880b102000ae58110162040014dd0b982c4080029b61730588100055742660b102000aad84cc162040014dd0a182c4080029b61430588100257340860b102000ae5810c162040014dd05bb4a4080031b9cb76948100043fc1eed290200087d83dda52040830fd05bb4a4080031ba0b769481020536c12ed2902000c6e725da52040010ff06bb4a4080021f60d769481000637412ed2902040c6d825da52040070f904bb4a4081031d08576948100061fb9ac92902000c3d73592520408387ce4b24a4080038b9c964948100062f43ac72902000c5d8758e52040838bce4b1ca408003939c9639481001c3fc3cc5290204087c8798a52040838dce5314a40800e9be1e629481020e37c3cc52902003a6d8798a52040818d90f314a4080031bdce629481000636b9cc5290204187f8758a52040838dce4b14a4081029d20562948102073210ac52902000a6f8758a52040838df0eb14a4080031bdcd629481000636b9ac52902040e648158a520400917f0eb2484080123b61e629081001c3e42eeca1020048bc84dd942040031b907bb284080021fe15765081001c3e42aeca1020008df835d942040031b906bb284080123d20576508100043ec36eaa102036c3e64dd542040018bcc7baa84080021fa1d65508100043e43acaa102000c5c7359542040091790eb2284080030fdd564508100061e3aac8a102000c9c7359142040011bb0db9a84080031799773508100062eb2ee6a1020afc9e64dcd420400193ac9b9a840800237a1d63508100046e43ac6a102000c5f7558d42040018b8eab1a84080031bdd66250810006363acc4a102000ccf739894204001998e731284080123b21d625081000637baac4a102000c6c75589420400199ee6b128408003331cd62508100065ab26e2a102000ce562dc54204001972c9b8284080033a58b70508100047cc30e0a102004ae5825db2104001cc8a4b164208012b9e1d62c841000733c2ac59082000e648558b2104001ccea6b1642080039954d62c84100053ac34a59082000e656294b210400196ac8b8c800807a1f61b75500104461f326eaa002000c5e63dd540040010fd0eb2a800801e1f21d65500100061fbaac8a002000c3c7559140040018beeab1a8008003171d5635001000637bacc4a002000
  | 2 => 0xc759881000536c18eb3102000a6e859d262040014db0b3a4c4080029be1574988100053642ae93102000acf835d2620400159906ba4c4080038bd5254988100053742ce73102000a6d859ce62040014df0ab9cc4080029b215739881000557c22e73102000aac845ce62040014dd0a39cc4080029b614739881000557420e73102000aad841ce620400199ae639cc4080029ba1f53988100053643ea731020b4a6d8594e6204001c9ea729cc4080029ba1d53988100053643aa73102000e4f8354e62041674dd0a29cc4080029ba16439881000536c2c873102000a6e8510e62040014db0a21cc4080029ba16709881000536c2ce13102000aaf84542620400155908a84c4080029ba14409881000536c28813102000a6e85cc262040014db0b984c408002aba13309881000556c26613102000a6e850c262040014db0a184c40800e1fa1f75588102063a38eeab10200087d83dd562040070fd05baac4081031b60b755881001c3e416eab1020048f4815d562040810fd0e3aac4081071d1c475588100043fc2ae6b10200387c855cd620400117f08b9ac40800a2f21173588100247a40ae6b1020008f8805cd62040010fd0fa9ac40800e1f21f535881000537416a6b1020b3c7471d4d62040010fd0ea9ac4080021f21d535881000536412a6b1020b4c747154d62040091dd0fa92c4080031bdd752588100257340ea4b102003c6e7594962040078d8eb292c4080123b21d52588102043f438a4b102041c747114962040018deea292c4081029ba1c525881000637438a4b102000a6d831496204083cc8e2292c4080123ba1f42588100053742e84b102000a6d85d0962040095cd03a12c4080123ba1f32588100053742e64b102000a6d85cc962040095cd03992c4080029b21632588100247643a64b102000a6f854c962040014d90a992c408002abe1132588100055642264b102001ccc734c962040014dd0a192c4080029b61432588100055742064b102000aad840c9620400199ae6192c4080029b60f75588102073238eeab102041a6e859d562040018deeb3aac408012b9a06755881000572c0ceab102000ae7815d562040095c902baac4081029ba1c755881000637438eab102000a6d831d56204083cc8e23aac4080029ba16745881000536c2ce8b102004ae6819d162040015cb033a2c4080029be1574588100053642ae8b102000acf835d1620400159906ba2c408012b9205745881000574402e8b102000e2f5495162040014dd0b39ac4080029b61673588100257340ce6b102000ae5819cd62040014df0ab9ac4080029b215735881000557c22e6b102000aac845cd62040015cf02b9ac408012b9205735881000575c02e6b102000ae8805cd62040014dd0a39ac4080029b614735881000557420e6b102000aad841cd620400199
  | 3 => 0x6b202000ab7815cd640400956902b9ac8080028fa1473590100051ec28e6b202000a3e82d4d640416947b0b29ac80800387d4e53590100070fc1aa6b202000a3c8254d640416747d0a29ac8080028fa1772590100051ec2ee4b202000a3f855c964040014790ab92c808002a7e0d72590100054e41ae4b202004ab4815c9640400157100b92c8080038bd4a52590100051ec18a4b202040a3e82149640400147d0b992c8080028f61732590100255b40e64b202000ab581cc964040014790b192c8080022fe1d32590100045e43a64b202000a3f854c964040014790a992c8080022fa1c32590100045ec3864b202000a3e850c9640400147b0a192c808003a34c832590100051f428e0b202000a3d851c16404001c76a1282c8080022fe1d50590100345e43aa0b2020068be87cc1640400117b0f982c8080028fa1730590100051ec2e60b202000a3e850c1640400147b0a182c808012ada0430590100055ac0860b202000c5f759d563041694bb0f3aac60800297a0a7558c105cd6bc0aeab182004ad4815d563040018bf0ebaac608002972097558c100072bc0aeab1820b4e54815d563041674bd0a3aac60800297a177458c100052ec2ee8b1820b8ad7815d163040095a902ba2c60800297a147458c100052ec28e8b182000e1f5495163040014bd0bb92c608002976177258c100052fc2ae4b182000a5c855c9630400153f08b92c608002a72117258c105bd6bc0ae4b182004ad4815c9630416d5b700b92c608002b62017258c100052f428e4b182000a5d851c9630400153d08392c608002a76107258c1000666b90e4b182000e4f5294963040014bf0e292c6080029761c5258c102052f410a4b182000a5e85d0963040014bb0ba12c608012b5a074258c100056ac0e84b1820b5ad5819c16304001cb6a1282c608002a7e115058c100054e422a0b182000a5e8510163040014bb0a202c608012b5a044058c100056ac0880b182041a6e82dd662040814dd043acc4080021fe15749881001c3e42ae931020008df835d262040031b906ba4c4080021fe15739881001c3e42ae731020008bf845ce620400517908b9cc4080021fa1f539881001c3e43ea73102000a6e82d4e62040010f90ea9cc4080029b209539881000637baea531020048ed8794a62040078dceb294c4081029ba08529881002476c38a53102041c6d8714a62040014db06294c4080029ba17429881000536c2e8531020048ed8710a62040014dd0b994c4080029b617329881002476c3c653102000a6c858ca62040014df0a994c4080029b215329881000557c22653102000aac844ca6204003998e6994c4080123b61c329881000537428653102000a6d850ca620400155d08194c408002ab610329881000666b98653102000a6d83dd662040018deeb3acc4080031ba1
  | 4 => 0x440018dcea31440880031b5d4628811001c3f42eec902200087d85dd9204400517d09bb240880022f613764811000c6f41eec90220008dd83dd920440010ff0abb2408800e1f21576481100045fc22ec90220028bc845d920440011bf06bb240880063720d76481105f43f436ea9022000c3c64dd520440018b8c7baa40880021fa1f654811025c3e43eca9022000c3c74d9520440018b8e7b2a408812f1d1c7654811024c5f436e89022000c3f65dd12044001878cbba240880032718f74481100045f43ec8902204a8bc87d91204400187eebb2240880030f1d764481100064e39ec8902204acb471d91204417b1bd0db9a408800317d9773481100062e32ee69022000c9f64dcd2044001938c9b9a408800237a1f63481102446e43ec69022000c5f75d8d20440018b8ebb1a408800327dd363481100064e3a6c69022048cd471d8d20440018deebb1240880031b1d7624811000657ba6c49022000cac74d89204400199ee7b124088003331cf62481101e67238ec49022000c6f7518920440018d8ea31240880032bdd06248110006563a0c49022000ccf731892044001998e631240880ef391c462481100063bb2ee29022000c7465dc5204400196ec9b8a40880032d19371481100066bb1ee29022000cd463dc520440019c8c5b8a408812f1d9db65841102565b3b6c90822002cb6761921044001d28c63242088123359db63841101e6733b6c50822000e645218a10440779ccec314208800399d94628411000732328c50822000ea76418a1044001d48c83142088003b1d8c628411000762318c50822000e678518a1044001cc90a314208800399d4c628411000732a98c50822000e646294a104400187ee93a2ca080021fa0b73594105a43ec3ce6b282000c5f739cd65041794ef02b9aca080129d20573594100062fc1ae6b28200087c825cd65040018ef02b9aca082d31d205735941059c3f438e6b28200087e8790d65040010fb0f21aca080021fa1c43594100043ec3886b282000c6f729c965041774ef02b92ca080129d20572594100043ec18e4b28200087e87d0965040010fb0fa12ca080021fa1f32594100043ec3e64b28200087c878c965040010ff0e992ca080021f21d32594100051fc2264b282000a3c844c965040010fd0e192ca080021f61c32594100051f42064b282000a3d840c96504001c9a64192ca082ea9d60670594100043f43880b28200087d87101650400f0fd0f982ca080021f61f30594100051f42660b282000a3d84cc165040010fd0e182ca080021f61c30594100245f43ea8b202000c3f75d5164040091790eaa2c8080123d20573590100245f43c86b202000a3e8590d640400147b0b21ac8080122f21d435901001c3f42ee4b20200087d85dc9640400187eeb3aac8080028fa1673590100051ec2ce
  | 5 => 0x80029b61f629491000636c3ec52922000c6f73d8a52440018dae7b14a48800e1f61e62949101b51f424c52922000a3d8498a524406b4bd07314a4880029760e629491000537414c5292200087f8758a524400147f08b14a4880da8f21162949100052fc1ac52922035a5c8358a52440014ef02b14a48800e1fe1c62949100043e438c52922000c6e7218a52440014dd0c314a4880031b9d8629491000717b20c52922000e2c6418a5244001c9ec6314a4880039318c629491001d37c38c52922000c6f8718a52440074db0e314a4880031b21c629491000637b98c52922000c6d7318a52440070fd0bbb484880021f617769091000c6f41eed21220008dd83dda42440011dd05bb484880021fe15769091001c3e42aed21220008df835da42440031b906bb4848800a3b61c629091001c3f42eeca12200087d85dd942440031bd07bb284880023760f765091001c3f42ceca12200087d859d942440031bd073b284880023760e76509100043fc2aeca12200387c855d942440011bf06bb284880063720d765091000477c12eca1220008f7815d942440011f700bb2848800e1f214765091000c6e418eca12200087e86dd5424406d878c9baa84880031718f75509100043f43ecaa12200087c87d9542440018b8e7b2a84880030fdd764509100061e3aec8a122000c9c73d9142440011bd0db9a848800317d9773509100062e32ee6a122000c9f64dcd424415f938c9b9a848800237a1f63509100046e43ec6a122000c5f75d8d42440018b8ebb1a848800a3ba1f625091000637baec4a122000c6c75d89424400199ee7b128488003331cf625091000637ba8c4a122000c6c75189424400199ee63128488003331cc625091000674316e0a0a2000cbb641c141440019d0c438282880033a18a70c851001c3e428ec90a200087e86dd52144001878c9baa42880031718f75485100043f43eca90a200087c87d95214400187eebb2242880030f1d764485100062fbaec690a2000c5c75d8d21440018deebb1242880031b1d7624851000637ba8c490a2000c6c751892144001970c9b8242880033618f70485100065c320e090a2000cd8631c121440019d6c438242882fa1fa1b75501104461e326eaa022000c5c63dd540441130fd0fb2a808812e1f21f65501100061fbaec8a022000c3c75d914044095968e3b22808800317dd763501100062e3aec6a022000c6f75d8940440018d8ebb1280880031bdd46250110006363a8c4a02203bce47118940440019a8c7b8a80880033918b71501101de73388c59022000ce4625c720440070f90b3b4408806a1f21975881100061e322eb1022000c5c635d620440010ff0fb2c408802e1f61f65881100061f3aec91022000c3d75d9220440018bcebb1c4088003175d76388110006373aec51022000c6d75d8a2
  | 6 => 0x637438ea3122000a6d831d46244001ccd023a8c4880039960475189100053742ce83122000a6d859d062440014df0aba0c4880029b215741891000567c1ae83122000acc835d062440775cd023a0c488002b9604741891000717aa4a83122000a6e859cc62440014db0b398c4880029be1573189100053642ae63122000aaf845cc624400155908b98c4880029ba14731891000536c28e63122000aae841cc624400155b08398c488003335cc73189101dd73408e63122000ae5811cc62440015d500398c4880eeba60073189100053743ea63122000a6c87d4c62440014db0b298c48800393d4e53189100053743aa63122000a6c8754c6244001c9f06a98c4880029ba1453189100053742c863122000a6d8590c62440014dd0a218c4880029b61443189101dd73408863122000ae58110c62440014df0ab88c4880029b21571189100053742e823122000a6d85d0462440014dd0b988c4880029b617311891000575c02623122000ae8804c462440014df0ab80c4880029b215701891000557c22e03122000aac845c0624400159f06b80c488002b320d70189101dd7340ea03122000ae581d40624400155f08a80c488002ab211501891000573c0aa0312203bae48154062440775cd03a00c488002b9607401891000537428803122000a6d8510062440014dd0b980c4880029b617301891000557426603122000aad84cc062440775cd03980c488002b9607301891000573c0a60312203bae4814c062440014dd0a180c4880029b614301891000537c2a203122000a6c85440624400155f08880c488002ab211101891000567c1a203122000acc83440624406d47d09bb4a4880028f61376949101ad2f41eed2922000a5d83dda52440014dd05bb4a4880031718e769491000637394ed292200087f839da52440010fb073b4a4880031b20a76949100051fc22ed2922036a3c845da52440014bf06bb4a4880d69720d76949100043f430ed2922000c5c631da52440014dd043b4a4880031b9c876949100043fc18ed292200087d831da52440010fd043b4a4880031ba0876949101b51f436c92922000c3e76d925244001878edb24a4880038718f64949100061fb9ec92922000c3d73d92524400187ce5b24a4880038b9cb64949100043fc3ac9292200087c8759252440014bf06b24a4880d69720d649491000537c12c92922000a6c82592524400147d0c324a4880030f9d864949100061e3b0c92922000e1c63192524406b4bd0db1ca488003179db63949100062e3b6c72922000e1f64d8e5244001c38c9b1ca48800317e1f63949100062e43ec729220bfc5e72d8e5244001c9ce5b1ca4880021f61f629491000637396c52922000c6e76d8a52440018d8edb14a4880038bd93629491000716326c52922000e4f63d8a5244001c98c7b14a48
  | 7 => 0x7f855d062440070f90aba0c48800237e0d741891000c6e41ae8312200087f855cc62440070f90ab98c4880022fe1173189100145e422e6312200087e87d4c62440070f90fa98c4880029ba0b53189100043e43aa63122000a6c8254c62440014dd0b390c4880029b616721891000557424e43122000aad849c8624400159d07390c488002b360e721891000637baea431220038ed8794862440078dceb290c4880023b61c521891000572c08a43122000c6d8714862440014db06290c48800399a04521891000732c08a43122000a6e85d0862440014db0ba10c488002b960442189100053742e643122000a6d85cc862440031db0f190c4880029b216321891000537c2a643122000a6c854c8624400155f08990c488002ab211321891000e6639a6431220008ed870c862440014dd0a190c4880029b614321891000557420643122000aad840c8624400199ae6190c488002b960432189100053742cec3122000a6d859d862440018dd0b3b0c4880031b616761891000537430ea3122000c6e761d462440018dcedb28c4880029b60f651891000476c3cca3122000aae84994624400155b09328c488002b3a0e651891000566c1cca31220008ef87594624400155f08b28c488002ab211651891000567c1aca3122000acc8359462440018dcec328c4880029b60c6518910006573b6c83122000e2f65d906244001c58cbb20c4880038bdd76418910007163aec831220008ed8799062440014dd0b320c4880029b61664189100056741cc83122000acd8399062440011df0eb20c4880029be1564189100053642ac83122000acf83590624400159906b20c4880032b9d8641891000717b28c83122000e2c651906244001c5eea320c4880038b1d4641891060f55880c831220c1ea810190624400199cedb18c48800393d9763189100072632ec63122000e8f64d8c6244001d18c9b18c48800393e1763189100072642ec63122000e4f75d8c6244001c98ebb18c4880023b61e63189100053742cc63122000a6d8598c624400155d09318c488002ab612631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000a6e8518c62440014db0a318c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891000727428c63122000e4d8518c6244001c9eea318c488003931d4631891060765880c631220c0ec81018c62440014dd0da98c4880029b21b5318910006373b6a63122000e2f64d4c6244001c58c9a98c48800393d8f53189100072631ea63122000a6e8654c62440014d90ca98c4880031b9d9531891000717b22a63122000e2c6454c6244001c9ec6a98c4880039318d531891000536c1eea3122000c6f759d462440775cd023a8c488002b960475189100
  | 8 => 0x9b9cc488003179d673989100062ebace73122000c9e749ce624400193ae939cc488003179d573989100062ebaae73122000c9e745ce624400193ae8b9cc48800317a1573989100062ec2ae7312200387f87d4e62440010fb0fa9cc4883130f9d353989100061eba6a73122001c5e73d4e62440018bae7a9cc4880021fe1d53989100043ec3aa731220c3c3e7454e624400187ae8a9cc488007179cd53989100062eb9aa73122085c3e7414a624400187ae8294c48830b179cc52989100062eb98a5312200387e86dd562440010fd0fb2ac4880030f1d365589100062e39ecab12200087e871956244001878e832ac488003171cc65589100061fb2ee8b122000c3c65dd1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c7319162440031bd0db9ac48800317d9773589100062e32ee6b122000c9f64dcd6244001938c9b9ac48800237a1f63589100062fbaec6b122000c5c75d8d624400193ee9b1ac488003271d363589100046f438c6b122000c5f7518d62440018b8ea31ac48800327dd063589100064e3a0c6b12200087d83dd5624400117f08baac48800a2f21175589100046fc1aeab1220018dc835d562440011df04baac4880023de0575589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fc2ee6b122000c5c85dcd62440010ff0ab9ac48800e1f21573589100045fc22e6b1220028bc845cd62440011df04b9ac4880023de0573589100047dc02e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b12200087e87d4d62440070f90fa9ac4880030fdd353589106261e3a6a6b122000c5f73d4d62440038b8e7a9ac4880021fa1d53589100043e43aa6b122000c3f7454d6244187878e8a9ac48800317dcd535891000e2e39aa6b122000c6f75dc962440018d8ebb92c4880032bdd37258910006563a6e4b122000ccf73dc96244001998e7b92c4880030fdd0525891042e1e3a0a4b122000c5f7314962441858b8e6292c4880031ddd771589100063a3aee2b122000cb774dc56244001968e9b8ac48800335dcf71589100066a39ee2b122000c7753dc562440018eaa7b8ac4880031d14b71589100065c3a6e0b122000cd873dc162440070fd0b3b0c4880021f61676189100061e3aec83122000c3c7519062440018b8ebb18c488003171d4631891000477c3ac43122000a6f8558862440014d90ab10c488002abe11621891000556422c43122000acf83588624400159906b10c4880038bd90521891000716320a43122000e4f631486244001c98c6290c4880029ba0b751891000537410ea31220008
  | 9 => 0x64d89100056741cc9b122000acd8399362440014df0ab26c4880029b21564d891000567c1ac9b122000acc835936244001c5eca326c4880038b19464d8910007173a8c9b122000e2d751936244001c9ecbb1ec4880039319763d891000747b26c7b122000e8c64d8f6244001c9f0bb1ec4880039321763d8910007273aec7b122000e4d75d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f62440014dd0a31ec4880029b61463d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d891000727428c7b122000e4d8518f6244001c9cea31ec488003935d463d891000537436a7b122000a6c86d4f6244001c5ec9a9ec4880038b19353d891000727b1ea7b122000e4c63d4f62440014dd0ca9ec4880029b21953d891000717b22a7b122000e2c6454f6244001c9ec6a9ec4880039318d53d891000536c1cebb122000c6f875d762440014df06baec4880031b5d475d89100053742ee9b122000a6d85dd3624400159d07ba6c488002b360f74d891000537428e9b122000a6d851d36244001c5ea92a6c4880029ba1773d891000536c2ee7b122000aae84dcf624400155b09b9ec4880029ba1673d891000536c2ce7b122000aae849cf624400155b0939ec48800333dce73d891000537428e7b122000a6d851cf62440014df0fa9ec4880029b61f53d891000727a9ca7b122000a6f8754f62440014db0ea9ec48800393e0d53d89100053742c87b122000a6d8590f62440014dd0a21ec4880029b61443d89100053742ee3b122000a6d85dc762440014dd0ba0ec4880029b61741d89100053742e63b122000a6d85cc7624400155f08a86c488002ab21150d89100053742881b122000a6d8510362440014dd0b986c4880029b61730d89100055742661b122000aad84cc362440014dd0a186c4880029b61430d89100061f3a6cb3122000c5e73d96624400187ce832cc488003179cc65989100061fb2ae93122000c3c655d2624400187cebb24c4880030f5d764989100064f39ec93122000c3e75192624400187aea324c488003279cc64989100062fb2ae73122000c5c655ce624400193ec8b9cc4880032719173989100062f3aec73122000c5d75d8e624400193ce9b1cc488003275d363989100062f3a8c73122000c5d7518e624400193ce831cc488003275d06398910006373aec53122000c6d75d8a624400195ce9b14c4880032b5d362989100066739ec53122000ccd73d8a624400517d09bacc4880022f613759891000c6f41eeb31220008dd83dd662440010ff06bacc4880030f9d674989100061ebace93122000c3e755d2624400187aeaba4c48800e1fa1773989100043ec2ee731220028be84dce624400117b
  | 10 => 0xb1a2000ace82997634400159b0532ec68800237e1d65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100052f430cbb1a2000c5e7619763440014bd0432ec688003279db64d8d100070fb2ec9b1a2000e1c65d936344001c3eebb26c688003871d764d8d100046ec3cc9b1a2000a5e8599363440014bb0b326c688002a7a1264d8d1000567414c9b1a2000acd8299363440011bf0eb26c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c688002a7a1864d8d100064f3b0c9b1a2000e1f651936344001c38ca326c68800387dd464d8d100070e3a8c9b1a2000a5e8614b63441858bcec296c68800387d9052d8d100070e320a5b1a2000a5e82dd763440014bd0b3aec688003175d475d8d100052f438ebb1a2000c5e871d763440014bd043aec68800297a1674d8d100052ec2ce9b1a2000a5f855d363440014b90aba6c68800387d5254d8d100052f42ee5b1a2000a5d85dcb634400153d09b96c688002a761372d8d100052f42ce5b1a2000a5d859cb634400153d09396c688002a761272d8d1000667b94e5b1a2000a5f855cb63440014b90ab96c68800393d4a52d8d100052f438a5b1a2000a5c8714b634408f4bd04296c68800297a1742d8d100052ec2e85b1a203aada80dc763440014bd0ba0ec6880029761741d8d100054fc22a1b1a2000a9c8454363440014bd0a206c6880029761440d8d1005c3ec3ecbb122000a6e82d9762440014dd0432ec4880030f9d764d89100061ebaec9b122000c3e75193624400187aea326c488003179d763d89100062ebaec7b122000c5e7518f62440018baea31ec4880038bd9052d891000716320a5b122000e4f6314b6244001c98c6296c4880021fe0d75d891000637c12ebb12200387e85dcf62440010fb0bb9ec48800a2fa1373d89100045ec26e7b12200387f87d4f62440010fb0fa9ec4880029ba0b53d89100043fc3aa7b12200087d8754f62440014d904a9ec4880031b5d752d891001e373aca5b122003c6c7594b62440071df0ea96c4880031b5d452d891000536c38a5b122000c6d8714b62440014db06296c4880029ba1742d891000536c2e85b122000a6e85ccb62440014db0b996c4880029b21632d891000c77c3a65b122000a6f854cb62440014d90a996c488002abe1132d89100055642265b122001cce734cb62440014dd0a196c4880029b61432d89100055742065b122000aad840cb624400199ee6196c4880029b61f65d891000536c1ecbb122000aae84997624400155b0932ec488002b3a0e65d891000566c1ccbb122000aaf84597624400155908b2ec488002b3e0d65d89100056641acbb122000a6d831976244001c5ecbb26c4880038b19764d8910007173aec9b122000e2d75d9362440014dd0b326c4880029b616
  | 11 => 0x44001878c9baac8880021fa1f65591100062e39ecab22200087e8719564440018b8e632ac88800317d9773591100062e32ee6b222000c9c64dcd64440018beea31ac888003171d4635911000637b2ee4b222000c6c65dc96444001958c9b92c8880033318f725911000637b28e4b222000c6c651c96444001958c8392c8880033318c725911001c3f43eeab22200087d83dd564440010fd05baac8880022fe1175591100046fc1aeab2220018dc835d564440011df04baac8880023b20975591100043f438eab222000c3f75dd16444001878ebba2c88800637a1f73591100062fbaee6b222000c5c75dcd644400193ee9b9ac88800317e1773591100062e42ee6b22200087f855cd64440070f90ab9ac8880022fe11735911000477c12e6b2220008ec825cd64440011ef02b9ac88800237a1c73591100062fba8e6b222000c5c751cd644400193ee839ac8880021fa1f535911001c3e43ea6b222000c5f73d4d64440038b8e7a9ac8880021fa1d53591100043e43aa6b222000c5f7354d64440038b8e6a9ac88800e1fa1772591100043ec2ee4b222000c6f75dc964440018d8ebb92c8880032bdd3725911000667b9ee4b222000ccc73dc964440018dd0bb92c8880031b617725911000637a9ee4b222000c6d53dc964440018deea392c8880031b1d4725911000657ba0e4b222000ccf731c96444001998e6392c8880031be14725911000636428e4b222000c6f531c964440018daa6392c8880021fa1c525911001c3e438a4b222000c5f7314964441858b8e6292c8880031bdc8525911000636390a4b222000cd473dc564440019c8e5b8ac8880033a1cb70591100061f3b6ca3222000a3d83d94644400147d05b28c8880022f61e65191100051f42cca3222000a9e83994644400153b07328c888002aba0a651911000556c14ca32220008bf87594644400153f06b28c888002a720d651911000557c12ca3222000aac82594644400147d0c328c8880030f9d865191100051ec18ca3222000a3e82194644400117b0f318c8880028fa1663191100051ec2cc63222000aae8298c644400155b05318c8880022fe1d63191100051fc2ac63222000a3c8558c644400155f04b18c888002ab20963191100055bc0ac63222000a3e8518c644400147b0a318c88800387d9463191100070e328c63222000e1e8518c6444001c3b0a318c8880028fa1b53191100051e436a63222000c3e76d4c6444001c3ec7a98c8880038718f53191100051f432a63222000a3c8654c644400187ceca98c88800387d8d53191100070e31aa63222000a3e861486444001c38c6290c88800297a1b75d8d100062f3b6ebb1a2000a5e861d763440018bcec3aec688003179db65d8d100052f416cbb1a20008dd8799763440014bd0b32ec688002a7a1265d8d100054ec24cb
  | 12 => 0x28f61263d951000537414c7b2a2000a6d8298f65440010ff0eb1eca880028fe1163d95100051e422c7b2a2000a6f8258f65440014d904b1eca8802e1f61c63d95100062eb98c7b2a2000c5d8718f65440018b8c7396ca880030f5d074d95100043f416e7b2a200087d879cf65440018bf06b9eca880021f20973d95100043f438e7b2a2000c5d731cf65440010fd0f21eca880021f61e43d95100043f43887b2a200087d8710f65440010fb07396ca880031b5c872d95100043f43e85b2a200087d87d0b65440010fd0f996ca880021f61f32d95100043fc3c65b2a200087f874cb65440010f90e996ca880028fe1132d95100051e42265b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2000e4d320cb65440714f501b8eca880021fa1f41d95100043ec3e83b2a200087e87cc765440010fb0f98eca880021fa1c40d951005c3ec3881b2a204b87e87cc365440010fb0f986ca880028fa1330d95100051ec2661b2a200087e870c365440170fb0e186ca880030f5d754d911001c5fc3aa9b222000a3e8590f644400147b0b21ec8880062fe1d43d91100043fc2ae5b22200387c855cb644400147b07b2ec8880028fa0b65d91100054f41ccbb222000a9d83997644400155d0532ec888002ab60a65d91100054fc1acbb222000a9c83597644400155f04b2ec888002ab20965d91100051ec18cbb222000a3e82197644400147d0b31ec8880028f61663d911000557414c7b222000aad8298f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f644400147d0a31ec8880028f61463d91100070fb28c7b222000e1c6518f6444001c3d0a31ec8880038761463d91100051f436a7b222000a3c86d4f644418987ceda9ec88800387d8f53d91100070e31ea7b222000a3e8654f64440014790ca9ec88830f0f9d953d91100070fb1aa7b222000e1c6354f644400147d0c296c8882170f9d852d91100070e318a5b222000c3d751d7644400147d0b39ec8880028f61673d91100051f428e7b222000a3d851cf644400147d05a9ec88800387d4e53d91100070fc1aa7b222000a3c8254f644400147d0bb96c8880028f61772d91100054f41ee5b222000a9d83dcb644400147f0ab96c8880028f21572d911000717a94a5b222000a3d8314b644400147d0b996c8880028f61732d91100051e42c65b2220008bf874cb64440011790e996c8880028fe1532d91100051e42a65b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000e8d320cb644400147f0ab8ec8880028f21571d91100051f42e63b222000a3d85cc7644418b17f0ea86c88812a2f21d50d91102545f43e61b2220008bd87cc3644400147d0b986c8880028f61730d91100051f42861b222000a3d850c364
  | 13 => 0xc3e42ae5b2420c6cf1719c364840070fd0fbaac9080021f60f75592100043f416eab2420008bf845d564840010fd0e3aac9080030f1d774592100043fc2ae6b24200387c855cd64840011df04b9ac9080023b20973592100043f43ea6b24200387c87d4d64840010fd0ea9ac9080021f21d535921001c3f42ee4b24200087d85dc964840010fd0e292c90800e1f21c52592100043fc1aebb14200387e85dcf62840010fb0bb9ec50800a2fa1373d8a100045ec26e7b14200387f87d4f62840010fb0fa9ec5080021fe1d53d8a100043ec3aa7b142000a6c8254f628400517d09bacc5080022f6137598a1001c3f43eeab14200087d83dd5628400117f08baac50800a2f2117558a100046fc1aeab1420018dc835d562840010fd0e3aac50800a2fa1f7458a100061fbaee8b142000c3c75dd1628400187eea3a2c5080030f1d47458a1000c6f43ee6b142000c5f75dcd62840018b8ebb9ac50800327dd37358a100064e3a6e6b142000c5f85dcd62840018b90bb9ac5080021fe157358a1001c3e42ae6b1420008bf845cd628400517908b9ac50800237a1c7358a100062fba8e6b142000c5c751cd628400193ee839ac508003271d07358a100043f43ea6b14200387c87d4d628400187ee9a9ac5083130f1d35358a100062fb9ea6b142001c5c73d4d62840010fd0ea9ac5080021f21d5358a100061fba2a6b1420c3c3c7454d62840018bee6a9ac508007171cd5358a100061fba0a4b142085c3c7414962840018bee6292c50830b171cc5258a100063bbaee2b142000c7475dc5628400196ee9b8ac5080032d1d37158a100066bb9ee2b142000cd473dc562840011df0eb10c5080021fe157418a1001c3e42ae83142001c5e7354c62840018bae6a98c5080029b2095318a101b51f426ed2942000a3d84dda52840014dd05bb4a5080029ba087694a100043fc3ac9294200087c8759252840010fb0fb14a5080021fe1d6294a100051fc22c52942036a3c8458a52840014bf06b14a5080d69720d6294a1001c3f42eed214200087d85dda42840070fd0b3b485080021f6167690a1001c3f42ceca14200087d859d942840031bd073b285080023760e7650a100043fc2aeca14200387c855d9428400117f08bb2850800237e0d7650a1000c6e41aeca14202ea3c8559141840791df0eb1643080039958a52c86101dc7743cc490c20008f587d8821840013cb0fb1043080eef8a0362086101e5f1400c410c2000e676294821840414790ab2481080122fa1f64502100061e3aec8a0420008ee8718920840779c8e2312410800279a1f214821000477c3ac410420009e4825db10840014bd07326ca880029760e64d951000537414c9b2a2000a6d8299365440010fd0db9eca8800e1fe1f63d95100062eb9ec7b2a200087d8798f654400147d0931eca88
  | 14 => 0xd83dd561080010ff0ab9ac21000e1f21573584200045fc22e6b0840028bc845cd61080010fd0fa9ac21000e1f21f53584200043f43aa6b08400087c8754d61080014d904a9ac2100aa1fa1e52584200043f438a4b084003c7475945610800156b0928ac21000e3d21d515842000c7a43a62b084004c76615d4610800996cc2ba0c2100133598573184200047bc3ac23084000c7575584610800196ae8b08c210003355cd61184200247b40ced2084004c76615d641080018eaeab0c82100021fe15765042001c3e42aeca0840008df835d941080031b906bb2821000e1fa1476504200043ec28eca0840018de831d941080011bb063b282100ba8f215645042000656b20e4a0840028f48758541080019e2c238282100031b149768842000636bb4a51084000c6f535da21080018daa6bb442100039994961084201def0082e01084020a3c85592400800195ac939480100ee3be1d61c80201de7338ac3900401ac79765d620081932f30f29440103239a98a528802000636296ec9004000c6f769492008001acca438a4010003591487148020006363aeec9004000ccc73dd920080018dea7bb240100031b54f764802000637bb6ea9004000caf76dd1200800195eec3a24010003631cc744802000667bb6e69004000ce776dc520080019ceec38a401000359dd47148020006b23a8e29004000da7741c52008001b48e838a401000371dcc7148020006e2398e2900403bce5861c52008001acea638a40100035954c71480201dc7643ac2900403bce47158520080018f0ebbb24010003361cf76480200063da9eec9004000c7953dd920080018f0a5bb240100031eddb75480200065dbb6e89004000cbb761d120080019b6edb9a401031e5ea1e52480200063dbb4a49004000cf376dc520080019e6ec38a40100036c1d07148020006e8398e29004000de3721c5200800917d0faa2c9880030fdd754593100062fb9aa6b262001c5c7354d64c40091790ea1ac988007271cd435931001c3f42ee4b26200087d85dc964c40010ff0aba4c58800e1f2157498b1000e2f39aa73162000c5d7354e62c40014d904a9cc58800e1fa1f7558b100043ec1eeab16204087e871d562c40010ff0ab9ac58800e1f2157358b100045fc22e6b1620028bc845cd62c40010fd0fa9ac58800e1f21f5358b100043f43aa6b16200087c8754d62c40014d904a9ac5881021fa1c5258b1000537416ed296204187f8758a52c40010ff0abb4858800e1f2157690b100245fc3ac9216200087f855d942c40070f90abb2858800237e0d7650b1000c6e41aeca162000c3c7559140c40771df0eb1641880f23ba1e62483100267238cc49062004ce47158920c400187aebaa6c908007179cd53d92100062eb9aa7b2420018bf8750f648400393ce6a1ec9080021fe1572d921001
  | 15 => 0x2bac42900021f61f65885200061f3a6cb10a4000c5e73d9621480011790cba442900030fd9574885200061e32ae910a4000c9c635d22148009968c2ba442900022f61f64885200061f3aec910a4000c3d75d92214800193ce7b2442900023721973885200062fb2ae710a4000c5c655ce214800193ec8b9c42900032719173885200266a30ae710a40008dd87d8e21480018bcebb1c4290003175d763885200064f3a6c710a4000c9d74d8e21480018ecebb0c42900031d5d761885200065b3a6c310a4000cb574d8621480019ace7b0c4290003355cf61885200267830ce110a400087e86dd52148001878c9baa42900031718f75485202063a30eea90a404187e87d95214800187eebb2242900030f1d764485200062fbaec690a4000c5c75d8d2148081cc8c329242900031ddd761485200063a3aec290a4000cb864dc121480019b0c7b8242900032e19070485200066c318e090a4000d6a521c121480019e6c238242901031b1db75485202073230eea90a4000e8c6319121480015cd0db8a4290012b9a1b614852000733b28c290a4000e64651852148001d4ec830a4290003a9190614852000763b18c290a4000ec4631852148001ad6ea382429000378dc470485200043f436eaa024088c3c64dd540480018b8c7baa80902261fa1f65501204443e43ecaa024000c3f75d914048001878ebb22809000317dd763501200062e3aec6a024000ccc63dc9404800195ec839280900033318c72501200063bbaec2a024000c7475d8540480018eeea30a80900031d1d4615012000673b90c2a024000ce47218540480eb4f50d2964090003ac19061c812000768318c3902401a87c865d62048001878c8bac40900031718d75881200c43ec3ecb1024000c3e75d92204800187aebb244090003179d763881200062ebaec71024000c7675d8620480018eaebb0c40900031d9d461881200063aba8c31024000e66521862048001cc8a430c40900631b9db65881200be573b6c91024002cae761922048001d18c6324409005b339db63881201e476432e3102403cce4615c62048001cceca30c409000399194618812000753b20c31024000ea4641862048001d8ec630c4090003b118c61881201e672c38c31024000e66751862048001ccaea30c409000399d4c618812000732a98c31024000e6b65d8220480038bce6a9ec810003175cd53d90200043fc2ae3b20400387c855c764080070fd0fbaac8100021f60f75590200043f416eab20400087e871d564080071790eaa2c8100021fe15735902001c3e42ae6b2040008ec825cd64080010fd0fa9ac81000e1f21f53590200043f43aa6b20400087c8754d64080031790ea1ac810002ab20943590200043f438a4b20400387c87149640815d0ff0eb24a4100021f21d64948202ae3c3b2e1290400087
  | 16 => 0x3185200072a31aa630a4000e67655c86148001cc8cab90c290003a9d91721852000752322e430a4000ec7635c86148001d88c6b90c2900029da1a52185200071bb24a430a4000e34649486148001caec7290c2900039518e52185200053b430a430a4000e37641486148001c68c8290c29000395d8c52185200072a318a430a4000e375495061480014ed05a98c2902cf999cb53185200072ba9ca630a4000e578354c61480014e904a98c2902d3999c953185200053b42c8630a4000a758590c61480014ed0a218c2900029d6144318520005734108630a4000ae58210c6148001ccea5290c2900029d60e52185200053ac18a430a4000e66821486148083ccce4290c2900029da1742185200053ac2e8430a4000a778550861480014e90aa10c290002b5e0d42185200056a41a8430a4000af38050861480015e100a10c290003a950842185200053b42e6430a4000a7585cc861480014ef0b190c2900029d21632185200053bc2a6430a4000a74854c8614800156f08990c290002ad211321852000579c026430a4000af0804c861480014ed0a190c2900029d61432185200055b4206430a4000ab5840c86148001d8a64190c290002b9a0b501852000572c16a030a4000e7350940614800156f08a80c290002ad211501852000573c12a030a4000ae48254061480015cd05a00c290002b960b40185200053b4288030a4000a758510061480014ed0b980c2900029d61730185200055b4266030a4000ab584cc061480015cd05980c290002b960b301852000573c126030a4000ae4824c061480014ed0a180c2900029d61430185200053bc2a4030a4000a7485480614800156f08900c290002ad21120185200056bc1a4030a4000ad48348061480070f90b3b482900021fe15769052001c3e42aed20a40008df835da41480031b906bb482900123d20576905200043e432eb20a40a8c3c645d641480018b8c6bac82900131d18575905200043fc3ecb20a400087d87d96414800187cebb2482900030f5d764905200062f3aec720a4000c5d75d8e414800195ec939482900033318e72905200267230ce520a4000ccc635ca41480099c8c2b9482900031d9d761905200063abaec320a400387e85dd941480010fb0bbb2829000637a0f76505200046ec1eeca0a40028f687d8541480018d8a53b642900031b9da52c85202073230ca590a4000c6c659db2148001998c73b642900031bd4e76c852000636a9ced90a4000ce7819db21480018dcedb2e42900032b9db64c8520006573b0c990a4000e8c63193214800199cedb1e4290003399db61c852000733b28c390a4000e64651872148001d4ec830e4290003a919061c852000763b18c390a4000ec46318721480799c8c338642900021f21975885200061e322eb10a4000c5c635d621480098e8c
  | 17 => 0xa4004c74615d6614800187ce9b2cc290003179cf65985200061f3a0cb30a4000c5e73196614800187ecaba4c2900030f19574985200265a30ae930a4000c3e75d92614800187aebb24c290003279cf64985200061f3a8c930a4000c3d75192614800193ce6324c29000317d9573985200062e32ae730a4000c9f645ce6148001938c8b9cc2900133518573985200062f3aec730a4000c5d75d8e614800193ce9b1cc290003275d363985200062f3a8c730a4000c5d7518e614800193ce831cc290003275d063985200063b3aec330a4000c7575d86614800196ce9b0cc2900032d5d361985200066b39ec330a4000cd573d8661480070fd0dbaac2900021fa1f65585200061e3a6cab0a4000c5c73d9561480010fd0e32ac2900030f1d065585200062e398cab0a4000c3f65dd16148001878cbba2c2900022fa1f64585200061fbaec8b0a4000c3c75d916148001938e7b22c2900022fa1c64585200061fba8c8b0a4000c3c751916148001938e6322c29000637a1b73585200062fb2ee6b0a4000c5c65dcd614800193ec9b9ac2900032719373585200046f43ec6b0a4000c5f75d8d61480018b8ebb1ac29000327dd363585200064e3a6c6b0a40008de8718d61480018beea31ac290003171d463585200064fba0c6b0a4000c9c7418d61480011ef0eb08c2900029de1561185200053a42ac230a4000ab784584614800156908b08c290002b5e0d61185200056a41ac230a4000c7676d9461480014eb07b28c2900023d61e65185200055b424ca30a4000ab58499461480015ad07328c290002b560e65185200047bc3aca30a4000ab784594614800156908b28c290002b5e0d65185200056a41aca30a4000c767619461480014eb06328c2900032d9db64185200071bb2ec830a4000e3465d9061480011eb0f320c2900029da1664185200053ac2cc830a4000ad68399061480015ab07320c2900023de1d64185200053bc2ac830a4000a748559061480015af06b20c290002b520d64185200065b3b0c830a4000e37651906148001c68ca320c290003359db63185200072bb2ec630a4000e5465d8c6148001d2ec9b18c290003a519363185200072bc2ec630a4000e5485d8c61480011eb0f318c2900029da1663185200053ac2cc630a4000ab68498c614800156b09318c2900023de1d63185200053bc2ac630a4000a748558c614800156f08b18c290002ad21163185200053b428c630a4000a758518c61480019acec318c29000395d9463185200072a328c630a4000e976418c6148001d28c8318c29000395a1463185200072ac28c630a4000a7686d4c61480014e90da98c2900038dd9353185200071a326a630a4000e5763d4c6148001ca8c7a98c2900029da1953185200053a432a630a4000e376454c6148001c68c8a98c29000395d8d5
  | 18 => 0x800156b0928ec29000e3de1d51d85200053b42e83b0a4000a7585d0761480014ed0b98ec2900029d61731d852000c7bc3a63b0a4000a76850c761480014eb0a18ec290002ada1031d85200055ac2063b0a4000a7583d97614800156d0932ec290002ad61265d85200056b41ccbb0a4000ad583997614800156f08b2ec290002ad21165d85200056bc1acbb0a4000ad48359761480014eb0632ec2900038dd9764d85200071a32ec9b0a4000a768599361480014eb0b326c290002b5a0e64d85200056ac1cc9b0a4000a778559361480014e90ab26c290002b5e0d64d85200056a41ac9b0a4000e37651936148001c68ca326c29000395d9763d85200072a32ec7b0a4000e9764d8f6148001d28c9b1ec29000395e1763d85200072a42ec7b0a4000a768598f61480014eb0b31ec290002ada1263d85200055ac24c7b0a4000a778558f61480014e90ab1ec290002ade1163d85200055a422c7b0a4000a768518f61480014eb0a31ec29000395d9463d85200072a328c7b0a4000e976418f6148001d28c831ec29000395a1463d85200072ac28c7b0a4000a7686d4f61480014e90da9ec2900038dd9353d85200071a326a7b0a4000e5763d4f6148001ca8c7a9ec2900029da1953d85200053a432a7b0a4000e376454f6148001c68c8a9ec29000395d8d53d85200072a31aa7b0a4000a768694b6148001c6ec9296c2900038d19252d85200072bb1ca5b0a4000e546394b61480014ed0c296c2900038dd9052d85200071a320a5b0a4000e576314b6148001ca8c6296c290002ade1175d85200055a422ebb0a4000a77855d361480014e90aba6c2900029da1474d85200053ac28e9b0a4000e375495361480014ed0b39ec2900029d61673d85200055b424e7b0a4000ab5849cf61480014ed0a39ec2900029d61473d85200053b416a7b0a4000e575394f6148001caf06a9ec2900029d20953d85200053b42c87b0a4000a758590f61480014ed0a21ec2900029d61443d85200053b42ee5b0a4000a7585dcb6148001ccea5296c2900029d60e52d85200053ac18a5b0a4000e668214b61480014ed0ba16c2900029d61742d85200053bc2a85b0a4000a748550b61480015af06a16c290002b520d42d85200053b42e65b0a4000a7585ccb61480014ef0b196c2900029d21632d85200053bc2a65b0a4000a74854cb614800156f08996c290002ad21132d85200053b42865b0a4000a75850cb614800156d08196c290002ad61032d85200076299065b0a4000a7685dc361480014eb0bb86c290002ada1370d85200055ac26e1b0a4000ad683dc361480015ab07b86c290002ade1150d85200055a422a1b0a4000a768510361480014eb0a206c2900029da1730d85200053ac2e61b0a4000ab684cc3614800156b09986c2900029da1430d85200053ac2861b
  | 19 => 0x28f21953191200061f3b2a63224000e1f6354c6448001c38c6a98c8900028fa1852191200070e318a43224000a5e86dd763480018bcedbaec69000297a1875d8d200062f3b0ebb1a4000c5e76d9763480011bb0f32ec69000297a1665d8d200054f424cbb1a4000a9d8499763480015ad0332ec690002b560665d8d200046fc3acbb1a4000a9f84597634800153908b2ec690002b5e0565d8d200056a40acbb1a4000a5e8619763480018bcec32ec690003279db64d8d200070fb2ec9b1a4000e1c65d936348001c3eebb26c690003871d764d8d200046ec3cc9b1a4000a5e8599363480014bb0b326c690002a7a1264d8d200056b40cc9b1a4000ad58199363480011bf0eb26c69000297e1564d8d200052e42ac9b1a4000ad78159363480015a902b26c690002a7a1864d8d200064f3b0c9b1a4000e1f651936348001c38ca326c69000387dd464d8d200070e3a8c9b1a4000a5e8614b63481858bcec296c69000387d9052d8d200070e320a5b1a40cba5e82dd763480014bd0b3aec690003175d475d8d200052f438ebb1a4000c5e871d763480e94bd043aec69000297a1674d8d200052ec2ce9b1a4000a5f855d363480014b90aba6c69000387d5254d8d200052f42ee5b1a4000a5d85dcb634800153d09b96c690002a761372d8d202c56d406e5b1a4000e4f5294b63480014bd0e296c69032e9721c52d8d203a52f410a5b1a4000a5e85d0b63480014bb0ba16c69000297a1671d8d200052ec2ce3b1a4000a9e849c7634800153b0938ec69000297e1571d8d200052e42ae3b1a406dace821c7634800159b0438ec690002a7a1251d8d200054ec24a3b1a4000a5e85d0763480014bb0ba0ec690162b3a0b70d8d200072da84a1b1a4000a9f84543634800153908a86c69000297a1440d8d200052ec2881b1a4000c5c639da524806d47d0db24a4900030f9db64949200070e31ec92924000c3f73d92524800187ae7b24a4900030f9cb649492000717396c9292400087f8759252480014bf06b24a4900d69720d64949200053bc0ac92924040a7481592524800147d0c324a4900030f9d864949200070e318c92924035a5e86d8e52480018bcedb1ca49000387d9363949200070e326c72924000c5f87d8e52480e98b90fb1ca49032f179cb639492000727396c7292400087e86dd5424806d878c9baa84900031718f755092042c3f43ecaa12403687c87d9542480018b8e7b2a84900038b10b65509200061fbaec8a124000c3c75d914248001938e7b22849000237a1b73509200062fb2ee6a124000c5c65dcd424800193ec9b9a84902bf2719373509206546f43ec6a1240af8dc87d8d42480018beebb1a8490003171d763509200065db20e0a1240008bf845d7614800517908baec2900021fe1574d852001c3e42ae9b0a4000ab684947614
  | 20 => 0x4699065b224000a3f855c764480014790ab8ec8900028fa1471d91200051ec28e3b224000aad821c7644800117d0f28ec8900022f61e51d91200051f42e63b224000a3d85cc7644800117d0e18ec8900022f61c31d91200051f42863b224000a3d850c7644800147d0bb86c8900028f61770d91200071da84a1b2240c58bf8754364480411790ea86c8900022fa1f30d91200045ec3e61b224000a3e85cc3644800147b0b986c8900028fa1430d91200051ec2861b224000c3c64dd564480010fd0fb2ac890003171cf65591200043f438cab224000c5c7319564480018becbb9ac8900031719773591200064e326e6b224000c5f7518d64480018b8ea31ac8900031dd9771591200063a32ee2b224000cb464dc564480019a8c7b8ac8900031dd9471591200063a328e2b224000cb4641c564480019a8c638ac89000e1fa1f75591200043ec1eeab2240008bf845d564480011bf06baac8900063720d75591200047bc0aeab2240048f4815d564480010fd0e3aac8900030fdd774591200061e3aee8b2240018de87dcd64480018beebb9ac890003171d773591200064fba6e6b224000c5f85dcd64480018b90bb9ac8900021fe15735912001c3e42ae6b2240008bf845cd64480011df04b9ac8900023de0573591200247a40ae6b2240008de871cd64480018beea39ac890003171d473591200064fba0e6b22400087e87d4d64480070f90fa9ac89000317dcf535912000e2e39ea6b2240b3c7471d4d64480010fd0ea9ac8900021f21d53591200062fb9aa6b224001c5c7354d64481698e8e2a9ac890003331cf72591200043f438a4b224000c5f7314964481858b8e6292c8901071d1c452591200063bbaee2b224000c7475dc5644800196ee9b8ac89000335dcf71591200066a39ee2b224000c7753dc564480018eaa7b8ac8900031d14b71591200063bba8e2b224000c74751c5644800196ee838ac89000335dcc71591200066a398e2b224000ce7721c564480019e0e3b82c8900030f9db65191200051ec1eca32240008bd87994644800147d0b328c890002a7a0e65191200054ec1cca3224000ab681994644800156b03328c8900022fe1d65191200054fc1aca3224000a9c83594644800156f02b28c890002ad20565191200051f430ca3224000c3e76194644800147b06328c8902168f20865191200045ec3cc63224000a3e8598c644800147b0b318c890002ada0663191200055ac0cc632240008bf8758c644800147f0ab18c8900028f215631912000557c12c63224000ab78158c644800156902b18c8900028fa1463191200051ec28c63224000e1f6518c6448001c38ca318c89000387a1463191200070ec28c63224000a3e86d4c64480014790da98c8900030f9db53191200070fb1ea63224000e1c63d4c644800147d0ca98c8900
  | 21 => 0x8199365480014eb03326ca900021fa1b73d952001c3fc3ec7b2a4000c5d73d8f65480010fb0f31eca900028fa1263d95200051ec24c7b2a4000a768198f65480014eb0331eca900021fe1d63d95200051fc22c7b2a4000a3c8458f65480014ef02b1eca900029d20563d95200c43ec38c7b2a4000c5d7318f65480018bb0e31eca900030f5d074d95206143f416e7b2a400087d879cf65480018bf06b9eca9000e1f20973d95200043f438e7b2a4000c5d731cf65480010fd0f21eca900021f61e43d95200043f43887b2a400087d8710f65480ab4f501b96ca900021fa1f42d95200043ec3e85b2a400087e87ccb65480010fb0f996ca9000e1fe1e32d95201ac3e43c65b2a40c287f874cb654806b0f90e996ca900028fe1132d95200051e42265b2a400087e870cb65480310fb0e196ca900028fa1032d95200051ec2065b2a4000e4d320cb654800147d0838eca900028f61071d952066d37410e3b2a4000a6d821c765480010fd0fa0eca900021f61f41d95200043f43e63b2a400087d87cc765480010fd0e18eca900021f61c31d95200051f42063b2a4000a3d840c7654800147d09b86ca900028f61370d95202ad37416e1b2a400087e8710365480310fb0e206ca900021fa1f30d95200043ec3e61b2a4000a3e84cc3654800147b09986ca900021fa1c30d95200c43ec3861b2a4000c3d75d53644800717f0eaa6c8900028fa1643d91200051ec2c87b2240018bf8750f64480010ff0ab8ec89000e1f21571d91200051ec1ecbb224000a9e83997644800153b0732ec890002ada0665d91200055ac0ccbb224000a9f83597644800153906b2ec890002ade0565d91200055a40acbb224000a3d83197644800147d0b31ec8900028f61663d91200055b40cc7b224000ab58198f644800147f0ab1ec8900028f21563d91200055bc0ac7b224000ab48158f644800147d0a31ec8900028f61463d91200070fb28c7b224000e1c6518f6448001c3d0a31ec8900038761463d91200051f436a7b224000a3c86d4f644818987ceda9ec89000387d8f53d91200070e31ea7b224000a3e8654f64480014790ca9ec89030f0f9d953d91200070fb1aa7b224000e1c6354f644800147d0c296c8900038718c52d91200061eba8ebb224000a3e859cf644800147b0b39ec8900028fa1473d91200051ec28e7b224000a3e82d4f6448001c3ea729ec89000387e0d53d91200051e412a7b224000a3e85dcb644800147b0bb96c890002a7a0f72d91200054ec1ee5b224000a3f855cb64480014790ab96c8900038bd4a52d91200051ec18a5b224000a3e85ccb644800147b0b996c8900028f21632d91206645fc3a65b2240338bc874cb644800147f0a996c8900028f21532d91200045f43865b2240178bd870cb644800147d0a196c8900028f61432d9120007
  | 22 => 0x192cb100021f61c32596200051f42064b2c4000a3d840c965880018bee6192cb10003934c832596200051f424e2b2c4000a3d849c565880018eee338acb100029be09715962067536412e2b2c400087e87d0565880010fb0fa0acb100021fa1f31596200043ec3e62b2c400087e870c565880010fb0e18acb100028fa1031596200051ec2062b2c40c8a6e829c165880010fd0e202cb100021f61c40596200d43f43e60b2c400087d87cc1658800147d09982cb100028f61330596200043f43860b2c400087d870c165880010fb0f32ec910003179ce65d92200043fc3acbb244000c5e7359764880018bccab9ec9100031759573d922000c6f41eebb2440008dd83dd764880010fb0f3aec91000e1fe1d75d92200043fc1aebb24400387e85dcf64880010fb0bb9ec9100023761e73d92200062f3ace7b244000c5d759cf64880031bf0eb9ec910003179d573d92200062ebaae7b244000c5e855cf64880018bb0ab9ec91000e1fe1f53d92200043ec3ea7b244001c5e73d4f64880018bae7a9ec9100021fe1d53d92200043ec3aa7b244001c5e7354f64880018bae6a9ec9100062fe1d43d922000e4f39a87b244000aac8250f64880010fb0e296c91030b179cc52d92200062eb98a5b244000a9e83dd1648800117d0f21ac91000e1fa1771592200043ec2ee2b24400087d87d92528806b4bd07b24a5100029760f6494a2019d4f41ec9214400087d86dd5428806d0fd0eb2a85102161f21d6550a200062e39acaa144000c9c7359142880018bccbb9a8510003175977350a2001c3f42ee8b0c400087d85dd161880018bee6a9ac310007171cd535862000536412a6b0c400387f865d461880010fb0f328c3100030f9d265186200062f39cca30c400087f87594618800187ce8b28c310003179cd65186200061f32ae830c4000c3d655d061880018bccab98c3100031759573186200047bc3ac230c400387e859da41880010fb0b3b4831000e1fa1576906200043fc32eb20c400087f8759641880010fb0eb2c831000e1fa1476506200043ec28eca0c400087f865d621880010ff0eb2c43100030f9d165886200062f39acb10c4000c3e655d2218800187acaba443100031799573886200062eb2ae710c4000e66525862188079bc04338443100035a949708862000732b2ac310c400087d86dd521880830f90eb2a43100039959521086200063732aec10c4000c6d7659421880013cb0fb084310003995976108620005f1406c210c401e87d86dd540880010fd0eb2a811006a1f21d65502200063732aed9044000c6d7659720880791df0eb0e41100f3399c561c82200063d32aed9044000c797659720880d74f30d2964110002da61a52c822035f34c34a59044000d697694b2088001cd2ed296411000297a0e64d95200052ec1cc9b2a4000a76
  | 23 => 0x585400062e398cab0a8000c5f65dcd61500018b8cbb9ac2a00031bd9772585400063632ee4b0a8000c6f651c961500018d8ca392c2a02270f9d065185400047bc3ac230a8000ad48358461500015c904b08c2a02268fa1b65505401751e428c4a0a8000a3e869494150001c68cbb0a82a00038dd9461505400645f430e0a0a8000c3c651c141500010ff0abb642a000e1f21576c854001c3e42ced10a80048bc849da21500010ff0abb442a000e1f21576885400043e432eb10a800087f87d9621500010fb0fb2c42a02230f9d365885400062f39ecb10a8000c3f655d22150001878caba442a000317d9573885400062e32ae710a8000cce73d8a215000195ae831442a0003339cc628854001c3f42eec90a800087d85dd921500070fd0b3b242a00021f616764854001c3e428ec90a800087e86dd521500010fd0fb2a42a00021f21f65485400043fc2aec10a800387c855d821500011bf06bb042a00063720d76085400061e32ae810a8089a3e86d96405011187cedb2c80a02238ed8365901401051e428c52028000a3e8694a40500051790cb8c80a00030f19571901402565a30ae3202800087d879d764c80070ff0ebaec9900021fe0d75d932001c3f42ee7b26400087d85dcf64c80091ed03b9ec9900023d60773d932001c3fc3ea7b26400087d87d4f64c80010ff0ea9ec9900021f61d53d93200051f42ee8b2640008be87d5164c800187eebaa2c99000317dcd535932000e2e39aa6b2640018bc8750d64c8003938e6a1ac99000e1fa1771593200043ec2ee2b26400387d87d9252c800517d09baac3900022f613755872001c3f42ee8b0e400087d85dd161c80011ef0eb08c3900030f9d5649072001c3f42eeca0e400087d85dd941c800917d0fb2283900ba8fa1764507202073330ca590e4000d6a529c321c80018d8ebbb243900031bddb75487201051f42ec92064000c3c7559140c80010ff0cb9acb103425b20973596200043f43ec6b2c4000a3e84d8d658800147b09b1acb1006a1fa1e63596200051f424c6b2c4000a3d8498d65880018bee731acb1000e1fa1d63596200062fb9ac6b2c400087e8718d658800187ee93a2cb100030f5d074596200043ec3ce6b2c4000a3e849cd658800147b0939acb1000317dce735962000537c12e6b2c40cfa6c825cd65880018bf06b9acb100031be09735962000636412e6b2c400087e871cd65880010fd0f21acb100021f61e43596200043f43886b2c400087d8710d658800147f08b92cb100028f21172596200052fc1ae4b2c4000a5c835c965880014ef02b92cb100029d20572596206453dc02e4b2c400087e87d0965880010fb0fa12cb100021fa1f32596200043ec3e64b2c4000c5f738c9658806b0ff0e992cb1030a1f21d32596200051fc2264b2c4000a3c844c965880350fd0e
  | 24 => 0xc800087c8754d61900070fd0bb92c3200021f617725864000c6f41ee4b0c80008dd83dc9619000195885b92c3200021fa1e52586400043e43ca4b0c800087e8714961900070f90e292c3200023de1d61186401049e42ce520c800093d8794a419009317f0cb84832000e1fa1776c86400043ec2eed90c80018de83ddb21900011bb07bb6432000e1fa1676c86400043ec2ced90c80018de839db21900011bb073b643200824f21574c864000656ba4c590c800087f855d921900070f90abb24320012b920562486400043fc2aec10c800387c855d821900010fd0db9ecaa000e1fe1f63d95400062eb9ec7b2a800087d8798f65500010ff0eb1ecaa00029be0963d954000536412c7b2a8000a778158f65500014e902b1ecaa007a1f61c63d95400062eb98c7b2a800087e82dcf65500010fb0f39ecaa000317e0d73d95400043e412e7b2a800087e871cf65500018bae639ecaa00021f60e72d954000636b90e5b2a800087e87ccb65500010fb0f996caa00021fe1e32d95400043fc3a65b2a800087c874cb655000147f08996caa02228f21132d95400043f43865b2a800087d870cb655011147d08196caa00028f61032d95400072699065b2a8088a3e841c7655000147b0838ecaa00021fa1f31d95400043ec3e63b2a800087e870c765500010fb0e18ecaa02228fa1031d95400051ec2063b2a808887e87cc365500010fb0f986caa02228fa1330d95400051ec2661b2a800087e870c3655003d0fb0e186caa007a1f61f65d894000537416cbb128000a6e8219762500070ff0ebaec4a00021fe0d75d894001c3f42ee7b12800087d85dcf62500070ff0fa9ec4a00021f61f53d894000537416a7b12800087f8754f62500010fb0ea9ec4a00029b20953d894000556c2065b128000ccf730cb62500010fd0fb2ac4a0003171cf65589400043f438cab128000c5c7319562500018becbb9ac4a00031719773589400063bb2ee2b128000c7465dc562500018eeca38ac4a00031d194715894000477c3ac43128000acc8358862500015c902b10c4a00029ba0b75189400052ec18ea3128000a6e821d462500010ff0ab98c4a000e1f21573189400145e422e6312800087e87d4c62500070f90fa98c4a00029ba0b53189400043e43aa63128001c5e7354c62500018bae6a98c4a00029b209531894000666b9864312800087f855c462500070f90ab88c4a00028f613769494000537416ed292800087f839da52500010fb073b4a4a00030fd0676949400061e204ed292800087e861da52500014dd043b4a4a00021fe0c76949400043ec18ed2928000c6e821da525000917908baec2a00021fe1572d854001c3e42ae5b0a80008df835cb61500031b906b96c2a0002ad61031d854001c3f436eab0a800087e87d9561500018b8e7b2ac2a00021fa1c65
  | 25 => 0x4010fd0e32ac0908030f1d065581210062e398cab024200c3f65dd16048401878cbba2c09080317d9773581210062e32ee6b024241c6d7219460484011f70eb00c090802ae21160181210056c41ac0302420087f855d060484070f90aba0c090807179cd53181210062eb9aa63024200a6c8254c604840157509980c0908122fa1f54590210061fbaea8b204200c5f7354d64084038b8e6a9ac8108122f21d435902100e4e39a86b20420387e851c164084010fb0a382c8109031d1d971948210063a3aeec9084200c7753dd921084018eaa7bb242108033994b764842100672a96ec9084200c7452dd921084018eeedbaa4210902d920b754842120cbb43ca49084200c777694921084836cd0f2924210b4b59a1e5248421206b3bb4a49084200e677694921084018ceed2924210b46d9e0e524842168db2c1ca49084200b6785509210840178f06a1242108035994870484210045fc22eb30042028bc845d660084010ff0aba4c01080e1f21574980210247cc3c61300420387e87dd560084978e8e3baac0108021f60f75580210045fc22eab0042028bc845d560084011bf06baac0108063720d75580215f63a388eab0042028be87dd1600840187eebba2c0108030f1d774580212565a38ee8b004200c3f751d16008401878ea3a2c0109272d1c4745802100c6f43ee6b004200c5f75dcd60084018b8ebb9ac01080327dd373580210064e3a6e6b004248cd471dcd60084018bf0bb9ac0108031721773580210043fc2ae6b00420387c855cd600840117f08b9ac01080a2f21173580210062fba8e6b004200c5c751cd600840193ee839ac010803271d073580215ee6a388e6b00420087e87d4d60084070f90fa9ac0108030fdd353580216261e3a6a6b004200c5f73d4d60084038b8e7a9ac0108021fa1d53580210043e43aa6b004200c3f7454d6008587878e8a9ac01080317dcd535802100e2e39aa6b00421a87e87949600840187ee9292c0108db0f1d252580210062fb9ca4b004235c5c7394960084010fd0e292c0108030fdd0525802142e1e3a0a4b004200c5f7314960085858b8e6292c010807361ce30580210247c43a60b004200a6c8254e62900070fd0fbaac5200021f60f7558a400043fc2ae6b14800387c855cd62900010fd0fa9ac52000e1f21f5358a400043f43aa6b14800087c8754d62900014d904a9ac5203322f21d4358a4000477c3ac43148000a6e82dda529006b4bd073b4a5200029760e7694a400061f3a0ed2948000a6e821da529000187eecba4a5200662fe1d6290a4000716b14a5214801b8bf865c242900070fd0fbaac3200030fa1375586400061ec26eab0c800087d83dd561900010fd05baac3200030fdd754586400043fc2ae6b0c800387c855cd61900010fd0fa9ac32000e1f21f53586400043f43aa6b0
  | 26 => 0x31ba0b73d952100636c16e7b2a420087d879cf65484018bf06b9eca908021fa1c73d95210051f420e7b2a4200a3d841cf65484018bae639eca908021fa1e43d95210043ec3c87b2a420087e8710f65484010fb0e21eca909021fa1f42d95210043ec3e85b2a424087e87ccb65484010fb0f996ca90803175ce32d95216143fc3a65b2a424087c874cb654840147f08996ca908028f21132d95210043f43865b2a422787d870cb654840147d08196ca908028f61032d95210062eb9865b2a4200e4d320cb65485274dd05b8eca908021fa1f41d95210043ec3e83b2a420087e87cc765484010fb0f98eca908028fa1370d95210051ec26e1b2a427da6e821c365484814db04386ca908021fa1c40d95210043ec3881b2a420087e87cc365484010fb0f986ca908028fa1330d95210051ec2661b2a420087e870c365484010fb0e186ca908123b60b73d912101c3f42ce1b22420087d859c364484010fd0fb2ac890803171cf65591210043f438cab224200c5c7319564484018becbb9ac8908031719773591210063db2ee0b224200c7865dc164484018f6ca382c8908031e19470591210065c320e0b22420387e87dd564484010fb07baac89080237e0d755912100c6e41aeab2242008fb805d564484011f100baac8908021fa1c755912100c6f43ee6b224200c5f75dcd64484018b8ebb9ac89080317e1773591210062e42ee6b22420087f855cd64484070f90ab9ac8908022fe1173591210047dc02e6b2242008f8805cd64484011bd0e39ac89080317dd473591210062e3a8e6b224200c9f741cd64484010fd0fa9ac89080e1f21f53591210062fb9ea6b224201c5c73d4d64484010fd0ea9ac8908021f21d53591210062fb9aa6b224201c5c7354d64484031790ea1ac890807271cd43591210055641286b22420087e8714964484018bee6292c890b0b171cc52591210063dbaee0b224200c7875dc164484019b6e7b82c890803361cf70591210063da9ee0b224200c7953dc164484018f0a5b82c8908031edd470591210063c3a8e0b224200cbb741c164484019b6e6382c890803361cc705912100675b90e0b224200cf3711c164484018f6a6382c8908031e54c70591210065da18e0b224200cb9431c164484018f0a4382c8908032e10870591210043fc3ac92924200a5f83592524846b4b906b24a4908029ee0164949210053c402c929242048bf87592424846753906b248490802ae201649092120c3f436eaa12428587e87d9542484810f90fb2a8490803171cf65509210064e39ec8a124200c5f65dcd42484018b8cbb9a849090399d8b65c85214dd3b434a590a4240e676294b214840517d09baec0908022f61375d81210055d42661b02420387e86dd560484810f90dbaac0908021fa1f65581210061e3a6cab024200c5c73d956048
  | 27 => 0xfc2ae4b244200a3c855c9648840153f06b92c910802a720d72592210055dc02e4b244200ab8805c96488401c5ea5292c9108028f60c52592212051f410a4b244200a3e85cc9648840147b0b992c910812ada0732592210055ac0e64b244200a3c858c9648846717f0e992c910b322f21d32592210051fc2a64b244200a3c854c9648845317d0e192c9108022f61c32592210051f42864b244200a3d850c96488401d1a64192c9108028fe1570592210051e42ae0b244200aaf825c1648840147d0a382c9108028f61470592210045fc3aa0b2442008bc87541648840117d0f982c9108022f61f30592210051f42e60b244200a3d85cc1648840147d0a182c9108028f61430592210255b40860b244200ab5810c164884018beeb3aac710ad29761e7558e214f52f414eab1c4200c5f875d563885ab4b904baac710ace97a147558e210052f42ee8b1c4200a5d85dd163884014bd0a3a2c710802976147458e210070faa4a8b1c4200a5f855c963884014b90ab92c710802a7e117258e210054e422e4b1c42d6ad7815c963884015b700b92c710802b62017258e2100727a94a4b1c42d5a5f8714963884014bb0e292c71090297a085258e210052f42e84b1c4200a5d85d0963884095ad03a12c710802b56074258e210052f42ee0b1c4200a5d85dc1638840153d09b82c710802a76137058e2100567c12e0b1c4264acc825c163884014bd0a382c710802976147058e210054fc22a0b1c4200a9c8454163884014bd0a202c710802976144058e210256b40880b1c4200ad581101638840187ee6b24a5108030f5cd6494a2120e1f392c92944200e2e72592528853d8bd0eb1ca5108031761d6394a2120e2f392c72944200e4e7258e52884010fb0dbaa85108db0f9937550a210062f31eeaa14423687e87595428850b0f90eb2a8510803171cd6550a2100716212caa144200c3f755914288401878eab228510803271cd6450a210046ec36e6a144200c5e65dcd42884018bacbb9a8510abf279937350a210064eb26e6a1442af8de8758d42885951b90eb1a851080317dd56350a210062e3aac6a144200cb564dc5428852f4eb0d2964310902d961a52c86214bf32c34a590c4240d657694b2188401ccaed2964310903c999252c862120792b24a590c4240f466394b2188481e8ac729643108022fe1175982210145e422eb304420087f855d260884070f90aba4c1108022fe1175582210145e422eab04420087e86dcf65485a92dd05b9eca9080e1fe1f63d95210062eb9ec7b2a420087d8798f65484010ff0eb1eca908028fe1163d95210051e422c7b2a4200a7b8058f65484014f100b1eca9089e1f61c63d95210051f420c7b2a4200a3d8418f65484018bae631eca908030fdd274d95210061eba0e9b2a42d3a6e82dcf65484814db05b9eca9080
  | 28 => 0x58862504014d904a98c4a08021fe15701894101c3e42ae031282008df835c062504031b906b80c4a08030f9d3769494100537416ed2928200a5f835da525046b4b906bb4a4a08029ba0876949412051e432e92928200c3c765d2525044d17b0fb1484a08038bd8a529094124c5e432e1212820087f855cb60504070f90ab96c0a08023ee1d601814100574412c030282028bc845d460504070ff0eba8c0a08030fe1175181410061e422ea302820087f835d460504010f904ba8c0a08030f5d7541814101c3f42ee6302820087d85dcc60504070ff0fa98c0a08021f61f53181410043fc3aa6302820087d8754c60504010ff0ab90c0a080e1f21572181410046fc1ae430282018dc835c8605040195884b90c0a08021fe1e52181410043ec3ca4302820387f8714860504010fb0e290c0a0807179cd53d93210062eb9aa7b26420387e859c364c84010fb0b386c99080e1fa1f75593210043ec1eeab26424187e82dd564c84010fd0e3aac99080e2f21d54593210043fc2ae6b26420387c855cd64c84091d904b9ac9908021fa1f535932101c3e43ea6b26420087e8754d64c84010f90ea9ac9908062f21d43593210055641286b26420087e8714964c84070f90e292c990aba1fe1d6494b212043e43ac9296422ea3c8559141c840195ac839283908021fe0d759832101c3f42ee7306420087d85dce60c840517d09b9cc1908022f613739832101c3fc3ea7306420087d87d4e60c84010ff0ea9cc1908021f61d539832100536412a7306421887d8794a60c84010fb0e294c1908022fe1175583210145e422eab0642008fb8758060c840187ee93a2cb10ad21f61e73596210062fb9ce6b2c4200c5f835cd65885670fd0e39acb108021fa1e43596210043ec3c86b2c420087e8710d65884010fb0e21acb10b5e9de0572596210043f43e84b2c420087d87d0965884010fd0f992cb108021f61f32596211ac3fc3a64b2c42c287c874c9658840147f08992cb108028f21132596211543f43864b2c420087d870c9658840147d08192cb108028f61032596210072699064b2c4200c7b709c1658840147f08b82cb108028f211705962100537c12e0b2c4265a6c825c165884010fd0e202cb108021f61c40596210043f43e60b2c420087d87cc1658840147d09982cb108028f61330596210043f43860b2c420087d870c1658840917d0faa2c9108030fdd754592210245e43aa8b2442048be8790d648840147d0b21ac9108028f61643592210245e43a86b24420387e851c164884010fb0a382c9108030fdd675592210051f42ce6b244200a3d859cd648840147d0a39ac9108028f61473592210051f416a6b2442b4a3d8594d6488401c3ea729ac91080387e0d53592210051e412a6b2442b3a3e8514d648840147d0bb92c9108028f61772592210051
  | 29 => 0x82c2a100336d8f70585420066c31ee0b0a8400c7b651c161508018f0ca382c2a100336d8c70585420066c318e0b0a84008f78758461508015e100b08c2a1003179cf65981420062f398cb3028400c5f655ce60508018b8cab9cc0a1003179d763981420062ebaec73028400c5e7518e60508018baea31cc0a100e1fa1b75581421b43e436eab02840087e87d9560508018b8e7b2ac0a10021fa1c65581420062e398cab0284018de86dcd60508631b90db9ac0a100317d9773581420062e32ee6b0284008de87d8d60508018beebb1ac0a1003171d763581420046f438c6b028400c5f7518d60508018b8ea31ac0a136333dc863581420063bb2ee2b028400c7465dc560508019aec7b8ac0a10033518f71581420063bb28e2b028400c74651c560508019aec638ac0a10033518c71581420047dc3ac03028400af081580605080155904a18c0a10021fe15711814201c3e42ae230284008df835c460508031b906b88c0a10021fa0b73596415a43ec3ce6b2c8200c5f739cd65904018bf06b9acb208021f209735964159c3f438e6b2c8200c6f729c965904010fb06392cb208021fa1f32596410043ec3e64b2c820087c878c965904010ff0e992cb208021f21d32596410051fc2264b2c82a8a3c844c965904010fd0e192cb208021f61c32596415451f42064b2c8200a3d840c96590401c9a64192cb208031edc270596410051fc22e0b2c82a8a3c845c165904010fd0f982cb208021f61f30596415451f42660b2c8200a3d84cc165904010fd0e182cb208021f61c305964120d37416eb3148200a5d831d662904814dd043acc5208021fe157398a4101c3e42ae7314820087e87d4e62904070f90fa9cc5208029ba0b5398a410043e43aa73148201c5e7354e62904018bae6a9cc5208029b2095398a4100666b9865314820387e859c262904010fb0b384c5208021fe157098a4101c3e42ae1314820387e87dd562904010fb07baac5208021fe157358a4101c3e42ae6b14820087e87d4d62904070f90fa9ac5208029ba0b5358a410043f43aa6b14820087c8754d62904014d904a9ac5209021fa1c5258a410257340e64b148200aad840c9629040199ae6192c5208029ba0b7694a410043fc1eed294820087d83dda52904018dd05bb4a5208021fe0d7694a410043ec1aed294820387c825da529048187e82bb4a5209030f5057694a410061e202ed294824187f8758a52904010ff0ab94c12080e1f21572982410046fc1ae530482018dc835ca60904018bee6a9ac120807171cd535824101c3f42ee4b04820087d85dc960904070ff0ebaec4a08021fe0d75d894101c3f42ee7b12820087d85dcf62504070ff0fa9ec4a08021f61f53d89410043fc3aa7b12820087d8754f62504014d904a9ec4a0b322fe1d43d894100477c3ac43128200ae88
  | 30 => 0x82421b43fc3ca5304841887d8794a60908070ff0e294c1210021f61c52982420062fb9aa6b048401c5c7354d60908011f70eb00c1210021fa1b73d954201c3fc3ec7b2a8400c5d73d8f65508010fb0f31ecaa10021fe1d63d95421943ec38c7b2a8400c5d7318f65508018bb0e31ecaa138387a1063d95420070ec20c7b2a84e0e1c4218f6550801c38c6a1ecaa1002cb20943d95420043ec3ce7b2a8400c5f835cf65508010fd0e39ecaa10da8fa1073d95420051ec20e7b2a8400c5d731cf655086d0fd0f996caa10021f61f32d95426143fc3a65b2a843587c874cb655080147f08996caa10da8f21132d95420043f43865b2a843287d870cb655086d47d08196caa10028f61032d95420072699065b2a8436a3e841c7655080147b0838ecaa10031d5c471d95420043f43e63b2a840087d87cc765508010fd0e18ecaa10021f61c31d95421b51f42063b2a8400a3d840c7655086d47d09b86caa10028f61370d95420063cb80e1b2a840087e87cc365508010fb0f986caa10da8fa1330d95420051ec2661b2a840087e870c365508010fb0e186caa100297a1b75d8d420062f3b6ebb1a8400a5e861d763508018bcec3aec6a137f179db65d8d420046ec3ccbb1a84dca5e8599763508011bf0eb2ec6a136e97a1865d8d426f62f3b0cbb1a8431a9e86dd3635086793cedba6c6a1376e3a0b74d8d426dd2f430a5b1a84c2c5e7614b63509b54bd05baec6a100297a1675d8d420062eba8ebb1a8400a5e871d763508018bd0e3aec6a12b697a0875d8d4200727a94a5b1a8400a5e8714b63509b54b90e296c6a12b697a0852d8d420052f42ce3b1a8400a5d859c7635086353d0938ec6a1002a761271d8d420066bb8ce3b1a8400a5f855c763508014b90ab8ec6a12bea7a1251d8d420054ec24a3b1a8400a5e859c363508014bb0b386c6a100297e1570d8d420052e42ae1b1a8400a9f845c3635086353908b86c6a1002a7e1150d8d4257d4e422a1b1a8435a5e86d8e52509b98bcedb1ca4a136fc310b63949420062fc3ec729284adc5c87d8e52509b58bce5b1ca4a1003939cb63949420070e31ecb2128436e2f62d96425086753d0db1c84a12168fa1a52909425870e31ca52128436d2e7294a425086dc5ec529484a1002ab20943d854201c3f42ce1b0a840087d859c361508031bd07386c2a10023760e70d85420062f39ecb30a8400c5e7319661508018becab9cc2a10031719573985420062f3aec730a8400c5d75d8e61508018bcea31cc2a1003175d463985426ce66b90c730a840087e87d9561508018b8e7b2ac2a10021fa1c65585420062e398cab0a8400c5f65dcd61508018b8cbb9ac2a100237a1f63585420062fbaec6b0a8400c5c75d8d61508011bd0e31ac2a100317dd463585420062e3a8c6b0a8400c7b65dc161508018f0cbb
  | 31 => 0xa436c3e74592619486b0ff0eb1cc3290d7179cd63986520062eb9ac730ca400a778158e61949c96cd05b0cc3290024fe1170986521b49e422e130ca41396c825c261948810fd0f322c3290030fdd264586522053b40cc8b0ca40087e87191619480127f08b9ac3290da4f211735865269d37416c6b0ca44087c8758d61948018bee6b1ac3290d7171cd63586522053a40ac6b0ca493b6682d8561948392dd04382c3291070f989741865200697312e830ca436c3e74d9061948014eb03b20c3290021fe1d64186521b61f3a2c830ca43587d87d8c619480187ce9b18c3290030f5d363186520062eb9ec630ca400a7581d8c619480187ce8b18c3290030f5d16318652004bbc3ac230ca4e3d667258461948814ef0eb08c3290031de1d61186522071b3a2c230ca440e357458461949c78ece4b08c329103999c961186521b49fc3ae9b04a400c3e625d36094801a5cc4ba6c1290db0f9d364d82521b61f3a2c9b04a43693e84dcf609480127b09b9ec1290025ba0b73d8252204bb40ee7b04a40097581dcf609486b0fb0fb1ec1290030f9d363d82520061eba6c7b04a400c5d73d8f609480187ce8b1ec1290030f5d163d8252006973a4e5b04a400d2d749cb609480187ce9b0ec1290030f9d161d82520061eba4c9304a43693e84dce609480127b09b9cc12933e9ba0b63982521ac3fc3ac7304a435c5e7358e60948018bae6b1cc12908e5b20971982520063ab8cc3304a400a3e84186609480147d09b04c12916edaa0b60982520043f43ec8b04a43687c87591609486d878e8b22c1290029e20164582521ac3e43ac6b04a400c5f7358d609486b8b8e6b1ac1290029e20163582520043f43ec2b04a44087c8758560948818e8e2b0ac1290029e20161582522adb5416c0b04a40087d87990609480187ae8320c1290029e6006418252004b7416e6304a43587d865cc609486b0fb0fb18c1290d7179cf63182520062eb9ec6304a4e2a6e82d8c60948014f301b18c1290021f61e61182520051f420c2304a400c757118460948014f300308c1290028fa136018252646b5394c0304a40087f8758060948012f70eb00c1293875a9c960182520053dc3ac0304a400c7b8758060949c38f4e4b00c1290039a9c960182521b61fbb2e9294840387e87dd5619080187d09baac3210030f61375586420043ec1eeab0c848587e82dd561908010ff0ab9ac32100e1f21573586420043f43ea6b0c840387c87d4d61908010fd0ea9ac3210021f21d53586421543f43ca4b0c843687c8794961908010fd0e292c32100e1f21c52586420047bc3ac230c840387f875d6609080187f08bacc1210030f21175982420043fc1aeb304848587c825d660908070fd0bb9cc1210021f617739824201c3fc3ea7304840087d87d4e60908010ff0ea9cc1210021f61d539
  | 32 => 0x80000150010004000017003011000a000002000000400100200580000110000000004008000000400e01c00480080020070188060084005005803c00c00000400ac01600200200ec0000020000000020002001007c02200002d800000000a002002800606500e8004002006000800c004003002000c02400a000800000800300580380020000028028002000000002400a01900900000020030070008002002001002c00801500400140000080068010022011000000400200100000f4016002000003c092028000011c038012003000c00e000010000001c03c0000004012000001803c02e00102180080000030040000000004009800401a000002000800200a04e00380280060050010026002002002806a000001800002e02b000000000000c0020098008003003800c002000008800800200001700240100040098030008002013800000a000001800800c0000000088010009002000c00a006002000004c00000500080060000018008002005000800400c000002800400c00500c800000e0030100008006001001800806c00600a8014008003000000c01a0090050020004003000009400800100700080060220018000002001001802804e00d00200040060000018010004000003800402400700000680020000040090008005002804c00200200a000001400a00000140000270010008004006000000c022003000000000600700600e4000015001003408800c01b800000600000c800402200001a802003a002005805c004021006000c012009001802000000200b003c00001d00b000c00800000300100060010050030016006000000000e00700a00640020010020000024004004801c00000a000000800a01000180100000070118000034000004800002600700880000040180070018010018005006801c01400d80140020000020000006000001004800c000001800c00201b00000080000150000054028000000801400400600100080140000010080002002003801800e009000000000400d001000400600c00d8014000008000003c066001002001402c006003800002200200100700020170050008000000001001400400800080040040000000018002015001002800000a00f0014008004000002c00402e00100140187cc9b9ec9290025ba0b73d92520061f322e7b24a43587d87d8f649486d47d09b1ec929003175cf63d925273f17324e5b24a400c3e645c7649480187cc9386c9290db0fddb645925273597416c8b24a436a3c84d8d649486b0f90eb1ac9290da8f21163592520062fb9ac6b24a435c5c7358d649486b2790ea1ac9290028f21943592521ae8e39a86b24a400c3d7419361948012dd05b9ec3291021f61f63d86521ae2f39ec7b0ca400c5d73d8f61949cb4dd05b1ec3291029da0763d86521b43fc3ac930c
  | 33 => 0x9802c01000100d006800000f00200280000040050038008007000003c02200f02800000280000020000002006005805002c0010048018026000000000006a001004809c002000000001400a004008000400a00a000800401a0010000014002002001000802000300180180160040118020000003002801c01000200c0000002000001001000c000008800c00c00000f80000040040098000016008000800000000800000200000050028000020004015801001400200000040080020018028008000000001c086006000000c006007000801401600203a8004014008002006000000900a00c0028000000800c000000000001400e019005001801a000002800c00a005000000407e007000003c03200f003800000401600c8004000006001000000800200080000680110000030026003000801000c05f0000000004023003001c056003003001813606d0000000000006001800401c00000000a00140020000008028003001800800c00000000d800004900980280000020010090006017001015000202e00f00000400000008004008000003000c0020080000024004000008800002a00000680080340040088000016003001003800800300102200000060048004002041010800805e00700180f4008005001806400e004001800000e00100300140020030010000000002000000800a0150068044050000000800800000c00c0000000000008807400000700080140140060028018030012003800000200000b8010004001003803800e00000001b800000a019023c010009003801800000000f8040008000000003403a0040010024006000003803800c0210008010000001004001c00000600200340080050000030000007003000000a00000080280040080000020030004015001800a01300e80000080030000050000003002001c002004001005c0de00e00c801803a00b000001c014006004801800000c0020034000000006800000a009001800403400200900200400040010000002007000801c0020050000000004000002801800200001c00480000040010030000002001800002400c0018010024007000005406000700100000a400c000800800a0080020050006000001004c0080070008000010000006001c000000002802c000001008001000402b0030014012001000006c01a001002803800a0040030000002006014002400a00000e80000080000020008000004001804004e001009804400400700980200060000090048006004000009800005e000015800a014004000000c0000000000022002008800000001b000000800401000080f800000600a000800e0010010028000005006001c01a01401f000800800700a0000002016001000000e001008003000800a006801000000d0000018024001007004c00e003001003
  | 34 => 0x8c0b3a192098100800000003169dbe5520a564d8932850c98b443b19d66aa80006800fbe4051b545461dfa2d81e640558cd61fc99546270a9a00021dc8460a8c3d1800052f84da08b87bc608161633a146c3c7039c26f0f826ba9f1204e000041d954a4809be48491968000135c35e00600caa2ac44901424cf826486f8d5850711b6789176e3ce8d6a27fa16c01208f22d98b96556000000007dc2e698403e3880417b9d4c20d900c2ba8ac04d21f1017d87e881e9ac65fe9dd6358a234180124e33da02217c000012ea1ae7bd01e07a000a42cc93a4000169c542927a1f822903151c022b704f05ff000000018680001ea202d000000014f031980008458c98000183c000000040f80004bd800014692b456e02a00361a7836813605ff9de200021ec33f21b41fd0860874000084297dc000081a5fc80000e794ca4c3941a7dd00005370c4c8102222342a13a0000280000209a31d0000000214a38c0bfa1c980000db9d160b68e2c03309626e7812081d9c60373883e09480ea78a994c7681aa08508faa1ae99a03b092d82a8220200004bc27689aa6909fa80081dc44ab87be534969207b9dc8077988e305082264618042050bde2ec000037d80002a01eb417980000028004006001005000400a017004000800c063000000000600000d000000400100700140020000018008006002000001400a020001800801000000480000080030120000000004000004800000400e014800a0070010000022000000801000a00000080340280030008008000010000802400600c001003c00a010008008c000000000001002202b0058000006006000804c000020002801c0160090050008024002001002800000a000801000c00300080380c000001d800000200300180140060020028058000006000003400001b00e0010024000000001c0080150008020024008004800001200f006001c002000000001000200b010001801a00e007000803a00000e000400000000080fc00800502680b802a00d0038148000004000800000800e0030028002020009004c0000000030020008000004804401c01100100200460000010000000000007000000600100a00040060050040000000000000000400200a00200140040020010018000005000007400e001006003800600000000000060000028004006000000001000a000000800400400803f800400000700a000c002003002801002a009001000c00400000180180140020238008002003001801000a001009003400000600080140980150000018004003007000000e004002000000a0010010030000000001000c002000001803803e00000200340000010008064000002000000800000300a00300060030060044006013028002401a02000000440160030010084000002000008401c004000000000600
  | 35 => 0xf3a0e43f590f856b064600014a05968e8839d13026ce024400022c60000dfa7138db058217345740d4800000002fd00001b9997a6b40d807050e7a2210da225c80000000fa81ba000055801300c100000000fb0000000037f86960a7208a6b890f618610ba1e0161c36e091825b95e614913c66e90b742b31aae75902ea6201a9600007381f58ea283c87ba00009de458998480380001a888b40601cb01de03784dc166200019e445f1dfc00000002f8921a0c987b00001b005b68cbc5f11e2c8188000049843a00000000001de601c199a794855c8448150791000019b00000ac864854c9d181f39c96000200867182ee14480001068880578939045d024655d80003f9000000021c64f5127074c87fc30a000029183a201000004cb15707d700005400d38629023204100000000d3033a9646682a0825369a1a43c00000000af62aa1e36700176423606dc627a0366d6a08e16f94c67fc129c5fc047221d1b0a84b9cea37188dc47380660f796ce79e813c6c7a2ae07017580f997ca7400cb63b001d8540897662a846484a192048d1636336019e1d91f66588858e10d1cf035306b61c70fa414292463071482754165e4da9d046a7082c4a8906810203d447d83584df9cce8928e9c8501df20a188ec2db96d868aa2c463a1bfe0000eb0470800041217c618a2292000205624318f413e9fee5b80f2203f8b8225b145e7eb9324744800045900f852293dc4408c342d4054a68300384b6a25661398f22c48e9035f1d4a4248c161569cf200011c68610c3a5b288e077d04e000013567cb978a0b40ecc32420680000c9408f8b3c0c21f22800800070e000039b8d2e4340d360ce8e0684522e80000b5e74b9e8c75f030244515860e200161d720d022587fe309829a7de15a47e008fa63aa0f418787568030bb2897203a12c00001e1898c07908f04850cb240d04d2780800024400f01269ad236da0ce35ca05206c20b421f8634013817e8b8846c4f0106275681f41a01ee207e19a65c0000021c16c02669ad85f90d200cf92fe7f210a85c3a0467db814a000000060214a26ae8ff019a075289088e47af979e6449fa673b800000020ec2e71434616132a55f0eee88f9d7236180002a60e6442013642f308624900000769005a5cf875a6048b1035b1330000020219d876c000000000020e60ec9de40000000594910c83c00004b8816e00016ae78405b67a20c2255113f479702922bf967618ca2962b113e63df00004b109522f1000024c897478b834881b884e0659cfa704860a3ae9b300ec00907d217ac869a01630310467a80bd478482cc7fe0742158157a76a8a9680784d45699e1e7bf963a48414488081f924ed9f0a84715b4584123266091fe21c9f1e7eb0b0259401f0095161400021f000000a6000072c57c800004294d44c89b2e556a2
  | 36 => 0x3fe2e322545340f0a5810c4a000195a0001df673a126a68902fc0000fd0592000082a80005d9931e1e80eea299977c6ee87e618714720001596734a2486340cbe2a200e638600003b41ae88319d543730b461d78c1a67201828321c0a01303b43ad879c01120e03781cfe4ae0e78667113406990fe26d12c84d481cc3cb03e25b71bde7a38c6238311920278d646d794de0e48dd652d04f8000002600020320661d485ae14e629215d26eb108e5ac00004ab18185898bd63c69b0c16421045308b886c211be3cd86a80bca0b242101f6793848400013f040100004d19b3c27a0e244ef215a6d38f240400bf040b810c6e899564cd1d0e85417ba3e017687318f5a1ce9d3c00b179a68e226a34c953c26b1fd60001b74000000011580000000e280788d961bd202c4a000002da0b225c780000971a6e0001c9a2399d984a7956a6cd12cc2de8412647915215a816837c9f8a193198083698be06383a61b1845816c0f2864a1d6066380002d20036000000063e9d103008a8a000173c35c093a49500007600ef830404362561ef65418f840000a820000c68249a0964961f3000003b85e494780000c86000000020180004c405b43c780000b9982c2b0800017e0e967ab89347c12152000174029c225272d8a6451890f4000118c6cc884c3b709f20b20cf832497d00000f766540982716953887315c43f2000018393b841f029e69616a000018b0538968022806c47b280002c506ac4f498a816103cc2ba0d3a000044e3e413aa7af03640d3154236b897a3b69cf682b02aa1fba13c6701cb85d2164059c8e500000ba028480001171ea8044000071489c05a1000000000001aa887a1c09252879927e57b915008c1c182a51ee628022380bc22c80000bfc3fc8000000197e35580004109216000093c73104be00000884eb9e6a859a1fa35982664de963c8a20bfe76e000060410b018d8e120cf15f400000000001f6c7ae86de1868824625a0e2529815c694a2c28091d7878888ea2429b1c5ed9402153069e4bb1e380e110e4476156453e9574000000070680002418000000000042d843e812800000004dc1628000000000025294227a29bb23ed800067a80000000c7a4a404c87da883c30b1530317112c6e380001a313447e6000000017067a1073c00008de2dc14560001fec6f3000064297be0001e424d60de45ca11b285e80004b8065a7ca1c9481f19700000000281800032b9dba0000000000000032a800064110183fa1cd07719600461162a2d0823a2a1101a41118e022f852264e22e0165a1e2527821a0001e4a81c96f206e89086cf80000fe9d8c0001bb60a2024e80680b806194b80001a7c26596f6111077652300004c2945081c0564235822283080008778000000088e06b000063d800014c80001b4803e068007a07f9a9e00000000
  | 37 => 0x5a5006879d9d207d60000545a08865101fa0000f4a000041866e176000022142b6008c691842429d0c040860000000032e5e8800000003e000016fc0c921907b100007a1800015e1480483000042c80008a3a1b201c958a0000c567f60a3e00004a466306820eb80005311fe20c6016a000046628e049c00012b21df9fc60fd19887ce030c50190e8560932e2260d8885310120b8142608010b814608864af000036a09dc3ee89ec00015662ee8b1e3aa835667383140000cba88b982a7d8228465b122c54b15284ef94bc15b123e4fa07a41c69f346f48cdc61f853a48e228a8201f5012b000021987327229b6235491b429e80000000e3825e151261719523da00003729a5a4b18bb883b8922000195e5689b828510ce47698bc03e78cb40000d5a7ba8c9c00015fc1309f1a71317e27ff05fe1009cb44cf13680219e9240b1f8c17a01bc8b00aec6c9036605f1438761a20084c9afe0b4833242785428ac8606168803c74b07e24c983a400019be194a2983101fb44ac0b6209a9bee7ec851679d1b02000000072380005ef09cc2ac01122bf000079f9b680000af83c0800000019083161476000000000000006e221ee00003362c70dd470300000311b521e99c7a73888920381a3e1e100001040b643298de67620f00727988422b84a809e07c22ad80ee7ee05366f6019c3e71cf46a911b03bd9af21da857c23f06f802a800080a95907ec07fa000205a708166c47f113a000152a460a12a00018f817487d829806626fe1d4669c215e5a205b211d05e432c10f28071b840ee990c0fa13007e91b641e3a130709094448117243dc86240a3a21a3721aa81dc194a20aa2e47111b585218000000000053a000036e8000000000000000001401c8072c80001451f8e00003540001bf41c2000039b00000000e981810dd80fb87d47f99fe402022447a50fac6ff14a400021fc6f5866684384944889c983f503f645a800055e01ca24680000000dd26ae16660000c6a862099039c177465b8ca216608164d0a1825eb930c0a91138269211a11b82a877286ee4dd1c8862e9dde3e4818454e80005d50eac1be878207a8000626816266a8e360001e26255000070183da00004ae05820dc000186c52a881000000007479b3675a0572232939c87f97828b385cc5728db47430f6a11819dc7b49dcc6b511aa3a300002fa141831c0d225af1a820fa8c960a1195c8a5000019a9a3c00014f63bc0cac6710c0e01b1146399989868c09ae1c5842613f89ce5109e4c0000bdc3d315562ed0000732121c45a222a0001b96071043845f92f40bd85bc27804e85fb99ba7a4000071b8e5c14f99305ca936e057819244111d41d19c787b50eb882481542d384782f193e473e00be511894c14a892842183d00000a3672717b41c8032c5a40000785a1c06f6986644d8
  | 38 => 0x85401f29b481ee1cc000000006b72038610881e3820b2e62e1efa3a3800073598fc0001e66000225a00011b88a8812e81311961d98b0e2c0214e000031a403988222912f21a519064ea1a1657e127c32a176c889925073808ba89387060000000000219474c0ffc54d87966a100003f28b7620c07f61e30000000020457001480f00c605649b563278a1e197800036388d471b0ece036835e34616ec2fe1cfc72a185e16b97a8692a26e4801c5600008e800000001cd8000000184600016c213b8000071911800000006a518e63a00fa2549800061e921880503c400018a63e981dc21d9a601a19c8400013c4000183e00004547640dde00000000000000000107e7378bbe1db8000691206a477a05e00016968b721260001c0e000000005998e200004f40931fd27c990ae000189224da1c80b180008b31d5c3e516ee67c800000080004479e3c000166e6b918a002c800000000001f492ea7a99a906c19ac42b905d03b120fa5ae9a0e48d90267ac092a2ca1b043898fc217787aa4ff928886b0d0482e9be04c801a80a3006e5e800007b2059a6d00a025ac9dd00000bce3a5000076f0000351161e000096685f09c676d8000006986060b916060197167fa0b8a0000000646a1ba68b1c7000021f603f20d47c01e8200017220000e7e000000073680005f3a11e22c093e64d0000000000056691ba2140af2000179c1849b8c7488712272151a624099200b9d242568c5000011206940ed80d1891e26980008660ee4650800000022b84ce06a444012067ee97f666d89401e29fc422686881f00e3e62b800048a89f80000a3a1b38f566f0125e60696d088588a8561011c19720986cb07507391ac81ab91422e4139e3a1098a000097c58b8382881977a57209b8286000000001be00012482508a0800000000e00c4476695bc2ca9cbc09b0b2c78ea1a24f580bc0d10802000000000019a47c8085213a85aa12e1b7a20e17e815fa05482814ee0000d2678a0000000000048e813e68c80001e693800da0c084988000000144e000000000003520001eda5d422d61711f3c5828a1c81391d02621d284c48f2020392ca5e21f8837a134e5b58d904b5874c70e966022f0e4404512426930d9a49707f045616ea54f983a6351ce685711dc3dc0f5225c109a7d58f321ae16e202382b06e813f64a5a0442c290663af8a16882105836b229a66a06c042a9b460628c3670118868861d38189809651a0f8c3231a026939f5e4a10cd213109200db0e140e29cbe5031644466112a6ef95341bc077c0bf80ac19910ea7689bbc41e140827e9efc279186e8769ed07ef9f3611419ec1118e8228c944420804765f998b650a0bda3ef167435785746a385ac780043227d88d2176196a1080bc85f21dfe11e838e6f98e0e7451ee0112a2d871611a878380002300f38
  | 39 => 0x57a00000003b51e084c59faa00005c800000005331bb00000e462cf8ac8453913e614089c392159e027080a6989a8a00000000001e5a01706d82bb800004180000dd02dc2571cd80001e1c8a1a134043888a0a080004d513782aa800000000003d1000000000002ab14b25f0200a84d80000000000000000486a909c3db92664090000000000069e94121bca0063d0177845b84c06b00b0614119a201517621908e5a31f1eb85238000017a2d22d300d0000219c096950800000002b6964c00000e80000f608ae8bbc00021f261319f02af80008ba928e6c585f487d10cc3869f3e1f687580b9062e8ad9e5e19802f825a88406580b7800013da88ca01269f8cc24c119bc3c594f22d01a3a02686ec6920cc68990d40000000057911fa62f1ca200012085471386346800000022625f60d4e82c0c1e00000ba00007405198ae086a049031081b82b514b06d29a10504000c76b9cca4f81f2a1e2169a759934a5990ee612a8cec80a1aa643e9c3c7f796e80be9a561af1afc5f8000013f0f2a6148ef40350e10000021e6ac10020000744459811e0001e344e288d00ad80ca09005301888ff84378e8a85b8ea67e102061dc9e0c6e4935e3fd20de1e622363c2000018c000000000002890e585c30d0800c206c2ce85e2767a1b650b1abc014a03e6db174a60d80f40002280000048e0000000422915c21b0ba24a80ace0001470000143c03e8c640ab8ce6000053c00001760c00094664111c29b11ae6501f8257e8a2a4fe9f947fc89020000f2e0539d6c7ed9a8824703b648800007b91e580c70e2a00011e409b88c2317800087e155000017464e8803435d1b7270212e42f91b9a44c9c6670d97d6525800004580002e484d06e6081c19e971000013b44ff0f780001ace3430ffe85511220001dec4699dee0000b3626711f25881996144005826780007988000688000043f108256c8a2024b898007c8000000000040d96c82938e5203c820a0ef14548a996343eb800039c8000681000000020f63138dec45e0000517000083004d61f2226638e9230151098e6ea13cc200215810b80006fd821621f01a23550d1e268958e4f7985a5c69e9e00019e86db83fc5df86100f211cc00008685be80004f621c47129f2c215989405695fe618a1d65191a8656d8a9c5650ab4883091455388424781bc40908c3e00507180c805545d1139a0391eb2615877a09d160601d9e603701e201ad1de06fb0c000f905a063205ec59090a280007c67b608a23f61be26a88fcc3ec908c85e12f019c9278715085a88118e404e85621ac1ac25e599666c8013251480000000e9a5778e6800004827f30fea52702127d91ef85478eae7c190c800019d03c1800000000008a700003228bf600000000da82ec7fa99d2123024a7059fd43661514000013445d9e18677
  | 40 => 0xe0a2c0001e686a6193256011902a3a18a0001b444849b1422d8b4479515c64d694d6000193a1eca09c2748bc24429a800cd00c216717b02a1800036f063c36518ce311a0782a7a02e11f094e01e20d627aa03431b0fda066a27285a8ca486599e21a2810207510647f41f3234b01b617e9e464b3812c6ed15a814816181a411540fb139239aa2a86679db0000000000015a04f0947a432816c000000037d221c049030627080001028d6000009481a6157e7e68000378854600013980001b6a000115a0001c3041819e61a81b8000020ca00000000870000172800083e1f4272b0b187c380000000724000126e00018288a9155e5da99b200016783300cc434000007c714fc64506141b2000072480000001ca622e000050018724a516f000006386d40592000150c0001ffa49693d061e0b7238107b40000ae600000001130000000188c1030e4c38b8000717213e000000056b87ac31c8e1c3649ddc4b7119c0548092188138e43b922834400187b0a22c2d50f4e14220bc44487f80158d461b4125600008a600020ea57a8f9620d041c2e1022019e04e43be86d40000566557182261c168c53380007650588000000083f800043000006ad81d20df80000000c0a85200000000fc04498000000000066b0f8621b956240a931c3df8000595808432e172655a05c285c11ac20b9acc508000000000008af8000471000011aa13800003307de80000000000000037c000000031480000001e320000000000008a000000069997aa0000000000000006b992613d95105c2091284219925e190a668a20a230b87c46f38b3435098b2000000043680000001f9000480001ca0000425800044692d200000000d6863a52114042909cae5cb8f3c439a22489018d27498dea42f0a4088f1f16051000074d14243ee0e42000029425a00004cc862c2d61d0887092b633e81ce77a22b00d4051c0978b0869c8a102e603be00003c2450079e1ea000030a91800001f8646284e67ef15cc6bd968619d000073311a46849d7616e971c3338f543cc13ac0001c3200000000000658707872e41680000000e1e0000f34785001e49100007240dbe89f117081091863540ebc7df8b242681d400000000729109400008125b191a00000fa054b8d9c48282bc824138c19b80000000d8229b8fde18096fe67684e222c97801201d9663f960c42d15d8652000803700003f4931400007ae2c580000001cdc4458a506b699103471b606ac9d5e25f994e00020b88a7870a710947e631831600013400001268000000052a18d60000fc400011ee1ca800021280006ca1f4c2af1e4882a064075f827e50c03f264b85f23b1800033d00007e8029059384de5708000000079200e854e35f852600012c2018800059f80004898f6c4139dc03e6800063b980a000000026e97b862b000
  | 41 => 0x3056616a438d0000605919a720800014194981540028821000026c86501d382383f709601d221622fc929240c00006b792e8699045a71f85c000000004aa93ec222000a00017b2595022a000000000000000000000000020c00010165b100002d580000000000764a0e810500000000a925b78f5030c0594000000044b93ee0ea96980000d3e0000000000000056c0a2e00000001f400b6000137c7dc8000662835c15a02c25518cd057b000085d000041a963234183940b5031e8b514ac0d287a22f400001288a720001e4000020585c512a615ba0502111dda41b9458000171800000003448d34105852884088788b78f5e7a6a10671a90c23ba0c8e41c1f6869500007760e2277080000001c72000105e4dc862a06a80004a6800085c85b8000224c5d7206600aa1ca53017d445e83d20d38aca3710762875199820c93e26878f0477487de1f910a06220f4801089d000021e06560b26000085474d8848000000027c1d8e11f9cd46c993b223680c82c69864676000082180004c180005269b943c5000065d201029a987c23120b64b51a2249d85a430c910868619227d297a4712037a09a0fce1b2962483606f658b18144b78a5e85d95ba4f21a2e85a21d841e963822b00d656f9bd02ae0df83fb168e6c69b5c31e0f66042119e69a93ea6491ea42830a1a7e71b6624011723a91b8618f80644db08c83061b181770846829092400021bc78180000001bb88558ba65181f767bc800032217a60b89f967281b4c70a14f43049bdc85818545cc875489d9ec029681363bf0e0a05c06fc50d83ca7d89a262b89d025f680c62c800d23fd91d265198243950c200e321ea3f18af4697122e1a99ede79c22da81f8cee0ba071e4ae82d60ea06be690029667280de417227039822582d2a05c01193667750eec2e50f12337888240413845ad1c223740a522410a306f2040059e93a6096007467d228277c1c5059a879074f98a210393363281baa59703963770dc24a0928670b0eca4511bc68b4219a0e682a607984b64530d844361c681b890725c80b808af212075a91ea5c1037634502280560ee06651d0a35b8552577192a1609d06008956c23d82ba45217de3ed1ec669d01c2402904c2ea13503121e566fa210c3858d680e8044226102a200022605b314d886c00002e784a600009d6009058089f9aee000006a7b722ca8978e3c00000ce00000004ec1382007022435d864a6c499c227880ae3b206c20c3990e01f888c0001e7c539209468d00002ce000019c067c6b297020bd16e6000196233509c412802705d6a0263cf90d24be800088e84b231b98ca2618262834855602a10be84884623e21ed63769d424148f6465f19fa45781d668521e8291154c4151e6c75389be13615aa06c86ea14b830a15216e47101cc22a912a88841612410218c5c
  | 42 => 0x160256298849e000184800009b67fd0c2415780001079f7c0001f44000000006500003b5950e4bf00000000ce200001c800019fe00000000a28000000070e4a31ef059f000019f997600010000001f4e3801b9c1d8110e756000059a11d66470b0c00000003631b0e612981e7119c265a0804a282909829f0fe07c600320000f8a40c924c4f3924a34f0db25f31c3e78c16aa71d000e51699023fea12c34093888518000254160e7f685d466182b80e61a363490dfc0f59ab412d03706c8800046518000f70f745d300000851df8000000004a0e9e64f02500001522000000008380000000000483942e4071bf00000eb270718dc19504cc0001bca2ab868450a80008400000000000081900004a905ce000000000010d66b8000000000004d321ce35e81903c40e5622a86b22a991da4240c8231f80002951ece7a5928a5dc017a03b1c2a5d797845250e9209c80002b187342da88284b4076877a94ae5e380e20000b862d6817823b89f430e0496227a27a592800027990280300808059197872a890e0d08a7e0000c0629a008211a1d84697a230161914a09e8448092049260c92740000ccc369126c4079bea175800000000003bf8c8420e877453e18d85f4899411c00006bc1c6400013760001cba0eb08e2782800052200007f80e4a26a1c7600000002f28ba400019cc82b8bec000107400000001a480005480000000027c6c4186a000220a74686561560000292a1a000000a00001d62000074a0001dac63b04984ee800014393a02a89fa27c3174260719b03bc9ee802c149058a1d523c61f081c0011838c993e5131658499203c00000001698b7c11780005b51d3a24c09ee0000ad616308940001db205d03120000ade6821ecc1fb023c000007c2f816f849c94b667510224080ee2114857081d0cda16a014c39f14e07ff8826611217e71f20be1858bb621722124728d5c10a0ad20000146362946a6030704233200459c070c000000000009fc39380003aa0000000179823f99ee53f9730255987639000001cc14c857c000064b08646330000000183002622e65cd89ca5fb01da289a0485cb22204351d4444a16b64ce8000143052c40f000067f0fe26e28e7650582985751e1a66d1f5a57d8be6131860c70d00000002164894059e56318de69b208c3a19e506ce8f5886e053850384402d481b4000143a580885e338188a6bd08900d803c642b219e7230e6276d0a287bb106c4b9873e79e1504600903a89191e847982b4345822c46218da12293ca47219f87a70bae0000f628311cec33f970a69d926029e14ec21a929841401403fb940a5ce8ab22578234000118e2f615da2851156388155244400002e38cf264d8f7a15d9c1010888ce57a0bac5fe05ea431043027610dc5d595d64689c623c9881888a000076a1a9a72191f03b4a0
  | 43 => 0x18c2000000000009b000003f013383865dc96306f0963e02899166dd80500001826681974e3200000000037246f177604880060000f9836784ca13c8eb407f0ede81809d477389387dc00004c68000578011a2d70b7e55c9d7a74aa0cc7a619e05aa17124fe1c2e55ba2b46b997f47d00dee0001e6e00000005fa80001c51224332800028894ba2be800063c05da28d0daa23193940001a927fd96ac000000037c2180259018844c1b7c4af880c0001f52000079424b00007f29c5e000218e6be8000505039000000f6000113c5d4868e5e31e3e40e1fdc8839d1c1c89834122027647e048600000001ed8c764789b9050f96a687480000b2a2aa000000008996be0001f3a08d80002f4800056703226a300004e586080001fc219110e2000000000000000000b046eb80000000a90549000000000004c600000000af00000000000000000022a051f1e0489d05fc14086e00d015546de00000ab000000006e46bb18384129f0279c94ea767116c0b106da1b318c47d5000010a80002b40e0200021861c41d6e43380006fe8bea28f16f440199f6000064e1b58da600000008278a0e10f02106dc00005e5031000000004bb996400005346fc9d821fa800000008f40b600006ca9d8a66ba26c29d82081a68c9a0ca000007a16a2000180e7e782de89a144a0fe03d82661eb65b48f0c4b00ea010102be2ea8000000000004a8d4a6f50a4c14780002aea0a648f00001f319725a790c64fc80006df86fe5e400100001d7480614926e980000001a68869144030f0d286b58f4257392f883f0b6c297094647b0a0475583625868e5e47005e007b05c6245818c63010a413b04060001eaa562105600000000000a58000000000000000001eac000000023e1fce06900006ab22784c2154000000000000bee0000fe64381088844033834aa1e4000000033c1d707c501d0343987451b8000000141e6af9b42000000000000007bb990010b1a1c5f094748878f0e48791063d71f240b01fc06be00002cc069c47d1f460000cc805c968a2
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x3633a080000008a8602802ecb499c6804163802b87ac122c144a46200022c004100c3070060b99282dcf649480103e97219435925200613a0973d8f619480184e825cf63182520041ba4a8754d619080106c9261d539824201c172617354e629040184d732095398a410040fa60765d2525040106c9261d53181410040fe61741d3654840144e92e0d73d95210052a249431c1644840184d73209531812100519a4b53dd9210848186482ddb75484210040fa63765d2529000106e92a1d535864001c172617354c625000184d7320953189400040fe61741d1658800184f83209735962000613dcc8254d618800186587597610862000538a5b711c1214800184d732095398b10006135cc8254c628400146597d8a520861000519658521c91004001465962147244010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x4c
  | 6 => 0x4d
  | 7 => 0x4e
  | 8 => 0x124c
  | 9 => 0x94c
  | 10 => 0x94d
  | 11 => 0x94e
  | 12 => 0x124d
  | 13 => 0x124e
  | 14 => 0x138c
  | 15 => 0x138d
  | 16 => 0x138e
  | 17 => 0x8c
  | 18 => 0x8d
  | 19 => 0x8e
  | 20 => 0x128c
  | 21 => 0x150c
  | 22 => 0x98c
  | 23 => 0x98d
  | 24 => 0x98e
  | 25 => 0x128d
  | 26 => 0x128e
  | 27 => 0x150d
  | 28 => 0x150e
  | 29 => 0xa0c
  | 30 => 0xa0e
  | 31 => 0x130c
  | 32 => 0x130e
  | 33 => 0x20c
  | 34 => 0x20d
  | 35 => 0x20e
  | 36 => 0x154c
  | 37 => 0xb0c
  | 38 => 0xb0d
  | 39 => 0xb0e
  | 40 => 0x140c
  | 41 => 0x140d
  | 42 => 0x140e
  | 43 => 0x154d
  | 44 => 0x154e
  | 45 => 0xb8c
  | 46 => 0xb8e
  | 47 => 0x148c
  | 48 => 0x148e
  | 49 => 0xd0c
  | 50 => 0xd0e
  | 51 => 0x160c
  | 52 => 0x160e
  | 53 => 0x164c
  | 54 => 0x164d
  | 55 => 0x94055
  | 56 => 0x94056
  | 57 => 0x95254
  | 58 => 0x94054
  | 59 => 0x8a
  | 60 => 0x128a
  | 61 => 0x155254
  | 62 => 0x154056
  | 63 => 0x154054
  | 64 => 0x164a
  | 65 => 0x44a
  | 66 => 0x164054
  | 67 => 0x5654
  | 68 => 0x124956
  | 69 => 0x124954
  | 70 => 0x164954
  | 71 => 0x95654
  | 72 => 0x12ca
  | 73 => 0x10a
  | 74 => 0x130a
  | 75 => 0x134a
  | 76 => 0x139256
  | 77 => 0x139254
  | 78 => 0x21256
  | 79 => 0x21254
  | 80 => 0x155256
  | 81 => 0x165254
  | 82 => 0x125654
  | 83 => 0x165394
  | 84 => 0x139654
  | 85 => 0x98096
  | 86 => 0x99514
  | 87 => 0x9294
  | 88 => 0x98094
  | 89 => 0x99294
  | 90 => 0x9514
  | 91 => 0x128096
  | 92 => 0x129514
  | 93 => 0x8994
  | 94 => 0x128094
  | 95 => 0x150094
  | 96 => 0x150096
  | 97 => 0x20094
  | 98 => 0x20096
  | 99 => 0xb1514
  | 100 => 0x140094
  | 101 => 0x140096
  | 102 => 0x155514
  | 103 => 0x164094
  | 104 => 0x9654
  | 105 => 0x128994
  | 106 => 0x128996
  | 107 => 0x150996
  | 108 => 0x150994
  | 109 => 0x99554
  | 110 => 0xb0994
  | 111 => 0xb0996
  | 112 => 0x98b14
  | 113 => 0x154994
  | 114 => 0x154996
  | 115 => 0x164994
  | 116 => 0x99654
  | 117 => 0x151296
  | 118 => 0x151294
  | 119 => 0x21294
  | 120 => 0x21296
  | 121 => 0x141294
  | 122 => 0x141296
  | 123 => 0x165294
  | 124 => 0x129654
  | 125 => 0xb1516
  | 126 => 0x155516
  | 127 => 0x165514
  | 128 => 0x151654
  | 129 => 0x130a16
  | 130 => 0x130a14
  | 131 => 0xb8a16
  | 132 => 0xb8a14
  | 133 => 0x44d
  | 134 => 0x164a14
  | 135 => 0xa1654
  | 136 => 0x134d
  | 137 => 0x14d
  | 138 => 0x149316
  | 139 => 0x149314
  | 140 => 0x131494
  | 141 => 0x161316
  | 142 => 0x161314
  | 143 => 0x131614
  | 144 => 0x165314
  | 145 => 0x131654
  | 146 => 0xb0214
  | 147 => 0xb0216
  | 148 => 0xb1554
  | 149 => 0x164214
  | 150 => 0x21654
  | 151 => 0x154b16
  | 152 => 0x154b14
  | 153 => 0x164b14
  | 154 => 0xb1654
  | 155 => 0x155416
  | 156 => 0x155414
  | 157 => 0x165414
  | 158 => 0x141654
  | 159 => 0x165554
  | 160 => 0x155654
  | 161 => 0x160b96
  | 162 => 0x160b94
  | 163 => 0xb9614
  | 164 => 0x164b94
  | 165 => 0xb9654
  | 166 => 0x165494
  | 167 => 0x149654
  | 168 => 0xbcd
  | 169 => 0x160d16
  | 170 => 0x160d14
  | 171 => 0xd1614
  | 172 => 0x164d14
  | 173 => 0xd1654
  | 174 => 0x188e
  | 175 => 0x15cd
  | 176 => 0x165614
  | 177 => 0x161654
  | 178 => 0x40e
  | 179 => 0x1a4a
  | 180 => 0xeca
  | 181 => 0x4954
  | 182 => 0x5514
  | 183 => 0x5554
  | 184 => 0x5854
  | 185 => 0x59d4
  | 186 => 0x4956
  | 187 => 0x5556
  | 188 => 0x56d6
  | 189 => 0xca
  | 190 => 0x14a
  | 191 => 0x94454
  | 192 => 0xc092
  | 193 => 0x10092
  | 194 => 0x44c
  | 195 => 0xecd
  | 196 => 0x1a4d
  | 197 => 0x10e
  | 198 => 0x4955
  | 199 => 0x9296
  | 200 => 0x129516
  | 201 => 0x8996
  | 202 => 0x3cd
  | 203 => 0x98454
  | 204 => 0x40c
  | 205 => 0x99556
  | 206 => 0x128216
  | 207 => 0x1283d6
  | 208 => 0x128454
  | 209 => 0xb02165c
  | 210 => 0x21416
  | 211 => 0xb03d6
  | 212 => 0xb0454
  | 213 => 0x140454
  | 214 => 0x141554
  | 215 => 0x141556
  | 216 => 0x3d295
  | 217 => 0x3cb15
  | 218 => 0xd0454
  | 219 => 0x15d655
  | 220 => 0x15c455
  | 221 => 0xd0414
  | 222 => 0x443d5
  | 223 => 0x1643d5
  | 224 => 0x3d655
  | 225 => 0x99516
  | 226 => 0x83d6
  | 227 => 0xb1556
  | 228 => 0x140216
  | 229 => 0x1543d6
  | 230 => 0xd0416
  | 231 => 0x45655
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1749
  | 6 => 5573
  | 5 => 4470
  | 4 => 30
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 101)*7) 7
  | 7 => packedAt gbK7 (71709+((h/583+packedAt gbK7 (64713+(h % 583)*12) 12) % 2538)*12) 12
  | 6 => packedAt gbK6 (291645+((h/1857+packedAt gbK6 (267504+(h % 1857)*13) 13) % 7356)*14) 14
  | 5 => packedAt gbK5 (283100+((h/1490+packedAt gbK5 (263730+(h % 1490)*13) 13) % 5365)*14) 14
  | 4 => packedAt gbK4 (2160+((h/10+packedAt gbK4 (2100+(h % 10)*6) 6) % 37)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffc03ffffffffffe00ffffffcf878ffc7ff1ff
  | 1 => 0xffffc07e01f01fffff03fffff479f38fa23e3f
  | 2 => 0x1ffff8001ffe03ffffc0f80387e7cf3c3cfcc
  | 3 => 0x1fffffffe00003ffffff0003f807f03fc0ff0
  | 4 => 0x1ffffffffffffc0000000003fff8003fff000
  | 5 => 0xfe00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa200058ac254284a004510aa818285340cd0d5
  | 1 => 0x54d2c05410a11694d902ad5514393289a2262a
  | 2 => 0x11656a80213b42276aa80e01a85c58d2c34b4c
  | 3 => 0x61b9b36774020439b4f3c0063e806f03740db0
  | 4 => 0x81fe3c79b9cf9f00382084183f6f8003fbb000
  | 5 => 0xf8302041c00c1801c0c308603ff7ffec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37375
namespace PEqualNP.Outside.L_meta_37375
open PEqualNP.Outside.L_meta_37375.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 6 := bs1_3_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 1 := bs2_2_0
theorem alls2 : ∀ k ≤ 2, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 14 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_128 : Interval s3Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_160 : Interval s3Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_192 : Interval s3Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_224 : Interval s3Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 227 := (concat (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 bs3_3_96)) (concat (concat bs3_3_128 bs3_3_160) (concat bs3_3_192 bs3_3_224)))
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
theorem bs3_4_96 : Interval s3Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_128 : Interval s3Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_544 : Interval s3Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_608 : Interval s3Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_640 : Interval s3Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_704 : Interval s3Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_736 : Interval s3Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_800 : Interval s3Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_832 : Interval s3Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_896 : Interval s3Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_928 : Interval s3Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_960 : Interval s3Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_992 : Interval s3Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1024 : Interval s3Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1056 : Interval s3Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1088 : Interval s3Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1120 : Interval s3Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1152 : Interval s3Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1184 : Interval s3Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1216 : Interval s3Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1248 : Interval s3Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1280 : Interval s3Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1312 : Interval s3Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 bs3_4_192) (concat bs3_4_224 (concat bs3_4_256 bs3_4_288)))) (concat (concat (concat bs3_4_320 bs3_4_352) (concat bs3_4_384 (concat bs3_4_416 bs3_4_448))) (concat (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)) (concat bs3_4_576 (concat bs3_4_608 bs3_4_640))))) (concat (concat (concat (concat bs3_4_672 bs3_4_704) (concat bs3_4_736 (concat bs3_4_768 bs3_4_800))) (concat (concat bs3_4_832 bs3_4_864) (concat bs3_4_896 (concat bs3_4_928 bs3_4_960)))) (concat (concat (concat bs3_4_992 bs3_4_1024) (concat bs3_4_1056 (concat bs3_4_1088 bs3_4_1120))) (concat (concat bs3_4_1152 (concat bs3_4_1184 bs3_4_1216)) (concat bs3_4_1248 (concat bs3_4_1280 bs3_4_1312))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_704 : Interval s3Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_736 : Interval s3Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_800 : Interval s3Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_832 : Interval s3Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_864 : Interval s3Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 890 := (concat (concat (concat (concat bs3_5_0 (concat bs3_5_32 bs3_5_64)) (concat (concat bs3_5_96 bs3_5_128) (concat bs3_5_160 bs3_5_192))) (concat (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)) (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 bs3_5_416)))) (concat (concat (concat bs3_5_448 (concat bs3_5_480 bs3_5_512)) (concat (concat bs3_5_544 bs3_5_576) (concat bs3_5_608 bs3_5_640))) (concat (concat bs3_5_672 (concat bs3_5_704 bs3_5_736)) (concat (concat bs3_5_768 bs3_5_800) (concat bs3_5_832 bs3_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 60 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_160 : Interval s4Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 165 := (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 50 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 56 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_768 : Interval s5Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 781 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352)))) (concat (concat (concat bs5_4_384 (concat bs5_4_416 bs5_4_448)) (concat bs5_4_480 (concat bs5_4_512 bs5_4_544))) (concat (concat bs5_4_576 (concat bs5_4_608 bs5_4_640)) (concat (concat bs5_4_672 bs5_4_704) (concat bs5_4_736 bs5_4_768)))))
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
theorem bs5_5_800 : Interval s5Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 801 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat bs5_5_96 (concat bs5_5_128 bs5_5_160))) (concat (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)) (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 bs5_5_384)))) (concat (concat (concat bs5_5_416 (concat bs5_5_448 bs5_5_480)) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576))) (concat (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)) (concat (concat bs5_5_704 bs5_5_736) (concat bs5_5_768 bs5_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_4_0 : Interval gbAtlas 4 0 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 30 := bgb_4_0
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
theorem bgb_5_4448 : Interval gbAtlas 5 4448 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4470 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))))) (concat (concat (concat (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344))) (concat (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))))) (concat (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208))))))) (concat (concat (concat (concat (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 bgb_5_2336)) (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 bgb_5_2464))) (concat (concat (concat bgb_5_2496 bgb_5_2528) (concat bgb_5_2560 bgb_5_2592)) (concat (concat bgb_5_2624 bgb_5_2656) (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752))))) (concat (concat (concat (concat bgb_5_2784 bgb_5_2816) (concat bgb_5_2848 bgb_5_2880)) (concat (concat bgb_5_2912 bgb_5_2944) (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)))) (concat (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168)) (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 (concat bgb_5_3296 bgb_5_3328)))))) (concat (concat (concat (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456)) (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584))) (concat (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 bgb_5_3712)) (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 (concat bgb_5_3840 bgb_5_3872))))) (concat (concat (concat (concat bgb_5_3904 bgb_5_3936) (concat bgb_5_3968 bgb_5_4000)) (concat (concat bgb_5_4032 bgb_5_4064) (concat bgb_5_4096 (concat bgb_5_4128 bgb_5_4160)))) (concat (concat (concat bgb_5_4192 bgb_5_4224) (concat bgb_5_4256 bgb_5_4288)) (concat (concat bgb_5_4320 bgb_5_4352) (concat bgb_5_4384 (concat bgb_5_4416 bgb_5_4448))))))))
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
theorem bgb_6_5568 : Interval gbAtlas 6 5568 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5573 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)))) (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152))) (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)))))) (concat (concat (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696)))) (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))))) (concat (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))) (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)))) (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))))))) (concat (concat (concat (concat (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912))) (concat (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008)) (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)))) (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264))) (concat (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360)) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456))))) (concat (concat (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616))) (concat (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712)) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)))) (concat (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968))) (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)))))) (concat (concat (concat (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320))) (concat (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)))) (concat (concat (concat bgb_6_4544 bgb_6_4576) (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672))) (concat (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)) (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864))))) (concat (concat (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024))) (concat (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120)) (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)))) (concat (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376))) (concat (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472)) (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568))))))))
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
theorem bgb_7_1728 : Interval gbAtlas 7 1728 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1749 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608))) (concat (concat bgb_7_640 (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 bgb_7_832))))) (concat (concat (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 bgb_7_1056))) (concat (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)))) (concat (concat (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376)) (concat (concat bgb_7_1408 bgb_7_1440) (concat bgb_7_1472 bgb_7_1504))) (concat (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)) (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 38, 54),(inputs.getD 5 zero, 22, 54)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 3 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888eae8e8a8eaa8e888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941132456 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37375.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,4]⟩,⟨.or,[3,6]⟩,⟨.and,[4,7]⟩,⟨.or,[3,5]⟩,⟨.and,[1,7]⟩,⟨.and,[2,9]⟩,⟨.or,[8,11]⟩,⟨.or,[1,12]⟩,⟨.and,[10,11]⟩,⟨.or,[0,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132456 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132456 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37375

open PEqualNP.Outside.L_meta_37375 in
theorem PEqualNP.Outside.L_meta_37375 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132456 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132456 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
