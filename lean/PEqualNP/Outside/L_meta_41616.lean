import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_41616.Model
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


end PEqualNP.Outside.L_meta_41616.Model

namespace PEqualNP.Outside.L_meta_41616
open PEqualNP.Outside.L_meta_41616.Model
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

def SBf (j : Nat) : Nat := [8, 5, 8, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_41616

namespace PEqualNP.Outside.L_meta_41616
open PEqualNP.Outside.L_meta_41616.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x8300568b0040c00080171011020451803072c0016fc41fd42fc32fd10ff43fd32fc10fe32fe10fd41bf41fc31fe31bc40fc21fc30ff42ff31fe40fe30fd21fe21fe20ff10fe41fc42fd20fd43bd41ff41ff32ff40ff20fe43be40fd31fc20ff30fc43fc40fe42fd30fd40ff21
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x283bf54443be8721df55320dfa10817c504c678a898770c430dfa0e417e54082faa7a0efd5132de206417751483be64195714d10de21a83bf429037a85205f94432bf2a2417f544c2faa890efd0740bf2a0615e53886fea998df94230bf29083bf4390ed8a4985f55021bf2a665f4318427ca820ef90320bf2a441b751506faa5105f54041dfa0081bd50506fea790dfd4d42bf29021f451482fca1207bd0b32bea92217e53902faa1995f94641de2a241bf409037e82887d90441b6292217d53483ec6218df55220de988817e50883be61185f94232f721085dc430cb7ea2a0df55240df282837e50102faa1a0fbd4930ef188617c540837ca1a0efcca40be29a43bc408837a63206f50840bea9885bc421037843205fd5132f799441bc52506faa421ef10f41be2a441df438cafaa4205f14e10bf2a0637f5050ef8a2a1ddd4530bf296217d50d0f7c81105f55032bfa8a417d53902fea910778ca30bfa9281bc31902f8a0a0df946429eaa483bd43102faa2196f50e40bea96815c5348378a2206f94440df21881bd410427ca910cfd5110b7290217f54886fea2986fd0941bf296613d54042fca3a16f95031bf28861df300c2faa3986f50731df20661ec42ccaf8a5086f55231be2a663bd51102fca3205f94341df20a837e508c7bc60985f14143fd982617f5250fda84215f15221fba0a83bd54042f8a8987bd0832bea9061bd54886f8a9985fd4f20aea9c43dd4310fd843104fd5210bfa9a417d54442faa190df94a10bea9c41bc535077e82087b48720fa880217d529039a6419778c830de20461bd321037ca4205f94b40de21c857f54c837881985f54831b629287bf41cc7e843085fd4c21bf29e81bd32902fca7a15fd5030be290217e54cc7ee21085f94242bf29c857d520427aa9985f94e21bfaa661df430ca7ca9886f50720be29a217d52cc77e8320cf55031f790e417d54ccbb865186f90b41bea8c217e50c87ba60184f54640bea96613d54c437e64205fd5021bf2a4437d5190efaa920dfd5310deaa043bf42d07f640907bcc932bf29c417f54442fca4887d48421bfa92637c54ccbbc63186f50620dea0a63bc40c43ee8320ef10a40bf286877e518cbf680a05f948309e2a265be531037842205f94e43dea1283fb4090378a9087b94810bf29e837e51cc2fca6905f55010bea8e417d53c42faa3a1df15030de20261be21903e8a2985fd5210fb90c217d53d0bbc8621ef50431bea9a43bf53902faa998ef90310df194817e538437aa620770c830dfaa241bf414c6fea2997d88421be28285bd43507d865106fd5130fb90c43f731042faa620df95041bf29085ec5250ff621084f95021bf294877d5110afca6885f94f20be2a065bd418c7f440106f15130fc880217e52902fca3186f90130df29683bd4310efca9887b54a31
  | 1 => 0xe53887d86590ef50440df29c817e51c82fea2a0774c730df2a6217e544437aa9986f0c941bf28043bd52103f280205f95210efa9a41df314c2f8a9185fd4a10dfa0a437e5310efca2105f54632dfa90817e50cc77aa9885f14940bea9e417f524437ca6a0df95330fb98c63bf4210b7a83185f95131dfa9481bd41887de64105f54440beaa4637e530c37a8290efd0610bea9a215c5350afca3105bd4930dfaa4217c54c42faa021dfd5321de28683ec32486fca418efd0721bf29881dd53042fca690dfd4c109faa2417d530877ca3204f14141bf29483ec21083ec20885754c10fa98863de324c6f8a710ef0cb41bf28887bf50506faa7217e90040dfa1a83fb1044374a0206fd0630f7a14857f504c6bea6884f15110fd180617d548877887205f14f20bfa9a837d509077e8318ef90d43ef98c63bf51902faa221efd0c43bf29865f710042f8a918cf950319eaa0656d528c7e842085f94c10bf28e816f5250f7ca810df14c21fba8a417e51887ba62986f14b41bea80857f53882fca7886f50520bfaa241bf43d077880885f94342beaa421dc5350b7e82186f54e40f7a9221bc53902f8a4985f94832bea8e65dd53886fca2086f10c40dfa0c437d53083de42905f15121dea0a817e5290b7a82187b88521bf29663fb208837aa5205f95232dfa0c81bf43d0b7a8220ef50420bfa9c213e54c837c80885f15021bea84857d5290f7e62205f14910bea9881bd4210b7a83205f94643bea90837f52c43bc649957d4d42bea8043dc5344378a6205fd5232be28a817f52507b86498df54e30ef18a63be42902fca6215f948409e2a421f920082faa3104f94341f6190417d52c42fea890df94c21dfa98817f548c2fea918df15110f7a1285ed21482faa5a1ef14141dea1683f731843d8a4884f55320bf28e877d5090fee42085fd4543df21885be311037e8220df54430bf29043bf411037e82105f94010bf28885bf415037e829077cca32bf2a243be540cafaa3184f95231df294816e528c77aa5a0dfd4142be296217d51d0ae8a2985f54642de218857c5350bea8220df15131bf29c83bf52d067ca8196f543419eaa043dd320cb7aa6a0ef505109f284817c5150af8a2985f55321bf294653f544c37aa3205bd4910bf298837d54082fca1997b88420df21081bc40043dea4a1df54c10ee18c61be42507b8a6905fd4810bfaa0217d52887de41105fd5032df20881be53d06fca218dfd5020be2a643be40042f8a29977d0d439f28081be54cc2fca8995f94041deaa641be54c82fca210df54e41bfa9a217e548c67ea8995f94f21bf2a6417c54842faa790df55230df21c81be41902fca01857d4d20dea9283be321037862205f95043be2a465df5350bf420086fd0d42be29287bc53d06faa5a0dfd4121f6900417c504cb7a83a06fcc640bfa8
  | 2 => 0x28086200a200040c8bc0a0b0010cf059a00b008088580284a010360a004f10000006f04018000100185408000348000006430824058000080a1c80002808020b086856018020000c000128c966040603000002002150060086e000020b814000a01f800598000406a0011c009ce0314a0b010748000a0340587a0a01a2b8780c8221c864010020990400004688000c00e0680c04016030007f0120a00009026100860287c078443602c051fa01010040004d00a1181cbe8181304c20014018a000800000080000445026018fe00000c985a26824050000482a37800098185995202808560360b0001b060438001f810710021100e028160600613806960023104003b461981409828110120180a0200e038040116a108000081a020081491c0089a55972000073b000170000400a1261426020090020102e7a03c05840141d603818009f60001c038000bfbcca32bf294617f524c2faa818df55131dfa0c417d544c2e8a2906f95010dea1e837d51902fca1087dc8521de19081be43506fca5a1df55310dfa1485be52507dca518df54e32dfa08633c54482faa8995fd5031fd98461bc40843be6218fb4c832dfa86837e5210efea0996fd4d41df90881be40842fea6a05fd4e21de992837d53887dc43105f145209eaa463bf2190378a4205f54a109f2a0217e511077aa818ef0ca40df2a463ef20082fea690df54342de212837d54cc37e87205f54420bea8e817e52082f8a498df54031dea0e61dc438cb7aa7a0df54331bf2a0857e530c7d8a4985f14c10df21e837c544cafaa520ef48440df196833d51102f8a6a0df95230df992837d53842f8a6906f88440df21285bd21903de6590df94032df18c81bf52506fca810efccb41be29e43bf53d07eea298774c431dfa8881bd32d077c81185f15031be29a81ee20482bca6085f14e20f799243bf43102faa110ef14640dea08437f53c4378a5205f55030bf2a0657d54482daa4087794c10f6a90217e54102f8a090fbc8421df192837d53d037c80186f50710df2a4437e51102fca6106f55032bf2a6437e5010af8a9905f94b41de2a265df31cc2f8a8907b10832de2a221bf41cc2faa118df14941bf280877e509077a87a15f54e31f7190657e500c6fea6106f90020fa188217c53082faa1195f95010de20061bd414c3da4210df94a31bea8065be4390bee6298df55232beaa4857f544c77880106f10440bea94617e50082f8a7885f95130df20241df53443bc6598df54a319eaa443bf41086fca121ef10b41bf284437e518c77880905fd5332bf28e65bf41c437883207e4c030df20281bd401027ca9986fd0530df28081bd418437a86a15f55243f790c437c54042fea2a1770cb31dea0e43d
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4321023e6494c30cd146404823c6454c208f59741c826d6214c108f19153442b661cc941d9d48514c25d6510c328fd9150c863f654c9418fd91500865c6354021c794f418866e6215030c7d4c404823f64540318f585540426c62551308f982548c6b56194d41abd8943d066f6254031ad584400427965840108f592518c2b860507208f587544c23e64951308fd8554cc23d6414b109758c540427b6055131a718d521032d52900108fd9150cc67b65480209718d528438e544c8328f592510863d6494d208f994211032d5494810d914a104423d6590440c7d4d414431c53d05108f994544431d53d0410cd147414c25d63d5220aed8153506ac6254c40cd545211032c5210130b998732486ba60d4440d394e520425e63150109b58b530429d6388640a7d8d525069d63146409b98b548c66d62150308fd91508863d64d4121ab58851102af6254f419dd85544c25f6355121cbd4a404426e62949109758e544432d5210b41c714c404823c64542328f590530863d6595021ab58b539031f53505209b189538432c5250510b358e320caac6254f419798c548878d320c9419718d54442ce63884208f992544425e65cc5309b98b548c23e64145308fd91508cab8605073097d95320ca5c6355120cb949418c71d5454c10ad586400423e6414c209b988530434e5354810cb54b410432f5414910b3991320ca7661153329dd95210865c6354910ab189439029f63508408fd9741cc2ae628c440cd951411073751101309b98a544c26d62d5231cbd48404c34d5394810ad58752d074d530cb21cd945410823f645483097994534423d64145309758e51c833464d4530ad587325072f52d0510ae181410825f6354840d3548320c23e650ca40a7191320cb1f5414d20c754f418863e6095031cb149425066e6295110c7153534823d6414c109e58053086b6618c9418f594400425e63153219718d54486ad62d43418f19152cc71f54d4d20aed8131102b86050430a798c519031f54d4d10cb150524436552c84109b988548c63d6494e208f99253442ba60148408f992528423f6550040a7d8d505063f6550c438f994325073764d45308fd9152442cc624c0308f181540863f65d0720cd193514823d64d48108f19150ccb2d5454810e34c8329023c64542319799453482cf654c8328f994544c26d6215331b9185200823d64948209b98b540431c54d4d109798e524434f53149109758f520429c6354141c715053482776550441c754c53d063e6015110a718d429023d65d04218f992518c33a60d52109798e51c83366414520a718d4210aae62d4e408fd91500ca3e6494720cdd53514c2ae6214f41d5185530434c5388120cdd44404823d6494a308f596540c65c63548408f994219034f43149439e980530863c6454032a798f50d06ba60d4640
  | 1 => 0x25d63d4b10e3d0f420ca6f654c832a798c511023f6155032c7150534423d6414520e3191320ca5f654c4318f592530c2b56114b41d5146304c25d6394421cd990514c26f6255130d5d4f514823c65d05308f594219023c654ca409b58a544425e63d5220a758c511027561d4f20c754c531025d63d5010ab988531032f52505108f195321031c53d05208fd95410867b654c0308f992510865e6314810c7551538863d6494e10cb548521033751d05309b994524423c65d0520cb552528c63e6414d21aed81525063d6494720cb94b418c74f530ca209b58b548c32c52d05309d185534823d650c640d514f51483375190120d5147314c32f54d4910cbd4b414c33561d52108f997414423f654cb418f982540866f65484219758c540823e6494910ab191320ca5d6394910ad586408423e64944308f590538869f6354b418fd91508c6766114c20cd547411023e60d5132cb949429025f63540219d986544823d61151308f990540863c601511097d8d524436451c85209b98854cc73751505408f997414c26e62d4c10ab189435063e650c6409798e544432d5210840ab58851902766115030ab58a319023e6414f108fd95329033754145308f994311032c54cc9329d58454cca3d6494a108f593504caba60d4a408f592518833751d05209d98753c832c54d4910e34c8321023d6494420abd89505063d6195320cd54741d031f53101108f59251cc23d61d51208f5964310a3d6115132c794e400423e6494632ab588531023e64d4f209798f548865e63d50109b988540423d6494910cbd4a529026d6588420cb94a40043355188440c754c535063e65d05408fd91534826c6254031d3d4f524423e6550530ae181535066c6254d10cb148404423d65084409b98a534431c53d0d429d185500ca9c6354b41ce982501023c64542219b594420cb2d54d0832b318d200823d6414f20cd146404c2b5619494197596310c23e64944319758c520426f6254d108f994544826f62551108f996404423e6414c10ab18943d0aaf6250e408f993520427b6054d21a798e219032d5454a319bd89544c735514c4408f993504c63c64540218f992544823d61953308f59053c863d64d4c21d5d4c514832d52d0631abd89535066d6215231ae9835310354514c530a7d8d521025e63d4810cd147414823e64d4132ec10110042ba6014640c754e400431c53901109bd8953102746155120a758c52d063d658c640cb94b410428c644c832ae181414423f65507208fd95410423d6195032c7553430ca3d6414f108f990540ca3c6550520ae181311023c6454e10c794f410427b65500409b58a51cc2d46344010a798f529023e641501097d954310e3d6414810c7952538875453145208f99251cc31d5494c10d9148514c27461551308fd9152cc69c63549418f59
  | 2 => 0x6454e10b918910042b561d4f419d986544c25d63951209ed95100431f53901109798e534423d64d4f10cd14440482ba6014e409758c54c863d650ca40b318d4210a3f61550108f592510c63e64145329dd85524429f6350a40cdd45414823e650c840cd545419023d65d0410c754c43d074e52cc6319758f548871e5454e21cb14a404c23f6454c208f191500c78d544c8329798c540823c6454331d914b514c31d5350621b358c420ca3f61553208f994544ca3d64d4b109d984540823e6590130cd590514c23e64d4e209798f52c432d5210010e9505210872e5494810c7952530429c6350b41ab98b50d063d6595032cb549418c63e6494620b398e218823c6454f219b99732486756115232a758f50d072e5250410cb54852d065c6354b41b3588430ca6d62d5010c794d410425f654c030c7d4e539023d6595010c794d418878d320cb41cb14b414434c53c8520a758e211023c6454830cbd50524c26c6254f419b58b53c423f65504419d986534826d6294d108f992510caac6250c43ab988519026c6255131ce980548427561951309dd85500cb1e5454c10cbd53524c2b860549419798c530426e62148108f592510423e6414f218f994404825f63551208f59640042ad6214f41cd150514833754145208f990520425d63152218fd9541cc36451881209d584540c27761551208f99621902786055121c7d4f414426f6548020a758c521032e5494a318f997414823f654c840c718d540ca5e6394421c754c43102756115020ecd0510042af6250d418fd954210a77654c431cdd93514826f62551329b98a51cc31c5350510c7d4e404831d5494e218f584544823c6055032e3d91320ca3e6414520e5505310c63e6494732cbd4a404c25d6594c108f590530831c5350d42ab98851102756195120d3149314c23e6494a308f191524429f6350b419d586534831d53504108f191534873551504208f98254886ce628c531b398e21486786055131b5185300c2ae628c6408f59353c826f65508428f996211026c6255110b3181320cb1c548c9328f992544cb1c5390942cb548525063e6494e20d514e104431c53901208fd91534866f6254f418f982540ca3d64d41318f59353887356115210d354832cc6af6254c40cd145414834f654c832cd145414c32e54548108f990530873454145309d59431043355150430c7d50534438c43108329d59421042ac6254141ae983418433751901309d584530832e5454a31d9d4b514c34e53c86218f592534423c6055031ab189431023d65507308f59541c823d61d51329b59652042b76154941a718d421023d64149318f996404835553cc4108f996311023c6550510d314c524423e658c640c7d4f414823d650c94197d8d528436451485208f993504872d5250410ad584408425e6395120aed81211
  | 3 => 0x8113c013cc0400401040f10240b000228d80b1f0010140016801078020345a0000a004040000a064960f0031540b0e439030050c404118060ac7f00c4905c1c2a005091590000607c9c0080806d680000900870028001844401c05088080043a0486000041114211c400050020380a00027168010310f054090200e0cc0317c2401c010040c25c0c000053448f08c01000f51ec0001802148003983c0104a0009302c0b028080f0020000d00400114aa00c5b0cc001b0cc098020380c1440a02c000100200c0002000000270145601c0002801010000181300003000001f400000180980009c020b41f044000586d000ba3cc001bd980400023c0007c030180200005484980102a3141835810070960400009000868360381309c2c0000802400000001781a06c09001610d402080000280604c240400766c130110b19c3c13811000010073451101308f59251cca3f6454332b31894310f365150430cbd49414c23e6510130ab189535066c6254c40ad98452102b86050610b398a310c23c654cb418f990524c6ad628c440ae983414432e43149438f994404423d658c4408f992534823e6550520d354c324865e6394d208f9974350ab561148409d984548ca3f6454a10a798c52d063d65d0431c714d435063e64d4c218f99432d073751505308f19153482b66114c40d354c320834d53548109dd85534823f65100109bd8953482b5618c9418f99353c431e5310010cb153524c31c5350520cdd53514829e63148408f195414c2ac6250f41b3d85320ca3e6414e218fd95410c7356414520cb948400423d64145329b99721482b56114c409b58854042776154d10cb149414c32c54149308fd96400433454d45309b594320826e62d4c21ae980511029f635094197d8d544caba6014a40ad58453d07646154810ae181211023e60151328f99352c423d6494632a758f529027765440108f592510cb4c53d49108f596219034c5348520abd89431023c654c941add85535073454d45208f992538429e63884409e181534869c63509418f593538823e64150318f181548c6cc644c8328f993538863f6454f218f594311023c6454321cb189540caba60d4840d314a304c23d64d4c108f99052c434c53d09428f181548863e64d4c108f590534865f6354b418f596211023e6494420cbd48404423d64944308f191528423d650cb41c754c400423e6414f20c714c404426e62d4f109ed81544863f6454d10b5986324c72c5290110d314b314c335518c4408f59741cc26d6295130c794d43902ac6250d42b398a318c25f63551108f992510426f6254e108f99252082ba6014c40ae983539023f
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x8002d0060014c63c20003450ac1404001800c760601201da18e6a90a5a0d0c74548320c2873a6a6194418a1486050510a1eea990652060d5358853d070c298c0a0a21239c0644c832a1ce7a94a52048e74991320cb06a9ac429881431d5320cb41a18e4a98a7a0e0c53189435068c382a629a838c5446050420d20c6202200850c73548421030631ca4a14818358d5214b41c2aa6b08a62050c7454c32486463b4a899065895496110010a18ea99064a0e1563546211035031080880218358d5214840a18e8a906598d0c7254c531028639aa4290818554d6110010c4ac4a8c622050e72d4e539021ab88ca99081431cd5210b41c1ca63128720528705485250706b2a6419081895496114840c18c6312a819631619835484306318a4a1283431c95310f41a18e8a9864105487054c324868639aa429283431c95314d41918ecaa2641948d71191320ca863a2a6196438c5446050430a18ea990642050c7254c431021c382ca1928383595320cb41
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x2040000a048254d6114c40905811d5320c84080c87595320cb41a04835496114840885811da544c83280c87595320c840
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 6 => 2*((h/28+packedAt s0K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/267+packedAt s0K5 (21627+(h % 267)*10) 10) % 801)
  | 4 => 2*((h/260+packedAt s0K4 (29678+(h % 260)*10) 10) % 781)
  | 3 => 2*((h/32+packedAt s0K3 (2744+(h % 32)*6) 6) % 56)
  | 2 => 2*((h/9+packedAt s0K2 (360+(h % 9)*3) 3) % 6)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81ffffffe07ffffffff81ffffc7ff1ff
  | 2 => 0xf81ffffe07ffffff81f07c1fffe1ffffa23e3f
  | 3 => 0xffe03ffff80fe0fffe007fe0fffe1e03c3cfcc
  | 4 => 0x3ffffff000ffffff8000ffffe003fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x882808c4122400016509421280222a80cd0d5
  | 2 => 0x924519103244986580a4291a53215551a2262a
  | 3 => 0x2149aa2490e909aaaa084f489d54181ac34b4c
  | 4 => 0x859634492481d2d34d3d0210e6998063740db0
  | 5 => 0xc6183871c70e1cfc71ce739c07111183fbb000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0fcccccc0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_41616
namespace PEqualNP.Outside.L_meta_41616
open PEqualNP.Outside.L_meta_41616.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xcc32
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | 3 => packedAt s1K3 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffc0fffffc0ffffffffff80ffff1ffe3f
  | 2 => 0xe07f01ffffffffff0781e07c0fffffffe493ff
  | 3 => 0xff8001fff03f03fff801ff800fff07c0f8e3cc
  | 4 => 0x1ffffc003fffffe00000ffff800ff03f0
  | 5 => 0xfffffe00000003fffffffffff0000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x220a100460821040188a228462884a4a092615
  | 2 => 0x491462c88514c18b0320c868853194b46490ea
  | 3 => 0x8526b55123a856d568497b2129da4706b8e34c
  | 4 => 0x1658d9a24a0e9b66b5ec12424e6ce218df03b0
  | 5 => 0x1860e1c38c30e3b8c6719c7380708420f6d800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_41616
namespace PEqualNP.Outside.L_meta_41616
open PEqualNP.Outside.L_meta_41616.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x20008100200000001000000001f2000020e300010000800404000010000000005000000c0001c0101002fe42fc31fe20fd21fe21ff20fc43ff32fd43dc31fd41ff31fd31ee21fc30ff43fd42fc42ff41fe41fc41fd20fe31fd40ff40fc10fc21ff21fd10fe30de31fc32fe10fc20ec21ff30fe40fd32fe32ff42fe43fc40ff10fd30
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x465de438c7f680a07bd4c21be29a837d518c2faa9105f14d20bea8c217c54c87bca6106fd0842f729c437d5010efaa7205f55121f610861ee21102fea610f78c630fa880217e51ccad8a4a0df94640bea9a437d50d0bcca210f70c430efaa463df438c7ea4210f70c440b728c437e53c86faa3907bd0621bf2a661ee210c3bc630877ccb30bfaa061ef41087b863205f95131b7290617e518cafca8217bd4941be2a041dc328c6faa2195f54232e618c437d544c2f8a0995f94d20efa0863de53842fca7a0f754f21fb082217d52cc6faa510f70c521afa9a83b940102fca3215b14910bea80857c544c2fca2105f94c42ef21a657f524c7a86210df54231eea9841de418c6f0a0a0df55243df208817c504c6fca3105f95210dfa0c83bd4210abaa6205f54343f610a217d5290fd8a4885f15132f6a9421ee52cc6fca5207710431ee990657d540c7bca6215f54e30ef994657f53886fca5a0f74ca31beaa2215e518c6f8a498fb88510bea9e81ee52842dca210df54841be292817e548c3de8410df14e10ef18a41dc31442fca6195794c40fd200817f53c82b8a690f90c421bea94633f54443dea710fb48421f7a1443ec21902faa92177d0831be28285dd418c6fca3a15f14532f6a90817d5390bee6318efd5110f6a1843fa200837a8220df54c41eea1863ed20082faa7a0fbd5221bfa9a417c54cc6f8a0a1df94020fba0c83ee52103be6318fb50e21f710a43dc53487eca2207ecc230fc98061ee21903bc62105f94841be2a443ec214c3ba8418df54a41f6a10437d51d0ebaa708770c530ee290636d52103da85905f94743af29841be41903da641957d4d10bea9c63fb50507da85197b10421f710a617d54042eca220778c440fb20a21be4350efaa610f7d4d10bfa9021ef32086fca9107b4c621bf280837d544cafca721fdd0541f699241df4350ef8a710fb10621be2a463fa10043da8510fbcca21ef990637e5210fbc87997b08620bea84856e52102baa6105fd4e20bf2a061de304c3de41107ec4210beaa4437c52842bca218fb54b31ee18c417e500c6fea090dfd4141bea8885ed52d07dc43107714d41bfaa661ed4210bea6218fb55221bf288657c53086f8a9997b4c4219e2a2217e50887d88610df55231bf2a2215d5310afea098df14d10b729663de310c3d8a910dfd5021efa14637d50106dea4a0f74c431bfaa0637e54103bc86985fd4142faa0a217c548caf8a810f7cc832bf2a665bc54442fca9885f54440bf29c857e520cafca4217754231efa0c637c53c86fca890efd0c43bfa9821ce31087b86390db54b41bfa96217f52503daa010df54032be298217f51482bea690f78c530bda82837f5150bec8220f710c31bea94817d50087d88710fb90a21bf2a4637e52906f8a2a15f94910ef294637c52507d8a610df55230
  | 1 => 0xd54c42fea998fb88540bf29487f940103b862a05b54843be29a437e52102fca610dfd5010ee21063ec42886f8a4085f94430be2a4617e50086faa4887b50932f7992657d53c86fca3985f94d21af29885fb10442f8a2905f14e20eea90637e54cc6faa5a1df94c43bf28087bc41902fca9195f94010ef21e617f548c7da8310f754f41beaa6617f54ccafaa5106fd0240bf280857d54483d86210df54730ef192657f525077e80205f95130fd98261de548c6faa3207d90710f7218437e50d0bea83885f94a30bea86437e50cc6fea6885f54e10ea18e43ed53886e8a2995f54c20ef18e81ec31887bc8518fbd0c21f72a443ec218c3d8a010df94242bf28463f910042baa7a0dbd4931fd904417c54c42fca990df54b41f6aa043dc318c3ba86985fd4930bfaa2217f54487dc84907b88630beaa263dc31482fca7a05f94c20fd180617d54cc7886210df94441aea9e43dc508c6fea2a1df94720efa18637f54c86daa598ef50040beaa6437e51103d843085f94c40ee996617e54482faa198fb94b41f7a1c437e528cbf240105f14b10bf28441cd320cbba87995f54b40f710c21dc31842fca608778c730ef18843bd4310fee6390fb14941b6292637d54906fca218f790c31ef298817c54882faa418df94e40bfa9a437e500cafea4887dcc421beaa465dc320c7bc6390dfd5131ef980617c540c3be64985b94843bf28c617d53c83be8721f78c710f719241ef50086faa018fb90421bea9c657d53042f8a2986fd0a42f7280436e52d06f8a898fb90621efa9a837e540c6fca4087b8c832dfa1c87ec32087bc8218df54241bf29e415c53443de84a1778ca31bea96617e530c6fca810df94740eea9c21dd4310fd84290778c410bea9e85ed41086f8a9905f94343be2a063ee5210efaa8195f54a10f6a9087ee43887d86510df94a10ee29a217d51882f8a7905f15330bfa9a81de31886f8a888778c720bfa94217f5250fdc42907754c40fc28283df508c6fea6a17710a31bfaa443ec524c7bc62a07795031eea08637e50c86fca321fd54440df21285dd500c6faa6217b08420fda0621ef31887de852177cc431bea9e2177514cafca7a1730c421ee990637e53887de6210f754c42bea90217e508c3dca810fdd4532bf2a6417d53442eaa220770c420bf29c217e5110bdc42107794f21be29a857e52d03de40105f54443eeaa063ed32086faa810ef90541be28283f721487dea498df94f10f699443f6310c7e8a2997715031b6a9061ee31086faa3195f95032f6284437f548c2fca1207750f30bea90877e51906fca1a0fb4cb20be282437f54082faa9085f54243bf2a0837e50ccafea6105f55332f718c43ed520c2fca1195fd4132fda0021de508c6fea7085f54e41bfaa4217e539077c80a05f54430bf29463ee520c2fca0207b08440f799
  | 2 => 0xcc0a89e000220000c20000010040c844258440001e058bc3d8000014a3d0de0d84c000ba1237a0a0c402826138001093c03018000002a0000c8040100000020008000180438804118d2078260600a1b03c010184c00c0009a0002c00014068181300007814090001cc7800014120c02a00a00800010300491e4281e2b9d6070003c002000002404a1d80a37000078040c00a350820f8ce0403c0c0f80101a0383406a960d014950fa020020c800188600181a308d20001026804068000180200056118740b8040a8420a800010002bd200b000000140505434caa5c8440101e2080c0000403802048004b0040a802000ea0300c0280c00802099782b0dc07830000542c8660181c058286607c0701e01a5e1400c0001c000100080825806068880298a0583e34828078001982e0480200006290040006e009c61201a790000682e050317d50ccbdaa610fb88120bfa8a61de420c7bea690df94c30f629c437c53083b8a518f78c831bea8e657c54843d843a077d4831f7aa043ee42c82fea2995f54221f721043ee428cbbea818df94b10bea9a417c5250efaa990770c740fd902417e54082faa210778c510bea9461ee21d02fca121df94830be2a241f721887ee20085bd4910faa08835e53843ce6210dfd4540bf290437c54043be61185fd5130f7a92217e53883ba8718df54b10fb108437e544cafca2085f14910eea1a657e5110fbc6290fb15021bea8c857d50d07dc43985f94210bf28c437f54483b8a018dfd5132f610e61ee4210bbc63205f54830bfaa465df528c7daa110dfd5310bfaa0657e52083dea110fb94221bfaa6417e54043ba6498770c730bfa9e437e51087aca218db94a10b6a94217c54486fea7885f14d40ee188437f54882faa8105f14930ef29063ce31886fca5216f10440be28a87dc418c7e86390df55240bfa9a837e52d0efea0a1fb50920f7908437c51502b8a6a0df94831be29e217e53443d843887790c43bea8e81dc438c7dc6410f750a31ef28063bf41107be6518df15032f719443dd528c6faa321f70c710f790c43f431087dca610fb88710bf29883f7314c7bc63105f54e20bf2a087ee424cafaa6207b8cb20beaa061f840c43d842087b08540bea8e85ee51087d84390774c030fb884217e52cc6fca318fb88410af29e83de510c7b8a918fed0240f621043dc31042faa710f70c621ee18e41de53d06bca790fb88720efa8063f840042faa4207755231bf284837e54886fca018778c531bf296617
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x530865c6154c42d354d52843aa2150040d914421503c6540c421ea085401036651884409758e509074e534ca2197597410c6e661d4c21f10c4211026f65884309718d510834e520c610b398c540865d6510c31b5185320cacf624c431d3548318426d65884309798c5484355510c440cb95142887c4430c421d394d521031f548c510ae185401035763544409b594210c36651084408f590530866d62951319d58454082796510010d918a51103664214532f194631086d661148318f590520426d6215210b318d41886cd6210e31ae181411065e6394d109b59741086cc6350932b398b318c7c5310c4218fd95411065f6354640d554431882d661d4a319798c548834f5388521f10c4219025d63d5020f1d04310874d5350842d9544218c26c6254730d314e214425f658c4209b98853082e4614c920f1508310863e6495110b358c428863e6414c10d954951102776155132d6d4f50506db6050431f119431086d66115231d354b300c23f65500409b988548c26e6194843b6580310c2ad6414c219b58a53442756195132d9597310863f6550842b3d8d21086ad6414021f1904310865e6510a319d984548c25e631532197996314432c5488510c7153534431c5414d10d9d442150279658401097d8d51d0b4c520c5109b18951d0e5e6510831f10c42184356510c7309ed95100434c53149419dd8553486d561cc8319b98854cc25d6510a319798c53082ae6414021cb150214425c6550d32c7550430c7c5650c421b358c540866f65504219b58b5150f4f5294a31aed95401034f53085109b1855210f5950140319758c54c825e6514d10ba181418865e6394010ba18141086d6618c4218f990520426e61149109dd85544c26d6510e219758e524423c6454d109798c525025d65108319d584548c26e62952319798f528431f540c5109b588530426c61149109bd89519023f6454910d3d4e21443645188520b9d85320866d65884409d987538826d62150319758c52843c5640c421f10c4210434c534c920f10c421c834f528c51097d95310c74e5388610f1185320ca5f63546428fd954310fc4540c4219758c54842d66294431b959731087576394440b3988500c74e53086109798c528426f6508440b358c420866d6294231d5594310865c6154c40b998754886d761508319b58b54842746155130d314c2144355530c721f1cc8310865d6590c31d394c2108356518c630d394e210832f54149109d185534826d6215230f14c8310865c6354720ae191100426e6294e41b3588430c7c43108420cb550420867a6015021d3d95320ca5e6394d219bd94210c26e62150319e58354c865e63d45429e181544ca6c654c9209798c5050b56518c4409bd89511027661951329b58a54486e86050920e654d40103c7430c421b3d89418c7c43108510
  | 1 => 0x426c62546439b58854043c6620c42197d8d51d034d520c430b398c42086ce6215031b358b418c66d6294e419b98b5150f1f5414d10d998651086e661d4e21f19803108675650c421ba98221482b964900409b98b540c34f5314941b3588540c72f5488510d9d89511026d6215030b398e548865e63150329b594430871d5415031d34c9500cb1f54d4d10b358b310c6e96008420f118031086e66114c219d185544cb4d520c8319b988544c25c63551109b98b515023f6454d109bd9621102756115220b398c42886da608c5309758e544425f6354720d58c8514cb2f5408510b918532c83c43108430d5986510c65d631532197994314426c6255131d354e521026d62952319758e544c65e6194c40d394a311034e528c6109b59731086d661d08319758f51502cc6250431d5146314c32f5495221d518e511031f54952319b596320874c53d4941f1d5031086d4614c930d3949328c67b6055132ec94540102e5650c4219ed95200834c524c930d6d42508c74f528c531dad485050755650c721a7990520c6d463484219dd95411066f654c421d9cc8514cb4d5348020b3189310c756510c430da14b5050756520c4219799431487395410010f1984318866f6254d10f10c831086ce62d0431cb153524434d52148319798e52086e561d0c21b958b31087c431c8421b5987520c65d6395121d9949511027960150218f590530426c62551109798f51483c5600c421f154c31087c6610c42197d94311026d6215130d34ca510ca6e6294d109758f5150a6e62152109758f52842cd6295231d594d51103c7600c421b358b410c66e65149109b98854cc74e5394840d9d44214c27b6055131b5984540c67a6014c219b58854cc757510c52097d95320cae661d0c219b98853503665108720d614c50506746155120cd546411026f6254630d314f52443555354440d514f214865f654c030b9586320867860551219bd8951d026c6254440d5546311026d6215330b318d410865c6354440f10c4218c3c7650c421d314d320874d520c440d3d4e538866e621503097d8d544874e520c440ba580540874f53d49109798f54c866f62546439b986520c26e62150109798e544425c6354640d354a31843c4310871097986530823e6494d109e580530874d528c4409d984540c2cc6348421ba98053086756115030d354d521027661150109b988540ca5d63d45209b58b514c25e63953109758e520863c6454910d314d32c827a60150318f191534825d6315021b6181434c25d63d5210b6d81418c66e6510e21da540500866d6214143f198c31086cd63c86219b58b53843b241103109dd95310c74d5394a109798e544867a60d53319bd89544865c63547409b588538426e6588510ce153104434c528c5109b58b54cc73b5410310f1944310865e63d4540ba58
  | 2 => 0x31085409b98b54cc65e6114d109798c540826e6215020d3944310866d6295310cbd53524425d6594c20d5144315025d63151209718d51882e4614c8329718d544825d650c420d954a511036b52d414197195434c3546354440b358c5008756510c440d5d8553c86ce63c8621b3d89410c7c431140218f592534434d530c821ea54940103c5620c421b398c50086cd63c8421ced95401025c63544429e983540cace63c8421b9d9431087c6420c421b358e548874d544c8329798e52906da6015031d9944210831c5450d30d9144214c2e66394421d354e211034d5390842b398e50886f16110310d354e218434d5308440d3946310865f63551319dd95100432d5415021d614f50507c43108520f10c7500867a60d53219798c54086e6630c421f1d08310874d5394b419b189510c25e6314810b398431086d5650c721c7150314425c6114d10cd15241442786055131b9987540869d64148319798c540c26f6254d21d9d88514cbc431940219758c54882746550510d5d8c514cb564314532b998631086cd63942219bd8951d0e6e6294241cd584544426f6255131d5d44315026d6294010d354d52d06cc614c8329b98a500426c62546408f99053086e76150c21d354e210826e62d4e109758c540823d6494910d394e52d06d661d52319758c5050bc6320c4219b994430866f65508429b189518c3c43154021d9189511025d6394010d390d5210f4d528c430f1108310869e64140319d98454883554314532d354c210834e5394a10b358a508c77060544409bd895110e6e6214143d394e211026d6294f109798e52c43c4410c4219798e524426e6295310b518532cc34e5354b4197d95410c66d6214d409b98a544426f62551109b58b515026e62d4530ab99053086d860504319b58b540c2eb605062197d8d511026c6154830d394c211025e6315010cb150524426c6550932b3d8d41886cd638c8329718d524434c528c531d954621102ce618c421b3189418c63e64949109b18953442cd6214031d354c21843c7614c8329ed95300c3676294440d9544211026c6550920b5185420c66d6508440b3d8d410873a41141419b189544c25f6354620f1190310865d63952219ed8154443c7640c421d394d5284354510c5209799453486b960104409718d51d0b1e5450e31d914b314c74d4354843f194c310866e6294910d9508514cae4624c43197d8d5110a7960d5032b398b418c74f5314910f10c4218826f65480209b98a544c74d5314c219798c5448356650c4219dd85544826e61948409d587538834e520c4309758f54c874c5314910979865310a6e6508510dad42508866e6214c10b6580540c67765484219798e548865c6354642b5587420c66d6295110bad81410874f530ca21f10c5210867b65500408f9945444356510c6209798f548
  | 3 => 0xa802000013781b2701a028000000f028114840e0cc0e014003107b084002705200c04020080204d0483500c10081860240b0b401034030741e0c6e5004000000000016010190d442038060081308c00100380bc1700035010240000100400240841e4000ec00000800b89f28c2118c07074002040002400000c200401250431380100c0c04c00010190e89e1d00002c4b000000005e09401128440040302800064070000004018018cd0200d4a4040980207068040050bc3654c580001347c0905c01038280c1bb04c0802c07150011589b26413004f00283c0080102c0168c272081905802000970a46a000ce0301201c0000c0e1240b0840a1d015000b50100801409188040103b018233500000404014020404100010000b10401d2d4260a00700020005d100caf0940f0540002800054410384000c2a02c00040060d4a30689bd554e51103c431087409b18951d039a315004097996314866d6294d219d984540834c538852197d8d5108366529444097d8d54443685214141a7590500c65d6394a419bd89510c2ea60150219758e52c43676154b31b5987540c7c5410c4219798c54c823e6414f209b185521027960d53319e580540c66e62942319b594420866f6548421b398b310c74d524c030b6980520c7aa5250040f155031086e46150c21f1994310865d650c440d3d51320ca5c6355121b398a508c7c6430c421b398f41886cd63d0621b9984548874f520c51097d9431082cd63d042197d9631102e6611502197d954310f6651886209bd89544c26d650c8219bd8951cc3665108630cb151424826c62544439b58a509065c6154c209758e50886ce63d04219b59642087c6640c421e694d401034f53d4941b1185320ca5d658c440b3988438c65d63150109dd8553482d66114a318fd91534835653944409bd95320cac6618c421b9984538865d658c4209b988538425f6355120f10c421cc25d63148109ed8154486f060507109b98a53c425f6354910e60c540102ce6295231d354f200825d6314940b6580520c74e528c430c715231442ce6210c31b3189434ca5e63942419798e50886cd62cc6318f59053c825d63953109798f54082d86050631f150c31086d7614c8319b98b54843b15150040d6d4c50506cf654c832f10c4214c3c4
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x400048052040001600004000030a1a0da83140cd80020c018290c3820008980000639300000330e0410015511c53294432e08a818842886495358021082e03828218843915943108440a52ea10a802074031540500870caa2c02a063835516215031c8ea830a641954671d4a528c6a239aa210881511cd4214532b0ce83006210d4970d51320cae0b80a81884391594650c421a8eea1884210644631895110306aa2c621043511c55308440b0ce83286210f07540c42144323ba8c299065865915014031c8eca188421864952580520c6a238aa6108418a5915014021c88a630a659062954580540868cba862a0081525c0534c821c88c6314a2206c16018031086e0b80c818843511c9510c440d0ac83206210e44531853248323b286210881511c53254032a8ce5a8862a0547750c421102a2388a610a21835915214831b84e03206210d0d7414d32c8342b20622804391550614c832d20c218a8020545750c42110390a92a2a0081519c75394e21c92a6b00a610e0d54588430c788a9aa2a008192549600c430a8aea3206210dc1701943108722290c299261435d0534c821b84e02a06210e4962540500c706b22a62984370dc1410c421f006210a80204c67615031086a238aa418881835516315021a88e2a906218686640c45008723b28c299065615d0650c421d40c210a80205c27019431086a33a8c818843315d8540c421a88e4a18a299645650c83108724b1aa028043519cf51085408a8e2b18a4a0585741803108782aa0a818843191c56214d40
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x5000501010061000000c8174580600c421c0575590640c421d01750c42150040c0576550540c421b01850c42150040c05655d0650c421e01640c55014021d01545c0540c421a4081549600c430c41655c0650c421a058414c614cb20a408154d6008420a4180d50614c832c11751843150040c81645c0640c421
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 779
  | 4 => 754
  | 3 => 85
  | 2 => 15
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
  | 6 => 2*((h/56+packedAt s2K6 (704+(h % 56)*6) 6) % 44)
  | 5 => 2*((h/259+packedAt s2K5 (21033+(h % 259)*10) 10) % 779)
  | 4 => 2*((h/258+packedAt s2K4 (28652+(h % 258)*10) 10) % 754)
  | 3 => 2*((h/49+packedAt s2K3 (4165+(h % 49)*7) 7) % 85)
  | 2 => 2*((h/19+packedAt s2K2 (900+(h % 19)*4) 4) % 15)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfc0ffffff01fff81ff87fe1fffff07fb18fe3f
  | 1 => 0xfff01fc1fffffffe0ff83fe0e03ffffce733ff
  | 3 => 0xffffe001ffe07ffff0003fff003ff87f07c3c7
  | 4 => 0x1ffff81ffffffc000003fff87f803f8
  | 5 => 0xfffffffe000001ffffffffffffc00007fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2461429011c1048031814605238b44c908561b
  | 1 => 0x8a4c502224a281606881a20449509106330ed
  | 3 => 0xb14289b5448751aad0452d560926d46705c346
  | 4 => 0xa38b163989141dcd6b5581141238e647b803b0
  | 5 => 0xc20c18210e1861718c6631989c008006d6a800
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaacc888800eeeeeeaacc888800eeeeeeaacc888800eeeeeeaacc888800eeeeeeaacc888800eeeeeeaacc888800eeeeeeaacc888800eeeeeeaacc888800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_41616
namespace PEqualNP.Outside.L_meta_41616
open PEqualNP.Outside.L_meta_41616.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x1c502230112d00b01618104b001006085205fd10fc40ff32fc41fd43fc21ff42bf42fd42bd42df32fe31ff40fd32fe41fc32fc30de31fe20fe42fd41fd20fc10ff20fe21fe32dd32fc31fe40fc42fd21ff21ff30dc31fe10ff41ff10fc20ff31fd30fe43fc43fd31ff43fd40fe30
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1000c01c82443c0184a544850230035141070c162888200948003219e80091000d095e53082daa4205754e429eaa0435d53086baa518f594431e721265d431443a86390de54021ea28a655f538867ea8885bd4910afa9a435c53503a86210eb509209f2a06554514cabaa7904f95232af29e435e510c67aa990cf950219f2a6433d548caeea2994fd51309f2a641d7514ca7aa9906350932af298655c53886f4a010dd94440cea16655e53c8278a8984f55242aea9e835d5310b3e8518eb50a21bb2884174514cabea6885714d41d6a10433c544427aa8105714d10aea9e439d428c6baa7194f55032af29c215e5390b3a84995754831afa9a83ad428cb3e8418db54b41ea18e213e5410abca6205754e10aea9841ad424cab8a690e7d0932aea98816e52d079a84995794f41b7290813e540833a8418d714532af28c637551082bca610ebd4942afa9a815e5310b5a859067d0b32e7a92657551102dca421d794732b6292216d5210eeaa3185d94630
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x271008401c0119f8542d45329518553c831742145329559431087294254021c3549420c744520c510a3592424ca2d6215130d40c5500870d5350b20d1508514cb154214532d1908514cb0d4214532c354d4208785420c421c9508514cb854214532c1508514cb0f5350a21
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x701420c5500868238aa6a164181595420c421
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/29+packedAt s3K5 (736+(h % 29)*6) 6) % 46)
  | 4 => 2*((h/40+packedAt s3K4 (2673+(h % 40)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s3K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/8+packedAt s3K2 (147+(h % 8)*2) 2) % 3)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ffff81fffc3e0ff87f0ffff87fe07d19f3f3
  | 1 => 0xf81f0ffe0fffc3f0ff87f0e07f87ff82e6ccfc
  | 2 => 0xffe00ffff0ffffff0007ff007ff8ffff070f1f
  | 4 => 0xfffff0003fffff800007fff0003f80fe0
  | 5 => 0xfffff000000003ffffffffff80000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x10c2008c200840011809012318092118085171
  | 1 => 0x32441114645004506883104528824b0862c4b4
  | 2 => 0x4108aa2082a222a60444aa0845509463050a0a
  | 4 => 0xe596cc494a3aab3bb550881276640633b80fc0
  | 5 => 0x861888718cc333ccc666cc9c04401843d7a000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_41616
namespace PEqualNP.Outside.L_meta_41616
open PEqualNP.Outside.L_meta_41616.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x1840000000f1de000000140106182001017040000a001800437c1fc30ff30fc32fd10fe10dd32fd21fc42ff40fc41fc10fe43ff21fd31bf42ff20fc40df32fe32ff43bd42ff32fe31fd41dc31fc31fe30fd30fe21fc43fe42de31fd32fd42fc21fd40ff10fc20fd20ff41fe41ff31fd43fe20ff42fe40
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4214002c08d000418400040012b50100002440b001004400581820004000060090000002000208000601c3800858181000420e000418200ac211015e53d067aa810d714d40d6a16416e5210ebea690d714d41bca80435d538cb3a859957947329eaa065cf524cb9a84994f95032aea90637551083a862885794e42b6a96835d53c82bea710db54840bb28c615f535027aa9906b509209eaa4659d428c6eea299750c710af288633f54442b8a690f5d4532afa9a835d53842bca7086b50821d7a92855c53887aca218e7d0831b729683d431c867ca990dd94440b7a92213e5410b3e85995754c40af298815d530875a8510db54843aa28a659d424cb3e84994f952329f2a6418d424cabaa6215714532aea9e836e52103a8a2995794f20baa8c616c52442bca6215d14532d6a12653c544c2baa518f390932d6a14653f544c3a86210d7d4d10baa88815e53c873e8518de940219e2a2215e530ca7ca8104f55020af298419d420c67aa990d794c21aea9e435d5390a7aa9215794631ae29a215d530827ca810dd94420
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x4200062f11400183294254021c3d4d428872542145329559431086546154f20d1908514cb0d5250831d1508514cb44520c510c354d42c838542d4532c3508514ca2d6215130d40c550087054214532c5508514cb0d5350821c5d08514cb854214532e1508310868d6490932
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x701420c55008702b2a8418843411c55350b20
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/36+packedAt s4K5 (736+(h % 36)*6) 6) % 46)
  | 4 => 2*((h/68+packedAt s4K4 (2673+(h % 68)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s4K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/1+packedAt s4K2 (147+(h % 1)*2) 2) % 3)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ffff81fffc3e0ff87f0ffff87fe07d19f3f3
  | 1 => 0xf81f0ffe0fffc3f0ff87f0e07f87ff82e6ccfc
  | 2 => 0xffe00ffff0ffffff0007ff007ff8ffff070f1f
  | 3 => 0xfffff0003fffff800007fff0003f80fe0
  | 5 => 0xfffff000000003ffffffffff80000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x10c2008c200840011809012318092118085171
  | 1 => 0x32441114645004506883104528824b0862c4b4
  | 2 => 0x4108aa2082a222a60444aa0845509463050a0a
  | 3 => 0xe596cc494a3aab3bb550881276640633b80fc0
  | 5 => 0x861888718cc333ccc666cc9c04401843d7a000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeae8e0e8e0eeeaeeeae8e0e8e0eeeaeeeae8e0e8e0eeeaeeeae8e0e8e0eeeaeeeae8e0e8e0eeeaeeeae8e0e8e0eeeaeeeae8e0e8e0eeeaeeeae8e0e8e0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_41616
namespace PEqualNP.Outside.L_meta_41616
open PEqualNP.Outside.L_meta_41616.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x85be54082f8a2995f55231df2a4217d508c7baa610df55010be2a2657e54043be86997b90842bf296617d5390af2a010d794c20efa18637e5210efca610fb48020ee990657e510c3f640085f94a30ee996637d50ccafca598f7d0e30fc900417c52506fca3995f15030bea98437c54042fca918f794c40bf2a461dc320c6f8a2a1efd0e43ee21e657e51d02f2a021df14d41dea12817d53043bea690df94243bea8c21de434c2f8a9197d88421bfaa0617f53083bc6298df95210bf29083bd540c2fca3a16fd0641bf29e215e5390afaa3a07d88710fd882217b50487bc6518f7d4d41bf28c41f820042fca621df95121bfa9c417e53886f8a9986750c43bfaa6217d51d0bde4310dfd4530f690843f721887bc87986f50040beaa461de53087788520cf95210be298413c544c7f6611877d0d43bfaa2637e5310afaa5985f15020ee18a61de53082f8a4a05f95032bf29e43be4350efea8995f94c20bea9481bc41d02f8a9885f54a21bfaa0417d52d03bca7086f95232bf28c63bd54086fca0105fd4b10bf29c877e518cbbe87995fd5330bf2a0637e54cc3f4a021df94321bf290617e50cc6faa5105fd4a10ef990655f535077e85a0774c930ef99663be41503b8a6a05f94842bf28e617d528c6baa6205fd5230de2a2437d538cafea8985f54f40be282437d518c2fca5205f94e42be292637d528c37aa9086f90c40bf2a6217d50106fea9996f90140de21a857e5410fbc60985f94443bea9e437e500c2fca521df55210fd20461bf41106fea708774cb30efa9a817e508437c86a15fd5120be29421f521086fca0084fd51319faa2617d508cafaa9985f14132bf28485dc31cc3f621085f94642bfaa0637d54906bca7085fd4940bf290637e518c2fca110dfd4542afa9a437a50087de401077cc230be2a261f521c43ec6218df14e21bf29e83dc438c6fca990df54720beaa6217f54cc6f8a910efd0b41fd180617d5310afaa2216f10841be298217f5048678a8985f94e20beaa4877e54886faa321df94c31bf298837c548c6fca5195fd4c21bfaa2217e51902f8a7105f14943bf2a6657d53102fea2a04f552109eaa4657e5010afaa9907b88521bf29021df324c2f8a8885f54830be2a441be4250afea098f750d30be28a417d54ccaf8a9187dc4210bea9a217f540877882a06fd5130be2a2437c52043f660987e54021fba0a83f710043baa6207bd0a42bea8043f9408c2fca020df55220dfa1281f7318c6faa7a0df54620de21881f621442faa018f7d0e31ee218617f53486fca7085f55132be296217e53c82faa1215f94e40bea8c853c54487be65985f55031eea1e617e53d037c87205f54743fb90a437d50d06faa720770ca31bfa9a41fb20c437a84a0f7cc631de21c817c5350afea4a1df94820bf294837e51c83baa7086f15130
  | 1 => 0x10008000f0000404600000080000000a0000c1b5fd4f20beaa0657e53486fca8185f95220bf284637f52506f8a8195f54841ee29a43be42906fca810df54732beaa6437c54c86fea0a1df54432bf284417c54086fca1a1ef10e41fd202617d5290efaa9216fd0c43ef21887bf54486faa7185f14d20bd280877d53482f8a0a15f94e41bf288857651082faa998df55131be29e217c5150afca2195f14f21fc902213e540c2fea990df540439f2a043f541106faa421df54730bf2a4657e50087be86187e08310beaa443dd324c7f480205fd5320fd10221ee320caf8a4887e4c030df20a837c53c82faa8905f94240bf298617c54cc77e87a06f90c41beaa243f5310c6baa7084f95232bea8487ed4210af8a2985f94b40bf28483fb40902fca8205f14540bea9063f910042fca0195fd4132ef19265ef328cb7e84215f55232beaa0617f540cbbc6418df94c32fd28043de314c2fca1a0dfd5220bea84837f54887ea4288774c431bea96837c50506faa5885f94441df21e857e510c77a85a0ef90e41bfa98217d52907f0a090cf55030be2a665bd43d02fea4986f15131fca0261dd5390afca018df54b31bfa9a837d50c86fea4087b88120bf2a6417d52442fea9197d94420ee29a835c53486b8a6a05f55020ef18e617d500cafaa7885f94743fca0081f7314c6fca0205f94621bfaa2437f53886fca518dfd4f10df21083bc43106fca5085f94420fc904217e51042fca5a0fbd09429eaa0417c53086f8a0a1df95131fb082217e51102faa3207d44010bf298815d53082faa720f74c030bf2a0837d53843f680a05f943329faa243fa20842fca021f7cc931ef988637d540877887a157d4d40bf2a0413d54086eaa2105f14d40f7908437d52042fca1185f94a42be2a2417d53486bca6205f95120bea9687df300c37a85a04f95020dea08837d50cc6fea2907e84010bea86877d51102fea0a15f95331bfa8283bf4290bbe65195f54443f699065de5390b7ea898df55110be29a217d53106faa4205f94c10bf2a265f741906f8a4985754c21bf29621fb50486fca5a1efd0d40bfa92217f514caf8a7085f15320fca8087bf40102bca610df15210ee21a65bf42507be8721df55130df2a0437e544c2baa7215f55240bfaa0217e5190efca320df14d21bfa9a21ef324cbb88618dfd4543bf290437e53d0afaa710ef90740bea9c417f524c77aa8105714d41dea18877f54842faa6107710e30bc282437d5010afaa5085f14131bfa9a857e50d0bbaa6106f50d40bfa9a817e53442fca8217750c43bf284657e54442faa7a17d54420bf28843bd548cafca4195f54430bea9c63fb20482fca6905f15031bf292217d53c837ca8185f54221fb208837d50d0afaa2107e88020bf290817c544c6fea790dfd5231bea8c65ef20883f641106fd0240dea1
  | 2 => 0x105c093b00380c008400006c0083e03829238280000000010fc01205800058140083a020000301a52000020300a0063f81e00000080064201e12000128320000ad58060182602800000000b8801b07800816008005481e0200e08020078800080000002028360e002008002b000040065a8020533c020120295e060d8040020c804028540000000b860400e0183067004480240888c00864020040000000390050020b00016b0a0001e000060402605800000121301f14806030000101e0000803000040061385a0000400000030020000044846008081000e0180c0486805b8a048002980403800068021b814000260d8120101a000000f80023010248040008800800050000080e24800000061a00400a5a00008038140285a028160805a043260080800802008000f8
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1324c25d63d53109758e52d027765440109d185534833a54940219bd95320ca5e63150209758c540867b654c030dc546200823d64149109798c540423d6494b318f191538863d64d4c20c7152314c65d63951218f191534865e6514d219758e509065c63551108f99053043365494420d650d5010e3e64141329758f54c827b65500409d584540826f65484219b988540423d6494d21c7552530876452485108f997425067965c80109e980520426f62551109d984520425f6354442dc485500865f63547409ed81534871d5310c408f99053083355454420c7952538423d64d4f2197997324c63d64d4f108f19151c823f6550441e690e404c27a60150219dd95411071d54cc0308f99252cc67960153329e983548c69c644c4319e580530871e5454c21c794f4290a7860551218f99052c425d63942218f19151cc39b43502308f994544c65d6594c219718d5110a3e6515130d654d401025d63d521097d95300c25d63152108f19153042766114c20bc58420c423e64d4a10c7d50438c31e5494c208f590530423d64d4a10c650d5010f1e54cca329798f54c425d6314142d694d500865f654c83297d8d544839943501309e580540ca3d6595021b6982314c31c54d4d21a718d401026d6214c10c750d5010f7151480209798c520423f65500409e583530869f6550c438f596431031c63550308f191534423e6415030c7d50438c67860551328f191524425d6510c318f191510ca6f6254d10c714f42503585314121c714e415063e6414a1097d8d544c25e6590d30ce552300c25e6314c209798f54c839843902309798c524429c635044197594430c29c6150c43cd552510827a60d5021d690d5010f1c5490d30ced50504863d64d4e108f590528425f63551219dd95310c63e64948329d987540823f6454d10c714c415023e64d4c20ce951500865c63551209798c548425d6315010c754d40102786548110ce551300c25c6355220c7153324c7596014d409d58453082b96010d42c714f435025f63550109e181534867a60951219758c52c433943540439798c5050ad96010e31c755043cca3d6494832c714e415025e6394241b6580434cb565354420c7152314c23f6454e209e594200423f6454e21c714f425063d6590841d654e500869e63908419e98054cca3f64547208f992500425c6354910c7550430c25f6355110c7951530829e648c9328fd9151cc23e64951319b588540c71c544c931a71814310e9f6250c438f990538423d6414810c7151324c25e63d5321c7951538425c6354720c755253083706054420ce55250086776154d208fd91534865e6394010a7992320c63f64549109ed81544ca5c63552218f592508873b54d41219e582544863c6454e20ce150504865e63d5210a798e429063e6414c219798c52c42796015021
  | 1 => 0x20282c062d0180c0c180884418100102002051f8000600000c438070c005d200138d008071b60c723b0280000050002000ea01b9c001f000008cf0068080c0000800001305850100001a6402130380402565d02c00003f80026210b2d0020b6601000620003c2a00410011000058cc3403018500000000040400770041a001e8343eab03800082c018100002030a40c010300004010f014000802801820f0483016fd000f9a22a9798f540863d6414c21ae580439031d5390c40c754f401031d5494e10c714e405029d6490c43c715143cc31d5310f4297596530826e62150319798c540c25e63d50209e58054cc63f64544328fd954310f5853d41218f990524431d5454c21d6d4c504865d63d50208f590530825d631502097d95310c65d63d4a10e650e5010e9c644c030c755153082d96010c318f997435023d64d4c21d594e510823e64d4c219ed81524425d63d50219798e52d071e5494c21c7150314c39943540438f99353c427b654802097d8d548865e63150219d584540ca7a60150318f992544863f6454d208f990538831f5414d218f590538425e6314c219bd954210a3e64d4e10b6580430c27a65881109758e52d075553544208f9905408276611502097d8d544c67a6014c21c7551300c25f6550c438f59353c833954540218fd954210a796094d218f99454486f161080108f590538825d6315220b6580438c3595354021c7d954310f1c548c130b658043ccb595390040bc18121c426e6214c108f99353c867661d52309798e544865c635512197195434c23e64150218f59052c431d5310c41dc885500869e648ca31c714d425071c54cc9309798e534863d659503097d8d548835553944209798e508866f65480208f992508c67960d5021ce153504863e64148108f99252cc31d63151308f99353c823e64942219798c548823f6454c10ae580431031c5350940c714d43502d86350230cd951510827965840109798f540cb1d5410d329e583548c65e6394b409718d540435b53d41219758f54c865e65d0d32ae58043d0a7661d4c209d984540ca5e6314a109e980540c25d63940109e195404c27461551209758c524425d6314a109e982534871d5410c319758c520427a60150328f592500425d658c8319d185544cb5a539402197d8d524423e649513097d8d51c823d64141328f992534865c63547409e98353086b96010c41c7d5353486ba60905409dd85544cb1d5454e109e98054cc69e63909429798f52842746548510c7151434c26c62551109dd85544827b65440109d587548c27b6055121ce580544c3385490130ced0d5010e7765484219b189534427960150319d587540823d6494231c715053486b860509409b588540425d65d0c30c7553430c27561d4c208f59252cc23d6595020ae580439063c6454d20b618
  | 2 => 0x360c024043d59030020002088060d0008c12000602400019a064041103021a40707104014
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x31c027072100002000271b800004146dc94354043a30e0aa0869961963580544c28d386a821c63265d0604c930c32a6b008620e1954580430c24cb98c0a12818614c6050940c36a8b008718c9973982415028c38286a808786152608c530c30a730482a051671d50438c30ca9ac021e85865516010f32c30caa1a809861954580430c70daa2c021c61265d2608c530c30a8302649851a7590e404c20e3b2a898061269db4350230a30eca1aa021d187150d5010e8a38aa821a65865516010d32
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2400081987150604c93081987152608c530a10815516010d32a1281d516010e30
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 601
  | 4 => 396
  | 3 => 29
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/256+packedAt s5K5 (16227+(h % 256)*10) 10) % 601)
  | 4 => 2*((h/181+packedAt s5K4 (15048+(h % 181)*9) 9) % 396)
  | 3 => 2*((h/23+packedAt s5K3 (1421+(h % 23)*5) 5) % 29)
  | 2 => 2*((h/15+packedAt s5K2 (240+(h % 15)*2) 2) % 4)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc0ffff03ffff1f07c3f0f1ffe3ff81fc41f3f3
  | 1 => 0xff03fffc0fffe1f803fffe1ffc3ffe007e7cfc
  | 2 => 0xfffc1ffff07ffffffc00ffe1ffc3ffff878f1f
  | 3 => 0x1fffff8001ffffff0001fffc0007f80fe0
  | 4 => 0xffffe000000001fffffffffe00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x52185118a212310160b83132626484b440b171
  | 1 => 0x864882286424022801515204a4092c101a54b4
  | 2 => 0x8210441014800528400844108825141850a0a
  | 3 => 0x2cb2d892490e559cea6a0111d3301866e80fc0
  | 4 => 0x30c310e38e7099e7338ce9980220618777e000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0fce8e8e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_41616
namespace PEqualNP.Outside.L_meta_41616
open PEqualNP.Outside.L_meta_41616.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x403403850310010c00800000064417410000000803820c00200000000c200000254700900ff10007fc43007f50c07fe5300ffcc005fc32027f950057d5200ffd0005fe21017fd4805fd3202ff55003fe2000ff4c003ff10017f94809fc5402ff14405fc52017f1080bff51017f8c807fe4300ff5400bff5301ff14c03fe50017f5080bfe51027fd0409ff4300ff84005ff3202ffd5005fd2100ff08007ff31015fd480bfd51017f08401fd31017f54803fc5000ff8c003fc1000ff0c003fd1002ff54c05fe42007f50405ff21027f10401fe31017fd0807fc3100ff50003ff20007f90403ff5000ff90003fd20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x12820bff9823105fba611882eff608c415ffb148213ff58241057fecb20823fc544c415ff28c6204ff50e41027fca8a0813fe4250431ff2928603ff50e3103ffe8498853fd529040dff2826211ffcc54101fee631880afe624c431fe10a860cff10a31027fe812085fff1050c2dfeb2c820eff5463101ffe6098813fe4350407ff1846206ff54131015fcc4a082bff109042fff102860cffd4a31027fe84a0813fc545040fbfa926200bfd913107ffc40a080fff5350c21dea128216ff5464107ffca0a080ffd304c41ffea828204bf99231066faa518833fc528c41fff982820dff9523100dfcc0a0853fc5290407ff9928600afd913109ffc612080fbe4350c077fb228603ff94d3101ff8a69880fff438c421bfa92820cbf58a31087fca4a0857ff319040b7f32a8209ffd5131065fec518837fc548c40fff2926213ff94241015f8c498806fe6050c0dff882620fff4c14107ffe20a080ffe314c407ffa9a620fffd81410a6faa520847fc5350401ff20a6204efd094101ffe631880fdc438c431ff10a8606ff88131097fea6a0833fd428c4217fb128211ff94d41095fecaa081bfc604c401fea0c620cff90a3105ffe8118863fc6250c09ff2028604bf98641027fc852080afc62904097fb0a8204ffd0e410a7fea520816fc6590409dfa028619ff14543027f88520813fe54904037e304820cdfd4a31027fa8520833ff428c427ff1048210ff1894101dfcc72082ffd508c409ffaa28600bfd923103dfac498813fd5450c07fe1928604efd0241027fc82a085ffc5050c0ffe10a6218ff485430bffc20a180fff308c4057f3146203f70ca3101ffc64a184bfc5150417ff2846218bf58943015f8c518802df635040b7f32a8600ef9054101db8c6a0853be4290407ee18a6212ff5954101ff8a71885ffc2050c2fffa828606ff901310a6fea52081ffe214c427ff9848207ff9893103dfec498813ff4290421fe10a8217ff4414302df8caa080ffd308c42bfe29c820bbf5823109ffaa120803fe6150c037e3028203ff10d4304ff8a298813fe4050407fe21a6204fd10541025fcc898803ff644c407ff29c6205bf196310c7fe42a184ffd30904017eb226204fdd0541027f880a185fff2050c15fe3246210ff8c941087fc42a0857fe5390419ef1946204f7d0d430cdfecaa1803bf644c409fea048207f74c931057fec120802ff6350407de21a8607ff48531057f8432081ffc624c407fe1826210ff9894101dfcc31885bfe6590409ffa0c8201bf18231057fe2118863fd6250c07fe1828603ff0c9310cffccaa1826ff654c415ff20c620cff94a31087fa42a0816fe658c417ff104620fff98141037fea098813ff5450407ffa9c6219ffd454302dfcca9880ffe324c415fe10c6210ff0c941037f8a09880ffc438c41ffe1828200bf18543
  | 1 => 0xffd5350c2f7fb028603bf18d4106ffcc918803fc6150c09ff2048208ff9913104ffea298813fd4050c25fea9a8217ff48143007bec6a0803dc6350407ff21a6210bf5894101ff8611880ffc328c415fe28c8201bf98131007fac898813ff54904317fb128612ffd4541027faa92081bfd604c427fe1848217ff0414301ff8629883ffc2050413ffb2a6209bf595310c7faa4a1847fc3150407ef982860bff4423105ffea11885fbd4050c097e3226200ff58e4101ffc6518863fe6250c1f7eb02820fff1814105ff8a118853fc3290415fe20c6203bf98d4101ffa6498803fd6350427ffa848217f74c14305ff8811880ffd534c415fe32c820affd923109ff8a12082bfc41904077fb1a8604af19131067fe4318867fe5150c09fe21c8209ff99531027f8a8a182fff208c40b7e32a620aff18a41027788720867fd6550c2fffb028619ff54543077faa91881bfd404c40dfe9026210ff4c941037fc209881bff604c4077fb0a6219ffd9543057f8c12084ffd1090429ff3148204bf5924101ffc60a1833fe628c431ffb128618ff1494302df8caa180fff4350c15ffb1c8206ff04131027f88120813ff4250c2fff2828604ffd054307ff820a080ffe4350c07ff98a8615ff98e410277e832083ffd2050425fe32a8204ff501410bffcc0a1813ff4050c15fe32c6203ffcc93103ffac49882bff628c409fe20a860bff08231077fea31883eff6050409ff21c8203e710d43027fa84a183ffe105040ffea926203fdcc5310c6faa4a182ffd608c4057f3148209ff9453101ffa869880ffe438c427fe1048218ffd49430b7fea320806fe609042bdf21c8207ff10931027f884a0813fe5450c057e3128600f78c53100df8c0a1843ff3250421fea92820fff8c141057f86318813fd4350409ff2128617bf5814309f7a812081ffd424c4097e324620df7d0e3104ffaa29880ffe304c423fe31a820aff94641027fe80a084bfe5150415fe3046219ff1954309dfec12080fdf318c423ff31a8207ff1493105ffa811880ffd328c401ffb1a8209ff59531077fccb1884bfd5150415fe18c820cff54a3101dfec69881bfe604c40b7f32c8200ff59231047f8c898806fc604c407ee21a8614ff4ca41015f8c4a0813fc54904097fb228203ffcc143077facb1881f7d524c4017eb1c8210ff149410bffaa0a181bff404c417fe9046208ff9513101ffe869880ffd538c415fe0846210ff5894103ffea49881ffe424c4077e31c820aff18a3109ffa41208637f5250c17ff0846200ef1913101ffa60a1827fc654c41ffeb028216ff54e4101ffca6a1813bc429042ffe3028603f7cc23101ffe629884afd6550407ff9946217ff5814309ffc2120813ff4350421bea928200ff5053101ff8a6a183aff658c415fe0848210ffd49410a5fac520853ff3290409fea
  | 2 => 0x901c0081c460407050a20f488700418068081a000682000010186822000000004010000028090a074e2130000400041200c0006244bc50093b0041231001d47a67020301a359383c001f00004040051814004b020bcce660000004082c98c30b4080f00403db29c74000603402190480428d10080d700002804142700030060d008380803000001600018522c13120341a5d000081c050d84c390e21000100000058060421000c00015830c60f0c9501e7400008140105938020202804160c2c800080000004ac00000b41a080cda402060007c220d03ffe4298823ff414c415fe31c820ebf59631057fecb1881bff204c429ff2948208ff105310b7fea72081aff604c427ff3048212ff99541037fa209880fdf324c413feaa26203ff4c943005fac91883fff5050401feb0a8613bf5824101fe86298813fc4350415ffb046219bf5954301dfac71883ffc505040dfe2026202bf98943057fc4320843ff6250425ffb2a8214bfd8a410a7fac52080ff4318c42d7fb2c8204ffd05410b5facb20813fc4150415ff10c6203ff0c543087fe42a0813f74190409fe2128606bf5813100dfcc11883fff2050429ff90c820fff44141037f84098813f4419041bffa0c6213ffc824105ffc8118853fe3290429fe90c8207ffd8931027faa8a0813fc4050401ffb0a860effd5231057f8a318802ff6150c19fe90c620cff58a310277882a080
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe71d9231054ff721854306fd741d8d4106edd43d8d41004fd7559231004fd70d8d41054fc75d923108ede53d8d41046be54d913108ede43d8d41004fd7558e41004ff7059231006df72d8d4100cfe70d8543006de60d8d4106edf735923106edc74d8d41006dd70d8d41054fe71d8d41006de10d8d41014fe7259131006be72d9131014fc72d8543056bf6190541116df4318543054ff7018543006bf72d913100cfc70d91310aedf30d9231046be76191310f4ff7650631006dc10d8d410067f5258e410067d5258e410aebf71d913106edd71d8d41056de3158e41006df75d8d41006dc20d8d4106dde7618d4101cfc7650531006dd30d92310aebe31d91310ae9c6390541046be64d9131006bc75d913106edc40d8d41056bc6459231006dd53d8d410af9c439854306edd54d8d4106edd40d8d4100cde768c531054fc71d9131004ff7558e41006dd72d8d4106ede40d8d4100cfc7059131046dd4358e41057b6719054108ede7618d4100cfe7059131004fd72d913106edf41d8d410e5dd728c53106edf54d8d41006dd50d8d410edbe76d9131006bc51d9131004fd75d923108cfd7650531004fd7559131006dd3258e4108cfd74d92310afb731d9131006be51d913106edc54d8d4108ebf43592310aebd43d91310079d42d8d4106edd42d8d410aebc31d913101cfd71d9131006de75d8d41006dd65d8d410febf60905410aebd32d9131054fc715923102cfe75185430067d52d9131006be62d9131006de65d8d41004ff7258e41004fd7059231006bc62d9131006be50d9131014fc72d9131006df62d8d410aebe30d9131006bd51d9131006dd30d8d41056dc3158e41006df21d8d41006bd60d91310eef53118543006bf52d9131056f671d9231014fe7218543056f42118543006bd52d9131006f5101854301cfc74d8d410067d52d85430067f52d8543024fd715923106fd441d8d41014fe72d923108edc53d8d410eebf6119131046bf40d9131006bc70d9131054fe7158e410aebe4358e4111ef641d8543006bd21d913106f9c41d8d41006de70d8d4101cfe73d913101cfc73d9131006dc50d8d4101ddc73506310067f52d9131006df60d8d4106e9c648c531006dd6218d410aebc30d9131056f710185430af9f32d91310acfd73d913108edc4359231004ff70591310acbe761913100cfe7058e41014fe72592310aebc6390541006df51d8d4100cfc70d9231006f771591310aebf53d913100cfe70592310aebf6490531006bd72d9131006dc6218d4108edc32d8d41006de62d8d41004fd75d8543004fd70d9131006df50d8d410075d5218d41004fd701854301cfd74185430a6be6290541004ff70d8543006bd42592310075f5218d410067d52d92310067f52d923106edf4359231006dc65d8d41006bf60d9131024ff7159231
  | 1 => 0x8d41004fd7058e41066de628c531004ff70d913108dde76d8d41006de51d8d41054ff73d9131006be75d91311073d5290541006dd3059231006bc21d9131006bc52d9131054fe71592310d6dd608c531116bf4018543006de30d8d41056dc6358e4108f9c43585430a6bc62905410aebf73d9131006dc75d8d4106edf42d8d41046bc54d91310f6df6118d41006be70d9131006bf51d913106edf43d92310075d52d8d41054ff7518543055df728c531006f56118543006bd6219131004fd70d8543066dc628c5310075f52d8d410aebc32d9131006dd32d8d41006dc62d8d410aebf30d9131006be52d913101cff7158e4100cfc705923106ede41d8d41014fe72d9131004fd7059131004fd72592310aebd30d91310efb43119131006dd6518d41046be71d913102cfc7559131006dd62d8d410ecfe7690531006de6518d41006f510d8543014fc72d8d410eebe4318543006dd51d8d410febd60905410aebc53d9131054fc7218543014fc7259131004fd72d8543006dd21d8d41006be20d9131006dc60d8d41004ff725913108ede71d8d410067f5259131054ff72d9231004fd75d913102cfe75d9231006bd10d9131056dd73d9231117d44118d4110dbd7290541054fc7518543006df6218d4106f9f4359231006dd60d8d41006bd20d91310079c648c531054fc7158e41006dd52d8d4108ebd43592311179c4118d41026bc64505310aedf3258e4106edf40d8d410d6df608c531006df6018d410adbe761913108edc30d8d410aebf32d913106cdf7359131024fd73d8543006de32d8d41006be6019131006bf50d9131004ff7559231006f710d854306f9f42d8d41006bc6019131006bf70d9131006df65d8d41014fe7258e41004ff72d85430f6f631d8543006f761985430ef9c431854300cfc7018543006bc50d913102cfe7559131116f54118543006be6519131004ff72d913101cfe765053101cff7658e410af9e4358e41006bf10d91310079d3219131006bf62d91310063d52d9131046bc42d91310aebf31d9131006df735913102cfc75d9131057d6718c53101ddc7359231024ff765053102cfc7558e41056de768c5310ef9c3119131024fe76d913102cfc75d85430063f52d913102cfc75d8d4100cfc70d85430067f52592310067d5259231025bc7458e41006bd4018543014fc7258e41006bc6519131004fd7258e41006dc6518d41006bd6519131006bd75d9131046bf4058e41027b76190541054ff75d9231006df20d8d410aede4358e4102cfe7558e41006de6218d41054fc72d92310aebc4358e41056be415923108cff735913100cfc7058e410eedc4318543004ff75d8d410df5f528c531014fe72d8d410df5d528c53106ede42d8d41006f721185430f79c43d854301ddc735053108ede74d8d41006dd75d8d41054f
  | 2 => 0x264000707808289a08064263a0003800000ae9c43d923106edc41d8d410aebd71d9131006bf7459131055bf7290541004fd725913106ebf40d9231006dc52d8d410079c639054111df77158d41006bd4058e41024fd731854300cfe7018543004fd72d8d410aebe73d9131006bc72d9131004ff72d8d41056f63118543006dc6018d41004ff70d8d41056f6411854308edf32d8d41046bf42d91310eedf30185430eebf6319131006bf621913108edf30d8d41006bf20d9131006dd20d8d41006de52d8d41006dc21d8d41006dd3018543006dd10d8d41014fe72d8543006dc70d8d41004ff75d9131006be42d9131056df618c531005df7350531014fc7259231006bf65d913102cfe75d8d411179f4218d41006de20d8d4106edf74d8d41006bd62d9131006dd6018d4101cde76d8d41006de72d8d410aedf6418d41056bc4159231006dc72d8d410afb431d9131006de21d8d410065d52d8d410aebc73d913102cfe75d9131055be7190541054ff70d92310aebe53d9131006be10d9131055de718c531006df6518d4102cfc75592310aebe32d91310efb7311913108edf31d8d41006bd70d91310aebc43d92310aebf43d9131006be40d9131004ff75d85430065f52d8d4108edc6358d410aebd53d9131006df10d8d41004ff7058e41117d74118d41006be62191310073f52d9131006bc10d9131006bc20d91310073d52d9131006bd601913100cfe70d8d4106edf71d8d410079f648c531024fd71d8d41006bf64505310aebe43d9231046bf41d9131046bc40d913102cfe7559231006dc51d8d41004fd7518543006de50d8d410079f6390541056bf7459231006bd50d91311073f5290541006df70d8d4100cfc70d8d41004fd70d923101cfd74d8543054fe71d91310f5f77159131006be60d9131006bc6219131006bc60d91310079d32d91310aedc43d9231006bd40d9131006bf54d9131006bd54d91310aebe639054106ede648c53106edc42d8d41004ff7559131006df53d8d41006f721d85430f4ff71591310067d525913106ede54d8d41006bf75d9131006bd40d92310aebd73d91310067f52d8d41004fd72d92310ef9f321913106edc648c53101cfe76d8d41024be76d91310acff7459131006be65d9131006bf6519131006df52d8d410073f521913100cfe70d923100cfe70d9131006bd65d91310073d521913106ddf735063102cfe75d8543026bc64905310079d4218d41006be21d9131006bc65d9131006bd42d9131006bf21d913101fd7618c5310eebc43185430af9c31d913108ede63d8d410067d52d8d41006f421d8543006bf601913106ebf425923101dde768c5310ee9c4318543024ff7659231004fd72185430067f5218543004fd75d8d410067d521854308edf3059231046bc6459131004ff7259231006de601
  | 3 => 0x1b2301400012a75c24280280c0000018387c00039c89a1100184000c06820001800848040000808002700008026e084bda803018000000108084e811600028062c80000040c8040400018000680042cce684061a416961001c34080f030001e1d834000101a0018040000c060105828087a0000460002f81034a7000040a0009800004a170242e2810138087a08800019600004062a011300e09020080b6e000e00c7d0011c758f000040c00050980001748fc000007030060600000320102d40042c00584c8043700000020e800042c04350143300000044c079f4000039000181500830d601028207c00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa3d85083644c40317f0ea06c918856a7a0e70d91310051ec2ce5b226200cbb709c3644c4014bd0a10ec6a08038b18952d91310045fc3ac4322623aab7845846150c0117f08baac8988dba510f211854313f0e21aa5b246200a3e85087644c401c5ec4a90c89880297a1721d8d410054ec1ce1b2262008bd87143644c4011bd0e10ec6a08161f21570185430051ec2cc43226202c6c72549648c4014bb0b906c6a0836a7a1020d8d410052e42ac1b1a82008f7815c9644c40147d0a310c898847279db63905410054ec2041b1a8200a9d84994635044953d0db2462988028fe1510d91310066db84e1b1a8200ab581143644c401c9f04a96c6a0802976166218d410052f428e5b1a8200e4c6254b63504014bb0a310c6a0802a7e0d621913100c5fc3a81b226200ace82994635042b53d06106c89880b1b1c952591310055ac2043b0a8600a3e85c87644c40159f04b06c6a08029721510d8d410051e42ac1b226224a9e864c8644c40187aebaa6c8988029761632d8d410051ec2e41b226200a9f8448763504058dce4a90c2a18029761721d8d410046ec3cca31a8200ad681083635040153f08b28c6a08029761421d8d4100566c14cbb1a8200c6d725486150c4953d0ca10c6a0802a7e116018d410052f42c65b1a8226c5f73549644c4039b4e0986c9188a387d8f52191310052f42cc5b1a8228c5f73d49644c42b93cedb246298803a3d894218d4101c6e41ae430a8600a5e85c8363504011bd0e286c6a08c2b5e056218d410062ebaea7b1a8200a9d83083644c4159c842b90c2a180297e1560d8d4100578c0043b0a8600e2d52483644c40155d05328c898896ad60660191310047bc3ac230a8600e4d52483635041b53d09086c6a089b87d8d521913100566412c031a8200e2c62548644c40147b0a310c898856a7a0c72d913100727b12a431a8200a9d8498063504011bf06baac8988028f61472d913100717c12a5b226200a3e85988644c40187aea3aec898877279d932d913100556c14ca3226200a9d849c3635040153b09310c6a080237e1d6518d410051ec2e43b22621da9e83188644c41117b0e10ec898802b3a0a65d8d410045f438a1b2262058bf87553644c40793cec31c82a08028f61421d913100c6fc3a61b1a8200a5e8518863504018dee4a92c8988072e9c140d923100556412c1b2262008df8758063504015ab02106c6a0802ada0420d913100566412c1b1a8229c3e76d48644c40153b0610ec898803931895218d410052ec2ce5b1a8200e4d52c83635040147d0b216c8988022f61e62191311c70e21ea430a860da9e841cb635040153b0810ec6a0856a7a0c50d91310055ac0841b2262008bd87980644c44f87ceca90c8988323721d21d8d4118c6fc3a43b1a82028df874cb63504014bd0a106c6a08022fe117059131
  | 1 => 0xd0a316c8988028f21560191310051e42a21b22620da9c84487635041b53908986c918802abe0960d91310054ec18e5b226200a3e85c83644c4014b90ab00c6a08022fa1c20d91310046fc3ac431a8232c9e7650b635043b53906a00c2a1802a760e10d91310045fc3aca3226204c9e76192314c46bd2886880c2a18028fa1472d913100567c12c031a82038bd84dcb6150c291790e90ec8988123760f72d85430ac5f43c21b226200a9d84143635046fc3886a90c2a180237e0d72591310076290843b1a820087d85dc36150c01d1ec4990c898802b6a0021d8d4101476412e0b226200a3f85583644c4151790ea12c9188b70f9db52d913108c6ec3843b1a8200a5e859cb635040159b04286c6a08022f61c20d91310045fc22e4b226234c5e76d4b635042b53d0610ec8988022f61e10d91310052f42cc431a8200acd82994635040159d04286c6a08072e9c140d91310062eba8ebb1a8200a5d8598b63504011df04b82c89880637e1d30d92310046f43841b1a822aab781588644c4015b30010ec6a0802b5a0450d8d410054ec20e5b1a8200c9c435cb648c401c5aa5906c8988023761e6018d410052ec28c5b1a8200aad82143644c42353d09386c6a0836a7a1021d8d410045fc3ac032262008be87087644c4010ff0ab82c89883637a1e10d8d410054ec1cc03226200aac82580644c401c5ec4a96c8988023761e6218d410ad4f41c21b2262058df8754f635040153f0690ec89882a3d205721854319e2f3b2a5b1a82018f7874436150c014bf0ab00c6a0802a760c50d91310145fc3a85b22622fa9e841886350401d4a4210ec89880395d4651d8d4106e4e326e6a0a6200a3d8590b644c4015390c990c8988029761420d8d411661f3b2a5b226215a9c83487644c4015730010ec8988bab56066018d410046ec3841b1a8200a9d83994644c4735af06b08c2a189f87d915218d410051ec2cc5b226200aad82997644c4031bd0db9a8298802aba0850d91311254f436c720a820587e85dc36150c53c3887a96c91880237e0d70591310043fc2ae030a86008dd8714363504015390ca10c6a088aa721130185430054fc22c431a82048bc845c86150c0156d02286c8988023761e10d8d4114f0fb26a431a8200a5e8518b63504058d8e4a92c72080297e1510d8d410055d40043b226215c9c73d91414c40155d0532ec8988031bdc952592310054ec2421b1a8200ad58114363504014bb0a396c6a0856a720d40d92310051f42841b226200a3e8598b644c40147d0b396c898802a7e0d60191310051fc2ac03226200e4f6254b635040193886b90c2a182a3721d3258e4100e6d38261b1a8200aaf82580644c40153b07310c8988161f21570591310056ac1843b0a8600e3751947644c40153f06b28c8988028f61462d91310045ec3cca3226200
  | 2 => 0x2101480c0e17000001e2a05854021f01058040600c582e18000b45c00010941076050880226018283600048b012030100c24240580860000000c580e06a5c0a01090480218010e04000118a01aa80104c1400000000011000cc06152602c080917004167e0003c061b00038940379836a7a1050d8d4100637b92a4b1c822b8bf87487644c40147
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2000049c842110d72185430070310d725486150c498948110d7218543
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0xb49
  | 7 => 0xb4b
  | 8 => 0xb4d
  | 9 => 0xb4e
  | 10 => 0x2
  | 11 => 0x1449
  | 12 => 0x144b
  | 13 => 0x144d
  | 14 => 0x144e
  | 15 => 0xb89
  | 16 => 0xb8b
  | 17 => 0xb8c
  | 18 => 0xb8e
  | 19 => 0x1489
  | 20 => 0x148b
  | 21 => 0x148c
  | 22 => 0x148e
  | 23 => 0xe89
  | 24 => 0xe8b
  | 25 => 0xe8e
  | 26 => 0x144b51
  | 27 => 0x144b53
  | 28 => 0xb5453
  | 29 => 0x28c
  | 30 => 0x184c
  | 31 => 0x148b91
  | 32 => 0x148b93
  | 33 => 0xb9493
  | 34 => 0x24d
  | 35 => 0x16cd
  | 36 => 0x58a
  | 37 => 0x28954
  | 38 => 0xd5455
  | 39 => 0xd5494
  | 40 => 0x1a1455
  | 41 => 0x1a1494
  | 42 => 0x29554
  | 43 => 0x28b
  | 44 => 0xd4d
  | 45 => 0x1a0d
  | 46 => 0x24955
  | 47 => 0x188c
  | 48 => 0x25555
  | 49 => 0x24b
  | 50 => 0xd0c
  | 51 => 0xd4c
  | 52 => 0x1a0c
  | 53 => 0x94294
  | 54 => 0x154294
  | 55 => 0xd4294
  | 56 => 0x1a0294
  | 57 => 0x25455
  | 58 => 0x29494
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 508
  | 6 => 509
  | 5 => 281
  | 4 => 3
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/48+packedAt gbK8 (1612+(h % 48)*6) 6) % 62)
  | 7 => 2*((h/190+packedAt gbK7 (18796+(h % 190)*9) 9) % 508)
  | 6 => 2*((h/225+packedAt gbK6 (24432+(h % 225)*9) 9) % 509)
  | 5 => 2*((h/100+packedAt gbK5 (16579+(h % 100)*9) 9) % 281)
  | 4 => 2*((h/8+packedAt gbK4 (210+(h % 8)*2) 2) % 3)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fffc1f01f83c3ffe1ffe01fc3468cfc41f3f3
  | 1 => 0x83807e001ffffc1ffe0fffe004b973607e7cfc
  | 2 => 0xfc007fffe003ffe1fff0fffff8c18387878f1f
  | 3 => 0x7ffffffc0001ffff00003f01fc07f80fe0
  | 4 => 0x7ffffffffffe000000003ffe0007fff000
  | 5 => 0xffff800000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x487405105a0c132609920458102042c40b171
  | 1 => 0x81090a000a854404a2024ac0801831601a54b4
  | 2 => 0x681014a620022a411520951a18c18281850a0a
  | 3 => 0x2022673b53680111d9cc01832f01dc06e80fc0
  | 4 => 0x404479cd9c73b3980088060c37ee000777e000
  | 5 => 0x7278000e00402200110018103ef5ebd0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_41616
namespace PEqualNP.Outside.L_meta_41616
open PEqualNP.Outside.L_meta_41616.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 6 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 56 := bs0_3_0
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
theorem bs0_4_768 : Interval s0Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 781 := (concat (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 bs0_4_288)) (concat (concat bs0_4_384 bs0_4_480) (concat bs0_4_576 (concat bs0_4_672 bs0_4_768))))
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
theorem bs0_5_768 : Interval s0Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 801 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 bs0_5_288)) (concat (concat bs0_5_384 bs0_5_480) (concat bs0_5_576 (concat bs0_5_672 bs0_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 44 := bs0_6_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 15 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 85 := block_range (n:=85) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 85 := bs2_3_0
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
theorem bs2_4_672 : Interval s2Atlas 4 672 82 := block_range (n:=82) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 754 := (concat (concat (concat bs2_4_0 bs2_4_96) (concat bs2_4_192 bs2_4_288)) (concat (concat bs2_4_384 bs2_4_480) (concat bs2_4_576 bs2_4_672)))
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
theorem bs2_5_672 : Interval s2Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_768 : Interval s2Atlas 5 768 11 := block_range (n:=11) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 779 := (concat (concat (concat bs2_5_0 bs2_5_96) (concat bs2_5_192 bs2_5_288)) (concat (concat bs2_5_384 bs2_5_480) (concat bs2_5_576 (concat bs2_5_672 bs2_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 44 := bs2_6_0
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
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 99 := (concat bs3_4_0 bs3_4_96)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat bs4_4_0 bs4_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := bs4_5_0
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
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 396 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 601 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := bs5_6_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 89 := block_range (n:=89) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 281 := (concat bgb_5_0 (concat bgb_5_96 bgb_5_192))
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
theorem bgb_6_480 : Interval gbAtlas 6 480 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 509 := (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480)))
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
theorem bgb_7_480 : Interval gbAtlas 7 480 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 508 := (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat bgb_7_288 (concat bgb_7_384 bgb_7_480)))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0feeeeeeafce8e8e0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071594 * 2 ^ 32 + 4243122400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_41616.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.and,[1,7]⟩,⟨.or,[0,6]⟩,⟨.or,[2,5]⟩,⟨.and,[0,5]⟩,⟨.and,[1,10]⟩,⟨.or,[9,12]⟩,⟨.or,[2,8]⟩,⟨.or,[11,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4243122400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4243122400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_41616

open PEqualNP.Outside.L_meta_41616 in
theorem PEqualNP.Outside.L_meta_41616 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4243122400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4243122400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
