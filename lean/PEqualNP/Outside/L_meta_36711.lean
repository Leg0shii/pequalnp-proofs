import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36711.Model
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


end PEqualNP.Outside.L_meta_36711.Model

namespace PEqualNP.Outside.L_meta_36711
open PEqualNP.Outside.L_meta_36711.Model
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

def SBf (j : Nat) : Nat := [3, 6, 8, 6, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36711

namespace PEqualNP.Outside.L_meta_36711
open PEqualNP.Outside.L_meta_36711.Model
def s0K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (i*4) 4
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (5+((h/1+packedAt s0K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffdfc7fff87ffe3f
  | 3 => 0x6bf878ff8783cc
  | 4 => 0x73ff80fff803f0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffff8041102888a8d5
  | 2 => 0x20b2245455522a
  | 3 => 0x1517459d461b4c
  | 4 => 0xe2476e66463b0
  | _ => 0
def s0Atlas : Atlas := ⟨2,rawDecor 30 s0Pos s0Neg, 0xccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36711
namespace PEqualNP.Outside.L_meta_36711
open PEqualNP.Outside.L_meta_36711.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xa80258004180ec42406014088000df31f631dd31f531d531be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x6900000308e8204a000412aaa718d514131ca98c819531102aaa218714c620e298841a840082aea7085554c10
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x420290604c440b018131083813110020
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 10
  | 2 => 3
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
  | 4 => packedAt s1K4 (228+((h/4+packedAt s1K4 (208+(h % 4)*5) 5) % 22)*5) 5
  | 3 => packedAt s1K3 (282+((h/3+packedAt s1K3 (270+(h % 3)*4) 4) % 15)*5) 5
  | 2 => packedAt s1K2 (116+((h/1+packedAt s1K2 (114+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x3f807f807fff00fff80fe07f07ffc0fec47c7
  | 3 => 0xfc0007fff807ffffffff0007ff81fffff078ff
  | 4 => 0xfffff8000007fff00ffffff80001fff03f80f8
  | 5 => 0xfffffffffff800000ffffffffffe00003fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2408304850501121208b1628b08a2c92459b5b
  | 2 => 0x615552d534a328ea47c0aaa5546d558eac45c5
  | 3 => 0x4b46a4a4a5354a4c8b5581066d219b2d3068ae
  | 4 => 0x7264c6c6c6c68c88ede6cdb40849e3c63e80f0
  | 5 => 0x8387070707070f0f0e78f1c78e7102083b7600
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36711
namespace PEqualNP.Outside.L_meta_36711
open PEqualNP.Outside.L_meta_36711.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x1e52380803000022004c6213e1c79b2c0001d009d500003411c0c41223005c200220059234654264a0000a5621014000ca890a0c10410c0004100050103ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x881be501027ca0206e94040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730dfa0e61bd41cc3be6398774c730df20661bc40cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c61bf418c37a8318778c630ee18c617e508c37c81186f10230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4987bd4930b7a92617c524c3d8a4985b14930bfa8a61f7514c2eea2985f14530fa28a6174514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea9061de320c3b864185f94430bea8861bf410c37a8218778c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c837e83906f50720f790e41ed21c837c81906f10320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef32883d865105f94620bea8c41bf418837a83107b88620f610c417e508837c81106f10220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53482fea2907dd4520bba8a417c51483e8a2905d14520dfa0a41bd41483de42907b48520df20241bc40483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef32083d864105f94420bea8841bf410837a82107b88420f6108417e500837c80106f10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c437c81886f10310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21bf418437a83087dcc610fa18c21f721843e843085f94210df20421bc40843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd414437c80886f10110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2086fd0410dea0821f731043e862087dc8410fa108217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xe435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef19663dc32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31f7294636e528c6faa518fb54a31b6a94637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7bc6498f70c931dfa0a63bd414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87de6590fb0cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53887bca710d794e21bea9c43dd53886baa710df14e21bea94437e518877e8310ef50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f799243ec324877e8290ef50521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf290437e510877e8210ef50421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40bf296817d52d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c817e509037e81207ed0240dfa9c81be539037aa7206f14e40dfa9481be529037aa5206f14a40df99481be329037a65206f0ca40dfa8c81be519037aa3204f54640de28c81bf319037c63206f4c640de18c81bf219037c43206f48640de10c813e50902fea6a05f14d40bfa92817c52502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53102faa6206fd0c40df21881bd431037886205f94840bea9081bf421037c84206f50840de210817e51102faa2206fd0440df20881bd411037882205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28881bf311037c62206f4c440de18881bf211037c42206f48440de10
  | 2 => 0x3acc71b12be0fc1f26f3fe13d05a3e4ea7684285b3368b8158c325eaf94d18861ec70260040202c0602e01004000020c800000060280408064070000180a000060081e0500002800000280482c02004038041a802010000900c080000a80628006078000003c0000002002028000f0000a0181580c07800028401280e028000707e0000007008000060c82a0285406052088281300c000101500000006000000081204000060020301203004030160d8040280002806000640c00c0302c008020001e0003c0300a0100c000180300201816038340f0180180e02800000200100a2b00a0281c000060607c0182801032098060384e0000200816088120200c0180a02808010360180c0180c060140100002058018000081e000180084c050000302800004000020e802008000202a0c00e00000030540080001804108540080e0100802012000160000c0080c0201003006010060006a030000200a090840000000002000000604a008080d8000080200df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250fdea4a1dbd4943be29287ec5250ed8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855f5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997bd0b32f6216657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cbbe86197710c32bf29065ef420cbd8841977cc832f719065dd320cbda6419734c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83b
  | 3 => 0x2504e00c19d4262c40f2e0460000001570e25492d1c3244019821cc21c2fc6e87b0ceae4622893926d4e81b92b2c44808543d00985a0da4c43a094a472244d8c384e50a1c92c9cd2c8b148396639e40cc490f000210de866000a7d6e84b4f05c44a1ea4ec1d84c8e95c49815e11711a588f125d5ac80800000548001900221481cd721df0003c83d0001646a80009262a3b07102361c6cc9e15532c9fd278de4e05fc852ba55e6f8800d70000016714054e3e0a41d94ac2d4898b856611c69a732da5b084a830b86ac003092ca165518645d078cda236520bc4b19545b4c18ee2876363a84db1a33220cc020d0e8074a72990fa1b8168a502a1fc2ea3c18a0008b0b744ab98569a8322ab58f8655228bd4b027222180010cb318ba40009307200000000000364f21ad5c6418a59045085753b8c92f2a001d8e65d68380b1501766403780f1f60000027d000001501335b83e8b70313a8bb4eb23b0143557fa1e0000a1530ae4361f8c30a92c0814ca15e2fa305859e11c2348002a940622d7ea9210e0409f969000000000001c06fc4780025ca54002cf2540dd46ab11f2748e725e536480d48c62ec9e434889246805318412a2408958f30682185b18d194bed120ce44c8b4409140d85616ca6b000000e32b459a79d088fd40c1a8cf83659438c8f2a8308b30c92390664151faf612c8603ca4443e2e40890b0169209dac41145f0002ae49a72000000000be000000000000000001ea940000005d8a85818000003f14416b62c0904d1e50060000024b3c000000000000001792423fc000eb80c1380007294f094000a183c582350002333de0000000029a6ed4ba3d1b67e0001354b8824292d53b6c04222670909d12d89d5864711412440e0056414143ab609bab223e5f8ef1e9462aed7f00038a3d0f80000004e8049b63d8654e50982b81008817a4e2b9c9617435c0016d9081462092305f50c118002bd4466797a81f00083d4e0f02184c121a5852614c8c800000000000000744b4b400063cc6410038570b24178000b0000d2000000320fc81a2e08ad2ba2900a0002491d17c0016a0ac236558000f60000c80013d000b40989af04a000e00564e46e86c0004801ac0e01b140000000e702433589000000c61040620005dc002ab1b80008a8003f43c4002b74a604d451b25a23b9410a600064cc1ac734c49458251000220000004d2584b98b3264525898422b400000043180000b91ac24c0d53530d4f63082baf04a4000001fb00051c0019a47427940890482238150d10009b0002490002a0000005ca72d22a980000012a9f40005115a9452a659d108ab1de000bc07053ac40769d80288a8069d131e3dc5d2610c60018ea1a0000000008c000831529d30004604bb1428c001838df3301e02f000604391080a24240013e03d00065ce12df40
  | 4 => 0x4588593d2b0346a2d5b1a53ea9f8000003dcb84002c63e2245370000f80009c9dd0000003094a0005084a84c0000010e0515aebcc50a4c000bb8c10af1fc1545e98b13e8d10b9a105800169800000000fb800000b00040d65e888010afc000530001b0000000c28000527114f21446a6e12a1f300000147b0a00056c3b80051c6282d0004d00000016f0005ec002bf4dac01658000001b56f2a2000000000754948891382e34e6042819c3aa5a8dba5f24ebe46380e3ec29c8d28c5ee7b4662652ea33c26b17610828020bc0004349a1fc27c71c681215a4be90c9e6528ba8de2aa4cc2a977830470854f58ff46e01c0bac208ac315623260a938d11a04c8810e09fd1001a00c9f2
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xc404831c5310120cdd4440483345110120d314e204836451881209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209b594320834d530c8208f992510823d6494420cd94541083355150420ae181410826d6588420b398e210826f6548020b318d20082e461480209ed95200823e64d4f108f59353c426e62d4f109b58b53c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c433561d5210ce98354843356115210ce980548423e6494e108f592538423f6454e108f191538426f6254e109b189538423e6494a108f592528423f6454a108f191528425f6354a109718d52842ba60d0610ae18141842b56190210ad584408423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414423e6590110c7d4e404431c5390110cbd4a404432c52901108f994404431f5310110c714c404432f5210110cb14840443545384110d914a104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d5185530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520423e64944108f592510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410435553cc4109d594310436552c84109d594210423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400427965840109dd9510042d46344010b918910043b040440109ed9510043b34144010
  | 1 => 0x2ba60d4440a798c511029d6314440ab98851102ad6214440ae980511023e658c4408f59631102ae628c440ab58a3110335518c440cd54531102bb604c440ae181311023e650c4408f594311023e65884408f596211029e6388440a758e21103355188440cd54521102bb6048440ae181211023e65084408f594211033a60940408f58654cc23f61553308f99251cc23d64947309b98a51cc26d62947308fd9741cc23d65d07308fd9541cc23d6550730ae18141cc26e62d52309b58b548c23e6494a308f592528c23e64946308f592518c2ce628c6308f587544c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c23d6115130cbd53524c32c54d4930cbd50524c32c5414930cdd53514c33454d4530d9d4b514c36452d4530cdd93514c33464d45308f990514c23d6414530cdd50514c3345414530d9d48514c3645214530cd990514c33564145308f997414c23c65d0530cbd4b414c32c52d0530cdd47414c33451d05308f995414c23c6550530cbd49414c32c5250530cdd45414c334515053097997314c34c52cc530d5147314c34c524c530d5145314c23e6590130cbd4a404c32c5290130cdd46404c33451901308f994404c32f5210130cb148404c3375110130cd144404c34c528c130d5146304c26e62150309b588540c27661150309d584540c23e6494c308f592530c23f64548308f191520c34d520c8308f992510c23d6494430cd945410c3355150430ae181410c25d658c430b398a310c25f654c030b3189300c2d4614c0309ed95300c23d61953208fd8554c823e64d4f208f59353c827661d4f209d58753c823e6414f208f59053c823e64947208f59251c825e63947209758e51c823f65d07208f59741c823f65507208f59541c82b860507209798f548825d63d52208f993538823d64d4e208f992538823d6494e20d3d4c328823e64946208f59251882ce63886208f587544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6115120c7d53534831c54d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f191534826f6254d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f514833764d4520cd193514823e64145208f59051483375414520cd15051483575314520d514c51483366414520cd590514823e65d05208f197414831f53d0520c714f414833751d0520cd147414823e65505208f195414831f5350520c714d41483375150520cd145414826e65c8520d314f214836451c8520d314d214836451485208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4
  | 2 => 0x5214941ad98732506b561cc941ad98632506b5618c9418fd95325063c654c9418f994325063d650c941e34c8325069f6354141a718d50506af6254141ab189505063f65504419dd95411073654504419b98854cc66d62153318fd9152cc63c6454b31d354832cc63f64543318f19150cc66e62d52319b58b548c63e60952318f181548c66e62152319b588548c72e5494a31cb552528c72e5454a31cb551528c72e52d0631cb54b418c72e5250631cb549418c74e52cc6318fd91508c63c64542319bd89544c66c62551319ed81544c67860551318f990524c63d6414931b5986324c6ce628c5318f993504c63d64d41318f596540c63e60950318f181540c63e64150318f992510c63d64944318f597410c63f655043197d95310c795414c4319dd95310c63f64540318f191500c66f62540319b189500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c874d530cb218fd9150c863c64543219798f548865d63d52218f982548863c60552219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e21c794f418871d53d0621c794d418871d5350621d394f218863f64542218f191508865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e6414d218f590534866e65cc921b9987324874d530c921b398e214863e64d41218f593504863d65950218f982540863c60550218f990540863e64d4c218f593530866e62d4c218f990530863d6414c219e98053086796014c218f992510863d64944219798e510865d63944218f597410863f65504219bd9521087a541484219dd95210863f64540218f191500865f63540219718d500873551d0740c794d43902af6250e40ab189439029f6350a40a718d429032e5250a40cd54541902ae62d4e40ab58b53902ba60d4e40c7d4e53902ba6014e40a798f529029d63d4a40ae983529032f5294a40ae980529023f654ca408f195329023e650ca408f594329038d320ca40ae983519029e6314640a758c51902ae6214640ab58851902ba60146408f996319023d658c640ab98a31902ad628c6408f994319023d650c6408f996219023d6588640a798e219029d63886408f994219023d65086408f997415033751505409bd89531026c6254c40abd8943102ac6250c40c754c431025f63548409718d521029f6350840a718d421032d5210840cd547411023d65904408fd95401027b6550040ae98353102af6254c40ab189531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae98053102ba60d4840a7d8d521029c6354840a798c521029d6314840cb54852102b66114840ad58452102ba60148408fd95321023c654c8408f994321023d650c840e34c8321
  | 3 => 0x3a8001e8360c316907c000001ab4b06f0000190005480029d01810c0580200001800400801000004018030000040100301a00c00813058040030000100200080000400000011002028030010180100400401201400036016014008000000200000e00a008040000000080080d0160000f8020140040000700000000000004004000050060000080201c0141f0010020080000001e0400300900002c0100000203c2303d0000040000d00000c008080100000080001000c0000000e00c0280e01a00c0180000201003800008034000000000000500d0020000282d00600c0000100000400005008004000020120540c0000000040300f00603400000000018060180020100480000a00c0101000000c000030080040a80000c01c0f0000060080680000a05c0180300602c010070040480000d000014020010040000300000e0100700100e0340000400a0000d008004010020020080200000300403c010120000080880500000c0800f00201000006002004018000060800380900c0040080500e01b4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3e64947328f59251cca3f64543328f19150cca7661152329d584548ca3e64946328f592518ca3f64542328f191508ca3d61d51328f983544ca3e649513297d8d544ca6f62551328f994544ca3d61151328f980544cb2c54cc932c7152324ca3e64145328f590514ca3e64d41328f593504ca3d65950328f586540ca3e6095032c718d540cb2c62550328fd85540ca3c60550328f990540cb1d54d0c3297594430cacd6210c32cb553420cb8f43d08329b594420cacd6310832e310c420cacd638c83297d95320ca9c644c8329bd95320caac644c832b3d95320cb4f654c832e3d91320cace644c832b3191320cb8c644c832a3191320cb8e544c832e3551320cacf614c832b3181320ca3e64944328f592510ca3f64540328f191500ca7761540329d185500ca6f6254f419b18953d06af6250f41ab18943d071d5310f4197d8d52d065c6354b41a7d8d42d069c6350b41cb54842d06b561d4f41abd8953d06ac6254f41c754c53d06ae6214f41ab58853d06b56114f41ad58752d069f6354b41a718d52d069e6314b41a758c52d072d5214b41ad58452d063f654cb418f19532d063e650cb418f59432d078d320cb41a798f50d069d63d4341ab98b50d06ad62d4341c714d43506af6250d41ab189435069f6350941a718d425072c5250941ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506b56194941a7d8d525069c6354941add8552506bb6054941ae181525072d
  | 4 => 0x6c000a12924c85d2c00002500000000001c72000000c1d4619b00090c971b900000180000416114001a000000148262000834400004e0001810bb09e4086d000082000912cc0609d14c8005dca7cd297e00077c23b052b26294484b4a83a8128950f02988b1b03e6480000001124d4e786f47a288140000a4990798310004e101864474970000003420f17c80029e000b2a94000034e9800072ab8f213b4249b11196a0003f47b0001f857ce2ac8576061690004440011b0001e00002403a4fab0c7099a1bc9b400000000b44000132cc3045988534c4282a1680363816322b16e37c6aac9496018f40110804b4e916227e58c3125109ca7045aed046b9c0a9bb284231759545ae338f109253c0b8998ee000000c71460001b02e1183b2a6178aff5745cc1007c29441c549d60d028c3eacf0b2ab184aa9094484fe22d19251d299294dc2952d8a41e293813a28000b714ba7c2ae880fd80048c25c7f80050c4e48210f40247d399b85700009d12b414000000f20067f81611c2aa3e0ce9af54e9a95e9230004a8678012ce4bcc98515f00996d2310669c40016d248000002b7374670fba1e0140b448a1614e260150be0ae0d93c08f000000420003d862cbd80017827579abe00085cea903418001568000003115317800079c610750000000000049e87c4e17d16a59000257286744600002b42a00000032e001468002dc5d5429940000010d17000007400000000000cf0000005fc00000000000e81102a07a8000aa000000001991ea47545a92000000c1282448a280bac25625349310c2c03bc1d9e148ab5400000000000000873686444f2130008204f9e00002e40000059a8605600001c9ac5c00019a9801a8c7306000558005481d00000056a000000000000010e000000ad9401f541ea88769c027a0016c8001f60013b0e20c61b43700032472000177000bbd408003b4000688000000081b8904b456c350730009fca58002de00000000358a0cc41a80000014d01a4aa0145b05d0be6fd7195c32c0004caa54b2544f58000008c0309e34ca00000000000000000000d2bd0002f7000041652d45225840000017a000001f0000aac382db1620002d80023ca1c001e63dc97d070cb21207c4114020c8cd823065ac000002fd53619c002102f863133ae02220000e1135f67391700010c0009a03f05e238eeab90083e5038164a46255f8813a8130962695be1615e21452c048282195965b06ea062988dc718c84cc0893f2415d8a553d87a5d2b743b0fa15e084d21723540003b9f93528d0729981a01e4a9a3e1b20a53b8a03f4024691bd09a7a52105617e3a46509651e634d88e61681c95923c48e001681b356620d740d31b6448e6a40000404001d7000b78e21f10008a4d12af2827fd7b04200000075800472370939f824a5212490d110825
  | 5 => 0xb04000145f43b1028004f4450ee1565d48104685e01e7940005300045c7f2b40007f49b8c64d070d84202000000e60d45b0180daae200072c0000000069c4981e2344f9698002e86dc00000000940e09c72167b46b0005460000023f0000002d0460006b4001f4400000bc90e000455670c32ec7bc15a27384911192e42baa103300000035c002e100000073800000001638004941f9179f24bca20001ae46a000ac0003b6414a28b02d69591d9360fe3a0000f74540010d800498000db000200000041ca0000001c1b2000614a700032a9c80006b164314ec044616ac08c80049ab1400000000984450003004f0000492bc000c80cc15c51000000136aa11609a0000002a984048420b8a110ca001780343bcb953c9a351cbf856a2638cb10c79c933e1ed8187107a9740000037c8840000026298d1c2e60004c17e225000000002a0064c298621d490bd4000005e461d498000007d95097a000aa937b0142a00000000000000940003024
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x80002edc00c342930946000002c00000006502744543811ec83000038e335495a9e42006b6606c2285ed172c16000000a0d2113ab402b3e0000824c5490304ca0201000800704086820000383028c001c18c6312a81948e74991320ca46b88c899065239c0644c832918ed2a2641948c76551320ca86392a621e83431cd5210b41a18e4a98a7a0e0d5358853d068639aa4296838358d5214b41a18ea99065a0e0d654c832d0706298c4a1a838318c5250941a18e4a98a6a0d187054c535068639aa4292834a1c15214941870e0b2864a0d0c754c832506863a2a419663431d1530cb21a18e8a986490d487054c3248707298c4a1c818318e5250a40a1ce5a9ca72050e73d4a5290287baa6419481431c95310c40a18e6a90842050c7254c5310306a9ac4298818554d6114c40a18e6a90a42060d635485210312a92c2290810d5c4654c840a18ea990642060d654c83210312b12a3188818558d5188440a18e8a90641863151181410c2873a6a619441431d1530c820c62a2302821063161983548430c298c0a0a218a1486050510c2aa6b0880086255258440043483188088021a81884044010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xa00802406000000885811da544c83280c87595320cb41a048254d6114c40a04835496114840905811d5320c84080c87595320c840
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 6 => packedAt s2K6 (788+((h/14+packedAt s2K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s2K5 (24297+((h/267+packedAt s2K5 (21627+(h % 267)*10) 10) % 962)*11) 11
  | 4 => packedAt s2K4 (32538+((h/260+packedAt s2K4 (29678+(h % 260)*11) 11) % 1031)*11) 11
  | 3 => packedAt s2K3 (2870+((h/18+packedAt s2K3 (2744+(h % 18)*7) 7) % 74)*7) 7
  | 2 => packedAt s2K2 (368+((h/2+packedAt s2K2 (360+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff81ffffffe07ffffffff81ffffc7ff1ff
  | 1 => 0xf81ffffe07ffffff81f07c1fffe1ffffa23e3f
  | 3 => 0xffe03ffff80fe0fffe007fe0fffe1e03c3cfcc
  | 4 => 0x3ffffff000ffffff8000ffffe003fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x882808c4122400016509421280222a80cd0d5
  | 1 => 0x924519103244986580a4291a53215551a2262a
  | 3 => 0x2149aa2490e909aaaa084f489d54181ac34b4c
  | 4 => 0x859634492481d2d34d3d0210e6998063740db0
  | 5 => 0xc6183871c70e1cfc71ce739c07111183fbb000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88ee888888eeaaaa88ee888888eeaaaa88ee888888eeaaaa88ee888888eeaaaa88ee888888eeaaaa88ee888888eeaaaa88ee888888eeaaaa88ee888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36711
namespace PEqualNP.Outside.L_meta_36711
open PEqualNP.Outside.L_meta_36711.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xa1660240a288033808001bdf43dc43df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x68108e2a26538505069aa598d354830
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s3K3 (111+((h/1+packedAt s3K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fffe07ffc0ff07ffffc1fff03fe07e7e7e73
  | 1 => 0xfc1ffffffffffff81f03fe0fffffffff918fff
  | 2 => 0xffe07ff81fff07ffe003fff0ffc1ff81e1f39c
  | 4 => 0x7fffe00007fffffc0000fffe0001fe03e0
  | 5 => 0xffff8000000007ffffffffff00000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x48430231448521016514c0513213212c263631
  | 1 => 0x11042442091082280a41120a44644a509088c6
  | 2 => 0x28894890d2242d52a09265609a919505615318
  | 4 => 0xb2d6712483b6b79cd3d83148ef390619fa03e0
  | 5 => 0xc31861c71c38c6e71ce3b98c0c201861ddec00
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36711
namespace PEqualNP.Outside.L_meta_36711
open PEqualNP.Outside.L_meta_36711.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0xf80542400b0045480000001d00546903c380000000000580000c2c816af5028012361411900000141e0170748002000000000005d12742000a53068180002000000ac0004c00000000000000009804670006000000080060008108040051a00002ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x617e510c2faa2186fd0430dea0861df310c3bc6218774c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030efaa061de540c3baa8187715030efa9061de520c3baa4187714830efa1061de420c3ba84187710830efa8861de510c3baa2185754430ee28861df410c33e82187790430eea08619d410c3b8821877c8430ef10861dd210c3b842187794030af28061da500c3be80187790030cf20061dd400c3b880186710030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20bf28e417d51c837e83906f50720ef98e41dd31c83de43907b48720df20641bc40c83bc6190770c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106fd0620dea0c41df31883ba63107b88620f610c417e508837c81106f10220ef18441dc30883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a4174514837e82906f50520ef98a41dd31483de42907b48520df20241bc40483bc6090770c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841bf410837a821077cc420ee98841ee21083d842105f94020df20041bc40083bc6010770c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c43be6388774c710df20621bc40c43bc6188770c310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c21df53842bea7085f94e10bea9c217c53843b8a7085714e10bfa94217e52842faa5085f14a10bea8c21bf418437a830877cc610ee98c21f721843e843085f94210df20421bc40843bc6108770c210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd41443be6288774c510df20221bc40443bc6088770c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821bf410437a820877cc410ee98821f721043e842085f94010df20021bc40043bc6008770c010fb88021fa10043ea20087e44010
  | 1 => 0x721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa0a43bd41487be6290f74c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421ef98843dd31087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40bf28e817d51d037e83a06f50740ef98e81dd31d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c81df31903ba63205f94240dfa0481fb409037ea7206f94e40dea9c81bc539037ea5206f94a40dea9481bc529037e65206f8ca40de99481bc329037ea3206f94640dea8c813d5190378a3206fcc640cf98c81be319037a6320674c640de18c81bf219037c43206f48640de10c813e50902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c52502fea2a05f14540dfa0a81bd41503be62a0774c540fda0281be40502fca8205f94c40bea9881bf431037c86206f50c40de218817e52102faa4206fd0840df21081bd421037884205f94440bea8881bf411037c82206f50440de20881df31103ba62205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28881bf311033e62206f8c440de988819d311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc2fca5985f54b30bf28e617d51cc37e83986f50730ef98e61dd31cc37c81986f10330bfaa4617e548c2faa9185f15230bea9c61df438c3bc87187750e30ee21c617e528c2faa51877cca30ef19461dd328c3b865185f94630bea8c61bf418c37a831877cc630ef18c61dd318c3b863185f94230df20461bc408c3be61187ecc230efaa461de548c3baa9187715230efa9461de528c3baa5187714a30efa1461de428c3ba85187710a30efa8c61de518c3baa3185754630ee28c61df418c33e83187790630eea0c619d418c3b8831877c8630ef10c61dd218c3b843185794230efa0461de408c33c81187750230ee204619c408c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930bfa8a617c514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ef21861dd430c3b886185f94830bea9061df320c3bc6418774c830ee19
  | 2 => 0xcbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53907bca720d794e41bea9c83dd53906baa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83be435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41ef298835e53106faa620f754c41aea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc7be8798f790f31eea1e63dc43cc6fca598df54b31ef99663de32cc7ba6598f70cb31dfa0e63bd41cc6fca198df54331efaa663de54cc7baa998f715331efa9663de52cc7baa598f714b31efa1663de42cc7ba8598f710b31efa0e639f41cc7bc8398f750731cea0e63dc41cc7bea198f794331af28663dd50cc7b8a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31aea9c637e528c6faa518df94631dfa0c63bd418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f790d31eea1a63dc434c6fea498df14931ef99263de324c7ba6498f70c931dfa0a63bd414c7ee6298f78c531bfa82637c504c7bea898f795131eeaa263dc544c7bea498f794931eea9263dc524c7be8498f790931eea1263dc424c7bea298f5d4531efa0a639f414c7bc8298f750531cea0a63dc414c7bea098f794131eea8263dc504c6b8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31af298637e520c6faa418df94431dfa0863bd410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21dfa0e43bd41c87be6390f74c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621dfa0c43bd41887be6310f74c621f790c43f
  | 3 => 0x28fc3577b6724bbbf254421c8a18c020191e21637ee78000000422df91c00061e0000001a79250c8522a61a000bd800708fcda22ab5200017e3255f4f158eb7927696d7aa04022e50d51bb52a000003673be165f28000000007a000058de19eb8b000dec0022b12aa69caa4905e000002ad000dd8ee000000d980010c1a00006b039382a2525320108cd11c967172464b7a0d2220000010d00000000000170c48e0049224000000000008d867000000001a6bae000168000002e6000f82b63fe3a8001a500000600c0300f0060240400001001c008020080080001602602c000000040000181a04601800803026018020020000100081b0000040100500600800001002004000050120000400701000000000002008098000000380300301400c0200003c02001800002000010010000000280100600001802000000000000040100180100000800800008010000000000200081501a000000010060100000600a000000000080080000300601c0800000601402002000008000110000180d00a008000010000000040200100400000003012038010010000000400600e00c0100000a0000001200a0300180300601001801002008050040000000300b0020000a0040080440000500800c040060040000200000000c01802008020130020040000500100003801808000004030000020000000100000c0000000c01c0180c000044088050000140c003000004008010000000000200208000803002014048000320000000301800002000000000028000000180080900c018000020240000500e0000040600100c018018000040000000000c0180381700000403007000000028000020540000902c02400000008000008000020000000b00001404802002000000000000080000c004000018030040000280501606800df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528
  | 4 => 0x40ed5d1e5196e7c743dd000b0dc896b0000014da4d4122f0c80000003f4cb1b63343ac001a810c0005d800000000000003484f0c08000006c8000002207099c000000001ab000700dcc00000000bec3b00011e2c9ec000598f458bbb20002ccdf0b60000005a83c436a14fe34004e000ad8800f4290748000fe93900ae021048cbf9312ae401f20c3024f38c8a71720f4c7333b770000300000005c8f7299000f2800257000000000da46000146bd41c4a389e800000000002101f0b083ba940004f9a3a31000f69fb08524c4080018900061dae8001aa1d195bc600000000083304000000b01ca7e40000000000171b10000d0d808230e42600021c28ced5ef000000f300000000000000000000480f18006e0fc00d8e075a0995ab9e47ea107b8000000000005b62871871979000001ac8401b2fb1ba3d003a95846b2c00000120948490080002e9000000cbb08000594a8a5a1a6001a787025a4cd353eb0bc2c435b1165a00153afe45a0e00012e59e230570000e68b98d14d726e04c31ce6840010a8dc1800f80036b10464d2a9ea3708597b279000304b40000002a800304414d68000c613e9d13700018a000360000004d00000013c189310d46eaaf4ff000000ac9adb4a2bc9f5540004401590e80030a4884738306a83c000ad4bacb8cfac81a2089f39cf7b80008aa12786741548894b2eb06c19c66400016b8512c3313202515000000144570b6cac1d25040012a0006de2acd1800714cd5981cb64639ddd9606366d000263000e6d5e0000000000026b2c20200000031aee80000056600000260442000000002dcd88003c20da0008b00050600000000426000000006d40010f1a72a4b54000001941d57fa8a136334a280022e000000004d8000e1800428d78fd2d4522d800004d3ce4bc79b6e0000012fb4b28422032a81562b396815401429c002c057c001578002daae41e800000501279d3000324000004f8120eb800000000eaac6000d04dab4620e56400000000a2d19800000001c91d13da1ec001010005f400000000555f739d0c60d9950005cac2503ada48c051859846525c5438c80a21a90300051e150578006c6c90003e000091c2380047c6a59e13f2421a514a655e25e1d133a28285c9bbef26a865d98023f607d36b7770c110980006b0000000000640000005d604349cb800000b98bf22328ef5c4e11e778a300035055cca00000033c000001a1606fd00019b0009dcbd0035ceba80024b000a99e00000004e800000704000939ef406000bb000000a7c002f439a000000000000000000079a7d45300076e911db000000f5989800066001770001b619d4c00047800000000000000f4800000e25698300c200140339468984003526a26bc02b2f03047cef17459a3e80018f05c5280020263c5690faa14445748226663e6
  | 5 => 0xfc2269f9551a2400aecdd353790280611880003d82b9704104607d9b70a4f3c8d1b118e0007f24c78e001c41996e27900e23553abe00015f000000000002f852c001da0009fd7236866ce30fb8005be000000002366000680020ab11fa80062ae71432ef56efb5d20df0f210400000000db1291eb0a09bc9c82960a00095b336928ec7fb8771e1f0001c40000000000072c0fdbe053264000fe83144cb75d28c435600133800000730002eb2c4a48000003b0b284884567e8bdb91bd00000170800000001f3000050d14003e901c1bdaa2d75c4e993b1b9000084000175d84b0000002a602c0030700094c370003d0d84000000002e8772d11ba00000296366091658be00c3d54f1284a0ec1608f135a2284e8000000005e9f13ac0a8000372cc698001c70000016c800248e9d441830ccb1c00000000000a79dd116ad1b2a70000001d1a400005d4003210000000000003c571989e6358000ab00f7d47880000000000116000000001938007348dd343370000ac000040000002600000089cde0433e601d79000448001a71384e4424001061d80017b9ec4160014e0a577c8680001624a0002a85800200000000000f8c0005c4eae64233bd450000001f64d2d21910000001e1af8000004a400000000970f90001bc660d00a15daafc0007e33a001e5baa1c2ea5d78a260c3b4002f3238bc1ae0e46323c00000013235cea000000000001bf3c26c12183a000001eab3e54a525ecaa019e000000007400000000064c000272d6000a4c000713906b800000094ba0000000002fc000000000000000000000087ba85b0000000002a00000037a4e60000000002a8152f0940000012138e26cb490c09a7a4db5d894c7d00018e000000e845a0b700003004af95faed15196400013c3eb690006504b800618000000004a2c01191ca5bc4a885a7a3b6895062dc0847d01a0920000000011d71a000003982d200000000000000001c552e17d1d0002d8c28003640000005490300000164800000000518ac77e960001d96aa1a0002ac62c00009800630539dc80061c204ca8007c23e4002a448a638002b07be9edfc34c1de000b510e6fa9e0c5890756838792c5096065bfa3d782fc4c90937c
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc40842b56110210c7d52308431c548c210b5586308431f540c210c715030842d5610c210f808620842f06148210f8c85208423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425e6014d1097180534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414425e65cc510c7d53314431c54cc510d3d4b314434c52cc510b6983314425c654c510c7d51314431c544c510d3d49314434c524c510e550531442d8604c5108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c521011097996304431f548c110c7152304434f528c110d314a304425e650c110c7d50304431c540c110d3d48304434c520c110da14a20442786548110d914a104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c1097d85530425d6154c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810d9185520423e64148108f590520425e63148109758c520426e62148109e980520423e64944108f592510425e63944109758e510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410425d65cc410c7953310431d54cc410d394b310434d52cc41097d95310431e544c410c7551310434e524c410d3549310436552c84109d594210423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400425f658c01097596300431e548c010c7552300434e528c010d354a30042d5618c01097d94300425d650c010c7950300431d540c010d3948300434d520c010b55843004398400c0109e596100436952840109dd9510042e462440109ed9510043695244010
  | 1 => 0x8398400c2208f587544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6115120c7d53534831c54d4d2097587534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534825d6114d20cdd53514833454d4520d5d4f514835453d4520cdd93514833464d4520d5d8f514835463d45208f990514823d64145209798c514825d6314520cdd5051483345414520d5d4c51483545314520cd99051483356414520d598c51483556314520dc580514823e65d05208f197414831f53d0520c714f414833751d0520cd147414823e65505208f195414831f5350520c714d41483375150520cd145414825e65cc52097197314831f54cc520c7153314835751cc520d5147314825e654c52097195314831f544c520c71513148357514c520d5145314826e65c8520d9147214836451485208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4c404831c5310120cdd444048334511012097996304831f548c120c71523048357518c120d5146304825e650c120c7d50304831c540c120d5d443048354510c120e61003048364518812097d8d540825c63550209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948208f992510823d64944209798e510825d6394420cd94541083355150420ae1814108356514c420d554531082d8604c4209b59621082e960084209bd9520082e46148020ea10120083c830480209ed95200825e63d53109758f54c425e63153109758c54c423e64d4f108f59353c431e5494f10c755253c431e5454f10c755153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c431e53d0710c754f41c431e5350710c754d41c431e54cc710c755331c431e544c710c755131c4395414c710c794e40c431d5390310c794c40c431d5310310c795230c431d548c310c795030c431d540c310e610030c433561d5210ce983548425e63952109758e548425f63552109718d54843356115210ce980548431f54d4e10c7153538435561d4e10d6983538423e6494e108f592538423f6454e108f191538431f5414e10c715053843556114e10d6980538423e6494a108f592528425e6394a109758e528423f6454a108f191528425f6354a109718d528431f53d0610c714f41842ba60d0610c7d4d418431c5350610ae181418431f54cc610c715331842da60cc610c7d51318431c544c610b618131842f16008610c7d4e408431c5390210ad586408431f5310210c714
  | 2 => 0x605063097994418c25d651063097996218c25d6588630a7992218c29d648863097994218c25d6508630a7990218c29d6408630b6980218c2d96008630a7586408c31d5190230a7584408c31d5110230e6980408c23d61d51308f992544c25d639513097d8d544c23e65151308f584544c23e64145308f590514c23e65d05308f197414c23e65505308f195414c25e65cc530c7d53314c31c54cc530c7d51314c31c544c530d5d45314c23e65901308f994404c31f548c130c7152304c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30c7151430c25d6510c30c7550430c23f64548308f191520c29f644c830a7191320c29e640c830a7590320c34d520c8308f992510c23d6494430cd945410c3355150430ae181410c35551cc43097596310c29e648c430a7592310c29e640c430a7590310c29e64cc030a7593300c25f654c030a7d91300c29c644c0309ed95300c2da60d5030c7550540c2ce6215030b3588540c2d66115030b5584540c2da6015030b6983520c29f6454830a7191520c29e6414830a7590520c34d5214830b5984520c2d56114830b6980520c2da6090830b6582420c25f655083097195420c25e651083097594420c2da60d4430a7992510c29d6494430a7990510c29d6414430b3988510c2cd6214430b6980510c31d51d0430a7983410c25e659043097596410c29d6490430d5546410c3555150430b6d81410c2d86050430e5d85410c3965150430c7545410c3955150430c5545410c39b6050430a7181410c3986050430a6181410c25e651043097594410c29e641043097996210c25d6588430a7992210c29d6488430d5546210c3555148430b6d81210c2d8604843097994210c25d6508430a7990210c29d6408430b6980210c2d96008430c7d06500c31d4194030d6982500c39b4194030e6506500c25d65d0030a7586400c31d5190030a7982400c31e5090030e6942400c25f6550030a7584400c31d5110030a7980400c39a6010030c7940400c39a50100309798f54c825d63d53208f58654c823f61553209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f209758653c831e5454f20c755153c825f6154f208f99053c823d6414f208f99251c823d64947209798e51c825d63947208fd9741c823d65d0720c794f41c831d53d07208fd9541c823d6550720c794d41c831d5350720ae18141c825f65cc7209759731c831e54cc720c755331c825f654c7209759531c831e544c720c755131c82d8604c720c794e40c831d5390320c794c40c831d5310320c795230c831d548c320c795030c831d540c3209798f548825d63d52209798e548825d63952208f993538823d64d4e208f992538823d6494e208f992518823d64946209798e518825d6394620ba580218
  | 3 => 0xe40c7d4e53902ba6014e40a798f529029d63d4a40ae983529029e6394a40a758e529032f5294a40ae980529023f654ca408f195329023e650ca408f59432902ba60d4640a798e519029d6394640a798c519029d6314640ab98851902ad6214640ae980519031d51cc640a7983319023e658c6408f5963190397614c640c7545319029c604c6408f994319023d650c6408f996219023d6588640a798e219029d63886408f994219023d6508640a798c219029d6308640ae98021902b9600864097587535025d6114d409798c515025d63145408f997415031f53d0540c714f415031f5350540c714d4150337515054097997315025c65cc54097995315025c654c540c7d4e405031c5390140c754c431025f63548409718d521029f6350840a718d421029e6310840a758c421032d52108409798e511025d6394440cd547411023d6590440a798e411029d6390440a798c411029d6310440d59453110355514c440b6181311029e63d0040a758f401023f6550040a7d8d401029c63500409ed9540102ba60d4c40c754c53102ae6214c40ab58853102b66114c40ad58453102ba6014c40ae983521029f6354840a718d521029e6314840a758c521032d5214840ad98452102b56114840ae98052102ba608c840ae582321023f654c8408f195321023e650c8408f59432102ba60d4440a798e511029d6394440a798c511029d6314440ab98851102ad6214440ae980511031d51cc440a7983311023e658c4408f596311029d638c440cd5463110335514c440aed8131102b8604c440e5d853110396514c440c75453110395514c440c5545311039b604c440a71813110398604c440a6181311023e650c4408f594311029e630c4408f996211023d6588440a798e211029d6388440cd54621103355148440aed8121102b860484408f994211023d6508440a798c211029d6308440ae98021102b96008440c7cc6501031d3194040ce982501039b3194040e64c6501023d61953308fd8554cc23e64947308f59251cc23f65d07308f59741cc23f65507308f59541cc2b86050730c795331cc31d54cc730d554731cc31e544c730c755131cc26e62d52309b58b548c31e5450e30c7d50438c23e6494a308f592528c29f644ca30a7191328c34e524ca30a7990328c29d640ca308f992518c23d6494630a7992318c29d648c630d5545318c29e640c630a7590318c29e64cc230a7593308c2ce62d5230b358b548c2da60d5230c7d52548c2da6015230a7993528c29d64d4a30b6983528c29e6494a30a7592528c34f5294a30b6980528c25f6550a3097195428c25e6510a3097594428c2da60d4630a7992518c29d6494630a7990518c29d6414630b3988518c2cd6214630b6980518c31d51d0630a7983418c25e659063097596418c3976150630c7545418c29c
  | 4 => 0x7590524c74d5214931b5987424c6d561d093197d95424c65c655093197994424c65d6510931e5d47414c69e60d053197996414c69d6490531e5d85414c7975150531a7181414c65e6510531a7990414c69e64d4131a7593504c69f6454131a7191504c6cf6254131b3189504c71f4114131c7504504c65e63d50318f596540c63e60950318f181540c63e64150319798c540c63e64944318f592510c63d65d0431c794f410c63f6550431c794d410c71e54cc431c7553310c65f654c431c7951310c71d544c4319dd95310c756534c4318fd91500c63c645403197d8d54c865c63553219798c54c865d63153218fd9153c863c6454f218f99053c863d6414f21e550531c863f64543218f19150c865f63543219718d50c865e63d52219758f548863e60952218f181548865e63152219758c548863e64d4e218f593538871e5494e21c7552538865e6094e21c7951538871d5454e2197181538863e6414e218f590538871e53d0621c754f418871e5350621c754d418871e54cc621c7553318871e544c621c7551318863f64542218f191508865f63542219718d508865f63551219718d544867b60551219e181544865e63151219758c544863f6454d218f191534867b6054d219e181534863e6414d218f590534863e64d41218f593504865e63d41219758f504865e63d50219758f540867a60d50219e583540863d65950218f982540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c2197982530871e5454c21c7551530865c6054c218f990530863d6414c219798c530867a6014c219e580530863e64944218f592510865e63944219758e510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410865d65cc421c7953310871d54cc42197d95310871e544c421c75513108795414c4219bd9521087a54148421f14c521086776548421ce95250087395494021d694e50087595394021ced9250087386494021d6d8e50087586394021ced0650087394194021d6cc6500875931940218fd91500863c645402197d8d500865c6354021ce95150087395454021d694d50087595354021ced9150087386454021d6d8d50087586354021ced0550087394154021d6cc550087593154021dac85500876921540219758653d025f6154f409798e51d025d6394740c794f41d031d53d0740cd54741d031e5350740c754d41d025f65cc7409759731d025f654c7409759531d02d8604c740c794d439025e6394a409758e529029f6350a40a718d429032e5250a40a798c429029d6310a409798e519025d6394640a798e419029d6390640cd545419029e6310640a758c419029e63d0240a758f40902ae62d4e40ab58b53902ba60d4
  | 5 => 0x51cca3f64543328f19150cca7a60d52329e583548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f587544ca3e60d51328f992544ca5f63551328f994544cb1d63151328f584544ca3e601513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3e64145328f590514ca3e64d41328f593504ca3d65950328f586540ca3e6095032c718d540ca3f61550328f181540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c8328f992510ca3d64944328fd91500ca3c6454032c754c43d065f6354b419718d52d069f6350b41a718d42d069e6310b41a758c42d072d5210b4197d8d50d065c6354341ad58753d071d5314f41ab98853d06ad6214f41ad58453d06b561d4b41a7d8d52d069c6354b41a798c52d069d6314b41cb54852d06b56114b418fd9532d063c654cb418f99432d063d650cb41a798f50d069d63d4341ab98b50d06ad62d4341a7d8d50d069c635434197982539065c6054e41c794f419071d53d064197d8d509065c6354241c714d435065e63149419758c525069f6350941a718d425072c5250941a798c425069d6310941a798e415069d63905419798f505065d63d4141ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506b56194941a7d8d525069c6354941add8552506bb6054941ae181525069e6314941a758c525072d5214941ad98732506b561cc9418fd95325063c654c9418f994325063d650c941a798f505069d63d4141a7d8d505069c6354141abd8950506ac625414197982531065c6054c41c794f411071d53d04418fd95411071e5350441c754d41106776550441cd951411065f63540419718d501066e62153319b58854cc71c5450f31c755043cc63f6454b318f19152cc69f644cb31a719132cc69e640cb31a759032cc74d520cb318fd9150cc63c6454331b558754cc71d5415331b398854cc6cd6215331b558454cc6d561d4b31a7d9152cc69c6454b31a799052cc69d6414b31d354852cc6d56114b3197d9542cc65c6550b319799442cc65d6510b31a798341cc7976150731a718141cc69e64d4331a759350cc6ce62d4331b358b50cc71f4194331c750650cc69f6454331a719150cc63e60952318f181548c71e54cc631c7553318c63f64542318f191508c66f62551319b189544c67b60551319e181544c65e65d0d3197195434c71c5450d31c7550434c63e64149318f590524c69f644c931a7191324c74c524c931a7990324c69d640c931a7992314c69d648c5318f993504c63d64d4131b5586544c6cf6255131b3189544c6d76155131b6d81544c6d86055131c7550544c6d56194931a7d91524c69c6454931b5d85524c6db6054931b6181524c69e6414931a
  | 6 => 0xab9f89eb9041710f1169895a5d287920a3c9c28cda221e6a2b1a811a07b1e718c997a61a2ca9f8c8a898cb0b921a8b30da9aa00021b1fca23a1c99f96d18990a00b0cb8f80cc21a0dd90c20c846a380ec05189c8da1b822720b07821e2268c32450a596501ba438a42558209989e020b80200019c80005d0210441d326117b285959a341a6a489b1a068960000830611bd9fa11609007f86609212f9d2a0c14a2511d38030020680000a80e0000080200604206000008000008100090020000081b0000c4008000020000700a002060010000060740980b01a0141080101200006011042004000050000000601601a0000401001803800000020000078100000040000100c0000100a0000180380400c020098000000480000c01e0cc0c0050000000400200a04c0681500201805801002008010000000100600002c0000001900600c0000b0180000080b0100040400a0000500000500e0001281501605802805000000208010420100180208a0000480600a01c000160000000080700c00c0880900000000003048084000110040100280000004409800000000000070060000100e01c000000190040000480400801c1000300007c0380d006030040010000280300600403c008030da0040380600003400009000010038010000040d0020000180000000401c020120000040302c00e0200980301400c0000700200c0000c0000300181b0060280580300002c0f00000000408000002034008000000002401502600801000004010018000000000000c0040240100201601419000028000100000140181800900200000804004038030010000080281500408c0300905a06c02806000010000000020281f8000300040700000c02007003000000028050060000480801a028078090240140900100c00004000042014018040000000080101c000038080000580200200005c0300501a008000050040240980100e01000003016010160020020080580c014038200070220000200d000004000230040000100002601400004000014078000040100400406e00c08800006008000010060b8000070420002d8080000629d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a71814310f1d4354843c750d5110f1d43940439798e51d0a5d639474297d8d50d0a5c63543429798e5190a5d639464297d8d5090a5c6354242975875350a5e60d4d42975845350a5e6014d428f9974350b1c53d0d42c714d4350b1c53909429798c5150a5d63145429798f5050a5d63d4142975865310a5e6094c4297d855310a5c6054c428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429798e5110a5d639444297d8d5010a5c63540429d98454cca756115332c715143cca3e64947328f592
  | 7 => 0x426f10d08697e98e04d89520486b000275a588000001a014821902686e864232171a0611c1d40d70750172481728ad0c382381891d19103180716696704b1b6919016a360e68de8f30158cf02e862059a260408d29dca0d24d9a408126522e8a002e0e71ce1520b08a89f52000588ef17a20d9008bb9178d31428000ed800231000073000111a8227f8fb2009dd272a1106819011529d97909e1950e29281ce96c85521da5f89d9271b51bf8011228a9a9e0c19f607f11009f16405c8f01fd00000c10987a1e89ec1350000708f9a390669c98a48891920389e48001e6000000000000262a649f319e0000001b400023e8451682120e60be0448338e02918ff1d680f21800011b9f70e3a129b907702d000061a460eb23380013791b027a409469200001ed0000e8a0587787ea108e993f1340ff8ed08c1b98f18ba1821019af0382719ad181236a659d70c50728308458220c5882a8d0a61a7a948fd1060c70df88aa0a0f712104a99191e1580ab0ce9771a10ca82fa3712a8d09761b700423785805909885aa078af9460baa8f9a227d10010d98016884c98699b9b8875a2280026300a23023f19297819c05c28395f0000001bd0000970000001578ad8000000cf8001551818000000e495c0000001e99e09e80000002541ba8000c026b0539311d81f400022016908e0f58b88800e22988a7924a020b283b04c05080025d9b586c19412313e0c2a4f800079a9210a83e80001185700011a80022c08ba689ed80020418d9c0218847a0fa501c70d400f8001b78d3a098391491220f691800026aa8b08702700000000001a13e8000a30001ee09180000000005b00029f00009b00000016b9148e10ac09980025f03aa3b2739ab29d02da279d50000788248e31531aea1506714990311d800000007a448d90eb88d8c404f8d98362091b297f0e79da89f83300002b28e0e82520bc2851858b4148a288f0a01967a5c28b8a908f8f38d6a4e80012f0fa11f8028d1a249df92e0a0a761a70000a185109e8a506988980014da2329a00026402aa468001f00eca5aa028ab97c8c78ee26381ca0a90e1a4837943a4b0289f11c500017527a0aa04994191118b14b0439559628001bb9540608000b598500022f8481441a90561de0219501842900b00e08a20351cb9390521d180000012d80008c80980025e8000f903ba470c9073915a829e3a1c036a7886d9e523f8851de9562550432911d211285fa35a9aa7b91f1eb269841080a579e400000004900013b0930198000540321bf017a4b8bf03d8fe1b0140277a4291415d1d598a1a9a0e131988a8a99614c9768e50250dc1db11c92d208a421f597d98395680023e214853298012960a2119e8000700260fc1519830000001f68ae82b8001301ea0b701489780010694a83017983d211a7021d10926a1e91
  | 8 => 0x8b1a5b1c308d24e25703f8948488691fe00000027c1b3a49119a30a40127a971c794e1d0a3b9f799682a20386e1ae00000009800008415f8470d8000165a2919d17420810c83480e97d00013200006592b1cc8000001c5800126835a928001c228a00e0f515a8001c11398630000000000e58db8000001611308000000190000001f28000370c688b1b610200000027a98f07616e0089da12b98c18717b9169ac2348299bc1c88000652690af23d02c9e29059ac9338cc92ea6c85a024125004a9392c29c0f216f24c943005a529ad91093f80000000013580020316624104d1b215ca931730c09cd0000001a8a7808e8000000fa8310000000000002950c61450db0d000c80019712c9048b228f11892a14b8558aa9c60769848000000001ef80000000000012580000018900000006aa9693881200000025316c000238800136a6b96d80028487e0001039c6a1f0939570878839af9788688f627118824c1e224195a14780a84e9fb26da298001331cb12886d01d8000fe9e309d00000000000000019927498780015b25917481a8c22708001c18001f49e58c4a8608f10e97c0001779fb98ea2e29080004219f09080000000022800000025e0a28139958b4a4aa1f8228d125680014c1130f8a539d9800034096a1389a80001c0001e78090080419a08f780000000010817a88180015e1a528ca2a10fa7991e9a604b9170001e180d08a07d0d5852a0f1b323980393c921a99944a6080000000000019307480012410b96aa6695121685492612901d22400027e26d0bc9ca9d61708b38b82771bea2500025986f80000019b0d60b107a9601dc1138002600de25c81104a2741fe962082000150a4323a19a1758000002350100ee884a7306a05e800288a8113aa8908585e0001fc140871a2d88893da791b107d80026c0001589370001dd8000018000000001298030001a28001cc03982802f1fda581458dc8f414d01b00022ba672819f81050001a30000001909faa172441619088000000232498f2a1780027c80003e00000029ea9c96e9f90ea85681628685f0001c40e900006387c0a3902a199471939f381401806c93b813232954a840001f080000000024a00001f0c100013619da560329538000291be0000000000000d89d79591a180000000000018fa9ba5b8ef80023c0dd1c380028e9d10df04e0000b692385d8678790ae1aa90f24789909b8ea17f84f09a2941c90a12960008c821419a9bb1948bf80014120e83f00b96b0000000710000d20002318000b99011b4a4d0f4a130b506f16388801e23da5a1ba21000d8000061f21cd9ca0429d48a7164864a620cd17022595d97390728083c0002801d90bd20526e1c49df0ce2548b78ca01ea209ec85ba1600002010b0fd98280000016f8000000000001c080001080006009122a80007
  | 9 => 0x21e94fa9598a80016322f0e193a26f8ac8e40d513d0001dba3a9ee9420460bb250a8815ea6e8629f18c9a7ea6782c07ca8d8000861e104027b2979862830002158002459d8a0113c1cf18ba9b2a0005006a6814e8720152721f98bda519980578002072218259329a597218080000000000015ba769ff1b08941a39d01bc938000107a1b9cf8001ef0001c80000000000d780026614f0a680015281f8001120001ea8be9ff80000016a0000000fb80028c28709c17e27f24f03ca9919983a22d0d486b87b8fca7d8b6134a7518d0500a8233092
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x3ebaaa3292bc6c68400000a09e00007238000074c80000beb496b24810440088182edc000090a202b0c2241cae2cc40000da007c000800cc8a62506042004e582886009c06b854d6ca9a300e261a14000000005e766636003a8c944c4a00b600008400d000ac00d40000de001ed8700c6aa83c785c4600827e34d2806400a620c0528e16a4002a6e56c604007ace985a0a2212000220020005000f1302030119010b010001000a00010705030400000000000a010305000403a2ee2a1aa221d187050e5010e8ab88a8a1e65469c35410e32838ecaa2641960d6354842d0706a9ac429e838358d5214b41c18c629284a0d0c7254c535068c382a629a83255c66314941a18e6a90a4a0d2870548525061c382ca19283435c85450f31c1ac8a906598e0d5458854cc706b22a429663431c95410d31a30e0aa08698e0c64149324c686392a82a263461c1541513192ae3320a498d0c74548524c6a4382a429263161c16510931a30e0a08a098f11414c55008790a0a42a8043d04c52154021a2ae329a83a060c639494290287396a729c81439cf5294a40c1ac6a908420651511813110306a9ac4298818554d6114c40934e1b1aa42060d635485210312a92c2290810d5c4654c840930e0b1ca220631511813110388a8ec09888185544604c440e22a2302622069251181311030ca88c098881a4544604c440c22a230262204987058e211030ab1aa310881455c6544c730a1ce5aa0871860c64949328c287396a92a461439d35294a30a1ae42a2861851571151430c306b22a4190618c5446050430c1aa8b10a81861554584540c24d386c8a9061835915214830c8aa4b08a41845571195420c24c382c928861945446050430e22a3b02821861551181410c388a88c0a0861a49446050430c32a2302821869151181410c308a88c0a0861261c16488430c2ac8a8c421861561544400c28ab8ca6a0e418694c6050720a2ae32a2639061a5418131c83882888018241a81844048020d80c2182401061853181418430c2a0c098c2185d4d6110210c2ea8b0861084e276c85208430c298c0a0a218a1486050510a28eaa0a62886146550531443822928298a21641c1414c510c30a83026288648521813144348a08c098a218554d6110010c4aa4b088008615545843004322a92c218021465d4400c010c32ca20060087095210030042c8b888018021a4584400c010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x13a00000c0649402000040010a108058d5188440a10805915188430a118194c6050720a1181950604c720d00521c1414c510e0052504604c510c11655c4400c010d01525c4400c010c1175584400c010e0152584400c010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 6 => packedAt s4K6 (880+((h/16+packedAt s4K6 (768+(h % 16)*7) 7) % 99)*7) 7
  | 5 => packedAt s4K5 (31188+((h/339+packedAt s4K5 (27459+(h % 339)*11) 11) % 1477)*11) 11
  | 4 => packedAt s4K4 (56038+((h/448+packedAt s4K4 (51110+(h % 448)*11) 11) % 1615)*12) 12
  | 3 => packedAt s4K3 (5784+((h/37+packedAt s4K3 (5488+(h % 37)*8) 8) % 148)*8) 8
  | 2 => packedAt s4K2 (615+((h/3+packedAt s4K2 (600+(h % 3)*5) 5) % 17)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 1 => 0xf07fffe0fffffff81f07fc3ffe1fffff463c7f
  | 2 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 3 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x210c08c42890400165098044c022425818d1b1
  | 1 => 0x44109102412221280a422429121494a1422446
  | 2 => 0xa22522481a440652a084ca8265412a0a854a98
  | 3 => 0xcb59c4929076ab9cd3d06223b9980c33e80f60
  | 5 => 0xc61871ce38733e71ce77330311030c3f7b000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36711
namespace PEqualNP.Outside.L_meta_36711
open PEqualNP.Outside.L_meta_36711.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x410900060024785544108026005181c3419f4a8c01c0088d0022000142e1c9014c80f1d18640021600a80009d5800058da9500800c2280146016002081ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x12ac0e13971e05800784811aa5a083168f052a242815aca1841914250a8924960f8c01920c800027100680220002951d2a80112690a917800000039d8000000022ab0b8029a6000d9e87000000001b8000000000001a0d000a211f00088b1f80199b082398021c1c94a7930011800000a32009800000001880000600000eaba88000004007450000c00001024001440040004043c20002c000000004c1004042e7ca721cf54a43b7290876d5210e7ca621e794c43d7290873d5210f5aa421cb548439f29e853d5490abea6a15714d42cfa9a853c5350b38a6a14714d42d7a92853e5410a7ea9994f153329f2a4653d548cb3887196b50a32bd2846579508ca7ea8994f15132d6a12653e540ca7aa8196710c32b7296836d52d06bca720d754e41ce21e633e548c67aa918cfd51319e2a2639c434c6dea498db14931bda826378504c67ca990cf55321d6a14433e540867aa810d794c21aea9843ad42086f4a010de54021afa9a815c53502dca4205b548409f2a4613d548c33887185b94a30b6a94613f544c278a8986710c309f2a6413d54c82bca7905754f20d6a1641ad424827ca8104f550209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1651cb8ea809800000000000020000200001226ac0184802801b000000001e000408a24301281189000070d6214d42a3588438ca8c6350a32c610e508cb2942542328b195424ca1d6510c32a358843cc62d6295231a3588434c70c4314931c610c504c61c6355321a318d428868c6350821c354d42087294254021a3588438c30c4394a308b588544c28d6210c30a318d42c830d5350b20a318d424821c6355020
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x40a68200684b908728465421cd4254232a12e4218a098c0c7654d420868439a84a8043031d95350b20
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (2670+((h/30+packedAt s5K4 (2430+(h % 30)*8) 8) % 130)*8) 8
  | 3 => packedAt s5K3 (998+((h/8+packedAt s5K3 (950+(h % 8)*6) 6) % 48)*6) 6
  | 2 => packedAt s5K2 (300+((h/2+packedAt s5K2 (294+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe07ff81ffff83f07ff0ff83fc3ffc0fd8f33f3
  | 1 => 0xffffffe0fffffff81ff07ffffc1ffffe71fc7f
  | 2 => 0xff81ffff03ffc3ffe0007fc3ffe3ff0381cf9c
  | 3 => 0x1fffffc0003ffffff8003fffc0003fe0fe0
  | 4 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x290c88c42892610165049a24c12642588711b1
  | 1 => 0x42101102412000280a102049040894a0306446
  | 2 => 0x8525a2481a462752a08c4ea26b432a0b818a98
  | 3 => 0x1659449290748a9cd3a90403b2900c335a0f60
  | 4 => 0x1861871ce38733e71cce7730230230c3edf000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8eec8e8c8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36711
namespace PEqualNP.Outside.L_meta_36711
open PEqualNP.Outside.L_meta_36711.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1700070e0f8018818a011a9e96120b090002201b848a9c96991e141380948018040e9d0280001f9f03059c051111800c1d839008000008a093079b158d178f150b86128d909a06800c8980000000198101500820202002850a2c40700a80af1614000017fd5005fe54017f55005fc5401ffd4c01fe53007f54c07fc53017fd0c05fe43017f50c05fc4300ffd4803fe5200ff54803fc5200ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803fe3200ff4c803fc3201ffd44017f51007f94401fd51005f54407fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8403fe2100ff48403fc2101ffd4001fe50005f94001fd5001ff140017c50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x222000efd91100057ec88802ffe64440057f322200bff5911005dfac88802ffc64440057e322200bef1911001578c88802fff5444017ff2a2200bff5511005ff8a888003ff63440017fb1a2000f7d8d10005bec688003fe63440137f31a2000ff58d10005fac688003fc63440137e31a2000f718d10005b8c688033ff5344001ff29a2000ff54d10067f8a68802fff4344017ff21a200bff50d1005ff8868802bff62440157fb122000fbd8910005dec48802bfe62440037f312200aff58910055fac48802bfc62440037e312200afb1891000dd8c48802bff5244015ff292200aff54910057f8a48802bff4244015dfa12200aff90910057fa848802bbd4244015fe212200affcc910057fc648802bfd3244015fe192200cffd4510006fea288013fe5144001fea8a2000df54510027f8a28802fff4144009ff20a200bff50510027f88288003ff3144009ff18a2000ff4c510027f8628802bff2144009ff10a200aff48510027f84288033ff5044001ff2822000df94110007faa088033fc5044001be282200bffd011005ffc808802ffd4044017fe2022000ffcc110007fc6088003fd3044001fe182200affc8110057fc408802bfa2044015fe902200afe48110057f84088013ff1044009fd8822000ff84110007ec2088013ff65040097fb282004ff9941001dfcca080137e65040073f3282004ff59410005faca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff99010015fcc808013be64040055f3202004ff59010035fac808013bd64040015eb202004ff19010025f8c80801bff540400dff2a02006ff55010037f8a808013ff63040097fb182004ff98c1004dfcc608013de63040016f3182004ff58c10005fac608013dd63040016eb182004ff18c10025f8c60801fff5304001ff2982000ff54c1003ff8a60801bff430400dff2182006ff50c10037f88608013ff62040097fb102004ff9881000dfcc408013ee6204003773102004ff5881002dfac408013ed620400176b102004ff18810025f8c408017ff520400bff2902005ff5481002ff8a408017ff420400bdfa102005ff9081002ffa8408017bd420400bfe2102005ffcc81002ffc6408017fd320400bfe1902004bf98410027fea2080137f5104009ff2882004ff54410026faa208013fc5104009ffa082004ff90410027fa8208013fc4104009ff9882004ff8c410027fa6208013fc3104009ff9082004ff88410027fa4208013fc21040117f3002007ffd4010007fca0080037e5004001fea802007ff14010006f8a00801bff400400dff2002006ff50010037f88008003ff3004001ff1802000ff4c010007f86008017ff200400bff1002005ff4801002ff84008013ff1004009fb8802004ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0x7f9300c025ff9006012ff88030097fa401804bfc200c009ffb2e2004bfd9710027fccb8800efe65c4009bf32e20039f99710027facb88002fd65c4009beb2e20009f59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb262010bf59310027f8c988012fc64c4021ffaa62010ff95310087faa988043fc54c4009ffb1e2004bfd8f10027fcc788026fe63c4009feb1e2000bf58f10027f8c788012fc63c4023ffa9e2000ff94f10007faa788047fc53c4021ffa1e2010ff90f10087fa8788043fc43c4009ffb162004bfd8b10027fcc588006fe62c4009feb16200fbf58b10027f8c588012fc62c401fffa96200fff94b1007ffaa58803ffc52c401fffa16200fefd0b1007ffc858803ffd42c401fdea16200fff10b1007ffe658803ffe32c401ffe996200fff0cb10027fea3880137f51c4009ff28e2004ff54710026faa388013fc51c4009ffa0e2004ff90710027fa8388013fc41c4009ff98e2004ff8c710027fa6388013fc31c4009ff90e2004ff88710027fa4388013fc21c4023ffa862000ff94310006fca188003fd50c4023fe2862000df14310087fe8188043fe40c4021fea062010ff10310007fe6188003fe30c4001fe9862000ff0c31007ffe418803ffe20c401ffe906200fff08310007fecb08002ff6584001bfb2c20009fd9610077fccb0800efe6584001feb2c2000bf59610077f8cb0800efc6584001be32c20039f1961006ffec908036ff648401bff3242002bf9921006ffac908036fd648401bfe3242002bf1921006ffea908037fe548401bfeaa4200dff15210007fec708002ff6384001ff31c2009bf98e10007fac708002fd6384001fe31c2009bf18e10077fea708003fe5384001fea9c200eff14e1006ffe8708037fe438401bfea1c200dff10e10047fec508022ff6284011ff3142001bf98a10047fac508022fd6284011fe3142001bf18a10047fea508023fe5284011fea942008ff14a10047fe8508023bf4284011ff2142008ff50a100477a8508023fc4284011ff9942008ff8ca10047fa6508023fc32840157eb0c200effd4610006fea308013fe5184001fea8c2000df54610027f8a308037ff4184009ff20c200dff50610027f88308003ff3184009ff18c2000ff4c610027f86308023ff2184009ff10c2008ff48610027f84308012fe608401dffa842000ff94210006fca108003fd508401dfe2842000df1421006ffe8108037fe408401bfea04200dff10210007fe6108003fe3084001fe9842000ff0c210047fe4108023fe2084011fd1042008ff48210047f24108023fc2084009ff8842000fdc4210027f62108003ff65440017fb2a2000dfd9510004feca88033fe65440077f32a2000ff59510005faca88033fc65440077e32a2000df1951001cf8ca8802fff64440177fb
  | 2 => 0x300affc4318057fd218c02bfe10c6009bf982300d7fea118003fe508c001bf2846000ff542300d7f8a1180037c508c033ffa046019ff902300cffa8118067fc408c013ff9846000f7cc23004ff66118057ff208c02bff1046015ff482300aff84118003ff654c0017fb2a6000dfd9530004feca98063fe654c0077f32a6000ff59530005faca98063fc654c0077e32a6000df1953001cf8ca9805fff644c02f7fb226000efd91300057ec89805ffe644c0057f3226017ff591300bdfac89805ffc644c0057e3226017ef1913001578c89805fff544c02fff2a26017ff551300bff8a898063ff534c013ff29a6000ff54d3004ff8a69805fff434c013ff21a6017ff50d3004ff8869805bff624c02d7fb126016ff9893000dfcc49805bfd624c02d7eb126016ff1893000df8c49805bff524c02dff2926016ff549300b7f8a49805bff424c02ddfa126016ff909300b7fa849805bbd424c02dfe2126009ffcc9300b7fc649805bfd324c013fe1926000ffd8530005fec298003fe614c001feb0a6000ff18530025f8c298063ff514c001bfa8a6000ff94530007faa2980037d514c031fe28a6017ffd05300bffc829805ffd414c02ffe20a6009ffcc530007be6298003fe314c001fe98a6000f74c53004ff8629805bff214c02dff10a6016ff485300b7f84298063ff504c001ff2826000df94130007faa098063fc504c001be2826017ffd01300bffc809805ffd404c02ffe2026009ffcc13004ff66098003fe304c001ef1826016ffc81300b7fc409805bfd204c02dfe1026009ffd943004dfeca18027fe650c0077f3286009ff59430005faca18027fc650c0137e3286009ffd903004dfec818027fe640c0057f3206009ff5903009dfac818027fc640c0137e3206013ffd503009ffca81804ffd540c027fe2a06009bf98c3004ffea618027fe530c013fea986009ff14c3004ffe861804fdf430c013ff2186009ff50c3004ff88618027dc430c013ffb106009bfd883004ffcc418006fe620c013feb106012bf5883004ff8c418006fc620c025ffa906012ff94830097faa41804bfc520c025ffa106012efd0830097fc841804bfd420c025dea106012ff1083004ffe6418027df320c013ff1906009ff4c830097ba6418027fc320c013ffb086009ff98430025fcc218027fd610c0017eb086009ff184300a7fea2180037f510c001ff2886000ff54430006faa218053fc510c027ffa086013ff9043009ffa821804ffc410c013ff9886009ff8c430007bc6218027fd310c013fe1886009f70c430097fe421804bfe210c025fe9086012ff084300adfcc018053ff500c001ff2806000df94030007faa018053fc500c001be2806013ffd003009ffc801804ffd400c027fe2006009ffcc03004fbe6018027fe300c013fd1806009ff4c030007ba601802
  | 3 => 0xfb18a003df98c5001efac62800f7c631403fbfa18a01fdf90c500fefa862807f7c4314007bfb10a003df9885001efac42800f7c621403dbfa10a01ecfd08500f6fc842807b7d421403d9ea10a01edf108500f6fe642807b7e321403dbe990a01edf0c85001efec22800f7e6114007beb08a0009f5845001ef8c22807f7f411403fbf208a01fdf504500fef882280037f3114001bf188a000df4c450006f8622807b7f211403dbf108a01edf484500f6f8422800f7e60140413f300a003de980500fefe802807f7e401403fbea00a01fdf100500f6fe402807b7e201403dbe900a01edf0805004ffecb98026ff65cc013ff32e6003bf9973004efccb9800e7e65cc013feb2e6000bf5973004efacb980027d65cc013fe32e6009bf1973004ffec998026ff64cc013ff3266002bf9933004ffac998072fd64cc013fe3266009bf193300e7fea998073fe54cc039feaa6601cff1533004ffea798027fe53cc013fea9e6009ff14f3004ffe8798027fe43cc013fea1e6009ff10f3004ffec598026ff62cc013ff3166001bf98b3004ffac59806efd62cc013fe3166001bf18b300dffea59806ffe52cc037fea96601bff14b300dffe859806fbf42cc037ff216601bff50b300df7a859806ffc42cc013ff9966009ff8cb3004ffa6598027fc32cc013ffb0e6009ff98730025fcc398027fd61cc0017eb0e6009ff187300effea3980037f51cc001ff28e6000ff54730006faa398077fc51cc039ffa0e601cff907300e7fa8398073fc41cc013ff98e6009f7cc73004ffc6398027fd31cc001ee98e6009ff0c7300dffe439806ffe21cc037fe90e601bff087300effea198003fe50cc001bf2866000ff543300eff8a1980037c50cc039ffa06601cff903300e7fa8198073fc40cc037ff906601bff883300dffa419806ffc20cc001ffb2c6000bfd96300d7fccb1800efe658c001feb2c6000bf596300d7f8cb1800efc658c033ffb246019bfd92300cffcc91800afe648c033feb246019bf592300cff8c91800afc648c033ffaa46019ff952300cffaa918067fc548c02d7eb1c601affd4e3004ffca718003fd538c013fe29c6019ffd0e300cfbe8718027fe438c033fea1c6009ff10e300cfb88718057ff628c02b7fb146015ff98a3000dfcc518057fd628c02b7eb146015ff18a3000df8c518057ff528c02bff2946015ff54a300aff8a518057ff428c02bdfa146015ff90a300affa8518057bd428c02bfe2146009ffcca300afbe6518057fe328c02bfe9946015f74ca3004ff86518003ff618c001ff30c6004bf98630007fac318002fd618c001fe30c601affd4630006fea318003fe518c001fea8c6000df546300d7f8a318067ff418c033ff20c6019ff506300cff88318027ff318c001ff18c6000f78c630007fa6318027fc318c001ee18c6015ffc86
  | 4 => 0xffe5394001bf29ca003ff54e50006faa72800ffc5394007be29ca023ffd0e5011ffc872808ffd4394047fe21ca020ffd8a50105fec528083fe62940037f314a020ff58a50105fac528083fc62940037e314a003ffd4a5001efea52800ffe5294041bf294a003ff54a50106faa52800ffc5294007be294a020ffd0a501077e8528083fe4294041fea14a020ef50a50107f88528083ff3294041ff194a020ff4ca50107f86528003ff6194001ff30ca004bf98650007fac328002fd6194001fe30ca003ffd465001efea32800ffe5194001bf28ca003ff54650006faa32800ffc5194007be28ca023ffd065011ffc832808ffd4194047fe20ca000ffcc650007fc6328003fd3194001fe18ca020ffc8650107fc4328083fd2194041fe10ca003bf9825001ffea12800f7f5094007fda84a003ff1425001ff0a12808fff4094047ff204a023ff5025011ff88128083ff2094041ff104a020ff48250107f8412808f7f6494047bf324a023df5925011ef8c9280037f6394001bf31ca000df58e50006f8c72808f7f4394047bf21ca023df50e5011ef887280837f6294041bf314a020df58a50106f8c5280837f42940419fa14a020df90a50106fa85280833d4294041be214a020dfcca50106fc65280837d3294041be194a000dfd8650006fcc3280037d61940013eb0ca000df1865011efe832808f7e4194047bea0ca023df10650006fe63280037e3194001be98ca000df0c650106fe43280837e2194041be90ca020df0865001cfcc12808f7f4094047bf204a023df5025011ef881280837f2094041bf104a020df48250106f8412800eff6554045ffb22a022bfd9150117fcc8a800afe6454045feb22a022bf59150117f8c8a800afc6454007ffaa2a003ff9515001ffaa8a800ffc5454001ffb1aa000bfd8d50007fcc6a8003fd6354001fe31aa009bf18d5001ffea6a800ffe5354007fea9aa003ff14d50117fe86a808bfe4354045fea1aa022ff10d5010ffec4a8086ff6254043ff312a001bf9895010ffac4a8086fd6254043fe312a001bf1895001ffea4a800ffe5254007fea92a003ff1495010ffe84a8087bf4254043ff212a021ff5095010f7a84a8087fc4254043ff992a021ff8c95010ffa64a8087fc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa004bf1855001ffea2a800f7f5154007ff28aa003ff54550006faa2a800ffc5154045ffa0aa022ff90550117fa82a808bfc4154001ff98aa000ff8c550007fa62a8003fc3154043ff90aa021ff8855010ffa42a8087fc21540077fb02a003ffd415001ff6a0a800ffe5054001bf282a003ff1415001ef8a0a800ff85054045ffa02a022ff90150117fa80a808bfc4054043ff902a021ff8815010ffa40a8087fc2054007bfb20a003df9905001efac82800f7c6414007b
  | 5 => 0x8231027fcc118802fe608c409feb046200bf58231027f8c1188b3ff508c459fe284622bffd023115ffc81188affd408c457fe204622affc8231157fc41188abfd208c455fe1046200ffd9531005feca988a7fe654c4077f32a6200ff59531005faca988a7fc654c4077e32a6228ffd9131145fec8988a3fe644c4057f3226228ff59131145fac8988a3fc644c4057e3226228ffd5131147fca8988a3fd544c451fe2a26229ffd4d3104ffca698803fd534c413fe29a6228ffd0d31147be8698827fe434c451fea1a6209ff10d31147b8869889fff624c44f7fb126227ff9893100dfcc49889ffd624c44f7eb126227ff1893100df8c49889fff524c44fff2926227ff5493113ff8a49889fff424c44fdfa126227ff9093113ffa849889fbd424c44ffe2126209ffcc93113fbe649889ffe324c44ffe9926227f74c93104ff864988a7ff514c401bfa8a6204ff94531007faa2988037d514c409fe28a6228ffd0531027fc82988a3fd414c409fe20a6209ffcc53104fee6298813fe314c409ef18a6227ffc8531027fc429889ffd214c409fe10a6200ffd8131005fec098803fe604c401feb026200ff18131005f8c0988a7ff504c453fe2826228ffd0131147fc80988a3fd404c451fe2026227ffc813113ffc409889ffd204c44ffe1026204ffd9431025feca18813fe650c4077f3286204df9943101cfcca18813fd650c4017eb286204df59431004faca18813fc650c4097e3286204ffd9031025fec818813fe640c4057f3206204ff5903112dfac818813fc640c4097e3206225ffd503112ffca818897fd540c44bfe2a06209bf98c3104ffea618827fe530c413fea986209ff14c3104ffe8618827fe430c413fea186209ff10c31027fec418812ff620c409ff3106201bf98831027fac418892fd620c409fe3106204bf18831127fea418893fe520c449fea906224ff14831127fe8418893bf420c449ff2106224ff508311277a8418893fc420c413ff9906209ff8c83104ffa6418827fc320c4097f3086204ffd4431026fea218813fe510c409fea886204df54431027f8a218813ff410c409ff2086204ff50431027f88218813ff310c409ef9886204ff8c431027ec6218813fd310c409ee9886209fd4c431027fe4218813fe210c409fe9086204ff08431027fec018813fe600c4017f3006204ff58031005fac018813fc600c44dffa806226ff1403112ffe8018897fe400c44bfea006225ff10031127fe4018893fe200c449fe9006224ff0803101dfacb2808fff64940477fb24a023ff99250015fcc92808ffd64940477eb24a023ff19250015f8c92800fff5494007bfaa4a003ff9525011efca92800ffd5494047beaa4a003ff1525001ef8a928003ff6394001ff31ca009bf98e50007fac728002fd6394001fe31ca003ffd4e5001efea728
  | 6 => 0x7fe282a203df1415118ffe80a88c7fe4054463fea02a231ff10151187fe40a88c3fe2054461fe902a230ff0815118efec8a88c77e6454463beb22a231df19151006fec6a88037e6354401beb1aa200df18d5118efe86a88c77e4354463bea1aa231df10d51186fec4a88c37e6254461beb12a230df18951186fe84a88c33f4254461bf212a230df509511867a84a88c37c4254461bf992a230df8c951186fa64a88c37c3254407bfb0aa2039fd855101eeec2a88c77f4154409bf20aa231df50551026f882a88c37f2154409bf10aa230df48551026f842a88037f6054401bf302a200df58151006f8c0a88027c6054463bfa02a231df9015118efa80a88c77c4054461bf902a230df88151186fa40a88c37c2054413ffb2e6209bfd973104ffccb9880efe65cc413feb2e6200bf5973104ff8cb98826fc65cc413ffb266209bfd933104ffcc99880afe64cc413feb26622ebf5933104ff8c998826fc64cc45dffaa6622eff95331177faa9988bbfc54cc413ffa9e6209ff94f3104ffaa798827fc53cc413ffa1e622ef7d0f3104ffc8798827fd43cc413fe21e6209f710f3104ffec598826ff62cc413ff3166201bf98b3104ffac5988b6fd62cc413fe3166201bf18b3116ffea5988b7fe52cc45bfea96622dff14b3116ffe85988b7bf42cc45bff216622dff50b3116f7a85988b7fc42cc413ff9966209f7ccb3104ffc6598827fd32cc45bee9966209ff0cb3117ffea3988037f51cc409ff28e6200ff54731006faa398813fc51cc45dffa0e6204ff90731177fa8398813fc41cc45bff90e6204ff8873116ffa4398813fc21cc413ffb066209ff98331005fcc198827fd60cc4017eb066209ff1833117ffea1988bffc50cc45dffa06622eff90331177fa81988bbfc40cc45bff906622dff8833116ffa41988b7fc20cc409ffb2c6204bfd9631027fccb1880efe658c409bf32c62039f99631027facb18802fd658c409beb2c62009f59631027f8cb18812fc658c409ffb246204bfd9231027fcc91880afe648c409df3246202af99231027fac9188aefd648c409deb246200af59231027f8c918812fc648c457ffaa4622bff9523115ffaa9188affc548c44f7eb1c622cffd4e3104ffca718803fd538c413fe29c622bffd0e3104ffc87188affd438c413fe21c6204ffd8a31025fec518813fe628c4037f3146204ff58a31155fac518813fc628c4097e314622affd4a31157fca5188abfd528c455fe294622affd0a311577e85188abfe428c455fea14622aef50a31157f88518827ff328c455ff194622aff4ca3104ff86518812fe618c409ffa8c6204dfd4631027fca318813fd518c409bea8c6204ff14631027fe8318813fe418c409fea0c6204ff10631027fe6318813df318c413fb98c6204ffc8631027fc4318813fd218c409fe10c6204ffd
  | 7 => 0xa98dfff4054c6fff202a637ff501531bff880a98dbff2054c6dff102a636ff481531b7f840a980f7f64d4407bf326a203df5935101ef8c9a880f7f63d4407bf31ea203df58f5101ef8c7a88d77f43d446bbf21ea235df50f511aef887a880f7f62d4407bf316a203df58b5101ef8c5a88d37f42d44699fa16a234df90b511a6fa85a88d33d42d4469be216a234dfccb511a6fc65a88d37d32d4469be196a235dfd0751026fc83a88d77d41d4409be20ea234dfc8751026fc43a88d37d21d4409be10ea203dfd835101efcc1a88027e60d4407beb06a203df183511aefe81a88d77e40d446bbea06a235df103511a6fe41a88d37e20d4469be906a234df0835101dfacb288c27d6594409ffb24a204bfd9251027fcc92880afe6494409feb24a233bf59251027f8c928812fc6494407ffaa4a203ff9525101ffaa92880ffc5494409ffb1ca204ff98e5104dfcc728813fd63944017eb1ca204ff18e5101ffea72880ffe5394407fea9ca203ff14e5119ffe87288cffe4394467fea1ca233ff10e51027fec528812ff6294409ff314a201bf98a51027fac5288cafd6294409fe314a204bf18a5101ffea52880ffe5294407fea94a203ff14a51197fe85288cbbf4294465ff214a232ff50a511977a85288cbfc4294465ff994a232ff8ca51197fa65288cbfc32944097f30ca204ffd4651026fea32880ff75194409fe28ca204fd14651027fe8328813fe4194409fea0ca204ff10651027fe4328813fe2194409fe90ca204ff08651027fec128813fe60944017f304a204ff58251005fac128813fc6094407ffa84a203ff1425101ef8a1288cfff4094467ff204a233ff5025119ff881288cbff2094465ff104a232ff48251197f84128812ff6554463ffb22a231bfd915118ffcc8a880afe6454463feb22a231bf5915118ff8c8a880afc6454407ffaa2a203dfd515101ffca8a88c77e5454407feaa2a231df5515101ff8a8a880f7c5454401ffb1aa200bfd8d51007fcc6a8803fd6354401fe31aa209bf18d5101ffea6a880f7f5354407ff29aa200df94d5101ffaa6a88037d5354407fe29aa203df14d5118ffe86a88c7fe4354463fea1aa231ff10d51187fec4a88c2ff6254461ff312a201bf98951187fac4a88c2fd6254461fe312a201bf1895101ffea4a880f7f5254407ff292a230df9495101ffaa4a88c37d5254407fe292a203df14951187fe84a88c3bf4254461ff212a230ff509511877a84a88c3fc4254461ff992a230ff8c951187fa64a88c3fc32544077fb0aa203ffd455101feea2a8813fe5154409bf28aa204ff14551026f8a2a880ff45154463ffa0aa204ff9055118ffa82a8813fc4154461ff90aa204ff88551187fa42a8813fc2154401ffb02a200bfd8151007fcc0a8803fd6054401fe302a200bf1815101ffea0a880f7f505440
  | 8 => 0x200201a00e00e00501704000100101802000103103400300100400300000300800500704000001302400504500100400700000200102300200a00000000100900000000100e00100800101800300300800000400600501900600301500001e00101b00401700400300300500001000100801000200300004800000100101000600000000100000100000103f01101d00101200000000100100b03200800601302408300100d00500b00200300000000403900101b00400000900000c00000d00000300f02401600700b00600000400603703500100300000800400100500d00300900600001a00003800100000001600f00200500b00f01801700001d01801002b00200000001dfacb29827ff6494c137fb24a609ff99253015fcc929827fd6494c737eb24a609ff1925304df8c92980fff5494c07ff2a4a603ff5525301ff8a929826fe6394c13ffa9ca609dfd4e5301fbea72980f5f5394c13fe29ca609f714e5304ffe8729827fe4394c13fea1ca609ff10e5304ffec529826ff6294c13ff314a601bf98a5304ffac5298e2fd6294c13fe314a601bf18a5301ffea52980ffe5294c07fea94a603ff14a531c7fe85298e3bf4294c71ff214a638ff50a531c77a85298e3fc4294c13ff994a609f7cca5304ffc6529827fd3294c71ee994a609ff0ca5304ffec329827fe6194c097f30ca609ff58653005fac329827fc6194c07ffa8ca603dfd465301ff8a3298e7ff4194c73ff20ca639ff506531cff883298e3ff2194c71ff10ca638ff486531c7f84329827ff6094c13ff304a600bf9825304ffac129802fd6094c13fe304a603ffd425301ff8a12980f7c5094c73ffa04a639ff902531cffa81298e7fc4094c71ff904a638ff882531c7fa41298e3fc2094c137fb2aa637ffd91531bdfec8a9803bf6454c015fb22a637ff99153015fcc8a98dffd6454c6f7eb22a637ff19153015f8c8a98dfbc6454c055e322a603ffd515301efea8a980ffe5454c07feaa2a637df5515301ff8a8a980eff6354c07ffa9aa603f7d4d5304ffca6a98277e5354c13fe29aa609df14d5301fb8a6a98dfff4354c13ff21aa637ff50d5304ff886a98dbff6254c6d7fb12a636ff9895300dfcc4a98dbfd6254c6d7eb12a636ff1895300df8c4a980fff5254c07bfa92a603ff9495301ffaa4a98db7d5254c07fe292a636ffd09531b77e84a98dbfe4254c6dfea12a636ef509531b7f884a9827ff3254c6def992a636ff8c9531b7fa64a98dbdd3254c13fe192a600ffd8553005fec2a9803fe6154c01feb0aa600ff18553025f8c2a980fff5154c07bfa8aa603ff145531bffe82a98dffe4154c6ffea0aa637ff105531b7fe42a98dbfe2154c6dfe90aa636ff08553007fec0a9802ff6054c01ff302a600ff58153007f8c0a9802fc6054c07ffa82a603ff1415301ef8a0
  | 9 => 0x1643620009542e834e000ed4ed047c000ec8da0d0a5124a63e40006902e260c1feb6856e9281186547cadc00009d41c0d76cb86360007fe7eced26b2572e829ca84c748eec566a74794d9e468e440eee728d0c7ee8a65c094664a4ad443c0872798804674570248224efc5cc764cf2aea51a13cc2aa9e3f2000d1600000000000050c4f00005e6d6e00085ce14000060e540001907504ca502c42660ae096a276aa2342d186462a6692452412eaad408b661e97c44e02e38a5422c2754caac764ce8a0edcb9ec32b22da6262cc0422a4ca320e0bbab7e942ae68f2802e845e03869aeb143a800846c7529305ec046df28ae1800049604b0e203ee934360ba07026fa34cb62514d66d8e57a00006c258c8c000682892194e2204eade000d705f06428887c406e0002f8932de20000007b2000e6c9b20cc8e6e8652200003c03100c00001900901506800b01c00500200000000100000901a00600200300000000a01a00500000100300000200000000200600001700100100200800400100401600300000700000502400700100700200b01600000200400700000100501000900001300300401700000000f00100000800100000100300700100000803f00c00600003800100e00200000300300800000001800204100200600000000000000000200201800701600200000500b00100000105802400500004600400000101800f00203700100300602600100800e00102d00600101a00100e00102001400300900200201800200001000400001b00100000600300100000b00600000f00100400004000002100101501f00b00100100001000001102901601100500d01808100100201200000800100700005500000503b00100300c00800500d00200503e00100800000000700400400200000203500400f00400000200000700300100100101905801500000000200e00104001000700a00604800300600c00500300000101300500600000005001000d00002a00200f00f00b00100000001b02c00c00d02001b02f00300400800202000201501c00000a00000000100001a02000000100200700c01704b00000500300003201e01a00100400700000200100500200500a00d00500302c02200001c00500201800301d00300e00100c01800201600002900000100001600000f00800a00a00000600400300600000e00100000c00600701600c00102001800301200100701f00901500f00b05800400a00200000000501200102e01403202400200200000400200103c00000500100600200008000900203c00600d00300200000300400600200400006000000900002800703000400000100a01500f00200000400803200000500000400200000000000000001100700002d00101603c00200600003700000100600800b0420000130010010170310
  | 10 => 0xbe8068024acc000206a1abf8d780d8000dd40002f62c89bc90c6a883a87861adcc11ebb6e6e7b0d1ca2a91401445812e5bc000ce600000099e216000000648a82e98e0815867cc4c390b8ebbeb38b5ed2a8c8000c2ebfeb1e41e000302000000ecc0007921da6b83fa2dee9685ac640f40004f6bc6000a78000cbae68cd028e00056a0480000000007082e6a04dce000aecdf43ba000d9a480000e28432000000304eb285201e28207296ea1600000000000096878248a26884a000a1e9d2000ad24420000008e8bee0000009f400000055098a5360000000005c080a99264a000a22eae298aa600000024e000736286b00dd088e69e0004d89a6b46020000830c0ccc2bbca00124546c5640a74c4c8016b847d80a48bc92c4880188004e8a6200020c6507a473c4fe6aeb7a1743feee0c9600027a2c033c2a2c0a000afe16a1a0f16d42a9ce3418c312bc41c2a70b2a02c89e71e3ce0de0dc6f2032ab04e49b6b30f12ca84be22a0003a02d876ceda2bc48ec3ae9e9da254ba2c9e4369a400000000057e72c904920bea000a2e1d467e002000000d64896000e6a7f6d3a0520007f055400000098e0ca5c800000052a5f825c00000050eea600000017a000000000d8226c0009169d60000000000000009b457861200053e328b8200009e000bf4000ce4d30340d7c76a084000000d8a0006a4000c1a000400000cb22b44c030a8624eeb0c58c48c0000000002a80000002ec00000000058e230000098582000000000000000000eba2905aea680003f071414664eb928b0ac679c0b40000007f81aa0000a67b6000000bfa000000000006bd8310aaad6075ad3240800072486c4c6000e3e92281c00008e0003ece0c6222c493a8f8f1a99676286a4209e48844ae6ec86e62ebec90e2385e42d0c54b449c8ea4e4c14eddc6e0a1889aeeaf089b023c0ac2f2530a342ca0c2c24152dbcbd00e6d88980994a027a22d4ab637a1eed4abe0150b18b9423a10846e5fe2705a6be40e4c48e7a814b362ce9ce9c0b666301f61e6cbe558d38c00ef8110b5a6064f8d5c2f06ee1006e60005c6000be23960006c4090e40000000000000c40000b2ce2abb208a4343ca0005b0000000000000000baa9feef40000000002505f2a8ae040006d400028a788d9664483e58871a4061b20000000004c400081687c78e59413285461400000021adb2c22af2818d361a8096e4a6961f04de45adac170dba244c723d6bcaa2010a5b415a8fe19c8d66d06cc1bcf0e7fc498da29a2964daa5dc68ec34392e2e3e2ec6bace50712a50c68c9a658a96a92e70500b1c5f66ce2ac7f42fa8eec2c0aea84680a946b62da56464010242e1f24daca25d897488a7e077410cb8cc664ea2aa1e832a438b521861ea3ae9443b6bb4474b24104bae4a4490740596b5cde01ca9e2000a4800
  | 11 => 0xb41b4bceaf0aac97a2e082e9aae8c694c786d845ed7a5ee92a08630c3c2902e16cfa308062000726000b749ac8601fca4e08011694012620ac8a0d276e82647236a88283200065a000a1444612272e22e000202ebc000dfc3e63ac756120dc4bc22ba14405611c7584a8f0658403ea3691020e336918e3641000000082c6727b85a43f688c0d6bd651c85ec1c2082b0e88abee3c2b2000000936000188f1c00004c688df822c0003fca08876000ac89387c81cc1429d8aa000099053a318000000ce8e06518a8064ca420002c6db8000bd40d04bc000d20000000d74000000000000bc0000288806078000000000d1a000cf08ec97678cc02e66000426c521d87d6d2e79e6d60000006201a66c2b108a8ae82ea7066ba6a224a6a6908f0ae7c59ec86ede19ab72db60007d0720a8616e1baa0aeb05b24641e418498686857c0347388125a855a414700a6639ede8316a88d284b296232e3682360fe50681054e5a28e44d0a54374070b86e26b42df0d6814cb884b635ecdc0444c295cae41e0ce0bde000ec48483346c05282666a07be0a29f600c326ba813a838a12a2c0fa982c06ba68ba21477c69a75e16221c628e90840a6462cea2b4e0c0222c94c3612cb26e32adc7905d25b631c1d65dac5e5200c8134cee52e62a0f21be7346f44020000da000000526d4e0007040003f8b2ed8656200041c0ecc62b508c4f10bcc00093e000966d94bfc00078aee4000000534000000ea0000ec01d0cc48d891e0000008ce7fa7466ca000000000356900668000e462a4a5c94649632c18e27e600d8094855e68c03aeee820a4652c3141b83d2ae2deeac0a90d922740b8d84718296e5a6341a4082000d341fa7104fcdc200000068a68407c114ad4c187444e686631e5d4d08000cb08fc40435c3c433a71c486f1e7deaa494c2044d6ca6b7ca446aca1014aa6e0006b4a76716352a24926d560b24503e01b07428eac14a7c1928cc8acb08d268d43dc00019849e9a8000e804a20000003d4000ece5d60003248f0ce2b78166e429e04e2000092380234c6e8863de44800000056c8340009244a050a5a0f028fa9cc7e6e7ed9c79a3887ee7967ea6dacd4d6c8501c8bb8bdc0aab96372508128d487e84406be9c4c9254a354228b565e2210000000000140d6aeac766c04ebeb80afc0000e2844caeb34000d107b4acad14c4600053ce1005e9eca306e4bd2c087ac60a1369ee54421eaf4000000e7829ea529be428000d900006f874ed12eb63b0b98000c3c476d7e3380885b8e8e6f64b4b203824aa3e8c3e44a00000000000000051035077eccc96c92e066686f0c8f4e02af8b0e6c86100d466a7cc3a63228dcb3c06ae12a58730e1e5aac30e1ce1aa8e7d201c722adaf047aed2287acce51e8da95e384c4e44c72a24291a4b8cf4e48652c1e82a37815ee38
  | 12 => 0x978a0653800000082800039c73ae5eb168949128be6bc25a0b666c2e4666000e5687e3d08e0b3ecfc0260a87a6d62dd693c676ee673e42a00000000038ed3c1780006fe698cc678063c466462456b90cfeabc040bf2dd28caad6000000d501ae0226dc0005d0d1e54c988196ad8c7aa56b7062689c7d49fce9c39445cd5e55c0009b8dde0008e2494ab2260e4ee2cc5cc580c417e824a1cdfea3c8d23a25ce65661670a430b48b4c07e3cce947dc4927bc0540e8984b40b4a4ec160074cf809a1c6cb63063c6c884dc2cc6085fa6de4e0c5aac2602e5c39a3482dcdc60ba4607c0c9cc1601a73259cc4a6f0b0aec2cbc7f200000000e08ccecdfa662000c0eb02552000b64ef0000b58000d06a40000cda000000000a287da0000007ba000d02000e3aaf691c29cd04000000000000590000000000890000a0c000560ab4000000000786a60dae0ce00000000000000000077a94a000532b04d0e000000ceac38c70076b2889802a26a65e8f6370c10ad0000decafa822038c6ab547685045dee30c2025e29aaba3da05ce0e95adda03017c49c000000dea43e000c9863e6ea66e00086494eeb803cef29dc77036e97e366a5a4cc0b0bf640e592000000232aceca07e443caae7aa148e0a47e950c12b063b8346db02d25ba42483c05a3324703aa33e130036bda000b8aefa7a8a6c59aa0e8a6e24200d2c3b211a16c4780000006240009ea6381c49068aa2567600f061858a000058cca8703f40002187a000035a9e68c6aee7c600a8460009de87428c0becc823e37e8b4e747ced3e67860e8589e80c61542205f4efe4ba000bc81387722400000005ac2800004f4156000000a383209a0be6c7c6e2c44e9ac28b320ea00000000000000026e998000604000418c60cf60004d4000ab80000005be38c952000e18000012000064454dca00000000024c000cdec266c642c000000da8aa877809c278d5aa8ce529588c29c6a3a344dc88b21e22f40103302920501121deb9c3d8b1a99aee88b80fc69c364c7483617290a0f82842a0e589f2c8edf6042b76b129fa18a1f807aef69f81ac19e0006b004a000000670cd881ad526d2b600000005c421200049aca430e598db45e812a1f4358a72c801d25c299c000e64586972ee210eeca3c8568784a3eb6a000376b3aa980002fcbb000063a632a7a3008089bad0c5fca9a80ca6a3be7e20003a4000000f1846a4840008c08a4ea85402aed982b6000de62fe0002be41a000f14272000e600001822640bc000a26f0052447a27c8803b4e0077615c7c267a02880edd8e92ed884ed8c81e1a2000d54ed61ec246106c82c9084200031a0001dc5480f66e8226970da4d2400095600013eeb498c580574cac6aab9ab6cc6c70c00070e74a0000002529d0856576d005cae76ba44fa0003985560002b8d46ac4c
  | 13 => 0x176168000d58e620008ded4c40ccd64f20001ce5eac50d729f061cc84000b6e516000bf00000009c24160a0000cd2728a7ede400037c34a4d24824ac3ea4446fc2d636c0000002ee75c43adbe0003bc0000001b62940000008a2000a5e00000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc64940101f67f63940102267e63940101f75e63940100065e63940100067d63940101f75d63940100065d63940101f67c63940101f67f62940101067e62940101f76e62940101066e629401021e7d62940101f76d62940100066d62940101f67c629401021f3f429401021f3d42940101f57f71940101f77671940101f57d71940100077571940100057571940101f67e61940101ed7e70940102167e60940101f77710940101f77a10940101f7791094010074ff765401001e7e65540100067d6554010116be6454010006bd6454010006de6354010006dd635401010eee6254010006ed625401001e7f761401001c7f76140101ee7e76140101ed7d761401003e7d76140100047d761401001e7c76140101ee7f64140100fe7e64140101ef3e64140100fe3e641401020e7d64140101ef3d64140100063d64140101ee7c64140101ee7f63140102067e63140101ef5e63140100065e63140100067d63140101ef5d63140100065d63140101ee7c63140101ee7f62140100f67e62140101ef6e62140100f66e62140101fe7d62140101ef6d62140100066d62140101ee7c62140101ff3f42140101ff3d42140101ed7f71140101ef7671140101ed7d711401003f7571140100057571140101ee7e61140101f57e701401003f7a70140100767e60140101ef7710140101ef7a10140101ef791014010004fd76cc01003d7e75cc0100057d75cc0100ee7e65cc0100067d65cc0100e6be64cc010006bd64cc01004ede63cc010006dd63cc0100deee62cc010006ed62cc0100077850cc010004ff768c01004cfd768c0100d67e658c0100067d658c0100cebe648c010006bd648c01004ede638c010006dd638c0100aeee628c010006ed628c010025f6718c010005f5718c010004ff764c0100057f754c01003d7c754c0100c67e654c0100067d654c010005bf744c010035bc744c0100bebe644c010006bd644c01004ede634c010006dd634c0100b6ee624c010006ed624c01004cff760c010024fe760c010004fd760c010024fc760c0100a67e650c0100067d650c01009ebe640c010006bd640c01004ede630c010006dd630c010096ee620c010006ed620c010025f6710c010005f5710c01000778500c010007d9300c010025f77644010006f77644010004f77644010007777544010007747544010027766544010027756544010007b774440101e7b47444010027b66444010027b56444010007d77344010007d47344010027d66344010027d56344010007e772440101d7e47244010027e66244010027e562440101d7b742440101d7b54244010025f77044010027f370440101def66044010027f26044010007765044010007f25044010007725044010007f15044010007745044010007f23044010007f130440101d7f320440101d7f02044010
  | 1 => 0x8c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c100069f4258c10006de4258c10006dd4258c100069d4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c100265f5158c10026de5158c10026dd5158c100265d5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c10006de7058c10006dc7058c10006df5058c10006dc5058c10006df4058c10006de4058c10006dd4058c10006dc4058c10006df2058c10006de2058c10006dd2058c10006dc2058c10026df1058c10026de1058c10026dd1058c10026dc1058c1004cff7694c10024fe7694c10004fd7694c10024fc7694c1001e7e6594c100067d6594c101cebe6494c10006bd6494c1004ede6394c10006dd6394c1003f5f5394c101c6ee6294c10004ff7654c10024fe7654c10004fd7654c10024fc7654c1001e7e6554c100067d6554c10005bf7454c10035bc7454c101bebe6454c10006bd6454c1004ede6354c10006dd6354c101b6ee6254c10005fb7054c10005f87054c10006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ae7458810006ed7458810006ad7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026ef51588100266f5158810026ee5158810026ed51588100266d5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec315881002eef7058810006ee705881002eed705881002eec7058810006ef5058810006ec5058810006ef4058810006ee4058810006ed4058810006ec4058810026ef1058810026ee1058810026ea1058810026ed1058810026e91058810026ec1058810074ff7694010024fe769401001cfd7694010024fc769401001e7e65940100067d659401011ebe6494010006bd6494010006de6394010006dd6394010106ee6294010006ed6294010025f67194010005f571940100067f76940100047f769401001e7e76940101f57d769401001e7d769401001c7d76940101f67c76940101f67f649401011e7e64940101f73e649401011e3e649401022e7d64940101f73d64940100063d64940101f67
  | 2 => 0x267c215941003e7f70594100067e70594100067c70594100067f40594100067e40594100067d40594100067c40594100067f20594100067e20594100067d20594100067c20594100267f10594100267e10594100267d10594100267c1059410006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006bc5359010006bf7259010004bf7259010006be7259010006bd7259010004bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf51590100263f5159010026be5159010026bd51590100263d5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc2159010036bf7059010006be7059010036bd7059010036bc7059010006bf5059010006bc5059010006bf2059010006be2059010006bd2059010006bc2059010026bf1059010026be1059010026bd1059010026bc105901004edf7598c1004ede7598c1004edd7598c1004edc7598c1004edf7498c1004ede7498c1004edd7498c1004edc7498c10006df5498c10006de5498c10006dd5498c10006dc5498c1004edf7298c1004ede7298c1004edd7298c1004edc7298c10006df5298c10006de5298c10006dd5298c10006dc5298c10006df4298c100069f4298c10006de4298c10006dd4298c100069d4298c10006dc4298c10026df7198c10026de7198c10026dd7198c10026dc7198c10026df5198c100265f5198c10026de5198c10026dd5198c100265d5198c10026dc5198c10026df4198c10026de4198c10026dd4198c10026dc4198c10026df2198c10026de2198c10026dd2198c10026dc2198c1004ede7098c1004edc7098c10006df5098c10006dc5098c10006df4098c10006de4098c10006dd4098c10006dc4098c10006df2098c10006de2098c10006dd2098c10006dc2098c10026df1098c10026de1098c10026dd1098c10026dc1098c10004ff7558c1001cfe7558c1001cfc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c10026df7358c10006df5358c10006dc5358c10006df4358c10006de4358c10006dd4358c10006dc4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c10006bf4258c10006bd4258c10006df3258c10006de3258c10006dd3258c10006dc3258c10024ff7158c10024fe7158c10024fd7158c10024fc7158c100267f5158c100267d5158c10026de3158c10026dc3158c1004cff7058c1004cfd7058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df745
  | 3 => 0xc62141100f66c62141102473f42141102473d42141100057d711411024d7e70141100677a70141102477a20141102477920141101ef7b1014110024fe76cc110024fc76cc1100657e75cc1100057d75cc1100067f65cc1100ee7c65cc110006bf64cc1100e6bc64cc110006df63cc11004edc63cc110006ef62cc1100deec62cc110025f671cc110005f571cc110004fe768c1100067f658c1100d67c658c110006bf648c1100cebc648c110006df638c11004edc638c110006ef628c1100aeec628c11004cff764c110004fd764c110024fc764c1100057f754c1100657c754c1100067f654c1100c67c654c110005bf744c11005dbc744c110006bf644c1100bebc644c110006df634c11004edc634c110006ef624c1100b6ec624c110005f7714c110025f4714c110004fe760c1100067f650c1100a67c650c110006bf640c11009ebc640c110006df630c11004edc630c110006ef620c110096ec620c1100057f75841100657c75841100067f65841100767c6584110006bf648411006ebc6484110006df6384110006dc6384110006ef6284110046ec6284110007775184110007755184110025fa7084110026fb6084110025f67684110026f67684110024f67684110007777584110007747584110007776584110007746584110007b7648411023fb46484110007d76384110007d46384110007e76284110237e46284110237b74284110237b54284110025f67084110026f76084110027f36084110007765084110007745084110237f22084110237f120841100267f7559410004ff7459410014fe7459410004fd7459410014fc745941003e7f54594100067e54594100067d545941003e7c5459410004ff735941004cfc735941003e7f535941003e7c5359410004ff725941000cfe7259410004fd725941000cfc725941003e7f52594100067e52594100067d525941003e7c5259410006bf4259410006bd4259410024ff7159410024fe7159410024fd7159410024fc71594100267e51594100267c515941001cff705941001cfd705941003cfc705941003e7c50594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100063f42594100067e42594100067d42594100063d42594100067c42594100067f32594100067e32594100067d32594100067c32594100267f71594100247f71594100267e71594100267d71594100247d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d2159410
  | 4 => 0x45100277810d451001cfc76545100067f655451001e7c6554510006bf645451018ebc6454510006df6354510006dc6354510006ef6254510186ec6254510005fb7054510005f87054510027f0105451001e7f76545100067e76545100067d765451001e7c765451001c7c76545102767f64545100073f64545100063f645451018e7e64545102767d645451018e7c64545102773c645451018e3c64545100067f63545100075f63545100065f635451027e7e63545100067d635451027e7c63545100075c63545100065c635451026e7f62545100076f62545100066f62545101867e625451026e7d62545101867c625451026f6c62545101866c625451026f3f425451026f3d42545100257f71545100677771545100267f615451002776415451027775415451002776315451002776215451026f7521545100077b70545100057c70545100077870545100057870545100267f605451026f7a205451026f7920545100277b1054510027741054510027781054510027701054510004fe76cc5100067f65cc51017e7c65cc510006bf64cc510176bc64cc510006df63cc51004edc63cc510006ef62cc51016eec62cc510005fa70cc510005f970cc51004cfc764c5100067f654c51014e7c654c510006bf644c510146bc644c510006df634c51004edc634c510006ef624c51013eec624c51000775514c510005fb704c510005f8704c510027f0104c51008cfe76941100067f659411001e7e65941100067d659411001e7c6594110006bf649411011ebc6494110006df6394110006dc6394110006ef6294110106ec62941100057e76941100067e76941100047e76941102667f64941100073f64941100063f649411011e7e64941102667d649411011e7c64941102673c649411011e3c64941100067f63941100075f63941100065f63941102267e63941100067d63941102267c63941100075c63941100065c639411025e7f62941100076f62941100066f62941101067e629411025e7d62941101067c629411025f6c62941101066c629411025f3f429411025f3d42941100057d71941100657e709411025f7a209411025f7920941101f77b109411001cff7654110064fd7654110024fc76541100067f655411001e7c6554110006bf6454110116bc6454110006df6354110006dc6354110006ef625411010eec6254110005f77154110025f471541100057e76141100667e76141100047e76141102567f64141100073f64141100063f64141100fe7e64141102567d64141100fe7c64141102573c64141100fe3c64141100067f63141100075f63141100065f63141102067e63141100067d63141102067c63141100075c63141100065c63141102467f62141100076f62141100066f62141100f67e62141102467d62141100f67c62141102476
  | 5 => 0x6df2118d102a6de2118d10006dd2118d102a6dc2118d1004edf7018d1004edd7018d10006df5018d10006dc5018d10006df4018d10006de4018d10006dd4018d10006dc4018d10006df2018d10006de2018d10006dd2018d10006dc2018d102a6df1018d10006dd1018d102a6dc1018d1004cff7694d10004fe7694d10004fd7694d1004cfc7694d100067f6594d1001e7c6594d10006bf6494d101cebc6494d10006df6394d1004edc6394d100675f5394d101c6ec6294d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1001e7c6554d10005bf7454d1005dbc7454d10006bf6454d101bebc6454d10006df6354d1004edc6354d101b6ec6254d10055ee76d8910056ee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910007af74d8910007ac74d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d891029feb70d8910057e870d891029feb10d891029fe810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006af74d8910006ee74d8910006ed74d8910006ec74d8910006ac74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d891029eee71d8910056ed71d891029eec71d8910006ef51d891029eee51d891029eec51d8910006ef41d891029eee41d8910006ed41d891029eec41d891029eee31d891029eec31d891029eef70d8910056ee70d8910056ed70d8910056ec70d8910006ef50d8910006ec50d8910006ef40d8910006ee40d8910006ed40d8910006ec40d891029eef10d8910056ed10d891029eec10d891001e7f76d45100667e76d45100047e76d45100667d76d451001e7c76d45102967f64d45100073f64d45100063f64d45101ae7e64d45102967d64d45101ae7c64d45102973c64d45101ae3c64d45100067f63d45100075f63d45100065f63d451028e7e63d45100067d63d451028e7c63d45100075c63d45100065c63d45102867f62d45100076f62d45100066f62d45101a67e62d45102867d62d45101a67c62d45102876c62d45101a66c62d45102873f42d45102873d42d45100257d71d45100267f61d45100057e70d45100677a70d45100057a70d45100677970d45100267f60d45102877a20d45102877920d45100277b10d45100277410d
  | 6 => 0xe72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d100069f42d8d10006de42d8d10006dd42d8d100069d42d8d10006dc42d8d10006df71d8d102aede71d8d10006dd71d8d102aedc71d8d10006df51d8d102aede51d8d102aedc51d8d10006df41d8d102aede41d8d10006dd41d8d102aedc41d8d10006df21d8d102aede21d8d10006dd21d8d102aedc21d8d102aedf70d8d10006dd70d8d10006df50d8d10006dc50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d10006df20d8d10006de20d8d10006dd20d8d10006dc20d8d102aedf10d8d102aedc10d8d100657e7598d100057d7598d100067f6598d100067c6598d1005dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10055ee7298d10005ed7298d10006ec6298d100057f7558d100657c7558d100067f6558d100067c6558d10005bf7458d1005dbc7458d10006bf6458d10006bc6458d10005ef7258d10055ec7258d10006ec6258d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d10006bf4258d10006bd4258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d1004ede6318d10006dd6318d10006ec6218d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006df6218d10006de6218d10006dd6218d10006dc6218d10007cc6218d10006cc6218d100079f4218d100079d4218d10007da2018d10007d92018d102a7db1018d102a7d81018d1004edf7518d1004ede7518d1004edd7518d1004edc7518d1004edf7418d1004ede7418d1004edd7418d1004edc7418d10006df5418d10006de5418d10006dd5418d10006dc5418d1004edf7218d1004ede7218d1004edd7218d1004edc7218d10006df5218d10006de5218d10006dd5218d10006dc5218d10006df4218d100069f4218d10006de4218d10006dd4218d100069d4218d10006dc4218d1004edf7118d1004ede7118d1004edd7118d1004edc7118d10006df5118d102a6de5118d102a6dc5118d10006df4118d102a6de4118d10006dd4118d102a6dc4118d10
  | 7 => 0x95100057e76195100667e76195100047e76195100067f64195100067e64195100067d64195100067c64195100073c64195100063c64195100067f62195100067e62195100067d62195100067c62195100076c62195100066c62195100073f42195100073d42195101ee7f60195100077a20195100077920195101ef7b10195101ef78101951005dbe76d911005ebe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ac62d9110006ac62d9110007ba20d9110007b920d91102b7bb10d91102b7b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006bc53d9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d91102b6be71d911005ebd71d91102b6bc71d9110006bf51d91102b6be51d91102b6bc51d91102b6be31d91102b6bc31d9110006bf21d91102b6be21d9110006bd21d91102b6bc21d91102b6bf70d911005ebe70d911005ebd70d911005ebc70d9110006bf50d9110006bc50d9110006bf20d9110006be20d9110006bd20d9110006bc20d91102b6bf10d911005ebd10d91102b6bc10d911004cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10006ec62d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df53d8d10006dc53d8d10006df43d8d10006de43d8d10006dd43d8d10006dc43d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006bf42d8d10006bd42d8d10006df32d8d10006de32d8d10006dd32d8d10006dc32d8d10024fe71d8d10024fc71d8d1004cfe70d8d1004cfc70d8d1004cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d100079f42d8d100079d42d8d10007da20d8d10007d920d8d102afdb10d8d102afd810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006d
  | 8 => 0x5bf744c21006dbc744c210006df634c21004edc634c210024fd760c2100067f650c2100a67c650c21004ede630c210006dd630c210025f6710c210005f5710c210005f576c4210026f576c42100277675c42100277575c42100077765c42100077465c42102bfb742c42102bfb542c4210027f260c42100077650c42100077450c421001cfe76d95100667e65d9510006bc64d9510006ec62d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100667f54d95100067e54d95100067d54d95100667c54d951004cfe73d9510004fd73d95100667f53d95100667c53d9510004ff72d951000cfe72d9510004fd72d951000cfc72d95100667f52d95100067e52d95100067d52d95100667c52d9510006bf42d9510006bd42d9510024fe71d9510064fd71d9510024fc71d95100667f51d951001cfe70d9510024fd70d951001cfc70d95100667f50d95100657e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067f62d95100067e62d95100067d62d95100067c62d95100076c62d95100066c62d95100073f42d95100073d42d95100077a20d95100077920d95101f77b10d95101f77810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100063f42d95100067e42d95100067d42d95100063d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d95101f67e71d95100067d71d95101f67c71d95100067f41d95101f67e41d95100067d41d95101f67c41d95101f67e31d95101f67c31d95100067f21d95101f67e21d95100067d21d95101f67c21d95101f67f70d95100667e70d951001c7e70d95100067d70d951001c7c70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f20d95100067e20d95100067d20d95100067c20d95101f67f10d95101f67c10d95100667c6559510005bf745951005dbc7459510006bc6459510005df7359510005dc7359510005ef7259510055ec7259510006ec6259510064ff75595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510004fd7459510014fc7459510006bc7459510014bc7459510004ff7359510006df7359510004df735951004cfc7359510006dc735951004cdc7359510004ff7259510006ef7259510004ef725951000cfe7259510004fd725951000cfc7259510006ec725951000cec7259510006bf4259510006bd4259510074ff7159510006f7715951008cff7059510006fb70595100667c505
  | 9 => 0xf7258e1000cfe7258e10004fd7258e1000cfc7258e10006bf4258e10006bd4258e100067f6518e100067c6518e1004ede6318e10006dd6318e1004cff7694e10004fe7694e10004fd7694e1004cfc7694e100067f6594e1001e7c6594e100775f5394e10004ff7654e10004fe7654e10004fd7654e10004fc7654e100067f6554e1001e7c6554e10005bf7454e1006dbc7454e100767e76d46100767d76d46102f67f64d46101ae7e64d46102f67d64d46101ae7c64d46100067f63d461028e7e63d46100067d63d461028e7c63d46102ee7f62d46101a67e62d46102ee7d62d46101a67c62d46102ef3f42d46102ef3d42d46100057e70d46100777a70d46100057a70d46100777970d46100267e60d46102ef7a20d46102ef7920d46100277710d46100277b10d46100277810d461001cff765461001e7e65546100067d6554610005fb7054610005f8705461001e7f765461001e7c76546102e67f645461018e7e64546102e67d645461018e7c64546100067f635461027e7e63546100067d635461027e7c63546102de7f62546101867e62546102de7d62546101867c62546102df3f42546102df3d42546100777771546100077b70546100057c70546100077870546100057870546100267e60546102df7a20546102df7920546100277710546100277b10546100277810546100067f65cc61017e7c65cc61004ede63cc610006dd63cc610005fa70cc610005f970cc61004cff764c6100067f654c61014e7c654c61004ede634c610006dd634c610005fb704c610005f8704c61001cfe7694210024fd769421001e7e65942100067d6594210025f67194210005f5719421001e7e769421001e7d76942102d67f649421011e7e64942102d67d649421011e7c64942100067f63942102267e63942100067d63942102267c63942102167f62942101067e62942102167d62942101067c62942102173f42942102173d42942100077671942100057d71942100077571942100057571942102177a20942102177920942101f77b109421003cff76542100067f655421001e7c65542100057e76142100767e76142100767d76142102ce7f64142100fe7e64142102ce7d64142100fe7c64142100067f63142102067e63142100067d63142102067c63142102c67f62142100f67e62142102c67d62142100f67c62142102c73f42142102c73d42142100757f71142100777671142100057d71142100777571142100057571142100777a70142102c77a20142102c77920142101ef7b10142100757e75cc2100057d75cc2100067f65cc2100ee7c65cc210006df63cc21004edc63cc210024fd768c2100067f658c2100d67c658c21004ede638c210006dd638c210025f6718c210005f5718c2100057f754c2100757c754c2100067f654c2100c67c654c210
  | 10 => 0x9610004fd73d96100767f53d96100767c53d9610004ff72d961000cfe72d9610004fd72d961000cfc72d96100767f52d96100067e52d96100067d52d96100767c52d9610006bf42d9610006bd42d9610006f571d96101f67e51d96101f67c51d9610006fa70d96100767f50d96100067f64d96100067e64d96100067d64d96100067c64d96100067f62d96100067e62d96100067d62d96100067c62d96100073f42d96100073d42d96100077571d96100077a70d96100077a20d96100077920d96101f77b10d96101f77810d96100067f74d96100067e74d96100067d74d96100067c74d96100067f73d96100067e73d96100067d73d96100067c73d96100067f43d96100067e43d96100067d43d96100067c43d96100067f72d96100067e72d96100067d72d96100067c72d96100067f42d96100063f42d96100067e42d96100067d42d96100063d42d96100067c42d96100067f32d96100067e32d96100067d32d96100067c32d96100067d71d96100067571d96100067f41d96101f67e41d96100067d41d96101f67c41d96101f67e31d96101f67c31d96100067f21d96101f67e21d96100067d21d96101f67c21d96100067e70d96100067a70d96100067f40d96100067e40d96100067d40d96100067c40d96100067f20d96100067e20d96100067d20d96100067c20d96101f67f10d961001cff76596100767c65596100067f7559610004ff7459610014fe7459610004fd7459610014fc7459610004ff735961004cfc7359610004ff725961000cfe7259610004fd725961000cfc7259610006bf4259610006bd42596100767f5159610024fc70596100767c50596100767e76196100067f64196100067e64196100067d64196100067c64196100067f62196100067e62196100067d62196100067c62196100073f42196100073d42196100777571196100777a70196100077a20196100077920196101ef7b10196101ef7810196100067f65d8e100067c65d8e1001cfe75d8e10004fd75d8e1001cfc75d8e10004ff74d8e10014fe74d8e10004fd74d8e10014fc74d8e10006df43d8e10006dc43d8e10004ff72d8e1000cfe72d8e10004fd72d8e1000cfc72d8e10006bf42d8e10006bd42d8e10006df32d8e10006dd32d8e10006f571d8e102aede31d8e102aedc31d8e10006fa70d8e10004fd7698e100757e7598e100057d7598e100067f6598e100067c6598e10006df6398e1004cff7658e100057f7558e100757c7558e100067f6558e100067c6558e10005bf7458e1006dbc7458e10004ff7558e100067f7558e100047f7558e1001cfe7558e1001cfc7558e100067c7558e1001c7c7558e10004ff7458e10006bf7458e10004bf7458e10014fe7458e10004fd7458e10014fc7458e10006bc7458e10014bc7458e10006df7358e10004f
  | 11 => 0x67d72597100067c72597100067f42597100063f42597100067e42597100067d42597100063d42597100067c42597100067f32597100067e32597100067d32597100067c32597100267f71597100267e71597100267d71597100267c71597100267f41597100267e41597100267d41597100267c41597100267f31597100267e31597100267d31597100267c31597100267f21597100267e21597100267d21597100267c21597100067f70597100067d705971008e7c70597100067f40597100067e40597100067d40597100067c40597100067f20597100067e20597100067d20597100067c20597100267f10597100267e10597100267d10597100267c1059710004ff7558f1001cfe7558f1001cfc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f10026df7358f10006df4358f10006dc4358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f10006bf4258f10006bd4258f10006df3258f10006dd3258f10024fc7158f100267f5158f100267d5158f10026de3158f10026dc3158f1004cff7694f10024fe7694f10004fd7694f10024fc7694f1001e7e6594f100067d6594f1008f5f5394f10004ff7654f10024fe7654f10004fd7654f10024fc7654f1001e7e6554f100067d6554f10005bf7454f10085bc7454f10005fb7054f10005f87054f10064fd76943101f67f659431001e7e65943100067d659431001e7c65943101f57d76943100067d76943101f67f649431011e7e64943103167d64943101f67c64943101f67f63943102267e63943100067d63943101f67c63943101f67f62943101067e629431030e7d62943101f67c629431030f3f429431030f3d42943101f57d719431001cff7654310024fc765431001e7e65543100067d6554310005f77154310025f471543101ed7d761431008e7d76143101ee7f64143100fe7e64143103067d64143101ee7c64143101ee7f63143102067e63143100067d63143101ee7c63143101ee7f62143100f67e62143102fe7d62143101ee7c62143102ff3f42143102ff3d42143101ed7f71143101ed7d711431008f7a701431008d7e75cc3100057d75cc3100ee7e65cc3100067d65cc31004ede63cc310006dd63cc310025f671cc310005f571cc3100077850cc3100d67e658c3100067d658c3102aedf638c31004edc638c31004cff764c3100057f754c31008d7c754c3100c67e654c3100067d654c310005bf744c310085bc744c31004ede634c310006dd634c310005f7714c310025f4714c3100a67e650c3100067d650c3102a6df630c31004edc630c31000778500c310007d9300c3100767e65d9610074fd75d9610004ff74d9610014fe74d9610004fd74d9610014fc74d96100767f54d96100067e54d96100067d54d96100767c54d961004cfe73d
  | 12 => 0x870544303767e605443027f5f305443027f7a305443027f79305443004ddd768c4302a6dd768c430004dd768c4302a75e758c4302a75d758c43009dde748c4302a79e748c43009d9e748c4302a79d748c4302a5dc748c4302a5df728c43036ddd728c4303679f428c4303679d428c43004dde718c43004fd6718c43004edf618c4302a6dd618c4302a75f518c4302a75d518c430005dd708c4302aede608c43004fda608c4300d4ff769403004cfe769403001cfd769403004cfc769403001e7e65940300067d659403004dde7394030005dd73940300067f769403001e7e769403001e7d76940302267c76940302267f649403011e7e649403035e7d64940302267c64940302275e73940300075d73940302267e639403035f5f43940302275c43940302267f62940301067e62940303567d62940301067c62940303573f42940303573d42940302275f32940303575d32940300057d71940301f67e61940300067d61940300075e31940302275c31940302057e709403034e7e60940302275f30940302277a30940302277930940300d4ff765403001e7f76140302067e76140300a67d761403001e7c76140302067f64140300fe7e64140303467d64140302067c64140302075e73140300a75d73140302067e63140303475f43140302075c43140302067f62140300f67e621403033e7d62140300f67c621403033f3f421403033f3d42140302075f321403033f5d32140300057d71140301ee7e61140300067d61140300075e31140302075c31140302257e70140300a77a70140300d67e60140302075f30140302077a301403020779301403033f7a201403033f79201403004ddf764c030006df764c030004df764c0300075f754c0300075c754c0300079f744c03009dde744c03009ddc744c0303279c744c03009d9c744c030335df724c030335dd724c03031f9f424c03031f9d424c0302a5dc714c030006dd614c0300075f514c0300075d514c03004ddf704c03004fdb704c03032ede604c03004fda604c0300075e504c0300075c504c030327da404c030327d9404c03031fda204c03031fd9204c0300267f7559710004ff7459710014fe7459710004fd7459710014fc745971008e7f54597100067e54597100067d545971008e7c5459710004ff735971004cfc735971008e7f535971008e7c5359710004ff725971000cfe7259710004fd725971000cfc725971008e7f52597100067e52597100067d525971008e7c5259710006bf4259710006bd4259710024fc71597100267e51597100267c515971008e7f50597100067f74597100067e74597100067d74597100067c74597100067f73597100067e73597100067d73597100067c73597100067f43597100067e43597100067d43597100067c43597100067f72597100067e7259710
  | 13 => 0x41301ee7c61141300075f31141300075d31141303ad7e70141300c77a70141302077b30141300067f658c1300d67c658c130006bf648c1300cebc648c13004dfa708c13004efb608c1300075f658c1300075c658c1300079f648c1300cede648c1300cedc648c1303a79c648c1300ce9c648c13039edf628c13039edd628c13039f9f428c13039f9d428c130005dd718c1302aedc618c1300075f518c1300075d518c13004dde708c13004edf608c13004fdb608c1300075e508c1300075c508c13004e7f7559430004ff7459430014fe7459430004fd7459430014fc74594300a67f54594300067d545943004cff735943004cfe735943004cfd735943004cfc735943004e7e535943004e7c5359430004ff725943000cfe7259430004fd725943000cfc72594300a67f52594300067d5259430006bf4259430006bd425943004edf3259430006dd3259430004ff7159430024fc71594300a67f51594300a4fc70594300a67c5059430004ff755843001cfe755843001cfc7558430004ff7458430014fe7458430004fd7458430014fc7458430006df435843004edc4358430004ff725843000cfe7258430004fd725843000cfc7258430006bf4258430006bd425843004edf3258430006dd325843004ef77158430006f64158430006f5415843004ef7315843004edc315843004ef43158430006f62158430006f52158430024ff705843004edf305843001e7f76d443028e7e76d44300a67d76d443001e7c76d443028e7f64d44301ae7e64d44303967d64d443028e7c64d443028f5e73d44300a75d73d443028e7e63d44303975f43d443028f5c43d443028e7f62d44301a67e62d443038e7d62d44301a67c62d443038f3f42d443038f3d42d443028f5f32d443038f5d32d44300267e61d44300067d61d44300267c61d44302a75c31d44300057e70d44300d67e60d443028f5f30d443028f7a30d443028f7930d4430024ff769443004cfe7694430004fd769443027d7d7594430026f66194430006f56194430004ff7654430004fd765443004cfc765443027e7f655443001e7e65544300067d655443001e7c6554430005df735443004ddc7354430026f66154430006f56154430005fb7054430005f870544300067f765443027e7e76544300067d765443027e7c765443027e7f645443018e7e64544303867d645443027e7c64544300075f735443027f5c735443027e7e63544303875f435443027f5c435443027e7f62544301867e625443037e7d62544301867c625443037f3f425443037f3d425443027f5f325443037f5d325443028d7f71544300a77771544300267e615443027f7661544300267661544300067d615443027f7561544300067561544300267c61544302a75c31544300077b70544300057c70544300077870544300057
  | 14 => 0x19ebc649453004dde7394530005dd7394530004ff7654530004fe7654530004fc76545300067f655453001e7e65545300067d655453001e7c6554530006bf645453018ebc64545300067f76545300057e76545300067e76545300047e76545300067d76545300057c76545300067c76545300047c76545304067f64545300073f64545300063f645453018e7e64545304067d645453018e7c64545304073c645453018e3c64545303fe7f62545301867e62545303fe7d62545301867c62545303ff3f42545303ff3d42545300c57f71545300c77771545300067f61545300267e61545300267c61545300057c705453027f7b3054530005de76cc53004ede76cc530004de76cc5300075f65cc5300075c65cc5300079f64cc530176de64cc530176dc64cc5303f79c64cc5301769c64cc5303eedf62cc5303eedd62cc5303ef9f42cc5303ef9d42cc530026de61cc530026dc61cc5300075f51cc5300075d51cc530005de70cc53004edf60cc53004fdb60cc5300c57e758c5300057d758c5300067f658c5301667c658c5300bdbe748c530005bd748c530006bf648c53015ebc648c5303e5dd738c530006f7618c530026f4618c530005fa708c530005f9708c53004fd8308c530024fc764c5300067f654c53014e7c654c530006bf644c530146bc644c530006f7614c530026f4614c530005fb704c530005f8704c530024dc764c5300075f654c5300075c654c5300079f644c530146de644c530146dc644c5303df9c644c5301469c644c5303d6df624c5303d6dd624c5303d79f424c5303d79d424c53004ddf714c53004fd7714c530007d7614c530026de614c530026dc614c530007d4614c5300075f514c5300075d514c530007db704c530005dc704c530007d8704c530005d8704c53004edf604c53004fdb604c5300ecfe76941300067f659413001e7e65941300067d659413001e7c6594130006bf649413011ebc64941300c77b50941300057e76941300067e76941300047e76941303ce7f64941300073f64941300063f649413011e7e64941303ce7d649413011e7c64941303cf3c649413011e3c64941303c67f62941301067e62941303c67d62941301067c62941303c73f42941303c73d42941300057d71941300067f61941301f67c61941300075f31941300075d31941300c57e70941302277b309413001cff76541300c4fd765413004cfc76541300067f655413001e7c6554130006bf6454130116bc6454130005df735413004ddc73541300057e76141300c67e76141300047e76141303be7f64141300073f64141300063f64141300fe7e64141303be7d64141300fe7c64141303bf3c64141300fe3c64141303b67f62141300f67e62141303b67d62141300f67c62141303b73f42141303b73d42141300057d71141300067f611
  | 15 => 0xe62195300067d62195300067c62195300073f42195300073d42195300057d71195302067f60195302077b30195302077830195300bdbe76d91300bebe76d9130014be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130005bf72d9130005bd72d9130006bf62d9130006be62d9130006bd62d9130006bc62d9130427bb30d9130427b830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130006bf73d9130426be73d91300bebd73d9130426bc73d9130006bf53d9130426be53d9130426bc53d9130006bf72d9130004bf72d9130006be72d9130006bd72d9130004bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d9130426bf32d9130006be32d9130006bd32d9130426bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006bc51d9130426bf31d9130426bc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d9130426bf70d91300bebe70d91300bebd70d91300bebc70d9130006bf50d9130006bc50d9130426bf30d91300bebd30d9130426bc30d9130006bf20d9130006be20d9130006bd20d9130006bc20d913001cfc7654d300067f6554d3001e7c6554d30005bf7454d300bdbc7454d30006bf6454d301bebc6454d3004f5c5354d30005fb7054d30005f87054d300067f65d85300067c65d8530006bf64d8530006bc64d85300067f75d853001cfe75d8530004fd75d853001cfc75d85300067c75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d8530004ff72d853000cfe72d8530004fd72d853000cfc72d8530006bf42d8530006bd42d8530006f721d8530006f421d8530024fe70d85300c57e75985300057d75985300067f65985300067c65985300bdbe7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300c57c75585300067f65585300067c6558530005bf74585300bdbc7458530006bf6458530006bc6458530005ef72585300b5ec72585300c57e75185300057d75185300067f65185300067c6518530006bf6418530006bc6418530026f66118530006f5611853001e7f76d45300057e76d45300c67e76d45300047e76d45300c67d76d45300c57c76d453001e7c76d453001c7c76d453041e7f64d45300073f64d45300063f64d45301ae7e64d453041e7d64d45301ae7c64d453041f3c64d45301ae3c64d45304167f62d45301a67e62d45304167d62d45301a67c62d45304173f42d45304173d42d45300067f61d45300267e61d45300267c61d45300057e70d453028f7b30d4530004fe7694530004fd7694530024fc769453040d7d75945300067f659453001e7c6594530006bf6494530
  | 16 => 0x423043f3d421423043f5f321423043f5d32142300057d71142301ee7e61142300067d61142300075e31142300075c31142300d77a70142302077b3014230005dd76cc23004edd76cc23004f5e75cc23004f5d75cc2300cdde74cc23004ddc74cc23004ddf72cc230435dd72cc23042f9f42cc23042f9d42cc2302adde71cc230006dd61cc2300075f51cc2300075d51cc23004fda60cc2300075e50cc230007da50cc2300075a50cc230007d950cc2300075c50cc23001cfe76d95300c67e65d9530006bc64d9530004ff74d9530014fe74d9530004fd74d9530014fc74d95300c67f54d95300067e54d95300067d54d95300c67c54d953004cfe73d95300c4fd73d953004cfc73d95300c67f53d9530004ff72d953000cfe72d9530004fd72d953000cfc72d95300c67f52d95300067e52d95300067d52d95300c67c52d9530006bf42d9530006bd42d9530024fe71d9530004fd71d95300c67f51d95300c67c51d953004cfd70d95300c67f50d95300c57e76d953001c7e76d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95300067f62d95300067e62d95300067d62d95300067c62d95300073f42d95300073d42d95300057d71d95302277b30d95302277830d95300067f74d95300067e74d95300067d74d95300067c74d95300067f73d95302267e73d95300067d73d95302267c73d95300067f43d95302267e43d95300067d43d95302267c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300063f42d95300067e42d95300067d42d95300063d42d95300067c42d95302267f32d95300067e32d95300067d32d95302267c32d95300067f71d95300067e71d95300067d71d95300047d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95302267f31d95302267c31d95300067f21d95300067e21d95300067d21d95300067c21d95302267f70d95300c67e70d95300067d70d95300067f40d95300067e40d95300067d40d95300067c40d95302267f30d95302267c30d95300067f20d95300067e20d95300067d20d95300067c20d95300c67c6559530005bf74595300bdbc7459530006bc64595300c4ff75595300067f7559530004ff7459530006bf7459530004bf7459530014fe7459530004fd7459530014fc7459530006bc7459530014bc74595300d4ff7359530006df7359530004ff725953000cfe7259530004fd725953000cfc7259530006bf4259530006bd4259530004ff7159530024fc71595300c67f51595300ecff7059530006fb70595300c67c50595300057e76195300c67e76195300047e76195300067f64195300067e64195300067d64195300067c64195300073c64195300063c64195300067f62195300067
  | 17 => 0x6bd4258630006df3258630006dd32586300d57e75186300057d75186300cdbe7418630005bd74186300adee7218630005ed7218630026f66118630006f5611863001e7f76d46300d67e76d46300d67d76d463001e7c76d46304867f64d46301ae7e64d46304867d64d46301ae7c64d46300d75e73d46300d75d73d46304875f43d46304875c43d463047e7f62d46301a67e62d463047e7d62d46301a67c62d463047f3f42d463047f3d42d463047f5f32d463047f5d32d46300267e61d46300067d61d46300267c61d46300057e70d463028f7b30d4630024ff7694630004fe7694630004fd7694630004ff7654630004fd7654630004fc76546300067f655463001e7e65546300067d655463001e7c6554630005df735463004ddc73546300067f76546300067e76546300067d76546300067c76546304767f645463018e7e64546304767d645463018e7c64546300075f73546300075c73546304775f43546304775c43546303767f62546301867e62546303767d62546301867c62546303773f42546303773d42546303775f32546303775d32546300d77771546300267e61546300067d61546300267c61546300057c705463027f7b30546300d57e758c6300057d758c6300cdbe748c630005bd748c630026f6618c630006f5618c630005fa708c630005f9708c6302af5e758c6302af5d758c6300cdde748c6302af9e748c6300cd9e748c6302af9d748c6302addc748c6302addf728c63046ddd728c6304679f428c6304679d428c63004dde718c6302afd6618c6302aedd618c630007d5618c6302af5f518c6302af5d518c6302afda708c630005dd708c6302afd9708c63004ede608c630024ff764c630026f6614c630006f5614c630005fb704c630005f8704c630005dd760c63004edd760c63004f5e750c63004f5d750c6300cdde740c63004ddc740c63004ddf720c63045ddd720c6304579f420c6304579d420c63004fd6710c6302aedd610c6302af5f510c6302af5d510c630005dd700c63004fda600c63001cfe769423004cfd769423001e7e65942300067d659423004dde7394230005dd73942300d77b509423001e7e769423001e7d769423044e7f649423011e7e649423044e7d649423011e7c64942300075e73942300075d739423044f5f439423044f5c439423034e7f62942301067e629423034e7d62942301067c629423034f3f429423034f3d429423034f5f329423034f5d32942300057d71942301f67e61942300067d61942300075e31942300075c31942302277b30942300a4ff76542300d67e76142300d67d76142304467f64142300fe7e64142304467d64142300fe7c64142300d75e73142300d75d73142304475f43142304475c431423043e7f62142300f67e621423043e7d62142300f67c621423043f3f421
  | 18 => 0xe765473027d7d76547300067d76547300047d765473027e7c765473027e7f645473018e7e64547304be7d645473027e7c645473027e7f62547301867e62547304b67d62547301867c62547304b73f42547304b73d42547300ef7771547300267e61547300067d61547300267c615473027f5f31547300077b70547300057c705473000778705473000578705473004ddf764c730006df764c73004f5e654c73004f5d654c730146de644c73004edc644c73004edf624c7304aedd624c7304af9f424c7304af9d424c73004fd7714c730026de614c730026dc614c7300075f514c7300075d514c730005dc704c7300c4fd76943302267f659433001e7e65943300067d659433001e7c65943302257d76943300067d76943302267f649433011e7e64943304a67d64943302267c64943302267f62943301067e629433049e7d62943301067c629433049f3f429433049f3d42943300057d71943301f67e61943300067d61943302275f31943300075d319433001cff765433004cfc765433001e7e65543300067d6554330005df735433004ddc73543302057d76143300ee7d76143302067f64143300fe7e64143304967d64143302067c64143302067f62143300f67e621433048e7d62143300f67c621433048f3f421433048f3d42143300057d71143301ee7e61143300067d61143302075f31143300075d31143300ef7a701433048f7a201433048f7920143300d67e65d96300cdbe74d9630005bd74d96300adee72d9630005ed72d96300d4fd75d9630004ff74d9630014fe74d9630006be74d9630014be74d9630004fd74d9630006bd74d9630004bd74d9630014fc74d96300d67f54d96300067d54d9630006dd73d96302267e53d96302267c53d9630004ff72d963000cfe72d9630006ee72d963000cee72d9630004fd72d9630006ed72d9630004ed72d963000cfc72d96300d67f52d96300067d52d9630006bf42d9630006bd42d9630006df32d9630006dd32d9630024fe71d9630004fd71d96300d67f51d9630006fa70d963001cff76596300d67c65596300067f7559630004ff7459630014fe7459630004fd7459630014fc74596300d67f5359630004ff725963000cfe7259630004fd725963000cfc7259630006bf4259630006bd4259630006df3259630006dd3259630004ff7159630024fc71596300d67f515963004cfc70596300d67c505963001cff7654e3001e7e6554e300067d6554e30005bf7454e300cdbc7454e30005fb7054e30005f87054e3004fdb3054e300d57e75986300057d7598630006f76198630004ff755863001cfe755863001cfc7558630004ff7458630014fe7458630004fd7458630014fc7458630006df4358630006dc4358630004ff725863000cfe7258630004fd725863000cfc7258630006bf4258630
  | 19 => 0xc4501ee7d760c4500047d760c45001d7c760c4501ed7f740c4500fd7e740c4504e57d740c4501ed7c740c4502057e730c4501ed7f720c4500f57e720c4504dd7d720c4501ed7c720c4504d73f420c4504d73d420c4501ed7e710c4501ee7f610c4501ee7d610c4501ef5f310c4501ef76310c4501ef5d310c45020775310c4500057e700c4500057d700c4501f67e600c4501377a600c45004e7f7559730004ff7459730014fe7459730004fd7459730014fc74597300ee7f54597300067e54597300067d54597300ee7c545973004cfc735973004e7e535973004e7c5359730004ff725973000cfe7259730004fd725973000cfc72597300ee7f52597300067e52597300067d52597300ee7c5259730006bf4259730006bd4259730004ff7159730024fc71597300ee7f51597300ee7c51597300ee7f50597300067f74597300067e74597300067d74597300067c745973004e7f735973004e7e735973004e7d735973004e7c735973004e7f435973004e7e435973004e7d435973004e7c43597300067f72597300067e72597300067d72597300067c72597300067f42597300063f42597300067e42597300067d42597300063d42597300067c425973004e7f325973004e7e325973004e7d325973004e7c32597300067f71597300047f71597300067e71597300067d71597300067c71597300067f41597300067e41597300067d41597300067c415973004e7f315973004e7e315973004e7d315973004e7c31597300067f21597300067e21597300067d21597300067c21597300067f70597300067d70597300ee7c70597300067f40597300067e40597300067d40597300067c405973004e7f305973004e7e305973004e7d305973004e7c30597300067f20597300067e20597300067d20597300067c2059730004ff755873001cfe75587300067e75587300067d755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc7458730004ff725873000cfe7258730004fd725873000cfc7258730006bf4258730006bd425873004ef7715873004ef7315873004ef4315873028d7f76d473001e7f76d473001c7f76d473028e7e76d473028d7d76d47300ee7d76d47300047d76d473001e7c76d473028e7f64d47301ae7e64d47304ce7d64d473028e7c64d473028e7f62d47301a67e62d47304c67d62d47301a67c62d47304c73f42d47304c73d42d47300267e61d47300067d61d47300267c61d473028f5f31d47300057e70d4730024ff769473004cfe7694730004fd769473001e7e65947300067d659473004dde7394730005dd7394730004ff7654730004fd765473004cfc765473027e7f655473001e7e65547300067d655473001e7c6554730005fb7054730005f8705473027d7f76547300067f76547300047f765473027e7
  | 20 => 0x57d750c550006df630c55004edc630c5505567f649415011e7e64941505567d649415011e7c64941500067f63941502267c639415054e7f62941501067e629415054e7d62941501067c629415054f3f429415054f3d42941500057d71941500067f61941501f67c619415001d7e709415001f7a709415001e7f609415001f7b60941500067f74584500067e74584500067d74584500067c74584500067f73584500067e73584500067d73584500067c73584500067f43584500067e43584500067d43584500067c43584500067f72584500067e72584500067d72584500067c72584500067f42584500063f42584500067e42584500067d42584500063d42584500067c42584500067f32584500067e32584500067d32584500067c325845001e7f715845001e7771584500067f41584501ee7e41584500067641584500067d41584500067541584501ee7c41584500067f21584501ee7e21584500067621584500067d21584500067521584501ee7c21584500067e70584500067c70584500067f40584500067e40584500067d40584500067c40584500067f20584500067e20584500067d20584500067c20584502057f76cc45001d7e76cc45017d7d76cc45001d7c76cc4502057f74cc4500fd7e74cc4505457d74cc4502057c74cc4502075e63cc45017f5d63cc45053f5f43cc4502075c43cc4502057f72cc4500f57e72cc4505357d72cc4500f57c72cc45052f3f42cc45052f3d42cc4502075f32cc45052f5d32cc4500067d61cc4500057e70cc4500057d70cc4502267e60cc45017f7a60cc4501ed7f768c45001d7e768c4501ee7e768c45001c7e768c4501657d768c4501ee7d768c4500047d768c45001d7c768c4501ed7f748c4500fd7e748c4501ef3e748c4500fd3e748c4505257d748c4501ef3d748c4500053d748c4501ed7c748c45014d7d738c4501ed7f728c4500f57e728c45051d7d728c4501ed7c728c4505173f428c4505173d428c4501ed7e718c4501ee7f618c4501ef76618c4501ee7d618c45016775618c45000675618c4501ef5f318c45020777318c4500057e708c4500057d708c4501f67e608c4501677a608c45014d7f764c45001d7e764c45014d7d764c45001d7c764c45050d7f744c4500fd7e744c45050d7d744c4500fd7c744c45014f5e634c45014f5d634c4505075f434c4505075c434c4504fd7f724c4500f57e724c4504fd7d724c4500f57c724c4504f73f424c4504f73d424c4504f75f324c4504f75d324c45014f76614c4500067d614c45014f75614c45000675614c45020777314c4501ef5e314c4500057f704c4500077b704c4500057b704c4500057c704c45000778704c45000578704c4504ee7e604c45014f7a604c4501ed7f760c45001d7e760c4501ee7e760c45001c7e760c4501357d760
  | 21 => 0xd768c6500047d768c6501f57c768c6501f57f748c65011d7e748c6501f73e748c65011d3e748c6505ad7d748c6501f73d748c6500053d748c6501f57c748c6501f57f728c6501057e728c6505a57d728c6501f57c728c65059f3f428c65059f3d428c6501f67d618c6501f75f318c65022777318c6500057e708c6500057d708c6500057f764c6500057e764c6500057d764c6500057c764c6505957f744c65011d7e744c6505957d744c65011d7c744c6500075e634c6500075d634c65058f5f434c65058f5c434c6505857f724c6501057e724c6505857d724c6501057c724c6504ef3f424c6504ef3d424c6504ef5f324c6504ef5d324c6500067d614c65022777314c6501f75e314c6500057f704c6500057c704c6501f57f760c6500057e760c6501f67e760c6500047e760c6500057d760c6501f67d760c6500047d760c6501f57c760c6501f57f740c65011d7e740c65057d7d740c6501f57c740c6501f57f720c6501057e720c6505757d720c6501f57c720c65056f3f420c65056f3d420c6501f67d610c6501f75f310c6501f776310c6501f75d310c65022775310c6500057e700c6500057d700c650004ff74d8d50014fe74d8d50004fd74d8d50014fc74d8d500d6de53d8d500d6dd53d8d50006df43d8d50006dc43d8d50004ff72d8d5000cfe72d8d50004fd72d8d5000cfc72d8d50006bf42d8d50006bd42d8d50006df32d8d50006dd32d8d50024fe71d8d50004fd71d8d500d67f51d8d500d67c50d8d50006df6398d500c5f97098d50005bf7458d50115bc7458d500edfb7058d5004ede6318d50006dd6318d500067f75d8550004ff74d8550014fe74d8550004fd74d8550014fc74d855004cfe73d8550004fd73d8550004ff72d855000cfe72d8550004fd72d855000cfc72d8550006bf42d8550006bd42d8550076f651d8550076f551d85500767c50d8550006f76198550065f97098550005bf7458550115bc7458550005df7358550005dc7358550005ef725855010dec725855008dfb7058550026f66118550006f561185500247c76545505667f645455018e7e64545505667d645455018e7c64545500067f635455027e7c635455055e7f62545501867e625455055e7d62545501867c625455055f3f425455055f3d425455001d7f715455001f7771545500067f61545500077761545500067761545500267e61545500267c61545500077461545500077b70545500057c705455000778705455001e7f605455001f7b6054550004fe76cc550004fd76cc55004cfc76cc550004fe768c550004fd768c550024fc768c55001d7e758c5500057d758c550115be748c550005bd748c550006df638c55004edc638c550004ff764c550004fe764c550004fc764c550004fe760c550004fd760c550024fc760c55001d7e750c550
  | 22 => 0x86502257e73d86500057d73d86500067f63d86500067e63d86500067d63d86500067c63d86500057f72d86501057e72d86500057d72d86501057c72d86500067f62d86500067e62d86500067d62d86500067c62d86500073f42d86500073d42d86500057e70d86500077a70d86500057a70d86500777a60d86500057d76986501f57f749865011d7e74986500057d74986501f57c74986502257e73986500057d73986501f57f72986501057e72986500057d72986501f57c72986500073f42986500073d42986501f67f61986500077761986501ee7e609865008f7a60986500057f745865011d7e74586500057d745865011d7c74586500067f64586500067e64586500067d64586500067c64586500057f73586502257c73586500067f63586500067e63586500067d63586500067c63586500057f72586501057e72586500057d72586501057c72586500067f62586500067e62586500067d62586500067c62586500073f42586500073d42586500077761586501f67e61586500667e60586500677a60586500067f74586500067e74586500067d74586500067c74586500067f73586500067e73586500067d73586500067c73586500067f43586500067e43586500067d43586500067c43586500067f72586500067e72586500067d72586500067c72586500067f42586500063f42586500067e42586500067d42586500063d42586500067c42586500067f32586500067e32586500067d32586500067c32586500067f41586501f67e41586500067d41586501f67c41586500067f21586501f67e21586500067d21586501f67c21586500667e70586500067c70586500067f40586500067e40586500067d40586500067c40586500067f20586500067e20586500067d20586500067c20586501f57f741865011d7e74186501f73e741865011d3e74186500057d74186501f73d74186500053d74186501f57c74186502257e73186501f75e73186500055e73186500057d73186501f75d73186500055d73186501f57f72186501057e72186501f76e72186501056e72186500057d72186501f76d72186500056d72186501f57c72186500073f42186500073d42186501f57e71186501f67f61186501f77661186501f67d61186500077561186500057e70186501f77a70186500057a701865003f7a60186502257f76cc6500057e76cc6500057d76cc6502257c76cc6502257f74cc65011d7e74cc6505cd7d74cc6502257c74cc6502275e63cc6500075d63cc6505c75f43cc6502275c43cc6502257f72cc6501057e72cc6505bd7d72cc6501057c72cc6505b73f42cc6505b73d42cc6502275f32cc6505b75d32cc6500067d61cc6500057e70cc6500057d70cc6501f57f768c6500057e768c6501f67e768c6500047e768c6500057d768c6501f67
  | 23 => 0x1f7a60946500247f76546505ed7f745465011d7e74546505ed7d745465011d7c74546505e67f645465018e7e64546505e67d645465018e7c64546500057f73546502257c735465027e7e63546500067d63546505dd7f72546501057e72546505dd7d72546501057c72546505d67f62546501867e62546505d67d62546501867c62546505d73f42546505d73d425465001d7f715465001f7771546500267e61546500077661546500067d61546500077561546500067561546500267c61546500057f70546500077b705465000778705465001e7e605465001f7a605465004cff76cc650004fe76cc650004fd76cc6502257f75cc65001d7e75cc6500057d75cc65001d7c75cc65004ede63cc650006dd63cc650024ff768c650004fe768c650004fd768c6501f57f758c65001d7e758c6500057d758c65001d7c758c65011dbe748c650005bd748c650004ff764c650004fd764c650004fc764c6500057f754c65001d7e754c6500057d754c65001d7c754c65004ede634c650006dd634c650024ff760c650004fe760c650004fd760c6501f57f750c65001d7e750c6500057d750c65001d7c750c6500057f74d8e5011d7e74d8e500073e74d8e5011d3e74d8e500057d74d8e500073d74d8e500053d74d8e5011d7c74d8e500067f64d8e500067d64d8e500057f72d8e501057e72d8e500076e72d8e501056e72d8e500057d72d8e500076d72d8e500056d72d8e501057c72d8e500067f62d8e500067d62d8e500073f42d8e500073d42d8e500075f32d8e500075d32d8e501f57e71d8e500057d71d8e500057e70d8e500077a70d8e500057a70d8e500d77a60d8e500057d7698e502257f7498e5011d7e7498e500057d7498e502257c7498e502267f6398e500075f6398e500065f6398e502257f7298e501057e7298e500057d7298e501057c7298e500073f4298e500073d4298e501f57e7198e500057d7198e502067e6098e500ef7a6098e500057f7458e5011d7e7458e500057d7458e5011d7c7458e500067f6458e500067d6458e500075f6358e502267e6358e500057f7258e501057e7258e500057d7258e501057c7258e500067f6258e500067d6258e500073f4258e500073d4258e500057f7158e501f57c7158e500c67e6058e500c77a6058e502257f7418e5011d7e7418e500057d7418e502257c7418e502257e7318e502267f6318e502275e6318e502267d6318e500075d6318e500065d6318e502257f7218e501057e7218e500057d7218e501057c7218e500073f4218e500073d4218e502275f3218e500075d3218e501f57e7118e500057d7118e500057e7018e502277a7018e500057a7018e500a77a6018e500057f74d865011d7e74d86500057d74d865011d7c74d86500067f64d86500067e64d86500067d64d86500067c64d
  | 24 => 0xf725803100cfe7258031004fd725803100cfc7258031006bf4258031006bd42580310267f51580310267d5158031026df3158031026dd3158031026fb7058031006fa4058031006f9405803104efb305803104edc305803104ef83058031006fa2058031006f92058031026fb1058031026f8105803111dbe74d8e50005bd74d8e50105ee72d8e50005ed72d8e500a5fa70d8e50006df6398e50004ff7458e50014fe7458e50004fd7458e50014fc7458e500c67f5458e500067d5458e500c6de5358e500c6dd5358e502267c5358e50004ff7258e5000cfe7258e50004fd7258e5000cfc7258e500c67f5258e500067d5258e50006bf4258e50006bd4258e50004ff7158e50024fc7158e500c67f5158e5004ede6318e50006dd6318e500d5fa7018e502257f7494e5011d7e7494e5063d7d7494e502257c7494e5001d7e7394e5001f5e7394e502275e6394e502267d6394e500075d6394e500065d6394e502257f7294e501057e7294e506357d7294e501057c7294e5062f3f4294e5062f3d4294e502275f3294e5062f5d3294e501f57e7194e500057d7194e502277a7094e500057d7094e50227797094e50005797094e5001e7e6094e5001f7a6094e5004c7f7654e506257f7454e500073f7454e500053f7454e5011d7e7454e506257d7454e5011d7c7454e5061f3c7454e5011d3c7454e5061e7f6454e5061e7d6454e5001d7f7354e5001f5f7354e5004e7e6354e500075e6354e5004e5e6354e500075d6354e5004e7c6354e506157f7254e501057e7254e506157d7254e501057c7254e5060e7f6254e5060e7d6254e5060f3f4254e5060f3d4254e5060f5f3254e5060f5d3254e500057f7154e501f57c7154e500057f7054e500077b7054e50007787054e5001e7e6054e5001f7a6054e5003dfa70d8650006f761986500067d7558650004ff7458650014fe7458650004fd7458650014fc74586500667f54586500067e54586500067d54586500667c5458650004ff735865004cfc73586500667f53586500067e53586500067d53586500667c5358650004ff725865000cfe7258650004fd725865000cfc72586500667f52586500067e52586500067d52586500667c5258650006bf4258650006bd4258650066f65158650066f551586501f67c51586500667f505865011dbe7418650005bd7418650005de7318650005dd7318650105ee7218650005ed7218650026f66118650006f56118650075fa70186501f57f749465011d7e74946506057d74946501f57c74946502257e73946500057d73946501f57f72946501057e72946505fd7d72946501f57c72946505f73f42946505f73d429465001d7e719465001f7671946501f77661946501f67d61946500077561946501f77a70946500057d70946501f779709465001e7e6094650
  | 25 => 0x81310067d51d8131006fb50d8131006f850d8131006fb60981310057f755813114d7c7558131005bf7458131145bc7458131005ef725813113dec7258131006f9601813101cfe7518131004fd751813101cfc7518131004ff7418131014fe7418131004fd7418131014fc7418131006df4318131006dc4318131004ff721813100cfe7218131004fd721813100cfc7218131006bf4218131006bd4218131006df3218131006dd32181310067f51181310067d51181312a6de31181312a6dc3118131006fb5018131006f85018131024ff75594310267f7559431004ff7459431014fe7459431004fd7459431014fc74594311367f54594310067e54594310067d54594311367c545943104cfe735943104cfc735943104e7e535943104e7c5359431004ff725943100cfe7259431004fd725943100cfc72594311367f52594310067e52594310067d52594311367c5259431006bf4259431006bd4259431024fe7159431024fc71594310267e51594310267c5159431004ff7059431004fc70594311367f50594311367c50594310067f74594310067e74594310067d74594310067c745943104e7f735943104e7e735943104e7d735943104e7c735943104e7f435943104e7e435943104e7d435943104e7c43594310067f72594310067e72594310067d72594310067c72594310067f42594310063f42594310067e42594310067d42594310063d42594310067c425943104e7f325943104e7e325943104e7d325943104e7c32594310267f71594310267e71594310267d71594310267c71594310267f41594310267e41594310267d41594310267c41594310267f31594310267e31594310267d31594310267c31594310267f21594310267e21594310267d21594310267c21594310067f70594310067e70594310067d70594310067c70594310047c70594310067f40594310067e40594310067d40594310067c405943104e7f305943104e7e305943104e7d305943104e7c30594310067f20594310067e20594310067d20594310067c20594310267f10594310267e10594310267d10594310267c10594310067f759803101cfe7598031004fd759803101cfc75980310067c7598031004ff7498031014fe7498031004fd7498031014fc7498031004ff729803100cfe7298031004fd729803100cfc7298031006bf4298031006bd42980310267f51980310267d5198031026fa7098031006fa4098031006f9409803104efb309803104ef83098031006fa2098031006f92098031026fb1098031026f81098031004ff75580310067f75580310047f755803101cfe755803101cfc75580310067c755803101c7c7558031004ff7458031006bf7458031004bf7458031014fe7458031004fd7458031014fc7458031006bc7458031014bc7458031004f
  | 26 => 0x267f51582310267d5158231026df3158231026dd3158231026fb7058231006fa2058231006f92058231026fb1058231026f8105823101cfe76d953114e7e65d9531004ff74d9531014fe74d9531004fd74d9531014fc74d9531024fd73d953114e7f53d9531004ff72d953100cfe72d9531004fd72d953100cfc72d9531006bf42d9531006bd42d9531006df32d9531006dd32d953104cfd71d953114e7f51d9531004fe70d9531004fd70d953114e7c50d953114e7c6559531005bf7459531145bc7459531005ef725953113dec7259531005fb7059531005f8705953114cff75595310067f7559531004ff7459531006bf7459531004bf7459531014fe7459531004fd7459531014fc7459531006bc7459531014bc745953114e7f54595310067d5459531164ff7359531006df735953127e7e535953127e7c5359531004ff7259531006ef7259531004ef725953100cfe7259531004fd725953100cfc7259531006ec725953100cec725953114e7f52595310067d5259531006bf4259531006bd4259531006df3259531006dd325953117cff7159531006f77159531004ff7059531006fb7059531004fb7059531004fc7059531006f87059531004f8705953114e7c5059531024fc7654d310067f6554d3101e7c6554d31005bf7454d31145bc7454d31005f77154d31025f47154d3104fd43154d3101e7f76d453114e7e76d453114e7d76d453101e7c76d453165e7f64d45311ae7e64d453165e7d64d45311ae7c64d453114f5e73d453114f5d73d45310267f63d453165f5f43d453165f5c43d45316567f62d45311a67e62d45316567d62d45311a67c62d45316573f42d45316573d42d45316575f32d45316575d32d45310257d71d45310267f61d453128f7731d45310275e31d45310275c31d45310277431d45310057e70d453101cff765453114cfd765453104cfc76545310067f655453101e7c6554531005df735453104ddc7354531027d4315453101e7f765453127e7e76545310067d765453101e7c765453164e7f645453118e7e645453164e7d645453118e7c64545310075f73545310075c73545310267f635453164f5f435453164f5c43545316467f62545311867e62545316467d62545311867c62545316473f42545316473d42545316475f32545316475d32545310257f715453114f7771545310267f615453127f7731545310275e31545310275c31545310277431545310275431545310057c705453102777105453114d7e75d81310057d75d813101cfe75d81310067e75d813101c7e75d8131004fd75d81310067d75d81310047d75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d8131004ff72d813100cfe72d8131004fd72d813100cfc72d8131006bf42d8131006bd42d81310067f51d
  | 27 => 0xd74596310067c74596310067f735963127e7e73596310067d735963127e7c73596310067f435963127e7e43596310067d435963127e7c43596310067f72596310067e72596310067d72596310067c72596310067f42596310063f42596310067e42596310067d42596310063d42596310067c425963127e7f32596310067e32596310067d325963127e7c32596310267f71596310267e71596310267d71596310267c71596310267f41596310267e41596310267d41596310267c41596310267f31596310267e31596310267d31596310267c31596310267f21596310267e21596310267d21596310267c21596310067f70596310067e70596310067d70596310067c70596310047c70596310067f40596310067e40596310067d40596310067c405963127e7f305963127e7c30596310067f20596310067e20596310067d20596310067c20596310267f10596310267e10596310267d10596310267c1059631006bf7559231006be7559231006bd7559231006bc755923115ebf7359231666be7359231006bd7359231666bc7359231006bf5359231666be5359231666bc5359231006bf7259231004bf7259231006be7259231006bd7259231004bd7259231006bc7259231006bf5259231006be5259231006bd5259231006bc5259231666bf3259231006be3259231006bd3259231666bc3259231026bf7159231026be7159231026bd7159231026bc7159231026bf51592310263f5159231026be5159231026bd51592310263d5159231026bc5159231026bf3159231026be3159231026bd3159231026bc3159231026bf2159231026be2159231026bd2159231026bc2159231006bf7059231006be7059231006bd7059231006bc7059231006bf5059231006bc5059231666bf3059231666bc3059231006bf2059231006be2059231006bd2059231006bc2059231026bf1059231026be1059231026bd1059231026bc105923101cff7654e31024fc7654e3101e7e6554e310067d6554e31005bf7454e3115dbc7454e311bebe6454e31006bd6454e3104f5c5354e31005f77154e31025f47154e3104fd73154e310067f759823101cfe7598231004fd759823101cfc75982310067c7598231004ff7498231014fe7498231004fd7498231014fc7498231004ff729823100cfe7298231004fd729823100cfc7298231006bf4298231006bd4298231024fe71982310267f51982310267d5198231026fa7098231006fa2098231006f92098231026fb1098231026f81098231004ff75582310067f75582310047f755823101cfe755823101cfc75582310067c755823101c7c7558231004ff7458231014fe7458231004fd7458231014fc7458231004ff725823100cfe7258231004fd725823100cfc7258231006bf4258231006bd4258231024fc7158231
  | 28 => 0x81511ee7e21181510067d21181511ee7c21181510067f40181510067e40181510067d40181510067c40181510067f20181510067e20181510067d20181510067c20181511ee7f101815104e7f7559731004ff7459731014fe7459731004fd7459731014fc745973117e7f54597310067d5459731024fc735973104e7e535973104e7c5359731004ff725973100cfe7259731004fd725973100cfc725973117e7f52597310067d5259731006bf4259731006bd425973104edf3259731006dd325973117e7f5159731004ff7059731004fc705973117e7c505973128e7e76d473117e7d76d473128e7f64d47311ae7e64d47316867d64d473128e7c64d473128f5e73d473117f5d73d47310267e63d47316875f43d473128f5c43d473128e7f62d47311a67e62d473167e7d62d47311a67c62d473167f3f42d473167f3d42d473128f5f32d473167f5d32d47310275e31d47310277631d47310275c31d47310057e70d473101cff765473104cfc765473101e7e65547310067d6554731005df735473104ddc7354731027d6315473101e7f765473101e7c765473127e7f645473118e7e64547316767d645473127e7c64547310075f735473127f5c73547310267e63547316775f435473127f5c435473127e7f62547311867e625473166e7d62547311867c625473166f3f425473166f3d425473127f5f325473166f5d325473117f7771547310275e31547310277631547310275631547310275c31547310057c705473101cfe7598331004fd759833101cfc7598331004ff7498331014fe7498331004fd7498331014fc7498331024fe7398331024de7398331006df439833104edc4398331004ff729833100cfe7298331004fd729833100cfc7298331006bf4298331006bd429833104edf3298331006dd32983310067f51983310067d51983312aede319833104edc319833104efa709833104edf309833104efb309833104ef83098331004ff75583310067f75583310047f755833101cfe755833101cfc75583310067c755833101c7c7558331004ff7458331014fe7458331004fd7458331014fc7458331024fc7358331004ff725833100cfe7258331004fd725833100cfc7258331006bf4258331006bd42583310067f51583310067d515833104efb705833104efb305833104ef830583310267f7559631004ff7459631014fe7459631004fd7459631014fc74596311667f54596310067e54596310067d54596311667c54596311667f5359631004ff725963100cfe7259631004fd725963100cfc72596311667f52596310067e52596310067d52596311667c5259631006bf4259631006bd4259631024fc71596310267e51596310267c5159631004ff7059631004fc70596311667f50596311667c50596310067f74596310067e74596310067
  | 29 => 0x67d6258d510073f4258d510073d4258d510075f3258d510075d3258d510057f7158d51007777158d51005777158d5114f776158d510057f7058d510077b7058d510057b7058d510057c7058d51007787058d51005787058d510057e7618d5127d7f7418d5118d7e7418d510057d7418d5127d7c7418d5127e7f6318d5127f5e6318d5127e7d6318d510075d6318d510065d6318d5127d7f7218d511857e7218d510057d7218d511857c7218d510073f4218d510073d4218d5128e7f6118d51137776118d510057e7018d510057d7018d510057f74d815118d7e74d81510057d74d815118d7c74d815127d7e73d81510057d73d81510057f72d81511857e72d81510057d72d81511857c72d81510073f42d81510073d42d815108e7f61d815108f7761d81510057f749815118d7e74981510057d749815118d7c74981510067f64981510067e64981510067d64981510067c649815127d7e73981510057d73981510067f63981510067e63981510067d63981510067c63981510057f72981511857e72981510057d72981511857c72981510067f62981510067e62981510067d62981510067c62981510073f42981510073d42981510077571981510777761981510057e70981510067f60981510077b60981510057f74581510073f74581510053f745815118d7e74581510057d745815118d7c74581510073c745815118d3c74581510057f73581510075f73581510055f735815127d7c73581510075c73581510055c73581510057f72581510076f72581510056f72581511857e72581510057d72581511857c72581510076c72581511856c72581510073f42581510073d42581510077771581510677761581510077b60581510067e60581510057e76181510057f741815118d7e74181510057d741815118d7c74181510067f64181510067e64181510067d64181510067c641815127d7e73181510057d73181510067f63181510067e63181510067d63181510067c63181510057f72181511857e72181510057d72181511857c72181510067f62181510067e62181510067d62181510067c62181510073f42181510073d421815103e7f611815103f7761181510067f60181510077a60181510067d60181510077960181510067f74181510067e74181510067d74181510067c74181510067f73181510067e73181510067d73181510067c73181510067f43181510067e43181510067d43181510067c43181510067f72181510067e72181510067d72181510067c72181510067f42181510063f42181510067e42181510067d42181510063d42181510067c42181510067f32181510067e32181510067d32181510067c321815103e7f71181510067f41181511ee7e41181510067d41181511ee7c41181511ee7e31181511ee7c31181510067f211
  | 30 => 0xe7394d5127e7f6394d510075f6394d510065f6394d5127f5c6394d5127d7f7294d511857e7294d516b57d7294d511857c7294d516af3f4294d516af3d4294d5127f5f3294d516af5d3294d510257e7194d5127f767194d5127f757194d510257c7194d5101e7f6194d5101f776194d510057e7094d510057d7094d510247c7654d516a57f7454d510073f7454d510053f7454d5118d7e7454d516a57d7454d5118d7c7454d5169f3c7454d5118d3c7454d5169e7f6454d5169e7d6454d5101d7f7354d5101f5f7354d510075f6354d5104e7e6354d5104e7c6354d510075c6354d5104e5c6354d516957f7254d511857e7254d516957d7254d511857c7254d5168e7f6254d5168e7d6254d5168f3f4254d5168f3d4254d5168f5f3254d5168f5d3254d51007777154d510257e7154d510257c7154d51007747154d5101e7f6154d5101f776154d510057f7054d510057c7054d51024fd75d8151004ff74d8151014fe74d8151004fd74d8151014fc74d815104cfe73d8151004fd73d8151004ff72d815100cfe72d8151004fd72d815100cfc72d8151006bf42d8151006bd42d815108efa50d815108e7c50d8151006fb6098151005bf745815118dbc7458151005df7358151005dc7358151005ef7258151185ec7258151006f960181511ee7f7518151024fd7518151004ff7418151014fe7418151004fd7418151014fc741815103e7f54181510067e54181510067d541815103e7c541815104cfe7318151004fd731815103e7f53181510067e53181510067d531815103e7c5318151004ff721815100cfe7218151004fd721815100cfc721815103e7f52181510067e52181510067d521815103e7c5218151006bf4218151006bd42181511ee7e51181511ee7c511815103e7f501815103ef950181510057f74d8d5118d7e74d8d510057d74d8d5118d7c74d8d510067f64d8d510067d64d8d510057f72d8d511857e72d8d510057d72d8d511857c72d8d510067f62d8d510067d62d8d510073f42d8d510073d42d8d511667f61d8d511677761d8d510057e70d8d510057d70d8d5127d7f7498d5118d7e7498d510057d7498d5127d7c7498d5127d7e7398d5127e7f6398d510075f6398d510065f6398d5127d7f7298d511857e7298d510057d7298d511857c7298d510073f4298d510073d4298d5127f5f3298d510075d3298d510057d7198d5127f757198d51005757198d5117f776198d510057e7098d510057d7098d510057f7458d510073f7458d510053f7458d5118d7e7458d510057d7458d5118d7c7458d510073c7458d5118d3c7458d510067f6458d510067d6458d510075f6358d5127e7e6358d510057f7258d510076f7258d510056f7258d511857e7258d510057d7258d511857c7258d510076c7258d511856c7258d510067f6258d51
  | 31 => 0x815300cfe7218153004fd721815300cfc72181530a67f52181530067d5218153006bf4218153006bd4218153006df3218153006dd3218153024fe7118153004fd71181530a67f51181530a6f95018153006fa2018153006f920181530067f74983510067e74983510067d74983510067c74983510067f73983510067e73983510067d73983510067c73983510067f43983510067e43983510067d43983510067c43983510067f72983510067e72983510067d72983510067c72983510067f42983510063f42983510067e42983510067d42983510063d42983510067c42983510067f32983510067e32983510067d32983510067c32983510067f71983510067f41983511f67e41983510067d41983511f67c41983511f67e31983511f67c31983510067f21983511f67e21983510067d21983511f67c219835101e7e709835101e7a70983510067f40983510067e40983510067d40983510067c40983510067f20983510067e20983510067d20983510067c20983511f67f1098351004ff7458e51014fe7458e51004fd7458e51014fc7458e51026df7358e5114ede5358e5114edd5358e51006df4358e51006dc4358e51004ff7258e5100cfe7258e51004fd7258e5100cfc7258e51006bf4258e51006bd4258e51006df3258e51006dd3258e51024fc7158e510267f5158e510267d5158e51026de3158e51026dc3158e51004ff7058e51004fc7058e5114e7c5058e510067f7598251004ff7498251014fe7498251004fd7498251014fc749825104cfe7398251004fd7398251004ff729825100cfe7298251004fd729825100cfc7298251006bf4298251006bd4298251024fe71982510267f51982510267d5198251026fa7098251076f95098251006fa2098251006f92098251026fb1098251026f81098251004ff7458251014fe7458251004fd7458251014fc7458251004ff735825104cfc7358251004ff725825100cfe7258251004fd725825100cfc7258251006bf4258251006bd4258251024fc71582510267f51582510267d5158251026fb7058251066fa50582510667c5058251006fa2058251006f92058251026fb1058251026f81058251024fd75d8d51004ff74d8d51014fe74d8d51004fd74d8d51014fc74d8d511667f54d8d510067d54d8d51166de53d8d51166dd53d8d5127e7c53d8d51004ff72d8d5100cfe72d8d51004fd72d8d5100cfc72d8d511667f52d8d510067d52d8d51006bf42d8d51006bd42d8d51004fe70d8d51004fd70d8d511667c50d8d51006df6398d5114df57198d51005bf7458d5118dbc7458d51005ef7258d51185ec7258d5117df77158d51005fb7058d51005f87058d5104ede6318d51006dd6318d510247e7694d5127d7f7494d5118d7e7494d516bd7d7494d5127d7c7494d5101d7e7394d5101f5
  | 32 => 0xc67f515825304efb70582530c6fa50582530c67c505825304efb305825304ef830582531bdbe76d91531bebe76d9153014be76d91536c73f75d91531bf3c75d91536cf9f53d91536c73e53d91536c73c53d91536cf9c53d9153005bf72d9153005bd72d9153006bf62d9153006be62d9153006bd62d9153006bc62d91536cf3f52d91530073d52d91530079f32d91530079d32d91536cf3f51d91536cf3c50d91536c6bf75d91531bebe75d91531bebd75d91531bebc75d91536cebf73d91536c6be73d91531bebd73d91536c6bc73d91536cebf53d91536c6be53d91531bebd53d91536c6bc53d9153006bf72d9153004bf72d9153006be72d9153006bd72d9153004bd72d9153006bc72d91536cebf52d91536cebe52d91536cebd52d91536cebc52d91536c6bf32d9153006be32d9153006bd32d91536c6bc32d9153006bf71d9153006be71d9153006bd71d9153006bc71d91536cebf51d91536ce3f51d91536cebe51d91536cebd51d91536cebc51d91536c6bf31d91536c6bc31d9153006bf21d9153006be21d9153006bd21d9153006bc21d9153006bf70d9153006be70d9153006bd70d9153006bc70d91536cebf50d91536cebe50d91536cebd50d91536cebc50d91536ce3c50d91536c6bf30d91536c6bc30d9153006bf20d9153006be20d9153006bd20d9153006bc20d9153006bf64d8553006bc64d855328e7f75d855304cfd75d8553004ff74d8553014fe74d8553004fd74d8553014fc74d855317e7f54d85530067d54d855328e7e53d855328e7c53d8553004ff72d855300cfe72d8553004fd72d855300cfc72d855317e7f52d85530067d52d8553006bf42d8553006bd42d8553006df32d8553006dd32d855317ef651d8553004fe70d8553004fd70d855317e7c50d85531bdbe7498553005bd7498553006bf6498553006bc6498553006f76198553005bf74585531bdbc7458553006bf6458553006bc6458553005ef72585531b5ec7258553005fb7058553005f87058553006bf6418553006bc6418553026f66118553006f56118553006bf64d8153006bc64d815304cfd75d8153004ff74d8153014fe74d8153004fd74d8153014fc74d8153004ff72d815300cfe72d8153004fd72d815300cfc72d8153006bf42d8153006bd42d8153024fe71d8153004fd71d81530ee7f51d81530eefa50d81530ee7c50d8153006fa20d8153006f920d81531bdbe7498153005bd7498153006bf6498153006bc64981531b5ee7298153005ed7298153006fb6098153005bf74581531bdbc7458153006bf6458153006bc6458153006bf6418153006bc6418153006f960181532067f751815304cfd7518153004ff7418153014fe7418153004fd7418153014fc74181530a67f54181530067d54181532067e53181532067c5318153004ff721
  | 33 => 0xd00080180000030018000006007006808002a00000280200180060010000038005002800401200b00a002800200300400180080090020080000005000004c0020090058000004001000001c004003002000400e000000001400201700000480060010018020004006001800c0040030020004000000001003800003a0048004004002001001000a004000003800000001200c4014000001000400a000002002001a0020070030000001005003000c0230110028000006018001c000000000801000801c00280200080010010034018002007801800001c006800400800a000800800600a0048000016003001802000c005001000000600a007800400200000f800801a00a002800401c01400000a8000000009000c00a017000800000c00a000000404c001000000001a0020128008016000000800000000000480000040080030004002000000800c000001007000000001c006000400600d002000000000100080000000010028020000004000003003e00300000000080000018004000019015802400200700d800000000300a8048000004000800402c008004800400000200080400000030018000006015000802800e0010060010002001005802c02c001001000400400500280080160050000000000001004800000c00100a80000340200000014000005001801000000100000100000010080000010001000000000a000004800001c0000028024002000000000400a000001803805c000000800400000700080880140010000008004011000000c02e0040050024000007000000800200600300000060360088010004001000007c00e0000000008036006000000000a00d00600100040090008028000001000004800a0010000024002004003003c0040170060004036000000800000200d002800000000a001000800000a0067d7558653004ff7458653014fe7458653004fd7458653014fc745865304cfc735865304e7f535865304e7d5358653004ff725865300cfe7258653004fd725865300cfc7258653006bf4258653006bd425865304edf3258653006dd325865304ef7715865314ef6515865304ef7315865304ef43158653004ff7058653004fc705865314e7c50586530067f7598253004ff7498253014fe7498253004fd7498253014fc749825304cfe739825304e7f539825304e7d5398253004ff729825300cfe7298253004fd729825300cfc7298253006bf4298253006bd429825304edf3298253006dd3298253024fe7198253004fd71982530d67f519825304efa70982530d6f9509825304efb309825304ef83098253004ff7458253014fe7458253004fd7458253014fc745825304cfc7358253004ff725825300cfe7258253004fd725825300cfc7258253006bf4258253006bd4258253004ff7158253024fc7158253
  | 34 => 0x10044001001802400c001000001c002018000000001e00d000001000a00600000140060160000028002002000000000000100300040020030048004000000002001c0020030000004002002000000001e0000020000000000004004001a0030070000000023000001c0000180018008002001000005c0040010128000000002001800c0640040000034004000001803000a0030000000048007001802400200500000000000020058030006000002800c00c000003800400001d007004c002010016804c00601b000002400c00800080040280000030044004002000000401a00000100180000010028024000004000800008000400580080140010000014012001000800c00a00200f801400000000e000000200b003800c00a000000003001000e000000800600e009800c000002002801c0020020050030002013000002c00e0010028000008004002000000200000200040020080010004000000000800000200000e00180060020070044004002000007c0020000018000000005005802400600b0030078000001002800000200201c001004000100180080020050010008006000000000000a010000800000800500e80100060030030034000002001800000000000280040080050048008016000000800003600400a80140060000008010000000008004401400d0048008022001004800c01e000000000003800800180580020170018000000006003801001800a00080000000020018008006002001000001c001001001001a0060000000000000000801800e000007805c008004000000000400b0010000004000001000801c002002000400e008000003001400100000000040120018014000001001001001c003000801001a000000001000200b0000010000000003000400a00a001000c00600400100400000070050014008024000802000c00c001800800e0080058004000009000001402800200080000020180010010000001002000800200c001804c00001400000040040140008000006000000801800a010001001800c0020000000004037000000401000100100040080010008024006000000000801c008000000c01202100080100100020020008000000000805c000000001006c00600b00280000040020018000000002001800800e0020008000038001001006800800100000000000000030008000000000002c000000000000000a005000000400201200000100040030010028018023000000c012018000001800a0090098030012002000005800800d005005400000e000800c002003002001000e0020058014002003000000c000007001004800c002000000c002004003800000e005000800c00a000004005401a0040000010038021003803800800d001004401a005008000c00a009000801803a003003003800400
  | 35 => 0x20008008000000005800000200c00500800000010038004008000000000001a0010000000004003004003c01a0000010000000002000000c01a0150010040002007001811800a006003803400800100080240120010000024012008002000000200900600040000100030000000004004000000200b003001400000a006800002e000002801800600100c002c01a015005800c00200f000800002e014002001c0000060008000002001001800800600a00080380000040000004008000002800000600d0018010000003001809400c00700200280020000088048008003000802000000000300140000000080000000003004807800200700080100000000008018032000002801c006001003000400002800b801401800000a8008008017012800c02400d00380c401c00500400000060380018018010002001001800800d008800000600b00000000380040120000026000000000000000000400140060010048004034002002000003c0180040000000001000002000c004000001800600200000000080000180020002000007001400801c0010000052000000000400200f002000000001100100000160020048018006000002800000000200180140040000058010006008003801000a0000018000002006001800c004001003002c00002100e800000000c003000000001a00280000020030020014020003003800400600000300040060020008000030000008005800a0060028010004011000800c02000100000300000050008000006000000000000a000000001000c0010020008000000004001000c005000000c0040000028030002022003803c002001019001c00200500280000080000008004002000000002c004015000000c00000000300180100230010004000006001803c00201500000380080000010014024004000000400000a00a801c002001000800c000011005004c028003000800c008001000000000001600800200000060038004002001000005800400200280080000020010008008004000003800600f00e00000080020000030000003000006400200000b000801e0000038010020003006001000200000000080000040000028006003001801c0200040068020002005003801c00400c000807800400000600000060010020078000004001002c00a000000800c00000f000000000400000d8028008011009000c002008000800005200a004000c000005001000400000100180000000000010000002004000000000c000000800400a00000900ac032003000803800c00400b004004a00300b0000004001000001c00003c000004c01000100180000040130018000000003006802000000000080040000050058008006002006001400400000100040020030090020002004001000c002001001800400001200200
  | 36 => 0x81037953500000304df003f40000000bd72da0e5a5175540396d2df207800022980004d243a1000035e000128e4cf10660fb400011bc0000aacb4852dc0001fd82e800000003e8051b0038ff600b41002108d950000000000089215155f933d020e28b8e941f9880a2cd113058e85a30000000547521e000068b00015ee1edc00018bc0005230d9d2d444c800000004134e070b5401e3f187150000b143d052ed43640002524000000000021ec00003f00003778e1006509773334fd93a800001cd037721882732f480003d9852056f490600007890664d5c1e0400000000000000000000047e1d3445608a4d9314a475e163d00a0645364400c00015cc4b11d2d431000000057f8000168800039a400052c83d7284ceb1000000005c0d6420d102c062400000015e44e5d22b00000000000ee82c9917e07d80000000973422c2a9000000023940004fa12c100000004fd40002e8533731a8d744d4487d41e433e513800053780000a713440000ad9000000030a00000000a83007098020a8e662968000000000000011bf476c0004a405a63ee000000001eb08780000000000000000044c400000000000000bd6445400035cc00046d8000128d3b52c748054d3d29432d547653a471c40d83f60eccdc43c6cfec16f4bd1385829e15b0ff40001377551891e31c93f803b001616cd3e90a2c0001e64b021334679567d4e635a036c1d88bbf46ad53806803c11d30fbf000015d32a49d7438097e000039923f52e04e7c0004d9d3311ecc9472dc01970000000382800000000002644a29014d148160000011e0292000000056d04924828669044831f0000000342cd8e00008b32fec8452e051b40000f0600004a2000094c55782552e4c622456856a000032143ed3d8306cc6033749d8569c000443c6a200000050028000014000008003000200000580780060020048004008004000802c00000400280000000070000000008001002800802600a0038040000002000000c00800100180440160000040000000002000800000000000100500020270000050000009009805802201000180fc002001000005c00000600000040000010000010002006001005c000002000801800000700180000020000050024000001005000401c001000003000000c001800400600100200000060030000028012000000000801a00700500180060010000018014002005801800400a000803005000b0020004006000000805c00000000a8024000000001800c002005001800c000004001000400600100000140000030050004000000003800400c0060018000058013001000800a001000800400000c0008020004006008001c00600100000040180040070024014005001800006c036000801000000300300040020030008004000000001800c00000400680000000
  | 37 => 0xc742f388d9214018b4498343407cad724a82090000000535473c1ae0ac6000000017e037d2ef518100008810000d0623415e0000078e260803f35ad4da33c13a200009b521a95511b3883008e89213d793ad0000ef731a40600000bea51904544e713304da0aef00013321de4b8e3b58a901ff561b01ed01e55400812664baa08e03f42da40a1428cd37436c46d15306a80000ae0134d15f000000000000001c3000000006a900002c00540a5501680003a8d0a13b040000a740000000000427c0003b50ba2003d5a420dc00000011fd2eed37413e00001644caa0e88f920001078000055b532d3a0000103c206c1102d700001b54138139493d458ca300000cec43e4e121f9c3fe0c6000054f40451ff0000000000032ad3d001e52b65454fa10000623576109116ec0e80001471372c2e108501650000f220000b883c7c000249c2be15c80000000cfa0c514f827b40000cdcea11864f743a692d20620a253c000004e3cb0501e8d3055acce71778685587892c3330ab81de8a99394065e08e500508c84522ce49b3221927e0000000000000000014be000095e0130000000000000008f438f882d10d000000003e80000670000037f186000006a800025b80000c2cfb94370000520000050fd1e72374000000119d3ad46d2519d4a3230884d3d700004e1961f15600004df012c36f8e5942a8f2b2750b08147caa81b7535927114f32bf89923bfc1324f10e2236d471d000122d425513900000a900000000000000386c00000000000001228028800041a800050f8c20000049a47685824b8c00000e4f3907b4c113d88e020cb92fe00001af071c0d4000025a022525628b07da509cf1a1384f46554c7970000f7e29340000000ce444d0000000000000bc2cb000000000004bf08a82b300000b31844119291459a0000ebc0000000000031057c040a0000000418800056252a2133cece32e8000000000003c4b00007c0000000d553ce80000000c19000000012b110254d916f18a8f8c00011a302d54d600000000000bf511d8a27000147c13c489100000214d8d31917d4ccf27c13063f849f82acc4f70f90e0d4f7c0372718929551037345ec000535c42717100000000b7f36d8b6b000033857e0c27000153f5100b5a488090827682802f6424141651194cbd31b50b8f011b780003af400000006e00000d7643b05070e110df089c277023519100008e84404f5919a899b49ad4fe00008d30000ee02ac93e300001ff0000c1557513802df4c6f0ee05ac12192331935087536486b550502f0ba851e000077d13e55f246690713bbc30a08955df2288000526800000013624298d19000124f5588a9d4fb0f17000000000f4003143501300000000700a6648c4a4200000001f7505744f54e021d12c03bb557a0334eca13504d93e7938c31d52580
  | 38 => 0x39d8000086c00038e000054e41fc00011ea000056e56f800000011752cf80004fbc000298c000000027247d0ff03fa00002df09fe10910cb2f946b757d53fd38e40000000bcc0a84e3d259cd224fc8b5420440005490000000113c32a028a48ed221000057100015340310bc7348c000148800015acfb14eb00002110d2157f40001bdc00000012830f8026f2bd92dd0000dbc33fd3170000000332526e01001461ce860100000000000d7936dccbe1bb0f15183115501f0592000092600000000bacca3000000000000003fdc4ae00000001be800002803ae19dc1b800003fa45f135351940004a208d42d6c3bc408000027ecdd24f1ca381fa8fcc15bca5e1c4511200012a600000d90d3800038940000000ce000013aa0000abb37186bc366ce552ccc7521c0d50d14e929d178d0c4099490229fc41001f4808383d11c00004da387cf8a2b30ae12a6d17a1e1517d00007eb57fd30000000152bd405600000002bdd513395cb6e30a4d5207b882010e87e20eb4f074c39035346d07e20249940368ef1085490b28d87b554600f525c4f2f1dc024d3c3d44150304804d14ffd2b58d0d42f432c112c44632e55bb46bd4ad518cf9b000149e0000f4800003ff0d1432218ec00045c00004660e4f1ee0d51000040f3dac09e0ca158a03bcc371d014a7000068347e13874f304aa39708a0319061d3524c362ad400027740e00e0800010f8cd20000a3f000000043955d60001504195527605bcd960000493391c297000024b0000e8530ad1090c182f70000e060b48d0c027d2d900000001ce11471130c6e559863747501f2247548b4ca0f9a1aac0004dcc10e35b80001f70000480161d1f2c9752a3d414000039501fc0d64e513bd1424a682b4804400008b4028ca1e34091ba13291f329c8de110b8b4922780002630d2d05509b1142c000560c8d50b788841df000000009c944cd0ad000075f579800004147f434780001f3c0002ddc5641bd06e83c10d2c3e203ea029041f542400017446a72cd4a7800007180a7c000566400013f80003d90a7500006b4000000029b0cb44f0c587000000040443f1504800000000003d6cb4500008be1a354bf50ac00005dc000546ca3a425c000175c3c207bd54b2d1c00000000004e7879a017010614c0ed843bc10b00013eb4ee42c12a98c244d7061540401e1053c75039250ab4f149842fd847b496c0000000f4c49fd4db00000d322e14540000bc93d4469054b94bc1ec8d0e00000000000764293053f37d1523291c1350001329254c0260cfd3750ae8000000151f504400000000003480000000147f2f8cd4343c0000000000000014020d59007564c50a00000d52d3112900005aa000018d0a40d1c2e3492b2370a34303055d4ecd5c933c839c2c1d5790000d401538e600000000000098a19a14b526bc
  | 39 => 0xfe458dc7331fd433029bccd402a869200009d525095262bf4714000006314a069150b08bd0118f7a3cb800000e8aeb01746ca057956921447cc00010ac14f40003918000000000039493350a3c788091cdab556932616dc000455910c2a14000496813d02f4edd09a912a24142033e5400817bc743000069d4f4c1ea0001399000000000007d127a40735558000000000043d07aa08fcf6e46f400007d15a90474c840000ac3341131a331c4a400004ec00000004974a8106289242d5800056791f22cdc2e456fc5a93fc400054494001ad935030b0ec8159cf9c46307ec180868c4f90c6152e4161094c00028700db2784cf3172400000015b2463800029800004a351504275602000054f44dcfd8431555c1e009bf00006c1000106331295eb190800027389a12f287ac4ae8cd73d3d1f1229cbda41280003585204026400022fcdd900005a521f0b9041b52b908cd13f00006781c7c0000f0c370000000029d8916000000000012b700000000000df307688d25648746000000000000000000000000151a4c4839800000002c9c1c810241243cec2712368000141034131a0ae358c82db2ff0dc726e084010884bb0d4d3ba22ecb2c17c0f380eac24e3a6112b0001222513d52c1ed82492ba4d4c2ab40001e90bc357f0dd8426547734fc0004860ded2da8b9a3d6153e3eb0d3657d85df00015a52bfd4ac1c790f60f7042c0c3d4f90564f083f455ae4bc400010f03661ae80000000f2d139130545708b22985215474c45800014ce38b52f5106507a4a590fa111cc01000145c3168e7817f893f28545954064ee619bcabd3d1ce7f06ad5b91c0880605f08f10b50e4135a42f13768cf5263891f16fcd4e3ae411141185410f8d5030000699186d0a93a252b83dd4000000023e0000ad400009720000333000017b0b94d942e2c25d000108319d00002f34d8700005fc0000cde000000000011d11e8400049146b518ac8e40000000000009400000000048000420800000000000f28000000000018f0000423c10d2bb4000000000000008850000ee400000000000ac000010e60fcccb60001611433c000471ca10204c67a197000013f44e036e40000c7400043c559d49283bb1c80fbc58d4ef30708e3b3f256264154c5100014812ed883c32b55e509b942023e8000000148e11a000000002883e7400017180001b980000f5800019cc0003e14fa412b4b3a24b800017804630000600507d16805a40004abc8270000d53000075300006750000868405c05b00000000f38d7b125870a344cc9d2edc3520a58000413c00058046460d647c100013ea2b54d454daca6d00007964c949e3000153521b90f520111de18951c91e6c4c3000069e000000040887083228b941484000166c62c09786b9573443500001862688000355cbb300000000a800eb
  | 40 => 0xf19ec00000014914d7c4f638dc33a482d58f12cd16e4f05527227caa139ecd8025988f236cc0002d386e93cd803e3ef8c7924e5354106d0a70aa137d000004f1604000000082500012cb027400000000000d283b75124a1b2a70e8a0000f9711747d40000fd6000000004d08972560df60d3430500002f6222400022d89550000000000000000000001184c1c00012e650f40001a5cf23557ce42000000021754d248c0de018a48460000eda0524d48000001d243c0003a2063135f402a2c340003aa4000085cdac0000eb30000dc9407431b2660fd34a04e8b051d2630000000504000053bc80351e400000002304a000005704d8a12f0c9a116d494245c0ea1594ec0285047d38215e32b90ff846480fb0d2462d0b6418113d53f641dc6b00988c1e41a0c8744f8d9a00005e911442fa3680c5f51a8f81000118f0000e720000000000000052484e914987773d68465488d3402eb80000df07cd558cf8b00013e618913e00f40bb05860216026d5db4e911b748dc70b1cf44723154cc348684001d640003e8829b31346ef0000c983358ca62f99612059d00c03e91cc121409c000136e4e412f73218a12039d42f361009544740000000000000000013fc000000000000014e149080003cf000007cd20248c805839782b70000b430000f710000c0300003160520017000147a10dc0000000a2315253bf3d2c1b3329000056c0000530c0000e6c0ee3100a94312c88a00000000000c8e1ec47600000ced0000000208464c0000da300015ba00006494048ad051acc053e640f6541d1e8023c0001bac3c70724d1538d80000000fae58a0c6c4aa00003eb4001000139d326c3230000f901fbd0b635fc0de13ad5cb1ea0878198d26400000004a5d13a494c09a12a421805584082a300002330a871790000000115107112d70610c4900015712fe496038990140ab4c543d4cf1d21c8eac17b56160b400504bcc6df2e9d0650000f863a7418e1a1941840c098700000000de845a00004cc0cc8bc23e946d60900000449000009e05d6222085a3f78055219400051811433a88ee30000f34543900b2de109b07ec0000e342ec489400053f4dbb46a093a000000005e4b1f50e080101f8000000153c56ad10846c88d756c49bb497958d49c899d0000b6255c808a4c70b2521312ef4000b863bb8b6c3a4d4e31748cf71f14f8f13796342e792d307e4080353c14d46351ae0a5063a4c5424a2510dd03eac95b208848d17a93c916c51bb4e6c7554b38f051cfc3cc0c38acd06f4e8e3fed3033b8524320ac0f72c3c0001e2c9092be43a53f7525c0d84000502d07b0000000044cf2536d0000000075155bd14c4cb89d21fc54c9000042154300bc13d0a0d07c4bd02d040e13498ce50f454a10e7c9eb000016d04b8ac5398d3ee45ac74532cca0b1100cce000
  | 41 => 0xf800046b14c849f456621908c431b47ba09c04110000e530ca4000000022b346153b2d3c000000019d000041e0000fc500000001db839e00003a606b00001674732155d32d4d989de000147d25ed2e9478126c3c44b7e476527b3a7cc4e3ba449514047db00011d70ae538b00014f65890000382c1150000391000093c0d1099f39f00000000c2a2b0896f1820000000044221a400004086122de45d400014fa295c19552e8000000118316c887913380003f414a50000000144885b374540f0dac000000161a0000000129c92312c143b17a0d8f57550d14e089ff09185bc141525100000004d55271000041708ecd7c421092212940004d94000383800008b0b9143a40000000cda00002ee000155955d018330bcafc4bc0428000143721d4000000000027005a4368800047dc000542800019840000000b725614a963cf8b760044000000081a4250952000104200011a20000c954a1c000151c9464da8d9f000107650346e14c8031311d4cdb15f11884070fba42186fb43b82593ae14294a952741058cac017d3e50e9d21d3720b31257c000417d52a35044dc000086f3f2c00000002ca2f780000001178000000050143e70f648e600013ed418080d51bcf804c04000000076a00013de00003362fc40000000140182472f565c3fb082c641456434c12984b2373805449b4eec197c5f60b80a5816e8c5b2ec47274c34d5907a00000000782376c00000000fe0000f280a5496c527c000365c53e105499e53f0f6f108d14e4d2d3270000945000095d073000047191bc13400292d5c00013001fd0000a5b000133d3bf000000000000000b2d09fd43200015ef3340000406c00023189f54bfd3980000d05501d0b73bd11ce0000000000104b00015ec00011fe000141d18c0e914864dae0000ae74ce0285495501516307f0588c000000000004801cd29dd0da2d940004eb8cb700011fc4160be117290923b147350f554982f2c0002c5c00000001ec106800042c80004700000367108800000002928fb01764fe5000000000009e0000038e14a89480000000191c0004ec412d00003542314116100c1cf00000000000c732af80c30bf000047d8309000070e347d57515c000000008e333040000dd043054b426025f46cc4eac0004dc40000000550533c1a32a492c71878000000084b24000003da000022f0ba324cc08312f891300003c546e022f0050b300001050162c81419c827625a954917748eb4f4400014690b000015a833c520827c54ee331800006fc0000840d584ebd55b3a0d5dd3decbdf0000b1c3c700000129304290134e00005b8078c5e22cb8000527020838bc0002c543b646a83720000000063c0003c2d2aa22e4f131d20ce13cb0000076022607f8add068954700014ea00001e51de09f955c028100000002bb80c24e0448
  | 42 => 0xfa2a940001a90000020800000000004fcc7943174bec32f00000000000000000026b852500000002f4c0001e4159a2c28907170400028b40004b280000b4d0b90028861047cd25530060a3558bc4531096138b8e751fdce2a49bc06200003752c652b142c4c703bad05e000000008b4000000084910a51820000000000112247ec000018400016780344a48f5001b11f51cecb502b4cead000076d2a9d33650cc0005370c34294411a4280ce80000d5d4a311c534514472058772439d4ec00012c905700004d5cd9236c92e14f5cefa0000000000000000012ae00006061620a07000026100009ee00001d0048800048e0be405c879e000096511d0000000001846f8000378905c0000000169c3f22a280000000000000000030c0000056907f000137800000000000000006800028cc0004be8a9126d853214d4000076426d001949b3d340471cc45c50ac80b727f00001a2034751444d8000032d1e755e70000c7a000000036412ec000021f00010442654d8821c54612a00b2b000047a43cc000000128f1b3c00000005ae000000020bc506000160f377c0005134b6313140974d09226000000038ac7245639299000000044d40003b40d5f2fe919b28c51ec143c35723255da2a791c3448002432fd1cf2e10d9816c0051479107d00006354ac88c8461112e29e911e1a10df7369920d293c49e14e40004dd934715d0ab60c34c520a68a8e00008383e4530c28243be540465304e934d53dd3f928748a34f1800028ec00033bc0000940000499c07400000003974b710da04391114e670f84000459406d31080ff00007d00000c3a0b7c00042ec2f24f00d7a000000000014a84a600000000e4834248354a791800cac52f3c490160000bc6000101a3110bed11383b53a6c936149d35d00010fc15640003c0c200047146208a020f191400000000003f3ce0936b4f4a0000cf8000000000004cb09a4b0c000102a000008c0f787e40000b6649ccce2451800045cd5a2000000000009032ce04fa3f34aaf5820cd800000003cf4ea815a0a1819f4f6d447d5102d74ac90000e311460b52459cce600000000e6800000008cb52a4eb6127470124547e95178dcd4c58f0217385941e8cef548d8e6d3f68f9444684c953c13fb1c255731ea451d112954e1d1129a0000235036000002eca8d0000aec0b388ac154cbff482498526f110600007bf4e9d38e00005d541acc2144a0c811ebc0000b746bb15d95c32e08a010294b0624dc000492400031c5196015ccc5174c82821dcbd82c8118558b4e203e1038b3f1c84a3d480003160dc3328400040eca4819acbf357308f849954f400012390000aaa0d200c50aed2c42858e4e00000000000be034c8c8c0c0000018a064e1f200000000000386800043008e226dc3df260cf6a3178c06393485400009ac4a
  | 43 => 0xe6a0d5400046c55c8029847c34c54cd56bc000000000010ec1333a40000000106f00ec000000157b00000000000000105000000004ed04ad2e44ad159600000000d2c000000148421980001c100000db8c9210480a74f6c21d173c00000001b205ac000110c8de1eb907038f0000000000000003ac15080000000000000000008d00000000af00c0400000008db000000000008df000068f00000001fe000009f8cea0770000487d3582714000000000000000001c5c0000cf0000000000029cc00000000002e94e2c56540005010107090822e23cc1ad4bed3fa127039700002bc0000f8701acb220000ba814cd60617ec00000005b54ab492845b12f636e94a41af84e74fc1490341c48300000000fac1f029f902300001933a189cf000000000000001eec142000150522d4eb40000000473531d4628000252c365536000048d03030bd013906d914b45d945f3eecc4700007f230240000b8d58c00884133fa4a6a165c000000000000014aa3afc0001420c1f4ff943c2d547d70001314222c9a828695a641a52b300000cb39b80003b3508000000003b9d1f0467c94f585160a10f4edf4cecfe010b4000137c6340000141462caf84ec014c17c87c726c09cd0d080003a78aae1bd4ceb262c326188052d173514022006fc4650e9500007070000f1814dc3125484b85586490d02b48fb000056900000003d84f0a4fd0f10000132440f4f55000006939294664b08c1a0f6c5af00002510000117000000019b0f964eec36f3dd8b7a05541210788a0a395805e57ccd6c1c6d20f28102a23b541ae3b3c4b925e83e622716055580e014aec689315d1b501a8d24385caac3aa8abc51ec70f21fc3401f0d3b746400b41870f8d00000000000c163ca416c06588180e20000493480b1b080ab28dc000152c6f82550000240406e00000000000000000125200012c8000000007e80003440bac1a8c00030ec2af279487623fc000379c42b05e0833295000013f00ac584014a2e6144234e0fe2484d25439309a400000002b7806f51a4320262162f4e149680000a5f43f4000000082c000045522b81532d78e99050c000000124000000004b500003adc00051d058923815cf08910b84bc8e1500016043ddc6aa20f4000000098f37f560052e051000007ee21cc1081e0c0004e94000021493800006e70ff00dd314158033e48934db496326c8173423016a3b4c000219c12955fc00034e84b739f86fd343c0910000eb240e8000416d04030e4acf205c8d10000000000019005d800000001d73d250320001519461ceb00cd431e0ee93d61388a3e0f242e7454c815196537200010d63f6c46c049c4531134b3f0d4557c20ed20e0bd4cee0c1002b40b872a00000864f2800047e45e624b40000000000000125000002750000a2b4bf09ca000000000cca
  | 44 => 0x487000088717fc91b0000d3e22c131e00008290000f355738fb7484483601d51003df0fe6125102d48a4a242e5c8aa0f1142a45c45f940cc7230000f655650c4c0000bb246783504fdc643468415835c94011a0000012312ac43080001c18000072d493000012a40241a857446ea02fc0003be54e839504f0449d622443859f14450e32ac07ad274c0040000000000000038e8000000091c28880004cb000049a000000000000c940000d8c7c63ed468113080003770cbd1c6536c41491950beca9f0dec00000002da000017a3a985f43c98000451000000010e107802b515f8af13fac6d9390d45521f852419b8dff000000000016390000000038d56a00000001cb0000000000011dc5cb00e04324814934000083f44113b237f0000374d4992d08b953874e3000007610000000189d02112a1422128094130b485c0000000000088240614c5000050e00012f427bc7980190390349c40b07e0498000000000006d11e80bbe046ce450c650d5000060b397c1511e483b9539156d490400000000000000ea417e847100013a83d503cb000000000010dd000103406f9157506c57500006033b7147800006763cfc72e08702131cf84643db0b035319246168502b000155d5130f4e17706c536049180ab13c8508cfe31928201127d37943b5452000000000002d83a34000000083e095000000015d3449503153ac8fc16181a44c608ef1e351863911313176c438515d0d83bec6ee1a94aea2ae860d552047009a000029f4c4800010d042b8bcf0000bc54d6cc9346ccd1728f0fbd580cbb4120922e57890c60000c10340ca2f000159829ed11022940000000ab72fb8000358cff354a43aa1e3d2a109708e9000116956f07bc0000ed216106af3b0c00000000ba00007e30000daa3a042cd3cc07223f04b1100010ca0000d700dd884100013a6000000030e000000003d40ad80000001488224062110d800000000003f54a05504d22c1c40fc32e709963bd878a32091b01a1c23122dcd834e54a2131180c61c84a5356d944829e49f712848983050c77562c63d12acdc5356d1a52f883cd218c6b31a84cb83b1044f32c855442907b42430df119983a93294e2731ad3bc0f490282918fb6445800731f47a648fca880bf828400013dd2e807ab2e3c7750000cfc088950f00015a3000000000000005594dc25158a7c0001453532800006707420a384e80e240002b9800000000001838d2e558552f022c0004a1000045e448a4ed05900000800000000000000000b59244000000040fcb213e980000b14c901ac484700006cd176881915fc0000f74b234f85047555000025e000033f494d04d830c43dc2582e5814b00004881af453b4d7922751b4d333598eaf00002c9308d09a21384025388000066800013cc784454813b53446fe4434a0600003960
  | 45 => 0x25d000056b027d0000b892300a5c32b949d4c2c27a101c8f044e15022040bef238410f235888e17841740ba534c0389235084548903951641d0515d2360c624a914281f4cddd00005614b18c251178763410ce68401957617c41b534d00680000a35210cff534690cd13c906e5298d7158c43f015695d736bd05a497d0cc399400000007f9000048b47200004ea491900005f700003782e908700000000000075d00000000000f16340549723b0ef027893d2302065a1f380300000e840000ff9077c7361e947fe000100200b8d6f28a121635180002fa11170ec06da4b44da416e4a4141d00004c8c1dd347400022553f1000000000b052b30887d80000000000000002c054843e00001d24000000108506c40cc02c804236c46bf2f6c0003534fc2000069343c800000006ff0aa8000270800047842ef3e6000002411142e308e700000001554fea000059932ec31c0000d500000009000137e4324000000000029a40004f9ca9a37515ca24bc7d206307c0117d0244c1d2f800000001a393d501992db42e800000004af000036a0000000010c1b7000000000004204184426076c0001fed14a00000ae18f800036180001dd019b000100100014b0000091400015e81b8d1625288f450bb4a82019d04505b8aa33d9ce3434d400036140001ca54162f00b3d000000000000be19440003f481de0000d3b02bcc8811fccb10868000000000047b4000181000049c000019f07c911a9578098d587006c9c7328882e195897f15188c320744d539e954c185cbfd43fcbdc264c9ad03c0ac72e9857a1f804bd422875a3234d08302c7692ebc0d00000000289886d44611541b000590000000250010900012ab0000e0c3b5c3d81b4c00000007de1b2c06513483c01bc869b1660f5657dd48a58ac202000085e2468c8f00006f12160747000079300000ce08645cc51651df00000000c554d333111413af90d2000008450c121b4748a1148a8000164d0fe0000f2a398800030c51e60000d91362c00004286960990acb14f14960000531319543413b812f21489d1430c0001720f091c480520000fc8384c00000000004ce800000009c147b80002d7d1ef429418218b82bd0b88f69510ccfe4664d5a1f5830820c4000389107357490480be50c1054933903240003f110d74b9c5be000140336643b20001383000114f0000b1621b0a4b1db11c22a2d5d0000000000006b2040400058955084e58032195c000448400000011c14bac35f0f19174092157753d461f1fa07562e00b53099d3fc000081c24107302a6127c1990d752afc03c000000027ccdfb035c67e280c04900344b4000054451b8cca1f641f52dcc0ed05d4f37229069c3060000000000016814b427411a03a3c91026e4497000161712654ab0001530071930a37305ee0000b0400005960001
  | 46 => 0xc0000000b9b43a800025880000e9000000009560000ac80000000336469510bc7394788c562bcc75742f103905f824c157cbf84d815161708d5e16d115e4dec00028094f108d94363e0882317cc0190e808b13ea429103e0d44380c3851900031379454d55f87162d9100e2268d8d330154f199cdb83c815c5115c95a589cecb19c413c51145a82c38e2930012dc450946c562159b2494def2bc931118c8479446c40d0958ae82274eab2fdd39356712f90e0c0252d812752eb4c4121214c2000040521640000b1c0004964e0058b82d13bc8a8600000000000b2a3884b6d1be514d13ec0000000000270cc0d5304ee5000110b242929f00000000000ccb45152ee000124700000000000ec654cc6483f3885537a45c00afcce351cc00005800000a6400000009aa23380002cd936f1dbd5903d01506012038011acf434d200001030e803b1c23d4bf4a444a80b5925ac88c201d4752e7432a2dece1944bc0b1047940908851234c4035a1a08fd718505512fd0da951a151e000026c09f000027b14cc1d610904e109df444caa40000a2a4ba9291427000038704b8276c58d0fbcb740a3425f3cc875c3a489a03fb8cb0588038c50b491134a0791000132a119c0000a0800002d884f0d18a6211b8000559d51c13180000e74f704d0400029d00001e70369138c38a2f9c00014d0767064800027593081ffc74f233ca3d4e496152bd071a24ec519000062623352d80d70000301d0af0ac5470243800000012120000000000000000016133790b920758000378c49b588521c39cc9c81bccb28069cfdf29b94b62974ada2e1d27a32804b5263529555904c42dd45d04b1550b4f6435d4258a84081400003281a52d0000019888a13ba86384d4840e19510a8413860539b112c19b4df831ecc80000162a203d34628200204c845fd000143a000061300000000000ea7000000040341ba00009b439840df08195252d2c0f23ab80f9480cad81fccadb4a143391f10a391b5d16a19600e4286561c1b2496d1c4c5001dc4ac10fdce871240c0e1fb46ed48300dc3074d39545cf7d36788320d9d4823d1157d090c00051f81281bc00000000c5c42cd38823b880e1f085630bc09f2162905603480001b6c000000025734483b4345815f555c0001b400000fd40000ebc45c046095c17b0d11000000032bc000000163611242c80a180000000f7f0000fca2ae46e2000000038500002d191ca00001a600000000000000000000000000002ad0093485ca170000d82000000000000000000157000000037a0c85000000035a800000014bb0000000000000000010e8000000000000000bcc92030c832f0c0800007dccdf47948f52098ae245fcaa250283ee1450000000070040a4c134dc141e0000a0f279c2c40000b01000000000005ad37000002b44e281fe9282
  | 47 => 0x133e3d8051713bd23d3dcd63000005d84b540004b6897c032032757a8ac400005eb15f50e23fbc000048c00000013ff145522f2ed52a7299cf83320c0001e8800000015e9000000000004ba2770b3c0a8c324184000000010e4000000038d41b92ef05e52cbc00049a400000000000000c59000000000000001dcd38a4261361000148f329c000008c04130f554235e0000000000000000363ccc00038fd52b0e490370c5c80246700981ec131f34bcdd63ea948549dc0e915ec0003d7c13e0248000000000000003bd00008a9000000032643941e7c1ca0bf483a48503113ae833d552836d1e1c5134af132b508441c09156294f2d0b51e9d543002c1e626f838f06f0b4457c4d6533d8a4e15e497022e95b3150060702a145a4a4d60e537d48d1dd8387000044153b55864ed8c9f2ced06c51c8dd51458a700834a712a551eb300866023f867f2ee4b6f3be01620f212bd23dc6ae31fd40e2c2cc8b3c5155222343e55218bf01e180b900002121d285381b1ce1129495fa120452e42f8cfb318c000000064b47fc33b537507250680003b8869a00010272fc91fa0000a6503d0000000000010a80001f955dc31e1248196c126582477f14714830000e7d1614912409493e44c80000001160039800000000001b212d018680000000fa800008c14150a0e0001278000000010fcc2e40f80001ab000000008f6099908d0000c3550711663e241662e2945000000004278000000000000000000000000074800048f8000000152800000002528393000000000001300000c17000000038c800000012e5350824f00008ed081c00000013da0000000107400000015b52d6000000009ba4da42b037a8efd265d0642e64000399000000000002048e6f0000000313c00000014af3b78dd7012d0892880df54ccc0003624a492fac93508f052c55a09e6001512d4c892061b9541715dcce9280116d39d10de4098000000000000008ea0000fa352cc8243d5c6942c691072e0d4e50f689a536fcec92d3515800000003528168000129c1ca135a0a94ed12c6ce82000000048e82232a4c00032702c30000a590000ae539c119346e400018d8c455098f0c09d0f9f00003812544989369c4890000ea500011e9000144657005030dc518954c878c4cfc19e1558b1847712cc36f40001f842931010c89431d5d952c40021a7c9e434f4f7803449644e44bc157ecffa000040611653cf148c969100507556b49a3581c00042fcfaf51110514a180c02b282ae000000004110a200011cb2cc929b534076b26180001c94fdc215c2f800001712c4c0000c1c000000000001c03f958e15c737f92cf000000000000004174cd50d6113b00000000000000000153100001a9000143500002a64ac000000000001110000000000049e40000000cc23048bd4516c000440
  | 48 => 0x2d1d000007263ffc0003ed0000000000004940001b0d439359c071351c9433c9000030cc1d52ca400038ccbc83f513d435dc89900000005778e041b900002a5c7d5121020c4f34e770000df20df81c1000000000000c70d9000000000000000a6b00005830000000000000000000722aa51d8560400000000000000000075065d41040f3025926a3e9c9fd51609ea059159106840003a300001d3800011400004ef8ec222ac94e3a5d3dc2b380272a805784b595a1194910a1cac59c1c349a7290d5845400b670b5c0000000e231238afb08dcc0f582c3b12250c7c373c8f937b8ed93ec800c061d0c8000058e49893e20000c3f000077e30f842525e54c75488000150c00000011ad00009761e5400002e126156091d64891210310cd6d000028c3c786dc00014bd337141931f8000000000019409f410ccc9e0000e6b0000000314c9e83695201231c1854f0855e0000930074475400a000014080001b1000000000870e18d4b0000ebb46912b50ad0990334d08e00003620000d0033440004e24b4a36c000000007650000000170c9a622a0b9f000124b55b0000434c0000000fed0000000000137f4e8cc912ee800000011dd47541e400006ad302800031d8c67121d1c41da0d6010c4c660000d2b3a700002c24000033c7df36304d634a4adf444417d4c3c8602990c9601e000054510ce0040a1f09ac63f3ff089b00014f24414e1835f940820307be20e43e930f124c1a6003500000001a811970000000136c4ea37054ae1c1427911980000000000000000045c949506ed5ed2d846f6118915b15b54240515334124537a0ff49a957092a316ac5624b78de655b900808803a825642e60cd008e4998f3115706d800015c61a28000000000006010d44130013217cfe7096c000493954d2ff8b120a1c000309800039611a93320c943b6c0762c78dec39e541554440000b314fb000000034280002f5400000000000000efe40e15b7000004d42055aa00000003a580002730deb21583ec131c93100013a150944604b34bab000000004c400058b0077179d23c16d84dd05108ca00000002670d2a15801e900000004e6960d171d30200002523dc80000000f1939002a40d80b10000000050180000000f6336a02dc000047339453ce41f14a04b88000372800000008532604aab0a0cbb84a24a0c38152572540fb30138d624aa49fa37e55200f3cecc000028922bd54507141e700013b8220c0002b7087a000010c28c8000000063354dcba91ded5582c9106757d160c414c24434f00003de500f066073711a4000143000000011a738784e64ba0f8e00000000e8c20a35501c3301000006c15c40ae14e7040cda14c24e710000552000000000004484a28a5058cc15b512853600000884afc000000000000003f800000000000000000000042d000
  | 49 => 0x2fa42c60bfc35b401128b0b0813f2a240000f883bf43ac4d11a9819f4b0c616135c9ab05387ca00011491b1834f45dd3560a6138d0c6841800011a649800001528f0e0000000325d1e30000a563fc89bd00004b600000000000000512c6d4199534a3f015a02ac41141ef49f619101b40a9c63944d916126690492f749d9424c17f3d083d31ee4137183d34353fc72d3c8488f1304f5d56e0ffe0cc42cf058d207255c27b073953a207c7660001555193c8ad00015e137e8f0d3e4c8961d6c000392c9323c9c1d327
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc6f71588500407bccce2b10a0080f71b5c5621401000732b8ac4280203ec6e705885004001cd4e0b10a0080f79a84162140101ef34882c4280203d977865c450040238ef0cb88a0080f71dd9171140101ee9b322e22802000c75645c4500407ba6ac8b88a0080030d59171140101ee3bb1ae2280203dd56635c450040018eac6b88a0080f75558d71140100062ab1ae2280203dc77625c4500407baccc4b88a0080031d58971140101eeb2b12e22802000c65625c45004001a6e84b88a0080034d5097114010006b9402e2280203dd71805c4500401d8ecc0b88a0080f75c981711401001c3f42aed980201d87f865d7300400187cc8bae60080271798d75cc01000637312eb980200787f8759730040010fb0eb2e60080030f9d564cc0100061ebaac99802000c5e7558f30040018baeab1e60080031b9d562cc01000636baac59802000a79861433004001cb2c628660080039a58850cc010005b8c08a198020048df8758e30040019aac6b8c600800e1f217764c0100145e426ec98020048dc83dd930040310fb0dbaa60080030f993754c0102262f31eea9802000c6e62dd530040010fd0eb2a600801e1f21d654c0100061e3a2ca98020178bd86dd1300400187ccbba260080030f597744c0104264f31ee89802000cae62dd1300400117d0eb22600801a2f21d644c0100061fbaac89802000c3c7559130040018beeab1a6008003171d5634c0100064fba2c69802000c9c7458d30040018deeab1260080031b1d5624c01000657ba2c49802000cac7458930040091bb06bb060080131d9c5650c0100265b38ac81802004ce67158830040018eacab8860080032d591710c01004e6b31ae21802000ce5625c430040014f30c28060080031e5d8500c01000734b10a01802000b71811403004001ae2e22806008003365d9300c0100074cb22601802000ec9624c03004001ba2e298060080032d1d3764401000672396ec8802000c7785dd910040018e90bbb220080032de1376440100065a426ec8802000cd783dd910040019a907bb2200800339e0b764401000672416ec8802000cb742dd9100400196a85bb220080031dddb75440100063bbb0ea8802000cb776dd110040019aeedb9a200800335dd87344010006e2390e68802000ce776dc9100407b2ed0f28220080031ddda50440101edb943ca08802000d7287941100407d6e70d28220080fadc61a50440101f6b9bb4a08802000e73769411004001e66e9282200836fcc1d250440101f799324a0880203ef31649411004001ea6e72822008003d41ce50440101f7a931ca0880203ef51639411004001ec6e5282200836bd81ca50440101f7b1314a0880203ef616294110041b5e6685282200836bcc50a50440101f4bb438a08802000c7776141100407d6e5002822008002dce153044010
  | 1 => 0xd0eb22a6080022f21d6454c100246e43ac6a982000c9f7458d5304001938e8b1aa6080031e5977054c100066cb1ee0a9820008f9861c153040013e302382a608002aba13755881000556c26eab102000aae841d5620400155b083aac408002b3a0c755881000566c18eab1020dfaad879d162041bdc5ea33a2c40837b8b54674588106f755084e8b1020deea9109d162041c15cf02ba2c408012b9205745881000657c3ae8b102000ea7815d162041bfd4902ba2c40837f2b9c574588106fe5638ae8b1020dfe2f515d162041bfc5aa2ba2c4080032bdc1745881000656b82e8b1020dfeaa105d162041bfd5220ba2c40837aaba10745881000717aa4a8b102000aae84dcd620400155b09b9ac4080032b5d3735881000656ba2e6b1020ddae7815cd62040095c902b9ac4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac40800393d4e535881000557c22a6b102000aac8454d62040015d700a9ac408002ba20153588100047743886b1020008ed8710d62040014dd0a21ac4080029b61443588106e572c0ce0b102004ae68114162040015cb02282c4080029ba17405881000536c2e80b102000a6f8550162040014d90aa02c408002b3e0d40588100056641a80b1020008ee8710162040011db0e202c4080031d595719401003d3d406ed2802000c3f42dda500400187a85bb4a0080fa1f60776940101ec3f406ed2802000a3f82592500400147b04b24a0080fb0fdc564940101f61eb8ac9280203dc3e705925004001c3e8531ca0080038750a63940101f62fb8cc7280203ec5d7198e500407b8bce131ca00800387d0963940100070ea12c7280203ec5f7158e500407d8bae2b1ca0080f7179c1639401000717422c52802000e2d8458a500407d8dee2b14a0080fb1b5c562940101ee37382c5280203ee6a1058a500407dcd220b14a0080031ddd971940101f4bbc32e32802000c77865c6500407da6cc8b8ca0080fb4d59171940101f6ab31ae3280203ed55635c6500407daccc4b8ca0080fb5958971940100069ba12e32802000d35425c650040018ecc0b8ca0080fb5c98171940100061fa12ec2802000c3d425d850040070ff02bb0a00800e1f60576140101f43f402ec2802000c7a805d8500407b8f420bb0a0080f71e44176140100051fc12c82802000a3d82590500407b87ee2b20a0080f78d9c564140101ee1eb8ac82802000e3571590500407d87ce0b20a0080038e9c164140100070fa14c62802000e1d4298c500407b8bee3318a0080f7175c663140101f62f384c62802000e5a7098c5004001c3e84b18a0080038750963140101ee2fb8ac6280203de567158c500407b8bae2b18a008003955c563140100072c402c6280203ec5e7058c5004001cb4e0b18a0080038ba11621401000716c22c4280203d
  | 2 => 0x520590100051e42a40b2020008be87081640400117b0e102c80800387d525498c100054f424a53182000a9d8494a63040131bd0e294c6080023761c5298c100054f420a53182000a9d8414a63041bdc3ea3a14c60837b875474298c106fd4ec24853182000e8f8250a63041c3d1ce4a14c608387a35c94298c106ff0fa8a8531820dfe1d5150a63041bfd1c42a14c60837fa30854298c106f54f420853182000a5e85d0263040014bb0ba04c60800237e1d4098c1004c6e43a813182000a5f8550263040014b90aa04c608002b3a084098c1000566c108131820098de87c8263040011bb0f904c60800297a172098c100052ec2e413182000a9e84c82630400153b09904c608003a350b2098c100052fc2a413182000a5c854826304001d1a84904c608002a7a102098c100054ec204131820048de87d4d63040018beeba9ac60801237a1f4358c100246e43a86b182000a5e8510d63040014bb0a21ac608002b3a084358c1000566c1086b1820048f4815c9630400395ce4a12c6080032b5c94258c100246f43c64b182000a9e848c9630400153b09192c608003a350a3258c100246e43a64b182000e8d424c963040014bd0a192c608002976143258c100054f42064b182000a9d840c963040018beeb3aac608002a7e117558c100054e422eab182000ad8805d563040014bd0a3a2c608002976147458c1000567410e8b182000acd821d16304001c3ea92a2c608002a7a127258c100054ec24e4b182000ad7815c963040095a902b92c60800297a147258c100052ec28e4b182000a9e841c9630400153b08392c608002a7a125258c100054ec24a4b1820008de8714963040011bb0e292c608002a7a105258c100054ec20a4b1820dee1f51d0963041bdc3aa3a12c60837ea76124258c1000747c1284b182000e8e725096304001d1ae4a12c60837f87d454258c106ff0ea8a84b1820dfe8e2150963041bfd1842a12c60837aa7a104258c100256b408a0b182000ad58114163040014bd0ba02c608002976174058c100046fc3a80b1820008dc8750163040014bf0aa02c608002972154058c100056741080b182000acd8210163040095ad02202c608002b56044058c100046f43e40b1820008dd87c8163040014bd0b902c608002976172058c100054f42640b182000a9d84c816304001d1a85902c60800297e152058c100052e42a40b182000e8d42481630400153d08102c608002a76102058c100256b40840b182000ad58108163040018bea6bb4a6080121fe1d6594c100052fc1acb2982000e1f5359253040074bd0ab1ca6080121f2177654c100145e426eca9820008bf845d9530400517908bb2a6080121f21d6554c100061e3a2caa9820008bd86dd153041b387ccbba2a6080030f5977454c106c64f31ee8a982000cae62dd1530400117
  | 3 => 0x69822000c9f74d8d3044001938e9b1a6088157351c7634c11000637baec49822000c6c75d89304400195ee9b1260880032b1d3624c11000672316e29822000c3c64dd610440018d8c5bac20880030fdd764841100061e3aec90822000c5f75d8e10440018b8ebb1c208800317dd463841100062e3a8c70822000c6f75d8a10440018d8ebb1420880131d9db51841100263b3b2a30822004d727054610440016e501bac2088002dca0075841101f63b3b6cb0822003c767619610440ad96cedb242088157359db638411004e6b3b0c70822000ec46218e10440a79ccedb1420880029da1a508411001e3b3b4a10822000a768614210440078ecec28420880121fa1e54594100061fba4a8b28200487c8755165040090fd0f292ca080028fa1252594100051ec24a4b28200487c87549650400187ee93a2ca0800317dce73594100051fc22e6b282000a3c845cd65040014f100b9aca080021fa1c43594100043ec3886b282000a6e8210d65040014db0421aca080028fa1272594100051ec24e4b282000a3e841c9650400147b08392ca0800297a0c72594100052ec18e4b2820dec3f71d0965041bd87ae3a12ca0837e8f612425941000717c1284b2820dfc3f7150965041bf87ae2a12ca0837f8b88542594106ff1610a84b2820dea3e84109650400147d09192ca080028f612325941000716a1464b282000e2d424c965040010fd0e192ca080021f61c32594100051f42064b282000a3d840c9650400f0fd0fa02ca080021f61f40594100043fc3a80b28200787c8750165040014bf06a02ca080029720d40594100053741080b282000a6d8210165040094ed02202ca080029d604405941003c3f43e40b28200087d87c81650400147d09902ca080028f61320594100052f41e40b282000a5d83c816504001c5a85902ca080021fe1d205941003c3e43a40b282000e2d42481650400147d08102ca080028f61020594100253b40840b282000a7581081650400187eeb3aac8080028fa1473590100051ec28e6b202000aae821cd640400155b0439ac80837b0fd4772590106f61ea8ee4b2020df8bd879c964041c756f02b92c808012ad205725901000657c12e4b202000cb7815c964041bf96902b92c80837f0fd4572590106fe1ea8ae4b2020dfcae215c964041bf95842b92c80837a2fa1c72590100045f43ca4b2020008bd87949640400117d0e292c8080022f61c52590100054f418a4b202000a9d83149640400117d0f192c8080022f61e325901000656b9464b202000cad724c9640400117d0e192c8080022f61c32590100051f42864b202000a3d850c964041c556b03382c808012ada0450590100055ac08a0b2020068be87c81640400117b0f902c8080028fa1720590100051ec2e40b202000a9e83c81640400153b07902c8080028fe1
  | 4 => 0x440014df04b2ca0880829b20965941100061e324ed2822000c6c629da50440074f1013b4a0880030fd0a76941100061ea14ed2822023a3e86d92504400187cedb24a0880038b18b64941100051fc16c92822000a3d82d9250441d387ce1b24a088003179db63941100070fb26c72822000e1c64d8e5044001c98c5b1ca08800387d0b63941100070ea16c7282200087f8758e504400147f08b1ca08808e8f211639411000537c12c72822020a6c8258e50440018bcec31ca08800387d9063941100070e320c72822000e4c6218e5044001c3e8431ca08800387508639411010537436c52822000c6e76d8a5044001c5ec9b14a0880038b193629411000727b1ec52822000e4c63d8a5044001c5f09b14a0880038b213629411074637386c52822000c3f645c65044001878c8b8ca08800317d8d71941100062e31ae32822000c6f625c650440018d8c4b8ca0880fa5e20171941101f63a38ecaa822000c7765dc55044001878c93b0a0880031b18a76141100061fa14ec2822000c3d429d8504403f47d0db20a0880030f9db641411000716316c82822000a3f82d90504400147b05b20a08839f0f9c364141100071d386c82822040a5e86d8c50440018bcedb18a08800387d9363141100070e326c62822000e4c62d8c5044001c3e85b18a0880038750b63141100062f386c62822000e5a70d8c50440010ff0eb18a0880028fe1163141100fd1e422c62822000a6f8258c504403d4d904b18a0880029ee0163141100052f430c62822000c5e7618c5044001c3ec8318a08800387190631411000726310c62822000e1f4218c5044001c3a84318a088113179c063141100072d380c62822000e5a2018c5044001cb240318a08839b96c4063141107372c080c6282201ea6e86d8850440018dcedb10a0880038bd93621411000716326c42822000e4f63d885044001c98c7b10a0880038be13621411000716426c42822049c6e70d885044001cd4e1b10a0880030fd9171141100061e322e22822000c5f635c450440018b8c6b88a0880031bd89711411000636312e2282203d87c865d73044001878c8bae60880271718d75cc11000636312eb982203e87f87d9730440010fb0fb2e60880030f9d764cc1100061ebaec99822000c5e75d8f30440018baebb1e60880031b9d762cc11000636baec5982200087f855d930440070f90abb260880022fe11764c1100145e422ec98220008ef825d930440031d904bb260880f61fa1b754c1100061e326ea9822044c5c63dd530440018d8c5baa60881021fa1f654c1101f43e43eca9822000c3c74d9530441cb17d0dba260880030fd97744c1100061e32ee89822084c9c63dd13044001958c5ba260883922fa1f644c1102b45e43ec89822000c3f75d913044001878ebb22608800317dd7634c1100062e3aec
  | 5 => 0x80038b18b64d45100051fc16c9a8a2000a3d82d9351440ad87ae3b26a28800387d9363d45100070e326c7a8a2000e4c62d8f5144001c3e85b1ea2880038750b63d45100043fc3ac7a8a200387c8758f514400147f08b1ea2880d68f21163d451000537c12c7a8a2034a6c8258f5144001c3ec831ea2880038719063d451000726310c7a8a2000e1f4218f5144001c3a8431ea2883aa9ba1b62d451000717b26c5a8a2000e2c64d8b5144001c9ec7b16a2880039318f62d451000717c26c5a8a2000e2c84d8b51440a78dae3b16a2880f61fa1a70d45100061fb24e1a8a2000c3c649c351440018bec7386a2880031718e70d451000637b14e1a8a2000c6c629c3514407b2f50d386a2880471ea1a70d45100069db24e1a8a2000d38649c35144001ab6c7386a2880035618e70d4510006b5b14e1a8a2000d68629c35144001a7685386a2880034e50a70d4510006b9c0ce1a8a203ec7b619c351440019b0c7b82a2880031ed9470545100066c318e0a8a200ca75819d9514400147f08bb2a2880c68f21176545100052fc1aeca8a204fa5c835d951440014df04bb2a2880c29b20976545100753bc0aeca8a20e5a3e86d915144001c58c5b22a28815bcc04364545100051fc16c8a8a2000a3d82d9151440ad87ee3b22a2880038ddc764545102a52f436c6a8a2000e1f64d8d5144001c38c9b1aa2880039318b63545102afa8086c6a8a2000e1f42d8d5144001c3a85b1aa28815717dc763545100072bb8ec6a8a200087f8758d51440070f90eb1aa2880028fe11635451018d1e422c6a8a2000a6f8258d51440614d904b1aa28815697a1863545100070fb20c6a8a2000e1c6418d5144001c98c431aa288153d404063545100070fa10c6a8a2000e1d4218d51440a9cad0231aa28813f9560463545102a62fb88c6a8a2000e577118d51441d54dd0db12a2880038bd93625451000716326c4a8a2000e4f63d895144001c98c7b12a28814fd8043625451000717c26c4a8a2000e2c84d8951440a78dee3b12a28800399dc762545100072c31ee0a8a203e87e861c1514400187ec8382a2880030f19070545100062fb18e0a8a2000c5c631c151440018dec4382a2880031b18870545100072c318e0a8a203e97a861c151440018f50c382a2880034ed9070545100069c320e0a8a2000d5b631c151440018f4c6382a2880031e18c7054510006ac318e0a8a2000c58631c15144001ad6c4382a2880035a18870545100069da10e0a8a2000d39421c1514407bae462382a2880273618e70cc51004e6c31ae198a2029a7486545314409f8e8eca8a628813f9518d514c510005b8402a298a2000c7865dc131440018f0ca382628800336d8c704c510006b8a88e098a200487f87596504400147f08b2ca08808e8f21165941100052fc1acb2822044a5c835965
  | 6 => 0x70fa9ec929a2003a5c85d8e534400517d09bb2a6880022f6137654d1000c77416eca9a20008ed82dd9534400517d093b2a6880022f6127654d100045fc22eca9a20028bc845d953440011bf06bb2a6880023be097654d1000c76412eca9a20008fb805d95344005179083b2a6880261fa1f6554d100061e3a6caa9a20008be86dd1534400187ecbba2a6883670f1977454d106c64e31ee8a9a2000cac62dd1534400117d0fb22a6880022f21f6454d1001c6f43ec6a9a2000c9f74d8d5344001938e9b1aa6880031b9db65d891000476c3ccbb122000a6e85997624400155d0932ec488002ab61265d89100056741ccbb122000acd8399762440011df0eb2ec488002abe1165d891000556422cbb122000acf83597624400159906b2ec4880029ba1865d8910006373b0cbb122000aae86dd3624400195cedba6c4880038bd9774d89100071632ee9b122000dab70dd3624400155d0c3a6c4880032b9d874d891000717b28e9b122000e2c651d3624400195cedb26c4880038bd9764d89100071632ec9b1220008ed8799362440014dd0b326c4880029b61664d891000557424c9b122000ace83993624400159b07326c4880023be1d64d891000537c2ac9b122000a6c85593624400159f06b26c488002b320d64d891000557430c9b122000cae761936244001c5eca326c4880038b19464d8910006673b6c7b122000e4f65d8f6244001c98cbb1ec488003a3d9363d891000746326c7b122000e8f74d8f6244001d18e9b1ec4880023b61e63d89100053742cc7b122000a6d8598f624400155d0931ec488002ab61263d89100056741cc7b1220008ef8758f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f624400159d0c31ec488003339d863d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d891000747ba0c7b122000e8c7418f624400155d093aec488002ab61275d89100056741cebb122000acd839d7624400155f08baec488002ab21175d89100065738ee9b122000cac71dd3624400195ee1ba6c4880032b5c374d891000557424e9b122000aae871d3624400195d0e3a6c4880038bd5254d891000657ba6e7b122000a6e859cf62440014db0b39ec488002aba1273d891000556c24e7b122000aaf845cf624400155908b9ec4880032bdd173d891000727a9ca7b122000aaf8454f624400155908a9ec4880023ba1c43d891000476c3887b122000a6e8510f62440014db0a21ec4880eabaa0371d89100047743e83b1220008ed87d0762440014dd0ba06c4880029b61740d891000537c2a81b122000a6c85503624400159f06a06c488002b320d40d89100047743881b12200a8ed87103624400187e853b6a2880030f50a76d451001c3e404eda8a203ec74109db51441cb47d0db26a28
  | 7 => 0xaf725096344003958e4a12c688003391cb7158d1001c3f42ee0b1a200087d85dc163440018f0ebb82c68800237e1d6318d100052fc2ac631a2000a5c8558c634400153f08b18c688002a72116318d1000567c12c631a2000acc8258c63440018bcedb28c6880023761e6518d100054f424ca31a2000a9d84994634400159d05328c688002b360a6518d100046fc3aca31a2000a9f84594634400153908b28c688002b3e096518d1000566412ca31a2000c5e7619463441dbcb620328c6883b7960406518d100064f3b6c831a2000e1f65d906344001c38cbb20c688002a760b6418d100046ec3cc831a2000a5e8599063440014bb0b320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc82590634400193cec320c68800387d946418d100070e328c831a2000a9d8219063440011bb0f310c68800297a166218d100052ec2cc431a2000a9e84988634400153b09310c68800237e1d6218d100052fc2ac431a2000a5c85588634400153f08b10c688002a72116218d100054f420c431a2000a9d841886344001c9eca310c688003931946218d1000747b20c431a2000e8c641886344001d1d08310c688003a36106218d1000764c00c431a2000a9e86d0863440015390da10c688003279db4218d100070fb2e8431a2000e1c65d086344001d1ec5a10c688003a318b4218d100054f4328431a2000a9c86508634400193ceca10c68800387d954218d100070e32a8431a2000e8f625086344001d18c4a10c688003961962018d10007643144031a2054ad8864806344001cb0ca900c688003b21892018d10007c4a124031a2054bd0814806344001c3ea92a0c688002a7a125218d100054ec24a431a2000ada8094863440015b301290c68802637a1c5218d100046ec38a431a2000a9e84148634400153b08290c688386a76124218d1000747c128431a20e1e8e7250863441c3d1ae4a10c6883b3a38854218d107674610a8431a20eba9e84108634400159d05a08c688002b360b4118d100054f4264231a2000a9d84c8463440014bd0ba00c688002976174018d100cc6fc3a8031a20098dc8750063440014bf0aa00c688002972154018d10005674108031a2000acd8210063440131bd0f900c6880023761f2018d100052f42e4031a2000a5d85c80634400153d09900c688002a76132018d1000746a164031a2000a5f8548063440014b90a900c688003a35092018d100056bc0a4031a2054ad481480634400153d08100c688002a76102018d10007649004031a2000a5f8544063440014b90a880c688002a7e111018d100054e4222031a2000c5f539da534400117f08bb4a68800a2f2117694d1004c6e41aed29a20008ef825da53440031d904bb4a6880029760f6594d100
  | 8 => 0x9396c688002a7a1072d8d100054ec20e5b1a2000ada801cb63440ab5b300396c688002a7a1252d8d100054ec24a5b1a20008de8714b63440011bb0e296c688002a7a1052d8d100054ec20a5b1a2000e8f8250b6344001d1ee4a16c688003a31c942d8d107874710a85b1a20f0e8c2150b634400159d05a0ec688002b360b41d8d100054f42643b1a2000a9d84c8763440014bf0ab86c6880029721570d8d100052f42e81b1a2000a5d85d0363440271bf0ea06c6881563721d40d8d100052fc2a81b1a2000a5c85503634400159d04206c688002b360840d8d102ac6f43e41b1a20008dd87c8363440014bd0b906c6880029761720d8d100054f42641b1a2000a9d84c836344001d1a85906c68800297e1520d8d100052e42a41b1a2000e8d42483634400153d08106c688002a761020d8d1004e2e31aeb31a2000c3e74d9663440018dce5b2cc6880030f9d06598d1000637390cb31a2000c3f655d26344001878caba4c6880272718d7498d100061f3aec931a2000c3d75d92634400195ce5b24c6880030f9d46498d100061eba8c931a2000cae7219263440018bcebb1cc688003175d76398d100064f3a6c731a2000c9d74d8e634400199ce5b1cc6880031bd957298d100063632ae531a2000caf645ca6344001958c8b94c68800333d8d7298d1004e6631ae531a2000c6e7518a63440018daea314c6880032b9d06298d1000656ba0c531a200087e87d956344001878e9b2ac6880031b1cb6558d100043f438cab1a2000c3c7419563440018d8e432ac68800a2fa1b7458d100061fb2ee8b1a2000c3c65dd1634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac7219163440031dd0db92c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880031bdd46258d10006363a8c4b1a2000caf741896344001958e8312c6880030fdd77458d100061e3aee8b1a20008bd82dd163440010ff0aba2c68800e1f2157458d100046fc1ae8b1a20008ef825d163440031d904ba2c6880030fdd47458d100061e3a8e8b1a2000c5f75dcd63440018b8ebb9ac68800327dd37358d100064e3a6e6b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc9634400195f09b92c6880032b2137258d100043fc2ae4b1a200387c855c9634400117f08b92c68800a2f2117258d100046fc1ae4b1a20008f7815c963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880022fa1f4258d100145e43e84b1a2000c3f75d0963441df878eba12c6880032bdcb4258d1000e5639684b1a20008be8750963440011790ea12c6880030fdd54258d107761e3aa84b1a2000c
  | 9 => 0x62d91100054ec1cc5b2220008bf8758b644400147f0ab16c8880028f21562d91100054fc1ac5b222000a9c8358b644401717b0e316c8880032b5c862d911000717b28c5b222000e2c6518b644400195b0e316c888003aa60062d91100075431441b222056ab8864836444001b56e4906c88815aec20520d91100061eba8ebb222000a3e859cf644400147b0b39ec888002aba0a73d911000556c14e7b2220008bd879cb644400195f04b96c8880022fa1c72d911078d5d400e5b222056ab9801cb644400117d0f296c8880022f61e52d91100045f438a5b2220008bd8714b644400153d06296c888002a760c52d91100045f43c65b2220008bd878cb644400195ee5196c8880032bdc932d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91101e55d406e3b2220008be87c87644400117b0f90ec88815a2fa1f20d91100045ec3e41b222000a3e85c83644400147b0b906c888002a7a0f20d91100054ec1e41b222000caf72c83644400147f0a906c8880028f21520d911000657b9241b2220008be87083644401717b0e106c888003175d753d8d100146fc3a87b1a2000a5e8510f63440014bb0a21ec688002b3a0843d8d1000566c1087b1a2000caf7250b6344003958e4a16c688002a7a1232d8d100054ec2465b1a2000e8d428cb63440031bf0e996c688003a350932d8d100052f42865b1a2000a5d850cb634400153d08196c688002a761032d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100070fb2ec9b1a2000e1c65d93634400153b05b26c68800297a1664d8d100052ec2cc9b1a2000ace82993634400159b05326c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c68800387d9464d8d100070e328c9b1a2000a9d8219363440014bd0b316c6880029761662d8d100054f424c5b1a2000a9d8498b63440014bf0ab16c6880029721562d8d100054fc22c5b1a2000a9c8458b634400153d08316c688002a761062d8d1000727b28c5b1a2000e4c6518b6344001d1ec8316c688003a319062d8d1000747420c5b1a2000e8d8418b6344001d9300316c688002a7a1b42d8d100054e43685b1a2000e1f65d0b6344001c38cba16c688003a3d8b42d8d100074631685b1a2000a9e8650b63440015390ca16c68800387d9542d8d100070e32a85b1a2000e8f6250b6344001d18c4a16c688003b218a20d8d102ad6c43241b1a2000f894248363440ab7a102906c688002a7a1375d8d100054ec26ebb1a2000c5d751d763440014bd0b3a6c6880029761674d8d1000567414e9b1a2000acd829d36344001c3ea92a6c68800297a1672d8d100052ec2ce5b1a2000a9e849cb634400153b
  | 10 => 0xb2a203e87c874836544001c5a84906ca880028fa1020d95100051ec2041b2a2000e69200836544001878cbba2ca880032b1c864595100062e32ee6b2a2000c9c64dcd65440018b8ca39aca880032719073595100063632ee4b2a2000cac64dc9654400195ee8312ca880032b1d0625951000667b98c4b2a2000ccc73189654400517d0fba2ca880030fdd774595100045ec16e8b2a2000c3f51dd16544001878a1ba2ca880021fe1574595100046fc1ae8b2a20098dc835d165440011df04ba2ca880063b20974595100045f438e8b2a2000c3f751d165440131bd0fb9aca8800317dd773595100064fba6e6b2a2000c9c74dcd65440018bea3b9aca880031714373595100062fba8e6b2a2000c9f741cd6544001938e839aca880063ba1f725951000637baee4b2a2000caf74dc96544001958e9b92ca8800333dcf72595100066639ee4b2a2000caf84dc9654400195909b92ca880031bd47725951000636286e4b2a200087f855c9654400117f08b92ca8800a2f21172595100046fc1ae4b2a20098dc835c965440011dd0e392ca880031bdd4725951000657ba0e4b2a2000cac741c9654400199ee6392ca88003331cc72595100045f43e84b2a20028bc87d09654400193ee7a12ca883af271cf425951000657b9684b2a2001cac72d09654400117d0ea12ca880022f21d42595100064fb9a84b2a20e1c9c73509654400195ee4a12ca880072b1c942595100066c39ee0b2a200087d8799065440014bd07320ca880029760e641951000537414c832a2000a6d8299065440010ff0eb20ca8800297e0d64195100052e41ac832a2000a6f8259065440014d904b20ca880028f60864195100061fb88c832a200087d87988654400147d09310ca880028f61262195100052f41cc432a2000a5d8398865440010ff0eb10ca880028fe1162195100051e422c432a2000a5f8358865440014b906b10ca880028fa1062195100051ec20c432a2000e2c641886544001c5d08310ca880038b610621951000637b88c432a2000e6980188654400147d0da10ca880028f21b42195100061f3b68432a2000e2f62d086544001c58c5a10ca880028f21942195100061f3b28432a2000e2f625086544001c58c4a10ca880039a18a20195101ed3c4324032a2000f2942480654407b6e102900ca880030f9db65d91100045ec3ccbb222000a3e85997644400153d0732ec888002a760e65d911000557414cbb222000aad82997644400117f0eb2ec888002a7e0d65d91100054e41acbb222000aaf82597644400155904b2ec8880028fa1865d91100061f3b0cbb2220008be86dcb644400187ecbb96c8880030f19772d91100061fb2ae5b222000c3c655cb644400517f0fb16c8880032b5cb62d91100045ec3cc5b222000a3e8598b644400147b0b316c888002a7a0e
  | 11 => 0x8403b0ff0eb1ca1080fa1f21d63942100051fc22c72842023a3c8458e5084001a6e84b8ca1080034d50971942101f6b9c02e32842000d70805c65084001ae440b8ca1080035c48171942100243f43ecaa84200087f8758c50840070f90eb18a1080028fe1163142100fd1e422c62842003c74865c450840018eec8b88a1080031d59171142100063bb1ae22842000c75635c450840018eec4b88a1080031d58971142100069ba12e22842000d35425c4508407bae700b88a1080035c20171142101ee3b302e22842000d72205c45084001ae240b88a1080021f61f65cc2100cd4e422c7184200087e87d953084001878e9b2a61080030fd97744c2100061e32ee89842000c9c74d8d308407d8ece3b28610800237e1d630c21009d4e422c61842000c77655c430840012eb0fb2e21080031d5db65c42101edb9406cb88420009758719710840018eaec32e21080fadca0065c42100061eba4a9b2a200287f87553654400147d09296ca880028f61252d951000c3fc3aa5b2a2000a5e8399365440014bb07326ca880029ba0a64d951000536c14c9b2a2000a5f8359365440014b906b26ca880029be0964d951000536412c9b2a2000a3d82193654400147d09316ca880028f61262d95100052f41cc5b2a2000a5d8398b654400147f08b16ca880028f21162d95100052fc1ac5b2a2000a5c8358b654400147d08316ca880028f61062d951000716320c5b2a2000e2e8418b6544001c5b08316ca880039a60062d95100051f43685b2a2000a3c86d0b65441df87ceda16ca880038bd8b42d95100071631685b2a2000a3c8650b65441dd87ceca16ca880038bd8942d95100071631285b2a2000e6862883654407d4f10c906ca880039a18920d951000794a1241b2a203eb7081483654400187ae83a6ca880028fa1373d95100051ec26e7b2a2000c5d731cf65440010fd0e21eca880021f61c43d95100053741087b2a2000a6d8210f654400147d09396ca880028f61272d95100052f41ce5b2a2000a5d839cb654400147d08396ca880028f61072d95100053d400e5b2a203ea79801cb654403d87ce1a16ca880830f1c342d951000717c1285b2a20f2e2e2150b65441e5c5842a16ca8807b0f9c142d95101061e38285b2a2000a3e848cb654400147b09196ca880038b50a32d951000716a1265b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2000a6e82d0765440014db05a0eca880028fa1321d95100051ec2643b2a203e87e87d0365440010fb0fa06ca8807e1fe1d40d95101f43e43a81b2a2000a5f8350365440014b906a06ca880029ba0840d951000536c1081b2a203e87e87c8365440010fb0f906ca880028fa1320d95100051ec2641b2a2000a5e83c8365440014bb07906ca880038b50b20d95100f43fc3a41
  | 12 => 0x28fa1232d96100051ec2465b2c2000e2d428cb6584001c5a84996cb080021fa1c32d96100043ec3865b2c2000a3e840cb658400147b08196cb080038dd0971d96100071aa12e3b2c2000a6e82d0765840014db05a0ecb080028fa1321d96100051ec2643b2c2000c75719c365840018f4e7386cb080031e1ce70d96100071da14e1b2c2000e39429c365840018f2e3386cb080039c5c670d96100043ec3e81b2c200087f8750365840014bf06a06cb080029720d40d96100053741081b2c2000a6d82103658407d4ed02206cb080029d60440d96100043ec3e41b2c2000a3e84c83658400147b09906cb0800297a0f20d96100052ec1e41b2c2000e2d42c8365840010ff0e906cb080038b50920d96100051f42041b2c2000a3d84083658407d4ed02106cb080029d60420d96100073490041b2c200087f855d165840011bf06ba2cb080263720d74596100043fc2ae4b2c200087d8799065840010ff0eb20cb0800297e0d64196100052e41ac832c2000a6e8219065840014db04320cb080021f61e62196100051f424c432c2000a3d8498865840014bd07310cb080029760e62196100043fc3ac432c2000a3e84188658400147b08310cb080038b989421961000716b128432c203da798688065840012f70e900cb08003ca509201961000566c1087b1c2001cae7250b638400195ae4a16c70800637e1d32d8e1000746a1265b1c200087e87d956384001878e9b2ac7080021fa1c6558e100061e3a0cab1c2000c3f65dd16384001878cbba2c70800e1fa1f7558e101ec3f406eab1c20028be87dd1638400187eebba2c7080030f1d77458e100045ec16e8b1c200087f855d163840070f90aba2c70800237e0d7458e100045f438e8b1c2000c3f751d16384001878ea3a2c708002ab6087458e100064e3a6e6b1c200087f855c963840070f90ab92c7080022fe117258e100145e422e4b1c20008be87d0963840051790fa12c7080030fdd74258e1077e1e3ae84b1c20008be8750963840011790ea12c7080030fdd54258e107761e3aa84b1c2001cae72509638400195ae4a12c70800237e1d6318e100054e422c631c2000a5d83d96538400517d093b2a7080022f6127654e1000c77414eca9c20008ed829d953840010ff0abb2a7080022fe117654e100145e422eca9c200987e87d955384001878e9b2aa70802697a0f6554e100061fb2ee8a9c20d9c3c65dd153840010ff0eb1ea3080028fe1163d46101ad1e422c7a8c2003c7a869c35184001a7685386a3080034e50a70d46101343e43ac6a8c2000a3f8458d518406347908b1aa3080031e98c70546100063c318e0a8c2000d3b421c15184001a7284382a30815637e1d63cc6101754e422c798c2028a9c8458d31840018f0cbb8263080031e194704c6100066cb18e098c203ea788059650
  | 13 => 0x52f418e4b2e2000a5d831c965c40018dae4392cb8837e8f612425971000717c1284b2e2000e2f7250965c4001c58e4a12cb8837f8b88542597106ff1610a84b2e20dea3e8410965c400147d09192cb880028f612325971000716a1464b2e2000e2d424c965c40010fd0e192cb880021f61c32597100051f42064b2e2000a3d840c965c400147f08b82cb880028f21170597100052fc1ae0b2e2000a5c835c165c40014df04b82cb880029b20970597100043f43e80b2e200087d87d0165c40470ff0ea02cb8807e1f21d40597100052fc1a80b2e2000a5c8350165c40014dd04202cb880029b60840597100043f43e40b2e200087d87c8165c400147d09902cb880028f61320597100052f41e40b2e2000a5d83c8165c4001c5a85902cb880821fe1d20597100f43e43a40b2e2000e2d4248165c400147d08102cb880028f61020597100246f43e86b1e2000acd8210d63c400195ee4a12c7880072b1c94258f100246e43a64b1e2000e8d424c963c40090ff0eb2ca78800297e0d6594f100243e42eeca9e20008bf845d953c400517908bb2a7880023be097654f1000c76412eca9e200487c8759553c4001878e8b2aa7880269720d6554f106ce1f32ee8a9e2000c3d65dd153c40018f2ca382a7880031d59771543100043fc32eb986200087f8759730c40a91bf0eb1e61880021f61b754c3102243f43aca986204087c8759530c4001878e8b2a61880030f997744c3100061eb2ee89862000c9c7458d30c400187ae92a6cb0800a1fe1d54d96100051f424a5b2c2000a3d8494b65840014f501296cb080061fe1d52d961000e37392a5b2c2001cae7250b658400195ae4a16cb0800297e0d64d96100052e41ac9b2c2000a6e8219365840014db04326cb080028fa1262d96100051ec24c5b2c2000a5e8398b65840014bb07316cb080028fa1062d96100051ec20c5b2c20efc3e76d0b65841dd87ceca16cb080038b98942d961000716b1285b2c2000d71719c3658407d4f30d106cb080025ee1d20d96100073431241b2c2000f294248365840014eb03ba6cb080029ea0374d96100061eba0e9b2c2000a6e821d365840014db043a6cb080029d60474d96100053d400e9b2c2000a3e84dcf658400147b09b9ecb080029ba0b73d961000536c16e7b2c2000a7581dcf65840014f501b9ecb0800317dce73d96100062eb98e7b2c2000a75811cf65840014f50039ecb080021fa1c43d96100043ec3887b2c2000a6e8210f65840014db0421ecb080029d60772d96100053d406e5b2c2000a3e849cb658400147b09396cb0800297a0e72d96100052ec1ce5b2c2000c6f729cb658400147d08396cb080028f61072d96100053ac08e5b2c2000a7a801cb6584001c5f04a16cb080038b9c942d961000716b9285b2c20f2e2e2150b65841e5c5842a16cb08
  | 14 => 0xc874c9610c001d1a84992c2180029d616415843004d6b41c82b0860098f487505610c199d2886a0ac2180029d616215843000752a1442b0860018f487485610c0090fb0bbb2a2180022fe1176544300145e422eca8860008ef825d9510c0031d904bb2a218027171cd655443027e2fb2ee6a8860098f487585510c0018f6ca382a2180033c58470544300253a40eeca886000a3f845d9510c06347908bb2a21813f171cd765443000537c12eca886030a6c825d9510c0014ef02bb2a21813f179db73544302a72a18ac2a886003a7687585510c0074e90eb0aa21815395e0d61544300072bb9ac2a88604fe5473585510c001cae86b0aa21813f9510d61544300071ba12c2a886000e3542585510c09fcae64b0aa218003954c9615443027f2b982c2a886000e7161dc1510c07b8ecc2382a2180031d58470544300053cc30e0a886000d5b731c1510c001ab0e6382a2180039c58470544300063cc30e0a886000d5a831c1510c001ab306382a2180035698c7054430006ada18e0a886000d58431c1510c001a7684382a2180034e5087054430006ad990e0a886000d59321c1510c001ae4c2382a2180031e5847054430006b8b08e0a886000c71611c1510c1dbab462382a2183b7560c470544300064fa12ed1886000c9d425da310c0a98bea2bb4621815317545768c43004e2f39acb2806023a3e84dda500c00147b09bb4a018113179cf769403010537416ed2806000a6d82dda500c0294f501bb4a018113171d97394030004aec3c632806000a5d868c6500c0d763d0918ca0180f71d98571140300063ab8ac2280600095d878c4500c0014bb0d188a0181a2c7a123114030006aab8c622806000c9c74dd9300c00193e85bb260180032750b764c0300062fbb6ea9806000d1c74dd5300c0018beec3aa6018003471d0754c030724cf43ee89806000c9f76dd1300c0a91b90eb0a6018003271d1614c0302a66a38ac2980600095e87d45300c0018beeda8a60181cb471d3514c030005ad406a2980600095c87545300c0018beeca8a60181c3471d1514c0300072ab0aa29806000b5880545300c0812bd0f282601800317dda504c03035e8e3a4a0980604495e87141300c0018beec28260181a3471d0504c0300243f43ca8b2e2000c3f7495165c40090f90eaa2cb880121fa1e52597100051f424a4b2e2000a3d8494965c40090f90ea92cb880071b1c9525971000657b9284b2e2001cac7250965c400187ee93a2cb880029ba0a745971000536c14e8b2e2000c5f739cd65c400147f08b9acb880028f211735971000537c12e6b2e2000a6c825cd65c40014f700b9acb88003175cc73597100043f43886b2e200087d8710d65c40014dd0421acb880029b60843597100051f424e4b2e2000a3d849c965c400147d08392cb880028f610725971000
  | 15 => 0x3b22a2980038ddc764545300061fb20e0a8a6000c3c641c1514c001938c93b6629800327d0a76cc5300064ea14ed98a6000c5e76d97314c001c38c9b2e6298003179d865cc5300070e320cb98a60e4a9e86d93314c00193cedb26629800297a1b51cc5302ae2f3b6a398a60d0e1c64d47314c0014b90ca8e6298157179d951cc5306770e322a398a6000c9c649c3314c0010f90cbac62980030f191758c5300043ec3ecb18a6000c3e74d96314c0011790cba462980030fd95748c5300061e32ae918a60ccd98305d2314c00117b0fb2462980030f9d7648c5300061ebaec918a6000c7865dc1314c0018f0ca382629800387193654c5300070e320ca98a6028a9e86d91314c001d28c9b0a629800395d94614c5300052f436a298a6004c5c76d45314c197c38c9a8a629800297219514c5300262e3b2a298a60c9e1c64545314c009ca8c2a8a629800327190704c530004ed430e098a6000cda861c1314c001ab6ca382629800356194704c530006cdb20e098a6000d98641c1314c001b3684382629800366508704c530006ada88e098a6000d59511c1314c0894f301b2ca0980261fe1d65941300051fc22cb2826023a3c84596504c001c76a1b24a0980030f19276941300061fa14ed2826000c3d429da504c0010fb033b4a09808e8fa1b64941300061f3b6c92826000a3f82d92504c00147b05b24a0983d30f9c364941301f43e432e32826000c3f645c6504c001878c8b8ca0980fb1d18571941300043fc3ec32826000c7571d86504c0014bd0d98ca098103179db31941305c70e326632826000c5e764c6504c163c38c898ca098002d620131941302262e39ecaa826000c5f65dcd504c001938c9b9aa0980030f19276141300061fa14ec2826000c3d429d8504c0010fb033b0a09807e8fa1b64141300061f3b6c82826000a3f82d90504c00147b05b20a0983cf0f9c364141300071d386c8282603d87c865c4504c00187ec8b88a0980030f19171141301ee3a30ae2282600087f87d84504c0018eae3b08a09800297a1b31141302262f3b66228260a7e1c64cc4504c0018bcec988a098283871913114130006aab8a622826000b58804c4504c0898bcedb2c609800387193658c1302272db06cb1826003c5e76196304c001c38c832c6098066a7a1b648c1304264f3b6c918260098dc865c6304c001938c8b8c609815735185718c1300052f436a31826090e1c64d46304c0014b90ca8c609823b87191518c1300052f434a11826089e1c64942304c089cb6c1284609800297a18508c1304470e320a118260098dc835d1650c0130f90eaa2ca180269720d545943000c3e43aa4b286000e8d424c9650c0091bb07ba2c2180263720d74584302a46f43e86b086054ad681d0d610c0131b906b92c2180032bdc9425843000e5639284b0860548d
  | 16 => 0x1d91304254f418e3b226000a9d831c7644c00117d0f90ec8980022f61f21d91300051f42c43b226000a3d85887644c00195ee510ec8980022fa1c21d91300045ec3843b226000a3e85087644c00147b0a10ec898212a7a0c21d91300054ec1843b226000caf72087644c0015750010ec898002ae60021d91304245f43e41b2260008bd87c83644c00147d0b906c8980028f61720d91304254f41e41b226000a9d83c83644c00195ee5906c8980028fe1520d91300051e42a41b226000caf72483644c00117d0e106c89805e2f61c20d91300061e3a6caa9a60008be86dd1534c00187ecbba2a6983670f1977454d307bc5f43ec8a9a60d98bc87d91534c0018f6ca382a6980030f1d464d853000556c10c9b0a6000a7581dd7614c0014eb023aec2980021fe1574d853001c3e42ae9b0a60048dc835d3614c0010ff0ab96c29800e1f21572d853077e1e3ae85b0a60eec3c7550b614c00395ce4a16c2980032b5c942d85300056ac1843b0a6000ea542087614c0015e30010ec2980030f9d365985300061f3a0cb30a6000c3f655d2614c001878caba4c2980030f9d764985300061ebaec930a6000c3e75192614c00187aea324c298002ab60864985300043f43ecab0a6000c3c74d95614c0018d8e5b2ac2980021fa1c65585300061e3a0cab0a6000c6c72195614c00517d0dba2c2980030fd9774585300061e32ee8b0a60008be87d91614c00187eebb22c2980030f1d7645853000656396c8b0a60008be87191614c00187eea322c2980030f1d4645853000556c10c8b0a6000cac72191614c0018decbb92c2980031b197725853000657b26e4b0a6000cac64dc9614c0310fb0fb28c2980029d60765185300053ac08ca30a6000c3e75d90614c00187aebb20c2980030f9d464185300061eba8c830a6000aad82190614c0011ef0eb08c298002b920961185300061e324eda8a6000c3f429db514c00187a853b6a2980d68fa1b64d45300061f3b6c9a8a6000c3c76d93514c00147f05b26a2980028f60b64d45300ec3f434e1a8a6000c3f649c3514c001878c9386a2980022fe1176945300145e422ed28a6044c5e73d96514c1ed87aebb24a29800317d9573945300064e322e728a60028be84dd9514c00117b09bb2a2980121f21d65545300051fc22caa8a6031a3c84595514c06347d09bb2a2980028f61376545300043f434eca8a6000c3c649d9514c0014eb033b2a2980030fd0a76545300061ea14eca8a6000c75819d9514c00147f08bb2a2980c68f211765453000537c12eca8a6030a6c825d9514c0014ef02bb2a2980029ee0176545300061e320eca8a6000c3f421d9514c00187a843b2a2980031ecc076545300063c180eca8a6031a3e86d91514c00187cedb22a2980030f1db64545300051fc16c8a8a6000a3d82d91514c1eb87ee
  | 17 => 0x2a6044a5e83907654c0014bb0720eca980021fa1c41d95300043ec3883b2a6000a3e84c87654c00147b0990eca980021fa1e21d95300043ec3c43b2a6000e2d42887654c0010fd0e10eca980021f61c21d95300051f42043b2a6000a3d84087654c0894bd0610eca980029760c21d953000716a1043b2a6000a7a80087654c0014f30010eca981121fa1f40d95300043ec3e81b2a601f87f87503654c0890f90ea06ca9800297e0d40d95302252e41a81b2a6000a6e82103654c0014db04206ca981121fa1f20d95300043ec3e41b2a6000a3e84c83654c00147b09906ca9811297a0f20d95300052ec1e41b2a6000e2d42c83654c03d0ff0e906ca980821f21d20d953000716a1241b2a6000a3e84083654c00147b08106ca980030f197745953000556c10c8b2a60028be87dd1654c00187eebba2ca980022f60b74595300061fa8ee8b2a6000c3c50dd1654c0010ff0aba2ca9800237e0d74595300045f438e8b2a6000c3f751d1654c001938e9b9aca980021fe1572595300045fc22e4b2a60028bc845c9654c0011ef02b92ca980123d20572595300045f43e84b2a60028bc87d09654c00117d0ea12ca980022f21d42595300043ec3cc832a600087f87590654c0014bf06b20ca980029ba08641953000536c10c832a6000b2d82190654c001c5d04320ca980028f608641953000716c10c832a6000a2d82190654c0010fb0f310ca980028fa1262195300051ec24c432a6000a5d83988654c0014f301310ca980021fe1d62195300051fc22c432a6000a3c84588654c0014ef02b10ca980029d20562195300051f420c432a6000a3d84188654c00147d0da10ca980028f21b42195300061f3b68432a6000a3c86508654c00187ceca10ca980038b989421953000716b128432a6000c3c645c4654c00187cedb2ec8980028f60765d91300045ec3ccbb226000a3e85997644c00117f0eb2ec8980028fa1865d91300061f3b0cbb226000a3d81197644c00117d0db96c8980030fd9772d91300061e32ee5b226000c3f655cb644c001878cab96c89800a2fe1f62d913000656b96c5b2260008bd8798b644c00147d0b316c8980028f61662d913000657b94c5b2260008bf8758b644c00147f0ab16c8980028f21562d913000657b92c5b226000ab78158b644c00156902b16c89805e2f61c62d913000656b90c5b226000c3d751d7644c0c957501b9ec8982138794f53d91300045ec3ce5b226000caf729cb644c00195f04b96c8980022fa1c72d91300045f43ca5b2260008bd8794b644c00117d0e296c8980022f61c52d91304254f418a5b226000a9d8314b644c00117d0f196c8980022f61e32d913000657b9465b226000caf724cb644c00147d0b38ec8980028f61671d913000557c12e3b226000aac825c7644c00147d0a38ec8980028f6147
  | 18 => 0xc0011db05ba6cb180022f61e74d96300145fc3ae9b2c60008bf825d3658c00187ea2ba6cb180030f14174d96300143fc3aa9b2c6044a5c83553658c00517d09b96cb180022f61372d963000476c3ce5b2c6000cae749cb658c00195ae9396cb180063be1d72d9630006573a2e5b2c6000cad745cb658c00195d08b96cb180032b61172d963000637a8ae5b2c6000c6c505cb658c0030ff0ea96cb180071b9c952d96300145fc3e85b2c60008bd87d0b658c00395ce5a16cb180032b5cb42d96300045fc3a85b2c60008bd8750b658c00395ce4a16cb180032b5c942d963000e6739665b2c60018df874cb658c001d1a84996cb180033a5ca70d963000746a1264b2c60558de8710d618c00159b0421ac3180032bdc9425863000e5639284b0c60558de87cc9618c001d1a84992c3180023de1d61186300243f43ecaa8c6031a3e84d95518c00147b09b2aa318113171cf655463018537416caa8c6000a6d82d95518c0018bacbb9aa3180c68fa1276546300051ec24eca8c6030a6e829d9518c0014db053b2a3180029d60676546300053bc0aeca8c6000c5d76dcd518c0018bcec39aa318157958c561546300ccce422e018c6044a7880596508c0018bacab9ca1180025761e319423044d8f424632846000b59808c6508c0012bb0e18ca1180025761e31142304458f424622846000d55718c4508c0012bb0e188a11815637e1d61cc2302ae6b38ac3984600095d87d47308c0016b501a8e611800257e1d51cc230225acc3ca19846000d5987943308c001ab2ed2866118113965da50cc2307c78da14a198460f8f1942943308c00155b04326ca980030f5d254d95300143fc3aa9b2a6000a3e8494b654c00147b09296ca980061fe1d52d953000e5739285b2a6000cad7250b654c0014dd04326ca980029b60864d953000596c10c9b2a6000e2e82193654c00147b04326ca980038b60864d953000516c10c9b2a6000a3e8498b654c00147b09316ca980028fe1162d95300051e422c5b2a6000a778158b654c0014e902b16ca980028fa1062d95300051ec20c5b2a6000a3e86d0b654c0014790da16ca983bf0f9db42d95300051e43285b2a60eec3e7650b654c001c5cc4a16ca980038b58942d95300061e322e3b2a6000c3d741d3654c0014dd043a6ca980029b60874d95300051f426e7b2a6000a3d84dcf654c0014dd05b9eca980029b60b73d95302262e39ae7b2a6000a3e849cb654c00147b09396ca9811297a0e72d95300052ec1ce5b2a6000a3e841cb654c00147b08396ca980038be0942d95300071739285b2a6000e2d7250b654c00147d09196ca980028f61232d953000716a1465b2a6000e2d424cb654c00187e84b8eca980030f50971d95300052ec18e3b2a6000a6e82d07654c0014db05a0eca980021fa1e41d95300043ec3c83b
  | 19 => 0xf71d8c5760c4501ee2e98aec188a040c75315d8311407b0f900bb06228103170c1760c4501f43fc34e0188a00387c869c0311407d0ff0cb8062280024fe11700c4500fc9e422e0188a00987e8795165cc00187ee92a2cb980261f21d545973004c3f43ca4b2e6000a3e8494965cc00147b09292cb980029e602525973000c3e43aa4b2e6000c3f749d165cc00147d09392cb980028f61272597300053d404e4b2e6000a79809c965cc00147d08392cb980028f610725973004d2f418e4b2e601da5d831c965cc1c347b09212cb980038be09425973070f1719284b2e60e1e2d3250965cc1d747d08212cb980030fd0b71597300061ea16e2b2e6000a3e849c565cc00147b0938acb9802697a0e71597300053dc02e2b2e6000a6e82d0565cc0014db05a0acb980021fa1e41597300043ec3c82b2e6009a5e8390565cc0014bb0720acb980021fa1c41597300043ec3882b2e6000a3e84c8565cc00147b0990acb980021fa1e21597300043ec3c42b2e6000e2d4288565cc0010fd0e10acb980021f61c21597300051f42042b2e6000a3d8408565cc0134bd0610acb980029760c215973000716a1042b2e6000a7a8008565cc0014f30010acb980028fe1170597300051e422e0b2e600087e87d0165cc0010fb0fa02cb9808e1fe1d40597300fc3e43a80b2e6000a5f8350165cc0134b906a02cb980029ba08405973000536c1080b2e600087e87c8165cc0010fb0f902cb980028fa1320597300051ec2640b2e6009a5e83c8165cc0014bb07902cb980038b50b20597301043fc3a40b2e601e87c8748165cc001c5a84902cb980028fa1020597300051ec2040b2e6000e692008165cc09f4eb033aac3981469de05755873001c3f42ee8b0e600087d85dd161cc0131bd07ba2c39800e1fa1772587300043ec2ee4b0e60efc3e75d0961cc1dd87ceaa12c3980032bdc9425873000e5639284b0e6000c3f425db51cc00187a84bb6a39814717cc576d473028e2e182eda8e601887d869c351cc0018bacab9ca3980121f617765473004c3e42eeca8e6000c7965dc151cc0018f2ca382a3980030fd0b76547300061ea16eca8e600387d81dd951cc09f8be63bb2a39813f170c376547300053bc0aeca8e6000c3f425d951cc00187a84bb2a3981461fe0576547300063bc0aeca8e6000c7b805d951cc0070fd0eb0aa39813e1f61d61547300063cbb6e0a8e6000c79761c151cc0012f30c382a3980031e61870547300069da10e0a8e6000d39421c151cc0018f2c2382a39800356cc470547300052ec36a298e6000a5f8654531cc009ca8c2a8a6398002d6201514c7301f43fc32e3286603ec76615c650cc0018eae2b0ca1980031759773543301ec3fc32e2286603dc76615c450cc0018eae2b08a198003555c53114330005ac4026228660018ee82dd3658
  | 20 => 0x1ec2642b08a03de6621c8561141f54ed0f10ac2280f71da1e21584501ed3bc2442b08a000a758488561140014eb0710ac2283e69d60a21584500071ba1442b08a000e66428856114001c6a8510ac2280039950a215845000712a1442b08a000a7680885611407bcc84290ac22800e9da1d215845001d3a43a42b08a000a778448561140014eb0890ac2280029de0d21584501ed3bc1242b08a03de67824856114001ccee490ac228003991c921584500071ba1242b08a000e354248561140014e90090ac2280329d60670584501ec3f43e80b08a00087d87d01611407b4ed03a02c2280029d60740584500071aa0e80b08a000e364190161140010ff0ea02c2280f61f21d40584500052fc1a80b08a000a5c8350161140014ef02a02c2280f69d20540584500071aa0a80b08a000a6e8210161140014db04202c2280f69da0440584500053ac0880b08a000e3641101611407b0fd0f902c2280021f61f20584500051f42640b08a000a3d84c8161140014bd07902c2280029760f205845000716a1640b08a03da7681c8161140014eb03902c2280039948720584500073310c40b08a00087f87481611407b0f90e902c2280038b50920584500053bc0a40b08a03da74814816114001cca42902c2280028fa1020584500051ec2040b08a03da768108161140014eb02102c2280039988420584501ef2b18ac3988a04487f865c3311400187e84bb462280030f509768c4501ee2f98aed188a03dc5d315da311400127f04ba462280024f609748c4501ee1fb0ae9188a03dd36615d2311407b87ac2ba462280034d585748c4501f61f302e9188a000d3a605d2311407b4ef0eb0c622809b1de1d618c4501ee3bba2c3188a03de367458631140018eae8b0c62280f78d5d1618c4500061aba2c3188a03dc777258631140018eae4b0c62280038dd09618c4500071aa12c3188a000c75619c2311407d0ff0cb8462280f7950c5614c45001e3bc3ac2988a003c748758531140018eee8b0a62280031d5d1614c4500072bc1ac2988a000e5483585311407b8eee6b0a62280f795dcd614c4500072ba1ac2988a000e544358531140018eee4b0a62280031d5c9614c4500071ba12c2988a000e35425853114001cae64b0a6228003954c9614c45000738b0ee0988a00097986dc131140018f30db8262280034ed0b704c4500069ca16e0988a000c7961dc131140018eac238262280039c584704c450004bdc30e0988a000979861c13114001ab4c638262280035658c704c450006ada18e0988a000d58431c13114001a768438262280034e508704c450006ad990e0988a000d59321c13114001ae4c238262280031e584704c450006b8b08e0988a000c71611c131141cdab462382622839b560c4704c4500061fa12ec188a000c3d425d8311407b8be62bb062280
  | 21 => 0x425d8319407d8be62bb063280fb174c5760c65001c3e402ec18ca044c5c305d8319407b0ff0cb8063280024fe11700c65011c9e422e018ca000a5d8510f635400159b0421ec6a800637e1d32d8d5000746a1265b1aa0008df8758c635400153908b18c6a80121f21574d85500046fc1ae9b0aa0098dc835d3615400117f08b9ec2a800a2f21173d85500243e42ae5b0aa001cae7250b615400195ae4a16c2a80023de1d61185500253a43ec2a8aa000e3742d855154001c6a85b0aa2a80039cd8770545500743f430e0a8aa000e73611c151540090f90b3b462a813f1718d758c5500062ebaec718aa000c9e74d8e31540090f90b3b062a80022fe11760c5500145e422ec18aa000c5d75d8c31540070f90cb8ca0a80fb1d18571941500063ab8ec3282a000c3f749d161140014dd053a2c2280029b60a74584507dd3ac0ce8b08a0ffa77815d161140018bee739ac2280a69d60673584500051fc22e6b08a000a3c845cd61140014df04b9ac2280029b209735845017d3bc0ae6b08a000a78805cd61140018bae639ac2280f69da0743584500053ac0e86b08a03da768190d61140014eb0321ac2280021fa1c43584500043ec3886b08a000a6e8210d61140014db0421ac2280f69da0443584500053ac0886b08a000a3e849c9611400147b09392c2283e69d60672584507f53bc0ae4b08a000a3e841c9611400147b08392c22800297a0c72584500052ec18e4b08a000c6d721c961140014f500392c2280f69e60072584501ed3b40e84b08a000a7581d096114001c6d03a12c2280038d607425845077f1bb8e84b08a0eea3d84909611407b4ed03212c2280029d606425845000717c1284b08a000e2f725096114001c58e4a12c2280038da0542584500071ac0a84b08a0eee377150961141fbc5c42a12c2283f78b085425845077d1f42084b08a03da768110961140014eb02212c2280f69da0732584500053ac0e64b08a000a3e848c9611400147b09192c2280038b50a32584501ed3b40c64b08a000a75818c961140014f501192c2280029e602325845000716a1264b08a00087e870c961140010fb0e192c2280028fa1032584500051ec2064b08a03da76810c961140014eb02192c2280029ba0b415845000536c1682b08a03de3641d0561141f94ed0f20ac2280f71da1e41584507dd3ac2482b08a03de568390561140014eb0720ac2280f79560e41584500052ac1c82b08a000a75829056114001c6e8520ac2280038d50a41584500053b40482b08a03de344150561140074ed0ea0ac22800e9d21d41584501ed3bc2282b08a03de37845056114001c6ee8a0ac2280038d1d141584500053bc1a82b08a000e36435056114001c6886a0ac2280029de0941584500071ba1282b08a000e354250561140014e900a0ac2280028fa132158450005
  | 22 => 0x21ac3280029d60443586500051f424e4b0ca000a3d849c961940014bd07392c3280029760e725865000637b94e4b0ca000a75819c961940014ef02b92c3280028fa1072586500051ec20e4b0ca000a7a801c9619407d4f300392c3283bf0f1c3425865000717c1284b0ca000e2f725096194001c58e4a12c3283cb8b88542586507971610a84b0ca0eec3c70509619400147d09192c3280028f612325865000716a1464b0ca000e2d424c961940010fd0e192c3280021f61c32586500051f42064b0ca000a3d840c9619407d4ed02192c3280029d60432586500053741682b0ca000a6d82d05619400147d0990ac3280028f61321586501f43f43e80b0ca00087d87d01619407d4ed03a02c3280029d60740586500043fc3a80b0ca03e87c8750161940014bf06a02c3280029720d40586500053bc0a80b0ca03ea748150161940014dd04202c3280029b60840586501f43f43e40b0ca00087d87c81619400147d09902c3280028f61320586500052f41e40b0ca000a5d83c816194001c5a85902c3280fa9da0720586500053ac0e40b0ca00087f87481619407d0f90e902c3280038b50920586500053bc0a40b0ca03ea7481481619400147d08102c3280028f61020586500073490040b0ca00093f825d0619407d87ec2ba0c3280fb0f58574186501ee1f302e830ca000d3a605d0619407d8bec3398c3280fb1758673186501ee2f304e630ca000d5a609cc619407d8bec2b98c3280fb1758573186501ee2f302e630ca000d5a605cc6194001a5d08b90c3280034b61172186501f637b0ae430ca03ec6d615c8619407b8dcc0b90c3280035a981721865011c9fc3e8430ca00093d87d086194001a3ce7a10c328003475cf4218650106973968430ca000d2d72d08619400127f0ea10c3280024f61d42186500068f39a8430ca000d1d735086194041a5ce4a10c3280034b5c94218650004bbc3ac230ca000d3b429c06194001a7285380c3280fb5c9867018650006b8b0ce030ca02393e849db319400127b093b663280fa57a0e76cc6502262f31ced98ca02096e829db31940012db053b663280025ea0276cc6502262e3b2c798ca044d5b309c331940810ff0cb8663280025ea02768c6500061fa14ed18ca000c3d429da31940018f5013b463280030fd09768c6500061ea12ed18ca03ec5f315da319407d8ba62bb4632800e1f201768c6500049fc12e918ca00093d825d2319407d87ec2ba463280fb0f585748c6501ee1f302e918ca03d87f865c231940018f4c1bb2632808e4fa12764c6500049ec24ec98ca02096e829d931940012db053b263280025ea02764c650004bd400ec98ca000c5e7698d319407d2b90eb1a6328003171d9634c650004bd404ec18ca000c3f429d8319400187a853b063280031ea02760c6500061fa12ec18ca000c3d
  | 23 => 0xd8e500069da14e1b1ca000d39429c36394001ab665386c728003564ca70d8e50005ad406c731ca044a5d87d8e63940018bb0fb1cc72800387a136398e500070ec26c731ca000e4e82d8e6394001c9b05b1cc72811317dcb6398e500052ec0ec731ca040a5e80d8e6394001cb501b1cc72800317d8d7298e500070fb1e8531ca000e1f6350a6394041a5ce4a14c7280034b5c94298e502243e43ac8b1ca023c3c7459163940894b906b22c728002d6a036358e501043e43ac4b1ca044a5c835896394041a5ce4a12c7280034b5c94258e5000716b1284b1ca00095f8758c63940894bf0eb18c72800317e1d6318e500042fc3ac631ca044e5a7058c6394001c3ac7a10c7280038758d4218e50106973928431ca000d2d725086394001e1a84990c7280031758d7118e500062eb1ce031ca044d5a639c06394001ab2c7380c7280034ed0a7018e500069ca14e031ca044d5b329c06394001ab265380c7280025ea0374d86501f43ec3ec9b0ca023c3c74593619407d0fb0e326c3280030f5d064d865000537410c9b0ca000a6d82193619407d4ed02326c3280028fa1363d86500051ec26c7b0ca044c5e73d8f61940014dd05b1ec3280029b60b63d86500062eb98c7b0ca03ea768118f61940012f501b96c3280fa1f61f62d865010637396c5b0ca000a3e8498b619400147b09316c32800297a0e62d86500052ec1cc5b0ca000c6f7298b619407d0fb0e316c3280028fa1062d86500051ec20c5b0ca03ea768118b6194041a5ce4a16c3280034b5c942d86500071731285b0ca000e2d6250b61940018f4c7386c3280034ed0a70d86500069ca14e1b0ca0f2d2f7250a6194041a58e4a14c328002dca0361986501f43f43cc8b0ca03ea7681991619407d0f90eb22c32808f0f1d1645865000537410c8b0ca000a6d82191619404727d09b9ac3280024f61373586500051f426c6b0ca000a3d84d8d61940014dd05b1ac3280029b60b63586501f43f43cc6b0ca000c5f7398d619407d4ed0331ac3280fa1f21d63586502262e39ac6b0ca03e87e87989619400147d09312c3280028f61262586500052f41cc4b0ca000a5d8398961940018dee5312c3280fa9da0662586501f43e43ac4b0ca000a3e84189619400147b08312c3280029ea00625865000697b9284b0ca020d2c725096194001c5cc4a12c3280038b5894258650005b9406c2b0ca000a5e839d161940014bb073a2c3280029ba0a745865000536c14e8b0ca000a75819d161940014ef02ba2c3280030f5d074586500051f426e6b0ca000a3d84dcd619400147d0939ac3280028f61273586500062fb9ce6b0ca000a6e829cd61940014db0539ac3280029d60673586500053bc0ae6b0ca000c5d731cd61940010fd0e21ac3280021f61c43586500053741086b0ca000a6d8210d619407d4ed02
  | 24 => 0x6200c3c75dd1600c509938e7ba2c0188022f60b74580312b61fa8ee8b006256c3d51dd1600c4010ff0aba2c01880e1f21574580310cc6fc1ae8b006200c3f751d1600c401878ea3a2c018b93271cc745803100556c10e8b00620087f855c9600c4070f90ab92c0188022fe1172580310145e422e4b0062008be87d09600c4051790fa12c0188030fdd7425803177e1e3ae84b0062008be87509600c4011790ea12c0188030fdd542580317761e3aa84b006201cae72509600c40195ae4a12c01880b2e1d240580310247c43a80b0062048f887481600c401d5284902c018812bc205205803100e5739284b1ca000cad7250963940011bf0eb18c72811297e1d6394e500062fc3ac729ca000e1f4258e5394001c3a84b1ca7280031758d7194e502043fc32e129ca01d97b865c253940818f70cb84a7280034ed097094e500069ca12e129ca02393e87dd153941b187eedba2a7283638798f7454e500049fc16e8a9ca00093d82dd153941b387cc1ba2a7283674e9837454e5004d2fc32c6a9ca051c5e63dc553940310fb0db82a7280034edd37054e500069dba0e0a9ca000d38741c1539400147f08baac3280028f21175586500052fc1aeab0ca000a5c835d561940014df04baac3280029b20975586500043ec3ca8b0ca03587f87551619400517d09b9ac3280022f61373586500062e29ee6b0ca000a3f8454d619400147908a9ac3280031b14b72586500043ec3ca4b0ca000a3e84949619400147b09292c3280d21fe1d525865000657b9284b0ca001cac7250961940011ef0eb08c3280f61fe1970946500071ba12c2a8ca000e354258551940190fb0db82a3280039c587705465000738b08e0a8ca0028be849db319400117b093b6632801237a0e76cc65000c77414ed98ca0008ed829db31940138bcc6bae632811317dd563cc6500049fc22ea98ca02393c845d5319409f8bcc6baa63280025be09754c650104b6412ea98ca000c5f7558d31940412dd05ba6c7280025b60b74d8e50004bd406e9b1ca00093f825d36394001a74c0ba6c7281121f61f64d8e502252f41ec9b1ca023c3e74593639404727d09b96c7280024f61372d8e50004bd406e5b1ca000d2e749cb6394001a5ae9396c7280034b9d172d8e5000696ba2e5b1ca000d2e845cb6394001a5b08b96c7280035a98172d8e501043ec3ec5b1ca044a5e83d8b63940418dce5b16c7280831b9c962d8e5011c9fc3e85b1ca00093d87d0b6394041a5ce5a16c7280034b5cb42d8e500049fc3a85b1ca00093d8750b6394041a5ce4a16c7280034b5c942d8e5000716b1285b1ca020d4e72ccb6394001c9ac5996c72808257e1d32d8e500052fc3265b1ca000f0d424cb6394001a74e9386c7280034e5d270d8e50006b5394e1b1ca000d69729c363940018f6c5386c7280031e58a70
  | 25 => 0x40117d0fa12ca9880a2f21f425953100657b9684b2a6201cac72d09654c40117d0ea12ca988022f21d425953100657b9284b2a6201cac72509654c403998e5992ca988063721d325953100746a1264b2a6200cbb74dc1654c401970e9b82ca988033adcb705953100674396e0b2a6200c7a85dc1654c40197685b82ca988032e50b70595310063da8ee0b2a6200c7b751c1654c401976e8382ca988032e1d070595310066db98e0b2a6200ceb721c1654c4019d0e4382ca988031ee1470595310063daa0e0b2a6200c79541c1654c4018f4a6382ca988031e14c70595310063da90e0b2a6200c79521c1654c40197684382ca988032e50870595310066d990e0b2a6200cd9321c1654c4018f6a2382ca9893e9d60765545310062fb2ee6a8a6200a3f845d9514c46347908bb2a2988029be09765453118536412eca8a622fa77815d9514c49f8bcedb9aa29893f175d87354531025aa408e6a8a6200c7b805d7604c4070fd0bba6c0988021f61774d813101c3f42ee5b02620087d85dcb604c5df87ceba16c0988030f5d742d81317761f3aa85b026200c3d7550b604c40195ee4a16c0988072b1c942d81310043ec3ea3b02620787f87547604c4014f100a8ec0988031e5d450d81310047dc3ac03026200a7885580604c4131b906ba0c098802b360843181310056cc00863026201cae72508604c40195ae4a10c098802b6603321813100746a12643026200a7880544604c4015b306280c098802bc60450181310243f43ca8b286200c3f74951650c4090f90eaa2ca188121fa1e52594310051f424a4b286200a3d84949650c4090f90ea92ca188030fdd274594310051f424e4b286200a3d849c9650c40147d08392ca188028f610725943104d2f418e4b286226a5d831c9650c5bf47b09212ca188038be09425943170f1719284b2862e1e2d32509650c5bfc5c42a12ca18b7f8b08542594316f51f42084b286200a3f845c1650c40147908b82ca188269720d70594310061fa10e0b286200c3d421c1650c4010fd0fa02ca188021f61f40594310043fc3a80b28620087c87501650c4014bf06a02ca188269720d40594310053741080b286200a6d82101650c4010fd0f902ca188021f61f20594310051f42640b286200a3d84c81650c4134bd07902ca188029760f205943100716a1640b28620087f87481650c4010f90e902ca188038b50920594310051f42040b286200a3d84081650c47b4f501bacc0188fa9ea0075980310043fc2ae9300620387c855d2600c4010ff0ab94c01880e1f215729803177e1e3ae8530062eec3c7550a600c40395ce4a14c0188032b5c942980310247cc3c813006209ad883502600c4091f30f104c018803aa509209803101c3f43eeab006244c5c73dd5600c4818b8e63aac01880a2fa1f74580310061fbaee8b0
  | 26 => 0x28f612325963100716a1464b2c6200e2d424c9658c4014bf06b82cb188030fd0870596310061ea10e0b2c6200c7b301c1658c4018f060382cb188021fa1f40596310043ec3e80b2c620087f87501658c4010f90ea02cb1880297e0d405963127d2e41a80b2c6200a6e82101658c4014db04202cb188129da0440596310053ac0880b2c620087e87c81658c4010fb0f902cb188028fa1320596310051ec2640b2c624fa5e83c81658c4014bb07902cb188038b50b20596310043fc3a40b2c620087c87481658c401c5a84902cb188028fa1020596310051ec2040b2c6204a7681081658c4014eb02102cb188030fdd675592318055bc0ae6b2462cce1e53d4d648c5bd87ea3b92c918b7b0f54772592316fc5ec3ce4b246200caf825c9648c5bf87ea2b92c918b7f0f54572592316fe5710ae4b2462dfcac215c9648c5bd17d0e392c9188032b5c872592310045f43ca4b2462008bd87949648c40117d0e292c9188022f61c52592316654f418a4b246200a9d83149648c40117d0f192c9188022f61e325923100656b9464b246200cad724c9648c40147d0bb82c9188028f61770592310051fc2ae0b246200a3c855c1648c40153f06b82c918b32a720d705923100557410e0b246200aad821c1648c40956d02282c918802ad60450592310045f43e40b2462008bd87c81648c40147d0b902c9188028f61720592316654f41e40b246200a9d83c81648c40195ae5902c9188028fe1520592310051e42a40b246200cad72481648c40117d0e102c9188022f61c20592310061e3a2caa9c62008bd86dd1538c5b387ccbba2a7188030f5977454e316cc5f43ac8a9c62f78bc87591538c4018eacbb8aa7188f69ea0375982311f53d400eb304620087f855d2608c4070f90aba4c1188021fe15729823101c3e42ae530462efc3c75d0a608c5dd878eaa14c1188072b9c9429823100656b928530462048f987882608c401d5284904c11880e1fa1f75582310043fc2ae8b04620387c855d1608c4010ff0ab92c11880e1f21572582310061fbae84b0462efc3c75d09608c40187eeaa12c118bbb0f1d5425823100657b9284b046201cac72509608c4091f10e902c118803aa50920582310246ec1ee9b2a6200e8d424cb654c4018f0ca382ca9880a2fa1f74595310045ec16e8b2a6200c3f51dd1654c401878a1ba2ca988023be09745953100c76412e8b2a62008fb805d1654c4011f100ba2ca988022fa1c74595310143e43aa8b2a624fa5c83551654c4031dd0fb92ca988032bdd37259531006563a6e4b2a6200caf84dc9654c40195909b92ca988031bd47725953100636286e4b2a62008bf845c9654c40517908b92ca988023ee0172595310047c402e4b2a62008ee871c9654c40195ee8392ca988032b1d0725953100c3e43aa4b2a6201c6c72549654c
  | 27 => 0xd406e8302a200c3f749d060544014bd063a0c0a88029760c741815100537410e8302a200a6d821d0605440f4eb023a0c0a88029ea0074181510053d406e6302a200c5f739cc605440147f08b98c0a88028f21173181510051f420e6302a200a3d841cc60544018bae6398c0a88029ba08731815100536c10e6302a207a75811cc60544014f500398c0a88029ea0343181510053cc0686302a200a7b8050c60544014f100a18c0a88021fa1c43181510043ec3886302a200a6e8210c60544014db04218c0a88029ea0372181510051f424e4302a200a3d849c8605440147d08390c0a88028f61072181510052f418e4302a200a5d831c860544018dae4390c0a881e9d60472181510053d400e4302a200a7b8050860544014f100a10c0a88038be0942181510071739284302a200e2d7250860545fbc5c42a10c0a8bf78b08542181510071dc0284302a200e3880508605440147d09190c0a88028f612321815100716a1464302a200a7a808c860544014f301190c0a88038b50932181510053dc0264302a200a78804c860544010fd0e190c0a88021f61c32181510051f42064302a200a3d840c860544014dd05a08c0a88029b60b41181510051f42642302a200a3d84c8460544014bf06a00c0a88029720d40181510053741080302a200a6d82100605447b4ed02200c0a88029d60440181510051f42640302a200a3d84c8060544014bd07900c0a88029760f201815100716a1640302a200e2d42480605440147d08100c0a88028f61020181511ed3b40840302a200a758108060544091b906ba2cb988261f21d545973104d2e41aa8b2e620187c8754965cc401d1a84992cb98827171cd6554731025aa40ee6a8e62048de83dd260cc4091bd07b94c1988072b9c9429833100656b92853066200e8d424ca60cc4098bce7a8cc198813179cd519833101c3f43eeab06620087f855d160cc4070f90aba2c1988123720d74583310043fc2ae4b06620387c855c960cc40187eeba12c198bbf0f1d742583310061fbaa84b0662eec3c7550960cc40395ce4a12c1988032b5c942583310043f43ea2b06620787c8754560cc4090fd0f2a2cb188030fdd254596310243e43aa8b2c620487e87949658c40147d09292cb188028f61252596310243e43aa4b2c6200caf72509658c403958e4a12cb188030fdd2745963100537414e8b2c6200a6d829d1658c49f8bce7b9acb188028fe1173596310051e422e6b2c6200a6f825cd658c4014d904b9acb188029ee0173596310053c402e6b2c6200a3e849c9658c40147b09392cb188028fa1072596310051ec20e4b2c624fa5e831c9658c4014bb06392cb18b7e8f612425963100717c1284b2c6200e2f72509658c401c58e4a12cb18b7f8b88542596316ff1610a84b2c62dea3e84109658c40147d09192cb1880
  | 28 => 0x58c63544014b900b18c6a8803962016318d510052c402c631aa200c5d635c86354401c3ac7a10c6a88038758d4218d51186973928431aa200d2d72508635440127f08b80c6a88c64f2117018d5127caf41ee9b02a20095d83dd36054401a5ee4a16c0a88c34b1c942d8151004bac0ee9302a231c3c74d92605440187ae9324c0a88029ba0a649815100536c14c9302a200a798099260544630ff0eb24c0a8803175ce63981510053cc04c7302a200a3f8458e605440147908b1cc0a893f179cd639815100537c12c7302a200a6c8258e60544012eb03b94c0a88028fa1262981510051ec24c5302a23087f8758a60544618dce4b14c0a88029ee0162981510051f420c5302a200a3d8418a60544014bd06314c0a88029760c629815100637b90c5302a230d2e7250a6054401a5ae4a14c0a88038bd8942981510071631285302a20093d82dd16054401a6ec3ba2c0a88021fe197458151004afc1ae8b02a24f95c835d160544012df04ba2c0a88c25b2097458151004bbc0ae8b02a200d1f74dcd6054401a38e9b9ac0a880355d8773581510068fba0e6b02a200d1c741cd60544a38bec239ac0a880355d84735815100697ba6e4b02a200d2c74dc96054401a9ee7b92c0a8803531cf725815100697c26e4b02a200d2c84dc96054401acec3b92c0a88021fe1972581510049fc22e4b02a23193c845c960544012bf06b92c0a893e5720d7258151004bbc0ae4b02a200d2f741c96054401a58e8392c0a880353dcc7258151006a6398e4b02a20093e87d0960544632790fa12c0a880347dcf42581510068e39e84b02a200d2f72d096054461a58e5a12c0a88024fa1d42581510049e43a84b02a200d1f735096054401a38e6a12c0a88034bdc942581511869639284b02a200d3774dc56054401a68e9b8ac0a880355dcf7158151006aa39ee2b02a200d6772dc56054401ac8e5b8ac0a8803561cf60581510061fba4c0b02a200c3c7498160544018bee7302c0a8803171ce605815100637b94c0b02a200c6c7298160544630fb0fb20c0a88c70f9d3641815100537414c8302a200a6d8299060544010fb0e320c0a88024fe11731815118c9e422e6302a24f87d87d8c605449f8bce7b18c0a88029e60363181510051fc22c6302a200a3c8458c60544014df04b18c0a88029b20963181510053dc02c6302a200c5d7318c60544610fb0fb10c0a88028fa1262181510051ec24c4302a20087d87188605440147d08310c0a88028f61062181510052f418c4302a200a5d8318860544018dae4310c0a88c34b9c9421815100696b9284302a200e2f625086054401c58c4a10c0a88021fe1d60181510051fc22c0302a200a3c8458060544014bf06b00c0a88029720d601815100537c12c0302a200a6c8258060544012f70eb00c0a8802d620d60181510053
  | 29 => 0x82a6a89031718c7054d5104c6f41ee9b02a2008dd83dd3605440195ee4a16c0a88072b1c942d81510047dc3ac0302a200ad88358060544070f90aba0c0a88f61fa1e54181511ec3e43aa8302a2008bf845cc605440517908b98c0a88031714d73181510051fc22a6302a200a3c8454c60544014f700a98c0a88029e201531815101c3e42ae4302a200c6c525c8605447b0fd0f290c0a88028fa1252181510051ec24a4302a23d87c87548605440395ce4a10c0a88032b5c9421815127c3ec3ec9b1aa231c3e74d93635449f4bd07b26c6a88c21f61f62d8d5127d2f41ec5b1aa200d2f7250b6354461a58e4a16c6a88038bd8942d8d51064bac0ce1b1aa24fa5d87d8e63544018bb0fb1cc6a893f955c76398d510070fb1e8531aa200e1f6350a6354461a5ce4a14c6a88034b5c94298d5100786a126531aa200c5f635c66354401aaec6b8cc6a893f5518d7198d510069ba12e331aa200d35425c6635449faae64b8cc6a8803554c97198d510062fb1ce131aa20093d82dd16354401a6ec3ba2c6a88025be097458d51184b6412e8b1aa200977815d163544012f700ba2c6a88025e2017458d5118e1e3a6c8b1aa24f87c87591635449f4b906b22c6a88034bdd37258d51006963a6e4b1aa200d2f84dc96354401a5909b92c6a880359d877258d510049fc22e4b1aa23193c845c963544012ef02b92c6a88025ee017258d51004bc402e4b1aa200d2f741c96354401a58e8392c6a88c31b1cb6258d511843e43ac4b1aa24fa5c8358963544618d8e4b12c6a88024fa1f4258d5118c9e43e84b1aa200d2f72d096354461a58e5a12c6a88024fa1d4258d510049e43a84b1aa200d2f725096354461a58e4a12c6a88038bd894258d51186a639664b1aa200e4f62cc963544612b90e992c6a8802972193258d5100786a1264b1aa200d3774dc56354401a68e9b8ac6a880359dcb7158d51006b2396e2b1aa200d5763dc56354401a6e85b8ac6a88034d50b7158d51006ab996e2b1aa200d5532dc56354401a76e9b82c6a88034e1d37058d51006b5b96e0b1aa200d6872dc16354401ae6e3b82c6a88034ed0b7058d510069ca16e0b1aa200d7361dc16354401a76e8382c6a88034e1d07058d51006b5b90e0b1aa200d68721c16354401ae6e2382c6a88031ee187058d510063db20e0b1aa200c79641c16354401ab6c6382c6a88031e98c7058d510063c318e0b1aa200c7b621c163544018f2c4382c6a88034ed087058d510069ca10e0b1aa200d5b321c16354401ab264382c6a88035cd847058d51004afc3ac631aa200b578158c63544016b100b18c6a893e97e1d6318d510062fc3ac631aa20085f8758c6354401c3f08b18c6a8803872116318d5100727c12c631aa200e4c8258c635449f8bee4b18c6a894697e056318d510072bc0ac631aa200e5b8
  | 30 => 0x85530065db20e0b0aa600cb8641c16154c6b87cea320c2a9c2b0f5d464185530047bc3ac230aa70ac3d751936054c071bb07ba6c0a98063ee1d20d815300754a1241b02a600cae72d926054c0195ce4324c0a98032bd91729815300656322e5302a600ce972d826054c0517d0dba2c0a9b622f21b74581530045f43ec8b02a6008be871916054e1393ee6322c0a987f0f1d464181530047dc3ac0302a64087c875506054c814b906aa0c0a987a1f21d521815300e5739284302a600cad725086054c01d1a84990c0a98022fe1171181530145e422e2302a6008ef825c46054c031d904b88c0a98063e61e20181530053dc2a40302a600ea9424806054e114f501ba4c1a88030f5d0749835100537410e9306a200a6d821d260d460f4f5003a4c1a88028fa1373983510051ec26e7306a200a6e82dce60d44014db05b9cc1a88529ea0373983510062fb9ce7306a200c5d731ce60d44354f50039cc1a88021fa1c43983510043ec3887306a200a6e8210e60d44014db0421cc1a8c1a9ea0372983510051f424e5306a200a3d849ca60d44014bd07394c1a88029760e729835100637b94e5306a200a3e841ca60d440147b08394c1a8c169ea00729835177f1d38685306a200e2f8250a60d4401c5ce4a14c1a88038b5c942983517971710a85306a2f2e2c2150a60d45ddc74e0a14c1a88028fa1232983510051ec2465306a200e2d428ca60d4401c5a84994c1a88021fa1c32983510043ec3865306a200a3e840ca60d440147b08194c1a881e9ea0371983510053741683306a200a6d82d0660d440147d0990cc1a88028f61321983518243ec3e81306a200e3b4090260d46070ff0ea04c1a880297e0d40983510052e41a81306a200a6e8210260d44014db04204c1a88038e50040983518143ec3e41306a200a3e84c8260d440147b09904c1a880297a0f20983510052ec1e41306a200e2d42c8260d46030ff0e904c1a88038b50920983510051f42041306a200a3d8408260d4401cd240104c1a8802976144358e5100566c1086b1ca2048dc874c96394401d1a84992c7288031e1407058e511ed3d406eb304a2008df835d260944131b906ba4c1288022fe1173982510145e422e7304a201cae7250a609440195ae4a14c1288123e61e20982510053dc2a41304a200ea94248260944011bf06ba2c1288263720d74582510247c43a40b04a200ea942481609440195ee4a16c6a88072b1c942d8d510046fc3ac631aa200ad88058c635449f4bb0fb1ca6a88031761f6394d510070fa16c729aa200e1d42d8e53544018bec7384a6a88f61f2197094d5118c9f43ee8a9aa2d8c3c76dd153545b1c38c7ba2a6a88024fe0b7454d510049ec16e8a9aa2d9c3f61dd153545b3a6ec3ba2a6a882697a1b6354d510069bba6e2a9aa200d3474dc5535447b0fd0db
  | 31 => 0x1c004012000002c0020090010004012003000806c000000000004400a00400000040060120040070000001000001400200b0000070002000000005800200a001000800000101a803401201802a000000000100280040020090050004008003000000c010003002002001001d0028024018001004000800000700000000040020000000006001000001400203c000000400200000c8000000019000000800a00100a0000034013000802805403f010801801001300080240000030020000002001004800000e014000000000401a000802001a00f000003801402d0000000010004001800801a0260048008038006000003c024000001800400200300400000200080018044000001000801c0060010000008a34ef02baac3298029e201755865300657b9284b0ca601cac725096194c01d1a84992c3298031e14070586532053d406eb304a601cae7250a6094c0195ae4a14c129803a3509329825304c6e41ae8b04a601cae725096094c0195ae4a12c1298022fa1b72d91530145fc3ec5b22a600cad72d8b6454c0117b0f316c8a9802aea0262d91530055cc04c5b22a6008bf8758b6454c6f17b0e316c8a98032b5c862d91536c51e432a5b22a6d9a9c864cb6454c01b1ee4996c8a98030fd4772d91530061e286e5b22a6008bd879cb6454c0195ee5396c8a98032be0972d91530061fa8ae5b22a600c3c505cb6454c0117d0e396c8a9b668fa1472d91536c51ec28e5b22a6d8a9e831cb6454db353b06396c8a9b662fa1e32d91530045ec3c65b22a600caf728cb6454c0195ee4996c8a98de8fa1671d91530051ec2ce3b22a600aaf825c76454c0155904b8ec8a9b668fa1471d91536c51ec28e3b22a6d8a9e831c76454db353b0638ec8a98022fa1f21d91530045ec3e43b22a6d9a3e858876454c0147b0b10ec8a98032bdca21d91530045f43843b22a6008bd870876454db347d0a10ec8a98028f61421d91536c54f41843b22a600a9d830876454c0195ee410ec8a9802aea0021d91530055cc0043b22a6d9a3e85dc36454db147b0bb86c8a9b62a7a0f70d91536cd4ec1ee1b22a600aae829c36454c0155b05386c8a98028fe1570d91531bd1e42ae1b22a6008be87c836454c0117b0f906c8a9b668fa1720d91530051ec2e41b22a6d8a9e83c836454c0153b07906c8a98032bdcb20d91530051fc2a41b22a6d9a3c854836454c0195ee4906c8a98022fa1c20d91530045ec3841b22a65187c875536154ca34b906aa6c2a98d21f21d52d855300e5739285b0aa600cad7250b6154c01d1a84996c2a980a2fa1270d85530045ec24e1b0aa6018ee829c36154c011db05386c2a9c2f275cc64985530045f43ec8b0aa600cac72d916154c0117d0e322c2a98032b1c8645855300657b26e4b0aa600cac64dc96154c01976c9b82c2a98032e193705
  | 32 => 0x100480080000040070000004007000803405200f00a000800000a00080700060000000000002003001803c000000000000800a000001000801c002000800c000003000003400600000800040080010008008000000011000000400b001800c05c003000002800a00b0000000000000000000c01a003001801c00200000380000020010000004020005006001000e002006000c00e0190028004000001000800c006010005000000002c000000400c009004802c002002000000802c003000801c008008001001400200d00100380000030078004008009001002c0000000000018006006000800801e0010028004006001000000800c00600180380020010010004030003000802800200200180040000010000030010000001000000200b001001000601f0098054002002003002c000000002801000400b000800000000a00d0000004003000800000a001001000802c00000f00080000030030088008001000000000e00900301600100000030000004002002800800200100000180000090048050004001008004800000200d80240200000008004022000003800c00a00000c800000400200180300000070040000010000004803000000c0000008004001000800800e000008000800800100000080060140000020020000000008402c00400080d401a004000800002000100f8090000004000002800a0000008008004001001802400801a002800002000200c811c01800a001003400600e0000000002003002001402e01b0020000008000002800000200a001003000000d0038058002000000001000a00500000000020000000000000002000000c000000002001800000c0088004010000002000000a000005801404e000000000801c002001000800c000002800c0060000000008000000026000000000300480000040000010000002004008800000801900580640020050018000002015002000000200c000001400a001001803c03600000080080020050118000002002000000000600d002007c006007003001c00e00200080040080030008004002000013800400600000a0020040000005000000e000000000c00e005000800800001e001805000000100300b00040010000000004006002000800a008001001000000000180200160000000018000006000003c02e0080030014006008002000400a005001800000400000000300600020000000022001001003401c001003005c006001003804400401400100080000000038040004002000000c000002002800000001600000080100160008028000000002003c0000010000054002001000001000000000080f00000020018024012006003000c002006000002c01a0010038018002001000000800c007000802c012005000000c006003001803000e006009801400a00000000
  | 33 => 0x7000000c02200400380140000080168058000012015800c00200200000080020020008018020005000000400400000580040060010018048002001001000000400700000180000040068024000019003000800200500a00000000050000000002000000800c004004000803000602601500000040000010000006008000001c00a004005801c00600e0068008012000001000800c0000000004002019000006003400b00100000220140000028018004001000c000011003000000000e0018050006000002802000c00400080100000000128000006005000000400202400c800000a002000003002e0000000008010002000800400400b000001800401300000040060000098000000002004001000000600300000020060000000014001007801800e000000804c002015000005c008001000000400c0000038010010003005000800600e00100000520000078044008001000801800600b0040008036004002800c00c001004000400600000000000180000070004014009000002c008000000000800a00200500100140070058008012000000001000000100a002400002f0048058000000000000006c00e000802000000000c000c000002000003402c002003803c016001000800001c00e0008024014007004001c01200300180100000040000084002000010811001e0010010004004007001000c00000400100000100040170000002003001802002e00100300200000000000004004003000000c00c00000000080000000098000000009004000800801b000800000800300000000100110008004002001004800800000100f800800e0000000008008012001802801402d0098024004003005000c036007000000400202a007801401801100780100420030018024000021000800803e00200480000060000028000000003002002c00601400180ec000000002800400c0020060030002011001000001200000100040180000000000012003012800c02200600280180040060010048002002000001800400700480000120010008000030000000803000000800000080000020020040000000002000c002000003801c0160040080000000000003003c006005000002800c000004000c00400a009001800200f0010018004002006800c00000100080240080010000008008001005801401a0020028000008003004000c0040000190014002003000000400000a0180004010000004801c010011000006800600400a0000000002000000000000b002004002000100a804c004002003000800600a00000380000030018000012001000001c01c0170000098008002002800400a002003000c008008000801c002001000804000c000000804003a0000008000002014004004000a000000000000000c0018010000002002801c0240
  | 34 => 0xd719987a904ea3f880003f6970e108a1e868a80004a09c7c000068c40d800085b20b610797080ea08b40000000000097e000000000014e641b0000376894c7388370232a0d0189000081c8000000092a0a4002a80e013c27001f033c857a8201b0241b80005fb00e22920ec63b703a02b000006800c9c00004b0773000000004a43b1082e0001ecc18680007b4806601d18240000fd20150b0223491881f79ae86481af000018d40000134313000012e941259200000001bbe000039210d18825ea9f3c70f1f7c46a04ca0e8a042033105843c079800005ba05207321d78dd4387800000007263b0946e00019261ba149e83200c625600001c783be00020be084940005003ee4680d3e18a94f83c2157611d9e6c3b616dc80f00007169fb010c99b45260612398923c09592be27920902ab9ea68041cf277216fe2451132588800000006645c30000000000085f011a4dc9cae26180007b680004b2857c57e000e6ab8520000174072191648122100342219800000000001370000091e0ae0ca62bc89d88740dfc6968a9e7970d1c4519c18502089c78c91961fd87e221f9fca56121ec1640faa4bd0f2c2589c002350a0c00009ac000000000000006c6000000000003150e4e00000000000d807b407ca5c1194e2948e34000111800000007528000000219020a17c200008b855400007f69e3a3fd8ad273a9430459954445b82166b2142216990bc000189066c82b23ef1ee40001ff40d3938e3e9168a21189a600010aa000212212b8e527919b3867821be27583aa723a01a746906401117a009393e244aa11660d0ae058e05fa07ca0b806b8ddc5268bde1b112fc0000686825800276b945601f0a5e76403c40000fa000000000000b1403903b061221740000de000000006d403261450e0a1dd8ade7e1800044f9ff800000000000000000000027b90d256700007aa07f0000188a1298d200591d7638f8d0a84fa062000146a2a697d85aa9b86000220612b1afe87806004061edc5e60f3069799a00b68fd485e806484083505d5908665c204650e80004d900000000000127000000000001730b363be000041780007ac8e7e00000001d1000031a1ad0000000085b9a5625a80103091a6e18f053c7f81aca6f88baa22f0bdc00000006a1829a4d706cc77689cc31a858c0bd16ec29c0f9673d9c02422920c36b1caa1ee9a342841b0c4289c262771f2079100005d31f6404b0a3e7a888120000c8e13d8bf24d389927db06fc81a8dea0ee84c61ca9b9089880002858f1e1b48f782d6051e73491947bb99de3a4000078213760000b680001ec8000000080203de16c837400000000000004000004807c008004004002000000500980000020000020000010007001000800000c00000100140020028014000006000800c00000000400440020000018
  | 35 => 0xc224371f464318180691027408c8000000000000001e41789f3e2db8426000035e466000000014a87d58000000204e7fb80007a0865e0001fbc4c221f81679c4866e21fe6e48ba2394068084103947880b8822c800019508346e3215e4fe0b3c07e0dc80000784665852c210905c630000027c9a0a4210000112951231c01985f5119c00000000000c1000000008071da052480000f3953806b000009219b6740a02200003024b20d9038516ae000176426b88f44a9000028a8a9c76f9c9e45a04b483ea0005af0c0c0001af235617dc50c80004779f984f1000002096404c9814200000004f9873e14707601e81d144d4800012f917e4a3881e21c1adc8619b72000000004815a25d4818c3b9906200018ce22980007748000000143600000000000f6c00000007af85160000000000205c1e1881689607025438a64734167448a8000000000034300007158000585a21c19c8a5a612812e681a2102f2838a85204f8756206442b17b287d9d521320f7600011383a980000001e520001ca21179c067a5800075700001c621b8000000030500c20670bb82a100005ce000087991ae2e700b669a0b8082880002098b526e09c9a4f09d60207221804900000080000497018669e1f8e7d5062e1910000500864e00000000b48000640800000009780000000000000001e80007b59454000204c0c7930e286061625f0adc21414c234e009a6ff894e49592a02570b542f401468592144196878025b846e6f39142062800076c0dba6981b306530558154886c14a1d8e000060e80b000014d04f468b875826a80004968000426800084b81966019fe201818c600012b65fd1fce4e506e2000000079d80001ce80001a386486b99a7462205940d28fba000013a7260fa6000085477d0754377812857a035259c80004c7073481d9bee6f681102c5920820a9c4c40a1aec4db86ea0001484000198c5ab095270100006108000000097a2df0b9202c96fc11615f047486ec894a1b63a1196c00015da4cf0f5a3598f6068c9e2e687827c00000002e50af6711a07812d80000001a500f884fe230857813399a400d00000001320370800000011f43510e5a0000000000000061400005b500000fa000000000007e787dc6e10548000000036d1d0c00008c45240000616800000000000000000000000000011746e200000000e5858c88864fb09680650d7a4961f062fb871a1af81026ff079c317950240793e84ec942039b064c1a80e8e427022845b1bc679e027e5da13c05ba938a4ff0abc7ae8cd6593056006c1ee03e2886e4e117be6961f92034080c592953e5030522835889a7ee000000019f2123800006400000001cba00006f200020d4000020412600000002024000000069da0fc1008c3c16d900a3cb85300001d060001ef85cd1f7a29d00ac0d89d961
  | 36 => 0x8218fd61309a1c374101000011c60000f9262e0d605b1000059f800064a0000000098000005f451300003c8800000000002d795b60000000000075067000000000000000148e36a00000000c7634180005cd932e728063635d0b2801c0c8200007b4000115083d15a600016807f3063037c80006e295b000000000001a420001ca4661972600000000000000467a0c40000ce22a385be54d03985f480007ad0000000000000000002a81a620000dc000021ca00001a600015d80000dcc7d40000000031c0000b72759800001495fa5ca80006c59a903ee0d4c2690536000088c1750ff8397084a6151e567258c1a03e8ae67d882e62ba94e43aa800082f11d68980fa80ae882c5d880001a41e2851814783d384482c0151c2d581a86a79c8037d0184000141e000135656008761c2817000000003c40000667090c0000000000000087888da000000000000004b496e6000089646900004430ace12302f021e0d1e00008c0531162a2898000629800000007b256f19844751d8a049957e48614e0581089871c13f400f17fa6a69fc66eb000082c058000000007f9131668e20f2134003800314186848eae0000c640000000000098e7f41fac359186c00021ce3910cb843b8000000000000000004a711e671600000000eba81b07e06200000505918a70d1a880b014047b398e273316b46148000280a10e0f0a1e46d61c284bb0d3016702dc00000001c19b704111c1e000000019495e66568000000225a59e107c312800046d945a44e9e4a7e12128674153673d0e9a0ab0000439940e87113f272999406b800001b380005f405bc0000c4281f0000000000000007306d9101c0758cd217b0f1a0001aa88440bae32321ac4488e861b980006d686ac4cd1e0276e09c824807aa61e0b040919c1c0dc93a62950c6c24f91f037b089e1a507ec5178d426f09232251000048880a2403158615c08080dfa15a6279bd20ec9dfc3b91dd03620c0875215ba00019d4378a1c00001152000000020f93a252f800059f0000000000000000005f8805c6b91c383ae10982e98182844995478900a855694443e787002e1132c4980db679f80000001da2538800041a01d45209966303968263e1a9c84c03d60d302342e6210c0881daa4fc13e40470fdc0000e1a00000000638500000152264e84400708000000042c58380b873f04d43361d3441484383818ac454014e81c102c21c40f9467a060249e1b00679083864c124c568160a49007a60de9354006840410f86423ab1d68173915c5f80f46316813221882b04e79be820c90b824995ee0e211a63dc864a737983887e9008000043683799122a4982c6f78a4c40f00007319afa000000000017540af14723bb828867106b04bc9f220001f7e87c800000019ce87d14d68720000000002e1b2a0301498
  | 37 => 0x11f281f8000009141a0000df80001b9e000000084e9a5c536800032480007a3a19c0000f4263c06d40761d10441988c00012d618716d0000130616a0000000000000019886379e1873a0000000117647f10be85e1560000203613880001898000000215c4c500000001f4a757a254606186e000080a6d18d9a71b1d3617d8cdc49c129a3d514d000000005d9a0500cd03a6000000043b16645d68000418000046f0dd85f594740e306780000996000000000021321a1047061d800035f10a41ff8000000179000000000001dfa161983a7e5004c32201b632906f43c01c943d90c1e30613c60371dea021800017100f800015e200000007eb9e6464288741db93a431b822e7bd1be600015ca660225c5ae00007d1108c6c806f80001f823cda00c389030a7bd97c6000000049a1ee209b000001280004da1c6443d839e4d3059800007d00000000224914c36ba14624404a05ef0e8009d80004f28000000165e0001d8c0000eb61b40932000124a27194b26308000000021831f8be885014b833802007d48000000000000000000001a0201013dc0002002557800035e000000000f00000000570000076780000000a800ce8fb00fe000007f8000000000032a000066b8c1c8770e321d3127476500006b68000000000000021a600009744490000000219400000003950c9400000f63990f2883d815449202380000000270a09a0000c1224691a263e92aa0c21bd00000a0668408565de89b00001a20301800000011821f3981627800003ff800000000002822182000166c000000000000000001c4e000000076a067a0000e920000d9800000004a41a7a00008be1a480000000a4217f8cf80a9800068e854e4d6214c57820a081d09a8623838600000004458aa27a7948638a814c565958828f0588654a0ee40993182178d540a1990e890136a7d6000059a90700b303f03160aa4607897025216000b189d44e8000070b1a7c57d1716265181000012042a519363b7951a89aa21464212de31e9b2802ba2464c00cb65772244599855a6c48fec86802d872e114400003602b3066060c09fc00000966f8072259b956e03a053a1e908b6000075271a860a615846472d00001f3170629b94f44dd1a661718bbe176815c849806e50b9a4e0001c3e48984f07179af60c182525ae8000000000050d0000000000000005ea072950c77c800000000000000bbc00019d65108ea05dc8f50531800000000007400d100301bb831d182e5be0b085421a1400001ee2c400007d380002cb8000000223e00020180001dc0000000077189824801afc00000f451197fc5a516a80afa1ea007a13c2b51c0a0000a2c85389e800011b400001b47c397c843915c47ef93ac000000044a00005ed800008999640001cec39e8ec00001c6200017f8000039c63b80000001312
  | 38 => 0x4700a587978000000000000016542901be4000000044b10b20000f90081800000010c4241209c34995665f993ae0c81ba8573000026f0af88629bf040b8b781259eaa6e71fe675b80000000ebe1e78a220001fd65528000000063e00020fe3618000004800030a124653482b60000a623bb00001df10d667aa0e478d80007e421ba0000000000000071081182448000000000000000004db1e6000000003d880000000210000000020521de0000a206da80000001cc26d3000032800002ee935a00000002e6918c000000000020f07f09f0c000189623f968e000191474b133600012fa0001ec40001bb650e15640001642000000000012a800012a221009d285580000001cb200000000001cc000010000c9154e04f800067e94ac0000772000163a84d06380df1d720001b5e1fb97ee5ac98ea7fe8b6412096fa2e803165c6174a0000b1c4e41f8859712cc0769ee805288a43f98236458800073807e4259931e34c80004bc00003119efa0001af400000004139f000000e6634880007b99ebc0c68000021219a603161e61f93042d100006cf80805e59d3e03b987262187e82a5963c88981ea7338dbc00001de63980002d2999005c823e00000001ad80001e40b8c5c280007d982a050405dc0001c7a53c000083b0e1044794ae00000001a910a6000000000000003a0800058300ca000058e00010f455e800051d800089980000f4922446a800033f041470b8e182419bd67a200006098b3e0001d2a0000c006f500004a3000020800000002268574a10a3321ab02551d3200016f00fd9d7a0e90cd04ac0db22938f04519058a00000003cc800007a0dd66771e686b79ed400016cc4b617ce6d708d60001e8c44f00007bb00007e9902277911400000fde00000000a78000505184c67f97ae04190200869f04371815800000000001f2a3638d68000000045e120a09280001a98ed043387fa0000c907f500006470000000000065a9ad24ed800000006fa07e8ad00db000656c942a2918806339a22822100000000844089000000000000000c7c06e0000000000015899f4819800071d0000704027001d9e223558000000084c00010804d78000613840e11a0ccc5cc80004d299cc484159e0000000745918e00000004f818a44fe90665091da60b820f845e9fb46a48000000168c000000000012068331ac44710f180001e00000019e2ff8000000121a000057461c19ba2bd21240000000115957c4af14c063c91d07e6888038a21d81bf9cd657a8000676030463600006020e5600299480001d4418600001138a6c00011ee00000007bfa082058a0a4000000000013443f106da2001b147cb8a347e8912e0568b6022ba21e761211e6a58336344802c0000fb41119f100000a7e7939b7c09b98ca77980000001bc43d110d44cc21d64f5129e000
  | 39 => 0x60f1b623c5025a6c7000079c21d2022832c7a29d4c000000037b952e6081df80071b8042b8b2625d84b800007f2219800000000003c389e263692ae12c800077b800088d8ce41390e98518912684520266fe1e582ec066c754209e0d513cc6dd800000000000001ea07ab13b80aa0b8600000000620000381000043e95fe000217e80388f286c16505690000143148a810009c73f8aac00005ae3f08d722aa1b7a31800001b70916150994488c832a2f81fa088498c864599a850f08b054f0eda64e0000318800077280001970ab0068000000001f600019ca000127c00000000000000457a204000202e0000f86314000000000007868c04000000040183847fa800000000000000000000000085480001058000272800043815c6320000030b8000000000000006ba0001d2267f1de80be80000bd9646073012a00018b252e913666299ec29c8ac85a89c5421393888580aec2c78ada09792641ef18a800004e00f80c2c017939c32f074276701e26db191006890c87c59dac141201e5231ffe4ea80000000c9a40e169000005d07da18746391d7400007c02c485121060d36000000059e821c7c50bac33c1c2a7dd82c464f82680f7000004894fa00020d81de000036513f682b16124d00c4440e80000001c724d990567cc020a104852e41f8d6239c94ec7d780004b1800069b00006c192a623414c83198000724000000012447ec895e1c594580be00003fe918400000003898c4e5f280003b306f612216c04f3938000015f6672222a0298000000045c071871c3cf8000000000051987be4ff84740f298b60000ae228b9c6e86f091c000000087500006a800004b11ff66f2800074b9d6400011306cf00ce54190b012f08943eb06965549eb833196b00d01ec0064803224e97a60138f7e0700bc870885687050000276800023f000006a85322d6a16a6c89d825330bb27a19d9a5a79b60000066e0b3944a646a1ae000020e0001b403519276000172c0000c56855000016c142616480004850d5c8958000000078c4998000000185864f208c00013da322828e000208a4a600008719b686e5910854e80003521d5a00021685d19cc45bb9b3400000001ce1ab4000028010a0396000000035f80005eb1c4a000224a00012305df8ece4ed04944409ed84448368888961a07400003e89d541201af804d8dca1a2000000007621af00000a104cc000000002391c859c20b443a1378310009017f1d802f300002e78c2686a879200002fc4e582de23610f20000000000185c4c6997a00000004caa02802d1a2483380004790c0200019d248d20ea3be87c20001c840000d9205f972811b09606e5089000021b45bd89f04c096ca52a972e75f81300e3a03e72a04a87bc0c0a0000000000000081280285550f983f204a20000b0a2528ca2362800
  | 40 => 0x98000038019f0f5c0000000817800019f8510000000000000004ae8000000000043f000000000003ca9ab855d05a247813d23258dd2146859a67c00000001fec000128800003484848e6a113000072700005d1000003c9d1e15701fc5c9206e44d02b45ec0eb400020dc1cb911a4ba83782669ad655199227e91e801b088e827783182b299c66858d9c23803da4008f8206f02ae1cd8b487690d026f7048a47b07e66d513241b90a8c08220541ea0ea412402ea3cea1fc6ac88600d1876635b00008508546295801488f06a87a51e2c5440f7c0fe847c3fa0b2018b000000000007dc1d6a563804639c04207e30bfa2611a483929d186fa978a0000000000000000000003a702c85881bc043a830c8838cd43b216da45a94b40da9e1e79696e823390ba6180956157847e39b8d9e1f485a03901f3200016622f6800063800007ed828c27e9b4e1408da034105c07779cbc336a0120001a223bf95627ee80006950eca000000064b099e1e682643bc955c00018fc2b0928625b0656165883600000005fa8000194069a1b816e04e0823a5f904e84e18bf671e1158114107288e00483f60d7623d9f3822812dc1e50000000070e5a804924f4189400000007f71480000000000009b4487000015500000001e9a240180440a8000000000000015f22c38924692911c169055665a1bae7ac1f5a24080c80380296422000048f956a452201601580005840dfe05a8000000000078711902f600007b180001d200007c0997c000109e4b819e60000000000144e12100000001cac00000002fc00004be185e6191e6210915243121d040001d7855b0e080669d2061107d404789a22b591566cc88ea41202e40000e9e52c175c042893070d800028e08e258c00ba0000000000000051b000082e800062b062823b8f660a50ff013010b45029a847589b2a0001d260000e601cb0ef04a10b2403784fc4379ddc86c84fa6d5a25019a80005fa000005b000015d80007e70cee2420f705c09fd838583d0660849a4b5103484701e056a802200597f000015fc76d93421918a124cf80181b786400eb814e5860eb2346800081a19186f61aac00000001d196524cc8928608825810c130a62b82e805114ca7f200007508a8835c07c808087d600001e6000127a0000bc00000000000169a0000e7c000040a83194400548e366cb80001d3942c000220214a8000097000000000000001e7246005242069a0c22b00005c8000038000004f217de6af8e78274218800000003921608830120272f9ac6365a1764f6102c08f1f746898ee03da832200012b42fe03ea0eb133a000035a259163674c14886a9069836a804200005ee14218b0000044236915d4000000060c80000000000525104c00000001c51c0e755882430583580bb06b8445000000000001960000058056c00
  | 41 => 0x9486625969fe82711c2010f0a0475f15922df90a03cd189805e1ec26c78fe06579a8e59384f20c5027875b16566650ea81aa8b5021220e2216a1a810e9f8a7170cde0e68ef608307da778a0e87d305c82428a28574223a37385f004319b0805221a19995981708ebc52f16e43c989fe05ba0986b080007661d0a4ec1e10000000032c0fbe0000e2c3e30cec0001812098945c6371dc27398c2a19a01560000f1c0ef02a42bc000058f8fb20161acc78500004a2800000003fc5558b768600c341eb1b10000000075180d24b01f480000000782894624890d0380a02a0001e3e81ea20a32aa1623c8000000011d86ef1992000061400017887f79b42000139a3ce000002a80002cc00005d6104256e0f4c61f1b7e68a06744d1990c280186633e914a5db9b4a05d800071a1e2a783800072d80007810a0e3fc9a1a7c615ec00010b60001aea0098fcc1a880005891cd80bc90c02ff0000654218e03602927c69a3609800006e98000000000086886c81ee15280f0032e2b19a7e4988d5a1c4a00a631225e5c780001fd076c20e8abe00000d400013ee2038b6217a0b8a3e3891878f18be28c80002bb992a20f1900000000066f0000000157002520c234d09425b8977c4b4000027b00007a112ce00000002ca93de0cf1c4438e16f20001054279815e8541c1a1c81ce453a8e8c2a080007bc842e66f9d861461f7263a0ed609a88824d805380bb80003081c6000000004039b1a22286ae39a16140000afe00017da000010e00007b03c2987a64b80000001e6e67e1ba2000000032104e614f80005d803127cda1086dd1d387ea050a0f21dbc494028203a8c3a1f60d5076d104a3d61696104044478c128002c0b2c0878e8820c05400fb09f47e5901a27a9ede7c980002ce1faa70c97a260280c454c80305b78682461981a000000000000002b9203a65b956800000da03f05ca5c7117084d95262aa80be62d1b243fd1e6633d10762d194b64238f02286811260f84d21370db832b994a69c19c226416026ad99e2455067072209505c4975e0ffa05209c96603bd0a301d0030021e89ba7780ed47899efc000054a5e704d629f0ea200020047c4800001a8fb6000000021a19aa0000bc689091101f19b9a2ba07086810ab61ac96d60400e2e781800000020ca00008180000f5e1378a1c0c3800000020606b8800038c000082a000049398624428fea001110e0001978118840c0000fc01591eca27d8cce5f118ba0bf8f244c30328000109429e800009308fa00013481840c3e64180001f12092573800017580002ad0000821077a634800030e20e01d69e7c41e94520000e5e000000087318aa36f94684141a802c615ae4bf84ec38382d037d8b5c3311df668b1c3a649000017480000000000000000086597b82671cfa3f900d606e978c00000000001a
  | 42 => 0x5de188179424d80005b207822ac8ad800017fe71f976a8769a6a405168888c085851f2208744a0565e0842a26211f6425a0946a895821070cf62660fae0aa96a61eb92ee4401d400fd1c245d0952c53d856a6570e3c34b01c441a98a0100049e00011fe7d0a05855080000000cca00014ee4b690ca6d2122c58d0f3c7e0047860715784ea0d0e0000bc27a7078a60397c084a99565bd08aa16e07686c38000000158c4361d241e5800021495727db800067b9a8c0000088000103e53c800059600008468000889000049b8cfe2f387ea00008a26bb9d0e47700000d08ee80001f3a77522642d30000000069e86483b655300005ce80000000000000000000017144b897003798f8023e16a46901628000000000d91c25b38f845b490f800012946d10e20000171012a80003e7000000000005c891e22cc800007486326f300002e380000000a6600000001198000859800065d000022a10403f41a8a53f85aa2fa975056a11b21831a727a400000000ba46b500003c480003b88d185a18c787de193242a00001a700007739b8e15315b433a0a446b60b7a1df9ba464d0c5c05f205a0cc873c285046a29419da17c82667048a8a6af0da61e21bec8460a4a76e917258b00004a4800000000006a5000000009f856b000084b0244456800073521724df967602f000002606224091c661b010164538a785641a183300bb42f9872485c20e61e8a1f02e59220000027a57585666fd00005cf007223700005e90000000110473681ec32d126c0ed1a460000ed200018f62d38b66490925e05d08e605e8de461a9a3025c93505ee93be32f99f689202a2223878e23784ee72c1e420a7150a51220a679e81166668fc631c803a0000b6c00000000000000699000088b08ba2ed80000000d1483692ac36316d800000000001bc85289db2000000048381140000000000000000019620001e12000219e0001eea73e01be45f103274e800016114d84649cdc4b900006ae800018109a06269df02a40000116800073218fe181909213103567c2178400016920000f6e610086474a0eea00001080001dd654a86d82d01a4c0001bba6ce94de7c78000714140665c8b8277b077470202420d116061ca1c0c00019a27760c982c8800046e9b040950f0c000000021c835c000070c000037600011ea0000bd26ec959446b01dc0a61d4e00000000000000000000066988ec000161c0000db02390000000090e18d087c0f99e505791b786c2976c2501cca41680004330d6e85600007fc800050700004bd822c23c0f6832c8b746118a0a27383cc3c18b3424b21c273c147e1ff00622da83c6000021479a90fe384800080c9bf600012363de8eb000f8e0c34e80003d580004ee997654121ee18214a45911f403fb825079d05d802316687c2982818ea23418798685a71e0c4
  | 43 => 0x33a81ce6b0000064105ac3889f2460d97f280d1f6a8019b6e4ef21060f501b27f01e5489380685338c861419e3406904da0d99f348081d085f306c60001e482f90000000057e0000a3a2c689b253f050e2a610300001d9200007f849a9942527189266b03d80f9000000000003d48f4a000033800017f6387000000000000000d4e4731c7611485b4000000054592542009e380888e740fc800062f14a600000007f100001ad0dc4000074a01e1548438833e7470e3a03f800000000004308cba00009b87a49ff0000198e0001a522ae92e83d2000000000000000000000013865600a4000151e357945000000006a9937a7a600000000c9e52589340000b0c46691fa0001dc46d48d002f88310562800048b8000000000075c000037c15be6331078880123a0b50008600858200000001ed8b4288801660000d4a000000085280005e380002971a3c0000f1600006ee77f828a6cb1774785856e0000000000000000017b47c710045af89be42404864d88a6800004d800009b647a173e0d91a3e485962e4a58bec0000000000151874f0000151116044813d600003300e082e282398a246f80002f588c600000005e69eb66c214280e40afa1069baa000000032b1c52556086a00018d63a28a3676217926cd939847680a037e800000015c224e1f5c5a110821d919462f10fca7ff18ec89300002fd000001f92382ae000049f8d5211e88041a2898c7f4822a2330000000000034a8000000092e0169b980001470000000070c00002ea0000298000001b0fce30c0d248859c8a72080000001cee00007566c992726340e76487974e000000000000004b99bb07ab8e46000000000017764df21200000de800003b8000016800000000000c521181884705893c0000bd463d0b3a000009e04116982e41c925b1800047e01c80000cc20001e4c6580000000076a3689a0e71015c8667800011c82d603b00e68830f9a60aa18c3610d3c46e0a1e10220446a080006fc91b02c191ca000000000017800000e9600000002628000790152000020d200005de4ca0000000154034a1c8c6000000345800000012c235a80002a99ba00000000000000030ca184000000002497783d006f036085e05d2000053517706478e4c35005e4000138c000000054c00000db96261dc02406fe9f286b39046000082200000005450a864ac85e625694dc4c4081000000000001f6041d0000000159a4c8800001400003dd0a248690afc5c68000101a0703bf1aaa5e180000b281506ed06d622200003a5133823212b882210da62720ae0000a7630d90123909814000000000020aa3ff000007d0000000085c19d97a888b94a029a979e4fa80005ad8572154000065f800000000001150f884e496c208c0b7084e20b268217304738d2e6d9800050f85f848a147a7cb1
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x388c875093258f100050b6487459530c400148d921d1634c3100058364e6250b658400192b8750920d961000516a43739cf658400105f985cc73d96100058364e7250b6584001471911ce70d96100060b61d42c836584001a0d8350b20d96100060be1d424836584001a618148020d96100050b65e62508658400160d9398942196100050be5d62508658400192b87509201961000e23e1d424cb638400142d921d36558e100050b64874195638400182f756087458e100060b1d5821d1638400148d921d37358e100142b26172509638400128d922116318e1000748509205c650840014579359171142100050de51635c45084001c2562509711421000748509205c4508400142d921d3654c2100052364874d8d3084001a298460062d95100058a2594248365441e5a288650920d9510796c8205424836544001a0d8350b20d95100068a6118018865440016289650920195107ee8a2194248065441fbb208150920195100052aa5b72483644400188d83dcb20d9110006a26118018b63440016889650920d8d10786a22194248363441e1b808150920d8d10785a26407250b63441e188e8750b20d8d10006a26118018863441dba50811952018d10005a22594248063441d9a88865092018d10007821954248063441d9b80815092018d100062361d42c8063441d9a84815092018d1000568a4770dd3624400148d939c774d89100052a64271dd3624400148f935c374d891073616a18639c35144001c1b6418c705451000706190631c151441cdc529118c705451000714644631c15144001c4863d8870545100070a190621c15144001c486318870545100070618f421c151440014389650870545100070618d421c15144001e09424806314110735942452018c50441cdc501018d71141100050b64874d95304400148d921d3634c1100042ba6074d8930441cd45a90dd463841100068360d42c81650400188d8750b2098c106fd292457250963041bf684915c94258c100062361d42c81630400148d93dc174588106fe29205745cd62040012e1912015358810007185c670588500400143792591711401000714241635c45004001c2694589711401000709651625c4500407bc618058971140100050d65b425c45004001c1563d0971140100070958b425c450040014359650971140100070558d425c45004001c2562509711401001d1c65a805c45004001c6162a0171140100069458d811433004001a616260450cc0100050b64874595300400148d921d1634c0100042b66074589300400187176604500c01000698589811403004001871865c4500c01000718589711403004001c91645c5300c01000730589714c0300407d4729021776440100070cddb749411004001c5376dce504401073654a1c739411004001c6376dca5044010
  | 1 => 0x76e16dd88054531cc00195171201311433000523e5d424cb658c00388f8750932d963000417662761cd518c0016249158942d95300050b648645c7654c00160d939c942d95300060b61d42887654c00182d8750821d95300068360d42087654c001a294260021d95300060b61d42c83654c001a0d8350b20d95300f60be1d42483654c04782e7060864195300fe0b1c182190654c00142d9798942195300058364e62508654c0016299098942195300050be5d62508654c0016249158942195300050b648645c4654c00142d929db65d91300050b64a76197644c0050ae98dc962d913000629dc88158b644c0010af985c862d91300062360f72087644c0018ab7260021d91300062360f72c83644c0010ad92a1b7454d300060b1d582193614c001a858350821d8530006a850980087614c00142d929d365985300050b64a74196614c00182e7560864985300060b5d582192614c00182f7560864585300060b1d582191614c0010ad981c864585300042ba6064dc9614c00182e7560864185300060b5d582190614c05d88e7360864185300050b648649db514c00142d9219270d453000523648645ce514c00142d9219276545300050b648641d9514c00142d92190705453000523648649db314c00160d9219365cc5300058364864197314c00148d9219270cc5300050b648645d6314c00142d929d3658c5300042b648865d2314c0010af9261f648c5300058364864d95314c00160d92190654c530005a164864d85314c00148d92190704c53000706194641c1314c00158992190704c53000526259421c1314c00145896544704c5300050b648649da504c00142d921917194130006169d8804c6504c00148d9219373541300050b648649d8504c00142d9219171141301ee15219714c4504c001c14645c5311413000686190804c4504c0019517120131141300058364864d96304c00160d92190658c13000523648645c6304c1d988c8750932584300049c24185885610c001e05424c9615443000616618731c1510c001c53735847054430007141cd611c1510c0015189460c705443000456660431c1510c0015499210c705443000742509321c1510c1cdc503158470544300071498d611c1510c1cdc5393584705443000714a0d611c1510c001c5183584705443000714d0d611c1510c001c504358470544300070cd09611c1510c001c3142584705443000714cc9611c1510c001c5132584705443000615619718c4500c00148d921d3764c0300054364874dd5300c00150d921d0754c0300052364874585300c00185b76a03514c0300061521d61545300c001c1474585514c030006461d080545300c001a5161201514c03000417e61731cd65c400160d931c942597100060ba1d42c8165c4001a0d8350b20597100f60b21d4248165c4
  | 2 => 0xc401c89424c870595310068360d42c81650c40182f7560874580310060b1d5821d1600c43388f736087458031006231cd821d1600c4050ac985c942580310052a25d42481600c5bfaa08150920580310051364c52dc9619400182f8758942d8e5000543e5d424cb639404190f8750932d8e5000683e19424cb6394001c296250a70d8e500071258b329c36394001d09424ca70d8e500060761e84d8e639400181d876136398e500061361e82d8e6394001a0e84a0b6398e500061361d82d8e6394001a4982a036398e5000487a636350a6394001c0f635c94298e5000507e5d63d08639400141f9758d4218e5000742509329c0639400160d9398942d86500061360f7298961941e542e9798942586500058364e6250961941e56269198942586501050b25d62509619400122d92a13735865000607613739cd619400184f7360a735865000417e61731cd619400184d83dca72586507958a6407250961941e582e8750b20586500068360d42c8161941e5a268150b20586507960b21d4248161941e5a2481509205865000516a427698d319400105e981d9634c6500052364a74d8e315400105f985cc735845000516241731cd611400161593a0742584507ed89a4782509611400160d931c942584507ed8a64072509611400161593a0542584500058c2418150961141fba268150a32584500068a509808c961141fba264160b41584500068560f429056114001a158350a41584500068960942905611407b2369890d415845000589648435056114001a27825094158450004996488050561141fba262161321584500049c241838856114219a268750a21584507ef09a1d428856114001a258350a21584500049c24184485611400123594e0d21584501ed986407248561141fba278250921584500048d65080485611407b2349850540584500068520d4150161140012359890440584500068960a4110161141fb82e8750b20584500068360d42c8161141fba268150b20584507ee0b21d4248161141fba248150920584501ec9926121481611400126598884205845000689612210816114001437925d1618c4500050d65f42586311400143597509618c4507ef09dc9425863114001470905d1614c4501ed15a5f4358531140016459210d614c4500051c241725853114001c2772509614c450007815093258531140015189458c704c45000516658431c131140015499210c704c45000742509321c131141dbc5231584704c45076f140c5611c13114001c5263584704c4500071458d611c13114001c5393584704c4500071424d611c13114001c5343584704c4500071410d611c13114001c3342584704c4500070c509611c13114001c5332584704c450007144c9611c13114001a0d8350821597300068a5098008565cc001a0d8350b205973
  | 3 => 0x311e028b4071621341f2b1061618511c7443846000a039c94038061b16d1a40060907388000793d194be4dd944ed90008ba62414348ed000ee384f20010c5bc0f6044a121470009d13898249784e102580005993347400190390002320c004bcfa001420ed880000c5c8f93ac3a36400000a33242710d411587d080242a15c00067534af22d345b800000ff464ec001865c4dd5215f30c622ece31d4f43a4db2b4bd00079000000000047d841e16700077000990a0002c02a3d800454931d90a560d6674002013f0c8c7000a4000005740067072000ce000c8000000c4820d92e6558f00000350006845400103328001b40000000155141ecd353c9a49cbf0954e2352d000000015e35c905256c1f85e00000550d85acb14c974040045600000060407800061d038102600008000004000343601000a4000404000000e000488a02078190a0e028e812010004430000b8144e07008001e0000050280c030e42005000200e1c02828100100004460e05818300500038000b2f0280610008042c070580404000a004001e0701c020500004040f008000000018143200000041a0a050581c020301404a200024020005004001a0006002010051c644501c16194c0188d83dc821d91530062adc9800876454c0188d83dcb20d915300417e61731ce60d440160d939c942983510048ee614010260d461d82d8750b20983510068360d42c8260d461b82f8750920983510051364c525c86054401d05424c97198d510060b21f62509635440150c975093258d511864321d424c96354401a0c865093258d510074150932dc56354401458935907058d510051624d621c16354401c2b625087058d5100712d8b321c16354401458964c87058d5100742509321c1635440181f87e116318d5100607e1c8458c635440184f87e096318d5100613e1c8258c6354401a0c842096318d5100616e1f8058c635440185b872016318d5100686e108058c6354401a18842016318d5100692e088058c6354401a48822016318d5100616dc88058c63544014589058d7218d5100507e5d63d0863544016189058f4218d510048726163508635440141f9758d4218d5100586241635086354401c0d635c94218d510058364c6250a605440184d835c862181511850b65f62508605440142d9718942181510058364c62508605440122d92211731815100417e61731cc605440181d845cc731815100615605731cc605440184d7360873181510061360d721c86054401865815c872181510068a509808c86054401a2942e0132181510068360d42c80605440160d931c942596310060ba1d42c81658c401a0d8350b20596310060b21d42481658c40188d835cb20592310042be4986dd1538c4038a88750920582310052325d424c9654c40388c8750932595310051624d541c1654
  | 4 => 0x64d520004b0018d23d73485226000044c0000192499590d400000073686e000001c4a6420c006c0062c00100810f8190b4004e4ae1f18302c5f06111658e84700061d98295231c0e652d16544b52c8e546cfb5fc730018a218b90002f314aa0001039104105100013c494211a0d06442b5f9701409b000000001a5dd630019a45c960016921d0f33c221490504861000005e56a114514a9766799b1744f055300017a2447f1246f0e0bc65cef3701367c8e0342e0b118469016653a584fc15c88231a0098ab14c425f155165644f80000030000de63800000004c400000164d8fe42ca953156481403c0df5f4cd32d5a5186b020ea4b135228c21a8341e928594d5330d14490d318f5224c10dd4354cb816c1d168a721175110b7425440f1243dc3d0fc093ccf8284f127968000b64a4950009755c9f1995b528c4000a2214632cc292715038001401455ec6005c5c3f4051312b0cc0400c116
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1908000000e01560a01268f00321600d1445134472d004c1895c200000106006100300c97219424c96354401a044b284990e0b1aa200a032a1635c94218d5100581140b1ae4a10c6a880300f97e19424cb6394001407546c6b928531ca111c8160993a074258450004a13444a2c63826228002c10a458d611c13114001620d1086b08e0988a000f0050932584704c450006810cac90c83826298002c05a2191714c4504c001504d10c8402622826000e04191712013114130004a13444a306382a218002c10a460d611c1510c001428d4086b08e0a886000b1068843584705443000780284992c2382a218002c05a21d161545300c001484d10e8402a29806000e041d161201514c030006441024b284900ca8800328081259424806344221d00408caa124031a210fd80245424806314110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x32100004c01b229163584704c450005801b2191712013114130004c01b2291835847054430005801b21d161201514c030
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x4b
  | 6 => 0x4d
  | 7 => 0x4e
  | 8 => 0x124b
  | 9 => 0x4
  | 10 => 0x94b
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124d
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138d
  | 17 => 0x138e
  | 18 => 0xcb
  | 19 => 0xcd
  | 20 => 0xce
  | 21 => 0x12cb
  | 22 => 0x9cb
  | 23 => 0x9cd
  | 24 => 0x9ce
  | 25 => 0x12cd
  | 26 => 0x12ce
  | 27 => 0x168b
  | 28 => 0x168d
  | 29 => 0x168e
  | 30 => 0x14b
  | 31 => 0x14d
  | 32 => 0x134b
  | 33 => 0xa4b
  | 34 => 0xa4d
  | 35 => 0x134d
  | 36 => 0x24b
  | 37 => 0x24d
  | 38 => 0x24e
  | 39 => 0xb4b
  | 40 => 0xb4d
  | 41 => 0xb4e
  | 42 => 0x144b
  | 43 => 0x144d
  | 44 => 0x144e
  | 45 => 0x16cb
  | 46 => 0x16cd
  | 47 => 0x16ce
  | 48 => 0xbcb
  | 49 => 0xbcd
  | 50 => 0x14cb
  | 51 => 0x14cd
  | 52 => 0x19cb
  | 53 => 0x19cd
  | 54 => 0xecb
  | 55 => 0xecd
  | 56 => 0x17cb
  | 57 => 0x17cd
  | 58 => 0x94053
  | 59 => 0x95253
  | 60 => 0x94055
  | 61 => 0x14a
  | 62 => 0x134a
  | 63 => 0x14053
  | 64 => 0x14c
  | 65 => 0x14055
  | 66 => 0x135253
  | 67 => 0x134053
  | 68 => 0x134c
  | 69 => 0x134055
  | 70 => 0x124953
  | 71 => 0x124955
  | 72 => 0x14953
  | 73 => 0x95353
  | 74 => 0x14955
  | 75 => 0x134953
  | 76 => 0x134955
  | 77 => 0xbc953
  | 78 => 0xbc955
  | 79 => 0xbcc
  | 80 => 0x19c953
  | 81 => 0x19cc
  | 82 => 0x19c955
  | 83 => 0x128a
  | 84 => 0xca
  | 85 => 0x12ca
  | 86 => 0x130a
  | 87 => 0x139253
  | 88 => 0x15253
  | 89 => 0x15255
  | 90 => 0x135255
  | 91 => 0xbd253
  | 92 => 0xbd255
  | 93 => 0x19d253
  | 94 => 0x19d255
  | 95 => 0x15393
  | 96 => 0x15395
  | 97 => 0x135393
  | 98 => 0x135395
  | 99 => 0x9c0d3
  | 100 => 0x9c0d5
  | 101 => 0x9d2d3
  | 102 => 0xc9d3
  | 103 => 0x140d3
  | 104 => 0x140d5
  | 105 => 0x1352d3
  | 106 => 0x1340d3
  | 107 => 0x1340d5
  | 108 => 0x1440d3
  | 109 => 0xd453
  | 110 => 0xbd2d3
  | 111 => 0xbc0d3
  | 112 => 0xbc0d5
  | 113 => 0x19c0d3
  | 114 => 0x19c0d5
  | 115 => 0x12c9d3
  | 116 => 0x12c9d5
  | 117 => 0x9d353
  | 118 => 0x149d3
  | 119 => 0x149d5
  | 120 => 0x1349d3
  | 121 => 0x1349d5
  | 122 => 0xb49d3
  | 123 => 0xb49d5
  | 124 => 0x9cb53
  | 125 => 0x16c9d3
  | 126 => 0x16c9d5
  | 127 => 0xbc9d3
  | 128 => 0xbc9d5
  | 129 => 0x9cbd3
  | 130 => 0x19c9d3
  | 131 => 0x19c9d5
  | 132 => 0x130c
  | 133 => 0x1692d3
  | 134 => 0x12d693
  | 135 => 0x152d3
  | 136 => 0x152d5
  | 137 => 0x1352d5
  | 138 => 0x252d3
  | 139 => 0x12c253
  | 140 => 0x1452d3
  | 141 => 0x12d453
  | 142 => 0xbd2d5
  | 143 => 0x19d2d3
  | 144 => 0x19d2d5
  | 145 => 0x15693
  | 146 => 0x15695
  | 147 => 0x135693
  | 148 => 0x135695
  | 149 => 0xb5693
  | 150 => 0xbd693
  | 151 => 0xbd695
  | 152 => 0x19d693
  | 153 => 0x19d695
  | 154 => 0x24153
  | 155 => 0x14253
  | 156 => 0x14255
  | 157 => 0xb5353
  | 158 => 0xb4153
  | 159 => 0x14b53
  | 160 => 0xb4155
  | 161 => 0x14b55
  | 162 => 0x144153
  | 163 => 0x15453
  | 164 => 0x15455
  | 165 => 0x16c153
  | 166 => 0x156d3
  | 167 => 0x16c155
  | 168 => 0x156d5
  | 169 => 0x134a53
  | 170 => 0x134a55
  | 171 => 0xbca53
  | 172 => 0xbca55
  | 173 => 0x25353
  | 174 => 0x134253
  | 175 => 0x134255
  | 176 => 0x134b53
  | 177 => 0xb5355
  | 178 => 0x134b55
  | 179 => 0x145353
  | 180 => 0x135453
  | 181 => 0x135455
  | 182 => 0x16d353
  | 183 => 0x1356d3
  | 184 => 0x16d355
  | 185 => 0x1356d5
  | 186 => 0xbd353
  | 187 => 0x134bd3
  | 188 => 0xbd355
  | 189 => 0x134bd5
  | 190 => 0x14d353
  | 191 => 0x1354d3
  | 192 => 0x1354d5
  | 193 => 0xed353
  | 194 => 0x134ed3
  | 195 => 0xed355
  | 196 => 0x134ed5
  | 197 => 0x17d353
  | 198 => 0x1357d3
  | 199 => 0x1357d5
  | 200 => 0xbcb53
  | 201 => 0xbcb55
  | 202 => 0x19cb53
  | 203 => 0x19cb55
  | 204 => 0xb8c
  | 205 => 0xbd6d3
  | 206 => 0xbd6d5
  | 207 => 0x19d6d3
  | 208 => 0x19d6d5
  | 209 => 0xecbd3
  | 210 => 0xbced3
  | 211 => 0xecbd5
  | 212 => 0xbced5
  | 213 => 0x17cbd3
  | 214 => 0xbd7d3
  | 215 => 0xbd7d5
  | 216 => 0x1a8c
  | 217 => 0x178e
  | 218 => 0x1349405b
  | 219 => 0x1349405d
  | 220 => 0x4953
  | 221 => 0x56d3
  | 222 => 0x188a
  | 223 => 0xd0a
  | 224 => 0x5853
  | 225 => 0xd0c
  | 226 => 0x4955
  | 227 => 0x5555
  | 228 => 0x10c
  | 229 => 0x10a
  | 230 => 0xc152
  | 231 => 0x95355
  | 232 => 0x94153
  | 233 => 0x94155
  | 234 => 0x8a
  | 235 => 0x188c
  | 236 => 0xd00d2
  | 237 => 0x140d2
  | 238 => 0xd0e
  | 239 => 0x188e
  | 240 => 0xd12d2
  | 241 => 0x95295
  | 242 => 0xd1352
  | 243 => 0x9d355
  | 244 => 0x9c155
  | 245 => 0x9d9d5
  | 246 => 0x9cbd5
  | 247 => 0x58e
  | 248 => 0x135692db
  | 249 => 0xb0e
  | 250 => 0x20e
  | 251 => 0xb8e
  | 252 => 0x28e
  | 253 => 0xd0152
  | 254 => 0x154e
  | 255 => 0x184e
  | 256 => 0x1456d5
  | 257 => 0x150e
  | 258 => 0x98e
  | 259 => 0x180e
  | 260 => 0xa0e
  | 261 => 0x128e
  | 262 => 0x8e
  | 263 => 0x130e
  | 264 => 0x10e
  | 265 => 0x592d6
  | 266 => 0x74c
  | 267 => 0x58b56
  | 268 => 0xd0216
  | 269 => 0xd1516
  | 270 => 0xd0996
  | 271 => 0xd00c15a
  | 272 => 0x14d00da
  | 273 => 0x14d12
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 1936
  | 6 => 5691
  | 5 => 4406
  | 4 => 418
  | 3 => 27
  | 2 => 4
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
  | 8 => packedAt gbK8 (1870+((h/22+packedAt gbK8 (1716+(h % 22)*7) 7) % 80)*8) 8
  | 7 => packedAt gbK7 (79372+((h/645+packedAt gbK7 (71632+(h % 645)*12) 12) % 2324)*12) 12
  | 6 => packedAt gbK6 (297829+((h/1897+packedAt gbK6 (273168+(h % 1897)*13) 13) % 7513)*14) 14
  | 5 => packedAt gbK5 (279038+((h/1468+packedAt gbK5 (259954+(h % 1468)*13) 13) % 5816)*14) 14
  | 4 => packedAt gbK4 (30511+((h/139+packedAt gbK4 (29260+(h % 139)*9) 9) % 502)*10) 10
  | 3 => packedAt gbK3 (2241+((h/9+packedAt gbK3 (2187+(h % 9)*6) 6) % 36)*6) 6
  | 2 => packedAt gbK2 (371+((h/1+packedAt gbK2 (368+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe07ff80ffc07fc0fffc03fd13f3e7d8f33f3
  | 1 => 0xfff80fff03ffffff03fffffeec8d18e71fc7f
  | 2 => 0xf07fff00003ff83fffc3ffc030f0e1f381cf9c
  | 3 => 0x7fffffffc0003ffffc00003f00fe03fe0fe0
  | 4 => 0x7fffffffffffc0000000003fff0003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x50a00b28024c424c02464095801306348711b1
  | 1 => 0xd02805310110c911028952a06485088306446
  | 2 => 0x607555008626d226ae832a80b0b0a153818a98
  | 3 => 0x459e69dac80803bcd3003033b00fa035a0f60
  | 4 => 0x487e78e6cf3be70086020c0c3dfd0003edf000
  | 5 => 0x8e10400708030403082030303feefdec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36711
namespace PEqualNP.Outside.L_meta_36711
open PEqualNP.Outside.L_meta_36711.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 1 := bs0_2_0
theorem alls0 : ∀ k ≤ 2, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 3 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 10 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 13 := bs1_4_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 6 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 56 := (concat bs2_3_0 bs2_3_32)
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
theorem bs2_4_768 : Interval s2Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 781 := (concat (concat (concat (concat bs2_4_0 (concat bs2_4_32 bs2_4_64)) (concat bs2_4_96 (concat bs2_4_128 bs2_4_160))) (concat (concat bs2_4_192 (concat bs2_4_224 bs2_4_256)) (concat bs2_4_288 (concat bs2_4_320 bs2_4_352)))) (concat (concat (concat bs2_4_384 (concat bs2_4_416 bs2_4_448)) (concat bs2_4_480 (concat bs2_4_512 bs2_4_544))) (concat (concat bs2_4_576 (concat bs2_4_608 bs2_4_640)) (concat (concat bs2_4_672 bs2_4_704) (concat bs2_4_736 bs2_4_768)))))
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
theorem bs2_5_800 : Interval s2Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 801 := (concat (concat (concat (concat bs2_5_0 (concat bs2_5_32 bs2_5_64)) (concat bs2_5_96 (concat bs2_5_128 bs2_5_160))) (concat (concat bs2_5_192 (concat bs2_5_224 bs2_5_256)) (concat (concat bs2_5_288 bs2_5_320) (concat bs2_5_352 bs2_5_384)))) (concat (concat (concat bs2_5_416 (concat bs2_5_448 bs2_5_480)) (concat bs2_5_512 (concat bs2_5_544 bs2_5_576))) (concat (concat bs2_5_608 (concat bs2_5_640 bs2_5_672)) (concat (concat bs2_5_704 bs2_5_736) (concat bs2_5_768 bs2_5_800)))))
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
theorem bs3_3_0 : Interval s3Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 4 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
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
theorem bs4_3_96 : Interval s4Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 112 := (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96))
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
theorem bs4_4_864 : Interval s4Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_896 : Interval s4Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_928 : Interval s4Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_960 : Interval s4Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_992 : Interval s4Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1024 : Interval s4Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1056 : Interval s4Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1088 : Interval s4Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1120 : Interval s4Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1152 : Interval s4Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1184 : Interval s4Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1216 : Interval s4Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1248 : Interval s4Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1280 : Interval s4Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1312 : Interval s4Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1344 : Interval s4Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)))) (concat (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 (concat bs4_4_416 bs4_4_448))) (concat (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)) (concat bs4_4_576 (concat bs4_4_608 bs4_4_640))))) (concat (concat (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 (concat bs4_4_768 bs4_4_800))) (concat (concat bs4_4_832 (concat bs4_4_864 bs4_4_896)) (concat bs4_4_928 (concat bs4_4_960 bs4_4_992)))) (concat (concat (concat bs4_4_1024 bs4_4_1056) (concat bs4_4_1088 (concat bs4_4_1120 bs4_4_1152))) (concat (concat bs4_4_1184 (concat bs4_4_1216 bs4_4_1248)) (concat bs4_4_1280 (concat bs4_4_1312 bs4_4_1344))))))
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
theorem bs4_5_800 : Interval s4Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_832 : Interval s4Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_864 : Interval s4Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_896 : Interval s4Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_928 : Interval s4Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_960 : Interval s4Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_992 : Interval s4Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 bs4_5_224))) (concat (concat (concat bs4_5_256 bs4_5_288) (concat bs4_5_320 bs4_5_352)) (concat (concat bs4_5_384 bs4_5_416) (concat bs4_5_448 bs4_5_480)))) (concat (concat (concat (concat bs4_5_512 bs4_5_544) (concat bs4_5_576 bs4_5_608)) (concat (concat bs4_5_640 bs4_5_672) (concat bs4_5_704 bs4_5_736))) (concat (concat (concat bs4_5_768 bs4_5_800) (concat bs4_5_832 bs4_5_864)) (concat (concat bs4_5_896 bs4_5_928) (concat bs4_5_960 bs4_5_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 48 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
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
theorem bs5_4_64 : Interval s5Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 90 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 4 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 27 := bgb_3_0
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
theorem bgb_4_416 : Interval gbAtlas 4 416 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 418 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416))))
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
theorem bgb_5_4384 : Interval gbAtlas 5 4384 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4406 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))) (concat (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896)) (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))))) (concat (concat (concat (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312))) (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))))) (concat (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)))) (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 bgb_5_2016)) (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176))))))) (concat (concat (concat (concat (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432))) (concat (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)) (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720))))) (concat (concat (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 bgb_5_2848)) (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 bgb_5_2976))) (concat (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104)) (concat (concat bgb_5_3136 bgb_5_3168) (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)))))) (concat (concat (concat (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 bgb_5_3392)) (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 bgb_5_3520))) (concat (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 bgb_5_3648)) (concat (concat bgb_5_3680 bgb_5_3712) (concat bgb_5_3744 (concat bgb_5_3776 bgb_5_3808))))) (concat (concat (concat (concat bgb_5_3840 bgb_5_3872) (concat bgb_5_3904 bgb_5_3936)) (concat (concat bgb_5_3968 bgb_5_4000) (concat bgb_5_4032 (concat bgb_5_4064 bgb_5_4096)))) (concat (concat (concat bgb_5_4128 bgb_5_4160) (concat bgb_5_4192 bgb_5_4224)) (concat (concat bgb_5_4256 bgb_5_4288) (concat bgb_5_4320 (concat bgb_5_4352 bgb_5_4384))))))))
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
theorem bgb_6_5664 : Interval gbAtlas 6 5664 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5691 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184))) (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)))))) (concat (concat (concat (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))))) (concat (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)))) (concat (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624))) (concat (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))))))) (concat (concat (concat (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976))) (concat (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072)) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)))) (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520))))) (concat (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680))) (concat (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776)) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)))) (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032))) (concat (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)))))) (concat (concat (concat (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384))) (concat (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576)))) (concat (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736))) (concat (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832)) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928))))) (concat (concat (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088))) (concat (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184)) (concat bgb_6_5216 (concat bgb_6_5248 bgb_6_5280)))) (concat (concat (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376)) (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472))) (concat (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568)) (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664))))))))
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
theorem bgb_7_1920 : Interval gbAtlas 7 1920 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1936 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448)))) (concat (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672))) (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800)) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928))))) (concat (concat (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152))) (concat (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)) (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664))) (concat (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792)) (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 bgb_7_1920))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 66 := (concat bgb_8_0 (concat bgb_8_32 bgb_8_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 3 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8eeeaeae8eec8e8c8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 4006144200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36711.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.and,[3,6]⟩,⟨.or,[1,7]⟩,⟨.or,[0,2]⟩,⟨.or,[7,9]⟩,⟨.or,[3,6]⟩,⟨.and,[5,11]⟩,⟨.or,[0,1]⟩,⟨.and,[10,13]⟩,⟨.or,[8,12]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4006144200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4006144200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36711

open PEqualNP.Outside.L_meta_36711 in
theorem PEqualNP.Outside.L_meta_36711 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4006144200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4006144200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
