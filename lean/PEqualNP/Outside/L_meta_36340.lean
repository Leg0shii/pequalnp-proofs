import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36340.Model
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


end PEqualNP.Outside.L_meta_36340.Model

namespace PEqualNP.Outside.L_meta_36340
open PEqualNP.Outside.L_meta_36340.Model
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

def SBf (j : Nat) : Nat := [7, 6, 6, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36340

namespace PEqualNP.Outside.L_meta_36340
open PEqualNP.Outside.L_meta_36340.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x1abc8161e302230070c1a44852275404eac00987170c008803e940035a6d4095c00a803c009294000c80261c2ab0428a081600138d2472000c004f041140ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1486ca64d0d04844723d060647b3c10cc244289a06e7e011fc066b032004c2b0a1b0f23322a08cc040a9bc46002a92c5400249f10a1c00000b8113b9500a2d041901e160007c7a6531918122c00000c400001080067370400000000800000388ec002e2c01c325a1e128002435000ae48000bc00002382c807000130005f000fc3a001a8e90674291d4da4e208c01400300e0005e3e800e6252e85c7c39188d89e76098a0a00142030b63413834ac81108781c692c80030015418149400002420580c3c6c1004140000004450a40004041c0400000014080844f0080000000400127ca5a1cf947439ea86873d5490f3ea6a1cf149439e28a873f5050e7ca821cf54e429f294853e5190a7aa1215794c42aea98859e5310a7aa6216754c428ea98853e5210b5ca4214f944429ea80853e54cca7aa9996750f32bb28e657551cca7ea9194f152329faa2653c544cb3a86994f950329eaa0653d539067ca520cf946419ea84835e53106baa620e794c419ea98839d531063aa620cf948419f28883b6511067aa020cf953319eaa6639d43cc6dca598db54b319faa4633c548c67ea898cf15131cea1a633e540c67aa818cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cfd51219e2a2433f5408678a810f948421af29e815d53d033ca7a04f54f40cea9e811d53d027ca5a04f947409eaa4813f5350278a4a04f14540dda82813e541027ca9984f553309f2a4613d548c33a87184f951309eaa2613e540c27aa8186750c30b7290616d520c2eca2185d544309faa6413c54c827ca9104f552209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x90000001c98082a000000600384bb2280022000200080c0c0005807800144a800000019000002c00001a0000400410020048758e5190a1f6354242c550d51cca3661d523287195434ca8c6250d328758e529061f6354241c350d52cc62e62d523187195434c6946150d318758c544861d63150218e580540861d63149408758c515021d63951308b189544c2346155130c350d520c31543544308758c54c821d63952208758c54c421d6395210
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (864+((h/16+packedAt s0K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s0K4 (3970+((h/44+packedAt s0K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s0K3 (1036+((h/8+packedAt s0K3 (988+(h % 8)*6) 6) % 58)*6) 6
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff0ffffffff81ffff07ff07fffffe78f1ff
  | 2 => 0xf07fff03f07e1ffe1e0ff87ff878383fa73e93
  | 3 => 0xff83fffc007fe1ffe00fff87ff803fc1c7cf1c
  | 4 => 0x3ffffff8001fffff00007ffffc001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x800010208010000044120088008a0a10085025
  | 2 => 0x2519221924a430960a854853485090aca32692
  | 3 => 0x432a44486949032aa109950595012585458b18
  | 4 => 0x6a5388924c0d55cd33a0c446e6658109f00dc0
  | 5 => 0x8c630ee38e7199f1ddcee660c4460631fef000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0fcccfcc0fcccccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36340
namespace PEqualNP.Outside.L_meta_36340
open PEqualNP.Outside.L_meta_36340.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x201404000c341c2003bf43de43bd43dd439d43ee21ec21ef20ed20
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe2000064ac8068eaa4878f5250f18a4a1e350e21c6a18438d43c831a86905914520
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x801a0a19875250e0f6550e218319543483054314520
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
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
  | 4 => packedAt s1K4 (156+((h/3+packedAt s1K4 (144+(h % 3)*4) 4) % 14)*5) 5
  | 3 => packedAt s1K3 (224+((h/2+packedAt s1K3 (216+(h % 2)*4) 4) % 11)*4) 4
  | 2 => packedAt s1K2 (155+((h/1+packedAt s1K2 (152+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1fffff83ffffff81fffe0ffff83ffffe71f1ff
  | 2 => 0xe0fc1ffc1f83fffe1c1ff0f07fc3c1ffae4e4f
  | 3 => 0xff001fffe003e1ffe01fff007ffc01c1cf8f8c
  | 4 => 0x1ffffffc01ffffe000007ffffe01f00ff0
  | 5 => 0xffffe000000001ffffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x40080088010000002022011108044444009095
  | 2 => 0x8a312910ca2550960d0c90a2324288b8a6464a
  | 3 => 0x465a5229474a832ae2172a055ca8150d4b8b8c
  | 4 => 0x94a39c429460d5cd5741888867333811f00d60
  | 5 => 0x18c31873187319f19b99ccce06222021fd6000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36340
namespace PEqualNP.Outside.L_meta_36340
open PEqualNP.Outside.L_meta_36340.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x49c805000b414061046310dbf43bd43ee32ed32bf41bd41ee21ec21be40bc40ef20ed20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xd841009400058d434ca3aa7a0d354c21b4a80431d531026aa2205354f20
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (208+((h/4+packedAt s2K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s2K3 (197+((h/2+packedAt s2K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf87fffc1fe1fe1e1f87f0fffc3f87f0749f673
  | 1 => 0xff8787fe3fe1fffe1f87f0e0fc3f87ffb6499f
  | 3 => 0xfff807ffc001fe3fe007ff00ffc007f8c78e1c
  | 4 => 0x7fffffe003ffff80000fffff800f80fe0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x9010044042002002009012240481112009231
  | 1 => 0x10200888100280040882104404120244124086
  | 3 => 0xa31355148d55506ae445aa0aea8134b2c58e18
  | 4 => 0x86546621291054b355508810b3256020e80d40
  | 5 => 0xc4664439b199993d9e66cc9c220640c4ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88eeeeeeaaeeeecc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36340
namespace PEqualNP.Outside.L_meta_36340
open PEqualNP.Outside.L_meta_36340.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1024475a90300180310a3a30bf43bd43bf42bd42df32ee32dd32ed32cd32bf41bd41be40bc40
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2800800cce00000111ab4bc27628008081a6a9c658f424cb1a849963d0d32c6a1a658e544cb1aa8994754f4196a96838d32d071a64a0e34ca408ea98812d521031a64204d54440
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x32020a1586544ca0d654cb418359532103053254440
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (224+((h/4+packedAt s3K4 (208+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s3K3 (457+((h/5+packedAt s3K3 (432+(h % 5)*5) 5) % 22)*5) 5
  | 2 => packedAt s3K2 (155+((h/1+packedAt s3K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fc7fff87f0ff0ff0f87e1ffe1fc3f0fa4f4cf
  | 1 => 0x87f870ff8ff0ff0ff1f87e1c3e1fc7f1db4b33
  | 2 => 0x7ff80fff000fff1fe007fe03fe007fe638c3c
  | 4 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x400008001001000000802400240100001045
  | 1 => 0x20820111040140102088220882090241094112
  | 2 => 0x55112aa222aaa88356445541354094ac628c28
  | 4 => 0x14354cc44a882aa59b5511023992b024740e80
  | 5 => 0x662668876cccccc9ede67993910320c97fe000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeeeee8e8eeeeeaeaeeeee8e8eeeeeaeaeeeee8e8eeeeeaeaeeeee8e8eeeeeaeaeeeee8e8eeeeeaeaeeeee8e8eeeeeaeaeeeee8e8eeeeeaeaeeeee8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36340
namespace PEqualNP.Outside.L_meta_36340
open PEqualNP.Outside.L_meta_36340.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x920000486005ca2b007c0000000da7503401d043802400405803894000101488c2aa401608a800034981980e8002246645213c000131e2401010042c1002040003ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4617c548c2faa7185754e30bf294617d528c2fca3185f54630dfa0c61bd418c2fca11877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261df434c3bc86987750d30ee21a617f524c2f8a49877cc930ef19261dd324c3b864985fd4530be28a61bf414c37a829877cc530ef18a61dd314c3b862987ecc130ef18261df544c33ea8987795130eeaa261dc544c338a89877d4930ef29261dd524c3b8a49877d0930ef21261dd424c3b8849877d4530ef28a61dd514c3b8a29877d0530cfa0a61de414c3ba82986750530ee20a61df214c3bc42987748530ee10a61df504c3b6a09877d0130ef20261dd404c3b880985fd5030bf2a0617d540c2f8a8185f94c30af298617e520c2faa4185f94430bea8861bf410c37a82185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720dfa0e41bd41c83de43907b48720ef98641dd30c82fea9105f95220beaa4417c54882fea7105f94e20ef29c415e53882faa7107754e20aea9c417c53882faa5105f94620bea8c41bf418837a83105f94220ef98441dd30883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42482fea2905f14520dfa0a41bd41483de42907b48520ef98241dd30483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2106fd0420dea08417e50083be6010774c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21f641c437a83887d50710daa0e21f621c43ea438877cc310ee986217f54842fca9085f55210be2a4217f53842fca7087794e10af29c217d53843baa7085754e10be29c217f52842fca5085f54a10be294217d518437e83086f50610bf28421df30843f46108774c210fc98421d930843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c524437e82887d90510dea0a21f5414436a82887d88510fa90a21df30443f46088774c110fc98221d930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2086fd0410dea08217e50043be6008774c010fb88021fa10043ea20087e44010
  | 1 => 0xe541067ca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef99663dd32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f78ca31ee194637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7be6498f74c931dfa0a63bd414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc6590fb4cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21bea94437e518877e8310ef50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f719243ed324877e8290ef50521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53903bca7205794e40bea9c81dd53902baa7206f90e40de21c817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2206fd0440dea08817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3be87987790f30eea1e61dc43cc2fca5985f54b30ef99661de32cc3ba6598770cb30bf28e617d51cc37e83986f50730ef98e61de31cc3ba6398770c730efaa661de54cc3baa9987715330efa9661de52cc3baa5987714b30efa1661de42cc3ba85987710b30efa8e61de51cc3baa3987714730efa0e619f41cc3bc83987750730cea0e61dc41cc3be43987788730ee90e61dc21cc3be81987790330eea0661dc40cc2fea9185f95230beaa
  | 2 => 0x80800a0080080000000401006002000030020020000400500601c0680b00a00403005000020000060100000b003008008000010060240000c004010020040060000000500401401806000000000000000140280000201c030030000001080901a06808002002028048010020140c80200000c000000040000f01b0040240900201000000006004014010000000000000301e028000120020040000500006c02000006004028010020040201300a0000200b000008040070000000000000601c0100000a01c04800008000040030080000a8000040040000500600c07802000008008000160040000101600001800002034020000080100100400000c000020000000000100200400804000004040030000140000001001c0480002a0280000300a000008000000040381400600000000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332efa1e65dc43ccafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef94341dea8683bc50d06faa920cf55241bf29c837d53906fca520df54a41bf28c83bf41907ee8320df94241bea84837f53507bea6a0d7d4d41be29a83dc53506b8a6a0efd0d41df21a83bd435077886a0dfd4941be29283bf425077c84a0ef50941de21283f7415077c82a0dfd4141be28283bf535073ea6a0ef94d41dea9a83bc5350738a6a0efd4941df29283bd5250778a4a0efcc941df19283bd325077864a0efd4541dba8a83bf505077ca0a0ef54141de282837
  | 3 => 0x660001680000d80000031a0e864099310cc497aa20005f14f8000f6000f1a13524bbd008310009586ca405324204fb05000000ed00018c1c0ac16c564cac572e364c614b19cd1103a8e8ac658ac50001ed1722d00005552823cc0a1448c3d57880000000156800000000000485a2b91851db5f4000002bd00000198000000b20831772d4c8400000230000a39ff0009617a0f13803788625f43a5e0c52a464045ce0817060b5c2f0021b8860a680017072c7980046eca000000304814278292baa04d210b2261840001b256000000000000016dad5000000000db0c89d0aca360006c4690000002180000025c6c8000002680010895559a59c592700de3509e9b62e80003c0002ac0000026a000c88600000009714828b0a4354f702d1846e0001204fe9c4e4000294051838ca19a7240012940692800230220361622ce086000000003a699000000000aac00000000924001d75549840015008800194ac21980784599d5767851fadf000ab93e2fc2ea505282a15725151a8380ae2449d226276a60d580332433c250262460000000000000000000000ac505a17000ac00822c1400000005b248a8c621e71d00ac3913049e9818d8001380000007c3420000024300000000000000150411e21b40000030304a7bd0800018ebb84d07310a790002d600050c00148000164950006007d97f253202064150f72644b00018651e001430004dc56c00170166464000eb0923f93c86c6227e89b80000096d0f0000006b40016145a0012a000000000001f8000b947a19000082800000000000ea80003a0000010a0002b454063496935020e914e1e86b0e0400b790e17e2886fcae0000006951d10f000000000b7000c8cefaba0380000000e1ba7580032d000b3c298900000005e8bc3c0114288000cc000da8005226c07b02e000000ec80048e8f10c8006580e4e51225f24a134a85000000000002fe97564ab80002bc4b000000278039b91da7155614966412d1580041c188001c6000601172e21dc000b280035457c5d93c000bac102413780007323900000121310200a540000000054c7d8004500000000050e0003b81f1920005822f000578a900000089c54800626000819a20004949f000000b8041999000c545187f00014000000000568a780013008d3280000065c5fa89030cb8001ce0bec7c000000004343b04e1021096c316242000000060440000026b0001a800000204b050aa0960c2b115079000ad04d8a43ca000c3a330009e9662735ba0006ba3b5b8c24fb8c32de7ecab800434c31462200ce000c498f082c200229c2dca98c180000000a01c00808000014030000080040080000a028018190080080000103601c02000006000000050000040080c0200000180003a000058000000000381600c000028010000000
  | 4 => 0x88973238208af80000001296800000000000002ea0000002300002a000002633f803400000000820000005c200049b250ba00000333154ca92889446421133000000c050331a326ba54d1dd236508000921a21ad8e19b000000000fd13a9d54680063a7980022163c2851480001e1709aa84000b2d7e9110000000026d3e0000000004247a80025e11c6d0000a50000000013133c0001e1c74180d4d62450ca1681217340400150000010988400000000000022300038ce22ed000000000000008f4001bd00037c001361f89116a1f43f2598b02f55b25e52a8e40006694f08a0006f8931c33d8a755f9d45eca6c5d13f35c9e01b83b0ea6bc3f2b33522ac05800000000000ce000000000003ea000000001ce000262b5000000000000c02d469abc224000e13183745f4a882c18ab48002963766980010e0b02f9810003467708b16b05e1a41a1f14d83c985aa932232c530e1506b297600047c73d3401a2f6c340003e0000840000040e000198a23a0a3979a8000042549800000c3d5381211ac64ff20f0229484b8001c4478609a02706cc00000000b0d7c0000002d89ca763d200163a240009dc003120007490f8562665d9870001de00178016648000341464e4000ce0f020aa200021b498474001fd0000000006e2963e1128001f49bd4b9070000001fb04328000000000009ec0000033e0014500055ea08b20003e46584491f00211c0007d398b4cd40b1000000db9543e60004618c0000001387449c778002b631c1b4000005e4500b8ab75fe5c8b10ff42ccbc140e512a04d540003160c8002e7228b693f20d3b0000000000000f40000064e0007616932a920001150009f4a711a000c5cf4000080014002f70005b42691c2f495c00087000000000005f6b400000a000000001844b20006823454a0013394c25a69c0007124e3e4002c0000031742313d600000
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x7300825f654c020c7951300831d544c020d59453008355514c020cb553200836551c8020dc546200826f6548020cb55120083655148020f24c1200827b6548020dc5452008336619531097d8d54c425c6355310c7d8d54c431c63553108f99353c423d64d4f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b1097d8d52c425c6354b108f99052c423d6414b109798c52c425d6314b10cd95141c42b76550710cdd9541c43976350710e518d41c42b56488710c795330c431d54cc310e550730c431e544c310c755130c4395414c3109798f548425d63d52109798c548425d63152109b988548426d6215210d6982538423f6454e108f191538431f6454e10c7191538425e63d4a109758f528423f6454a108f191528423e6414a108f590528425e6314a109758c528431e53d0610c754f418431e5350610c754d418435a534c210b6d95308435b654c210e6d913084398644c210e6d053084399414c210b658e208425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423f64549108f191524425f63549109718d524423e64149108f590524425e63149109758c52442b564905109d19541443376550510cd19541443976350510e518d41443b36050510ec18141442b564885109d195214439541cc110b658e30443b1418c110e55053044278654c110ec505304435b654c110d6195304439b644c110e619130443d3614c110f4185304439b414c110f49053044399414c110f45053044391414c110f488530443d1214c110b658e20443b141881109e19520443b14148110f848520443b141c4110f44c2104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530425f6054c1097581530423e6414c108f590530425e6314c109b988530426d6214c109e980530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520427661148109e980520423e64944108f592510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410433651504109798e500425d639401097597300431e54cc010c7553300434e52cc010d354b300425f654c010c7951300431d544c010d3949300434d524c010d6941300433554c4010d954b10042796584010d654e100436952840109dd9510043355444010d9549100427b6544010d654d10043695244010
  | 1 => 0xc29d640c530c7150314c2ce620c530b3588314c2da600c530a7587544c29e6495130b6582544c2db6055130a7994544c31e6515130a7584544c31c54d4930a7992524c29d6494930b6582524c29f6454930a7191524c31c5454930b5d85524c2d46154930b6d81524c34d521493097996424c25d6590930b6d81424c2d86050930b6980424c2d96010930a7992514c29d6494530c7152514c2d96094530a7d91514c29c6454530b3d89514c2cc6254530b6d81514c29e6414530a7590514c31c5414530b3988514c2cd6214530a7997414c29c65d0530a7592414c2da6090530b6582414c25f655053097195414c31f6550530a7995414c29c6550530c7195414c21c6550530e5d85414c29e6410530b6980414c2d96010530a7992214c29d6488530b6982214c2d9608853097d95214c25c654853097994214c25d6508530a7990214c29d6408530b6980214c2d96008530c7d53504c31c54d4130e6d53504c39854d4130b6587504c39b41d4130e6507504c25e659013097994404c2ce6210130b3588404c2d66110130b5584404c39940101309798f540c25e63150309b988540c26d62150309d984540c27561150308f992510c23d6494430c794f410c31e5350430cd945410c335515043097d95300c27b654c030d694d300c25e63d53209758f54c823e64d4f208f59353c823e64947208f59251c825f63547209718d51c825e63d52209758f548825e63152209758c548827661152209d584548823f6454e208f191538831f6454e20c7191538823e64946208f592518831e53d0620c754f418831e5350620c754d41883365150620cd545418825e63d51209758f544831e63d5120c758f544823d61d51208f992544823e6515120cb588544823d61151208f992534823d6494d208fd91534823c6454d209dd8553482746154d20cb152424826c6550920ba181424823e64145208f590514825e63145209758c514823e65d05208f197414823e65505208f195414831f54cc120c7153304831f544c120c7151304825e63d50209758f540827661d50209d587540823d65950208f586540823f61550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c208f992510823d6494420cd95251083355494420d594e51083555394420cd99251083356494420cd95151083355454420d594d51083555354420cd991510833564544208fd97410823d65d0420c794f410831d53d0420cd947410833551d04208fd95410823d6550420c794d410831d5350420cd945410833551504209798e500825d639402097597300831e54cc020c7553300835651cc020d554
  | 2 => 0x53505218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530865d6094c21c7951530871d5454c2197d81530863e6414c218f590530865e6314c219b988530867a6014c219e580530863e64944218f592510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410874d53c84219bd95210874d5348421e9505210867765484219798e500865d6394021ce95250087395494021d694e50087595394021d698e50087596394021ced0650087394194021ce95150087395454021d694d50087595354021d698d50087596354021ced0550087394154021dac8550087722154021da485500877121540219798e52d025d6394b4097d8d51d025c6354740cd54741d031d5310e40a798e429031e53d0640c754f419029c6350640c794d419031d5350640cd945419033551506408f99742503375150540c754e43102b96010c40d394e521034d5394840d394d521034d5354840cb90d521032c43548408f596421029e6390840cb54a421032d5210840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cd99151103364354440cd10d51103364254440cd109511031e53d0440c754f411032e52d0440cb54b411033551d0440a718d411031e5350440c754d411032e5250440cb54941103365150440cb54b401033551d00408fd95401032d5250040cd545401027b65500409b98b54cc26d62d53308f99252cc23d6494b30a799232cc29d648cb30d354832cc23e64947308f59251cc29e648c730a759231cc29e640c730a759031cc2ce620c730b358831cc2ce62d5330b358b54cc2d960d5330b658054cc29e64d4b30a759352cc2d960d4b30a799252cc29d6494b30d354852cc2d96014b309799642cc25d6590b30b658351cc29e6494730a759251cc29e6414730a759051cc2ce6214730b358851cc2d9601473097d9541cc25c6550730c7d9541cc31c6550730e5d8541cc29e6488730a759221cc25f65487309719521cc25e65087309759421cc29e6408730a759021cc2da6008730b658021cc2ce6210330b358840cc2d66110330b558440cc26e62152309b588548c27661152309d584548c23e64946308f592518c3365150630cd545418c31d63d51308f587544c23e64951308f994544c31d63151308f584544c25e65d0d30c7152434c25c6550d30c7d50434c31c54cc930a7992324c29d648c930c7151324c34c524c9308f990514c23d64145309b988514c26d62145308f997414c23c65d05308f995414c23c6550530a7992314c29d648c530c7152314c2da608c530a7990314
  | 3 => 0x13297997434cace62d0d32a7992324ca3e64145328f590514ca7a60145329e580514ca5e63d50329d984540ca7561150329e980540ca7960150328f992520ca3d649483297d95320ca6f654c8328f992510ca3d64944328fd91500ca3c64540329798e52d065d6394b41a798e42d069d6390b41cb54842d065e63943419758e50d06ae62d4f41ab58b53d06b561d4f41ad58453d069e63d4b41a758f52d06b561d4b41a798e52d069d6394b41cb54852d06b56114b418f99632d063d658cb41a798e50d069d6394341a798c50d069d6314341ab98850d06ad62143419798e509065d639424197583535065d6014d41c714f435071f5310d41c714f425069e6390941a758e425071c5350941cb149425065e63141419758c505066e62141419b588505069d60d4d41a798e53506b56194d41add85535069e6514d41c7994535069d6014d41c714f525069e6394941a758e52506b56194941a7d8d525069c6354941c714d52506b76154941aed8152506b86054941cb548525063e658c9418f59632506b7614c941ad18532506b6610c941ad584325071f53d4541c714f515079753d4541e514f51506b560d4541a798e505069d6394141c714e505069f6354141a718d50506af6254141ab189505069e6314141a758c505071c5314141ab98850506ad62141418fd9541106776550441cd951411065e63940419758e501063e6494b318f59252cc63f64543318f19150cc71f6355231c7550438c69e648ca319b98a544c66d629513197d8d544c65e65cc9319b98b540c66d62d50319e983540c67960d50318f596540c71c63550318f990540c66e62150319b588540c67a60150319e580540c71d54d0c3197594430c6d56110c31cb952520c72d5494831cb951520c72d5454831d3d0d520c74c435483197596320c69e648c831d354a320c74d520c8318f992510c63d64944318f597410c72e52d0431cb54b410c63f6550431cb949410c72d5250431d354b310c65f654c431d3549310c795414c4319dd95310c73a5494031ce552500c76a5294031da54a500c73b4194031ce506500c73a5454031ce551500c76a5254031da549500c75a6354031d6d0d500c7584354031d68c9500c7583254031ced05500c7394154031d6cc5500c75931540319798f54c865d63d53218f99353c863d64d4f219798e50c865d63943218fd9150c863c645432197d8d548865c6355221c7d8d548871c63552218f993538863d64d4e218f990538863d6414e219e98053886796014e219798e508865d63942219798e544865d639512197d8d544865c63551219ed81544867860551218f993534863d64d4d21c7993534871d64d4d2197583534865e6394d2197994534874d6214d2197580534874c538c9219b19532486e4614c921c7d4f414871c53d0521c7d4d414871c
  | 4 => 0xce60006f879ceb04e000000003370003c0002de000c7800000000c90399ca1d007cee372000ba80027636e9dc000000000000000029000000314000000ac00013a778f61ff6f4a3db100015e5fc0001d42a018051393e8699361603d03783e1941d6000000006148100000000067c002a56323dcd1137000209242d158e1e40008f01ebd92e8000880000026a510001570b25f8b28a200000050800000544000de80000000165aaf00035169800000034790000008301880065624134b76000259b70362805050a28400000171b380000017737115037000205000ab03ab7d55a000002db066001439572a2b9c3b9c65a86a000039452001a131b3ba8bc4d04a1f6154c6a516960007d02b4c0618100003121a15d1326901ed9b21b0004ad5db173700018c1004f20000000038e8f11da206de968d5a92592000000000003b0000c36ae0f92a01833a6d80000060458cc40003de4cc5f108642b744931f68a6380816f0cc7d8000000002980027a0000017a0cb000000da8e1000000002e5420000122bd3ea52d841694de000b69c011a2fd0118c2bed243f9d059c000a78004e047c0033f2e8a8c0a340000000000003caa28002246a026c0012c0000011b0006460000000000065c0036b252024b5800000000008018030060000000000c00c008060040100000b0000000100000600000011010010008000200040500100202c010030480080000500801400006014000020020160000000100000c0280d01000400000000004008000000000001e00000800800002004010020000000200000006c010060020040180000001c000030000040002000400c00804000018038000100080080200c0100000100a010020010020100200000000004001004004010030060000000100400003800000000000010160000180300202c000010000000001200c00400001000000000000000040000001005c010030000000080d0200040000300400000000002008010140040340001901600001000014024020000000040400000000002005000000008000040000000f00a004040000020080680e006000000020020040200003e0240000100200c0000200600c0600000000004000000000000060100040700000000c00000006020010040000040000100000400802000000000020080100000000801c0100100e01c018010040000380000000c00002024008000008fd954310e5f6550c439798e50d0a5d6394342975825390a5f6054e42c794f4290a5e63942429758e5090aae6290d42a798e4250a5e63141429758c5050a7661141429d5845050a3f65508429bd954210a5f63544429718d5110a5e63940429758e5010a7a60d53329e58354cca3e64947328f59251cca3d61952328fd85548cb1e54cca328f992518ca3d64946329d986544ca756195
  | 5 => 0xde00d2272a600000000000a2c0021f0006c54280000000000138376000920000000000600000005c000000000000002d52e00024172000000f71100004296c0001ca000ad0000001c0d7800586dd02036d29a7804c85f1c68c58eab905ebacbf1520ae9d4c2ae208a215430da6b2d8012a0f660d519294c6a6b000006e000000000005f45c57ba2c58200110ac80005dd6f9c40007dc002802b2c48f334a0002e93e00037825002000000000000006228f4000000009d000000000b687217a6bc164968005542ac0003867c54024b6400034d46000292000e48000007a43b0fd1620018697c18c940002e916e924a381b00002ceaa086f2001ba8006080015b9e4000bcc000004dc000000000000000023844a001520c16828e4918001780009d9a30001a8449750a48a800000314000928000003d16b8004344252630b000000dd2cf53400122800000000000632d40010301119047848a32000000002892d83485e80000077d8e165000230cd0cf42ca648a1e2058210ff000098000002f12d0001318000de000838000000013f0000100003a0000f4ad0002f25fe998003090007cd29a2d6d41e08900030690166155000000d093d560000859e1000118e5b561dccb8000000004d40000000031daa8d11768d183b160009e00005300000000000000000ad8160000008122200073465000488c54360d861e39d5f0000000019486215c000000000000019d0000008fc000001d2cb4002420a00000013f006000000000000014f0000000006002e25c000b7072000000001ac52cca0150000007e89f007168000002180006b9993522405140010460c000000002060007b0006ce24c0030c000a51320b5000359740a244cac8bea412c4000001d90000003f15c00000000000348cbcd533b1ae12c00000640705359135269586220e06875ced9164ca61000000000330001a50000010eb1000000000373000280001910002a87e2a1000b84003666ba0014e0002bc8451825900400400098102658c92460000007f9b9304000003432020011411a2f65e40027f00081c0009700000000283000bb52791d000b8000000000bd4001b20000008cb690000007f1561580000cabc0000000003700074c001ce0000000013a000b18000005ac6f8000000000000019c368c9c0011b59a000000000000012382304c0004f0006b6a9c001430000012ab4f076000908000007f0000001ea38000000000afce92620007f400087148314000004e40a40019500000000000000824518001661589407d26c0000010c504000e294e1c40f4bc1bf09a20cb20003a85d8e8800494a610c800000455469ed698b98001900429f599a3a4b85190f0df0006c16e26d5360019a96700000038800000001ac0000001940033121e0000012a57048856afd0b42702d8ef000d7
  | 6 => 0x602001090005f01086ca5e024c9969000160b640033d16c0019c800000000000001d4b90e18cd000000d49f10003e0000300c25847ca8e000a4444118678d8cb31eb0003380012f4666805093122e191540006a2000f80f10000014ea4e000340001e358400000000000bec28905000150cd8c9184d840022b000001051cf4a420182a3e6d8039a389f562679622670860005480056a90c141fb11461c000003660019600069a2e0002ec00000139a6112a00125b7700000088800000000002fe000001598005aa000000000000000027b00062c0000000022c6e8f355200155b5c000000001270000c98702220c9c4000006341b44703f3847619506b0005cc001995de4981e05c53e000001702a8001818a71b685da20d56000000024d0000000019800082c001f846a2941d1da6f60000025f09e000002a056c000000000000000018f41a4d03480000000000257000871911ad0bc88c00015000438138000004342ea68000181018000000010981e000000000ed3f26051ba2e00000023800000070000000ce00168000000000003136d069d00b5a68c7a800000000000000003900014aac54b6471b2800000574000b969c04c43193000600000e60000019a0056e0bc00014a000a4020a582600d500281278be42c1f254c
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xe8100000094800010038d96150c211208800c80209d1c8b89990002830a81a19c0f801d80000a0717859b0019849285139e840010971698189f800e091a0000200d14069f020b11910f1e06159b9a9307880c8104106860c00001062c39a00051891c046038b2e031aa22143571191500cb0c298c0a92834a1c15214941962e030a64a0d197014c505070629ac428283515c4435483192ae33246418e0e6454a320c782a928298863545c44354031a34e9192a018f11414c5500c670b80c299243079db5350521e0aa6a0a4210f21414855008694b8086a9081265c26390840c1cc6a9484205317010d511028b39c84a8881265c06350440c18c6a92822041d76150314c28ab88a818a6183151620c530c28a830aa49854471548524c268b88c0a1261455c45414530c18a8b10a29841e75995414c20e3aac910a61a25894010130d22c2a00809841c7654d4188270b88c0a1241079db544c120e12a89824010741514c1200820e3b2a898621251d9414c310838eca9a830849876505308430a328c6a0a21645c06350510b22e630282886906318141442d0b90c0a0a21251d9414c110960eca0a60886186519130442c8b88c898221645d0614c110d20c830a60885c17218530442c8ba48298221261d9414c1109a0eca0a60886937650530442c93b28298221641d9414c110d20eca0a60884907650530442c8ba44298221a458d4188110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x50004a180e4601c80a40d32cd28160a098014d6214141a0581991528c831911819d23254031a098098d5290840911809ce4254440a098018d5250440a0581151620c530a05811516214530c10655c06350510c80635c86050510c10655c4644c110c80645c8614c110892869d9414c110890865d2214c1108908758d4188110
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
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (788+((h/14+packedAt s4K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s4K5 (25143+((h/273+packedAt s4K5 (22140+(h % 273)*11) 11) % 1191)*11) 11
  | 4 => packedAt s4K4 (37250+((h/298+packedAt s4K4 (33972+(h % 298)*11) 11) % 1427)*11) 11
  | 3 => packedAt s4K3 (3486+((h/22+packedAt s4K3 (3332+(h % 22)*7) 7) % 82)*8) 8
  | 2 => packedAt s4K2 (925+((h/5+packedAt s4K2 (900+(h % 5)*5) 5) % 19)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x87f8ffff07f1f1f878e3e3ffe3f070fe0cf70f
  | 1 => 0xf87f078ff8fffe3f80fc7c707c7fff0e3349f3
  | 2 => 0x7ff80fff01ffc7ff007f807f807ff1c38e3c
  | 3 => 0xff80000ffffe0007ffff80007fff8001fc0fc0
  | 5 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x90081101100222000820809120911024041305
  | 1 => 0x2104012204080410044242204242408114052
  | 2 => 0x652222244225400ab100490449024ac0c28c28
  | 3 => 0x3106b54894a06494daa90009724b02656c0f80
  | 5 => 0x4644c600e6c9892764d2724e000c0c89bbe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaece8ece8feeafeeaece8ece8feeafeeaece8ece8feeafeeaece8ece8feeafeeaece8ece8feeafeeaece8ece8feeafeeaece8ece8feeafeeaece8ece8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36340
namespace PEqualNP.Outside.L_meta_36340
open PEqualNP.Outside.L_meta_36340.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x6891c0a054002c6d3a04c50007169001e1c8c00a420840300014893210f802a006800000b802274818444c00f0c000251804008c10008030a1c3085ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398778c730ee98e61dc31cc3bea9987795330eeaa661dc54cc3bea5987794b30eea9661dc52cc3be85987790b30eea1661dc42cc3bea3987794730eea8e61dc51cc3be83987790730eea0e61dc41cc3be43987788730ee90e61dc21cc3be81987790330eea0661dc40cc2fea9185f95230beaa4617c548c2faa7185754e30bf294617d528c2fca3185f54630bf28461df308c3f661185fd5130bf2a2617d544c2f8a89877d0d30ef21a61dd434c3b886985fd4930be29261df324c3bc6498774c930ee192617f514c2f8a29877cc530ef18a61dd314c3b862987ecc130ef18261df544c3bca8987755130ee2a261df524c3bca4987754930ee29261df424c3bc84987750930ee21261df514c3bca2987754530ee28a61df414c3bc82987750530ee20a61df214c3bc42987748530ee10a61df504c3b6a09877d0130ef20261dd404c3b880985fd5030bf2a0617d540c2f8a8185f94c30af298617e520c2faa4185f94430bea88617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83dc85907b50b20bf28e417d51c83de43907b48720ef98641dd30c82fea9105f95220beaa4417c54882fea7105f94e20ef29c415e53882faa7107754e20aea9c417c53882faa5105f94620bea8c417e50883be6110774c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920bfa8a417c51483de42907b48520ef98241dd30483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020ef98041dd30083de40107e88020f690041f920082fea9885f95310beaa6217c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c43ec83887d50710fb10e21f521c43be6188774c310bfaa4217e54842faa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f481087e50210ef98421fa30843ba61087e4c210ec98421fa20843f241087dc4210fd884217f54442fca8885f55110be2a2217f53442fca6885f54d10be29a217f52442fca4885f54910be29221f641443ea82887d88510fa90a21fa40443f2808877cc110fd18221dd30443f26088764c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043be6008774c010fb88021fa10043ea20087e44010
  | 1 => 0xc514cafea0995f14132bfaa0657e540cafaa8195f15032bf29865de430cbba86195f94832f721065ed420cbbe64197b8c832ee99065ed320cafca2195f54432bf280657d500cafca7a0df54f41dfa1e83bd43d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0f7d4d41afa9a837c53507b8a6a0d714d41dfa1a83bd43506fea4a0df14941dfa1283bd42507ee82a0ef90541bfa82837c50506fca820df94c41ef298835e53106faa620f754c41aea98837e52107dca420db94841bea9083ed52106daa420df94441dfa0883f6411077a8220fd50441bf28083fa50106f4a020df54041fca80837950106fea998df95331beaa6637c54cc7bc8798f750f31bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7bc8698f750d31bfa92637c524c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863df430c7b88618df94831f7290636e520c6faa418fb54831b6a9063de320c7b86418df94431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc8590fb50b21f719643ed32c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea94437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487dc8490fb50921f719243ed32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410df94421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53903bca7205794e40bea9c81dd53902baa7205f94a40bea94817e51902faa3205f94240dfa0481fb40902fea6a05f14d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa88817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3be87987790f30eea1e61dc43cc2fca5985f54b30ef99661de32cc3ba6598770cb30bf28
  | 2 => 0x6000180550000016807a0e038c028f40d6335619720d453d589dd08e830a580028a261679953e63c55a8000000010016c3a20008683b49c738d38b34d24b068a8d1d69153f06e2286f16b8003fa6252380014c65c5d1f8478330f410505e62c481630002f8980611f45a9530970da378a12200000d0c70a70008c4b002118c190c00e0346000d4ad115aaa8000bb5025691b1dc434a48ce000420b348c9a84383892f800526000b68b41d43dcc11292d62b0f619e0309c4f88003dc001590d70005115f2c94e4364f48f245ca9c730b111a8a8a8a9a1822040f0fb58e4d02c89f4f29f559aab514a0cad9201b01e0a0ad41143584f16e0725380a2521e0590590441848548e22b03a3b1571c836a758741fc56e5ec4b0d02a03d8169740020080c010000481c07000000020700015810008020103607008018080104a14896088080200802002000384183c00002008000500e0590805002068040380001800020140080225802018200002201800000020001003802068160004c008000082e020000000a0600002018030020380200800008080201805000088000100a010200102c0082a018720406e03804028000200a02802078000b81c0a86c0081800806018001283c02000008000201a000020102c0200001812008001c0240080e0e8063a83a0100c008000100a1203c0280601802018020180a010000280c178240000202806060140a80a12060030040180000008038640000c0000401800010200000e0000200004008060100201000000001102a2180a0c802030040280417802020160280a000100d00000816000117e52d0fdca5a1db94b43bea9687ed52d0edaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0bbca7a15794f42bea9e85dd53d0abaa7a16f90f42de21e857e51d0afaa3a15f94342bea86857d5490afca7217794e42af29c857d5390bbaa7215754e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85be4350b7886a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42bf29085bf4210bdc84216f50842f6a1085ad4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbbe87997710f32f721665ed42ccafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7197790e32eea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132efa1a65dc434cbde6499778c932bfa8a657
  | 3 => 0x542753702514c849404225580ae1f2230bb9754ce999140b605c000000992762481f8d455e969262d60244a80000c06e0a4941ad2e64004211d0004100b9ed180a751d00000862804277000694f10c9000a14e90b0000860eaadd20c818001a04228993f90a5105c00da3f3286607c1321d23bc082573ceaa4eda040a66146a90f16e0915d29f1fc284bc21b1e66ad2e912320068342a150e960158ab2d04e96200a40e4314f2d358219c000162aa1a400a62000001230002ec00097000366000ff9c73cc9a0de8005b81216da42104820b08da36296ce59af47a7143b91a000000efac605800080846000689218380803950e800000001209da00024426063000548000582f485c85abd27c0f8ab0bf3ca02cbf98c52e674000003a023cd9239598750000e13080007fad80cc4789c9c0000000a4800000001278bd5440f13d0740003900026e0000005a8000460001280010a9d873a16000a440000009c000000950003b4000c708a491058aa414134b88002f2a540000000078d0a20500010d1296641a6ed1b9aa000824a30b9342ae4d218631e9a82898327ab392a9e139459ccf85054a8391982a0be349478764a640c9f85710e27441807512734142800000015f9bf4e8000000004d80000010700000000157424374000f5000000ae15419c34c2592f126000f827c000000db9cc02a4ad2004234c5741919b1fa5210f0563020000014c000000001f50003148825e3320000028b3ec6214b0001527191107158a54c362bc000219258002786d0198001881d4fd8003d69282797e00064d220c82949400025604e560068000009441b2350000d4988c30007793d9ac11c000f51f400032851800196001569b9246149180001401947e1b63b0b21301d30000012a16f0f8070a38002806b8520b85b4a6c37ab44d61cc8111f4704380008843ea08fbab8000000002a80004dd0083d0f2a31179252bc0390ca2949a000000000fe0006f80000000008800082000e18804e67e89105d4dea3890862388000000224068b08418d4489942f000382534df05c5841816ca1324e1f95b0003927c8f20005280088b1cf3fc4544e1e04f0a108c24904cb48af80f5580e86da0f30eb011397d4c62691d9170e45652c89b14aa40f7a2d3840000c9d93248c96a82000002496a6446850c0000011675c18a9c2c42f07705a5bc150932bb26637165aa4374a816513800633c9aaa32228848d9360000000007b50c6c00024800c970c884a3f29b4b281f2d25f05107d47c9c130a230260014c113212658cd0af0b
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xf544825e63951209758e544823e6494d208f592534826c6550920cb15142482e860509208f990514823d64145209798c514825d63145209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510825e63940209758e500825d65cc020c7953300831d54cc020d5947300835551cc02097d95300831e544c020c75513008356514c020d5545300832d54c8020d9547200837151880209bd95200832d5448020d954520083c930480209ed952008371514802097d8d54c425c63553109798c54c425d63153109b98854c426d62153108f99053c423d6414f109b98853c426d6214f1097d8d52c425c6354b108f99052c423d6414b109798c52c425d6314b109798f548425d63d52109798c548425d63152109b988548426d6215210d6982538425e63d4a109758f528423e6414a108f590528425e6314a109758c52842d96390210d694d30842db654c210d6d9530842d9638821097d8d544425c63551109bd89544426c62551109798c544425d63151109b988544426d62151108fd91534423c6454d109bd89534426c6254d108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109d19541442746548510b658e40442786550110ec50540442d9638c1109e19530442f0614c110d6d953044358654c110f4d8530443d0614c110f490530443d1414c110f488530443d1214c110b658e20442786548110f848520443d130841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150109d984540427a60150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530425f6054c1097581530423e6414c108f590530425e6314c109b988530426d6214c109e980530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520427661148109e980520425e63940109758e500425d65cc010c7953300431d54cc010d394b300434d52cc01097d95300431e544c010c7551300434e524c010d3549300435a504c010cd553100436552c40109e59610043395484010d654e100436952840109dd9510043355444010d954910043d330440109ed9510043395444010d654d10043695244010
  | 1 => 0x873a5494021ce552500875a5394021d654e500875a6394021d658e500873a5454021ce551500875a5354021d654d500875a6354021d658d500876b2154021dc88550087692154021dc485500865e6394b409758e52d025f63547409718d51d025e63d49409758f525032c5250940ae181425025e63145409758c515026e62145409b588515034e5394840d354e521034e5354840d354d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d9549511032d52d0040cd547401037151900408fd95401032d5250040cd545401027b6550040dc545401026e62d53309b58b54cc26e62953309b58a54cc2ce62d0f30b358b43cc31d5410f308f99252cc23d6494b30a799232cc29d648cb30d354832cc29e640c730a759031cc2ce620c730b358831cc2ce62d5330b358b54cc2d960d5330b398a54cc2cd6295330c755054cc2d96015330a799352cc29d64d4b30b658352cc29e6494b30a759252cc34d5214b30b658052cc25e65d0b309759742cc25e6590b309759642cc38d4210b30b658351cc29e6414730a759051cc2ce6214730b358851cc2d9601473097d9541cc25c65507309799441cc25d6510730b398841cc2cd6210730b698041cc2d9601073097d9521cc25c65487309799421cc25d6508730a799021cc29d6408730b698021cc2d96008730b398840cc2cd6210330b598440cc2d561103309b988548c26d62152309d984548c27561152309b98a544c26d629513097997434c2ce62d0d30b358b434c25c6550d30c7151434c29e648c930a7592324c34c524c9308f990514c23d64145309b988514c26d6214530b6982314c29e640c530a7590314c2ce620c530b3588314c2da600c530b398a544c2cd6295130b6582544c2db6055130c7550544c29e6494930a7592524c2d96094930b6d81524c34d521493097997424c25d65d093097996424c25d6590930b6d81424c2d86050930e3508424c2da6010930b6580424c2d96094530a7d91514c29c6454530b3d89514c2cc6254530b6d81514c29e6414530a7590514c2ce6214530b3588514c2da6090530b6582414c25f655053097195414c25e651053097594414c2ce6210530b3588414c2da6010530b6580414c2da6088530b6582214c25f654853097195214c25e650853097594214c29e6408530a7590214c2da6008530b6580214c2d961d413097996404c25e6510130b3988404c2cd6210130b5984404c2d56110130e6500404c25e63d50309798c540c26e62150309b588540c27661150309d584540c25f654c0309ed95300c35a534c0309798f54c825d63d53209798e54c825d63953208f99353c823d64d4f20cb15142c825f63547209718d51c825e63d52209758f548825e63152209758c548827661152209d584548825e63d51209758
  | 2 => 0x60145329798f540ca7661150329d584540ca7a60150329e580540ca5d6590c3297d95430ca3e64948328f592520ca6d6590832cb151420cb8e4350832ab592320ca5f654c8329bd95320caad62d0f419798e52d065d6394b41a758f42d065e63943419758e50d065f6354a419718d529065e63942419758e509065d60d4d4197580535071c53d0d41ab58b435069d63d0941c714f425071c5350941cb149425065e63141419758c505066e62141419b588505065d6094c4197d81531074e5394841d354e521074e5354841d354d521071d53d0441cb54b411063f6550441c754d411072d52504419dd95411065e63940419758e501075a5394041d654e501076a5294041da54a501075a6394041d658e501075a5354041d654d501076a5254041da549501075a6354041d658d501073b4154041dc90550107394154041dc505501066e62953319b58a54cc63e6494b318f59252cc66e62152319b588548c67a60152319e580548c6ce62d0e31a7992328c66e62951319b58a544c65f635513197996434c65c6550d3197997324c66e62d50319b58b540c67a60d50319e583540c63d6595031c718d540c63e64150319798c540c66e62150319b588540c67a60150319e580540c65d65d0c31c7553430c6ce62d0c3197594430c71d5410c31cb952520c72d5494831cb951520c72d5454831d3d0d520c74c435483197596320c69e648c831c7552320c74d528c831c7550320c74d520c831c7553310c74d52cc43197d95310c71d544c431d3549310c677654c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c7695254031d698d500c75b4354031d610d500c75a3254031d60c9500c75b3154031d64c5500c65e63d53219758f54c865e63953219758e54c863e64d4f218f59353c86cd6390b21cb15142c86ad648cb219798e50c865d639432197d8d548865c63552219798c548865d63152219e980548867960152218f990538863d6414e219e98053886796014e219798e508865d63942219798e544865d639512197d8d544865c63551219ed815448678605512197583534865e6394d2197994534874d6214d219758053486cd6390921d314e424866c6550921cb151424874c5350921ab592324874c538c9219b195324863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f990540865e63150219758c540866e62150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530865d6094c21c7951530871d5454c2197d81530863e6414c218f590530865e6314c219b988530867a6014c219e580530872d54c8421d354f210866f6548421cb551210874d53484219dd95210865e63940219758e500
  | 3 => 0x40000000000000000012b8000000006d8003ee00137000000000000000003700000000000000000244000000ce41a000001740009bc0000000000000000000000cc005000a50000000000000017113477c0014300000000000000000001e055a00000000000000000000000000002912c00000000242000000000000000024338c00000000000000f60004f2000af80000000026800232000b429c0d200049000000000000000000013d06325c79c4d967000000e48d7000000000000000000014e00000000000438204460000001580000000000000000000000d7800000000000000000000000000000000138384168000bd37c000000954d2000ea8b93520003714b58634800000000000001d6000000000be0008440001e0000000000000000000000000798000004a4000aaa3a00000000000000000000e700000000000000000620000006d4b2800000000001a3000000002314ea0a0000004a29042480000000000000100000000200100000000000300600000000000000300000000100000000100200000100b00000400100100000000100100000000100100000000200000000000000000100200000100200000100000100000000000300000000000000000000000000100000000100100000200000000100100000000000d00200000000000100000000000000000000300500300000100000000000000000200400200000200100100100000000100000000100100000000000000700000400000000300100000200100000000000000400000100000100000200000000200100000000000400000000000000100000400000000000000000000100000000100000200000000100000000000100400100000100000200000100000000000000000000000000500100200000300100200000000100100000000a002000000001001000001000000002000000003000000000000001000001000000001000001000000000000ab58b4390ece62d0e43b398b4350e6e62145439b5885150e7a60145439e5805150ead62d0c438fd954310e5f6550c439758253d0a5f6054f42c754e43d0a5e63943429758e50d0a5d6094e42d31895390a5f6054e42c794f4290ace63d0a429798e5090a5d6394242ab98a4350ace63d0942a798e4250a5e63145429758c5150a7a60145429e5805150a5e63141429758c5050a7661141429d5845050aad64908428fd954210a6f6550842abd954210b2f6550842cb94d4210a5f63544429718d5110b2d42544429798e5010a5d6394042cb5095010a7a60d53329e58354ccace62d0f32b358e42ccb2e5450b32e310d42ccb1d6395232c7952438cb1e5450e32c7953328cb2d54cca329758e544ca6d629513297997434cace62d0d3297994434ca9e648c9328f990514ca3d64145329e980514ca79
  | 4 => 0x15a00000292000aec000000000000000040a001180000000010a80000000083a7b000000511b90000000023b00000025000000000000001c600000242000000000000000013580000000000000000000001b749e034000000000000019f4c680400000000000000b500053000000000000000000005dc098000003bc2f80000092000000000001488000007880027600000000000000000000000001c95780000000000000000000000002f652400000000000001600009380019c00000000000000001280002bc00000000000000fc000000800000003f4000000004880006a8000000000004f0000000000042e00115800434000000000000000000051e29c000000000000000001e000000000000000000025000000000000000001a458e564892340000000000018019800000000000c500000000157000000000000004c2548191e10000015a800000000000000000000026643c4cc8a0000000000000000000000183212000000001840000022a000000d90eb404001328000000000000044e000000000002bc7f80000083800000000000c10000000000000000000000000000000000004f800000000000000548000000000000000065d598000240cc7f17303247c9e8000fa000000003500c07c87c00000000000182000389c30007a4000000000503a2b80002d951800000ad0000220000000026a0008dc001ef4ce66cd594d00056800000000000829f2236704001f033ca382d888186000000000000000000000000000000170000002ba1c8000b1800000000000d800080c0010e0000013a0000007e40009c000000000002d2000a98000005f55808400000000000000000000000000012c000000915541b3000000000000000008309f000860e28100000000000032c73cb09b40001510f97f3ba070ad97e00000000017000044000000003a4000672140e0a3000000634002080fe0000000013a000000002b08a40000041e108c58000000000000015c620c9000000000001ce00000000000000000000000005414fa1d0000000000000000000000000000128000ae768d68002cc00000000000000000000009f842800000000000000009b54413052c00000000000000518001ba0000000010c760498000007a0000b018e000000000000000000009800040000000000e01780001dd362820004d4a880000000052015000000000000000000000000009800000000000000001c44b4000000003cc00000000000001b802c00140831000000448000000dceb8003a2afc0016b3ea000000f1000000000000000000000000000000000000000000000000000000024e00000000106000000000000000011505e00099000000000a08ba000084000000000000002400040d3424d00000002000000000000001d434400000000000000000
  | 5 => 0xf8000000000003a4000000003b840090000000000000000000000000050c0000000027234c7a800000000ca00000071c00000000000000000004c40010b00000c00000000000000000002280000000000000000000b000027f000ab12321956c00000000000000000c8000000e525419822d438000000000002e514000000000bc07400023000001050000005e8000005361600000000000000000000280000000000000000000011c000200001ecd080000000000000268000000002f8000000004c4000000000008940013700064c000000000000000050a120000000000281e800150458000001f61bcec800000a10ef0b2334000000000008f8c09452f200066800000a4c00000000000002a0000000000002ba1540000026c00000000000358560000000008680047a0000000000000000000000970000000000001d000562000b68a100000000000544000000000003f51e27d0000014680000081c000000000000025b000a0c0000047e000000000000000000045c000208a5246278000002dc14c3205000000000000000498000004468d40000013200000000000000000002560012f0000000000000000000000000000000000000008100000000000000043290000000000d6711058000000014c8001948812e8d425443c000000000002e08727e000d280000000000082398000000000005d40000000009c00000000000000000000000002d20847800000000260dda70000000000005720003c83914c00103000000000000000000000027731c000a50000004740021300091c002b20000000018f00000000000000000000000000000000000000000000000001609c80001940000000000000000000000de000000000000002dea7800000000af800000000aac0000000000000290000b140012f000a5c302a60000000d000000501160000c2031111133e80005e0de3f80000000000000000000000000e980000000000000000324000003f6000000003fe0002c80000000000000000000000000000000021234e000a78000000009f1ba218b10732562a8001130000000000000051200000000000000001114429307a000530000d60000002fc36000000000000cf0000005500000061800000000000000004120000011a00068800000000add258000000000000000000000000000000000e84642502280000000000000000000000000009cc000000006f400000000000000750da00076800000001120000000000000000000000000000968002a90000000005212e0008c00000094d3880000000000000000000f2800000000000000000000015700002c25800000000000001f87b400000000000002a11c2630000000000000000000000140000036000000000000013200000032c000002880000000
  | 6 => 0xc41f87702b000000ae000000000002a4000000000000007f800000000000001720000000000000000000000000000000003d60002200031237c8b9cb000000000000005581a0000003c0e683500061cc8000000000c21e400000000000000000001fd0a2000001f6000000f50015346b87d22f000000030003e2a540000000086c0000e0000000000000000000000000000ed800000420000000002c4632551ee000000004700000012c0000000000000000124800000000000004be8504728b248000000b4450000000000001746d000000000000731a001cca9b60000000000000000000000000000000000009e000236000000000000007b800000000964000001e4000000000000f0000000000005b800000000000000002ccc296c000000000004940000000006c8e400000000000000000580ec00000000980000000000005d96200000062800030000001470000015e0001d8a9400000000b0800000000000000000000000000000000004800554470000000003d80009134c674c00000ec0a8f9800420a30b80001c04949e07a07e0009da16000000000000001a00000000000047800000000000003c600000000000000000000000000400000000000000000000000000000003c22d2041a95e8002ec0000019100059048000220508d0000000000000d9000000000000002ac00000000000000000000000000000000000000466404000003a0a9c0016a00000000000000a74d8ac603e000ea0000006c000000000000000000004e8000000000000020c07c1180000000000000000000000270003541c000000252000728000009000000000000000002000234001bf00000000000000000cc8000009c800
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2648022a08ad3211e5b8380d8000000000000000070032e01a022a10906800c00614b00e83140040003040368739ecaa1085165c06354442c18c6a12a22152571151420ca94b80a8a10658314d62d0d41c1aa93168618c1f76552320c707322a519063529cb4354031a34e9192a018c4d7614e4248706b20a7192432c5c460509409a2e2302849868942580424c344b128020261a458540101309c2e23028490709544c120083a0a8a60900412c5d0614c1109c2e430a60885917418530442e0b90c298221341d9414c1109a0ec90a608855175cc11004388aa66088021d054b3044010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8909809cf6550842a098018d4254442
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 735
  | 4 => 712
  | 3 => 30
  | 2 => 2
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
  | 5 => packedAt s5K5 (22295+((h/245+packedAt s5K5 (19845+(h % 245)*10) 10) % 883)*11) 11
  | 4 => packedAt s5K4 (29900+((h/237+packedAt s5K4 (27056+(h % 237)*12) 12) % 2212)*11) 11
  | 3 => packedAt s5K3 (1530+((h/10+packedAt s5K3 (1470+(h % 10)*6) 6) % 48)*6) 6
  | 2 => packedAt s5K2 (122+((h/1+packedAt s5K2 (120+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xcf0fe3fc7f0fc78fc78c78fc7e3f0e3f0d370f
  | 1 => 0xff1fc3f8ff1fff1f80f8f1f87c7ffc312c9f3
  | 2 => 0xf001ffc00ffe07fe3ff00fe007f80ffce30e3c
  | 3 => 0xfffe00000ffff8003ffff00007fff000fc0fc0
  | 4 => 0xfffffffff00000003ffffffff8000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x6120208881200910008410241209220a041305
  | 1 => 0x2004000120000020000810800420400004052
  | 2 => 0x80cc8911244496005b100a41249049b0630c28
  | 3 => 0x24641baa48a98324adad20025724e09abc0f80
  | 4 => 0x889123000cd2449364a4c9360008120dba000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeeece8feeeece8feeeece8feeeece8feeeece8feeeece8feeeece8feeeece8feeeece8feeeece8feeeece8feeeece8feeeece8feeeece8feeeece8feeeece8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36340
namespace PEqualNP.Outside.L_meta_36340
open PEqualNP.Outside.L_meta_36340.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa1697818e0499880f8601089d96000b00180209801d0a9b801a9c140500948013841b0e9e8291a01e03068005801f000c1c83901312170920959f9a0b8d078f151907128010800d80000c800000111885060e08082020000a021040a00bc0081614480017fd50057f54017f95005fd54015f55005fc5401ffd4c07fe5301ff54c07fc53017fd0c05fe43017f50c05fc4301ffd4807fe5201ff54807fc52017fd0805fe42017f50805fc42007fcc801fe32007f4c801fc3201ffd44077f5101ff94407fd51005f54407fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc2101ffd4003fe5001ff54003fc50017fd0003fe40017f50003fc40007fcc001df3000ff8c001fd3000774c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2e2004df59710004facb88013fc65c40097e32e2004ffd9310025fec988013fe64c40057f3262004ff5931004dfac988013fc64c40097e3262009ffd531004efea988027fe54c4013feaa62009df5531004ff8a988013ff63c40097fb1e2004ff98f10045fcc788013fd63c40017eb1e2004ff18f10025f8c78802bff53c4015ff29e200aff54f10057f8a788027ff43c4013ff21e2009ff50f1004ff88788013ff62c40097fb162004ff98b1003dfcc588013fd62c40017eb162004ff18b10025f8c58802bff52c4015ff296200aff54b10057f8a588027ff42c4013ff2162009ff50b1004ff88588003ff32c4001ff1962000ff4cb10007f86588006fe61c4009ffa8e2004dfd4710027fca388013f651c4009fea8e2004df54710057eaa3880037551c4009fe28e2004ffd0710027fc8388013f641c4009fea0e2009fd50710027f88388013ff31c4009ff18e2004ff4c710027f86388013ff21c4009ff10e2004fd88710027fa4388003f521c4009fe10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007df30c4003ff1862001ff4c31000fba6188007fc30c4003ff9062001ff8831000ffa4188007fc20c4003ff0862001fd8431000ff42188007fc10c4003fa0862006ffd9510035feca8801bfe65440077f32a2006ff59510035faca8801bfc65440077e32a2005ffd911002dfec888017fe64440057f3222005ff5911002dfac888017fc64440057e3222005ffd511002efea888017fe544400bfeaa22005df5511002ff8a888003ff63440017fb1a2000ff98d10045fcc688003fd63440017eb1a2000ff18d10045f8c68801bff534400dff29a2006ff54d10037f8a688017ff434400bff21a2005ff50d1002ff88688003ff62440017fb122000ff9891003dfcc488003fd62440017eb122000ff1891003df8c48801bff524400dff2922006ff54910037f8a488017ff424400bff2122005ff5091002ff88488003ff3244001ff1922000ff4c910007f86488006ff614400dffa8a2006dfd4510027fca28801bf6514400dfea8a2000df54510037eaa288003755144009fe28a2005ffd0510027fc8288017f6414400bfea0a2005fd50510027f88288003ff3144009ff18a2000ff4c510027f86288003ff2144009ff10a2000fd88510007fa4288003f52144009fe10a2001bfd811000ffea088007fe5044003fea822001ff1411000ffe8088007fe4044003fd2022001ff5011002ff28088007fc4044003ff9822001f7cc11000ffc6088007fa3044003fe9822001f74c110007f26088003d93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044009fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7dc104c00fffb2e4007bfd972003ffccb9000efe65c800ffeb2e400ebf5972003ff8cb9001efc65c800fffb264007bfd932003ffcc99000afe64c800ffeb26400dbf5932003ff8c99001efc64c801bffaa6400ddfd532006ffca990037fd54c801bbeaa6400dff1532003ffec79001eff63c800fff31e4008bf98f2003ffac790002fd63c800ffe31e4007bf18f20077fea79003bfe53c801dfea9e400eff14f2006ffe8790037fe43c801bfea1e400dff10f2000dfcc59001fff52c800fff2964007fb94b2003ffaa59003bed52c800ffe2964007ffd0b2003ffc859001fee42c800ffea16400dfb50b2003ff8859001fff32c800fff1964007ff4cb2003ff8659001fff61c800fff30e4004bf9872003ffac390002fd61c800ffe30e400effd4720076fea39003bfe51c801dfea8e4000df54720077f8a390037ff41c801bff20e400dff5072006ff88390003ff31c8001ff18e4000ff4c720007f8639001fff21c800ff790e4007ff8872003ffa4390003ed21c800ffe10e4001bf5832000ffea190007fe50c8003fea864001ff1432000ffe8190007fe40c8003fea064001ff1032000ffe6190007df30c8003ff1864001ff4c32000fba6190007fc30c8003ff1064001fb8832000ff44190007fc20c8003f61064001ff8432000ff82190033ff65480197fb2a4000dfd9520004feca90033fe65480077f32a400cff59520065faca90033fc65480077e32a400cdf1952001cf8ca9002fff64480177fb22400bff99120015fcc89002ffd64480177eb22400bff19120015f8c89002fff5448017bfaa2400bff9512005ffaa89002f7d5448017fe2a24000ffd8d20005fec690003fe63480117f31a4000ff58d20005fac690003fc63480117e31a400cffd4d20067fca690033fd5348019fe29a400bffd0d2005ffc869002ffd4348017fe21a4001bfd8920067fea49001ffe5248019f7292400cff54920067daa49001ffc5248017ffa124007ff9092005fdc849002ffd4248017f6a124007ff10920007fe649001ffe3248001fe9924007ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290012fc6148019ffa8a400cdfd4520067fca290033fd5148001bea8a400cff1452005ffe829002ffe4148017fea0a400bff10520007fe6290003fe3148001fe98a4000ff0c52003ffe4290003ef2148001ff10a4000ff48520007da429001ffc21480037fb024001ffd412000ffca090007fd5048003fe2824001ffd012000ffc8090007fd4048003fe2024001ffcc12000fbe6090007fe3048003fe9824001f74c12000ff86090007ff204800ffd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffc2090007fa1048003fe0824004ffd9710025fecb88013fe65c40077f32e2004df9971001cfccb88013fd65c40157eb
  | 2 => 0x3008fbaa9980475d54cc023ee2a66008f7d8b30007bcc598003dd62cc011ee3166012f7d4b30097bca59804bdd52cc025ee2966011f7d0b3008fbc8598047dd42cc023ee2166008f7d8730007bcc398003dd61cc011ee30e6012f7d4730096bea39804bde51cc025eea8e6000d754730097b8a398047df41cc023ef20e6011f75073008fb88398003df21cc001ef10e6000f748730007b84398006dd60cc003efa866001f79433000fbaa198007dc50cc003efa066001f79033000fba8198007dc40cc003ef1066001f70833000fbc2198007dc10cc021ffb2a6010bfd9530006feca980027f654c021ff32a6003bf99530087faca98042fd654c021fe32a6003bf19530086f8ca9800e7c654c01fffb22600fbfd913007ffcc89800afe644c01ffeb22600fbf5913007ff8c89800afc644c01fffaa2600fdfd513007ffca89803ffd544c01fbeaa2600fff1513000dfec698043ff534c021efa9a6008ff94d30087bca698043fd534c021eea9a6008ff14d30087b8a69803fff434c01fefa1a6008ff90d3007fbc869803ffd434c01feea1a6008ff10d3007fb88698003ff624c0017fb126000ff98930007fac498003fc624c00f7e3126010ffd4930087fca498043fd524c021fe292600fffd093007ffc849803ffd424c01ffe2126008ffcc930007be6498003fe324c001ef1926000ff4c930007ba6498023fc324c001ee1926000ffd8530005fec298003fe614c001feb0a6000ff18530025f8c298043ff514c021bfa8a6010ff94530087faa2980037d514c021fe28a600fffd053007ffc829803ffd414c01ffe20a6008ffcc530007be6298003fe314c001ef18a6000ff4c530007ba6298023fc314c001ee18a6000ffc8530007fc4298003fd214c001fe10a6001bfd813000ffea098007fe504c003fea826001ff1413000ffe8098007fe404c003fea026001ff1013000ffe6098023fb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ff8813000ff84098007fe104c003fd0826001ff04130087beca980035f654c021ef32a6010f759530087b8ca980435c654c01fefb22600ff79913007fbac89803fdc644c01fefaa2600fd7d513007fbca89803fdd544c01faeaa2600ff715130007bec498003de624c001eeb126000f718930087bea498043de524c021eea926010f71493007fbe849803fde424c01feea12600ff710930007bec298003de614c001eeb0a6000f718530087bea2980435f514c021ef28a6010f754530006baa298043dc514c01fefa0a600ff79053007fba829803fdc414c001ef90a6000f788530007ba4298003dc214c003efb026001b7d8130007b6c098007df504c003ef2826001f75413000fb8a098007df404c003ef2026001f75013000fb88098007de204c003ee1026001f78413000fb4209800
  | 3 => 0xeb284215bf59421026faca108027d6508409fe3284204bf19421027fec810812ff6408409ff3204202bf990210277cc81080abe6408409feb204214bf590210277ac810802bd6408409fe3204204bf190210a7fea8108537f5408429ff2a04214ff550210a6faa810853fc5408409ffb184204bfd8c21027fcc610822fe6308409ef3184200b798c21027fac610802fd6308409eeb184200b758c21027f8c610812fc630842bffa984215ff94c210affaa610857fc5308429ffa184214ff90c210a7fa8610853fc430840f7f3104207ffd482103ffca41081ffd520840ffe2904207ffd082103ffc841081ffd420840ffe2104207ffcc82103ffc641081ffd320840ffe1904204bf98421027fea2108137f5108409ff2884204ff54421026faa210813fc5108409ffa084204ff90421027fa8210813fc4108409ff9884204ff8c421027fa6210813fc3108409ff9084204fbc8421027fc4210813f62108409fe9084204fb4842103fea4210813ff6008409ff3004201bf98021027f4c010806fa6008409feb004200bf58021027f2c010802f96008409fe3004201bf180210affea01084ffe500842bfea804213ff140210a7fe801084ffe4008429fea004213ff1002109ffc601084ffc300840fff1004207ff08021027fc2010813fc1008411ffb2e6008bfd9730047fccb9800efe65cc011feb2e6012bf59730047f8cb98022fc65cc011ffb266008bfd9330047fcc99800afe64cc011feb266011bf59330047f8c998022fc64cc023ffaa66011dfd533008ffca998047fd54cc023beaa66011ff1533000dfcc798023ff53cc025efa9e6008ff94f30047bca798023fd53cc025eea9e6008ff14f30047b8a798023ff43cc023efa1e6008ff90f30047bc8798023fd43cc023eea1e6008ff10f30047b88798023ff62cc011ff3166007bf98b30047fac598002fd62cc011fe3166012ffd4b30097fca59804bfd52cc025fe2966011ffd0b3008ffc8598047fd42cc023fe2166008ffccb30047be6598023fe32cc001ef1966008ff4cb30007ba6598023fc32cc011ee1966008ffd8730047fcc398012fe61cc011feb0e6000bf58730047f8c39804bff51cc025bfa8e6012ff94730097faa3980037d51cc025fe28e6011ffd073008ffc8398047fd41cc023fe20e6008ffcc730047be6398023fe31cc001ef18e6008ff4c730007ba6398023fc31cc011ee18e6000ffc8730007fc4398003fd21cc001fe10e6001bf5833000ffea198007fe50cc003fea866001ff1433000ffe8198007fe40cc003fea066001ff1033000ffc6198007de30cc003fd1866001ff0c33000fb86198007fe20cc003fe1066001ff8433000ff82198023df65cc025ef32e6012f759730047b8cb98023df64cc023ef3266011f759330047b8c998047df54cc023afaa66011f7953
  | 4 => 0x813fe31c8401fe98e4204ff0c72103ffec19081ffe60c84037f3064207ff58321005fac19081ffc60c84037e306421effd43210e7fca19087bfd50c8439fe286421dffd03210e7fc8190877fd40c8439fe206421cff8c3210e7f8619081ffe20c840ffe106421cff84321027f82190813ff65884097fb2c4204ff9962101dfccb108137e65884073f32c4204ff596210ddfacb108137d65884013eb2c4204ff19621025f8cb10813ff64884097fb244204ff99221015fcc910813fd64884357eb244204ff19221025f8c91086bff5488435bfaa4421aff952210d7faa91086b7d5488435fe2a44204ffd8e21025fec710813fe63884117f31c4204ff58e21005fac710813fc63884097e31c421bffd4e210dffca71086ffd5388437fe29c421affd0e210d7fc871086bfd4388435fe21c4217bf58a210dffea51081ffe5288437fea944207ff14a210d7fe851081ffe4288435fea144207ff10a21007fe651081ffe3288401fe9944207ff0ca21025fcc310813ff5188409bfa8c4204ff94621027faa3108137d5188409fe28c4204ffd0621027fc8310813fd4188409fe20c4204ffcc621027fc6310813fd3188409fe18c4204ffc8621027de431081ff72188409ffb044204ff9822100dfcc110813fd60884017eb044204ff1822100df8c11086fff5088433ff284421bff542210cff8a11086bff4088433ff204421aff502210cff88110867fe3088433fe1844219ff8822103ff84110813fe1088409fe0844218ffd95210c5feca90863fe65484077f32a4218ff595210c5faca90863fc65484077e32a4217ffd91210bdfec89085ffe64484057f3224217ff591210bdfac89085ffc64484057e3224217ffd51210befea89085ffe544842ffeaa24217df551210bff8a890803ff63484017fb1a4200f7d8d21005bec690803fe63484117f31a4200ff58d21005fac690803fc63484117e31a4200f718d21005b8c690863ff5348431ff29a4218ff54d210c7f8a69085fff434842fff21a4217ff50d210bff88690863ff524840fff2924218ff5492103ff8a49085fff424840fff2124217fb909210bffa849085fed424840ffe2124200ffcc92103ffc6490803ee3248401fe9924200fb4c92103ff86490863ff5148431bfa8a4204ff945210c7faa2908037d5148409fe28a4217ffd0521027fc829085ffd4148409fe20a4200ffcc521027fc6290803fd3148409fe18a4207ffc852103fee4290813fe2148409f710a4200ffd8121005fec09085bfe60484037f3024200ff581210b7f8c090806fc6048431ffa824216ff941210c7faa09085bfc504842fffa024216ff901210bffa809085bfc404842dff1824216ff0c1210b7fc409081ffc204842dff0824204ff04121027feca10812ff6508409ff3284203bf99421026fcca1080e7e6508409f
  | 5 => 0x893103df8c498893ff524c449ff2926224ff54931127f8a49888fff424c447ff2126223ff5093111ff88498823ff324c401ef9926200ff8c931007fa6498803dd324c411fe1926224ffd4531126fea298813fe514c449fea8a6200df54531027f8a29888fff414c409ff20a6223ff50531027f88298823ff314c411fb98a6204ff8c531027bc6298803ff604c4017fb026222ff9813100dfcc098803fd604c445fe3026201bf18131127fea09888bfe504c449fea826222ff1413111ffe809888bfe404c447fea026222ff10131117fc6098823fc304c445ff1026222ff08131117fc2098813fc104c409ffb286204bfd9431027fcca1880efe650c409bf32862039f99431027faca18886fd650c409beb2862009f59431027f8ca18812fc650c409ffb206204bfd9031027fcc81880afe640c409df3206202af99031027fac818882fd640c409deb206200af59031027f8c818812fc640c441ffaa06220dfd5031107fca818883fd540c441beaa06220ff15031045fcc618823ff530c411ff2986208ff54c31047f8a618823ff430c411ff2186208ff50c31047f88618813ff620c409ff3106207bf98831027dcc418802ee620c409feb106200bf58831027dac418802ed620c409fe3106221ffd483110ffca418887fd520c443fe2906220ffd0831107fc8418883fd420c441fe2106208ffcc831047fc6418803de320c411fe9906208ff0c831047b86418812fe610c409ffa886204dfd4431027fca218813fd510c409bea886204ff14431027fe8218813fe410c409fea086204ff10431027fe6218813df310c409ff1886204fd8c431027fa6218813dd310c411fa9886204ffd8031027fcc018806fe600c409fd3006201be98031027fac018802fd600c409fcb006200be58031027f8c018806fc600c443ffa80621fff9403110ffaa01887ffc500c441ffa00621fff90031107fa801887ffc400c411ff1806208ff0c0310fffc401887ffc200c409ff0806204ff0403103ffecb9081eff65c840fff32e4203bf9972103ffacb9087afd65c840ffe32e4207bf1972103ffec99081eff64c840fff3264202bf9932103ffac990876fd64c840ffe3264207bf193210effea9908777f54c843bff2a6421dff553210eefaa990877fc54c840fffb1e4207bfd8f2103ffcc790822fe63c840ffeb1e4200bf58f2103ff8c79081efc63c843dffa9e421eff94f210f7faa79087bfc53c843bffa1e421dff90f210effa8790877fc43c840fffa964207ff94b2103ffaa59081ffc52c840fffa164207ff90b2103fdc859081ffd42c843bf6a164207ff10b2103ffe659081ffe32c840ff71964207ff4cb21007da659081ffc32c843dffa8e421edfd4721027fca39087bfd51c8401bea8e4204ff147210effe8390813fe41c843bfea0e4204ff10721007fe6390
  | 6 => 0x1beb02a22bdf18151166fe80a88af7e4054459bea02a22bdf1015115efc60a88af7c3054457bf102a22bdf0815115efc20a88137c1054411ffb2e6208bfd9731047fccb9880efe65cc411feb2e622abf59731047f8cb98822fc65cc411ffb266208bfd9331047fcc99880afe64cc411feb266229bf59331047f8c998822fc64cc453ffaa66229dfd533114ffca9988a7fd54cc453beaa66229ff15331047fea798823fe53cc411fea9e6208ff14f31047fe8798823fe43cc411ef21e6208ff50f3114fba8798823fc43cc411ffb166208ff98b3103dfcc598823fd62cc4017eb166208ff18b31157fea5988abfe52cc455fea96622aff14b3114ffe85988a7fe42cc453fea166229ff10b31047fe6598823df32cc411ff1966208ff4cb31007ba6598823fc32cc455ffa8e622adfd4731027fca3988abfd51cc401bea8e6204ff1473114ffe8398813fe41cc453fea0e6204ff10731047fec198823fe60cc4037f3066208ff58331005fac198823fc60cc4037e306622affd4331147fca1988abfd50cc451fe2866229ffd0331147fc81988a7fd40cc451fe2066208ff8c331047f861988a3fe20cc451fe1066228ff84331027f82198813ff658c4097fb2c6204ff9963101dfccb188137e658c4073f32c6204ff5963113dfacb188137d658c4013eb2c6204ff19631025f8cb18813ff648c4097fb246204ff99231015fcc918813fd648c44d7eb246204ff19231025f8c91889bff548c44dbfaa46226ff95231137faa91889b7d548c44dfe2a46223bf58e3113ffea718823fe538c44ffea9c6208ff14e31137fe8718823fe438c44dfea1c6208ff10e31027fec518813fe628c40f7f3146204ff58a31005fac518813fc628c44fffa946227ff94a3113ffaa51889ffc528c44dffa146226ff90a31137fa851889bfc428c411ff9946200ff8ca31007bc6518803fd328c411fe1946200f70ca31025fcc318813ff518c409bfa8c6204ff94631027faa3188137d518c409fe28c6204ffd0631027fc8318813fd418c409fe20c6204ffcc631027be6318823f7318c409ffb046204ff9823100dfcc118813fd608c4017eb046204ff1823100df8c11889fff508c44bff2846227ff5423112ff8a11889bff408c44bff2046226ff5023112ff88118897fe308c411fe1846225ff8823112ff84118813fe108c409fe0846224ffd9531125feca98893fe654c4077f32a6224ff59531125faca98893fc654c4077e32a6223ffd913111dfec89888ffe644c4057f3226223ff5913111dfac89888ffc644c4057e3226223ffd513111efea89888ffe544c447feaa26223df5513111ff8a898893ff534c411ff29a6224ff54d31047f8a69888fff434c411ff21a6223f790d3111ffa869888fdd434c411fe21a6200ffd8931005fec498803fe624c401feb126200ff1
  | 7 => 0x1901fff608c80fff3046401bf9823203ffac119002fd608c80ffe3046401bf182321affea1190cffe508c86bfea846433ff142321a7fe81190cffe408c869fea046433ff1023219ffc6119023fc308c80fff1046407ff0823219ffc21190cffc108c865ffb2a6432bfd9532197fcca9900efe654c865feb2a6432bf59532197f8ca9900efc654c863ffb226431bfd913218ffcc89900afe644c863feb226431bf5913218ff8c89900afc644c863ffaa26431dfd513218ffca8990c7fd544c863beaa26431ff15132197fea699023fe534c865fea9a6408ff14d3218ffe8699023fe434c863fea1a6408ff10d32197fea49901ffe524c865fea926407ff1493218ffe849901ffe424c863fea126407ff10932047fe6499023ef324c80fff1926407f78c932007fec299002ff614c801ff30a6400ff58532007f8c299012fc614c865ffa8a6432dfd4532197fca2990cbfd514c865fe28a6431ffd053218ffc82990c7fd414c863fe20a6400ffd8132005fec0990c3fe604c8037f3026400ff58132187f8c099006fc604c865ffa826430ff94132197faa0990c3fc504c863ffa026430ff9013218ffa80990c3fc404c861ff1826408ff0c132187fc409901ffc204c861ff0826430ff0413203ffeca1901eff650c80fff3286403bf9943203ffaca190befd650c80ffe3286407bf1943203ffec81901eff640c80fff3206402bf9903203ffac8190bafd640c80ffe3206407bf19032177fea8190bb7f540c85dff2a0642eff55032176faa8190bbfc540c8117f3186408ffd4c32047fca619023fd530c811fe2986408ffd0c32047fc8619023de430c811fea18642ef750c32047f8861901efe620c80fffa906407ff9483203ffaa41901ffc520c80fffa106407ff9083203fdc841901ffd420c85df6a106407ff1083203ffe641901fdf320c80fff1906407fb8c83203ffa641901fdd320c811f69906407ffd843203ffcc219012fe610c80ffeb086400bf5843203ff8c2190bfff510c85fbfa88642fff9443217ffaa2190bffc510c85dffa08642eff90432177fa82190bbfc410c80fffb006407ff9803200dfcc01901ffd600c8017eb006407ff1803200df8c0190bfff500c85bff280642fff5403216ff8a0190bbff400c85bff200642eff5003216ff88019023fe300c811fe1806407ff8803203ff840190b7fe100c85bfe080642cdfd9151164fec8a88b37e6454459beb22a22c9f59151166f8c8a88037f6354401bf31aa200df58d51006f8c6a88b37f4354459bf21aa22cdf50d51166f886a88037f6254401bf312a200df58951006f8c4a88b37f4254459bf212a22cdf50951166f884a88037f3254401bf192a200df4c951006f864a880f7f61544073fb0aa203ddd8551166fe82a88137e4154459bea0aa204df10551006fec0a88af7e605440
  | 8 => 0x400400300300080100081180400000080080080000100500000300900000000200080180780781e00880000d80d80580700180380900800400000000080000080f00000180100200200080480000000180080004100000680080001300000b00c00000000480480b80280180080080080080080000000c80c00480100380180000100300000501900080300000580300380000200002281d00100000200000800100000182100182c00a80000000000400000000000080080880081c00800300400080000000001781580480480180200300000680000701d01200000080300600000300680200000100080480480080200680080380e00180300180000100000000000000680000280100700500e00680100100780080081100080081600000d00000100500500400080080080080000a80c00080000000b80680000200000800600900000400300000000080100500080600200000880180080000000180280e00600d807008823ff65cc8117fb2e6408ff9973201dfccb99023fd65cc8717eb2e6408ff19732045f8cb99023ff64cc8117fb266408ff99332015fcc999023fd64cc86f7eb266408ff19332045f8c9990dfff54cc86fbfaa66437ff953321bffaa9990df7d54cc86ffe2a66408ffd4f32047fca799023fd53cc811fe29e6408ffd0f32047fc8799023fd43cc811fe21e6438ffd4b3203ffca5990e3fd52cc80ffe2966437ffd0b3203ffc85990dfee42cc86ffea166437fb50b3203ff88599023ff61cc811ff30e6404bf98732047fac399002fd61cc811fe30e6438ffd47321c6fea3990e3fe51cc871fea8e6438ff147321bffe83990dffe41cc86ffea0e6437ff10732047fec199023fe60cc8037f3066408ff58332005fac199023fc60cc8037e3066438ffd43321b7fca1990e3fd50cc86dfe2866437ffd03321b7fc81990dffd40cc86dfe2066408ff8c332047f861990dbfe20cc80ffe1066436ff843321b7f8219901fff658c80f7fb2c6407ff9963201dfccb1901f7e658c8073f32c6407ff596321adfacb1901f7d658c8013eb2c6407ff1963203df8cb1901fff648c80f7fb246407ff99232015fcc91901fbe648c8055f3246407ff592321a5fac91901fbd648c8015eb246407ff1923203df8c9190d3ff548c869bfaa46434ff952321a7faa9190d37d548c869fe2a46431bf58e321affea719023fe538c86bfea9c6408ff14e321a7fe8719023fe438c869ef21c6434ff50e321a7ba8719023fc438c80f7f3146407ffd4a3203ffca51901ffd528c80ffe2946407ffd0a3203ffc851901ffd428c80ffe2146407ffcca3203fbe6519023ef328c80fffb0c6407ff98632025fcc31901ffd618c8017eb0c6407ff186321affea3190d77f518c86bff28c6435ff546321aff8a3190d3ff418c869ff20c6434ff506321a7f883
  | 9 => 0x3df4dc2c31166e200000041937c0004df00029838636e0003052df18f2cc5884eb48b2594960003852dc0991180005fa6381f500000076f14300000061004c1de50468300055315006f0002d80a077267e0000000006d025a28928b66930b51237d45309b5983cb00000006e76413c2225b24ea10220a00c6020b10001934363d96e94734665e25c70ae6b760e0005e51770eb2ca3584a557e43d74460b5c25fd5cb11c7043215804176bc04d0aa2b268040562b40c03619615b31440600075472f4c14a31200001973a470c4b05b44c90000005217380006030de0000007394dd05f3a64490006740004a41a90000002e20004c30000000000000000000000000000004a200000000000018a56b6ce0a515e00000000044a00004400023800003800008a0005427100000000006660007690007301e800071b1715e33c220f6ee43546007530c06752759c3020c762c0ee0000000002e033d2856f124863c1614740002b70e264b1d60001e121246a2956a037646205b68b00031f0002f000023d1f71950b25293c86a37406b84ad5b56d90006fa6a80b519e6ae47c2ba70969836134100003132c07800300380300600080180080480180080280000000000180000080a00180000680001000180200180080000300000000980d81100680880400200c00180080400001280800000500600a00800b80680580001780d00200100d00180000080000880000180000000080400381000b01b00680001500400480380300080300000201080000400100000280400280201000080000200000200180180000180080080d00580080a00580080180380000380080500180102b00180080500300380d00a80500000280000000700000080900200200600980001100580301600180280000000000000100180200f80080000000081d80080080300000200a80200200300100080a80080200000101a80a00080980400001300000000480400000500780980a00280000000200000d80480000000780001200280700100080000000081300080480000500001700880780081200180400100100600000100680a00500000280100180000000180080280100300300200080280200080a80980100580180000c80000180180400300000000900580780000680080080100280000100280000700200900080200400000480580180000e00080480b00000580000000480b80280280700d80001200080e00000080080000180600280d80000200100080100080000000000000180a80080280900100680180580000400780180000900602000000201e00000100302080000a80080180500380380700300180000000000000300000480000200900200180000480080300280280080080400780600080380000000100600200200680480400300000400000400000
  | 10 => 0x280005bd57858100000028c76a00000001e04b5726520000000ac00010d4375dd71d6092d712156f5af0005b900075614010a2a15e00006684215840d10015b80480000fd12662477837807a44f0001d759b22c3bd5404ac00024c0004e03966d53c91c52350006f56f900022e73e57d0004ca40d16e40111b0005b00006375061907366f45f04f10005180462e331d00028406d4bc1590030002742d40002f40000000c300017675e2dd2d65a700056123e0006440000db59f30d17a19470f00054e5640254c22d06bf22838757668735f4f033351c69237332911169d00015d47e51939f00004a6150c10fb0533166e00000000270a81133906eb3031e33fd52d0af2686f70000a96880000000001494b852a76d4130000c81cc00024746b45c37b4142035ab5a262f5f629076775152653369163f21938d6853896d608c1575200df4266005484da0572792112673373805e14d948c4904be24e6df4127224e56d26756893340b61ab2b94886e504f67d4923566c47154913470262e45857492ef00b20835b6060801273440303ec47a50a6d771a27672465c66048d4582c12f65ed3f71603b848949334073a1010373984862071f84203e454a02259055269b5b75a447112d47b0ff0004b10833ab1cd7331c823a47074f1042a03da3f111465349b2021be0133665c92af1d57771fa2a302c5c54830c22b01d173c2fc48737e0971a34d83eb54f18127a64133b73d2541e54670000000c623f26160c77a4f931a16800060d00009f20000000026d36c00052e0000000325c66aa2e141f61c27e45218368200002e74d0b91315da0d46042a42820760003f605e1030885d72e714144212500a5dc4230005581da0000870ec2aa57061f4f810b0005d36a753b62a6c113400077000046f1a754558c5744af4e216d10f7552577626726183b90000167311290000000793a50000000cf0001587126c63af01255a3483a71870006902ff0f20000b30000000000000000000000000d937432b3e834e5945cd1f962758a69e6de3ff35318b4327185695bb00064d6637500003281bf00000049f0000000006ec4801b100032e0003006560004ba4510003255fe0000001af1f218200072a0005f35100006195016c925153156769f0006b664051a5bf3c420e3ea26e20600069603b53851e6ed0007030003e16b340300000043172b4985356cd0591e621a7590000004a77005035ae7634a100038f2f964a6af4f572655b2620770002b66fc2e60f55db35525c06232d44600041a45a00022974e66b5e851323466c2ae3112d10e47274b33393ba21e1b83f814c29f2c23993352374f44d641621b32303f7796772ce2240242f73271b60cc64240936a6a534a08f1a46f365f5791eb1dc3aa4c644831343f23069404172e5f82c64a617b00008653648a073
  | 11 => 0xd40f0006d30005573192215510470d244750b07d2cb0000006bb0e12360007411880002f86ef4d53bb0684cc33800005c3db2693916ba22b24b15377400000041570b4ce0001e000022d0a216467b3f570a0001550003c51634cd2de6c52c95a14f34d40000c46086e80004db2925ee0000115167166792f30cb2d30003d10000dc0001e719d77552831b2d528d0003a367364715400053c36b2a231233c1a869c21d3522441195775541a05ff68f46d0006144f20b059257a0150a45a37354fd2c563912f2882465820493245006ab57c1223f45c000011a0004ee3e06dd29d3ca3fc0e84ef0562e536f4726a96b92551db0000005ba00076b7083315ca45002b0002ee0003084fb6174004fc2ec1c90e05250060333423a949700041134f0000003cd4b70006481ad00050f0000006640000002fd24d4bb1f60003e209d4fa3ad00201c4d700f3492163105861ce1286610f13545235bc6546c75a60d020501b49900007f3590be06a65b0005fb0bd5b30006c20007133d75aa3bf76853d2f55c15fc2421ba2be61b52b1333f00005f952406327b1c343e0f40043223cf4576502ad3ee58900059300000008200061d1e438a24f1a51c239314845b0d76931ec13043410856d2ea16b46e00064e26a7530006a21461c777317f3be1626970055321bc27263d5b10954400c92715d55e90006ca07b33e3502910856f01f33e31b33ef21434511d33f0002526e175772c00049a00055517462d55e3ed0bc55f0e500000000000005d0ba0f91aa0003c729926b2fa0e91754337280b71780000f83772bc0004d30000000666990003d554c59e5990000004f75d21915560000000006950000000b45ad68c3b00e741e4ae3a10d553e14b18c6e31ee6da13d32066525e20900030122520d4ed21f5116e629b4d240418651771f00044d0004f65d835d64f0000000000940000cd4412630000da5d025d64300056a00006000066d1bb4c038e2b10004fe0235d15ea2b53710003062c76864ec6bd1801a241c41d1ff44e68a4245083f36b16fe01a13806c00020b39d3515306d117c40850770d5870001527656d85c30001664ff3327054e31e93cc1cf08902d6291cb0003b600000042c08d3b50003651b507214f0a11c12cf0005432b35f468400062e03475a74b2a804530e40a4c514e2182960e631e45e02f6b43180005663ac41b00004229424a27819262100063476e2706fb42a4384c767c00031764925b23251500036200000059608b6cf66a00064c2c06262cd1d348166700062503e42b07e13a3971fb30f0000001361d00001004b21d827c3836512642da1a10006361e228f2f201955d1fd6be0f746474816c1b01df5eb3f20003b427d00028071c2a56ad16a70e70150d4297601ae1984685c422f56e16f0c075f0000001090393680961ef29e6
  | 12 => 0x2b448e43068d3844183c328363e28e5950001393f97065a80000006d435c4e901005232a0510000916354de0000582275a55a060f48f39a6db1fc00037060a20c30947d42f2101d258306457577117d1241104b43430bf6cb39e14a29370754b1a61700933dd75201437924523b4e839b0ed21c3e700000000018e24057b2432662201ed1473b13e65ce4942b85ac1452a62ed2e83ae0293de27f49e4795a900065e0c501802049d61166e76600967f5f52012c447542e4543a869a36474363353f2eb4254950005ef0502c847816910c00024100057161229a73768e0a64e44ab1653692261790925df4aa6dc2ab0690d300e74521512c58f46551f58e1c007c5d40f023961e61a12b3d452c6e768109c72143b59d6e459a65a7203a244519c0a300062252f0bb13e52208e5d60003882bd44403a00071900075b42d0f31b926074600000011f0000d835e16700000000008126f02815a0000000004286ea43c1b75be7587230000610003dc4840004822e92041060000170ca0983bc33a00834653466f65773f0006164d066255c4853b21723c60f625f51b0005de6596c374c2fe09e4a94d10001370001ac58b58d09a25600013223c2ac53a21312a1ea6301155390006b07142a954445f1990000b83d218942700000000000014239202115142201d06546103573b0000000000000003e50000002332bb08444b15600005a29722a14d3363c150c0003b74e10d64a83fa6fd31c3571c43955ec44c38c5650000005141f167a6b234d5500e330767800049c29c1ca00013b5971d434c6ff00036313501f10500d0000006a65055d97420001d93fe2532d21f44105cc0003fb3720000004074b527717e2810000004b93ce5371235cf00000027306b4bf00000063a00036700067000040e56823147f34b0741b271e75c1c640b5463942fb4b671754d19a6460a737a1fe02a1842656014cb33037f1854435605f731557318d0fe0fa07139c10e4c805465d3c036d0706c82d90403a00003d87613b37295624c46312a75c82756f645513f28700047663b5410006235e60ce0007762232db5e70003040076053811f021738b35a4590000003d030a19f4690fc6c00ef3e94027256454561dd6136cc7115592495f10ab2bf67109028646c00000015c63200067600076c6b52586200004774bd04e0000000006a47025910ad1bd43a6f24a05470000dd4e732600000046300000011728a2f160737500000032f50936000051d0007326ac56c15f72d6f800000017300074710700025050e0003d656326c5b614474a6556583d311257f03c4e675d38205519b12e11e5025e44397345496a10430000004cf5f203d0000ea1b445
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x7048510026f76048510027f360485100b7f2404851020ff140485100b7d730485100b7f230485100b7d530485100b7e720485100b7f220485100b7e52048510025f8764c110046f8764c110024f8764c1100077b754c1101f778754c1101fdfb744c1101fdf9744c1101ef7b544c1101ef79544c11000dfb734c11000fdb734c110007db634c110046fa634c110046f8634c110007d8634c1101f7db534c1101f7da534c1101f7d9534c1101f7d8534c1101efdb434c1101efda434c1101efd9434c1101efd8434c110005fb724c110007db324c110007da324c110007d9324c110007d8324c110007f3714c110025fa714c110025f8714c110007f0714c11000efb614c11000ff3614c1101f77b514c1101f7f2514c11000779514c1101f7f1514c11000771514c1101eff2414c1101eff1414c110007db314c1101e7da314c110007d9314c1101e7d8314c110007f2214c110007f1214c110007db764c110046db764c110007d8764c110006d8764c110207db754c1100075b754c1101f7da754c110207d9754c1101f7d8754c1101f758754c1101f7db654c1101f7da654c1101f7d9654c1101f7d8654c1101ffdb744c1101efda744c1101ffd9744c1101efd8744c1101efdb644c1101efda644c1101efd9644c1101efd8644c1101efdb544c1101ef5b544c1101efda544c1101efd9544c1101ef59544c1101efd8544c110007db724c110007da724c110007d9724c110007d8724c110007db624c110007da624c110007d9624c110007d8624c1101f7db524c1101f7da524c1101f7d9524c1101f7d8524c1101efdb424c1101efda424c1101efd9424c1101efd8424c110007db714c110007d3714c1101e7da714c110007d9714c1101e7d8714c110007d0714c11000fdb614c11000edb614c11000fd3614c1101f7db514c1101f75b514c1101e7da514c1101f7d2514c1101f7d9514c11000759514c1101f7d1514c11000751514c1101e7d8514c1101efdb414c1101e7da414c1101efd2414c1101efd9414c1101efd1414c1101e7d8414c110007db214c1101e7da214c110007d2214c110007d9214c110007d1214c1101e7d8214c110025f8764811003ef87648110024f876481100077b75481101d77875481101ddfb74481101ddf974481101cf7b54481101cf795448110005fb7348110005f9734811000dfb724811000feb7248110007eb624811003efa624811003ef86248110007e862481101d7ea52481101d7e952481101cfea42481101cfe94248110007f37148110025fa7148110025f87148110007f0714811000efb614811000ff361481101d77b51481101d7f251481100077951481101d7f151481100077151481101cff241481101cff14148110007eb2148110007f22148110007e92148110007f12148110007e12148110
  | 1 => 0x45100277421545100077b705451015f7870545100267f605451015f7a405451024779405451015f5f305451015f7a305451015f5d305451015f7a20545100277b105451015f76105451002774105451002778105451003777765451001e77765451015f74765451001e74765451024f77745451024d77745451024776745451024f75745451024d75745451024774745451024777645451024776645451024775645451024774645451000777735451000776735451000775735451000774735451000777635451000776635451000775635451000774635451024777435451024776435451024775435451024774435451000777725451000776725451000775725451000774725451000777625451000776625451000775625451000774625451024777425451024776425451024775425451024774425451000777325451000776325451000775325451000774325451015f77705451000773705451015f76705451015f75705451015f74705451015f70705451002777605451002677605451002773605451015f77405451015f76405451015f72405451015f75405451024771405451015f74405451015f77305451015f57305451015f76305451015f72305451015f75305451015f55305451015f74305451015f77205451015f76205451015f72205451015f75205451015f74205451000cfe76cc51000cfc76cc510006df63cc510046dc63cc5100077551cc51000dfa70cc510005f970cc510044ff764c51000cfe764c510114fd764c51000cfc764c510006df634c510046dc634c51000775514c510005fb704c51000df8704c51000cfe76c851000cfc76c8510006ef62c851003eec62c85100077551c851000dfa70c8510005f970c851009df67688510026f67688510025f7758851002776758851023df57588510027757588510005757588510025f77488510235f5748851022f77548851022f7554885100b5f5728851003ef6628851003ef46288510027f3708851000df6708851000df47088510027f07088510026f76088510027f360885100cff2408851022ff140885100cfd730885100cff230885100cfd530885100cff2208851003cff764851000cfe76485100b4fd764851000cfc7648510005df7348510005dc7348510006ef624851003eec6248510227775148510007755148510027e42148510005fb704851000df87048510027f0104851000df4764851003ef4764851000cf4764851021df7754851021df57548510215f77448510215f5744851020f77544851020f755448510007d77348510007d47348510025f77248510027e77248510007e7624851003ef6624851003ef46248510007e4624851020fe6424851020fe54248510007e63248510007e53248510007f3704851000df6704851000df470485100b7f
  | 2 => 0x14bc7458d100067f5458d100067d5458d10006df7358d10006de4358d10006dd4358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d10144ff7158d10006f77158d100067f5158d101e6de3158d101e6dc3158d10114ff7058d10006fb7058d10116df3058d10116dd3058d1012cfe7618d10046de6318d10006dd6318d1003cfe76d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d89100067f54d89100067d54d8910044fe73d8910004fd73d8910024fe71d8910024fc71d89100067f51d8910024ff70d891000cfe70d8910024fd70d891000cfc70d89100cedf30d89100cedd30d89100ceef20d89100ceed20d8910006ef62989100b5f571989100057f75589100357c7558910005bf745891002dbc7458910005df7358910005dc73589100e5f77158910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc74589100067f54589100067d5458910004ff7358910006df7358910004df7358910044fc7358910006dc7358910044dc7358910006ef7258910006ee4258910006ed42589100e4ff7158910006f771589100067f51589100b4ff7058910006fb70589100b6df30589100b6dd30589100ccfe76189100357e75189100057d751891002dbe7418910005bd7418910005de7318910005dd731891003eee6218910006ed6218910044ff76cc910004fe76cc910004fd76cc910044fc76cc910046de63cc910006dd63cc910006ef62cc91003eec62cc91000dfa70cc910005f970cc91003cff768c910004fe768c910004fd768c91003cfc768c9100357e758c9100057d758c91002dbe748c910005bd748c910006df638c910046dc638c910025f6718c910005f5718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c910046de634c910006dd634c91000dfa704c91003cff760c910004fe760c910004fd760c91003cfc760c910006df630c910046dc630c910006ef620c91003eec620c910025f6710c910005f5710c91000dfa700c910005f9700c91001e7f765451015e7e765451015e7d765451001e7c765451024d7f745451024d7d74545102467f64545101667e64545102467d64545101667c64545100067f635451025e7e63545100067d635451025e7c63545100067f62545102567e62545100067d62545102567c62545100257f71545100377771545100267f615451024777415451002776415451024775415451002774415451002776315451002774315451002776215
  | 3 => 0xe63ccb10006dd63ccb1003cff768cb10024fe768cb10004fd768cb10024fc768cb100557e758cb100057d758cb101ae7e658cb100067d658cb1004dbe748cb10005bd748cb1029edf638cb10046dc638cb1003eee628cb10006ed628cb10025f6718cb10005f5718cb10004ff764cb10024fe764cb10004fd764cb10024fc764cb101967e654cb100067d654cb10046de634cb10006dd634cb1003eee624cb10006ed624cb1003cff760cb10024fe760cb10004fd760cb10024fc760cb1017e7e650cb100067d650cb10296df630cb10046dc630cb10025f6710cb10005f5710cb1002777765471002577765471028e77765471028777745471028577745471027f76745471028775745471028575745471027f74745471002777645471002776645471002775645471002774645471000777735471000776735471000775735471000774735471002777635471002776635471002775635471002774635471027f77435471027f76435471027f75435471027f74435471000777725471000776725471000775725471000774725471002777625471002776625471002775625471002774625471027f77425471027f76425471027f75425471027f74425471000777325471000776325471000775325471000774325471015f77705471015f76705471015f75705471015f74705471015e75605471015f77405471015f76405471015f75405471015f74405471015f77305471015f57305471015f76305471015f75305471015f55305471015f74305471015f77205471015f76205471015f75205471015f742054710025f77648710006f77648710275f77548710275f5754871002776654871002775654871026df7744871026df57448710267775448710267755448710007d77348710007d47348710027e77248710027e7624871003ef66248710026f46248710027e46248710267e64248710267e54248710007e63248710007e5324871000df6704871000df470487100b7d730487100b7d530487100b7e720487100b7e52048710044fe76d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d100067f54d8d100067d54d8d1003cfe72d8d10004fd72d8d10024fe71d8d10024fc71d8d100067f51d8d10024ff70d8d1000cfe70d8d10024fd70d8d1000cfc70d8d1012edf30d8d1012edd30d8d10006df6398d10115f57198d100057f7558d100357c7558d10005bf7458d1002dbc7458d10005ef7258d10005ec7258d10145f77158d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10
  | 4 => 0x8520005df7348520005dc7348520006f76148520026f4614852003fe42148520005fb704852000df8704852003fe8204852000dec7648520026ec764852000cec76485202bdef75485202bded75485200076f65485202a76c65485202b5ef74485202b5ed74485202aeef64485202aeed64485202af6f54485202af6d5448520007cf7348520007cc7348520006ef6348520006ed634852003def714852003fe77148520007e76148520026ee6148520026ec6148520007e461485202a76f51485200076d5148520007eb704852000dee704852000dec70485200b7e8704852003eef604852003feb60485200b7cf30485200b7cd30485200b7ea10485200067f74597100047f74597100067e74597100067d74597100047d74597100067c74597100067f73597100067e73597100067d73597100067c73597100067f43597100067e43597100067d43597100067c43597100067f72597100067e72597100067d72597100067c72597100067f42597100067e42597100067d42597100067c42597100267f71597100247f71597100267e71597100267d71597100247d71597100267c71597100267f41597100267e41597100267d41597100267c41597100267f31597100267e31597100267d31597100267c31597100267f21597100267e21597100267d21597100267c215971015e7f705971015e7e705971015e7d705971015e7c705971015e7f405971015e7e405971015e7d405971015e7c405971015e7f305971015e5f305971015e7e305971015e7d305971015e5d305971015e7c305971015e7f205971015e7e205971015e7d205971015e7c20597100267f10597100267e10597100267d10597100267c1059710004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f100067f5458f100067d5458f10026df7358f10006de4358f10006dd4358f10004ff7258f1003cfc7258f10024ff7158f1000cfe7158f10024fd7158f1000cfc7158f100267f5158f100267d5158f10026de3158f10026dc3158f10116df3058f10116dd3058f10026fa1058f10026f91058f10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b100067f5458b100067d5458b10004ff7358b10006df7358b10004df7358b10044fc7358b10006dc7358b10044dc7358b10026ef7258b10006ee4258b10006ed4258b10024ff7158b1000cfe7158b10024fd7158b1000cfc7158b100267f5158b100267d5158b10026ee2158b10026ec2158b100b6df3058b100b6dd3058b100b6ef2058b100b6ed2058b10026fa1058b10026f91058b10044ff76ccb10024fe76ccb10004fd76ccb10024fc76ccb101c67e65ccb100067d65ccb10046d
  | 5 => 0xdf8704c92003fe8204c920024fe76d85200657c75d85200067f65d85200067c65d8520004ff75d85200067f75d852001cfe75d8520004fd75d852001cfc75d85200067c75d852001c7c75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d85200067f54d85200067d54d8520044fe73d8520004fd73d8520006ee42d8520006ed42d85200067f51d852000cfe70d852003cfd70d852000cfc70d85200e6df30d85200e6dd30d85200e6f710d85200657e75985200057d75985200067f65985200067c6598520006f761985200057f75585200657c75585200067f65585200067c6558520005bf745852005dbc7458520005df7358520005dc73585200657e75185200057d75185200067f65185200067c651852005dbe7418520005bd7418520005de7318520005dd7318520026f66118520006f561185200067f76545200057e76545200067e76545200047e76545200067d76545200057c76545200067c76545200047c76545202f57f74545202f57d74545202ee7f64545201667e64545202ee7d64545201667c64545200067f635452025e7e63545200067d635452025e7c63545200076e72545200076d725452015e7f62545202ef6e42545202ef6d42545202e57f71545200677771545200067f61545200267e61545200267c615452015e7f605452015f5f305452015f5d30545202577b205452015f6e205452015f6c205452015f78205452015f7a1054520004fe76cc520004fd76cc520044fc76cc5200067f65cc5201567c65cc520046de63cc520006dd63cc520004fe768c520004fd768c520024fc768c5200657e758c5200057d758c5200067f658c52013e7c658c520006df638c520046dc638c52003dee728c520005ed728c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c5200067f654c5201267c654c520046de634c520006dd634c520004fe760c520004fd760c520024fc760c5200657e750c5200057d750c5200067f650c52010e7c650c52005dbe740c520005bd740c520006df630c520046dc630c52003dee720c520005ed720c52000dfa700c520005f9700c52009dee76c852003eee76c852003def75c85202dded75c85200076f65c85202c76c65c852003def74c85202d5ed74c85202ceef64c85202ceed64c85202cf6f54c85202cf6d54c8520006ef63c8520006ed63c8520026ee61c8520026ec61c85202c76f51c85200076d51c852003feb70c852000dee70c852000dec70c852003fe870c852003eef60c852003feb60c85200e7cf30c85200e7cd30c85200e7ea10c852000cfe76885200657e75885200057d75885200067f65885200de7c65885200b5ed7288520006f76188520026f4618852000dfa7088520005f9708852000cfc76485200067f65485200c67c654
  | 6 => 0xf51487200076d514872000dee704872000dec70487200b7cf30487200b7cd30487203157e76d95200667e76d952001c7e76d95200057f74d95200057d74d95200067f64d95200067e64d95200067d64d95200067c64d95203076f72d95203076c72d95200076e42d95200076d42d95200057d71d95203075f30d95203075d30d952030f7b20d95203076e20d95203076c20d95203077820d95203077a10d95200067f74d95200047f74d95200067e74d95200067d74d95200047d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95203067f72d952030e7e72d95203067d72d95203067c72d95200067f42d952030e7e42d95200067d42d952030e7c42d952030e7e32d952030e7c32d95200067f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d952030e7f21d952030e7c21d95203067f70d95203067e70d95203067d70d95203067c70d95203067f40d95203067e40d95203067d40d95203067c40d95203067f30d95203065f30d95203067e30d95203067d30d95203065d30d95203067c30d95203067f20d95203067e20d95203067d20d95203067c20d95203067f10d95203067e10d95203067d10d95203067c10d9520044fe76d8d200067f65d8d200067c65d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d200067f54d8d200067d54d8d20006de43d8d20006dd43d8d2003cfe72d8d2003cfc72d8d20024fe71d8d20004fd71d8d200067f51d8d2003cff70d8d2003cfd70d8d2019edf30d8d2019edd30d8d2019efa10d8d200657e7598d200057d7598d200067f6598d200067c6598d2005dbe7498d20005bd7498d20006df6398d20185ed7298d200057f7558d200657c7558d200067f6558d200067c6558d201b5ef7258d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20014fe7458d20004fd7458d20014fc7458d200067f5458d200067d5458d20006df7358d201b4ff7258d20006ef7258d202fede3258d202fedc3258d20004ff7158d20024fc7158d200067f5158d20184ff7058d20006fb7058d20186df3058d20186dd3058d20186fa1058d2019cfe7618d200067f6518d200067c6518d20046de6318d20006dd6318d2000cfe76cc92000cfc76cc9200067f65cc9201c67c65cc920006df63cc920046dc63cc92000dfa70cc920005f970cc920044ff764c92000cfe764c920184fd764c92000cfc764c9200067f654c9201967c654c920006df634c920046dc634c920005fb704c920
  | 7 => 0x8130047d972d8130047d872d8130007db62d8130007da62d8130007d962d8130007d862d8130367db52d8130367da52d8130367d952d8130367d852d813035fdb42d813035fda42d813035fd942d813035fd842d8130047db71d8130047da71d8130047d971d8130005d971d8130047d871d8130007db61d8130007da61d8130007d961d8130007d861d8130367db51d81303675b51d8130367da51d8130367d951d81300075951d8130367d851d813035fdb41d813035fda41d813035fd941d813035fd841d8130007db21d8130007da21d8130007d921d8130007d821d8130004ff7558f2001cfe7558f20004fd7558f2001cfc7558f20004ff7458f20014fe7458f20004fd7458f20014fc7458f200067f5458f200067d5458f2003edf7358f2003cff7258f2000cfe7258f2003cfd7258f2000cfc7258f2003ede3258f2003edc3258f20004ff7158f20024fc7158f200067f5158f2003eef2158f20186df3058f20186dd3058f20004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720014fe7458720004fd7458720014fc74587200067f54587200067d5458720004ff7358720006df7358720004df7358720044fc7358720006dc7358720044dc735872000cfc725872003eee4258720006ed425872003ef771587200067f515872003ef7215872003ef421587200b6df30587200b6dd305872003efa205872003ef920587200b6f710587200067f76547202567e76547200067d76547202567c76547203557f74547203557d74547202567f64547201667e645472034e7d64547202567c64547202567f635472025e7e63547200067d63547202567c63547202576e72547200076d725472015e7e62547202576e425472034f6d42547202e57f71547200777771547200267e61547200067d61547200267c61547202576f215472015e7d605472015f5f305472015f5d305472015f6e205472015f7a205472015f6c2054720044ff76cc72003cfe76cc720004fd76cc720046de63cc720006dd63cc720024ff768c72003cfe768c720004fd768c7200757e758c7200057d758c720346df638c720046dc638c72003dee728c720005ed728c720004ff764c720004fd764c72003cfc764c720046de634c720006dd634c720024ff760c72003cfe760c720004fd760c7200757e750c7200057d750c72006dbe740c720005bd740c72033edf630c720046dc630c72003dee720c720005ed720c72000dfa700c720005f9700c72003def7648720006ef7648720335ef7548720335ed754872032def744872032ded744872003eef6448720326ed64487203276f54487203276d5448720007cf7348720007cc734872003eef6348720006ed634872003fe7714872003fe76148720026ee6148720026ec614872003fe4614872031f6
  | 8 => 0x2fddc75c85300075f65c85303cf5c65c85302fddf74c853007dde74c85303dddd74c85302fddc74c85303d75f54c85303d75d54c85302ffce62c8530007cd62c85302ffce42c85303d7cd42c85303cf5f51c85300075d51c85300e5df70c853000dde70c85300e5dd70c853000ddc70c85300e6df60c85300e7cf20c85300e7da10c85301e5df7688530005de7688530005dd76885301e5dc76885301e5df7588530085de75885301e75e75885300855e75885303c5dd75885301e75d75885300055d75885301e5dc75885300075f65885303bf5c65885301e5df748853007dde74885303b5dd74885301e5dc74885303af5f54885303af5d54885300b5dd7288530007cf6288530007cc628853009dde71885301e75f51885301e75d51885301e7cf21885302ffd721885300cddf708853000dde70885300cfda708853000dda70885300cddd70885301e7d97088530005d9708853000ddc70885300cedf60885300cfd710885300cfda1088530005df7648530006df7648530004df7648530005de7648530005dd7648530005dc7648530006dc7648530004dc76485303a5df7548530085de75485303a5dd7548530085dc75485300075f654853038f5c654853039ddf744853007dde744853039ddd744853007ddc74485303975f54485303975d5448530007ce6248530007cd6248530397ce4248530397cd424853038f5f51485300075d51485302ffd721485301e7ce21485300b5df704853000dde704853000ddc70485300b6df60485300b7da10485301e5df7608530005de76085301e6de7608530004de7608530005dd76085301e6dd7608530004dd76085301e5dc76085301e5df7508530085de75085301e75e75085300855e7508530385dd75085301e75d75085300055d75085301e5dc75085300075f650853037f5c65085301e5df740853007dde74085301e79e740853007d9e7408530375dd74085301e79d74085300059d74085301e5dc740853036f5f540853036f5d54085300e5de7208530007cf62085302ffcc62085300cdde71085301e75f51085301e75d51085301e7cf21085301e7d621085301e7cd21085302ffd5210853009ddf700853000dde700853009fda700853000dda700853009ddd70085301e7d97008530005d9700853000ddc700853009edf600853009fda100853000fda76d813000dda76d813000eda76d8130047db75d8130047da75d8130047d975d8130047d875d8130367db65d81300075b65d8130367da65d8130367d965d8130367d865d81303675865d8130047db74d8130047da74d8130047d974d8130047d874d813035fdb64d813035fda64d813035fd964d813035fd864d813035fdb54d813035f5b54d813035fda54d813035fd954d813035f5954d813035fd854d8130047db72d8130047da72d
  | 9 => 0xe75985301e75e75985300855e7598530005dd75985301e75d75985300055d75985301e5dc75985300075f65985300075c65985301e5df749853007dde7498530005dd74985301e5dc74985300075f54985300075d54985302fdde7298530005dd7298530006de6298530006dc62985300fdde71985301e6df6198530007d761985301e75f519853012ddd70985301e7d97098530005d9709853012edf609853012fda1098530005df75585300075f75585300055f7558530085de7558530005dd7558530085dc75585300075c75585300855c75585300075f65585300075c6558530005df74585300079f74585300059f745853007dde7458530005dd745853007ddc74585300079c745853007d9c7458530006df6458530006dd64585300075f54585300075d5458530005df7258530007cf7258530005cf72585302fddc7258530007cc7258530005cc7258530006df6258530006dd6258530007d761585301e6de61585300075f5158530115df7058530007db7058530005db7058530117da1058530145de76185301e5df7518530085de75185301e75e75185300855e7518530005dd75185301e75d75185300055d75185301e5dc75185300075f65185300075c65185301e5df741853007dde74185301e79e741853007d9e7418530005dd74185301e79d74185300059d74185301e5dc74185300075f54185300075d54185302fdde72185301e7ce7218530005ce7218530005dd72185301e7cd7218530005cd7218530006de6218530006dc621853012dde71185301e6df61185301e7d661185301e6dd6118530007d561185301e75f5118530045df701853000dde70185300fddd70185301e7d9701853000ddc70185300fedf60185300ffd710185300ffda10185300ffd510185300075f76545300075e76545300055e76545300075d76545300075c76545300055c76545303f75f74545303f55f74545303ef5e74545303f75d74545303f55d74545303ef5c74545303ef5f64545303ef5e64545303ef5d64545303ef5c64545300075f72545300075e72545300075d72545300075c72545300075f62545300075e62545300075d62545300075c62545303ef5f42545303ef5e42545303ef5d42545303ef5c42545300875f71545302e55f71545300875771545300075f61545301e75e61545300075d61545301e75c61545303ef5f41545301e75e41545303ef5d41545301e75c415453015f5f705453015f5e705453015f5d705453015f5c705453015f5f605453015e5f605453015f5f405453015f5e405453015f5d405453015f5c405453015f5e205453015f5c205453015f5f105453015f5e105453015f5a105453015f5c10545302fddf76c8530005de76c8530005dd76c85302fddc76c85302fddf75c8530085de75c85303e5dd75c8530
  | 10 => 0x95300055d71d95300075c71d95300075f41d95300075e41d95300075d41d95300075c41d95303ff5f70d95303ff5e70d95303ff5d70d95303ff5c70d95303ff5f60d95303fe5f60d95303ff5f40d95303ff5e40d95303ff5d40d95303ff5c40d95303ff5f20d95303ff5e20d95303ff5d20d95303ff5c20d95303ff5f10d95303ff5e10d95303ff5a10d95303ff5d10d95303ff5c10d9530005df75d8930085de75d8930005dd75d8930085dc75d89300075f65d89300075c65d8930005df74d893007dde74d8930005dd74d893007ddc74d89300075f54d89300075d54d8930007ce42d8930007cd42d89301e5de71d8930005dd71d89300075f51d8930045df70d89301b5dd70d89301b6df60d89301b7cf20d89301b7cd20d89301b7da10d89302fddf7598930085de75989302ff5e75989300855e7598930005dd75989302ff5d75989300055d75989302fddc75989300075f65989300075c65989302fddf749893007dde74989302ff9e749893007d9e7498930005dd74989302ff9d74989300059d74989302fddc7498930006df6498930006dd64989300075f54989300075d549893016dde72989302fedf6298930007cf62989301e5de7198930005dd71989300075f519893019ddd70989302ffd97098930005d9709893019edf609893019fda1098930005df75589300075f75589300055f7558930085de7558930005dd7558930085dc75589300075c75589300855c75589300075f65589300075c6558930005df745893007dde7458930005dd745893007ddc74589300075f54589300075d5458930007cf62589302fede6258930005df71589301e5dc71589300075f5158930185df7058930007db7058930005db7058930187da10589301b5de76189302fddf7518930085de7518930005dd75189302fddc75189300075f65189300075c65189302fddf741893007dde7418930005dd74189302fddc7418930006df6418930006dd64189300075f54189300075d541893019dde72189302fedf62189302ffce62189302fedd6218930007cd6218930006cd62189302ffce4218930007cd42189301e5de7118930005dd71189300075f5118930045df701893000dde701893016ddd701893000ddc701893016edf601893016fcf201893016fcd201893016fda1018930005df75d85300075f75d8530085de75d8530005dd75d8530085dc75d85300075c75d85300855c75d85300075f65d85300075c65d8530005df74d853007dde74d8530005dd74d853007ddc74d8530006df64d8530006dd64d85300075f54d85300075d54d85302fdde72d8530005dd72d8530006df62d8530006dd62d85300075f51d8530045df70d8530007db70d8530145dd70d8530146df60d8530147d710d8530147da10d8530147d510d85301e5df7598530085d
  | 11 => 0x12fda708c53000dda708c5301e7d9708c53000ddc708c530046df608c530047db608c53012fda108c53000cfc764c5300067f654c5301267c654c530006f7614c530026f4614c530005fb704c53000df8704c530047d8304c53000ddc764c530026dc764c53000cdc764c530445df754c530085de754c530445dd754c530085dc754c5300075f654c53042f5c654c53043ddf744c53007dde744c53043ddd744c53007ddc744c530436df644c530436dd644c5304375f544c5304375d544c530005df724c5302fddc724c530006df624c530045df714c530047d7714c530007d7614c530026de614c530026dc614c530007d4614c53042f5f514c5300075d514c530007db704c53000dde704c53000ddc704c530117d8704c530046df604c530047db604c530117da104c530145de760c530046de760c530045df750c530085de750c5300475e750c5300855e750c530425dd750c5300475d750c5300055d750c530045dc750c5300075f650c53041f5c650c530045df740c53007dde740c5300479e740c53007d9e740c530415dd740c5300479d740c5300059d740c530045dc740c53040f5f540c53040f5d540c5302fdde720c530047ce720c530005ce720c530005dd720c530047cd720c530005cd720c53033edc620c53012dde710c530047d6710c5301e6df610c5301e75f510c5301e75d510c53000dde700c530047da700c53000dda700c530047d9700c53000ddc700c530046df600c530047db600c5300ffda100c530004fe76c8530004fd76c853003cfc76c85300067f65c85300f67c65c85302fddf73c8530045de73c8530005dd73c8530045dc73c853003eee62c85302ffce32c8530007cd32c8530004fe7688530004fd7688530024fc76885300857e75885300057d75885300067f65885300de7c65885301e5df7388530045de7388530005dd7388530045dc7388530006ef628853003eec628853000dfa7088530005f97088530004ff7648530004fe7648530004fc76485300067f65485300c67c6548530005df7348530045de7348530005dd7348530045dc7348530007ce3248530007cd3248530004fe7608530004fd7608530024fc76085300857e75085300057d75085300067f65085300ae7c650853007dbe7408530005bd74085301e5df7308530045de7308530005dd7308530045dc7308530006ef620853003eec620853000dfa7008530005f970085300875e76d95304055e76d95300865e76d95300075f74d95300055f74d95300075e74d95300075d74d95300055d74d95300075c74d95300075f64d95300075e64d95300075d64d95300075c64d95300075f72d95300075e72d95300075d72d95300075c72d95300075f42d95300075e42d95300075d42d95300075c42d95300075f71d95300075e71d95300075d71d
  | 12 => 0xf620c9302ffce420c930497cd420c9301e5de710c930005dd710c930296dc610c93048f5f510c93000dde700c93000ddc700c930046df600c930047db600c93016fda100c930024fe76d85300857c75d85300067f65d85300067c65d8530004ff75d85300067f75d853001cfe75d8530004fd75d853001cfc75d85300067c75d853001c7c75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d85300067f54d85300067d54d8530146dd73d8530006de43d8530006dd43d853003cfe72d8530004fd72d8530006df32d8530006dd32d85300067f51d8530044fd70d8530146f710d85300857e75985300057d75985300067f65985300067c6598530006f761985300057f75585300857c75585300067f65585300067c6558530005bf745853007dbc7458530005ef7258530005ec72585300857e75185300057d75185300067f65185300067c651853007dbe7418530005bd7418530005ee7218530005ed7218530026f66118530006f561185300067f76545300057e76545300067e76545300047e76545300067d76545300057c76545300067c76545300047c76545303f57f74545303f57d74545303ee7f64545301667e64545303ee7d64545301667c64545300075f73545300075e73545300075d73545300075c735453015e7f63545303ef5f43545303ef5e43545303ef5d43545303ef5c43545300067f62545302567c62545300075f32545300075e32545300075d32545300075c32545302e57f71545300877771545300067f61545300267e61545300267c615453015e7f605453025f7b305453015f5e305453015f5c305453015f78305453015f7a10545300fdde76cc530046de76cc530045df75cc530085de75cc530485dd75cc530045dc75cc5300075f65cc53046f5c65cc530045df74cc53007dde74cc53047ddd74cc530045dc74cc530476df64cc530476dd64cc5304775f54cc5304775d54cc5302fdde72cc530005dd72cc530006df62cc530026de61cc530026dc61cc53046f5f51cc5300075d51cc530047db70cc53000dde70cc53000ddc70cc530047d870cc530046df60cc530047db60cc530147da10cc53000cfe768c5300857e758c5300057d758c5300067f658c53013e7c658c530115dd738c530006f7618c530026f4618c53000dfa708c530005f9708c53000dde768c53012ede768c53000cde768c5301e5df758c530085de758c5301e75e758c5300855e758c530465dd758c5301e75d758c5300055d758c5301e5dc758c5300075f658c53045f5c658c5301e5df748c53007dde748c530455dd748c5301e5dc748c53044f5f548c53044f5d548c5302fdde728c530005dd728c530346dc628c530045de718c5301e6df618c530007d7618c5301e7d4618c5301e75f518c5301e75d518c53000dde708c530
  | 13 => 0x89300067c65d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d89300067f54d89300067d54d89301b6dd73d8930006ee42d8930006ed42d8930024fe71d8930004fd71d89300067f51d8930044fd70d89301b6ef20d89301b6fa10d89300857e75989300057d75989300067f65989300067c659893007dbe7498930005bd7498930006ef62989300057f75589300857c75589300067f65589300067c65589300067f65189300067c651893003eee6218930006ed621893016dde76cc930046de76cc930045df75cc930085de75cc930505dd75cc930045dc75cc9300075f65cc9304ef5c65cc930045df74cc93007dde74cc9304fddd74cc930045dc74cc9304f75f54cc9304f75d54cc93003ede62cc93003edc62cc9304f7ce42cc9304f7cd42cc9301e5de71cc930005dd71cc9304ef5f51cc93000dde70cc93000ddc70cc930046df60cc930047db60cc9301b7da10cc93000cfe768c9300857e758c9300057d758c9300067f658c9301ae7c658c93007dbe748c930005bd748c930185dd738c930006ef628c93003eec628c93000dfa708c930005f9708c93000dde768c93019ede768c93000cde768c9302fddf758c930085de758c9302ff5e758c9300855e758c9304e5dd758c9302ff5d758c9300055d758c9302fddc758c9300075f658c9304cf5c658c9302fddf748c93007dde748c9302ff9e748c93007d9e748c9304dddd748c9302ff9d748c9300059d748c9302fddc748c9304d6df648c9304d6dd648c9304d75f548c9304d75d548c930045de728c9302fedf628c930007cf628c9302ffcc628c9301e5de718c930005dd718c93029edc618c9304cf5f518c93000dde708c93019fda708c9302ffd9708c93000ddc708c930046df608c930047db608c93019fda108c93000cfc764c9300067f654c9301967c654c930006ef624c93003eec624c930005fb704c93000df8704c93000ddc764c93003edc764c93000cdc764c9304c5df754c930085de754c9304c5dd754c930085dc754c9300075f654c9304af5c654c9304bddf744c93007dde744c9304bddd744c93007ddc744c9304b75f544c9304b75d544c930045df724c930047cf724c930007cf624c93003ede624c93003edc624c930007cc624c93003ecc624c930005df714c9301e5dc714c9304af5f514c930007db704c93000dde704c93000ddc704c930187d8704c930046df604c930047db604c930187da104c9301b5de760c930046de760c930045df750c930085de750c9304a5dd750c930045dc750c9300075f650c93048f5c650c930045df740c93007dde740c93049ddd740c930045dc740c930496df640c930496dd640c9304975f540c9304975d540c93019dde720c930047ce720c9302fed
  | 14 => 0x56ddd75887305175d75887300055d7588730515dc7588730515df748873008dde7488730565dd7488730515dc748873055f5f548873055f5d54887305175f51887305175d5188730517cf218873051fd721887300cddf708873000dde70887300cddd708873000ddc70887300cfd71088730005df7648730006df7648730004df7648730045de7648730005dd7648730045dc7648730006dc7648730044dc7648730555df7548730095de7548730555dd7548730095dc754873054ddf744873008dde744873054ddd744873008ddc74487305475f54487305475d5448730007ce6248730007cd6248730547ce4248730547cd424873053f5f51487300075d514873051fd72148730517ce21487300b5df704873000dde704873000ddc7048730515df7608730045de7608730516de7608730044de7608730005dd7608730516dd7608730004dd7608730045dc7608730515df7508730095de75087305175e75087300955e7508730535dd75087305175d75087300055d7508730515dc7508730515df740873008dde74087305179e740873008d9e740873052ddd74087305179d74087300059d7408730515dc74087305275f54087305275d54087305175f51087305175d5108730517cf2108730517d62108730517cd210873051fd5210873009ddf700873000dde700873009fda700873000dda700873009ddd7008730517d97008730005d9700873000ddc70087304057e76d95300867e76d953001c7e76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95303ff5f73d95300875e73d95303ff5d73d95303ff5c73d95300075f43d95300075e43d95300075d43d95300075c43d95300057d71d953050f7b30d95303ff5e30d95303ff5c30d95303ff7830d95303ff7a10d95300067f74d95300047f74d95300067e74d95300067d74d95300047d74d95300067c74d95303fe7f73d953050e7e73d95300865e73d95303fe7d73d95303fe5d73d95303fe7c73d95300067f43d953050e7e43d95300067d43d953050e7c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d953050e7f32d953050e7c32d95300067f71d95300067e71d95300067d71d95300047d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d953050e7f31d953050e7c31d95303fe7f70d95303fe7e70d95303fe7d70d95303fe7c70d95303fe7f40d95303fe7e40d95303fe7d40d95303fe7c40d95303fe7f30d95303fe7e30d95303fe7d30d95303fe5d30d95303fe7c30d95303fe7f20d95303fe7e20d95303fe7d20d95303fe7c20d95303fe7f10d95303fe7e10d95303fe7d10d95303fe7c10d953003cfe76d89300067f65d
  | 15 => 0xd6098b3019fcf2098b3019fcd2098b30045df7658b30005df7558b30095de7558b30005dd7558b30095dc7558b30005df7458b3008dde7458b30005dd7458b3008ddc7458b300075f5458b300075d5458b30045df7258b30047cf6258b3051ede6258b30046dc6258b30047cc6258b30046cc6258b30005df7158b30515dc7158b30046df6158b300075f5158b30185df7058b3000dde7058b3000ddc7058b30186dd6058b30187cf2058b30187cd2058b30045dd7698730515df7598730095de75987305175e75987300955e7598730005dd75987305175d75987300055d7598730515dc7598730515df749873008dde7498730005dd7498730515dc74987300075f54987300075d549873051dde7298730005dd7298730006de6298730046dc6298730045de7198730046df6198730047d76198730047d461987305175f519873012ddd709873012edd609873012fd7109873012fd51098730045df7658730005df7558730095de7558730005dd7558730095dc7558730005df745873008dde7458730005dd745873008ddc7458730046df6458730006dd64587300075f54587300075d5458730005df725873051ddc7258730046df6258730006dd6258730045df7158730047d76158730516de6158730046dc6158730047d461587300075f5158730115df705873000dde705873000ddc7058730116dd6058730117d71058730117d510587300075f765473025f5e76547300075d765473025f5c765473059f5f745473059d5f74547305975e745473059f5d745473059d5d74547305975c745473025f5f64547305975e64547305975d645473025f5c64547300075f72547300075e72547300075d72547300075c725473025f5f62547300075e62547300075d625473025f5c62547305975f42547305975e42547305975d42547305975c42547300975f71547302e55f715473009757715473025f5f61547305175e61547300075d61547305175c61547305975f41547305175e41547305975d41547305175c415473015f5f705473015f5e705473015f5d705473015f5c705473015e5d605473015f5f405473015f5e405473015f5d405473015f5c405473015f5e205473015f5c205473015f5f105473015f5e105473015f5c105473051ddf76c8730045de76c8730005dd76c8730045dc76c873051ddf75c8730095de75c873058ddd75c873051ddc75c873051ddf74c873008dde74c8730585dd74c873051ddc74c873057f5f54c873057f5d54c873051fce62c8730007cd62c873051fce42c873057fcd42c87305775f51c87300075d51c87300e5df70c873000dde70c87300e5dd70c873000ddc70c87300e7cf20c8730515df7688730045de7688730005dd7688730045dc7688730515df7588730095de75887305175e75887300955e7588730
  | 16 => 0x8730046df3258730006dd3258730046f771587300067f5158730046f73158730046dc3158730046f43158730046fa3058730046f93058730116f710587300067f765473025e7e76547300067d765473025e7c765473059d7f745473059d7d745473025e7f64547301667e64547305967d645473025e7c64547300075f735473025f5e73547300075d735473025f5c735473015e7e63547305975f435473025f5e43547305975d435473025f5c43547302567e62547300067d625473025f5f32547300075e32547300075d325473025f5c32547302e57f71547300977771547300267e61547300067d61547300267c615473025f5f31547305175c315473015e7d605473015f5e305473015f7a305473015f5c3054730045dd768c730516dd768c730515df758c730095de758c7305175e758c7300955e758c7305d5dd758c7305175d758c7300055d758c730515dc758c730515df748c73008dde748c7305cddd748c730515dc748c7305c75f548c7305c75d548c73051dde728c730005dd728c730346de628c730047d6718c730046df618c730516dd618c7305175f518c7305175d518c73000dde708c73000ddc708c730045df764c730006df764c7305bddf754c730095de754c7305bddd754c730095dc754c7305b5df744c73008dde744c7305b5dd744c73008ddc744c730046df644c7305aedd644c7305af5f544c7305af5d544c730005df724c73051ddc724c730006dd624c730047d7714c730026de614c730026dc614c7305a75f514c7300075d514c73000dde704c73000ddc704c73003cff76c8730044fe76c8730004fd76c873051ddf73c8730045de73c8730005dd73c8730045dc73c873003eee62c8730006ed62c873051fce32c8730007cd32c8730024ff7688730044fe7688730004fd76887300957e75887300057d7588730515df7388730045de7388730005dd7388730045dc7388730004ff7648730004fd7648730044fc7648730005df7348730045de7348730005dd7348730045dc734873003eee6248730006ed6248730007ce3248730007cd3248730024ff7608730044fe7608730004fd76087300957e75087300057d750873008dbe7408730005bd7408730515df7308730045de7308730005dd7308730045dc730873000dfa7008730005f97008730045dd7698b3051ddf7598b30095de7598b3051f5e7598b300955e7598b30005dd7598b3051f5d7598b300055d7598b3051ddc7598b3051ddf7498b3008dde7498b3051f9e7498b3008d9e7498b30005dd7498b3051f9d7498b300059d7498b3051ddc7498b30046df6498b30006dd6498b300075f5498b300075d5498b30045de7298b30046df6298b30047cf6298b30047cc6298b30515de7198b30005dd7198b30046dc6198b300075f5198b3019ddd7098b3019ed
  | 17 => 0x6f9505802109ef85058021006fb405802109efa4058021006f9405802109ef8405802109efa305802109ef8305802103efb205802103ef82058021026fb1058021026f81058021006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb54580210067b5458021006fa5458021006f95458021006795458021006f85458021006fb7358021006fa7358021006da7358021006f97358021006d97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f8435802103efb725802103efa725802103ef8725802103efb525802103efa525802103ef9525802103ef8525802103efb425802103efa425802103ef9425802103ef8425802103efb325802103efa325802103ef9325802103ef83258021026fb7158021026fa7158021026f87158021026fb51580210267b5158021026fa5158021026f95158021026795158021026f85158021026fb4158021026fa4158021026f94158021026f84158021026fb3158021026fa3158021026f93158021026f83158021026fb2158021026eb2158021026fa2158021026f22158021026f92158021026e9215802103ef12158021026f82158021004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b30014fe7458b30004fd7458b30014fc7458b300067f5458b300067d5458b3000cfc7358b30046dc7358b3000cdc7358b30046ef7258b30046ef3258b30046dc3258b30046ec3258b30046cc3258b30004ff7158b30024fc7158b300067f5158b30046df3158b30186ef2058b30045dd768cb3051edd768cb3051ddf758cb30095de758cb3051f5e758cb300955e758cb30615dd758cb3051f5d758cb300055d758cb3051ddc758cb3051ddf748cb3008dde748cb3051f9e748cb3008d9e748cb3060ddd748cb3051f9d748cb300059d748cb3051ddc748cb30046df648cb30606dd648cb306075f548cb306075d548cb30047ce728cb30046df628cb3051edd628cb30515de718cb30005dd718cb3029ede618cb305ff5f518cb3000dde708cb3000ddc708cb30045df764cb30006df764cb305f5df754cb30095de754cb305f5dd754cb30095dc754cb305eddf744cb3008dde744cb305eddd744cb3008ddc744cb305e75f544cb305e75d544cb30047cf724cb3003ede624cb3003edc624cb30005df714cb30515dc714cb305df5f514cb3000dde704cb3000ddc704cb30004ff755873001cfe7558730004fd755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc74587300067f54587300067d545873000cfc7358730046dc735873000cdc7358730046de4358730006dd4358730004ff725873003cfc725
  | 18 => 0xd4298c2103edc4298c21026df7198c21026de7198c21026dd7198c21026dc7198c21026df5198c210265f5198c21026de5198c21026dd5198c210265d5198c21026dc5198c21026df4198c21026de4198c21026dd4198c21026dc4198c21026df2198c21026de2198c21026dd2198c21026dc2198c21046df7098c21046de7098c21046dd7098c21004dd7098c21046dc7098c21006df5098c21006de5098c21006dd5098c21006dc5098c21006df4098c21006de4098c21006dd4098c21006dc4098c2103edf2098c2103ede2098c2103edd2098c2103edc2098c21026df1098c21026de1098c21026dd1098c21026dc1098c21004ff7558c2101cfe7558c21004fd7558c2101cfc7558c21004ff7458c21014fe7458c21004fd7458c21014fc7458c210067f5458c210067d5458c21024ff7358c21026df7358c21006df5358c21006de5358c21006dd5358c21006dc5358c21006df4358c21006de4358c21006dd4358c21006dc4358c2103cfe7258c2103cfc7258c2103ede3258c2103edc3258c21024fe7158c21024fc7158c210267f5158c210267d5158c21026de3158c21026dc3158c21026ef2158c21026ed2158c21004ff7058c2100cfe7058c2100cfc7058c21006de3058c21006dc3058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c210065f5458c21006de5458c21006dd5458c210065d5458c21006dc5458c2103edf7258c2103ede7258c2103edd7258c2103edc7258c2103edf5258c2103ede5258c2103edd5258c2103edc5258c2103edf4258c2103ede4258c2103edd4258c2103edc4258c21026df7158c21026de7158c21026dd7158c21026dc7158c21026df5158c210265f5158c21026de5158c21026dd5158c210265d5158c21026dc5158c21026df4158c21026de4158c21026dd4158c21026dc4158c21026df2158c21026cf2158c21026de2158c21026dd2158c21026cd2158c21026dc2158c21006df7058c21004df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21006df4058c21006de4058c21006dd4058c21006dc4058c2103edf2058c2103ede2058c2103edd2058c2103edc2058c21026df1058c21026de1058c21026dd1058c21026dc1058c21004ff755802101cfe7558021004fd755802101cfc7558021004ff7458021014fe7458021004fd7458021014fc74580210067f54580210067d5458021004ff7358021006de7358021006dd7358021044fc735802100cfd725802100cfd71580210267f51580210267d5158021026ef2158021026f62158021026ed215802103ef52158021024ff7058021026fb7058021006fb505802109efa5058021
  | 19 => 0x8121044fe73d8121004fd73d8121006dc73d8121024fd72d812100cfc72d8121006ee42d8121006ed42d812103cfd71d812100cfc71d81210067f51d81210067d51d81210b6fa20d81210b6fa10d81210057f75581210c57c7558121005bf74581210bdbc7458121005df7358121005dc7358121006df6358121006dc63581210b6f860581210067f74594210047f74594210067e74594210067d74594210047d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067f43594210067e43594210067d43594210067c435942103e7f725942103e7e725942103e7d725942103e7c725942103e7f425942103e7e425942103e7d425942103e7c425942103e7f325942103e7e325942103e7d325942103e7c32594210267f71594210267e71594210267d71594210267c71594210267f41594210267e41594210267d41594210267c41594210267f31594210267e31594210267d31594210267c31594210267f21594210267e21594210267d21594210267c21594210067f70594210067e70594210067d70594210067c70594210067f40594210067e40594210067d40594210067c40594210067e30594210067c305942103e7f205942103e7e205942103e7d205942103e7c20594210267f10594210267e10594210267d10594210267c1059421006bf7559021006be75590210063e7559021006bd75590210063d7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bd5359021006bc535902103ebf725902103ebe725902103ebd725902103ebc725902103ebf525902103ebe525902103ebd525902103ebc525902103ebf325902103ebe325902103ebd325902103ebc3259021026bf7159021026be7159021026bd7159021026bc7159021026bf51590210263f5159021026be5159021026bd51590210263d5159021026bc5159021026bf3159021026be3159021026bd3159021026bc3159021026bf2159021026af2159021026be2159021026bd2159021026ad2159021026bc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bd5059021006bc5059021006be3059021006bc305902103ebf205902103ebe205902103ebd205902103ebc2059021026bf1059021026be1059021026bd1059021026bc1059021046df7598c21046de7598c21046dd7598c21046dc7598c21046df7498c21046de7498c21046dd7498c21046dc7498c21006df5498c210065f5498c21006de5498c21006dd5498c210065d5498c21006dc5498c2103edf7298c2103ede7298c2103edd7298c2103edc7298c2103edf5298c2103ede5298c2103edd5298c2103edc5298c2103edf4298c2103ede4298c2103ed
  | 20 => 0x33edc5218d21006df4218d2133ede4218d21006ce4218d21006dd4218d21006cd4218d2133edc4218d21046df7118d21046de7118d21046dd7118d21046dc7118d21006df5118d210065f5118d21296de5118d21006dd5118d21296dc5118d21006df4118d21296de4118d21006dd4118d21296dc4118d2133edf2118d21296de2118d21006dd2118d21296dc2118d21046df7018d21046de7018d21046dd7018d21004dd7018d21046dc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d21006df4018d21006de4018d21006dd4018d21006dc4018d2133edf2018d21006de2018d2133edc2018d21296df1018d21006de1018d21296dc1018d21024fe76cc921024fc76cc921006df63cc921046dc63cc921025f671cc921005f571cc921005ee768c92103eee768c92103f6e758c92103f6d758c92103def748c92103fae748c921655ed748c92103fad748c921005ad748c92164f6f548c92164f6d548c92163ded738c921007cf638c921046ee638c921046ec638c921007cc638c921046cc638c92164fce438c92164fcd438c921025ee718c921025ec718c92103eef618c92103fe7618c9216476f518c92129fce318c92129fcc318c921005ed708c921024fc764c921006df634c921046dc634c92103fcc324c921005f7714c921025f4714c921025ec764c921046ec764c921024ec764c92163def744c92163ded744c9216376f544c9216376d544c92103def734c92103fcf734c921007cf634c921046ee634c921046ec634c921007cc634c921007e7714c921025ee714c921025ec714c921007e4714c92103eef614c92103fe7614c92162f6f514c921005ef704c92101e7f76545212567e76545210c67d765452101e7c76545216257f74545216257d745452161e7f64545211667e645452161e7d64545211667c64545210067f63545210075f63545210065f635452125e7e63545210067d635452125e7c63545210075c63545210065c63545210076f72545210076c72545210267f625452161f6e425452161f6d42545210076e32545210076d32545210257f71545210c77771545210267f61545210277631545212577721545210276e21545210276c215452102774215452102764215452115e7e605452115e7c605452102777105452103cfe76cc52103cfc76cc521006df63cc521046dc63cc52103dee72cc521005ed72cc521007cd32cc521044ff764c521004fd764c52103cfc764c521006df634c521046dc634c521005ef724c52103dec724c521007cd324c52100775514c52100cfe76d8121006df63d8121006dc63d81210b6fa60d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d81210067f54d81210067d54d8121006df73d
  | 21 => 0xd54d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21006df43d8d21006de43d8d21006dd43d8d21006dc43d8d210067f51d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d21044de76d8d210075e75d8d210075d75d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210075f54d8d210075d54d8d2129fcf72d8d21007ce42d8d21007cd42d8d210075f51d8d21347d721d8d2129fce21d8d2129fcc21d8d21347d421d8d21005dd70d8d21006de60d8d21006dc60d8d21006df75d8d21006de75d8d210065e75d8d21006dd75d8d210065d75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d210065f54d8d21006de54d8d21006dd54d8d210065d54d8d21006dc54d8d2129edf72d8d21346de72d8d21006dd72d8d21346dc72d8d21006df52d8d21346de52d8d21006dd52d8d21346dc52d8d21006df42d8d21346de42d8d21006dd42d8d21346dc42d8d21346df71d8d2129ede71d8d21006dd71d8d2129edc71d8d21006df51d8d210065f51d8d2129ede51d8d21006dd51d8d2129edc51d8d21006df41d8d2129ede41d8d21006dd41d8d2129edc41d8d21346df21d8d2129ede21d8d2129edc21d8d21006df70d8d21006de70d8d21006dd70d8d21004dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d21346df20d8d21006de20d8d21346dc20d8d2129edf10d8d21006de10d8d2129edc10d8d21006df6398d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d210067f5458d210067d5458d21006df7358d21004ff7258d21006ef7258d21004ff7158d21006f77158d210067f5158d21004ff7058d2100cfe7058d2100cfc7058d21004fe7618d21046de6318d21006dd6318d21005de7618d21006de7618d21004de7618d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d210075f5418d210075d5418d21007cd7218d21007ce4218d21007cd4218d210075f5118d2133fd72118d21297ce2118d21297cc2118d2133fd42118d21005dd7018d21006de6018d21006dc6018d21046df7518d21046de7518d21046dd7518d21046dc7518d21046df7418d21046de7418d21046dd7418d21046dc7418d21006df5418d210065f5418d21006de5418d21006dd5418d210065d5418d21006dc5418d21046df7218d21046de7218d21046dd7218d21046cd7218d21046dc7218d21006df5218d2133ede5218d21006dd5218d21
  | 22 => 0xc72103dee72cc721005ed72cc721007cd32cc721044ff764c721046de634c721006dd634c721005ef724c72103dec724c721007cd324c721004ff75583210067f75583210047f755832101cfe7558321004fd755832101cfc75583210067c755832101c7c7558321004ff7458321014fe7458321004fd7458321014fc74583210067f54583210067d5458321004ff7358321044fc7358321024fc725832103eee4258321006ed42583210067f51583210067d515832103ef6215832103ef5215832103efb705832103efb205832103ef820583210e6fa10583210067f74596210047f74596210067e74596210067d74596210047d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067d43596210067c43596210de7f72596212567e72596210067d72596212567c72596210067f42596212567e42596210067d42596212567c42596212567e32596212567c32596210267f71596210267e71596210267d71596210267c71596210267f41596210267e41596210267d41596210267c41596210267f31596210267e31596210267d31596210267c31596210267f21596210267e21596210267d21596210267c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067e40596210067d40596210067c40596210067e30596210067c30596212567f20596210067e20596212567c20596210267f10596210267710596210267e10596210267d10596210267c1059621004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e210067f5458e210067d5458e21026df7358e21006de4358e21006dd4358e21024fc7158e210267f5158e210267d5158e21026de3158e21026dc3158e21026ef2158e21026ed2158e21004ff7058e2100cfe7058e2100cfc7058e211c67e65cca210067d65cca21046de63cca21006dd63cca21025f671cca21005f571cca21044ff764ca211967e654ca210067d654ca21046de634ca21006dd634ca21005f7714ca21025f4714ca21004ff755822101cfe7558221004fd755822101cfc7558221004ff7458221014fe7458221004fd7458221014fc74582210067f54582210067d5458221004ff7358221044fc7358221024fc71582210267f51582210267d5158221026ef2158221026ed2158221026fb70582210cefa4058221006f940582210cefa30582210cefa2058221026fb1058221026f81058221044fe76d8d210c57e75d8d210057d75d8d21004ff75d8d2101cfe75d8d210067e75d8d2101c7e75d8d21004fd75d8d210067d75d8d210047d75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d210067f54d8d210067
  | 23 => 0x5dd708c831047da608c831047d9608c831004ff755803101cfe7558031004fd755803101cfc7558031004ff7458031014fe7458031004fd7458031014fc74580310067f54580310067d5458031046de735803100cfd7358031004ff725803103cfc7258031006de3258031046dc32580310267f51580310267d5158031026df3158031026dd3158031024ff7058031026fb7058031006fb50580310fefa5058031006f950580310fef85058031006fb40580310fefa4058031006f940580310fef84058031046df3058031046fb3058031046db3058031046f830580310fefa20580310fef82058031026fb1058031026f81058031006fb7558031006fa7558031006f97558031006f87558031006fb7458031006fa7458031006f97458031006f87458031006fb54580310067b5458031006fa5458031006f95458031006795458031006f85458031046fb7358031046fa7358031046da7358031046f87358031046fb5358031046fa5358031046f95358031046f85358031046fb4358031046fa4358031046f94358031046f84358031006fb7258031006fa7258031006f97258031006f87258031006fb5258031006fa5258031006f95258031006f85258031006fb4258031006fa4258031006f94258031006f84258031046fb3258031046fa3258031006da3258031046f93258031046f83258031046d83258031026fb7158031026fa7158031026f87158031026fb51580310267b5158031026fa5158031026f95158031026795158031026f85158031026fb4158031026fa4158031026f94158031026f84158031026fb3158031026db3158031026fa3158031026f93158031026d93158031026f83158031026fb2158031026fa2158031026f92158031026f82158031004ff7558f2101cfe7558f21004fd7558f2101cfc7558f21004ff7458f21014fe7458f21004fd7458f21014fc7458f210067f5458f210067d5458f2103edf7358f21024fc7258f2103ede3258f2103edc3258f210067f5158f21004ff7058f2100cfe7058f2100cfc7058f2103def764cb21006ef764cb2167def744cb2167ded744cb216776f544cb216776d544cb2103fcf734cb2103fcf634cb21046ee634cb2103eec634cb2103fcc634cb21025ee714cb21025ec714cb2166f6f514cb21005ef704cb2101e7f765472101e7c76547216657f74547216657d74547212567f64547211667e645472165e7d64547212567c64547212567f635472125e7e63547210067d63547212567c63547210076f72547212576c72547210267e62547212576e425472165f6d42547212576e32547210076d32547210257f71547210f77771547210267d61547210276e21547210277621547210276c215472115e7e605472115e7c6054721027771054721046de63cc721006dd63c
  | 24 => 0xd4398831046ec4398831026ef7198831026ee7198831026ed7198831026ec7198831026ef51988310266f5198831026ee5198831026ed51988310266d5198831026ec5198831026ef4198831026ee4198831026ed4198831026ec4198831026ef3198831026ee3198831026ed3198831026ec319883103eef709883103eee709883103eed709883103eec7098831006ef5098831006ee5098831006ed5098831006ec5098831006ef4098831006ee4098831006ed4098831006ec4098831046ef3098831046cf3098831046ee3098831046ed3098831046ec3098831026ef1098831026ee1098831026ed1098831026ec1098831004ff755883101cfe7558831004fd755883101cfc7558831004ff7458831014fe7458831004fd7458831014fc74588310067f54588310067d5458831026ef7258831006ef5258831006ee5258831006ed5258831006ec5258831006ef4258831006ee4258831006ed4258831006ec4258831046ef3258831046dc3258831046ec3258831046cc32588310267f51588310267d5158831026df3158831026dd3158831026ee2158831026ec2158831004ff705883100cfe705883100cfc7058831046df3058831006ee2058831006ec2058831006ef7558831006ee7558831006ed7558831006ec7558831006ef7458831006ee7458831006ed7458831006ec7458831006ef54588310066f5458831006ee5458831006ed54588310066d5458831006ec5458831046ef7358831046ee7358831046ec7358831046ef5358831046ee5358831046ed5358831046ec5358831046ef4358831046ee4358831046ed4358831046ec4358831026ef7158831026ee7158831026ec7158831026ef51588310266f5158831026ee5158831026ed51588310266d5158831026ec5158831026ef4158831026ee4158831026ed4158831026ec4158831026ef3158831026cf3158831026ee3158831026ed3158831026cd3158831026ec3158831006ef7058831006ee7058831006ed7058831006ec7058831006ef5058831006ee5058831006ed5058831006ec5058831006ef4058831006ee4058831006ed4058831006ec4058831046ef3058831046cf3058831046ee3058831046ed3058831046ec3058831026ef1058831026ee1058831026ed1058831026ec1058831045dd768c83133edd768c831004dd768c83133f5e758c83133f5d758c8310475e658c8310475d658c83133f9e748c83133f9d748c831046df648c8310479e648c831686dd648c8310479d648c8310069d648c8316875f548c8316875d548c831045de728c831047ce728c831046df628c831047ce628c83133edd628c831047cd628c831006cd628c83129ddf718c83129ddd718c83129ede618c831047d6618c83129f5f518c83129f5d518c83129fcf218c831
  | 25 => 0x8131006dd43d813103cfe72d8131004fd72d8131006df32d8131006dd32d8131044fd71d81310067f51d81310067d51d8131516de31d8131516dc31d8131116fa30d8131116fa10d81310057f75581311257c7558131005bf745813111dbc7458131005ef7258131005ec7258131116f860581310067f74594310047f74594310067e74594310067d74594310047d74594310067c74594310467f73594310467e73594310467d73594310467c73594310467f43594310467e43594310467d43594310467c43594310067f72594310067e72594310067d72594310067c72594310067f42594310067e42594310067d42594310067c42594310467f32594310467e32594310467d32594310467c32594310267f71594310267e71594310267d71594310267c71594310267f41594310267e41594310267d41594310267c41594310267f31594310267e31594310267d31594310267c31594310267f21594310267e21594310267d21594310267c21594310067f70594310067e70594310067d70594310067c70594310067f40594310067e40594310067d40594310067c40594310467f30594310465f30594310467e30594310467d30594310467c30594310067e20594310067c20594310267f10594310267e10594310267d10594310267c1059431006bf7559031006be75590310063e7559031006bd75590310063d7559031006bc7559031046bf7359031046be7359031046bd7359031046bc7359031046bf5359031046be5359031046bd5359031046bc5359031006bf7259031006be7259031006bd7259031006bc7259031006bf5259031006be5259031006bd5259031006bc5259031046bf3259031046be3259031046bd3259031046bc32590310469c3259031026bf7159031026be7159031026bd7159031026bc7159031026bf51590310263f5159031026be5159031026bd51590310263d5159031026bc5159031026bf31590310269f3159031026be3159031026bd31590310269d3159031026bc3159031026bf2159031026be2159031026bd2159031026bc2159031006bf7059031006be7059031006bd7059031006bc7059031006bf5059031006be5059031006bd5059031006bc5059031046bf30590310469f3059031046be3059031046bd3059031046bc3059031006be2059031006bc2059031026bf1059031026be1059031026bd1059031026bc105903103eef759883103eee759883103eed759883103eec759883103eef749883103eee749883103eed749883103eec7498831006ef54988310066f5498831006ee5498831006ed54988310066d5498831006ec549883103eef739883103eee739883103eed739883103eec7398831046ef5398831046ee5398831046ed5398831046ec5398831046ef4398831046ee4398831046e
  | 26 => 0x2975d650ca31296df640ca316cedd640ca316cf5f540ca316cf5d540ca31047ce720ca31296df620ca31346dd620ca31347ce420ca316cfcd420ca31045df710ca31295dd710ca31047d6610ca312975f510ca312975d510ca31005dd700ca31004ff755823101cfe7558231004fd755823101cfc7558231004ff7458231014fe7458231004fd7458231014fc74582310067f54582310067d5458231006dd7358231004ff725823103cfc7258231006de3258231006dc3258231024fc71582310267f51582310267d5158231026df3158231026dd3158231026fb705823112efa4058231006f9405823112efa305823112efa2058231026fb1058231026f81058231004ff75d893101cfe75d8931004fd75d893101cfc75d8931004ff74d8931014fe74d8931004fd74d8931014fc74d89310067f54d89310067d54d8931006ee52d8931006ed52d8931006ee42d8931006ed42d89310067f51d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d89311257e75989310057d759893111dbe7498931005bd749893129edf6398931006ef6298931296df631893103eee6218931006ed6218931005de76cc931046de76cc931004de76cc931045df74cc9316c5dd74cc9316bf5f54cc9316bf5d54cc93103ede62cc93103edc62cc9316bfce42cc9316bfcd42cc931025de71cc931025dc71cc931046df61cc931047d761cc9316b75f51cc931005dd70cc931024fe768c9311257e758c9310057d758c93111dbe748c931005bd748c9316addd738c931006ef628c93103eec628c931025f6718c931005f5718c931024fc764c931006ef624c93103eec624c931047cc324c931005f7714c931025f4714c931024dc764c9316addf744c9316addd744c9316a75f544c9316a75d544c931045df724c931047cf724c931007cf624c93103ede624c93103edc624c931007cc624c931007d7714c931025de714c931025dc714c931007d4714c931046df614c931047d7614c93169f5f514c931005df704c93101e7f765453125e7e76545311267d765453101e7c76545316957f74545316957d745453168e7f64545311667e645453168e7d64545311667c64545310075f73545310075c73545310267f635453168f5e435453168f5d43545310067f62545312567c62545310075f32545310075d32545310257f71545311277771545310267f615453125f7731545310275e31545310275c315453102774315453102754315453102776215453115e7e605453115e7c605453102777105453100cfe76d8131116fa60d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d81310067f54d81310067d54d8131516df73d8131024fd73d813100cfc73d8131006de43d
  | 27 => 0xe635473125f5e43547316df5d43547312567e62547310067d625473125f5f32547310075d32547310257f71547311577771547310267d61547310275e31547310277631547310275c315473115e7e605473115e7c6054731027771054731004ff75583310067f75583310047f755833101cfe7558331004fd755833101cfc75583310067c755833101c7c7558331004ff7458331014fe7458331004fd7458331014fc74583310067f54583310067d5458331046de7358331024fc7358331046de4358331006dd4358331004ff725833103cfc7258331046df3258331006dd32583310067f51583310067d51583311e6de3158331046dc3158331046fb7058331046df3058331046fb3058331046db3058331046f83058331146fa10583310067f74596310047f74596310067e74596310067d74596310047d74596310067c745963113e7f735963125e7e73596310067d735963125e7c73596310067f435963125e7e43596310067d435963125e7c43596310067f72596310067e72596310067d72596310067c72596310067f42596310067e42596310067d42596310067c425963125e7f325963125e7c32596310267f71596310267e71596310267d71596310267c71596310267f41596310267e41596310267d41596310267c41596310267f31596310267e31596310267d31596310267c31596310267f21596310267e21596310267d21596310267c21596310067f70596310067e70596310067d70596310067c70596310067f40596310067e40596310067d40596310067c405963125e7f30596310067e305963125e7c30596310067e20596310067c20596310267f10596310267e10596310267d10596310267c1059631004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31004fd7458a31014fc7458a310067f5458a310067d5458a31026ef7258a31006ee4258a31006ed4258a31024fc7158a310267f5158a310267d5158a31026df3158a31026dd3158a31026ee2158a31026ec2158a31004ff7058a3100cfe7058a3100cfc7058a3113d7e758ca310057d758ca311ae7e658ca310067d658ca31135be748ca31005bd748ca3103eee628ca31006ed628ca31025f6718ca31005f5718ca313475e758ca313475d758ca3129f5e658ca3129f5d658ca313479e748ca313479d748ca3129edf648ca316d6dd648ca316d75f548ca316d75d548ca31045de728ca3129edf628ca3129fce628ca31346dd628ca3129fcd628ca3129fd6718ca3129ddd718ca31347d5718ca31046de618ca3129f5f518ca3129f5d518ca3129fcf218ca31005dd708ca3103cff764ca311967e654ca310067d654ca3103eee624ca31006ed624ca31005f7714ca31025f4714ca31295dd760ca31046dd760ca312975e650ca31
  | 28 => 0xc9512557c768c9512557f748c9511657e748c9512573e748c9511653e748c95173d7d748c9512573d748c9510053d748c9512557c748c9517367f648c9517367d648c9511957d738c9510075f638c9510075c638c9517375e438c9517375d438c9512557e728c9512575f328c95125f6f328c9510257e718c9510057d718c9510257c718c95170e7f618c9511af77618c95115d7e708c9510057d708c95115d7c708c9510057f764c9510057e764c9510057d764c9510057c764c95172d7f744c9511657e744c95172d7d744c9511657c744c9517267f644c9517267d644c95125f6f324c9512575e324c9510057f714c9510257e714c9510257c714c9511967f614c95119777614c9510057f704c95115d7e704c95115d7c704c9512557f760c9510057e760c9510057d760c9512557c760c9512557f740c9511657e740c95171d7d740c9512557c740c9517167f640c9517167d640c95125d7e730c9510075f630c95125f5c630c95125f5e430c9517175d430c9512557e720c9512576e420c9517176d420c9512575f320c9512576e320c9512575d320c95125f6d320c9510257e710c95125776710c95102576710c9510057d710c95125775710c95100575710c9510257c710c95170e7f610c95117f77610c9512975c310c95115d7e700c9510057d700c95115d7c700c95115d7e76d81510057f74d81511657e74d81510057d74d81511657c74d81510067f64d81510067d64d815125d7e73d81510057d73d81512557e72d81510057d72d81510067f62d81510067d62d81510577771d81510257e71d815101d7d71d81510567f61d81510577761d815115e7e60d815115f7a60d815115e7c60d815115f7a10d81510057f74581511657e74581510057d74581511657c74581510067f64581510067d64581510057f735815125d7c73581510057f72581512557c72581510067f62581510067d62581517057f71581510077771581517057771581510367f615815103777615815115d7f70581510077b605815115e7e605815115e7c605815115f786058151004ff7558b3101cfe7558b31004fd7558b3101cfc7558b31004ff7458b31014fe7458b31004fd7458b31014fc7458b310067f5458b310067d5458b31024fc7358b31046ef7258b31046ef3258b31046ec3258b310067f5158b31004ff7058b3100cfe7058b3100cfc7058b31046df3058b31045df764cb31006df764cb316fddf744cb316fddd744cb316f75f544cb316f75d544cb31047cf724cb31047cf624cb3103ede624cb3103edc624cb31047cc624cb31025de714cb31025dc714cb316ef5f514cb31005df704cb3101e7f765473101e7c76547316e57f74547316e57d745473125e7f64547311667e64547316de7d645473125e7c64547310075f735473125f5c73547310267
  | 29 => 0x67d6498d5125d7e7398d5125e7f6398d510075f6398d512557e7298d510057d7298d511257d7198d5125f757198d51125757198d517467f6198d51157776198d5115d7e7098d510057d7098d5115d7c7098d510067e6098d510067c6098d510057f7458d511657e7458d510057d7458d511657c7458d510067f6458d510067d6458d510075f6358d5125e7e6358d510057f7258d512557c7258d511557f7158d51007777158d51155777158d511267f6158d51127776158d510057f7058d5115d7e7058d5115d7c7058d5113d7e7618d5125d7f7418d511657e7418d5125f3e7418d511653e7418d510057d7418d5125f3d7418d510053d7418d5125d7c7418d510067f6418d510067d6418d5125e7f6318d5125f5e6318d5125e7d6318d510075d6318d510075f4318d5125f5c4318d512557e7218d510057d7218d517467f6118d5110f776118d5115d7e7018d510057d7018d5115d7c7018d510067e6018d510067c6018d510057f74d89511657e74d89510057d74d89511657c74d89510067f64d89510067d64d895125d7e73d89510057d73d89510067e63d89510067c63d89510de7f61d89510df7761d895115d7e70d89510057d70d895115d7c70d89512557f74989511657e74989510057d74989512557c74989510067f64989510067d649895125d7e73989510057d73989512557e72989512567f62989510076f62989510c57d71989512577571989510c575719895170e7f61989510f777619895115d7e70989510057d709895115d7c70989510067e60989510067c60989510057f74589511657e74589510057d74589511657c74589510067f64589510067d64589510057f73589510075f73589510055f735895125d7c73589510075c73589510055c73589510067e63589510067c63589510076f62589512567e62589510f57f71589510077771589510f57771589510c67f61589510c77761589510057f705895115d7e705895115d7c70589510dd7e76189512557f74189511657e74189512573e74189511653e74189510057d74189512573d74189510053d74189512557c74189510067f64189510067d641895125d7e73189510057d73189512567f62189512576e62189512567d62189510076d621895170e7f61189510af77611895115d7e70189510057d701895115d7c70189510067e60189510067c601895125d7f76cc9510057e76cc9510057d76cc95125d7c76cc95125d7f74cc9511657e74cc9517557d74cc95125d7c74cc95174e7f64cc95174e7d64cc95174f6e42cc95174f6d42cc9510257e71cc9510057d71cc9510257c71cc9517467f61cc9511c77761cc95115d7e70cc9510057d70cc95115d7c70cc9512557f768c9510057e768c9512567e768c9510047e768c9510057d768c9512567d768c9510047d768
  | 30 => 0x42158632004ff705863200cfe705863200cfc7058632004ff755823201cfe7558232004fd755823201cfc7558232004ff7458232014fe7458232004fd7458232014fc74582320067f54582320067d5458232006dd7358232006de4358232006dd435823203cfc725823203edf325823203edd3258232004ff7158232024fc71582320067f515823203eef215823203efb705823219efa305823203efb205823203ef8205823219efa1058232004ff75d853201cfe75d8532004fd75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d85320067f54d85320067d54d85320067f51d853200cfe70d8532004fd70d853200cfc70d85321957e75985320057d7598532006f761985321957e75185320057d751853218dbe7418532005bd741853229edf6318532026f66118532006f56118532185fa7018532005f9701853200cfe76d8132186fa60d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d81320067f54d81320067d54d813251edf73d813203cfd73d8132044fd72d813251ede32d813251edc32d8132024fe71d8132004fd71d81320067f51d8132186fa30d8132186fa20d81320057f75581321957c7558132186f86058132004ff755843201cfe7558432004fd755843201cfc7558432004ff7458432014fe7458432004fd7458432014fc74584320067f54584320067d5458432046de4358432006dd435843203eee4258432006ed425843203edf325843203eee325843203edd3258432046ed325843203ef771584320067f5158432006f65158432006f55158432006f64158432006f54158432046f73158432046dc3158432046f4315843203ef7215843203ef42158432004ff705843200cfe705843200cfc7058432046df3058432004ff75580320067f75580320047f755803201cfe7558032004fd755803201cfc75580320067c755803201c7c7558032004ff7458032014fe7458032004fd7458032014fc74580320067f54580320067d5458032046de7358032046de4358032006dd435803203eee4258032006ed425803203edf325803203edd3258032004ff7158032024fc71580320067f5158032046dc315803203cff705803203efb705803216efa5058032006f9505803216efa4058032006f94058032046df3058032046fb3058032046db3058032046f8305803203efb205803203ef8205803216efa10580320057f74d8d511657e74d8d510057d74d8d511657c74d8d510067f64d8d510067d64d8d510075f43d8d510075c43d8d512557e72d8d510057d72d8d5113e7f61d8d5113f7761d8d5115d7e70d8d510057d70d8d5115d7c70d8d5125d7f7498d511657e7498d510057d7498d5125d7c7498d510067f6498d51
  | 31 => 0x873200cfe705873200cfc7058732046df3058732004ff755833201cfe7558332004fd755833201cfc7558332004ff7458332014fe7458332004fd7458332014fc74583320067f54583320067d5458332046de735833203cfc7358332006ee4258332006ed42583322fede3258332046dc3258332004ff7158332024fc71583320067f5158332046df3158332046fb7058332046df3058332046fb3058332046db3058332046f830583321b6fa20583321b6fa10583320067f74596320047f74596320067e74596320067d74596320047d74596320067c74596321ae7f73596327667e73596320067d73596327667c73596320067f43596327667e43596320067d43596327667c435963203e7f725963203e7e725963203e7d725963203e7c725963203e7f425963203e7e425963203e7d425963203e7c425963203e7f325963203e7e325963203e7d325963203e7c32596320067f71596320047f71596320067e71596320067d71596320067c71596320067f41596320067e41596320067d41596320067c41596327667f31596327667c315963203e7f215963203e7e215963203e7d215963203e7c21596320067f70596320067e70596320067d70596320067c70596320067f40596320067e40596320067d40596320067c40596327667f30596320067e30596327667c305963203e7f205963203e7e205963203e7d205963203e7c20596320067e10596320067c1059632006bf7559232006be75592320063e7559232006bd75592320063d7559232006bc75592321a6bf735923275ebe7359232006bd735923275ebc7359232006bf535923275ebe5359232006bd535923275ebc535923203ebf725923203ebe725923203ebd725923203ebc725923203ebf525923203ebe525923203ebd525923203ebc525923203ebf325923275eaf325923203ebe325923203ebd325923203ebc325923203eac3259232006bf7159232006be7159232006bd7159232006bc7159232006bf51592320063f5159232006be5159232006bd5159232006bc515923275ebf315923275ebc315923203ebf215923203eaf215923203ebe215923203ebd215923203ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232006bc505923275ebf3059232006be305923275ebc305923203ebf205923203ebe205923203ebd205923203ebc2059232006be1059232006bc1059232004ff755863201cfe75586320067e755863201c7e7558632004fd75586320067d755863201cfc7558632004ff7458632014fe7458632004fd7458632014fc74586320067f54586320067d5458632006de4358632006dd435863203cfc725863203edf325863203edd325863203ef771586320067f515863203ef7215863203ef
  | 32 => 0x4002001c00000040000010002002400600000010000007000400000140020000000000400100040000000001000c00600180010004003000000a00080000000001000000000040030008000000000000080000000000000000000200000028000000000700040010000000000800000000040000000000800200000000000000000800a00000040000000000c0000004000000000500000010014004000000400000010008001001000200000000024006000c005000000000040000004001003000000000020000000000c001000c0020000000001400100000000000000000400000040000004000000400000040010008002001800100080010000005000000800000000000001000400300000000004000000800200040000004002001000200000000004001001400200140030000000001800000080040008000000c00000000040000004002400200140000000001000c0000000009000000100080020014000000000400000020004001000800000040000008000000000000080000054001000800700000000008000000000000000000004003000000300040020000001000800000000070000000000000000080000008001000c00000080030024001003c0010000000000400000000000000000001400300280000024009000400500000000000008000800000040000000000000800000080000004006004c0000000002000000300000010010000000800000100010000000001000000040080008000000000000040000000000000400100100010008000000000200000000000001000000500000010004002000000200080040008002000400400000020010000000c009000800000040040004000000000000140000004004000c0040004005000c00000040000000000001c002000800100000000000001000000000080010004000000c001000000100000010004000000c000000c00200000000000001000400000000010004000000000000000000000000000000200000000008002000000000000000010005000400000000040004000000000200100000000003000000000280000004000000000000140030004000000400000040010000000001000400000030004004000800200080000008000000800600100040000003003000000000020014000000000000040000000002000400600000000020001000c001000c00100080040000000000000200000040008000001c0000008000000400400000000000000004ff755873201cfe7558732004fd755873201cfc7558732004ff7458732014fe7458732004fd7458732014fc74587320067f54587320067d545873203cfc7358732006ee4258732006ed4258732046ee3258732046ed3258732046f771587320067f5158732046f73158732046f43158732004ff705
  | 33 => 0x60000000000000100000000004001002c00100040000008002000c001000c00200040000000000000000000040000000000002c0010010006001c00100040010000001000400300140040000000000400100000020010002000400300040010004002003c00000000000004004002800000000000000000001c0000004002000000400040010004000000c001000000300080000000003000800400000010000000000c0000000000000c00100000000008002000c000000c00000080020030000002c0000004001000000000000000000000000400000000040000001000400400000020000000000000300300060008004000c001001c00000080050004001001c00000080000004001001000100100070004003000400000080000000005000000000000030004008000400200000000010001000400100040020000000000400500000000010004001000100080030020000000000200040060008001000000000000000010002000c0000000002001c00300080030000003000c005000800200000010000000001000200180010000000000c00100000070010000000000000000010000000000c0000004005000000100080020000002000c0110000002000c00000080010000000000000000000020008002000800200040050004000000c004000000400240000008005000800300100020000001000000000100010008000002c000000000d00000010004008000400b0004000000c003000000000000010014007000800100000010000009001400300000000000002000400100080000008003001000500000020000004000800100000020000002000800100000030008001000800400040010000000001000200000020000000000000100080020004002000400600080030010001000800100000000004000000000d002c01c000c0070054001000000e000400000040050000000000400100040000008000000000000000000014000000000000000010000000000400300000000014000001800000080000000000000000100140010000005000000400140060000000000400100000040004001000400000100020004002000400000000000000001000c0000000002000000000180010000000000c0010000004000000000000000010003000000200180040000000000400200040010000000000400000040030014000000000100000010014002001400000000010008001000000200040000024000000000200000060008000000400100000010008001000800000040000008005001800600000000000018001c002001400000040000004002000400000100000004001000c003000000200000040044000002c000000c00000080040010002000c003000000100100020008000000800000000020004002000400600140040
  | 34 => 0x10000000c00b000c000000c000000c000000400000000040000002000800000000010000003001800100080000000003000000000080010000003000c00200040000018003000400000080020018000000c00000000010000000000000000000070000002001c00100100010000001000c0010010000000000000000000000001000800000040000000003000400000000000004001001c0000000000000000200080000000002000000000000030000001000c00800000030000000000000700000000004000000000400000000000001000000000140010010000000400100000000000000000000000000020000000000c00900000010000004000800000000000008003001800000000010014003000000c0008001001000d00000010000000000c00000040000000004000000000000010000003001000000040000000000000c000001c0050008003000800000080030000001000000000040000000000000400000080040000003000000100000010004000000c000001c0010000001001800000240000000005000000200040000000002000c00200040000004000001c0050000004000c00000040000020004000800500040000000001000800000040020000000000400500000010008002000400000000010000000001c000001400000180050004000000000100000000004007000000100040020010000002000300080000068006000400000140010004001001c005000000000000010000000000000a00140000004002000400c0004002000000000140000000002000400700000000008001000400300000010000000000c001000000000040050004000000400700000030000001000000000080010000001000c00c000000200000050000000001800400000000000002001400000000000014000001400500000000000000000000000180000000000001000f000800000100010008001000000100000040004001002400000000060000004000800100000030004002000c004000400100100000004000000400000000010000003000000000080020000002000800000040020004008000000000000000000000000000000280050004003000c000000000100280040000003000800200000010008000000000000000040000004000c004001000100000010004001000c0020000000000c0000010002000000000000010010001000c00100040010000009000c00000400020000007000400000000030000001000800300080010010004000000600000000018000000000200440060000000001c0000010003000800000000040028001000c0010000000000000000000000000001000000a000400400040000008008000000200140020008002000c00500100000000001001c0000000001000800100040000000
  | 35 => 0x295c000000000000000000000463800000a9a12000220e8dc82907271e3880ba1361108000048000013f0f8a00000006d7a318677867e00000002430cfc00029a00000df6000000000000000000000475040600000000000df845581562fd000003d80008329024000037412b800071397be0000fbaab0850a26aa7c227ca2be0099dac6e3247800002ba0000626642800093b800000000005a61fce2e912d2871285a7dd25444fd019e000113c55680002f0983a2af14e851f8ba00390fb23328f2c502a1160f99bae13184bc36ba93e00010de30a80b47de235c0001490000245c00c80000000b78000000000008029ad86501a28000000031e0000f5c000123e4b10000000000045d80005650000000049c00017d600013560000000794000000000000d4275e00000000002aa0000114256e0136000000000000005d79164991800000000007a69b148d79d1e65b07ae00000000ef800000000000001a5e21280000000000096a4c800000003f921a29548c9200000000002a8200018a000000003a790b20000768000030e0000ce60001c1200000000000bb8321800000016b0000000000000000000af470e80000002a4c586000014820289a5800000029d600026a0259961a1d618602e199e800019d695e800000005760000a9a11500001d5824e8cd80007bf81e80000000000198a4c000000000000536a2daa63a0ba31b000000000005cf00008b80ed063b00001ac8f400000b12350800000000000000000000000000000009778e8a22494d200003f60000a920000000422060e00000000000000a468000230800023a000043f000049212cc000000050096b80000000930000000000000000a8e00023aca978a449520000a3c04e400001c0839800025c800000000000000000aac18280000f300000bb00000000000280498e1f7c30900005a982ecaab0000000124400000006ad864e29687b8000099200000006a2000000000007a117ea8662a5a05b205a4581a4a4b9800079b800055100003c1a81a09da5a400003fa9b9117222510d0884950e00008ee1ed0000000000030c00006c10f9415e8000a108006003c003000000000040010008001000800200100000000000000000000000080008000000000100000030000003000400000000010000000003c00100040050000005000800400000010014021000400000180010014000000000000040010000000000000a0020000000400000080010000000001000000040000004001000800200000000020000002c00000000000008005001c00000000010010012000800000040030000000001000000040000004000001400000080040000003000c000000400400040020008000002000800000020008000000000000000020004002000800100100010008000000c0030000001
  | 36 => 0x4576aabc4ff12a20000000000000016c2784815a4e8000000000003b00001a0673e800000011b8a7607e0000003626c1c2a1a0274a7c723e20000000000165e6cc827e50618d20000fa000019f4000000028c00000000000764a71a84400000000714000241400000001a795760001fd000008a686d238a00000003cfa8ae0002a2040d0000000153e00000000b9877000000007379e326920396a21190627280000001fe052e1d84278150200000000000000000242065429760b31d08000000029800000001ae4aa91b187d2142e2700a083d58000000183600000000001dea0922868621023e96186a4065897e00000007a1919e99f00006e39d6a6b8021e79116dc8209c3e6cb0cba0a480000000d025d305a60550774a790000000000000000004f421a4000021000000000000b3e67680000000000801000000000000000000655000000000007088c400000000286265a1bb95ac00000000000e9856c2a5800000002d28d2e698a15000000005a1000085a988800017326c79bf6667a6fe2e08cbc334aa6470288be0000000000095c00000000001218a801a9c2891fcc0000bce00000001cba60e84680006738000000000087e9f8c00013288bf000076a039e000096800000002e5800000000000000000593800097180000000b4c9b0992863627e44de8fc68241a3449b2282aae8000000000040f800050700000001cf4000000000000000c9800000027701e48000410000000009dc37b000020b1d38000000000000a6000000092b80000000078a9e00000000000000000000000000000000000000065e26a2000000000000008318d543bb1b7e8510000000000054898ea8160b0e9540410000000098c0000000136ca8292b488a8000000000000002360001d0600003920000000000111e000000053a95e6000000063316ae89729364d1800070a00ec3af800000000006c4800000000000000000000000000000006908ff03eb136217b8000a4b1b522ff00006a900008960a96251a82644b004c000000065d2a0e0001aae6d60000a0c800000017761ce2a2aa5900001339fb800000009488938435915271980001df8e8e00018a8a87a4560000f700000890a81043e22695367069d1213d922095003f4023000097600000002ab600000004ab000007a800000021e8000000011c0000aa29b94a1380007f7293a0002836902a3c835296227d0a706988937c9b591c643c80003d8979c77c053e9ad000013108d04848472000233a93080009e980000da9e20367068e6598ea89fa8320a4b8000000282c7bb1b68908a1dc33c8c740000000a59800050e0000130000000016c80669f140000b8c08c000094e8000514800000000000e60000000000000024d8000225e89322546c3000000009f41cc0c0208100000f8000037c0000000
  | 37 => 0xc000000002a22ba00003fd00000000000000057000000002d097522a7800000000007b1000028380000000d1685d03045521ee8000299e0000000000000059300000000000000000000000000000000000000000000001b800000000cb80001e520000be2206083c000032c35880000000000000000000001b0000000036a245a00006f800000000001d4075084ba0001a00000000000029320001d3c00024f67cc0624a5329c4307800000000003000000000037626f0480000269400022de39c8f3a8220000000000000000002e722d288100008eb800000000008a6844c8df9a5800011ec00006ba65f1a4e81800005db000000000008650426319800000000003c800000000000000000068280009a900003b8999c1598000000000000000002538000000160a00022303230b263de14c45eb80000000bfa0000000000246e000000000000002f10000000000000000002c580f81e316f40001420000267e00000005b00a780000bd40000000000000000000000000000000000000000000000f3607ca6620000a7c8bb14de000290e00000000000000286800000000008e922b86750a82000000000000000000000000000040580008cf2436000000036e91d6315962e26d800077e80008cb800050e8000313a10a00013f8000000000000000000000000229200018d400000008c8094800000000000000701a38655f876233585ea0001c5ea9700000000000580000000000000000000000000049f000060b132200000000000000000000041d0000000000000003106dd800000011bc0cc0000469059000000006cf222c5480000a52000000014a40000000000000043e94ae5848000000000011d000087c06b649c800029280007b50000000000000300008b8800052a800042d12b09e49ab285b0f124e70000a0599fe0000fbc000000000015d64b6800037d05681e180002959266401800075880004122278000237ca1ca73858102d400000002b796348189008000217e0001b3a2d90dd61e88de400000008a0000000012608238000000000079609b2054800000000002389c6a07f8000a1000000001564000000000000000000c2e66a80006bb800000000003bd8000852a39c34412f4777a5f43a00cac00005d6630898400000001d500000000000469800000000002d4117c35c800051880000000000000054a1bf0000000074000000006d180001aa800000011e298b80000000000000041600000000000fa8000125c46b00003f800008a90000496831472e800009181083621484a4d29ae6be800000000000038000000206c000000000000000000000000000000000007a40c1a000000050c053c0000000000197609080006aa1f6020800000000000000086c00000000000fd43d80e1c0001a0e0c928d05e485fc0942962146921
  | 38 => 0x30f9e8a000000055e0000123180801fa302000000000000000000000000000029ba0dc000000000028a000000860000000a88926200022dc864800051612fe00000006c18e464b5a3168d5800000006600000000000000000009d60000000000119a8a78000000116c0000440972253c000223ca8400000000000000145c000000063700009a30ad049e80001c8a94205b8e6852984da0000000000000000014065a78000989800000000001a18000000023c000000000000001bc20d2000000000000000000192a498c14a4c0000809a3a099501766530000000277a3df00004ae800000023aa0000000000082aa28a1cc00000000002950a0e193e07c000027a80007b31880000000000000005c217ec4e5a5ea81f88240001ad0a5780000000fca00017e804f0b8861ca8941c120300f7a2c8236150aa1124640d90f906f827d8000000000000002a1000000000000000000569000000015543d417c8000000000000767c69a6e9751d0e9b88ef8000000000000004f8800000000000001bc80000000000000000018fa99700003ff00486c0800058f8000000000000009f800029a869d000000000000000000000000076e978a000000077e00000000000000170c0000000000000000000008da0000000000000000000000000000298877ba10600014a0817153276780009d4000000000009240000000000084d00000000000736800000000000000000000000000000000000000000000000008167c989ce90002a86d08000000000000000004c80cc800000006f181c400000000448fa6691aa70000038c00000000000000000259497300000001e300e9800000019ba00000009c8800000000000000000523157087b0000000000000020f80000ed4000000000001d2000037e8ba97b00000000000261c0000d407e1000050208108e014a80000000a8d00006ca80000001650000226c9c2a17a00027ae000009e6669d5000000e80000f6e557800000017c200000004e194c2000000000003f038e1fe60000000031aa28619806695314040000000000000064417ac0000000581800000011eeaad0000280977206fa128953800000000000000000000000000000007530000610075279180000000000000178032c00000001bb200020f68b61648473161491f0000000204a0000e7a4240000000108000000000000000000000041f086e0002160000000036c800052c000011b000018680000000e2a00000009930000000000000000000000000000066200000001372a0c70d00006958000941a9f8292254a4bb800069fa2e81181e1c671800000000008949b9013e20780000da000000ba24f800000003008740eb22c500004a716a80001a52141a8b82cd00000000ad400000000000000927000000000001b40000000000028f80000b
  | 39 => 0xe00006359bfc9ef0d3836d012488720daa12271e6fd0e4e7031c0800000960001c640000000000000005f9838000000098696f600000000001bac1a8178e5c1142c18d80005ac80005af2862000000058ea6bc00006bc000000034c000019200007ed83945e980000000600000181e0000eaa31400000238000000000048c8e3032400002b9a6608918d508fc0000000000000028504ff8ce015199a097c80000000000000060400013e8000000009700000229a4c000029e516979e79698f883203b63c6000000012b62fc90b88ef07c276c00000280000a2d0000000000049000000a61fe22da0000819800072c92ae00004a2000105c000179a9d3958c524800049f80007908e9c46800000000ebc00001aaa27a0faa01890a44a197274b98108a31dc0403299c52b21bc00000000001d200850000000268800000006c586320000000a3827f838d81a451b0000629893600006e27b98d4822e0000a1b000078e9c1800002ae25e08829831a6c59d80000000a741228e082450aaa0000c46000097a94f935c000268a35a80004620e86000000087a980c02c1ffe78d819ca3fa2601fc80009c38000752875a69d80be0000b66000087e0f5a9840240000761810c6b980000070862000107a00024120e680000000000000264a00000005f4904e3e9149c56f000001f124c34b06a8a600d228fa0000000200a2191372554000000024a05e81690000000000017960000000000000000000000002266000000000027d2000124a2ce9a2a000000023217902c416ba002800004c82a64c0a59800000021e926449060acc95600000000aea000000000001c20001fc40000e16000000070810780000000a6e00000000000575054c3e599d04fc15d800000000000000000000000000000000000000022200000000000000138000000008cc57d000000000000001e3c0001e3454208ac8f621e426b08e07590000000000000008963fb83fc00015ba31a80001da86ac43c00006431df200023a200000009ae21c200000001c0800000008bc0000ed22ef80004a50000513990400020b200014602c08000407000060f07f0834000002c800026580004fd800087d800064b01eca82110c6ec13aa00000008c1000055a2a6800018340080ccc7261818a7989c4000000000000000de00006ea9cb800000000000000000000039512845f5059a00011662f7a4ba00013e0716a7ac0000000000000054d1cec1d2000065207189189a964ed1c9480da32c97c016086a800000000000001552000000033b9d360530000000187c82c0000000000009789e4000226a422888a99e80004ba29548d100006fa10da00000000518000000297a000000057416022a98000000027aa6f80000f900000001366a6c091c00000000001efc00000000000000000000000000
  | 40 => 0x8d41a0800075607a00000000a9b0000000000000000003e021e08f097301689e1000000000000b5e0001d94000043800000005d5058890f000029780000000000000000000000008411a700b09aa2950800066100000000000000000014b8d0400014dc0000000000000031b80004bd800097d800000009a200000000000c58407800074c22d6a9f000028f094a0001d6e165800000003600000530000000000000004bc955c69900003c38000000031800007c000001bc000000000021489b500000002a2600019fc87c80009b1060a7c196de7b6a30064927fa4600000000174e371000089580005d6000000000008cf80000f200000000a2e0d08000a1b8000000000000000000860000000000000000921a580006aea9d20000000000000000000003fb0000000147000021ee00000000b880000000000000000028e8a8876d0f4a81913a200011a23208000a911f380b4800000000006c00000a3a80005e8800000000003578000000204623b000068d8000a1e00000000efa2ea0dbe40d9dd60ad80003a08000000017c892096a82d215219000006dc10540000f6600016fa000000000000004cf800039e1800000000073e26284be0000000122800000004e90000000000012f893000011fc179000029f9f400bf8d8455310a0892800000000004ac92089160000000030a7e98000000000000000004b000000000000000083478f800000000000f1a5b229029c024a80000c4a1301f783586e5a7fc00000003840000657a1d44bf1c7224a000000015a0a4806b89bc26baab39da284fa5e04db9dda401058e487174600000006248000000034a0000da20000c5a94b83aa45d07c40f100000000f5e9ca9c0232d00001db000020f800000011da0000e4ca299956000158e0000f383f39daa00000000001dc69398e280000000000000057c00009b385f40000000000000008a188a00029dc000000000029c8000195200000000001bfa676116a0001af2707170a00000000000b287dc202a7d1a6aa8259a9ea6087f400018b80000f72a8e18860300000938932e47c15e4532113e3c780006fc8d760001210446a4428ee917e0001c7a73f107e00028ca17e09fe000000019b8362a1927301bd861805a293c00015040001aa600000000000000805aa6e40c01e20000608000197a98d00005300000000000000000007ba836c391001293c05e800029f2000000034f9ca80002834aa880002ab00003f4804033d1c82a5a00000000000194800000000000001f160000000000000000000000c7157465c000010213dc49600003981a660000000000000000000000001b9e00022e40001b2e32380066709958000000019787fc50da9709c418a40000000000000060c1d1835999e20f3000042ea8e470580000000000000190862300008
  | 41 => 0x1c18ac62bb10c800009ec3e080005cf800099c0000371800096b934800025bc3ba89e8585922600000000000000000000000004760000000233a76e00023da7db197e0000000506800000000000000000000000000000000000000005000033a0000000000077613383b580000000000331000013b80000000000000000054b8388821800062d151a045945072d10ac0000000000000050d000001ea2c600014248111ce857824fa00025a80001b6000013e400011dc000046e000118a0001b9a92a80004838000000057e0000000726800000017b400000005258000000219a4e0946a572000000000000000976565800085c00000000000000287c6e624ec7e1a7007668dc000021684c5856a3ea8eb453c992e000000019080001d10bd2000000000000000001f049d514004dd800005380000330000000185e869a2f8842000091121b6000012e20000005ffa014000000090180006f4281e3daa6740001f828739ec621981904b40eb02dfa52479295dc730886a000000015721ae653800093800000001f52aa11a40000010a0001630a4a99ec000000026200000000000a3500002eb16f800014861ac0000000223854e80000000cb20001e8c0000daa7fc8736000000000026e60002a3a1ba26d21b388400000000000179409000008990fd000001dca06000053b800074b0000000000000017dc2d3800015000004ec800011aa6c00000000ab280003e70000523a9ce5471c26164800000000000000ad2000000000016e400000007579c743e20000000260400000000000b400001d340000000000000064980000000000000000000000000001f5627600007488000a260ec085ca30600022f2a658000570000062b0eb676ba5e8480296e0000000000037c00015fa00000000e380000001dd40000000000162400018b6925205439faa60237a7b00000000000000000000000001ec2000000000000009a193bc78a9ac63770000000000000000000000000000238818800009f6800090f800042d80000000000000072ca0898fc0000eba00000004d01d7e000145e00006580000000013800000021024778102000000092600000000000000065c4ea0b9200016e692e085a656891683381e08c3000000000000000c1850fa4a8a70957c72d8000000273e5748000000176000009be77309a82328000000257c0000000623893ca7b000000000005ba26ac68980006ff80000000000000054800011f2000192006280000000000994873a8af0000000099a9ef99b60001e940001c581a61adaa3ca46051303ea66a0000000134a61400004c3800000000000000000000000079f00006f08000000160e00028d29d980003fd9edc00001265f7951e0001c967a08d9800010e40000000a5b1e1200000000001b1077480000000000000006a6340
  | 42 => 0x35200000000000c4a389800000010a4000294a0f680000000000337000000010dc90e29580000346000000043f85ce1be86467c285c2304a02000000fc000000069a84ac48d00002c1800000006da01105860000000000000022d18be00000000002a52000000000000001830000a3e00000000cc21e780008de800063280000000aca430130674a89020000270000000000000002e500000f411466fb8d688d3a9b60000df200000000001446a04800000005fa0002752000191c55028a48cd21221a4000000000002cc00000000162000000056180000000000000000047faacc8d2000016f800061300000a6841c17186cc723951200000000000000210a18000016086ef80000001fba32a000026d116e47226064f687887a3a3f6082000000000000000000000000005a800000005220000000000169a000258e2dd954e0000000000000000000000000f2e00000000000150000000010e800006980000000b907e81b369a400000001f3244100000001c8400000000000000a7a9fc03740760976800004500007cf91c448b800000000000000a4c00000001d4206ea408446000132c0001f2a3221f96000000073a800091026cc0001946000000025f11680ca8ce400013143b20000745800000889586a497b20000e2c000000060718f400009600001a5061e8000000000000000006f9a9940000000211800076f800000000005350000000069c81da33046f80000c59e800579c2e33780000000e9603615ec804aaa80d1000000000008fe80000002714886222ea42000000011f4947800000000000a8000003a867800000001fd800025d07240cc80a249c000007b800000002c416328ee00000003e31ee446c9e480000000000000000000000000000000278e0f38e4200029c61140de66b080005dd0ffe00000000000000000242620381d4000000000002ac000000000001ac7fa000000000000000000000123a63810ec278a8fc13c800000016a2000000000000009c308c400000000001a4400000000000000103170e00000005a7000000017fc9709ad4309a4767bd0ef086c00000002a020000000305a6dc000191e193049e2731b400dba2f418580000000000000063800020ec0002882000000000016520001e1e8ee25ec09910be303800061380001f896f294b262c0000000221869281f00006f003e21e51cce0000000000000000000001d29caa000000000000000001d3a0ae000000020026e480002d218f082f0ede0001c7e249831a1189454000052a00010ee21e800065900000001566000007489c800038b80004dd0ec22ff80000001c243108000000000097f0080000000087f1a22961189817d85bc63111629e90000052000071887986d8885002200002f68e004d4000023700005e200000000aa800000007e2a9a2
  | 43 => 0x5e12532000203200029fc0000fe600000001340288000296a000000000006c600012040001adc00000000000d6e000000000000002be23661b280009c1267800005ca302a5760001ed89891ade00000008f5a34c00024ac84802268d4a81c67ea5a08de047aa3021827d71ec849d08b064f0000000108610a8d861158d8a5031d80330251a1d19dcaa0a2a66034000083a185c37ba4f40002396360866a61c000078b249a00000000000000000167c50a800015800000001bde9af800000000002b69d8a0a700007a913c033622ac942800060096581780000a3780000000c94859022e0001ace00000005b807fa00023fe000000054600009b18d2a000253407626fc000019800022aa3d308f600000000000000000000000000006b88000000000098f9fec00006e406a1d1a4cc800084b2a94000071c17000000000c5e9140000000000000027ce2fb80006fe15140002098000000020ca5a251d828c9d89e960000eee76d80000000000000000000000005b4221615e0000000128e5cd80004c1102c0000cd021780006a800005f800000000000000088000003d87348bd66209134a7c28704ef8d1c00020947c8800000000002888000000000037500001df000000022b2000002e2af846857aa75ca4100002e019e09288000000000000000000002890000000000000000000000000000000000000000bd016b996200000000000000670000000022a000000000000c9800013700001c1e00000000001ce24908000000000000000008f1292209d135225513100001bf0000259e146104646a800000012163888508000247400000000000000126926a000000000000647eb000041d8000000029400000000001b8400004ca0001ec029b02f40000000000133c00000007670000413000000000006dd1d5200000006098000782800000020d66df0000526977e09c92d468ca402000000000000000000de82bc074e0000c484a580d400000004fe800041b844e6c7033c06b9190000000000000007bc8000000136a00007da00029fe0739636173000000000003fe80009bd0c4400005142d6832e55a8000a7e800036c000092d8000000000094e0000000000000000000000000000000000000000001f2c00000000848000000000033e15880001538625a44a73c800000014160001e2817c109e461258c287000066580000000676000000000000008898c680000000a0a80008c90924000289a0000000000000000000002a723920000f5a3d19c48445000000000007bc000092780000000000000000034200008c7156e052a9920000a7245300000000b2276e1dc844a912e92598de6b290e80cd0000a4a09e6000045a7e3800021300000002866000078e093113851b9ba0000261e00000000001eb40001f80317000000000000002a4a70e
  | 44 => 0xc9e8800019ee000000000000004eda83c0000000000000002080000000000000000000000000000000000000000000000948000a2c00009ca00000001ad6824a43200019ea0000000000236a000000000026ec52780003e68d6474100000000000000000052216386a10000688094c60c9e1a000000000000001bfa86005c0000000182e0000336000134c0000000660000000001ca0000000000120600000009e60000000000000010440001d7846a044400029b200000000000000aa9800049a00000001968922956c94480000000000000215400017c49cf11300000000258a87a45e919445c0000a5f98c61770a98534041200000001ca80009aa2a98627061421800609cb8000000000000000000001ba23c700000000000a1d800000000000000000000099800012027580e185b88000000000000000004388000000000000000000000000000204c2c000006bb14e400000004258000000000000000000000000374a30e2ec99f845e00000000000000109aaab9f3c00026d800000000002504a66000000008f018b219600000000000ae20000000109000000000002b0885884c800083c0afc8e6802ca22800000000005c7000081a00006de80008db80000001da01f3194281416645c91a947ff000024b0a42474a0742a900003d4815c1050e9200000000000000000000097480006d6800061d8000000000053d000082980008aa211e00015562601be200000003769fbe1160b207839ce491c1ddc7c41c881e980000000a804399ff800016202ea8000397000001a0000381034c44da3464cc0ace52280000000000080800000016fc2b916260dc800000012e2000000008380000000d900000000577800020e9b885830000000000055e8000000000000000004f39922268000000000000002a460000000000000086c800000014a200000000000000000000046e85746d2800000000006f104f024d010e614a8be4328000000138400006ae8a62a42145a6f68b514ca6a4000000017100000000000000038c95c671f22449f2172c0002672000000000021460ec800098aa69240890c6000000000017980000000508800000000003728b9e24c8000281a600591800000000004f3000000000000001d7c3bc9f1e0001038000000000000000000000924aa740000000000282400000003ca0000060800000e818c000095a000035a76400000000e9a000000000024a40ba8000000000000000005338e620001d96982000000000004e627868718000079000007d0000000073e00000000002a86000000022700000001dbc0000000000006e0000000000094400000000d7234a0000000000251400000003e628aa59f8000457aa48000259a34e8ca2855aa3e000000000000000000000000000000011c200000000000000000181674c800
  | 45 => 0x2c90000000159e000080c0000000000028a43e262038380002b22a14241000000000001b08bea00024280000000000291800000006968000000000000000000000000000000071b00007709d72000003c00000000000eda1430000000000000000d600000000000af2000059c00003f859c00002a300000000000000000000029ac0000428803800000019cc0001b2800019ae40096fe533071e001229057a16d245289f05ca8c4c8d883667b4a1f400000000001d447ad809c12c800066500000000000092a4e4000000021100000000ce20a595426e9a3600000000921800000000007a60000996000015b24b4698000057b84b63c98f0218d20f4000000098488ea000000000029009040000000000000000000000130151165a00000000002a1c00011ae000000000000000000000000000000000006b480000688000844800000000003b60000000000000000000000000a23a5d638780000001cbe79ea6ae933000000014e20000000408011c000202c16628809609ece2eb8dc847d8000000153c00000000000582551a3384fb0000363000000000007130ff2269a7e200000002d71d7497400003648fb6000279c8f30d127e4213c0000000000203a00023a8381800063219a400000005ee9cae000000041a80000001bea4e98000000000000025fa000000000008700000000449800000000000e01820000175c4e49c76144a4f8000109c00027e840a8c36160000000000000400000000255c0000000000000056a80000002528000266830f010629a8000000000000000005b09b48000000079c80000000000298800021e00000000000000000037f8ab2000180a1ef0000000000063000000000552685800000000008599c4aaac8000a3d800000015287dc8bdc000033a00000008b9800084a800000000005f0280e0001e6634500000001524000000000000000000b56000000000000006de12f00001f2e4a6967a22e80000001b200002518615800000010b00000000000065a404800028b1f9232f8fc462c000000000000000cc680d0000000000000007aa4f7920a863000028d8d803191f020000000000144a7f08ea40000000a9e8f7e31f8c9c88200000000000000257e94aa42e0cf8de299a800046600006bd8d5a00a0000000036867721629c200007f6000000000000000ac0a49000000005365c49c9200000000002810000000000000001b780009f700000000c7083304e66db20240000f92000132417400e600009fa00000000001e7e9b814b60000000971103c53d8000418143c0000000000000071b80007d28b049e4004674429cc00015900508000969800075700000c20000428800000000005dc000000025c097ba2ee000000000000000ad000000007ba00010a800000002dc8000917800000000000000b6041
  | 46 => 0xa588060001cee000121e00012c2000000000000000001d1c5110e5624b973a0000000000000000000007358000000000073825b08759dfe00023f200000003e1a234a860000000038463b83fe2bda63624400007f900000001c8c000174a28c800010c0000000050e914800097700000ba00000000d28000000000000000000fa200000000000000000000000000002950000000278a15b82a418e800000000000000c3449d8000a7a138c00000006b0000000000002dc08e6017275aa2727b40000000000082e17200006aaa376000000034302320001f8800000507109b0a00000000a38000000000000000005ab03568fe231e96e8000000000000000000000000000118c89b800008e122200022f6141108c0fc8000000091a0000610000000000000005d88188000000007425e42d89de412d000000026f8943a93800009644e6870e7a9800059b80008f48000000000000020ee92000000000000000000000000001929ea86368a4e82b886811200008d0a80c73c1d3e000000000027b8000000010d00007e79f9c5fe9fbc90200003c680000001d8e153a97c00000008030000000000036b000000000009480000000000000006d800027c62848000aaf8000000000081ca28a0000000000000077108480000000000000000000000000000000000000011ea137800000011f800024c60001112943000000000000000000000000000028967a70000a42aaaa0988000668971462b8000147221e1fe0ee600019b0827049400027de78222ce0000000000274200000caaa58000000000068100006d3800000016b63b926167f7a20200016ee4a480000000000000050095e00003c000000001dec000000000029e0813800067c92a610296b40000000000000000008220000e3a35320fc112a2220000000000000015f1106890800000000000000d7ea9588b600005620000000000000000000008a9800088c837a00000000000000a4402860000000000115a22b8000000098c515800000000000000000000000000000000000000000000000000009a6000000004a47ab22ae51200002cb243a3ca838602e21426a013d85608000000078490b2188a0292520000000510a912aa404188b100002cca1be6641fb08f0000016b000095c00009f022a21798000724000000000000001bce0000b7400023585f900004a218f20000000000000000014ba72293a000002f200028cc49584a84830c22000105839980001bd12d8000000002d980600000000001ae80000000000048e556283a51c98240e71432329000000013d60f50000a8f09de0000000000000000004980001c56000018600018e6000000038500005048a6400000005f290ae000000000021240000000731940e0001a3e00000004d5168c7e5000000000000000000000103a9be80
  | 47 => 0x6c82878000625172003704a6030800056000006c6863000013601509c04000000000000000001c2c267132a79c00006ea000061d00003b2800082901b4a63000086a05de6c38000000000006e000000018b200000000000e409470a7617b00000001f5800000008070fdc00000000002398540000000000000000000a8b800000000006d325aa1cca4daa0c0cda2d500000000000000000039d000031d8000905800097380001e5aa727978000795a28e000283e0001ed677a1b6a00011fa018800000011e09b2004234d8000000000000000006c9215c00000000000000000000097e05282a8000000000000000000000128a0000000108a6640000000721800046d02fa5df0cfa00010a63ba24b00000644a2b165c95500002fc000076300000000000000000050981cc1f929ba2b10000000000017480000aa800025b92ce000000000000006ad000008d000000000007fa896c00000004a600000002126000187e1a500005908000297000086427b21f480000000000000000000027f000000000000000000000062e8000000000000014101d0a32a8ad000039400001de000000002c800000000001e2600000000001b221f180000000000000000053f00001198098000000000000001efa6d000000000998cf00001108000125400022cca11800076c8fde000006c73d892200008fca8c8d208120fc09808a140002960098291e3cd123003d124674017a83dd2228000000000000000000000a7d80003cf16a429a0000000000014907d600000000000a8600000005e096c40b9020600000000000000000000000008f800000000001a5c0000f44958005400000001d9800000000000000000a2a0c9e0000000a3990f40a0800042090f679d8000000000000000009c9902ea5d0dea23d13584429cdc000000000023540000000a3e947800008fe7741c705da1c3621f0000aa6800035b0000a2f07dc00000004a400ce0000000962a5020000000000000000000009798000000000084b8000000000051d0000000000000000007350000000000000000000000000000000082d9d7a6a61f1200000009ba8000000000086100008228000000021a0001cd000000000001a7239d85e2923851e000000094c20a21dda86a00016623418000879a32600600000001eb25b3a640526013e17680006468b0a28a800000000008149f3a0000000000000000014b4000285c0000000000000000000004c60000000099e00000006129510000000008806ec93500005fc00006ef02b223e88f2a1d1e920000000000000000023ec0002a540718000000000019f018e16a000000000003ec0bcc22c800018a03dc0000000000020c00000000000000778055e6bf92a443480002301ef644e8d185399f64000147a00009d259a00000000000000000006da0808
  | 48 => 0x93413423808000913800035d00000001f081f6000000000a87c91000000000000022240000000223a4888381ad87c80b8e99b94be000021c00000005ef1e78000000000000000000000000102604683b800000000000000000000000000000000000000201a8ed80000001bec3da03c000028d8000008400000009e309521e280005c880000002916034a3ca4a000005ee00002ac0000000211c000000000002d0000000000000009ac246a0000000000000000019980001eae00000004b80b2e00005b8000185a7aa80000000000000013436928f40001fa22368000a90000000000000000000000000047990101c4818400016c600015c400000000000000000239e00004aa0000000000000000000005c780000b38000000000000000000000000a76a09a00004e200016be9121368999800000000008020efe000000068b80000000000000066c3b813f290100000000000000000086384fa6068000000000000007ec83c80009498000000000072c0000aa788549400000000000086180009c90000000000000016540000f4e5cb8000000000000000004d9009a7ed11b056280002960302000000039600000001ee003e87fe49e04c800000089b7a6a60000000000000066d244c000081e00020ac3d6289200001585d5800000000000000000000000000017aa91c8e34000000000000008f421ca10780003a4000000000000001a68a53aac475c0782000093a2e88e6499d8b4654984d200000000e8000000000000000000000000000027e600000000000000000164a000000000000000b01a1000022ba1e4273a6e2a9ca0000000000000000000007ea86c0000000030e00000000000000000000026804d3800000000000001ed043aa3328be800000000003200000000052c0000000000224074080004198000000000071a000035700003e100fe2210000a8c000093f19c419c00000002888476000018b8beca75000000010680001018000000064e80000000da600000001a68f489e5898600000005a280009eea69a000000000000000000000000090000000004f9a4be000186e248181495990d818aa73600015a28e39ea06f7248c3020000000291c000222075d80009c805ba000000034291825731748383040e12083d20000000921000021c92be2172454234a1b80ee8d60000000000023142dba10e1e7077200001100000fbe000000000000002998cd400015f200021c0000000039780008108000000180e2ab800000000006c9aa166871cd800000000000f6c06500000001a3c000000027b80000000000967000093103a26d9810400000000000a0a68b00004e5000095b000000000000000000000000071e1a142f9996000000000000000728800000000009850b18000000000029bc000000000000002a297386502a8e0000
  | 49 => 0xa17c1ba92384140000000000000000009e8800084e9d144aa800082e0e7017115be075803e1cd00000000000a7408740000000000266c00015920001a1a0000000884000033f8000000131200000000001b865e323b20000bb44d687b600023d44978000000000000028580000000000110201780008d928ce000161e0000d2600008d66a18eac00000000000a9088000524658000000000082784cc00000ae9a080007fba1e283627b69958d34a1297f600000006e0177a0001cc8000000000000000001c303b10edc0000000000000056da9e28e101da00016782bb95ca5d98000a511c325f4090e4790f04000279e000000000017ee7afa56a15c8856000000000000009ac800000016ea0000764955800093c800027d8d2408900007698490727a7ee20693d28a2000038800000001286433000000000000000000000000065700000000000a77a1400000000000000078119a6000060600000005c59e2416c93ee16d03a812222d000000009f2989009f00007852a803a880003fe00000001c007ec800000005948f923ce57d8000031000000027d077f0000972aa24000000000028200001fae1fa80c81c6a3e641b0000000185400000004248000000247e000000000000007c3000000000000001a8c000000000018220fb0000000000000000000001af409a00005980ad600000001c216400000a387b2813a00017da15909ae00000002c2000010f000000017340e40bc61d30000000174473100007609f4e0000ca663a24240001ff66630ab837e80000951d0a000000000000000000000000000087680009e08000853a42a00000001c400009c60b7c75b05a01de8dcc20d89080001414000000000000008628000000053a00001b20b6a02200018e436f000000000006bf0f760dc123600013ae00000000000c7ca41a10c1ca08a23c5091e59d09d09d900009941ac47e923223560000000000000000009339506000162c0001a24000221a0000000000073c00000000002592421217600025965c9949401c00000000668000012200000000001f7a9328000000000075206844482430000000000000000001d88056800000007e8000000000000005b68000000059e00000005d0800000000000250000000000066b0000000000062a800000000003c3000000000000078000a54a8dc05e00000000b1e000000000000009bb80009a70db67be000020212a000000004e40e3e72803405e91f343f8a580920800079d281426284020ac0000000000000000006d7203e2e2a0fe00000000001f440002070000000012825b80000fd64741abe42f0e7c00015ce7550000599966c1808c7a10d82e04ba800000024d600013c637611c05a19ac8000223600013b80000000263a5e23ee0b5800006560e2811e34398ce000000000000004c99b64
  | 50 => 0x1042281000034000000000000000000025c298600000003d5000032ba97264c800000000004d78a503b380005aa800000000000002ab84940a3423925ac20980f2000259013b000051f043273fa20c2919de64c6986400029f4000089800000004b29b540000ceca359bd488f800000012de48f08120001a78176095e0000bf65b2a7a011f260a000000000014643c280004f100004cd92bc2e106128a50ea6714a85220c1ede55829405c083549c09c44000000007780000000000000238246700004bb0d4ea669f6e00002f800000000000e6e72f0c960001a3000000007a7800000011225b523ee0000ca0a64000094200008ac0000896a40c000000045005fe4ce9fa88e30efc000066400013ba00018e2000045246480001ec01f80001a1e0001f6613a990e00000000000d4653e28b2000000008b0000a00000051000001210c1046da95a9298000a9d80000eb000094d80005a4800060f8000000000000000000001f6245423e020289121a9800000007ce570800026e89560000000a369696000134400029a40002ac03e395a87f590c2423800093491186dc8b1a0d3a808a62a1de00000000000000aa20dfc00014662f92642392094210800008db0000a2d80000001e0c0001ce6000000000000008001718797000013080001b520c0000000000022760000e520000c72000000000021a01c2a94600028c6000159a00000003fa1eee0002734000285e0001b501560056059a7d60002632333a71c0001abc36780003faa69e0b6122a566229c2c323f4a00800000000000000000959000056d19880001f98000000000000000000000447000066f28ec000176a00028867da00000000000a558000000191679800007d7800000000002be8000000193844c88a80c1800020500000001a8a7fc00009d61f5433a954a7660950000110e64c00006119ffa61b000065b9aac9da915c6ee00e00369912000000091e80006f6939e000083841680000000000618800000018a204614d600919e418f80000001bd24e20990610aa9270517c6a9380009ea80000000000aa71bb495b9e160000b3600007261eb00005d0138e00000000000000000000000000000000dde13f8b1c5ed800000000000002776000235a4f200000000000000000000001a0000000016d800000000001011df41f40000000000000000005ca05540000a2801280002418000486800000000000001aea0000c0400000004c7000000000005d40aa29da000041280000000c2068e8000000000000000000000000000000000000007b8800000003eea150000749000000023fc00016723548d780000216793297898f1f9a7a880000000000000000000000007ac19f000000000000f108c2930a4b913801498a520000000000000000000006ae000000002781af9d462de
  | 51 => 0x1c5400006d68e50000569a0aa0000000759800000011861b99af00000f9e0000000000000000000009ea00008720000000000000000000000cf680785f28310a7079a15620002780a9890620000000000000036506f266c80009ba026e016848600000000002390000000052c93ac0eb8eb800006a28dd02c611fa7ec6d1227a5bc00000000000000000000d000092c80002071992000000005c80005c680000000000a9a80000000e9400017789e6800000000001870c0c000152c0000000000035e00000000001ff414080000001428000000000016d600004d400022627f6968e00022b6000045e59a80005672ac80001bca3f3000000000000000000000000048b00000000ecc0000010473a7161b123082fa000000000000000e8c87f8000000000000000003a8000064080006e922f000000000000000000026c683000015405a400006722db1e220000000000034805e800000027c45fd00000000000a818e88000168207e876e0af0000894000000000004050eae14e112449390ce5612546867a6da34f14c636e08a0156800000007c827214fe265042c000000000000007da90aa35e8adc71700005a82a8c8d0000000000002ef000000000000000f7a00000000000fc282fa7600000000403800057f800000000000000000000091800000000001480a0b8244365816480f061e000000078087a800000006a690980000d9a578a6ca87600003c9000000020d40001cac7f28fd800000006cfa774000000057e1ca6730000000023c632108a40000000000000022300000000000199a72c6d58ec60000a10957800012e00003180000000000090700008210f3259128e200e27481f280000000000000000078b871600000002b812a800000001a20030000101a67d800091983280000e3c000000000014f04458f1600000000000000000000095d00000001a7a4a0a5feab407d400000007430000135800019500000000fae00000000000000937800000013084402178720000014c800000000006db8fb40000000000198200006747290000000000032a80002768000000000030c80f0a6980009cc80004ae0d7010ba90c1e00ad80000000000000000000000000bd85d6800000007b20af80000000000000000000005d40a000008230d8e98ea15e000000000000009938c5432699d200000009a107ee402aa1289d1c3c71001c80f0800000000000000000000000000028e84f280000000de000000002fe00000bda8ba86b0000000227c0000000000000006e85aa856aa369dfa3289860180000000000000000000000231800000000008c68bc06b300009d592fa000206a00014e068600000000888000240e5f986dc0000000000000018f207a7f50000000000000017e200025164b180000c8800000000002f80a26000000
  | 52 => 0xca4f522686f5982a646189e0000000000000000000000002648000000000000000001c1000000000000000000163c9ff80009a38c2c00000006120000000000000000000b28000000000000007206ee800000020c22f280009d000000001f4c00012dc000000000000000000ab600003e83c88000000000000000007d40000000198e00025be95a0338000223a00023b00000000a23000054a817400000004e2812a75a0000661a4bc271800000000006510000a7b9de20f298f637380162ce000047a157245100000002856817962a00000bc9fc98780001706000190037080000a117f2389000000004d89de000007d931e6f90d56095915425000007738144000000000000008f780003bd055614d12c88d427d48a1274c83aa41e6720000000000056b970000000000b58b9a000210000000007df80000000000958800000000004c300000000000000000027f051040a000096d1e6a795000068200001c31a386ce000071400de8b29070000000000000008388cb60000000000000042500005bb00000001e0000000000000000000000000009a41d7800000000000000000000000000000000001fc801610e0837801a000165651a1d28000000000000000001c609440e12000058400000aa000000000024340000000000000053e8000711a84c8ed0000000000022aa28691b1a0269519e610693ea733176e00006b4545994a08000000000000a868000188a1f800003a400000005f3000000026f20001eba8ef800000000000799f180000000000215800022061d7000035f150c41797f87d69c0e68a0000435000000022704a30000000047800000003d094ec8bf9e64314823a1c0013800000000000000984000064d99b85b600006049f0056ca5880000a0c0000b2a8dc09b80001f76000000082a0000749800078619be01ca5720000bc861a963200022140000c3a000000000020a06f623dc69f20e4000000007f000052f01282800a7a3f200002ee80009d1800086e82580001e06a8b000053620400000000000129e5e180000c3201060127723c2000040c80003d90fda4561eb800000005f60000000000000016cc0000b3c8c48000000000089f83bc431191400027cc0290c8a0000000000000000024fe6ac13c239b219c91184e80b70000000000000015fc8450000000000000000006110000000045c2e980000000000000000000023ea6ed80000000e4a3868000000000000025b60000000000000021d80009fd800000012246e700005a5049690693343510000000000000000000000000793a31000000000001f287af0000000141e000211884e291434c800076920069f818583478e841a313786f324dc0000a20000000000000001629f0e000000004b2a5000014828530000000000085b800041900000001d5a000098279
  | 53 => 0x6cd277c00029aa307220a0000d1a9e209d4000000063f800000000ee62690560000804000084e0000bb679b02fc19e80ac87480e22d498bc0000000000000000000002ad0000472aac68e989c29d1192a22780007cd8000000000077d800000000002ae86d20000e5a31e0a940000c0610017ce54c265e000126e2e6000000000000001a828938000214800058a1efa9db137e6e080000000000000000038280004520000732826a000000012c000000000000001fc60000000806000000000000001af800017640500000124a2c09e51e62000271293a83b4000000000000000001d568b0aa7e453879a00016800000000a6d0afe00016106c2020a000082839aa87e000000049902de2da800000000000001934000000028590520bba8c200000006a3800091a111000013b065aa8c83188000a311b301190b4495687e613d03829fd000008a800061a1d4e5871fd230a168800019
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb538454530441fbea508a8a60883ffd4611514c1107fda8c22a298220fdf508454530441fdea6e8a8a60883f7d49d1514c1107f7a8ba2a298220fdf507454530441fbea6c8a8a60883f7d4991514c1107efa8b22a298220fdf50645453044001ea704a8a6088003d4a09514c110007a8c12a29822000f50825453044001ea6e4a8a6088003d49c9514c110007a8b92a29822000f50725453044001ea6c4a8a6088003d4989514c110007a8b12a29822000f506254530441fbea684a8a60883f7d4909514c1107efa8a12a298220fdf50425453044001ea2a390a6088002f4a1e214c1101e5e843c429822013bd2868853044079da50d10a60880f2f4e16214c1101e7a942c4298220fcbd1858853044079ea30b10a6088002d4616214c110007a9bac4298220fbf507588530440797a70910a60883eaf4612214c1107cfa9aa44298220f9f5154885304402d7a30510a6088003f0dca214c110007e03944298220009db8748530440013b10e90a60883dfd4d45214c110007a8a8a42982203cfc0214853044001ba70e90a6088002f4a1d214c110005e843a429822000dd08748530440037a50c90a6088006f4219214c1107c5e9c2a4298220f8bd1854853044001ea6ea90a60883dfd41d5214c1107b5e9c224298220f6bd18448530441ebea6a890a60883d7d4551214c1100cde9c1242982203cfc3824853044001f84e490a6088003f05c9214c110007e1b12429822000fc06248530441ebf848490a60883d7f0509214c11030e3c3b6ea90220048f8865cd20440016d30a3124088002ea6106248110005b8c28e29022000bb1841c520440012f10ea8a40880131e1d95148110006b9c3aa29022000b728754520440016e10ea8a40880035c21d5148110026b93b2a29022004d707654520441e96e708a8a40883d2dc611514811079eb9ba2a290220f3d71745452044001ae6e6a8a40880035c5cd5148110007b1412a29022000f61825452044057ae6e4a8a40880afd8dc95148110007b1b12a29022000f606254520441e5ec484a8a40883cbd85095148110026743b6429022000f6151c8520440099e0ed10a4088002dc61621481100b5f0c144290220019e88748520440099d0ec90a4088013781c52148110787b1a8a429022000f615148520440035e10c90a40880133c1d9214811003f70312429022001be0874852044009bc10e90a4088006f8a19214811000df0432429022007ee086485204400fdc6ec90a4088013789d92148110026f03b2429022007ee07648520441e37c70a90a40883c6f86152148110007b1baa4290220f0f607548520441df7c70890a40883bef86112148110776f1ba24290220eede17448520441dbec6a890a40883b7d85512148110007e1c1a429022000fc0834852044001bc6e690a4088003785cd2148110
  | 1 => 0x303bb2608802336a1c764c1100072c3a8ec9822000e5b541d93044001cb2a83b260880f396d44764c110405ad43eea982203ed5a87dd53044143cb6edbaa6088003961db754c110005adc26ea9822000b5984dd53044001ea703baa6088002d6607754c110007a840eea982207fe5b61dd530440ffea6c3baa6088003d4907754c110007a8a0eea982203cada869c930440015b30d3926088003361da724c1101f5ad42ce49822000b59859c9304407b735093926088002e6612724c1101e5e940ce49822000bd1819c930440015b70cb9260880f2b6219724c110005adc2ae4982203eb58855c930440017a702b9260880f2f4205724c1100066c3b0e49822000dc9721c930440797a5023926088002f4604724c1100b5e8c0cc498220009d88758930440016b70ab1260880fad6215624c110005cdc22c4982203db988458930440397a702b12608800276a1c624c1101e4ecc38c4982203eb5a8518930440016b30a31260880f6e6a10624c110005ccc20c49822000ec96218930440035b10db8a60880f3361db714c1101f5ac42ee29822000f5351dc5304403f7a50fb8a6088006f4a1b714c11000de8436e2982203cdd276dc53044001ba0edb8a6088002f4e17714c110007a9c2ee29822000bd185dc53044001ea10bb8a6088003d4dd7714c110007a83aee29822000bd384dc530440017a309b8a608800374dd3714c110006e8ba6e29822000f5354dc53044001ea2a9b8a6088002f460b714c110006e9b96e29822000dd172dc530440115b70cb8a60880f3361d9714c110005adc2ae2982203eb58855c5304400173708b8a60880f6e6211714c110005e5c12e29822000bc8825c530440517a50e38a60880f374a1c714c11012de9430e2982203ced2861c530440797a70a38a60880f3d4a14714c110005e8c28e2982203cf51851c530440016a30a38a6088003d4dd4714c110007a83a8e2982203cbd3841c53044079f250838a6088002f4610714c1101e7c8c20e29822000b91841c53044001ea6a838a6088003d4550714c1101e7e1410e29822000bd1821c53044079f830438a6088002f0608714c110005ad43aa29822000b58875453044097cb6eca8a60880f3961d9514c1107fdadc22a298220ffb598454530440b96b702a8a60880fbd4e05514c110007a9b8aa2982203cf50715453044057cb6c2a8a60880afd4d85514c1107efa9a0aa2982203cf524154530441fbea282a8a60880f3d4105514c1101e7a910aa2982203cf50215453044001ea70ea8a6088003d4a1d514c110005a943aa29822000f51875453044001ea10ea8a6088002d421d514c1101f7a9c32a2982202bf52865453044057ea30ca8a60880afd4219514c110007a9bb2a2982203cf52765453044001ea2eca8a6088003d41d9514c1107ffa9c22a298220ff
  | 2 => 0x72545100059ac20e4a8a202bb72801c951440016e300392a2880025de1d6254510034ba43ac4a8a2000b3784589514409166908b12a288002d5e0d6254510005aa41ac4a8a20479768718951440572eb0e312a288122cda1062545100059ac20c4a8a2000b568318951440016ab06312a28800399588625451015db940664a8a2000b7180cc951440012ed0f192a2880025d61e32545102459b42464a8a2000b35848c951440576e501192a288002dc602325451015db940264a8a2000a76860c951440014eb0c192a2880aedca003254510005b8c0064a8a202bb7287dc15144057ae50fb82a288012dca1b7054510025b8436e0a8a202bd7276dc15144057ae0edb82a288002dce137054510005b8c26e0a8a2000d7374dc15144001ae2e9b82a288002dc60f7054510005b8c16e0a8a2000d7372dc15144001ae2e5b82a2880f23761f63cc51015e3b3b2a398a202bd72705473144001ae2a2b8662880af1d1d9514c51025f2a31aa298a2000d7151dc131440578ececa8e42880af5c9c151c8510006b8a8ae190a2000977845d621440012eb08bac42880035ce017588510006b8402eb10a2004c77605d62144009ae6c0bac42880035c9017588510006b8a02eb10a2000d57305d62144001ae460bac4288003554c17588510006b9102eb10a2067ccc621cd2144001998e7b1242880af1d1d95148510006abb9aa290a2000d54735452144095cc8c4a8a42880063ea1b7048510006b8a8ee090a2068cd476dcd21440cf9a8ec39a4288002f46007348510005d2c20c490a2000bc583189214400174b091924288002f8602324851050e3c3b6ea98220019da878c930440119b0ed19260880fad6a16324c110005acc2c64982203db9a848c930440017330919260880f2f4a06324c110005e8c0c649822008cd8760c930440797a5021926088002f4604324c110005b8c28e29822000d70751c530440017630838a6088002f8608714c110004bc43aa29822004c78765453044079ea462a8a60880f3d40c5514c110006b9c3aa29822000b728754530440016e10ea8a60880035c21d514c110004b843aa29822004d72765453044009ae0eca8a60883fedce11514c1107fdb8c22a298220fed737454530441fdae2e8a8a6088003d4e0d514c110007a941aa29822000f51835453044001ea106a8a60880af5cdcd514c11015fa9b9aa29822000f53635453044001ea0c6a8a60883f7d4d0d514c1107efa921aa298220fdf514354530441fbea086a8a60880035cdc9514c110007a9992a29822000f52325453044001ea264a8a6088003d40c9514c1100266c3b6629822000f5151cc530440033b10e98a6088013361d9314c110026e838a629822000f51514c530440016e30b10a608800378dca214c110007e1192429822000fc13248530440457a
  | 3 => 0xab12200087d84dd562440018be61baac488003174c375589100045fc22eab1220028bc845d562440011bf06baac4880223720d75589100043f438eab1220028be87dd1624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd1624400193e61ba2c488003274c374589100043fc2ae8b12200387c855d162440011bf06ba2c4880223720d74589100045f438e8b122000c3f751d16244001878ea3a2c4880021fa1f545891001c3e43ea8b122000c3f74d516244005878e9aa2c48840f171cf54589100043f43aa8b12200087c87551624400187ee8aa2c48800b0f1d154589108162e39aa8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f54dcd62440018baa9b9ac48800237e0373589100046ec06e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000ccc73dc96244005958e9212c488407331ce42589100147643a84b122002cac745096244001c5aa8a12c4883af331cd42589100043f43ea2b12200387c87d45624400147b09a8ac4880030fdd351589108061e3a6a2b122000c5f73d4562441d18b8e7a8ac48801f2b98974189101e4ecc04e631220008ef87588624400195ae8b10c488002b320d621891003c6f41ced9922007acc8258f32440091f10cb8664880233698d70cc91000c7a432e319220048f8865c232440010ff0abb2648800e1f215764c9100045fc22ec99220028bc845d932440011bf06bb264880023be09764c91003c6e43ac69922007acc8258d32440010ff0abb0648800e1f215760c9100045fc22ec19220028bc845d832440111b906bb0648801e3b209760c9100046ec3ec619220018f4865c432440091f10cb80648801f3a189700c9100043fc3ac6a8a200387c8758d514400147f08b1aa2880b28f211635451000537c12c6a8a204aa6c8258d5144079ca862b1aa2880021fe1d625451001c3e43ac4a8a2000a3f84589514405947908b12a28800297e0d625451025d2e41ac4a8a2004a7a86dc151440576e101b9aa2880ae9da1a73545100053ac34e6a8a202ac74769cd51440576e50139aa288002dc6027354510006b8384e6a8a2000a77865cd51440574e90cb9aa288002dce01735451015db8402e6a8a2021c74761cd514409166d0839aa288002cd610735451015db9400e6a8a2000b71801cd5144001ae0e039aa2880025de1d6354510034ba43ac6a8a2000b378458d514409166908b1aa288002d9e096354510005b2412c6a8a2000e556318d51440576e101b92a2880ae9da1a72545100053ac34e4a8a201ec74769c951440576e501392a288002dc60272545100053bc32e4a8a202ba74865c951440016af06b92a288002d520d7254510005b9c02e4a8a202bb70805c9514402b8e8ec392a288122cda1
  | 4 => 0x5c40014bd07a12cb880029760f42597100061eba284b2e200087e8710965c40010fb0e212cb880038b50842597100061fba2a8b1e2002c3c7455163c40091b90ea1ac788003875514358f100046fc1aeab1620088dc835d562c40011bf06ba2c5880223720d7458b1081e2e39ea8b162000c3f7455162c4005878e8aa2c58840b171cd5458b1001c3f42ee6b16200087d85dcd62c40018bd0bb9ac588003176177358b100062faa6e6b162000c5d54dcd62c40a78bea3b9ac58814f175477358b1029e6d086e6b162053cd910dcd62c4203998e7212c5880123b21d4258b10016563a284b162000e2d5450962c41d7998e6a12c58814a37e1d63ccb1001c3f42aed196200087f865d632c40010ff0eb2c65880021f61d658cb100061f3a2cb1962000c3e655d232c400187acaba4658801f2b989748cb1000656ba2c51962008acc8358a32c40a71bf06bb265880123721d634cb100247643ac499620088dc835d832c40098ece2b2865880031d595710cb100053ac34e6a8e2000a77865cd51c409f66d0839aa388002cd61073547100053ac34e4a8e2000a77865c951c40016af06b92a388002d520d725471027d9b420e4a8e2000b35841c951c40012ed0f192a3880025d61e325471027d9b42464a8e2000b35848c951c40094ed0c192a3880029d6183254710005d2c246490e2000c3f745536344005878e8aa6c6880028f61351d8d1001c3f43eeab1a200087d84dd563440018be61baac688003174c37558d100045fc22eab1a20028bc845d563440011df04baac68801e3b2097558d100043f438eab1a20028be87dd1634400187eebba2c6880030f1d77458d100061fc2ee8b1a2000c3c85dd1634400193e61ba2c688003274c37458d100043fc2ae8b1a200387c855d163440011df04ba2c68801e3b2097458d100045f438e8b1a2000c3f751d16344001878ea3a2c6880021fa1f5458d1001c3e43ea8b1a2000c3f74d516344005878e9aa2c68841f1b1cb5458d100043f43aa8b1a200087c87551634400187ee8aa2c68800b0f1d15458d1083636392a8b1a2002c9c7490d634420b998e521ac68800a3721d4358d100164e3a286b1a2000e1d5450d6344209998e4a1ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031bd537258d1000636aa6e4b1a2000ccf30dc9634400199a61b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100043f43ea2b1a200387c87d45634400147b09a8ac6880030fdd35158d108061e3a6a2b1a2000c6f72d4563441c38d8e5a8ac68800237e1d6318d1000566412c631a2000c3f745536244005878e8aa6c4880021fe1573d891001c3e42ae7b1220008bf845cf624400517908b9ec4880028f61351d891001c3f43ee
  | 5 => 0x31719573185200047bc3ac230a400087e869d951480014eb033b2a2900021fe1276545200043ec24eca8a4000c75819d951480018be613b2a290003174c276545200063b884eca8a4000a3f845d9514805947908bb2a29000297e0d765452025d2e41aeca8a4000a77815d9514800127b083b2a2900b28fa1076545200051ec20eca8a400087f841d9514800187d083b2a2900021f61076545200061ec20eca8a400083d841d951480018db043b2a29000317cc076545200062e980eca8a4000c77101d951480018f4203b2a2900031d44076545200043fc3ac6a8a400087c8758d51480018d8ed392a29015ed9606725452015d36432e4a8a405bb67815c951480091bd073b662900021fe1576cc52001c3e42aed98a400387c859da31480010ff0abb4629000e1f215768c5200045fc22ed18a40028bc845da31480010f90cbac62900021fe1f658c5200043ec3ecb18a40018ec865ca31480070fd0bbb262900021f617764c5200246e43ac698a400387c859d831480091d9053b062900063e202760c5200043fc2aec18a400387c855d831480010f90cba862900021fe1f650c5200043ec3eca18a4000c3e74d9431480c38dce5b2862901831e9c3650c5200061fb2ae818a4000c3c655d03148011938c6ba062900023761f630c5200064eba6c618a40018ec865c831480018decab9062900031b195720c52000667b1ae418a4008ccc635c831480018f6cab8062900031e195700c5200066db1ae018a4008cd8635c031480011df0eb1e42900029b21951c85203143e432eb10a406087f87d9621480010fb0fb2c42901879908765485200062fb2ee690a4000c5c65dcd21480d1b9041b9a429000317d9473485200062e328e690a4060c6c76d9521480a7998edb9a4290003721c37348520296663b0e690a40048ec8758d2148001cceca30a42900029b2195148520026363b2a290a4004e646154521480070ff03ba2cb8800e1f60774597108461fa0ee8b2e2108c3d41dd165c40018be61ba2cb88003174c3745971084c3ec3ce8b2e2000c3f749d165c40094ed033a2cb8842a9d60674597100052fc1ae8b2e2000a5c835d165c400187f08ba2cb8800317e0d74597100062e41ae8b2e210987f815d165c42130fb02ba2cb884270f905745971084e1e20ae8b2e2000c3f405d165c400187a80ba2cb8800317cc174597100062e982e8b2e210887e871d165c400187ae83a2cb880028fa1073597100051ec20e6b2e200087e87d0d65c40010fb0fa1acb880030f5d343597100053741686b2e2000a6d82d0d65c400187ae8a1acb880021fa1c43597100043ec3886b2e2004a76819c965c409d4eb03392cb8800297e0d72597100052e41ae4b2e2000a3e841c965c400147b08392cb880021fa1f42597100043ec3e84b2e2000c3d74d096
  | 6 => 0x43fc0ae9b2a4000c5f305d365480018ba60ba6ca900021fa1c74d95200061eba0e9b2a4061a6e821d365480c14db043a6ca900028fa1273d95200051ec24e7b2a400087e87d0f65480010fb0fa1eca900030fdd343d952030d3741687b2a4000a6d82d0f654800187ee8a1eca900021fa1c43d95200043ec3887b2a406087e87d0b65480010fb0fa16ca900030fdd342d95200052f41e85b2a4000a5d83d0b654800187ee8a16ca901878b10942d95200051fc22e3b2a4000a3c845c765480010ff08b8eca900030fe1171d95200041fc22e3b2a4000c3c845c765480018be60b8eca90003174c171d95200051f420e3b2a4000a3d841c765480014bd0638eca900029760c71d952030d37410e3b2a4060a6d821c765480c14f50038eca901869e60071d95200043f43e83b2a400087d87d07654800187ae9a0eca900021fa1e41d95200043ec3c83b2a4000c3f7490765480010fb0ea0eca900030f5d141d95200043f43883b2a400087d87107654800187ee820eca9000297a0c41d95200052ec1883b2a4061a6e8210765480014db0420eca901829ea0041d95200053cc0083b2a4000a3d84197634800587ce8aa6c6900030f5d154d8d200146fc3a87b1a4000e1d5450f634800147b09a8ec6900030f9d36598d200051ec20cb31a4000c3e74196634800187ecaba4c6900030f1957498d200464e31ae931a4000c9d74d8e63480010fd0fb2ac6900021fa1c6558d200051ec20cab1a400387e87dd563480010fb09baac6900021f6077558d200062f986eab1a4000c5d30dd563480010fd0e3aac6900028f6107558d200043fc2ae8b1a400387c855d163480011ef02ba2c6900123d2057458d200043f43ea8b1a400387c87d5163480010fd0eaa2c6900021f21d5458d200161f3a2a8b1a4000c3d7455163480010fd0fa8ac69000e1f21f5158d200051ec26a2b1a4000a3d8419463480011bf0eb18c69017e3761f63cc9200051ec20cbb0a4000a7581dd7614800147b083aec2900029d60475d85200043fc2ae9b0a400387c855d361480010fd0faa6c29000e1f21f54d85200043e43aa9b0a4002c3e74553614800187ae8aa6c2900021fe1573d852001c3e42ae7b0a4002cac7450b6148001c5aa8a16c2900028f61351d85200051ec20cb30a400387e86dd561480c10f90dbaac2900021fa1f65585200061e3a6cab0a400087e87195614800147b0832ac2900030f1d065585200061fb2ee8b0a4000c3c65dd161480018becbb9ac2900031719773585200062fb28e6b0a4000c5c651cd61480190fb0fb28c2900030f9d365185200053ac0eca30a4000a3d84194614800187ce8328c29018b1b5c865185200053ac08ca30a410bc7970194614800187ecaba0c2900030f19574185200062fb2ce630a4000c5c659cc61480018becab98c29
  | 7 => 0x5b515c0214c079ab2a2b8042980f372c8570085301e6e910ae010a603cdc9215c0214c0bfba242b804298202d6a1b65d81308772d436cbb02607fd5a76d97604c0ffcb4edb2ec098002d6e1365d8130005acc26cbb026000b5981d97604c0613b30f316c0981b2d6a1662d8130005acc2cc5b02606bb9a8498b604c00173309316c0980ce76e1d62d8130005adc2ac5b02606cb588558b604c001ab6cab8ec0980035619571d8130006adaa2e3b026000d59545c7604c011ba702b8ec09800356d4571d8130365ac42ec3b026000dd171d87604c0453b30f30ec0981b2d6a1661d8130005acc2cc3b0260259db87587604c0016b70ab0ec0981b2d621561d8130005cdc22c3b02606bb9884587604c00179704b0ec098002f220961d813000cecc38c3b02606cb5a85187604c0016b30a30ec0981aee6a1061d8130005ccc20c3b026000bca82187604c0017930430ec098003745c461d8130005ad432a3b026000b5886547604c057ab4eca8ec0980af969d951d813086dadc22a3b02610db5984547604c0b96b702a8ec0981b3d4e0551d8130006acb8aa3b0260089da87887604c0013b30f10ec0981b2d6a1621d8130005acc2c43b0260089da87087604c0013b30e10ec098002b6a1821d81300056cc3043b02606cb5a85087604c0016b30a10ec0981aee6a1021d8130005ccc2043b026002c3e7455163c800187ae8aa2c7900028f6135158f200046fc1aeab0e40088dc835d561c80011bf06ba2c3900223720d745872081e2e39ea8b0e4000c3f7455161c8005878e8aa2c39040b171cd545872001c3f42ee6b0e400087d85dcd61c80018bd0bb9ac3900031761773587200062faa6e6b0e4000c5d54dcd61c80015b30039ac39000b2b1d1425872000716aa284b0e40ebccc7350961c800147b09a8ac39000317dcf51587207462e39ea2b0e402ba6e82dd951c80958dce5bb2a39000297e0d765472025d2e41aeca8e4000a77815d951c82196cf02b92a39000297e0d615472025d2e41ac2a8e40678df8758f31c80d11bf06bb263900223720d760c72002476c12ec18e4000c9f635d031c8011938c6ba0639019f33d8d720c7200466631ae418e4008cd8635c031c800199eec39a4390002f260073487200273230aa290e400087e86dd365480070ff0fb26ca900030f5d364d95200043ec3cc9b2a4000c3f7499365480014bd07326ca900029760e64d95200043fc3ac9b2a4000c3f7459365480190fb0e326ca900030f5d064d95203053643285b2a4000d2f7450b6548001c58c8a16ca900024fe1171d95200052f41ee9b2a4000a5d83dd365480018bd07ba6ca900031760f74d95200043ec0ee9b2a4000c3f40dd3654800187a81ba6ca9000317cc374d95200062e986e9b2a400087d879d3654800187ee93a6ca900030fe1174d95200
  | 8 => 0x8bb4429800276e017688530004ae432eb10a600095f845d6214c0012bb08bac429828b17d8175885301e6ab882eb10a603cd5a105d6214c079ab220bac429800257e1f6588530004aec3ecb10a607fd5a70d96214c00199eec3144298022762197088530006adb2ae110a6000d58655c2214c001ab6a8b844298003565517088530006e5b12e110a6000dc8625c2214c079ab6a2b8442980f35654570885301e6e590ae110a603cdc9215c2214c0212bd0bbb242980025761776485300062e32eec90a60009d980dd9214c0018bd0bbb242980031761776485300062faa6ec90a6000c5d54dd9214c0018bea3bb242980033660376485300066d086ec90a60008de869d9214c0012bf0abb24298042572157648530004cfc22ec90a600f99c845d9214c0013b700bb242980031719476485300062faa0ec90a6000c5d541d9214c00199b043b2429800333908764853000666a10ec90a6000c5f511d9214c00199c423b242980033308476485300446fc00ec90a60088dd801d9214c00199e403b242980033348076485300066b880ec90a6000cda101d9214c0019aa203b2429800317ddb65485300062e3b6ca90a60009ce87989214c001998ed3124298002e36126248530005e4c04c490a603c9cc87589214c001998ecb124298002f2e0162485300062fbb2a290a6000c5c76545214c079e8842a8a42980425721676085300062e32cec10a60019d8809d8214c0018bf0b3b042980031721676085300062faa4ec10a6000c5d549d8214c0798bea33b042980f31754676085300446fc04ec10a6000cdb809d8214c0111bb013b042980f33620276085301e66d084ec10a603ccd9109d8214c0012bf0abb042980425721576085300062e32aec10a605f9cc825d8214c0bf998c4bb0429800276e0176085300062fc2aec10a6000c5c855d8214c0018bea8bb042980031755176085302fe66412ec10a603cc5f515d8214c0798baa2bb042980f333c8576085301e66690aec10a60a28df805d8214c0019b700bb042980f3368417608530004ae432ea10a600095f845d4214c0012bb08ba8429817257e0575085305162fb02ea10a603cd5a105d4214c079ab220ba8429800257e1f6508530004aec3eca10a6000c5e76d94214c0018baedb284298003479d365085303fead386ca10a6000d1e855d0214c001a3b0aba0429800347d9574085300068e32ae810a605fd8c625d0214c079a3ea2ba042980f34754574085301e6c790ae810a603cd8d215d0214c14593ec0ba042980f36684174085301e6cc882e810a60009cd87d88214c00199aedb104298003635d362085305166d432e010a603ccd9865c0214c0113b10cb80429800356d957008530006ac32ae010a6000d5b545c0214c001ab2a8b80429800372d8970085302fee4312e010a603cd
  | 9 => 0x7518530006aa882ea30a603cd59105d4614c0212bb0fb28c298003479d36518530005aac0eca30a6000b1d84194614c001a3ce8328c298002d56046518530406ad380ca30a6000d1e855d0614c001a3b0aba0c29800347d9574185300068e32ae830a603cc9f615d0614c07993ac2ba0c2980f347d4574185301e68ea8ae830a60a2c9f605d0614c079b2e20ba0c2980f3668417418530006ca882e830a603cd99105d0614c0212bf0faa0c2980025761f541853007e8f3a6a830a6000d1d74d50614c221ab4e1aa0c29800257e1d5418530004aec3aa830a6000a5c86550614c01fa3ce8aa0c298003475d1541853087ead382a830a6000d4f659c8614c001a98cb390c29800353d527218530006a6aa4e430a603cd4f519c8614c079a9aa3390c29828b33d8272185301e6e5084e430a603cdc9109c8614c001a9ecab90c298003531957218530006a7aa2e430a6000d4d545c8614c07999ec2b90c2980f33358572185301e6a7a8ae430a603cd4d515c8614c14599ec0b90c2980f371c4172185301e6e5082e430a6000dc5105c8614c079b9220b90c2980023761e62185300064eba4c430a6000ccd72988614c00193ae8310c298003335c86218530004ebc3ac230a6000e5765584614c0017a700b08c298002d660376545300062fbb4eca8a6000b55819d9514c0012bd0d3b2a29800257e127654530004aec24eca8a600095d819d9514c001aab033b2a29800317d827654530006ab884eca8a6000d5a109d9514c001aaa213b2a298002c7e1176545303ed8e422eca8a6000b4f825d9514c00169904bb2a298002d5e057654530005adc02eca8a607db1e841d9514c00163b083b2a29800317a187654530004afc20eca8a6000d1e841d9514c0012bb083b2a2980034761076545300048ec20eca8a6000c5e641d9514c0018b8c83b2a29800317d807654530006ab880eca8a6000d5a101d9514c001aaa203b2a2981d2d560672545300052fc32e4a8a6000a5c865c9514c0f96af02b92a2981f6c7a1072545300058ec20e4a8a602bb5a801c9514c0016b300392a29800257a1e6254530004aec3cc4a8a6000c5c76989514c0fb63d09312a298002c76126254530005acc04c4a8a600095f87589514c0012b90eb12a298002d6e0162545300062e3b0c4a8a6000e4d62189514c0796ad02312a298002d56046254530084ae43ec2a8a6000c5c76d85514c0012bf0eb0aa2980425721d61545300062e3b2c2a8a6000b1f84585514c0fb63908b0aa298002d3e096154530005a6412c2a8a603ce5461585514c0016b700b0aa2980f273a0a76c8530004afc2aed90a601095c855db214c0013b700bb6429817f331d962c8530005e5c02c590a601095c859da214c0033b1013b4429800257e157688530084ae42aed10a600099f845da214c01f339
  | 10 => 0xb0a6000b5581197614c227ab6e032ec29800257e1574d8530084ae42ae9b0a60009db805d3614c0033b100ba6c2980f23761f64d853007e4e3a2c9b0a600095e87d53614c0212b90faa6c29840f56dc354d8530004ae43aa9b0a600fd1e74553614c001a3ae8aa6c2980038759154d8530816adb82a9b0a600095f855cb614c0212b90ab96c29800276e0172d85301e46ec3ec5b0a6000a5e86d47614c00163b09a8ec2983a356dc351d85302e6ac386a3b0a6000d5b75dc3614c001ab0ebb86c29800257e1175985305162fb02eb30a603cd5a105d6614c079ab220bacc298002c76106598530084afc3ea930a600095d87d52614c0012bf0eaa4c2980025761d54985300052e432a930a6112d1f74552614c01fa38e8aa4c29800356d957098530006ac32ae130a6000d5b545c2614c001ab2a8b84c29800374d8570985301e6e830ae130a603cd5b515c2614c079ab2a2b84c29804257a1f7558530404af436eab0a600095d84dd5614c001ab421baac29800267e11755853007cce422eab0a60009cf825d5614c0bf39904baac29800276e017558530004af43ecab0a6000d1c74d95614c0012bd0e32ac298002c761065585300068e3a0cab0a600f99e87dd1614c001a3eebba2c298003471d774585300068fc2ee8b0a6000d1c85dd1614c001a3ecbba2c298003471977458530006cd086e8b0a600095f855d1614c0212b90aba2c29800273e0974585302fce6412e8b0a60009db805d1614c001a3eea3a2c298003471d4745853007e4e3a6c8b0a603c8dc87591614c01f938e8b22c29800257a1f5458530084ae43ea8b0a6000d1f74d51614c01fa38e9aa2c29800257a1d5458530004ae43aa8b0a6000d1f74551614c01fa38e8aa2c298003875915458530006a7baee4b0a6000d4c75dc9614c001b1ee9b92c298003631d37258530006a7b2ee4b0a6000d4c65dc9614c001a9ea9b92c298003535537258530006e5086e4b0a6000d4f751c9614c001a98ea392c29800363dd07258530006c63a0e4b0a6000d4f651c9614c001a98ca392c29800333d90725853000666b20e4b0a6000d4f541c9614c001a9aa8392c29800333984725853000666308e4b0a60a3ccf601c9614c001b9420392c29800237a1f62585302fe66396c4b0a603c8dc87589614c0bf998e4b12c29800297a1b51585300058ec26a2b0a6000d1f74d45614c223a38e9a8ac29800353dcb5158530006a6396a2b0a6000d5b75dc1614c001ab0ebb82c29800366dd37058530006cc3a6e0b0a6000dcb72dc1614c001b90e5b82c29800676a1b705853000cec436e0b0a6000d5b65dc1614c001ab0cbb82c29800356d537058530006acaa6e0b0a60089d981dc1614c001ba6c3b82c29800356d477058530004afc22ea30a60a2c5f605d4614c079aae20ba8c2980f356841
  | 11 => 0x4c0012bb0fa0eca98003475d341d9530004af43c83b2a600095d87907654c001a3ee920eca981fed6a0241d9530005acc0483b2a600095d87507654c001a3ae8a0eca9800257a1c41d9530004aec3883b2a6000a5e86107654c0014bb0c20eca9800347dd041d9530005a741083b2a6000b4d82107654c0ff6b50020eca98002d660041d95300058ec20cbb126000a5c86553624c01fa3ce8aa6c498003475d154d893007ce7c3a85b12600fd8e7450b624c001e1aa8a16c498002c761351d8930004afc22eb312600095f815d6624c1478bec0bacc4980035684175989300068f3a6cb3126000b1d84196624c001a3ce832cc49800347a1574989300068ec2ae93126000d1f655d2624c001a38caba4c49817f6318974989302fec790ae931260a3c9f605d2624c001b3420ba4c49803f279d3649893007c6fc3ac9312600fc9e74592624c0212bf0faa4c4980025761f549893007e8f3a6a93126000d1d74d52624c0012bf0eaa4c4980025761d549893007e8f3a2a93126000d1d74552624c001c3ac8aa4c49800393d976298930006c6ba6c5312601095f87d46624c0012bb0fa8cc49800297a1b51989300058ec26a33126111d1e74d46624c001a3ae9a8cc49800356d957098930006ac32ae13126000d5b545c2624c001ab2a8b84c49800372d8970989302fee4312e131260009db815c2624c001ab6a2b84c49817f72c857098930084af43eeab12600095d84dd5624c0012bb03baac498003568437558930004edc02eab126000b1d841d5624c0012bd0fb2ac49800257a1c65589300058ec20cab12600095f855d1624c0212b90aba2c49800275e0574589301e4ea40ae8b1260009db805d1624c0012bd0faa2c4980425721f5458930004af43aa8b12600095c87551624c0014b90caa2c49803f479d154589300068eba2a8b12605face86d89624c0012bd0fa8ac4980425721f51589300058ec26a2b126000d5b75dc1624c001ab0ebb82c49800356d977058930006ac32ee0b126000d5b54dc1624c001ab2a9b82c49800372d8b7058930004ecc0ee0b126000d5b51dc1624c00163b08328c49803e3761f641893000566c16c8312600fd1e74550624c001a3ae8aa0c498003875915418930004e7c3ac43126000e4f65588624c001c98cab10c498002f2e0162189302fd67c3ac43126000ccf87588624c001c9f0ab10c49800393215621893000567c22c43126000e4f54588624c001c9aa8b10c498002b3205621893051d67c02c43126000ecb80588624c22bd9420b10c498002b361942189302fec63a2843126000e8f64508624c001e1aa8a10c4980033358971189300052f436a23126000b1d84d44624c001c9ac5a88c49800276e0175d853000cec402ebb0a6000b1d841d7614c229ab0e03aec298002d560765d85300058ec20cb
  | 12 => 0xf372842720c5301e6e4884e418a60678dc865c8314c0cf998c4b90629800333219720c530006a7b2ae418a6000d4c655c8314c001a9ea8b90629800353551720c5301e667b0ae418a603cccd615c8314c079a9ea2b9062980f353545720c53004667b02e418a6008dcb605c8314c079b9420b9062980f372441720c53000c6ec1ced90a60048ee829db214c0010ff0abb6429800e1f21576c853000c6e432e790a6007ccc764cb214c0070f90b3b442980063760e76885300043fc2aed10a600387c855da214c00117f08bb4429800a2f21176885300043e432eb10a600087f87d96214c0010fb0fb2c429800637219738853001c3f42eec90a600087d85dd9214c0111b9063b24298287171cf654853000c6f436e690a601095e85dcd214c0012bb0bb9a429800317d9773485300062e32ee690a60018dc865cd214c001998ed1924298002e36123248530044e643a6490a6000ccc764c9214c0070f90b3b042980063760e76085300246e41cec10a60018f8809d8214c0010ff0abb0429800e1f21576085300043e432ea10a600087f87d94214c0010fb0fb2842980030f9d3650853050e2f39eca10a607fc7a70d94214c00187ecaba042980030f195740853003e56312e810a60018dc865cc214c0018becab98429800317195730853003e66312e610a6000cad74d88214c00199ae7b1042980031ed9570085300063c32ae010a6000ceb625c0214c00f9d0c4b80429800297a1b74d9530004af436e9b2a6000c5e86dd3654c0012bb03ba6ca9800317d8374d95300068fa06e9b2a6000d1d40dd3654c001ab421ba6ca980025761e74d95300068fba4e9b2a6000d1f845d3654c0012bf02ba6ca9800317d8174d9530006ad082e9b2a6000a5e861d3654c001a3ae83a6ca9804257e1f64d95300068eba6c9b2a600095d87993654c001a3ee9326ca9800387d9264d9530005a7414c9b2a6000b4d82993654c0016b301326ca9800257e1d64d95300068fba2c9b2a6000b5b80593654c0012bd0e326ca980425761c64d95300068eba0c9b2a6000e1d64193654c0014bd0db96ca98002c7a1272d95300058ec24e5b2a607fb5a809cb654c0016b301396ca9800297a1872d9530004af43e85b2a600095d87d0b654c0014bd0da16ca980029761b42d95300068fba685b2a6000d1f7450b654c0012bd0e216ca980025761c42d953000786a1085b2a607fb5a8010b654c0016b300216ca9800297a1b71d95303fdad404e3b2a6000b59809c7654c00163f08b8eca98002c721171d9530004afc22e3b2a6000d1f845c7654c00123f08b8eca980034721171d95300062fb02e3b2a6000d5a105c7654c0014bd0c38eca98002c7a1071d95300058ec20e3b2a6000b4e821c7654c00169b0438eca981fed6a0071d9530005acc00e3b2a600095e87d0765
  | 13 => 0x64e3a287b0a6000e1d5450f614c0010ff0ab96c29800e1f21572d85301e46ec3e65b0a60678df874cb614c00147b09a8ec298173175cf51d85300051ec20cb30a600387e86dd5614c0ff0f90dbaac2980021fa1f65585300061e3a6cab0a600087e87195614c00147b0832ac2980030f1d065585300061fb2ee8b0a6000c3c65dd1614c0018decbb92c2980031b197725853000637b28e4b0a6000c6c651c9614c0210fb0fb28c2980030f9d365185300053ac0eca30a6000a3d84194614c00187ce8328c298203175cc65185300053ac08ca30a6113c7970194614c00187ecaba0c2980030f195741853000637b2ce430a6000c6c659c8614c0018decab90c2980031b19572185300047bc3ac230a600087e869d9514c0014eb033b2a2980021fe1276545300043ec24eca8a6000c5d839d9514c0018eb033b2a2980031dc4276545300051fc22eca8a602ca3c845d9514c0014df04bb2a29812a9b20976545300053bc0aeca8a600093d841d9514c05947d083b2a2980028f61076545300043fc20eca8a6000c3e841d9514c0010fb083b2a2980030f61076545300041ec20eca8a6000c5d831d9514c0018be863b2a2980031710c76545300063b880eca8a6000c7a101d9514c0018ea203b2a2980ae97a1b73545300062f3b6e6a8a6000c5c769cd514c1116ab0339aa2980ae972197354530485abc0ae6a8a6000c5e761cd514c0fb63d0839aa298002c76107354530004af43c64a8a600095d878c9514c0574bd0d192a298003171da32545303ed8f42464a8a6000b1d848c9514c0574b90c992a29812b9318932545300062e3b064a8a603cb56810c9514c0016ab02192a2980ae9760f61545302fc6ec3ec598a6000a5c86547314c1010f90cbac62981fe1fe1f658c5300043ec3ecb18a608095c865d6314c0012bf08bac629800257611758c5305162fb02eb18a604bd5b605d6314c079ab420bac62980f356441758c5303fcafc3ecb18a600095d87d96314c0ff8bcedb2c62981ff569c3658c5303fe2e3b6ca98a60528de87d89314c0bf998e5b12629800395d94614c5300052e432a298a6004c5c76545314c009ca8c2a8a629821257219750c530004afc22ea18a600095d845d4314c0118bec0ba8629802356d81750c5301e6ad082ea18a603cd59105d4314c0012bf0fb2862980425761f650c5300068f3a6ca18a607fd5a70d94314c001a3d0aba0629800347615740c5300068fb2ae818a6000d1c655d0314c001938c4ba062980f327d85740c5301e64eb0ae818a603cd1f515d0314c079a3aa2ba0629802327d81740c530046cdb02e818a603cd9a105d0314c079b3220ba0629800353d96720c530006a632ce418a6000d4f549c8314c001a9aa939062980f353d46720c5301e6a6a8ce418a6008ccf609c8314c011b96c13906298
  | 14 => 0xe87d0f654c0010fb0fa1eca980030fdd343d95300053741687b2a6000a6d82d0f654c00187ee8a1eca9828697a0f72d95303fd2ec1ee5b2a6000a3e849cb654c00147b09396ca9828697a0c72d95303fd2ec18e5b2a600087e87d0b654c0010fb0fa16ca980030fdd342d953050d2f41e85b2a6000a5d83d0b654c00187ee8a16ca980021fa1c42d95300043ec3885b2a6000e2d4210b654c1434bd07b8eca981fe9760f71d95300062eb9ee3b2a6000a3f845c7654c00147908b8eca98003175cd71d95300043fc22e3b2a6000c3f845c7654c00107f08b8eca980030f21171d95300051f420e3b2a6000a3d841c7654c1434bd0638eca981fe9760c71d953000537410e3b2a6000a6d821c7654c0ff4f50038eca982869e60071d95300043f43e83b2a600087d87d07654c00187ae9a0eca980021fa1e41d95300043ec3c83b2a6000c3f74907654c0010fb0ea0eca980030f5d141d95300043f43883b2a600087d87107654c00187ee820eca9828697a0c41d95300052ec1883b2a6000a6e82107654c0014db0420eca981fe9ea0041d95300053cc0083b2a6000a3d84197624c1018bae632ec4980063760f75d893000c6ec1ee9b126110c5d73d53624c00587ce8aa6c4980030f5d154d893087e2eb9aa9b1260028ef8750b624c00595ce8a16c4980038b55142d89300051ec26a3b12605cc5d73d47624c00187ce9b2cc4980028f61065989300061f3a0cb3126000c3f655d2624c001878caba4c49801f2b189749893000656ba6c5312600087e87d95624c0010fd0e32ac4980028f61065589300051ec20ca3126080c5d73194624c0011df0eb10c4982021f219758c9303fc3fc3ecb192600087d87d96324c00187ce9b2c64980030fd95748c9300061e32ae91926007cac625d2324c0bfb1864ba464980032b5d3628c930404ae432eb192600095f845d6324c0012bb08bac649800257e05758c93051e2fb02eb19260ecd5b605d6324c001ab420bac64981fe57e1f658c930004aec3ecb192607fc5e76d96324c001a3ce9b2c649800347a15748c9300068ec2ae91926000d1f655d2324c001a38caba4649817f63189748c9300068fa8ae9192605fd8f215d2324c14793ec0ba464983af66d81748c930006cd082e91926000e4f65d8a324c001b1ae9b14649804257a15718c9303fe2e3b6ca9926007ace86d89324c001c9eca312649800393194624c9302946e432e21926000a3d84197614c1018bae632ec2980063760f75d85300062eb9eebb0a6000a7581dd7614c00147b083aec298003175cc75d85300053ac08ebb0a60018dd83dd3614c0010ff0aba6c29800e1f21574d85300043f43ea9b0a600387c87d53614c2218bae7aa6c2980021f21d54d85300161f3a2a9b0a6000c3d74553614c21f8bae6aa6c2980f23761e43d853001
  | 15 => 0x9a8cc598003475d35198b3080e66316e8b1660ebccc625d162cc207c98c5aa2c598047479d15458b300068eba2a8b166102e4c6255162cc00163b09a8ac5983a39318b5158b30004afc22eb30e603cc5d605d661cc097ab2c0bacc39828b55c417598730006aa882eb30e601295f87d5261cc0012bb0faa4c39800257e1d5498730004aec3aa930e6116d1f7455261cc023a38e8aa4c39828a3721d645873008e4e3a2c8b0e6000d1f7455161cc023a38e8aa2c398003875915458730094af42ee4b0e600095d85dc961cc1451b90eb12c39828f331c962587300058ec26a2b0e604bc5e76dd951cc0016af02bb2a3982aad560672547300052fc32e4a8e604ba5c865c951cc1636af02b92a3982cac7a1072547300058ec20e4a8e600095e8798951cc0012bb0f312a3982cac7a1262547300058ec24c4a8e604be4c6258951cc145ca8c2b0aa398023331d962c8730004afc22eb10e600095d845d621cc0798bac0bac439828b55c417588730094af42eec90e600095d85dd921cc0018bd0bbb243980031761776487300062faa6ec90e6000c5d54dd921cc0018bea3bb2439800333c83764873000666906ec90e6000cd710dd921cc0019aa21bb2439800237a1c7648730046663b4c490e6000b8d8498921cc0113990eb124398023331d962487300062fbb2a290e604bc5c7654521cc145e8842a8a439800676a0176087300062faa2ec10e6000c5d545d821cc1458bea2bb0439828b1754576087305166790aec10e60a2ccd215d821cc1459b500bb04398003366017608730004afc22ea10e600095d845d421cc0b92bf02ba843980f31758175087300068f42ae810e6000d1d855d021cc145a3ea2ba0439828b475457408730516c790ae810e60a2d8d215d021cc07993ac0ba0439828a76e197008730006adaa2e010e6000d59545c021cc145ab6a2b80439828b565457008730516e590ae010e60a2dd2215c021cc145b9242b80439828f7448570087300043f436e9b2a600387f87d93654c00187ae9b26ca980021f61e64d95300061fba4c9b2a6000a6e82993654c0014db05326ca980021fe1d64d95300061fba2c9b2a601087d87193654c00187ae8326ca981fe57a1f43d9530004aec3e87b2a607fa5e86d0f654c001a3ee9a1eca9800387d9343d9530005a741687b2a6000b4d82d0f654c0ff4b90ca1eca9800347dd143d95300070e32287b2a600095e8710f654c0212bb0e21eca980024fe1171d953050d2f41ee9b2a607fa5d83dd3654c0018bae7ba6ca9800317a0f74d95300062ec1ee9b2a600087d81dd3654c00187e81ba6ca980030f50374d95300043ec3ce9b2a6000c3f749d3654c0018bae6ba6ca980030fe1174d95300043fc0ae9b2a600087e871d3654c00187ae83a6ca9828697a0c74d95303fd2ec18e9b2a607f87
  | 16 => 0x4580210072daa4e6b004200e59549cd6008545cb6a339ac010a8b9654673580215176590ce6b0042a2ed2219cd6008545d924339ac010a8fb448673580210053dc2ae6b004200a78855cd600840f5d104b9ac01080336e1d73580210072dc2ae6b004200e58855cd6008401cb6a8b9ac01080396551735802100765c12e6b00425fec8825cd6008479cb6a2b9ac0108f39654573580211e76590ae6b00423ced2215cd6008479d9242b9ac01097fb4485735802103d75416a6b004200ae982d4d60084015750829ac010802ae61053580210053d42e86b004200a7985d0d6008401c72a9a1ac01081ebaa0b435802100574c1686b004200e395450d60084014f50a21ac0108029e614435802100c6e41aeab166101ccc32dd162cc0031b906ba2c5983af330c97458b308862e39ea8b166103e4c32d5162cc00587ce8aa2c5980030f5d15458b3087e2e39aa8b166102e4c3255162cc00147b09a8ac598173171cf5158b3074726196a2b16600095f845d632cc0012bb08bac659800257e05758cb302fe2eb02eb1966000d1e855d232cc001a3b0aba4659800347d45748cb3051ec790ae9196605fc9d605d232cc0a71bf0cb8c659804a57a15718cb3000c6e41aeab0e60018dc835d161cc2218b8e7aa2c3980030fdd154587300161e3a2a8b0e610fc5c7355161cc1451b90ea1ac39800387551435873001c3f42ee4b0e600087d85dc961cc1451b90e992c3980028f61351587302e62e39ea2b0e602ba5e83dd951cc0978bce7bb2a3980ae9720d76547300053bc0aeca8e6118b57815cd51cc0574b906b12a39812f930c96254730004af43c64a8e600095d878c951cc16563d09192a398002c7612325473015d2e41ac2a8e60a2e543158551cc0012bf08bac639800257611758c7301e62eb02eb18e60688df865ca31cc0031bd0fbb2639828e3721d624c73051e66392c498e6004e546154531cc0031b906bb64398023331cd62c873000c6e41aed10e600387e85dd921cc0010fb0bbb2439800637a0f764873029c6fc1aec90e60018dc835d921cc0252bd0bb9a43980025761773487300046fc32e690e6008ccc7358921cc00171b0919243980123760d760873000c6e41aec10e600095f845d662cc0012bf02bacc59817f175817598b30766acb02eb31660a3d4f205d662cc001a9a40bacc59800347a157498b300068ec2ae931660ebd8f625d262cc147b18c4ba4c59828f63c857498b302fe4eb02e931660ebd99605d262cc147b1e40ba4c598003634817498b3008c6fc3ac93166011c9e7459262cc0252bf0faa4c5980025761f5498b3008e8f3a6a93166000d1d74d5262cc0012bf0eaa4c5980025761d5498b3008e8f3a2a93166000d1d7455262cc001c3ac8aa4c59804a57e1f5198b30004aec3ea33166000b1d84d4662cc22fa3ce
  | 17 => 0x184200c3d7455163084091bd0fa9ac61081eb3a0b5358c210246e43aa6b184200a9e8414d630840153b0829ac61081237a1f4358c210052f42e86b184200a5d85d0d6308401c3aa9a1ac61081eb3a0b4358c210246e43a86b184200e1d5450d63084014bd0a21ac610802976144358c215146f43860b184207ace829d5630840159b053aac610802a7a107558c210054ec20eab184200a5e859d163084014bb0b3a2c61081eb3a0a7458c2100566c14e8b184200a5e851d163084014bb0a3a2c610c2297e075458c218452ec0ea8b184308e4f21d516308611c9a43aa2c610c26976165458c210070faa4a8b184200e1f845516308401c3ce8aa2c610803875d15458c218370fa12a8b184306e1d4255163086134bf02aa2c610c26976055458c2184f0f20aa8b184309e1c415516308613c9e42aa2c610c27934855458c218452f428a8b184200c5f54dc163084018baa9b82c610a8b17d477058c215162ea8ee0b1842a2ccf21dc1630854599a43b82c61080297e157058c210052e42ae0b184207acc825c163084011bd0f282c6108023761e5058c210046f438a0b1842008dd87141630840153d08282c610802a76105058c2103d67410a0b184200acd8214163084095ad02282c610802b56045058c210052f42e80b184200a5d85d016308401c3aa9a02c61080237a1e4058c210046ec3c80b184200e1d5450163084011bd0e202c6108023761c4058c210052f42880b184200a5d85101630840f59d04202c610802b36084058c210256b40880b184200ad58110163084111bd07baac0108023760f75580210446f41ee8b0042008dd83dd160086078bce7aa2c01080b0f9d154580210061eba2a8b004302c5e7355160084795b30139ac010a8ab6e0173580210247d43ea0b0042048f88754160084091f50fa02c0108029ea1740580210053cc2e80b004200e3954d0160084091f10ea02c0108038e55140580210056d41eeab004200ad983dd56008401575083aac010802ae61075580210056d418eab004200ad9831d5600840f5d5043aac01084eba608755802102579408eab004213af1811d560084015b507ba2c010802b660f74580210053d42ce8b004200a79859d160084014f50a3a2c0108029e61474580210056d418e8b004200ad9831d1600840f5d5043a2c01084eba608745802102579408e8b004213af1811d160086114f703aa2c010c229e60754580218473590ea8b004308e7221d516008611cd243aa2c010c1f9c487545802184d3cc2ca8b004200e3b549516008401c7708aa2c0108038e9d154580210071cba2a8b004306e3b42551600860dc7284aa2c010c269ee05545802184d3cc0aa8b004309e3a415516008613c7082aa2c010c279ac85545802184f3910aa8b004309e6921551600860dce242aa2c010c229ea145
  | 18 => 0x86130fb0f3a2ca108030fdd274594210061fc22e8b284309c3e415d1650861387882ba2ca10c221fa1c74594210051f420e6b284200a3d841cd65084010fd0fa1aca108021f61f43594210061eba686b284207a6e82d0d65084014db05a1aca108030f5d143594210043f43886b28420087d8710d65084014bd07382ca108029760e70594210051f420e0b284200a3d841c165084014bd06382ca108029760c705942103d37410e0b284215a6d821c165084094ed02382ca108569d60470594210043f43e80b28420087d87d01650840187ae9a02ca1080297a0e40594210052ec1c80b284200c3d7450165084010fd0e202ca108021f61c40594210052f41880b284200a5d83101650840f4dd04202ca108029b60840594210253b40880b284200a7581101650840187eeb3aac810c268f61e75590218451fc0ceab204308a3d819d56408611c5e433aac810c238b48675590210061fc3aeab204306c3f725d5640860d87ae4baac810c268fe05755902184d1ec0aeab204309c3e715d56408613878e2baac810c278bc85755902184f1690aeab204308a3e851d5640840147d0bb9ac8108028f61773590210061ebaee6b204207aae82dcd640842955b05b9ac8108030f5d573590210051f428e6b204200a3d851cd640840f55d05a9ac810802ab60b53590210045f438a6b2042008bd8714d640840147d0bb82c8108028f61770590210061ebaee0b204200a9e839c1640840153b07382c8108030f5d570590210051f428e0b204200a3d851c1640840153d06382c810802a760c705902103d57410e0b204214aad821c1640840956d02382c810852ad60470590210054f41ca0b204200a9d83941640840117d0e282c8108022f61c50590210054f418a0b204200a9d83141640840f55d04282c810802ab60850590210255b408a0b204200ab58114164086114bf03aa4c610c22976075498c2184d2ec2ca93184200e1f549526308401c3f08aa4c610c0b879d15498c218170eba2a93184306e1f42552630860dc3a84aa4c610c2697e055498c2184d2ec0aa93184309e1e415526308613c3882aa4c610c2297a145498c210062fc2ae13184200c5c855c263084018bea8b84c610803175517098c211e62fa8ae1318423cc5d515c263084119b700b84c6108f3368417098c210446f43ca131842008dd8794263084111bd0e284c6108023761c5098c210054f420a13184200a9d84142630840f59d04284c610802b36085098c210256b408a13184200ad58114263084014bd0ba04c610802976174098c210070eaa68131842088de8790263084011bb0f204c610803875514098c210446f4388131842008dd8710263084014bd0a204c610802976144098c2103d67410813184200acd8210263084095ad02204c610802b56044098c210161f3a2a8b
  | 19 => 0x2976174118d2133d674168231a4200acd82d046348401d1a85a08c69080297a154118d2100746a128231a4200c5f855c063484018b90ab80c69080317d517018d210062eaa2e031a4200cce425c0634840199a84b80c69080317d457018d210466dc02e031a4200cdb205c063484019b040b80c69082237a1e5018d210046ec3ca031a4200cd97094063484019b2e0a80c69082237a1c5018d210046ec38a031a4200a9e84140634840153b08280c69099eb3a085018d2100566c10a031a4252ad68114063484015ab02280c69080297a174018d210052ec2e8031a4200e1d54d0063484cf59d05a00c690802b360b4018d2100746a168031a42088de8790063484011bb0f200c690803365c24018d210070eaa28031a4200e8d4250063484019b2e0a00c69082237a1c4018d210046ec388031a4200a5e8510063484014bb0a200c69099eb3a084018d2100566c108031a4252ad68110063484015ab02200c6908023761e2018d210046ec3c2031a4200cd9708406348401a5d0aba464908034b615748c92175e5731ae919242ebcac635d232485d7918c6ba4649081f2bd85748c92103ed3b0ae91924200d2f515d2324841159d0db1c6490803339db638c921006c6ba6c71924200d8d7418e32484a79a8e3b1a649094f331db634c921046663b0c69924253dc7731c532484017c30038a64908861fa1f63545212543ec3ec6a8a4252a5e86d8d51484a7e8843b1aa29080317a1f63545210062ec3ec6a8a4200c5f74d8d51484018bae9b1aa29094f17dc763545210072bb8ec6a8a4200a5d80d8d51484a7cae21b1aa29094e97a186354521297a2108c6a8a4200c5f7418d51484018bae831aa29094b93608635452100727210c6a8a4200e4d4218d51484a5cad0231aa29092f9560463545212962fb88c6a8a4200e577118d51484014bb0031aa29094b95c40635452100596c20e4a8a4204b64811c951484012dd0f192a290802cb612325452125f2631c64a8a4204b64818c951484a7e8c63192a2908129b2193254521025b240a64a8a42539cf874cb31484095990c99662909a3331cb634c521024e643a6498a4204acc864c9314840978902992629092b1d1d9514c52125f2a31aa298a424ad64725453148401e8a64a8a629080237e0d75d81210446e41aebb0242008df835d360484111b906ba6c090c0f171cf54d81210061fba2a9b024202c3c7455360486058b8e6aa6c090802b660373d81210056cc00e7b024301ccc7390b6048405958e8a16c0908038b55142d812175e6639a85b024200a3d84d4760485d18b8e7a8ec0908131d1c551d81210046f43ec6b024200c5f75d8d60484018b8ebb1ac09080327dd363581210064e3a6c6b0242008de8718d60484018beea31ac090803171d463581210064fba0c6b024200c9c7418d604
  | 20 => 0x2ec2e83b1a4200a5e8550763484014bd0bb86c6908029761770d8d210062f3aee1b1a4200c5d75dc363484018bceab86c690803175d570d8d210062faa2e1b1a4200c5d545c363484018bea2b86c69080297a1470d8d210052ec28e1b1a4200a9e841c3634840153b08386c6909a2b3a0870d8d2129d66c10e1b1a4253ad6811c363484d15ab02386c69080237a1e50d8d210046ec3ca1b1a42008de8714363484011bb0e286c690802a7a1050d8d210054ec20a1b1a4268ace82143634840159b04286c69094eb5a0450d8d210056ac08a1b1a4200a5e85d0363484014bb0ba06c6908038755340d8d210046f43c81b1a42008dd879036348401c3aa8a06c69080237a1c40d8d210046ec3881b1a4200a5e8510363484014bb0a206c6909a2b3a0840d8d2100566c1081b1a4253ad68110363484015ab02206c6908023761e20d8d210046ec3c21b1a42008df835d563484011bf06ba2c6908030fdd15458d210161e3a2a8b1a4200a3d84d4563484070fd0b3b0c6908021f6167618d210046fc3ac631a4200a5e859d863484014bb0b3b0c69080317a167618d210062ec2cec31a42008dd87994634840153d09328c690802a76126518d210046fc3aca31a42008dd8799063484014bd0b320c690802976166418d210046fc3ac831a4200a5e8519063484014bb0a320c690803179db5418d210062f3b2a831a4200e1f645506348401c38c8aa0c69094ab32194218d2100747b228431a4200e8c645086348401e1aa8a10c690802c76135118d210052f428c031a4200a5d85180634840153d08300c690802a76106018d210066cb80c031a4303e4e72d506348607c9ae5aa0c690802976075418d218152ec2ca831a4200e1f5495063484cf59d052a0c690802b360a5418d210070fc22a831a4302e1e745506348605c3ae8aa0c690c0b939c95418d2181726b92a831a4200a5f815506348633c3c82aa0c690c67871055418d2181d2f428a831a4267ace82150634840159b042a0c69082237a1f4218d210046ec3e8431a4200a5e85d0863484014bb0ba10c690803875534218d2133d67c3c8431a4301acd8790863485d759b09210c690c07a39d24218d2180f46ba48431a4200e4f549086348401c9aa9210c690803875514218d2133f462128431a42ebacf8750863485d759b0ea10c69099eb3e114218d2133f47c228431a42ebe8f7450863485d7d18e8a10c69080393d514218d21007472a28431a4200e4d545086348401d1aa8a10c690803835514218d210054f426a231a4200a9d84d4463484cf59d05a88c690802b360b5118d210070f426a231a4200a5d84d446348401c3b09a88c690802876135118d2100727416a231a4200e4d82d4463485d1c9ce5a88c69094b935cb5118d2100727216a231a4200e4d42d4463484014bd0ba08c6908
  | 21 => 0x839c165884014bb07382cb108129da0670596218dd3ac0ce0b2c4200a3e841c1658840147b08382cb1080297a0c70596210052ec18e0b2c424aa6e821c165884014db04382cb108129da0470596210dd3ac08e0b2c420087e87d0165884010fb0fa02cb108030f5d340596210052f41c80b2c4200a5d8390165884094ed03202cb108029d60640596210061eba280b2c420087e8710165884010fb0e202cb1080297a0c40596210052ec1880b2c424aa6e8210165884014db04202cb108129da0440596210053ac0880b2c4204a76818c165884014eb03182cb108129da0430596210053ac0860b2c4200a5e8388165884014bb07102cb108129da0620596210053ac0c40b2c4200c3f745516388405878e8aa2c7108123721d4358e210070eaa286b1c42528df8758f328840187ee8aa2c11080b0f1d154582210247c43a80b044200e3954501608840147b093aec6908021fe1175d8d210062fc1aebb1a42e187f815d763484070fd0bba6c6908021f61774d8d2101c3fc3ea9b1a420087d87d5363484010ff0eaa6c6908021f61d54d8d210061fba2a9b1a4202c3c7455363484078bceb29ec69080e37e1d53d8d210062eba8a7b1a4200a9e8414f634840153b0829ec69080297a1743d8d210052ec2e87b1a4200e1d54d0f63484051bf0ea1ec69080b279d143d8d210070eaa287b1a4200a5e8510f63484014bb0a21ec69080e1fe1f51d8d210043ec3ea3b1a4200a3d84d47634840163b093aec690802d560675d8d210054f424cbb1a4200a9d8499763484014bd0b326c6908029761664d8d210052f428c9b1a4200a5d851936348401c3ec8aa6c6908038719154d8d2129d6643285b1a4200e8c6450b6348401e1aa8a16c690802c761351d8d210052f428c1b1a4200a5d85183634840153d08306c690802a761060d8d210066cb80c1b1a4200a9e849d7634840153b093aec69080387a1275d8d210052ec24ebb1a4200e1d849d7634840143b093aec6908029760675d8d210062fc3aebb1a4200a5f845d763484014bf02baec69080297a1774d8d210052ec2ee9b1a4200a5e859d363484014bb0b3a6c69080327dd274d8d210052f428e9b1a4200a5d851d363484d159d043a6c69094eb360874d8d210052fc3ea9b1a4200a5d87d5363484014bb03aa6c69080387d5254d8d210052fc3aa9b1a4200a5d875536348401c3f08aa6c69080387dd154d8d210070e3a2a9b1a4200a5f815536348635c3c82aa6c690c6b8710554d8d2129c6f43e85b1a42008dd87d0b63484014bd0ba16c6908029761742d8d210070eaa685b1a4200e1d5450b63484d1d1884a16c690802a7a1351d8d210054ec26a3b1a4200a5f87d4763484014bb0fa8ec69080387a1351d8d210052ec26a3b1a4200e1d84d47634840143b09a8ec69080297a1741d8d21005
  | 22 => 0x3a2c018802baa08745803100574c10e8b006204af2811d1600c43f5e3023a2c018c0f969cf545803181f2c196a8b006308a7b81d51600c6114f303aa2c018c2396cc754580318472c98ea8b006309a7985951600c401c76a92a2c018802b6e0d54580310456c41aa8b006200e3b84551600c401c74e8aa2c0188038e5d154580310072dc1aa8b006302e5883551600c605cb4e6aa2c018c0b8ed0d54580318171ca1aa8b006302e5832551600c6134f702aa2c018c269e605545803184f1d20aa8b006309e3841551600c613cb662aa2c018c27964c554580318453d428a8b006208ada83dc9600c43f5b307b92c018822b620e72580310053dc2ae4b006200a78855c9600c4115b106b92c0188029ea1472580310053cc28e4b006200aba841c9600c40157308392c018822b6a0c72580310fd6cc18e4b006204af2811c9600c43f5e302392c018822b6a0f52580310056cc1ea4b006200adb83549600c4115b106a92c018802aea1052580310055cc20a4b006200a7a85d09600c4014f30ba12c0188038e55342580310456d41e84b006200ad983d09600c603d9065212c0188038e55142580310056dc1a84b006208ad883509600c5d7d9064a12c0188029ea1442580310053cc2884b006200ea942109600c4015b30f192c01880396a1632580310072cc2c64b006200e9a848c9600c401d3309192c01880396d5232580310072caa464b006208eca828c9600c4a75b703192c01894eb6606325803129f2da8c64b006253e59518c9600c4a7d9643192c01894fb248632580310161f3a2a8b1e4200c3d7455163c840147b09a8ac79094e37e1d63cc72129ce7c3a6598e42049cc874c931c84070fd0fbaac1908021f61375583210062f986eab064200c5d30dd560c84c30fd0e3aac1908028f61075583210053ac08eab06420087f855d160c84070f90aba2c1908021fa1f545832101c3e43ea8b06420087e8755160c84010f90eaa2c19080b0f9d154583210061eba2a8b064202cac7450960c8401c5aa8a12c1908021fa1f51583210051ec26a2b06425187c8754560c861187e83ba2cb10c230f50774596218463b886e8b2c430987d879d1658840187ee93a2cb1080297e0d74596210052e41ae8b2c4200c3f845d165884018bf06ba2cb108031720d745962184e1f20ae8b2c4309c3c415d165886138ee20ba2cb10c221fa1c74596210061eba0e8b2c4200a3e841cd658840147b0839acb108021fa1f43596210043ec3e86b2c4200c3d74d0d65884954dd05a1acb108029b60b43596210061eba286b2c420087e8710d65884010fb0e21acb1080297e0d72596210052e41ae4b2c431ca77815c965884010fd0fa12cb108021f61f42596210061eba684b2c4200a5e83d0965884014bb07a12cb108030f5d142596212571621284b2c4200a5e
  | 23 => 0x5883100537428e8b106200a6d851d1620c40195ae83a2c418c229be07545883184536c0ea8b106308e4f31d51620c611c9a63aa2c418c0f93cc3545883184d36c2ca8b106200e2f54951620c40159f06aa2c418822b320d545883100717c22a8b106200e2e74551620c401c5ae8aa2c41880393e0d54588318172641aa8b106302e2f43551620c605c5a86aa2c418c269be05545883184d36c0aa8b106309e2e41551620c613c5882aa2c418c2793cc5545883184f2698aa8b106302e4f30551620c6114dd0a2a2c418822b320f70588310456741ce0b106200acd839c1620c4014df0ab82c4188029b21570588310456641ae0b106200a6e851c1620c4014db0a382c418802aba10705883100556c20e0b106208ace831c1620c40159b06382c418812b9a04705883100572c08e0b106208ace83941620c40159b07282c4188023ba1c505883100476c38a0b106200aae84141620c40155b08282c418822b3a0c505883100566c18a0b106204ae681141620c4015cb02282c4188029ba17405883100536c2e80b106200e2d54d01620c41159d07202c418802b360e405883100716aa280b1062008ee87101620c4011db0e202c4188029ba14405883100536c2880b106208ace83101620c40159b06202c418812b9a04405883100572c0880b106200c5e855da320c4018bb0abb4641880327a11768c8310064ec22ed1906200c5f545da320c4018baa8bb4641882333a09768c83104666c12ed1906253c5f515da320c4a78baa2bb4641880237e01768c8316854fc3ac91906200a9d87592320c401c3d0ab24641880387615648c8310070f3aac91906200e1d75592320c41193ce4b246418823a39c9648c83129e4fb8ac91906253c9d71592320c4a7c3ea2b24641894f87545648c83129f4790ac91906253e8d21592320c4cfc9ceab14641899f935d5628c83133f473a2c51906267e8d7458a320c401c9ea8b14641880393551628c83129e67b8ac51906253ccd7158a320c4a7c9ea2b14641894f93545628c8310064eb22e11906200ccd625c2320c4031bb07baac0188063760f74580318862eb9ea8b006303e5b30d51600c40587ce8aa2c0188030f5d1545803187e2eb9aa8b006302e5b30551600c4031bb07b92c0188023761e32580310056cc0464b0062048fa87d41600c4091f10ea82c0188123ea1f40580310053d42e80b006200a7985d01600c401c72a9a02c0188123e21d40580310071caa280b006208ada83dd5600c43f5b307baac018802aea1075580310055cc20eab006208ada831d5600c43f5b3063aac018802baa08755803100574c10eab006204af2811d5600c43f5e3023aac018822b6a0f74580310fd6cc1ee8b006200a7a859d1600c4014f30b3a2c0188029ea1474580310053cc28e8b006208ada831d1600c43f5b306
  | 24 => 0x6200a3e85dc9640c40147b0bb92c8188030f5d772590310454f41ee4b206220a9d83dc9640c603d1865392c8188030f5d572590318ed4fc1ae4b206208a9c835c9640c5d7d1864b92c8188028fa1472590310051ec28e4b206200cad721c9640c41153d07a92c818802a760f52590310054fc1aa4b206208a9c83549640c40117d0e292c8188022f61c52590310051f42ee0b206200a3d85dc1640c40187aebb82c818822a7a0e705903140d4ec1ce0b206200c3d755c1640c40147d0a382c8188028f61470590310454f418e0b206220a9d831c1640c40155d04382c818802ab60870590310255b408e0b206220ab5811c1640c41153d07282c818802a760e50590310045f438a0b2062008bd87141640c41153d06282c818802a760c505903100557410a0b206200aad82141640c40956d02282c818802ad60450590310454f41c40b206200a9d83881640c40117d0e102c8188022f61c20590310051f42840b206200a3d85081640c41153d06102c818802a760c20590310255b40840b206200ab581081640c6114df03aa4c418c229b607549883181f27986a93106309a6d85952620c401c5ea92a4c4188038be115498831837173a2a93106306e2d74552620c605c5e86aa4c418c0b8b50d549883184d37c0aa93106309a6d81552620c613c5c82aa4c418c278b105549883181727982a93106308a6e85152620c41159d07284c418802b360e509883103c77438a131062008ed87142620c40155d08284c418802ab610509883104567418a13106200acd83142620c4095cd02284c418802b960450988310053742e813106200a6d85d02620c401c5aa9a04c418822b3a0e409883100566c1c813106200e2d54502620c40f1dd0e204c4188023b61c409883100537428813106200a6d85102620c41159d06204c418802b360c409883102573408813106200ae581102620c4111b906baac418c07330cb74588310446e41ae8b1062ebccc325d1620c607c9865aa2c41880b0f9d154588310061eba2a8b106302e4c32551620c4091dd0fa92c418822b3a0f52588310247643aa4b106208acc83549620c40155d08292c418802ab61052588310247743e84b106200a6e85d09620c4014db0ba12c4188038b55342588310456741e84b1062048ec87509620c405958e8a12c4188038b55142588310456641a84b106200a6e85109620c4014db0a212c4188032b5d042588310456741c40b106200a6e85081620c4014db0a102c418802aba10205883100556c2040b106208ace83081620c4095cd02102c418822b3a0e755883100566c1ceab106200acf835d5620c41159906baac418802aba10755883100556c20eab106301ccc73dd1620c4014dd0b3a2c4188029b61674588310456741ce8b106200acd839d1620c40159f06ba2c418822b320d74
  | 25 => 0x40187ee8aa2c11880b0f1d1545823100566412e6b0462a2adb805cd608c4015b301192c11880333dc832582310056cc0064b0462048f887501608c401c72a8a02c1188030fdd154d89310161e3a2a9b1262038ef8754b624c4051df0ea16c49880b2b9d142d893100716aa285b126200a3d84d47624c4014db0a106c498802ab61020d893100566c1841b126200ae581083624c40f8d8c4bacc49881f2b189749893100636baec53126200cad74d8a624c4011df0eb10c49880317d5276cc9310062eaa4ed9926268cce429db324c40199a853b6649894b17d4676cc9310046ec04ed9926207c6c625d6324c40f958c4ba464988031b5d7628c93100656ba6c51926200b1d841cd514c4096a90239aa29894a97a1b3254531025aa40e64a8a6204a5c864c9514c4096a902992a2988063720d75d813100c6e41ae9b026310c5c73d53604c40187ee8aa6c09880b0f1d154d813187e2e39aa9b026200ad98090f604c5451b90ea1ec0988038755143d813100c6e41ae5b0262008de87ccb604c4015b301996c0988028f61351d81315172a18aa3b026268ccf631c9604c6078be61ba2ca18c261f61e74594310061fba4e8b286320a5f835d1650c4114b906ba2ca188030fe1174594310062fc1ae8b286302c5c835d1650c61387c82ba2ca18c270f10574594318162f982e8b28630887e871d1650c63f4bf06b92ca188229720d72594310051f420e4b286200a3d841c9650c4010fd0fa12ca188021f61f42594310061eba684b286208a5e83d09650c4014bb07a12ca188030f5d142594310043f43884b28620087d87109650c401c5a84212ca1882297a0e705943141d2ec1ce0b286200a3e841c1650c40147b08382ca1882297a0c705943110d2ec18e0b286200a6e821c1650c4014db04382ca188129da04705943110d3ac08e0b28620087e87d01650c4010fb0fa02ca188030f5d340594310452f41c80b286200a5d83901650c40187ae8a02ca188021fa1c40594310043ec3880b286208a5e83101650c4014bb06202ca188029ba08405943100536c1080b286204a7681101650c4014eb02202ca1882297a0e20594310052ec1c40b28620087e87081650c4010fb0e102ca188028fa1020594310051ec2040b286208a5e83081650c4014bb06102ca188129da0420594310053ac0840b286200c3f759d5640c61347b0f3aac818c0f870ca75590318451fc0ceab206308a3d819d5640c611c3e633aac818c23874c6755903181f0f984eab20631ea9f835d5640c41153906baac8188030fe1d75590310070fc1aeab206302e1c835d5640c60587ee6baac818c0b0f5cd75590318170e192eab206309a3f815d5640c61347b02baac818c270f9c5755903184e1e38aeab206309e1f315d5640c613c3a62baac818c0b87cc175590318451f428eab2
  | 26 => 0x71d1c564d8151154bbc0ae7b02a204974815cf60544012bf06b96c0a892e5720d72d81510f4bbc0ae5b02a204974815cb60544570fb0fb16c0a892b1b9cb62d81510043fc3ac5b02a30887c86dd160544012bf06ba2c0a892e5720d7458151004b7c12e8b02a24a96c825d160544012ef02ba2c0a88ae1f21d64581510061fba2c8b02a22cc3c7459160544010fd0fb12c0a88ae1f21d6258151916b9b8ec0b02a202c3e7455162cc40187ae8aa2c5988028f6135158b3101c3f43eeab0662a1e5b30dd560cc4010fb09baac198a8717a0f75583310062ec1eeab0662a1c5f30dd560cc4018ba61baac198a861fa1c75583310051ec20eab066210c5d731d560cc4014eb023aac198c4f96cc075583310043fc2ae8b06620387c855d160cc4010fd0faa2c19880e1f21f545833181f2d986a8b06620087e8755160cc4010f90eaa2c19880b0f9d154583310061eba2a8b066302e5b3055160cc405938e8a1ac1988038755143583310056dc0286b066207ccc724c960cc4015b700992c1988021fa1f51583310051ec26a2b0662e8e5b30d4560cc4a30f90ea8ac19892f96cc151583318461fa0ee8b2c6308c3d41dd1658c6130fb0f3a2cb188030fdd274596310052fc1ae8b2c624ba5c835d1658c40187f08ba2cb1880317e0d74596310062e41ae8b2c6309c3e415d1658c61387882ba2cb18c221fa1c74596310061eba0e8b2c6321a77815cd658c4010fd0fa1acb188021f61f43596310061eba686b2c6200a6e82d0d658c4014db05a1acb188030f5d143596310052fc1ae4b2c624ba5c835c9658c40147d08392cb188028f61072596310043f43e84b2c620087d87d09658c40187ae9a12cb1892e97a0f42596310052ec1e84b2c6200c3d74509658c4010fd0e212cb188021f61c425963100716a1084b2c624ba5e839c1658c4014bb07382cb188028fa1070596310051ec20e0b2c624ba5e831c1658c4014bb06382cb188029ba08705963100536c10e0b2c6204a76811c1658c44f4eb02382cb188021fa1f40596310043ec3e80b2c6200c3d74d01658c4974bd07202cb188029760e40596310061eba280b2c620087e87101658c4010fb0e202cb1892e97a0c40596310052ec1880b2c6200a6e82101658c4014db04202cb188129da0440596310053ac0880b2c6204a76818c1658c4014eb03182cb1892e97a0e20596310052ec1c40b2c620087e87081658c4010fb0e102cb188028fa1020596310051ec2040b2c624ba5e83081658c4014bb06102cb188129da0420596310053ac0840b2c6200c3f74551628c405878e8aa2c5188123b21d4258a31016563a284b146200e2d54509628c4010ff0cbac65188021fe1d658ca310061f3a2cb1946200c3e655d2328c40187acaba4651881f2b989748ca31346c6192e91946200cad7458a328c
  | 27 => 0xf3a6c831aa200c3d74d90635445987ce8b20c6a88030f5d16418d510052fc1ac831aa20095f8758c63546516af02b18c6a88029761b4318d510068eba68631aa200e1d64d0c635440169d05a18c6a892f530c97218d5125ead982e031aa200c3d7498063544014bb07300c6a88028f6106018d510061eba0c031aa200a6d8218063544950fb0fb26c4a88b30f9d364d89510061eba6c9b12a200c3f745936254459878e8b26c4a88029720d64d89512543ec38c7b12a200a3d8418f62544954dd0431ec4a88b21fe1d64989511661f3a2c9312a200c3d74592625464facae3b14c4a88028f610609895100536c10c1312a20095f835d162544972b906ba2c4a88025de057458951004bdc02e8b12a22b978805d162544950f90eb22c4a88030fdd164589511661e3a2c8b12a200a5c8359162544954d904b22c4a880317d9373589510062eb26e6b12a200c5f61dcd6254401aaec3b9ac4a88025760373589510062fb20e6b12a200c5d641cd62545d18bec239ac4a880355d847358951004aec00e6b12a200a3d8418d62544018bee631ac4a880355dcf7158951006aa39ee2b12a326d6772dc5625440187d0cba0c4a892b0fd8974189512561eb12e8312a2e1c3f615d06254401a6ec2ba0c4a892b4bc8574189511643ec3ec8312a22cc3e74d90625440187ae9b20c4a88029b60b64189511661f3a2c8312a200c3d7459062544012df0eb10c4a8c96d9e0562189510061eba4c0312a200a3d84180625440187ae8300c4a88029b6086018951004bbc0aed992a24bd5b305c332544010ff093b464a88021f612768c95101c3ec0ced192a24ac6f219da32544012ef02bb464a88021fe11768c9510043ec22ed192a200c5f835da32544018ef02bb464a88030fa19748c9510061ec32e9192a324d2f325d23254495a5864ba464a8b870fd85748c9510069bb0ae9192a24ad2f215d232544018baedb1c64a8803479d3638c9510062ebb0c7192a200b1d8418e3254401a3ce831c64a894f558c5718c951004bac0eec992a20095f835d932544012ef02bb264a88b24fa10764c9510049ec20ec992a204974819d832544972b906bb064a88025de05760c951296aa18ae2192a203976865c432544072e90cb8864a88031dd91710c9510063ab22e2192a252d57835c43254401aaec6b8864a892f5518d710c95125eab21ae2192a200d55435c43254495acc84b8864a880359509710c951256ab992e2192a24ad66325c43254495aaa64b8864a892f594c9710c951004bbc02e2192a24bd57305c432544010ff0cb8064a88021f219700c95125ead982e0192a20095f835d360544972b906ba6c0a8c8e5de0574d8151024ba40ae9b02a22b87d87d93605445987ce9b26c0a88030f5d364d81518463a38ec9b02a200c3f745936054459878e8b26c0a8c2
  | 28 => 0x28c1648c80155b05182c9193aea7a0e10592320054ec1c20b2464008be87041648c80117b0e082c9190028fa1410592320051ec2820b2464eba9e83041648c80153b06082c91901eaba08105923200556c1020b246400a3d849d5618c8954eb033aac3193869de05755863201c3f42ee8b0c640087d85dd1618c8070ff0faa2c3190021f61f54586320043fc3aa8b0c6400c3f74551618c805878e8aa2c31914e37a1e43586320164f3a286b0c6400e1d5450d618c80147b09a8ac31900e1fa1770586320043ec2ee0b0c6402c3e74551608c80187ae8aa2c11928eb6e0173582320056cc0486b0464118df8750d608c801c3aa8a1ac1190028f61351582320053ac0ea9b0a6402c3e74553614c80187ae8aa6c2990028f61351d85320043fc2ae1b0a640387c855c3614c8a793ec6ba0c2990023de1d611853229e6db1ae030a6402c3e74553604c80187ae8aa6c0990063720d71d81320051ec26a3b026400a7581d51610c80187ee8aa2c21900b0f1d154584322946e43a86b086400e1d5450d610c805958e8a12c2190038b551425843275f4721a84b086400a3d84d45610c80f1e90ea8ac2190029d61641584320071aaa482b0864078f487505610c801d2a86a0ac219003a9509415843201c3f43eeab0064a1e5b30dd5600c8010fb09baac01928717a0f75580320062ec1eeab00640087d81dd5600c9438be61baac019003174c3755803230c3f438eab006400a3d841d5600c8218bae63aac0190029d604755803289f2d980eab00640087f855d1600c8070f90aba2c0190021fa1f545803201c3e43ea8b006503e5b30d51600c8010fd0eaa2c0190021f21d54580320161f3a2a8b006400c3d74551600ca05cb660aa2c01900b271d143580320070eaa286b006400adb8050d600c805958e8a12c0190038b551425803275f4721a84b0064ebecb30509600c8031bb07b8ac0190021fa1f515803201c3e43ea2b006400a3d84d45600c9d1cb661a8ac01901e3e21d505803203c7c43a80b006400e3954501600c8115b506a02c019003aa509405803225c3ec3ec9b1aa22cc3e74d93635440187ae9b26c6a88030fdd164d8d511661e3a2c9b1aa24ba5c8359363544014bb0da1ec6a88038759343d8d51005a741687b1aa200a5d8610f63544590ff0eb24c6a88b30f9d16498d510061eba2c931aa32ad5571d8e6354497ab660b84c6a88028f6106098d510052ec18c131aa200a6d8218263544012bf06ba2c6a88025de057458d5125c3e43ac8b1aa200c3f745916354459878e8b22c6a8ca755dcf7158d5125cae41ae831aa24bd1c435d0635440187d0cba0c6a892f4720d7418d5125e1fb1ae831aa24bc3d635d06354497a3864ba0c6a8ba30fd857418d510069bb0ae831aa24bd1f315d06354497a3e60ba0c6a88b21f61f6418d511661
  | 29 => 0x8acb190030fa1371596320043ec26e2b2c6400c3d84dc5658c80107b09b8acb1901e9ba0a715963264536c14e2b2c6400a5f835c5658c9d94b906b8acb190021fa1f41596320043ec3e82b2c640087e87905658c8010fb0f20acb190030f5d241596320043f43a82b2c640087e87105658c8010fb0e20acb190030f5d041596327652f41882b2c6400a5d83105658c80f4dd0420acb190029b60841596320053d40082b2c6400a7980105658c9d94bd07382cb190029760e70596320051f420e0b2c6400a3d841c1658c9d94bd06382cb190029760c705963203d37410e0b2c6435a6d821c1658c8014ed02382cb190029d60470596320043f43e80b2c640087d87d01658c80187ae9a02cb193b297a0e40596320052ec1c80b2c6400c3d74501658c8010fd0e202cb190021f61c40596327652f41880b2c6400a5d83101658c80f4dd04202cb190029b60840596320053b40880b2c6400a7581101658c80f4dd05182cb190029b60a30596327652f41c20b2c6400a5d83841658c8010fd0e082cb190021f61c10596320051f42020b2c6400a3d84041658c9d94bd06082cb190029760c105963203d3741020b2c6400a6d82041658c80187eeb3aac91941a8f61e755923200717994eab246507e2c329d5648c80147b033aac91941f8bc8675592320061fc3aeab246400c3f735d5648ca0d87ee4baac91941b0f5c9755923200717992eab246506e2c325d5648c80147f02baac91941b8bc85755923283d1f428eab246400c3d755cd648ca5955f04b9ac919413a30c9735923203d57416a6b246400aad82d4d648c80155f04a9ac91901eab20953592320051f42ee2b246400a3d85dc5648c80147d0b38ac9190028f61671592320061ebace2b246407aae829c5648c99355b0538ac919002a7e0d715923275d4e41ae2b246400a3e851c5648c80147b0a38ac9190030f5d4715923275d4f418e2b246400a9d831c5648c80f55d0438ac9190d2ab60871592320055d400e2b246400ab9801c5648c80117d0fa8ac9190022f61f51592320051fc3ea2b246400c3e87d45648c80147b0fa8ac9190030f61f51592320041ec3ea2b24652be2f32d45648c9c3c5865a8ac9193878bc8751592322551ec2ca2b246407aae82945648c80155b0528ac91901eaba08515923200556c10a2b246400a3e85dc1648c80147b0bb82c9190030f5d7705923275d4f41ce0b246400a9d839c1648c80187aeab82c9190028fa1470592320051ec28e0b2464eba9e831c1648c80153b06382c91901eaba0870592321a556c10e0b246400ab6811c1648c80156b02382c9193aea7a0e50592320054ec1ca0b2464008be87141648c80117b0e282c9193aea7a0c50592320054ec18a0b246407aae82141648c80155b04282c919002ada0450592320055ac08a0b246407aae8
  | 30 => 0x8000000002801000800100a00000380000010000000000000001000000000300a0058001003800c004020005005400600900000a80000030040048034000000000000c0050048018002005006000001000300200900000010018000002002000000800200000b8040004004002000800000000e000001c0000030028022000016801000c001002000000a009000000403800000180180120010000030000002000800000200000100140080320000020000000001800400a0000000078068002012000801e006008000000e0010038024006001000000000000000300240140030020018006005000800000a008000800804c026009801800c001001800000e002000003000800800a001c0000010010048008003001000002a00000000000040040010004010000005000c04c015001002400400000080040120000000000006004000000000000e000003c010000002801000a0010078000006000000000c00000000100040120000080024014008006000000a0380028018030019009800c02200c004003c0000000018000004000000000c0480030038014008000001805402600000f008c024000003801400200000680000000140050020012001000800800000000080140000020008040006009002000001400600200640000070058000000013000003001e01900000140020000008148006006000003401401a00080000000300010040000004001000c00a001002800000001f0030004004001000001400000100180680020080030000000000000803c000007001802c00400000080000080010000000010007000000400001100000100020020000000000008000801401800000300000160000000020012002007006000200000e800402a000000000000c007001004400400000e801401000000580580060010038030000009000001c004007000800000400100a0000030002000001000a002000000000200000480100080040008000030000000800000a0140018030000002001000c0300010000000000011000800400600100100640020020010004004015000000c018000000809000000c3f7455161cc805878e8aa2c39900b2b9d1425873200716aa284b0e6400a3d84d4561cc8070fd0bb82c3990021f617705873281f2d986a8b066402c3e7455160cc80187ae8aa2c19940b96cc1545833280f6598484b066402cae7450960cc801c5aa8a12c1993afb2cc142583320051ec26a2b0664e8e5b30d4560cc8010fb03ba2cb1941a1f61e74596320061fba4e8b2c64eca5e839d1658c8014bb073a2cb190030fe1174596320043fc0ae8b2c650787e871d1658ca5b4df04b9acb190021fa1f43596320043ec3e86b2c6400c3d74d0d658c80f4dd05a1acb190029b60b43596320061eba286b2c6400a3e84dc5658c80147b09b
  | 31 => 0xa801000200100580000020000018000000002000800000000e0000010000001002001c00000001a801001800100380040040020138010006001003800000a0000008000002004000801800000000100380060000028014012006001800c000000000001c00601d001804c02c00200a005c01e00100300000220020000004000001000000000e001003002c00000100780340120000020010000004001801800800b00080140240010018000010004002000801000d000000000a016001000800600b0068134000000002802c0040020040000000003001800800200000f800000000d000000402a00a000801400001400000440000000008004006000001801400a002000000c01200a000001400e000001000003a00c000803c0100020138004008000004800000601d006000000e00500b00000000020128000006000000000800800400e0014008000000801c01e000004000400400200380100040050000024002001000003c004001001000000000201d8004000002001800001a008000000000400200080000380030000010006005000006400400b000000c000000001800400e00100a0008004000002000401a0050000000006006001004400000d00180000040000030008002005026000c006000003000002a010000000400000c0008000022000004800c012003003001400e01400080080000000048004080000000801c000004004800000000b003800404a01b00000140060110018014002000003000c00000001080380000000040018004000000000403001b0000000000009020001000600d010802400000000000100020000090028032000000000c0000040010008000002002001400401800f80580180010070000000003001004c000002003003801800a00000040000070010008004003001000001a00d000800001200100b804000200300a00000000040000004000005002003c00000000e000001600001c001000000000300040020020000028006001000000002a00b0010004000005000800402000b017001c00400100000bc0080000028004010000000001402600900000240040000020048002000004000000401f0000010012001003800c00a0030000034006002001800401a00a000802c00402900100040280000028058018005000801c03c001009800000000000580200140050008000002011000001000000f0038008010005000800800600600000000020010000024028006005800402c003002800000003100080180080160008008002002001803400200a001000401e000002000000a003004000400e001005801400000d000009800c020000003000800100000140040000048008006000001000000800400080000040010068010022004012000000003e001800c00e00501080200020050080
  | 32 => 0x6b9075869000002f70000000094c00012967dc000000000002c5000008b866400000001180000553800065800000000000505000000000000001b680001ba05489b541f4800051680003199c2c3ee9ce200000001bf9c9e2f100003f99230000000032608a274b912254109a20d58000805863826e06925908b7233480002a6960013400006d487a8000023202c144400000004408bfa4c7800000000003de08766831be8491805618513b849f9b245cb8ed87f99e9200000006528cd60831d3a7468fb44358bbc3dc2088023000000017cc67b06aa272040e000000011b8f465e61c92675893a60e0d7422e878800380007fc800008618be72c18d261d98da23c95ca7729f7816c000036b821c6012066000132457883647c889100000d0a0ae000040b039465912e027700003fb19100001de612309b000011ba1fb00000000de072116ca3ec1c7c27183ba74318726ee854251187560000bca00018586b61f525219ac4299959800014f22fa9b361179ee628e80002eb00000000b564de075e2a7849a01d00006e5885e00004061a894c400014b058295b62ba028a0001b1058e94720b5161c660860a2940270494000069a01527aa80007e992f282a95bc0841c345f3939e38b9dba0000fbc55c114e24780000d080003340e3a5c194226658a4e2370ce4000057e00000000000000000000010d80fe209065a3fa204e1ea9e826ef82427a88000000000051c031a5a39fee4c505704ca888c00000008051d660000000008001c0060000000004000021005001800a000000000000400100a00540060240000004008004001000800e0000018000004003000002000800200e00000000030018014002002000003004800000100080020000040000004000001807400c000000000400000a003000400000a005000000000300080040100000038008002004000001400200600800240020030010004008003002000c01e00e000800000400d0030004010001000001800000200d800403e01f000800800600700a0004004000000001401a0020028000000000000804000c009000800000e00c0068004000001000001c004000000001c002001002800400400300300000160090000000012000001002000000b00100340020020000004000001006801c0000000000000002008000000000c0000028004000004000004800800e000005001000100080400160010000000000000001000c04a0020080014002006000000002800300b800801400d003800000a00100480c0000003002004800200300100080080000058028008000000001800a0010048028002003025800000000100a8000000004001800c01e000000001c004001008802800e004000800000202100080d401e000015800401c00c01e003400800c000000000e00100a8014000
  | 33 => 0x7591bd213f8fea11484744160b82703000054591c000014427ed0000473000057b88a04609b5881a1b1c7639a1a1ce9b7653d86241979112291800000011e6000102007a9b747fe93ac270204c07a00a632f01924771b1659a9aca64f203857383a45650c422fb0ef02c0917a55993f871411242d01e027b788520001c1a54496940c194382ac984c11aa050456108653588f6816976c0bf926a33e801c69291887d00fc85868ec813197422aa05662980d3e59e91bc3328c521de9f6413e8b521a60b3a157800000d99922c48afa446800032e1a2218889c2693833e1720000352919617b921c5999e984b880004a4877e38a0488000046665d9ee86510c941fd042a21e1eac40f87a40db80000001a06769143e21b874226d107844b838024a909e11a0ee8502865231c19840001f380001c2e64d0a7078a05840eb1a9a04a96f22c800003ab90960001e1e000000000000006b1895400000005fd800070f800000011fc00000000001aaa559000000000000aa1cc25148d4200000004ed00000b5924233c800075d934872806485d102a60000000498016a5f01cca00012f65e785506e6964c52c80000b6965c5be800000015b246a80007b880005ff8d8e62784da0000000000121000000004189cac38f000000000da4af0ad404213a25e995580001af20709ddc1ab091a00013227aa062c6a087f800013ca42e068079895004cf80703eb00002ae01a05288000000071a7371daa2d60dde74180406b489740229498000000038c80003309a3e4291a8e5fa16a45a8827e2261a722b1047e2f415a430b04e61b5800074a8000000000073b991c5df066a653080c3d89ee46d09a4c5cd95320000a8e0000382000104626b98225b10a021cf92aa7b511300e286a60000160045909273a80002c7090c2970cbe00006f25b9206a7f88eaa2020b4e55a0cba6a297b05020e700000b08000000000014ce2949f1200000002369f9065c0000000119e16917686999e5400003c229d854e6c316dc0001c5860b824071e95b85d300000000a00186800044a0fae00015767da00000f300960001c78000000023295dc23d018a00000001a3000000007ee000096e590021a3119d7c00000005cb195600018b07558000128a05e0b9800000013ce18c9ec4021000016494e4000084480c000037e1e7418a93ea0961e5a77808ac7c78b940bc1458067118466419467b203101379b5667d999a5808cdc49e98f668a14d20001ade4b400002b380005a4951c000000000020562d50e2600000007719db0000000066615723cb8000000000000003440001a1e0000000000000000019367c311108238f744a79e7e0f9833c073800070e1a8654f00de584a0ba38799c672200000e6a07a5de90840001236782000005e00e83f38606810839668d85e84bf00000000
  | 34 => 0x92c43a88c787ac907274f949600014e269d0ccc77f9aba0269c301e398861fa08185a207343709f1459511e2000048e7cc07b007d0ab60000cd80000a3275511ea00000007d0800000001220001f50000087a6248000324000025f96b41c59ab87ca0f1600020b02c7806e61a90fc46d198050d9b920000000000118a0ef8b32060197c000000041d89d0256829200017a279987ea4e515180000964698000000000008269ccc0000f4200010302a0000017a8000000123e1291b263d280e67fa0ade7e78000000196e14f80007620b980bd8d860001d28000024c1ad000025897c40001ba852f81bc144000000000004710a745ee944050c050011319f278100002fe15083e1800067c00003209550000000000007480001ae056300000001b3a13807fa23a8dd657490da0b08f2650412c640097126be88b61cc9f067a4019e23c035444500005d2986200000000000b9e4221a8c6371ca40001460000152a00017fa2aa94de10f8cc810d0f7c48e1b84596945e000114600005644dc80006f280000001ed263f9fa226f88aa00003fc00000006ab96723630c6a10517d22e498960000000000104c6030000825800026696ec62a8b2a2071eb86d40000413936a000000036981540eb80000e180000e60000000000053c000007c80003e20f3a0000000000187c0e496246ce06942190000760168420898883bc9704758909a121000058780005e2804400000be4f60d6600010005570c60672834e1c2800000009860001eb637a9834000000035b000081da0044b09028000000065080002738000289000000000001a0800050e800000000007b403d60000b8a3088f304df00987b597ea150000067a80006c8000077a1d5a7c588163258000464800024000000000000000000057300000c50000000000065e000057e1a164050e141e68000000000064c1368000186869f09f46b5828c1688f100c780ae000000000000002d117100001d242c40eea20c1c406db86c456880006e7147a80218b813d9884000120a00002560c2105211580000000b9000006a800000007bb035a165064438203a057c826a1468000000000053aa01c3d11c96000065c45a90f604f9fc281c96480430ae05c900007658000000046410a10160380012053800044319bc612870e392165230e8e8e01f94c600020c20001cde8180420627000067910e00b316a02258000364000076700000bb9cc016d000049c89080bc93b25a687b438f8d501a214e68041d2c5898d4c78294fa21393584151e7c6e6015e000077455791f86809e400000fa01d711a23f488c818b950641b053010b94780000ca86b098127bd000000000001638000645851c726a0a400008564778cc65ae80000000cf08240a6247e8176362825480311ca0ad0e9a48d1dce7970e4c012002e4ef9954
  | 35 => 0x829aee6de948e803800c5b08d607131f5e3e4914268e0d1607e800045c1a5e2d180000001f4e000099821b16e82fa00007c2985e1419b7e2311ce818d968c37b00163000000000000005284ac72000005eb9d201cb9bf20000000000064a650139a78e03343f78bf409d93f4000142806596365db847a7b380002b890064d700001110de26cc11625990c1a00019d27251d3656b81f86d983ec22090d07b693625d8082623903f27298000000000026493960001df82a580a40000110731000042b8dc40000000000000050300000001aa400000000f8982a00009466de000000000000000222407800000011a40000ed438180000478d5800000004958aea734000000004f80001bd473c000065480002a220ca7c00000000178037c9e6822c1e3a5c080000000d526589bac000000000806b268280007ad13cc79c8ef63c6920c6320c4c27680ba66d1e8835c996a04e072c0001d5c36800000000fdc173800019c06da43c9c08000000000000004f70000000000000020a600020c66c50000385800061d1d4668e9a505c8151a2a9904081b9fd22b004cc4c2040a6ef11943b180d279099a634d96c60a3858230209cc6ab1ae23e09b0439f9f8c69e1a6e7d8841c5e6800066500008080000000000050b8000471800069d800063f063452a88607f707401e503b60001546167018c326904200007027819be64bc19fa4208000000000000013bc0fa8ad6000000034880004e980004530d2600000004801ba23d6095c08f000000012d66bc08360000b7625290c600013ae1ac088676b0832000000000015e0609a044000000030105202a094045799b94000189000000000ab0e9021d00000b2912c4838f0480b00ce1cd8eb240b81de6c614d416e046c5aa95c8463911e4e109fa278825a02b044200001740000000486962a02a014064aa006000000052a000020b0000743910664e8c920e712680000b2e00000000000880788925200019264e293000001056000000024d8118618076013b800023492da000127c26d800000d16e222e1c8239e82465589b5c8311bc60e98db63dd86202e80e827f580006ed8aee14d97d413c07524a3093024a0d7625596a67f318a40000f8e25010cc00000001c706dc20f9d424cb06ae16b1c7480d9d4006aa0b876c836c71a922023fa08410e10fe1c500004d980000b780005098e4a000083a263000009b1d52468004a22b925a5b800006451796000000017f80005bb99a20cc000079480005528cf4536983c695061e35f1cc827b8f1c3739e9e7db9258744000070807206839f1a5501aa62c58dba4761cd81e80d32000000000011ce052116e00000005ae07fe43519683f91df21a2838c00017587859c1e5d59d6c5e4004214503f64748abe71f8d567fc1b3e16b89e86f58afe1730014309113a2db
  | 36 => 0xf8d103b117140b619e60c08114271069c770930e70a0dc04e608121c48dd4097950e36e060c0ba924a37213302b7094e43782163b70f223c204b005b1dda2f8184678603d239911c84890c9c30f028604e83ca4bd141a56592a400014cc079000081206843d781a854a02e834c100e1cf0e580001c5c28f8000000201e73f0e6845a11d481e162e27592646ec1e5076613284741f182271e1424287b21bb9c062039ed872e839e39589225d79bea3041bec1551f9200013f24a400003450c281660ac810c800000000004d11f7664c800036a8228811834c4b508d601a81d22c28ce620299184c8000001d82e4000000039d8000000002c0001f3200000000c300003d7024a0c8813017d0b743ac0e8055b19c88330800612107a77e93ee46c9f442340d940001dd87e388be7108d9c64a101260381dc06d982c0530e2239b0a2e4d3824e0190d403fb869a49003b03c79ff850a8264570000037a0000130993e1d1800051a00000469386000107e456800065700003538f545cc98566408c7460d97a8631003e00013d6269800000001d844f80000b41ab642b00006a895d437f829c000000070e80001be80004ac8cf600001940000f4800016d000009805e7145028612c841700001b00a867ea0ae400000002f1990c00012e87089d300001ae616a80000000e5a000138e00000002868b2272a0b0055e8ff48249004000000008f9d1240c88fa59b99744d4099c72f000060e935e796000044a84021ae84b4761800043b1e8016781ae757800066b981e6f6998e00000ea2779bfe00000001ce0000000175a0001f606bb13f014e80a035e02b07741ffc04991f607580000001c4a497095e74200003a10000000133c27a84be0da955605f097061e8dc622380006f3910e10687c6000009e0001b86000167e000135639f000000000003d5932e06f969605c9d1613c80002bb000271c99ee1f880004e80fa40000be40001b7c5441e8a24f01a61b490d843997300000af637c1d007450bfe25a8ca04a9827a42500001001a525c29fce04718d85191afc3cd1fb80c918166ba9c644110da20518e924310bce1ba130c4ba826e381121850705da00015386c29b282e3862633b000000010a676519fe747007c5710f6c6359bfa194033624e00008088000131000000000004cc80002f200005201c4600000001619f987c4180a000061c229800021280006018f20000000066c0000768000058f1d7a0b115ba21a9ae87ab9a12367800000000000f600881ae09442a41eb01c6016254b94622c3982082d9d321c9a0707688cee26097d65790b3c522000069c00003f5800000010c20000000000164400005dc0000f5a80a1e767b009a41c41b0038a80001788f3672c80005dd800000000007cd000062b80002df0f06680195e68a800077587f64b397d
  | 37 => 0x1ee00391ac804b14fc5e1037e0240a2082a19b645720c80000c122520000316800027c80006a1107c27800000001972303923a0620000000027200018d40fd0db07eb000000010ce642200263b9dcc1a788e600000002bf00005eb1d821d91a4412802626c195604ac0006721846242f922814e1cce5a4108e000067e53e20be0001b6c0ef0000560000046b0eac094860839b800005e91320a800003d39a5a6b50a101a1a08c04f0000072173475297f05dc8fd0230000050800003a1964a2b6209e428955a4f18d202450cfc6dc0bb05d41a425ab800070a810a216105e70416621fc956a05f959e24700007918b961f6203400000000001de22fb8ed20b71bdc00000002a3133a000000009100806c8833800018e25a6161414315ea15700004bb16161bf0c181c0033243e9fc853603dc00004460001674064172882600007348f520000eb400002ba00019e269200000f202141db15263be9024469875a464097c3f180a266702c803104f428c06543ae0d0250016505ad947634380004231b3c2639f467090d463a208901f28156000000009a0e7253b80000000b5a00017784790182169966c0c10c7c27982061af83586e2813662a0d825881e1c6a013de08c093e6208480426005e4e498a2728800011c1dfc5509dae2ab18000ab9c0e56698e41711dec753055230b8ff81b206400001d500000af000000004b491d674284bc3c28fca2d980002d90f024810ebe7f1800056a0000000064c0000c8400010bc55207e674100000879ec6620102a5d887ce00003627de800050d00004f518fa0000dfa43482026170e52000004652085a835a00000001cbe0c494120309c66122821200001ac013a03c27500005e3883c40616a858e18b659a08d86ff00264089f882f48c540000b6c2581f845c58f844028128438878c11c908029a8000686127600019d85bf80001dd800034e032813f01f02bc98547d9801a000000000000007488bde344995a1b88000000146c0000000000000023e0000243914a1b095e800001c0133800068100002ec88844898000000038e7df987000c8fc27060cce1f5835066188d40a6000063e0000000098a2e8800058b0000581800061f80006780000000000000000000001c70000000008b10b60000ce0000000032d9bd80000000000085c10b000000013e600000004a38bd41961e4a0839e3c5c216f079380005298a0a0000000000045827b15360000e60149957e00010361f4000054304c8000189813500004459d263171100198000000000000000b240001e7a6eb8000722800002a9c760d98000000037200014926630000267800000000007ee99e83279fec12e0862000207e3c4990a2d30ec200000004471a46723800021c813217795f463796cc4a115d00000e0a2c99ba67d6841e2051ef075
  | 38 => 0x4189ca1558d62139049e459000021c15da49b00000ac9e7800007687f908ec07b9eba3910bd852b157454e830a53a1bb200018280001df6547937626c80001eb80000021808000202659e0f60000008e407004c000059000019d469700827c3934c10211ae3731db40719d4e5da9d6a5ef80b269b1a3468b14fe6d187064a18a3c21f16e64190000301800000017bc5c38da40000af424b1e004ff845a1bc16607e0a05c3a580001af0a5a31c937077c000019580003a286ec3b88a1244e1b4e00007e062e845060c8e7828717b4000144c00019be00009780001ef23a7029a65618ea0001aa80000e6678b9abc01487d42b2862845e15f60001e8406e1f5c357879072d80005d38eee000056e630968a50c9f947a714c255b80004ce00006c7849822780000000f2c0000000000000078d80003c600005671bde00005f800000000001840607168602e1cec2c11d184858b2c5f2196657c0d06819193833680285549ab027c14023ee02ec2e99acc2010b627da8a983a605a040407500688e3871880f60ec98f07e70b366c387707791f54380878a289969c51f80d428d83e06b69f2e0000000633800051599a07099c5a5830d3c2b4800015d8a687e58f3814882244d48d3a2ce0aa2676a0a27b7000017188a818600221e9866833008943d311205f887780000c3418e80000d7857a15898cc1c8940e72d000000000000000d340000000000000000002080000d1a000104a000000080b8000000160452d97e6241000000000002c1800000000006ac906036100005a003680001b0216014ca1630000000144a31285d00000a7c0000000000206264107c210f1eea7fa960e1c119c40000326136124800000008049ad07ff850e1569d8c281981a37b80000c70cd43e680000001bf06d00000000000000014d0000173c000076e00008504031026000000018f8000000040c69600005d200007be1f200000f6a0000ebc76e08203a81da67ef80006a500000001bb81ee0000034000022c85ec4c98854384123216f86903e780f039a981026b1722677903839395aa6be0b9a25c8f2481d06e02dc18ac4511f2607502fc5b020525078b860319af40b38f005e200000c0202a000115264904ec018892679c09507df15de00e85ca00003c000004180000000000203a8300b5e00004e80dd00002de0ef823b95207139efc28a9e0c762936c1f216ac7561a1447d00001e880003bb0dd80a11a3000000004c080007e900004c580b66a492e64e095447ca85e665f8ed6735875448a8a2c4b6094206c1b4a4421cfe0ff8e5c34a1b5a31b8f505ba8e462641b6200010aa5ce113c2d416f8000000000000000d183de2cd00001d309a80000bc2000000000000000000cae25e800000a8786000000000000003fd800042d0d1e00006f400000005ed80
  | 39 => 0x574245800000009bc82190f80be8dca0408e503ca92c03a796083658c5e237809c1ed963e6f8896c4911a5607109020d4957819f03e402513743160b8065392820410a5453706621840728049059a29e8f14265a06c5f70fd80668f9c79b90b248b97ca0d011c210107c0000044a5211ce481606ce49c12020001a081e7854a07f1ebc5dd000005a00006ea800038600001f90170000000000000006280a9401e11485b58e4278c183e70f000000016de000043a0001e8e79817de00000003b2800064b80000001ac0000000070d8000249000017f00001b90000000052a63412b87d200001e000583298b7e0000cc475c18c000003840001c6e000201a4d000000001f58000101a46a1efa22f022a1e600001be0000000000080c800049e09585d0096618f112626e99ce4d29e345fb80003d009200000d2c0001fca11d800000014b8699070800000004be8000000000034a8ca453b081a12e8f0e68f09326a797462f5800000000002fc0000000115423f080214b8d4400014bc5c717fc81f000019b0da8268000003b018e00005fa000000035a998a000150a0001e48180800000000003bf00007dc80e21ad80000000a4200019484bf95fe01500004818000000106a0000d8836d1bc80b190664e9000056c000000010ca46300000000000000000031d94a000017f2303000009e000036b000021698f47f6124e2ab9a626269d1e14a02b682b0ff03660f7a0cb0e8c69a9efe2960988000010e63b0000000123c0001d024e3073038c0d1c64380000000fe04c404d60c8000000000000001d3800000000001be437d00cc4b90e244d68000000188c793074a717847856f9f563fe965e5058d540d2906e000000000006d43e007f05b600000000c30786a09c0000ada6b396823121dd4761000012998e629014b42b9800043d048250197c22b402aa42e91b6527917278f816642808a400000006bd800052b9b1265401d03a90c360000a6c5760e744c691362318546000188a27487ac77d02001ef8ece5dc00006730ff20810a9232d1c025f9000057f00007849f02540800005b926666c918000016b23ad98140001d687fd117c1e7000014480000001f3c58600006238866430149403d0e403988ecc2a282605fb082800000000ce90ee6319ba419e19064821dea05105d45640dbc0001c000af11ec7db000076a1e6a37f00004ad000000000ca40ea04a7f80d041561ebe318815a57e8e12281146a632948a64693c013484945fd04903d9a0a01258f8a6cd03fa1d9832a5f684245bd958e47c070c7a80f0c387000031e800040d1fc00921b4413706ca47816d40a890686e09174575930624606cc08d96584168c1e19192a04cd1fd45b203a838d8eda7f681cc687000006110a866a9fc42d0800000019c220b9ce000000000e897d800020940
  | 40 => 0x14c800009d037646e175c6a603d000013aa6c68a3478b05d8374044e50f049c000000000000002959dc42ad147c0001e940001f8647f80ee10889680a0954c4bb986e3f692ca5699d722850ee056d05bc006050228200006f307bc5d51cf40c5841645800dc61402c04df8ac2004006c5b6872a3138ca23ef93b050b00005f180004e407fc25491e8593800000011865ea8c6c7ef0a160d71cf801403185e49ab430a800073690e83da000028893126fd9f2c509029619090484660be643c005c43a8ede73512be0f188486d2109c1b98a4c6fe1bc05caa0001479f9a4e005082d80b6a4f697643e597b262c838807b17b877b883429c877c7959dd264482502ea00007c108e0810103c15a8000109881e00002807b30ba400015144a88acc15e0e0e80f99dc02483e85c99a327a68c1400001ca4240934044975262d0ffe000082a00019f401800006a70d244021b9e08e80000fc099411f18420de000073c85b274f16467eb81e623387cc2ed80001d1041231004aa4f816327cf80000f500001f70c8623a000000000007cd8cfe0de92887ea92b6000137a0001fde2ee00002fc80243f51e44238871e8201e0e061825c2f000004850faa57180002e21ea44ae96f40000d0872a89fe078946e06e98944b700002761dc05c6884c1ee8ef42ae857c82c800036480001b419a4000127416da0bc27d945c3080000121800056800007d280001a58000000000019e80003e3108a09f01b256b1c687271d60019800014d09124500ec07640a0c815000000015ec2d220820000000718032e4f8841060080000001b6a64b00004b7800000011b01790000117023400000c0000000004b860061e015c0001cfa28e000034000000000fcc724000000000000dc19ac0f6856c000000036000000000000287800000004b618380004db93d24a28a7800007de7e2879238b0000702816456080000000000674198830702be3cf125e35680fa00017a0000067254900007121d445af93c87070f6e58c0000000066600000000000ee668b806882d000000000000000000000000000013c4000107000006ea0000000000000000000000ee0676000000003f12980001c8c0000b84000000072e11761bd80f256186303e8872482299a878c800017c0b8c2da07820001b722cf93a8211800000020ae00000000000bbe35f80004ab8000595849235200007979aa029289fc0000000040000038301580000cb002d000004d13ba00009e40000abc7b291ee52300387a30220000000076f9adc7c90cb26d30b1a764837c1f69b5e2a8191e4be171e7e803b415a1b2c3669b2e70c92946e39e2009998bc7890e000000c3e15219fc00012a84d803601759a7a34b8c8e0769262185929a5df90dc4930000000000016e800059f16d23f880003e986746e209f837d80000000
  | 41 => 0x1b180001459c561f11e262991ef61a909766fb8e540000000000152c35b8c502220cea47c88420011afe3d91b8c2228000000000055f00004fa00007a999006139074000167600004b25e9144e29113c236c9b086fd00004c10be200013f600003f852e98e859c03c40b8800078400000000f7200016345620fb64d500006cc8d0c6ed00001e5800017800002ac0d180be000000000007669584359000075e0a8400002d26898c027e005c02ca00002d28000000184400000000000e9400000000001abe4598f907ec1c5417d80c80001a9071b000037680007678cde45b043031a155412a126e48b1f740000ac66f100001628b304e216283ec96ce12b97f84ed93d03b914740480000000000a2c61a205120c807148ea637499f81d88eba089814201e93ec75b83ce0a416b046699225291f1c72b85964b3000014604481a39c040000000000000065e92225ce8bae000000065b00000001e8629b978621f8e1a000149028a1a24054066e24b85c235706de24195306e011be0001cc668405724e700002a7000060614c8181000014f170063800005cf85881da8c440001c447f4119c00002e0000000060c153e000054c66e9f3a1b60504519a01845f800021a000050600000001bc21300000476910a7ec8efe1388bb400002a438d000000002380000000000089a0001c98000000061b00002f68000564850a06d0caa6a2115e14b18240a503901e11db62ff19c036f88cc4c60440000028800000003230000000121e2978000705800000000005c600000079fb670480f800017e00000c565301d4842c11565af199e77788062ea83ee0001e640d212ac3cf88921581a962a9000073d985a76f04545d980000000c266f4169e0000c6432b1d3439780000001364000125400000005e5000078a80003ea110430580003e601a42c30c8a3cc800000000007d3000000000004a71610000000000000002d70030132985200000004f912803f01be030280000781e6c00000bc000000013a80002fd8198000111800000002610c88000200a7b0800043900007fd9622283933620e0d7a75d00865c30cf83aa05240001ce60000a7e4fe96fc5629b6437987724d18f945150fc41a800006e413fc30c949c5e099b8174953401c905017c94f4454192030e0ce863c881044d0bcc0bd029e0001b6000000005269b2a07f8000016803c7c203aa31f8000000000015118644c718661d3978c35c0ffc000000053801f64849eee2100ce2000000037900007050ddc2ee8b7a5708f7e38806122308a484d080d826aa02462980d64c288b41938f2869f830e3b40b9c77210c87a58af8
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x155297e07754c110004c6e5181dd5304400155297207754c110005c465081dd5304400174192207754c110004d4a6241dd53044001b1384907754c110006c461141dd530440014c8965c8724c110006705c9811c930440014c897588624c110006a261162189304400171194d47714c11000554a5c85dc5304400171194217714c110005c465075dc5304400135395613714c110004d4a6354dc53044001b1184553714c110007445d154dc530440013539560b714c110006321d8825c5304400135394614714c110005c4650751c53044001b1295610714c110006c4655841c53044001b1375610714c110006c41d5841c5304400135198d50714c110006c4613541c5304400135198550714c1100055425d541c53044001b1184550714c110006d0dd5821c53044001b4075608714c110006d0d51821c53044001b4154608714c110004c665087545304400195087dc5514c11000654e1e87545304400135297a1d514c110004d4e5287545304400135194a1d514c11000594e598754530440017139461d514c1107edc42518754530440017439261d514c110005d02498754530441fb7129421d514c110005c46508754530440019529721d514c110004d4e50875453044001b129421d514c110004d4650875453044001b119421d514c110004c46508754530440019527421d514c110006541d087545304400195087dd9514c110004d4e6176545304407d350985d9514c1100065421d765453044001713945d9514c1107edc4251765453044001743925d9514c110005d0249765453044079c51761d9514c11000554e5d82545304400155097609514c1107edc4a5082545304400171194209514c110004d4a62725453044001351989c9514c1100065421e7254530441fb712949c9514c110005c4652725453044001353985c9514c110004d4261725453044001950871c9514c110007505c872545304400135398589514c1101f4d426162545304400155097589514c110005c4e516254530441fb71094589514c1107e4d4a6062545304405735198189514c11000554a5c62545304407955197189514c1107edc4a5062545304400171194189514c1100079058862545304400135097616214c110004d4e5185885304400135194616214c110004d4e637588530440019535121d214c11000654e1d5148530440019507521d214c11000670e088748530440013c2989c9214c110005e06527248530440793c0985c9214c1100067021d7248530440795c197189214c110005e06506248530440011399421d5148110004cc6508754520440015319421d51481100045c26173545204405756097609514811015cd86606254520440017219418951481100055825d514852044009c6076545214811030f181db7548520440d1ac086e0d2148110
  | 1 => 0x40f66074195614800103e9819774585200050765065dcd614800141d9419473585200040fe5d84194614800182d7261065185200060e5c184194614800103d989d065185200061c5c181194614800141d94196731852000507650655cc61480014559119573185200040f662841d9514800182d84608765452000607613301d9514800181d844c076545200060d613101d951480018398484076545200060d611101d95148001c533044076545200040f6508758d514800103d94219758c5200040fe5187d96314800103d94219750c5200040f660655d0314800142d94195720c5200050e650655c0314800122d9421951c85200040fe5187d96214800141d94197734852000507650651cd214800122d94219514852000417261305d165c400103f985d074597100060b5d182d0d65c400181d7460f42597100160721d5450d63c400141d94a177358b100160b21d5450962c425dc0c735514258b100040f653865d632c400103d98995748cb1075e2320d7458a32c400141c975514358d100160721d5450d634425fc0c725514358d100040f25d84d45634400182c726135158d100040fe6374d45634400182d84dcb5158d100050b25d54509624400582c875514258910977031cd54509624400103c976135158910006071cd84d45624400103f98dd351589100060761373d45624400188d7420d62189100054c650709cd5144001551931c2735451000558648709cd51440018347661073545100054c650701cd5144001931841c0735451000558648701cd51440013519020d72545100060d1d9841c9514407935190a0c625451001c1d25d860c951440013539361370545100064c61374dc15144001933845d37054510004d4e4d82dc151440579518354570cc5100054c650805d6214400155193201758851000558648805d621440015519390175885100064c611405d62144079551938c175885100055464e205d621440018d07660073485100054c650751c5304400193075610714c110006581d5821c530440011399421d514c1100045ca5e8754530440013319421d514c1100054c6508754530440011739421d514c1100064ca508754530440011719421d514c1100064c6508754530440011319421d514c1100065464c8754530440019534321d514c1100065410c87545304400195087a0d514c11015d5425d8354530441fb7129420d514c110005c4650835453044001352988c9514c110004d4662325453044057552978c9514c1100065421e3254530441fb712948c9514c110005c4652325453044001950870c9514c1100055425d51cc5304400155097545314c110027141d9514c5304400117097616214c110005e0652324853044001619941d4764c11000594644751d9304400145897550764c110004d4e4584dd53044
  | 2 => 0xc001a0d86551421893000531245625c4624c00124f9858b51189300068361162d44624c2299187061075d853000646dc184197614c02111c985d154d853000546e4174553614c00181c8759154d853000646dc184d47614c2259187061351d85300054665075dc3614c001551911d770d85300844765387552614c00181f74219549853000546650655c2614c00111d981d0655853000447a6065dd1614c01f41c9759154585300060721d64551614c00150d94197725853000543650651c9614c001c0d64550725853000523650611c9614c00111c9761351585300064361372d45614c00184e861cb51585300064361072d45614c0015199419770585300054665351dc1614c00111f9761065185308a6469c184194614c00111d989d0651853000507259855d0614c00181c865d1541853000543650659c8614c00150d94195721853000551644655c8614c00144c96551721853000447e51819d9514c00111d98a10765453000607259841d9514c00181d84990765453000513a4a641d9514c00105d98190765453000607610641d9514c00181d84d80765453000645613101d9514c00191984840765453000645611101d9514c001c536044076545300050765076989514c00181e841da62545300044765087589514c00141d941d862545300051325d62189514c001a456260462545300050765076d85514c00141d941d961545300060721076585514c00184c76209615453000447650865d6214c00105c96611758853000447e5187d96214c00151994195708853000554644655c2214c00141d9419776485300050765285dd9214c00141d94d47764853000507650651d9214c00145591194764853000703551421d9214c00141d94d44764853000532642211d9214c0010cd98084764853000523650211d9214c0014c990084764853000730481101d9214c00188c76612624853000507650659d8214c00141d94216760853000507650655d8214c00141d94215760853000447650865d4214c00111d98195740853000546650655c0214c00131b9460765d813000546650655c7604c00151994d4571d8130004c665086547604c00141d94a177358720977031cd5450961c800181c7361351587200060761373d4561c80018cb76600734872000607dd183993654800703e98dd164d95200040fe6174193654800142e96dd142d952000417e6130dd3654800103f985d074d95200060bdd182d0f654800181f7460f42d952000607e13305c7654800181f844c171d95200040f66374107654800181f7460c41d95200060bdd182107654800183b7460041d952001607e1d5450f634800103d989d06598d200040f65287d95634800103f946077558d2001c0f261745516348213434915d15458d2001c0f26174553614800142c9755142d852
  | 3 => 0x3001c0fa6374593654c00103f985d064d953000643dd182d0f654c00141e96dd143d95300040fe61741d3654c00182f7460b43d953000607dd183d0b654c00181f845cd71d95300040f66374107654c00181f7460c41d95300060bdd182107654c00183b7460041d9530006075cd84197624c00582f8755142d8930006075cd84d47624c00103d989d065989300040f65287d95624c00181d7361065189300040f660655d2324c00111d94e05758c93000447660655d2324c00111d98d45748c9300058365065189324c00181d7361065d853000607611731d7614c00703c985d154d85300050725d5450f614c22581d7361351d85300040f66074195614c00103e9819774585300050b65065dc9614c00142d9419472585300040fe5d84194614c00181d7361065185300060e5c184194614c00103d989d065185300061c5c181194614c00142d9419672185300050b650655c8614c0014659119572185300040f662841d9514c00181f9361076545300060724d841d9514c00181d8460c765453000607613431d9514c00144e92d0c765453000417660431d9514c00181d8410c76545300060d613101d9514c0018398484076545300060d611101d9514c00141d941da325453000607a10768c9514c00141d941d832545300048765086547314c00103f9461f658c53000447e5187d96314c00121d94219514c53000417259845d4314c00141c96615740c53000447660655d0314c00150d94196720c53000543650655c8314c00154591195720c53000513259545c8314c00103d9421975885300040fe5187d96214c00141d941977348530006231d9848c9214c00103d9421975085300040f660655d0214c00141d9419573085300050e650655c0214c00141e96e1174d953000447e61741d3654c00190f7460a64d953000646dd180993654c02111e98dd164d953000507a5b74593654c00191b74e0164d953000447e6174193654c00121f9859064d95300060761b74d0b654c001b094260042d953000607e13605c7654c00191b8484171d953000646dd180907654c00111d98dd041d95300060761b74107654c00190f7460841d953000646dd180107654c00181c865d154d893007e43e1d5450b624c00160c9655142d893000447653815d6624c00111d989d0659893007d07e5d64552624c00181f87591549893000447e5d84d46624c00111d985d3519893000546650655c2624c00151994d45709893000447e5181dd5624c00111d94a1f65589300844726174551624c00181c865d154589308954524574551624c00151b905d154589300054665075dc1624c0015199419770589300054665351dc1624c00184f87d9562189300058365065588624c00184f87e1562189300058365085588624c00128d942056218930004b124586508624
  | 4 => 0x8c401c0d5450a76cc93108e0721d5450f604c42581c7361351d81310060760d75dc9640c65dc0c325d57259031987030c974551620c40160d939d1545883100583e4d74551620c40122d94215705883175e23a09845da320c5d788e7261d648c83100507e5d85592320c40181f879d5648c83100513e5d5458a320c4012399421572580310068655183d09600c65de083255142580310068655383509600c401a1a85a12325803175ea2a09848c9600c40125b98552325803101c0f2617455160c840142c9755142583210040fe61741d1658840182d7460b4359621006075d183d09658840581c875514358e210160e21d54501608840703e98dd154d8d2100507e5d5450f6348635a0c8655142d8d2100487653815d7634840181f87dd154d8d218d58364874553634863581e8755342d8d210048765387d47634840121d94a1770d8d210050765275dc3634840141d949d570d8d2100507653515c3634840121d94a167618d2100507652859d8634840160d951914218d218ce8321954508634863581e766135118d2100616615701806348401899845c06018d210060761d54d08634866160d959514218d2197683e1d54508634865da0d875514218d2100583e45545086348401a0e926135118d210068364984d446348401a0e726135118d218ce835c984d446348401a0d84a0b5118d210068361182d446348401a0d8490b5118d210068361142d446348401a0d8550b4118d2198c8765285504634840141d942157018d2100515644855c06348401c0d545097018d2100507653515c06348401459950817018d2100526650205c06348401a0d5460b4018d210068361542d006348401c19545c14018d2100722509705006348401c0c63a15748c92100549646855d23248401c0c63615748c9210044b663515d23248657c0c63d45748c92133e23a1974d8e32484a79c373600714c9210050765287d8d514840105f985d36354521007035d14218d5148649a0c6361232545210255125d325453148409644964c9514c521977031cd5450b604840181c7361351d81210060b60975dcd640840141d942157098c210058364a74551630840121d942157058c210048e650855cd60084016199421573580210068a55182d0d6008661c0c325d15458b30006071cd84d4562cc001a0c326135158b3000447653815d632cc00111d98d45748cb308b60721d5450d61cc22d81c73613515873000447653815d662cc0bfc49604817598b302ff22581205d262cc02341f975915498b3000607e1d6455262cc00111f976135198b300044766174d4662cc261c0c625d15458b300068318984d4562cc02511d94e1d549873008d0725d6455161cc00141d94a1776487300050765351dd921cc001cc120443764873075e231d98498921cc00182f7460a64d95
  | 5 => 0x8d8259450002bc39931338744c693c28e000d71dd32c35c000091d0000409cd4e065c4d8ae38c400fe000044a10041da14c000001d936e63d1387f14e8993796d0000005e01e08c6d0e8097370998d60234167300f825480979121412f42912705b0143d862958490220f99b31ac43480a4133a76c87811254884299ea4e62ac390002f80fcd69330884a03da05256211248332462192b8fe3da000000c605e000ad09308e7f4b89373424a40022f0003b0001fa3ae6607ba0808488d3b000000000b908c09a6d90124a10a0013125d2a498cbf1750008405d27c02a6311f80802401030020000401802100060000f0041504c050080001803078040180200000000090100608405014000040c00c090001802003088030180000009024000000b004050000d038150180407c0105004010010000d0200100808000040240e0080a0180001c2201001010110040007c070040203c3200c02038180380001806008010082604c05000250140901c07004000380202402024010080a0041700800000010180306400010020000001000014040440104004000230082403c080000401010004130040806801018020180302401014040240302400004190180301400000030080103c00018030140202c01014000180301c050200200400000090040d010040040002c000040397782cc15450960cc801a1b3061351583320040f65287505658c80181d7460c41596320060e5d180105658c80142d92dcd755923297f030c9755cd648c80182d825d47159232006075d5831c5648c8018397560071592320040f66287d45648c80182f3261f51592320060b0c987d45648c80182f2161f515923201c0fa6374551618c80141f97551435863208e07e1d5450d608ca3381c87551435843203e2921d42505610c80103f946077558032086075cd841d5600c801a1b306107558032086155cd811d5600c801a533060475580320041d64487551600c80703c985d154580320050725d5450d600c801a1954e0143580320050b25d54509600ca5de0b30551425803200686cc184d45600c80f8a887509405803275ea2a0d42501600c80181d74e0d6418d51006435d282d0c635440181d7460e6018d510060b5d182180635440141d94d877358951006076137318d625440182d7460b64189510060b5d182180625440111d989d0638c95100705591435c43254401c2564509710c9519274190d425c4325440103d94219700c951086075cd841d560cc401a1b30610755833100694cc1811d560cc40703c985d154583310050725d5450d60cc401a1954e014358331086075cd84d4560cc401a1b3061351583310040fe61741d1658c40182d7460b4359631006075d183d09658c40582c875514258a310040f653865d6328c40103d98995748ca310160e21d5450160
  | 6 => 0x1a80c200109111290878140dd4e2244bc80000004c0000013c3f0be99a000000bf80045456428012090614001a042602c1b8a24666646c08a094348350400009900019337e1711c8be006250ca0573760000011700000076a2d0408d51e2161c62d0108520006240006f32406c0000019e178bb2310000d807000372854ca96c43a0000008026442c1d18300000000000000000001d3000584c20000008f45d8ea0002343f0e7182208001b043659c0026d1e8555341f62c6258300003f0090c51881382f40012f2066ac3621f0647fd41a2e2f09dc000000003793500046852d1910a0924ed301e03e42b05022b344598f28550f42412792735e3bcda9183e00c08a0c30c894cbb8000ca1ac0d14e2be498920003360013d9392920010682a3845002e8f92e09f49c1fb4a47f9349192ac5bc1aa1919c964c5a4d146604d39ca4983800c89940e7d0ea95b2880d0d88003de344b2067000040540d43b88e0039c416c030000004c22fd101654884e80b81626a50c001041e6000001733224480e91c0989543700d4006986416920a2e0a9a06444001390001341a08a9ce0004f4a68ff33c85c0003d0708a000005000a08b103c16a3987492d2dc9092d27422c16908843000330fa84530e224bd8da0da3e8000060000000012c000000000c0000788001df142294000001ca7a0e496a00080447203164340001d80ea9ac27a851dc0007d91a4149600e1ba4122c53396b38e9141ca3a39691c000db18e5307915d4a84840000f4346a8f18001968dc000000c44085c800000860ef0002a00014004e2186f5282300d2001328543522c0b4000000354001f73ac618a30014f04893f0f127c5706f83b07c0003a11b1b2308170660a24fc4ea5b0b01593d23b0289b0e00003f21640013613e3d4000003d654443800000000e41f130083cb010738a608c81ee0fa1e4e08ad06220c9708f26869400018000370000fd0820000014a0008f84c0000000004a9a419a0ac8e8711942dd28a5f4dc3903b1303a4894df0000ee0010622912479cf60f031c70d3f8e11f017cab8262a8810af27921273d0a11029e000001bc23c90c000292101e1070634ea5d1160e2284008648271522cc459201a6419259e9058798cf9d43463ad2e00043843889a460e0785408c40f80b48f80424a790551b24ac
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x40094a0a2461e004c0061d00b118000003006e01838722508048ccb955a8843e22a470716e9a057a7802f7658c801a4171b6ca079f0401fa056000b262000034e01a9a26a8e000804442001c00d81026c0010400180020c49300482b424baa8a1ac019002425a125d54509600c801406d3d24c26a231a4200d0118d91a15748c921006018c6cc6a2ba4649080280ea2e4d841d9514c001806c2525a18eca8a6000807ea1941da325453000403b53420ed192a2980030149121974551624c00150250b0caa284312600092169091589711893000601b09494c83b2a29800381184d81101d9514c00100ed4d083b4c4a8a60009036909758862545300050894eb1302312a29800201da921076585514c001406d20ec412c2a8a6000e0461330440765452000624308c90e039aa288002921a41d5821c53044001098d4d2843aa29822000c44e8d9421d514c11000622146ca10ea8a60880031119464c875453044001888ca68643aa29822000a50a8b4321d514c1100042a3522190ea8a60880031119410c875453044001488d210f192a29822000c44a50878c9514c1100052234843864a8a6088002511a425d51cc53044001288d212ea8a62982200084c69097616214c1100051814cb930239260880030889761162189304400148853b2ac20e29822000c4425d84550714c110005603483ab0438a6088002940a7551821c53044001488d210fb8aa298220008c46a69421d514c1100062214eca10ea8a6088003111949d08754530440014a1514e843aa298220008546a47421d514c110006223283a10ea8a6088002911a421f765453044001488d210ebb2a29822000c44250875d9514c1100062810e492eca8a6088002911a421e7254530440018894a10f392a298220008c4690985c9514c11000522348438e4a8a6088002940a85c8725453044001188d212ec2c42982200085429d94616214c11000522349a890e90a6088002911a41d4874853044001098d2130b9aa29022000948690975452148110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1a400000c7008054000000020000801000004805b429d626046254530005102b2e8d9421d514c11000610194a8b4321d514c110004113b9690878c9514c110004111baa50878c9514c11000610194a8a7421d514c110004111ba250875d9514c110005101b421c925d9514c110004111baa50879c9514c110004901b42a1721c9514c110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x3
  | 8 => 0x4
  | 9 => 0x138d
  | 10 => 0x138e
  | 11 => 0x98d
  | 12 => 0x98e
  | 13 => 0x150d
  | 14 => 0x150e
  | 15 => 0x9cd
  | 16 => 0x9ce
  | 17 => 0x168d
  | 18 => 0x168e
  | 19 => 0x209
  | 20 => 0x20d
  | 21 => 0x20e
  | 22 => 0xb09
  | 23 => 0xb0d
  | 24 => 0xb0e
  | 25 => 0x1409
  | 26 => 0x140d
  | 27 => 0x140e
  | 28 => 0x1549
  | 29 => 0x154d
  | 30 => 0x154e
  | 31 => 0x249
  | 32 => 0x24d
  | 33 => 0x24e
  | 34 => 0xb49
  | 35 => 0xb4d
  | 36 => 0xb4e
  | 37 => 0x1449
  | 38 => 0x144d
  | 39 => 0x144e
  | 40 => 0x16c9
  | 41 => 0x16cd
  | 42 => 0x16ce
  | 43 => 0xbc9
  | 44 => 0xbcd
  | 45 => 0x3c9
  | 46 => 0x3cd
  | 47 => 0x3ce
  | 48 => 0xcc9
  | 49 => 0xccd
  | 50 => 0xcce
  | 51 => 0x15c9
  | 52 => 0x15cd
  | 53 => 0x15ce
  | 54 => 0x1709
  | 55 => 0x170d
  | 56 => 0x170e
  | 57 => 0x98955
  | 58 => 0x98956
  | 59 => 0x94995
  | 60 => 0x9ca
  | 61 => 0x9c955
  | 62 => 0x9c956
  | 63 => 0x949d5
  | 64 => 0x949d6
  | 65 => 0xb0955
  | 66 => 0x94b15
  | 67 => 0x94b16
  | 68 => 0xb0956
  | 69 => 0x140955
  | 70 => 0x95415
  | 71 => 0x95416
  | 72 => 0xbc955
  | 73 => 0x94bd5
  | 74 => 0xbcb
  | 75 => 0xbcc
  | 76 => 0xb1395
  | 77 => 0x138b15
  | 78 => 0x138b16
  | 79 => 0xbd395
  | 80 => 0x138bd5
  | 81 => 0x4e
  | 82 => 0x3ca
  | 83 => 0x15ca
  | 84 => 0xb0996
  | 85 => 0xb0995
  | 86 => 0x98b15
  | 87 => 0x98b16
  | 88 => 0x154996
  | 89 => 0x154995
  | 90 => 0x99555
  | 91 => 0x99556
  | 92 => 0x19c9
  | 93 => 0xbc995
  | 94 => 0x98bd5
  | 95 => 0x9cb
  | 96 => 0x1649
  | 97 => 0x134b
  | 98 => 0x449
  | 99 => 0xb1516
  | 100 => 0xb1515
  | 101 => 0x150b15
  | 102 => 0x150b16
  | 103 => 0x24b
  | 104 => 0x144b
  | 105 => 0xbd515
  | 106 => 0x150bd5
  | 107 => 0x1689d5
  | 108 => 0x1689d6
  | 109 => 0x209d5
  | 110 => 0x9c215
  | 111 => 0x209d6
  | 112 => 0x9c216
  | 113 => 0xb09d6
  | 114 => 0xb09d5
  | 115 => 0x9cb15
  | 116 => 0x9cb16
  | 117 => 0x1409d5
  | 118 => 0x9d415
  | 119 => 0x1409d6
  | 120 => 0x9d416
  | 121 => 0x1549d6
  | 122 => 0x1549d5
  | 123 => 0x9d555
  | 124 => 0x9d556
  | 125 => 0xbc9d5
  | 126 => 0x9cbd5
  | 127 => 0x17c9
  | 128 => 0x5c9
  | 129 => 0x249d5
  | 130 => 0x9c255
  | 131 => 0x249d6
  | 132 => 0x9c256
  | 133 => 0xb49d6
  | 134 => 0xb49d5
  | 135 => 0x9cb55
  | 136 => 0x9cb56
  | 137 => 0x1449d5
  | 138 => 0x9d455
  | 139 => 0x1449d6
  | 140 => 0x9d456
  | 141 => 0x16c9d6
  | 142 => 0x16c9d5
  | 143 => 0x9d6d5
  | 144 => 0x9d6d6
  | 145 => 0x3c9d6
  | 146 => 0x3c9d5
  | 147 => 0x9c3d5
  | 148 => 0x9c3d6
  | 149 => 0xcc9d6
  | 150 => 0xcc9d5
  | 151 => 0x9ccd5
  | 152 => 0x9ccd6
  | 153 => 0x15c9d6
  | 154 => 0x15c9d5
  | 155 => 0x9d5d5
  | 156 => 0x9d5d6
  | 157 => 0x1709d6
  | 158 => 0x1709d5
  | 159 => 0x9d715
  | 160 => 0x9d716
  | 161 => 0x134c
  | 162 => 0x168a
  | 163 => 0x168b
  | 164 => 0x21695
  | 165 => 0x168215
  | 166 => 0x168216
  | 167 => 0xb1696
  | 168 => 0xb1695
  | 169 => 0x168b15
  | 170 => 0x168b16
  | 171 => 0x141695
  | 172 => 0x169415
  | 173 => 0x169416
  | 174 => 0x155696
  | 175 => 0x155695
  | 176 => 0x169555
  | 177 => 0x169556
  | 178 => 0xbd695
  | 179 => 0x168bd5
  | 180 => 0xb5696
  | 181 => 0xb5695
  | 182 => 0x168b55
  | 183 => 0x168b56
  | 184 => 0x145695
  | 185 => 0x169455
  | 186 => 0x169456
  | 187 => 0xcd696
  | 188 => 0xcd695
  | 189 => 0x168cd5
  | 190 => 0x168cd6
  | 191 => 0x15d696
  | 192 => 0x15d695
  | 193 => 0x1695d5
  | 194 => 0x1695d6
  | 195 => 0xbcb15
  | 196 => 0xb0bd5
  | 197 => 0xccb16
  | 198 => 0xccb15
  | 199 => 0xb0cd5
  | 200 => 0x15cb16
  | 201 => 0x15cb15
  | 202 => 0xb15d5
  | 203 => 0xbd555
  | 204 => 0x154bd5
  | 205 => 0xcd556
  | 206 => 0xcd555
  | 207 => 0x154cd5
  | 208 => 0x15c255
  | 209 => 0xbcb55
  | 210 => 0xb4bd5
  | 211 => 0xccb56
  | 212 => 0xccb55
  | 213 => 0xb4cd5
  | 214 => 0x170b56
  | 215 => 0x170b55
  | 216 => 0xb5715
  | 217 => 0x3d455
  | 218 => 0x15d455
  | 219 => 0xbd6d5
  | 220 => 0x16cbd5
  | 221 => 0xcd6d6
  | 222 => 0xcd6d5
  | 223 => 0x16ccd5
  | 224 => 0x124e
  | 225 => 0x19cb
  | 226 => 0x3cbd5
  | 227 => 0xbc3d5
  | 228 => 0xccbd5
  | 229 => 0xbccd5
  | 230 => 0x15cbd5
  | 231 => 0xbd5d5
  | 232 => 0x19cc
  | 233 => 0x170bd5
  | 234 => 0xbd715
  | 235 => 0xd0c
  | 236 => 0xd4c
  | 237 => 0xb09895d
  | 238 => 0xb09499d
  | 239 => 0x9894b1d
  | 240 => 0xb09895e
  | 241 => 0x9894b1e
  | 242 => 0xbc9895d
  | 243 => 0xbc9499d
  | 244 => 0x9894bdd
  | 245 => 0xb09c95d
  | 246 => 0x9c94b1d
  | 247 => 0xb09c95e
  | 248 => 0x9c94b1e
  | 249 => 0x1409c95d
  | 250 => 0x9c9541d
  | 251 => 0x1409c95e
  | 252 => 0x9c9541e
  | 253 => 0xbc9c95d
  | 254 => 0xbc949dd
  | 255 => 0x9c94bdd
  | 256 => 0x19cd
  | 257 => 0x160c
  | 258 => 0x104c
  | 259 => 0x1a8c
  | 260 => 0xe8b
  | 261 => 0x178b
  | 262 => 0x104b
  | 263 => 0x1a8b
  | 264 => 0x1a8a
  | 265 => 0x104a
  | 266 => 0x138b96
  | 267 => 0x14b
  | 268 => 0x151556
  | 269 => 0x1689cbdd
  | 270 => 0x9d696
  | 271 => 0x1049
  | 272 => 0x1a89
  | 273 => 0x19c9d5
  | 274 => 0x1049d2
  | 275 => 0x14c
  | 276 => 0x9d256
  | 277 => 0xcc3d1
  | 278 => 0x105692
  | 279 => 0x19d695
  | 280 => 0x1696d6
  | 281 => 0x1043d2
  | 282 => 0x1055d2
  | 283 => 0x140956
  | 284 => 0x141556
  | 285 => 0x255d5
  | 286 => 0x25a55
  | 287 => 0x255d6
  | 288 => 0x258d6
  | 289 => 0x1456d6
  | 290 => 0x139256
  | 291 => 0x184e
  | 292 => 0xd0bd4
  | 293 => 0x21556
  | 294 => 0x155416
  | 295 => 0x140b16
  | 296 => 0x256d6
  | 297 => 0x16d456
  | 298 => 0x144b56
  | 299 => 0x19cd14
  | 300 => 0x15d715
  | 301 => 0x15d716
  | 302 => 0x104d14
  | 303 => 0x104e93
  | 304 => 0xd1054
  | 305 => 0x3d052
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 1915
  | 6 => 5481
  | 5 => 4199
  | 4 => 646
  | 3 => 64
  | 2 => 10
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
  | 7 => packedAt gbK7 (78511+((h/638+packedAt gbK7 (70855+(h % 638)*12) 12) % 2299)*12) 12
  | 6 => packedAt gbK6 (288666+((h/1827+packedAt gbK6 (263088+(h % 1827)*14) 14) % 10590)*14) 14
  | 5 => packedAt gbK5 (265928+((h/1399+packedAt gbK5 (247741+(h % 1399)*13) 13) % 5542)*14) 14
  | 4 => packedAt gbK4 (47370+((h/215+packedAt gbK4 (45220+(h % 215)*10) 10) % 776)*11) 11
  | 3 => packedAt gbK3 (5331+((h/21+packedAt gbK3 (5184+(h % 21)*7) 7) % 84)*7) 7
  | 2 => packedAt gbK2 (935+((h/3+packedAt gbK2 (920+(h % 3)*5) 5) % 24)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc3f0fff8f061f0fe0fe3f0383fc520cf0d370f
  | 1 => 0xfc3f0e07007e1f0ff07c7fffc1cac33412c9f3
  | 2 => 0x3ff007ff801ff0007f803ffe331c38e30e3c
  | 3 => 0xffc00007ffffe000007fffc0003c1fc0fc0fc0
  | 4 => 0x7ffffffffff800000003fe000fff000
  | 5 => 0xfffffff80000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x40401210102020120120908804800041041305
  | 1 => 0x84110420000201048004241201004114004052
  | 2 => 0x2aa04364801aa022490125b8130c28630c28
  | 3 => 0x6a800095b975400045724b808cac16c0bc0f80
  | 4 => 0x22088106ce599cc96e000201103fa000dba000
  | 5 => 0xb33cc9e00c11088188000c06213ffbbe000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36340
namespace PEqualNP.Outside.L_meta_36340
open PEqualNP.Outside.L_meta_36340.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 26 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_128 : Interval s0Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 134 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 9 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 7 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 16 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 13 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 15 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 68 := (concat bs4_3_0 (concat bs4_3_32 bs4_3_64))
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
theorem bs4_4_864 : Interval s4Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 894 := (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat (concat bs4_4_96 bs4_4_128) (concat bs4_4_160 bs4_4_192))) (concat (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)) (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 bs4_4_416)))) (concat (concat (concat bs4_4_448 (concat bs4_4_480 bs4_4_512)) (concat (concat bs4_4_544 bs4_4_576) (concat bs4_4_608 bs4_4_640))) (concat (concat bs4_4_672 (concat bs4_4_704 bs4_4_736)) (concat (concat bs4_4_768 bs4_4_800) (concat bs4_4_832 bs4_4_864)))))
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
theorem bs4_5_800 : Interval s4Atlas 5 800 20 := block_range (n:=20) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 820 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat bs4_5_96 (concat bs4_5_128 bs4_5_160))) (concat (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)) (concat (concat bs4_5_288 bs4_5_320) (concat bs4_5_352 bs4_5_384)))) (concat (concat (concat bs4_5_416 (concat bs4_5_448 bs4_5_480)) (concat bs4_5_512 (concat bs4_5_544 bs4_5_576))) (concat (concat bs4_5_608 (concat bs4_5_640 bs4_5_672)) (concat (concat bs4_5_704 bs4_5_736) (concat bs4_5_768 bs4_5_800)))))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 2 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 30 := bs5_3_0
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
theorem bs5_4_704 : Interval s5Atlas 4 704 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 712 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 (concat bs5_4_192 bs5_4_224)) (concat bs5_4_256 (concat bs5_4_288 bs5_4_320)))) (concat (concat (concat bs5_4_352 (concat bs5_4_384 bs5_4_416)) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512))) (concat (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)) (concat bs5_4_640 (concat bs5_4_672 bs5_4_704)))))
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
theorem bs5_5_704 : Interval s5Atlas 5 704 31 := block_range (n:=31) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 735 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 (concat bs5_5_384 bs5_5_416)) (concat bs5_5_448 (concat bs5_5_480 bs5_5_512))) (concat (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)) (concat bs5_5_640 (concat bs5_5_672 bs5_5_704)))))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 10 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 64 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 646 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 bgb_4_192) (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)))) (concat (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 (concat bgb_4_416 bgb_4_448))) (concat (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)) (concat bgb_4_576 (concat bgb_4_608 bgb_4_640)))))
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
theorem bgb_5_4192 : Interval gbAtlas 5 4192 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4199 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))))) (concat (concat (concat (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280))) (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))) (concat (concat (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664)) (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792))) (concat (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080))))))) (concat (concat (concat (concat (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 bgb_5_2208)) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 bgb_5_2336))) (concat (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 bgb_5_2464)) (concat (concat bgb_5_2496 bgb_5_2528) (concat bgb_5_2560 bgb_5_2592)))) (concat (concat (concat (concat bgb_5_2624 bgb_5_2656) (concat bgb_5_2688 bgb_5_2720)) (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 bgb_5_2848))) (concat (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 (concat bgb_5_3104 bgb_5_3136)))))) (concat (concat (concat (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 bgb_5_3392))) (concat (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 bgb_5_3520)) (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 bgb_5_3648)))) (concat (concat (concat (concat bgb_5_3680 bgb_5_3712) (concat bgb_5_3744 bgb_5_3776)) (concat (concat bgb_5_3808 bgb_5_3840) (concat bgb_5_3872 bgb_5_3904))) (concat (concat (concat bgb_5_3936 bgb_5_3968) (concat bgb_5_4000 bgb_5_4032)) (concat (concat bgb_5_4064 bgb_5_4096) (concat bgb_5_4128 (concat bgb_5_4160 bgb_5_4192))))))))
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
theorem bgb_6_5472 : Interval gbAtlas 6 5472 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5481 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)))) (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152))) (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)))))) (concat (concat (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)))) (concat (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824))) (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016))))) (concat (concat (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))) (concat (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)))) (concat (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528))) (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))))))) (concat (concat (concat (concat (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)))) (concat (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200))) (concat (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392))))) (concat (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552))) (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)))) (concat (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904))) (concat (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000)) (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)))))) (concat (concat (concat (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256))) (concat (concat bgb_6_4288 bgb_6_4320) (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)))) (concat (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576))) (concat (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672)) (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768))))) (concat (concat (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928))) (concat (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024)) (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120)))) (concat (concat (concat bgb_6_5152 bgb_6_5184) (concat bgb_6_5216 (concat bgb_6_5248 bgb_6_5280))) (concat (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376)) (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472))))))))
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
theorem bgb_7_1888 : Interval gbAtlas 7 1888 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1915 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448)))) (concat (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672))) (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800)) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928))))) (concat (concat (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152))) (concat (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)) (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))) (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8feeefeeafeeeece8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4277071080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36340.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,4]⟩,⟨.or,[5,6]⟩,⟨.and,[1,3]⟩,⟨.and,[2,3]⟩,⟨.or,[2,4]⟩,⟨.or,[0,9]⟩,⟨.or,[0,1]⟩,⟨.and,[7,11]⟩,⟨.or,[8,13]⟩,⟨.and,[10,12]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277071080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277071080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36340

open PEqualNP.Outside.L_meta_36340 in
theorem PEqualNP.Outside.L_meta_36340 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277071080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277071080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
