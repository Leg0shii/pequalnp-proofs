import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37055.Model
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


end PEqualNP.Outside.L_meta_37055.Model

namespace PEqualNP.Outside.L_meta_37055
open PEqualNP.Outside.L_meta_37055.Model
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

def SBf (j : Nat) : Nat := [6, 7, 5, 5, 7, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 50,swapRows 84]

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

end PEqualNP.Outside.L_meta_37055

namespace PEqualNP.Outside.L_meta_37055
open PEqualNP.Outside.L_meta_37055.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xa00300c19000d0401ce14008f1082c9004a0000df43be43bc43dc439c43be42bc42de32dc32be41bc41de31dc31bf40bd40df30dd30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40000050000000531c02c20000000000000000cf00000600030824d000291394412002080000821c794e438f290871e5110e3aa021c794e429b28c851e548caaca31947150328f29c832e529063ca918d394a318e2a0631c5350258a4a04d145408e2a6611c544c298a4985514530
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x30420859865210e0e6294443831895010e146154043
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
  | 2 => 4
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
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (297+((h/5+packedAt s0K4 (272+(h % 5)*5) 5) % 23)*6) 6
  | 3 => packedAt s0K3 (609+((h/7+packedAt s0K3 (567+(h % 7)*6) 6) % 46)*6) 6
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffff03ffffffffffffff87ffff
  | 2 => 0xfc0fffc0fff80ffffc1ff03ff03ff81ff9ce73
  | 3 => 0xfff03fff03fff01fffe0ffc0ffc0ffe07e739c
  | 4 => 0x3ffffc00001fffff0000ffff00007f83e0
  | 5 => 0xffffc0000000001fffffffff000000007ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x844108482092040400a5245124510a8a0294a5
  | 2 => 0x2922948649215a8b2c0a522a522ad055394a52
  | 3 => 0x30a4a5121a4542b355409a889a88e5415c6318
  | 4 => 0xa2cb3a2490766cdd9a730c30ef3c41866f83e0
  | 5 => 0xc30c3c38e3878f1ee39cef3c0c30861877fc00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37055
namespace PEqualNP.Outside.L_meta_37055
open PEqualNP.Outside.L_meta_37055.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1450a802b4e000005200800388d0221a14318486d289087cb91244c00b0000d00003c01e2c00000005418000040260084e80002002c0e005000000c8c1c082440100680000e103800204100ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21ee21fd21fc21ec21f421e421ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x40f80e001cc4a181909c7a331301cd8030117400110f988a219111f8525b0e990de05001b8d4611b1ec34711e1dc72683e96814132300046001b9d4e04e0011450172494cae66001d8f2002580074000419cb80026010a0060f0bc000000100a4121883048001f000846d0000076590008440000786c88651a9e8860d17000822a058d0386b000b060001f800a814001a4be013c0b4bc15390589e001c120ac00159341258239fcc6553a181004a03808100098084080283818501000504810004828204819101850000000486050001190302870280060b0a5b94b43b6a96877651d0eeaa3a1db94a43b6a9487765190eeaa321e750c43af29e855d53d0aeca3a15d54742bba8a85745150a7ca9994f55332bb28e657551ccaeea2995d14532af29e835d53d06dca5a0db54b41b7a92836c525067ca998cf55331b7296636d52cc6dea498db14931bb28c436e51886cca310f948421b728843e651087ce8210f990421f2a0843e441087ce6210f98c421f298843e431086eca410f994821f3a1043e642087ca8410f910821f399043e632087ca6410f90c821f3aa043e654087caa810f915021f3a9843e653087caa610f914c21f3a1843e643087ca8610f910c21f3a8043e650087caa010f914021f210e81e421902bea6a05714d40b7a92816c52502eea2a05d14540f210a815e53102baa6205b94840b6a90817651102eaa2207908440f210e61e4218c27ea8984f15130b7a92616c524c2eea2985d14530f210a613e540c27aa8185b94830b6a906176510c2eaa2187908430f210e417651882eaa31079086209faa2413c54482bea6905714d20bba8a417451483c842907908420f210e216e52842daa50879086109faa2213c54442bea6885714d10b7a92216c52443c842887908410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1200189b00000080161c800f801900119d000a82800d001d88159e000000000008800000000015000000000011020001800c05a08b830000000793948b002180070500040d8f0109000616800000001800001f899c038c9b80001280109a8e9f00100e211e931a170a142004868000001980000017808004043000e180010038081040800100004009918552d0e646254743991855290e646254643b198f41086c563d0421a999331086a564cc421b198f42086c563d0821a999332086a564cc821b198f54086c563d5021b198e54086c56395021c955054086a664d4c21a959353086a66494c21a959253087455314c2199997430866565d0c219999643086656590c21e150c43086a76454021a919150086c76354021b118d50086a66414021a959050086c66314021b158c500866661d49409998b515026665085409919421503475308540d114c2150264615484099189511026765084409959421103465308440d154c211026661d49309998b514c266650853099194214c3275408530c9150214c264615483099189510c267650843099594210c3265408430c9550210c3275408520c915021483475308520d114c21482646114910c9d5021443245408510d1d4c21443445308510
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (825+((h/15+packedAt s1K5 (720+(h % 15)*7) 7) % 72)*7) 7
  | 4 => packedAt s1K4 (3827+((h/43+packedAt s1K4 (3483+(h % 43)*8) 8) % 155)*9) 9
  | 3 => packedAt s1K3 (2738+((h/22+packedAt s1K3 (2584+(h % 22)*7) 7) % 118)*8) 8
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffffffffffc0fffffffffffffff0fffff
  | 2 => 0x1fc0fc0fe07e07fff0f07c1f03e0f81ff53267
  | 3 => 0x1fff000fff8007ffff007fe003ff001ff9c387
  | 4 => 0xe000000ffffff83fffff800003ffffe0fe03f8
  | 5 => 0xfffffff00000003ffffffffffc000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc04208002104000001108c21186108c10054ab
  | 2 => 0x4a9631964728aa9cb074351a29a8d15a753265
  | 3 => 0x930c5aaa8a1d352d57085b4852da429cb9c386
  | 4 => 0x1a28a34d1451a1b66aad0210831ce708de0350
  | 5 => 0x1c30c38e1861c63b8cce639ce0108410efa800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000faaaaaaaaaaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37055
namespace PEqualNP.Outside.L_meta_37055
open PEqualNP.Outside.L_meta_37055.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x9d43
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | 3 => packedAt s2K3 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s2K3 (17+((h/1+packedAt s2K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 1 => 0x87c1ffc3e0fffff8707f8783fc3c1fffd64c9f
  | 3 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x800880400040008090088880444422009131
  | 1 => 0x2112910909522128342485112428894c524486
  | 3 => 0x12a52290d2a406538859502aca8152a2a58b18
  | 4 => 0x5539c42a9836ab9d5d0c4443733380c4f80ec0
  | 5 => 0x663187331cc733e66e6e667062220308ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37055
namespace PEqualNP.Outside.L_meta_37055
open PEqualNP.Outside.L_meta_37055.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x9d43
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | 3 => packedAt s3K3 (i*16) 16
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s3K3 (17+((h/1+packedAt s3K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 1 => 0x87c1ffc3e0fffff8707f8783fc3c1fffd64c9f
  | 2 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x800880400040008090088880444422009131
  | 1 => 0x2112910909522128342485112428894c524486
  | 2 => 0x12a52290d2a406538859502aca8152a2a58b18
  | 4 => 0x5539c42a9836ab9d5d0c4443733380c4f80ec0
  | 5 => 0x663187331cc733e66e6e667062220308ff6000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37055
namespace PEqualNP.Outside.L_meta_37055
open PEqualNP.Outside.L_meta_37055.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x920018000285c0003e3000b003c01b4eac01d0434000484140a389400000200112aa4d16001150500981980e811a20084c893c000131c3c0100044040004000003ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x463a20860a48325c6c58ae78366e00309c84169e000000622c000060920098006aa00000001a8e00043c3800026888004200004e00182a0000000000b200000000a2b4228000004cb63e66260c0000008294008a90401e000e28445296082400b006a400aca65a5000007c2e004a000000107e761ca800648c14701254349a000000000000567a0000740072aa00005e020200040302040003000200000001020300000f01000901000002040102b7290876d5210ebca6215754c429f2a0653d540cb9a64195794f41aea9e836e52d06daa5a0e794f41cea9e83ae52d075aa5a0cf943419eaa483b75150678a0a0cf950419f2a4633d548c6dea498db149319f2a0633d540c6dca418db54831bd2806379500c67ca910cf55221afa9a435c534867ca810cf55021af298435d53086f4a010de540219ea8c813e50902bca6205754c40b7290816d52102eca2205d54440cf298819d531035ca4206b54840db288813d511036aa2204d544409f28081ba501027ca9984f55330b7296616d52cc2dca5185b54a309faa2613c544c27ca9904f55320af29e415d53c82bca7105754e209faa2413c544827ca9884f55310daa0e213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xc6e2a840010c3551320cb0d5354b41c354d52103165354440c554d51103265254440c954951102346550510
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2724+((h/30+packedAt s4K4 (2484+(h % 30)*8) 8) % 147)*8) 8
  | 3 => packedAt s4K3 (312+((h/2+packedAt s4K3 (304+(h % 2)*4) 4) % 12)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc3ffff81fe1f0f0ff0fe1fffe1fc1c1e99f793
  | 1 => 0xfc1f0ffe3ffffff07f0fe1c0fe1fffff6648ff
  | 2 => 0xffe00fffc01ff1ff800ffe00ffe01fe1878f1c
  | 3 => 0xfffffe001fffff00000ffffe001f80fe0
  | 5 => 0xfffff000000001ffffffffff00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4846008c04221001901202466024444c089391
  | 1 => 0x81001110100800202104208802090910224026
  | 2 => 0x188aaa248d548356888b5412b54092c5858d18
  | 3 => 0x32d4cc492906a59b5aa11024d992c089d80ec0
  | 5 => 0x23188871b198c9ec6ccd993811030311f76000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaecc8ecc8eeeaeeeaecc8ecc8eeeaeeeaecc8ecc8eeeaeeeaecc8ecc8eeeaeeeaecc8ecc8eeeaeeeaecc8ecc8eeeaeeeaecc8ecc8eeeaeeeaecc8ecc8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37055
namespace PEqualNP.Outside.L_meta_37055
open PEqualNP.Outside.L_meta_37055.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x248060a30a000302380071658000268489b34001064e00ba91e10a2a4c54e803c711900a215804a25200007cc8d4404001608968005f040042ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2c130423271807288680a611190b17060f1599a69d918c000180001a9e8aaa8492000220000005a0939a23850001161487a1a9802a102122800815002d9c9e0f8b800d80280e80002b8a250009a4039f1880000e1ba7a9000d12968c88ab1f94179b24828003092d10a225802c9d1c000202348800e1018018000090e0010d2e5c78000000000200001b7290876d5210ebca6215754c429f2a0653d540cb9a64195794f41aea9e836e52d06daa5a0e794f41cea9e83ae52d075aa5a0cf943419eaa483b75150678a0a0cf950419f2a4633d548c6dea498db149319f2a0633d540c6dca418db54831bd2806379500c67ca910cf55221afa9a435c534867ca810cf55021af298435d53086f4a010de540219ea8c813e50902bca6205754c40b7290816d52102eca2205d54440cf298819d531035ca4206b54840db288813d511036aa2204d544409f28081ba501027ca9984f55330b7296616d52cc2dca5185b54a309faa2613c544c27ca9904f55320af29e415d53c82bca7105754e209faa2413c544827ca9884f55310daa0e213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x6084e000ca0204c3551320cb0d5354b41c354d52103165354440c554d51103265254440c954951102346550510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2694+((h/30+packedAt s5K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s5K3 (312+((h/2+packedAt s5K3 (304+(h % 2)*4) 4) % 12)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc3ffff81fe1f0f0ff0fe1fffe1fc1c1e99f793
  | 1 => 0xfc1f0ffe3ffffff07f0fe1c0fe1fffff6648ff
  | 2 => 0xffe00fffc01ff1ff800ffe00ffe01fe1878f1c
  | 3 => 0xfffffe001fffff00000ffffe001f80fe0
  | 4 => 0xfffff000000001ffffffffff00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4846008c04221001901202466024444c089391
  | 1 => 0x81001110100800202104208802090910224026
  | 2 => 0x188aaa248d548356888b5412b54092c5858d18
  | 3 => 0x32d4cc492906a59b5aa11024d992c089d80ec0
  | 4 => 0x23188871b198c9ec6ccd993811030311f76000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8eeeaecc8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37055
namespace PEqualNP.Outside.L_meta_37055
open PEqualNP.Outside.L_meta_37055.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x193618a000041b2158c40385200c261800e2b00552b2168c4008c4423a1a9208a12d4b1e5509bc70009d8e7a4981f34ba213680000000fd10000010004ee5400003de330074b807c0202c000008000000051209a8220080808a28a00017f95001fd54017f15007ff52007f94801fd5201ff14805ff42007f90801fd42017f10801fe32007f4c801fc32017fd0401bf4100ff90401fd41006f50403fc41007fc8403fe21007f48403fc21017fd0001fe40007f50005fc40007fc8001fe20007f48001fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24004ff88120027dc4090037ff1048009fe0824004ffd9420025feca10013fe65080077f3284004ff59420005faca10013fc65080097e3284004ffd9020025fec810013fe64080057f3204004ff59020005fac810013fc64080097e320400cffd502005ffca810003fd5408017fe2a04004ffd8c20025fec610013fe63080017f3184004ff58c20005fac610013fc63080097e318400cffd4c20007fca610003fd5308019fe298400bffd0c20007fc8610003fd4308017fe2184000bf98820067fea410027fe5208001fea904009ff1482005ffe8410027fe4208001fea104009ff10820007fe6410027fe3208001fe9904009ff0c820027fec210013fe61080037f3084004ff58420005fac210013fc61080097e308400cffd4420006fea21002bfe5108001fea884000df54420057f8a21002fff4108001dfa08400aff90420007fa8210003bd4108015fe2084000ffcc420057fc6210003fd3108015fe1884009ffc8420057fc4210003fd2108013fe1084004bf98020027fea010013fe5008009fea804004ff14020027fe8010013fe4008009fea004004ff10020027fe6010013fe3008009fe9804004ff0c020027fe4010013ef2008009ff1004004fe88020027fa4010013ed2008001fc9004004ffc4020027f82010013ff64840097fb242004ff99210015fcc908013fd64840017eb242004ff19210025f8c90801ffe5484001feaa42007ff15210027fec508012ff6284009ff3142000bf98a10027fac508002fd6284009fe3142004bf18a10047fea508003fe5284001fea942008ff14a1003ffe8508003fe4284001fea142007ff10a10007fc6508003fd3284001fe1942001bf5861000ffe8308007bf4184003ff20c2001ff5061000f7a8308007fc4184003ff90c2001ff8861000ffa4308007fc21840097f3042004ffd0210027fc8108013fd4084009fe2042004ffc8210027fc4108013fa2084009fe9042000fe48210027f84108013ff1084009fb8842001fec4210027f82108013f81084001ffb222000bfd911002ffcc88800afe6444001feb222000bf5911002ff8c88800afc644400bff2a22000ff5511002ff8a888003ff62440017fb122000ff98910005fcc488003fd62440017eb122000ff18910005f8c48801bff5244001ff2922000ff54910037f8a488017ff4244001ff2122000ff5091002ff88488003fe3244001fe9922000ff0c910025fec288007ff4144003dfa0a2001ff9051000fec8288007fd4144003dea0a2000fd505100076a8288007fc4144003ff90a2001ff8851000ffa4288007fc21440037fb022005ffd0110027fc8088003fd4044009fe2022000ffc8110027fc4088003fa2044001fe9022000fe48110027f84088007ff1044003fd8822004ff84110027ec2088013fc1044009fa0822001fe04110
  | 1 => 0x3bd41c8027fe20e4000ffcc72009ffc6390003fd31c8027fe18e4009ffc8720007de439004ffe21c8001fe90e4000fb4872004ff84390057ff50c8009ff2864000ff54320027f8a190053ff40c8009ff2064000ff50320027f88190003ff30c8027ff8864004ff04320027fecb10012ff6588009ff32c4003bf99620027facb10002fd6588009fe32c4004bf19620027fec910012ff6488009ff3244002bf99220027fac910002fd6488009fe3244004bf19220097fea910047fe5488001feaa44011ff15220027fec710012ff6388009ff31c4000bf98e20027bcc710002de6388009feb1c4000bf58e20027bac710002dd6388009fe31c4012ffd4e20007fca710003fd5388025fe29c4011ffd0e20007fc8710003fd4388023fe21c4000bf58a20097fea510003fe5288001fea944012ff14a2008ffe8510003fe4288001fea144011ff10a20007fe6510003fe3288001fe9944000ff0ca20027fec310013fe61880037f30c4004ff58620005fac310013fc61880097e30c4012ffd4620006fea310043fe5188001fea8c4000df54620087f8a310047ff4188001dfa0c4010ff90620007fa8310003bd4188021fe20c4000ffcc620087fc6310003fd3188021fe18c4000ffc8620087fc4310003fd2188021fe10c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009ff9044004fbc8220007f64110013ff1088009fe0844000ffd9520005feca900037f65480013fb2a400fff9952001dfcca90003fd65480017eb2a400fff1952001df8ca900037c65480073e32a4000ffd9120005fec890003bf64480015fb22400eff99120015fcc890003fd64480017eb22400eff19120015f8c890003bc64480055e322400fffd5120077fca890003fd544801dfe2a24000ffd8d20005fec690003fe63480017f31a4000ff58d20005fac690003fc63480017e31a400fffd4d20007fca690003fd534801ffe29a400effd0d20007fc8690003fd434801dfe21a400fffd4920007fca490003ee5248001fea924000fb5492007ff8a49003bff4248001ff2124000fb90920007fa8490003ed424801dfe2124000ffcc920007de6490003fe3248001fe9924000ff0c920007d86490003ff61480017fb0a400dff9852000dfcc290003fd614801bfe30a4001bf1852007ffea2900037f514801bff28a4000ff54520006faa290037fc514801dffa0a4000efd052006ffc8290003fd4148001dea0a400dff10520007fe6290037fe3148001fe98a400dff0c520007fe4290003ef214801bff10a4000ff48520007da4290037fc214801fffa824004ff94120007faa090013fc504801dffa024004ff90120007fa8090013fc4048001ff9824004ff8c120007fa6090003ff2048001fd9
  | 2 => 0x40017788720013ff6290009ff3148000bf98a40027fac520002fd6290009fe3148019ffd4a40007fca520003fd5290033fe2948002ffd0a40017fc8520003be4290005fea148002ff10a40017788520003ff3290001ff1948000ff4ca40007f86520013ff6190009ff30c8001bf98640027fac320002fd6190009fe30c8004bf186400cffea3200037f5190031ff28c8000ff54640006faa320063fc5190005ffa0c8002efd0640017fc832000bfd4190001dea0c8002ff10640007fe6320063fe3190001fe98c8018ff0c640007fe4320063fe2190001fe90c8018ff08640025fcc120013ff5090009ff2848004ff14240027fe8120013bf4090005fda048004ff10240027f08120013ff1090009fe0848000ffd9540005fecaa00037f65500013fb2a8017ff9954001dfccaa0003fd65500017eb2a8017ff1954001df8caa00037c65500073e32a8004bfd9140017fea8a000bfe5450005df2a28002ff551400077aa8a000bfc5450001ffb1a8000bfd8d40007fcc6a0003fd6350001fe31a8000bf18d400bffea6a0003fe5350001fea9a8017ff14d40017fe86a000bfe4350005fea1a8002ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0002fc625002fffa928000ff94940007faa4a005ffc5250005ffa128002ff90940017fa84a000bfc4250001ff9928000ff8c940007fa64a0003fc3250001ffb0a8000bfd85400b7fcc2a0006fe6150001feb0a8016ff1854000df8c2a005fff5150001bfa8a8016ff94540007faa2a00037d515002dfe28a8002ffd05400177e82a000bfe4150005fea0a8000ef50540017f882a0003ff315002dff18a8000ff4c5400b7f862a0003ff215002dff10a8000ff485400b7f842a000aff605002fffa828004ff94140007faa0a0013fc5050005ffa028002fed0140027fc80a0013be4050009fe2028004ef10140017f080a005bff1050009fe0828009ffd9720005fecb90057fe65c80077f32e4000ff59720005facb90027fc65c80077e32e4009ffd9320005fec990053fe64c80057f3264000ff59320005fac990027fc64c80057e3264015ffd53200a7fca990003fd54c8029fe2a64009ffd8f20007fcc790002fe63c8001feb1e4000bf58f2004ff8c790002fc63c802bffa9e4000ff94f20007faa790057fc53c8029ffa1e4000ff90f20007fa8790053fc43c802bffa964009ff94b20007dca590003fd52c8001f6a964009ff14b200a7fe8590027fe42c8001f72164000ff50b20007da8590027fc42c8001ff9964000fbccb2004ffc6590003fd32c8013fe1964000fb0cb2004ffec39004ffe61c80037f30e4000ff58720005fac390027fc61c80037e30e4015ffd4720006fea39004ffe51c8001fea8e4000df5472009ff8a390053ff41c8001dfa0e4013ff90720007fa839000
  | 3 => 0xfa8a8201ef9454100f7aa2a08073d5150403de28a8201ef8c54100f7862a0807be2150403de10a8200efd81410077cc0a0803bd6050401de302821eefd41410f778a0a0807bf1050403db8828201ef0414104ffecb90802ff65c843bff32e4203bf99721007facb90802fd65c8413fe32e4203bf1972104ffec990802ff64c8439ff3264202bf99321007fac990802fd64c8413fe3264202bf193210effea990873fe54c8401feaa6421cff1532104ffec790803fe63c84017f31e4200ff58f21005fac790827fc63c84017e31e421dffd4f21007fca790803fd53c843bfe29e421cffd0f21007fc8790803fd43c8439fe21e4201bf98b210effea590827fe52c8401fea964209ff14b210e7fe8590827fe42c8401fea164209ff10b21007fe6590827fe32c8401f71964200ff4cb21007da6590827fc32c84037eb0e4201ffd472100efea390807fe51c8403fea8e4201df5472100ff8a390807ff41c8403dfa0e4201ff9072100ffa8390807bd41c8403fe20e4201ffcc72100ffc6390807fc31c8403ff10e4201fb8872100fec4390807fc21c8403f610e4209ffd8321007fcc190812fe60c8401feb064200bf5832104ff8c190877ff50c843bfe286421cffd03210e7f88190807ff10c8403fe0864200ffd9521005feca9086ffe65484077f32a4200ff59521005faca9086ffc65484077e32a4200ffd9121005fec89086bfe64484057f3224200ff59121005fac89086bfc64484057e322421bffd51210d7fca890803fd5448435fe2a24200ffd8d21005fec690803df63484016fb1a4200ff98d21005fcc690803fd63484017eb1a4200ff18d21005f8c690803dc63484016e31a421bffd4d21007fca690803fd5348437fe29a421affd0d21007fc8690803fd4348435fe21a4201bfd89210dffea490803fe5248401fea92421bff149210d7fe8490803fe4248401fea12421aff10921007fe6490803fe3248401f71924200ff4c921007da6490803fc32484037fb0a4201ffd452100efea290807fe5148403fea8a4201df5452100ff8a290807ff4148403dfa0a4201ff9052100ffa8290807bd4148403fe20a4201ffcc52100ffc6290807fd3148403fe18a4201ffc8521007ee4290807fe2148403f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024204bf181210dffea09086ffc5048435ffa02421aff1012100ffe2090807fc1048409ffb2c8004bfd9640027fccb2000efe6590009feb2c8000bf59640027f8cb20012fc65900057eb248002ffd52400cf7ea92000bfe5490005feaa48002ff1524001778a920013ff6390009ff31c8000bf98e40027fac720002fd6390009fe31c8019ffd4e40007fca720003fd5390033fe29c8002ffd0e40017fc8720003be4390005fea1c8002ff10e
  | 4 => 0x8ffe414c847fe20a6423ff8853211ff84299003ff604c8017fb026400ff98132007fac099003fc604c8097e3026424ffd0132127f8809908fff104c847fe0826409ffd9032005fec819087fe640c8057f3206400ff59032005fac819027fc640c8057e3206421ff95032007faa819087fc540c8017f3106422ffd483204ffca419003fd520c813fe2906421ffd083204ffc8419003fd420c813fe2106409ff8c832007dc6419003fd320c801f69906400f34c83204ffec219083fe610c8037f3086400ff58432005fac219027fc610c8037e3086421ffd0432107fc8219083fc410c841ff1086420fb8843204ff84219083ec210c813ffb006400ff98032025fcc019003fd600c8017eb006409ff1803210ffe8019087fc400c841ff8806420ff040320177ecba080bbe65d0405deb2e8202ef197410177ec7a080bbe63d0405deb1e8202ef18f410ff7ea7a0803be53d0401dea9e821fef14f410177ec5a080bbe62d0405deb168202ef18b410ff7ea5a0803be52d0401dea96821fef14b410077e65a0803be32d0401de9968200ef0cb4100d7ac3a0807bf51d04039fa8e8201ef9474100f78a3a0807be31d0403de18e8201ef8874100f7843a080bbf60d0405df3068202ef5834101778c1a087fbf50d043fde2868201efc434100f7821a0803ff65504017fb2a821eff9954101dfccaa0803fd65504017eb2a821eff1954101df8caa0806ff6450405ffaa2821eefd5141017fca8a080bbe5450405feaa28200ef55141017f8a8a080bbc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8200bf18d410f7fea6a0803fe5350401fea9a821eff14d41017fe86a080bbf4350405ff21a8200ef90d41017fa86a0803bd4350405fe21a8202ef10d41007fec4a0802ff6250401ff3128200ff58941007f8c4a0802fc625043dffa928200ff94941007faa4a087bfc5250405ffa128202efd0941017fc84a0803be4250405fea128200ef50941017f884a080bbc4250401ff9928200ff8c941007fa64a0803fc32504037fb0a8201ffd454100efea2a0807fe5150403fea8a8201ff1454100ffe82a080bf74150403ff20a8201ef9054100ff882a0807bc4150403fa20a8201ff8c54100ff862a0807fe2150403fe10a8200ffd8141005fec0a0803fe6050401feb028200ff18141025f8c0a087bff505043dfe2828202ffd01410177e80a080bfc4050405de2028201ffc414100fee20a0807fc1050401dfb2a821eef995410077acaa087bbc6550401dfb1a8200ef98d410077ac6a0803bc635043ddfa9a8200ef94d410077aa6a087bbc5350401dfb128200ef989410077ac4a0803bc625043ddfa928200ef949410077aa4a087bbc5250401df9928200ef8c9410077a64a0803bc3250403dfb0a8201afd85410176ec2a0807bf51504039
  | 5 => 0x8e42005fcc721003fd63908017eb1c8409ff18e42167fea721003fe5390859fe29c8402ffd0e42017fc872100bfd4390805fe21c8402bf98a42167fea521027fe5290801fea948409ff14a42017fe852100bbf4290805f7a148409ff10a42017d88521027ff6190857ff30c8401bf98642007fac321002fd6190813fe30c8401bf18642167fea3210affe5190857fe28c8402ffd06420177e832100bfe4190805fe20c842bff8c64215ff863210affe2190813fe10c8409ffd8242007fcc121012fe6090801feb048400bf5824204ff8c1210b3ff5090859fe2848402ffd0242017f8812100bbc4090857ff884842bff04242007fecaa1002ff6550855ff32a8403bf99542007facaa1002fd6550855fe32a8403bf19542015fec8a100bff5450805ff2a28402ff55142017f8a8a1003ff63508017fb1a8400ff98d42007fac6a1003fc63508017e31a842affd4d42007fca6a1003fd5350855fe29a8402ffd0d42017fc86a100bfd4350805fe21a8402bfd8942157fea4a1003fe5250801fea92842aff14942017fe84a100bef4250805ff2128400ef90942017f884a100bbc4250805f62128400ffd8542005fec2a10a7fe61508037f30a8400ff5854214ff8c2a1006fc6150855ffa8a8429ff9454214ff8a2a100bff4150805dfa0a8402ff90542017f882a10a7fe3150853fe18a8429ff8854214ff842a1003ff60508017fb028400ff98142007fac0a1003fc60508097e302842affd4142157f8a0a100bff4050805fe2028429ffc414214ff820a1027ff658c8017fb2c6428ff9963201dfccb19003fd658c8017eb2c6409ff1963201df8cb19027ff648c8017fb246427ff99232015fcc919003fd648c8017eb246409ff19232015f8c9190a3ff548c84fff2a46400ff5523213ff8a919002fd638c851ffa9c6400ff94e32007faa7190a3fc538c84fffa1c6400ff90e32007fa871909ffc438c8017f3146428ffd4a3204ffca519003fd528c813fe2946427ffd0a3204ffc8519003fd428c813fe2146400ffcca32007de6519027ff618c84dff30c6401bf98632007fac319002fd618c813fe30c6401bf18632147fea31909bfe518c84dfe28c6427ffd0632137fc831909bfc418c84dff18c6426f78c632137f8631909bdc318c84dff10c6409ff0863204ffec119003fe608c8097f3046400ff58232005fac119027fc608c851ffa846428ff1423213ffe811909ffc408c84dff8846426ff04232007fec899002ff644c849ff3226402bf99132007fac899002fd644c849fe3226402bf19132127fca899003fd544c849fe2a26425ffd4932007fca499003fd524c84bfe2926424ffd0932007fc8499003fd424c849fe2126400ff8c932007bc6499003ff614c8017fb0a6423ff9853200dfcc299003fd614c847fe30a6401bf18532127fe8299
  | 6 => 0x480080300080000000300600200000000300880200600f00180380480000280000700380000780000180000180500f80280200380300180000380080c00000380100081680200000180000100000000680080080380300000400000000580380b80180680500100281380100180000380180180080100100600000200100380400180500080100100100200100000280200300480200300000080000380180180000aff6455005ff2a2a802df95154017f8a8aa00bbc54550059e2a2a800ffd8954005fec4aa003fe6255001feb12a800ff18954005f8c4aa00fff5255007fe292a803df14954017fe84aa00bfc4255005de212a800ffd8554005fec2aa0c7fe61550037f30aa800ff5855418ff8c2aa006fc6155005ffa0aa802efd0554017fc82aa00bfc4155063ff10aa831ff08554007fec0aa002ff6055001ff302a800ff58154007f8c0aa012fc6055005ffa02a802efd0154017f880aa0c7ff1055063fe082a803bf5965204ffec9290c3fe64948057f324a400ff59252005fac929027fc64948057e324a403ffd525201efea92900ffe5494807feaa4a400df5525201ff8a929027ff6394801ff31ca400bf98e52007fac729002fd6394813fe31ca403ffd4e5201ff8a7290c3ff4394801ff21ca430ff10e5201dfcc52900fff5294807bfa94a403fbd4a5204ff8a52900fec5294861ffa14a409ff10a5204ffec3290bffe61948037f30ca400ff58652005fac329027fc61948037e30ca403ffd465201efea32900ffe5194807fe28ca430ffd065217ffc83290bffc419485fff18ca42fff0c65217ffc4329027fc2194813ffb04a400ff98252025fcc129003fd60948017eb04a409ff1825201ffea12900ffc5094807be284a430ffd0252187f881290bfff109485ffe084a403bfd9552007fec8a9002ff645485dff322a402bf99152007fac8a90bbfc64548057e322a403ffd515201ffca8a900ffd5454807fe2a2a400ffd8d52005fec6a9003fe6354801feb1aa400ff18d52005f8c6a900fff5354807fe29aa42effd0d52007fc86a9003fd435485dfe21aa403bfd895201ffea4a900fef5254807ff292a400df9495201ff8a4a900f7c5254807f6292a42effd0952177f884a9003ff61548017fb0aa42dff9855200dfcc2a9003fd615485bfe30aa401bf1855201ffea2a900f7f5154807ff28aa403ff14552177fe82a90b7fe415485bfe20aa42dff8c55216ff862a90b7fe215485bfe10aa400ffd8152005fec0a9003fe6054801feb02a400ff18152025f8c0a900fff5054807fe282a42effd0152177f880a90b7ff105485bfe082a409ffd9642005fecb210b3fe65908077f32c8400ff59642005facb21027fc65908077e32c8402bf59242017fea92100bfe5490805df2a48402ff552420077aa92100bfc5490813ffb1c8400ff9
  | 7 => 0xde0b160d0000000000000000219036bf4000010ddd80014b5cd5ba5261090002d78f18000000000000bf0a60003882be00017800021a00010700041d23820924f0000dd54b0004c55de9550003d545f8721648000010004060928000000000855bb1be4cb129000337cd91392f239d1df5bf17180002da9a50b43448200004f8000004e28052920004be4a40608500005110004361a12a98cd0005d196d3705674b51f93fe0001270003fa2e029e13a27abe71e61565d628341e8000638001eb0000001f302b8000000c3800000290000248000372450dc580023d8000000000001b50000000001281d42a73ee1660d22434743b280000046c00000280100000000000180800281480000100380000400100000180080280100100200000300100100100080080000300000500180000080080000100100080200000080080600800100a00800000400081180080080480500000c80a80900000700000280180180380780001200200000000200080080180080200080000100580a00000201b80180301380480000100080200280200d80100080080080180000c80200000200180000480000281380180000000000000000181800380480080080280000700200000680180000100280081600000400180080b00400a80000400100300080000000181b81f00001500000a80500680080700500080100000000980000000b80000181b80080000a00580880200200880000000280380780180900680380200400400200000000000300080300280100000a80280600000700080200680000100680580000080080180000580381180180100000380280400280000700380300c80400000680b80000180200a00000f00480200280300300200180000000080000180000980780000280480080100000100000000700080480100000500300180200000200281380600000100080580100200e80081b80680100000280400000180280500100000502480080780200000380380401780080080000000080000000280000000100100000000000700080300080300000480080001100280300200200300100500000400400280000100480300100080480780000680a80000480980000580000380180000580600080080080500000300180180100000080180100080000200380480280080000000181101b00000000000080080900000180880180080c00900200200180200f00200d00180600200280000100000080280200280480000500180000000080080000a00080c00800300000700700000080180200380000200980280300180280100000300200480000080a00480080200080080380200000900000300080000c80000000000a81580580000000002280000000580080000a00080280100a80380300400f00080000100280380080180000080
  | 8 => 0x5373c822a4618000000001dc00027a00027d5c84d00004810ae23532a1cb2dc8000085da8000005cfc688cf4500005e03ce00042c1bb00042b34258137d8c448b3f811ac200a512601e440a0b37c408000000464c261aa00a9bc16e4421b6aba028cee5e904f5e11f00000b68e8b0a31707707f0db4e849c064a77d975bd18539232229ac135c31ff3762ad4cf03aa460242c45175e2a230559c52e420328488acae45c52b339012b2b05cc53baf3d434b5b912342f18d1774b846f11bb6848e17955f49f9c93494c207431d0e343fc2500003c80000006e038016c414a0de3b3a0004da0004fd53f4488002884a34d102509f3a01c712404900024214e0000005d100019c1e50000000000000000000b784151d0fcd3b00030100057686995180054e00300042f8cb5354e94fe18f0000d10000003e6000000000432b102061652eadd90001b400009dc3800000c0001a50440000000000814b656c0005695a01d1346ad603a0000a43c35724c917a34e5ceaed5e1ceb5340574c74f026d5cca6a061a2ad4814f2982153f50803112ff1d9347a3a3b700013300049600051916a04e8023f751515f50d0468001960d5508469d4a21e2b85a800032f29c0654940c91f61603aa16f26150f2c75495cb4991930ac00001d9342520000005dca99d6800039b00055735a21807d5b12eba8523e27b58f47e05d1bd0001b80004bb52e00011e5d22655c71b9052cd81ee1081db5aa22b1e3af957f13f38a5462d58f381b9181f816b00000005e0005013c92d2009ba24dc3b580000000044b36a44482e1e48004c32664338000000948000002ea0e756f03c0005c113da4a007b62d0959e3cf520000000140092170c2a0b50003eb31b18408f49700000000035e29b80059f5980004219ab1cc9fb00000017c00004814658a0b85d0b380000000000003b407e0000000001a600006bbf90002c91582e1000023278ad33b04735871d819e443874abd066ac300b44297300003f5c4c834a60000000000001af18800045ece50000000002e200040d0aa48942937ab9a12accc08a0000a0360000031af32910568000fea4919544000011f0000000000000005d451200000000038737a0000002cc8002c20c6c41cf109fcf72310e008b5da5292ae437b812335a53213412f81353844b902c0138278674ff1b12f60000360141ec42e53630e4f936915c579000045a583444640000001b320700019121e8004a110b95d48a00000002a9d043f0000001362b60002510001c20000f200000053d00022b8001610439e207180000000000000043a01ebfb0000004ac00026fa1f3303073360fb47138c1ef06f24b0004904ca3630222d700fce24a258d19a4ad23757c2545be0321a706fa3433385c44d5100000000000004d60000000470f51502fe91b2f7
  | 9 => 0xe9412dc030242cf6b745d80004015763274753940bc0000000003e30002bc00000000001a3863b53330004792701cd27457132831445bc6cca82a91dd45a000452a2e000044cf314d01014203581c0900f007845dbde40e00000010f2fd0ab3954145ca0fa007017daf4101ac4aa0c300005f0005450004b44670000003dd80058b4bd319111365061343cb00004e70003af80006a8000005c61dfa640be5924470170b404b3fc80035d5b500052a2f52a61828000000000005cf00028d40232daf756351e30d0001adb4d5c5046214211183d4d3a722819d0003480a240723c0eb3dd2b50000000000001fc47702685484d0de26837900007390880009428a1fd3ca0000000000005e980023f3f00000000c20954c6453022a0800046280058631227c0620c61e40002e30002b300027f0060d90153370000a88990001e0b8780050c2e500039900057414b80000055c22c3d95dc3b80545a304c45e19836f20c06b46926906622235939f58e4310fe1c1997388b8e1e83be18255e55505502d06ece352f4d337146fc20ddbd3e3a10a325b44fd6d5271700434c018608820d2d500000017b3e540b3ba2790001b7030c518830000001ffd7729d53100007646dd7b2f11c00005430df59a039b2445f0001020003250b01512aa08d3c22e64ef00001580000031a0002601ba16c5c23510000160004358000000818003290343ec3062a14a494352443ec4459648c42dd882cf1e008c2dabc73ff01d00005fd320768000004210000000001ce2db2b95ab2d00004544f44563003150002bf0000005d990d3640000001443ae0005b61cc0005e855343880008e0dc0710000420003d030c05100db75018b519ed49f05bd8300456a3965e41b8c4530427510e54709e40c48fc3dbdf0d802b283c24db018319f00cc435dfc3032fb1e2993550b933c5ce4980002e81891104ad9193fd82700000014a0000000000000120002870003934db36c41a0000c700054f0000180002244dd0f15d000000038f000417a2daf05615540fb8840ed1a22c000000000059400051f00000026c01b00000056b80028959d0000001fa52105195b1e7109a7613d0002c84b591c09ca2543928b5c38002df1f43ab2b700005200036201303106d41246e3d1b820003ed5070005891640a9bcb0791d75d50238564191eeddd13e0003a51f232e57e06929709a10a5903b64a70e81c3dc91da01c8ff4de15e3453d2c040005a25950000b60005cc4fa40017f3131a919b53300000035200045d0003f32fc4a00003b90a75221715053773a30354a90e93e4000000049caf53a4b30005410000003ac1738004550d44bf14718a048acc4ba00000000d23b4c80004f23bb1d0b5725d2fe0001c100009158c2cd36e0600000000000ad55619050e2d4ad104e00000012550024109b0
  | 10 => 0xba437f165b5c33f4f546d430883c605e230b02035b3f10001ac80027100000000002a0000004624e11060000bb00051629b4ed000075b9113c23259100000021680026220f2844182962ab38b5664ce08200000000000e8000000002ee9d24845581203cc8004c43f237300000000000000052514900001149b5752d94ab5b480000044c2a812d4398002efd2c00054c0000583b38001d350a4e4373b800000004c10da0005a903d33280035f0000930004280001454f0d1300047a2100ef1d55284224cd46319412e0bd5ae43b409038b5800909c4ec47f2c510c3cd5de3972fb4923fc48529316725629eda43b35b73e03a81b64035e6b475e61f52200001de1141b25e322602fc482405d30258a149324c8000965b300029f8b715c999221c523610004678004bc05d8000001e124e00bd1836b476032c274168a93830000590c13020000e08001cdd603db2050005bc1f706350200000000046a00000000000018700037828c0828000002dd0000f34fb0c032346a9cf2b144a1ad0684350005b241f0f404a9c4014a8e0000c500012a00052d00000000051438900003700011600000032c2810f8000000478000000000000534c700000003d84571ae019a7801f4609a280025a1743cb80021c3e80000002ee000309191c3e41c40a3265653663432a523d0005a1029cd50002e72b40193ffb7d0ce3402da59c3545a74461678003340000450e63bd00000000045ca4500000000051b07a0215030000000e100028f00000034f3bf000067c2380000029543180021495a54405e837afa5cd8af11321322f27e10c8ea00010300043d2b25521a03cda7235017d41b578047a1d3f600043c1570b10003ea0000330000000005992633d63313dc8002302730000abaac573375b2c9258003ad1483c610418000041655a0005df0000860001a330f0003a60000005b43dc0d7255334aa3050c5928212f00056e5b582ebef07c5624513c00ec55b4664d25b8068c914ea1684805c43671722dbd3fde8c8d09d0ee07346b2005840539a838d1523fd5ea9c613012b4b159310b5402ef55d46bcf642400002c8fd2a022953c4f800891d0b21ca0d7c47a67053072ba955906295ad853e11533985e720133b1000004368000708000700000001c08002f402609733d37e54245800000000005a00000035600040500002849badf8e245b1c822108749a47d26b39e1cea5e3c41010980c836d00000000000000000f2cb00000028644f4e600018b4610000004333b141f800422a5943200006c0000005ac49d00a1210000000004df4e780032d03e2d441e00000000000025c00001a8000e78000000000000000000003d32419e335326f33e5385230f906424446800051a551286d822ce31c029122342b852eb089c8724730849c91a0d30001ea5db00000046
  | 11 => 0x1bf4e020c80005b37bdd70001810cc04b98c0001f1411000057dc01d1ab03cc1d65700000004e3aca59b0002020000001924b721225725f43725000000003bb7b2c628011249500e5a646384ca2d1152e947c34c5063e914c3d10000005e50004fc00030bbb2000000000409c1732023e9b00002ec34a18e44e24d3c10001372a43c500042d0000e424bc2300043c8393da00003d8d6526c0a8002c120439c0ba0000ca0000000000002530000a821fa272360001a429f13858017e8400b32de46511e96247b0fc53926d82f0000002945043050002d8000000152cd40000000000002160003350000000001fe08931f1173d717e11fc8f2175300baa0e00024c16957a1c348621b1312390002bb00000049e0003e206a5505ea0003900000000000000002af03b0bbdad5278f643495440f533c88000000107ca500057d4b247226e4d71591053ca8002a213230317f8750e556b1755e48f741512c3d20e1b180001e91633463bc27700033213b44907b024a0a00004a51c176564065
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x74350510007b64350510007b5435051002fb4435051002fb74250510007b64250510007b5425051002fb44250510007f37050510025f67050510025f47050510007f0705051000ef7605051000ff3605051002fb74050510197b64050510197b4405051002fb77650510016b77650510007b47650510016b47650510007b7755051019fb67550510007b5755051019fb47550510007b7655051019fb66550510007b5655051019fb46550510007b77350510007b67350510007b57350510007b47350510007b76350510007b66350510007b56350510007b4635051019fb75350510007b65350510007b5535051019fb45350510007b77250510007b67250510007b57250510007b47250510007b76250510007b66250510007b56250510007b4625051019fb75250510007b65250510007b5525051019fb45250510007b73250510007b63250510007b53250510007b43250510007b77050510007b37050510197b67050510007b57050510197b47050510007b0705051000fb7605051000eb7605051000fb3605051019fb75050510197b65050510197b45050510197b63050510197b43050510197b62050510197b42050510014ff765011000cfe76501100b4fd765011000cfc76501100057f75501100357c7550110006bf6450110016bc6450110005f7715011000df47150110007755150110007b5415011000cfe76c811000cfc76c8110006ef62c811004eec62c811000df671c8110005f571c81100077551c8110007b541c8110055fa7688110026fa7688110025fb7388110027da7388110005f97388110027d97388110005d9738811006df9728811004efa628811004ef8628811000dfa7188110025f87188110026fb6188110027f361881100877b5188110087f25188110087795188110007f15188110007715188110087bb4188110087f24188110087b94188110007f14188110007b1418811004cff764811000cfe764811006cfd764811000cfc76481100057f75481100357c7548110005bf744811002dbc7448110006ef6248110006ec6248110005f7714811000df47148110007755148110007b54148110027e8204811000df8764811006ef8764811000cf876481100077b7548110007787548110007bb7448110007b87448110005fb7348110005f97348110025fb7248110027eb7248110007eb624811004efa624811004ef86248110007e86248110007ea5248110007e95248110007ea4248110007e94248110007eb3248110007e83248110007f3714811000dfa714811000df8714811006ff07148110026fb6148110027f3614811006f7b514811006ff2514811006f795148110007f1514811000771514811006fbb414811006ff2414811006fb94148110007f14148110007b1414811006feb214811006fe92148110
  | 1 => 0x5110004fc7655110016be6455110006bd645511002f3c545511000df6715511001cfe75d8910004fd75d891001cfc75d8910014fe74d8910004fd74d8910014fc74d89101a4fe73d8910004fd73d8910006ef52d8910006ec52d8910006ef42d8910006ec42d8910024ff71d8910024fd71d89100867f51d89100867d51d8910086bf41d8910086bd41d8910086ef21d8910086ed21d8910006ef629891006df9709891001cfe7598910004fd759891004cfc7598910014fe7498910004fd749891004cfc74989101a4fe7398910004fd739891004cfe729891009cfd719891004ef5719891009e7f519891009e7d519891009ebf419891009ebd419891006cfd709891004ef970989100057f75589100357c7558910005bf745891002dbc7458910005df7358910005dc735891009dfb7058910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df73589101a4fc7358910006dc7358910004dc7358910006ef725891006cff7158910006f7715891006e7f515891006e7d515891006ebf415891006ebd415891009cff7058910006fb7058910084fe7618910006ed621891001cfe7518910004fd751891004cfc7518910014fe7418910004fd741891004cfc74189101a4fe7318910004fd731891004eee7218910006ef521891004eec5218910006ef421891004eec4218910024ff711891000cfe7118910024fd711891000cfc71189100567f51189100567d5118910056bf4118910056bd411891004eef2118910056ed2118910024fe701891004ef97018910024fc701891004cff7694910004fe7694910004fd769491004cfc76949100067f659491001e7c6594910025fa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc765491004cff7690910004fe7690910004fd769091004cfc7690910006bf6490910016bc6490910025fa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc765091004cff768c910004fe768c910004fd768c91004cfc768c910006df638c910006dc638c910025fa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c91004cff760c910004fe760c910004fd760c91004cfc760c910006ef620c91004eec620c910007cd320c91000df6710c910005f5710c910025fa700c910005f9700c910025f47650510016f47650510024f47650510005f77550510005f5755051000df7745051000fb77450510007b76450510016f66450510016f4645051002fb4645051019fb7545051002fb65450510007b5545051002fb4545051002fb
  | 2 => 0x4bf7458a10014fe7458a10014fc7458a10006bc7458a10014bc7458a10004ff7358a101a4fc7358a10026ef7258a1006e7f5158a1006e7d5158a1006ebf4158a1006ebd4158a1006eef2158a1006eed2158a10024ff7058a10024fe7058a10024fd7058a10024fc7058a10026ee2058a10026ec2058a1004cff7694a10024fe7694a10004fd7694a10024fc7694a101be7f6594a1001e7c6594a1004eee6294a10006ed6294a10025fa7094a10005f97094a10004ff7654a10024fe7654a10004fd7654a10024fc7654a10006ee6254a10006ed6254a1004cff7690a10024fe7690a10004fd7690a10024fc7690a101b6bf6490a10016bc6490a1004eee6290a10006ed6290a10025fa7090a10005f97090a10004ff7650a10024fe7650a10004fd7650a10024fc7650a10006ee6250a10006ed6250a1004cff768ca10024fe768ca10004fd768ca10024fc768ca10006de638ca10006dd638ca10025fa708ca10005f9708ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca10005f7714ca1000df4714ca10025fa704ca1004cff760ca10024fe760ca10004fd760ca10024fc760ca1004eee620ca10006ed620ca10007cd320ca10025fa700ca10005f9700ca10025fb7648210006fb76482100077b7548210007787548210007bb7448210007b87448210005fb7348210005f97348210027eb7248210027eb624821004efa6248210026f86248210027e86248210007ea5248210007e95248210007ea4248210007e94248210007eb3248210007e8324821000dfa714821000df8714821006f7b514821006f79514821006fbb414821006fb9414821006feb214821006fe92148210014fe76d911002ebe64d911001cfe75d9110004fd75d911001cfc75d9110006bf54d911002ebc54d91101a4fe73d9110004fd73d911002ebc43d911004cfe72d9110004fd72d911002ebc42d9110024ff71d911000cfe71d9110024fd71d911000cfc71d91100c67f51d91100c67d51d91100c6bf41d91100c6bd41d9110024fe70d911000cfd70d9110024fc70d911002ebf40d91100057f75591100357c755911002ebc6459110005df7359110005dc7359110005ef7259110005ec72591101adfb7059110004ff75591100067f75591100047f755911001cfe755911001cfc75591100067c755911001c7c75591100c4ff7459110006bf745911002ebe5459110004ff7359110006df7359110004df73591101a4fc7359110006dc7359110004dc7359110004ff7259110006ef7259110004ef725911004cfc7259110006ec7259110004ec72591100b4ff7159110006f771591100b67f51591100b67d51591100b6bf41591100b6bd41591101acff7059110006fb7059110196be4059110196bc4059110004ff7655110004fe7655110004fd765
  | 3 => 0xe60544201cf6f20544201cf7a20544201cf6d20544201cf771054420016bf76d04201c6be76d042005ebd76d0420016bc76d04201c6bf65d04200febe65d0420006bd65d04201c6bc65d04201c6bf63d0420006be63d0420006bd63d04201c6bc63d042009ebe62d0420195bd71d04201c6bf61d042000ebe61d0420056bd61d042000ebc61d04200573f51d04200573d51d04201c6be60d04201c7af20d04201c7ba20d04201c7ad20d0420004ff7650420004fd7650420024fc7650420196bf6450420016be6450420006bd6450420016bc6450420005ef725042004dec725042000ef66150420006f56150420006bf7650420196be7650420006bd7650420196bc7650420196bf65504200f6be6550420006bd6550420196bc6550420196bf6350420006be6350420006bd6350420196bc6350420007af7250420007ac725042009ebe62504201c5bf715042005fb77150420196bf615042000ebe6150420197b6615042000eb66150420056bd6150420197b56150420006b5615042000ebc61504200573f51504200573d5150420196be6050420197af2050420197ba2050420197ad2050420197b710504201a4ff76cc420024fe76cc420004fd76cc4201a6de63cc420006dd63cc420004ff764c420004fd764c420024fc764c420006de634c420006dd634c420005ef724c42004dec724c42000ef6614c420006f5614c42009cff7648420005df7348420005dc734842009eee6248420025fb7648020006fb7648020004fb76480200077b7548020007787548020007bb7448020007b87448020025fb7248020027eb724802004efa6248020027ea6248020006f961480200077b5148020007795148020007bb4148020007b9414802004feb2148020007e92148020004ff75592100067f75592100047f755921001cfe755921001cfc75592100067c755921001c7c7559210026bf745921003ebe5459210004ff73592101a4fc7359210004ff725921004cfc72592100b67f51592100b67d51592100b6bf41592100b6bd4159210024ff7059210024fe7059210024fd7059210024fc7059210026be4059210026bc4059210026f71059210026f51059210004ff7655210024fe7655210004fd7655210024fc7655210016be6455210006bd645521003f3c545521001cfe7598a10004fd7598a1004cfc7598a10014fe7498a10004fd7498a1004cfc7498a101a4fe7398a10004fd7398a10026ee7298a1009e7f5198a1009e7d5198a1009ebf4198a1009ebd4198a1004eef2198a1009eed2198a10024fe7098a10026fa7098a10024fa7098a10024fc7098a10026ee2098a10026fa2098a10026ec2098a10004ff7558a100067f7558a100047f7558a1001cfe7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7458a10006bf7458a10
  | 4 => 0x8c20026de7398c2004ede3298c2004edc3298c2000cfe7198c20004fd7198c2000cfc7198c20024fe7098c20026de3098c20026dc3098c20026ef2098c20026ed2098c20004ff7558c2001cfe7558c2001cfc7558c20004ff7458c20014fe7458c20014fc7458c20024ff7358c20026df7358c201a4ff7258c2011cfd7258c2004cfc7258c2004ede3258c2004edc3258c20004ff7158c2000cfe7158c2000cfc7158c20024fe7058c20024fc7058c20026de3058c20026dc3058c201a4ff7694c20024fe7694c20004fd7694c201a6de6394c20006dd6394c200675f5394c2004dee7294c20005ed7294c20004ff7654c20024fe7654c20004fd7654c20024fc7654c2001e7e6554c200067d6554c20006de6354c20006dd6354c201a4ff7690c20024fe7690c20004fd7690c20024fc7690c201a6de6390c20006dd6390c2004dee7290c20005ed7290c20004ff7650c20024fe7650c20004fd7650c20024fc7650c20016be6450c20006bd6450c20006de6350c20006dd6350c2004cff759882001cfe75988200acfd759882004cfc759882004cff7498820014fe74988200a4fd749882004cfc749882004cff73988201a4fe7398820004fd739882004cfc739882004eee529882004eee429882004eec329882000cfe719882004eef2198820026ee2098820026fa2098820026ec20988200acff76548200aeee62548200a4ff76508200a6ee6250820004fd76cc820006ee62cc820004ff764c82004fcc324c820004ff755842001cfe755842001cfc7558420004ff7458420014fe7458420014fc7458420004ff73584201a4fc735842000cfd7258420026f77158420056f65158420056f64158420056f6315842004ef7215842004ef42158420024ff7058420024fd7058420024fc7058420026ef2058420026fa2058420026ed2058420026f61058420026f4105842001e7f76d44201d67e76d44200667d76d442001e7c76d44201d67f64d44201e67e64d44200067d64d44201d67c64d44201d67f63d44200067e63d44200067d63d442009e7e62d44201cd7d71d44201d67f61d442000e7e61d44200567d61d442000e7c61d44201d67e60d44201d76f20d44201d77a20d44201d76d20d4420004ff7654420004fd7654420024fc76544201ce7f655442001e7e65544200067d655442001e7c6554420005ef725442004dec725442000ef66154420006f561544200067f76544201ce7e76544200067d76544201ce7c76544201ce7f64544201de7e64544200067d64544201ce7c64544201ce7f63544200067e63544200067d63544200076f72544200076c725442009e7e62544201d57f71544200677771544201ce7f615442000e7e61544201cf76615442000e7661544200567d61544201cf75615442000675615442000e7c61544201ce7
  | 5 => 0xde7c6548520006bf64485200d6bc6448520005df7348520005dc7348520006f7614852000ef46148520005fb7048520025f87048520025ec764852000eec7648520024ec7648520005ef7548520005ed75485200076f65485200076c6548520005ef7448520005ed7448520007af6448520007ac6448520007cf7348520005ee7348520005ec7348520007cc7348520005cc7348520006ef6348520006ed634852006def7148520007e77148520007e7614852000eee614852000eec614852006fe4614852006f6f514852006f6d514852006faf414852006fad4148520007eb7048520025ee7048520025ec7048520007e8704852001cff765412007cfd765412001cfc76541200067f655412001e7c6554120005bf7454120075bc7454120006bf6454120206bc6454120005ef7254120005ec7254120014ff7650120074fd7650120014fc76501200057f755012007d7c75501200067f65501200be7c6550120006bf6450120016bc6450120005ef7250120005ec7250120004fe76cc1200067f65cc1201fe7c65cc120006bf64cc1201f6bc64cc120006df63cc1201a6dc63cc120005ee72cc120005ed72cc120007cc32cc120004fd764c120004fc764c120005bf744c120075bc744c120006bf644c1201eebc644c120005ef724c120005ec724c120007cc324c1200067f65c81200ae7c65c8120006bf64c81200a6bc64c8120025ee72c8120024fa76c81200077b65c81200077865c8120007bb64c8120007b864c8120025fa72c8120027eb62c812004fea52c8120007e952c812004fea42c8120007e942c8120007eb32c812004fe832c8120005f971c81200077b51c81200077951c8120007bb41c8120007b941c812004feb21c8120007e921c8120024ff75594200267f7559420004ff7459420014fe7459420014fc74594200667f5459420004ff73594201a4fc73594200667f535942001cff725942001cfd725942004cfc725942004e7e525942004e7c5259420004ff715942000cfe715942000cfc71594200667f5159420024fe7059420024fc70594200267e50594200267c5059420026ef2059420026ed2059420004ff755902001cfe755902001cfc7559020024ff7459020026bf745902005ebe5459020004ff73590201a4fc735902005ebf4359020014ff7259020014fd725902004cfc725902004ebe425902004ebc4259020004ff715902000cfe715902000cfc715902005ebf4159020024fe7059020024fc7059020026be4059020026bc4059020026ef2059020026ed2059020004ff7655020024fe7655020004fd7655020024fc765502001e7e65550200067d6555020016be6455020006bd645502005f3c545502001cfe7598c20004fd7598c201a4fc7598c20014fe7498c20004fd7498c201a4fc7498c20024fe739
  | 6 => 0xd655452001e7c6554520006bf64545201debc64545200076e52545200076d52545200067f76545200057e76545200067e76545200047e76545200067d76545200057c76545200067c76545200047c76545200067f64545200073f64545200063f64545201de7e64545200067d64545201de7c64545200073c64545201de3c64545200067f63545200067e63545200067c63545200076e72545200076d72545200076e42545200076d42545200076f32545200076c325452006d7f715452007f77715452006e7f615452000e7e615452000e7c61545201cf6e205452006f771054520016bf76d0520005be76d0520076be76d0520004be76d0520076bd76d0520075bc76d0520016bc76d0520014bc76d0520006bf65d05200073f65d05200063f65d05200febe65d0520006bd65d05200febc65d05200073c65d05200fe3c65d0520006bf63d0520006be63d0520006bd63d0520006bc63d0520077ae72d0520077ad72d0520007ae52d0520007ad52d0520007af32d0520007ac32d052006dbd71d052006ebf61d052000ebe61d052000ebc61d052006f3f51d052006f3d51d05201c7ae20d0520004ff7650520004fe7650520004fc76505200067f65505200f67c6550520006bf6450520016be6450520006bd6450520016bc6450520007ae4250520007ad4250520006bf7650520005be7650520006be7650520004be7650520006bd7650520005bc7650520006bc7650520004bc7650520006bf65505200073f65505200063f65505200f6be6550520006bd65505200f6bc65505200073c65505200f63c6550520006bf6350520006be6350520006bd6350520006bc6350520007ae7250520007ad7250520007ae5250520007ad5250520007af3250520007ac325052006dbf7150520077b7715052006ebf615052000ebe615052000ebc615052006f3f515052006f3d5150520197ae205052006fb71050520004fe76cc520004fd76cc5201a4fc76cc5200067f65cc5202267c65cc520006bf64cc52021ebc64cc5201a6de63cc520007cf32cc520006f761cc52000ef461cc520004ff764c520004fe764c520004fc764c5200067f654c5202167c654c520006bf644c52020ebc644c520006de634c520005ef724c520005ec724c520007cf324c520084fe76c85200067f65c85200ee7c65c8520006bf64c85200e6bc64c8520005ee76c8520086ee76c8520005ef75c8520005ed75c85200076f65c85200076c65c8520005ef74c8520005ed74c8520007af64c8520007ac64c8520005ee73c8520005ec73c8520006ef63c8520006ed63c852006ded71c852000eee61c852000eec61c852006f6f51c852006f6d51c852006faf41c852006fad41c852004feb70c8520025ee70c8520025ec70c852004fe870c8520024fc76485200067f6548520
  | 7 => 0x920025f87050920025ec7650920016ec7650920024ec7650920005ef7550920005ed75509200076f65509200076c6550920075ef7450920007af7450920007af6450920016ee6450920016ec6450920077ac6450920005ec7350920005ef7150920077af4150920007eb7050920025ee7050920025ec7050920007e87050920024fe76cc9200067f65cc9202467c65cc920006bf64cc92023ebc64cc920006df63cc9201a6dc63cc920025fa70cc920005f970cc920025ee76cc920006ee76cc920024ee76cc920005ef75cc920005ed75cc9200076f65cc9200076c65cc920005ef74cc920005ed74cc920007af64cc920007ac64cc920006ef63cc920007cf63cc920007cc63cc920005ed71cc920236ee61cc920236ec61cc920025ee70cc920007ea70cc920007e970cc920025ec70cc920004fe768c9200067f658c9201467c658c920006bf648c92013ebc648c920006de638c920006dd638c920005ee728c920024fc764c9200067f654c92012e7c654c920006bf644c920126bc644c920006df634c920006dc634c920005fb704c920025f8704c920004fe760c9200067f650c9201167c650c920006bf640c92010ebc640c9201a6de630c920007cd320c920005ee760c920006ee760c920005ef750c920005ed750c9200076f650c9200076c650c920005ef740c920005ed740c920007af640c920007ac640c920005ee730c920007ce730c920006ef630c920007ce630c920006ed630c920007cd630c920006cd630c920005ed710c920106ee610c920106ec610c92022fce310c92022fcc310c920025ee700c920025ec700c92000cfe76d85200067f65d85200067c65d8520006bf64d8520006bc64d852006ef661d85200067f75d852001cfe75d8520004fd75d852001cfc75d85200067c75d8520006bf74d8520014fe74d8520004fd74d8520014fc74d8520006bc74d85201a4fe73d8520004fd73d8520024fd72d852000cfc72d852006ef431d852006ef621d8520024fe70d8520024fc70d852006ef710d85200057f755852007d7c75585200067f65585200067c6558520005bf7458520075bc7458520006bf6458520006bc6458520005df7358520005dc735852006ef4615852001e7f76d45200057e76d452007e7e76d45200047e76d452007e7d76d452007d7c76d452001e7c76d452001c7c76d45200067f64d45200073f64d45200063f64d45201e67e64d45200067d64d45201e67c64d45200073c64d45201e63c64d45200067f63d45200067e63d45200067c63d452007f6e72d452007f6d72d45200076e42d45200076d42d45200076f32d45200076c32d452006d7d71d452006e7f61d452000e7e61d452000e7c61d45201d76e20d4520004ff7654520004fe7654520004fc76545200067f655452001e7e65545200067
  | 8 => 0x1a4fc7498d201a6ed7298d2000cfe7198d20004fd7198d2000cfc7198d201a6f97098d200057f7558d2007d7c7558d200067f6558d200067c6558d20005bf7458d20075bc7458d20006bf6458d20006bc6458d20005f77158d2006df47158d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20014fc7458d20006bc7458d20014bc7458d20006ef7258d20004ff7158d20006f77158d20004f77158d2000cfe7158d2000cfc7158d20006f47158d2000cf47158d20004ff7058d20006fb7058d20004fe7618d200067f6518d200067c6518d20006bf6418d20006bc6418d20006dd6318d2001cfe7518d20004fd7518d201a4fc7518d20014fe7418d20004fd7418d201a4fc7418d201a6de7318d2004cfc7218d2000cfe7118d20004fd7118d2000cfc7118d20006de3118d201a6dc3118d201a4ff7694d20004fe7694d20004fd7694d201a4fc7694d200067f6594d2001e7c6594d20006bf6494d20266bc6494d2007f5f5394d20004ff7654d20004fe7654d20004fc7654d200067f6554d2001e7c6554d20006bf6454d2025ebc6454d20005ef7254d20005ec7254d201a4ff7690d20004fe7690d20004fd7690d201a4fc7690d200067f6590d202567c6590d20006bf6490d20016bc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d2024e7c6550d20006bf6450d20016bc6450d20005ef7250d20005ec7250d20094fe76949200067f659492001e7c6594920006bf6494920186bc6494920005ee7694920096ee769492007ded75949200076f659492001eee659492001eec659492007f6c659492001e6c6594920005ed7494920007af6494920007ac649492007f6f54949200076d5494920005ee7394920005ed719492007f6f5194920025ee7094920025ec70949201bf6e50949201bf6c5094920024fc76549200067f655492001e7c6554920006bf6454920176bc6454920005fb7054920025f87054920025ec765492001eec7654920024ec765492007def75549200076f75549200076f655492001eee655492001eec655492007f6c6554920005ef7454920007af6454920007ac6454920005ec7354920005ef715492007f6f5154920007eb7054920025ee7054920025ec7054920007e8705492008cfe76909200067f65909201667c6590920006bf6490920016bc6490920005ee769092008eee7690920005ef7590920005ed75909200076f65909200076c6590920075ed7490920007af6490920016ee6490920016ec6490920077ac6490920016ac6490920077ae5490920007ad5490920005ee7390920005ed7190920077af4190920025ee7090920025ec70909201b7ae40909201b7ac4090920024fc76509200067f65509201567c6550920006bf6450920016bc6450920005fb705
  | 9 => 0xf65d91200067c65d9120076be64d912001cfe75d9120004fd75d912001cfc75d9120006bf54d9120076be54d9120076bc54d91201a4fe73d9120004fd73d9120076bf43d9120076bc43d912004cfe72d9120024fd72d912004cfc72d9120076bf42d912000cfe71d9120004fd71d912000cfc71d9120076bf41d9120006be41d9120076bc41d9120074fd70d9120076bf40d9120075be76d9120014be76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d91201b7af72d9120005bd71d9120006be61d9120006bc61d91201b7ae20d91201b7ac20d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006bc53d91201b6bf72d9120076be72d9120006bd72d9120006bf52d9120006bc52d9120006bf71d9120006be71d9120006bd71d9120004bd71d9120006bc71d9120006bf51d9120006be51d9120006bc51d9120006be31d9120006bc31d9120006be21d9120006bc21d9120006bf70d91201b6be70d9120006bd70d91201b6bc70d9120006bf50d91201b6be50d91201b6bc50d91201b6be30d91201b6bc30d91201b6be20d91201b6bc20d9120006bf10d91201b6be10d91201b6bc10d91200057f755912007d7c75591200067f65591200067c6559120076bc6459120004ff75591200067f75591200047f755912001cfe755912001cfc75591200067c755912001c7c7559120074ff7459120006bf7459120004ff73591201a4fc735912008cff7259120006ef7259120004ff715912000cfe715912000cfc7159120076bf41591200a4ff7059120006fb7059120005be7619120076be7619120004be7619120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c6519120077ad721912026ebf6219120005bd7119120006be6119120006bc611912026fae201912026fac2019120004ff7655120004fe7655120004fd7655120004fc76551200067f655512001e7c6555120006bf6455120016bc64551200773c54551200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20014fe74d8d20004fd74d8d20014fc74d8d20006ed72d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006de31d8d20006dc31d8d2007d7e7598d200057d7598d200067f6598d200067c6598d20075be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d2001cfe7598d201a67e7598d2001c7e7598d20004fd7598d201a67d7598d200047d7598d201a4fc7598d20014fe7498d201a6be7498d20014be7498d20004fd7498d201a6bd7498d20004bd7498d20
  | 10 => 0x620006bd6550620196bc6550620196bf6350620006be63506201979e63506200069e6350620006bd63506201979d63506200069d6350620007af7250620007ac725062008fb77150620196bf615062000ebe6150620197b6615062000eb66150620086bd6150620197b56150620006b5615062000ebc61506200873f51506200873d5150620197af2050620197b71050620197ba10506201a4ff76cc620024fe76cc620004fd76cc6201a6de63cc620006dd63cc620004ff764c620004fd764c620024fc764c620006de634c620006dd634c620005ef724c620005ec724c62006cfd76c8620006de63c8620006dd63c8620025f870c862000cff7648620005df7348620005dc7348620006de6348620006dd634862000ef66148620006f56148620005fb7048620025f87048620025f976c822004ef976c8220027da63c8220027d963c8220027ea72c8220005f971c82200077b51c82200077951c8220007bb41c8220007b941c822001cfe76d952007e7e65d9520014fe74d9520004fd74d9520014fc74d952007e7f54d95200067e54d952007e7c54d95201a4fe73d9520004fd73d952007e7f53d952007e7c53d952004cfe72d9520024fd72d952004cfc72d952007e7f52d952000cfe71d9520004fd71d952000cfc71d952007e7f51d95200067e51d952007e7c51d952007cfd70d952007e7f50d952007d7e76d952001c7e76d95200067e64d95200067c64d95201bf6f72d95200057d71d95200067e61d95200067c61d95201bf6e20d95201bf6c20d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067c43d95201be7f72d952007e7e72d95200067d72d95200067f42d95200067c42d95200067f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067e41d95200067c41d95200067e31d95200067c31d95200067e21d95200067c21d95200067f70d95201be7e70d95200067d70d95201be7c70d95200067f40d95201be7e40d95201be7c40d95201be7e30d95201be7c30d95201be7e20d95201be7c20d95200067f10d95201be7e10d95201be7c10d952007e7c6559520005bf7459520075bc745952007cff75595200067f7559520004ff7459520006bf7459520004bf7459520014fe7459520014fc7459520006bc7459520014bc7459520004ff73595201a4fc7359520094ff7259520006ef7259520004ff715952000cfe715952000cfc715952007e7f51595200acff7059520006fb70595200057e761952007e7e76195200047e76195200067e64195200067c641952007f6d72195202767f62195200057d71195200067e61195200067c61195202776e20195202776c2019520014fe76d91200067
  | 11 => 0x4fd7690e201a6de6390e20006dd6390e20005ee7290e20005ed7290e20004ff7650e20024fe7650e20004fd7650e20024fc7650e20006de6350e20006dd6350e20026ee2058a2007cfd7694a201be7f6594a2001e7c6594a20006de6394a20006dd6394a200976f5294a2001cff7654a20024fc7654a2001e7e6554a200067d6554a20006de6354a20006dd6354a20005fb7054a20025f87054a20074fd7690a201b6bf6490a20016bc6490a20006de6390a20006dd6390a20014ff7650a20024fc7650a20016be6450a20006bd6450a20006de6350a20006dd6350a20005fb7050a20025f87050a201a6de63cca20006dd63cca20025fa70cca20005f970cca20006de638ca20006de634ca20006dd634ca20005fb704ca20025f8704ca201a6de630ca20006dd630ca20007cd320ca20004ff755862001cfe755862001cfc7558620004ff7458620014fe7458620014fc7458620004ff73586201a4fc7358620026f77158620086f65158620086f64158620086f62158620024fc7058620026ef2058620026ed2058620026f61058620026f4105862001e7f76d46201d67e76d46200967d76d462001e7c76d46201d67f64d46201e67e64d46200067d64d46201d67c64d46200067e63d46201d75e63d46200065e63d46200067d63d46201d75d63d46200065d63d46201d67f61d462000e7e61d46200867d61d462000e7c61d46201d76f20d46201d77a10d4620004ff7654620004fd7654620024fc76546201ce7f655462001e7e65546200067d655462001e7c6554620006de6354620006dd6354620005ef7254620005ec725462000ef66154620006f561546200067f76546201ce7e76546200067d76546201ce7c76546201ce7f64546201de7e64546200067d64546201ce7c64546200067e63546201cf5e63546200065e63546200067d63546201cf5d63546200065d63546200076f72546200076c72546200977771546201ce7f615462000e7e61546201cf76615462000e7661546200867d61546201cf75615462000675615462000e7c61546201cf6f20546201cf7710546201cf7a1054620016bf76d06201c6be76d062008ebd76d0620016bc76d06201c6bf65d06200febe65d0620006bd65d06201c6bc65d06201c6bf63d0620006be63d06201c79e63d06200069e63d0620006bd63d06201c79d63d06200069d63d06201c6bf61d062000ebe61d0620086bd61d062000ebc61d06200873f51d06200873d51d06201c7af20d06201c7ba10d0620004ff7650620004fd7650620024fc7650620196bf6450620016be6450620006bd6450620016bc6450620006de6350620006dd6350620005ef7250620005ec725062000ef66150620006f56150620006bf7650620196be7650620006bd7650620196bc7650620196bf65506200f6be655
  | 12 => 0xf4159220024fc7059220026be4059220026bc4059220026ef2059220026ed2059220004ff7655220024fe7655220004fd7655220024fc765522001e7e65552200067d6555220016be6455220006bd645522008f3c545522001cfe7598e20004fd7598e201a4fc7598e20014fe7498e20004fd7498e201a4fc7498e20026de7398e20006df5398e201a6dc5398e20006df4398e201a6dc4398e2000cfe7198e20004fd7198e2000cfc7198e20006de3198e201a6dc3198e20024fe7098e20026de3098e20026dc3098e20026ef2098e20026ed2098e201a6df7598e20006de7598e20006dd7598e201a6dc7598e201a6df7498e20006de7498e20006dd7498e201a6dc7498e20006df5498e20006de5498e20006dd5498e20006dc5498e201a6df7298e20006dd7298e20006df5298e20006dc5298e20006df4298e20006dc4298e201a6df7198e20006de7198e20006dd7198e201a6dc7198e20006df5198e20006de5198e20006dc5198e20006df4198e20006de4198e20006dc4198e20006de2198e20006dc2198e20026df7098e20026de7098e20026dd7098e20026dc7098e20026df5098e20026de5098e20026dd5098e20026dc5098e20026df4098e20026de4098e20026dd4098e20026dc4098e20026df2098e20026cf2098e20026de2098e20026dd2098e20026cd2098e20026dc2098e20026df1098e20026de1098e20026dd1098e20026dc1098e20004ff7558e2001cfe7558e2001cfc7558e20004ff7458e20014fe7458e20014fc7458e20026df7358e20006df5358e20006dc5358e20006df4358e20006dc4358e20004ff7158e2000cfe7158e2000cfc7158e20006de3158e20006dc3158e20026de3058e20026dc3058e20026fa1058e20006df7558e20006de7558e20006dd7558e20006dc7558e20006df7458e20006de7458e20006dd7458e20006dc7458e20006df5458e20006de5458e20006dd5458e20006dc5458e20006dd7258e20006df5258e20006dc5258e20006df4258e20006dc4258e20006df7158e20006de7158e20006dd7158e20006dc7158e20006df5158e20006de5158e20006dc5158e20006df4158e20006de4158e20006dc4158e20006de2158e20006dc2158e20026df7058e20026de7058e20026dc7058e20026df5058e20026de5058e20026dd5058e20026dc5058e20026df4058e20026de4058e20026dd4058e20026dc4058e20026df2058e20026de2058e20026dd2058e20026dc2058e20026df1058e20026de1058e20026da1058e20026dd1058e20026dc1058e201a4ff7694e20024fe7694e20004fd7694e201a6de6394e20006dd6394e200975f5394e20005ee7294e20005ed7294e20004ff7654e20004fd7654e20024fc7654e20006de6354e20006dd6354e201a4ff7690e20024fe7690e20
  | 13 => 0x47200076d72547200076e42547200076d42547200076f32547200076c32547200af77715472000e7e615472009e7d615472000e7c615472009f771054720016bf76d07200a6be76d07200a6bd76d0720016bc76d0720006bf65d07200febe65d0720006bd65d07200febc65d0720006be63d0720006bd63d0720006bc63d07200a7ae72d07200a7ad72d0720007ae52d0720007ad52d0720007af32d0720007ac32d072000ebe61d072009ebd61d072000ebc61d072009f3f51d072009f3d51d0720004ff7650720004fd765072004cfc7650720006bf6450720016be6450720006bd6450720016bc6450720007ae4250720007ad4250720006bf7650720006be7650720006bd7650720006bc7650720006bf65507200f6be6550720006bd65507200f6bc6550720006be6350720006bd6350720006bc6350720007ae7250720007ad7250720007ae5250720007ad5250720007af3250720007ac32507200a7b7715072000ebe615072009ebd615072000ebc615072009f3f515072009f3d515072009fb710507201a4ff76cc72004cfe76cc720004fd76cc7201a6de63cc720006dd63cc720007cf32cc720004ff764c720004fd764c72004cfc764c720006de634c720006dd634c720005ef724c72004dec724c720007cf324c720025ed76c872000eed76c8720024ed76c872004def75c8720005ed75c872004def74c8720005ed74c8720005ee73c872004dec73c8720006ed63c872000eee61c872004fe661c872004fe561c872000eec61c872009f6f51c872009f6d51c872009faf41c872009fad41c8720025ee70c872004fea70c872004fe970c8720025ec70c8720054ff7648720005df7348720005dc7348720005ef7648720056ef7648720005ef7548720005ed7548720005ef7448720005ed7448720007cf7348720005ee7348720005ec7348720007cc7348720005cc7348720006ed634872004fe7714872000eee614872000eec614872009f6f514872009f6d514872009faf414872009fad4148720025ee7048720025ec704872001cff765432001e7e65543200067d6554320005bf74543200a5bc7454320005ef725432004dec7254320014ff76503200057f75503200ad7c7550320016be6450320006bd6450320005ef725032004dec725032004dee72cc320005ed72cc320007cc32cc3200267f7559620004ff7459620014fe7459620014fc74596200967f5459620004ff73596201a4fc73596200967f5259620004ff715962000cfe715962000cfc71596200967f5159620024fc70596200267e50596200267c5059620026ef2059620026ed2059620004ff755922001cfe755922001cfc7559220026bf745922008ebe5459220004ff73592201a4fc735922008ebf4259220004ff715922000cfe715922000cfc715922008eb
  | 14 => 0x1a4ff7694f2004cfe7694f20004fd7694f2001e7e6594f200067d6594f200af5f5394f20004ff7654f20004fd7654f2004cfc7654f20005ef7254f2004dec7254f201a4ff7690f2004cfe7690f20004fd7690f2004cfc7690f20016be6490f20006bd6490f20004ff7650f20004fd7650f2004cfc7650f20005ef7250f2004dec7250f20025ed7694b2004eed7694b20024ed7694b2001eee6594b2004f6e6594b2001e6e6594b2004f6d6594b2004eec6594b20005ed7494b200af6f5494b200076d5494b20005ee7394b20005ed7194b200af6f5194b20025ee7094b2004fea7094b2004fe97094b20025ec7094b201bf6e5094b201bf6c5094b20064ff7654b20005ef7654b20066ef7654b2004f6f7554b2001eee6554b2001eec6554b20005ef7454b20005ec7354b20005ef7154b200af6f5154b20025ee7054b20025ec7054b20025ed7690b2004eed7690b20024ed7690b2004def7590b20005ed7590b20016ee6490b2004fae6490b2004fad6490b2004eec6490b200a7ae5490b20007ad5490b20005ee7390b20005ed7190b200a7af4190b20025ee7090b2004fea7090b2004fe97090b20025ec7090b201b7ae4090b201b7ac4090b2005cff7650b20005ef7650b2005eef7650b20005ef7550b20005ed7550b2004faf7450b20016ee6450b20016ec6450b20005ec7350b20005ef7150b200a7af4150b20025ee7050b20025ec7050b20005ed76ccb20006ed76ccb20005ef75ccb20005ed75ccb20005ef74ccb20005ed74ccb20006ed63ccb20005ed71ccb20236ee61ccb20236ec61ccb20025ee70ccb20025ec70ccb2004fcc324cb20024ed760cb2004def750cb20005ed750cb2004def740cb20005ed740cb2004fce730cb2004fce630cb20006ed630cb2004fcd630cb20006cd630cb20005ed710cb20106ee610cb2004eec610cb2027fce310cb2027fcc310cb20025ee700cb2004fea700cb2004fe9700cb20025ec700cb2004ef46158720004ff755872001cfe755872001cfc7558720004ff7458720014fe7458720014fc7458720004ff73587201a4fc7358720024fc725872004ef7215872004ef4215872009ef7105872001e7f76d47200ae7e76d47200ae7d76d472001e7c76d47200067f64d47201e67e64d47200067d64d47201e67c64d47200067e63d47200067d63d47200af6e72d47200af6d72d47200076e42d47200076d42d47200076f32d47200076c32d472000e7e61d472009e7d61d472000e7c61d4720004ff7654720004fd765472004cfc76547200067f655472001e7e65547200067d655472001e7c65547200076e52547200076d52547200067f76547200067e76547200067d76547200067c76547200067f64547201de7e64547200067d64547201de7c64547200067e63547200067d63547200076e725
  | 15 => 0x461505400b73f51505400b73d5150540007bb7050540025be7050540025bc7050540007b87050540016bf6050540017bb60505400b7b71050540004fe76cc540004fd76cc5401a4fc76cc5400067f65cc5402267c65cc540004ff764c540004fe764c540004fc764c5400067f654c5402167c654c540005ef724c540005ec724c540004fe76c8540004fd76c854004cfc76c85400067f65c85400ee7c65c8540004ff7648540004fe7648540004fc76485400067f65485400de7c6548540005df7348540005dc7348540014fe7654140204fd7654140014fc7654140005bf7454140015bc74541400073d5454140014fe74d972004ebe74d9720014be74d9720004fd74d972004ebd74d9720004bd74d972004cfc74d97200ae7f54d97201a4fe73d972004ede73d9720004de73d9720004fd73d972004edd73d9720004dd73d972004eee72d972000cfe71d9720004fd71d972000cfc71d97200ae7f51d972004ef970d97201be7e50d97201be7c50d972004e7c655972004e7f7559720004ff7459720014fe7459720014fc74597200067e54597200ae7c5459720004ff73597201a4fc73597200ae7c5359720024fc725972004e7e525972004e7c5259720004ff715972000cfe715972000cfc71597200ae7f51597200ae7f505972001cfe75d932004e7e75d932001c7e75d9320004fd75d932004e7d75d93200047d75d932004cfc75d93200a6be54d93201a4fe73d932004ede73d9320004de73d9320004fd73d932004edd73d9320004dd73d932004eee72d932000cfe71d9320004fd71d932000cfc71d93200a6bf41d932004ef970d93201b6be40d93201b6bc40d932004ebc6459320004ff755932001cfe755932001cfc755932004ebf7459320006bf54593200a6bc5459320004ff73593201a4fc73593200a6bc4359320024fc725932004ebe425932004ebc4259320004ff715932000cfe715932000cfc71593200a6bf41593200a6bf4059320004ff765532004cfe7655320004fd765532004cfc76553200067f655532001e7c6555320006bf6455320016bc64553200a73c545532004edf6398f2001cfe7598f20004fd7598f201a4fc7598f20014fe7498f20004fd7498f201a4fc7498f20006df5398f201a6dc5398f20006df4398f201a6dc4398f20024fe7298f2004ede3298f2004edc3298f2000cfe7198f20004fd7198f2000cfc7198f2004edc6358f20004ff7558f2001cfe7558f2001cfc7558f20004ff7458f20014fe7458f20014fc7458f20006df5358f20006dc5358f20006df4358f20006dc4358f20024fc7258f2004ede3258f2004edc3258f20004ff7158f2000cfe7158f2000cfc7158f20014fe7418f20004fd7418f2004cfc7418f2004eee7218f2000cfe7118f20004fd7118f2000cfc7118f2004ef97018f20
  | 16 => 0x894000cfc711894005ebf4118940006ee211894004eec211894026ebe401894026ebc4018940004fe7694940004fd769494004cfc76949400067f659494001e7c65949400073d5494940004ff7654940004fe7654940004fc76549400067f655494001e7c6554940004fe76cc940004fd76cc9401a4fc76cc9400067f65cc9402467c65cc940006df63cc9401a6dc63cc940004fe768c940004fd768c94004cfc768c9400067f658c9401467c658c940006ef628c94004eec628c940004ff764c940004fe764c940004fc764c9400067f654c94012e7c654c940006df634c940006dc634c940006ef624c940006ec624c940004fe760c940004fd760c94004cfc760c9400067f650c9401167c650c940015be740c940005bd740c940007cd320c94000cfe76d85400067f65d85400067c65d85400b6f661d85400067f75d854001cfe75d8540004fd75d854001cfc75d85400067c75d85401c6bf74d8540024fd74d854000cfc74d854000cbc74d854003ebe54d8540006bd54d85401a4fe73d8540004fd73d854004cfe72d8540004fd72d85400b6bf41d85400b6f641d854003ef541d8540014fd70d85401c6be40d85401c6bc40d85400b6f710d85400057f75585400bd7c75585400067f65585400067c6558540005df7358540005dc7358540005ef7258540005ec72585400b6f46158540285fb705854001e7f76d45400057e76d45400be7e76d45400047e76d45400be7d76d45400bd7c76d454001e7c76d454001c7c76d45401e73e74d45400bf3d74d45401d67f64d45400067f63d45400067c63d45400067f62d45400067c62d45400b57d71d45400b67f61d454000e7e61d454000e7c61d45400b73f41d45401ae7f60d45401e77b40d45401d73e40d45401d73c40d45401e77840d4540004ff7654540004fe7654540004fc76545400067f655454001e7e655454001e7c6554540015be74545401df3e54545400073d54545400067f76545400057e76545400067e76545400047e76545400067d76545400057c76545400067c76545400047c76545401df3e74545400073d74545401ce7f64545400067f63545400067c63545400067f62545400067c62545400b57f71545400bf7771545400b67f615454000e7e615454000e7c61545400b73f41545401ae7f60545401df7b40545401cf3e40545401cf3c40545401df7840545400b7771054540196be7650540025bc765054000ebc7650540024bc7650540005bf7550540005bd7550540006bf65505400073f65505400063f65505400f6be6550540006bd65505400f6bc65505400073c65505400f63c6550540006bf6350540006bc6350540006bf6250540006bc6250540015bf7150540017b771505400b6bf6150540007b76150540006b7615054000ebe615054000ebc61505400b7b
  | 17 => 0x67e21d95400067c21d95402b67f70d95402c67e70d95402b67d70d95402c67c70d95402b67f40d95402c67e40d95402c67c40d95402c67e30d95402c67c30d95402c67e20d95402c67c20d95400067f10d95402c67e10d95402c67c10d95400be7c65595402bdfb7059540204ff7459540006bf7459540004ff725954004cfc7259540004ff715954000cfe715954000cfc7159540206bf41595402bcff7059540006fb70595402b57e76195400be7e76195402b47e76195402a73e74195400bf3d74195402ae7f64195402ae3f64195400057d71195400067e61195400067c61195402a73f41195402a67f60195402a77b40195402af3e40195402af3c40195402a7784019540025bc765514001ebc7655140024bc7655140015bf75551400173f75551400073f655514001ebe655514001ebc65551400bf3c655514001e3c65551400bf3c53551400bf3c5255140005bf71551400bf3f5155140007bb7055140025be7055140025bc7055140007b87055140016bf6055140017bb60551400bf3f50551400067f65d8d400067c65d8d4001cfe75d8d40004fd75d8d4001cfc75d8d40024fd74d8d4029ede43d8d4029edd43d8d4004cfe72d8d40004fd72d8d4000cfe71d8d40004fd71d8d4000cfc71d8d4029ebf41d8d40006de31d8d40006dc31d8d400bd7e7598d400057d7598d400067f6598d400067c6598d40006df6398d40005ee7298d40005ed7298d401edf97098d400057f7558d400bd7c7558d400067f6558d400067c6558d401f5fb7058d400067f6518d400067c6518d40006dd6318d4001cfe7518d40004fd7518d401a4fc7518d40024fd7418d40296be5418d40006bd5418d401a6de4318d40296dd4318d4004cfe7218d40004fd7218d4000cfe7118d40004fd7118d4000cfc7118d40296bf4118d40006de3118d401a6dc3118d4028ebe4018d4028ebc4018d40004fe7694d40004fd7694d401a4fc7694d400067f6594d4001e7c6594d400073d5494d400bf5f5394d40004ff7654d40004fe7654d40004fc7654d400067f6554d4001e7c6554d400067f65d89400067c65d894001cfe75d8940004fd75d894001cfc75d8940024fd74d89401a4fe73d8940004fd73d894008eee42d894008eed42d894000cfe71d8940004fd71d894000cfc71d894008ebf41d8940006ee21d8940006ec21d89400bd7e75989400057d75989400067f65989400067c6598940005de7398940005dd7398940006ef6298940075f970989400057f75589400bd7c75589400067f65589400067c65589400a5fb70589400067f65189400067c6518940006ed621894001cfe7518940004fd751894004cfc7518940024fd741894005ebe5418940006bd54189401a4fe7318940004fd731894004eee421894005eed421894000cfe7118940004fd711
  | 18 => 0xe65546400067d655464001e7c6554640005bf7454640015bc74546400cf3f54546401df3c545464000ef66154640006f561546400067f76546401ce7e76546400067d76546401ce7c76546400073f74546401df3c74546400067e63546400067d63546400073e43546401df3c43546400067e62546400067d62546400073e42546401df3c42546400cf7771546401ce7f615464000e7e61546401cf76615464000e7661546400c67d61546401cf75615464000675615464000e7c61546400c73f41546401ce7e60546401cf3f40546401df7b40546401cf7840546401cf771054640195bf765064000ebf765064000cbf76506400cdbe75506400cdbc7550640196bf65506400f6be6550640006bd6550640196bc6550640005bc7350640006be6350640006bd6350640005bc7250640006be6250640006bd6250640015bf7150640017b7715064000ebe6150640197b6615064000eb661506400c6bd6150640197b56150640006b5615064000ebc61506400c73f51506400c73d5150640195bf7050640007bb7050640197b87050640016be6050640017ba6050640197b710506401a4ff76cc640024fe76cc640004fd76cc640005bf74cc640015bc74cc6401a6de63cc640006dd63cc640004ff764c640004fd764c640024fc764c640005bf744c640015bc744c640006de634c640006dd634c640005ef724c640005ec724c64004cff76c8640024fe76c8640004fd76c8640005bf74c8640015bc74c864004eee62c8640006ed62c8640004ff7648640004fd7648640024fc7648640005bf7448640015bc7448640005df7348640005dc7348640006ee6248640006ed624864001cfe76d95400be7e65d9540024ff74d9540014fe74d9540024fd74d9540014fc74d95402b67f54d95402b67d54d95401a4fe73d9540004fd73d95400be7f53d95400be7c53d954004cfe72d9540004fd72d95400be7f52d95400be7c52d954000cfe71d9540004fd71d954000cfc71d95400be7f51d95400067e51d95400be7c51d95402b6bf41d9540014fd70d95400be7f50d95402a57e76d954001c7e76d95402c73f74d95402b73c74d95400057d71d95400067e61d95400067c61d95402b73f41d95402b77b40d95402c73e40d95402c73c40d95402b77840d95402c67f74d95402b67e74d95402b67d74d95402b67c74d95400067f73d95400067e73d95400067d73d95400067c73d95402b67f43d95402b67e43d95402b67d43d95402b67c43d95400067f72d95400067e72d95400067d72d95400067c72d95402b67f42d95402b67e42d95402b67d42d95402b67c42d95400067f71d95400067e71d95400067d71d95400047d71d95400067c71d95402b67f41d95402b63f41d95402b67e41d95402b67d41d95402b67c41d95400067e31d95400067c31d9540
  | 19 => 0x4e40004fd7654e40024fc7654e40005bf7454e40015bc7454e40006de6354e40006dd6354e400cdbe7590e400cdbc7590e40006bd6590e40015be7390e400179e7390e402cf9e6390e40006bd6390e402cf9d6390e40005be7290e40005bd7190e402cfba7090e402cdbd7090e40007b97090e40016be6090e40017ba6090e4001cfe7598a40004fd7598a4004cfc7598a401a4fe7398a40004fd7398a40026ee7298a4004eee4298a400a6ed4298a4000cfe7198a40004fd7198a4000cfc7198a400a6bf4198a40024fe7098a40024fc7098a40026ee2098a40026ec2098a40004ff7558a400067f7558a400047f7558a4001cfe7558a4001cfc7558a400067c7558a4001c7c7558a40004ff7358a401a4fc7358a40026ef7258a40076ee4258a40076ed4258a40076bc4258a40004ff7158a4000cfe7158a4000cfc7158a40076bf4158a40024fc7058a40026ee2058a40026ec2058a4004cff7694a40024fe7694a40004fd7694a401be7f6594a4001e7c6594a40015be7494a40005bd7494a400cf3f5494a4004eee6294a40006ed6294a40004ff7654a40004fd7654a40024fc7654a40005bf7454a40015bc7454a40006ee6254a40006ed6254a400cdbe7590a400cdbc7590a401b6bf6590a40006bd6590a40005be7390a40015be7290a40017ae7290a401b7ae6290a40006bd6290a401b7ad6290a40005bd7190a401b7ba7090a401b5bd7090a40007b97090a40016be6090a40017ba6090a401a4ff76cca40024fe76cca40004fd76cca40015be74cca40005bd74cca40006ee62cca40006ed62cca4004cff768ca40024fe768ca40004fd768ca40015be748ca40005bd748ca40006de638ca40006dd638ca40004ff764ca40004fd764ca40024fc764ca40005bf744ca40015bc744ca4004cff760ca40024fe760ca40004fd760ca40005bf740ca40015bc740ca401a6de630ca40006dd630ca4004eee620ca40006ed620ca40007cd320ca40004ff755864001cfe755864001cfc7558640006bd7458640006bf545864002ebc5458640004ff73586401a4fc7358640006be435864002ebc4358640004ff725864004cfc7258640006be425864002ebc4258640026f771586400c6f651586400c6bf41586400c6f6415864002ef54158640024fe7058640024fc7058640026bf4058640026bd4058640026f61058640026f4105864001e7f76d46401d67e76d46400ce7d76d464001e7c76d46400cf3f74d46401e73c74d46400067e63d46400067d63d46400073e43d46401e73c43d46400067e62d46400067d62d46400073e42d46401e73c42d46401d67f61d464000e7e61d46400c67d61d464000e7c61d46400c73f41d46401d67e60d46401d73f40d46401e77b40d46401d77840d4640004ff7654640004fd7654640024fc765464001e7
  | 20 => 0x1a6dc63cc921236ef62cc92100df671cc921005f571cc921104fe768c921136df638c921006dc638c921105ee768c921006ee768c921104ee768c92111ded738c921137cf638c9211a6ee638c9211a6ec638c921007cc638c921006cc638c92100dee718c92100dec718c92104eef618c9211376f518c9211376d518c921137af418c921137ad418c921137ce318c921137cc318c921005ed708c9211a4ff764c92100cfe764c92111cfd764c92100cfc764c921006df634c921006dc634c921005f7714c92100df4714c92100dec764c92111eec764c92100cec764c921007cf734c921007cf634c9211a6ee634c9211a6ec634c921007cc634c921006cc634c921007e7714c92100dee714c92100dec714c92111fe4714c92111eef614c92111f6f514c92111f6d514c92111faf414c92111fad414c92111fcf314c92111fcd314c921005ef704c921134fe760c921006df630c9211a6dc630c921135ee720c921106ef620c921007cd320c921007d763c8521007d463c852100df672c852100fe672c852100ef762c852100fe762c852104fe632c8521007e532c8521006df63d8121006dc63d812101cfe75d8121004fd75d812101cfc75d8121014fe74d8121004fd74d8121014fc74d81211a4fe73d8121004fd73d812109e7f51d812109e7d51d812109ebf41d812109ebd41d812109efa10d8121005de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581210dd7c7558121005bf74581210d5bc7458121005df7358121005dc7358121006df6358121006dc6358121006df6318121006dc6318121026fa6018121006f960181210267f75596402067f54596400cebf54596400ce3f54596402067d5459640206bc5459640004ff73596401a4fc7359640206bc4359640004ff725964004cfc7259640206bc4259640004ff715964000cfe715964000cfc71596400ce7f5159640206bf4159640024fe7059640024fc70596400267e50596400267c5059640026bf4059640026bd405964001cfe7598e40004fd7598e401a4fc7598e40026de7398e401a6de4398e401f6dd4398e4004cfe7298e40004fd7298e4000cfe7198e40004fd7198e4000cfc7198e401f6bf4198e40024fe7098e40024fc7098e40026de3098e40026dc3098e40004ff7558e400067f7558e400047f7558e4001cfe7558e4001cfc7558e400067c7558e4001c7c7558e40026df7358e401eede4358e401eedd4358e401eebc4358e40004ff7258e4004cfc7258e40004ff7158e4000cfe7158e4000cfc7158e401eebf4158e40024fc7058e40026de3058e40026dc3058e401a4ff7694e40024fe7694e40004fd7694e4001e7c6594e40015be7494e40005bd7494e400cf3f5494e401a6de6394e40006dd6394e400cf5f5394e40004ff765
  | 21 => 0xe7458d21014fc7458d21006ef7258d2111cff7158d21006f77158d2111ebf4158d2111ebd4158d21004ff7058d21024fc7058d21134fe7618d21006dd6318d2101cfe7518d21004fd7518d211a4fc7518d21014fe7418d21004fd7418d211a4fc7418d211a6de7318d21006df5318d211a6dc5318d21006df4318d211a6dc4318d211a6ed7218d2104cff7118d21104fd7118d211067f5118d211067d5118d21106bf4118d21106bd4118d211a6df3118d21106dd3118d21106ee2118d21106ec2118d21024fe7018d21004fd7018d21135de7618d21006de7618d21134de7618d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d21107cd7218d211075f5118d211075d5118d211079f4118d211079d4118d21107ce2118d21107cc2118d21107d42118d211a6df7518d21006de7518d21006dd7518d211a6dc7518d211a6df7418d21006de7418d21006dd7418d211a6dc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d211a6df7218d21106dd7218d21106cd7218d21006df5218d21006dc5218d21006df4218d21006dc4218d211a6df7118d21106de7118d21106dd7118d211a6dc7118d21106df5118d211065f5118d21106de5118d21106dd5118d211065d5118d21106dc5118d21106df4118d211069f4118d21106de4118d21106dd4118d211069d4118d21106dc4118d21106df2118d21106de2118d21106ce2118d21106dd2118d21106dc2118d21106cc2118d211a6df7018d21006de7018d21006dd7018d211a6dc7018d21006df5018d21006dc5018d21006df4018d21006dc4018d21106df1018d21106de1018d21106dd1018d21106dc1018d211a4ff7694d21004fe7694d21004fd7694d211a4fc7694d21006df6394d211a6dc6394d210df5f5394d21005ee7294d21005ed7294d21004ff7654d21004fe7654d21004fc7654d21006df6354d21006dc6354d211a4ff7690d21004fe7690d21004fd7690d211a4fc7690d21006df6390d211a6dc6390d21005ee7290d21005ed7290d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d21006dc6350d212dcfe769492101e7e65949210067d6594921006df6394921006dc63949210df6f529492104fe4219492101cff765492100cfe765492116cfd765492100cfc76549210067f655492101e7c6554921006df6354921006dc6354921005f7715492100df4715492116fe421549212d4fe7690921016be6490921006bd6490921006df6390921006dc6390921014ff765092100cfe765092114cfd765092100cfc7650921006bf6450921016bc6450921006df6350921006dc6350921005f7715092100df4715092100cfe76cc92100cfc76cc921006df63cc921
  | 22 => 0x9521006ef72595210de7c525952116cff7159521006f7715952116e7f515952116e7d515952116ebf415952116ebd4159521004ff7059521024fc7059521014fe76d91210d6be64d912101cfe75d9121004fd75d912101cfc75d91210d6be54d91211a4fe73d9121004fd73d912100cfd72d91210d6bf42d912104cff71d912115cfd71d912115e7f51d912115e7d51d912115ebf41d912115ebd41d9121024fe70d9121004fd70d91210d6bc40d91210d6bc6459121005df7359121005dc73591212e5ef7259121004ff755912101cfe755912101cfc755912115cff7459121006bf7459121004ff7359121006df7359121004df73591211a4fc7359121006dc7359121004dc73591212e4ff7259121006ef72591210d6bc425912114cff7159121006f7715912114e7f515912114e7d515912114ebf415912114ebd4159121004ff7059121024fc7059121004ff7655121004fe7655121004fd7655121004fc76551210067f655512101e7c6555121006bf6455121016bc64551210d73c545512101cfe75d8d21004fd75d8d2101cfc75d8d21014fe74d8d21004fd74d8d21014fc74d8d21006df53d8d21006dc53d8d21006df43d8d21006dc43d8d211367f51d8d211367d51d8d21136bf41d8d21136bd41d8d21136df31d8d21024fe70d8d21004fd70d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d21137cf72d8d211375f51d8d211375d51d8d211379f41d8d211379d41d8d21137ce21d8d21137cc21d8d21137d421d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21136df72d8d21136dd72d8d21006df52d8d21006dc52d8d21006df42d8d21006dc42d8d21136df71d8d21136de71d8d21136dd71d8d21136dc71d8d21136df51d8d211365f51d8d21136de51d8d21136dd51d8d211365d51d8d21136dc51d8d21136df41d8d211369f41d8d21136de41d8d21136dd41d8d211369d41d8d21136dc41d8d21136df21d8d21136de21d8d21136dc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006dc50d8d21006df40d8d21006dc40d8d21136df10d8d21136de10d8d21136dd10d8d21136dc10d8d21006df6398d2111ded7298d2101cfe7598d21004fd7598d211a4fc7598d21014fe7498d21004fd7498d211a4fc7498d211a4fe7398d21104de7398d2111cfd7298d211a6ed7298d21234fd7198d211a6f57198d212367f5198d212367d5198d21236bf4198d21236bd4198d21236ee2198d21236ec2198d21024fe7098d21004fd7098d21235ef7258d21004ff7458d21014f
  | 23 => 0x2367f5198f212367d5198f21236bf4198f21236bd4198f211a6df3198f21236dd3198f21236ee2198f21236ec2198f21024fe7098f21004fd7098f2104edc6358f21004ff7558f2101cfe7558f2101cfc7558f21004ff7458f21014fe7458f21014fc7458f2100cfc7258f2104ede3258f2104edc3258f2111e7f5158f2111e7d5158f2111ebf4158f2111ebd4158f2111edf3158f21004ff7058f21024fc7058f21014fe7418f21004fd7418f2104cfc7418f2104cfe7218f2104eee7218f2104ef57118f21106bf4118f21106bd4118f21106ee2118f2104eec2118f21024fe7018f21004fd7018f211a4ff7694f2104cfe7694f21004fd7694f210ef5f5394f2104dee7294f21005ed7294f21004ff7654f21004fd7654f2104cfc7654f211a4ff7690f2104cfe7690f21004fd7690f2104cfc7690f2104dee7290f21005ed7290f21004ff7650f21004fd7650f2104cfc7650f212ecff7654b2104e7f6554b2104e7c6554b2116fe62154b212e4ff7650b2104ebf6450b2104ebc6450b2111cfd76ccb21236ee62ccb2100ded768cb2104eed768cb2100ced768cb211a6ee638cb2104fce638cb2104fcd638cb2104eec638cb2100dee718cb2104fe6718cb2104fe5718cb2100dec718cb211376f518cb211376d518cb21137af418cb21137ad418cb21137ce318cb21137cc318cb21005ed708cb21234ff764cb2104fcc324cb21235ef764cb21006ef764cb21234ef764cb2104fcf734cb2104fcf634cb211a6ee634cb211a6ec634cb2104fcc634cb21006cc634cb2100dee714cb2100dec714cb2111f6f514cb2111f6d514cb2111faf414cb2111fad414cb2111fcf314cb21005ef704cb21005de7398321005dd739832104efb6098321026f860983210057f75583210ed7c7558321005bf74583210e5bc745832104ef86058321004ff75583210067f75583210047f755832101cfe755832101cfc75583210067c755832101c7c7558321004ff7458321006bf7458321004bf7458321014fe7458321014fc7458321006bc7458321014bc7458321004ff73583211a4fc735832100cfc725832106e7f515832106e7d515832106ebf415832106ebd415832104efb205832104ef8205832106efa105832101cfe76d95210de7e65d9521014fe74d9521004fd74d9521014fc74d95210de7f54d95211a4fe73d9521004fd73d952100cfd72d95210de7f52d952104cff71d952117cfd71d952117e7f51d952117e7d51d952117ebf41d952117ebd41d9521024fe70d9521004fd70d95210de7c50d95210de7c6559521005df7359521005dc73595212edef725952117cff75595210067f7559521004ff7459521014fe7459521014fc7459521004ff7359521006df7359521004df73595211a4fc7359521006dc7359521004dc73595212ecff725
  | 24 => 0xf619814103fb761981410c73f51981410c73d5198141195be7098141196bf6098141007bb6098141197b71098141005bf75581410073f75581410053f75581410f5be75581410f5bc75581410073c75581410f53c7558141006bf6558141006bd6558141005bf73581410079f73581410059f7358141005bc73581410079c73581410059c7358141005bf7258141007af7258141005af7258141005bc7258141007ac7258141005ac7258141007b7715814102fb761581410b73f51581410b73d5158141007bb6058141196be60581410b7b710581411adbe76181410f5be75181411973e75181410f53e7518141005bd75181411973d75181410053d7518141195bc7518141006be6518141006bc6518141005be73181411979e73181410059e7318141005bd73181411979d73181410059d7318141006be6318141006bc6318141005be7218141197ae7218141005ae7218141005bd7218141197ad7218141005ad7218141006be6218141006bc6218141015bf711814100dbe7118141015bd7118141197b5711814100dbc71181411c6bf61181412ffb761181412f73f51181412f73d5118141196bf6018141197ba6018141196bd6018141007b96018141197b71018141197ba10181412f7b9101814116cfd75d9721014fe74d9721004fd74d972104cfc74d97210ee7f54d97211a4fe73d9721004fd73d972104cfe72d972104eee72d972104e7f52d972104ef571d972117e7f51d972117e7d51d972117ebf41d972117ebd41d9721024fe70d9721004fd70d97210ee7c50d972101cff765972104e7c655972104e7f7559721004ff7459721014fe7459721014fc7459721004ff73597211a4fc735972100cfe725972100cfc725972104e7e525972104e7c525972116e7f515972116e7d515972116ebf415972116ebd4159721004ff7059721024fc705972101cfe75d9321004fd75d932104cfc75d932114cfd74d93210e6be54d93211a4fe73d9321004fd73d932104cfe72d932104eee72d932104ebf42d932104ef571d932115e7f51d932115e7d51d932115ebf41d932115ebd41d9321024fe70d9321004fd70d93210e6bc40d9321014ff765932104ebc6459321004ff755932101cfe755932101cfc755932104ebf7459321004ff73593211a4fc735932100cfe725932100cfc725932104ebe425932104ebc425932114e7f515932114e7d515932114ebf415932114ebd4159321004ff7059321024fc7059321004ff765532104cfe7655321004fd765532104cfc76553210067f655532101e7c6555321006bf6455321016bc64553210e73c545532104edf6398f2101cfe7598f21004fd7598f211a4fc7598f21014fe7498f21004fd7498f211a4fc7498f2100cfe7298f211a6ee7298f2100cfc7298f2104ede3298f2104edc3298f21
  | 25 => 0x494100dbc719494117ebf6194941187b7619494117f3f519494117f3d5194941195be7094941005bd70949410f73c509494117fb71094941005bf7654941005be7654941005bd7654941005bc765494117dbf7554941005bf7354941005bc73549412edbf7254941007af6254941007ac62549410f7af52549410073e52549410f73c52549410f7ac525494116dbf715494100dbe715494100dbc715494116ebf6154941177b7615494116f3f515494116f3d5154941005bf7054941195bc705494116fb71054941005bf76cc941005be76cc941005bd76cc941005bc76cc941005bf75cc9410f5be75cc941005bd75cc9410f5bc75cc941007af62cc941007ac62cc94100dbe71cc941235bd71cc94100dbc71cc941236bf61cc94123fb761cc9412373f51cc941237ae21cc941237ac21cc941195be70cc941005bd70cc941237b710cc941005bf768c941005be768c941005bd768c941005bc768c941005bf758c9410f5be758c941005bd758c9410f5bc758c94111dbd738c9410079f638c9410079c638c941105be728c9410079f328c941007af328c94100dbe718c941135bd718c94100dbc718c941136bf618c94113fb7618c9411373f518c9411373d518c9411379e318c9411379c318c941195be708c941005bd708c941137b7108c941005bf764c941005be764c941005bd764c941005bc764c941005bf754c9410f5be754c941005bd754c9410f5bc754c941007af324c9410079e324c94111dbf714c941007b7714c941005b7714c94100dbe714c94100dbc714c94111fb4714c94100db4714c94111ebf614c941127b7614c94111f3f514c94111f3d514c941005bf704c941195bc704c94111fb7104c941005bf760c941005be760c941005bd760c941005bc760c941005bf750c9410f5be750c941005bd750c9410f5bc750c941235be730c9410079f630c9410079c630c941135be720c941007af620c941007ac620c9410079f320c941007ae320c9410079d320c941007ad320c9410078d320c94100dbe710c941105bd710c94100dbc710c941106bf610c94110fb7610c9411073f510c9411073d510c9411079e310c9411079c310c941107ae210c941107ac210c941195be700c941005bd700c941107b7100c9410f5be75d8141005bd75d81410f5bc75d8141006bf65d8141006bd65d8141005be73d8141005bd73d8141005be72d8141005bd72d8141015bf71d8141287b771d8141015bd71d81411aebf61d8141287b761d81411af3f51d81411af3d51d81411afb710d81411afba10d81411afb910d81410f5be7598141005bd7598141195bc7598141006be6598141006bc6598141005be7398141005bd7398141006be6398141006bc6398141005be7298141005bd7298141006be6298141006bc6298141197b571981411c6b
  | 26 => 0x6bf6318d410079e6318d41006bd6318d410079d6318d41005be7218d41005bd7218d41015bf7118d4100dbe7118d41015bd7118d4100dbc7118d41336bf6118d4133fb76118d413373f5118d413373d5118d413379f3118d413379d3118d41195be7018d41005bd7018d41337b71018d41005bf7694d41005be7694d41005bd7694d41005bc7694d41315bd7594d410f73e6594d410073d6594d4132dbe7394d410079f6394d410079c6394d410f73f5394d410f79f5394d410f71f5394d410f79c5394d41005be7294d41005bd7294d4100dbe7194d41325bd7194d4100dbc7194d41326bf6194d41267b76194d413273f5194d413273d5194d41195be7094d41005bd7094d410f73c5094d41327b71094d41005bf7654d41005be7654d41005bd7654d41005bc7654d41325bf7554d4131dbf7354d410079f6354d410079c6354d410f79f5354d410073e5354d410f73c5354d410f79c5354d41005bf7254d41005bc7254d41315bf7154d4100dbe7154d4100dbc7154d41316bf6154d4125fb76154d413173f5154d413173d5154d41005bf7054d41195bc7054d41317b71054d410f5be75d89410073e75d89410f53e75d8941005bd75d89410073d75d89410053d75d89410f5bc75d8941005be73d8941005bd73d8941015bf71d8941015bd71d89412e6bf61d894130fb761d89412e73f51d89412e73d51d89412e7af21d89412e7ad21d8941195be70d8941005bd70d89412e7b710d89410f5be7598941005bd75989410f5bc7598941006bf6598941006bd6598941005be7398941005bd73989412d5be7298941006bf6298941007af629894115dbd7198941007b57198941005b571989410e7b7619894115f3f519894115f3d5198941195be7098941005bd709894115fb71098941005bf75589410f5be75589410f5bc7558941005bf73589410079f73589410059f7358941005bc73589410079c73589410059c7358941007af6258941006be625894114dbf7158941007b77158941005b771589410d7b7615894114f3f515894114f3d5158941005bf7058941195bc705894114fb710589412e5be76189410f5be7518941005bd75189410f5bc7518941006bf6518941006bd6518941005be7318941005bd7318941006bf6218941007ae6218941006bd6218941007ad6218941015bf711894100dbe7118941015bd711894100dbc71189412d6bf6118941307b761189412d73f51189412d73d51189412d7af21189412d7ad2118941195be7018941005bd70189412d7b71018941005bf7694941005be7694941005bd7694941005bc769494116dbd75949410f73e65949410073d6594941005be7394941005bd73949412ddbe7294941007af6294941007ac62949410f73f52949410f7af52949410f7ac529494100dbe719494117dbd719
  | 27 => 0xf748c941015be748c941005bd748c941015bc748c941006df638c941006dc638c941004ff764c941004fe764c941004fc764c941005bf744c941015be744c941005bd744c941015bc744c941005f7714c94100df4714c941004fe760c941004fd760c94104cfc760c941005bf740c941015be740c941005bd740c941015bc740c941006df630c9411a6dc630c941006ef620c94104eec620c941007cd320c941024fe76d814101cfe75d8141004fd75d814101cfc75d814100cfd74d81411aebd74d8141286be54d8141006bd54d81411a4fe73d8141004fd73d814104cfe72d8141004fd72d8141014fd71d81411ae7f51d81411ae7d51d8141286fa40d8141196bc40d81411aefa10d8141006fb60981410057f75581410f57c7558141005df7358141005dc7358141005ef7258141005ec72581410f57e75181410057d7518141005de7318141005dd7318141005ee7218141005ed7218141026fa6018141006f9601814137dbe76d954118dbd75d95410f6be65d95410f73e65d95410f63e65d95410f6bc65d9541005be73d9541005bd73d9541005be72d9541005bd72d9541015bf71d954100dbe71d9541015bd71d954100dbc71d9541366bf61d9541377b761d95413673f51d95413673d51d9541195be70d9541005bd70d95410f73c50d9541367b710d954136dbf7659541365bf75595410073f65595410f6be65595410f6bc65595410f73c65595410f63c6559541005bf7359541005bc73595410f73c5359541005bf7259541005bc72595410f73c525954118dbf7159541007b77159541005b7715954118ebf61595411dfb7615954118f3f515954118f3d5159541005bf7059541195bc70595410f73f505954118fb710595410f5be75d8d410073e75d8d410f53e75d8d41005bd75d8d410073d75d8d410053d75d8d410f5bc75d8d41005be72d8d41005bd72d8d41015bf71d8d41015bd71d8d41346bf61d8d4135fb761d8d413473f51d8d413473d51d8d413479f31d8d413479d31d8d41195be70d8d41005bd70d8d41347b710d8d410f5be7598d41005bd7598d410f5bc7598d41006bf6598d41006bd6598d41335be7398d41006bf6398d410079f6398d41005be7298d41005bd7298d41355bd7198d41007b57198d41005b57198d4121fb76198d413573f5198d413573d5198d41195be7098d41005bd7098d41357b71098d41005bf7558d410f5be7558d410f5bc7558d410079f6358d41006be6358d41005bf7258d41007af7258d41005af7258d41005bc7258d41007ac7258d41005ac7258d4134dbf7158d41007b77158d41005b77158d4120fb76158d4134f3f5158d4134f3d5158d41005bf7058d41195bc7058d4134fb71058d41345be7618d410f5be7518d41005bd7518d410f5bc7518d41006bf6518d41006bd6518d41
  | 28 => 0xd410079c6390d41005be7290d41005bd7290d4100dbe7190d41357b67190d41007b57190d4100dbc7190d41016bf6190d41017b76190d413573f5190d41195be7090d41005bd7090d412cebc6090d41357b71090d4100dbc7650d4134ebc7650d4100cbc7650d41005bf7550d410f5be7550d41005bd7550d410f5bc7550d41015bf7350d410179f7350d410079f6350d411a6bc6350d410079c6350d41005bf7250d41005bc7250d41007b77150d4100dbe7150d4100dbc7150d4134fb47150d41016bf6150d41017b76150d4134f3f5150d41005bf7050d41195bc7050d4134fb71050d410f57e75d89410057d75d894101cfe75d89410067e75d894101c7e75d8941004fd75d89410067d75d89410047d75d894101cfc75d894100cfd74d89412e6bd74d89411a4fe73d8941004fd73d894130eee42d894130eed42d894130ebc42d8941014fd71d89412e67f51d89412e67d51d89412e6ef21d8941024fe70d8941004fd70d8941006ef62989410d5f57198941005df7358941005dc73589410e5f77158941006ed621894101cfe7518941004fd751894104cfc751894100cfd741894104ebd7418941306be5418941006bd54189411a4fe7318941004fd731894104ebf421894104eee4218941306ed421894104cff7118941014fd71189412d67f51189412d67d511894104eef21189412d6ed2118941024fe7018941004fd7018941306bc4018941004fe7694941004fd769494104cfc769494101e7e65949410067d6594941015be7494941005bd7494941015bc74949410f73f54949410073d5494941006ef629494104eec6294941004ff7654941004fe7654941004fc7654941005bf7454941015be7454941015bc7454941006ef6254941006ec625494100dbe769094115ebe769094100cbe7690941005bf75909410f5be7590941005bd75909410f5bc7590941006bf6590941006bd6590941005be7390941005bd7390941015be7290941017ae7290941006bf6290941007af6290941007ac629094100dbe719094115fb67190941007b5719094100dbc7190941016bf6190941017b7619094115f3f5190941195be7090941005bd70909411b6bc609094115fb7109094100dbc765094114ebc765094100cbc7650941005bf75509410f5be7550941005bd75509410f5bc7550941005bf7350941005bc7350941015bf7250941017af7250941007af625094104ebc6250941007ac6250941007b7715094100dbe715094100dbc715094114fb47150941016bf6150941017b7615094114f3f5150941005bf7050941195bc705094114fb71050941004fe76cc941004fd76cc9411a4fc76cc941005bf74cc941015be74cc941005bd74cc941015bc74cc941006ef62cc941006ec62cc941004fe768c941004fd768c94104cfc768c941005b
  | 29 => 0x79d320cb41007ad320cb410078d320cb4100dbe710cb41105bd710cb4100dbc710cb411073f510cb411079e310cb411079c310cb41107ae210cb41107ac210cb411c5be700cb41005bd700cb4101cfe76d95410f67e65d9541015be74d954100dbd74d95410f73f54d954118cfd75d954100cff74d954100cfd74d9541366bd74d954100cbd74d95413767f54d95410f6bf54d95410f63f54d95413767d54d9541376bc54d95411a4fe73d9541004fd73d9541376bc43d954104cfe72d9541004fd72d9541376bc42d9541014fd71d95413667f51d9541024fe70d9541004fd70d95410f67c50d9541376bf40d9541366f710d954101cff76595410f67c655954136dbf74595411df3e54595411df3c54595411e5f7715954136cff7459541006bf74595411de7e54595411debc54595411de3c5459541004ff725954104cfc72595410f67c52595411debc425954118cff7159541006f77159541004ff7059541024fc70595411debf405954118ef7105954100dbc765514101ebc765514100cbc7655141015bf75551410173f75551410073f655514101ebe655514101ebc65551410f73c655514101e3c6555141005bf7355141005bc73551410f73c5355141005bf7255141005bc72551410f73c5255141007b7715514100dbe715514100dbc715514118fb47155141016bf6155141017b7615514118f3f515514118f3d5155141005bf7055141195bc70551410f73f505514118fb710551410f57e75d8d410057d75d8d4101cfe75d8d410067e75d8d4101c7e75d8d41004fd75d8d410067d75d8d410047d75d8d4101cfc75d8d4100cfd74d8d41346bd74d8d4135ede43d8d4135edd43d8d4135ebc43d8d4104cfe72d8d41004fd72d8d41014fd71d8d413467f51d8d413467d51d8d41346df31d8d41024fe70d8d41004fd70d8d41006df6398d4120df57198d41005ef7258d41005ec7258d4121df77158d41006dd6318d4101cfe7518d41004fd7518d411a4fc7518d4100cfd7418d411a6bd7418d4133ebe5418d41006bd5418d411a6bf4318d411a6de4318d4133edd4318d4104cfe7218d41004fd7218d411a4ff7118d41014fd7118d413367f5118d413367d5118d411a6df3118d41336dd3118d41024fe7018d41004fd7018d4133ebc4018d41004fe7694d41004fd7694d411a4fc7694d4101e7e6594d41015be7494d41005bd7494d41015bc7494d410f73f5494d410073d5494d41006df6394d411a6dc6394d410f75f5394d41004ff7654d41004fe7654d41004fc7654d41005bf7454d41015be7454d41015bc7454d41006df6354d41006dc6354d4100dbe7690d41356be7690d4100cbe7690d41005bf7590d410f5be7590d41005bd7590d410f5bc7590d41006bf6590d41015be7390d410179e7390d41006bf6390d410079f639
  | 30 => 0xe7458432014fc7458432006ee3258432006ed3258432006cd325843204ef72158432106ee2158432106ec215843204ef42158432004ff7058432024fc7058432106f71058432007cd329803204efb6098032026f86098032005bf745803210dbc7458032007cd325803204ef86058032004ff7458032006bf7458032004bf7458032014fe7458032014fc7458032006bc7458032014bc7458032004ff715803200cfe715803200cfc715803204efb205803204ef82058032265bf7694f41015be7694f41265bd7694f41015bc7694f412673e6594f412673d6594f4132dbe7394f410ff3f5394f410ff9f5394f410ff1f5394f410ff9c5394f41005be7294f41005bd7294f4100dbe7194f41325bd7194f4100dbc7194f413273f5194f411c5be7094f41005bd7094f410ff3c5094f4125dbf7654f41015be7654f4125dbd7654f41015bc7654f4131dbf7354f410ff9f5354f410073e5354f410ff3c5354f410ff9c5354f41005bf7254f41005bc7254f41315bf7154f4100dbe7154f4100dbc7154f413173f5154f41005bf7054f411c5bc7054f41185bf7694b41015be7694b41185bd7694b41015bc7694b411873e6594b411873d6594b41005be7394b41005bd7394b412ddbe7294b410ff3f5294b410ffaf5294b410ffac5294b4100dbe7194b4117dbd7194b4100dbc7194b4117f3f5194b411c5be7094b41005bd7094b410ff3c5094b41175bf7654b41015be7654b41175bd7654b41015bc7654b41005bf7354b41005bc7354b412edbf7254b410ffaf5254b410073e5254b410ff3c5254b410ffac5254b4116dbf7154b4100dbe7154b4100dbc7154b4116f3f5154b41005bf7054b411c5bc7054b4123dbf76ccb41015be76ccb4123dbd76ccb41015bc76ccb41005bf75ccb410fdbe75ccb41005bd75ccb410fdbc75ccb4123fae62ccb4123fad62ccb4100dbe71ccb41235bd71ccb4100dbc71ccb41237ae21ccb41237ac21ccb411c5be70ccb41005bd70ccb4113dbf768cb41015be768cb4113dbd768cb41015bc768cb41005bf758cb410fdbe758cb41005bd758cb410fdbc758cb4113f9e638cb4113f9d638cb410079f328cb41007af328cb4100dbe718cb41135bd718cb4100dbc718cb411373f518cb411379e318cb411379c318cb411c5be708cb41005bd708cb41125bf764cb41015be764cb41125bd764cb41015bc764cb41005bf754cb410fdbe754cb41005bd754cb410fdbc754cb41007af324cb410079e324cb4111dbf714cb4100dbe714cb4100dbc714cb4111f3f514cb41005bf704cb411c5bc704cb4110dbf760cb41015be760cb4110dbd760cb41015bc760cb41005bf750cb410fdbe750cb41005bd750cb410fdbc750cb4110f9e630cb4110f9d630cb4110fae620cb4110fad620cb410079f320cb41007ae320cb41
  | 31 => 0x493212f6c525493223cfe7690932014ff7650932124fd7650932014fc7650932006bf6450932016bc6450932005df7350932005dc7350932127ac4250932007cf628c932005dd718c932136de618c932136dc618c93200cfe76d853211ef661d8532014fe74d8532004fd74d8532014fc74d853211ef641d853211ef621d8532024fe70d8532004fd70d853211ef410d853211ef46158532014fe74d8132004fd74d8132014fc74d8132006de32d813200cfe71d8132004fd71d813200cfc71d8132006fb6098132005bf7458132125bc7458132005f7715813211df47158132026fa6018132006f9601813201cfe75d903204e7e75d903201c7e75d9032004fd75d903204e7d75d90320047d75d903204cfc75d903210cfd74d903210ebe54d90321a4fe73d903204ede73d903204cfe72d903204eee72d903200cfe71d9032004fd71d903200cfc71d903210ebf41d9032024fe70d9032004fd70d903210ebc40d9032014ff765903204ebc6459032004ff755903201cfe755903201cfc755903204cff745903204ebf7459032006bf545903210ebc54590321a4fc73590321a6be43590321a6bc435903204cfc725903204ebe425903204ebc4259032004ff715903200cfe715903200cfc715903210ebf4159032004ff7059032024fc705903210ebf4059032004ff765503204cfe7655032004fd765503204cfc7655032006bf6455032016bc645503210f3c545503204cff759883201cfe7598832144fd759883204cfc759883204cff7498832014fe749883213cfd749883204cfc749883200cfe7198832144ff765483213cff76508321a5ed738c832005cd738c8321a6ee638c83204fce638c832105ee718c83204dec718c83239fce318c8321a7cc318c832005ed708c832004ff764c8321a5ef764c832006ef764c832004ef764c83204def734c8321a6ee634c8321a7ce634c832397cf534c8321a7ce534c832007cd534c8321a7cc534c83238fcf434c8321a7ce434c832007cd434c8321a7cc434c832105ee714c832105ec714c832387ce314c8321a7cc314c832005ef704c832007cf764c832005cf764c832006cf764c832007cf744c83238fce744c832007cd744c83238fcc744c83204fcf644c83238fce644c832007cd644c83204fcc644c83238fce544c832007cd544c83238fcc544c832007cf714c832387ce714c832105ce714c832007cd714c832387cc714c832105cc714c83204fcf614c832387ce614c83204fcc614c83238fcf414c832387ce414c832387cc414c832007cf704c832005cf704c832007ce704c832007cd704c832007cc704c83204fcf604c83204fcc604c83238fcf404c83238fcc404c832387cf104c832387cc104c83200cff7658432007cd325843204ef4615843204fe42158432004ff7458432014f
  | 32 => 0x1557c75581421b6bf6418142026fa6018142006f96018142014fe74d9632004fd74d963204cfc74d963204edd73d963204eee72d963200cfe71d9632004fd71d963200cfc71d96321467f51d9632024fe70d9632004fd70d963204e7c655963204e7f7559632004ff7459632014fe7459632014fc74596321467f54596321467f535963204e7e525963204e7c5259632004ff715963200cfe715963200cfc71596321467f5159632004ff7059632024fc70596321467c505963201cfe75d9232004fd75d923204cfc75d923204edd73d923204eee72d923200cfe71d9232004fd71d923200cfc71d923213ebf41d9232024fe70d9232004fd70d923204ebc6459232004ff755923201cfe755923201cfc755923204ebf745923213ebe545923213ebf435923204ebe425923204ebc4259232004ff715923200cfe715923200cfc715923213ebf4159232004ff7059232024fc705923213ebc4059232004ff765523204cfe7655232004fd765523204cfc765523201e7e65552320067d6555232016be6455232006bd645523213f3c545523212cfd7694e321475f5394e3201cff7654e3201e7e6554e320067d6554e32005ef7254e3204dec7254e32124fd7690e32014ff7650e32016be6450e32006bd6450e32005ef7250e3204dec7250e3204cfc7498a3204eec2198a32114ff7654a3204f6c5254a32007cf3254a3210cff7650a3204fac4250a32005ed76cca321a6ed76cca321a7ce53cca32007cd53cca32236ee61cca32236ec61cca3204ef46158632137d63158632004ff755863201cfe755863201cfc7558632004ff7458632014fe7458632014fc7458632006df3258632136de3158632136f63158632136dc315863204ef7215863204ef42158632004ff7058632024fc705863204efb6098232026f8609823204ef86058232004ff755823201cfe755823201cfc7558232004ff7458232014fe7458232014fc7458232006ef3258232004ff715823200cfe715823200cfc715823204efb205823204ef82058232014fe76d9132126be64d913201cfe75d9132004fd75d913201cfc75d9132126be54d9132124fd73d9132126bf43d9132124fd72d9132126bf42d913200cfe71d9132004fd71d913200cfc71d9132126bf41d9132024fe70d9132004fd70d9132126bc40d9132126bc6459132004ff755913201cfe755913201cfc7559132124ff7459132006bf745913213cff7359132006df735913223cff7259132006ef7259132004ff715913200cfe715913200cfc7159132126bf4159132004ff7059132024fc7059132004ff7655132004fe7655132004fd7655132004fc7655132006bf6455132016bc64551321273c5455132244fe769493212f6f529493201cfc76549320067f655493201e7c6554932005df7354932005dc735
  | 33 => 0x46158642004ff755864201cfe755864201cfc7558642006bd74586420d6be5458642006bd5458642004ff73586421a4fc735864204cfc72586420d6bf425864215ebf415864215ef6415864204ef7215864204ef42158642004ff7058642024fc70586420d6bc4058642005de7398242005dd739824204efb6098242026f8609824204ef86058242004ff755824201cfe755824201cfc7558242076be5458242006bd5458242004ff73582421a4fc735824204cfc7258242004ff715824200cfe715824200cfc7158242076bf4158242076fa40582421b6bc405824204efb205824204ef8205824201cfe76d95421567e65d954204cff74d9542184fd74d95421867f54d95421867d54d95421a4fe73d9542004fd73d9542014fd72d95421567f52d9542186bc42d954200cfe71d9542004fd71d954200cfc71d95421567f51d9542186bf41d9542024fe70d9542004fd70d95421567c50d95421567c65595423adef7259542184ff75595420067f7559542174ff7459542006bf7459542004ff73595421a4fc73595423acff7259542006ef72595421567c5259542176bc4259542004ff715954200cfe715954200cfc71595421567f5159542176bf4159542004ff7059542024fc705954201cfe75d8d42004fd75d8d4201cfc75d8d4213ede43d8d4213edd43d8d4200cfe71d8d42004fd71d8d4200cfc71d8d4213ebf41d8d42006de31d8d42006dc31d8d42024fe70d8d42004fd70d8d42006df6398d42125ed7298d4223def7258d42006dd6318d4201cfe7518d42004fd7518d421a4fc7518d421a6de4318d4210edd4318d4200cfe7118d42004fd7118d4200cfc7118d4210ebf4118d42006de3118d421a6dc3118d42024fe7018d42004fd7018d42004fe7694d42004fd7694d421a4fc7694d42015be7494d42005bd7494d421575f5394d42005ee7294d42005ed7294d42004fe7654d42004fc7654d423a4fe769494201e7e65949420067d65949421576f529494204fac429494201cff7654942014fe7654942174fd7654942014fc76549420067f655494201e7c6554942005bf7454942015bc7454942177ac4254942006bf6590942006bd659094204dbe729094204fae729094204ebf6290942017af6290942005bd719094200cfe76d854214ef661d854201cfe75d8542004fd75d854201cfc75d8542006bf74d85421a4fe73d8542004fd73d8542014fd72d8542006be42d85420e6bc42d854214ebf41d854214ef641d854214ef621d8542024fe70d8542004fd70d8542005df7358542005dc735854214ef4615854201cfe75d8142004fd75d814201cfc75d81421a4fe73d8142004fd73d814200cfe71d8142004fd71d814200cfc71d81420a6bf41d81420a6fa40d8142005de7398142005dd7398142006fb60981420057f7558142
  | 34 => 0x8d521467f51d8d52006de31d8d52006dc31d8d52024fe70d8d52004fd70d8d52006df6398d52006dd6318d52014fe7418d52004fd7418d521a4fc7418d521a6de5318d52116dd5318d5200cfe7118d52004fd7118d5200cfc7118d521167f5118d52006de3118d521a6dc3118d52024fe7018d52004fd7018d52004fe7690d52004fd7690d521a4fc7690d5201d7e7590d520057d7590d52005ee7290d52005ed7290d52004fe7650d52004fc7650d520067f649495204d7e729495204f6e729495204e7f629495201f6f62949520057d719495200cfe76d855216ef661d85520067f75d8552014fe74d8552004fd74d8552014fc74d85521a4fe73d8552004fd73d855201cfd72d85520067e52d85520ee7c52d855216e7f51d855216ef651d855216ef621d8552024fe70d8552004fd70d8552005df7358552005dc735855216ef46158552014fe74d8152004fd74d8152014fc74d81521a4fe73d8152004fd73d815200cfe71d8152004fd71d815200cfc71d81520ae7f51d81520aefa50d8152005de7398152005dd7398152006fb6098152005bf7458152175bc74581521be7f6518152026fa6018152006f96018152174fd75d964204ebd74d96421a4fe73d9642004fd73d964204cfe72d964204eee72d964200cfe71d9642004fd71d964200cfc71d96421667f51d9642186bf41d9642024fe70d9642004fd70d964201cff765964204e7c655964204e7f75596421767f54596421767d5459642004ff73596421a4fc73596421667f535964204cfe725964204cfc725964204e7e525964204e7c5259642004ff715964200cfe715964200cfc71596421667f5159642176bf4159642004ff7059642024fc70596421667c5059642165bf765524201ebf765524201cbf7655242015bf75552420173f755524201ebe65552421673e655524201e3e65552420073d655524201ebc65552421673c5355242005bf7255242007af7255242007ac7255242016be6255242017ae62552423b73e52552423b73c5255242005bf71552421673f51552421b5bc70552421673f505524204edf6398e4201cfe7598e42004fd7598e421a4fc7598e4223ebe5498e42006bd5498e421a6de4398e4223edd4398e4204cfe7298e4204ede3298e4204edc3298e4200cfe7198e42004fd7198e4200cfc7198e4223ebf4198e42024fe7098e42004fd7098e4223ebc4098e4204edc6358e42004ff7558e4201cfe7558e4201cfc7558e42126de4358e42126dd4358e4204cfc7258e4204ede3258e4204edc3258e42004ff7158e4200cfe7158e4200cfc7158e42126bf4158e42004ff7058e42024fc7058e4204cfe7694e42004fd7694e420073d5494e421675f5394e4204dee7294e42005ed7294e423acff7654a42015be7454a42177af4254a4200cff765864204ef
  | 35 => 0x18ef641d8554024fe70d8554004fd70d85541e6bf40d85541df3c545855418ef46158554024fe76d81542bf3c54d815401cfd74d815404cfe72d8154004fd72d815400cfe71d8154004fd71d815400cfc71d81542bebf41d81542befa40d81543c6bf64981542b73c5498154006fb60981542073c54581543c6bf64181542a73c5418154005ee7218154005ed721815418df67118154005f57118154026fa6018154006f96018154014ff765925204ebc6459252186be5459252156bd5459252004ff73592521a4fc7359252186bf435925204cfe725925204cfc725925204ebe425925204ebc4259252004ff715925200cfe715925200cfc71592521567f5159252186bf4159252004ff7059252024fc7059252186bc40592521857f76552520167f76552520147f765525201d7f745525201f3f74552520167e64552521873e64552520163e64552520073d64552520167c64552521873c43552520057f72552520076f72552520076c725525201e7e625525201f6e62552523b73c42552520057f71552521873f41552521bd7c70552521873f405525204edf6398e52014fe7498e52004fd7498e521a4fc7498e522467f5498e520067d5498e521a6de5398e52246dd5398e5204cfe7298e5204ede3298e5204edc3298e5200cfe7198e52004fd7198e5200cfc7198e522467f5198e52024fe7098e52004fd7098e522467c5098e5204edc6358e52004ff7458e52014fe7458e52014fc7458e5212ede5358e5204cfc7258e5204ede3258e5204edc3258e52004ff7158e5200cfe7158e5200cfc7158e5212e7f5158e52004ff7058e52024fc7058e5204cfe7690e52004fd7690e520073d5490e5204dee7290e52005ed7290e5200cff765865204ef461586520067d7558652004ff7458652014fe7458652014fc74586520de7f54586520067d5458652004ff73586521a4fc735865204cfc72586520de7f525865217e7f515865217ef6515865204ef7215865204ef42158652004ff7058652024fc70586520de7c5058652005de7398252005dd739825204efb6098252026f8609825204ef86058252004ff7458252014fe7458252014fc745825207e7f54582520067d5458252004ff73582521a4fc735825204cfc7258252004ff715825200cfe715825200cfc715825207e7f515825207efa50582521be7c505825204efb205825204ef82058252014fe76d9152176be64d9152176be54d9152166bd54d91521a4fe73d9152004fd73d915201cfd72d91521667c52d9152176bf42d915200cfe71d9152004fd71d915200cfc71d91521667f51d9152176bf41d9152024fe70d9152004fd70d9152176bc40d9152176bc64591523bdef7259152014fe74d8d52004fd74d8d52014fc74d8d52146de53d8d5200cfe71d8d52004fd71d8d5200cfc71d
  | 36 => 0xc0050000000000800400000010004002000800c002c004002c000000400000000050000000002000000000010000006000400200080040008003001c000000000200000000004001000000200080010008025001000600040000000001000000200140000004010000800100080030004003000c000000400600080000048006004000300100000020002001c00200000000030002000000500040000020002000000000040040020001000c00400000020000000000800f000c000002c000000c0000004003000800000140000004000000000000040020014001000000400000020000000000800d00000000030000000800d00040020008000000800300280010000000000000500040060000007003c000001000300040050000008000000000100000000003000000000440010004002008400f000800b005000e00040000000001000000d000000300180000000003002002400040010004000002c001001c00100040040004001000c000001000100040020010002000c007000000000000080010010000000b000000400100020004000001400e00000080008000000c002000400100000000048000000400100240000004000001800100280010000002000000c0008006001c00300000000000004000000000000030008016000000600100020004001000400100000050000006000000b0000002001400a00100000000000001400200000000000004002000100000070010000000000000280010000005000000700140020004000000c026001800000000110004000000800b0004000000800000480060000000001800000000000000019000c00500000000014000000000c005400700040000004001000c0000004001000000300200030000000001c0020004000002400200000010018007001c00100000020008003001000300000000000016000c0010004004000000100000070028001001800300080000000000000000300140003af3c54d8954014fd75d89543ae7d75d895401cfd74d89543bebd74d89541a4fe73d8954004fd73d89543beee52d89543be7c52d89543aeee42d89543aebc42d895400cfe71d8954004fd71d895400cfc71d89543be7f51d89543aebf41d8954024fe70d8954004fd70d89541873c5498954006ef62989541773c54589543a73c5418954006ed6218954014fd751895401cfd74189541a4fe7318954004fd731895404eee52189543ceed521895404eee42189543a6ed421895400cfe7118954004fd711895400cfc71189543ce7f51189543a6bf4118954024fe7018954004fd701895400cfe76d85541e73c54d855418ef661d85540febf74d855401cfd74d85541e67e54d85541e6bc54d85541e63c54d855404cfe72d8554004fd72d85540fe7c52d85541e6bc42d855418ebf41d8554
  | 37 => 0x1400100080020000011002000100000000010000000800000000010008004000c0110014001001c0090004000000400600000450010003000800900100020000002000c0010018001004c0000000003001800e00000030028000000400a001400600040030004008000000b0000001000001b0014008003800f0000003003c0120004000001001e0078000001800200100000018001000000300040050000002000c000002c000000000000180030008005000400200000160000004000000b0004001001800000040000018001001c0000004001000800500040010014007000c001001001b00180030000003001c00d0004001004400e00180000004000000800400080030000003000c00000040130000002000400f00180020034002002c0000008000002c00900000010004004000400d00240010008009000000000100010008000000000300000020000002000c015001c00500040000018001000400000180000000000000400300040080024001000400000540340048002000800d0004000000c0050004002000400000540030000002000400d00380020004003001800400040000004003000400000000050064005000800400040000004000002c0010010000000c000000000100c00010000000000c0050008009000800f00000000008000004800000040040030003000c002000400300000010008006002400c000000000080030004003003000000000050004000000400100640080008008001400000000070008007001c00800180000008002000400100140010004000000c00a00040020014010003400200000000038010000400200540020008003001800300080100004000000800000000010030017000403f002400200380040030000000800000040010000002002c004003c00b0000000000000f0000002000000000580050010000004c0000000000000800e00000000010001000800000000010044004000000000000150000000001400200040000000001003000700040030000007001400300000040000002001c0000000000002800600000000004010002c002000000300000040004000000c0000024001001400000340010004009000000000000050018003001400300200080014000000c0000000005000000400300000008000003400200080040038001000c00e001000000000050008007000000600200050004001006000100080020000005000000300000020010004000000400180010008002000000000000020000002001800c000000000100010000000001400100000000008009000000100700010008000000000d0020005001000300900000004000005000000100060000000004000000000060004000002400000140100008001000c00400140170008004007800000780200000003001000
  | 38 => 0x100010000000000c0050000010006800d000c0020000004000c00b004c00700140100008001001400000000000000000000400b0014003000c002000000900540040010002000000000040000004003000000000080070000002001800b001400200040010000012000400c000c0000004005000400100000000000001002800000100000004002003800100040000000000001c0000000001000c006000800200180030008009001c001000000300000040018001001400200040040014008000000300000000000001000c00000000060020004000c0170000002000000300140000000004000000000300000000002001800000000000000000000c0000000009000c000000c0000004001001c0000018005008c0040000000000400500040020008003000c006001c003000400b00100000004000000002100140050004001000c001000801200100000000000000400100000000004004000800200040060004007000001e0058000000c00c0010008003400f001c003000c000000400900000000000001003c00100000050000007000400000380070000003001000d00180170010031000000400180090000005003000100000040020005000c0040000003000c00e0018000001000a0000001000800500240010020003001000600000040004000000000000040000034001000c00b000002d0008006004c0000034000000000800040000000000003800a000000200180000004001000c000005c0000000007000c00900040030000001000000700040090000001000c0040024000000000100240000038001000800000080000004003001000000000010000007008400300080060010009001c0000000000000000000000020000001000801b0008000000000c00080000004000003c00200080000004000000c0000000000000c009001000100040040008003000000500000000050000001000600040030000004001000200000000004000000000000080000014001001800400240020004000000000e0048001000000700100000030004000000800080000000005001c000000400d001400000080020024000000c00100240020000009000c0000020005002800200080000018016000000f0000001002400000140000020002006000a000c009000400500000020014001000000000040000008000001801a0000000007800000300080008007001401600000010028000007c003001c00100040130010001000001d0000004000400700000010010000000c009000800e000000200000040004000003c0060000002005800000380000010002000000000000000000000000000100140000004000002c002000c0160000001000c001000c01200000000000001000001a000c000000400f001400200040000004002000400800
  | 39 => 0x800000080000014000000400900440000000000000000000000000000001001c00a000c00a00080030008001003c000000c0030000002003c0030000007000801200000060048000001000000480120010000000000b00000010010000000001a001000000000090014003000c0010014004000000000440030000006000000800000050004002000000000000110010000003400a002c00100000020014007003c00600180010000002001000d0038007000000100100010034001001c000000000400100230008003001400500040000000019000c008000c0080010004006c000002800500000020008001000000000000120000000000c00900080020028000001400000200050018001001c006000000000300010000002000800c002000400000000028001000401600000050004001000c0140000000004c03a0000002000c0010000003003c00e00080000024001001003600000010008000001001300040030008020001800000000000000004001000000000070014004000c0020004000003000000000090018002000801000040020010005000c0000034005001000100140010008009001800b0014004000000200080020008001002800100380050000001003c003000000400000020000000000000c0008001002c00800040040000005000800100040010000004000000a00040060084000000800200140040008001004400000040000000001000000100000020000002000400500100020014002002400600000060004000000c000003c00000140060000001009800100480020010001000800b0030000000c00000200010000007002400000000010014000000800900180250000003000c00100000060000001000c0020000005000c002002c005000c0090000001000000000440110008000000c00400080040000007000400f000000100180110008000000400d0004000000800100300010004000001401000180000004006002400d000c000000800e000400200040060008007000000200000080018000003c0010000007003400600080000000002001c00f000000100000000000003001001800000000010004000c003004402100040000000004003000000000000000001002400500100040014000000001c000000000380020034004000000400500020008013001c00800040030000000000800000500000000002000c00700600010010002000c00a00040020000000000400000140050000000000c0010000006003c003000000200380040024000000400000000000008001000c002000400c00100010008006000000700180010000000003000e000c000000000200080080020001000c0010000004003400600200020004000000000c002000000040000008004002c00b0004013004c008001000300000
  | 40 => 0x669642afb4a098000a068000b19800001c000026e271000021389e21cfe6be1eaba00010a000000043c000000010091268e0e00000005f68ee8711a80c00003c148a14aa00000000000000b4d19047b90000000000000015501690000afbcd840000e0c8468af432400003c980000000000b0980005b28000162294c00001c9000096c8cd0b2417aa3fe4079c160000abc43a847675f000063117aa0002ce600015e4c169d4a30602d000000002a80c261e800009922de6b1f9e7881640e4908938c3f7156275446199b700000d80000bc52a1e000000000000001f600000001dfe98a9ca2a388b8c54e15145382602000000083400005108746054800050b96749e69dae219af9eb7f178f58aae3e6a9cace02b8000c170396014c000b8a87f035d28ea00000009728f7e75d800093900003be089e0001baaa93813c00019cc00019e41eb400098d2c64777207a9101cf80000000516000075494a89af84b40da861b0000000bc9b007a2785e00000000000151e5d5800000000007f9000090f0000634800000000009a4800072d90585b780006a351002378c6440aa3da2f980007c110b600000006f9c0008f58000000000059f8f2a00000000001a5e7de00006b1204e359000010f8000a9f800022f80000dc8000664000000006c450f988e8bb282bb8d00005a4000000008a8a070d5c582822430c08d4b9e8000049000000020365e70a3aa90160e3f629478bd0000000201e19f2ba6894af4c3e280009c5ebd62ea0b1e55c2f90500882823a8b2c57512ee122836e06e226c1999f2c83300008860000bf5000087619649bb23ae464dbea44c9cf27ce800000006a41100bc64f28000000176f0729f58b7114a21ca885b9ed2085035a9300cfafdea5640000001c0600005908c626df557800015684f60002a6807f94f41470642000060e0001e102b5033000000004ab8000bf6af84000000000000000002fe0b8c80000001ede7c98a62a51a687000000096e149416880008e8800068b00005ae2b503cc0000000000200000150018002001400000080000000001000000100000000010000000000600000010000003000c00b00040000048000000400300040010004006000000b000400200080000038002000c0000000001000000000000070010002000c004000c00500040050000007001800b006800a0008011001c0010014012002c00e001400000e8001000400100380040004008006c003000800400040060004003002002e0000000002400e000400a0018006000400000080000000002000000800240060000004000400000240010004000005c00500040030004000008400300080020000004000000a000000100f00080000002001001e00000040038000002000300180000000000001000900080000000001000002200000000
  | 41 => 0x242000000024de2b11d5668a03666321f82a1700008b28000978861000000004f5000020027660fc9e2882a568e65d0000000096200000005600fe6713987bab0143ab5027c8a68c8c881988ca00000001628000ac2af86223c1663bdab18577a77e2c501a20000000b529aea00000008f9ab64a1a0c82200800000008fe0e4650289ca01493b0c104e681000dc5db86a900004ed8c8aa8d8000000163e8dbae263b712daa9805ec6cf000000016ba2eaa0fc00014d44ddafb27ba8448bd9a5200002a742a20000000131e000011267fa5a21a611a60000000553800025c06e84d9000081d00000002f5600005e2aa28196000297c00000000000000000140982c800079c8000000000000023c22e026d49ca14349660efc79f8000248c00000021be83d9d40b6b91ab00027fa000000000000000d390f60002e547400a4a5d49198a4816263d826a71da15129d3000048c0362a1300000001468a0587c65799edb22900f472b800000000000902d640000dd42e38aeaa250b4e92b2ee05610e3e58588840000e008c580008b909d00000c2c41880000002b8209d00001028000000127c00015da000236c40baa320001e8ca4ddfa600003e8866c00000010ca438000000002de63fc00032e0000000226677883b07c4906003aa2fe332906c9bf95a83308f1838c87221222006104abfc8278bac02800000000c949e29d28000091f2fa8000a40a2b8bc9000000000009fdaa3460c0eb67ab001a000000013a000034dd116000000065125aeb2c800095f286c5f72a00be0a4aa96280dc00000004eb0d7f7758ef49e44bfa23009782728e164ef82f29df267000027d044e01c015d16626ec520091821b686cacc62f767a20001bb60002f0a37c9df2000050e000079861c81923aba56b00029e40000000009e9ea97f28d0ab7400045f0000281870c3310d68525a0728d684be00003f023d1a9680291af79a8f1a14827ee0eeae0ea1498342c5800000000002481aa0000260000003780001ecc2f500000000000000182439888720000000424800092f80004af40008f39d1eaa206f21d7c0004f5703c7090000a2c161c0000b0e000075c109817ab31267e77a14ec7432e7807c2d9440eae305d3d1902b78ad60e340a4a498ac649309e246c947480127de2f90674b6681ee46a158a0001b9e00002a6a248a0d99cc3822aa12df226615e81b8dca60a12b909121480003004030163072827ea913986801da63e777800000007fe67e1278acba4a48718bcca3f000000012d8742adf4000198c37180007f6800060c9c7f8d3a2349ef0000000009073905f8969e6aa6cb8000c0396b647e8726884000000001c20000000964000000000000000000a692988000000000011a994c800000022e600000006a300003351ee02a6102000000000000b500000
  | 42 => 0x22869e79ac64b00e9ea9c6e2c0000000abb800018a00009d5871c6d1839a2ab80002eda3024df9e849f581cb1c5d2cd88f865800000002808ed8b2b132d836037c00001d148bae1c04590f36d90b7884392f858a2bb400024f8578064c8e620ab94a24fa3168cbe91ea8046258ed249a80625eb8bf86a68a2698c8ffa9cd21f55ed24329c115c0111ad0651293ef2850e74b21a1fca7e237e115cf9c4c820f00001f7d000182200014e48c1aff42a3084600000003c88000000000000000001aead4486f4000000262656e1d960000f786f41cb896100000000fc00001b6ca89898417096a429b535688c82e28ba83a468319ae4b797fc5b5a2262d0800000e880cb5885956ce80005d4293436720882ce2f375fc93064ecabecad940002ef9ce000008a615f9cdab729d49b520d70b4f041cb82863c174ac8e5c69ebc8638c6a75bde7a1761a38917800057880000b00000000133ca42ac6e03f0f8c000041a963a05c268ab4000000008ab865600028b453200004f4282c271a4d8786a0214f5f04cbba11c09b45a8a35f119a0d31b94aa3ae8c256985e23a0024254000016e049c000123c23800000002b7800007585c80000000005a0000a16648133e000000059c80007e4ac160002d4c27901b01be1b2026d80000000000acd400000000000000000b131aba0000ff4bc8adfe99d400015bc000000000017788066859f500be8000000000035b84baa3ec00071eae74000276e873817e000302a5400000000000000000007c0225400001946458000a8624dc5e2975c8e3a6ac409ac1c06c814aa76161200009f2873000000028c818f8fe0b938000ad89e1600000009400000365577e0001a3e0000000000000058b8000000141400000009d8a8a44ea0000000098e9ba0000000247c5a68906b1a9cbe59a147eb3c00e66e19cd846880003cbac0c4c58000b9600008359736ae52c3a000011e0001cd00001a2640e0000210106ab1b13309210000000121122b01a439a8000630c00073d0b7a3f383de00025b24c90000000000000000004aa00000000000ad98cb4a6a9d5e7a52d6e0001ab8000033c62206b6000122c6af00008c8a1980000bde000000035c854e7848eec0001afc0002e7600000c841280007e6130437f15ea000076f0000000000063a00005c000000004e02a6e1e9268e49480000000000000158800028087bd0bf60b080008dda878795800000002020002ef6a66000000000004fb95b087e00007e328480001d70135a11eb120fe274e8000000000099b057f9a2000076f8cfe0ea1976000000600004e4ab10a727e2a6d00002dda39a1e406b923826f98842918801c64f00000000000b420278af29cea27f00002691f4c000293c6491f0e1bbaa96a3a0e4a1e585bc75cac7801800002158000a70085025280000002c7a
  | 43 => 0xe8f883075a288d041304b803e9d900000000a4bc0000000000000000048ca030b0418fcaf800009b680006469a11950000096e80008851c2e487126600020c89ffc0009c199c60000000531ae880000af600005b6000013aa1ba9c650290d40b1824a70500007d198e61ce8000b638000967a1900c500000000b4d954910c55285975c28000000169476c000e7d596c0803a21a287082a8e78000833a6e08a6800000000000001bf497a17a29c9000000001a86d38fd44ce20546d100002da090c000062c22680a200014ee22e25b04d680000000000523ad740000b5439b80000002992000076787680006a3800008700ebb480000a5f984e26a26660000b5f0000000b840000000000001caa0a80991e8b002b2a00013e267980080000c680cd0f1008ea32a0001a1a00015b4600993b54f9280a1588682520000000199641d3062296963c8a501689bd8ead1979b90658091c2ad0e920e00000ae215be000000000000000001e2a000000039d40007d2800000026547fc00003dd000000000000000f2caf980000000e900000b3e804abaa06e828c8fb81dc0000aac0001d54a1c8bb48871d2e3eba53e37814264d02a8186d46a8349abb854fd2b249fa48a30a19a495d8a005809464bfa292c4b2e18239718a6a30828a889531019b80a6a6e847c3458ffe0002b025b921a801f93122998e3a5e99d58b6d0f9855f144e2170dd6b1f0f3a94881ae000000084121c82699eb89542dcc0001fba47824909a586f4000000000000000000000aa1edbc00c0260863189e9dddd641d69e5400026c64c8e60c230881400026fb20b964b7dd185c37482b8b128b089e7de86b73aab638918f470e1d8451a9c6882808ae5ab21de3878aec0000000437a900678831845629353002f7203c800000021b116f6cca42fa45899489be00025b40002f180000000a38c000066c0267802c0a000147674a8000718a3e06bb97705fe8c5218194a40000f481e6df7000000000000000b609ee630300000000000bd92a166e580008c980000000e18483017c0f883f655d01463c1800090b2c400000ccc6d21ba46c32bfe7b200003bc1b128819b2c0731e2c1b98000b849798065c00000025cc253974a0001e8eaab9a9481004ec483eeb861f8d4a29a93daad1a8240000b56154800070a29e20001880baf295e924e91c07400001ce30266991dce5219ec34e489443b28ddcc11aae65db12b72e78000000162cb8008d2588230029bce88933ab8a0a97022a581d202b60e6400027081be8f6f105a94432e842800013af37b0000000000000000008d8949a6af80002459e6e871000000016a89551de61e9a0c62bf170f70f2cfc142120e000193e69600000002c2a00017400002ce200000009b8a49610d909644600000001932a1924749aa00004cb085a0000480000
  | 44 => 0xa76f711000000015202139d6a48420c4143292a5c128540000a3259813ce78800000001dbc000000000018b50002e900e89b4ca262c8a0001a4400001ec1e680007ab80005f8800000000002f5c4940002f1281f9e3c885cdc88e1e5d232a8fbc7269c8a519a7c41d9828400000000000e1c991139c1f10000000000073a0b607a7ebda4829934000302eb37acae0000000a7c063400000f000000000000c5c00025261578064a666806b338000011000000000009e3aab100001809c08f043070c14000073e178c1287fea716218a73a0df88bca46e9970000e96a05235606180009759cb00002b00000000000018a43c0a2c434219ce5cba75b78fa34692e97bc93f9c3028782486fc970b9e6082c00019f07258e8c27625306652b8684c9b62ba111306aa812c00000a80000000297e35c0002b306b29ba21b9c4e064aa9622da8176000157e0000130a3c8000000000000000006b4a4c0000000000014fc96182269d000002f400001da400056f00000002aa34a9000000000000000000a596c5453100001a8a1888cf1e46727ade8a1103be24640001c38000000000029e80007a719269320000b35aa9e2b40000239232e0a89706c0c000000000002536990b4797d9a7d9e021dd8000bb38000882206000000000001a5a00000002e88729c0807c800000000002f580002c62704800000000000000000000000000000008f4800024a0fc204719ed385489608d1fee6340b744d32bf80f22976000000000000006a219ee00027220f7c00015b615c69f90bc0000b2a16621feb0f1ad84ad156cab6128200028be00022620000000436800090658c00000000007800000018fa00000003e911e20002e82000120299c9e4706217a80000000848201a0000000000000018480000002f20000000000000005d1810c3fd80000bf800090328f300000007f793945fd8496808c9a050a8000ba614f600000001b01b8d00011504d780003681d3287cd1f2266222c00016aa903858d13fae287e3800090794501cba27a2961c5300000f868aa84abed992c68ea0e24b66a330044000892000000010828a7b01300000009690000740a7e400a8000a4400005fba0ae4b5255c1a403245fd17e6000022ca9340000000c1e00000000000000965aeac0000db400000006920c546cb424c86a47b80000b267b4a116451810e31317549e740000000000000183b1f5ac9e024a742211c00021300007818000718c000000156e00023bb31caa2200003ee8ea85d40000000a1d800059f0156000138a38e13cc0002efc0000dc01bf0ea59e1c0008b30bfd00008c4604000000008084d0ea6500011600002d5600000000c711d60000000000191e11058580001ebe461800045c800000000000000eea4e788444f605ae894400079912a36ac0fa50361d9e3fe0ba
  | 45 => 0x3ce000000063e1b404342c7600000008f31288bff2cdc614800000012b8000281f00009e82e601f400015686112cee000197c44b16dc09f010f0af87fa0e31ef8074c4ee00000000001640000299e0001f840000acc6158d52add51a40001820564af340000000395a7523e10f2460a8000b629f9c13887d20001cc0a9f02505f3000000000001b780002440c806fda9c400000004e81a12000045280c80000000000a600000626000000000000000dc20000000865800000025800000000000205e7da1544697206800daffe9bca10a17e57e8555800038ba43e000292732b0c6e00000000000000b81860c0000000000000000023bd80429744a1ac0856722b40000474a54eaa400000000001bd787261e3bf7c0468f0283c68d8ef27012d7804daa850a48000bda300d0000000000000030180001b7096d0002a06000064469d8000606800000000000000000000086400000003d58655000000000021804d1e9ee3e22e40b9f035c7b5641475183100d91e3702c1548000303a000066200000006a0c00054900000001745a1f43e60001d7e00000001340b887f41e801eb3001000098c00007940d0e1925fb2c943542563a1d23b00000000147a9d6a9d400079c2b3e30e00000666368000124300000000000f6200011d8b270000067000000000007e8192800000000002f361399c266c6808c94e00008148000ab880001829b5c13e8ae4763800000012d2a9784a6000180e75a58ad00009bd9780a7c74113ea653c9b0aa700006ddaba06dd0000000008864607de7708000a850000455000000000c900000008c6800086f1b287c190648dc0a2e3b880005c900004ef0000bea226e7e1828622d8617a2a874c9be02620000c628b6000029f80000001b8742700008682d280b707e8000000000008a0936c43800027ce1082aa21ff1c0300000000002df6b76062b00000001bf8000485a28820486be85b80004178543be81d6657218e086b6a6689d242a7651b10378ab700002b0e000000000000001a0900067b2ea60000000a70a9ec9281c2c0000000749800040400000000000000000000000001128000000000028480003e88000943a99f0f1a774ba68151a3765bc5212b9e000000000003a60002379000052aba4916a00000002b2800000000be8fe0d124d9ada600019d875ae49a000253b2f0165800013b8191aef29698b6e0000000000000000011b683a2793b630f2f0001938515261093d0000b1cab38000011043f00003d100009bc000000011cc91a1d550000adcbcfaed07d680000000e20a0e800000000000002e20824af100000000890a1e25444000a6e000000007d08509e087e3c35eafb9d08b44921807c91e644800002c4800000006e028540000002c909519ea900004f00000b8a5cb09123e8d98ab4
  | 46 => 0x9500000000d3a0001c10000000000000000002714000000002d86b02cc800020d208247c0320117ad7d0c2a57895803cc23884a06c5800065080009fc22b29e508d600000000001c0c0001adeafaacc07aa00000000000a2580003d2c0000000fac0948a17000131a51e2d1600000006cf96c8041e25eac5979662de8fec100fde593005c00001233398000b9c80ac00000008b50000000069ca83800091d854c879ce6300011c827500001cd000000000000bb0756b9300000000000000207609785d6851140806aa9a12f46a580002fd60000d349380d2ea0f84c00000000000238c8a3800029914b40000d54b538d460000000000000033f2b32000112e92c2d3a89a8000b3aab5400029c1a420000085800000009210000000000000050800009e187cc4c540002cf0000c058bd93b1adb80000000b9fa64a299e2120002a4a0000c9200000000000000000000000000000000bc28291ffc26200000000000aa41c357c40bf2bd500000000c780002f6c0000000000002e556ab7e0000000000000012b261200000000000cb041cae770002170ad5a4d447d000000000000a582f852d9f2091c893a98693aaa04a01c32609340002276b9fcebc98e0000bc08b6f00000008fe9d9a0001c547cd9db46ea25f62fa2c9d4b5b01034fa83681b2e3a503e92db9696a09ea4712359941c05b988a972284ea0d204617d42daa8a21645f22dec54c9b9d00284d81ec000000004f800000000000d6c90700003409eb249180003489e9e00019da00016a213100009902f7e4a962b065a8000223631000025dc00000000000000000087a00000001e7a9fab29032c31600002f8a5424742f2a459250a8189c8862ad191ae60b1c0000a840002c4628d44a400011560000ae63fbcae865227ad6818946604a37a7d8edd0816a2380000000000100226096c611b9cce6dc80009522dfa7c500003f591269f09c6c5572cb416d40009a9545d574af7f78929a04ab00003fe400016100002ddce30bc0000000000008e026863b400001498a309b9166c005805e7ea80001cd91ee1d3a2987b880000000df80002b7c3501c66715858b0000000406928e86e06c2a5e2aa561502565328c3e00000de0002d2c9630000000000095a800072392ce000000000023320001d8aa55dd80ac78000ada1bd20001a8717e9c2a0001acc6a24d36a8682a40b2000000018cc3d69068bf841e25e1800000000000000000b3d0da6000148c7e648300001aac500282f27c0cae8918cb2a525b6e00000007d49f60000000000000004a3439e0001372448a88a41517c060d86800001fbd00000001ee80001239c604e405165c39bbc7a90aee56b27e000023b43471f557b528f092700e2a6c2df045d2320a1e494900007185e6821014e1f0a4548000aefaa434718f384caa3d400000
  | 47 => 0xe5a01a91f664ad75e000210cab7a30800000005dd8000b6c8000b6e8a246e680000001f620001b8a394a918aae1bbea4ac000ac80000a1e9f6fbd780000002a546bc9f6a2601bb2a9ce7969ae2e9421a6db05cd000002d2a9a5e410e27ee0625084916c49d27b0aef0e0a5061d6ebd185726ff12c62a18b4a0eb0d4235f400040040003b580008e20000000227811900007931afa0000000847153451b858c0001968af32a5cb009052620979e0001e62702812200017176f0c00000000000000000926095f8af1efaa5680000000000000000000000002db1a3200026e6b4a800000000009b78000a7f64081768000000000082d8b5e000103400000000008e61aeb8b9c970c208930a0de4d2ac389e995731c4ea129daaa6c3960b2e0002cd250c0000000000000024705df06aa297a2c858ce19a63f90c0000052800017124390236a49044232dae500000ba043497ca2a29a988d288d800016a607aa44653f80008e196e80128000be70ce40000000000000028e61460c9807c9ccc000076800000012c47d980000000ba60000000000000000000000000000bbb90429470000aa189ce0000f460002241a2c96484372bf600000002cc0000ad283d233005b04a32ea03140000000259aa891ee8000223a8a8800000000009c68c340000000000000071c0000000015c77b800000025e4290800023c2b6e8c92a5211e000000004f40000d283ea18065418000a7f8a4828400006aa10860001cb4a3580000002dc80000000000210085daf2806051b000000003a60ab80002fb00000b971541fdc0000000000000000020d285b0000941800000000001d514d00001f32b600000000184c6028b3a60512348fb169c94e991218d828e56ae3b616b261862c0dfaaad1d71be98de82e480000001b9359aed989460000b4280000000f724b05c90000098a4d5000000000007d39b5e0000000000000000028289938000000000000000000000f28000000094f1ba6522228a1400542384a130a9dc000000226f36183860a21d9c3c704a85b8800025568139adc0002f580009a4c00000018b200000005f42ceca96806c8ba14900002ad616a1686000000030b80000001d75000000025f8000000000065797941609e98a726d841970000995a20299a1e5824a8dd07cee17440607428be8e7e5c00d56915970c5da8d943630e2a0002608a1780000002b26adbccc872521ec7190aa26e2000071280000001dd82e158ca65e64f00002044bfac81f4811b006710a6584f8522a66942c0e72ba28f7a9abbcc871672126bc00000000000000000166e000031250d9322ac505fe6121afeaf90000157000000000000000000395237b52b00008fa1c1e54d800000028d201de79500000001e723523b0a8180001396a8b9cde000000000000cb53611b800000005
  | 48 => 0x8ec80000002d5287d000012c9762172000000010c80001ba1bb1000098924fcb2cd526add254415508485a300baa0cdc763ddad180000ea000000008728d0c00021ba6850fd264f40008542a8c59c1032000000000016f800000000000000540ab846a787742f4c0000002832000000000024387ec076e9a126eea3702e8413800000000007f880000001d4800000000000a680000000000000036c4a786af57c30810c8c0e3dbac11813f06a1916e2491a1800006545358000b2fafc479d830c79a07ae10000003ef97e02460000c0093331f9a683451d9ac0000000403a8db000000010c2a100642db68e427f439324a609729a23e480008651a682d3000085e800000008ce76a00009109f47403c00000000002f3867a00021cd6cd01046f61732b9a000000000002860000b1bc00065700008c518e419029f32088b640002a7a67287ca4f01c6d0da1348000111a00021aaa7c589200000000002e0808794f09ad9dac8a303741d9673cbe90000443ac7098113588ca2bb649d800064ead880002698b8520e40000762000161a000031e919082600000000350000965144000002f40bb98da8588fcc82e000087aa67100000009a50abe7370e145e00649000000000019aa0000000bf29906294000000000001e411c21c085480000e449eb0000000246a000150a10780006ba29ce4dd00008772a1c2b08000b7197c457a0000000014e4bf053500000005f3800093c82822fd40003b90000000000000000000001bfd10080000000892906ab9c1d8c0005b996660000852636054a3c02f6abf8ccfabb3018293a1022bb6164616a80002d4800073c136e0002af2a638ff3abd000000000000001d100000000000000000000000002afc027dbde7261a8b8b0272e00012be7b3884aa3910488218a0f00000005371300b98800057584c88259e0e808000058e0000577000000000003cc9ba012124040000000a49400000000009ea1f0200000001cb00001a28f8e00000003fc0000a5a297b00012b0a5002766fadd3e55080001b40000b8600008b8800015e8cf28008000a1f800078ec0000000618be5800000000000000000000000000000007cb800000000000001826000000017a2cd86f800000000eb89a5d73cc0d80003e58032b2e8f4c13d6adc239ac710000000b288000beb000000000000000000000305e561ae64304935c31380009a2a9423bf80007f59ac80001a00abe212c2209c43bdc236025be5589d614800000000000178b28694040000370b8e2af000007c27fb160420900000000000000166a00000000000f3463096f200013c800000001f50000022800001300002d99998000000062f8eee38880000001c48000000006f121d28d9f1e7cce0f854609270000000000076454dc000a880000a78e680000000000000000508
  | 49 => 0x1000000000003c32f040001d3c00000001e9eef800000006889956000000009e80000002512b3c82f6000112a0000000702000034380000c58000000000021c0000000294e21b840e70c9eb44018b401d8198218e078a329304a3d0800000022f00000000036adea29528a048680e800020161c400007060000a80883c0002c9200002d442a9c74bdda2441728b0a3451fac6e7118e2dd65d03a395b585815d0ba2887cb9b98a00718000000000089900000002aa61868cf6af41ccc23c5bcc2106870a438d7622c87f86b50f49669800087000000001f9e00028889a30ec8b1ccf86000194a9d7a1064a802b600028f677e11d4014800031d000091f86b2a48cca806303aa000000000011de2b88000a6b0000000233092d000086d0e080698996000047000000004c200009de000000016225c5a9388889ec4000000034c2fff00009bc0001bae0002a2114f0040000000012f000070d9498497a99c29c0000b2c1ca828b1b2221780005800dacc030000c1830340b1227e1d293f2000000086191100000d965cc000000000000000000009400000000009e4af8056080003da2b52a91555241b87996ee8000ac900000510c881c28556760da42ae411fe00024e672b110a0002782a02aff09c480000000000000181e61a891a00013786b080009dd80000498311000000000000000002ab09e7119e568209c000134232f06a600023bea6121b06c71de427ea72c97e876a0000000a8e137c0001884000113c57f0000356183a60e2ae800020700002445893aabb00017680c08eac4170a764b2800000000003cf01fc0002d043271b7a20800006a025f00000000000262889280006da09c2967000000000001b5abde3a109545ab800000000004aac0004f5910868b9a0e0000dbc0000000000000000005868de04b608f000063da07c495800090e80009f30bfe6fb255a7e85fc8227269b84621a2000017813300005818b720001fd8a31800000017d5000249284900000001d0e1a18000000000079980000000f6c000000000001f866f80000002d3e00000007472b9abac2b4e0712d7266d00008a48afec150000000000000018aa10910d13e001ac6750f08000182e00022a80a600001f92ed6828c00034a8560101af0e000000000021f9527277000000000000000750ee44325aabc160d0ba4a9c8ec55f41e51650d1887c6c4e83caebeb751914431a9b942b950886795f0000245c89f2922593a75c5ad00008f6158eb77150b0d2a36a4ad97b0a32af1a8c48bd8875923a0002d698ee1b060001a347cf0000bce80008eb16360002a1b010800000002d8b7800005031b026b56b06000051800002640002d7cb0f87abaf116ecac88860b2f1a6000011ca0ce00001c18000b86936800027e8260c000b498f9400012e620e80000000000
  | 50 => 0x294d5c6eb1498f28212ca60002eba9b2800000009024f0aa4261d2b04a799c80b1580560000e8273d995823704dc0001a3100011a50e3afbe5f79b80291248200007507142e4a37303d16efcb514ed0ff70001ada781033a02603eaad7026c2a6a720809c3560001a4a48a859c39f00007938600785000099427d20002d3894d800000015a627b944c000296cb2d8e340002d5f000000000000001d780008ce00000000000000097169b28bcb4b80000000e280000000905ab5f6fe1e8219a8fec00d138e7a42ed214c878c7538000a8f9dc8327965200000007ca1e8a8500000b6485ce5e800000d190b40001258477000000010945180e103711dc6a4fa5100751930040982c52c0c7e9622d9c00027fcb269fe69fe196c000009e1fd80000001f5c77529c857307a3000012a7a98d1e0001e9600000000001d73000000075e10082bc8000000057c655c000000000000023ca33a1900000000073e80005e10000317612aadb5e8869886da000069400022ac6cd8394b908000bd48904165aa6a0000000ab4000064b9bc6000090e4e8a1fa798000022408cc3ee018a4240000a5ca15600004560002fe68980000acf2c8000008e7566126082b000021a963233b2b8069f25044ff63e40ed0eb09340a829ea97d67389db26e5d75aaf0aeaa8b6928a0a52ada895869e7dc800000000007f28f9f000000023e91147ac12a21ef80006cc9a70b3d80007889e5200000000000000000000000016d40001e180d414e9c0fa3ea0000a80b5b1a568380645b2580000002a679ac0000946a1f2485091e000056669e0c704044c024112ad593100005b82050306abfa00013840ca24f6a16a6a459ea840b979688b1818ec7bb2726a8f11fc0050a209768000000274e0001b565f9152d54a845800000000001314aeb2f5a33730123e800004f90f1e0002a645110724b27cae03622516000000000015a237b80003fb8000c00c0004260c3601d0d6b96a145e3e09b04afa0000ad305440f58670b3f929430eab10000000000000000000000000243600000000000dfe61ea30c0481f545fe25be4fd8f4a28a84449f9cea436e9fce360074875e959466880001ea4f400000000000000087900007621432295a22a5bb95ecadda08000004867271e300c00000bef0490a98a7305a098e284093dc50e11d26c7914eb87800023f000000025f40002eb6000000028940006010000896a05b00016ea46826a6be880008878bda19b0752000000018e5d4235f80000908b04266818e2f1101b1dce70e000271cbbaa9799e80000a8218de000000004e11700002fd00002aa8000113ea6c9df4a732366761800045289262cd293200003d7ada81e850f2aba16d07f400015ca0000f5c23d80000001feaae380007c219fc66f2ac6000017f40719e800000000000000000
  | 51 => 0x4000053e29a8a28a44821da54c8e448aab1a13465228000a2d800090a042e2114fc680b80000000000bfbdb42000000000000004c9999c5ca8000000000029ac0000000000305a9ed49e99f409a80000000b228942a50a91064e0000df000000004ce99b0000150477b000075b64c6b5824506022fd300025c07ef82fcad22f500000000000114400006600001bb0000000000005a0a3b304e993214c870ac04000295c5b31d0643d000000001a10002993a0400d2416b032bab80000001fb7aa08000748ae96000184200000000000a9c000274a34c9c5746000000002674b9e4000a38000010aaf600000000000022e537680e000000000030082c8000018d4000000271d0002b61000000055524440000000000200854e8fe8000000000000000000000000000039189685a10c48732045073199de88c301158c40005de19780000000b052616050000000011da46a80005710000490a7547b0ade20001aa200009d228e2e36998d39892505d07df1fb6c06000076302660000000c1494a06881cd60aa9c5c6ab91063eea56c00002b200006962938000257952874d0000110d7582e6a69e000000078b959a2b49fa21c1435a04d2524031282749b00ce8061f88637039727aa126502c58eac705062a78b069d6a70c8bd8000000274400006d40002f625a0122500014240611d920000f9052e800077480009ec81593d911428c113520000000534a7caa33ae6ca781bb40002803936af312810000189ee48aa6282aab480007e74e268298d8a1c68cf8a7789f6a351f6e5e6c932797877c187a70a7589cb258423bca74000076903cf96d800055e800000009724a9a5083761e4235120aa00000000002ae4000000068f0000c0b00d00000000752dd2c00019f2789a98c77e857d79f2cc89b20cf42cd970256780000000000bf7000000000ee2288b1015b00000000000b75a572839800031e93282f7d38682f96d83f2a995000220a6218a9205a9208c0780000001eda0000000b888000127b01c0000000997152b000090a33680000efcca60001d240000000000057800004c3000000061fc000b0d0dce10b0ea8b809c020a7abd46500000b9d6048a142d7a5cea1720000704a959f34597942887b8a0e80b03d84c2ae736d9868ea61837a0002ea8bf1a42600018ac9878000ad6800085a000062d80000001f3e0000e3c592944800000008edf009b440bb200029da9da108eb9594105bea97a21e09f4659916641c126872092200000f2d4a42e9c35a80000002838000000068c000018119f600025ea0002b5d0000000959a906b6a2f88b3e13881052ea29f2c2cc4c095306682f8ea556e6082f0de65f75d748c390e872fc00000000000a9c00078dace435680007b28000bdd22404532c502570a5c4fa1b2a49c2a304bf83b81bd9f4439c9e3
  | 52 => 0xf000001640001b780a682f00001e0c5d100001dcaff988b84c68a08aa48bb8e506f219baa6743406e302220000000c06800000000004f7800028f80003b79972077800094a99c826520900f08f1656a8000032800018fecd00861c588855b520000000000019a0001c7e0002acaa11800000000000000faa09193b04a688430001c6a0002f9a00005c6000188ca7e6b9204340009fc87c000000000000000000000025322c600000003f914bc0001ff863c00000ec9e4a8931cee976211418b9fbc0002a04000109aa3fe9b430107810001c000880676000043c102063206fc3ec0f68000000266e2c840006b72e4689a1aec4569f9a3bb4000000233e3021fa44c30000334800090600006bc0e360aa0804a07a7848be0b460ae83e0a4796c4bd089c04eb80004ce43fa0000000a1801748a9107cbbea2fcbacaf4e182246e41985048ea15fa69004340678af0196856a4339f7e31000000e624aeb70a86f742d7ba405aeec047c000000000038680000002fcc00023964be80000001a1098c0000000000039a4000b6fa0ca00030588858000520a1b931280000002b44b3812bc2230000b7e1e9aa5c0576516af1c7f1613a1c78238a7482ea17f2b7127f6aaa7662e042e580005c50000000114000015ce000120666e1c8600003f4b9aa4a28568000000131cada40000000000b5849c400013621a6800000000004e90000000000000000000001dda0000000842016c000135000000004bbc960000099e00000aa7e5c000ab4d81c00004ea3b68d3b023800000000004911c8c0b480000001a4e4cb800011fa95251ea2ba376af2c0000ec073500005c98000000000000009b2b0880004b2199eaec2b0708c1e455e38f5800007b40000bbc3bd400061e12e05a7a7a400000009abb0007541349080187069d2c8c9bd062057f899c000096ead80bd559919105e323a03b317ac54b0ee695a16da04180009f19ca4756655e9e00000000000000000001df800000000003db80005388000000000073f20ec00000000000b53888256700000001ad126e000000000007824a867fb00028e606d8e428a10000277a48c585000085983b60002ee2a13dfe03864b63ac32d247871685bbd1f424b0e5ecaab6d369ee8b2800012ea0002fd76820000a0b807a5faa1a61edac5eabd9ab228dded061d8dd54cd0d387aeb042aaca34c003da6e5e0c00000022280002e704a5800000014ea8a8507a00010462d20c0e0f2883e92c800040d800000002288442258527a86254728580f8c0000000000b8b8000000294bab821ac53005be000080e6780000000246c308000003d800082500000001c3a595c0008289ab66e3800021767f76fe6de40ab000024f269a8b793440002caa6fb98a27922afa00015460394ea219c8f14c111f1a00014ce9ad0000716800041
  | 53 => 0xdaeb7b80000001742000000027300000002c127b01d684928df42fd1192b5da2277de98622042e2413f55c2501a2dcac20094206000025ac15e4fb6951000000000000007bd8000000254a00000000000000b5fa7ae123032e61ba582aab257085f1bb871eef6e7468b0000029eb57d10a80000e062b00000a346cfa4b30708a52235eb68940da2005806a1238b0002f9862d000055ca0981bb08362dcc00061180009ca93e004b9de078d1b50751184a40281e40d4a2b629008ee4478b446bda3adb0a0ac8344000011692c204c800071e2f9400000005ed9d8245da83000000004f8c0222945b08000000001a000000000000000000a210000000290c216124881a82064299b148dd21e00000000000000069aa718511a112246c00096a80003aa8000000000028a40000001bfe00000001d00d0488315b27072a480c55d6c2e11cc20000000259aa0c2fb2b721798000c120000bb90000000000000000000000000000000027980000002ede04245e48799d16947921700003920000683000103037da8900000cd01cc1760c02903c00010280001bc20001ad000028ac00017d80002564a36684554318e80002763000000000000002f7257a0002d0eab504ca99e80e75bf91781fa9ae60001250a628358000000065ea0ea00000009db23f2b3a00005af8d8e75718ce30a80006a480005d385304bd80002dd90b200000000000000104108c5ec80003d50afa0001624c01a9f410e8270759c6840000c5662e0000ae91b5a0002358353a8f4489901212c46140000f52000013e2ae8a46a44ab9680a0ec40001a0a000141a40f800092f278c00029ff0000000713000087a0c373a6aace000000000000003f403dc97b80008a7000000029dc000000000019700000000000269f00000000000000000186c000004e000000000012db0000000000000000000000b3a15811eab127c90000156262011a2c7449c80002ad800000012dc0002f2e6620000000000068900002d8a2c279100001b18000000000000000001f8000000022490000000000136aa468422606000000008389f680000000000b5500000000000338232c77311940540f19746000079d0b0200000000001f486f2800000017660000000000264207d97db5a4a364717833200000006df93c6136917ea2a199207213ba9db6a495398fb46612f7cbb50c8676a91b490028827bba91425e854681588f2af3802c00000c60000c3c0000000bfb66ba000000058eae0c74c000032109f14bb1088278000000003ae288aac28afab630000d5e0000bb0336000000000003f66e3c2f20784914800000000003f94000000080a003000047a9656bcc300f00000000000e6cc0a1c20b330000bd283f8000194c84b800000000000002c20a6f00000000148c0e0cc68ea40000e4000007ea3
  | 54 => 0xbca56f4941991894200025c6b450dbe000265a00006cc1b1ef3c000158c4b9190200022e00799084000045c222800000000009648000aa523540c222807f4887e631852400e21a400491684e0a96e1e391ec7e9c0005b404a2360800000000007bc29ca00016f40002a7800000007c5a1d4000000041015ee00023ba000000000025f2000000000000000000000000000083e995a021a52c7eba62c4de918a000000077d80000002afe0002a890000000be312f40000540352169600000000b58f120780000626a23600a2a2a4fe2d6600029f211300005e0a20e59101e90003064b48800000023c44d2c64a2e903fc24521fd47ee6140000000a00924f1e1a94f41e0c9a00009f800015602a5a5f39b0000000000000000f700000000bf22665b282b5e7fa07bc7b599c200005f20001fbb00027ec8b38fc85b488f8bf395b6000225b00000003cfa6a23468388000060200000000001ec60d15ad659d998eb6800004f48000a269a1c0000000000265ea4a1772000000020719d21990000666800000025ce0001dca0000000000131830c99360001c1a51c91aebb702bc97e04c290c17a5877ed905f5df0c57621d08e51fc40000f667f0c11a7712bf2000141eacd00000001c3739ea61c09b8beeb21000000008b00002f8a81909646c3900c00000009a80000ba3800088901ce80d1bc098880006f380000000e40000000000000004d38000000000058313ec31f24a800010ee8238078794273637a95c6415afec70e451a5b3a7a11fb9f94afc15109b11ba995b9b18a1990b86949b58586231e6cc2966a406820a4ba6bb43b256299aaf1ebc2189c49715164dc1a66536a5ac31b0b18308945c00008327c627d443e92a914480008934000428845462a0000000100400000001db1c3456ea4b80f102e412bc0004d3400014da13c0000000000000041da402a6080006e1130e717c0003c29aa59e5d024000000015d4fda0000000000000000009900c114ae9048c5e0000e7891e171ebf4625f294a3d0b4700000002bba4db0886b35000000004d2000069200000006a412240580000a5dce2c93597a4af20000000050a0828000925c761000000000000000001c6f1858000abdd281000059a7a853a6000036f54f00003c829c5000000065b9ef2afd099200007ce00000005cf8000714a4cc00017385c7000000000007e580001e2204a9e6d3fa3ac9124291c7e2000008067cd29805c00000000d2c7cc00001b3800000000005ca0000058ac1860f0000b1627500001edc000000000000009b3800000028ee000023e7d78af800006788548000000177a02697100000000a7a07ec000305672aa270183ea3a8fd10c497523a6b5611963a522d600000009b62b85a5aa49114b3005083911c1b604f22c3000000000001b28db800015ae0002d320
  | 55 => 0x24e09b439996bc95248880aba45a7108000b0b8f6a59080000000000999008400003a06e61c0e00000001771522beaa7c03118f5e897269c2ff2936a465462b61a4b63c3af5cbb9834251b1d3800021d10000aaa9ac9236440adaa0141b70000288c3a01aa66438562bfcac246d2919c6f6a76444a000024b29647ce0c42b5a8c6035e800017d2d0c28a1c7166f40000000000353140e25f2b6c35e0aa600000008d08eba6e7e29099a4d989bf00000002dde7580000000053e9818000b9480000198000000000000012dd34f277a4a10000830800000000005db80005d906306181ea2a5168b88352ec200000000e28000000000033aaaec803000000006262a38fb2bb1800069521849202cda66005a64a79ace60f8f9e0952abdad0a574a9ca4410001f6544daec80f51360a7f2f3853797f046ea57571ca60e13509521b4a31c1deac443ff29674f6400098f13fc2200000a9d9deaba180009349fc61fc80000000000aa0e9b700010cc00018bc000150e00000005590000000000000012ba670017298b800027b22aa6548a6e00faff8b572c5a7e400007e2ed96979800000020b0ab20384379124e5c6046686280000002c0e000068ca3327fe00020b453ea44a5b08258b678000000000024880000000000b22000011c8000b0c1134189000069400003ad267c73280000001faf45e868822600006f5222dade8000674073236a95097ad96781d10db0488a6767f3241d0444780368a3846fa216a27fc2b400020fe00015bf000000000000000001452000000000000009090ca00000000a4eac42a1aaefe457000051c1fa8bd2180073121340000b825f4985ab0da6cb6c92fd2458af4055d80000002bd8b579e6c00000002df0000bf0aa9219740002f80000000000036ca8f80000000338a9ae610073c7742c1a8f2049200019b20000e8602e00007ff84de9cc8a5d68112f0380a760b56926487dadac3ead0ac9be830600004fc5d20bdb0000e484a48000341a0a85c88000a65093e0c0c000074a4ca09f89367d021f031d8fea0460b1a8dc9a8514d1262b20acb8328aba84791bcb6f1052e261a63a08300006e080002925dba0002fe20002d70ae268a60000096000123e5bd80000000000044c0009ba800000000009ee000043090f87dd8000000102c6758f1700000004a7239c0002d000001fc02f4800038100000002bb90a826d29150a9465511c400000000000000000000064cefbabfd89aa7a808e530280000f4000000004aa00000000002690000045b6488cee0002bd200000000000000133a6e753c9b7c4359e3a0000d200001412000071482e8bbd55e04ae00000000000fb67568000a4100000000a7462e8000319800000001088df000062b83e4000212217300000000b9381600006f649563cf4000beb893041f80000000
  | 56 => 0xa39a6c2956a473829c00826586d51c3ea362ea40001816b6913fe00016984ba27dc0000f3b5bc18901c550b0a312eca4902b369b30000000244c0002b2c00005ba9484000a66cab211b0bba93a80009539e1e00000cf00000000000a0a1baa038000037600000000000000c140272880133600028ae000000003b238a0000ebe000165caf700000060000075a77214ec6a099e14b2b0b009c77c17c6713d80c8b40da880f82caa698f5014e9b92436014c0939c9221d06aea552aea0569f1c11aa916316451400029563978000bc19fd40002ffa298000000025a00000ee000000006a095cfbee000057d99080001ff4000000006f4354753040406814be86b98ee7399148982800058d000000006e419fc0007f1e6366e242e08d200000002aa0a3e9bfa28d00000000000852800067eac5c00000000001f22556059200000004292ec07700000000006e17d8000000253400024343668e7000014cc0001af439813c4b2a1da648e01d788f034400022f20000000b6cc000a271f64a9329bebbc000084d8f366ad40004608000000070002f0000000000057e21d2206892e0000000000000043ca55600000000152acc0db26d92561cec755c69d085079222d05b2b4c01543640000b5418641f2cc44000174c52e01987bf80007ea4b9400024064aaa7a39028000000194e921a00004527383b5000000000007cf591c0000f33196400000016fcba7800000009dc3a71608000282200000007bf000000000002a400790000fb002bc0008e905f080e91f8559a5fe00000000001c7c215000000025c2000207b10c90a000014e800000000000000000257e00000009982f78000208a71552125f34000462000026ba1282830000000000019483fe6f8ab2846f0c8e00000000002392b99aa299b0997e000000067a80000000a4c00000000000000782800000020f4810800012080000000000b971785af1aeb42318000000177400016b200017fea52800070894227db29dfaa109f766a09742d622d2b0780009d20048a2e8778000000000004b7693147c457800073480000ef0f7a4b40b7e5501a7a000000046b286500010e6a1f03c000000008371e5c06d18d4904235015c00000000ff2000113a113800067722a02e18000358908a367861c0000000223aa7080f0000826aa8000000000000000a7d4000bd100005ef80005059a464bc9463bf02fee72e951abe4800066196b09ed9a9c000207800000008a9800000000002476be20b9859ea3780000000e8a00000000a400006b000001a1c0000000000bcbc000c090000a2180000869c40b74800066d800017b8082596adc05879962a4a4ab01dc4bb800000002820568b5a1d120000ea6054db603be93174cd40001f728429f893e72059b6a42783223d38cf09cf826826b07206ad067e8f71254
  | 57 => 0x88065de2fc0000000000000000cc0002bb29710158ac6ab58016214e72f07700001da0a6d87b2a91803c8302d4633786c87ed2b8cbf91ca66ce08ba1f6a6821e880c28a5832a29b0db60d21104aaf80b218f525aa561bf01ab154cace8000b509ae2bc5a746bf62f7a61f215479684628ff0000000000025d80004fac30eb1f63408810d920381d36106096a4835e92236acc210309400ac20ee6199080000031a03f9fb900009fe631e950b0180007fdadf23e6881e54b9f2a393994626ea662096a17846f84981bc00008e246e28c28000000051077f1d142d70cce000190c349280f5f5248e9081bd6b1dc6500001e38000000000014c23f12eda90babc025e53e67b619419432fea4cc8000000271e7f0800018a918434280007aa9a0200019710000000000000085f800024029bf0000ece3778000463000021b2466000000069c80001eaa3c630901be0000000000000093b97b8a750fa6000000008c80009e4000015ba3369c0301400000001ea12e20000000000000033580003580000468c00017100007f040000041da200000003e6c81b6c9ae806f90000a2394a60001ae02dc2996a36a0a1524ae160000a3cb4680005f099502b69ff2594145693893f4000089439d95a41ae204c19a0000754c0007ec9708517cb5a1af202aa30028043fa6d60001a1e000000000004ef0001f804448000000064800023f600024882e4202414089da9d4e52e57ca9c7808a5149f6000040500006358564b2608555e48f7c7e5521e00000001ca0000000233a3691db67f241d89ef80000cdaf0c0001788188aa2c252d85000009c89f98d00625000012c249e565800082320da867234424c4000197d5906f718ea275ac3208a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xdb276dc14144001b60edb8282880036cdd77050510006d8baee0a0a2000bb183dc1414400176305b8282880cb2d1d970505100059bc2ae0a0a2033b34855c1414400172f06b828288002e520d7050510005d3c12e0a0a2000ba4825c1414406b7650e38282880cb6ca1c70505100c5d9430e0a0a2032eb2861c14144065e650a38282880cbcc6147050510197c9418e0a0a2000bb1831c14144065f23063828288002e460c7050510197d1410e0a0a2000bb1821c14144065f43043828288002e860870505100061e3aec8a0220009768754540440012e90ea8a80880126d21d41501100255a43282a022002cb7765054044001a6eeaa0a80880cf4d1d54150110025d840282a022004cdb615ce2044009ba6c2b9c408800356d457388110006e928ae71022000d59515ce2044001b3682b9c4088003749057388110006cca0ae71022000dd1735462044001ae70ea8c40880e75c21d5188110056b93b2a31022039e72765462044073ea4e6a8c40880035c5cd51881101cfa8b9aa31022000d51735462044001ec704a8c4088003d8209518811006eb8b92a31022000dd1735062044001b670ea0c40880cb6c21d4188110056d93b2831022032eb2765062044065b66e6a0c40880cbe49cd4188110006d8b9a831022032f91735062044001b22e6a0c4088003e8e094188110007d041283102200ddb17250620440018d8ebb1240880032b1d36248110006363a8c49022000cac7418920440091ed0db8a40880025da1d5148110004ba43aa29022000d377454520440f5a68e8a8a40880e7d80815148110004db43a8290220009b4875052044001a6eeaa0a40880cf4d1d54148110197d0102829022000c7876dd520440018f0ec3aa4088002dc60475481100065c3b6e89022000cb8761d12044001763023a240880063e2197348110024f543e649022046ce876cc920440139d0ec1924088003725cc3248110005f0c08649022000f62525452044001ec2a4a8a40880035ce1d5148110005b943aa29022000b70875452044001ae10ea8a40880075c9d9514811000eb83b2a29022000f33745452044001e60e8a8a40880035cdcd5148110007b1412a29022000f61825452044073ae6e4a8a40880e7d8dc95148110007b1b12a29022000f60625452044001ec484a8a4088003d85095148110007b1992a29022000f60325452044001f4484a0a4088003e85094148110006d9c3a829022000bb28750520440017610ea0a40880036c21d414811000ed93b2829022001db0765052044001e66eaa0a4088003cc1d54148110006d9b9a829022000db1735052044001f4504a0a4088003e86094148110196d9b92829022032fa3725052044001f46c4a0a4088003e81894148110007d1292829022000fa1525052044001f4664a0a4088003e80c94148110
  | 1 => 0xee839ac488003271d073589100062fa88e6b122000c5d511cd624400193e8239ac488003275047358910006363aee4b122000cac74dc96244001998e7b92c488003351cf715891000477c3ac43122000a6c85588624400155908b10c488002b320d621891000732a8ac431220098ec825d462440131d904ba0c488027330c9731891000557426a43122000a6e85d0862440031f10cb84a4880021fe1576549100045fc22eca9220028bc845d952440011bf06bb2a4880d23720d765491000477c12eca9220018f8865c242440010ff0abb2848800e1f21576509100045fc22eca1220008df835d942440691b906bb284880023be09765091000c7c432e119220008bf845d9324400517908bb264880023be09764c9100047bc0aec99220008bf845d8324400517908bb064880263b209760c91000567432641922000acc864c832440091e90cb886488003714c9710c91000c7c432e019220019b584dd54144067a6ea9baa82880123d21975505103d69a2a2eaa0a2002cb47690d41440657650121a8288002ec60243505100165a3b484a0a2032bb2809094144001763012128288002f460c7050510005f0c10e0a0a2002cb7761d9414406766d0a3b28288002cd61476505100055bc32eaa0a2032ab4865d54144067a68eabaa8288002ece017550510195d8402eaa0a207ee3665d95414400b3690eb2a8288002e5e0d6550510005ca41acaa0a2000ba782595414400174904b2a82881f6ece01655051019d9b42ee6a0a2000b3585dcd414406556d0d39a8288002ad61a735051021e5a3b4e6a0a2032bb2809cd41440017630139a8288002ade1973505101955a432e6a0a2000ba7825cd414400174904b9a8288002ece017350510195d8402e6a0a2067cb4761cd41440657650039a8288002ec60073505103e5d8c04c6a0a20059b48758d414400166f0ab1a82880cecd2156350510005d3c12c6a0a2000ba48258d41440f776700b1a82880cfc5d4e5350510195d9404a6a0a2000bb18094d414406766d0bb928288002cd61772505101955b434e4a0a2000ab5869c94144039968ed39282880caeca027250510005d8c04e4a0a2000ab7865c941440655690cb928288002e5e0d7250510005ca41ae4a0a2000bb3805c9414406576100b9282881832d1d87250510195d9400e4a0a2000bb1801c9414401b7630131282880166d21d62505100059bc2ac4a0a2033b3485589414400172f06b128288002e520d625051009dd9c02c4a0a2032bb28094941440017630129282880caeca033250510005d8c0664a0a2032bb2808c94144001763011928288002ade1932505100055a43264a0a2000f85320c94144065765001928288002ec600325051000d5a436e0a0a2032cb476dc141440657650fb828288006eca1b705051000dd8436e0a0a2032
  | 2 => 0x875480200065dbb6e89004000cbb761d12008013dc642b0a40100031eddb51480200063dbb2a29004000e71615452008001976eda0a40100032edd9414802000758b0a82900400387e87dd5648400187e83baac9080030f50775592102c63b886eab242058c7510dd564840ab87ee83aac9081e22fe1176552100245e43ac8aa42003a3c8559154840091d904b9cc508027330c97398a1001c3f43eeab142000c3f41dd5628400187a83baac50800a2fa1f7458a100061fbaee8b142000c3c75dd1628400187ea3ba2c5080030f5477458a100061fba8e8b142000c3c751d162840074d90ab14a5080de1fe157654a100045fc22eca9420028bc845d952840091d90eb12a50800aab2116290a100043fc2aeca14200387c855d9428406d17f08bb285080123b21d6250a100246fc3ac719420048fa80dd9328400117f08bb2650800a2f211764ca100045fc22ec19420028bc845d8328400159f0c9906508002b3619320ca10105e240a6419420019f0815cd2084001b92e619241080030f5d754d91100055ac0ea9b22200087f855cf64440070f90ab9ec8880021fe1572d911001c3e42ae5b222000c9c641cd6444001958c8392c88800e1fa1f75591100043fc0eeab22200087d81dd5644400187e83baac8880030f50775591100061e3aee8b222000c5f75dcd64440018b8ebb9ac88800317d4773591100062ea8ee6b222000c9f41dcd644400193a83b9ac88800317dd473591100062e3a8e6b222000c9f741cd644400193ca839ac88800317d4473591100062ea88e6b222000c9f411cd644400193a8239ac8880032790073591100064e200e6b222000c6f75dc964440018d8ebb92c88800333dcf72591100066639ee4b222000c6f51dc964440018daa3b92c8880032bd07725911000656a0ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c9644400195ca8392c8880031bd44725911000636a88e4b222000caf411c9644400195a82392c8880032b900725911000656200e4b222000c3c549d9544400117f08bb2a8880023be09765511004c76412ecaa22000c3c541d954440071790eb22a88800e8f21564551100054e41ac8aa22000aac82591544400155d09a96c488002b960752d89100053742e85b122000e6551d8a62440070fd0fbaac4880021fe0775589100043ec0eeab122000c3f41dd5624400187a83baac48800a2fa1f74589100061fbaee8b122000c3c75dd1624400117f03ba2c4880022f60774589100061fa8ee8b122000c3d51dd1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fa8ee6b122000c5d51dcd624400193e83b9ac4880032750773589100062fba8e6b122000c5c751cd624400193
  | 3 => 0x690a4000c9f64dcd2148001938c9b9a429000317d9473485200062e328e690a4000c9f641cd2148001938c839a42900833518473485200066a39ec290a40048ec865d5214800139906baa42900df1b1db65485200073230eca90a404ec6c7619521480091d90cba242900027320d74485201b6563b6c890a404dcac76191214804d998edb9a42900123ba1a7348520404e741ce690a4020ccc761cd214800199d0c39a4290117336187348520006a7b28e690a4000d4c651cd2148001b1ec839a429000363190734852010667308e690a4020ccc611cd214808bb88c239a429011753d44734852022ea6a88e690a4045d8f411cd214808bb1a8239a429011772840734852022ee4880e690a40208ee87d8d2148001998e7b1a42900063b21d63485200066639ac690a4001ae48158d2148001b88e7b0a4290003721cf70485200061e3a6caa8240008be86dd1504800187ecbba2a0900670f19774541203fc5f43ec8a8240198bc87d9150480018decbb92a0900031bd9472541200043f436eaa024056c3c64dd540480a90fd0fb2a809015a1f21f65501200061fbaec8a024000c3c75d91404800195ec839280900031b19672cc12000656324e59824000c6c655cb3048001958c8b9660900d33318d72cc120024e6c386598240008bf845d9304800517908bb260900063d205764c1200145e420ec98240008be86dd1304800187ecbba260900030f197744c1200045f43ec898240008bc87d91304800187eebb2260900030f1d7644c12000666bb0649824037c7a76d9720480078f4ec32e40900db2e9db64c81200165d3b0c99024009de3215c72048003974eca0e4090002f220d21c812000c5e426e2b20400487c87595540800547908b2aa8100122f21d645502001d1e42ac8aa040008ef865ca53080091b90eb1aa6100023be197290c200245e43ac8a1840048dc8758d43080091d904b9cc410027330c9739882004e66196ec990400187d85dd951080011bf06bb2a2100d23720d76544200243e43acaa8840008ed86dc951080091e90eb0aa2100069d20776544200052fc1aeca884000a5c835d951080014ef02bb2a2100029b61b725442001d3b43ac2a884003a74875855108001ccee4b0aa210003991c961544201cf33902c2a884039e72205855108073cca40b0aa2100062f61376504200046fc1aeca0840348dc835d941080091790eb2282100023b61b72504200247a43ac2a084001ab481dd9410800153f06bb28210002a720d76504200055bc0aeca084000aad86dc9410800556d0eb0a821000aad21d615042000753b92c2a084000ea4725854108065d4e40b0a82100cbac881615042019752902c2a0840468ef825d93108013998e531a62100123721d634c42004e66392c6988404fcce621cd21080018f6edbaa40100031edd
  | 4 => 0x14800195e433b682900032b48676d05200065d084eda0a4000cb9109db414803f47d0db2e82900030f9db65d05200061e3b6cba0a4000a3f81d97414800147b03b2e82900022fe1d65d05200145e43acba0a4000c3e761974148001878ec32e829000a2fa1e63d05200045ec3cc7a0a401fa3e8598f414800147b0b31e82900022fe1d63d05200145e43ac7a0a4000a3f8558f414803f4790ab1e8290002ade0563d052000d5a40ac7a0a401fe2c6594b41480715590ca9682900e2aba1b32d0520006573b665a0a4000cae760cb4148001d1ac6196829000e1fa1776505200043ec2eeca0a40018be87d9141480031790eb2282900028fe1564505200f51e42ac8a0a4000cac7690941480055590ca1282900032b1d942505200f51f42eeca0a4000a3d85dd9414800117d0d3b28290002ad60676505200065ac0ceca0a4000c3f519d9414800187aa33b282900032dc4276505200051fc2aeca0a401ea3c855d9414800153f06bb28290002a720d76505200055bc0aeca0a4000cad821d9414800517f023b2829000a2f60476505200061fa88eca0a4000c3d511d9414800195e423b282900032b484765052000657100eca0a4000cac201d9414800196e203b282900032e84076505200065c880eca0a401ea3e86d95414800187cedb2a82900030f1db65505200051fc0ecaa0a4000a3d81d95414800187ee3b2a82900038ddc765505200071b886caa0a40008bf8759541480011790eb2a82900028fa1865505200061f3b0caa0a4000c3c76195414800117d0f31a82900022f61e63505200f51f42cc6a0a4000a3d8598d414800117f0eb1a82900022f21d63505200051fc2ac6a0a401ea3c8558d414800156f02b1a8290006ad205635052000557434e4a0a4000cac769c9414800174b0339282900caab2197250520006563b2e4a0a4000b8c835c9414800174f02b9282900032b1da52505200f71632ca4a0a4032aac865494148001958eca9282900caaba1b3250520006563b664a0a4000cac760c94148001d1ac6192829000637a0e76cc5200043fc2aed98a400387c855db314800117f08bb6629000a2f21176cc520006673b66598a4046ec461ccb31480070fd0bbb262900021f617764c5200145f426ec98a40008bd84dd931480131d9043b2629000237a1e634c52000637b2ee498a4000c6c65dc9314800195ec9b9262900032b193724c52000637b28e498a4000c6c651c9314800195ec839262900032b190724c52000667318e498a40809ce87cc93148001998ed992629000273a0e76c852000477436eb90a4000c6e7619721480016cb0232e42900023ba1b74c8520006573b0c990a4000ba58119321480011db0fb1e4290003339cf63c852000477c3ac790a4000ccc7358f21480035c902b1e429000317d9773485200062e32ee
  | 5 => 0x116f1205630c920005e5c02c61924000acf8758c324800199f0eb186490003a3e11630c92000746422c61924000ec78158c324804159d02b186490082b3205630c9200076240ac61924020ac48158c324800159f00b186490003b2e01630c92010476432e21924000ccd635c432480014eb03baec2900022fe1175d85200145e422ebb0a4000a75811d7614800187eebba6c2900030f1d774d85200055ac0ee9b0a400087f855d361480070f90aba6c2900030fdd474d85200061e3a8e9b0a4000ab5811d361480010ff0ab9ec29000e1f21573d85200045fc22e7b0a40028bc845cf61480010fd0fb2ac2900030f1d365585200043f438cab0a4000c3c74195614800187ecbba2c2900030f19774585200045f43ec8b0a4000c3f75d916148001878ebb22c2900022fa1c64585200061fba8c8b0a4000c3c7519161480018becbb9ac2900031719773585200064fb26e6b0a4000c9c64dcd61480018beca39ac2900031719473585200064fb20e6b0a4000c9c641cd61480019a8c239ac2900030fd0676d45200061ea0ceda8a4000c6f219db51480018da433b6a2900031e84276d45200063c884eda8a403ca3e86d93514800187cedb26a2900030f1db64d45200051ec0ec9a8a400087f8759351480070f90eb26a2900030f9d864d45200061e3b0c9a8a400387e8798f51480010fb0f31ea2900f28fa1263d45200051ec24c7a8a403ce2c6490b51480754d90ca16a2900ea9ba1b32d4520006373b665a8a4000c6e760cb514800517d09bb2a2900022f613765452000c3f43ecaa8a400187c87595514800147f08b2aa2900ee8f2116554520006363b4a4a8a4003a6c8654951480018d8eca92a2900ee8fa1376545200051ec26eca8a400087e869d951480014eb033b2a2900031d60676545200063b884eca8a4000a3f845d9514807747908bb2a29000297e0d76545200052e41aeca8a4000a77815d951480018db043b2a29000e1fe04765452001c3ec08eca8a4000c3f411d9514800187a823b2a2900031bc84765452000636908eca8a4000c6e201d951480018d8403b2a2900031dc4076545200063d080eca8a4000c79101d9514807747d0db22a2900030f9db64545200061e3b6c8a8a4000a3d81d91514800187ee3b22a2900038ddc764545200071b886c8a8a400087f8759151480010f90eb22a2900028fa1864545200061f3b0c8a8a4000c3c7619151480010fd0f31aa2900021f61e63545201dd1f424c6a8a4000a3d8498d51480014dd0d392a2900031b1da7254520005b2c0ce4a8a4039a6c865c951480018d8ecb92a290002d320d7254520005b3c0ae4a8a4000c6c769095148077c58c9212a2900e69b2194254520006363b284a8a4039a6e86cc951480018d8ed992a2900031b1d832545200061fa8ceda0a4000c3d519db4
  | 6 => 0x51ec08ca3224000c3f655c46448001878cab88c8900028fa1661191200051ec2cc23224000a3e85184644800147b0a308c890002a7a0c61191200054ec18c23224000cb5711846448001878a93b2a8900021fe1576551200045fc22ecaa24000c3c541d954480050fd0fb2aa89000a8fa13655512001c5f43ec8aa24003a3e85d91544800159b0418ec690002b660031d8d200061f3a6cb31a4000c3e74196634800187ecaba4c6900030f1957498d200061f3aec931a4000c3d75d92634800187cea324c6900030f5d46498d200043fc0aeb31a40008bf815d263480010fd0fb2ac6900030f1d36558d200063a38ecab1a400087e871956348001878e832ac6900031d1c46558d200061fb2ee8b1a4000c3c65dd1634800117d0fb22c6900030fdd76458d200061e3aec8b1a4000cb471d91634800117d0e322c6900030fdd46458d200061e3a8c8b1a4000cb47119163480018eecbb8ac6900031d1977158d200065bb26e2b1a4000cb464dc5634800187eebba2c6900022f6077458d200061fba8e8b1a4000c3c751d1634800196ee9b8ac6900032d1d37158d200065bc26e2b1a4000cb484dc5634800196ee838ac6900032d1d07158d2000673b90e2b1a40008df8758c63480015a902b18c6900022fe117694d200145e422ed29a4000a5d83d965348001c3ea7b24a69000a2fa137654d200045ec26eca9a403487e87d9553480091dd0db92a6900031bd977254d2000637b28e4a9a400087f855da43480070f90abb4869000e1fa177650d200043ec2eeca1a400087f855d943480070f90abb286900023de057650d2000c7a40aeca1a40348be87d9143480091dd0db9286900032bd907250d2001d37436cb2924000c6e76d965248001c58cbb24a4900038b194649492000536432a92924037c7870d9552480078d8edbaaa4900df1b1db65549201b6563b6c8a92404dcac76191524806fad6ea382a4900038b193659092000716320cb2124002aae86d92424800195cedb248490002ab21954909201b65c386c8a1240048ec865d542480093d100baa84900df1b1db655092000716326caa12404ec6c761954248005958edba284900db2b1db64509201b6d5ba0e0a1240048ee86dd7324806f8dcedb2e649013b1b9d865cc92002477436e999240049ea80dd3324806d95cedb2664901372b9d864cc92000727b2ec79924026ad48158e32480011bd0e31a6490026b3208634c92000727b2a641924072e4c654c83248001d1ec899064901c7a3191320c92000477436ea19240009ad84dd432480018dcec32864900023ba1b740c920004b6c2ee81924000cae7619032480091db0fb186490002f2602630c92000477c3ac61924020ae48158c324800139f0eb18649000393d95630c9200072632ac61924000e8f6458c3248001d18c8b18649
  | 7 => 0x7e878c765480010fb0f18eca900028fa1231d95200051ec2463b2a400087e870c765480010fb0e18eca900028fa1031d95200051ec2063b2a4000a6e820c765480014db0418eca900de9ea0031d95200053cc0063b2a400087d87887654800147d0910eca900028f61221d95200043f43843b2a400f87d87087654800147d0810eca900028f61021d95200052f41843b2a4000a5d83087654806f4f50010eca900028fa1370d95200051ec26e1b2a4000a5e83dc365480014bb07b86ca900021fa1f10d95200043ec3e21b2a4000a3e84c43654800147b09886ca900030f19774595200145f43ee8b2a4000c3f75dd1654800117b03ba2ca900030fd4774595200061fba8e8b2a4000a3e84984654800147b09308ca900028fa1061195200051ec20c232a4000a5e8318465480014bb06308ca900031d5c461195200061ebaea9b224000aad82d5364480010ff0ab9ec89000e1f21573d91200051f42c83b224000a3d85907644800147b03b2ec8900038b60865d91200051ec08cbb224000c3f655c76448001878cab8ec8900028fa1661d91200051ec2cc3b22400e8bd87187644800147d0a30ec8900028f61461d91200054f418c3b224000a9d83187644800196ae230ec8900030fdd675d91200061eba8ebb224000a9e831d7644800153b063aec890002aba0875d91201b556c10ebb224036aad82dcf644800147f0ab9ec8900028f21573d91200045f43ea7b2240008bd87d4f644800147f0ab96c8900028f21572d91201b45f43ea5b2240008bd87d4b644800147d0b38ec8900028f61671d91200051f428e3b224000a3d851c7644800153d0638ec890002a760c71d912000557410e3b224036aad821c7644806d5750038ec890002ae60071d91200045f43ca3b2240008bd87947644800117d0e28ec8900022f61c51d91200045f43c63b2240008bd878c7644800147d0b18ec8900028f61631d91200045f43863b2240008bd870c7644800147d0a18ec8900028f61431d91200055741063b224000aad820c7644806d5750018ec890002ae60031d91200045ec3c43b224000a3e85887644800147b0b10ec8900022fa1c21d91200745ec3843b224000a3e85087644800147b0a10ec890002a7a0c21d91200054ec1843b224036aba80087644800147d0bb86c8900028f61770d91200054f41ee1b224000a9d83dc3644800117d0f886c8900022f61f10d91200051f42e21b224000a3d85c436448001878c9baac8900021fa1f65591200043f438cab22400387e87dd564480010fb03baac8900030fd0775591200061fbaee8b224000c3c75dd1644800187cedb28c8900038b5cb65191200051ec0eca32240008bd87994644800147d0b328c8900022fe1d65191200051f430ca3224000c3e761946448001c5b04328c8900038b5c865191200
  | 8 => 0xe10ac71000297a142158e200052ec2842b1c4000a9e84085638800153b0810ac710012b6a002158e200056cc0042b1c4034cce639ca53880691df0cb94a7100d33398d7294e200246e43ac6a9c4034cce639ca43880691df0cb9487100d33398d7290e200246e43ac6a1c4000e4f5258e52880699b4c6b8665100033658f704ca201ce2eb8cc7a8c403ae4f2098f5188075c9a4131ea3100eb9684163d462000c3ec2eeca8c400487c87595518800199cc7b92a3100033398c72546200247a43ac2a8c4001a7481dd951880014ef02bb2a3100eb17dc663546200072bb8cc6a8c4039e4f2098d5188073c9a4131aa3100e795c4263546201cf2a884c6a8c4000e577158d5188073cae20b1aa3100e79684163546201cf2a882c6a8c4000e4e63dc95188001c9cc6392a31000e9da1d615462001d3a43ac2a8c4000e67725855188001cc8e4b0aa3100e799c8161546201cf32902c2a8c4032c9d7198f4188001c3ea331e83100038754663d06201c747904c7a0c4038e8d2098f4188001c3ea2b1e83100038754563d06201c74d082c7a0c40018bd84dd941880091790eb2283100033398f725062000667318e4a0c40048f487585418800356903bb28310002ade0576506201c64fb8cc6a0c4000e977198d4188001c3ea331a831000387546635062019747904c6a0c4032e8d2098d4188065d2e2131a83100cba544263506200074bb8ac6a0c4000e1f5158d4188001c3aa2b1a83100cba5c4163506201974d082c6a0c4032e951058d4188001d1cc7b928310003a398c72506200155b43ac2a0c4002ab4875854188001d4ee4b0a8310003a91c9615062019753902c2a0c4032ea52058541880091b90eb1a63100033398f724c62000667318e498c4000ccd631c931880011bb0db9a43100023761873486201346f43cc690c40348dc8798d218804d1bd0eb1a43100823721d63486200061eba4a9b2a4000a6d82953654800117f08b9eca9000a2f21173d95200051f424a3b2a4000a3d8494765480014db0528eca900028fa1261d95200051ec24c3b2a400f87d87187654800147d0830eca900028f61061d95200052f418c3b2a4000a5d8318765480018eae230eca900030fdd274d95200061eba0e9b2a4000a5e831d365480014bb063a6ca900029ba0874d95201bd36c10e9b2a4037a6d82dcf654800147f08b9eca900028f21173d95200062eb98e7b2a400087e87d0f65480010fb0fa1eca900028fe1172d95200051e422e5b2a403787e87d0b65480010fb0fa16ca900028fa1271d95200051ec24e3b2a4000a3e841c7654800147b0838eca9000297a0c71d95200052ec18e3b2a4000a6e821c7654806f4db0438eca900de9ea0071d95200053cc00e3b2a400087e8790765480010fb0f20eca900021fa1c41d95200043ec3883b2a40008
  | 9 => 0x63c872004e6639ac790e40009cc835d521c800139906ba2439020733dd8734872000666c30e690e4020cce611cd21c8041998c239a439013f53d44734872027ea6a88e690e404fd8f411cd21c809fb1a8239a439000372a007348720006e4c00e690e4000ccc7358d21c8001878e8b2aa1900030f1d5645032002566c30659864004bca800cb30c80090f90eb2aa91000a8f21165552200245e43ac8aa44003a3c8559154880091b906bacc7100123720d7498e200054f426a731c4000a9d84d4e63880014bd0ba1cc710002976174398e200052f42c6331c4000a5d858c6638800153d0918cc710002a76123198e201a62fbaceb31c4000a9e849d6638800153b093acc71000297a167498e200052ec2ce931c4000e1f549526388001c3aa82a4c710002a7a135298e200054ec26a531c4000a5e85d0a63880014bb0ba14c71000297a167198e200052ec2ce331c4000a9e849c6638800153b0938cc710002b3e097198e200054f424a331c4000a9d84946638800153d0828cc710002a76105198e200052f42c8331c4000a5d8590663880014bd0a20cc710002976144198e200052f42c4331c4000a5d85886638800153d0910cc710002a76122198e201a46f4384331c40008dd8708663880014bd0a10cc710002976142198e200054f4204331c4000a9d8408663880095b50010cc710002b66002198e200062fbaea6b1c4000a9e84d4d638800153b09a9ac71000297a174358e200052ec2e86b1c4000a5e858c563880014bb0b18ac710002a7a123158e200054ec2462b1c4004ada808c563880014bd0a18ac710002976143158e200054f42062b1c4000a9d840c5638800159b0418ac710012b6a003158e200062fbaceab1c4000a9e849d5638800153b093aac71000297a167458e200052ec2ce8b1c4000e1f549516388001c3aa82a2c71000297e157258e200052e42ae4b1c4000a9f845c9638800153908b92c710002b5e057258e200056a40ae4b1c4000a9e84d49638800153b09a92c71000297a174258e200052ec2e84b1c4000a5e859c563880014bb0b38ac710002a7a127158e200054ec24e2b1c4004ada809c563880015b30138ac710002b3e097158e200052f428e2b1c4000a5d851c5638800153d0838ac710002a76107158e2000567410e2b1c4000acd821c563880095b50038ac710002b66007158e200054f424a2b1c4000a9d8494563880095b50128ac710002b66025158e200054f420a2b1c4000a9d8414563880095b50028ac710002b66005158e200052f42c82b1c4000a5d8590563880095b50120ac710002b66024158e200052f42882b1c4000a5d8510563880095b50020ac710002b66004158e200052f42c42b1c4000a5d85885638800153d0910ac710002a76122158e200256d40442b1c4000ad98088563880011bb
  | 10 => 0xb2e4000c5e509cf65c80018b8a139ecb9000317d4573d972004c3f43ca8b2e4000c3f7495165c800517d09b9acb900022f61373597200043fc0aebb264000c3f415d764c800193ca939ec99000327d0673d93200064f204e7b264000c9c409cf64c800193e82b9ec9900262fa1f54593200061fbaea8b264009aae82d5164c80070fd0bb9ac9900021f61773593200061e2a6ecaa640048ee82dd954c8001878a8bb2a99000a1fa1f65553200151f426caaa64000a5e83d9554c800717d0fb22a99000e8fa1764553200054f41ec8aa640098dc835d663c80131b906ba4c790002a7a135398f200052f42e8731e4000c5f75d4d63c800153d09a9ac790026b3a0b5358f200052f42e86b1e4009ace82d0d63c80091d904bb4a79000297e0d6594f2002476412ed21e4000a6f8655252c808d1df0cb8e6590026b3e1d630cb2000667c3ac61964020ace8158c32c804159902b1865900033358d710cb200145f426eab0e40008bd84dd561c80070fd0bba2c3900021f617745872001c3f42ee6b0e400087d85dcd61c800517d09b9ac3900022f613735872001c3f43ec9a8e400087d87d9351c80014bd07b26a3900029760f64d47201d536c3485a8e4000e4d630cb51c800517d09bb2a3900022f613765472002477416eca8e400187e87d9551c807747d09b2aa3900028f61365547200052f41ecaa8e4000a5d83d9551c80030f90eb2aa39000e9b61a525472000637bb4a4a8e403ba3e84dd951c800147b09bb2a3900ee8fa1276547200051ec24eca8e4000a5e839d951c80014bb073b2a3900029d60676547200053bc0aeca8e400087e87d9151c80010fb0fb22a39000297a0f64547200052ec1ec8a8e4000a778158d51c80034e902b1aa3900e69b61a725472000637bb4e4a8e4000b65819c951c800169906b92a390002d9e0572547201cd36c3484a8e4000e4d630c951c800517d0fb2e83900022f61f65d07200054f41ecba0e4000a9d83d9741c807155b0d296839007f8b99652d072000746b1865a0e400387e85dd941c80010fb0bbb283900123ba0b765072000c5f43ec8a0e401ea3e85d9141c800147b0bb228390002a7a0f64507200054ec1ec8a0e40018bc8759141c800555b0d21283900032bdda42507200f51f42eeca0e4000a3d85dd941c803d47d0b3b283900028f61676507200054f41ceca0e4000a9d839d941c800156b033b28390002ade0576507200045f43ecaa0e40008bd87d9541c800153d07b2a8390002a760f65507200055bc0ac6a0e4001ab48158d41c806555b0d39283900032bdda7250720005d2c0ce4a0e4000b8c835c941c800174f02b9283900caab61a52507200f71732ca4a0e4000e8d630c941c80091d904bb66390027331ca634c72000c6e43ac698e4009ccc7258d31c810539d0f992639011a3be1d
  | 11 => 0x5000159b0610ec4a0002ba60021d89400062fb2ce73128000c5c659ce62500018becab9cc4a000317195739894004e66312e73128000ccd73d8a62500010fd0fb2ac4a00021fa1c655894000477c3ac43128003c3c7555062500011bf06b88c4a00d23720d711894000556c24423128003a3c86552525000187cecaa4a4a00021fe1576cc94001c3e42aed992800087f855da32500070f90abb464a000e1fa17764c9400043ec2eec9928009ace82d8d325006959d07b1264a00021fe15760c94001c3e42aec1928000c3c655d0325000199cec99064a0027331d9320c94000727b2a641928072e4c654c832500a9878e832ec2a00029d60775d854000c5e422ebb0a8000c3f741d7615003f878e83aec2a00029d60475d85401c45e43aa9b0a8003c3c7555361500010ff0ab9ec2a000e1f21573d854000c5e422e7b0a800087f855cb61500070f90ab96c2a00062f21172d85402c43e436eab0a800087e87d9561500010fd0e32ac2a000317d9773585400062e32ee6b0a8000c5f651cd61500018b8ca39ac2a00031bd9772585400063632ee4b0a8000c6f651c961500018d8ca392c2a00030fd0676d45400061ea0ceda8a800387c851d9515000187ca83b2a2a00061fa1f655454001d1e432a8a8a8000c3c7655151500010fd0d3b2a2a00029d60676545400063ac0ceca8a8000c3f419d951500018ee213b2a2a000297e0d76545400052e41aeca8a8000a6f825d951500014d904bb2a2a00030fa1076545400061ec20eca8a800387f811d951500070fb023b2a2a00030fd0476545400061ea08eca8a8000c3e401d95150001878803b2a2a00031dc4076545401cd1e432e8a8a8000c3c765d1515000166f02ba2a2a01562fa1b75505400f61e32eeaa0a80048bc865d5415003d878cabaa82a01528fa1b65505402c61e3b6caa0a8000e3461d95415000147f03b2a82a00028f60765505402b61fb8ecaa0a8056e3771d954150001c6e21b2a82a00062f21d65505400055bc0acaa0a8056a3e8619541500ab87cec32a82a01570f1d865505400071bb2ec2a0a8000e3465d8541500035690fb0a82a00038de1761505400071a42ec2a0a8002ab580d854150001d66c3b8282a0003acd8470505400043fc2aed98a800387c855db31500070fd0bbb262a00021f617764c54004c77414ec98a80008ed829d931500018decbb9262a00031b197724c54000637b28e498a8000c6c651c931500010ff0abb642a000e1f21576c854001c3f42eec90a800087d85dd921500691bd073b242a00023760e76485400062fb2ee690a8000c5c65dcd21500018beca39a42a00031719473485400061fb2ee8a828019c3c65dd150500094790caa2a0a000b0f1d954541400259c402a8a8280008bf815d365c800187ea2ba6cb9000317d5273d97200062fa8ce7
  | 12 => 0x28f21574586400054e41ae8b0c8000aac825d1619007156f02ba2c320002ad60754586400043fc3ac7a8c800387c8758f51900010ff0eb16a32000e1f21d62d464000c3ec2eeca8c8000c3f545d951900011bf06bb2a3200d23720d765464000477c12eca8c80098ec825d951900090f90eb2aa3200030f59774546400247a43ac2a8c8000e37545855190107c68a8b0aa3200069d20776546400052fc1aeca8c8000a5c835d951900014df04bb2a3200029b20976546400053bc0aeca8c8000c3d76dd151900010ff0eb1aa3200021f21d63546400043fc3ac4a8c800087c8758951900074ed0eb0aa32000e9d21d61546400c71b422c2a8c8000e35845855190001c6ee8b0aa32020f8d1d161546400071b21ac2a8c8083e34435855190001c6c84b0aa32020f8d10961546401cf1ba02c2a8c8039e3540585519003387ceab2a83200028fe1563506400f51e42ac6a0c8000a3f85589419003d4790ab1283200cbac1c1615064000758b0ee0a0c800087f855db31900070f90abb663200021fe15764c64001c3e42aec98c80008ef825d931900131d904bb263200123721d634c64000667318e498c8000ccd631c931900010ff0abb6432000e1f21576c86400043fc2aec90c800387c855d921900011bf06bb243200d23720d76486400066639cc490c80048ec875892190001998e6b12432000a2f21173d95400145e422e5b2a8000a3d84947655002f0fb0e30ecaa00031d5c461d95400051fc22e7b2a8056a3c845cf65500018bae639ecaa00028fe1172d95402b51e422e5b2a8056a3e849c7655000147b0938ecaa00030fd0571d95402b51f420e3b2a8058a3d841c765500010fd0f18ecaa00021f61e31d95402b51f42463b2a8000a3d848c765500010fd0e18ecaa00021f61c31d95402b51f42063b2a8000a3d840c765500014dd0418ecaa00029b60831d95402c53d40063b2a8000a79800c765500010fd0f10ecaa00021f61e21d95402b51f42443b2a8000a3d8488765500010fd0e10ecaa00021f61c21d95402b51f42043b2a8000a3d8408765500014bd0610ecaa00029760c21d95402c53d40043b2a8000a798008765500ad0fd0f886caa00021f61f10d95402b51f42621b2a8000a3d84c43655003387ec8b88caa00034dd0571195400051ec24c232a8000c7571184655000747d0db2aa8a01630f1db65551400fe1e32ee2aa28058d3b751c1545000153b0818ec6a0002b360831d8d400056cc0063b1a8000c6f659ca63500018d8cb394c6a00031bd957298d400063632ae531a8000ccf635ca6350069998c6b94c6a00021fa1f6558d400043f438cab1a80008df8758c6350007878eaaa0c6a00023be097118d4004c76412e231a8000a9d848c463500014bb07b2ca6a000e8f2195494d400061f3b2a929a8000aad8408762
  | 13 => 0x52ec2e8631a420087f855c063484070f90ab80c6908022fe117018d210145e422e031a42008dd87994634840153d09328c690802a76126518d2145566c14ca31a42008df87594634851359f04b28c6908023761e6418d210052f42cc831a4200a5d85990634851159b05320c69080237e1d6418d2143d67c12c831a4234c5f759d4634840153d093a8c690802a76127518d210052f42ce831a4200a5d859d06348401c3ea92a0c690803875505418d210054f426a431a4200a9d84d4863484415ad03a90c690802b56075218d210052f42e8431a4200a5d85d0863484415ad03a10c690802b56074218d2122d66c14e031a4200a5f855c063484014b90ab80c690802a7e117018d210054e422e031a42348de8714063484011bb0e280c690802a7a105018d210054ec20a031a4200ace82140634840159b04280c690882b5a045018d210056ac08a031a42348de8710063484011bb0e200c69080297a144018d210052ec288031a4200ace82100634840159b04200c690882b5a044018d210056ac088031a42348dc835da5348469998c7394a6908063b2197294d211a66631ae529a42038de87d8d53484691b906bb486908d33318e7290d2100c76432e521a4234ccc635ca43484011bf06bb286908023be097650d210146f43ec6a1a420187f875965248401c9ea5b1ca4908062fe1d64909211a56641ced1924220cce7618e324844199ce231c6490883331c4638c92143727a88c71924286e4d5118e324850dd1e8231c6490a1ba3504638c9210066631ae11924226cd471d8d32484e159d0db9a649089b331db734c921136e238ee69924234ace86d8d324844d998edb1a64908d3331d8634c92100567438c69924234cce8718d324841359f0231a64909c2b3604634c92110667388c69924220ccc7118d324850bc9ea231a6490a1793544634c92142f47a08c69924285e8d4118d3248401998c7b826490882b3a19320c9211a566432641924245ccd7218e60484011bd0fb1ac09080317dd763581210062e3aec6b024200c9f74d8d6048401938e9b1ac09080237a1c63581210062fba8c6b024200c5c7518d604840193ee831ac090803271d0635812142667b90c6b0242008fb87580604840187ea9b8acb200d3330c97298e4001c3f43eeab1c8000c3c43dd563900010fb03baac7200030fd077558e4001d2e42ac729c80048dc8758d53900a317f0eb1c87200028fe156390e4004e66192e7314800387e87dd5629000187885baac5200021f6077558a400061fa0eeab148003a6c8558a52900091d90eb12a5201362fe1d6290a400051fc2ac5214800087f855d932900070f90abb265200023de05764ca4000c7a40aec994800087f855d832900070f90abb065200664fa17740ca4000567c32641948000acd864c83290001878a9baac320
  | 14 => 0xd75194605051996ae2328c0a08e327d867318141006cbb0ce63028200d1f519cc6050401a3aa3398c0a08cb65c427318141196ca884e63028238c9f615cc6050401b2ec2b98c0a080347d4573181410068ea8ae63028232d97105cc6050465b3420b98c0a08cb654417318141006cc882e63028200c3d7598c605040193ae7318c0a08030f5d463181411c657b0ce43028200da7619c86050401a5ea3390c0a08034b5467218141196d3884e43028232da5109c8605047195ec2b90c0a080369d85721814100697a8ae43028200d2d515c86050465b4e20b90c0a08cb6a8417218141196d2882e43028200da9105c8605040187aeb310c0a08032b5ca62181410061eba8c430282009bb8758060504050fd0fb2aa99080a8fa13655532101c5f43ec8aa64203a3e85d9154c840117f08b80c79080a2f2117018f2100567438c69964209cce8718d32c8413d8b0231a6590883339c4634cb2110666388c69964285e8f4118d32c850bd1a8231a65908033318f704cb2101c3f43eeab064200c3f41dd560c840187a83baac1908029d60475583210145f43ee8b064200c3f75dd160c8401878ebba2c1908030fd4774583210061ea8ee8b064200c3f751d160c8401878ea3a2c190802ad60474583210062fa8ee6b2a4200c5d51dcd654840193e83b9aca908032750773595210062fa88e6b2a4200c5d511cd654840193e8239aca908032750473595210066639ee4b2a4200c5f51dcd64484018baa3b9ac89080327d0773591210064ea0ee6b224200c5f511cd64484018baa239ac89080327d0473591210064ea08e6b224200ccc73dc964484691bd07bb2a8908023760f76551210046fc1aecaa242348dc835d954484011f700bb2a8908123e20176551210143f43ecaaa24202a3e84d95544840717d0fb22a89080e8fa1764551210062ebaea7b1a4200a9e84d4f634840153b09a9ec69080297a1743d8d210052ec2e87b1a4200a9e84997634840153b0932ec69080297a1664d8d210052ec2cc9b1a4200c5d751d7634840153d083aec690802a761075d8d210052f428e9b1a4200a5d851d36348401c3ea92a6c6908038755054d8d210054f426a5b1a4200a9d84d4b63484014bd0ba16c6908029761742d8d210052f42ee1b1a4200a5d85dc3634840153d09b86c690802a761370d8d2113566c10e1b1a42008de8714363484011bb0e286c690802a7a1050d8d210054ec20a1b1a4200ace82143634840159b04286c69089ab5a0450d8d210056ac08a1b1a42008de8710363484011bb0e206c69080297a1440d8d210052ec2881b1a4200ace82103634840159b04206c69089ab5a0440d8d210056ac0881b1a42008df8758c634851759f04b18c6908d23720d7518d211a46e41ae831a4200a9e84d4c634840153b09a98c69080297a174318d2100
  | 15 => 0xa3b664a08026d607768c941004dbc0aed192821e93e851da325040127b0a3b464a08026d607764c9410f49f42cec992820093d859d9325040136f02bb264a08026de05754c94100cda40aea9928246da471cc9325044db28e319264a08066da1f714c941014db436e299282029b486dc5325040136b01b8a64a08066d207704c9410f49f42eec192820093d85dd8325040136b03bb064a087a4fa16760c9410049ec2cec19282009b7815d8325040117d0dba864a08022f61b750c9410064ebb0c61928200b8d8218c325040195aec31064a0802e360c620c94142dc6c1c64192820099f874c832504417290299064a08026be1d320c941105d240a641928200b8f874c83250401b1f0e99064a0802e3a19320c941005c6432641928200f87814c8325044171d0299064a0882e3205320c941387c240a641928220b84814c832504e1b1ae299064a09c3a3d85320c94138fc3b0a641928270f0f514c832504e1e1aa299064a0802e3e01320c941387c38826419282008bf865c032504011790cb8064a08024fe15700c9410f49e42ae0192823c9b7815d7605046517b0fb2ec0a087b0f9d765d81410f61e3aacbb0282419b5819cf605040135f04b9ec0a08026b20973d814121cdbc0ae7b02821a9b5819cb605040133f06b96c0a08026720d72d81410e4dbc0ae5b028200c3d75996605040153d0732cc0a0802aba0a65981410055cc04cb3028200c3f75196605040127f0ab9cc0a087a4f21573981410049fc2ae5302821e93c855ca605043d27d0fbaac0a08034dd8775581410069b886eab028200c3f761d5605040117d0fb2ac0a087b0f1d765581411945e43acab02821ec3c755956050401a3eebb9ac0a0803471d77358141006cbb0ee6b028200d1f51dcd6050401a3aa3b9ac0a080365c4373581410068fba8e6b028200d1c751cd605040193eca39ac0a0803275947358141006cbb08e6b028200d1f511cd6050401a3aa239ac0a08032798073581410064e300e6b028200d97101cd6050401a5eebb92c0a08034b1d77258141006c7b9ee4b028200d8c73dc96050401b4ec3b92c0a08034bd47725814100696a8ee4b028200da710dc96050401a5eea392c0a08034b1d47258141006c7b98e4b028200d8c731c9605040195eca392c0a08032b5947258141006d3b08e4b028200d2f511c96050401a5aa2392c0a08032b980725814100656300e4b028200da7101c96050401a6eebb8ac0a08034d1d77158141006cbb9ee2b028200d9473dc56050401b4ee5b8ac0a0803691cb71581411e49fc0aea302823b93d815d4605047187ec2ba8c0a08034dd8575181411961fb02ea3028232c3d605d46050465a6e20ba8c0a08cb4d44175181410045ec3cca3028200c3d75994605040153d07328c0a0802aba0a65181411e65ab8cca3028200c3
  | 16 => 0x20c94100566432641928220bc4814c832504ff17f0eaa6c0a080f0f1d554d814100477c12e7b0282098ec825cf60504011bf06b96c0a08d23720d72d81410047dc3ac0302821ea3e86d95655043d87eedb2acaa0a378d19771595411e69bc2ee2b2a8231d3485dc56550401a6ecbb8acaa0a374d197715954146e9a29ee2b2a828dd3452dc5655040136b01b8acaa0a374dd4371595410f49fc3aebb1a823c93f815d7635047727b02baec6a08030fd8575d8d410069bb0aebb1a8200d37105d7635043d17f0eb2cc6a087b0f9d56598d410051ec2ec731a8200d97635c6635040136f00b8cc6a080369d877258d4100697a8ee4b1a8200d2d51dc96350401b4e21b92c6a080363d8c7258d41006d3b08e4b1a8200d2f511c96350401a5aa2392c6a080369c407258d41006d3b96e2b1a8200da472dc56350401b2ec7b8ac6a08026d6037158d410f45ec3eca31a821ec3e75d94635043d878eab28c6a08028f6176318d41005cac0cc631a82008bf8758c635040133f0eb18c6a0802e32096318d41005cbc0ac631a821c9b7815c8635040127f0ab80c6a087a4f2157018d41004dac0eed29a82009af825da535040135904bb4a6a08026de057694d41004d7410ed29a82009ad821da535040187cecb2ca6a0802c7e0d6594d410059bc0acb29a821eb1e85d8e535043d33b0e31ca6a087ac7a146394d410070eb28c729a8200d3a505c2535040136b03bb2a6a08024f6167654d41004d7c12eca9a82009ac825d9535040136f02bb2a6a08026ee017654d41194dc402eca9a821e99e87d8d535043da3ee729aa6a087a4fe1d75d89411e49fc0aebb12823b93d815d7625040187ec2baec4a08034dd8575d89410069b882ebb12821e8bf87596625043d87ceab2cc4a08028f6176298941006d3b12e331282009b7805c66250401b2ec3b9ac4a080347d4773589410068ea8ee6b128200d9710dcd6250401b2ec239ac4a080347d4473589410068ea88e6b128200d97101cd6250401b18e7b12c4a080365dcf7158941006ca39ee2b128200da762dc5625040136b01b8ac4a087a2f61f65189410f61f3aeca312821ec3c75594625048736f02b98c4a08028f6176218941005d2c0cc431282008bf87588625040135f0eb10c4a0802e320d6218941005d3c0ac4312820093f855c0625043d2790ab80c4a08026d6077694941004cfc1aed292820099c835da525040136f02bb4a4a080267a0c7694941004cec18ed2928200c3e76596525040166f02b2ca4a087acba1762949410f4d6c38c5292821eb2e8518a5250401c5aca314a4a08026d60776549410049ec2ceca92820099f835d9525040133906bb2a4a08026de057654941004ddc02eca9282329b8805d9525043d35d0fb12a4a08026d60776cc941004dbc0aed992821e93e851db325040127b0
  | 17 => 0x9064209ce87dc5320c80159f0cb8a641908273a07704c832104e640ee09906400acd869c1320c80159f0cb826419002e3e11704c83238dc6422e09906400bc7815c1320c8e178902b8264190827321d3258432105e240a64b08640387e85dd1610c8010fb0bba2c2190823ba1e32584321057340c64b086434ec4318c9610c8411d90e992c219082b920532584321a76398a64b086400ccf874c9610c8415990e992c2191c33321d32584321046643a64b086400ec7814c9610c84159d02992c219082b320532584323876240a64b086420ac4814c9610c80159f00992c2191c3b1c413258432004e7c3a653006400bcb804ca600c80139f0e992c01900363dd1325803238ec63a264b006400bcb804c9600c80187eebba2c0190022f60774580320061fba8e8b006400c3c751d1600c801a74a0b84a7a087f47dce5354f410145f436ea19682008bd86dd432d040133f0e99065a08026be1d320cb41005c7c3a641968200d8f874c832d052371f0c99065a0a46e3619320cb41105c740a641968220b8c814c832d04e1b1ae299065a09c3c3d45320cb41005c7c026419682008bf865c032d04051790cb8065a08024fe15700cb410fc9e42ae0196823ba3e85dd1655052187eebba2caa0a3f8d153715954101d1f436caaa2823cd3775dc5545040187ae93aec6a080e1fe1d75d8d410061eba2ebb1a8200c3c435d763504790ff02baec6a080237e1d6318d4100566412c631a8203c3c75550635046999864b90c6a08021fe157018d4101c3e42ae031a82348dc835da53504011df04bb4a6a08263b2097694d4100c5e432e929a820293f87552535040187cecaa4a6a0802c7e0d5494d414770e31aa929a8203a5e85d8e535040317d0dba2a6a080e37a1f6354d4100c5f436eb21a82418bd87d8e435040147b0bb1c86a08062f2197550d410061eba4ebb12820387f875d7625040187ae8baec4a08030f10975d89411e43fc0aebb1282008ef87588625040159906b10c4a080f0f1d5541894104e66192e6312820087f855c062504070f90ab80c4a080237e0d76949411a46e41aed29282098ec825da525047787ce8b2ca4a08062f21974949410149fc3aa92928200c3e7655252504edc58c4aa4a4a080e9ba1762949410043ec2ceca9282018be86dd152504071dd0fb12a4a08062fa1b75909410045fc3acb212821ec3e75596425043517b0fb1484a08028f617629094100c5e432eaa1282018be86dd332504031790cba664a08062fa1b748c94100c5e432e9192820387e859d932504010fb0b3b264a08062fa1b744c94100c5e432e899282019b4815d132504051ed0db8a64a080e1fa16760c9410043ec2cec19282018be86dd0325043d27d0bba064a08024f617740c94100c5e432e81928234c9c635d03250413958c4ba064a0802b3a193
  | 18 => 0x4002000000000c00c00100000000080010000000002000000000c00000000380040040000000004000000000000000a0040008000002000001800000200400000000000030010000000000000800000000200000080000020000000000000000800000a00000000000000010000004006000002000400000200200000040010000000000000000000000400000000080020000030004000001001000001c006002000c008006000000400000200000080000000000010000002000801000c0050000000006008ef875886255001a58a9390c0aa0034b15172181543c65bb22e2302a800d34545c460550011f70eb00c0aa1e2aee1160181540151fc32c8aa4a42a87d86dc9549480727b09b92a9290f30f99371552520161e3a2a931ca4008bf845c2639480517908b84c7290030f5d95490e523b697392a921ca402c3e74551619480517d09b82c3290022f61370586522a43e43aa8b04a402c3e7455160948014bb0b18ec6a90029761431d8d5200566c1063b1aa400ad9800c763548011bf0eb18c6a9002976163118d520045fc22e031aa4028bc845c063548691d90cb9486a90029d60652d85520045fc22e1b0aa4028bc845c361548011f70eb00c0a900e8fe1965552421745ec36e4aa4840293d85dc954908eda5ca5b92a92107f0f997715524201e1e3aaa931c840087f855c263908070f90ab84c7210030f5d95494e423b697392a929c8403c3e7555161908070fd0bb82c3210021f61770586423fc5e43aa8b048403c3e75551609080153b0818ec6a1002b360831d8d420056cc0063b1a84008df8758c635080153b09188c6a10021fe157018d4201c3e42ae031a84348ec865ca53508050ff0eb2ca4a10030fd97745494201c5fc3acb2128400ab58190b61508010ff0ab86c2a100e1f21570d854200c5e422e1b0a84008fb8758060508130f90eb2aa91900a8f211655523204c5e43ac8aa46403a3c85591548c80159b0d992a51909a37a1f32586321356b40e64b0c640387e85dc1618c8010fb0bb82c31900a2fa1370586320045ec26e0b0c64018f681dd9544c8011eb03bb2a89900e2fa1f645513201d1f42ec8aa26400c5f65dcd524c84d1b90cb8c649909b35185718c93204ee390ae319264008bf845c3614c80517908b86c2990023ee1d60181320043fc0aebb206400c3f415d7640c8698be60baec8190271bc8175d903204c5f43ea8b206400c3f75d51640c801878a9bb2a8190030f151765503201c5f43ec8aa06403a3e85d91540c86999ca7bb2641900333dd9534c83200666c36ec9906409ccf65dd9320c80199acbbb2641908273a07764c832104e640eec99064009cd80dd9320c81399d0fbb2641900333dd7764c83200666baeec9906400acd81dd9320c80159f0cba26419027a3191644c83238f862a2a89
  | 19 => 0x2003001800000200100080000060030038000002001002000c004000003000400200000100000060030010000000000001000c002000000000000a000001000400000000100080080000008000000001001800400000000100080040000000000004000000000000000000080000040000018008000000000000000000000080100000010000008010000000801c000000001000000000100000000000000000000004003000000000000700000000000010000004002000000000400000000300040020030000000002003000000000000300000000000020008000000000000000000200100180000000000010000000000003000000800300200000020000000000000003000000400000000100000000000000004000000000800c0000030000008012000000002c000000000000000000200000040000000020000004002000000000000000180040000010028004008004000000400000000080000000040008000000003000000400c0000020020000001000000400000000000000000000018004000000000000800600000300000000010000000002001003001800400400100040000010010000000000000000c0000000000000002006000800000000000180040000050000004000000000000000600100000000000000000000000000000000000200000000000100010008000000002000000000400000080000000000000004002004000000000000300000040040020000010006000000800000200600000040000010000000008000001800c008000000000000200a000000000400100000180020000000000000004001800000400100200000040000018000000000000001800000000200000000000000000000000001000000000e00000040040000038004000000001000c004005001800000a000001800400400000080040000000000014000003000800000800000000200000010048004004002000800800800200080000020010008008000000000000000000000080100000000008000000002000000000e0000008000006000000000000a001000000000000000200100080000000000002003000800c000001003000000200000080040080000000008002000001000000200000000000000030000004000002000000000000000180000020000008004002001000003c00400000080000020000008010004001001001000000000000080020000008004010001000802401200500100080000020000008000001000800000000500080000000000010004000002000800400c0030010004000000001801400e0010010000008000000000c0020000008000006000000000c004001000001c004000000800400000300100000020010020000000001000000000000000100000040000000000000000003000000e000
  | 20 => 0x11202e480000000000000000000000249000085c0000000000fa600000001fc00002e000000000093a4ee00000000000000001322000000103d3250000001a140001cd878854cfe60001159d0c6c40001c195288b000029594b8000393800282400071a000000000000002298ec0000002d1006eb680000000b5483a0000000000e9c2e90631e900000000000000000000000000000041b00000aa000000000000000080b000000000000000010e89b300000020acd5241110c800023035c3c2800000000000007e000022a05f21940000000400a8a6c08b10dca3482740000000000000000000000000076d0001aa80000000000e70000032078000000059a0e646140009e200000000009cf000000022e000000000000000000000000005e015580000007730001d14000000083000127e00000000000000000000000000359000000000000000000000000000000ce0d3819219414c42f891d975804800063133114a80006bf4a40000ed800000000000007244eb0ef073600000019a0000000414000000000000001d400028100000000002181f7000000000001f0d3cafc9d40205998a7e1ea44989647b459600000002c261640826fcbf00000000000e1a7543ce51b00000001b81448000000000000060892626905e4f0200023100000000004e980000000000000fd00008af0000d00e02000000000000002f0000000000975000247c0002e10000000dfe3cc3441c9521e00004280011b89f38001b1c8643ec00000000000003fe9af8ba229620b878a78014f24358850c200025297b526ea174fd85a1158684000223f1ec54f00000000000000000000000000000000000000000000000007c325b8000bfc0e900000000347a600000000008ee0ae0000ca00000000000d6c00000000013622dd4a5017000000000000000000004525ce00000003b004c000000000021b000000024500000002b12758000000000000c002000000001000400100000040040000020020000001000800000400600000100000010008000000002000000000200000100240000040000008000000000000400400000080080040000000004000000000000800200300000040020010008000000003000000800200000080180000060000014000000001800c0000020008004002001000001c0040000000000004000002800000e00400000040000010000000008004000800800e004000800c00400000000040000020000004000002001000c000003002001000000900100000000010000000002001000800000000a0008000006000000001400200100100100020000000004000002007000c000000000800000000000000000000000018004000003000000000c000000000000000100080040060000028000000001001800000a0020000000000001004000
  | 21 => 0x51b0b5a07c00000000011d400000024400005ce00000000000000000000000ad400042f8000ff4000000242ceb2000000000000000000013a50e200046c9994eac43123317a87ac14d0000000e5e00000016fcc1c4be000266e00000013f8000d120e080000002bc60800000000009582ef80000420000000000db455000012f40007123c6800000027d000000000000723ca70800000000000004a3000000000000000000000009605710d10ae400082f0b814f80003df00000000000003349a640000001eb92e40000004be9f180006f1000000021a000000000000000007300010ce80a00000008a012d31807dc00016d00000000000000000000000157000039400000008e09e800032e14e80003c28d00000000000000000230cbe0000000000000000000000000000000000000df628d02c00000000003e000000003892e38c2800000000000000001c80000000da85b624a000000032500000000000000000f64000000000000000089000000000004cf80008d438600016f800000030d4c38b28000000000171014400005b54a4000000000000000059105902340003fe0000000ba874900000000000002bd1d84a2c6a43bb9fe255a00000000000000000000f6c42655200028c0000000000000000000046aa20c00064638882ca492000000000000047a0001a949947781d29a344e31fd800000000000000000000005a7000133400000000000009501440001b5c00025300000013960003b800006361904cd0000056000000000052e00000000000005fb39180000000000000a9400069d1b480000000003f880000008a600000000004000001bd00006dc000000011698980000004764683510a1400000048698f40d200000000003fe2c088080000000002ce400000000000000000000000760744000000271800000000018b000070e25a3258f2891a0002008000000934000000000000026a09388d64ba0ece62ef1e378000000000000017b806a380000000029800069200000003d60000000a986fe0000001308000330000090800000000021d94188b93ff18a8e2800000000006d0260000207800000046e81acf8400000000000000004a7c00063800000015f400040a0000000fd82281e584440000000000000000055800080c00000046c00005cc00000012f08b200004600006ca0000000000c9a728000000000088a46100000000af26f890486c95745f93111ce26b46f227000033c3b7800000000000006e80000000000524000000000066466a390000185c0000000000c0000000000026d80006cc2ed58dc8bc58500000000002150000dd53de5fdcbb800000008e0f8800000000003c0000b1468b0000c04cfa9591aac650b788af8002874b3c0000000000000000000000000000038aa7f80000001da00009a
  | 22 => 0x37b13a00000000000000000000000000000000013a9d9545a4230000001022000508800000000039580000000000000000000a23000000041e52d1e124bc16280650d87a00000000000000ae6000000000000096b00000000808c118486ac0000002ed10382a00000921e281060000000e4a2540000001ad45081f202f00000000003eb000060a000000201000027700000013b63b50a880000007050000000a189c93f3256cfc70001418a1875c4771e0400000000000000004489f94b192ec32ca1327395b924208a00000007fa57b0001d300005de0000000cb800047680007a41e400008b00003560001604d2a0000000d90000000000008ec5600000000000b68704188000000000105000066c00000000000d451c032864271011b0e0935921c3e700000600001a709f1754a480113d59c600da62e2cf80000008f33cc0000c4a7f718395c915c5f63981c4058a4a61ae8fa006a79b4638b301c20000df8deb08c12c84b80005d8038000000000067e0b3000000000001a000000000049e800000066a0000000000000000000073a4ad0000dc935400000000003ea000000000000000000000000000000000000000000028800000000041901080000c8bb4a1f91d45b73ad800000088180000000006a1800000000000000000cd41e00000000000006b23ee800000000022880000000004f903c80005dd0784e780009f80c4800000000019fd1bc000000428000000063f0001e952a25b90000000e443824f6000103000000026a419200000000000002e195d8000d360000000000000000000228000000000000000000002d20d1c8e2a1800001200001340001fbcc3000000bc0005f15602689e38000000000178c00000000fc0011e300037317ce00037e2410e00000000000000000062d800000000003c000000000088f00020fcf5253c00013e80003d400000012ce00043405d48f818129d8de60dca06000014c00000000001bb3aa0040000000a2000000000000000000001d98ade0000001ae0000000000000000005a0000000630000450a294000000000000000000000000000000000000000000000000143c00068f00000011047a8000042400000044a801800008929a0b7137658e00000000008a200001cc0000000000000000000000111cedc00000001340003e24d900000002713ed1224000809000000000000000005f80000002d60000000000000000000000000000000000000000590f726ca00014ba00096e000277800000000000000000000710dcc0001153aa8a400002a900ba1a40002d900006080000004e700006240001a74000de600000000000009ed1d300000004334dc8ba800000b00000000000000000000ac8000000000000000000000000000004981f8000000000020e0fb6000000000111d18080
  | 23 => 0xd794282c177f000000108a71300000013500002ff887c6287ee000000000034805098287de00000000000000000000000a0c00000000000005c20000000d6e00000000000002af0000000a26055446000104c9810000000fc60000000e9c0000000000000000000000000000020380026141f800044d8000854448000000000000000023fe00000000001400000003d10152fec0000000a708ae0001898000000000000000000043b00000000000002bc800000000000000002e60004278264000a32000000000037627980000000000000a813fa6d324c035e000000093800000000000000008f63710000000bc200048a09452540003d50000cc800000000000000002cec000000460000000000000032b8000d5000000000000000003f50000000000119947ceb163a0548000000000000272800000000000003cc0979cad7c40000000000000000000254981800000000000000005e2089000051e0220000000000607000172800000000020b00000000000000000000000173c18e394800000000033b00024cc00004b000000122ca070000d4000002b80000000000000000000f920002a300012aa0000000000a7a0000000000dd661c0cd800031a00048cc9bc0c20000002014000000000000084c9a1000099457a00047c93b40005aa000000094709c00000013b00000000b1c00000000000000004040000000000000000000000073400006680ae2c380022d88a600041c8000a12000201000000093e19b800000077e000000000000000000000000dd0000000000000400000000061e39a8b6cad60000000bab3c266c2a41c302fe0004ae23c8000813000000000081239b80011909cd0000000000000169800145f0001238000000905151a8ac0004f9000000000000030a122ca6a0001ff888932a4a74491968000655000000000085c000000000095f00008c00007740001e751947f2b57873441c000000000000000000021fc00000000000000000000000000000000000000000072d3bb000081a2730000fb40000002a9800000058400000000002310000000000a1a0000a88000000000000000000020c2110000000000000056c1d9000000134a0003e92064000a1f2320b580008eb15f8000000000000000000000000005051db49f1508000000000000076800000000012644d40000002690000000000000000020d0000000b2a0000000000c360000000acc0000000000000b1a00012f8000a2a000000000019f5f72df18c935c3193a0890d28a0795008c0c00000000000008d122d0f6925c3d200013e000000018e00003d800063300018d8c6a000000000063a84e190a80c000000000264e0000260000000f5800000000000001a82d9051c0000004a48000000000000000000021c00000000004830000cac00000000000000
  | 24 => 0x47400000001ee00000007327de26600000000000d800007020f1800000025801900000000003d800000013101602be00000000d82618000000000000000000000043f58482945760658e5ec980412ab8e3e3784c91ee04024aa07126000000000000e3000000000003600000001d8168c0001dd00000022c20000002adc0000000000000000000a2c0001aac4a90000001cc80000000001a98a80998000000131e0000000000000000000000000000011a00000005f309996ac00000000000000de0000000000000287000000000099b32ca83501c00000003fc5e200000006a800006600000000000000000000db2901000000000000000002110920003728550c8264e00007bc00000026d8b2000066d0001ab436a9b5000030092c17b07a0000000000000000000000018309d82eb2be0df145cbf21f60000000e9e83522100002764d3000116c0000000ad0a2c000654000000009e3c1000000096600005cd6b4000511000092800000000000008860003c000000001e500000000284da0002670000186000000000000000000000000000000000000000000000000000000025a93a485d00000000000000000000000853000059c1ea00000005d2b746431d480001274700001e840002cb4eec41a000000076800000097e00008b85d000000020a800057807c0cb0000000000000000008600000d800000000000e41aa1ce22b1890bd01378eda38b0061360001d4c00000000000000008810001efc00000002189787e20d400000009fa00000000000002ac4ec80000007fc32400012640000000000eba1bd47d000000000002a16200000000000000ca93a800000000000000000148c44000000119e00000000024a40001bb2f5800000000047c058cf6242100000000000002ae80002c7000149000039800000000000000002d480002960000d78c8c00058c000000000000000000000000001010000000a0200013f8a0000000000000002e40bbc0000008403c10000000906000000008e989000000074400000000dce7600017a00000000000001f1000000000000000000003c4a5b0e540000002202000663000197e00091502300012d00000000a7800000036580000000000000000e4000023a0bb80000000001864ff30000c01a3009c6ac01807542c552c2ba8de4bb800033a80012e400045c036c0000000e98cfc000000472800104696d00004a0000000234943800000000019c80002e5000000118a00008b00000000002720000000000000000000000041b00000000e800000000004030000000000000000000054e1ca4ed000045e000000000000000000000003700003908001206000363000101a00000000006f60000001e780000001aa1de4286000452000075a6050000000000000000000000000000080000004c73
  | 25 => 0x70d00000005140005cd00000a6000000000000000050101380000003d12ae00009fe272000000000000000000005de703000000000067342f00006ce6f90001c2400000000000003620000e398830c0a200b9c3a800000000023bd29c00000000000006600001b740000004f502420007bc00024680000004b8946800000038b259400087a4e4167a43407b000000000000000012fd29e91129980013c670b0000000000000000000000099598a9a4000095d13306b40006c300000000000000000000d463c300000000008c411d00000004ae0000b3400025b00000000000004cb22640007e500000000000001fca14400000000000000004ee000000000000000000000000002a880000000004900000e32947000000000059b000000000000006b800001800033d0bc0f760003af80000000de1290000000000000000000050836b00003ac000069800000077b04a4a660002672b39f40000000320c000000000000000096244f000000000000000000000000000000c787f000026a96c0de023600000013160952334960000000000000000000000000000000000000000000110213800000000000000000000004a100000000000000000f6e0000000000fce00033800000008e30e8000145c000000000072a4cb00000002620290fd104818816f2c805d000000017b00000513520000000000000000066000075e00000000000000000000000000273000000000000001d0000327000000000000000000003be0000001f6e00000042a80008ba00000000000000000002380946000000000000038d000000017600046f80000001972641a5c0943bfbdf057c908649000000000000000022d400035150a23c452a0004df000000000000000000000001fb80006cc5ef0000000550298360a69c0007b030e873e2100003a38b000000004a60000bd20000000000000000000110119e2a40000918694000397000000092d000226800000000000000000000d6212c0000003b2000000000000000013ce348800000000000000542ccc26000176800000000000026483f80001f2a8200000004ce872400078800000000000000000000000000000000000025d000000013e9f0000000041600007580009e400000000000000000000000000000000000005a0003e780000005d309f800000000000000001840000000000000000000163c0001f40000000000000000000000000000000000f43610ebd94c708000000082000078345a1a9cf2a000000233000063799200000006fd267258400000000022c800000006740000000000000000c0097c1df1f7e0008632aac00000000000003b60000000000000f6c67900000012f26ef2ab000000007e3210d04be400037025bc4e89e537f000050400000000000002640000000
  | 26 => 0x8115a873c00092300000249340000000000c180000d9800000000000000000315fd0002800d34a2800003380000000000000d260000001b380003e6000000000000000000000000001a18d1800023c0000ec400000039b00000000000000000fb80000002260000000000000000065e454a4b002a2003948bf8e665c0000000000016500ec00111000043a800085e000245de800005f41c7843c000000187000083c00029c800000000000000000008ab24e800000000000000000009e4868800000099fc18167068400000000001224860001f291c40000000aeb3bd5f50001f3126a00024880000000000000000000000000000000000000000000008074d58678a9800000000000000000001408e780004d180000000000002688c7283c00019dd3c0122453a0f88176ae000000000000018f80000000c84e300000000004b3000000000000028a8000000000000036c00028c0000000000000000000024c0000000fd29cc07718083e04d5b9f84e6a1a6860000fe878a68a0000a2440a00034a00003229e800000b0ad229b26c800113e7000001bc8000000055a88e00000000000000000001a2800000022fa47006600000000008180000000000000000000216000000000016f09b125c00000009964b811f00000000000004f8807a1400000528000e040593438000aaa000000150cd7600000015614380002140b1822800000003e50da65100000010cc0002e4142c3e62d1058024c00000000000014529b44fe2440fb00000000000170978000000034a26d0794538000000482285889871b000000000000000000000000000000380a922bc445a3351d88f70000eb0f7a9390000000050000000077400070400025cc00048c0001ac0000000000000131c000000141d31b0000000f200000000000000ef400024080000000000b600ba000925800158800000000000000000000000ae85a86df00018f000000032fa2e835289e00b22c0000455000176c00000000000000000002a3800000061f80008dc0006e200025f60001dc000216000015800000000002618000bd40003ab0000000d029700b94ef40000002de800068f204b3f80000cd00021f10894593e0000000000002a3dc12800000002e81ee80000002c38000cf6407000000000000000000008a416247e8db40004b80001b8c0003e400000000000000001050e8000000000000000000000000000000000000000000000007500000000000000000000000000000000012b000085600028f000000087880000000000230000000000000000000000033300000000000000000000000000242c0010a80004d61a00d1c0000000000000000000000000000021e66980006612350ae000000034f00000000000310c311225d900000000007480f6000000000000000010ee000
  | 27 => 0xd2ac872cce22b200000000000002f2000000000000000008be44900005d80006ba0099d9c88800029100000003c700000002ba0004a6800000005f46b80000005984f200000000000000000f6800000000000000002c18000a0600008e800000035b07ea2f91500f3000000099e000000000000059227a135c00000000000000fa00000000000009741af0000000000000236898a86a0000fc0000000000104000040646a0cbc3060002fd1054a42000000157c98900020c8f3c000156000000000048021f800000000004800000005a6122168c0000004b213bc9d818d8000000dd20000fc40000000002940000000000000000000000024e08780000000001e4ceae0d207f0cc49366a11e722382f452f4e3a6780000000001be00000000000000000000000000085a0003bea227004000000000000000037d079e00000036d9514e5800000000000000004a9000000015186b000000000000000000000000000000000000000000000000000015c01b40002c484ac000927131886c00066b00000000000000000000fe400038b80000001b70000d3827232204c2276000000000000000000000002dc00039838f0250cba33200010680002620eec0000000000000000000000305898ebb0000006800000000051380000003f52ba00000000cd0624000b0000048480007e40000000000000184138021d01038600015760000000000ce400000000000000003970001bdc3fc000089800000000000000000004932230c80d84000000000136e6f542d8000a4e0004434e2c000000001000000000014f80000009174d78e5800000039c800016f0004faa1b8000000517965c00093b43200000008bb502806c00000027b0304000000125867021836e17e80000000000000f8c604473255193d2860000000d4c0002e217d000048a0004c9800000000000000007230000001ac400000017e23de0006260be800000006027e04e13880000000000000000000000000083a00000000009ff000232ca400e30001b54000000000000072100007640002520000ce80000006c80000a200000004eb8000d2c1db80024a00008db3da8000000000000000032a0000002080fc5000000000069a92b0001b907a612f031800126c000000000000000000000000e4000000000000000a00000000000000000000fa812605a00011ea0000000000c4e47e4fa000000000029800006d40ba0001b9c00015b00004f00000000000000000a153c8000123c209000000000000019a00000000002e180000000000acd2903fa26e4fb04f400000000000000000001d81f3800000000000000004132e5800000000000011505e400000000000000002cc919456e90c4bf831470a5e70000000a8800000000000000000120094e0e0000000000000000000218823282e000000
  | 28 => 0xd7062c00061123923f0e9a1400001094c940004dd00000000000000000e1c5b5000000000000000004000000820000000000000110824a01e8fcace9dacca40cf082000098d2d73c31030fb2172220800000060f10080000000000001d60000000000023f178000000000074082d0000000000000000260cc7c00000000000000000002428c120001d90000000593423800079a9763600000b9862d43d400000075a000282849a0000000e7c0000004d008f80000003238000000841000085caee00000000000000003ef9958ac600031c000000055a00002a096a5362d880000001051a220cc0000000002848000554000000000000000000000004d8000000131831047da4900000002710000000000000000000000000000000000000002864a847f5000000000000023c000047a3260fc9f04766000000000000000000006280000000000a7330000000020844fc6fc376000000000000018040000000001ce90e41a03d9902c9201c23ba99d8000000000000138200000000000000000000c3c6d681c0000000000000000000000000021a095c3c000004f08c8f383b64a00a0000000000009e00001880000000000000000088c00000000000011ac00049c0000fa2000000234d20e00000002d400000000022007428b7000000033e31700000002d400000000000000002990000000000151e28c0000000ffe8380003b800000007261358000000134000000000000000000000007e60001a4e4f000000027080000004de000000048b37d00004b90348225120000098000000000137986b246518c000000230800000000000022508fa000000000000000020e00006100000a1000128c0000000efc0000000560bcc0000004cf88400000004ddc00000000034c01a00000000001fb40008ce35a21300000000000000000000000000000000000000000000000000a440000001c9000000000000000007540000000aa80000000e280200000000000000d3e94100012d800000000000000003ea3f5800000026cb48800000000000008500008962fe16e00004c1492a7e80004b4000000000028c00000003bca100000874a70254463000088a2b40001eb800062f0001f840000002728d8c02000044a400000000030f80009ba55b000000137012100024c523000001d82d9408261000000000073e3f200013040001dc8000000000000000000000000026280000000001d8c8400004bd800140f0032b6000031800000000000009bd000000000000000000000000002eb26400000000000000a280bc11c27cc00005600027740000000e200010f900000010580008b30551dc4f90000000000000083b0650000000000000093c00075100000000000000000e5000000011299f00000000070000000000000000132e727161800121081
  | 29 => 0x574811d48b9c00041e86c800087c3fa000000054b00022a8000467437a3d00ee20714c8f7800043d0000000000000000240000000005e8000000000000000048000000021ec44e7cb08f0000da21388000001311349000257800000000000007180000000000000000000000000000000000000000000001e3000000000000000004f521c16cc5a40ef3b400006e801f27b90252f433c80008c6000000000000102ca2604641910487ff2b2995e894568225826c42c66f000213481016e00012c80009ee4454000000000000000044c00019ddba80000000000000257000000000000000000000000002e000000000000700000364d9a000000063c0007cd0b880000004ea0001914a3a1a4000000080a000000000083e00000014640006c7800000000079f0f1162ce88a2100000000000000001ec80006d20000f18b8a00000008ee0000000000000000000000000130846d4e001d80000000000000c889120000f100000000000000c2a01e22e05e0000000000188d3a22d83ea8342d9e47f0002224b5e94b00000004400000000001332000000000045282500000007d62c401882b912e00000000007aa0000000000000000439800008800015fd41400000000000000004760001b240008e609aa06c0000003d1800000000019e8554b760000000000b4000000020dc00068200022740000001f48000afe0000000000000000472000089a0a70000d600005a5000000000000014993c455c000000046800000000000000000004e28000000000000000019b0003ef63fcd725ae000000000039a0b480000001d700000000000000000000000000000000000000029180000000002a080f4acc66e3cb800000000000009a0ada8fe3c212bc58200000000009586200001fa00000004431df0000000102039000000000021d012c67817f9b400009863a1000052800004ea1e00000002f700000001ea800209d3a788743e800000a00021b800000000000000012d2000000000000000013c8000000000255800000000000000000002cc80000000008560f387a6000731000000000063400000000000000000000bcc000000000000000000004382906b34749d28000000442a05c00000051280000000d01d780000000000000000cce00000017180002c90001af40008c900000000000000000e4400000000000000000000000f840000002d40d686de4dc21c8000ee47fb0000000000000000000102a000000000000000038300000000000000000b280002c118b07f834c00000000004c6000040c0005254ad0000dda3f600000000000000001e640000000000000d0600000000000000004ef97490f21590990000e380000000548ec400000000000000000000000000000000000000000000000000000001060000f0e000000000000000000000
  | 30 => 0xe240000000000001b600006ee4b1000003854e1718248000000000000000000000000000000000001f5c000000000000009b00048da47400029a00014dc0006de308000011e000424149800000000000000000004060000f34000000000138600042c955200008811c8000944000081000000000040a000000000000000000000fbbf800000000000000000c3d0004420000000000000000000000000000000008342b0800000045a000000020e000000000000002007da2b46f80001950000d782ce3c5a58000092200006d00004fb3f1000000000000008fc0000001d20000abc98d00000000000000001f140003bb00021681f4000000000141600042900013cc50421228886be000000030c00084248c800000000000007480003a31ee80005b431148e0000000708000078c00095400010c0000000000000000005c800183400000024380fc00000008589200000000000000e7a70f0a6265e000000000000000000000000002465ec06600013d67c73c91b140000002e08074f4e38580006846960bf4fb82e428c0000338000ff24e000000000005860000000000000000000000000000000006d800000000000008d100000000000000000a2800044e06e0edc00084a000000086a000000000000000000014e94626280000428000000185a44c00067400000000003291c70ce80000000000000000000000000015a0001fd8000c080000c38f4092a0000d3005af2800005191b80006a00000000000000000000000054d0001d1800028e00004dc0000000001ba0bca0001611e585f60f71c501f000019300005dd1806f88000c6800000000000000003774d692ca65a00016808481be950000196d3781a300000010520000000000ff071f00000000002cf13d80000000000000ee800075c4ab000111a125301800000033e3c8a6c05f25a14a9800000000001d17a200000000000000008e1000000090a0003b513c00000000000000e96000000000000048f000000143c000000127800000032c000000000000020044222b000000000009d78001d4000000030d268200000000000000004d017c0000000000000000132800001240011e037a4d9800121900000000013d28bd0001eb40006e100000000007f19281b10e3a0000000a82e1400000025100000000000f240000e731481749f00a421487ec87800000000000000000d340006aa000000203c0000002eb9284e4c8574e817da4d20000000000000000320210c0923
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x401d1151441731814100748d45105c86050401d2151441721814100487e6154153634840121f985505418d210040fa6354dc5659000143591d537159640104b1245864c8329000103e98d5176546402ac0fe6165dd1519000103f985db74546400050d25d8458551900016149361161546400058924984585519000143696d0571195400fe0d607411d951500014359190076545400040f660401d9515000143591100765454000507650509cf65c80014559114273d972000507654409cf64c80014959110273d93203b40f66054dd954c80ed42e9215376553200040fa60545d954c80410cc9858d710cb2010531245635c432c80416449158c3254720105a1245630c941c800121f985505498e2000487e6154151638800103f985d074d95200040fe61751d7644800103d9815276551200040fa60541d9544800142e92150765512000613e1f6558c3248001a4481d95630c920006912046558c3248001a8481d91630c920006a12046458c324800184f85e1d630c92000631e1c8158c3248001a8784205630c920006a12108158c32480018cb87e01630c92010433261635c432480414c49158d710c9200051324d219db5148001c314144276d45200051324d211d9514800144e93880765452000519646201d9514800146591080765452000718485101d9514800184c7620d72545200052324d219db4148001c315144276d052000523e5d630cb41480416849158c32d05200052324d211d9414800148e93880765052000529646201d941480014a591080765052000728485101d9414800188c7620d72505200052325d630c941480416849158c3250520006199d98119721480010ce981cd63c8520106312047358f2148001c4461d947348520106312047358d21480414c4915d8324c12010570245730c9208400141d9519073591100050b654641c9644400141d9510073591100050b654401c9644400103d9815276551100040f660541d954440014359115076551102ae0d604541d954440018678754562189100069120d5158862440014c4964c9710c910005a1259320c94144001531951db7050510004e8e4983dc141440013939360b7050510006251d8835c141440018a476209705051000564652515ce2044001d1151d05738811000554656415ce2044001d1351505738811000744545415ce2044001465911d462481100061c1d9811d520440018b076604744811010532259730c920440019c173604324811000658dc887545204400156297a0951481101cd5825d825452044001960876095148110005d024d82545204407356297cc9514811000668dc88750520440034b0965cd414811000568a5e8250520440655a09760941481100066821d82505204400178093609414811019568a5f325052044001d81730c94148110
  | 1 => 0x2600054e20000068a6230416c9e6c34104030000120721b000000c0a3c0a00854429ac00000b0d830842a8000022260b80065391d8dc4300160e07323d7478862c80042071a00074120800000670000000000000000000e0004a001f8021342188c9044d301003a170700000662f00000002b118f60b3e89cb45c0618c8e00178000000001f00069000b06011354007c6230800003300034de491217c0000048003b00148dc54753692200740f12c70500003c5601291a9021f0c8010000045908a203f1440000270085a7f1d9e8000022000008302850f2032500000000000000770015c263d1a81c18000000080068300000080800000ca80444181808040800004c0c140014000008200004000c001c1004043804080142e9615272181540050ba58545c860550014369615171181543b40f66054dd9540c80103e98151765503210433a63874c9610c8412c698e053258432104b1247804c9610c801531919417094d41104e1a63814c8325044138491e01320c94100507654601cd605040142d951807258141006075d683994605040189571a0e65181410060b5d68299460504018a571a0a651814100744d45105cc6050
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2041460532e6c08649022020b20299730c94148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x124d
  | 8 => 0x124e
  | 9 => 0x3
  | 10 => 0x8a
  | 11 => 0x8d
  | 12 => 0x8e
  | 13 => 0x98a
  | 14 => 0x98d
  | 15 => 0x98e
  | 16 => 0x128a
  | 17 => 0x128d
  | 18 => 0x128e
  | 19 => 0x150a
  | 20 => 0x150d
  | 21 => 0x150e
  | 22 => 0xa0a
  | 23 => 0xa0e
  | 24 => 0x130a
  | 25 => 0x130e
  | 26 => 0xb0d
  | 27 => 0xb0e
  | 28 => 0x154d
  | 29 => 0x154e
  | 30 => 0xb8e
  | 31 => 0x184e
  | 32 => 0x3ca
  | 33 => 0x3cd
  | 34 => 0x3ce
  | 35 => 0xcca
  | 36 => 0xccd
  | 37 => 0xcce
  | 38 => 0x15ca
  | 39 => 0x15cd
  | 40 => 0x15ce
  | 41 => 0xd0a
  | 42 => 0xd0e
  | 43 => 0x160a
  | 44 => 0x160e
  | 45 => 0xd4a
  | 46 => 0xd4d
  | 47 => 0x164a
  | 48 => 0x164d
  | 49 => 0x104a
  | 50 => 0xb89
  | 51 => 0xb8956
  | 52 => 0x4
  | 53 => 0x180a
  | 54 => 0x1609
  | 55 => 0x1649
  | 56 => 0x1849
  | 57 => 0xbc9
  | 58 => 0x19c9
  | 59 => 0xbcd
  | 60 => 0x19cd
  | 61 => 0x9cd
  | 62 => 0x168d
  | 63 => 0x168e
  | 64 => 0xa4d
  | 65 => 0xb4d
  | 66 => 0xb4e
  | 67 => 0x16cd
  | 68 => 0x16ce
  | 69 => 0x3c992
  | 70 => 0x170a
  | 71 => 0x170d
  | 72 => 0x170e
  | 73 => 0xe8e
  | 74 => 0x178e
  | 75 => 0xecd
  | 76 => 0x17cd
  | 77 => 0x409
  | 78 => 0x449
  | 79 => 0x3d512
  | 80 => 0x138d
  | 81 => 0x589
  | 82 => 0xcd
  | 83 => 0x12cd
  | 84 => 0x14d
  | 85 => 0x749
  | 86 => 0x134d
  | 87 => 0x198d
  | 88 => 0x1949
  | 89 => 0x1789
  | 90 => 0x40a
  | 91 => 0x44a
  | 92 => 0x188a
  | 93 => 0x1a0a
  | 94 => 0x10a
  | 95 => 0x4d
  | 96 => 0x20d
  | 97 => 0x140d
  | 98 => 0xeca
  | 99 => 0x1a4a
  | 100 => 0x17ca
  | 101 => 0x5ca
  | 102 => 0x58a
  | 103 => 0x24d
  | 104 => 0x18ca
  | 105 => 0xe8a
  | 106 => 0x178a
  | 107 => 0x144d
  | 108 => 0x194a
  | 109 => 0x1a8a
  | 110 => 0x14cd
  | 111 => 0x74a
  | 112 => 0xcc3d2
  | 113 => 0xcc3d5
  | 114 => 0xcc3d6
  | 115 => 0x15c3d2
  | 116 => 0x44d
  | 117 => 0x1a0d
  | 118 => 0x104b
  | 119 => 0x188e
  | 120 => 0x1a89
  | 121 => 0x40e
  | 122 => 0xbc955
  | 123 => 0x168a
  | 124 => 0x9ca
  | 125 => 0x198a
  | 126 => 0x94b96
  | 127 => 0x10e
  | 128 => 0x983d2
  | 129 => 0x3c092
  | 130 => 0x1503d2
  | 131 => 0x94bd5
  | 132 => 0x3d292
  | 133 => 0x3ccd2
  | 134 => 0x3d5d2
  | 135 => 0x3d892
  | 136 => 0x3cd12
  | 137 => 0x3da12
  | 138 => 0x3cd52
  | 139 => 0x3d712
  | 140 => 0x2cd
  | 141 => 0x184b96
  | 142 => 0x104c
  | 143 => 0x19cbd5
  | 144 => 0x1a9952
  | 145 => 0x3ccd5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 36
  | 7 => 1515
  | 6 => 6195
  | 5 => 2611
  | 4 => 135
  | 3 => 2
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
  | 8 => packedAt gbK8 (1083+((h/21+packedAt gbK8 (936+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (63531+((h/623+packedAt gbK7 (56055+(h % 623)*12) 12) % 2469)*12) 12
  | 6 => packedAt gbK6 (329952+((h/2328+packedAt gbK6 (297360+(h % 2328)*14) 14) % 10144)*14) 14
  | 5 => packedAt gbK5 (166399+((h/950+packedAt gbK5 (154049+(h % 950)*13) 13) % 6664)*13) 13
  | 4 => packedAt gbK4 (9826+((h/47+packedAt gbK4 (9450+(h % 47)*8) 8) % 207)*9) 9
  | 3 => packedAt gbK3 (164+((h/1+packedAt gbK3 (162+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff0ff03fc0ffffe0ff01c07c09d33e99f793
  | 1 => 0xf01f07fc1ff0780ff07fffffc36acc96648ff
  | 2 => 0xf001ff8001fff800fff801ff83c730f1878f1c
  | 3 => 0x1fffffe000000fffffe0003f83f01f80fe0
  | 4 => 0x1ffffffffffff0000000003ffc001fff000
  | 5 => 0xfffe0000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x110c0190024008866009044118000112089391
  | 1 => 0xa102024409105080102509460128448224026
  | 2 => 0xa0255682116ad012bad0092b09c530b1858d18
  | 3 => 0x80499b5ab4084024dce4ac0212e83b01d80ec0
  | 4 => 0x881ec6f39bce6780840300c237fc001f76000
  | 5 => 0xccf0000c203084401080c03043bffeec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37055
namespace PEqualNP.Outside.L_meta_37055
open PEqualNP.Outside.L_meta_37055.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 21 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 68 := (concat bs1_3_0 (concat bs1_3_32 bs1_3_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 129 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 45 := (concat bs1_5_0 bs1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
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
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 8 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 92 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 8 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 92 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 2 := bgb_3_0
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
theorem bgb_4_128 : Interval gbAtlas 4 128 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 135 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
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
theorem bgb_5_2592 : Interval gbAtlas 5 2592 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2611 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)))))) (concat (concat (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440))) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)))) (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760))) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920))))) (concat (concat (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080))) (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240)))) (concat (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400))) (concat (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496)) (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)))))))
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
theorem bgb_6_6176 : Interval gbAtlas 6 6176 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6195 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)))))) (concat (concat (concat (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))) (concat (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)))) (concat (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))) (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272))))) (concat (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464))) (concat (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)))) (concat (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072))))))) (concat (concat (concat (concat (concat (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)) (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264))) (concat (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360)) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)))) (concat (concat (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648))) (concat (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)) (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840))))) (concat (concat (concat (concat bgb_6_3872 (concat bgb_6_3904 bgb_6_3936)) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032))) (concat (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)))) (concat (concat (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)) (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416))) (concat (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608)))))) (concat (concat (concat (concat (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704)) (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800))) (concat (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896)) (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)))) (concat (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184))) (concat (concat bgb_6_5216 (concat bgb_6_5248 bgb_6_5280)) (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376))))) (concat (concat (concat (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472)) (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568))) (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat bgb_6_5696 (concat bgb_6_5728 bgb_6_5760)))) (concat (concat (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856)) (concat bgb_6_5888 (concat bgb_6_5920 bgb_6_5952))) (concat (concat bgb_6_5984 (concat bgb_6_6016 bgb_6_6048)) (concat (concat bgb_6_6080 bgb_6_6112) (concat bgb_6_6144 bgb_6_6176))))))))
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
theorem bgb_7_1504 : Interval gbAtlas 7 1504 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1515 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))))) (concat (concat (concat (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928))) (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))) (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 36 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 44, 60),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8feeaeeeaeeeaecc8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4008373448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37055.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[4,5]⟩,⟨.and,[1,6]⟩,⟨.or,[0,7]⟩,⟨.and,[2,9]⟩,⟨.and,[3,10]⟩,⟨.or,[0,8]⟩,⟨.or,[4,5]⟩,⟨.or,[1,13]⟩,⟨.and,[12,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008373448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008373448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37055

open PEqualNP.Outside.L_meta_37055 in
theorem PEqualNP.Outside.L_meta_37055 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008373448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008373448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
